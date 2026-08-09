# Implementation Plan: Task #506

- **Task**: 506 - s4_loopchecking_machinery_termination_bound_and_decidability
- **Status**: [COMPLETED]
- **Effort**: 19 hours
- **Dependencies**: None hard. Phase 9 is gated on task 510 (see "The Task 510 Gate").
- **Research Inputs**:
  - specs/506_s4_loopchecking_machinery_termination_bound_and_decidability/reports/01_frame-specific-tableau-extensions.md
  - specs/506_s4_loopchecking_machinery_termination_bound_and_decidability/reports/02_spawn-analysis.md
  - specs/506_s4_loopchecking_machinery_termination_bound_and_decidability/reports/03_parent-phase-plan-reference.md
- **Artifacts**: plans/01_s4-loopchecking-termination-decidability.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Deliver the S4 (reflexive-transitive) tableau system: the 4-rule, equality-blocking
loop-checking machinery, `ReflTransGen` countermodel extraction, S4 soundness, and the
box-positive truth-lemma bridge — then attempt the `#worlds <= 2^|modalSubfmls phi0|`
termination bound and `Decidable (s4Valid phi)`.

S4 is deliberately **not** an instantiation of `RuleApplicationSpec` (GenericDriver.lean).
Phases are ordered so that all green, landable work (Phases 1-7) completes and commits
**before** the high-risk termination bound (Phase 8) is attempted, so a blocker there
strands nothing. Definition of done: Phases 1-7 green and committed; Phases 8-9 either
green or `[BLOCKED]` with a documented goal state and a recommended follow-on task.

### Research Integration

From reports 01-03 and direct source inspection of the current tree:

- **Equality blocking, not subset blocking** (report 01 §7, open question 2): equality-of-
  relevant-formula-set blocking is simpler and still terminating at `2^|Sf|`. Adopted.
- **`Relation.ReflTransGen` gives `Std.Refl` + `IsTrans` free** (report 01 §4). The
  `extractModelWith` skeleton for exactly this already exists at FrameCompleteness.lean:78,
  and its module docstring already names `LoopChecking.lean` as S4's home and assigns S4
  the `ReflTransGen` row.
- **`LoopInduction.lean` is a red herring** (report 01, line 97): it is one `Forall2` list
  lemma about the *fuel* loop, not modal loop-checking. Do not import it for S4.
- **Reusable scaffolding confirmed present**: `modalKnownWorlds` (Branch.lean:89),
  `Accessibility`/`hasEdge`/`successorsOf` (Branch.lean:55-84), `outDeg`
  (FmpMeasure.lean:793), `boxPositivesOf` (Branch.lean:183), `boxPropagation`
  (Branch.lean:197).

### Prior Plan Reference

No prior plan for task 506. The parent plan
(`specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md`)
Phases 5-6 is the source of this task's scope. Calibration taken from it:

- Parent Phase 5 was budgeted 3h and Phase 6 4h, both explicitly flagged as exceeding the
  one-agent-run guideline "by design" and as "strong candidate[s] for a dedicated task".
  This plan splits those two phases into nine agent-run-sized phases.
- Parent Phases 5 and 6 both already carry an explicit `[BLOCKED]` fallback. Both are
  preserved and sharpened here.
- Task 503 Phase 4 (TDriver.lean, 770 lines, green) and task 507 (FmpMeasure `_gen`
  lemmas, green) are the validated precedents for file conventions and for how far
  rule-generic reuse actually goes.

### Roadmap Alignment

No ROADMAP.md found at `specs/ROADMAP.md`. No roadmap phases included.

## Three Corrections to the Task Description

Source inspection contradicts the task description on three points. Each is load-bearing;
implementers must follow this plan, not the description, on these.

**1. Do NOT extend `ModalPotentialInv`; build a sibling `S4LoopInv`.**
`ModalPotentialInv` (FmpMeasure.lean:2326) has 8 fields, two of which are exactly what
transitive propagation breaks:
- `rankBound : forall x in b, modalDepth x.formula <= rank x.label` — fails because the
  4-rule places `T(box psi)` (unchanged modal depth) at a successor.
- `rankEdge : forall w w', acc.hasEdge w w' -> rank w' + 1 = rank w` — fails outright: an
  S4-closed `acc` has edges `w -> w''` with `rank w'' + 2 = rank w`.

Adding a field to `ModalPotentialInv` would also force every existing K consumer to
discharge it, and would edit a 3,392-line file shared with K (bad under concurrent
sessions). Instead mirror the **existing extension precedent**: `ModalLoopInv`
(CompletenessLoop.lean:57) *holds* `ModalPotentialInv` as a field. S4 defines its own
`S4LoopInv` in `LoopChecking.lean` reusing the six rule-independent fields
(`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`), dropping the two rank
fields, and adding the blocking invariant. **FmpMeasure.lean is not modified by this plan.**

**2. Do NOT prove the 4-rule's soundness via `Satisfies.four`.**
`Satisfies.four` (Basic.lean:348) is stated in **diamond form**: `<>​<>phi -> <>phi`. The
4-rule is **box-side** (`T(box phi)@w`, edge `w->w'` |- `T(box phi)@w'`). The box dual
`box phi -> box box phi` does **not** exist in Basic.lean. Do not try to route through
`Satisfies.four` and do not add it to Basic.lean. Instead prove rule soundness directly
from `IsTrans.trans`, exactly as the T arm proves directly from `hrefl.refl` rather than
routing through `Satisfies.t` (FrameSoundness.lean:162-193 is the template to copy).
`Satisfies.four` may still be cited in docstrings as the semantic counterpart.

**3. S4 cannot discharge `RuleApplicationSpec`; do not attempt it.**
GenericDriver.lean:105-108 states this explicitly and names task 506. Fields
`outputsSubsetUniverse` (presupposes the depth-based `modalWorldBound`) and `rankStep`
(demands the exact-decrement edge invariant) are unsatisfiable for a transitively-
propagating `apply`. Any phase producing `modalApplyOneS4_spec : RuleApplicationSpec
modalApplyOneS4` is a defect. S4 reuses the generic driver **definitionally only** (see
below).

## Key Design Decisions

**D1. `phi0`-parameterized rule application.** The minting guard needs `modalSubfmls phi0`,
but `RuleApply Atom` (Saturation.lean:104) has no `phi0` argument. Resolution: define
`modalApplyOneS4 (phi0 : Proposition Atom) : RuleApply Atom` and partially apply.
`modalStepBranchGen (modalApplyOneS4 phi0) : ...` typechecks because `RuleApply Atom` is a
plain function type and `modalStepBranchGen` takes `apply` as an ordinary argument. So S4
reuses `modalStepBranchGen`/`modalExpandBranchesGen`/`modalTableauGen` **definitionally**
while discharging none of `RuleApplicationSpec`. `modalTableauS4 phi := modalTableauGen
(modalApplyOneS4 phi) phi` — `phi0` is in scope at the entry point.

**D2. Replace the universe's world bound, keep the counting engine.** `modalWork` and
`modalExpMeasure` (FmpMeasure.lean:192/197) take the universe `U` as an explicit
parameter and know nothing about worlds, rules, or `acc`. They are reused verbatim. Only
`modalWorldBound` is replaced: `modalWorldBoundS4 phi := 2 ^ (modalSubfmls phi).length`,
with `modalUniverseS4` mirroring `modalUniverse`'s construction (both signs x every
subformula x labels `0..bound`). `geomCap`/`modalPotential`/`modalPotentialTerm`/`rank`
do **not** transfer — they are the geometric tree-capacity argument.

**D3. S4 owns `modalHintikkaSetS4`.** `modalHintikkaSet` (Saturation.lean:423) is public
but conjunct 2 hard-codes `modalApplyOne`. Conjuncts 1, 3, 4 are apply-agnostic — and
conjuncts 3/4 are *existential* over successors (`exists w', acc.hasEdge w w' /\ ...`),
which a **loop-back edge satisfies natively**. This is a genuinely favourable accident:
the existential shape was chosen (per its own docstring) because fresh-world minting
breaks the membership condition, and blocking-with-loop-back fits the same shape. So
`modalHintikkaSetS4 phi0 b acc` is a small delta over `modalHintikkaSet`, and
`hintikka_box_neg`/`hintikka_diamond_pos` analogues are one-line projections.

**D4. Truth lemma is hypothesis-parameterized, hence 510-independent.** The public
bridge lemmas (`hintikka_box_pos` etc., Completeness.lean:146+) take `modalHintikkaSet b
acc` as a *hypothesis* and conclude in branch-membership + `acc.hasEdge` — never in model
satisfaction. S4's analogues take `modalHintikkaSetS4 phi0 b acc` as a hypothesis. Nothing
in Phases 1-7 needs the private chain.

## The Task 510 Gate (assessed explicitly, per task instruction)

**Assessment: the private-chain risk is real but narrower than task 503 Phase 5 made it
look. It gates exactly one phase (9), not the S4 mathematics.**

What is private: `modalApplyOne_fst_eq_of_not_box` and `modalHintikkaClause_lift`
(Completeness.lean:684/718), plus 14 of 16 declarations in CompletenessLoop.lean:57-712.
The shape is uniform — **every entry point is public, every helper is private**. So the
chain is callable end-to-end for K and re-provable for nothing else.

What S4 needs from it: only `modalExpandBranches_hintikka` (CompletenessLoop.lean:746,
~310 lines) + `modalStep_preserves_invariant` (:671) — the machine turning "the driver
returned `.openBranch bR aR`" into "`bR` is a Hintikka set". That machine is ~90%
rule-agnostic fuel-induction bookkeeping. Re-deriving it for S4 by copy-paste would
duplicate ~700 lines that task 510 is generalizing — and CompletenessLoop.lean's own
docstring (lines 112-121) admits two of its lemmas are *already* copy-paste workarounds
for FmpMeasure privates. Doing it a third time is the wrong call.

What S4 does **not** need from it: the truth lemma. `modalTruthLemma`
(Completeness.lean:474) is hard-coded to `extractModel` (`r := acc.hasEdge`). S4's model
is `extractModelWith Relation.ReflTransGen`. `Satisfies (extractModel b acc) w (box phi)`
and `Satisfies (extractModelS4 b acc) w (box phi)` are *different propositions*. The K
truth lemma is unusable for S4 **regardless of visibility**. Writing a new one is not a
blocker — it is the actual mathematical content of this task.

**Decision**: Phases 1-8 proceed with no dependency on 510. Phase 9 is gated. If 510 has
not landed when Phase 9 is reached, mark Phase 9 `[BLOCKED]` (not sorry'd) at the single
named lemma boundary `modalExpandBranchesS4_hintikka` and land Phases 1-8.

**Cross-task requirement to raise on task 510 now, not mid-implementation**: 510's
generalized loop lemma must conclude in `modalHintikkaSetGen apply bR aR`, **not**
`modalHintikkaSet bR aR`. If 510 generalizes only `modalHintikkaClause`/`ModalLoopInv` and
leaves `modalHintikkaSet` (Saturation.lean:423) K-only, its conclusion is still unusable
for S4 and Phase 9 stays blocked even after 510 completes. This should be communicated to
510 before it plans.

## Goals & Non-Goals

**Goals**:
- 4-rule in FrameRules.lean, following FrameRules/TDriver conventions.
- `LoopChecking.lean`: `formulasAtWorld`, relevant-set equality test, minting guard with
  loop-back edges, `modalApplyOneS4`, S4 driver defs, `modalHintikkaSetS4`.
- `extractModelS4` via `Relation.ReflTransGen`, with `Std.Refl` + `IsTrans` free.
- S4 rule-level soundness (from `IsTrans`, per Correction 2).
- Box-positive truth-lemma bridge by `ReflTransGen.head_induction_on`; `modalTruthLemmaS4`.
- Attempt: `#worlds <= 2^|modalSubfmls phi0|` invariant, fuel sufficiency, `s4Valid`,
  `Decidable (s4Valid phi)`.
- Zero `sorry`, zero `axiom`, zero vacuous definitions, at every phase boundary.

**Non-Goals**:
- Discharging `RuleApplicationSpec` for S4 (provably impossible — Correction 3).
- Modifying FmpMeasure.lean (Correction 1) or CompletenessLoop.lean.
- Re-deriving the K Hintikka/saturation loop chain for S4 (task 510's job).
- Re-deriving already-green rule-level work in FrameRules/FrameSoundness/FrameCompleteness.
- Subset/anywhere blocking (equality blocking only — report 01 open question 2).
- T, B, S5, or 5 systems (tasks 503-505, parent 300 Phase 7).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `2^\|Sf\|` invariant does not close | H | H | Phase 8 is last of the core work and depends on nothing downstream of it. Phases 1-7 commit first. Standing `[BLOCKED]` permission; recommend follow-on `s4-loop-checking-termination` task. |
| Task 510 not landed at Phase 9 | H | M | Phase 9 is the only gated phase. `[BLOCKED]` at `modalExpandBranchesS4_hintikka`. Raise the `modalHintikkaSetGen` requirement on 510 now (see gate section). |
| Implementer tries `RuleApplicationSpec` for S4 | H | M | Correction 3 states it is a defect. GenericDriver.lean:105-108 names task 506 explicitly. |
| Implementer edits `ModalPotentialInv` | M | M | Correction 1. Sibling `S4LoopInv` in LoopChecking.lean; FmpMeasure.lean untouched. |
| `Satisfies.four` is diamond-form, no box dual | M | H | Correction 2. Prove from `IsTrans.trans` directly, mirroring FrameSoundness.lean:162-193. |
| Loop-back cycles break the truth lemma | M | L | `ReflTransGen` absorbs cycles (report 01, line 275). Confirm explicitly in Phase 6. |
| Concurrent sessions clobber work | M | M | Every phase scopes `git add` to its named files only. Never `git add -A`/`.`. |
| Phase 8's pigeonhole needs unfamiliar Mathlib | M | M | Phase 8 tasks name the candidates (`Finset.card_powerset`, `Finset.card_le_card_of_injOn`) and budget lean-lsp search. |
| New file missed in barrel | L | H | `lake exe mk_all --module` in Phase 2 and every later CI gate. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4, 5 | 1, 2 |
| 3 | 6 | 3, 5 |
| 4 | 7 | 6 |
| 5 | 8 | 5, 7 |
| 6 | 9 | 4, 7, 8 |

Phases within the same wave can execute in parallel. Wave-1 and Wave-2 phases own disjoint
files (territory contract below), so parallel dispatch is safe.

**Territory contract** (file ownership; no phase writes a file owned by a concurrent phase):

| Phase | Owns (writes) |
|-------|---------------|
| 1 | `Cslib/Logics/Modal/Tableau/FrameRules.lean` |
| 2 | `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (new), `Cslib.lean` (barrel) |
| 3 | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` |
| 4 | `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` |
| 5, 6, 8 | `Cslib/Logics/Modal/Tableau/LoopChecking.lean` |
| 7, 9 | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` |

Wave 2 pairs Phase 4 (FrameSoundness) with Phase 5 (LoopChecking) — disjoint. Phase 3
(FrameCompleteness) completes in Wave 1, before Phase 7 reopens that file in Wave 4.

**CI gate (every phase)**. Run in this order; all must pass before commit:
```
lake build
lake exe checkInitImports
lake exe lint-style
lake lint
lake test
lake exe mk_all --module      # required whenever a file is added
lake shake --add-public --keep-implied --keep-prefix
```
Prefer `lake build Cslib.Logics.Modal.Tableau.<Module>` during the inner loop; run full
`lake build` before the commit. Verify zero `sorry`/`axiom` via `lean_verify` on each new
top-level declaration.

**Commit discipline (every phase)**: `git add` only the files in this phase's territory row
plus the plan file. Never `git add -A` or `git add .` — concurrent sessions are active in
this repo. Message: `task 506 phase {P}: {name}`.

---

### Phase 1: 4-rule in FrameRules.lean [COMPLETED]

- **Goal**: Add the S4 transitive propagation helpers and `modalApplyOneS4Rules` to
  FrameRules.lean, reducing to `modalApplyOneT` outside the two 4-relevant shapes.
- **Tasks**:
  - [ ] Read FrameRules.lean (113 lines) and Branch.lean:183-206 (`boxPositivesOf`,
        `boxPropagation`) first. `boxPropagation b acc psi w` is the exact template.
  - [ ] Add `modalFourBoxProp b acc phi w : List (SignedFormula ...)` — mirror of
        `boxPropagation` but emitting `T(box phi)@w'` (i.e. `.box phi`, **not** `phi`) for
        each `w' in acc.successorsOf w`, filtered against formulas already on `b`.
        Note `T(phi)@w'` is already produced by K's `boxPos` arm; the 4-rule's new content
        is propagating **the box itself**.
  - [ ] Add `modalFourDiaNegProp b acc phi w` — dual, emitting `F(diamond phi)@w'`.
  - [ ] Add `modalApplyOneS4Rules : RuleApply Atom` wrapping `modalApplyOneT` (not
        `modalApplyOne`) so the reflexive component is inherited: merge the 4-arm outputs
        into the `.persistent` output at `(.pos, .box _)` and `(.neg, .diamond _)`,
        deduplicated. Copy `modalApplyOneT`'s merge idiom verbatim (FrameRules.lean:72-95).
  - [ ] Add `modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg`, mirroring
        `modalApplyOneT_eq_of_not_boxPos_diaNeg` (FrameRules.lean:100-109) including its
        `omit [Hashable Atom] in` and its `rcases ... <;> simp_all` proof shape.
  - [ ] Extend the module docstring's `## Main Definitions` with the new declarations.
  - [ ] CI gate; commit `FrameRules.lean` only.
- **Timing**: 1.5 hours (~200 lines)
- **Depends on**: none
- **Files to modify**: `Cslib/Logics/Modal/Tableau/FrameRules.lean` (append; do not alter
  existing `modalTBoxSelf`/`modalTDiaNegSelf`/`modalApplyOneT` — they are green).
- **Verification**: `lake build Cslib.Logics.Modal.Tableau.FrameRules` green; full CI
  clean; zero sorry; `modalApplyOneS4Rules` typechecks at `RuleApply Atom`.

---

### Phase 2: LoopChecking.lean foundation — per-world formula sets and the equality test [COMPLETED]

- **Goal**: Create `LoopChecking.lean` with the per-world relevant-formula-set extractor
  and a decidable equality test over `modalSubfmls phi0`. Land the new file green and in
  the barrel.
- **Tasks**:
  - [ ] Read TDriver.lean's header block (lines 1-60) and copy its exact module structure:
        `module` -> `import Cslib.Init` (non-public) -> `public import` deps -> non-public
        `import` for proof-only deps -> module docstring (`# Title`, `## Main Definitions`,
        `## Main Results`, `## Strategy`, `## References` with `[Fitting1983]`) ->
        `@[expose] public section` -> `namespace Cslib.Logic.Modal.Tableau` -> `open
        Cslib.Logic.Tableau Cslib.Logic.Modal` -> `variable {Atom : Type*} [DecidableEq
        Atom] [Hashable Atom]` -> ... -> `end Cslib.Logic.Modal.Tableau` -> bare `end`.
  - [ ] Do **not** import `LoopInduction.lean` — it is a `Forall2` list lemma about the
        fuel loop, unrelated to modal loop-checking despite the name.
  - [ ] `formulasAtWorld b w := b.filter (·.label == w)` + membership characterization
        lemma (`sf in formulasAtWorld b w <-> sf in b /\ sf.label = w`).
  - [ ] `relevantFormulasAt phi0 b w` — `formulasAtWorld b w` restricted to formulas whose
        `.formula` is in `modalSubfmls phi0`, in a canonical order so equality is
        well-behaved (dedupe + sort, or compare as the induced `List Bool x Proposition`
        membership vector over `modalSubfmls phi0` — prefer the latter if ordering lemmas
        prove awkward; record the choice in the docstring).
  - [ ] `sameRelevantSet phi0 b w w' : Bool` — the equality test; prove `Decidable`,
        reflexivity, symmetry, transitivity, and the characterization
        `sameRelevantSet phi0 b w w' = true <-> (forall sf, sf.formula in modalSubfmls phi0
        -> (sf@w in b <-> sf@w' in b))`. This characterization is what Phase 8's pigeonhole
        consumes — state it deliberately.
  - [ ] Add barrel entry to `Cslib.lean` (alphabetical: `LoopChecking` sorts between
        `FrameSoundness` and `Rules` among `Cslib.Logics.Modal.Tableau.*`) via
        `lake exe mk_all --module`.
  - [ ] CI gate; commit `LoopChecking.lean` + `Cslib.lean` only.
- **Timing**: 1.5 hours (~200 lines)
- **Depends on**: none
- **Files to modify**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (new), `Cslib.lean`.
- **Verification**: `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green;
  `lake exe checkInitImports` passes (confirms `import Cslib.Init`); `lake exe mk_all
  --module` leaves the barrel clean; zero sorry.

---

### Phase 3: `extractModelS4` and free frame instances [COMPLETED]

- **Goal**: Instantiate the existing `extractModelWith` skeleton at `Relation.ReflTransGen`
  and harvest `Std.Refl` + `IsTrans` for free.
- **Tasks**:
  - [ ] Read FrameCompleteness.lean:91-130 (the `extractModelT` block). This phase is a
        mechanical mirror of it; follow its docstring conventions exactly.
  - [ ] `extractModelS4 b acc := extractModelWith Relation.ReflTransGen b acc`.
  - [ ] `extractModelS4_r` — `... .r = Relation.ReflTransGen (fun w w' => acc.hasEdge w w'
        = true)`, by `rfl`.
  - [ ] `extractModelS4_refl : Std.Refl (extractModelS4 b acc).r` — via
        `Relation.reflexive_reflTransGen` / `infer_instance` after `rw [extractModelS4_r]`.
  - [ ] `extractModelS4_trans : IsTrans WorldIndex (extractModelS4 b acc).r` — via
        `Relation.transitive_reflTransGen` / `Relation.instIsPreorderReflTransGen`. Note
        Cube.lean spells S4's transitivity `IsTrans World m.r` (Mathlib's `IsTrans`), while
        T uses `Std.Refl` — match that mixed provenance.
  - [ ] `extractModelS4_hasEdge_imp_r` — every raw edge survives, via
        `Relation.ReflTransGen.single`. Mirrors `extractModelT_hasEdge_imp_r`.
  - [ ] Update the module docstring's `## Main Definitions` (the S4 `ReflTransGen` row of
        its Strategy table already exists — do not duplicate it).
  - [ ] CI gate; commit `FrameCompleteness.lean` only.
- **Timing**: 0.5 hours (~120 lines)
- **Depends on**: none
- **Files to modify**: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (append).
- **Verification**: `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green; both
  frame instances resolve with no manual relation reasoning; zero sorry.

---

### Phase 4: S4 frame vocabulary and 4-rule semantic soundness [COMPLETED]

- **Goal**: Add `s4FC`/`s4Valid` and prove the 4-rule's rule-level soundness from
  `IsTrans` directly (per Correction 2).
- **Tasks**:
  - [ ] Read FrameSoundness.lean:141-229 (the T block). It is the exact template: the T
        arms prove from `hrefl.refl` directly, **not** via `Satisfies.t`. Do the same with
        `IsTrans.trans`.
  - [ ] `s4FC : FrameCondition := fun {World} r => Std.Refl r /\ IsTrans World r`.
  - [ ] `s4Valid (phi) : Prop := frameValid s4FC phi`. Docstring must state the
        correspondence to `Cube.S4` (`K ∪ T ∪ Four`, Cube.lean:81).
  - [ ] `branchSatisfiableIn_s4FC_boxPos_trans_mem`: given `branchSatisfiableIn s4FC b acc`,
        `T(box phi)@w in b`, and `acc.hasEdge w w'`, adding `T(box phi)@w'` preserves
        `branchSatisfiableIn s4FC`. Semantic core: from `Satisfies m (f w) (box phi)` and
        transitivity, every `m.r`-successor `u` of `f w'` is an `m.r`-successor of `f w`
        (`IsTrans.trans _ _ _ (hedges _ _ hr) hu`), so `Satisfies m (f w') (box phi)`.
  - [ ] `branchSatisfiableIn_s4FC_diaNeg_trans_mem` — dual, for `F(diamond phi)`.
  - [ ] `modalFourBoxProp_sound` / `modalFourDiaNegProp_sound`: lift the two semantic cores
        to the concrete rule outputs, mirroring `modalTBoxSelf_sound`
        (FrameSoundness.lean:199-211) including its `by_cases`/`simp only [..., if_false,
        List.mem_singleton]` shape.
  - [ ] Add a `/-! ### 4-Rule Semantic Soundness -/` prose block, mirroring the T one at
        :151-157, and explicitly record why `Satisfies.four` is not used (diamond-form; no
        box dual in Basic.lean).
  - [ ] CI gate; commit `FrameSoundness.lean` only.
- **Timing**: 2 hours (~300 lines)
- **Depends on**: 1
- **Files to modify**: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (append; the T
  block and `modalTableau_sound_frame` are green — do not touch).
- **Verification**: `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` green; zero
  sorry; no reference to `Satisfies.four` in any proof term (docstrings may cite it).

---

### Phase 5: Minting guard, `modalApplyOneS4`, driver defs, `modalHintikkaSetS4` [COMPLETED]

- **Goal**: Build the loop-checking minting guard and assemble the complete S4 driver.
  This is the phase that makes S4 a real, executable tableau.
- **Tasks**:
  - [x] `blockingWorld phi0 b w : Option WorldIndex` — search `modalKnownWorlds b`
        (Branch.lean:89) for the least `w'` with `sameRelevantSet phi0 b w w' = true` and
        `w' != w`. Prove: result is in `modalKnownWorlds b`, and the returned world has an
        equal relevant set.
  - [x] `modalApplyOneS4 (phi0 : Proposition Atom) : RuleApply Atom` (Decision D1 —
        `phi0`-parameterized, partially applied). Wrap `modalApplyOneS4Rules`. At the two
        **minting** shapes (`isMintingShaped`: `(.neg, .box _)` and `(.pos, .diamond _)`,
        FmpMeasure.lean:786), consult `blockingWorld`:
        - blocked -> return `.persistent []`-equivalent / `.notApplicable` and
          `acc.addEdge w wBlock` (loop-back edge, **no** new world);
        - unblocked -> fall through to the underlying rule's fresh-world minting.
        Record in the docstring that this is the one place S4 departs structurally from K.
        *(deviation: altered -- the blocked case uses `RuleResult.linear []`, not
        `.persistent []` or `.notApplicable`. `modalStepBranchGen` discards the returned
        accessibility component entirely when the result is `.notApplicable` (its
        `.notApplicable => none` arm never references `newAcc`), which would silently drop
        the loop-back edge; and `.persistent []` never marks the source formula expanded,
        which would cause `b.findSome?` to re-select the same blocked formula on every
        subsequent fuel step. `.linear []` is what K's own fresh-world rules
        (`diamondPos`/`boxNeg`) use for exactly this one-shot-consumption shape, and
        correctly both threads `newAcc` through and marks the source formula expanded.
        Documented in `modalApplyOneS4`'s docstring.)*
  - [x] `modalStepBranchS4 phi0 := modalStepBranchGen (modalApplyOneS4 phi0)`,
        `modalExpandBranchesS4 phi0 := modalExpandBranchesGen (modalApplyOneS4 phi0)`,
        `modalTableauS4 phi := modalTableauGen (modalApplyOneS4 phi) phi`. Mirror
        TDriver.lean:62-86, where the three driver defs come first, before any lemma.
        **Do not** attempt `RuleApplicationSpec` (Correction 3).
  - [x] Guard spec lemmas: (a) every step either adds no world or adds exactly
        `modalNextWorld b`; (b) when blocked, `acc` gains exactly one edge to an existing
        known world and `b` gains no new label. These are Phase 8's inputs — state them to
        be consumed there.
  - [x] `modalHintikkaSetS4 phi0 b acc` — copy `modalHintikkaSet`'s four conjuncts
        (Saturation.lean:423-443) with `modalApplyOne` replaced by `modalApplyOneS4 phi0`
        in conjunct 2. Conjuncts 1/3/4 are unchanged and apply-agnostic. Docstring must
        record the D3 observation: conjuncts 3/4 are existential over successors, so a
        loop-back edge satisfies them natively — this is why blocking is compatible with
        the Hintikka characterization.
  - [x] CI gate; commit `LoopChecking.lean` only.
- **Timing**: 2.5 hours (~400 lines)
- **Depends on**: 1, 2
- **Files to modify**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean`.
- **Verification**: `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green; zero sorry;
  `modalTableauS4` typechecks and **evaluates** — sanity-check with `#eval modalTableauS4`
  on `box p -> p` (should close) and on `p` (should return an open branch). No
  `RuleApplicationSpec` instance exists for S4. *(deviation: altered -- the sanity checks
  were confirmed interactively via `lean_run_code`/`#eval` (T-schema `□p → p` closes,
  4-schema `□p → □□p` closes, bare atom `p` stays open) rather than embedded as permanent
  `#eval`/`#guard`/`native_decide` declarations in LoopChecking.lean: all three forms fail
  in this file's `module` compilation context -- `#guard`/`native_decide` fail at either
  `meta`-accessibility or native-symbol-lookup for `modalFuel`, and `decide` cannot
  kernel-reduce `modalFuel`'s triple-exponential closed form in reasonable time even for
  tiny formulas. No existing file in `Cslib/Logics/Modal/Tableau/` uses any of these forms,
  confirming this is a structural constraint, not a defect introduced here.)*

---

### Phase 6: S4 Hintikka bridges and the `ReflTransGen` path bridge [COMPLETED]

- **Goal**: Prove the S4 bridge lemmas and the box-positive bridge across `ReflTransGen`
  paths — the mathematical heart of the task.
- **Tasks**:
  - [x] Single-edge 4-rule bridge `hintikkaS4_box_pos_step`: `modalHintikkaSetS4 phi0 b acc`,
        `T(box psi)@w in b`, `acc.hasEdge w w'` -> `T(box psi)@w' in b`. Proof shape copies
        `hintikka_box_pos` (Completeness.lean:146-195): unfold, kill the propositional
        rules via the **public** `tryAllPropRules_pos`/`modalApplyOne_eq_prop_of_applicable`
        kit, land in `.persistent`, contradiction. Budget generously — this is the fiddliest
        proof in the phase. *(deviation: altered -- an orchestrator correction mid-run
        (from task 510's research) clarified that `hintikka_box_neg`/`hintikka_diamond_pos`
        are the ONLY pure structural projections; `hintikka_box_pos`/`hintikka_diamond_neg`
        unfold `modalApplyOne` concretely and do not transfer. This matches exactly what
        this phase's own text already anticipated ("fiddliest proof") -- no plan change
        needed, just confirmation. The actual proof required one more unfolding layer than
        K's original (`modalApplyOneS4` -> `modalApplyOneS4Rules` -> `modalApplyOneT` ->
        `modalApplyOne`), resolved via three chained `have` equations (`hshape`/`htR`/`hk`)
        and a generic two-case "append-then-filter" membership lemma (`hmem_merge`) that
        avoids needing to know the K/T layers' exact list contents.)*
  - [x] `hintikkaS4_box_pos_self` (T-rule endpoint): `T(box psi)@w in b` -> `T(psi)@w in b`.
        Follows from the `modalTBoxSelf` arm inherited via `modalApplyOneT`.
  - [x] `hintikkaS4_dia_neg_step` / `_self` — duals for `F(diamond psi)`.
  - [x] `hintikkaS4_box_neg` / `hintikkaS4_diamond_pos` — one-line projections
        (`hH.2.2.1` / `hH.2.2.2`), mirroring Completeness.lean:206/:228.
  - [x] **The crux**: `hintikkaS4_box_pos_reflTransGen`: `modalHintikkaSetS4 phi0 b acc`,
        `T(box psi)@w in b`, `Relation.ReflTransGen (fun a b => acc.hasEdge a b = true) w w'`
        -> `T(psi)@w' in b`. Prove by `Relation.ReflTransGen.head_induction_on`, carrying
        `T(box psi)` along each edge via `hintikkaS4_box_pos_step` and discharging the
        endpoint (including the reflexive `w = w'` base case) via `hintikkaS4_box_pos_self`.
        The induction carries `T(box psi)@·`, not `T(psi)@·` — that is why the 4-rule must
        propagate the box itself, and is the whole reason S4 needs the 4-rule.
  - [x] Dual `hintikkaS4_dia_neg_reflTransGen`.
  - [x] Confirm explicitly (in a docstring note) that loop-back cycles in `acc` are
        harmless: `ReflTransGen` is a closure, so a cycle adds no new reachable worlds
        beyond those already related; the induction is on the *path*, not the graph.
  - [x] CI gate; commit `LoopChecking.lean` only.
- **Timing**: 2.5 hours (~350 lines)
- **Depends on**: 3, 5
- **Files to modify**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean`.
- **Verification**: `lake build` green; zero sorry; every bridge lemma stated as a
  *hypothesis-parameterized* lemma over `modalHintikkaSetS4` (no dependency on the private
  chain — check by confirming LoopChecking.lean imports Completeness.lean non-publicly and
  uses only its public surface).

---

### Phase 7: `modalTruthLemmaS4` and open-branch countermodel [COMPLETED]

- **Goal**: The S4 truth lemma against `extractModelS4`, and the countermodel corollary.
  This is the last phase of guaranteed-landable work.
- **Tasks**:
  - [x] Read `modalTruthLemma` (Completeness.lean:474-625) as the template. Note it is
        unusable directly: it is pinned to `extractModel` (`r := acc.hasEdge`), whereas the
        S4 model's `r` is `ReflTransGen`. This is a new induction, not a reuse.
  - [x] `modalTruthLemmaS4 phi0 b acc (hH : modalHintikkaSetS4 phi0 b acc) ...`: induction
        on the formula. Reuse the **public, apply-agnostic** consistency kit verbatim —
        `openBranch_noTBot` (Completeness.lean:98) and `openBranch_noContradiction` (:113)
        depend only on `isModalClosed b = false`. Atom/bot cases reuse
        `extractModel_atom_sat_iff`/`extractModel_atomPos_sat`/`extractModel_bot_false`
        (note: these are stated for `extractModel`; check whether they transfer to
        `extractModelS4` by `rfl` — the valuation clause is preserved verbatim by
        `extractModelWith`, so they should; if not, prove the two-line analogues).
        *(deviation: altered -- the propositional cases (imp/and/or) also needed a new
        private lemma `modalApplyOneS4_eq_of_not_modal_shaped`, chaining the three existing
        "not-shaped" equation lemmas (`modalApplyOneS4_eq_of_not_boxNeg_diaPos`,
        `modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg`, `modalApplyOneT_eq_of_not_boxPos_diaNeg`)
        to show `modalApplyOneS4 φ₀ sf b acc = modalApplyOne sf b acc` for any non-box/
        non-diamond-shaped `sf`. This is what lets K's `modalApplyOne_imp_pos` etc. bridge
        lemmas be reused verbatim inside `modalHintikkaSetS4`'s conjunct 2. Also required
        adding `public import Cslib.Logics.Modal.Tableau.LoopChecking` and `public import
        Cslib.Logics.Modal.Tableau.FrameSoundness` to FrameCompleteness.lean, since the S4
        truth lemma needs `modalHintikkaSetS4`/the bridge lemmas (LoopChecking.lean) and
        `s4FC` (FrameSoundness.lean) in scope -- neither was previously imported here.)*
  - [x] Box-positive case: consume `hintikkaS4_box_pos_reflTransGen` (Phase 6) — the
        model's `r w w'` unfolds by `extractModelS4_r` to exactly the `ReflTransGen`
        hypothesis the bridge wants.
  - [x] Box-negative / diamond-positive cases: consume `hintikkaS4_box_neg` /
        `hintikkaS4_diamond_pos`, lifting the raw edge into the closure via
        `extractModelS4_hasEdge_imp_r` (Phase 3).
  - [x] `modalOpenBranchS4_countermodel` — mirror `modalOpenBranch_countermodel`
        (Completeness.lean:627): a `modalHintikkaSetS4` containing `F(phi0)@0` yields a
        reflexive-transitive countermodel, discharging the `s4FC` witness from
        `extractModelS4_refl` + `extractModelS4_trans` (Phase 3, both free).
  - [x] CI gate; commit `FrameCompleteness.lean` only.
- **Timing**: 3 hours (~400 lines)
- **Depends on**: 6
- **Files to modify**: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.
- **Verification**: `lake build` green; zero sorry; `modalOpenBranchS4_countermodel`
  typechecks with the `s4FC` witness discharged with no manual frame reasoning.
  **This is the landing milestone**: at the end of this phase the task's green,
  non-negotiable deliverables (4-rule, LoopChecking machinery, soundness, truth-lemma
  bridge) are all committed. Phases 8-9 are strictly additive.

---

### Phase 8: S4 termination bound `#worlds <= 2^|Sf|` — HIGH RISK [COMPLETED WITH EXCLUSIONS]

- **Goal**: Prove the equality-blocking loop invariant and the `2^|modalSubfmls phi0|`
  world bound. **This is the crux and the acknowledged blocker candidate.**
- **Tasks**:
  - [x] `modalWorldBoundS4 phi := 2 ^ (modalSubfmls phi).length` (Decision D2). Do **not**
        reuse `modalWorldBound` — it is `(2*complexity+1)^(complexity+1)`, a
        branching^depth *tree* bound, and S4's world graph is not a bounded-depth tree.
  - [x] `modalUniverseS4 phi` — mirror `modalUniverse` (FmpMeasure.lean:149) with
        `modalWorldBoundS4` swapped in. Prove `modalUniverseS4_length_le`, mirroring
        `modalUniverse_length_le` (:155).
  - [x] Reuse `modalWork`/`modalExpMeasure` **verbatim** — they take `U` as a parameter and
        are rule- and world-agnostic. Do not redefine them. *(no new references needed
        yet -- consumed by the world-bound/pigeonhole steps below, which are blocked.)*
  - [x] `S4LoopInv phi0 b e acc : Prop` — a **sibling** of `ModalPotentialInv`, not an
        extension of it (Correction 1). Fields: the six rule-independent ones
        (`bClosure` over `modalUniverseS4`, `eNodup`, `eClosure`, `accFresh`, `accKnown`,
        `outDegEq`), **omitting** `rankBound`/`rankEdge`, plus:
        - `worldSetsDistinct : forall w w' in modalKnownWorlds b, w != w' ->
          sameRelevantSet phi0 b w w' = false` — **the** loop invariant the guard enforces.
        Follow the `ModalLoopInv`-wraps-`ModalPotentialInv` precedent (CompletenessLoop:57)
        for structure/docstring style, but hold no `ModalPotentialInv` field.
  - [ ] **BLOCKED**: Prove `worldSetsDistinct` is preserved by `modalStepBranchS4`. See the
        "BLOCKER" note below -- the anticipated hard sub-goal is real and, on inspection,
        is not the only gap; the guard's fresh-minting side also does not establish the
        needed property. Not attempted as a sorry'd proof (prohibited); left unstated as a
        lemma so no false claim of a closed goal exists in the file.
  - [ ] **BLOCKED (depends on the above)**: Pigeonhole: `worldSetsDistinct` -> `(modalKnownWorlds
        b).length <= 2 ^ (modalSubfmls phi0).length`. Map each world to its relevant set as
        a `Finset (Proposition Atom) x Sign`-valued key, injective by `worldSetsDistinct`,
        into the powerset of `modalSubfmls phi0`. Mathlib candidates:
        `Finset.card_powerset`, `Finset.card_le_card_of_injOn`, `List.Nodup.length_le_card`.
        Not started -- its hypothesis (`worldSetsDistinct` as an actual loop invariant, not
        just a static definition) is unavailable.
  - [ ] **BLOCKED (depends on the above)**: `modalStepBranchS4_worldBound`:
        `modalMaxWorld b < modalWorldBoundS4 phi0` is a loop invariant. Not started.
  - [x] CI gate; commit `LoopChecking.lean` only (the mechanical portion: `modalWorldBoundS4`,
        `modalUniverseS4`, `modalUniverseS4_length_le`, `S4LoopInv`'s structure definition).
        **FmpMeasure.lean remains untouched.**
- **Timing**: 4 hours budgeted; ~1.5 hours spent (mechanical definitions + blocker analysis)
  before invoking the standing `[BLOCKED]` permission rather than forcing a proof attempt
  likely to require `sorry` or a silent scope reduction.
- **Depends on**: 5, 7. (Logical dependency is only on 5; **7 is a deliberate sequencing
  gate** so all green work is committed before this high-risk phase is attempted.)
- **Files to modify**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean`.
- **Verification**: `lake build` green; zero sorry/axiom for everything actually landed
  (`modalWorldBoundS4`/`modalUniverseS4`/`modalUniverseS4_length_le`/`S4LoopInv` all verified
  via `lean_verify`, axioms = `{propext, Quot.sound}` only). The `2^|Sf|` bound itself does
  **not** yet typecheck as a proven loop invariant -- only its target statement
  (`S4LoopInv.worldSetsDistinct`) is defined; the preservation lemma is the open item.

**BLOCKER** (Phase 8):
- **What failed**: The task-list item "Prove `worldSetsDistinct` is preserved by
  `modalStepBranchS4`" (the step immediately after `S4LoopInv`'s definition).
- **What was tried**: `modalWorldBoundS4`, `modalUniverseS4` (+ `modalUniverseS4_length_le`),
  and the `S4LoopInv` structure (with `worldSetsDistinct` as its final field) were all
  written and verified (zero sorry/axiom, full CI green, committed). Before attempting the
  preservation proof, the guard's actual behavior (`modalApplyOneS4`, Phase 5) and the
  minting/blocking case split were re-examined in detail to scope the proof, following the
  plan's explicit instruction to "assess this early."
- **Why it's stuck**: Two independent gaps, not one:
  1. **The plan's own anticipated gap is real**: a *persistent* rule firing (K's `boxPos`,
     T's self-propagation, or the 4-rule's `modalFourBoxProp`/`modalFourDiaNegProp`) adds a
     formula to an *already-known* world's relevant set. `worldSetsDistinct`, as stated, is
     a property of the *current* branch `b`; after such a persistent step changes `b`, two
     worlds that were distinct before the step can become identical after it (the new
     formula lands at one world but not, coincidentally, at the other -- or vice versa).
     Nothing in `modalApplyOneS4`'s persistent arms re-checks distinctness against the rest
     of `modalKnownWorlds b` after appending; the guard only fires at the two *minting*
     shapes (`F(□φ)@w`, `T(◇φ)@w`), never at persistent-rule steps.
  2. **A second, independent gap in the minting side**: `blockingWorld` checks whether the
     *source* world `w` (the one with the pending `F(□φ)@w`/`T(◇φ)@w` formula) already
     matches some *other existing* known world's relevant set -- it does **not** check
     whether the *freshly minted world's own prospective content* (the witness formula(s)
     the underlying K rule is about to place there, e.g. `T(φ)@w''` from `diamondPos`) would
     coincide with some existing world's relevant set. So even on the "unblocked" branch,
     nothing rules out the fresh world `w'' = modalNextWorld b` being born with a relevant
     set identical to some pre-existing world's, which would violate `worldSetsDistinct`
     the instant it is created, before any further step.
  Both gaps mean `worldSetsDistinct` is not, as currently designed, an actual per-step loop
  invariant of `modalStepBranchS4` -- it is a *design target* the guard was built to serve,
  but the guard's exact check (source-vs-others, at minting time only) does not establish
  it. Closing this requires either (a) redesigning the guard to check the *prospective new
  world's content* against all existing worlds before minting, and to re-run (or
  re-establish) the distinctness check after every persistent step, or (b) restating the
  invariant over a "saturation-stable" notion (e.g. only asserting distinctness once a
  world's relevant set has stopped changing) as the plan's own text anticipated as the
  fallback.
- **What is needed to unblock**: A follow-on task should (i) decide between guard redesign
  (re-check the *new* world's content, not just the source's, before minting; re-validate
  distinctness after persistent steps) vs. a saturation-stable invariant restatement, (ii)
  implement whichever is chosen -- this may require revisiting `modalApplyOneS4`'s
  definition itself (Phase 5, currently green and committed; any change there needs a fresh
  CI pass across Phases 5-7's consumers), and (iii) only then attempt the pigeonhole bound
  and `modalStepBranchS4_worldBound`.
- **Prohibited workarounds**: Did **not** use `sorry`, `def X := True`, or any vacuous
  placeholder for `worldSetsDistinct`'s preservation, the pigeonhole bound, or
  `modalStepBranchS4_worldBound`. These three items are simply absent from the file, not
  stated-and-unproved.

**Recommended follow-on task**: `s4-loop-checking-termination`, scoped to: redesigning the
minting guard and/or `S4LoopInv` per the two gaps above, `worldSetsDistinct` preservation,
the pigeonhole bound, and `modalStepBranchS4_worldBound`. Should re-read `modalApplyOneS4`
(`LoopChecking.lean`, Phase 5) and this blocker note as its starting point. Phases 1-7 remain
green and committed regardless of this phase's outcome.

- **[BLOCKED] fallback (standing permission — exercise it rather than degrade)**: If the
  invariant does not close within the run, mark this phase `[BLOCKED]`. Record: which
  field of `S4LoopInv` is open, the exact goal state at the failure point, what was tried,
  and whether the persistent-rule sub-goal above is the cause. Recommend a dedicated
  follow-on task **`s4-loop-checking-termination`** scoped to: `S4LoopInv` preservation +
  the pigeonhole bound + `modalStepBranchS4_worldBound`. Phases 1-7 remain green and
  committed. **Never** introduce `sorry`, `axiom`, or a vacuous `def X := True` (see
  `.claude/rules/cslib.md` — these are semantically equivalent to `sorry` and are
  prohibited). Do **not** force the bound.

---

### Phase 9: Fuel sufficiency, `s4Valid`, and `Decidable (s4Valid phi)` — HIGH RISK, 510-GATED [COMPLETED WITH EXCLUSIONS]

- **Goal**: Close the decidability endgame. **Doubly gated**: needs Phase 8's bound *and*
  task 510's generalized Hintikka chain.
- **Tasks**:
  - [ ] **Gate check first, before any writing**: confirm task 510 has landed **and** that
        its generalized loop lemma concludes in `modalHintikkaSetGen apply bR aR`, not
        `modalHintikkaSet bR aR`. If either fails, stop and mark `[BLOCKED]` — do not
        copy-paste CompletenessLoop.lean's ~700-line private chain.
  - [ ] `modalFuelS4 phi` — closed form over `modalComplexity phi` mirroring `modalFuel`
        (Saturation.lean:94), sized for `modalWorldBoundS4`.
  - [ ] `modalExpMeasureS4_entry_le_fuel` — mirror `modalExpMeasure_entry_le_fuel`
        (FmpMeasure.lean:208) over `modalUniverseS4`.
  - [ ] `modalExpandBranchesS4_hintikka` — instantiate task 510's generalized loop lemma at
        `apply := modalApplyOneS4 phi0`, with `S4LoopInv` in place of `ModalLoopInv`.
        **This is the single named lemma boundary at which to block if 510 is unavailable.**
  - [ ] `modalTableauS4_sound` — fuel induction over `branchSatisfiableIn s4FC`, consuming
        Phase 4's rule-level soundness arms.
  - [ ] `modalTableauS4_complete` — chain `modalExpandBranchesS4_hintikka` into Phase 7's
        `modalOpenBranchS4_countermodel`.
  - [ ] `modalTableauS4_decides : modalTableauS4 phi = .closed <-> s4Valid phi`, then
        `instDecidableS4Valid : Decidable (s4Valid phi)`. These three are pure plumbing and
        transfer verbatim from CompletenessLoop.lean:1290/1334/1346. Note the K precedent
        needs **no** `Fintype Atom` — the tableau computation *is* the decision procedure.
  - [ ] Confirm `s4Valid` corresponds to `Cube.S4` (Cube.lean:81) in the docstring.
  - [ ] CI gate; commit `FrameCompleteness.lean` only.
- **Timing**: 2 hours (~300 lines)
- **Depends on**: 4, 7, 8, **and task 510**.
- **Files to modify**: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.
- **Verification**: `lake build` green; zero sorry/axiom; `Decidable (s4Valid phi)`
  typechecks; `lean_verify` on `instDecidableS4Valid` shows no `sorryAx`.
- **[BLOCKED] fallback**: If Phase 8 blocked, this phase is unreachable — mark `[BLOCKED]`
  with "depends on Phase 8's open bound". If Phase 8 closed but 510 has not landed (or
  concluded in the wrong predicate), mark `[BLOCKED]` at
  `modalExpandBranchesS4_hintikka`, record the exact 510 requirement, and add it to the
  recommended follow-on task. Phases 1-8 remain green.

**BLOCKED (this run)**: Phase 8 is `[BLOCKED]` (see its BLOCKER note), so per this phase's
own fallback text, Phase 9 is unreachable this run -- not attempted, not sorry'd. No writing
was done in `FrameCompleteness.lean` for Phase 9. Recorded for the follow-on task's benefit:
task 510 (`generalize_completeness_loop_hintikka_chain_over_spec`) **completed all 9 phases
during this run** (commit `817a5b45`, "task 510: complete generic Hintikka/saturation chain;
unblock task 503 Phase 5"). The follow-on task `s4-loop-checking-termination` should verify,
once Phase 8's bound closes, whether task 510's generalized loop lemma concludes in
`modalHintikkaSetGen apply bR aR` (the requirement this plan's gate section raised on 510
before it planned) before attempting `modalExpandBranchesS4_hintikka` -- this was not
verified in this run since Phase 8 blocked first.

---

## Testing & Validation

- [ ] Every phase: full CSLib CI (`lake build`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake lint`, `lake test`, `lake exe mk_all --module`,
      `lake shake --add-public --keep-implied --keep-prefix`).
- [ ] Zero `sorry`, zero `axiom`, zero vacuous definitions at every phase boundary
      (`lean_verify` per new top-level declaration).
- [ ] `modalTableauS4` evaluates: `box p -> p` closes (T component); `p` returns an open
      branch; `box p -> box box p` closes (4 component). Add these as `#eval`/`example`
      sanity checks in Phase 5, and consider promoting to `CslibTests/` if a modal tableau
      test file exists.
- [ ] No file outside each phase's territory row is modified.
- [ ] `FmpMeasure.lean` diff is empty across the whole task.
- [ ] No `RuleApplicationSpec` instance for any S4 `apply`.
- [ ] `git log --oneline -- Cslib/Logics/Modal/Tableau/` shows one commit per completed
      phase.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (new) — Phases 2, 5, 6, 8.
- `Cslib/Logics/Modal/Tableau/FrameRules.lean` (4-rule) — Phase 1.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (`extractModelS4`, truth lemma,
  decidability) — Phases 3, 7, 9.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (`s4FC`, `s4Valid`, 4-rule soundness) —
  Phase 4.
- `Cslib.lean` (barrel entry for `LoopChecking`) — Phase 2.
- `specs/506_.../summaries/01_s4-loopchecking-termination-decidability-summary.md`.
- If Phase 8 or 9 blocks: a recommended follow-on task
  **`s4-loop-checking-termination`**, with the documented open goal state.

## Rollback/Contingency

- Each phase is a single scoped commit; revert with `git revert <sha>` for that phase
  alone. Phases 1-7 are independently valuable and should never be reverted for a Phase 8
  failure.
- `LoopChecking.lean` is a new file: if the whole S4 effort is abandoned, delete it, revert
  the `Cslib.lean` barrel entry, and revert the FrameRules/FrameSoundness/FrameCompleteness
  appends. No existing K or T declaration is modified by this plan, so rollback cannot
  regress tasks 503/507.
- If a phase times out mid-run, mark it `[PARTIAL]`, commit whatever is green (the CI gate
  guarantees a green commit), and record the resume point in the phase's Tasks list.

---

## Reconciliation Note (Phases 8-9)

Phases 8 and 9 stood at `[BLOCKED]` while their objectives were, in fact, delivered through a
different route. Both are now marked `[COMPLETED WITH EXCLUSIONS]`: the goals are met, but the
specific implementation line planned here was excluded rather than executed.

**Phase 8's blocker analysis was correct and is vindicated.** The open item was proving
`worldSetsDistinct` preserved by `modalStepBranchS4`, and this plan declined to force it. That
judgement held up: `S4/BirthKey.lean:77` records that the birth-key formulation is "a genuine
loop invariant where the old `worldSetsDistinct` (over the live branch) was not." The planned
proof was not merely hard — its target was not an invariant.

**Where the objectives actually landed**, all sorry-free:

| Planned deliverable | Delivered as |
|---|---|
| `S4LoopInv` (was to live in `LoopChecking.lean`) | `S4/Invariant.lean:85`, restated over birth keys |
| `worldSetsDistinct` preservation | superseded by the birth-key invariant (`S4/BirthKey.lean`) |
| Pigeonhole `#worlds <= 2^\|Sf\|` | `S4/Universe.lean:119` |
| `modalStepBranchS4_worldBound` | `S4/InvariantAcc.lean:1330` |
| Fuel sufficiency | `FrameCompleteness.lean:8830` ("outer fuel induction") |
| `s4Valid_decides`, `instDecidableS4Valid` | `FrameCompleteness.lean:9089`, `:8281` |

The invariant material was split four ways across `S4/InvariantKeys.lean`,
`S4/InvariantAcc.lean`, `S4/Invariant.lean`, and `S4/HintikkaInvariant.lean` because a single
file would have run to roughly 4,445 lines. `LoopChecking.lean:74-79` documents that split.

**Exclusion recorded**: the unordered keyed driver this plan targeted was not the one the
decision procedure was built on. `LoopChecking.lean:152` notes that soundness is false for the
unordered keyed driver, so `instDecidableS4Valid` points at the *ordered* successor instead.
Retiring the surviving unordered stack is tracked separately and is not in scope here.
