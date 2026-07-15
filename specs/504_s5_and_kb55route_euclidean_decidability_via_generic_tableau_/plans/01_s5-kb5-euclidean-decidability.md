# Implementation Plan: Task #504 — S5 universal-cluster simplification + 5/KB5 Euclidean coverage via the generic tableau driver

- **Task**: 504 - Deliver S5 universal-cluster simplification (no loop-checking) and 5/Euclidean coverage via the KB5/S5 equivalence route
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: 513 (generic soundness chain, COMPLETED), 505 (B system end-to-end via generic driver, COMPLETED), 510 (generic completeness/Hintikka, COMPLETED), 507 (generic termination, COMPLETED), 503 (generic driver + T, COMPLETED)
- **Research Inputs**: reports/01_frame-specific-tableau-extensions.md; reports/02_spawn-analysis.md; reports/03_parent-phase-plan-reference.md
- **Artifacts**: plans/01_s5-kb5-euclidean-decidability.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Deliver the S5 modal tableau end-to-end — soundness, completeness, and `Decidable (s5Valid φ)`
against `Cube.S5` — plus 5/KB5 (Euclidean) coverage via the S5/equivalence route, as a new
instantiation of the already-landed generic tableau driver. The S5 rule is the Bimodal-style
"propagate box to ALL branch worlds" universal rule: because it only ever adds formulas at
existing branch worlds (drawn from the finite `modalUniverse φ0` catalog) and never mints a world
itself, it discharges the generic `RuleApplicationSpec` interface with the same shape as B's
backward rule and needs **no loop-checking** (unlike S4/task 511). The definition of done is a
green (`lake build` passing), zero-`sorry` / zero-`axiom` (standard trio only) result whose
extracted countermodel is `Relation.EqvGen`-closed (hence `IsEquiv`, hence `RightEuclidean`) "for
free" off Mathlib. The plan mirrors task 505's B build (`modalApplyOneB`/`modalApplyOneB_spec`/
`extractModelB`/`modalTruthLemmaB`/`hAgreeB`/`modalTableauB_sound`/`bValid_decides`/
`instDecidableBValid`) declaration-for-declaration, reconciling against the ACTUAL current generic
interface rather than the pre-513/505 report.

### Research Integration

The report (`reports/01`) and spawn analysis (`reports/02`) are adopted as follows, corrected
against the current code (the reports predate 513/505's generic soundness + B work):

- **Strategy B (closure-at-extraction)** — extract with a *closed* relation
  (`Relation.EqvGen (fun w w' => acc.hasEdge w w' = true)`); the frame instance (`IsEquiv` via
  `Relation.EqvGen.instIsEquiv`, plus its projections `Std.Refl`/`Std.Symm`/`IsTrans`) is free.
  Directly mirrors `extractModelB` via `Relation.SymmGen` (`FrameCompleteness.lean:425`).
- **Universal-cluster / no loop-checking** — the S5 rule adds formulas only at existing worlds, so
  world creation stays confined to the unmodified K `diamondPos`/`boxNeg` arms and each diamond
  mints at most once per formula. This is exactly the "downstream reuse" contract the generic
  driver's module docstring records for task 504 (`GenericDriver.lean:118-122`).
- **The three generic lifts already exist** — termination (`RuleApplicationSpec` +
  `modalStepBranchGen_*` wrappers, `GenericDriver.lean`), completeness/Hintikka
  (`modalExpandBranchesGen_hintikka`, `CompletenessLoop.lean`), and — the correction to the
  reports — **soundness** (`modalStepBranchGen_preserves_satIn` and
  `modalExpandBranchesGen_closed_unsatIn`, `FrameSoundness.lean:192,728`, task 513). S5 supplies
  its own rule + spec witness + `hAgree`/`boxPos`/`diaNeg` soundness triple and instantiates; it
  re-ports no monolith.
- **5/KB5 via S5** — every equivalence relation is `Relation.RightEuclidean`; expose it for
  `extractModelS5` and state 5/KB5 validity + completeness via `Satisfies.five` (`Basic.lean:376`)
  and `Cslib/Foundations/Relation/Euclidean.lean`. Genuine pure-K5 (Euclidean without full
  equivalence, no Mathlib closure operator) is documented in-file as OUT OF SCOPE, per the parent
  plan's non-goals (`reports/03`).

### Prior Plan Reference

The parent plan `reports/03_parent-phase-plan-reference.md` (task 300, [PARTIAL]) is reference
only. Its Phase 3 (S5) and Phase 7 (5/KB5) map onto this task, but its architecture predates the
generic driver: it assumed S5 would rebuild a K-scale driver/termination argument inline (the
exact blocker recorded in `reports/02`). That blocker is now resolved — 503/507/510/513 built the
generic driver, termination, completeness, and soundness lifts, and 505 validated the full
instantiation pattern for B. This plan therefore does NOT copy the parent's phase structure; it
follows the 505/B shape. Effort calibration: the spawn analysis budgeted this task at 5-7 hours;
mirroring B's realized scope (~1,200 driver lines plus completeness/soundness content) the risk-
weighted estimate here is ~10 hours across 7 small phases.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context and no ROADMAP.md consulted (read-only if it
had been). Task 504 continues the Modal Logic tableau line (siblings: 505/B done, 511/S4 pending).

## Goals & Non-Goals

**Goals**:
- A new file `Cslib/Logics/Modal/Tableau/S5Simplification.lean` implementing the universal
  "propagate box to ALL branch worlds" rule `modalApplyOneS5`, its `RuleApplicationSpec` witness
  `modalApplyOneS5_spec`, and the generic-driver instantiation
  `modalStepBranchS5`/`modalExpandBranchesS5`/`modalTableauS5`.
- Countermodel extraction `extractModelS5` via `Relation.EqvGen`, with `IsEquiv` (and its
  `Std.Refl`/`Std.Symm`/`IsTrans` projections) obtained free.
- The S5 truth lemma `modalTruthLemmaS5` over the equivalence relation, `modalTableauS5_complete`.
- The S5 soundness triple (`hAgreeS5`, `modalApplyOneS5_boxPos_soundIn`,
  `modalApplyOneS5_diaNeg_soundIn`) and `modalTableauS5_sound`, instantiating 513's generic
  soundness lemmas at the equivalence frame condition.
- `s5Valid` (against `Cube.S5`), `s5Valid_decides`, and `instDecidableS5Valid`.
- Euclidean exposure: `extractModelS5` satisfies `Relation.RightEuclidean`; state 5/KB5 validity
  + completeness via `Satisfies.five` and the `Euclidean.lean` API
  (`RightEuclidean.symm`, `refl_serial`).
- Every delivered phase ends green: `lake build`, zero `sorry`, zero new `axiom` (only the
  standard `propext`/`Classical.choice`/`Quot.sound` trio), and full CSLib CI clean.

**Non-Goals**:
- Genuine **pure-K5 / pure-5** completeness (Euclidean without full equivalence): no Mathlib
  closure operator exists; documented in-file as out of scope and deferred to a dedicated
  `pure-k5-euclidean-closure` task. Never introduce a custom `EuclGen` here.
- Any loop-checking / subset-blocking machinery (that is S4/task 511's territory).
- Re-porting or refactoring the K or generic driver / termination / completeness / soundness
  machinery beyond instantiating it for S5.
- Any `sorry`, `axiom`, or vacuous `def X := True` / `theorem X := trivial` placeholder.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universal-rule soundness needs an "all branch worlds are one equivalence cluster" invariant (the universal rule propagates to ALL worlds, not just edge successors) | H | M | The recorded-edge → `m.r` contract in `branchSatisfiableIn` plus `IsEquiv m.r` (refl+symm+trans) lifts edge-connectivity to `m.r`-equivalence; every branch world is connected to root `0`. Thread this connectivity witness through `modalApplyOneS5_boxPos_soundIn`, mirroring how B threads its predecessor-edge reasoning (`branchSatisfiableIn_symmFC_boxPos_pred_mem`). Flag early; prove the connectivity lemma before the soundness triple. |
| `RuleApplicationSpec` (11 fields) discharge is the heaviest single unit | M | M | Isolate it as its own phase (Phase 2). Reuse the agreement lemma `modalApplyOneS5_eq_of_not_boxPos_diaNeg` so `freshLocal`/`boxNegWitness`/`diaPosWitness`/`branchingLength`/`localShapeInvariance` reduce to `modalApplyOne` facts (as in `modalApplyOneB_spec`, `BDriver.lean:821`); only `boxPosNotExpanding`/`diaNegNotExpanding` (persistent shape) and `outputsSubsetUniverse` (catalog membership of `T(ψ)@w'` outputs) carry S5-specific content. |
| `outputsSubsetUniverse`: universal-propagation outputs `T(ψ)@w'` must lie in `modalUniverse φ0` | M | M | `ψ` is an immediate subformula of a box already on the branch, hence in the subformula catalog; only the *label* `w'` ranges over known worlds. Confirm `modalUniverse` is label-agnostic (as it is for K/T/B) so no universe enlargement is needed; if it is not, mirror B's handling exactly. |
| No unconditional "IsEquiv → RightEuclidean" instance (and no `RightEuclidean.symm` lemma) | L | M | Construct `RightEuclidean` from `IsEquiv`'s `Std.Symm`+`IsTrans` components via `Relation.symm_rightEuclidean_iff_trans` (`Euclidean.lean:236`), or directly (`r a b → r a c ⊢ r b a` by symm, then `r b c` by trans). `RightEuclidean` class is in `Defs.lean:49`. Small, self-contained. |
| S5 truth lemma needs the `accSourcesKnown` side condition (like B) | L | L | Reuse the generic-over-`apply` machinery already in `BDriver.lean` (`accSourcesKnown`, `accSourcesKnown_empty`, `modalExpandBranchesGen_openBranch_accSourcesKnown`) instantiated at `(modalApplyOneS5, modalApplyOneS5_spec)`; no new machinery. Threaded in Phase 4. |
| Shared-file contention: `FrameSoundness.lean` and `FrameCompleteness.lean` are touched by several phases | M | M | Keep S5 rule/spec/driver in the new `S5Simplification.lean`; add `equivFC`/`s5Valid` to `FrameSoundness.lean` and `extractModelS5`/truth-lemma/completeness/soundness-triple/decidability to `FrameCompleteness.lean` in the B pattern. Execute shared-file phases sequentially (or under H7 territory contracts if parallelized). |
| Report/parent-plan references are stale (pre-513/505) | M | H | Implementer MUST reconcile every referenced name against the current files before writing; this plan's names were verified against the working tree on the planning date. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2 | 1 |
| 3 | 4, 5 | 2, 3 (Phase 4); 1, 2 (Phase 5) |
| 4 | 6 | 4, 5 |
| 5 | 7 | 3, 6 |

Phases within the same wave are logically independent, but Phases 4/5/6/7 all edit
`FrameSoundness.lean`/`FrameCompleteness.lean`; run them sequentially unless H7 territory
contracts are in force. Each phase is a single agent run ending at a green, zero-sorry milestone
with a task-scoped commit.

**File-layout note (reconcile with B):** task 505 split B's rule into `FrameRules.lean`
(`modalApplyOneB`, `modalBBoxBack`, agreement lemma) and its driver into a dedicated
`BDriver.lean` (`modalStepBranchB`/`…`/`modalApplyOneB_spec`/`modalExpandBranchesB_hintikka`). This
task's mandate is a single new file `S5Simplification.lean`, so consolidate the S5 rule **and**
driver instantiation there (S5Simplification.lean plays the combined `FrameRules`-arm +
`BDriver.lean` role). If the implementer finds a clean split preferable, an `S5Driver.lean`
mirroring `BDriver.lean` is acceptable — but the task explicitly names `S5Simplification.lean`, so
prefer consolidation. `extractModel*`, truth-lemma, soundness triple, and decidability live in
`FrameCompleteness.lean`; the frame condition + `s5Valid` live in `FrameSoundness.lean` — exactly
as for B.

---

### Phase 1: S5 universal rule + characterization + driver instantiation [COMPLETED]

- **Goal:** Define the universal S5 rule and instantiate the generic driver on it (no spec/proof
  obligations yet — the driver functions are computable and spec-free to *define*).
- **Tasks:**
  - [ ] Create `Cslib/Logics/Modal/Tableau/S5Simplification.lean` with `import Cslib.Init` and
    `public import Cslib.Logics.Modal.Tableau.GenericDriver` (plus `FrameRules`/`Saturation` as B
    imports them); open `Cslib.Logic.Modal.Tableau`.
  - [ ] Define the propagation helpers (mirror `modalTBoxSelf`/`modalBBoxBack` naming):
    `modalS5BoxAll b φ w` = the `T(φ)@w'` signed formulas for every `w' ∈ modalKnownWorlds b` not
    already on `b`; dually `modalS5DiaNegAll b φ w` for `F(◇φ)` → `F(φ)@w'`.
  - [ ] Define `modalApplyOneS5 : RuleApply Atom`: on `T(.box ψ)@w` return
    `.persistent (modalS5BoxAll …)`, on `F(.diamond ψ)@w` return `.persistent (modalS5DiaNegAll …)`
    (or `.notApplicable` when the propagation set is empty), else fall through to `modalApplyOne`.
  - [ ] Prove the agreement lemma `modalApplyOneS5_eq_of_not_boxPos_diaNeg` (outside the box-pos /
    diamond-neg shapes `modalApplyOneS5 = modalApplyOne`), mirroring
    `modalApplyOneT_eq_of_not_boxPos_diaNeg` / the B analogue.
  - [ ] Prove the shape-characterization lemmas mirroring `modalApplyOneB_boxPos_fst/_snd` and
    `_diamondNeg_fst/_snd` (`BDriver.lean:134-189`): the `.fst` payload and `.snd = acc`
    (persistent → no edge change) for the two S5 shapes.
  - [ ] Instantiate the driver: `modalStepBranchS5`/`modalExpandBranchesS5`/`modalTableauS5` as
    `modalStepBranchGen modalApplyOneS5` / … / `modalTableauGen modalApplyOneS5` (mirror
    `BDriver.lean:76,85,94`), plus the `_eq` unfold lemmas `modalStepBranchS5_eq` /
    `modalExpandBranchesS5_eq` / `modalTableauS5_eq` (mirror `BDriver.lean:838,843,850`).
- **Timing:** 1.5 hours
- **Depends on:** none
- **Files to modify:** `S5Simplification.lean` (new); `Cslib.lean` barrel via `lake exe mk_all --module`.
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.S5Simplification` green; zero sorry/axiom;
  full CI (checkInitImports, lint, lint-style, test, mk_all, shake) clean.

---

### Phase 2: `modalApplyOneS5_spec : RuleApplicationSpec modalApplyOneS5` [BLOCKED]

- **Goal:** Discharge all eleven `RuleApplicationSpec` fields for the universal rule, unlocking
  the generic termination + Hintikka lifts.
- **Tasks:**
  - [ ] Prove `modalApplyOneS5_spec` as a `where`-block (mirror `modalApplyOneB_spec`,
    `BDriver.lean:821`). Discharge via the agreement lemma wherever the rule coincides with
    `modalApplyOne`:
    - `freshLocal`, `boxNegWitness`, `diaPosWitness`, `branchingLength`: the S5 rule is
      `.persistent`/`.notApplicable` on its two shapes (no world minting, `.snd = acc`) and equals
      `modalApplyOne` elsewhere → reuse the K facts (`modalApplyOne_fresh_local`,
      `modalApplyOne_boxNeg_witness`, `modalApplyOne_diamondPos_witness`,
      `modalApplyOne_branching_length`).
    - `boxPosNotExpanding` / `diaNegNotExpanding` (F9/F10): direct — the S5 result on those shapes
      is `.notApplicable` or `.persistent` (use the existentially-quantified payload).
    - `localShapeInvariance` (F8): on non-box/non-diamond shapes the rule equals `modalApplyOne`,
      whose result is branch-independent (`modalApplyOne_fst_eq_of_not_box`).
    - `outputsSubsetUniverse` (S5-specific): the propagated `T(ψ)@w'` / `F(ψ)@w'` outputs have
      `ψ` an immediate subformula of the triggering box/diamond (already in `modalUniverse φ0`) and
      label `w'` a known world; confirm `modalUniverse` membership is label-agnostic and reuse the
      subformula-closure facts (mirror B's `outputsSubsetUniverse` discharge).
    - `persistentFresh`, `rankStep`, `outDegStep`, `knownWorldsStep`: reuse the K per-call lemmas
      via agreement for the fall-through shapes; for the two S5 shapes the result is persistent
      with fresh, catalog-bound, existing-world-labelled formulas (mirror B's per-call discharges).
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify:** `S5Simplification.lean`.
- **Verification:** `lake build` green; zero sorry/axiom; `modalApplyOneS5_spec` type-checks; CI clean.
- **[BLOCKED] fallback:** If `outputsSubsetUniverse` reveals a genuine universe-enlargement need
  (unlike B), mark [BLOCKED] with the exact open field and goal state and recommend a scoped
  universe-generalization follow-up. Never `sorry`.

**BLOCKER** (Phase 2):
- **What failed**: The `rankStep` field of `RuleApplicationSpec` (`GenericDriver.lean`) cannot
  be discharged for `modalApplyOneS5` as designed (universal propagation to
  `modalKnownWorlds b`, unrestricted by any edge relation to the trigger world). This is not an
  unproved goal -- it is a **mathematically false** statement, proven false by a fully
  mechanized, sorry-free counterexample landed in `S5Simplification.lean`
  (`modalApplyOneS5_rankStep_not_dischargeable`, section "Phase 2 Obstruction").
- **What was tried**: (1) Implemented `modalApplyOneS5`/`modalS5BoxAll`/`modalS5DiaNegAll`
  exactly mirroring B's design, substituting "every known world" for B's "recorded-edge
  predecessors" (Phase 1, COMPLETED, green). (2) Began the eleven-field `RuleApplicationSpec`
  discharge per this phase's task list. (3) Before writing the other ten fields, hand-analyzed
  `rankStep` specifically (it is the one field whose B-mirrored proof genuinely depends on an
  *edge* relating the trigger world's rank to the target world's rank, via `hedge`) and found
  the analogous relation does not exist for S5's *unrestricted* known-world target set. (4)
  Constructed and mechanically verified (via `#eval`, `rfl`, `decide`, and finally a full `theorem`
  in the file) a concrete counterexample: `Atom := Nat`, `φtest := ◇◇(atom 0)`
  (`modalDepth φtest = 2`), branch `[T(□φtest)@0, T(atom 0)@3]`, accessibility chain `0→1→2→3`,
  tight rank map `rank w := 3 - w`. `rankStep`'s two hypotheses (`hbound`, `hedge`) hold at this
  instantiation (mechanically confirmed), yet `modalApplyOneS5` emits `T(φtest)@3` (confirmed by
  `rfl`) while `modalDepth φtest = 2 > rank 3 = 0`, and any valid `rank'` is forced (by the
  field's own "agrees off the fresh point" clause) to have `rank' 3 = rank 3 = 0`. No valid
  `rank'` witness can exist.
- **Why it's stuck**: `RuleApplicationSpec.rankStep` is universally quantified over *any*
  `rank : WorldIndex → Nat` satisfying the depth-bound (`hbound`) and edge-decrement (`hedge`)
  invariants -- the exact bookkeeping the K-style FMP potential/termination argument threads
  through the branch. T's self-propagation (target = trigger's own world) and B's backward
  propagation (target = a *recorded-edge* predecessor, so `hedge` directly relates the two
  worlds' ranks) both stay within worlds whose rank is provably tied to the trigger's rank. S5's
  universal rule targets `modalKnownWorlds b` unconditionally, including worlds with **no**
  recorded-edge path to the trigger world's rank budget (e.g. deeper subtrees created by
  unrelated diamond expansions) -- so `modalDepth φ ≤ rank v` has no derivation in general. This
  is the *same* underlying obstruction the codebase already documents for S4's transitive 4-rule
  (`GenericDriver.lean`'s module docstring: "S4 is explicitly NOT an instance... needs a
  structurally different termination argument") -- S5's *unrestricted* universal propagation
  hits it too, even though S5 never mints new worlds (the two problems are independent: bounded
  *world creation* vs. bounded *rank/potential bookkeeping* per emitted formula).
- **What is needed**: Either (a) a fundamentally different S5 rule design that restricts the
  target-world set to preserve rank-compatibility while still achieving the full equivalence
  closure needed for Hintikka completeness (not obviously possible -- `EqvGen` genuinely needs
  transitive reach across the whole known-world tree, and forward-direction transitive
  propagation is exactly S4's blocked case), or (b) a new, S5-specific termination argument that
  does not route through `RuleApplicationSpec`'s rank-potential machinery at all (comparable in
  scope to S4/task 506's loop-checking problem). Recommend spawning a dedicated
  `s5-universal-rule-termination` follow-up task to investigate option (a)/(b), analogous to how
  task 506 (S4) was scoped out of this generic-driver line. Given `S5` genuinely needs no world
  creation beyond K, a bespoke bound on world count (not needing `rankStep`'s rank-potential
  argument at all, only the world-bound half) may be a smaller, separately-tractable deliverable
  than S4's full loop-checking machinery -- but that decomposition itself needs research, since
  the *current* `RuleApplicationSpec` bundles world-bound-preservation and rank-potential
  together via `rankStep`/`outDegStep`/`knownWorldsStep` jointly.
- **Prohibited workarounds**: Do NOT use `sorry`, `def X := True`, or any vacuous placeholder.
  (None introduced; the mechanized counterexample theorem is a genuine, sorry-free,
  axiom-clean proof of non-dischargeability, landed as permanent documentation.)
- **Downstream impact**: Phases 4 (completeness, needs `modalApplyOneS5_spec` for the generic
  Hintikka lift), 5 (soundness, needs `modalApplyOneS5_spec.freshLocal`), and 6 (`s5Valid`
  decidability, needs 4+5) are all BLOCKED as a direct consequence -- `modalApplyOneS5_spec :
  RuleApplicationSpec modalApplyOneS5` cannot be constructed (Lean requires every field of the
  structure). Phase 3 (`extractModelS5`, pure closure-model construction, independent of the
  rule) and the `RightEuclidean` half of Phase 7 (needs only Phase 3) are unaffected and were
  completed regardless.

---

### Phase 3: Countermodel extraction `extractModelS5` via `Relation.EqvGen` [NOT STARTED]

- **Goal:** Extract the S5 countermodel and read all frame conditions off the Mathlib closure for
  free. Independent of the rule (pure closure-model construction).
- **Tasks:**
  - [ ] In `FrameCompleteness.lean`, define `extractModelS5 b acc` with
    `r := Relation.EqvGen (fun w w' => acc.hasEdge w w' = true)` and the same valuation `v` as
    `extractModelB` (mirror `extractModelB`, `FrameCompleteness.lean:425`).
  - [ ] `extractModelS5_r` (`.r = Relation.EqvGen …`, by `rfl`) — mirror `extractModelB_r:432`.
  - [ ] `extractModelS5_equiv : IsEquiv _ (extractModelS5 b acc).r` via
    `Relation.EqvGen.instIsEquiv`; derive the projections needed downstream
    (`Std.Refl`/`Std.Symm`/`IsTrans`) — mirror `extractModelB_symm:441`.
  - [ ] `extractModelS5_hasEdge_imp_r` (raw edges survive into the equivalence closure via
    `Relation.EqvGen.rel`/`.refl`) — mirror `extractModelB_hasEdge_imp_r:452`.
- **Timing:** 0.75 hours
- **Depends on:** none
- **Files to modify:** `FrameCompleteness.lean`.
- **Verification:** `lake build` green; zero sorry/axiom; the `IsEquiv` instance type-checks; CI clean.

---

### Phase 4: S5 completeness — Hintikka instantiation + truth lemma [NOT STARTED]

- **Goal:** Land `modalTruthLemmaS5` over the equivalence relation and `modalTableauS5_complete`.
- **Tasks:**
  - [ ] `modalExpandBranchesS5_hintikka` as a one-line application of the generic
    `modalExpandBranchesGen_hintikka` at `(modalApplyOneS5, modalApplyOneS5_spec)` — mirror
    `modalExpandBranchesB_hintikka` (`BDriver.lean:858`).
  - [ ] **Reuse the generic `accSourcesKnown` side-condition machinery** (defined generically over
    `apply` in `BDriver.lean`: `accSourcesKnown:886`, `accSourcesKnown_empty:892`,
    `modalStepBranchGen_preserves_accSourcesKnown:977`,
    `modalExpandBranchesGen_openBranch_accSourcesKnown:1060`). S5's truth lemma, like B's, needs
    this invariant because the extracted `EqvGen` relation is generated from recorded edges whose
    sources must be known branch worlds. Instantiate the generic `_openBranch_accSourcesKnown` at
    `(modalApplyOneS5, modalApplyOneS5_spec)` to obtain `accSourcesKnown bR aR` on the open branch —
    no new machinery needed.
  - [ ] Prove the S5-specific bridge lemmas `hintikkaS5_box_pos` / `hintikkaS5_diamond_neg` (mirror
    `hintikkaB_box_pos:1211` / `hintikkaB_diamond_neg:1281`): universal saturation means
    `T(□ψ)@w ∈ b` ⇒ `T(ψ)@w' ∈ b` for **every** known world `w'`. This is structurally *simpler*
    than B's predecessor-edge tracing: since `Relation.EqvGen` only relates worlds connected through
    recorded edges — all of which are known branch worlds (via `accSourcesKnown`) — any
    `EqvGen`-related `w'` already carries `T(ψ)@w'` by universal propagation. Reuse the generic
    *free* projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` (`Completeness.lean`)
    for the other two shapes.
  - [ ] `modalTruthLemmaS5 (b) (acc) (hSrc : accSourcesKnown b acc) (hH : modalHintikkaSetGen
    modalApplyOneS5 b acc)` (strong induction on `modalComplexity`, box case over the `EqvGen`
    relation) — mirror `modalTruthLemmaB` (`FrameCompleteness.lean:1368`), which takes the same
    `hSrc`/`hH` pair.
  - [ ] `modalOpenBranchS5_countermodel` (`F(φ)@0 ∈ b ⇒ ¬ Satisfies (extractModelS5 …) 0 φ`) and
    `modalTableauS5_complete` — mirror `modalOpenBranchB_countermodel:1535` /
    `modalTableauB_complete:1553`, discharging the `IsEquiv` frame witness via
    `extractModelS5_equiv` and the `accSourcesKnown` side condition via
    `modalExpandBranchesGen_openBranch_accSourcesKnown` + `accSourcesKnown_empty`.
- **Timing:** 2 hours
- **Depends on:** 2, 3
- **Files to modify:** `FrameCompleteness.lean` (and any S5 Hintikka helper placed in
  `S5Simplification.lean`).
- **Verification:** `lake build` green; zero sorry/axiom; `modalTableauS5_complete` type-checks; CI clean.

---

### Phase 5: S5 soundness triple + `modalTableauS5_sound` [NOT STARTED]

- **Goal:** Instantiate 513's generic soundness lemmas at the equivalence frame condition and land
  the top soundness theorem.
- **Tasks:**
  - [ ] In `FrameSoundness.lean`, add `s5FC : FrameCondition := fun {World} r => IsEquiv World r`
    (mirror `reflFC:953` / `symmFC:1166` / `s4FC:1044`).
  - [ ] Prove the cluster-connectivity soundness core: adding `T(φ)@w'` (a universal-propagation
    output) to a branch witnessing `branchSatisfiableIn s5FC` preserves it, given `T(□φ)@w ∈ b`
    and that `w'` is a known branch world. Key step: recorded edges map into `m.r`
    (`branchSatisfiableIn` contract) and `IsEquiv m.r` closes edge-connectivity into
    `m.r`-equivalence, so `m.r (f w) (f w')` holds for any two branch worlds — hence
    `Satisfies m (f w) (□φ)` gives `Satisfies m (f w') φ`. Mirror
    `branchSatisfiableIn_symmFC_boxPos_pred_mem` (`FrameSoundness.lean:1186`) and its diaNeg dual;
    name them `branchSatisfiableIn_s5FC_boxPos_all_mem` / `…_diaNeg_all_mem`.
  - [ ] Rule-output soundness wrappers connecting `modalS5BoxAll`/`modalS5DiaNegAll` outputs to
    those cores (mirror the `modalTBoxSelf`/`modalBBoxBack` output-soundness lemmas at
    `FrameSoundness.lean:1009,1027,1232`).
  - [ ] In `FrameCompleteness.lean`, prove the soundness triple `hAgreeS5`,
    `modalApplyOneS5_boxPos_soundIn` (with `hFC : s5FC m.r`), `modalApplyOneS5_diaNeg_soundIn`
    (mirror `hAgreeB:1619`, `modalApplyOneB_boxPos_soundIn:1635`, `modalApplyOneB_diaNeg_soundIn:1676`).
  - [ ] `modalTableauS5_sound (φ) (h : modalTableauS5 φ = .closed) : s5Valid φ` by instantiating
    `modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:728`) at `(s5FC, modalApplyOneS5)`,
    passing `modalApplyOneS5_spec.freshLocal` as the `hFreshLocal` argument plus the `hAgreeS5` /
    box-pos / dia-neg triple — mirror the `modalTableauB_sound:1725` call pattern exactly
    (`… symmFC modalApplyOneB modalApplyOneB_spec.freshLocal hAgreeB …`).
- **Timing:** 1.5 hours
- **Depends on:** 1, 2 (`modalTableauS5_sound` consumes `modalApplyOneS5_spec.freshLocal`)
- **Files to modify:** `FrameSoundness.lean` (`s5FC`, connectivity cores), `FrameCompleteness.lean`
  (soundness triple + `modalTableauS5_sound`).
- **Verification:** `lake build` green; zero sorry/axiom; `modalTableauS5_sound` type-checks; CI clean.
- **[BLOCKED] fallback:** If the cluster-connectivity invariant cannot be closed sorry-free, mark
  [BLOCKED] with the open goal (which connectivity step fails) and recommend a scoped
  `s5-soundness-connectivity` follow-up. Never `sorry`/`axiom`.

---

### Phase 6: `s5Valid` + decidability [NOT STARTED]

- **Goal:** State `s5Valid` against `Cube.S5` and deliver `Decidable (s5Valid φ)`.
- **Tasks:**
  - [ ] In `FrameSoundness.lean`, `def s5Valid (φ) : Prop := frameValid s5FC φ` (mirror
    `bValid:1170`), with a docstring justifying that an equivalence frame realises `Cube.S5`
    (= `K ∪ T ∪ Four ∪ Five`): `IsEquiv` gives `Std.Refl` (T), `IsTrans` (Four), `Std.Symm` (B),
    and `RightEuclidean` (Five). If a `Cube.S5`-membership bridge lemma is wanted, state
    `s5Valid_iff_cubeS5` relating `frameValid s5FC` to validity over `Cube.S5` models.
  - [ ] `s5Valid_decides (φ0) : modalTableauS5 φ0 = .closed ↔ s5Valid φ0` combining
    `modalTableauS5_sound` and `modalTableauS5_complete` — mirror `bValid_decides:1761`.
  - [ ] `instDecidableS5Valid (φ0) : Decidable (s5Valid φ0)` by running `modalTableauS5` — mirror
    `instDecidableBValid` line-for-line.
- **Timing:** 1 hour
- **Depends on:** 4, 5
- **Files to modify:** `FrameSoundness.lean` (`s5Valid`), `FrameCompleteness.lean`
  (`s5Valid_decides`, `instDecidableS5Valid`).
- **Verification:** `lake build` green; zero sorry/axiom; `Decidable (s5Valid φ)` resolves via
  `instDecidableS5Valid`; CI clean.

---

### Phase 7: 5 / KB5 Euclidean coverage via the S5 route [NOT STARTED]

- **Goal:** Expose the Euclidean frame condition on the extracted model and state 5/KB5 validity +
  completeness via the equivalence route; document pure-K5 as out of scope.
- **Tasks:**
  - [ ] `extractModelS5_rightEuclidean : Relation.RightEuclidean (extractModelS5 b acc).r`.
    Note: the `RightEuclidean` class lives in `Cslib/Foundations/Relation/Defs.lean:49` (field
    `rightEuclidean : r a b → r a c → r b c`); there is **no** unconditional `IsEquiv → RightEuclidean`
    instance and **no** lemma literally named `RightEuclidean.symm`. Construct it from
    `extractModelS5_equiv`'s `Std.Symm` + `IsTrans` components via
    `Relation.symm_rightEuclidean_iff_trans` (`Euclidean.lean:236`, for a symmetric relation
    `RightEuclidean r ↔ IsTrans α r`), or directly: `r a b → r a c` gives `r b a` (`Std.Symm`) then
    `r b c` (`IsTrans` with `r a c`). Seriality glue for KB5 comes from `refl_serial`
    (`Euclidean.lean:35`).
  - [ ] Add `fiveFC`/`kb5FC` (or reuse `s5FC` and note `frameValid s5FC` entails `Five`/`KB5`
    validity): state `fiveValid`/`kb5Valid` and their completeness via the same `extractModelS5`
    countermodel (which satisfies `RightEuclidean`, plus `Std.Symm` for KB5). The soundness arm uses
    `Satisfies.five` (`Basic.lean:376`, needs `Relation.RightEuclidean m.r`) and the `Euclidean.lean`
    API.
  - [ ] Add an in-file docstring block stating that genuine **pure-K5 / pure-5** (Euclidean without
    full equivalence) has no Mathlib closure operator and is OUT OF SCOPE, deferred to a dedicated
    `pure-k5-euclidean-closure` task (per `reports/03` non-goals). No `EuclGen`, no `sorry`, no
    `axiom`.
- **Timing:** 1.25 hours
- **Depends on:** 3, 6
- **Files to modify:** `FrameCompleteness.lean` (Euclidean instance + 5/KB5 validity/completeness),
  `FrameSoundness.lean` (5/KB5 validity defs + soundness arm via `Satisfies.five`).
- **Verification:** `lake build` green; zero sorry/axiom; the `RightEuclidean` instance and
  5/KB5-route validity results type-check; the pure-K5 out-of-scope note is present; CI clean.
- **[BLOCKED] fallback:** If a `Cube.Five`/`Cube.KB5` completeness statement cannot be closed
  sorry-free through the equivalence route, deliver only `extractModelS5_rightEuclidean` +
  documented handoff and mark the 5/KB5-completeness portion [BLOCKED]. Never `sorry`/`axiom`.

---

## Testing & Validation

Run the full CSLib CI pipeline at the end of **every** phase (order per `cslib.md`):
- [ ] `lake build` — green, and **zero `sorry` / zero new `axiom`** (only the standard
  `propext`/`Classical.choice`/`Quot.sound` trio; verify with `lean_verify` on each new top-level
  declaration).
- [ ] `lake exe checkInitImports` — `S5Simplification.lean` imports `Cslib.Init`.
- [ ] `lake lint` — docstring on every new decl (docBlame); Prop-valued results as
  `lemma`/`theorem` (defLemma); lowerCamelCase, no underscores in decl bases (`modalApplyOneS5`,
  `extractModelS5`, `modalS5BoxAll`); `@[simp]` only with verified LHS (simpNF); `omit` unused
  section vars; instances inside the namespace (topNamespace).
- [ ] `lake exe lint-style` — clean.
- [ ] `lake test` — CslibTests passes.
- [ ] `lake exe mk_all --module` — `S5Simplification.lean` registered in `Cslib.lean`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — import minimization clean.
- [ ] Acceptance: `instDecidableS5Valid` resolves `Decidable (s5Valid φ)` (Phase 6);
  `extractModelS5_rightEuclidean` and the 5/KB5-route validity results type-check (Phase 7).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — `modalApplyOneS5`, `modalS5BoxAll`/
  `modalS5DiaNegAll`, characterization + agreement lemmas, `modalApplyOneS5_spec`, driver
  instantiation (`modalStepBranchS5`/`modalExpandBranchesS5`/`modalTableauS5` + `_eq` lemmas),
  `modalExpandBranchesS5_hintikka` and any S5 Hintikka helpers.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — `s5FC`, `s5Valid`, cluster-connectivity
  soundness cores, 5/KB5 validity defs.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `extractModelS5` (+ `_r`/`_equiv`/
  `_hasEdge_imp_r`/`_rightEuclidean`), `modalTruthLemmaS5`, `modalOpenBranch_countermodelS5`,
  `modalTableauS5_complete`, S5 soundness triple, `modalTableauS5_sound`, `s5Valid_decides`,
  `instDecidableS5Valid`, 5/KB5 validity + completeness.
- `Cslib.lean` — barrel updated via `mk_all`.
- `specs/504_.../summaries/01_s5-kb5-euclidean-decidability-summary.md` (on completion).

## Rollback/Contingency

- Each phase is a self-contained, task-scoped commit at a green milestone; revert an individual
  phase's commit to roll back without disturbing prior phases or the B/T/K results.
- The S5 line is purely additive: it introduces `S5Simplification.lean` and appends to
  `FrameSoundness.lean`/`FrameCompleteness.lean` in the established B pattern, so reverting the S5
  additions restores the sorry-free B/T/K tableau intact.
- Preferred contingency for the two risk items (Phase 5 cluster-connectivity, Phase 7 5/KB5
  completeness) is a documented **[BLOCKED]** handoff with the open goal state and a recommended
  scoped follow-up task — never a `sorry` or `axiom`. Phases 1-4/6 stand alone and ship the S5
  decision procedure independently of the Euclidean exposure.
```