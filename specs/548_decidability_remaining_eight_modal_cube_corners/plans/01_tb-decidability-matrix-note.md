# Implementation Plan: TB Decidability + Intentional-Completeness Matrix Note

- **Task**: 548 - Decidability for the remaining modal-cube corners (SCOPE NARROWED)
- **Status**: [IMPLEMENTING]
- **Effort**: 16 hours
- **Dependencies**: 511 (complete), 535 (archived-complete), 597 (complete)
- **Research Inputs**: `specs/548_decidability_remaining_eight_modal_cube_corners/reports/01_eight-corner-decidability-research.md`
- **Artifacts**: plans/01_tb-decidability-matrix-note.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Land exactly two deliverables. First, **TB end-to-end**: the frame condition, validity
predicate, extractor, rule, `RuleApplicationSpec` discharge, truth lemma, soundness,
completeness, `tbValid_decides`, and `instDecidableTBValid` — taking the modal-cube decidability
matrix from 7/15 to 8/15. Second, the **intentional-completeness matrix note**: a documented
in-tree record stating, for each remaining corner (D, K4, K45, D4, D5, D45, DB), its frame
condition, assessed tier, named blocking gate, and cost estimate. Definition of done: `lake
build` green, zero live `sorry` in the tableau subtree, standard axiom triple only, every frozen
declaration byte-identical, and the matrix note present and accurate against the shipped tree.

This plan does **not** attempt any other corner. The generic-driver extension is out of scope —
the tableau driver abstraction decision formally rejected it and kept per-regime drivers bespoke,
and this plan works within that decision rather than re-litigating it.

### Research Integration

Findings from `reports/01_eight-corner-decidability-research.md` that drive this plan:

- **The matrix is 7/15, not 6/15** (§1.1). `instDecidableS4Valid` exists at
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:8281`. The matrix note must state 8/15
  after TB, not 7/15.
- **TB is the only ungated corner** (§0.5, §4.1). Both ingredient rules exist and are pure-
  `persistent`, never-minting: `modalApplyOneT` (`FrameRules.lean:85`) and `modalApplyOneB`
  (`FrameRules.lean:362`). Both discharge the full eleven-field `RuleApplicationSpec`
  (`modalApplyOneT_spec`, `TDriver.lean:740`; `modalApplyOneB_spec`, `BDriver.lean:772`).
- **`Relation.ReflGen.compRel_symm` is already in tree** at
  `Cslib/Foundations/Relation/Confluence.lean:368`, with the exact statement TB's frame instance
  needs: `ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a`.
- **Cost band**: low end of Tier A, ~1,300–1,800 lines (§4.1), because both arm families and both
  truth-lemma conjuncts already exist and only their *conjunction* is new.
- **D's seriality rule cannot satisfy `RuleApplicationSpec.boxPosNotExpanding`** (§5.1,
  `GenericDriver.lean:239-243`), and all three mint-avoiding alternatives are refuted (two
  unsound, one non-terminating). This is the gate the matrix note records for the five serial
  corners.
- **Frozen sets** (§6) are carried verbatim into "Frozen Deliverables (No-Touch)" below.
- The **task-534 third of the original freeze clause is vacuous** (§6, no artifacts, no
  `specs/534_*` directory) and is dropped from this plan.

### Structural findings added by this plan (verified at HEAD, beyond the report)

These were confirmed by reading the tree while planning and change the phase decomposition:

1. **Per-corner drivers already live in their own files.** `TDriver.lean` (809 lines) and
   `BDriver.lean` (1,124 lines) each hold driver instantiation, shape lemmas, the
   `RuleApplicationSpec` discharge, and the Hintikka-chain instantiation. TB therefore gets a
   new sibling module `Cslib/Logics/Modal/Tableau/TBDriver.lean`, not an append to an existing
   driver file. This is the single largest structural decision in the plan and it follows
   established file layout rather than inventing one.
2. **`tbFC` in the tableau namespace is name-safe, with precedent.** `tbFC` already exists at
   `Cslib/Logics/Modal/Metalogic/Systems/TB/Completeness.lean:58` in namespace
   `Cslib.Logic.Modal` with type `Model World Atom → Prop`. But `s4FC` and `s5FC` *already*
   exist in both namespaces the same way (`Metalogic/Systems/S4/Completeness.lean:48` and
   `Metalogic/Systems/S5/Completeness.lean:47`, versus `FrameSoundness.lean:1056` and `:1572`).
   The tableau-side name `Cslib.Logic.Modal.Tableau.tbFC : FrameCondition` is therefore
   consistent with shipped precedent, not a new collision.
3. **`accSourcesKnown` and its preservation lemmas are already generic over the spec.**
   `accSourcesKnown` (`BDriver.lean:841`), `modalStepBranchGen_preserves_accSourcesKnown`
   (`:860`), and `modalExpandBranchesGen_openBranch_accSourcesKnown` (`:1071`) are parameterised
   on an arbitrary `RuleApplicationSpec`. TB's predecessor-reading arms reuse them with zero new
   proof content — this is free reuse, and Phase 7 must confirm it rather than re-derive it.
4. **The TB truth lemma's box-positive case decomposes into exactly three subcases.** TB's
   extracted relation is `ReflGen (SymmGen (acc.hasEdge · ·))`, whose constructors are `.refl`,
   `.single (.inl h)`, and `.single (.inr h)` — i.e. same-world (T's self conjunct), forward edge
   (K's existing bridge `hintikka_box_pos`), and backward edge (B's backward conjunct). This is
   a clean three-way `rcases`, and each branch already has its lemma at T or B.

### Prior Plan Reference

No prior plan. This is version 1 for this task.

### Roadmap Alignment

No `specs/ROADMAP.md` in this repository; no roadmap phases added.

## Goals & Non-Goals

**Goals**:
- Land `tbFC`, `tbValid`, `extractModelTB` (+ its `_r`/`_refl`/`_symm`/`_hasEdge_imp_r`/
  `_hasEdge_symm_imp_r` lemmas), `modalApplyOneTB` (+ agreement lemma), `modalApplyOneTB_spec`
  (full eleven-field `RuleApplicationSpec`), the TB driver triple
  (`modalStepBranchTB`/`modalExpandBranchesTB`/`modalTableauTB`), `modalTruthLemmaTB`,
  `modalOpenBranchTB_countermodel`, `modalTableauTB_sound`, `modalTableauTB_complete`,
  `tbValid_decides`, and `instDecidableTBValid`.
- Land the intentional-completeness matrix note covering D, DB, K4, D4, K45, D5, D45, each with
  frame condition, tier, named gate, gate-owning successor task, and cost estimate.
- Keep `lake build` green, zero live `sorry` in `Cslib/Logics/Modal/Tableau/`, and the standard
  axiom triple only (`propext`, `Classical.choice`, `Quot.sound`).

**Non-Goals**:
- Any of D, DB, K4, D4, K45, D5, D45 — these are documented, not implemented.
- Any generic-driver / traversal-rung abstraction. The driver abstraction decision rejected it;
  do not build it, do not re-litigate it.
- Prototyping `RuleApplicationSpecSerial` or the additive `modalLoopGen_eBoxOnlyNeg_serial`
  sibling (owned by successor task 598).
- The universal-cluster rule-combinator prototype (owned by successor task 599).
- The unordered S4 stepper-stack retirement (owned by successor task 600).
- Any edit to `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`.
- Any strategic `sorry` or new axiom. This plan has no skeleton and no planned sorries.

## Frozen Deliverables (No-Touch)

Carried verbatim from research report §6. These declarations may be **read and reused** freely;
their source text must be byte-identical after this task. All additions to the shared files below
are **append-only** at the end of the relevant `/-! ## ... -/` section — no reordering, no
re-indentation, no docstring rewrites of existing declarations.

**From task 300** (`handoffs/phase2-blocked-handoff.md`):

| File | Frozen declarations |
|------|---------------------|
| `Tableau/FrameRules.lean` | `modalTBoxSelf` (:62), `modalTDiaNegSelf` (:69), `modalApplyOneT` (:85), `modalApplyOneT_eq_of_not_boxPos_diaNeg` (:111) |
| `Tableau/FrameSoundness.lean` | `FrameCondition` (:75), `trivialFC` (:79), `frameValid` (:85), `branchSatisfiableIn` (:112), `modalTableau_sound_frame` (:918), `reflFC` (:965), `tValid` (:969), `branchSatisfiableIn_reflFC_boxPos_mem`/`_diaNeg_mem`, `modalTBoxSelf_sound`, `modalTDiaNegSelf_sound` |
| `Tableau/FrameCompleteness.lean` | `extractModelWith` (:85), `extractModelWith_id` (:98), `extractModelT` (:105), `extractModelT_r` (:113), `extractModelT_refl` (:120), `extractModelT_hasEdge_imp_r` (:132) |
| `Cslib.lean` | barrel registration of `FrameRules` |

**From task 506** (`summaries/01_s4-loopchecking-termination-decidability-summary.md`):

| File | Frozen declarations |
|------|---------------------|
| `Tableau/FrameRules.lean` | `modalFourBoxProp` (:133), `modalFourDiaNegProp` (:146), `modalApplyOneS4Rules` (:158), `modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg` (:184) |
| `Tableau/LoopChecking.lean` **and its `S4/` split** | `formulasAtWorld`, `sameRelevantSet` (+ refl/symm/trans), `blockingWorld`, `modalApplyOneS4`, `modalStepBranchS4`/`modalExpandBranchesS4`/`modalTableauS4`, `modalHintikkaSetS4`, `hintikkaS4_*` bridges, `modalWorldBoundS4`, `modalUniverseS4`, `S4LoopInv` |
| `Tableau/FrameCompleteness.lean` | `extractModelS4` (:145), `extractModelS4_hasEdge_imp_r` (:183), `modalTruthLemmaS4` (:234), `modalOpenBranchS4_countermodel` (:405) |
| `Tableau/FrameSoundness.lean` | `s4FC` (:1056), `s4Valid` (:1060), `branchSatisfiableIn_s4FC_boxPos_trans_mem`/`_diaNeg_trans_mem`, `modalFourBoxProp_sound`, `modalFourDiaNegProp_sound` |
| `Cslib.lean` | barrel entry for `LoopChecking` |

**Path-drift note** (report §6): most of what 506 called `LoopChecking.lean` now lives in
`Cslib/Logics/Modal/Tableau/S4/` (10 modules, 10,573 lines). Current homes:
`modalApplyOneS4`/`modalTableauS4` → `S4/Driver.lean:122,219`; `modalHintikkaSetS4` →
`S4/Hintikka.lean:74`; `S4LoopInv` → `S4/Invariant.lean:85`;
`modalWorldBoundS4`/`signedSubfmls` → `S4/Universe.lean:208,280`; `blockingWorldS4Keyed` →
`S4/Guard.lean:173`; `successorBirthContent` → `S4/BirthKey.lean:79`.

**Additional explicit no-touch**: `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` must remain
untouched (506's plan `:201,586`). TB needs no new termination measure — it inherits K's
`modalWorldBound`-based one through the full `RuleApplicationSpec` — so this constraint costs
nothing here, but a phase that finds itself wanting to edit `FmpMeasure.lean` has taken a wrong
turn and must stop.

**Implied freeze** (report §6): all seven existing `Decidable` instances and their
sound/complete/decides triples, plus `CslibTests/S4LoopGuardRegression.lean`,
`CslibTests/ModalFrameSeparation.lean`, and `CslibTests/TableauConformance.lean`.

**Task 534**: vacuous — no `specs/534_*` directory, no artifacts. Dropped from this plan's freeze
clause with the report's finding as the reason.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The three termination fields (`rankStep`, `outDegStep`, `knownWorldsStep`) fail for the *conjunction* of T and B arms even though each discharges them alone | H | L | Phase 6 discharges these first, before the F8-F12 chain. Both arm families are pure-`persistent` at existing worlds and never mint, so the `.linear` edge-invariant path is never entered — the same argument that works at T and at B independently. If a field genuinely fails, stop and mark the phase `[BLOCKED]` with the exact goal; do not weaken the spec and do not add a sorry |
| F9/F10 (`boxPosNotExpanding`/`diaNegNotExpanding`) break because the TB box-positive arm now emits two conjuncts (T self + B backward) | M | L | Both conjuncts are `.persistent`; F9 forbids only `.linear`. The existentially-quantified `∃ out, ... = .persistent out` form the bundle already uses accommodates the merged output list directly (report §4.1) |
| Accidental modification of a frozen declaration during append-only edits | H | M | Phase 11 runs `git diff` restricted to the four frozen files and asserts every hunk is an addition below the last frozen declaration; any modified or deleted line in a frozen declaration fails the gate |
| `tbFC` name resolution ambiguity against the Hilbert-side `tbFC` in files opening both namespaces | M | L | Precedent verified: `s4FC`/`s5FC` already coexist across the two namespaces with different types. Phase 2 confirms elaboration is clean; if a genuine ambiguity surfaces at a call site, qualify at that site rather than renaming the declaration |
| TB truth-lemma box-positive case needs a `ReflGen (SymmGen ...)` reachability decomposition not present at T or B alone | M | M | The three-subcase decomposition (`.refl` / `.single (.inl h)` / `.single (.inr h)`) is stated in "Structural findings" above and each branch reuses an existing lemma. Phase 8 is sized for this being the single hardest proof in the task |
| Scope creep into a second corner because "D looks close" | H | M | Non-Goals is explicit; the matrix note is the sanctioned output for every other corner. Phase 11 verifies no new `Valid` predicate beyond `tbValid` was added |
| The matrix note drifts from the shipped tree (e.g. states 7/15 after TB lands) | M | M | Phase 1 writes the note; Phase 11 re-reads it against the final tree and reconciles counts, file:line anchors, and gate ownership before the task closes |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 3 |
| 3 | 5 | 4 |
| 4 | 6 | 5 |
| 5 | 7 | 6 |
| 6 | 8, 9 | 7 |
| 7 | 10 | 8, 9 |
| 8 | 11 | 1, 10 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Intentional-Completeness Matrix Note [COMPLETED]

**Goal**: Land the second deliverable — an in-tree documented note recording, per remaining
corner, the frame condition, assessed tier, named blocking gate, gate-owning successor task, and
cost estimate, so the matrix is intentionally complete rather than accidentally ragged.

**Tasks**:
- [ ] Append a new top-level `/-! ## Modal-Cube Decidability Matrix: Coverage and Intentional
      Out-of-Scope Notes -/` doc section to `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`,
      immediately before the closing `end Cslib.Logic.Modal.Tableau` (currently `:8287`)
- [ ] State the covered column: K, T, B (KB), S5, K5 (Five), KB5, S4, and TB — with each
      `Decidable` instance named and its driver named. Anchor by declaration name, not line
      number
- [ ] For each remaining corner record a row: **frame condition** (from `Cslib/Logics/Modal/Cube.lean`),
      **closure operator** that would be needed, **tier** (A/B/C), **named gate**, **owning
      successor task**, **cost estimate**:
  - [ ] `D` — `Relation.Serial`; no closure suffices; Tier A cost; gate = serial-rule spec shape
        (`RuleApplicationSpec.boxPosNotExpanding`, `GenericDriver.lean:239-243`, forbids the
        `.linear` mint at exactly the box-positive shape a D tableau must mint at); owner = task
        598; ~1,700 lines once ungated
  - [ ] `DB` — `Serial ∧ Std.Symm`; `SymmGen` + serial repair; Tier A/B; gate = serial-rule spec
        shape; owner = task 598; ~1,700–3,600 lines
  - [ ] `K4` — `IsTrans`; `Relation.TransGen`; Tier C; gates = unordered S4 stepper-stack
        retirement **and** T-arm removal from the S4 rule chain; owner = task 600; ~13,500 lines
  - [ ] `D4` — `Serial ∧ IsTrans`; `TransGen` + serial repair; Tier C; gates = both of the above
        plus serial-rule spec shape; owners = tasks 598 and 600; ~13,500 lines
  - [ ] `K45` — `IsTrans ∧ Relation.RightEuclidean`; `EuclGen` (+ transitivity); Tier B; gate =
        universal-cluster rule-combinator prototype; owner = task 599; ~3,600 lines
  - [ ] `D5` — `Serial ∧ RightEuclidean`; `EuclGen` + serial repair; Tier B; gates = combinator
        prototype and serial-rule spec shape; owners = tasks 598 and 599; ~3,600 lines
  - [ ] `D45` — `Serial ∧ IsTrans ∧ RightEuclidean`; as K45 + serial repair; Tier B; gates =
        combinator prototype and serial-rule spec shape; owners = tasks 598 and 599; ~3,600 lines
- [ ] Record the three refuted mint-avoiding alternatives for D by name and reason
      (self-loop-at-dead-ends closure: unsound, licenses the T inference; fresh sink world:
      relocates without discharging; `F(□⊥)` seeding: sound but non-terminating under
      `rankStep`), so the refutations are in-tree rather than only in the task tracker
- [ ] Record that the per-regime driver split is a settled decision and that no generic traversal
      rung is to be built
- [ ] Note that the ordered S4 driver, not the unordered keyed one, is the sound one, and
      cross-reference `instDecidableS4Valid`'s existing docstring rather than restating it
- [ ] Confirm no task-number citation appears in any file outside `specs/**` — reference gates by
      their descriptive names in the Lean docstring, and keep successor-task numbers in this plan
      only

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts seven remaining corners and one new doc section in one
file. Confirm at implementation time by (a) enumerating the `Cube.lean` system definitions and
checking exactly eight of fifteen are covered after TB lands, and (b) `git diff --stat` showing
`FrameCompleteness.lean` as the only file changed by this phase, with an addition-only hunk.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — append one `/-! -/` doc section before
  the namespace close

**Verification**:
- The changed hunk lies entirely inside a `/-! ... -/` comment block (diff read-through)
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` still green (a doc comment must not
  change elaboration; if it does, the hunk crossed a boundary)
- Every remaining corner from `Cube.lean` has exactly one row; no corner is omitted and none is
  described as "revisit later" without a named gate and a cost figure
- No task-number citation in the Lean source (per the deliverables rule)

---

### Phase 2: TB Frame Condition, Validity, and Extraction [COMPLETED]

**Goal**: Land `tbFC`, `tbValid`, and `extractModelTB` with the five extraction lemmas the truth
lemma and completeness proof will consume.

**Tasks**:
- [x] In `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, append a `/-! ## TB (Reflexive-Symmetric
      Frame) -/` section after the B section: `def tbFC : FrameCondition := fun {_} r => Std.Refl r ∧ Std.Symm r`
      and `def tbValid (φ : Proposition Atom) : Prop := frameValid tbFC φ`, mirroring `s5FC`/`s5Valid`
      (`:1572,:1576`) exactly in shape
- [x] Confirm the tableau-side `tbFC` elaborates without ambiguity against the Hilbert-side
      `Cslib.Logic.Modal.tbFC` (different namespace, different type — same coexistence pattern
      `s4FC`/`s5FC` already ship) *(confirmed: `lake build` green, no ambiguity)*
- [x] In `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, append a `/-! ## TB
      (Reflexive-Symmetric Frame) Extraction -/` section after the B extraction section (currently
      ending near `:472`), defining
      `def extractModelTB ... := extractModelWith (fun r => Relation.ReflGen (Relation.SymmGen r)) b acc`
- [x] Prove `extractModelTB_r` by `rfl`, mirroring `extractModelT_r` (`:113`) and
      `extractModelB_r` (`:437`)
- [x] Prove `extractModelTB_refl : Std.Refl (extractModelTB b acc).r` — `rw [extractModelTB_r];
      infer_instance` off `Relation.reflexive_reflGen`, mirroring `extractModelT_refl` (`:120`)
- [x] Prove `extractModelTB_symm : Std.Symm (extractModelTB b acc).r` using
      `Relation.ReflGen.compRel_symm` (`Cslib/Foundations/Relation/Confluence.lean:368`), which
      states exactly `ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a` *(required adding
      `public import Cslib.Foundations.Relation.Confluence` to `FrameCompleteness.lean`'s import
      list — not previously imported there — deviation: added, not in original task list)*
- [x] Prove `extractModelTB_hasEdge_imp_r` (forward edge survives, via
      `Relation.ReflGen.single (Or.inl h)`) and `extractModelTB_hasEdge_symm_imp_r` (backward
      edge survives, via `Relation.ReflGen.single (Or.inr h)`), mirroring
      `extractModelB_hasEdge_imp_r` (`:457`) and `extractModelB_hasEdge_symm_imp_r` (`:468`)
- [ ] Add a `extractModelTB_frame : tbFC (extractModelTB b acc).r` convenience conjunction if the
      completeness call site reads better with it; otherwise pass the two lemmas as a pair
      *(deviation: deferred — plan marks this conditional ("if... otherwise pass the two lemmas
      as a pair"); Phase 10 will add it if the completeness call site needs it)*
- [x] Confirm no frozen declaration in either file was touched (`git diff` hunks are all
      additions, all below the last frozen declaration in their section) — verified: both diffs
      are addition-only

**Deviation (front-loaded Phase 9 content)**: while writing the TB frame-condition section in
`FrameSoundness.lean`, also landed the rule-level TB soundness lemmas
(`tbFC_imp_reflFC`/`tbFC_imp_symmFC` projections, `branchSatisfiableIn_tbFC_boxPos_self_mem`/
`_diaNeg_self_mem`/`_boxPos_pred_mem`/`_diaNeg_pred_mem`, and
`modalTBoxSelf_tbFC_sound`/`modalTDiaNegSelf_tbFC_sound`/`modalBBoxBack_tbFC_sound`/
`modalBDiaNegBack_tbFC_sound`) that Phase 9's task list assigns to a later dispatch. These
depend only on `tbFC`/`reflFC`/`symmFC` and the already-shipped T/B rule definitions, not on
`modalApplyOneTB` (Phase 3) or the driver (Phase 4-8), so they slot naturally into the section
Phase 2 creates. Phase 9 still owes the `modalApplyOneTB_sound` bundle (which needs
`modalApplyOneTB` to exist) and the `FrameCompleteness.lean` discharge block; Phase 9's own
checklist is annotated accordingly when reached.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts two files changed and roughly six new declarations
(`tbFC`, `tbValid`, `extractModelTB`, `_r`, `_refl`, `_symm`, `_hasEdge_imp_r`,
`_hasEdge_symm_imp_r`). Confirm by `git diff --stat` naming exactly `FrameSoundness.lean` and
`FrameCompleteness.lean`, and by grepping the diff for `^\+def |^\+lemma |^\+theorem ` to count
the actual declarations added. If the count differs, record the actual set — the count is a
hypothesis, not a target.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — append TB frame condition + validity
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — append TB extraction section

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green (this transitively builds
  `FrameSoundness`)
- `#print axioms extractModelTB_symm` shows only the standard triple
- No `sorry` in the new hunks
- `git diff Cslib/Logics/Modal/Tableau/FrameSoundness.lean Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
  contains no `-` lines

---

### Phase 3: TB Rule and Agreement Lemma [COMPLETED]

**Goal**: Land `modalApplyOneTB` and its agreement lemma in `FrameRules.lean`, append-only.

**Tasks**:
- [ ] Append a `/-! ## TB-Augmented Rule Application -/` section at the end of
      `Cslib/Logics/Modal/Tableau/FrameRules.lean` (after `modalApplyOneB_eq_of_not_boxPos_diaNeg`,
      `:390`)
- [ ] Define `modalApplyOneTB` by wrapping `modalApplyOneB` (`:362`) with T's self-propagation
      arms `modalTBoxSelf` (`:62`) and `modalTDiaNegSelf` (`:69`), merging both into the inner
      layer's `persistent` output — the exact layering pattern `modalApplyOneS4Rules` (`:158`)
      uses over `modalApplyOneT`
- [ ] **Layering rationale to record in the docstring**: B's arms are the predecessor-lookup
      family and carry the larger spec discharge (`BDriver.lean` 1,124 lines versus
      `TDriver.lean` 809), so keeping them in the inner layer maximises reuse from
      `modalApplyOneB_spec` and leaves the outer agreement lemma the simpler of the two. If the
      goal shape at Phase 5 forces the opposite layering (wrap `modalApplyOneT` with B's backward
      arms `modalBBoxBack`/`modalBDiaNegBack`), flip it and record the flip and its reason in the
      phase notes — the report sanctions either order
- [ ] Prove `modalApplyOneTB_eq_of_not_boxPos_diaNeg`: outside the box-positive and
      diamond-negative shapes, `modalApplyOneTB` collapses to `modalApplyOne`. Mirror
      `modalApplyOneB_eq_of_not_boxPos_diaNeg` (`:390`) and
      `modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg` (`:184`). **This lemma is the load-bearing
      reuse mechanism** — it is what lets TB inherit every propositional and mint case from K
      unchanged (report §2.3)
- [ ] Confirm all eight frozen `FrameRules.lean` declarations (four from task 300, four from task
      506) are byte-identical

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameRules.lean` — append TB rule section

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameRules` green
- `git diff Cslib/Logics/Modal/Tableau/FrameRules.lean` shows additions only, all after line 403
- `modalApplyOneTB_eq_of_not_boxPos_diaNeg` proved without `sorry`
- Spot-check by `#eval`/`example` that `modalApplyOneTB` on a box-positive input yields a
  `.persistent` result containing both the T self-conjunct and the B backward conjunct

---

### Phase 4: TBDriver Module Skeleton, Shape Lemmas, and Barrel Registration [COMPLETED]

**Goal**: Create `Cslib/Logics/Modal/Tableau/TBDriver.lean` with the driver triple and the shape
lemmas for the two TB-relevant signed-formula shapes, and register it in the barrel.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Tableau/TBDriver.lean` with a module docstring stating what TB
      is, which two arm families it merges, and that it discharges the full `RuleApplicationSpec`
      — mirroring `BDriver.lean`'s header (`:15-70`)
- [ ] Define `modalStepBranchTB`, `modalExpandBranchesTB`, and `modalTableauTB` by instantiating
      the generic driver at `modalApplyOneTB`, mirroring `BDriver.lean:76,85,94`
- [ ] Add the `/-! ## Shape Lemmas for the Two TB-Relevant Signed-Formula Shapes -/` section,
      mirroring `BDriver.lean:97-200` and `TDriver.lean:87-247`. These characterise the merged
      output list at the box-positive and diamond-negative shapes and are the substrate every
      spec field below consumes
- [x] Add the local universe-membership helpers (cross-world variants) the B arms need, mirroring
      `BDriver.lean:201-234`; reuse `modalBPredecessorsOf_hasEdge` (`FrameRules.lean:238`),
      `modalBBoxBack_mem` (`:278`), `modalBDiaNegBack_mem` (`:297`),
      `modalBPredecessorsOf_mem_of_hasEdge` (`:317`), `modalBBoxBack_mem_of` (`:331`), and
      `modalBDiaNegBack_mem_of` (`:343`) rather than re-deriving them *(deviation: altered —
      TBDriver.lean treats `modalApplyOneB`'s own result as an opaque witness satisfying the
      already-proven `modalApplyOneB_spec` bundle, rather than descending to B's
      `FrameRules.lean` primitives the way `BDriver.lean` had to descend to K's. Every field
      discharge below consumes `modalApplyOneB_spec.<field>` directly, so the cross-world
      predecessor-membership helpers B needed to re-derive its own fields from K primitives are
      not needed a second time by TB. This maximises reuse from `modalApplyOneB_spec`, consistent
      with Phase 3's stated layering rationale.)*
- [ ] Register `public import Cslib.Logics.Modal.Tableau.TBDriver` in `Cslib.lean`, inserted in
      alphabetical position among the existing `Cslib.Logics.Modal.Tableau.*` entries
      (currently `:492-523`; TBDriver sorts after `Support.KnownWorlds` and before `TDriver`)
- [ ] Leave the `RuleApplicationSpec` discharge as a named `/-! ## Discharging
      `RuleApplicationSpec` for `modalApplyOneTB` -/` section header with no declarations yet —
      Phases 5 and 6 fill it. Do **not** stub it with a `sorry`

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts one new module plus one barrel line, and a shape-lemma
block sized against `BDriver.lean:97-234` (~140 lines). Confirm by building the new module
standalone and by `git diff --stat` naming exactly `TBDriver.lean` (new) and `Cslib.lean`. The
line figure is an estimate from the B analogue, not a target — record the actual.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/TBDriver.lean` — new file
- `Cslib.lean` — one barrel import line

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.TBDriver` green
- `lake build Cslib` green (confirms the barrel entry resolves and nothing downstream broke)
- Zero `sorry` in the new module
- The module compiles with the spec-discharge section present but empty — no placeholder axiom,
  no `sorry`

---

### Phase 5: Discharge `RuleApplicationSpecCore` Fields F1-F7 for `modalApplyOneTB` [NOT STARTED]

**Goal**: Prove the first seven `RuleApplicationSpecCore` fields for `modalApplyOneTB`:
`freshLocal`, `outputsSubsetUniverse`, `persistentFresh`, `branchingLength`, and the three
termination fields `rankStep`, `outDegStep`, `knownWorldsStep`.

**Tasks**:
- [ ] Discharge the three **termination** fields first — `rankStep`, `outDegStep`,
      `knownWorldsStep` — because they carry the plan's highest-impact risk. Both TB arm families
      are pure-`persistent` at existing worlds and never mint, so the merged rule agrees with
      `modalApplyOne` on every mint-shaped input via `modalApplyOneTB_eq_of_not_boxPos_diaNeg`,
      and the exact-decrement edge invariant is never entered by a TB-specific arm. Mirror
      `BDriver.lean:235-665` and the T analogue in `TDriver.lean:248-620`
- [ ] Discharge `freshLocal` by agreement with `modalApplyOne` on mint-shaped inputs
- [ ] Discharge `outputsSubsetUniverse` — the merged output list is the union of T's self-conjunct
      output and B's backward-conjunct output, each already known to lie in the universe at its
      own corner
- [ ] Discharge `persistentFresh` and `branchingLength`
- [ ] If any termination field genuinely fails, **stop**: mark the phase `[BLOCKED]`, record the
      exact goal state and which field, and do not weaken `RuleApplicationSpec`, do not add a
      `sorry`, do not fall back to a `Core`-only discharge without escalating. TB's whole value is
      that it needs no bespoke termination argument

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/TBDriver.lean` — spec-discharge section, F1-F7

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.TBDriver` green after each field lands
- Each field's proof is `sorry`-free; commit per green field or small group of fields
- `#print axioms` on each named field lemma shows only the standard triple

---

### Phase 6: Discharge F8-F12 and Assemble `modalApplyOneTB_spec` [NOT STARTED]

**Goal**: Prove the Hintikka/saturation chain fields `localShapeInvariance` (F8),
`boxPosNotExpanding` (F9), `diaNegNotExpanding` (F10), `boxNegWitness'` (F11'), and
`diaPosWitness'` (F12'), then assemble the full eleven-field `modalApplyOneTB_spec`.

**Tasks**:
- [ ] Discharge F8 `localShapeInvariance`, mirroring `BDriver.lean:666-771` and
      `TDriver.lean:621-739`
- [ ] Discharge F9 `boxPosNotExpanding`: the TB box-positive arm emits the T self-conjunct **and**
      the B backward conjunct, both `.persistent`, never `.linear`. Use the existentially-
      quantified `∃ out, (apply sf b acc).1 = .persistent out` form the bundle already uses so the
      merged output list is accommodated directly
- [ ] Discharge F10 `diaNegNotExpanding` dually
- [ ] Discharge F11' `boxNegWitness'` and F12' `diaPosWitness'` — these are K's own two mint arms,
      inherited unchanged through the agreement lemma
- [ ] Assemble `theorem modalApplyOneTB_spec : RuleApplicationSpec (Atom := Atom) modalApplyOneTB`
      from the eleven field proofs, mirroring `modalApplyOneB_spec` (`BDriver.lean:772`) and
      `modalApplyOneT_spec` (`TDriver.lean:740`)
- [ ] Confirm it is the **full** `RuleApplicationSpec`, not `RuleApplicationSpecCore` — TB is a
      Tier A corner and a Core-only discharge would silently move it to Tier B

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/TBDriver.lean` — spec-discharge section, F8-F12 and the assembly

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.TBDriver` green
- `#check @modalApplyOneTB_spec` reports type `RuleApplicationSpec modalApplyOneTB` (not
  `RuleApplicationSpecCore`)
- `#print axioms modalApplyOneTB_spec` shows only the standard triple
- Zero `sorry` in the module

---

### Phase 7: TB Instantiation of the Generic Hintikka/Saturation Chain [NOT STARTED]

**Goal**: Instantiate the generic Hintikka/saturation chain and the `accSourcesKnown` plumbing at
`(modalApplyOneTB, modalApplyOneTB_spec)`, with no TB-specific proof content.

**Tasks**:
- [ ] Add the `/-! ## TB Instantiation of the Generic Hintikka/Saturation Chain -/` section,
      mirroring `BDriver.lean:790-827`
- [ ] Prove `modalStepBranchTB_eq`, `modalExpandBranchesTB_eq`, and `modalTableauTB_eq` — the
      definitional bridges from the TB-named driver to the generic one
- [ ] Prove `modalExpandBranchesTB_hintikka` by applying `modalExpandBranchesGen_hintikka
      modalApplyOneTB modalApplyOneTB_spec`, mirroring `BDriver.lean:826`
- [ ] **Confirm rather than re-derive** the `accSourcesKnown` reuse: `accSourcesKnown`
      (`BDriver.lean:841`), `modalStepBranchGen_preserves_accSourcesKnown` (`:860`), and
      `modalExpandBranchesGen_openBranch_accSourcesKnown` (`:1071`) are already parameterised on
      an arbitrary spec. TB's predecessor-reading arms should consume them with zero new proof
      content. If a genuine TB-specific obligation appears here, record it explicitly — that
      would be a deviation from the B analogue and worth naming
- [ ] Confirm `modalExpandBranchesGen_openBranch_accTargetsKnown` (`BDriver.lean:1100`) is
      likewise reusable

**Timing**: 1 hour

**Depends on**: 6

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/TBDriver.lean` — Hintikka chain instantiation section

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.TBDriver` green
- The section contains no proof longer than the B analogue's corresponding one — if it does, the
  generic reuse was not achieved and that fact must be recorded
- Zero `sorry`

---

### Phase 8: TB Modal Truth Lemma and Open-Branch Countermodel [NOT STARTED]

**Goal**: Prove `modalTruthLemmaTB` against `extractModelTB` and derive
`modalOpenBranchTB_countermodel`. This is the hardest proof in the task.

**Tasks**:
- [ ] Add a `/-! ## TB Modal Truth Lemma -/` section to
      `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, after the B truth-lemma section
      (currently `:1322-1700`)
- [ ] State `modalTruthLemmaTB` mirroring `modalTruthLemmaB` (`:1527`): for every `φ` and `w`,
      `⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelTB b acc) w φ` and the negative dual, given
      `accSourcesKnown b acc` and the Hintikka hypothesis
- [ ] Propositional cases: reuse the same structure as `modalTruthLemmaB` — no TB-specific content
- [ ] **Box-positive case — the three-way decomposition**: `rcases` the
      `ReflGen (SymmGen (acc.hasEdge · ·)) w w'` hypothesis into
  - [ ] `.refl` (w = w'): discharged by T's self-conjunct, the `hintikkaT_box_pos`-family bridge
  - [ ] `.single (.inl h)` (forward raw edge): discharged by K's existing `hintikka_box_pos`
        bridge via `extractModelTB_hasEdge_imp_r`
  - [ ] `.single (.inr h)` (backward raw edge): discharged by B's backward conjunct
        (`hintikkaB_box_pos`-family) via `extractModelTB_hasEdge_symm_imp_r`
- [ ] Diamond-negative case: dual of the above, same three subcases
- [ ] Box-negative and diamond-positive cases: reuse the free generic bridges
      `hintikka_box_neg_gen` / `hintikka_diamond_pos_gen` from `Completeness.lean` unchanged
- [ ] Derive `modalOpenBranchTB_countermodel`, mirroring `modalOpenBranchB_countermodel` (`:1694`)
- [ ] Confirm `modalTruthLemmaS4` (`:234`) and `modalOpenBranchS4_countermodel` (`:405`), both
      frozen, are untouched

**Timing**: 2 hours

**Depends on**: 2, 7

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts a proof sized against `modalTruthLemmaB`
(`:1527-1700`, ~175 lines), estimated at ~200-250 lines for TB because the box-positive and
diamond-negative cases each gain a third subcase. Confirm at implementation time by measuring the
actual added block; if it materially exceeds the estimate, the three-way decomposition assumption
in this plan's "Structural findings" was wrong and that must be recorded, not absorbed silently.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — append TB truth-lemma section

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green
- `#print axioms modalTruthLemmaTB` and `modalOpenBranchTB_countermodel` show only the standard
  triple
- Zero `sorry`
- `git diff` shows additions only in this file

---

### Phase 9: TB Soundness [NOT STARTED]

**Goal**: Prove the TB arm soundness discharges against `tbFC` and land `modalTableauTB_sound`.

**Tasks**:
- [ ] In `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, append a `/-! ### TB-Rule Semantic
      Soundness -/` subsection under the TB section added in Phase 2
- [ ] Prove `branchSatisfiableIn_tbFC_boxPos_self_mem` / `_diaNeg_self_mem` — the T arms' soundness
      relative to `tbFC`, reducing to the reflexivity conjunct `.1`. These mirror
      `branchSatisfiableIn_reflFC_boxPos_mem` / `_diaNeg_mem` but with the conjunct projection.
      Reuse the frozen `modalTBoxSelf_sound` / `modalTDiaNegSelf_sound` where the shapes allow,
      projecting `tbFC`'s `Std.Refl` conjunct into `reflFC`
- [ ] Prove `branchSatisfiableIn_tbFC_boxPos_pred_mem` / `_diaNeg_pred_mem` — the B arms' soundness
      relative to `tbFC`, reducing to the symmetry conjunct `.2`, mirroring
      `branchSatisfiableIn_symmFC_boxPos_pred_mem` (`:1486`) and `_diaNeg_pred_mem` (`:1508`) with
      the conjunct projection. Reuse `modalBBoxBack_sound` and `modalBDiaNegBack_sound` the same
      way
- [ ] Prove `modalApplyOneTB_sound` (or the equivalently-named per-arm bundle the shape demands)
      combining the four
- [ ] In `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, append a `/-! ## TB Soundness
      Discharges + `modalTableauTB_sound` -/` section and prove
      `modalTableauTB_sound : modalTableauTB φ = .closed → tbValid φ`, mirroring
      `modalTableauB_sound` (`:1885`) and its discharge block (`:1762-1884`)
- [ ] Note the projection pattern: because `tbFC r = Std.Refl r ∧ Std.Symm r`, every T-side
      obligation is `reflFC` applied to `h.1` and every B-side obligation is `symmFC` applied to
      `h.2`. This is the same projection `s5FC_imp_fiveFC` (`FrameSoundness.lean:1608`) already
      uses; follow it rather than re-proving the arm soundness from semantics

**Timing**: 1.5 hours

**Depends on**: 7

**Verification Tier**: interface

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — TB arm soundness subsection
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — TB soundness discharges +
  `modalTableauTB_sound`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green
- `#print axioms modalTableauTB_sound` shows only the standard triple
- Zero `sorry`
- Frozen `FrameSoundness.lean` declarations (`FrameCondition`, `frameValid`, `reflFC`, `tValid`,
  `s4FC`, `s4Valid`, and the four named soundness lemmas) byte-identical

---

### Phase 10: TB Completeness, `tbValid_decides`, and `instDecidableTBValid` [NOT STARTED]

**Goal**: Close the corner — completeness, the decides equivalence, and the `Decidable` instance
that takes the matrix to 8/15.

**Tasks**:
- [ ] Append a `/-! ## `tbValid` Completeness -/` section to
      `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, proving
      `modalTableauTB_complete`, mirroring `modalTableauB_complete` (`:1712-1760`). Supply
      `accSourcesKnown` via `modalExpandBranchesGen_openBranch_accSourcesKnown` instantiated at
      `modalApplyOneTB_spec.freshLocal` (the same call shape used at `:1738`), and discharge the
      frame condition on the open-branch countermodel with
      `⟨extractModelTB_refl b a, extractModelTB_symm b a⟩`
- [ ] Append a `/-! ## `tbValid` Decidability -/` section proving
      `theorem tbValid_decides (φ₀ : Proposition Atom) : modalTableauTB φ₀ = .closed ↔ tbValid φ₀`,
      mirroring `bValid_decides` (`:1921`)
- [ ] Land `instance instDecidableTBValid (φ₀ : Proposition Atom) : Decidable (tbValid φ₀)`,
      mirroring `instDecidableBValid` (`:1933`). No `Fintype Atom` assumption — the tableau
      computation is the decision procedure
- [ ] Write the instance docstring naming which driver it uses (`modalTableauTB`) and stating that
      TB is a Tier A corner discharging the full `RuleApplicationSpec`, following the pattern of
      `instDecidableS4Valid`'s docstring (`:8278-8280`)
- [ ] Confirm the seven pre-existing `Decidable` instances and their sound/complete/decides
      triples are untouched

**Timing**: 1.5 hours

**Depends on**: 8, 9

**Verification Tier**: interface

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — completeness, decides, instance

**Verification**:
- `lake build Cslib` green
- `#print axioms instDecidableTBValid` and `tbValid_decides` show only the standard triple
- A smoke check: `#eval` or `example` confirming `tbValid (□p → p)` decides `True` (the T axiom,
  valid on reflexive frames) and `tbValid (p → □◇p)` decides `True` (the B axiom), while a
  formula valid only on transitive frames (e.g. `□p → □□p`) decides `False` — TB frames are not
  transitive. Place any such check in `CslibTests/`, never in the library module
- Zero `sorry`

---

### Phase 11: Final Verification Gate and Matrix-Note Reconciliation [NOT STARTED]

**Goal**: Run the complete gate set, verify every constraint this plan committed to, and
reconcile the Phase 1 matrix note against the shipped tree.

**Tasks**:
- [ ] Full `lake build` from clean — green, zero errors, zero warnings introduced by this task
- [ ] Assert zero **live** `sorry` in `Cslib/Logics/Modal/Tableau/`: grep for `sorry` and confirm
      every match is inside a docstring or comment (the pre-existing baseline is 15 prose
      matches; the count may change if this task's docstrings mention it — verify each match is
      prose, do not compare the number blindly)
- [ ] Assert zero new axioms: `#print axioms` on `instDecidableTBValid`, `tbValid_decides`,
      `modalTableauTB_sound`, `modalTableauTB_complete`, `modalTruthLemmaTB`, and
      `modalApplyOneTB_spec` — each shows exactly `propext`, `Classical.choice`, `Quot.sound`
- [ ] **Frozen-declaration audit**: for each of `FrameRules.lean`, `FrameSoundness.lean`,
      `FrameCompleteness.lean`, and the `S4/` modules, run `git diff` and confirm every hunk is
      an addition; confirm no `-` line touches any declaration named in this plan's "Frozen
      Deliverables" tables
- [ ] **`FmpMeasure.lean` no-touch audit**: `git diff --stat Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
      is empty
- [ ] **Scope audit**: confirm the only new `frameValid` instantiation is `tbValid` — no `dValid`,
      `k4Valid`, `k45Valid`, `d4Valid`, `d5Valid`, `d45Valid`, or `dbValid` was added
- [ ] **Matrix-note reconciliation**: re-read the Phase 1 note against the final tree. Confirm it
      states 8/15 (not 7/15), names `instDecidableTBValid` in the covered column, and that every
      declaration-name anchor it cites resolves. Correct any drift
- [ ] Run the existing regression tests: `CslibTests/S4LoopGuardRegression.lean`,
      `CslibTests/ModalFrameSeparation.lean`, `CslibTests/TableauConformance.lean` — all green
- [ ] Confirm no task-number citation appears in any file outside `specs/**`

**Timing**: 1 hour

**Depends on**: 1, 10

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts a fixed audit list (four frozen files, one no-touch file,
seven forbidden `Valid` predicates, three regression tests). Confirm by executing each check and
recording its output; a check that cannot be run is a finding, not a pass.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — matrix-note corrections only, if drift is
  found

**Verification**:
- Every audit item above produces recorded evidence (command output or quoted match count), not an
  assertion
- `lake build` green from clean
- Task may close only when all audits pass

---

## Testing & Validation

- [ ] `lake build` green from clean, whole project
- [ ] Zero live `sorry` under `Cslib/Logics/Modal/Tableau/` (every match confirmed prose)
- [ ] `#print axioms` on all six TB capstone declarations shows only `propext`,
      `Classical.choice`, `Quot.sound`
- [ ] `instDecidableTBValid` decides the T axiom `□p → p` and the B axiom `p → □◇p` as valid, and
      the 4 axiom `□p → □□p` as invalid (TB frames need not be transitive) — checks placed in
      `CslibTests/`
- [ ] `modalApplyOneTB_spec` has type `RuleApplicationSpec`, not `RuleApplicationSpecCore`
- [ ] All three existing modal-tableau regression test files green
- [ ] `git diff` on the four frozen files shows additions only; `FmpMeasure.lean` diff empty
- [ ] The matrix note covers all seven remaining corners with frame condition, tier, named gate,
      and cost estimate each; none says "revisit later" without a named gate
- [ ] No task-number citation outside `specs/**`

## Artifacts & Outputs

- `specs/548_decidability_remaining_eight_modal_cube_corners/plans/01_tb-decidability-matrix-note.md` (this file)
- `specs/548_decidability_remaining_eight_modal_cube_corners/summaries/01_tb-decidability-matrix-note-summary.md`
- `Cslib/Logics/Modal/Tableau/TBDriver.lean` (new module)
- `Cslib/Logics/Modal/Tableau/FrameRules.lean` (append: TB rule + agreement lemma)
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (append: `tbFC`, `tbValid`, TB arm soundness)
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (append: TB extraction, truth lemma,
  soundness discharges, completeness, `tbValid_decides`, `instDecidableTBValid`, matrix note)
- `Cslib.lean` (one barrel import line for `TBDriver`)
- `CslibTests/` (TB smoke checks, if added)

## Rollback/Contingency

Every phase is append-only against existing modules plus one new module, so rollback is a git
revert of the phase's commits with no migration. Because commits are per-green-substep, a revert
never leaves a half-proved declaration in tree.

Phase-specific contingencies:

- **Phase 5 termination-field failure** (the highest-impact risk): mark the phase `[BLOCKED]`,
  record the exact failing field and goal state, and stop. Do **not** weaken `RuleApplicationSpec`,
  do **not** fall back to a `Core`-only discharge, do **not** add a `sorry`. A Core-only TB would
  silently reclassify the corner as Tier B and invalidate the plan's cost basis, so it needs a
  decision, not an in-phase workaround.
- **Phase 3 layering flip**: if the B-inner layering makes Phase 5's goals unworkable, flip to
  wrapping `modalApplyOneT` with B's backward arms and record the flip. Both orders are sanctioned
  by the research; this is a recorded design change, not a blocker.
- **Phase 8 truth-lemma blowup**: if the box-positive case does not decompose into the three
  expected subcases, record what it actually decomposes into before proceeding — that finding
  contradicts this plan's structural assumption and should be captured for the successor corners.
- **Partial completion**: Phase 1 (the matrix note) is deliberately Wave 1 with no dependencies,
  so the second deliverable lands even if the TB chain stalls. If TB blocks after Phase 1, the
  matrix note stands on its own and the task reports `[PARTIAL]` with TB's blocking phase named —
  but the note must then be corrected to state 7/15 and to list TB with its blocking reason,
  rather than claiming a corner that did not land.
