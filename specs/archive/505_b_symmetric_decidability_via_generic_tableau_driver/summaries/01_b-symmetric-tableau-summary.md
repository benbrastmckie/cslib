# Implementation Summary: Task #505 — B (Symmetric-Frame) Tableau via Generic Driver

- **Task**: 505 - B symmetric-frame decidability via the generic tableau driver (Phase 4 of task 300)
- **Status**: Implementation complete — all 9 phases delivered green
- **Plan**: plans/01_b-symmetric-tableau-implementation.md

## Overview

Delivered the B (symmetric-frame) modal tableau system end to end: the backward-propagation
rule, driver instantiation, `RuleApplicationSpec` discharge, generic Hintikka-chain
instantiation, symmetric-closure model extraction, the B truth lemma, rule-level and
driver-level soundness, `bValid` completeness, and `Decidable (bValid φ)`.

The plan's Phase 9 was written with an explicit `[BLOCKED]-on-task-513` fallback, since task
513 (`generalize_tableau_soundness_chain_over_spec`) had not landed when the plan was written.
Task 513 landed during this dispatch (commits `45c94d35..00b0ae34`, immediately before this
session started), exposing a spec-instantiable generic soundness chain
(`modalStepBranchGen_preserves_satIn`/`modalExpandBranchesGen_closed_unsatIn`,
`FrameSoundness.lean`). B's soundness side only needed to supply its own `hAgree`/`hBoxPos`/
`hDiaNeg` triple and instantiate — mirroring exactly how task 513 itself instantiated T. Phase 9
was therefore delivered rather than left `[BLOCKED]`.

## Phases Delivered

| Phase | File(s) | Key deliverables |
|-------|---------|-------------------|
| 1 | `FrameRules.lean` | `modalBPredecessorsOf`, `modalBBoxBack`/`modalBDiaNegBack`, `modalApplyOneB`, agreement lemma |
| 2–4 | `BDriver.lean` (new) | Driver defs, 11-field `modalApplyOneB_spec`, `modalExpandBranchesB_hintikka`, and the new `accSourcesKnown` invariant (source-side twin of `accTargetsKnown`) with single-step and top-loop propagation lemmas |
| 5 | `FrameCompleteness.lean` | `extractModelB` via `Relation.SymmGen`, `_r`/`_symm`/`_hasEdge_imp_r`/`_hasEdge_symm_imp_r` |
| 6 | `FrameCompleteness.lean` | `hintikkaB_box_pos`/`hintikkaB_diamond_neg`, `modalTruthLemmaB` |
| 7 | `FrameSoundness.lean` | `symmFC`, `bValid`, rule-level `modalBBoxBack_sound`/`modalBDiaNegBack_sound` |
| 8 | `FrameCompleteness.lean` | `modalOpenBranchB_countermodel`, `modalTableauB_complete` |
| 9 | `FrameCompleteness.lean` | `hAgreeB`, driver-level `modalApplyOneB_boxPos_soundIn`/`_diaNeg_soundIn`, `modalTableauB_sound`, `bValid_decides`, `instDecidableBValid` |

## The Structural Crux: `accSourcesKnown`

B's backward-propagation rule emits at *predecessor* worlds — sources of recorded `acc` edges —
rather than at the source formula's own world (T's self-loop) or at *targets* of recorded edges
(S4's forward 4-rule). `FmpMeasure.lean`'s existing `accTargetsKnown` invariant only bounds edge
*targets*, so it does not place predecessor worlds in `modalKnownWorlds b`, which is required to
discharge `RuleApplicationSpec.knownWorldsStep` and to force backward-propagated formulas onto a
real derivation's branch.

Two complementary fixes were introduced:

1. **`modalBBoxBack`/`modalBDiaNegBack` filter to known predecessors by construction**
   (`FrameRules.lean`): this makes `RuleApplicationSpec.knownWorldsStep`'s discharge
   unconditional (true for *any* `(b, acc)` satisfying only `accTargetsKnown`, as the interface
   requires), without needing any new invariant.
2. **`accSourcesKnown`** (`BDriver.lean`): a new bookkeeping invariant (`∀ w w', acc.hasEdge w
   w' → w ∈ modalKnownWorlds b`), proven preserved by `modalStepBranchGen apply` (mirroring
   `accTargetsKnown`'s own preservation proof) and propagated through the entire fuel recursion
   via a new top-loop lemma (`modalExpandBranchesGen_openBranch_accSourcesKnown`, mirroring
   `modalExpandBranchesGen_openBranch_initial_mem`'s double-induction structure but tracking a
   per-`(branch, acc)`-pair invariant via `List.zip` rather than a single formula's membership).
   This is what shows the filter in (1) never actually excludes a genuine predecessor on a real
   derivation — needed by the B truth-lemma bridges (`hintikkaB_box_pos`/`hintikkaB_diamond_neg`)
   and threaded through `modalTruthLemmaB`, `modalTableauB_complete`.

Several small local re-derivations of `FmpMeasure.lean`/`CompletenessLoop.lean` `private` helper
lemmas (`mem_modalKnownWorlds`, `modalKnownWorlds_mono_append`, `hasEdge_addEdge_cases`,
`modalStepBranchGen_newExps_const`, `modalSubfmls_trans`, `mem_modalUniverse_of`) were required
in `BDriver.lean` since those lemmas are inaccessible across files; each is a short (~5–30 line)
proof reproduced from the public `def`s they operate on.

## Verification

- `lake build` (full project): green.
- `lake exe checkInitImports`: green.
- `lake lint`: zero warnings in the four modified/new files.
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no new issues (the `BDriver.lean`
  `import Cslib.Init`/`import Completeness` "remove" suggestions are pre-existing false
  positives, matching the identical suggestion already accepted for `TDriver.lean`).
- `lake test`: green (`CslibTests` suite).
- `grep -rn "\bsorry\b"` across all four files: zero matches.
- `lean_verify` on `bValid_decides`/`instDecidableBValid`: standard axiom trio only (`propext`,
  `Classical.choice`, `Quot.sound`) — no `sorryAx`, no new axioms.
- Vacuous-definition grep: zero matches.

## Plan Deviations

- **Phase 8**: `bValid` itself is defined in `FrameSoundness.lean` (Phase 7), not
  `FrameCompleteness.lean`, mirroring exactly where T's `tValid`/`reflFC` precedent lives (T's
  `tValid` is defined in `FrameSoundness.lean` alongside `reflFC`). Phase 8 as delivered adds
  only `modalTableauB_complete` (+ `modalOpenBranchB_countermodel`) to `FrameCompleteness.lean`.
- **Phase 9**: delivered in full rather than landing the documented `[BLOCKED]-on-task-513`
  fallback, since task 513 landed immediately before this dispatch began.

## Concurrent-Session Note

`Cslib/Logics/Modal/Tableau/BDriver.lean` also appears in task 512's commit `f85e59f1` (a
concurrent orchestration operating on the same working tree) as a byte-identical snapshot of
this file's in-progress state at that time, including a since-completed `sorry` placeholder.
This session's commits (`3d4cc95f` onward) supersede that snapshot with the completed,
zero-sorry version. No task-512-authored content was discarded — the snapshot's content was
this task's own in-progress file, captured incidentally by a non-scoped commit boundary in the
other session.

## Artifacts

- `Cslib/Logics/Modal/Tableau/FrameRules.lean` — B backward-propagation arms (`modalBBoxBack`,
  `modalBDiaNegBack`, `modalBPredecessorsOf`, `modalApplyOneB`, agreement + membership lemmas).
- `Cslib/Logics/Modal/Tableau/BDriver.lean` (new) — B driver defs, `modalApplyOneB_spec`,
  `modalExpandBranchesB_hintikka`, `accSourcesKnown` + preservation/top-loop lemmas.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `extractModelB`, B truth-lemma bridges,
  `modalTruthLemmaB`, `modalTableauB_complete`, `modalTableauB_sound`, `bValid_decides`,
  `instDecidableBValid`.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — `symmFC`, `bValid`, rule-level soundness.
- `Cslib.lean` — mk_all registration of `BDriver.lean`.

## Commits

- `a65b8ed0` — task 505 phase 1
- `3d4cc95f` — task 505 phases 2-4
- `a0a89045` — task 505 phase 5
- `8e4afe89` — task 505 phase 6
- `f627d310` — task 505 phase 7
- `75182916` — task 505 phase 8
- `f85bcb2b` — task 505 phase 9
