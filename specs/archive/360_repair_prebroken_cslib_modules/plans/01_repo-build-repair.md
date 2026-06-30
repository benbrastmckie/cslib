# Implementation Plan: Restore Green Repo-Wide `lake build` (Task #360)

- **Task**: 360 - Repair pre-broken CSLib modules
- **Status**: [NOT STARTED]
- **Effort**: 7.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/360_repair_prebroken_cslib_modules/reports/01_repo-build-repair.md
- **Artifacts**: plans/01_repo-build-repair.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The repo-wide `lake build` fails at the final aggregation step (3130/3132) plus several mid-tree
modules. Per the research report, the 11 originally-listed failures collapse into **four
root-cause clusters**, not eleven independent bugs. This plan repairs them in order A -> B -> C ->
D, one cluster per phase, with incremental `lake build <Module>` verification after each fix and a
full CI gate (`lake build` + `checkInitImports` + `shake`) as the final phase. Definition of done:
full `lake build` is green and the post-build CI checks pass; **no new `sorry`/axiom is
introduced** (zero-debt policy). Cluster D modules that cannot be honestly completed are marked
`[BLOCKED]` rather than papered over.

### Research Integration

Key findings integrated from `reports/01_repo-build-repair.md`:
- **Cluster A (6 modules)**: downstream fallout of task-340's `neg`/`top` -> `PropositionalConnectives`
  typeclass-delegate migration. Mechanical fix = append `PropositionalConnectives.neg`/`.top`
  (and relevant derived-op abbrev unfolds) to ~35 downstream `simp only [...]` sites. Each site
  uses `simp only`, so a global `@[simp]` lemma is not picked up automatically; per-site edits are
  the recommended low-risk fix.
- **Cluster B (SequentCalculus)**: duplicate `Cslib.Logic.PL.cutAdmissibility._unary._proof_1`
  auxiliary clash between co-imported LK and LJ under the experimental `module` system. Fix via
  namespace isolation (`Cslib.Logic.PL.LK` / `.LJ`) and/or `private`.
- **Cluster C (Tableau.Minimal.Soundness)**: call-site arity drift vs the recently-modified
  `Intuitionistic.Soundness.intExpandBranches_closed_unsat`. Targeted call-site fix only; the
  inherited pre-existing `sorry` is out of scope.
- **Cluster D (3 modules)**: genuine WIP / blockers — `Modal.Tableau.Soundness` and
  `Classical.Completeness` (left mid-refactor by `df974743 "update"`), plus the newly-broken
  `HilbertLindenbaumRel` (task-344 API mismatch). Attempt genuine fixes; mark `[BLOCKED]` any
  module whose author intent cannot be honestly recovered.
- **Drift deltas**: `Temporal.ConservativeExtension` now builds clean (dropped from scope);
  `HilbertLindenbaumRel` newly broke (added to scope, Cluster D).

**Execution-order note**: Clusters A, B, and C are mutually independent leaf-ish fixes (the
report states their order is not load-bearing). They are presented as Phases 1-3 for readability
but may be executed in any order or in parallel. Cluster D (Phase 4) is sequenced last by
tractability. The final gate (Phase 5) depends on all repair phases.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (build-repair / maintenance task).

## Goals & Non-Goals

**Goals**:
- Restore a green repo-wide `lake build`.
- Repair Cluster A, B, C with the mechanical/targeted fixes identified in research.
- Attempt genuine, intent-bearing fixes for the three Cluster D modules.
- Pass the full CI gate: `lake build`, `lake exe checkInitImports`,
  `lake shake --add-public --keep-implied --keep-prefix`.

**Non-Goals**:
- Introducing any new `sorry` or `axiom` to force a green build (zero-debt policy).
- Removing or completing the pre-existing committed `sorry` inherited by `Minimal.Soundness`
  from `intExpandBranches_closed_unsat` (separate Intuitionistic-soundness completion task).
- Re-architecting the `PropositionalConnectives` connective layer (durable `@[simp]` reduction
  lemmas are explicitly out of scope; do the local per-site edits instead).
- Touching `Temporal.ConservativeExtension` (now builds clean; out of scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cluster A simp edits cause "no progress" elsewhere (`simp only` set over-pruned) | M | M | Edit one site at a time; re-run `lake build <Module>` after each module; prune the appended lemmas to the ops each lemma actually mentions |
| Cluster B namespace move breaks downstream references to `cutAdmissibility` | M | M | Run discriminating rename test first; grep for external references before moving; prefer `private` if no external callers, else add full-namespace qualification |
| Cluster C: new `intExpandBranches_closed_unsat` signature is itself unstable | M | L | Re-read the current signature in `Intuitionistic/Soundness.lean` immediately before editing the call site |
| Cluster D author intent unrecoverable -> temptation to paper with `sorry` | H | M | Forbidden. If a module cannot be honestly fixed, mark that specific module `[BLOCKED]` with a precise note and leave the build red for it; surface to user |
| Cluster D fixes are larger than estimated | M | H | Time-box each D module; on overrun, mark `[BLOCKED]` and proceed — do not block the whole task on one WIP module |
| lean-lsp REPL environment diverges from build environment | L | M | Trust `lake build`, NOT the REPL, for every final check (per research note) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 1-4 are independent module repairs;
Phase 5 is the final gate and requires all repair phases to have run.

---

### Phase 1: Cluster A — `neg`/`top` simp-set updates (6 modules) [IN PROGRESS]

**Goal**: Thread the `PropositionalConnectives.neg`/`.top` typeclass delegates (and relevant
derived-op abbrev unfolds) through the downstream `simp only [...]` sites missed by task-340, so
each of the 6 modules builds clean.

**Tasks**:
- [ ] `Modal.Denotation` (`Cslib/Logics/Modal/Denotation.lean`): replace `simp [Proposition.neg_def, Proposition.denotation]` at line 60 with `simp [Proposition.neg, PropositionalConnectives.neg, Proposition.denotation]`. Verify: `lake build Cslib.Logics.Modal.Denotation`.
- [ ] `Bimodal.Syntax.SubformulaClosure.NestingDepth`: add `PropositionalConnectives.top` (and `PropositionalConnectives.neg` where `neg` appears) to the `simp only` sets at lines 47,60,64,87,100,104,126,130. Verify: `lake build Cslib.Logics.Bimodal.Syntax.SubformulaClosure.NestingDepth`.
- [ ] `Bimodal.Metalogic.Separation.Defs`: extend the 22 flagged `int_truth_*` simp sites (73,85,118,134,149,154,227,231,235,239,257,263,284,288,301,305,323,329,382,387,512,518) with `Formula.allPast, Formula.somePast, Formula.allFuture, Formula.someFuture, Formula.neg, PropositionalConnectives.neg, Formula.top, PropositionalConnectives.top, intTruth` — pruned to the ops each lemma actually mentions. Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Defs`.
- [ ] `Bimodal.ProofSystem.Substitution`: add `PropositionalConnectives.neg`/`.top` to the flagged `simp only` sets at lines 91,106,112,118,124,131,455. Verify: `lake build Cslib.Logics.Bimodal.ProofSystem.Substitution`.
- [ ] `Bimodal.Theorems.Perpetuity.Principles`: add `PropositionalConnectives.neg, PropositionalConnectives.top` to the `swapTemporal` simp sets feeding the `exact`s at lines 84,164,176. Verify: `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles`.
- [ ] `Temporal.Metalogic.DenseCompleteness`: add `Formula.neg, PropositionalConnectives.neg, Formula.top, PropositionalConnectives.top` to the simp set at line 166. Verify: `lake build Cslib.Logics.Temporal.Metalogic.DenseCompleteness`.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Denotation.lean` - simp set at line 60
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` - 8 simp sites
- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` - 22 simp sites
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` - 7 simp sites
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - swapTemporal sites at 84,164,176
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` - simp set at line 166

**Verification**:
- Each of the 6 `lake build <Module>` commands succeeds (trust the build, not the lean-lsp REPL).
- No new `sorry`/`axiom` introduced.

---

### Phase 2: Cluster B — SequentCalculus namespace isolation [NOT STARTED]

**Goal**: Eliminate the duplicate `Cslib.Logic.PL.cutAdmissibility._unary._proof_1` auxiliary
clash so the `SequentCalculus` aggregator (the final build step) imports LK and LJ together
cleanly.

**Tasks**:
- [ ] Discriminating test (cheap): temporarily rename LK's `cutAdmissibility` -> `lkCutAdmissibility`; rebuild the aggregator. If the clash name changes/disappears, the same-base-name auxiliary clash is confirmed.
- [ ] Move LK's cut-elimination development into `namespace Cslib.Logic.PL.LK` and LJ's into `namespace Cslib.Logic.PL.LJ` (matches ORGANISATION conventions for parallel calculi), and/or mark `cutAdmissibility` (LK) and `ljCutAdmissibility` (LJ) `private` to keep their `._unary._proof_1` auxiliaries out of the public module interface.
- [ ] Grep for external references to `cutAdmissibility` / `ljCutAdmissibility` before moving; update any qualified references to the new namespace.
- [ ] Verify: `lake build Cslib.Logics.Propositional.SequentCalculus` succeeds.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - namespace and/or `private`
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - namespace and/or `private`
- Any downstream files referencing the moved declarations (discovered via grep)

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus` succeeds.
- LK and LJ still build in isolation.

---

### Phase 3: Cluster C — Minimal.Soundness call-site fix [NOT STARTED]

**Goal**: Update the call to `intExpandBranches_closed_unsat` in `Minimal/Soundness.lean` to match
the current signature in `Intuitionistic/Soundness.lean`, clearing the type mismatch and its
cascade errors.

**Tasks**:
- [ ] Re-read the current signature of `intExpandBranches_closed_unsat` in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`.
- [ ] Update the application at `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean:128-135` to the new argument shape (fixes root error at 131:30; the 132:5, 131:25, 132:23 errors are cascades that should clear).
- [ ] Confirm NO new `sorry` is added; the inherited pre-existing `sorry` (documented at lines 41-44,116) is out of scope — flag it to the user as belonging to a separate Intuitionistic-soundness completion task.
- [ ] Verify: `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness` succeeds.

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` - call site at lines 128-135

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness` succeeds.
- No new `sorry`/`axiom`; inherited sorry count unchanged.

---

### Phase 4: Cluster D — genuine WIP fixes or `[BLOCKED]` (3 modules) [NOT STARTED]

**Goal**: Attempt honest, intent-bearing fixes for the three incomplete-WIP modules, ordered by
tractability. For any module that cannot be completed without papering over with `sorry`/axiom,
mark **that specific module** `[BLOCKED]` with a precise diagnostic note and leave its build red —
do NOT introduce debt.

**Tasks**:
- [ ] `HilbertLindenbaumRel` (smallest, API mismatch — task-344 territory): re-check the `AlgEvaluate` and `relCanonicalV` signatures; fix `relCanonicalV_satisfiesΓ` where `SatisfiesTheory (AlgEvaluate (relCanonicalV ...) ...)` is mis-applied as a function (errors at 827:4 `Function expected`, 829:8 `introN failed`). Verify: `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaumRel`. If intent unrecoverable, mark `[BLOCKED]`.
- [ ] `Modal.Tableau.Soundness` (identifier rename): determine the intended replacement for the renamed/removed hypothesis `hnewBs` (~20 references at 303/335/362/402/649/705/729) by referencing the task-299 (`299_modal_k_tableau`) plan and the handoff updated by `df974743`; fix the duplicate `imp` alternative arm at line 746 and the nested `cases` errors at 275/624. Verify: `lake build Cslib.Logics.Modal.Tableau.Soundness`. If the intended `hnewBs` replacement is unclear, mark `[BLOCKED]`.
- [ ] `Classical.Completeness` (largest, missing lemmas): replace the non-existent Mathlib lemmas `List.findSome?_of_mem` (117) and `List.find?_of_mem` (147) with the correct ones (candidates via leansearch: `List.find?_some`, `List.findSome?_eq_some_iff`); fix the `Function expected` / partially-applied terms; reference the theory report `reports/01_theory-parametric-completeness.md` added by `df974743`. The module currently contains a committed WIP `sorry` — completing the proof must REMOVE it, not add more. Verify: `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness`. If scope is large / intent unrecoverable, mark `[BLOCKED]`.
- [ ] For each module marked `[BLOCKED]`: record a precise note (module path, error summary, why honest completion is not possible, suggested follow-up task reference) for the orchestrator handoff `blockers` array.

**Timing**: 3 hours (time-boxed; on overrun for any single module, mark `[BLOCKED]` and proceed)

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean` - `relCanonicalV_satisfiesΓ` (~lines 827-829)
- `Cslib/Logics/Modal/Tableau/Soundness.lean` - `hnewBs` references + `imp` arm + `cases` nesting
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - list lemmas + partial applications + remove WIP sorry

**Verification**:
- For each module: either `lake build <Module>` succeeds with no new `sorry`/`axiom`, OR the
  module is explicitly marked `[BLOCKED]` with a diagnostic note (build remains red for it).
- Zero-debt invariant: no `sorry`/`axiom` added anywhere; `Classical.Completeness`'s existing WIP
  sorry is removed if and only if the proof is genuinely completed.

---

### Phase 5: Final CI gate [NOT STARTED]

**Goal**: Confirm the repo-wide build is green and the post-build CI checks pass.

**Tasks**:
- [ ] Run `lake build` (full). Expect green if no Cluster D module is `[BLOCKED]`.
- [ ] Run `lake exe checkInitImports` (expected to pass once oleans exist).
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (expected to pass once oleans exist).
- [ ] If any Cluster D module is `[BLOCKED]`, record the residual red modules and the overall
      status accurately in the orchestrator handoff (full green is the target; partial green with
      documented blockers is an acceptable honest outcome).

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3, 4

**Files to modify**: none (verification only)

**Verification**:
- `lake build && lake exe checkInitImports && lake shake --add-public --keep-implied --keep-prefix`
  exits clean (or, if blockers remain, the specific red modules are documented and all
  non-blocked modules build).

## Testing & Validation

Per-cluster incremental verification:
- [ ] `lake build Cslib.Logics.Modal.Denotation`
- [ ] `lake build Cslib.Logics.Bimodal.Syntax.SubformulaClosure.NestingDepth`
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Defs`
- [ ] `lake build Cslib.Logics.Bimodal.ProofSystem.Substitution`
- [ ] `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles`
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.DenseCompleteness`
- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus`
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness`
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaumRel`
- [ ] `lake build Cslib.Logics.Modal.Tableau.Soundness`
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness`

Final gate:
- [ ] `lake build` (full) green
- [ ] `lake exe checkInitImports` passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes
- [ ] No new `sorry`/`axiom` anywhere (zero-debt invariant held)

## Artifacts & Outputs

- plans/01_repo-build-repair.md (this plan)
- summaries/01_repo-build-repair-summary.md (on implementation)
- Modified Lean source files across Clusters A-D (enumerated per phase)
- specs/360_repair_prebroken_cslib_modules/.orchestrator-handoff.json (orchestrator handoff)

## Rollback/Contingency

- All Cluster A/B/C edits are local and reversible via `git checkout -- <file>` per module; revert
  any module whose edit introduces a regression and re-attempt.
- Cluster B namespace move: if downstream references prove extensive, fall back to the lighter
  `private` fix alone.
- Cluster D: if a fix cannot be completed honestly, revert that module's working-tree changes,
  mark it `[BLOCKED]`, and document it in the handoff `blockers` array — never commit `sorry`/axiom
  to force green.
- If the final gate fails downstream of an unexpected new break, bisect by re-running the
  per-module builds to localize, then revert the offending edit.
