# Implementation Plan: Task #447

- **Task**: 447 - Apply lake shake import-minimization fixes to files touched by tasks 321/406/431
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/447_apply_shake_import_minimization_fixes_tasks_321_406_431/reports/01_shake-import-minimization-verification.md
- **Artifacts**: plans/01_apply-shake-import-fixes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Apply the 17 verified `lake shake --add-public --keep-implied --keep-prefix`
import-minimization edits across the files touched by tasks 321/406/431. These are
pure import-hygiene edits (no term-level changes, no `sorry`, no new axioms). The plan
sequences edits in the research-recommended order — independent leaf edits first,
GenericMCS bridge swaps next (with their hidden `open` correction), `Cslib.Init`
removals gated on `checkInitImports`, then the barrel/re-export edits — rebuilding
between each group so any break is isolated to the group that caused it. A final
verification phase re-runs scoped shake to confirm the 17 listed suggestions are
resolved and runs the full CI gate.

### Research Integration

Key findings from `01_shake-import-minimization-verification.md` drive this plan:

1. All 17 suggestions are **genuine current shake output**, not false positives.
2. The six `import Cslib.Init` removals are **genuine** (Init's linters/tactics remain
   active transitively; `checkInitImports` requires only a *transitive* Init import).
   Remove them; only fall back to `import Cslib.Init -- shake: keep` if
   `checkInitImports` regresses for a specific file.
3. **Hazard**: the three GenericMCS bridge swaps each also carry a dead
   `open Cslib.Logic.Metalogic.MCSProperties` line that shake does not model. It must
   be removed **together with** the import swap or the build fails with
   `unknown namespace`.
4. Paired moves (Structures→Elimination `Encodable.Basic`, Closure→Atoms `Satisfies`)
   are confirmed genuine and must be applied together.
5. **Scope**: shake reports MORE suggestions than the 17 listed (out-of-scope files:
   Defs/Branch/Closure/SoundnessStep/TimeOrdering/MCS.lean). The verification criterion
   is that **the 17 listed suggestions are resolved**, NOT full shake cleanliness.
6. **Environment**: uncommitted WIP in `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
   (unrelated to 447) causes shake's `--no-build` sanity check to abort with
   "out of date oleans"; local shake reproduction needs `--force` after a full build.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (import-hygiene cleanup, not a roadmap feature).

## Goals & Non-Goals

**Goals**:
- Apply all 17 verified import-minimization edits exactly as listed in the report.
- Keep the tree green (build/test/checkInitImports/lint-style) after the changes.
- Confirm the 17 listed shake suggestions no longer appear in scoped shake output.

**Non-Goals**:
- Addressing the out-of-scope shake backlog (Defs/Branch/Closure/SoundnessStep/
  TimeOrdering/MCS.lean and other codebase-wide suggestions).
- Any term-level, proof, or definitional changes.
- Committing or resolving the unrelated FmpMeasure WIP (only ensure it does not block
  verification; use `--force` for local shake if needed).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| GenericMCS swap leaves dead `open MCSProperties` → `unknown namespace` | H | H (certain if missed) | Remove the paired `open` line in the same edit (#8 line 72, #9 line 74, #10 line 62); build immediately after Phase 3. |
| `import Cslib.Init` removal breaks `checkInitImports` for a file | M | L | Gate Phase 4 on `lake exe checkInitImports`; if a file regresses, restore `import Cslib.Init -- shake: keep` for that file only. |
| Interface.lean barrel removal breaks a downstream consumer needing `Elimination` | M | M | Build after Phase 5; if a consumer breaks, add a direct `Elimination` import there. |
| Paired move applied one-sided (e.g. remove without add) → build error | M | M | Apply each pair (#13/#14, #15/#16) as a unit within its phase; build before advancing. |
| FmpMeasure WIP blocks canonical (no-`--force`) shake | L | M | Use `lake build` then `lake shake --force ...` for local verification; note this is a local-only workaround. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases are a strict linear chain: each group rebuilds so any breakage is isolated to
the group that introduced it. Phases within a wave could run in parallel, but here each
wave has one phase by design.

---

### Phase 1: Baseline & Environment Prep [COMPLETED]

**Goal**: Establish a green baseline and confirm shake reproduction works given the
FmpMeasure WIP caveat, before touching any imports.

**Tasks**:
- [ ] Run `lake build` to confirm a fully-built, green baseline tree.
- [ ] Note the uncommitted WIP in `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
      (git status `M`); do NOT commit or modify it as part of task 447.
- [ ] Reproduce baseline scoped shake with `lake shake --force --add-public
      --keep-implied --keep-prefix <17 touched modules>` (module list in the report's
      "Commands" section) and confirm the 17 listed suggestions currently appear.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- None (read-only baseline)

**Verification**:
- `lake build` exits 0.
- Scoped shake prints the 17 listed suggestions (matching the report's verdict table).

---

### Phase 2: Independent Leaf Edits [NOT STARTED]

**Goal**: Apply the four independent leaf edits/pairs that have no cross-dependency on
bridges or Init, then rebuild.

**Tasks**:
- [ ] #7 `FreeMeetExtension.lean`: remove `public import Mathlib.Data.Multiset.Basic`
      (retains `Mathlib.Data.Multiset.MapFold`, which supplies Basic transitively).
- [ ] #11 `.../CounterexampleElimination/BurgessHelpers.lean`: remove
      `public import Mathlib.Data.Finset.Max` and `public import Mathlib.Tactic.Linarith`;
      add `public import Mathlib.Tactic.NormNum`.
- [ ] #13/#14 paired: in `Temporal/.../CounterexampleElimination/Structures.lean`
      remove `public import Mathlib.Logic.Encodable.Basic`; in the sibling
      `Elimination.lean` add `public import Mathlib.Logic.Encodable.Basic` (Elimination
      declares `instance : Encodable PotentialCounterexampleKind` and imports Structures).
- [ ] #15/#16 paired: in `LTL/Semantics/GNBA/Closure.lean` remove
      `public import ...Satisfies`, `public import Mathlib.Data.Set.Finite.Powerset`,
      `public import Mathlib.Data.Set.Finite.Lattice`; add
      `public import Cslib.Logics.LTL.Syntax.Formula`. In `GNBA/Atoms.lean` add
      `public import Cslib.Logics.LTL.Semantics.Satisfies` (Atoms imports Closure).

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` - import removal
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/BurgessHelpers.lean` - swap Finset.Max+Linarith → NormNum
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/Structures.lean` - remove Encodable.Basic
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/Elimination.lean` - add Encodable.Basic
- `Cslib/Logics/LTL/Semantics/GNBA/Closure.lean` - remove 3, add Formula
- `Cslib/Logics/LTL/Semantics/GNBA/Atoms.lean` - add Satisfies

**Verification**:
- `lake build` exits 0 (paired moves keep every symbol reachable).

---

### Phase 3: GenericMCS Bridge Swaps [NOT STARTED]

**Goal**: Swap `MCSProperties` → `GenericMCS` in the three bridge files, removing the
dead `open MCSProperties` line that shake does not model.

**Tasks**:
- [ ] #8 `Bimodal/Metalogic/Core/GenericMCSBridge.lean`: remove
      `public import ...MCSProperties`; add `public import ...GenericMCS`; **remove
      line 72 `open Cslib.Logic.Metalogic.MCSProperties`**; keep line 71
      `open ...GenericMCS`.
- [ ] #9 `Modal/Metalogic/GenericMCSBridge.lean`: same swap; **remove line 74
      `open ...MCSProperties`**; keep line 73 `open ...GenericMCS`.
- [ ] #10 `Temporal/Metalogic/GenericMCSBridge.lean`: same swap; **remove line 62
      `open ...MCSProperties`**; keep line 61 `open ...GenericMCS`.

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` - swap import + drop dead open
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - swap import + drop dead open
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` - swap import + drop dead open

**Verification**:
- `lake build` exits 0 with no `unknown namespace` errors (confirms the paired `open`
  removals landed correctly).

---

### Phase 4: Cslib.Init Removals (gated) [NOT STARTED]

**Goal**: Remove the six direct `import Cslib.Init` lines (plus the #3 import cascade),
gated on `checkInitImports` staying green.

**Tasks**:
- [ ] #1 `Foundations/Logic/Metalogic/DeductionCharacterization.lean`: remove
      `import Cslib.Init` (retains `public import ...GenericMCS`).
- [ ] #2 `Modal/Tableau/Saturation.lean`: remove `import Cslib.Init`; add
      `public import Cslib.Logics.Modal.Tableau.Rules`.
- [ ] #3 `Modal/Tableau/LoopInduction.lean`: remove `import Cslib.Init` and
      `public import ...Saturation`; add `public import Cslib.Logics.Modal.Basic` and
      `public import Batteries.Data.List.Basic`.
- [ ] #4 `Modal/Tableau/Soundness.lean`: remove `import Cslib.Init`.
- [ ] #5 `Temporal/Tableau/Rules.lean`: remove `import Cslib.Init`; add
      `public import Cslib.Foundations.Logic.Tableau.PropositionalRules`.
- [ ] #6 `Temporal/Tableau/Saturation.lean`: remove `import Cslib.Init`.
- [ ] Run `lake build` then `lake exe checkInitImports`.
- [ ] If any file regresses in `checkInitImports`, restore only that file's
      `import Cslib.Init -- shake: keep`.

**Timing**: 0.75 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean`
- `Cslib/Logics/Modal/Tableau/Saturation.lean`
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean`
- `Cslib/Logics/Modal/Tableau/Soundness.lean`
- `Cslib/Logics/Temporal/Tableau/Rules.lean`
- `Cslib/Logics/Temporal/Tableau/Saturation.lean`

**Verification**:
- `lake build` exits 0.
- `lake exe checkInitImports` exits 0 (authoritative gate for Init removals).

---

### Phase 5: Barrel & DenseMCS Edits [NOT STARTED]

**Goal**: Apply the remaining re-export edits that need downstream-build validation.

**Tasks**:
- [ ] #12 `.../CounterexampleElimination/Interface.lean`: remove
      `public import ...CounterexampleElimination.Elimination` (barrel still imports
      Structures + BurgessHelpers).
- [ ] #17 `Temporal/Metalogic/DenseMCS.lean`: remove
      `public import ...DeductionHelpers` (retains `...MCS` + `...ListHelpers`;
      DeductionHelpers reachable transitively via MCS).
- [ ] Run `lake build`; if a downstream consumer of the Interface barrel fails to find
      `Elimination`, add a direct `public import ...Elimination` in that consumer.

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean` - drop Elimination re-export
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - drop DeductionHelpers
- (contingency) any downstream consumer of the Interface barrel that needs a direct Elimination import

**Verification**:
- `lake build` exits 0, including all downstream consumers of the two barrels.

---

### Phase 6: Scoped Shake + Full CI Verification [NOT STARTED]

**Goal**: Confirm the 17 listed suggestions are resolved and the full CI gate passes.

**Tasks**:
- [ ] Re-run scoped `lake shake --add-public --keep-implied --keep-prefix <17 touched
      modules>` (use `--force` locally if FmpMeasure WIP still triggers the oleans check;
      canonical CI run needs a clean tree).
- [ ] Confirm **the 17 listed suggestions no longer appear**. Out-of-scope suggestions
      (Defs/Branch/Closure/SoundnessStep/TimeOrdering/MCS.lean etc.) may still print —
      that is expected and NOT a task-447 failure.
- [ ] Run the full CI gate: `lake build`, `lake test`, `lake exe checkInitImports`,
      `lake exe lint-style`.

**Timing**: 0.75 hours

**Depends on**: 5

**Files to modify**:
- None (verification only)

**Verification**:
- Scoped shake output no longer contains any of the 17 listed suggestions.
- `lake build` exits 0.
- `lake test` passes (CslibTests suite).
- `lake exe checkInitImports` exits 0.
- `lake exe lint-style` exits 0.

---

## Testing & Validation

- [ ] `lake build` green after each phase (2–5) and at final verification.
- [ ] `lake exe checkInitImports` green after Init removals (Phase 4) and at final gate.
- [ ] `lake test` passes at final gate.
- [ ] `lake exe lint-style` passes at final gate.
- [ ] Scoped shake confirms the 17 listed suggestions are resolved (Phase 6).
- [ ] No `sorry`, no new axioms introduced (pure import edits).

## Artifacts & Outputs

- 17 import-minimization edits across 18 files (16 primary + paired downstream targets).
- Optional contingency edits: `-- shake: keep` restore for any Init-regressing file;
  direct `Elimination` import in any Interface-barrel consumer that breaks.
- Green CI: build, test, checkInitImports, lint-style.

## Rollback/Contingency

- All edits are import-line changes; revert via `git checkout -- <file>` per file, or
  `git restore` the touched set, leaving the unrelated FmpMeasure WIP intact.
- Per-file fallbacks are built into the phases: restore `import Cslib.Init -- shake: keep`
  if `checkInitImports` regresses (Phase 4); add a direct `Elimination` import if a
  barrel consumer breaks (Phase 5).
- Because groups rebuild independently, a failure localizes to the current phase; revert
  only that phase's files and re-plan that group.
