# Research Report: Task 447 — Apply lake shake Import-Minimization Fixes

**Task:** 447 — apply_shake_import_minimization_fixes_tasks_321_406_431
**Session:** sess_1782886187_0ef015
**Date:** 2026-07-01
**Type:** cslib (import hygiene / dependency minimization)
**Status:** researched

## Executive Summary

I reproduced `lake shake --add-public --keep-implied --keep-prefix` on the touched
modules against the current (fully built) tree. **All 17 listed suggestions are
confirmed as current shake output.** The most important correction to the task's
framing:

- The task labels the six `import Cslib.Init` removals as **"false-positive
  candidates"** on the theory that `Cslib.Init` provides linters/tactics. **This
  theory does not hold**: `Cslib.Init`'s linters/tactics remain active via the
  file's *transitive* imports, and `checkInitImports` only requires a **transitive**
  import of `Cslib.Init` (see `scripts/CheckInitImports.lean`). shake genuinely and
  correctly flags the *direct* `import Cslib.Init` as redundant. **Recommended action
  is REMOVAL** (matching shake), gated on `lake exe checkInitImports` staying green.
  Do **not** add a `-- shake: keep` comment as the default; only fall back to keeping
  `import Cslib.Init` if `checkInitImports` fails for that specific file.

- The three **GenericMCS swaps have a hidden hazard shake does not model**: each
  bridge file contains `open Cslib.Logic.Metalogic.MCSProperties`. Removing the
  `MCSProperties` import turns this into an `unknown namespace` error. The `open`
  line must be **removed together with** the import swap.

- **Scope note:** shake currently reports *more* Init-removal (and other) suggestions
  than task 447 enumerates. The task scope is explicitly limited to the listed files.
  After edits, shake will **still** report the out-of-scope suggestions — verification
  must confirm *the 17 listed suggestions are resolved*, not that shake is fully clean.

Baseline CI: `lake build` green, `lake exe checkInitImports` green (EXIT 0).

## Environment Caveat (affects reproduction)

`Cslib/Logics/Modal/Tableau/FmpMeasure.lean` has **274 lines of uncommitted WIP** in
the working tree (unrelated to task 447; git status `M`). It builds, but shake's own
`lake build --no-build` sanity check reports *"there are out of date oleans"* because
of it, aborting before printing suggestions. To reproduce shake I ran a full
`lake build` then `lake shake --force ...`. The canonical CI invocation (no `--force`)
requires a clean, fully-built tree; the implementer should ensure the FmpMeasure WIP
is committed or otherwise not interfering, or use `--force` for local verification
only.

## How Cslib.Init works (mechanism)

- `Cslib/Init.lean` line 7: `module -- shake: keep-downstream, shake: keep-all`
  (added in PR #379, commit 25232322). `keep-all` preserves Init's own imports;
  `keep-downstream` is intended to preserve Init in downstream modules.
- **However**, all six flagged files use *plain* `import Cslib.Init` (not
  `public import`). Codebase convention is split: **115** files use `import
  Cslib.Init`, **44** use `public import Cslib.Init`. shake continues to flag the
  plain (private, non-re-exporting) direct import when Init is already reachable
  transitively.
- `scripts/CheckInitImports.lean` computes `env.importGraph.transitiveClosure` and
  errors only if a `Cslib.*` module does **not** transitively contain `Cslib.Init`
  (exceptions: `Cslib.Foundations.Lint.Basic`, `Cslib.Init`). Therefore a direct Init
  import is unnecessary whenever another kept import supplies Init transitively —
  exactly what shake detects.
- **Consequence:** removing `import Cslib.Init` is safe **iff** the file retains at
  least one import whose transitive closure includes `Cslib.Init`. All six files
  retain `public import Cslib.*` lines that do. The decisive gate is re-running
  `lake exe checkInitImports` after removal.

## Per-file verdict table

Legend: **G** = genuine (apply as listed); **G!** = genuine but requires an extra
correction shake did not emit; verdict "remove/add" mirror confirmed shake output.

| # | File | Suggested edit (confirmed by shake) | Verdict | Recommended action |
|---|------|--------------------------------------|---------|--------------------|
| 1 | `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` | remove `import Cslib.Init` | **G** (not a false positive) | Remove; retains `public import ...GenericMCS` (transitively supplies Init). Verify `checkInitImports`. |
| 2 | `Cslib/Logics/Modal/Tableau/Saturation.lean` | remove `import Cslib.Init`; add `public import Cslib.Logics.Modal.Tableau.Rules` | **G** | Remove Init + add Rules. Retains `public import ...Closure`. Verify `checkInitImports`. |
| 3 | `Cslib/Logics/Modal/Tableau/LoopInduction.lean` | remove `import Cslib.Init`, remove `public import ...Saturation`; add `public import Cslib.Logics.Modal.Basic`, `public import Batteries.Data.List.Basic` | **G** | Apply all four. `Cslib.Logics.Modal.Basic` uses `public import Cslib.Init` (a 44-set root), so Init stays transitive. Verify build + `checkInitImports`. |
| 4 | `Cslib/Logics/Modal/Tableau/Soundness.lean` | remove `import Cslib.Init` | **G** | Remove; retains `public import ...Saturation/SoundnessStep/LoopInduction`. Verify `checkInitImports`. |
| 5 | `Cslib/Logics/Temporal/Tableau/Rules.lean` | remove `import Cslib.Init`; add `public import Cslib.Foundations.Logic.Tableau.PropositionalRules` | **G** | Remove Init + add PropositionalRules. Verify `checkInitImports`. |
| 6 | `Cslib/Logics/Temporal/Tableau/Saturation.lean` | remove `import Cslib.Init` | **G** | Remove; retains `public import ...Closure`. Verify `checkInitImports`. |
| 7 | `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` | remove `public import Mathlib.Data.Multiset.Basic` | **G** | Remove; retains `public import Mathlib.Data.Multiset.MapFold` (transitively provides Basic). Verify build. |
| 8 | `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` | remove `public import ...MCSProperties`; add `public import ...GenericMCS` | **G!** | Swap import **and remove line 72 `open Cslib.Logic.Metalogic.MCSProperties`** (would become `unknown namespace`). Keep line 71 `open ...GenericMCS`. Build to verify. |
| 9 | `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` | remove `...MCSProperties`; add `...GenericMCS` | **G!** | Same as #8; remove **line 74 `open ...MCSProperties`**, keep line 73 `open ...GenericMCS`. Build to verify. |
| 10 | `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` | remove `...MCSProperties`; add `...GenericMCS` | **G!** | Same as #8; remove **line 62 `open ...MCSProperties`**, keep line 61 `open ...GenericMCS`. Build to verify. |
| 11 | `.../CounterexampleElimination/BurgessHelpers.lean` | remove `public import Mathlib.Data.Finset.Max`, `public import Mathlib.Tactic.Linarith`; add `public import Mathlib.Tactic.NormNum` | **G** | Apply. (`Interface.lean` independently retains Finset.Max/Linarith — not flagged there.) Build to verify. |
| 12 | `.../CounterexampleElimination/Interface.lean` | remove `public import ...CounterexampleElimination.Elimination` | **G** | Remove the Elimination re-export. Interface still imports Structures + BurgessHelpers. **Verify the barrel and its downstream consumers still build** (any consumer needing `Elimination` must import it directly). |
| 13 | `.../Temporal/.../CounterexampleElimination/Structures.lean` | remove `public import Mathlib.Logic.Encodable.Basic` | **G** (paired) | Remove. Confirmed: Structures body has **no** `Encodable` use. |
| 14 | `.../Temporal/.../CounterexampleElimination/Elimination.lean` | add `public import Mathlib.Logic.Encodable.Basic` | **G** (paired w/ #13) | Add. Confirmed: Elimination line 130 declares `instance : Encodable PotentialCounterexampleKind`. Elimination imports Structures, so this is a downstream move. |
| 15 | `Cslib/Logics/LTL/Semantics/GNBA/Closure.lean` | remove `public import ...Satisfies`, `public import Mathlib.Data.Set.Finite.Powerset`, `public import Mathlib.Data.Set.Finite.Lattice`; add `public import Cslib.Logics.LTL.Syntax.Formula` | **G** (paired) | Apply. Closure retains `Mathlib.Data.Set.Finite.Basic`. Build to verify. |
| 16 | `Cslib/Logics/LTL/Semantics/GNBA/Atoms.lean` | add `public import Cslib.Logics.LTL.Semantics.Satisfies` | **G** (paired w/ #15) | Add. Atoms imports Closure, so `Satisfies` moves downstream to where it is used. Build to verify. |
| 17 | `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` | remove `public import ...DeductionHelpers` | **G** | Remove; DenseMCS retains `public import ...MCS` + `...ListHelpers` (DeductionHelpers reachable transitively via MCS). Build to verify. |

## Confirmed module relationships

- **MCSProperties re-exports GenericMCS**: `MCSProperties.lean` line 9
  `public import ...GenericMCS`; `GenericMCS.lean` imports only `ListDeduction` +
  `Consistency`. So swapping bridge imports from MCSProperties → GenericMCS narrows
  to the actually-used base module. The bridges' `open ...MCSProperties` lines are
  the only remaining reference to the MCSProperties *namespace* and are dead once the
  import is removed (shake reports only GenericMCS constants are used).
- **checkInitImports** = transitive closure requirement, not direct-import
  requirement (see mechanism section).

## Scope discrepancy (important for verification criteria)

shake, run on the touched set today, additionally reports (NOT in task 447 scope —
do **not** apply):
- `Modal/Tableau/Defs.lean`, `Modal/Tableau/Branch.lean`, `Modal/Tableau/SoundnessStep.lean`, `Modal/Tableau/Closure.lean` (Init removals / Rules→Defs / add SignedFormula)
- `Temporal/Tableau/Defs.lean`, `Temporal/Tableau/Branch.lean`, `Temporal/Tableau/Closure.lean` (Init removals)
- `Temporal/Tableau/TimeOrdering.lean` (Int.Order.Basic → Int.Notation + Tactic.ToDual)
- `Modal/Tableau/Rules.lean` (add PropositionalRules)
- `Temporal/Metalogic/MCS.lean` (add MCSProperties) — loosely related to #17.

**Verification criterion:** after applying the 17 listed edits, re-run shake and
confirm that *the 17 listed suggestions no longer appear*. shake will still print the
out-of-scope suggestions above; that is expected and is NOT a task-447 failure.

## Commands (verification pipeline)

Scoped shake invocation (canonical; run on a clean, fully-built tree):

```
lake build
lake shake --add-public --keep-implied --keep-prefix \
  Cslib.Foundations.Logic.Metalogic.DeductionCharacterization \
  Cslib.Logics.Modal.Tableau.Saturation Cslib.Logics.Modal.Tableau.LoopInduction \
  Cslib.Logics.Modal.Tableau.Soundness Cslib.Logics.Temporal.Tableau.Rules \
  Cslib.Logics.Temporal.Tableau.Saturation \
  Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension \
  Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge \
  Cslib.Logics.Modal.Metalogic.GenericMCSBridge \
  Cslib.Logics.Temporal.Metalogic.GenericMCSBridge \
  Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.CounterexampleElimination.BurgessHelpers \
  Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.CounterexampleElimination.Interface \
  Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.Structures \
  Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.Elimination \
  Cslib.Logics.LTL.Semantics.GNBA.Closure Cslib.Logics.LTL.Semantics.GNBA.Atoms \
  Cslib.Logics.Temporal.Metalogic.DenseMCS
```

Full CI gate (all must pass):

```
lake build
lake test
lake exe checkInitImports
lake exe lint-style
```

`-- shake: keep` fallback syntax (only if `checkInitImports` fails after an Init
removal): `import Cslib.Init -- shake: keep`.

## Zero-debt / hazards for the implementer

- No `sorry`, no new axioms, no deferral involved — pure import edits.
- **Build after every file** (especially #8–#10 for the dangling `open`, and #12 for
  the barrel). If a build breaks, the edit interacts with an `open`/re-export that
  shake did not model; fix by removing the dead `open` (#8–#10) or, for #12, by
  adding a direct `Elimination` import in the affected downstream consumer.
- After Init removals (#1–#6, and #3's cascade), `lake exe checkInitImports` is the
  authoritative gate. If a specific file regresses, keep its `import Cslib.Init`
  (optionally with `-- shake: keep`) rather than forcing the removal.
- Recommended edit order: independent leaf edits first (#7, #11, #13/#14, #15/#16),
  then bridges (#8–#10), then Init removals (#1–#6), then #12 and #17; rebuild
  between groups.
