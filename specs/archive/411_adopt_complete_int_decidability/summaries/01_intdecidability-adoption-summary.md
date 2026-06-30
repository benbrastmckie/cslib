- **Task**: 411 — adopt_complete_int_decidability (parent 370)
- **Status**: [IMPLEMENTED]
- **Date**: 2026-06-29
- **Plan**: plans/01_curated-intdecidability-adoption.md
- **Phase 3 triggered**: NO

## What Was Done

Adopted the complete, sorry-free `IntDecidability.lean` from branch `refactor/prop_logic` (tasks
415/416) onto `main` via a curated single-file swap. The swap delivers
`instDecidableDerivableIntPropAxiom'` — the FMP-based decidability instance that main's
prior 272-line witness-stub lacked.

## Phase Results

### Phase 1: Curated single-file swap [COMPLETED]

```bash
git show refactor/prop_logic:Cslib/Logics/Propositional/Metalogic/IntDecidability.lean \
  > Cslib/Logics/Propositional/Metalogic/IntDecidability.lean
```

- File: 436 lines (matches expected).
- Key identifier present: `instDecidableDerivableIntPropAxiom'` at line 430.
- `sorry` occurrences: lines 16 and 29 only — both prose: "sorry-free" in module header. Zero proof-body sorries.
- `Cslib.lean` import: `public import Cslib.Logics.Propositional.Metalogic.IntDecidability` — already present, no change needed.
- `GrindLint` skip: `#grind_lint skip Cslib.Logic.PL.IntFinWorld.mk.sizeOf_spec` — already present.
- `git diff --name-only HEAD` (task-411 scope): only `IntDecidability.lean` among tracked task-411 files.

### Phase 2: Build-verify gate [COMPLETED]

#### lake build (scoped)

```
⚠ [752/752] Built Cslib.Logics.Propositional.Metalogic.IntDecidability (889ms)
Build completed successfully (752 jobs).
```
Three style warnings (extra space in structure alignment, two unused-variable name bindings) —
all pre-existing in the branch's file, none are errors.

#### lake build (full repo-wide)

```
Build completed successfully (3156 jobs).
```
Pre-existing warnings in `Tableau/Classical/Completeness.lean`,
`Tableau/Minimal/Completeness.lean` — untouched, unchanged.

#### lake exe checkInitImports

No output (CLEAN).

#### lake lint

55 pre-existing errors in other files (GenericMCSBridge.lean, CutElimination.lean).
**Zero errors in IntDecidability.lean.**

#### lake exe lint-style

No output (CLEAN).

#### lake shake --add-public --keep-implied --keep-prefix

Pre-existing `remove #[import Cslib.Init]` suggestion applies to 20+ files system-wide
(including IntDecidability.lean). This is a known tension between `lake shake` and
`checkInitImports` across the entire project, not introduced by this change.

#### lake test

EXIT_CODE=0 (all tests pass).

#### #print axioms instDecidableDerivableIntPropAxiom' (lean_verify)

```json
{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[{"line":56,"pattern":"local instance"}]}
```

**CLEAN: ONLY `propext`, `Classical.choice`, `Quot.sound`. NO `sorryAx`.**

#### Pre-existing sorries confirmed untouched

- `Tableau/Minimal/Completeness.lean`: 5 sorries (unchanged).
- `Tableau/Intuitionistic/Completeness.lean`: sorries present (unchanged).
- `Tableau/Intuitionistic/Scheme.lean`: sorries present (unchanged).

### Phase 3: IntLindenbaum-drift contingency

**NOT TRIGGERED.** The build passed without any missing/renamed references from IntLindenbaum
or IntStrongCompleteness. Report 02's static analysis prediction (main's `IntStrongCompleteness`
is a superset of the branch's API) held empirically.

## Task-Number Collision Note

**IMPORTANT for future reference**: The branch `refactor/prop_logic` has a task-number fork
collision at 411. `main` task 411 = this adoption task (`adopt_complete_int_decidability`).
`refactor/prop_logic` task 411 = `dma_concat_closure` (an unrelated DMA automata-concat task).
The `IntDecidability` work on the branch was done under tasks 415/416, not 411. Any future
attempt to "merge task 411 from the branch" would land automata-concat work, NOT IntDecidability.
This adoption used a curated `git show refactor/prop_logic:path > local_path` file swap, not
`git merge`.

## Plan Deviations

None. The implementation proceeded exactly as planned:
- Phase 1 completed (single-file swap).
- Phase 2 passed (CI pipeline GREEN, axioms clean).
- Phase 3 NOT triggered (build was green without contingency backports).

## Files Changed

| File | Change |
|------|--------|
| `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` | Replaced: 272-line witness stub → 436-line sorry-free FMP + decidability instance |

## Downstream Impact

- Unblocks **task 421** (Min-side FMP) and **task 422** (route reconciliation), which depend on
  `instDecidableDerivableIntPropAxiom'` being present on main.
- Tableau-route sorries remain task 317's obligation (unchanged).
- Parent task 370 Int-side is now complete.
