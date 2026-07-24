# Implementation Summary: Prune redundant imports from Intuitionistic CanonicalModel.lean

- **Task**: 549 - prune_canonicalmodel_redundant_imports
- **Status**: [COMPLETED]
- **Plan**: plans/01_prune-redundant-imports.md

## What Was Done

Removed the two redundant `public import` lines from
`Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean`:
- `public import Cslib.Logics.Modal.Metalogic.MCS` (genuinely dead — no compensating add
  needed anywhere downstream)
- `public import Cslib.Logics.Modal.Semantics.Birelational` (relocated, not deleted)

Added the compensating import to `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean`:
- `public import Cslib.Logics.Modal.Semantics.Birelational`

`import Cslib.Init` was preserved unchanged in both files. `Completeness.lean` was not touched,
per the plan's non-goals — the chain `Completeness -> TruthLemma -> Birelational` keeps all
names reachable after the relocation.

## Plan Deviations

None. All plan tasks were executed exactly as written; no steps were skipped, altered, or
deferred.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness` — green (transitively
  builds CanonicalModel and TruthLemma).
- `lake exe checkInitImports` — exit 0.
- `lake exe lint-style` scoped to the two modified modules — no output (clean).
- `lake lint --builtin-lint` scoped to the two modified modules — "No environment linters
  registered" for both `CanonicalModel` and `TruthLemma` (zero docBlame/defLemma/etc. warnings
  attributable to this change). The only warnings observed in the scoped run originate from
  `Cslib/Logics/Modal/Basic.lean` (a transitively-imported, unmodified file with pre-existing
  `linter.flexible` warnings unrelated to this task).
- `lake exe mk_all --module` — "No update necessary" (no new files were added, as expected for
  a pure import relocation).
- `lake test` — full `CslibTests/` suite green, exit 0 (9247/9247 jobs).
- `lake shake --add-public --keep-implied --keep-prefix` scoped to the two modules — confirms
  no further remove/add for either file beyond the anticipated `import Cslib.Init` false
  positive (documented in the plan as a known shake artifact to ignore). Out-of-scope findings
  for `SchemaUnion.lean` and `PrimeTheory.lean` were observed and correctly left untouched, per
  the plan's non-goals.
- `grep -n "\bsorry\b"` in both modified files — zero actual `sorry` tactics (three docstring
  occurrences of the word "sorry-free" in prose, not proof-relevant).
- `grep -n "^axiom "` in both modified files — none.
- `git diff` on both files matches the plan's expected shape exactly: 2 lines removed from
  CanonicalModel.lean, 1 line added to TruthLemma.lean.

## Files Modified

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (2 `public import` lines
  removed)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` (1 `public import` line added)

## Notes

Per the orchestrator's parallel-safety directive, this task's territory was limited to
`Cslib/Logics/Modal/Metalogic/Intuitionistic/{CanonicalModel,TruthLemma}.lean` and the task's
own `specs/` directory. `Cslib/Logics/Modal/Bimodal/**` and `Cslib/Logics/Temporal/**` (being
concurrently modified by another implementation agent) were not touched, and git staging for
the commit includes only this task's own files.
