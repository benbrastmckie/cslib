# Task 517 Phase 7 Summary — `primeLemma` mainline transcription

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Plan**: plans/12_wellfounded-zorn-oldlabel-reconstruction.md, Phase 7
- **Status**: [COMPLETED]

## What was done

Transcribed the now-sorry-free `primeLemma` and its **actual** dependency closure (established
by Phase 6) from `probes/chain-union-reflection-probe.lean` (lines 70-1706, namespace-open
through the end of `primeLemma`) into a new mainline file:

`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/PrimeLemma.lean` (1709 lines)

Content landed: `swapFn`/`NIK.swap_relabel`/`NIK.freshWitness_transport` (two-label-swap
relabeling), `substFn`/`NIK.relabelFresh` (one-directional relabeling), `NIK.oldLabelTransport`/
`NIK.diaWitnessTransportOld` (the "old label" transport corollaries), `GChain`/
`TClosure.reflectChain`/`NIK.reflectChain` (the chain-union reflection theorem, Simpson's elided
"easily seen" step), `ChainCtx`/`ChainCtx.deriv_reflect`/`ChainCtx.chain_closure`, `primeC`/
`primeC_mem_base`/`primeC_chain_bddAbove`/`primeC_exists_maximal` (the Zorn poset and
`zorn_le₀` application), the five `TPrime` clause theorems (`clModel_of_maximal`,
`deductiveClosure_of_maximal`, `consistency_of_maximal`, `disjunction_of_maximal`,
`diamond_of_maximal` via `dwitness_mem_of_maximal`/`NIK.subst`/`NIK.subst_aux`), and `primeLemma`
itself.

## Scope deviation (resolved by the orchestrator continuation brief before dispatch)

**The FLO apparatus (`Stage`/`FloSeq`/`FLO`/`flo_succ`/`flo_limit`/`primeC'_exists_maximal`/
`flo_oldlabel_transport`) was NOT transcribed to mainline.** Phase 6 established that `primeLemma`
routes through `primeC_exists_maximal` (plain `zorn_le₀`), not the FLO-carrying reconstruction;
the FLO machinery is confirmed non-load-bearing for `primeLemma` and still carries 2 open,
documented, out-of-scope sorries (`flo_succ`'s superseded `redundantEdge` branch;
`primeC'_exists_maximal`'s `Maximal`-conjunct half). Since mainline transcription must be
zero-debt, transcribing FLO would either introduce sorry-debt into `Cslib/` or require closing
those 2 sorries — out of this phase's scope. The FLO apparatus remains in `probes/
chain-union-reflection-probe.lean`, untouched and preserved verbatim, as correct scaffolding
for a possible future task.

This is annotated on the plan's Phase 7 Task 7.1/7.2 checklist items per the deviation
convention.

## Verification

- Scoped `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.PrimeLemma`: green.
- `lean_verify Cslib.Logic.Modal.Labelled.primeLemma`:
  `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}` — no `sorryAx`.
- `lean_verify Cslib.Logic.Modal.Labelled.dwitness_mem_of_maximal` (the diamond-clause
  dependency closed in Phase 6): same clean axiom footprint.
- Zero `sorry` (all "sorry" occurrences in the file are prose inside doc comments describing
  Phase 6's history and the FLO apparatus's remaining sorries, not `sorry` tactics).
- Zero vacuous definitions, zero new `axiom` declarations.
- Full CSLib CI pipeline run:
  1. `lake exe checkInitImports`: pass (file imports `Cslib.Init` transitively via `Context.lean`
     -> `Deduction.lean` -> `Syntax.lean` -> `Basic.lean`).
  2. `lake lint`: `-- Linting passed for Cslib.` (zero warnings, including the 7 prevention
     categories, for the new file).
  3. `lake exe lint-style`: zero warnings.
  4. `lake shake --add-public --keep-implied --keep-prefix`: no suggestions for the new file
     (imports already minimal — `Context.lean`, `Mathlib.Order.SetNotation`,
     `Mathlib.Order.Zorn`).
  5. `lake exe mk_all --module`: `Cslib.lean` updated with the new
     `public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.PrimeLemma` line.
  6. `lake test`: green (`CslibTests` suite, 9235/9235 jobs).
  7. Full `lake build`: green (3243/3243 jobs) — guardrail modules (`Context.lean`,
     `Deduction.lean`, `Syntax.lean`, `CS5Canonical.lean`) unregressed.

## Style fixes applied during transcription (beyond mechanical copy)

- `Set.Infinite.diff` -> `Set.Infinite.sdiff` (deprecated rename).
- `Set.diff_eq_empty` -> `Set.sdiff_eq_empty` (deprecated rename).
- Wrapped 4 lines exceeding the 100-character style limit (2 in tactic proofs, 2 in doc-comment
  prose; no semantic change).
- Added `@[expose] public section` (module-system exposure marker) matching the convention used
  by `Context.lean` and the other files in `Constructive/Labelled/`.
- Kept the file-level `open Classical` (rather than scoping it per-declaration): this pattern
  triggers a non-blocking `linter.style.openClassical` style warning but matches existing
  precedent in 7 other mainline CSLib files (e.g. `Separation/Eliminations.lean`,
  `BXCanonical/Filtration/DefectChain.lean`); the classical-decidability need is pervasive
  across the file's `by_cases`/`List.toFinset` usages (label equality has no assumed
  `DecidableEq`), so per-declaration `open Classical in`/`classical` scoping would require
  touching ~10+ separate declarations for a warning-only lint with no correctness benefit,
  which would deviate materially from "mechanical transcription of already-green content."

## Next phase

Phase 8 (canonical model + truth lemma) depends on Phase 7's `primeLemma`. Before starting,
Phase 8 must confirm the flagged "T-Comp graph completion" question (original Phase 5,
carried from v4) — whether the raw relation `primeLemma` outputs is consumed directly by the
canonical model, making T-Comp unneeded. This confirmation is explicitly deferred to Phase 8,
per the dispatch brief's instruction not to build T-Comp material now.
