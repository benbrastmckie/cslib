# Task 317 — Plan 04 Phase 1 Summary: `Sfor`-Containment Loop-Check Design

## Status: COMPLETED (GO verdict)

Phase 1 of `plans/04_sfor-dedup-fuel-sufficiency.md` is a design-only gate (R1): produce a
precise, code-grounded specification of the Garg–Genovese–Negri `Sfor`-containment loop-check
that will make the existing `2^(2·complexity+2)` fuel bound adequate for closing sorry 985
(B2, fuel=0 case) in `Scheme.lean`. No proof code was written and no sorry was closed or
introduced this phase, per the plan's own scope.

## What Was Done

1. Confirmed GREEN baseline: last commit touching `Expansion.lean`/`Rules.lean`/`Scheme.lean`
   was `26508fe9`; scoped rebuild of the `Expansion` module passed cleanly before any edit.
2. Read the actual primitives (windowed reads only): `intExpandBranches`/`go`
   (`Expansion.lean:192-258`), `intFImpRule`/`propagatePersistence`/`posFormulasAt`
   (`Rules.lean:126-159`), `isAccessible`/`IEdges` (`Rules.lean:80-102`), and the call chain
   `intApplyRuleFull` (`Rules.lean:245-268`) -> `intStepBranch` (`Expansion.lean:150-157`) ->
   `go`.
3. Stated the check precisely against these primitives (see docstring in
   `Expansion.lean` on `intFImpReuseWitness?`).
4. Ran the R1 STOP-and-escalate gate: **GO** — the check needs no new persistent field,
   no new structure, and (crucially, beyond what the plan asked to check) **no signature
   change to `intFImpRule`, `intApplyRuleFull`, or `intStepBranch`**, because `go` already
   carries `bPers : IBranch Atom` and `edges : IEdges` in its own parameter scope at the exact
   point (the `.linearResult newForms nw' (some newEdge)` branch) where the reuse decision
   must be made.
5. Recorded the settled design as a docstring + trivial `none`-returning stub
   `intFImpReuseWitness?` in `Expansion.lean`, citing `GargGenoveseNegri2012` (BibKey addition
   deferred to Phase 6 of this same plan, as originally scoped) and a "why not G4ip weight"
   note referencing the `R1-measure` blocker from the abandoned plan 03 approach.
6. Committed only the touched files (`Expansion.lean`, the plan, the handoff, and the phase
   progress file) at `272ab4f7`.

## Key Finding (Beyond the Plan's Literal Ask)

The plan's Phase 2 goal statement mentions "without breaking any Preserved Asset or the
public `openBranch_countermodel` signature" — this phase's investigation surfaces the
concrete reason that constraint is easy to satisfy: **the reuse decision can live entirely in
`go`'s own body**, consuming `newForms`/`newEdge` that `intStepBranch` already returns, with
zero changes to `intFImpRule`/`intApplyRuleFull`/`intStepBranch` signatures. This significantly
de-risks Phase 2, since none of the ~15 `intApplyRuleFull`/`intStepBranch`-shaped lemmas in
`Scheme.lean`/`Soundness.lean` (e.g. `intApplyRuleFull_some_info`, `intStepBranch_some_exists`,
the soundness case split at `Soundness.lean:1270+`) need to be touched or re-proved — they
still characterize the same `intApplyRuleFull`/`intStepBranch` as today. Phase 2 only needs to
add logic to `go` and prove new lemmas about the *new* branch, not modify existing ones.

## Verification

- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion`: GREEN, 0 errors.
- `grep -n "\bsorry\b" Expansion.lean`: 0 hits (no sorry introduced).
- No vacuous definitions introduced (`intFImpReuseWitness?` is a real stub returning `none`,
  documented as not-yet-implemented, not a `def X := True`-style placeholder).
- `lake exe checkInitImports` could not be run to completion in this scoped dispatch (missing
  `.olean` for an unrelated module, `Minimal/Soundness.lean`, likely from concurrent
  in-progress work in the working tree at dispatch time); manually verified
  `Expansion.lean` line 9 has `import Cslib.Init`, satisfying the actual requirement this
  check enforces. Full multi-module CI pipeline verification is deferred to the plan's final
  wrap-up after all 6 phases complete.

## Plan Deviations

None. The phase was executed exactly as scoped: design docstring + stub only, no proof
obligations closed, `Expansion.lean` (design comment/stub) as the only Lean file touched.

## Next Steps

Phase 2 ("Implement the `Sfor`-containment loop-check") implements
`intFImpReuseWitness?` for real — the search over `(bPers.map (·.label)).eraseDups` filtered
by `isAccessible`/containment/obligation-open, per the docstring — and wires the reuse branch
into `go`'s `.linearResult newForms nw' (some newEdge)` case.

## Files Touched

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (design docstring + stub)
- `specs/317_propositional_tableau_completeness/plans/04_sfor-dedup-fuel-sufficiency.md`
  (Phase 1 checklist completed, verdict recorded)
- `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json`
- `specs/317_propositional_tableau_completeness/progress/phase-1-progress-plan04.json`

Commit: `272ab4f7` — "task 317 phase 1: Sfor-containment dedup design"
