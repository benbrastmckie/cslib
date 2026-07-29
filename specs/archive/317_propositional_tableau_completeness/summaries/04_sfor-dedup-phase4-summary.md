# Task 317, Plan 04, Phase 4: Soundness + Green-Build Regression Audit

## Status: COMPLETED (verdict: minimally-fixed; task-316 coordination flagged)

## What This Phase Did

Phase 2's `Sfor`-containment dedup (commit `619acd3a`) made `intExpandBranches`'s inner `go`
loop sometimes reuse an accessible ancestor world for the `F(φ → ψ)` world-creating rule instead
of always creating a fresh one. This phase audited the calculus SOUNDNESS proof
(`Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`, task 316 territory) for
regressions caused by that change, and made the minimal necessary fix.

## Audit Finding

A scoped rebuild of `Soundness.lean` before any fix showed exactly 4 errors, all inside one
lemma: `intExpandBranches_closed_unsat` (application type mismatches at the `linearResult ...
(some newEdge)` case, unsolved goals at the two `ih`/`absurd` application sites). Every other
soundness lemma (`intRule_preserves_sat`, `applyPersistenceFixpoint_sat`,
`applyAllTImpRules_sat`, the `monotoneEdges_*`/`freshAbove_*` helpers) is rule-level — it
reasons about `intApplyRuleFull`/`intFImpRule`'s semantics, which the dedup does not change —
and was confirmed untouched.

`intExpandBranches_closed_unsat` is the one exception: its induction walks `go`'s recursion
structure directly, and its `linearResult newForms nw' (some newEdge)` case assumed every
world-creating step strictly grows the branch (`Branch.extendMany bPers newForms` plus a new
edge). Post-dedup, `go`'s reuse path (`intFImpReuseWitness? = some x`) instead recurses on
`bPers` unchanged — a case the induction did not cover.

## The Fix

In `intExpandBranches_closed_unsat`'s `linearResult` case, hoisted an explicit
`rcases hnE : newEdge with _ | e_val` and, within the `some e_val` sub-case,
`rcases hwit : intFImpReuseWitness? bPers edges newForms e_val with _ | x` — mirroring exactly
the case structure `go` itself now has (previously this was implicit via a single generic
`edges' := match newEdge with ...` let-binding, which no longer matches `go`'s actual
case-dependent recursive-call shape). The `none` and `some e_val`/`witness = none` (create)
sub-cases reuse the pre-existing proof machinery (`intRule_preserves_sat`,
`freshAbove_world_create`, `monotoneEdges_update`, etc.) essentially verbatim, just re-nested.

The new `witness = some x` (reuse) sub-case is proved directly and is much simpler than the
create case: the branch fed to the recursive `intExpandBranches` call is literally `bPers`
unchanged (no `extendMany`, no new edge, world-label counter `nwH` unchanged), so
`applyPersistenceFixpoint_sat` already gives `hsat_pers : intBranchSatisfied val botForces wo
bPers`, and the fuel-induction hypothesis `ih` applies directly to `(bPers, edgesP)` — no
`intRule_preserves_sat`, no `worldOf'` extension, no new-world freshness lemma needed. This
matches exactly what plan 04 phase 4 anticipated: "the IH applies directly to the same branch...
no new satisfiability obligation arises."

## Verification

- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` → Build completed
  successfully (660 jobs).
- `grep -n "\bsorry\b" Soundness.lean` → 0 occurrences (before and after).
- `mcp__lean-lsp__lean_verify` on `Cslib.Logic.PL.intExpandBranches_closed_unsat` → axioms:
  `["propext", "Classical.choice", "Quot.sound"]` (the standard three; no new axioms).

## Plan Deviations

- **Diff size larger than estimated**: the plan estimated ~50-150 lines; the actual diff is 327
  insertions / 156 deletions (net +171 lines). This is because the `newEdge`/witness case split
  had to be duplicated across both pre-existing induction sub-branches (`bp = bh` and `bp ∈ bt`),
  matching the pre-existing proof's own style of duplicating the analogous `none`/`create` logic
  across those two branches. No new lemmas were added, no signatures changed, and the fix stayed
  confined to one lemma's proof body — judged to remain a "localized case addition" per the
  plan's own framing, not a re-architecture, so escalation to `[BLOCKED]` was not warranted
  despite exceeding the line estimate. This judgment call is recorded explicitly in
  `progress/phase-4-progress.json`.
- **Task-316 territory edited**: `Soundness.lean` belongs to task 316. This edit is flagged
  prominently in the plan checklist, the progress file, and the shared
  `.orchestrator-handoff.json` (`phase4` sub-key) for task-316 review.

## Files Touched

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (edited, committed alone in
  `8a5c0250`)
- `specs/317_propositional_tableau_completeness/plans/04_sfor-dedup-fuel-sufficiency.md` (Phase 4
  marked `[COMPLETED]`, checklist checked off, committed in `3b30f2d3`)
- `specs/317_propositional_tableau_completeness/progress/phase-4-progress.json` (new, committed
  in `f9111302`)
- `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json` (additive `phase4`
  sub-key only, committed in `8bff4afd`)

## Commits

1. `8a5c0250` — `task 317 phase 4: minimal Soundness.lean fix for dedup (coordinates task 316)`
2. `f9111302` — `task 317 phase 4: progress record for Soundness.lean dedup fix`
3. `3b30f2d3` — `task 317 phase 4: mark Phase 4 COMPLETED in plan (Soundness.lean dedup fix)`
4. `8bff4afd` — `task 317 phase 4: add phase4 sub-key to shared orchestrator handoff`

## sorry_inventory

None in `Soundness.lean`. (Repo-wide baseline sorries, e.g. `Scheme.lean:330,985`,
`Completeness.lean:113`, `Minimal/Completeness.lean:110`, are pre-existing and out of this
phase's scope — see Phase 2/3's own handoff records.)

## Relationship to Phase 3's Blocker

Phase 3 (running concurrently) found an independent, orthogonal blocker: `intFImpReuseWitness?`
does not guarantee the explicit `F(ψ)@x` Hintikka entry that `Scheme.lean`'s
`IBranchSaturation.sat_fimp`/`sfSatisfied` require. That is a semantic gap in the countermodel
construction, unrelated to this phase's fix. `Soundness.lean`'s fix only needed a *structural*
case addition (reasoning about `intBranchSatisfied`, not about Hintikka/countermodel conditions),
and does not resolve or depend on Phase 3's blocker.
