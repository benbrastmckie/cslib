# Handoff: Phase 7 blocked — Gap 1's closure route was removed by the ancestor-blocking repair

- **Plan**: plans/14_fuel-materialization-repair.md, Phase 7 (`truthLemma` T-imp discharge)
- **Status**: `[BLOCKED]`
- **Progress file**: none created (blocker identified before any proof-state work began; see
  Immediate Next Action)

## Immediate Next Action

Do **not** re-attempt Phase 7's task list as written — its first task depends on a mechanism
that has been deliberately removed from `Expansion.lean`. Before any further `Scheme.lean`-side
attempt at the T-imp case, a dedicated calculus investigation is needed (see "Remaining Goals"
below). Read the "GAP 1 UPDATE" paragraph of the STOP-gate note directly above `truthLemma` in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` first — it contains the full,
current analysis and supersedes the plan's Phase 7 task-list wording.

## Current State

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`: documentation-only changes
  this dispatch. The STOP-gate note above `truthLemma` gained a "GAP 1 UPDATE" paragraph (with
  "What survives" and "Recommendation for continuation" sub-paragraphs); the inline comment
  directly above the T-imp `sorry` was updated to match. **No proof code changed.** The `sorry`
  at the T-imp case (currently line 602; re-grep, lines drift) is untouched — same statement,
  same location, same content as at Phase 6's exit.
- `specs/317_propositional_tableau_completeness/plans/14_fuel-materialization-repair.md`: Phase
  7's heading changed `[IN PROGRESS] → [BLOCKED]`; a `#### Blocker` subsection was appended
  documenting what was tried and why it cannot be completed as written.
- Scoped build (`lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`) is green;
  `lean_verify` on `openBranch_countermodel` shows the same axiom profile as Phase 6's exit
  (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx` — the `sorryAx` traced only to the
  T-imp sorry, unchanged). Repo-subtree bare-sorry census: still 4 (T-imp, DP-2, DP-3, DP-4) —
  unchanged from Phase 6's exit, since nothing was discharged.

## Key Decisions Made

1. **Confirmed, not merely suspected, that Phase 7's premise is false.** Verified by direct
   `git show a70187dd` diff inspection: the `applyAllTImpRules` "Deliverable 6" self-copy of
   `T(φ→ψ)` to every accessible world was deleted by the ancestor-blocking calculus repair, and
   that commit's own docstring declares the resulting gap ("Gap 1", `sat_timp` at accessible
   worlds) explicitly out of scope for that repair.
2. **Did not attempt to re-add the removed mechanism.** `Expansion.lean` is out of this phase's
   territory, and unilaterally reversing a settled, measured, already-landed sibling-task design
   decision is not a call a single `Scheme.lean`-scoped dispatch should make.
3. **Identified a genuinely surviving, provable fact** (documented in the STOP-gate note) that is
   *stronger* than the removed mechanism in one respect — `applyAllTImpRules`'s ψ-consequence
   propagation still gives `T(φ)@w'∈b → T(ψ)@w'∈b` at any accessible `w'`, sourced from `w`,
   without needing a copy at `w'` — but confirmed it is insufficient because the goal needs
   `IForces` (semantic), and nothing in the file supplies `Force → T(_)@w'∈b` (a bivalence/
   totality fact) to bridge from the given `hforce_φ'` hypothesis to that membership fact.

## What NOT to Try

- Do **not** re-add a self-copy channel to `applyAllTImpRules` inside a `Scheme.lean`-scoped
  dispatch without first running the same kind of divergence probe the ancestor-blocking repair
  ran (its own Phase 1, variant methodology) — an unbounded self-copy is exactly what caused the
  original expansion-loop divergence documented in reports/13.
- Do **not** attempt to derive `Force(w',φ') → T(φ')@w'∈b` (or any general bivalence/totality
  fact) as a quick lemma — the STOP-gate note's earlier "monotonicity" blocker (Scheme.lean,
  `intExtractValuation` monotonicity along accessibility) is a closely related, independently
  documented open problem, and no sub-lemma found during this dispatch closes it.
- Do **not** weaken `truthLemma`'s statement, relocate the sorry to a different declaration, or
  mark this phase `[COMPLETED WITH EXCLUSIONS]` — none of the five strategic-sorry conditions
  are newly satisfied by this dispatch (the sorry's `follow_up_task`/`discharge_phase` remain
  unresolved, not merely unassigned).

## Remaining Goals (verbatim from plan Phase 7 task list)

- [ ] Thread `applyPersistenceFixpoint_genuine_of_count_le_fuel` (enlarged-universe version,
  Phase 3; Scheme.lean:2928) through the open-branch extraction so the returned branch is at
  a GENUINE persistence fixpoint: every world accessible from a `T(φ'→ψ')` source carries
  its own copy (the `applyAllTImpRules` copy channel at a fixpoint). **[Premise false post-repair
  — see Blocker above. Do not attempt as written.]**
- [ ] Close the T-imp case (Scheme.lean:601-617) with `sat_timp` per the in-file analysis:
  the `F(φ')@w'` arm contradicts via `ih_φ'.2`, the `T(ψ')@w'` arm closes via `ih_ψ'.1`.
  **[Still the right shape once Gap 1 is closed by some other mechanism.]**
- [ ] Update the STOP-gate note (Scheme.lean:504-557) from "Gap 1 UNCHANGED" to resolved,
  citing the fixpoint-sufficiency route. **[Partially done this dispatch — updated to "Gap 1
  CONFIRMED BLOCKED", not "resolved", since resolution did not happen.]**

## References

- Plan: `specs/317_propositional_tableau_completeness/plans/14_fuel-materialization-repair.md`,
  Phase 7 section and its `#### Blocker` subsection (this dispatch).
- Key files: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (STOP-gate note
  above `truthLemma`, and the T-imp case itself), `Cslib/Logics/Propositional/Tableau/
  Intuitionistic/Expansion.lean` (`applyAllTImpRules` docstring, "STEP 1" note).
- Evidence commit: `a70187dd` ("task 574 phase 2: bound the T-implication self-copy channel
  (STEP 1)") — `git show a70187dd -- Cslib/Logics/Propositional/Tableau/Intuitionistic/
  Expansion.lean`.
- Prior research: `reports/13_blocker-root-cause-and-correct-approach.md` (§F4, names the
  self-copy channel as "Decision A", in direct conflict with persistence propagation
  "Decision B"; §Recommendations Option A step 1 lists the two live alternatives cited above).
