# Implementation Summary: Repair Intuitionistic Tableau — Self-Copy Bound, Ancestor Blocking, Loop-Back-Edge Saturation Invariant

- **Task**: 574 - tableau_calculus_repair_ancestor_blocking
- **Status**: [COMPLETED]
- **Started**: 2026-07-27 (Phase 1)
- **Completed**: 2026-07-28 (Phase 8)
- **Effort**: ~52-78 hours estimated across 8 phases
- **Dependencies**: 573 (quotient-soundness spike, GO verdict — evidence held but the quotient
  recommendation was superseded in practice, see Decisions)
- **Artifacts**: `plans/02_tableau-repair-loopback-edges.md` (this task's plan, v02), `reports/`,
  `handoffs/`
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`intExpandBranches`, the intuitionistic propositional tableau decision procedure
(`Cslib/Logics/Propositional/Tableau/Intuitionistic/`), diverged (never terminated) on a
Lean-verified complexity-9 witness formula `φ0`. This task repaired the calculus by removing a
self-copy channel and replacing the descendant-directed loop-check with an ancestor-directed
`Sfor`-containment blocking check, then repaired the proof-side consequence — the reuse witness
now sits *below* the blocked world in the ordering, the reverse of what the saturation invariant's
`.neg,.imp` clause demanded — using a loop-back-edge augmented accessibility relation (Garg,
Genovese & Negri's published `M ∪ C` countermodel construction) rather than the originally-planned
quotient frame. `intExpandBranches_closed_unsat`, the acceptance gate, is verified sorry-free and
axiom-clean (`{propext, Classical.choice, Quot.sound}`) under the repaired calculus, and the full
CSLib CI pipeline is green on the task's own file set.

## What Changed

- **Phase 1** (`b1df9fd1`): Measured the divergence witness and three calculus variants via a
  standalone `#eval` harness (zero `Cslib/` writes). Confirmed the ancestor-directed check (not
  self-copy removal) is the termination mechanism (D3), and selected the `F(ψ)@x`-conjunct-retained
  variant (V1, D4) — it terminates at `fuel≥120`/`maxLabel=21` and all 19 conformance formulas
  match. Recorded in `handoffs/01_variant-selection.md`.
- **Phase 2** (`a70187dd`): Removed `applyAllTImpRules`'s `T(φ→ψ)` self-copy channel; repaired
  `applyAllTImpRules_sat` and `freshAbove_applyAllTImpRules` in `Soundness.lean`. A hypothesis miss
  surfaced a third dependent file (`Scheme.lean`) needing mechanical repair, fixed forward.
- **Phase 3** (`6aab037a`): Landed `intFImpReuseWitnessAnc?` / `_spec` (ancestor-directed,
  5-tuple, `F(ψ)@x` conjunct retained) additively, alongside the existing descendant-directed pair.
- **Phase 4** (`0a1cea04`, `c5f108e5`, `178cd446`, `659c713c`): Repointed `intExpandBranches`'s call
  site to the ancestor-directed check; re-verified the acceptance gate sorry-free on both arms
  (`Soundness.lean` needed only identifier renames); deleted the superseded descendant-directed
  pair; parked the proof-side consequence as one tracked temporary `sorry`
  (`Scheme.lean`, reuse-site discharge).
- **Phase 5** (`b70eadc0`…`1ebf52ad`) — **superseded, not salvaged**: built a ~480-line
  blocking-quotient frame (`intBlockRep`, `intAccessPreorderQ`, the `*Q`-suffixed predicate stack)
  intended to close the temporary sorry. All four sub-phases landed green.
- **Blocker research + plan revision** (`5c0db5aa`, `4b095c67`): A Phase 6 dispatch found the
  quotient stack cannot carry `intExpandBranches_openBranch_sat`'s forward induction —
  `intBlockRep` is a function of the *final* branch while the induction runs *forward* and is not
  monotone under branch growth. Research confirmed the obstruction is structural (matching Garg,
  Genovese & Negri's own reported inability to make a filtration/quotient route work) and produced
  a verified prototype for the replacement mechanism. The plan was revised to v02 around it.
- **Phase 6** (`04aecf54`, `2d92f09d`, `c6ec8766`, `149d2d48`): Dropped the never-consumed numeric
  ordering conjunct from `sfSatisfied`'s `.neg,.imp` clause and `IBranchSaturation.sat_fimp` (D8);
  threaded a parallel invariant-side `augSets : List IEdges` through
  `intExpandBranches_openBranch_sat`'s induction, decoupled from the algorithm's own edge list
  (D7); closed the reuse-site discharge with an explicit loop-back edge `(x, l)`, retiring the
  Phase-4 temporary sorry and restoring the exact 6-entry baseline.
- **Phase 7** (`175f7ea6`, `62667557`, `0464d237`): Deleted the ~480-line superseded quotient stack
  (grep-confirmed zero external references) and rewrote the design notes and docstrings it left
  behind — including a false "agrees by construction" claim and a stale reference to a deleted
  function — with no orphan references remaining.
- **Phase 8** (`1071df35` + this dispatch): Regenerated `CslibTests/TableauConformance.lean` — all
  19 existing propositional rows re-confirmed green via live `#eval` re-execution; added a 20th row
  asserting the divergence witness `φ0` now terminates with the correct semantic verdict `OPEN`
  (`φ0` is not IPC-valid: classically falsified by `a=⊤,b=⊥,d=⊤,e=⊥,u1=⊤,v1=⊥,u2=⊤,v2=⊥`),
  observed to match on the first real `#eval` execution with no divergence; rewrote the corpus
  provenance docstring (43 rows → 44: 24 temporal + 20 propositional); deleted the six Phase 1
  scratch probe files (findings already recorded in the Phase 1 handoff), retaining the Phase 6
  prototype/baseline evidence files; ran the full CSLib CI pipeline.

## Decisions

- **D3/D4** (Phase 1, measured not argued): ancestor-directed blocking is the termination
  mechanism; the `F(ψ)@x` conjunct is retained (a Massacci Def. 8.2 per-obligation shape, not the
  weaker per-world condition).
- **D5 superseded / D7** (blocker research): the quotient mechanism cannot carry a *forward*
  induction because its representative map is a function of the *final* branch. Replaced with an
  invariant-side augmented edge list threaded forward in lockstep with the induction — Garg,
  Genovese & Negri's `M ∪ C` construction, the same source the repo's `Sfor` naming derives from.
- **D8**: the numeric ordering conjunct in `sfSatisfied`/`sat_fimp` was a raw-`Nat` proxy for
  accessibility valid only under monotonically-increasing labels; under ancestor blocking it is
  false, and was verified never consumed downstream before being dropped.
- **D9**: no new `references.bib` entries; Massacci 2000's per-world/per-obligation distinction is
  recorded at plan level only, not attributed in Lean docstrings.
- **Supersession, stated not buried**: Phase 5's ~480 lines are preserved in git history (four
  green commits) as the record of the refuted approach, not silently erased.

## Impacts

- `intExpandBranches_closed_unsat` (the acceptance gate, consumed by `Minimal/Soundness.lean`)
  remains sorry-free and axiom-clean under the repaired calculus.
- The repo-wide bare-`sorry` count is at the exact 6-entry baseline (unchanged from before this
  task — the one temporary sorry this task introduced in Phase 4 was retired in Phase 6.3).
  `Soundness.lean` remains entirely sorry-free at every phase boundary, as required.
- `CslibTests/TableauConformance.lean` grew from 43 to 44 executable rows; the new row is a live
  termination regression guard for the divergence witness.
- Full `lake build` (3309/3309), `checkInitImports`, `lake exe lint-style`, and `lake test`
  (9374/9374) are green. `lake lint` and `lake shake` are **not** repo-wide green, but the
  non-green findings in both are entirely pre-existing, repo-wide debt in files this task never
  touches (`Bimodal/`, `LTL/`, `Modal/Tableau/FrameSoundness.lean`, `Temporal/Metalogic/`, and a
  handful of unrelated files for shake) — zero findings in `Propositional/Tableau/` or
  `CslibTests/` in either tool. This category of debt is independently attested by a separate,
  already-archived repo-wide lint-hygiene task as known and pre-existing. Risk R3 (an
  import-minimisation shift from Phase 7's ~480-line deletion) did not materialize — zero shake
  diffs in this task's file set.
- Residual, explicitly out-of-scope open items unchanged by this task and left untouched per the
  plan's postmortem constraints: `truthLemma`'s T-imp case (`Scheme.lean`, Gap 1, persistence
  fuel-sufficiency), `intExpandBranches_openBranch_sat`'s fuel-0 base case (refuted at its current
  statement, not merely hard), and the two `Completeness.lean` bridges (which now carry a named,
  expected obligation — GGN's Lemma III.5, valuation monotonicity against the enlarged preorder —
  as Residual Risk R1, not a regression).

## Follow-ups

- No task-internal follow-ups. Residual Risk R1 (valuation monotonicity against the enlarged
  preorder) is recorded in the plan's Risks & Mitigations for whichever future task attempts the
  `Completeness.lean` bridges.
- Minor, non-blocking: Phase 1 found `Expansion.lean`'s divergence-table docstring has one
  interior transcription discrepancy (fuel=60: table says 21, measured 20); recommended for
  correction whenever that docstring is next touched, not required for this task's acceptance
  gate.

## References

- `specs/574_tableau_calculus_repair_ancestor_blocking/plans/02_tableau-repair-loopback-edges.md`
  (implementation plan, this task's full record of Goals/Non-Goals/Risks/Postmortem Constraints)
- `specs/574_tableau_calculus_repair_ancestor_blocking/plans/01_tableau-repair-ancestor-blocking.md`
  (superseded v01, retained unedited)
- `specs/574_tableau_calculus_repair_ancestor_blocking/reports/01_phase6-blocker-resolution.md`
  (blocker research; the Phase 6 fix path's ground truth)
- `specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md` (Phase 1
  measurement record)
- `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/phase6-prototype.patch`,
  `scratch/Scheme.lean.prototype`, `scratch/Scheme.lean.baseline` (Phase 6 evidence, retained)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Expansion,Scheme,Soundness}.lean`
- Modified: `CslibTests/TableauConformance.lean`
