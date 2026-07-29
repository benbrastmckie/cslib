# Implementation Summary: Task #317 (v5 dispatch — Phase 1 complete, Phase 2 BLOCKED)

- **Task**: 317 - propositional_tableau_completeness
- **Plan**: `plans/05_frame-change-and-fuel-raise.md` (v5)
- **Status**: [BLOCKED] (Phase 1 of 11 COMPLETED; Phase 2 BLOCKED at STOP-gate a; Phases 3-11 not
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
  reached, gated on Phase 2)
- **Session**: `sess_1782919268_2df8d8_317`

## What was done

### Phase 1 (COMPLETED)

Widened the private lemma `intExpandBranches_openBranch_sat` (`Scheme.lean`) from concluding
`IBranchSaturation Atom b` to `∃ edges : IEdges, IBranchSaturation Atom b`, filling
`edges := edgesH` at the existing "none leaf" saturation case. This reuses the single
pre-existing `sorry` (the fuel=0 base case, now at `Scheme.lean:991`) — zero new sorries — and
composes through the existing induction with no changes to the recursive
(linearResult/branchingResult) cases, since the IH's existential passes straight through.
`openBranch_countermodel`'s call site was updated to `obtain ⟨edges, hsat⟩ := ...`. The public
`.openBranch` return type is untouched. Committed as `b646eb10`.

A concurrent session (`sess_1782919268_2df8d8_317b`) independently implemented Phase 1 via a
different, standalone `intExpandBranches_openBranch_edges` lemma (commit `d6d78714`), detected the
conflict against this dispatch's already-landed `b646eb10`, and correctly removed its own
duplicate in favor of this dispatch's solution (commit `ea452ce5`), per the plan's R6
single-writer-per-file discipline. Build green, sorries unchanged (330, 991) throughout.

### Phase 2 (BLOCKED — STOP-gate a triggered)

Full technical finding recorded in the plan file (`plans/05_frame-change-and-fuel-raise.md`,
Phase 2 section). Summary: `openBranch_countermodel`'s and `tableau_complete`'s byte-stable
(Postmortem 5) conclusions both fix `IForces`'s `World` type-class argument to bare `Nat`
(since `intExtractValuation b : Nat → Atom → Prop` and world `0 : Nat` appear literally in their
stated types), which forces Lean to resolve `[Preorder Nat]` to the unique, globally-registered
`Nat.instPreorder` — verified live via `#synth Preorder Nat` and a definitional-equality check
that this instance's `≤` is the standard, TOTAL, unbounded numeric order. This resolution happens
at theorem-type elaboration time, before any proof-body tactic could locally override it, so no
completeness-side-only edit can install edge-accessibility as the frame for these two theorems
without changing their stated types (forbidden).

Beyond re-confirming report 08's adversarial counterexample (`T(¬p→q)@0`, phantom-world `k`), this
dispatch established a **stronger, type-theoretic** version of the obstruction: `Nat.instPreorder`
is a *linear* (total) order, but general intuitionistic Kripke-completeness requires *non-linear*
(tree/DAG-shaped) frames — e.g. β-split sibling worlds are edge-incomparable, yet always get *some*
Nat label under a total order. No relabelling/retraction of edge-accessible worlds onto bare `Nat`
can make a total order represent a genuinely non-linear accessibility relation. This rules out any
reindexing workaround, not just the current numeric-labelling scheme.

Two escape routes were identified, both requiring escalation beyond this phase's scope:
(a) change `openBranch_countermodel`/`tableau_complete`'s stated types to quantify over a new
`World` type with a custom edge-based `Preorder` instance (a deliberate public-signature change,
currently forbidden by Postmortem 5); or (b) change `IForces`'s definition (`Kripke.lean`) to take
an explicit accessibility relation instead of `[Preorder World]` (rippling into the already-green
`tableau_sound`, task-316-adjacent, and other `IForces` consumers — forbidden without escalation
per Postmortem 4).

No Lean files were edited for Phase 2 (analysis-only STOP, per the STOP-gate's explicit instruction
not to force a workaround). Both sorries (330, 991) remain open and untouched.

## Plan Deviations

- Phase 1's chosen implementation deviates from the plan's literal suggestion of a standalone
  `intExpandBranches_openBranch_edges` lemma; instead, the existing `intExpandBranches_openBranch_sat`
  was widened in place (see plan file's Phase 1 "Implementation note" for the full rationale: a
  standalone lemma covering all fuel values requires an awkward disjunctive conclusion that would
  prematurely re-derive Phase 10's fuel-sufficiency content). This is a strictly smaller-diff,
  equally-general solution serving the same downstream consumers (Phase 2+).
- Phase 2 did not proceed to implementation. Per the plan's own Rollback/Contingency section
  ("R1 escalation... a clean [BLOCKED] here is the correct escalation"), this is the anticipated
  outcome of the STOP-gate, not a deviation from the plan's design — but this dispatch's finding is
  *stronger* than what report 08 (the plan's grounding research) established: report 08 found the
  T(→) obligation false under the current frame; this dispatch additionally found that the
  byte-stability constraint on `openBranch_countermodel`/`tableau_complete` (Postmortem 5) is
  *itself* incompatible with any completeness-side-only fix, which report 08 did not address (its
  own Q2 recommendation to "re-express `openBranch_countermodel`/`tableau_complete`... over this
  Preorder" implicitly assumes a signature change that Postmortem 5, as currently written, forbids).
  This is flagged as requiring a plan v6 / architectural decision, not treated as a phase failure to
  work around.

## Verification

- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` — GREEN (Phase 1 change).
- `grep -n sorry` across `Scheme.lean` (330, 991), `Completeness.lean` (113),
  `Minimal/Completeness.lean` (110) — four sorries total, all pre-existing, none introduced or
  closed this dispatch beyond the line-number shift for the Phase-1-modified lemma.
- No new axioms, no vacuous definitions, no weakened lemmas.

## Files touched

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (Phase 1 only; commit `b646eb10`)
- `specs/317_propositional_tableau_completeness/plans/05_frame-change-and-fuel-raise.md`
  (Phase 1/2 status + Phase 2 STOP-gate finding)

## Handoff

See `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json` for the structured
handoff (status `blocked`, `sorry_inventory`, `blockers`, `continuation_context`).

## Addendum: concurrent dispatch `sess_1782919268_2df8d8_317b` (supplementary Phase 2 work)

After this summary was written, the concurrent session referenced above (Phase 1's duplicate
lemma) returned to Phase 2 independently and, before seeing this dispatch's BLOCKED verdict,
implemented `intAccessPreorder`/`intAccessPreorder_le_of_isAccessible` in `Scheme.lean`
(commit `a1883c4e`): a genuine, `lake build`-green `Preorder Nat` instance built as
`Relation.ReflTransGen (fun x y => isAccessible edges x y = true)`. This sidesteps the need to
separately prove `isAccessible` itself transitive (an initial fuel-based attempt hit a
fuel-shrinking dead end: concatenating two `edges.length`-fuel DFS traversals needs
`edges.length + edges.length` fuel, with no general way back down to `edges.length` short of a
separate shortest-path argument). `Relation.ReflTransGen` gives reflexivity/transitivity for
free, and `.single` lifts any raw `isAccessible edges w w' = true` fact (all `sat_fimp`/future
`sat_timp` witnesses ever supply) directly into the order.

This genuinely fulfills Phase 2's first checklist item ("define the countermodel `Preorder`...
as the RTC of `isAccessible edges`") as real, tested code — a **Preserved Asset** for whichever
re-plan route (option a or b above) is eventually chosen.

That session then independently discovered a SECOND, additional blocker while attempting the
monotonicity proof directly: even if the byte-stability/signature question is resolved,
`intExtractValuation` monotonicity along edges is separately entangled with the B2
fuel-sufficiency argument (Phase 6-10, not yet implemented). Verified against source:
`intApplyRuleFull` (`Rules.lean:245-268`) maps every `.pos, .imp` signed formula (every
`T(φ→ψ)`) to `.notApplicable` — `T(→)` is handled exclusively by the fuel-bounded
`applyPersistenceFixpoint`, and `intStepBranch b e nw = none` (the only saturation witness for
the returned branch) does not guarantee that fixpoint loop actually converged. Atom monotonicity
for `T(→)`-triggered atoms co-inductively depends on the antecedent formula's own monotonicity,
resolved only by repeated fixpoint passes — i.e. by fuel. This is a wave-ordering inversion:
Phase 2 (Wave 2) becomes logically dependent on Phase 10's `intExpMeasure`/fuel-sufficiency
machinery (Wave 6). Documented in-file (doc comment immediately after
`intAccessPreorder_le_of_isAccessible`, no `sorry`) and in the plan file's Phase 2 section
("Supplementary finding" subsection) and the `.orchestrator-handoff.json`.

**Combined recommendation for the re-plan**: adopt option (a) or (b) to resolve the
signature-pinning issue, AND restructure `intExtractValuation` monotonicity as a
field/hypothesis threaded alongside `sat_timp` (Phase 4), discharged only once
`measure ≤ fuel` (Phase 10) is available — mirroring R3's own anticipated fold for `sat_timp`'s
succ-case, generalized to Phase 2's atom-monotonicity too. `intAccessPreorder` remains directly
reusable once the signature question is resolved.

No verdict change: Phase 2 remains [BLOCKED]. Build green throughout (662 jobs); sorries
unchanged in content, shifted only by doc-comment/lemma insertions
(330→409, 991→1070 in `Scheme.lean`; `Completeness.lean:113`, `Minimal/Completeness.lean:110`
unchanged). No new axioms, no vacuous definitions, no weakened lemmas, no workaround `sorry`.
