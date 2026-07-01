# Implementation Summary: Task #317 (v5 dispatch — Phase 1 complete, Phase 2 BLOCKED)

- **Task**: 317 - propositional_tableau_completeness
- **Plan**: `plans/05_frame-change-and-fuel-raise.md` (v5)
- **Status**: [BLOCKED] (Phase 1 of 11 COMPLETED; Phase 2 BLOCKED at STOP-gate a; Phases 3-11 not
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
