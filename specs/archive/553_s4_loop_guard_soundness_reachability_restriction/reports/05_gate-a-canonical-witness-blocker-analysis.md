# Blocker Analysis: Task #553

**Parent Task**: #553 - s4_loop_guard_soundness_reachability_restriction
**Generated**: 2026-08-05
**Blocker**: Plan v5's Gate A (Phase 1) failed at a **new**, fifth failure mechanism: the
structural-induction agreement lemma needed to preserve `branchSatisfiablePinnedIn s4FC` across
the redirect edge gets stuck one recursion level inside the `.box`/`.diamond` induction, where
the model point in play escapes to an arbitrary point of `W` that neither `accPinnedBy` nor
`hbox`/`hdia` constrain (both are deliberately stated only over `modalKnownWorlds b`). Per the
plan's own Kill Criteria this is outcome (iii) — route (1) is dead as planned, and per the plan's
own Terminal Condition text, no fifth route is proposed by that dispatch.

## Root Cause

**Mechanism, precisely** (see plan `05_pinned-witness-truth-lemma.md`, `#### Phase 1 Verdict`,
`plans/05_pinned-witness-truth-lemma.md:735-855`): the gate lemma extends the witness relation
`m.r` to `r' := m.r ∨ (m.r · (f src) ∧ m.r (f wBlock) ·)` and must show
`Satisfies m x χ ↔ Satisfies m' x χ` for every `χ` and every `x : W`, by induction on `χ`. The
propositional cases close for free. The modal cases split on which disjunct of `r'` licenses a
successor `y`; the "old" disjunct closes from the IH, but the "new" disjunct's proof obligation —
concretely, in the box-positive case, `Satisfies m' y φ` from `hbx : Satisfies m x (□φ)` plus
`m.r x (f src)` and `m.r (f wBlock) y` — has no route to a conclusion **unless `x` is known to be
`f w` for a branch label `w` with a recorded `T(□φ)@w ∈ b`**. The gate lemma's `x` is universally
quantified over all of `W`, not restricted to known labels, so for an `x` where `Satisfies m x
(□φ)` holds "by accident" of the arbitrary witness model (with no corresponding branch fact), no
invariant supplies leverage. Machine-checked stuck goals were captured for both the box-positive
(`m→m'`) and diamond-negative (`m'→m`) directions; both are recorded verbatim in the plan's
`#### Phase 1 Verdict`.

**Why this is a genuinely new failure mode, not a repeat.** The three earlier routes (Route P /
ordered-stepper scheduling, ancestor-only blocking, subtractive blocking + red channel) all died
on an "ambient predecessor of `f src`" that `accPinnedBy` (this route's Mechanism 1) was built
specifically to eliminate, by converting "predecessor among known labels" into an
`acc`-ancestor relationship. `accPinnedBy` succeeds at exactly that — sub-step 1.1
(`accPinnedBy`, `branchSatisfiablePinnedIn`, `branchSatisfiablePinnedIn_redirect_mechanical`) is
sorry-free, standard-axioms-only, and committed (confirmed present at
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean:5323-5390` in this dispatch's grep). The new
obstruction is one syntactic layer deeper: it is intrinsic to proving a **fully general**
`Satisfies`-agreement claim over an **arbitrary** witness model, because `Satisfies`'s `.box`/
`.diamond` clauses quantify over the entire carrier type `W`, and `accPinnedBy`/`hbox`/`hdia` are
deliberately restricted to `modalKnownWorlds b` (an unrestricted upper bound on `m.r` would be
false, since `f` is total on `WorldIndex` and would force every unused label equal — this is
recorded in the Phase 1 module comment itself).

**The plan's own diagnosis of the fix, not priced or owned by any remaining phase.** The Phase 1
Verdict names the fix directly (outcome (iv) analysis, `plans/05_...md:831-841`): a **canonicity**
assumption on the witness — "WLOG `W = WorldIndex` and `f = id`" — would make every model point
trivially a known label, closing the escape. It rejects folding this into route (1) only because
establishing it is "not a one-phase addition" and "not owned by any later phase in this plan"
(Phases 5-7 build the boxed driver and boxed invariant, not a canonicity argument), and because no
report has priced it. Per the user's decision recorded in the delegation context for this
dispatch, this is exactly the direction to pursue next: **assess whether a canonical/term-model-
restricted witness construction is viable for the redirect obligation, and price how large it
would be** — not to re-attempt route (1) as stated, and not to re-run the already-completed
FrameCompleteness refactor programme.

**Independent evidence the canonical-witness route is not a shot in the dark.** The completeness
line already builds exactly this shape of model on the other side of the theorem.
`extractModelWith`/`extractModelS4` (`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:85-148`,
re-read in this dispatch) return `Model WorldIndex Atom` directly — there is no existentially
quantified `W` or embedding `f` at all; the carrier **is** `WorldIndex` and the valuation reads
branch membership directly off labels. This is the literature's own precedent
(`Massacci2000` Thm 10.6, cited in the plan's Source-to-Implementation Mapping,
`plans/05_...md:235`: `W := {σ : σ present in B}`, `σRσ* iff σ ⊑_L σ*`) and it is a "canonical
model" in exactly the sense the Phase 1 Verdict's rejected strengthening would need for the
soundness side. Whether that same canonical shape can be adapted to a
`branchSatisfiablePinnedIn`-style existential — where the pinned invariant and the mechanical
conjuncts (sub-step 1.1) still need re-deriving against a fixed-`W` witness rather than an
existentially-arbitrary one — and whether doing so is compatible with reusing rather than
discarding sub-step 1.1's already-landed, sorry-free work, is precisely the open, unpriced
question a new task should answer before any large construction is scaffolded.

## Proposed New Tasks

### New Item 1: Probe and price a canonical/term-model-restricted witness for the S4 keyed redirect obligation
- **Effort**: 6-9 hours
- **Task**: TBD
- **Started**: TBD
- **Completed**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Task Type**: cslib
- **Rationale**: This is the single open, unpriced question left by Gate A's failure. It follows
  the same front-loaded-kill-gate discipline plan v5 itself used (Gates A-D before any of Phases
  5-12's scaffolding): before committing to a new multi-phase plan, machine-check whether
  restricting the witness (`W := WorldIndex`, `f := id`, matching `extractModelS4`'s existing
  precedent) actually closes the exact stuck goal recorded in the Phase 1 Verdict, and if so,
  price what changes it forces (which existential fields of `branchSatisfiablePinnedIn` collapse
  or need re-shaping; whether sub-step 1.1's three mechanical conjuncts and `accPinnedBy` survive
  unchanged or need re-derivation against a fixed carrier; whether the redirect-edge obligation
  becomes provable at that restriction, or dies at a sixth, still-different obstruction). If the
  probe succeeds, the task's report gives task 553 a priced, evidence-backed basis for a v6 plan.
  If it fails, the report names the new obstruction precisely, in the same machine-checked style
  as the four prior verdicts, rather than leaving 553 blocked on a vague "try canonicity" note.
- **Depends on**: None.
- **File scope**: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (isolated probe section,
  append-then-revert per the Phase 1 sub-step 1.1/1.2 pattern — no committed change to the
  existing sub-step 1.1 declarations), `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
  (read-only reference to `extractModelS4`/`extractModelWith`), this task's own `specs/` report.

## Dependency Reasoning

Only one task is proposed, so there is no internal dependency graph to reason about. It is
**not** split into a separate "research" task and a separate "plan/implement" task, for the same
reason plan v5 itself declined to scaffold Phases 5-12 before its kill gates passed: whether a
canonical-witness construction is even viable is exactly what determines what a follow-on task
would need to do (write a v6 plan adopting the restriction and re-deriving the mechanical
conjuncts against it, versus reporting a further-refined blocker if the probe also fails), and
that fork cannot be usefully pre-decomposed before the probe's own machine-checked verdict is in
hand — decomposing further now would be inventing structure the evidence does not yet support.

## After Completion

Once the spawned task is complete, resume the parent task #553 with `/implement 553` (or, if the
spawned task's report recommends a v6 plan, `/plan 553` first to produce it, then `/implement
553`).

The blocker will be resolved because: task 553's own `[BLOCKED]` state exists specifically
because no currently-known task targets the canonical/term-model-restricted witness gap the
Phase 1 Verdict identified but declined to price. The new task closes exactly that gap: a
positive, priced verdict gives 553 a concrete route (1-prime) to plan against; a negative verdict
gives 553 a sixth, precisely-named obstruction to escalate on, rather than the current
open-ended "assess viability" state.

## Update: Spawned Task Complete

The spawned task's report is at
`specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md`.
**Verdict: CONDITIONAL GO.** Restriction A (`W := WorldIndex`, `f := id` alone) does not close the
stuck cases -- it removes the escape-to-non-label-points obstruction but exposes a second,
distinct one: a semantic-to-syntactic truth-lemma gap. Restriction B1 (carrier restricted to the
known-branch-labels subtype) closes both stuck cases sorry-free, but only modulo two assumed
hypothesis groups: Decision Gate B's own conclusion (`modalS4Saturated`-family persistence facts,
this plan's own separate Phase 2, still unexecuted) and the truth lemma itself (new proof content,
not previously priced). The spawned task's Phase 3 prices a resulting v6 plan at 5-7 phases /
13.5-17.5 hours, decomposed by workstream, with a recommended front-loaded Gate 0 to de-risk the
truth lemma's box-positive case before committing to the full programme. Resume with `/plan 553`
to produce a v6 plan against this pricing, then `/implement 553`.
