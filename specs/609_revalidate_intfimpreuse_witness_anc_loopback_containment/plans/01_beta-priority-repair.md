# Implementation Plan: Beta-Priority Repair of Loop-Back Containment

- **Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows
- **Status**: [IMPLEMENTING]
- **Effort**: 15 hours
- **Dependencies**: 604 (completed). Coordination-only with 605; see "Coordination with Task 605".
- **Research Inputs**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/reports/01_loopback-revalidation-repair.md`
- **Artifacts**: plans/01_beta-priority-repair.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Land repair **V1 (beta-priority)** from the research report: defer the world-creating
`F(φ → ψ)` rule in `intStepBranch` until no other rule is applicable anywhere on the branch.
The report measured V1 green on every adequacy and conformance metric — 9/9 adequacy formulas
(including all three that refute the current calculus), 6/6 open conformance rows, and 0 verdict
differences over the 20-row corpus including the complexity-9 divergence witness. With the
calculus repaired, the augmented frame carries `IFimpAccess` *and* full positive persistence
simultaneously, which is exactly what `openBranch_countermodel` needs and what `truthLemma`
(already sorry-free and parametric over any frame carrying both) consumes.

Definition of done: the calculus change is landed and verdict-preserving; the snapshot existential
is dropped from `IReuseContain`; `openBranch_countermodel` is discharged; the two
`Completeness.lean` sorries are discharged. Standing constraint throughout: **zero new sorries,
zero new axioms, no weakened statements**. The live sorry count on this path goes 3 → 0.

### Research Integration

The report is prescriptive and its recommendations are adopted essentially whole: V1 over V2
(equally adequate, far more proof work) and over V3 (adequate but fails the termination gate at
real fuel, destroys the forest property, and is soundness-adjacent to the recorded UNSOUND
"Option B"). The report's §5.1 code shape for `intStepBranchPrio`, its §5.2 `none`-iff bridge, and
its §5.3 freeze-lemma obligation are all carried into phases below.

**Two corrections to the report's proposed phase ordering**, both established by direct inspection
of the tree and both material to sizing:

1. **The report's "three spec lemmas" undercounts.** There are 13 `intStepBranch_*` lemmas in
   `Scheme.lean`, of which **six unfold the definition directly** (`simp only [intStepBranch]` at
   `Scheme.lean` lines 992, 1146, 4601, 4686, 4808, 4938). Two of those six (4601, 4686) are
   `intExpMeasure`-decrease lemmas carrying `go`'s termination measure — they are not optional
   downstream conveniences. The report's claim that the conclusion of `intStepBranch_some_exists`
   is unchanged is correct, but the *proofs* that unfold the definition still need re-basing. This
   plan therefore inserts a dedicated re-basing phase (Phase 2) before the call-site swap.
2. **The report defers the `BetaSplitRefutation.lean` update to last; it cannot be deferred at
   all.** `CslibTests` is a `lean_lib` and the declared `testDriver`, and `goRaw`
   (`BetaSplitRefutation.lean:132`) calls the **library** `intStepBranch` directly while
   `branchesAgree` (`:355`) compares `goRaw`'s branch against the **real**
   `intuitionisticTableau`. The moment the call site in `intExpandBranches.go` swaps, the
   recreation and the real algorithm diverge, `branchesAgree` flips to `false`, and its
   `#guard_msgs` fails. The test reconciliation is part of the swap phase (Phase 3), not a
   follow-on. Only the *narrative* re-pointing and the `phiRef4` promotion are genuinely
   separable (Phase 4).

### Prior Plan Reference

No prior plan for this task. Effort calibration is taken from the sibling propositional-tableau
tasks in the 593 expansion tree, where Lean proof phases in `Scheme.lean` have run ~2 hours per
dispatch.

### Roadmap Alignment

`specs/ROADMAP.md` "Remaining → A. Completeness / decidability gaps" row *Propositional tableau
completeness (3 sorries, as of 2026-08-09)* names this task explicitly as the owner of the root
cause: "the frames previously tried for it are machine-refuted, with root cause
`intFImpReuseWitnessAnc?` in `Expansion.lean` tracked as task 609". Completing this plan retires
the `Intuitionistic/Scheme.lean` ×1 sorry directly and unblocks the `Intuitionistic/Completeness.lean`
and `Minimal/Completeness.lean` sorries in that same row. ROADMAP.md is consulted read-only here
and is not modified by this plan.

## Coordination with Task 605

Sibling task 605 produced a verified patch at
`specs/605_establish_minbranchbotforces_upward_closure_at_bot/verified-shape-fix.patch` that
**changes `openBranch_countermodel`'s statement shape**. Downstream task 606 depends on both 605
and 609, so the reconciliation surface must be explicit rather than discovered at merge time.

What 605's patch changes, verified against the patch itself:

| Site | Change |
|------|--------|
| `Scheme.lean` `openBranch_countermodel` | Adds a **third existential conjunct** between `huc` and `hcm`: `(∀ w w', (intAccessPreorder edges).toLE w w' → S.modelBot b w → S.modelBot b w')` — modelBot upward-closure |
| `Scheme.lean` `tableau_complete` | `hvalid` gains the matching premise; destructuring goes from `⟨edges, huc, hcm⟩` to `⟨edges, huc, hbuc, hcm⟩` and the application from `hvalid edges b huc` to `hvalid edges b huc hbuc` |
| `Scheme.lean` `isAccessible_*_mono` region | Two new supporting lemmas (patch hunks at `:340`, `:375`) |
| `Minimal/DecisionProcedure.lean` | Universe pin `MValid.{_, 0}` plus a `mvalid_descend` / `mvalid_universe_invariant` ULift transport bridge |

Interaction with this plan is confined to **Phases 8 and 9**. The contract is: detect the landed
shape, satisfy it, never reshape it. Concretely — 609 supplies `huc` (frame upward-closure of the
valuation) and `hcm` (the `¬IForces` conjunct) from the repaired augmented frame via `truthLemma`;
605 supplies `hbuc` (modelBot upward-closure). Phase 8 must **not** re-derive, weaken, or drop
`hbuc`, and must **not** revert the universe pin. If 605 has not landed when Phase 8 runs, Phase 8
discharges the shape that is actually present and records in-source exactly where the missing
conjunct will need threading, so 606 has a named seam rather than a merge conflict.

Three further facts come from 605's own planning handoff
(`specs/605_establish_minbranchbotforces_upward_closure_at_bot/.orchestrator-handoff.json`,
`coordination_notes`) and are load-bearing here:

1. **605 builds the witness 609 needs.** Its Phase 2 lands
   `openBranch_rawEdges_both_upward_closed`, which returns **both** upward-closure facts at one
   shared `edges`. Phase 8 should consume that lemma rather than deriving `hbuc` independently.
2. **The one-liner shape quoted in this task's research report is wrong, and 605 caught it.**
   The report's §5.4 gives `exact h Nat (intExtractValuation _b) _huc 0` as the DP-3 discharge.
   605's note: "That claim is false: `IValid` quantifies `World : Type v` while the countermodel
   frame is `Nat : Type 0`." DP-3 needs the same `.{_, 0}` universe pin and the same `ULift`
   transport (`mvalid_descend` / `mvalid_universe_invariant`) that 605 builds. Phase 9 is written
   against 605's correction, not the report's claim.
3. **Under 605's option A, the `Minimal/Completeness.lean` DP-4 site is already closed by 605.**
   Only the intuitionistic DP-3 one-liner remains for this task. Phase 9 treats the minimal site
   as conditional, not assumed-open.

**Territory.** Both tasks edit `Scheme.lean` (~8,166 lines) in disjoint regions: 609 owns the
`intStepBranch` / `intExpandBranches.go` rule-selection region and the `IReuseContain` threading;
605 owns the `isAccessible` monotonicity region, `openBranch_rawEdges_upward_closed`, and
`openBranch_countermodel` / `tableau_complete` at the end of the file. Note that Phase 8 of this
plan reaches into 605's region. Whichever task lands second **rebases rather than re-applies**.

**A second, sharper conflict for 606 to be aware of.** Task 606's description carries an in-bounds
prohibition: "do NOT discharge [DP-3] with `exact h Nat (intExtractValuation _b) _huc 0`; that
type-checks but only launders an undischarged conjunct through the file". The in-source note at
`Intuitionistic/Completeness.lean:164-170` states the premise of that prohibition explicitly — the
one-liner is forbidden *because* `openBranch_countermodel`'s upward-closure conjunct is open, so
`_huc` at that frame does not genuinely discharge anything. Once Phase 8 lands, that premise is
false and the one-liner becomes legitimate. Phase 9 must therefore **update that in-source note to
record why the prohibition has dissolved**, not silently delete it and not silently ignore it. An
implementer who applies the one-liner while Phase 8 is incomplete would be committing exactly the
laundering 606 forbids.

## Goals & Non-Goals

**Goals**:
- Land `intStepBranchPrio` and swap `intExpandBranches.go`'s single call site to it, verdict-
  preservingly, with the conformance corpus unchanged.
- Drop the snapshot existential from `IReuseContain`, replacing `IReuseContain_mono` with a freeze
  lemma justified by beta-priority.
- Export augmented-frame positive persistence from `intExpandBranches_openBranch_sat`.
- Discharge `openBranch_countermodel` and the two `Completeness.lean` sorries.
- Promote `phiRef4` to an assertion and re-point `BetaSplitRefutation.lean` at the repaired
  calculus.

**Non-Goals**:
- V2 (retract-on-violation) and V3 (cyclic edges). V2 is a recorded fallback only; V3 is a measured
  dead end (§6 of the report) and must not be attempted.
- Changing `intFImpReuseWitnessAnc?` or either of its two spec lemmas — the report's recommendation
  leaves them untouched and this plan does too.
- Deleting `intStepBranch`. It becomes `intStepBranchPrio`'s second pass and stays.
- Re-attempting the five excluded frame constructions (`rawEdges` itself, pruning at blocked
  worlds, pruning at strictly-blocked worlds, the greatest `IFimpAccess`-supported fixpoint, the
  maximal atom-inclusion frame). All are post-hoc constructions over unchanged algorithm output and
  are orthogonal to a change in the algorithm itself.
- Any change to `openBranch_countermodel`'s statement shape beyond what 605 lands.
- Restating theorems to dodge a proof obligation.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The six definition-unfolding proofs (esp. the two `intExpMeasure` termination lemmas) resist re-basing onto a shared extraction bridge | H | M | Phase 2 is dedicated to exactly this and lands *before* the swap, so a failure here surfaces while the tree is still green and behavior-unchanged. The strengthened bridge exports `sf ∉ e`, which is what the measure lemmas currently derive by unfolding |
| `#guard_msgs` fallout is wider than the 5 files identified (88 assertions) | M | M | Phase 3 carries a Scope Hypothesis and is declared `atomic-batch`; the corpus run is the confirmation step, and `#guard_msgs` failures print the actual value, making reconciliation mechanical rather than predictive |
| The freeze lemma is harder than the report's §5.3 projects | H | M | V2 (retract-on-violation) is the recorded fallback — equally adequate and equally verdict-preserving, at the cost of a new `go` recursion arm. Escalate rather than weaken `IReuseContain`. Phases 1-4 are already landed and independently valuable at that point |
| Phase 8 collides with 605's statement-shape change | M | H | Phase 8 opens by detecting the landed shape and adapts to it; the contract above forbids reshaping. Explicitly recorded so 606 inherits a seam, not a conflict |
| The research report's DP-3 one-liner does not typecheck (universe mismatch: `IValid` quantifies `World : Type v`, the frame is `Nat : Type 0`) | M | H | Already caught by 605 and folded into Phase 9. Route through 605's `mvalid_descend` / `mvalid_universe_invariant` transport. If 605 has not landed, building that bridge is a scope increase to surface, not absorb |
| Phase 9 does redundant work on `Minimal/Completeness.lean`, which 605 option A already closes | L | M | Phase 9 checks the site before editing it |
| An implementer applies the `Completeness.lean` one-liner before Phase 8 discharges the conjunct | H | L | Phase 9 depends on Phase 8; the laundering prohibition and the condition under which it dissolves are stated in this plan and must be re-stated in-source |
| Conformance corpus runtime (~10 min baseline, per report) makes iteration slow | L | H | Run the full corpus only at the phase-closing gate, not per edit; use the 9-formula adequacy set for inner-loop feedback |
| Line numbers in the research report have drifted (it worked in a worktree pinned to HEAD while a concurrent session edited `Scheme.lean`) | L | H | Every phase below re-locates its targets by symbol name. Report line numbers are recorded as approximate only; e.g. `IReuseContain` is at `:6814` today, not the report's `:6798` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 8 | 7 |
| 8 | 9 | 8 |

Phases within the same wave can execute in parallel.

---

### Phase 1: `intStepBranchPrio` and its bridges (additive) [COMPLETED]

**Goal**: Introduce the beta-priority stepper and every bridge lemma downstream work will consume,
without changing any existing behavior. Nothing calls the new definition yet, so the tree stays
green trivially.

**Tasks**:
- [x] Add `isWorldCreating : ISF Atom → Bool` to `Expansion.lean`, true exactly on `.neg, .imp`.
      Confirm no symbol of that name already exists (grep returned none at plan time).
- [x] Add `intStepBranchPrio` beside `intStepBranch` in `Expansion.lean`, following report §5.1:
      first pass skips `expanded` members and world-creating formulas; on `none`, fall through to
      `intStepBranch b expanded nextWorld`. *(deviation: altered -- factored the first pass into
      a named, non-private `intStepBranchPrioFirstPass` helper so `Scheme.lean`'s bridge lemmas
      can unfold it; `private` was dropped from that helper specifically so it stays visible
      across files, matching the plan's own file split for the none-iff/some-exists bridges)*
- [x] Prove `intStepBranchPrio_result_ne_notApplicable`, mirroring
      `intStepBranch_result_ne_notApplicable` (`Expansion.lean:218`) with one extra `if`-guard case.
- [x] Prove the `none`-iff bridge: `intStepBranchPrio b e nw = none ↔ intStepBranch b e nw = none`.
      Forward is definitional (the second pass *is* `intStepBranch`); reverse holds because the
      first pass searches a strict subset of the same candidates. *(placed in `Scheme.lean`
      beside `intStepBranch_some_exists`, per the phase's "Files to modify" list)*
- [x] Prove `intStepBranchPrio_some_exists`, the extraction bridge, **strengthened with `sf ∉ e`**
      relative to the existing `intStepBranch_some_exists` (`Scheme.lean:1141`):
      `∃ sf, sf ∈ b ∧ sf ∉ e ∧ intApplyRuleFull sf nw b = result ∧ newExp = e ++ [sf]`.
      The `sf ∉ e` conjunct is what the `intExpMeasure` lemmas currently obtain by unfolding.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - `isWorldCreating`,
  `intStepBranchPrio`, `intStepBranchPrio_result_ne_notApplicable`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - the `none`-iff bridge and
  `intStepBranchPrio_some_exists`, placed beside their `intStepBranch` counterparts

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` and
  `...Intuitionistic.Scheme` both succeed.
- Zero new sorries, zero new axioms: `lean_verify` on each new declaration.
- No existing declaration's proof was touched (diff is purely additive).

---

### Phase 2: Re-base the six unfolding proofs onto a shared extraction shape [COMPLETED]

**Goal**: Make the call-site swap a small, local edit by removing every direct
`simp only [intStepBranch]` from the proofs that carry `go`'s obligations. Behavior is unchanged;
this is a pure refactor over the *existing* stepper.

**Tasks**:
- [x] Introduce a shared predicate capturing the shape both steppers return, e.g.
      `IStepShape b e nw result newExp : Prop := ∃ sf, sf ∈ b ∧ sf ∉ e ∧
      intApplyRuleFull sf nw b = result ∧ newExp = e ++ [sf]`.
- [x] Prove `intStepBranch_some_shape` (strengthening `intStepBranch_some_exists` with `sf ∉ e`)
      and re-point `intStepBranchPrio_some_exists` from Phase 1 at the same predicate.
- [x] Re-base each of the six unfolding proofs to consume the shape lemma instead of unfolding.
      Confirmed sites by re-running `grep -nE "simp only \[intStepBranch"` at implementation
      time: 6 direct-unfold sites (matching the plan's Scope Hypothesis exactly), by symbol:
      `intStepBranch_none_compound_mem` (needs the `none` side only, confirmed no change
      required -- Phase 3 covers `none`-keyed results entirely via `intStepBranchPrio_none_iff`),
      `intStepBranch_some_exists` (now a thin weakening of `intStepBranch_some_shape`), the two
      `intExpMeasure` decrease lemmas (`intExpMeasure_step_lt`, `intExpMeasure_step_lt_branch`),
      `intStepBranch_branchingResult_length`, `intStepBranch_some_exists_fuel`.
- [x] Where a lemma in the `intStepBranch_*` family takes the definitional hypothesis
      `intStepBranch b e nw = some (...)` purely to extract the shape, generalize its hypothesis to
      `IStepShape ...` so it serves both steppers without duplication. Prefer generalization over
      cloning a `Prio` variant — the report's reuse-first constraint applies.
      *(deviation: altered -- generalized to `IStepShape` only for `intExpMeasure_step_lt` and
      `intExpMeasure_step_lt_branch`, which are confirmed UNCONSUMED (grep: zero call sites) and
      so cost nothing to generalize now. `intStepBranch_branchingResult_length` and
      `intStepBranch_some_exists_fuel` keep their `intStepBranch`-specific hypothesis: their live
      call sites are `CslibTests/BetaSplitRefutation.lean:203` and the `go`-induction sites this
      plan's own Phase 3 explicitly owns re-pointing ("its termination measure at :203
      (intStepBranch_branchingResult_length) to the corresponding shape lemma" is a named Phase 3
      task). Generalizing their signatures now would force touching `CslibTests` ahead of Phase
      3's declared atomic-batch boundary, which is out of Phase 2's scope ("Files to modify:
      Scheme.lean" only). Both lemmas were still re-based -- their proof BODIES now consume
      `intStepBranch_some_shape` instead of unfolding -- satisfying the phase's stated goal without
      the premature signature change. Phase 3 will generalize these two signatures itself when it
      re-points their call sites, per its own task list.)*
- [x] Leave the `go` call site still on `intStepBranch`, feeding the lemmas through
      `intStepBranch_some_shape`.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: Six sites unfold `intStepBranch` directly and thirteen `intStepBranch_*`
lemmas exist in `Scheme.lean` (`grep -c intStepBranch` = 102 occurrences in `Scheme.lean`, 8 in
`Expansion.lean`). Confirm at implementation time by re-running
`grep -nE "(simp only \[intStepBranch|unfold intStepBranch|rw \[intStepBranch)"` over
`Scheme.lean` and re-enumerating the lemma family; report the actual counts in the phase commit. If
the true set is larger, do not silently absorb it — record the delta.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - `IStepShape` and the six
  re-based proofs plus any generalized hypotheses

**Verification**:
- Full `lake build` succeeds.
- `git diff` shows no change to any *statement* that is not a hypothesis generalization, and no
  change to `intExpandBranches.go`.
- Zero new sorries, zero new axioms.

---

### Phase 3: Swap the call site and reconcile the test corpus [COMPLETED]

**Goal**: Land the actual calculus repair. This is the phase the report calls "worth landing
standalone": verdict-preserving, strictly reduces world creation, no new proof debt.

**Scope Correction (discovered at implementation time, not pre-declared in Phase 1/2 planning)**:
This phase's true blast radius is substantially larger than its own Scope Hypothesis or Timing
estimate (2 hours) accounts for. Confirmed by direct inspection: `intExpandBranches_openBranch_sat`
and its companion lemmas do **not** hand-write `match _hstep : intStepBranch ... with` blocks
mirroring `go`'s structure -- they use Lean's auto-generated functional-induction principle,
`induction ... using intExpandBranches.go.induct`, at **four separate call sites**
(`grep -n "using intExpandBranches.go.induct"` finds them at approximately `:5767`, `:5991`,
`:6734`, `:7147`). Once `go`'s match target swaps from `intStepBranch bPers e nw` to
`intStepBranchPrio bPers e nw`, Lean regenerates `go.induct` to bind the induction's `_hstep`
hypothesis at `intStepBranchPrio bPers e nw = ...` instead -- automatically, since the
principle is derived from the definition, not hand-authored. This means **every** call site
inside all four induction blocks that currently feeds `_hstep` (or a case-bound equivalent) to
an `intStepBranch`-hypothesis-typed lemma breaks, not just the six sites Phase 2 re-based.
Confirmed additional lemma family requiring the same `IStepShape` generalization treatment
Phase 2 gave `intExpMeasure_step_lt`/`_branch`: `intStepBranch_linear_preserves`,
`intStepBranch_linear_preserves_univ`, `intStepBranch_linear_preserves_labelStrict`,
`intStepBranch_linear_preserves_nw_of_none`, `intStepBranch_branch_preserves`,
`intStepBranch_branch_preserves_labelStrict`, `intStepBranch_branch_preserves_univ`,
`intStepBranch_branch_preserves_nw`, plus completing the deferred generalization of
`intStepBranch_branchingResult_length` and `intStepBranch_some_exists_fuel` (Phase 2 kept both
`intStepBranch`-specific precisely because their live call sites are inside this induction and
`CslibTests/BetaSplitRefutation.lean:203`, both explicitly this phase's territory). Call-site
count inside the four induction blocks is in the dozens (a non-exhaustive grep of
`intStepBranch_(linear|branch)_preserves|some_exists_fuel|branchingResult_length` within
`Scheme.lean`'s `:5700`-`:8000` range found 20+ occurrences before this note was written; a
fresh count should be taken at execution time, per this plan's own delta-recording convention).
This is recorded as a delta, not silently absorbed: the swap is a real, single atomic-batch unit
of work (the induction cannot be half-migrated and still build), but it is closer to the scale of
Phases 1+2 combined than to a standalone 2-hour edit. A future dispatch resuming this phase
should re-run the greps above to get current line numbers and counts before starting, and budget
accordingly rather than trusting the original Timing estimate.

**Tasks**:
- [x] Swap the single call site in `intExpandBranches.go` from `intStepBranch bPers e nw` to
      `intStepBranchPrio bPers e nw` (`Scheme.lean`, the `match _hstep : ... with` under
      `| f' + 1 =>`; report cites `:5005`, re-locate by the `match _hstep` anchor).
- [x] Re-point `go`'s proof obligations at `intStepBranchPrio_some_exists` and the `none`-iff
      bridge. Per report §5.2, every `none`-keyed result — saturation, `IBranchSaturation`,
      `intExpandBranches_openBranch_sat`'s open-branch leaf — needs no reproof, only the bridge.
      *(As predicted by the Scope Correction: this required generalizing 8 more `intStepBranch_*`
      lemmas -- `intStepBranch_linear_preserves`, `_linear_preserves_labelStrict`,
      `_linear_preserves_univ`, `_linear_preserves_nw_of_none`, `intStepBranch_branch_preserves`,
      `_branch_preserves_labelStrict`, `_branch_preserves_univ`, `_branch_preserves_nw` -- plus
      completing the deferred `IStepShape` generalization of `intStepBranch_branchingResult_length`
      and `intStepBranch_some_exists_fuel` from Phase 2, and generalizing the low-level
      `intStepBranch_some_exists` helper itself (not separately named in the Scope Correction, but
      needed by three direct call sites inside `intExpandBranches_closed_unsat`'s induction). Every
      call site inside the four `intExpandBranches.go.induct` blocks that fed the old
      `intStepBranch`-typed `hstep` to one of these lemmas now wraps it with
      `intStepBranchPrio_some_exists hstep` first. The `none`-case leaf
      (`IExpandedConsistent_sat`/`IExpandedAccessConsistent_sat`) wraps with
      `intStepBranchPrio_none_iff.mp hstep`, and the defensive `notApplicable` arm now calls
      Phase 1's `intStepBranchPrio_result_ne_notApplicable` directly. Confirmed empirically: only
      ONE of the four induction blocks (`intExpandBranches_openBranch_sat`, the one starting at the
      call site that was `:7147` at investigation time) needed any of this -- the other three
      induction blocks (`intExpandBranches_openBranch_closed`, `intExpandBranches_closed_unsat`,
      `intExpandBranches_openBranch_initial_mem`) either needed zero changes (their `hstep` is only
      ever compared to other equations, never fed to an `intStepBranch`-specific lemma) or, for
      `intExpandBranches_closed_unsat`, only the three direct `intStepBranch_some_exists` call
      sites.)*
- [x] Update `goRaw` in `CslibTests/BetaSplitRefutation.lean:132` to call `intStepBranchPrio`, and
      its termination measure at `:203` (`intStepBranch_branchingResult_length`) to the
      corresponding shape lemma. `goRaw` must continue to mirror the real algorithm — that is the
      entire purpose of the `branchesAgree` / `minBranchesAgree` fidelity checks.
      *(Confirmed: both `branchesAgree` and `minBranchesAgree` still evaluate `true` after the
      swap, unchanged and unflagged by the `#guard_msgs` reconciliation below -- the recreation
      still faithfully mirrors the real `intuitionisticTableau`/`minimalTableau` entry points.)*
- [x] Run the test corpus and reconcile every `#guard_msgs` whose expected value changed.
      **Actual results** (true set, per this task's own delta-recording convention -- the Scope
      Hypothesis below undercounted which files changed): `BetaSplitRefutation.lean` (6 of 10
      assertions changed: `report phiRef1`, `atomTable phiRef1`, `atRealFuel`, `decisiveFacts`,
      `reportMin phiRef1 realFuel`, `minAtomTable` -- the persistence-violation field
      `some (2, 1, 2)` became `none` exactly as predicted, and `pr` is no longer forced at world 2
      without also being forced at world 1); `MinProbe.lean` (3 of 8 changed: the world table and
      two `try1` witness rows flip from `false` to `true` on their falsification conjunct);
      `WitnessProbe.lean` (4 of 10 changed: `atomTable`, both `check` calls on the raw-tree and
      augmented-frame edge sets, and `searchSpaceSize`'s admissible-pair count `7 -> 8`);
      `WitnessSearch3.lean` (4 of 13 changed: the `phiRef1`/`phiRef3` intuitionistic-scheme rows
      and the `checkMin phiRef1` row all flip from the cited-failure `(true, false)` to
      `(true, true)`, i.e. the frame-adequacy gap the whole task exists to close is gone).
      **`TableauConformance.lean` needed zero changes**, confirming the Scope Hypothesis's central
      claim (0 verdict differences across all 20 rows) even though the per-file failure
      distribution among the other four files was wider than hypothesized. Stale prose narrative
      in the three probe/search files (not just `BetaSplitRefutation.lean`, whose narrative is
      Phase 4's explicit territory) was updated in place alongside the numeric reconciliation so
      the files stay internally consistent -- see `WitnessProbe.lean`'s and `WitnessSearch3.lean`'s
      updated module comments, phrased as empirical facts about the specific hardcoded edge sets
      rather than claims about the algorithm's general behavior.
- [x] Confirm the divergence witness (conformance row 20, complexity 9) still returns `OPEN` at
      `intFuelExt φ0` and the 14 IPC-valid rows still return `CLOSED` — this is the termination and
      completeness gate, and it is stronger evidence than any small-fuel growth table (the report
      explicitly declines to rely on those).
      *(Confirmed via `lake test`: `CslibTests.TableauConformance` built with zero `#guard_msgs`
      failures, meaning every one of its 20 row assertions -- including row 20 -- still holds at
      its pre-change expected value.)*

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 88 `#guard_msgs` assertions across five test files touch the intuitionistic
or minimal tableau — `TableauConformance.lean` (47), `WitnessSearch3.lean` (13),
`WitnessProbe.lean` (10), `BetaSplitRefutation.lean` (10), `MinProbe.lean` (8). The hypothesis is
that only `BetaSplitRefutation.lean`'s change materially, with the other four either unchanged
(verdict-only assertions) or changed in a way the report's adequacy measurements already predict.
Confirm by building `CslibTests` and enumerating actual failures; record the true set in the phase
commit. This is a hypothesis, not a finding — the report measured verdicts, not every asserted
tuple.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - the call site and `go`'s
  re-pointed obligations
- `CslibTests/BetaSplitRefutation.lean` - `goRaw`, its measure, and the affected assertions
- Any of `CslibTests/{TableauConformance,WitnessProbe,WitnessSearch3,MinProbe}.lean` the corpus run
  actually flags

**Verification**:
- Full `lake build` succeeds, including the `CslibTests` lib.
- Conformance corpus: 20/20 rows produce the same verdict as the pre-change baseline.
- Zero new sorries, zero new axioms.
- The `atomic-batch` boundary is the whole file set above: intermediate per-file states are
  expected red and must not be committed.

**Confirmed** (this dispatch): `lake exe cache get` (warm), scoped `lake build
Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` green, `lake exe checkInitImports`
clean, `lake lint` zero findings in touched files across all 7 prevention categories, `lake exe
lint-style` clean, `lake shake --add-public --keep-implied --keep-prefix` clean for touched
files, `lake exe mk_all --module` reports "No update necessary" (no new files), full `lake build`
green at 3325 jobs (identical job count to the Phase 1/2 baseline), and `lake test` green at 9397
jobs. Sorry count unchanged at 2 (`Scheme.lean:8203` `openBranch_countermodel`, Phase 8's
territory; `Completeness.lean:181` `intuitionisticTableau_complete`, Phase 9's territory). Axiom
count unchanged at 26. Committed as a single atomic-batch commit spanning `Expansion.lean`
(no change this phase), `Scheme.lean`, and the four `CslibTests/*.lean` files.

---

### Phase 4: Promote `phiRef4` and re-point the refutation narrative [COMPLETED]

**Goal**: Record the third refuting formula the report discovered, and re-point
`BetaSplitRefutation.lean`'s prose from "here is the defect" to "here is the defect and here is the
repair that removes it". Runs in parallel with Phase 5.

**Tasks**:
- [x] Promote `phiRef4` (`BetaSplitRefutation.lean:301`) from an interactively-inspectable
      robustness variant to a `#guard_msgs`-asserted case. The report §3 measured it as a genuine
      third refuting formula: it fails augmented-frame persistence exactly as `phiRef1` does, at
      `(2 → 1)`, contradicting its current docstring's "not promoted to an assertion" framing.
      *(Under the now-repaired calculus, `report phiRef4 40` evaluates to
      `("OPEN", 23, 2, [(1, 0), (2, 1)], [(2, 2), (1, 2)], none)` and `atomTable phiRef4 40` to
      `[(2, [4, 3]), (1, [4, 3]), (0, [])]` -- both asserted as new `#guard_msgs` cases, serving as
      a second regression guard on the repair alongside `phiRef1`'s.)*
- [x] Update `phiRef4`'s docstring to state what it actually is.
- [x] Re-point the file's module comment and "Verdict: REFUTED" narrative at the repaired calculus.
      The `#guard_msgs` values are a regression guard on the defect, and the defect is now removed —
      say so, and preserve the pre-repair values in prose as the durable record of what was
      refuted, following the `intExpandBranches_openBranch_sat` counter-instance precedent
      (`Scheme.lean` near `:6805`/`:6999`) of keeping the refutation legible after the repair.
      *(Added a "Post-repair status" paragraph at the top of the module doc, reframed the "Net:"
      recipe conclusion as pre-repair history, and retitled/rewrote "Verdict: REFUTED" to
      "Verdict: REPAIRED (machine-verified) -- pre-repair defect record below", preserving the
      full pre-repair mechanism description as an explicitly-labeled historical record.)*
- [x] Record in the same file that `IFimpAccess` and `¬ forces φ @0` already held over the
      augmented frame in the baseline, and that `hpers` was the sole missing ingredient (report §3)
      — this sharpens the inherited frame-adequacy table and is worth not losing.
      *(Recorded in the rewritten "Verdict: REPAIRED" section.)*

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Files to modify**:
- `CslibTests/BetaSplitRefutation.lean` - `phiRef4` promotion, docstrings, module narrative

**Verification**:
- `lake build CslibTests` succeeds with the new `phiRef4` assertions.
- The pre-repair refutation values remain findable in the file as prose.

**Confirmed** (this dispatch): `lake build CslibTests.BetaSplitRefutation` green (972 jobs),
full `lake build` and `lake test` both green, `lake exe lint-style` clean. Sorry count unchanged
at 2, axiom count unchanged at 26.

---

### Phase 5: The freeze lemma [NOT STARTED]

**Goal**: Prove the one genuinely new obligation the repair creates — under beta-priority, no arm
of `go` adds a positive entry at a world that already carries a recorded loop-back. Additive; the
snapshot-free `IReuseContain` that consumes it lands in Phase 6.

**Tasks**:
- [ ] State the freeze lemma. Informally (report §5.4): when the world-creating arm is reached, the
      first pass returned `none`, so nothing on the branch is pending; afterwards formulas are only
      added at the newly created leaf world or pushed **downward** by `applyAllTImpRules`' copy
      channel and `intTImpRule`, both of which write only to descendants; neither `x` nor `w` is a
      descendant of a world created after them, so their positive content is frozen.
- [ ] Obtain the first-pass-empty hypothesis at the world-creating arm by unfolding
      `intStepBranchPrio` — report §5.3 notes it is available directly there.
- [ ] Prove it. The downward-only property of the copy channel is the load-bearing input; check
      whether an existing lemma about `applyAllTImpRules` / `intTImpRule` target labels already
      supplies it before proving a new one.
- [ ] If the lemma resists: **escalate to V2, do not weaken `IReuseContain`.** Record the blocker
      and stop the phase at `[BLOCKED]` rather than introducing a sorry. Phases 1-4 remain landed
      and independently valuable.

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: local

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - the freeze lemma, placed beside
  the `IReuseContain` family (currently `:6814`ff)

**Verification**:
- `lake build` of `Scheme.lean` succeeds.
- Zero new sorries, zero new axioms — `lean_verify` the new lemma.
- No existing declaration modified.

---

### Phase 6: Snapshot-free `IReuseContain`, re-threaded through the `key` induction [NOT STARTED]

**Goal**: Drop the snapshot existential. This is the mint-time weakening the defect forced, and the
repair is what makes dropping it possible.

**Tasks**:
- [ ] Restate `IReuseContain` (`Scheme.lean:6814`) with `bSnap := b`:
      `∀ x l, (x, l) ∈ lbEdges → ∀ χ, (⟨.pos, χ, l⟩ : ISF Atom) ∈ b → (⟨.pos, χ, x⟩ : ISF Atom) ∈ b`.
- [ ] `IReuseContain_snoc` (`:6837`) already establishes the snoc case from
      `intFImpReuseWitnessAnc?_spec`'s `hcont` conjunct with `bSnap := b` — confirm it survives the
      restatement essentially unchanged.
- [ ] Replace `IReuseContain_mono` (`:6824`) with the Phase 5 freeze lemma at each of its use sites
      in `intExpandBranches_openBranch_sat`'s induction. `IReuseContain_mono` is only provable
      *because* of the snapshot, so it does not survive; every site must move to the freeze lemma.
- [ ] Update the `IReuseContain` docstring, which currently explains at length why the bare
      current-branch claim was avoided ("the genuinely large post-reuse closure lemma, not this
      export"). That reasoning is now superseded — say what changed and why, rather than deleting
      the note.
- [ ] Confirm `IAllReuseContain` (`:6856`) and the list-companion lemmas follow through.

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: full

**Scope Hypothesis**: `IReuseContain_mono` has approximately six use sites inside the induction
(observed at `Scheme.lean` :7042, :7139, :7249, :7380, plus further occurrences beyond :7432).
Confirm the exact set with `grep -n IReuseContain_mono` before editing and report the true count;
the induction is described elsewhere in the file as 10-case, so the true number may be higher.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - `IReuseContain`,
  `IReuseContain_snoc`, removal of `IReuseContain_mono`, and the induction sites

**Verification**:
- Full `lake build` succeeds.
- `grep -c IReuseContain_mono` returns 0.
- Zero new sorries, zero new axioms.

---

### Phase 7: Export augmented-frame positive persistence [NOT STARTED]

**Goal**: Give `intExpandBranches_openBranch_sat` a conclusion that carries positive persistence
over the augmented frame, which is the missing ingredient the report identified.

**Tasks**:
- [ ] Decompose augmented-frame persistence into raw-edge persistence (`IPosPersistRaw`, already
      sorry-free) plus the loop-back edges (the strengthened `IReuseContain` from Phase 6), per
      report §5.3.
- [ ] Chain them along `ReflTransGen`. The report names the model to follow: this is the same
      tail-peeling move as `openBranch_rawEdges_upward_closed`.
- [ ] Extend `intExpandBranches_openBranch_sat`'s conclusion (currently
      `IFimpAccess edges b ∧ IPosPersistRaw rawEdges b ∧ IReuseContain lbEdges b ∧ ...`, `:6940`)
      with the derived persistence fact, or expose it as a separate corollary if that keeps the
      induction's invariant set smaller. Prefer the corollary if the induction does not need the
      new fact threaded through it.
- [ ] Check the shape matches `truthLemma`'s `hpers` parameter exactly:
      `∀ (χ) (x y), isAccessible edges x y = true → (⟨.pos, χ, x⟩ : ISF Atom) ∈ b →
      (⟨.pos, χ, y⟩ : ISF Atom) ∈ b`.

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: interface

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` -
  `intExpandBranches_openBranch_sat` conclusion or new corollary

**Verification**:
- Full `lake build` succeeds.
- The exported fact unifies with `truthLemma`'s `hpers` argument — demonstrate with a
  type-checking `example` or by direct use in Phase 8.
- Zero new sorries, zero new axioms.

---

### Phase 8: Discharge `openBranch_countermodel` [NOT STARTED]

**Goal**: Replace the whole-existential `sorry` with a direct `truthLemma` instantiation at the
augmented frame. This is the phase that interacts with task 605.

**Tasks**:
- [ ] **First**, detect the landed statement shape. Read `openBranch_countermodel`'s signature
      (currently around `Scheme.lean:8014`) and check whether 605's modelBot upward-closure
      conjunct is present. Do not assume either way; both branches are legitimate.
- [ ] Instantiate `truthLemma` at the augmented frame, supplying `hfimp` from `IFimpAccess` (which
      the report §3 confirms already holds over the augmented frame for every measured formula) and
      `hpers` from Phase 7.
- [ ] Discharge `huc` (the valuation's upward-closure conjunct) and `hcm` (the `¬IForces`
      conjunct). Per report §3, conjunct 2 already held over the augmented frame in the baseline —
      `hpers` was the only gap, and Phase 7 closes it.
- [ ] If 605's `hbuc` conjunct is present: source it from 605's `openBranch_rawEdges_both_upward_closed`,
      which by design returns both upward-closure facts at one shared `edges`. Do **not** re-derive,
      weaken, or drop it, and do **not** revert the `MValid.{_, 0}` universe pin. If it is absent:
      discharge the two-conjunct shape and add an in-source note naming the exact seam where the
      third conjunct will thread, addressed to whoever reconciles 605 and 609.
- [ ] This phase edits 605's declared territory at the end of `Scheme.lean`. If 605 landed first,
      rebase onto its version rather than re-applying the pre-605 shape.
- [ ] Rewrite the `openBranch_countermodel` docstring. It currently carries a long
      frame-adequacy table asserting that "no candidate `edges` built from the algorithm's current
      output carries both predicates simultaneously" and that the residual obligation is open. That
      is true of the *pre-repair* calculus and false of the repaired one. Preserve the refuted-frame
      record as history — it explains why the repair exists — and state plainly what changed.

**Timing**: 2 hours

**Depends on**: 7

**Verification Tier**: full

**Scope Hypothesis**: 605's patch adds exactly one conjunct to this existential (verified by
reading `verified-shape-fix.patch` hunk at `@@ -8016,6 +8070,8 @@`, which inserts
`S.modelBot b w → S.modelBot b w'` and changes the `tableau_complete` destructuring from three
binders to four). Confirm against the tree as it actually stands when this phase runs — 605 may
have evolved past the patch.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - `openBranch_countermodel` proof
  and docstring

**Verification**:
- Full `lake build` succeeds.
- `lean_verify Cslib.Logic.PL.openBranch_countermodel` reports no `sorryAx` and no new axioms.
- `grep -c sorry` on `Scheme.lean` shows the live sorry count reduced by one (prose mentions of the
  word remain and are expected).

---

### Phase 9: The downstream `Completeness.lean` sorries and the 606 handoff [NOT STARTED]

**Goal**: Collapse the remaining downstream sorries and leave task 606 an accurate, non-misleading
record.

**Tasks**:
- [ ] Discharge `intuitionisticTableau_complete` (`Intuitionistic/Completeness.lean:170`).
      **It is not the bare one-liner the research report quotes.** The report's
      `exact h Nat (intExtractValuation _b) _huc 0` does not typecheck: `IValid` quantifies
      `World : Type v` while the countermodel frame is `Nat : Type 0`. This site needs the same
      `.{_, 0}` universe pin and the same `ULift` transport that 605 builds
      (`mvalid_descend` / `mvalid_universe_invariant` in `Minimal/DecisionProcedure.lean`). If 605
      has landed, route through those; if not, the transport bridge must be built here, and that
      is a scope increase worth surfacing rather than absorbing silently.
- [ ] Check `minimalTableau_complete` (`Minimal/Completeness.lean:166`) before editing it. Under
      605's option A this site is **already closed by 605** and needs nothing from this task. Only
      discharge it if it is genuinely still open.
- [ ] **Rewrite, do not delete, the in-source prohibition** at
      `Intuitionistic/Completeness.lean:164-170` and its counterpart in `Minimal/Completeness.lean`.
      Those notes forbid the one-liner *on the ground that* `openBranch_countermodel`'s conjunct is
      open and `_huc` therefore launders it. Phase 8 makes that ground false. The replacement note
      must say: the one-liner is now legitimate **because** the conjunct is genuinely discharged,
      and name the phase/lemma that discharged it. A reader who finds the one-liner with no
      explanation cannot tell honest discharge from laundering — which is precisely what task 606's
      description warns against.
- [ ] Update the "Notes on sorry" sections at the head of both files.
- [ ] Record the 605/609 reconciliation state for task 606: which conjuncts 609 discharged, which
      606 must thread from 605, and whether the universe pin was present when Phase 8 ran.

**Timing**: 1 hour

**Depends on**: 8

**Verification Tier**: interface

**Scope Hypothesis**: Two downstream sorries are assumed open at this point
(`Intuitionistic/Completeness.lean:170`, `Minimal/Completeness.lean:166`). Under 605's option A the
minimal one is already closed, making this phase's true scope one site, not two. Confirm by reading
both files before editing; report which sites were actually open.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - only if its sorry is still open

**Verification**:
- Full `lake build` succeeds.
- `lean_verify` on `intuitionisticTableau_complete` and `minimalTableau_complete`: no `sorryAx`, no
  new axioms.
- Live sorry count on this path is 0.

---

## Testing & Validation

- [ ] Full `lake build` green at the close of every phase, including the `CslibTests` lib.
- [ ] **Conformance gate**: `CslibTests/TableauConformance.lean`, all 20 rows, verdicts identical to
      the pre-change baseline. 14 IPC-valid rows `CLOSED`, 6 open rows `OPEN`, including row 20 (the
      complexity-9 divergence witness) at `intFuelExt φ0`.
- [ ] **Adequacy gate**: the 9-formula corpus (`phiRef1`-`phiRef4`, `exMiddle`, `dblNeg`, `peirce`,
      `deMorgan`, `dummett`) shows `IFimpAccess` failures empty, no positive-persistence violation,
      and `¬ forces φ @0`, all over the augmented frame.
- [ ] **Fidelity gate**: `branchesAgree` and `minBranchesAgree` both `true` after `goRaw` is updated
      — the recreation must continue to mirror the real algorithm.
- [ ] **Zero-debt gate**: `lean_verify` on every new or modified declaration reports no `sorryAx`
      and no new axioms. Net live sorry count on this path: 3 → 0.
- [ ] World creation is `≤` baseline (report measured `phiRef3` at 3 worlds vs baseline 4).

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - `isWorldCreating`,
  `intStepBranchPrio`, spec lemma
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - bridges, `IStepShape` re-basing,
  call-site swap, freeze lemma, snapshot-free `IReuseContain`, persistence export, discharged
  `openBranch_countermodel`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - discharged sorry, rewritten
  notes
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - discharged sorry, rewritten notes
- `CslibTests/BetaSplitRefutation.lean` - updated `goRaw`, reconciled assertions, promoted `phiRef4`,
  re-pointed narrative
- Possibly `CslibTests/{TableauConformance,WitnessProbe,WitnessSearch3,MinProbe}.lean` - only if the
  Phase 3 corpus run flags them
- `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/summaries/01_beta-priority-repair-summary.md`

## Rollback/Contingency

- **Phases are individually revertible and the natural stopping points are real.** Phase 3 is the
  standalone-valuable milestone: verdict-preserving, strictly fewer worlds created, no new proof
  debt. Stopping after Phase 4 leaves the calculus repaired and the test corpus honest, with the
  proof-side work deferred — a legitimate partial outcome, not a failure.
- **If the freeze lemma (Phase 5) fails**: escalate to V2 (provisional reuse with
  retract-on-violation), which the report measured as equally adequate and equally
  verdict-preserving. Its cost is a new `go` recursion arm, hence a new termination-measure case and
  a new case in every invariant threaded through the `key` induction. That is a re-plan, not an
  in-phase pivot. Do not weaken `IReuseContain` to make the phase close.
- **Never pursue V3.** It failed the termination gate at real fuel (no completion within ~25 minutes
  where baseline and V1/V2 each finished under ~10), destroys the forest property that
  `ForestComparable` / `IWorldsPlanted` / `IPosPersistRaw` are stated against, and its
  positive-propagation is the same shape as the recorded UNSOUND "Option B".
- **If Phase 8 conflicts with 605**: prefer 605's landed statement shape. 609 supplies the frame and
  the forcing conjunct; it has no claim on the modelBot conjunct or the universe pin.
- Git revert is per-phase. Phase 3 is `atomic-batch`, so its revert is the whole declared file set
  at once.
