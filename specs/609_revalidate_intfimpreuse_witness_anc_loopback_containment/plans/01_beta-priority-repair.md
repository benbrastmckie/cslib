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

### Phase 5: The freeze lemma [COMPLETED]

**Goal**: Prove the one genuinely new obligation the repair creates — under beta-priority, no arm
of `go` adds a positive entry at a world that already carries a recorded loop-back. Additive; the
snapshot-free `IReuseContain` that consumes it lands in Phase 6.

**Investigation note (discovered at implementation time, not pre-declared in Phase 1-4 planning)**:
The freeze lemma is TRUE (V1/beta-priority is NOT a dead end here), but it is substantially harder
than "check whether an existing lemma already supplies it" — it needs a genuinely NEW invariant,
not a single local lemma. Recorded here so the next dispatch does not have to re-derive this from
scratch.

Direct inspection confirms the mechanism report §5.4 describes, and pins down exactly why it is
global rather than local:
1. `applyAllTImpRules`/`applyPersistenceFixpoint`/`intTImpRule` (`Expansion.lean:157-192`,
   `Rules.lean:179-191`) all take the RAW parent-child `edges` parameter -- the same `edges` `go`
   threads as `pendingEdges`/`doneEdges` -- never the ghost augmented/loop-back edge list
   (`lbEdges`/`doneAug`, proof-side only, no runtime counterpart). Persistence propagation is
   therefore completely blind to loop-back edges and only ever pushes content along the fixed,
   append-only RAW TREE structure (ancestor to descendant in creation order).
2. At the exact moment a loop-back edge `(x, l)` is recorded (a reuse event, itself only reachable
   through `intStepBranchPrio`'s SECOND pass, i.e. only when `intStepBranchPrioFirstPass` returned
   `none`), EVERY world on the branch -- not just `l` -- has zero pending alpha/beta obligations
   (that is what "first pass returned `none` everywhere" means). In particular every RAW ANCESTOR
   of `l` is *also* exhausted at that moment.
3. Going forward, `l` (and every one of its raw ancestors) can only ever gain new content via (a)
   alpha/beta processing directly at that label -- impossible, since it has zero pending compound
   formulas and nothing new can ever add one (raw edges only grow by appending parent-child pairs
   for brand-new worlds; a world created LATER cannot be a raw ancestor of `l`, so `intTImpRule`
   fired from a later world can never target `l` or any of `l`'s ancestors), or (b) persistence
   copy from a raw ancestor gaining new content -- ruled out by the same freeze argument applied
   recursively up the (finite) ancestor chain.
4. This is therefore a GLOBAL, whole-induction invariant ("every label that was fully exhausted at
   some point stays exhausted forever, and its raw ancestors do too"), not a per-step transport
   fact like the `IReuseContain_mono` it replaces. It needs to be threaded through
   `intExpandBranches_openBranch_sat`'s induction as a NEW invariant alongside the existing R1 set
   (`IExpandedConsistent`/`ILabelBound`/`IPosPersistRaw`/etc.), most likely stated as something
   like "every raw-tree world with zero pending compound formulas keeps exactly the same
   `ISF` set at that label forever" (a per-label formula-set-pinning fact), proved by induction on
   the SAME `go.induct` skeleton the other R1 invariants already use, with the mint arm being
   where a NEW instance of the invariant gets established (for `l`, freshly exhausted, and
   transitively for its ancestors) and every arm needing to show it PRESERVES all previously
   established instances.
5. This is real, substantial new infrastructure -- comparable in shape (though narrower in scope)
   to the R1 invariant-threading work that spans Phases 1-11 of this plan's own lineage -- not a
   single lemma. A future dispatch resuming this phase should budget accordingly (likely closer to
   the plan's Phase 1+2 combined scale than the stated 2-hour estimate, mirroring Phase 3's own
   Scope Correction precedent) rather than attempting it inside a tight remaining-budget window.
   **This is not a reason to pivot to V2**: V2's retract-on-violation approach faces the identical
   "does this stay frozen" question in a different guise (a retracted/re-tried arm still needs to
   know its retraction doesn't disturb already-recorded containment elsewhere), so escalating to V2
   would not avoid this work, only relocate it.

**Progress note (this dispatch, resuming from the Investigation note above)**: the mechanism was
re-derived independently from first principles (confirming point 1-5 above) and sharpened into a
concrete, mostly-landed formalization. Six new sorry-free, axiom-clean declarations are committed
(`lean_verify`/`lake env lean #print axioms` confirm `[propext, Quot.sound]` and/or
`Classical.choice` only on every one — no `sorryAx`, no new axioms):

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean`: `isRuleShape` (a bare
  `(sign, formula)`-shape predicate, `nextWorld`/`b`-independent) and
  `intApplyRuleFull_notApplicable_iff` (`intApplyRuleFull sf nw b = .notApplicable ↔ isRuleShape
  sf = false`, for every `nw`/`b`).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`: `IFrozenBelow w0 e b` (every
  formula on `b` labeled below `w0` is world-creating, already in `e`, or ruleless) and
  `intStepBranchPrioFirstPass_none_frozen` (the checkpoint entry point: `intStepBranchPrioFirstPass
  b e nextWorld = none → IFrozenBelow nextWorld e b`, i.e. exactly the moment `intStepBranchPrio`
  falls through to its world-creating second pass).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (beside `IPosPersistRaw`, ahead of
  `IReuseContain`): `IWorldHist_isAccessible_lt` (a new, general corollary of the already-landed
  `IWorldHist`/`IWorldHistCounter` invariants: `isAccessible edges w w' = true → w ≠ w' → w' < nw →
  w < w'` -- raw-edge reachability only ever flows from a smaller label to a larger one, no new
  invariant threading required), plus the freeze STEP lemma family
  (`IResultLabelsGe`/`IResultLabelsEq`/`IResultLabelsEq_imp_Ge`/
  `intApplyRuleFull_labels_eq_of_not_worldCreating`/`IFrozenBelow_intStepBranchPrio_ge`): given
  `IFrozenBelow w0 e b` and `w0 ≤ nw`, a SINGLE `intStepBranchPrio` step's output formulas are all
  labeled `≥ w0` (world-creating arm writes only at the fresh `nw`; every other arm writes only at
  the selected `sf.label`, which `IFrozenBelow` itself forces to be `≥ w0` on pain of contradicting
  `intStepBranchPrio_result_ne_notApplicable`). This is genuinely mechanism 3(a) from the
  Investigation note above, proved in full.

**What remains (mechanism 3(b) and the multi-step composition)**: `IFrozenBelow_intStepBranchPrio_ge`
covers ONE `intStepBranchPrio` step in isolation. Two further, larger pieces are still needed
before Phase 6 can consume a genuine drop-in replacement for `IReuseContain_mono`:
1. **Persistence-fixpoint preservation** (mechanism 3(b)): show `applyPersistenceFixpoint`/
   `applyAllTImpRules`, applied at the TOP of each `go` call, also cannot write below the checkpoint
   `w0`. Sketch, not yet formalized: the ALREADY-landed `applyAllTImpRules_copy_complete_of_fixpoint`
   (`Scheme.lean` above `IPosPersistRaw`) plus the NEW `IWorldHist_isAccessible_lt` together show the
   generalized-copy channel is vacuous below `w0` whenever `IPosPersistRaw` already holds there (any
   accessible source reaching a target `w' < w0` is itself `< w0` by the label-order fact, and
   `IPosPersistRaw` -- already a continuously-threaded invariant of `bPers` at every induction step
   -- has no gap to fill there). `intTImpRule`'s OWN direct `T(ψ)@w'` clause additionally needs
   `IExpandedConsistent` (already landed) plus a branch-consistency fact (no complementary `T`/`F`
   pair -- should already be available from the open-branch path) to show its precondition
   `T(φ)@w' present ∧ T(ψ)@w' absent` cannot hold below `w0` once the source `T(φ→ψ)` is itself
   already-expanded there.
2. **Composition across MANY steps, i.e. actually threading `IFrozenBelow` through
   `intExpandBranches_openBranch_sat`'s induction** (all four `go.induct` blocks) so that the
   checkpoint fact at loop-back-record time survives all the way to whatever `openBranch b` is
   finally returned. This is Phase 6's original mandate ("replace `IReuseContain_mono`... at each
   of its use sites") and is where the genuinely large remaining effort lives -- item 1 above is a
   prerequisite lemma for it, not a substitute.

Given the standalone STEP lemma (item, not composition) is now fully landed and verified, a future
dispatch resuming Phase 5/6 should start from `IFrozenBelow_intStepBranchPrio_ge` and item 1's
sketch above, rather than re-deriving the mechanism a third time. Escalating to V2 remains
unwarranted: nothing found this dispatch weakens that conclusion.

**Progress note (this dispatch, completing mechanism 3(b) and closing Phase 5)**: the persistence
half sketched above is now fully formalized and landed, sorry-free and axiom-clean, in
`Scheme.lean` immediately after `IFrozenBelow_intStepBranchPrio_ge`:

- `isf_any_mem`: a small extraction helper (a `List.any` witness over the `(sign, formula, label)`
  triple pins down the exact `ISF Atom` membership), mirroring the existing extraction pattern in
  `applyAllTImpRules_copy_complete_of_fixpoint`. Used throughout the two lemmas below.
- `applyAllTImpRules_agrees`: the single-round case. Given the checkpoint facts about a FIXED
  branch `b` (`IFrozenBelow w0 e b`, `IPosPersistRaw edges b`, `IExpandedConsistent b e`, an
  open-branch "no complementary `T(χ)`/`F(χ)` pair below `w0`" hypothesis, and the
  `IWorldHist`/`IWorldHistCounter` pair `IWorldHist_isAccessible_lt` needs), one round of
  `applyAllTImpRules` applied to any `bv` that CONTAINS `b` and AGREES with `b` below `w0`
  (`∀ sf ∈ bv, sf.label < w0 → sf ∈ b`) still agrees with `b` below `w0`. The genCopies channel is
  closed directly from `IPosPersistRaw` (no `w0` restriction needed: any copy it would produce is
  already present). The ψ-consequence channel (`intTImpRule`'s direct clause) is closed exactly as
  sketched: `IWorldHist_isAccessible_lt` pins the source label below `w0` too; `IPosPersistRaw`
  propagates the SOURCE implication's copy to the target label; `IFrozenBelow` forces that copy to
  be `e`-expanded; `IExpandedConsistent` reads off the Fitting-split resolution
  (`F(φ)@w' ∨ T(ψ)@w'`); and the open-branch consistency hypothesis rules out `F(φ)@w'` given
  `T(φ)@w'` is exactly `intTImpRule`'s own firing precondition -- leaving `T(ψ)@w'` already
  present, so nothing new is ever added.
- `applyPersistenceFixpoint_agrees`: the fuel-recursive composition of the single-round case across
  `applyPersistenceFixpoint`'s own internal fixpoint recursion (the fuel loop WITHIN one `go` call,
  not the outer `go`-to-`go` recursion, which stays Phase 6's territory). The fixed branch `b` and
  all its checkpoint facts never change across rounds; only the varying branch `bv` (and its
  agreement-with-`b`-below-`w0` witness) is threaded as an explicit universally-quantified
  induction target, which sidesteps needing to `generalizing` the fixed hypotheses.
- `IFrozenBelow_applyPersistenceFixpoint`: **mechanism 3(b), landed** -- the direct corollary at
  `bv := b` (reflexive agreement/monotonicity): `applyPersistenceFixpoint b edges fuel`, run at the
  top of every `intExpandBranches.go` call, preserves `IFrozenBelow w0 e`.

This closes every Task item below: the freeze lemma (both the step half,
`IFrozenBelow_intStepBranchPrio_ge`, and the persistence half,
`IFrozenBelow_applyPersistenceFixpoint`) is now fully proved. Phase 5 is complete. What remains is
Phase 6's own, separately-scoped mandate: composing these per-`go`-call facts across the OUTER
`go`-to-`go` recursion (all four `go.induct` blocks) to actually replace `IReuseContain_mono` at
its use sites -- a distinct, larger induction-threading task, not a continuation of Phase 5's own
proof obligations.

**Tasks**:
- [x] State the freeze lemma. Landed as `IFrozenBelow` (`Expansion.lean`) plus the `IResultLabelsGe`
      family (`Scheme.lean`) -- the checkpoint precondition and the single-step conclusion,
      respectively. *(deviation: altered -- decomposed into a checkpoint predicate + step lemma
      rather than one monolithic statement, since the eventual multi-step composition (item 2
      above) needs both pieces separately)*
- [x] Obtain the first-pass-empty hypothesis at the world-creating arm by unfolding
      `intStepBranchPrio` — landed as `intStepBranchPrioFirstPass_none_frozen`.
- [x] Prove it (the single-step case). Landed as `IFrozenBelow_intStepBranchPrio_ge`; the
      "downward-only" fact this task anticipated is supplied by `IWorldHist_isAccessible_lt`.
- [x] Prove the persistence half (mechanism 3(b)). Landed as `IFrozenBelow_applyPersistenceFixpoint`
      (via `applyAllTImpRules_agrees`/`applyPersistenceFixpoint_agrees`), sorry-free and
      axiom-clean. *(deviation: this task item was not separately enumerated in the plan's original
      task list -- added here since it is exactly "the persistence half" the Investigation note's
      point 3(b) named as still open, and closing it is what completes Phase 5)*
- [ ] If the lemma resists: escalate to V2. *(deviation: not applicable -- the lemma does not
      resist; the freeze claim is confirmed true and BOTH the step-level and persistence-level
      cases are proved. No scope remains at the Phase 5 level; V2 was never warranted)*

**Timing**: 2 hours (original estimate; actual across the two dispatches that completed this
phase: full step lemma plus the persistence half and its fuel-recursive composition, all landed
sorry-free -- closer to the Phase 1+2 combined scale flagged by the Investigation note, as
anticipated)

**Depends on**: 3

**Verification Tier**: local

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` - `isRuleShape`,
  `intApplyRuleFull_notApplicable_iff` *(deviation: altered -- plan named only `Scheme.lean`; the
  bare-shape characterization of `intApplyRuleFull` belongs beside its definition)*
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - `IFrozenBelow`,
  `intStepBranchPrioFirstPass_none_frozen` *(deviation: altered -- same rationale, beside
  `intStepBranchPrioFirstPass`)*
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - `IWorldHist_isAccessible_lt`
  (beside `IWorldHist_forestComparable`), the freeze step lemma family (beside `IPosPersistRaw`,
  ahead of `IReuseContain` as planned), and (this dispatch) `isf_any_mem`,
  `applyAllTImpRules_agrees`, `applyPersistenceFixpoint_agrees`,
  `IFrozenBelow_applyPersistenceFixpoint` (immediately after the step-lemma family, still ahead of
  `IReuseContain`)

**Verification**:
- `lake build` of `Rules.lean`/`Expansion.lean`/`Scheme.lean` succeeds (confirmed; full `lake build`
  green, `lake test` green, verdict-unchanged from the Phase 3/4 baseline -- see the phase-closing
  CI run below).
- Zero new sorries, zero new axioms — `lean_verify` on all ten new declarations (six from the prior
  dispatch, four this dispatch) confirms no `sorryAx`, only `propext`/`Quot.sound`/
  `Classical.choice`.
- No existing declaration modified (confirmed: diff is purely additive across all three files).

---

### Phase 6: Snapshot-free `IReuseContain`, re-threaded through the `key` induction [IN PROGRESS]

**Goal**: Drop the snapshot existential. This is the mint-time weakening the defect forced, and the
repair is what makes dropping it possible.

**Investigation note (this dispatch, not pre-declared in Phase 1-5 planning)**: the mechanism was
worked out in full and is TRUE, but this dispatch made a deliberate decision NOT to force the
threading through in a single sitting, because a second, previously-unforeseen gap surfaced
mid-derivation that needs its own new lemma before the induction-threading can even start. Recorded
here in full so the next dispatch does not have to re-derive it. **Zero code was changed this
dispatch** (no edits to any `.lean` file); the tree is exactly as left by the Phase 5 closing commit
(`ab3f283e`).

1. **The target shape, confirmed.** Dropping the snapshot means `IReuseContain`'s bare claim
   (`(pos,χ,l)∈b → (pos,χ,x)∈b` for the CURRENT, growing `b`) can only stay true forever if nothing
   NEW ever arrives at label `l` after the edge `(x,l)` is recorded — i.e. exactly Phase 5's freeze
   mechanism, instantiated at the checkpoint `w0 := l + 1` (not `l` itself: `IFrozenBelow` covers
   labels strictly `< w0`, and `l + 1` is the smallest threshold that also covers `l`). This
   threshold is available for free at record time: `IFrozenBelow nwH eH bPers` already holds there
   (`intStepBranchPrioFirstPass_none_frozen` + the checkpoint), `l < nwH` (`ILabelBoundStrict`), and
   `IFrozenBelow` is downward-closed in its threshold (`w0' ≤ w0 → IFrozenBelow w0 e b →
   IFrozenBelow w0' e b`, immediate from the definition, not yet stated as its own lemma but trivial
   to add), so `IFrozenBelow (l+1) eH bPers` follows directly.
2. **The needed companion invariant.** A new per-edge predicate, sketched as
   `IReuseFrozen (lbH : IEdges) (e : List (ISF Atom)) (b : IBranch Atom) : Prop := ∀ x l, (x,l) ∈
   lbH → IFrozenBelow (l + 1) e b`, threaded ALONGSIDE `IAllReuseContain` via a new 3-list zip
   `IAllReuseFrozen` over `(bs, expSets, lbSets)` (mirroring `IAllWorldHist`'s 4-list-zip template
   at `Scheme.lean:3873` — `IAllReuseContain`'s existing 2-list zip is not wide enough since it does
   not carry the per-branch expanded set `e` that `IFrozenBelow` needs). This is what replaces
   `IReuseContain_mono` at every use site: given `IReuseFrozen` for the OLD edges plus Phase 5's two
   composition lemmas, the newly-added content at each step is provably disjoint from every
   recorded edge's frozen label, so containment survives branch growth without a snapshot.
3. **The gap Phase 5's own lemmas do not yet cover.** `IFrozenBelow_applyPersistenceFixpoint` /
   `applyAllTImpRules_agrees` (both landed, `Scheme.lean` ~7132-7292) require `hpp : IPosPersistRaw
   edges b` about the SAME `b` that is fed into `applyPersistenceFixpoint b edges fuel` — i.e. about
   the PRE-fixpoint branch. Checked directly: `IPosPersistRaw` does NOT hold for `bh` (the branch
   entering a go-call, before its own persistence pass) in general — it is exactly what
   `applyPersistenceFixpoint` exists to ESTABLISH, via `applyPersistenceFixpoint_copy_complete`,
   which only ever concludes `IPosPersistRaw edges (applyPersistenceFixpoint b edges fuel)` (the
   POST-fixpoint output), never about the pre-state. So `hpp` cannot be discharged fresh at every
   go-call the way `hIC_bPers`/`hACC_bPers`/etc. are. The correct instantiation is instead to hold
   `b` FIXED at the ORIGIN — the `bPers` at the exact go-call where `(x, l)` was recorded (case6,
   `hARC_new`'s site) — where `IPosPersistRaw edgesH_origin bPers_origin` IS freshly derivable
   (same `applyPersistenceFixpoint_copy_complete` call case6 already needs for other purposes), and
   let `bv` range over every LATER go-call's own branch, composing `applyAllTImpRules_agrees`
   per-round with `b` pinned at the origin (mirroring exactly how the OLD `bSnap` witness was
   pinned once and never re-derived).
4. **The newly-discovered second gap.** That "origin-pinned" composition also pins `edges` at the
   origin's `edgesH_origin` inside `hpp`/`hacc`, but the ACTUAL round being composed at a later
   go-call runs against that LATER go-call's own (larger) raw-edge list `edgesH' ⊇ edgesH_origin`
   (raw edges only grow, one new pair per minted world). `applyAllTImpRules_agrees`'s proof uses
   `hacc : isAccessible edges w w' = true` (at whichever `edges` is supplied) to justify `hpp`'s
   copy-propagation, so the origin-pinned and later-actual edge lists must be reconciled: I need
   `isAccessible edgesH_origin w w' = isAccessible edgesH' w w'` for `w' < w0` (both labels already
   existing at origin time). Checked: `isAccessible_append_mono` (`Scheme.lean:367`) only gives ONE
   direction (append never LOSES reachability) — the REVERSE (append never GAINS reachability whose
   target is not the fresh node itself) is not yet stated anywhere in the file. It is TRUE and
   should be a clean, self-contained proof: a freshly-minted edge `(nw, l)` has `nw` appearing
   NOWHERE as a parent-slot (first component) in the existing edge list (it is a brand-new node), so
   any DFS path that routes through `(nw, l)` reaches a dead end at `nw` — `nw` has no outgoing
   edges of its own in either the old or the extended list (the sole edge mentioning `nw`, `(nw,
   l)`, has `nw` in the child slot, not the parent slot) — so no reachability witness for a target
   `w' ≠ nw` can newly depend on it. A full proof needs a `isAccessible.go`-level induction
   parallel to `isAccessible_go_append_mono`'s (`Scheme.lean:316`) but concluding the REVERSE
   implication under the freshness hypothesis; sketch: `isAccessible.go (edges ++ [(nw, l)]) target
   current fuel = true ∧ target ≠ nw → isAccessible.go edges target current fuel = true`, by
   induction on fuel, splitting on whether the found child candidate came from an old edge
   (immediate) or from the new edge (only possible when `current = l`, giving candidate `child =
   nw`; since `target ≠ nw` the recursive call needs `isAccessible.go _ target nw fuel' = true`, but
   `nw` has zero candidate children in `edges ++ [(nw, l)]` under the freshness hypothesis, so that
   recursive call is vacuously `false`, contradiction — this branch cannot occur).
5. **Concrete task list for the next dispatch, in dependency order** (none of this is committed
   yet): (a) `isAccessible_append_eq_of_fresh` (or similar name) per point 4's sketch; (b) generalize
   `applyAllTImpRules_agrees`/`applyPersistenceFixpoint_agrees` (or add a corollary) to compose
   across a GROWING `edges ⊇ edges₀` using (a) to relate the origin's `hpp` to the current round's
   `hacc`; (c) land `IReuseFrozen`/`IAllReuseFrozen` per point 2 with the append/map_const companion
   lemmas the existing zip types all carry; (d) thread `IAllReuseFrozen` through the `key` suffices
   statement of `intExpandBranches_openBranch_sat` (`Scheme.lean:7434` as of this dispatch) alongside
   `IAllReuseContain`; (e) replace the six confirmed `IReuseContain_mono` use sites (below) with the
   composed freeze argument, and extend `IReuseContain_snoc`'s call site (case6, `Scheme.lean:7958`
   as of this dispatch) to also establish the newly-recorded edge's `IReuseFrozen` witness per
   point 1; (f) only then restate `IReuseContain` itself to drop the snapshot (this is a small,
   final step once (a)-(e) are in place, since the containment claim itself does not change shape —
   only what justifies its preservation does).

**Progress note (this dispatch, item (a) landed)**: task-list item (a), the go-level reverse-
direction `isAccessible` lemma, is now landed sorry-free and axiom-clean, right after
`isAccessible_append_mono`/`intAccessPreorder_mono_append` (`Scheme.lean:386-461` as of this
dispatch, under a new `### Reverse-direction append monotonicity (fresh-target case)` section):

- `isAccessible_go_fresh_dead_end` (private): from a fresh node `nw` (never a parent-slot member
  of `edges`, and `l ≠ nw`), the extended list `edges ++ [(nw, l)]` has no outgoing candidates at
  all from `nw`, at ANY fuel -- the standalone "dead end" fact the main lemma's new-edge case
  needs.
- `isAccessible_go_append_eq_of_fresh` (private): `isAccessible.go (edges ++ [(nw, l)]) target
  current fuel = true → target ≠ nw → isAccessible.go edges target current fuel = true`, at
  MATCHING fuel on both sides (i.e. it is fuel-preserving, not fuel-adjusting). Proved by
  induction on fuel exactly per point 4's sketch: the "candidate came from an old edge" case
  transfers directly; the "candidate is the new edge itself" case is ruled out via the dead-end
  lemma above (target ≠ nw forces the recursive call into `go ... nw fuel'`, which the dead-end
  lemma shows is always `false`, contradicting the hypothesis).

**Deliberately NOT attempted this dispatch: a wrapper-level `isAccessible` (non-`.go`) form of
the same fact.** This surfaces a THIRD gap, not previously identified, and is recorded here rather
than forced: `isAccessible (edges ++ [(nw, l)]) w w' = true` unfolds (via `edges ++ [(nw,
l)]).length = edges.length + 1`) to `go (edges++[(nw,l)]) w' w (edges.length + 1) = true` --
i.e. the go-level lemma above, invoked at fuel `edges.length + 1`, gives `go edges w' w
(edges.length + 1) = true`, ONE MORE than `isAccessible edges w w'`'s own fuel bound
(`edges.length`). Unlike the FORWARD direction (`isAccessible_append_mono`, which goes from a
SMALLER fuel bound up to a LARGER one and closes via the already-landed, upward-only
`isAccessible_go_fuel_mono`), the reverse direction needs to go DOWN by one unit of fuel on the
UNEXTENDED list -- and downward fuel reduction is NOT, in general, valid for a fuel-bounded DFS
with `List.any` search (more fuel can only ever preserve or extend what is reachable, never the
converse) without an extra "fuel `edges.length` already suffices, extra fuel changes nothing"
saturation fact. That saturation fact is very plausibly TRUE here specifically because `edges`
is provably a genuine forest under this file's own invariants (every child has exactly one parent,
established once at mint time and never revisited -- see `IWorldHistCounter`
(`nw = edges.length + 1`, `:3527`) and the already-landed `edges_shape_of_worldHist` /
`parAncestor_of_isAccessible` pigeonhole argument, `:3563-3599`, which already derives the
`parAncestor`-vs-`isAccessible` coincidence needed to make this rigorous) -- but proving it
requires threading that `par`/`nw` context through a bare `edges`-only lemma, which is
out of scope for a standalone `isAccessible` fact. Task-list item (b) ("generalize
`applyAllTImpRules_agrees`/`applyPersistenceFixpoint_agrees`... to compose across a GROWING
`edges ⊇ edges₀`") already has exactly this context available (`nw`, `par`, `IWorldHistCounter`)
at its call site, so the natural place to close this gap is inside item (b)'s own composition
proof, not as a preliminary, contextless wrapper lemma. Recorded here so the next dispatch does
not have to re-derive the diagnosis: reach for `IWorldHistCounter`/`edges_shape_of_worldHist`/
`parAncestor_of_isAccessible` first, rather than attempting a generic fuel-saturation lemma about
arbitrary `IEdges` lists.

**Scope Hypothesis, resolved this dispatch**: `grep -n IReuseContain_mono` finds exactly six use
sites, all inside `intExpandBranches_openBranch_sat`'s induction (`Scheme.lean:7493-8685` as of this
dispatch) and nowhere else in the file: `:7623` (case2, bh→bPers persistence transport), `:7720`
(case4, same), `:7838` (case5, bPers→extendMany step transport), `:7968` (case6, bh→bPers
persistence transport, alongside the `IReuseContain_snoc` call at `:8049` for the NEW edge),
`:8226` (case7, bPers→extendMany mint-arm step transport), `:8396` (case8, bPers→branch
step transport, once per BETA child). The induction has 10 cases total (`case1`-`case10`); only
cases 2, 4, 5, 6, 7, 8 touch `IAllReuseContain` at all (case1/3/9/10 are dead-end/absurd arms).
**Updated this dispatch** (`+90` line offset from this dispatch's own insertion of the new
`isAccessible_go_append_eq_of_fresh` lemma family ahead of line 386 — see the Progress note
above); the `key` suffices statement of `intExpandBranches_openBranch_sat` referenced in task-list
item (d) above is at `Scheme.lean:7524`. Line numbers will drift again on the next dispatch's own
insertions — re-run the grep before editing, per this plan's own delta-recording convention.

**Progress note (this dispatch, items (b) and (c) landed)**: this dispatch closes task-list items
(b) and (c) in full, sorry-free and axiom-clean (`lean_verify`: `propext`/`Classical.choice`/
`Quot.sound` only, matching the file's existing axiom profile). Zero of items (d)-(f) attempted;
Phase 6 remains `[IN PROGRESS]`.

1. **Item (b), landed via a NEW reconciliation lemma rather than item (a)'s go-level lemma.**
   Point 4's "newly-discovered second gap" (relating an ORIGIN round's `hpp : IPosPersistRaw
   edges_small b` to a LATER round's own bigger `edges_big ⊇ edges_small`) is closed by
   `isAccessible_reconcile_of_worldHist` (`Scheme.lean:3879-3960` as of this dispatch, right after
   `IWorldHist_isAccessible_lt`, under a new `### Edge-list reconciliation across growth` section):
   given `IWorldHist`/`IWorldHistCounter` witnesses at both `edges_small` (`nw_small`) and
   `edges_big` (`nw_big`), `nw_small ≤ nw_big`, `edges_small ⊆ edges_big` (list membership), and a
   target `w' < nw_small`, any `isAccessible edges_big w w' = true` reconciles down to
   `isAccessible edges_small w w' = true`. **Deliberately proved via `parAncestor`, not the
   go-level fresh-append lemma** (`isAccessible_go_append_eq_of_fresh`, item (a)): any
   `parAncestor`-chain ending at a target `c < nw_small` stays entirely inside `[0, c]`
   (`parAncestor_le`'s descent bound), hence entirely inside the domain where the two `IWorldHist`
   witnesses' `par` functions are FORCED to agree (`edges_shape_of_worldHist`'s uniqueness
   argument, using the `hsub` containment) — so the witness round-trips through the smaller `par`
   and `hWH_small`'s own (H1-acc) clause, at `edges_small`'s OWN canonical fuel. This sidesteps the
   fuel-mismatch gap 3 identified in the previous dispatch's Progress note entirely (no fuel
   arithmetic needed at all), confirming that dispatch's own prediction: "reach for
   `IWorldHistCounter`/`edges_shape_of_worldHist`/`parAncestor_of_isAccessible` first, rather than
   attempting a generic fuel-saturation lemma." Item (a)'s go-level lemma remains landed and
   correct but is NOT used by this reconciliation route; it may still be useful at a future
   go-call-local (non-wrapper) site, but is not required by items (b)-(f) as currently understood.

   Built on top of this bridge: `applyAllTImpRules_agrees_grow` and
   `applyPersistenceFixpoint_agrees_grow` (`Scheme.lean:7464-7625` as of this dispatch, immediately
   after `applyPersistenceFixpoint_agrees`, before `IFrozenBelow_applyPersistenceFixpoint`, under a
   new `### Growing-edges composition` section) are the literal growing-edges generalizations the
   task list asked for: identical
   proof shape to `applyAllTImpRules_agrees`/`applyPersistenceFixpoint_agrees`, except the
   checkpoint facts (`hfrz`, `hpp`, `hic`, `hcons`) stay pinned to `edges_small`/a fixed `b` while
   the round actually computed (`applyAllTImpRules bv edges_big`) runs against the bigger
   `edges_big`; every `hacc` witness the proof extracts from that computation is reconciled down to
   `edges_small` via `isAccessible_reconcile_of_worldHist` before being fed to `hpp`, while the
   label-order fact (`IWorldHist_isAccessible_lt`) is read off directly at `edges_big` (it needs no
   reconciliation). **Not yet wired into the induction** — these are free-standing lemmas, not yet
   invoked at any of the six `IReuseContain_mono` use sites; that wiring is item (e)'s job, and
   requires establishing at each use site the ACTUAL origin/later `IWorldHist` witnesses, the
   `nw_small ≤ nw_big` fact, and the `edges_small ⊆ edges_big` containment fact (raw edges only
   ever grow by append across the induction — true structurally, but not yet packaged as its own
   reusable "raw edges are append-only" lemma; the next dispatch may need one).

2. **Item (c), landed in full per the task list's literal wording.** `IReuseFrozen`
   (`Scheme.lean:7741-7742` as of this dispatch, right after `IAllReuseContain_map_const`) is
   `∀ x l, (x, l) ∈ lbH → IFrozenBelow (l + 1) e b`, exactly point 2's sketch. Companions landed
   (`Scheme.lean:7750-7815` region, `IReuseFrozen_snoc`/`IAllReuseFrozen`/`IAllReuseFrozen_append`/
   `IAllReuseFrozen_map_const`):
   - `IFrozenBelow_downward` (`Expansion.lean`, right after `IFrozenBelow`'s definition): the
     "trivial to add" downward-closure-in-threshold lemma point 1 named (`w0' ≤ w0 →
     IFrozenBelow w0 e b → IFrozenBelow w0' e b`), a one-line consequence of `IFrozenBelow`'s
     definition.
   - `IReuseFrozen_snoc`: extends `IReuseFrozen` by a newly recorded loop-back edge `(x, l)`,
     given the freeze checkpoint `IFrozenBelow (l + 1) e b` directly as a hypothesis (mirrors
     `IReuseContain_snoc`'s shape).
   - `IAllReuseFrozen`: the 3-list zip over `(bs, expSets, lbSets)` point 2 calls for, mirroring
     `IAllWorldHist`'s 4-list-zip template (NOT `IAllReuseContain`'s narrower 2-list zip, which
     lacks the per-branch expanded set `e` that `IFrozenBelow` needs) — plus `_append` and
     `_map_const` companions, mirroring `IAllWorldHist_append`/`IAllWorldHist_map_const` exactly.

   **Deliberately NOT attempted**: any "does `IReuseFrozen` survive branch growth on its own"
   lemma. Unlike `IReuseContain_mono` (a one-liner, since its snapshot witness is literally
   contained by hypothesis), `IFrozenBelow` is NOT naively monotone under branch growth — its
   universal quantifier ranges over `∀ sf ∈ b`, so a BIGGER `b` is a STRICTLY STRONGER
   requirement, not a weaker one; genuine preservation needs the real freeze machinery
   (`IFrozenBelow_intStepBranchPrio_ge` + `IFrozenBelow_applyPersistenceFixpoint`/
   `applyPersistenceFixpoint_agrees_grow`), which is exactly what item (e)'s wiring is for. Do
   not attempt a cheap "IReuseFrozen_mono" shortcut in a future dispatch — it is not a one-liner.

**Re-grep before editing** (line numbers shift again on the next dispatch's own insertions,
`+~280` from this dispatch's combined insertion at three sites): `grep -n
"IReuseContain_mono\|private def IReuseFrozen\|private def IAllReuseFrozen\|applyAllTImpRules_agrees_grow\|isAccessible_reconcile_of_worldHist"
Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`. The six `IReuseContain_mono` use
sites (item (e)'s target), current as of THIS dispatch: `:7962` (case2), `:8059` (case4), `:8177`
(case5), `:8307` (case6, alongside the `IReuseContain_snoc` call at `:8388`), `:8565` (case7),
`:8735` (case8) — same case mapping as the previous dispatch's Scope Hypothesis paragraph above,
only the line numbers moved.

**Progress note (this dispatch, a THIRD gap found and closed at the design level -- item (c)'s
landed `IReuseFrozen`/`IAllReuseFrozen` do not actually support round-to-round preservation, and
this dispatch lands the fix as new, sorry-free, free-standing machinery)**: before attempting
items (d)-(f) as literally sequenced, this dispatch worked out WHY the previous dispatch's own
"do not attempt a cheap `IReuseFrozen_mono` shortcut" warning (immediately above) is not just
a warning about a missing one-liner, but a symptom of a real design gap in `IReuseFrozen` itself:

1. **The gap.** `IReuseFrozen lbH e b := ∀ x l, (x,l) ∈ lbH → IFrozenBelow (l+1) e b` states
   `IFrozenBelow` about the CURRENT `(e, b)` directly. This is provable at the EXACT round `(x,l)`
   is recorded (`intStepBranchPrioFirstPass_none_frozen`), but is NOT re-derivable at any LATER
   round: doing so needs `IFrozenBelow_applyPersistenceFixpoint`'s `hpp : IPosPersistRaw edges b`
   hypothesis about that round's own PRE-persistence branch (`bh`, not `bPers`) --
   checked directly against `IFrozenBelow_applyPersistenceFixpoint`'s actual signature
   (`Scheme.lean`, Phase 5 section) -- and `IPosPersistRaw` about a PRE-persistence `bh` does not
   hold in general (only `applyPersistenceFixpoint_copy_complete`-style derivation about the
   POST-persistence output does, exactly the same asymmetry the Phase 6 investigation note's
   point 3 already diagnosed for `IReuseContain`'s own transport). So `IAllReuseFrozen` cannot
   actually be threaded through `key` and re-established at every round the way `IAllReuseContain`
   is -- it would need a fresh `IFrozenBelow` derivation at every round that the file's own
   machinery cannot supply.
2. **The fix: origin-tracking.** `IReuseFrozenOrigin (φ0) (lbH) (e) (edges) (nw) (b) : Prop`
   (`Scheme.lean:7841` as of this dispatch, right after `IAllReuseFrozen_map_const`) replaces the
   CURRENT-state `IFrozenBelow` claim with a full EXISTENTIAL checkpoint snapshot per edge: the
   origin `(b_o, e_o, edges_o, nw_o)` at record time, carrying its own
   `IFrozenBelow`/`IPosPersistRaw`/`IExpandedConsistent`/consistency/`IWorldHist`/
   `IWorldHistCounter` facts, PLUS three monotonicity witnesses (`e_o ⊆ e`, `edges_o ⊆ edges`,
   `nw_o ≤ nw` -- the origin's own bookkeeping only ever grows into the current state) AND the
   actual freeze CONTENT as its own conjunct, `∀ sf ∈ b, sf.label < l+1 → sf ∈ b_o` (current
   content below the threshold already agrees with the origin). This is deliberately heavier than
   `IReuseFrozen` -- it is the SAME kind of "existential witness that survives forever" idea
   `IReuseContain`'s OLD `bSnap` snapshot already used, just decorated with enough checkpoint
   context to be RE-EXTENDABLE forward using machinery already on hand, rather than merely
   asserting containment directly.
3. **Four supporting lemmas landed, all sorry-free** (`Scheme.lean:7866-7944`):
   - `IReuseFrozenOrigin_frozenBelow`: derives `IFrozenBelow (l+1) e b` about the CURRENT `(e,b)`
     FROM the existential (`hagree` transports `sf ∈ b` down to `sf ∈ b_o`, the origin's own
     `hfrz` classifies it, and `e_o ⊆ e` lifts the `sf ∈ e_o` disjunct to `sf ∈ e`). This is what
     unlocks `IFrozenBelow_intStepBranchPrio_ge` at any later round WITHOUT needing fresh
     `IPosPersistRaw` about that round's own pre-persistence branch -- the actual fix for the gap.
   - `IReuseFrozenOrigin_snoc`: records a freshly-minted edge, using the CURRENT state as its own
     origin reflexively (mirrors `IReuseFrozen_snoc`, but threading the full checkpoint).
   - `IReuseFrozenOrigin_persist`: advances across ONE round's `applyPersistenceFixpoint` (same
     `e`/`edges`/`nw` throughout a round, only the branch grows `bh → bPers`) -- a direct corollary
     of `applyPersistenceFixpoint_agrees_grow` (item (b), already landed) at each edge's own origin.
   - `IReuseFrozenOrigin_extendMany`: advances across `Branch.extendMany bPers newForms`, GIVEN
     every element of `newForms` lands at a label `≥ l+1` (the label bound
     `IFrozenBelow_intStepBranchPrio_ge` supplies at each SIX-SITE use, composed with
     `IReuseFrozenOrigin_frozenBelow` above -- not yet wired at the sites themselves).
   - `IAllReuseFrozenOrigin`/`_append`/`_map_const` (`Scheme.lean:7951-8038`): the 5-list zip
     companion over `(bs, expSets, edgeSets, nws, lbSets)`, mirroring `IAllReuseFrozen`'s 3-list
     zip but extended with the per-branch-position `edges`/`nw` context this origin-tracked
     version needs to check its monotonicity conjuncts against, plus append/map_const companions
     mirroring the established template exactly.

   All eight declarations verified individually via `lean_verify`: axioms are a subset of the
   file's existing baseline (`propext`/`Classical.choice`/`Quot.sound`), zero sorries.

4. **Not yet done (items (d)-(f) remain fully open)**: `IAllReuseFrozenOrigin` is NOT yet threaded
   through `intExpandBranches_openBranch_sat`'s `key` statement (item (d)), the six
   `IReuseContain_mono` use sites are UNTOUCHED (item (e) -- wiring each site needs its own local
   `IWorldHist`/`hstep`/label-bound facts, already present in context at each site per the earlier
   Scope Hypothesis paragraph, composed with `IReuseFrozenOrigin_persist`/`_extendMany` above), and
   `IReuseContain` itself is UNCHANGED (item (f), still the snapshot-existential form). The NEXT
   dispatch's job is exactly items (d)-(f) as originally sequenced, now backed by machinery that
   should make the six-site wiring mechanical rather than open-ended: at each site, derive the
   label bound via `IFrozenBelow_intStepBranchPrio_ge` (using `IReuseFrozenOrigin_frozenBelow`'s
   output as the `hfrz` input), then call `IReuseFrozenOrigin_persist`/`_extendMany` as
   appropriate for that site's transport shape (persistence-fixpoint vs. content-only growth),
   and finally build the ACTUAL `IReuseContain` (bare, post-restatement) transport from
   `IReuseFrozenOrigin_frozenBelow`'s derived `IFrozenBelow` fact plus a case split on whether the
   target formula was already present pre-transport (trivial, via existing
   `applyPersistenceFixpoint_mem_preserved`/`Branch.extendMany` monotonicity) or newly arrived
   (impossible below the freeze threshold, by the derived `IFrozenBelow` fact itself).

**Verification (this dispatch)**: `lake exe cache get` warm/no-op; `lake build` (scoped then
full, all 3325 jobs) green, only pre-existing warnings/sorries; `lake exe checkInitImports`
clean; `lake lint`/`lake exe lint-style`/`lake shake`/`lake exe mk_all --module`/`lake test`
results recorded in the handoff. Sorry count 196 -> 196 (unchanged), axiom count 26 -> 26
(unchanged).

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
