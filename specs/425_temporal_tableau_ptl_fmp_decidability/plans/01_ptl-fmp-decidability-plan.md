# Implementation Plan: PTL Finite Model Property and Temporal Tableau Decidability

- **Task**: 425 - temporal_tableau_ptl_fmp_decidability
- **Status**: [BLOCKED]
- **Effort**: 20 hours
- **Dependencies**: Sibling tasks 423, 424 (only for the final `instDecidableValid` task-301 registration; all six phases below are independently buildable without them)
- **Research Inputs**: specs/425_temporal_tableau_ptl_fmp_decidability/reports/01_ptl-fmp-decidability-survey.md
- **Artifacts**: plans/01_ptl-fmp-decidability-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Establish the finite model property (FMP) for Propositional Temporal Logic (PTL) inside the
existing temporal tableau at `Cslib/Logics/Temporal/Tableau/` and use it to introduce seven target
declarations that today exist only as docstring-stated obligations:
`eventualityDefect_unsat`, `temporalTableau_sound`, `temporalTruthLemma_untl`,
`temporalTruthLemma_snce`, `openBranch_branchSat`, `temporalTableau_complete`, and
`instDecidableValid`. This is genuine new formalization (not sorry-discharge — the Tableau
directory has zero real sorries today). The required FMP is the tableau-internal
ultimately-periodic (lasso) ℤ-model construction, not the canonical-filtration FMP used elsewhere
in the library. Definition of done: all seven declarations land sorry-free, no new axioms, and
`lake build Cslib.Logics.Temporal.Tableau.*` is green (full CI green).

### Research Integration

Integrates the single research report
(`reports/01_ptl-fmp-decidability-survey.md`). Load-bearing findings carried into this plan:

- **Targets are absent declarations**, not sorries; this is new formalization with no theoretical
  blocker (PTL FMP is a classical result), so the task is planned/implemented, not `[BLOCKED]`.
- **Critical design finding (report §4):** the current `extractModelℤ`
  (`Completeness.lean:133-135`) leaves every ℤ-instant not touched by the finite branch empty (all
  atoms false), so the `U(guard,event)` guard-between obligation over the many intermediate
  integers is not satisfied. `temporalTruthLemma_untl` is *false of the model as currently
  defined*. The countermodel must be redesigned as an ultimately-periodic (lasso) ℤ-model
  **before** the Until/Since truth lemmas can even be stated truthfully. This is the crux and the
  single highest-risk item (Phase B); it is scheduled as an independent early phase and must be
  spiked before the truth-lemma phases commit.
- **Already landed and reusable as-is:** `temporalTableau` (`Saturation.lean:534`),
  `temporalTableau_instantStrict` (`Saturation.lean:545`, discharges the run-level order-
  preservation component of `openBranch_branchSat`), `classicallyClosed_unsat`
  (`Soundness.lean:97`, the classical half of soundness), and the propositional truth lemma
  `temporalTruthLemma_propositional_aux` / `_propositional` (`Completeness.lean:425,946`). The
  `extractModelℤ_*` property lemmas transfer in *structure* but must be re-proved after the §4
  redesign.
- **Argument templates (do not import):** Chronicle `tUntilEventualityResolution` /
  `tSinceEventualityResolution` (`Metalogic/Chronicle/Frame.lean:234-252`) encode the exact
  eventuality→witness shape to mirror; task-421 `MinDecidability.lean` supplies the
  finite-model→truth-lemma→FMP-biconditional→`decidable_of_iff` *pattern* only.
- **Rejected reuse sources (surveyed):** Bimodal FMP filtration route, LTL ω-automata route — both
  structurally disjoint from the ℤ-indexed bidirectional tableau.

### Prior Plan Reference

No prior plan. This is the first plan for the task.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no roadmap consultation was
requested; roadmap alignment not evaluated for this plan.

## Goals & Non-Goals

**Goals**:
- Introduce `eventualityDefect_unsat` and assemble `temporalTableau_sound` (the `.closed` half of
  decidability) — an independent, self-contained soundness milestone.
- Redesign `extractModelℤ` into an ultimately-periodic (lasso) ℤ-model and re-prove its atom/bot
  property lemmas against the new definition.
- Prove `temporalTruthLemma_untl` and `temporalTruthLemma_snce` over the redesigned model.
- Assemble `openBranch_branchSat` and `temporalTableau_complete` (the `.openBranch` half).
- Expose `instDecidableValid : Decidable (Temporal.valid φ)` via
  `valid φ ↔ temporalTableau (¬φ) = .closed` and `decidable_of_iff`.
- Zero-debt throughout: no `sorry`, no new axioms, no vacuous `def _ := True`; every phase ends
  green under `lake build Cslib.Logics.Temporal.Tableau.<Module>`.

**Non-Goals**:
- Re-deriving order preservation: `temporalTableau_instantStrict` already discharges it; reuse it.
- The canonical-filtration FMP route (Bimodal) or the ω-automata route (LTL) — surveyed and
  rejected as non-transferable.
- The finite `ZMod k` domain alternative for the countermodel — kept only as a documented
  contingency if the periodic-ℤ route proves intractable (larger blast radius on the `branchSat`
  interface).
- Final task-301 wiring completion: `instDecidableValid` is exposed here, but its registration
  into the task-301 decision surface also depends on sibling tasks 423/424 landing. Phase F is
  scoped to expose the instance and flag the cross-task dependency to the orchestrator, not to
  close task 301.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Periodic-ℤ countermodel redesign (Phase B) proves intractable in Lean | H | M | Spike Phase B's core definition + one property lemma before Phase C commits; if it fails, fall back to the documented finite-`ZMod k` domain route (report §4 alternative) and re-check `InstantStrict` / `branchSat` interface |
| Redesigned `extractModelℤ` breaks the already-landed `extractModelℤ_*` property lemmas | M | H (expected) | Phase B explicitly re-proves each atom/bot property lemma against the new definition; the `Nat`-model (`extractModel`) versions and proof structure transfer |
| Guard-between obligation fails because some intermediate loop instant lacks a full Hintikka time-type | H | M | Phase B adds and verifies the "every instant carries a complete Hintikka time-type" helper (report §8.3); confirm `temporalHintikkaSet` saturation + G/H persistence force the guard onto every intermediate branch time |
| `branchSat` domain generality (`Nontrivial` + `LinearOrder`) not satisfied by periodic ℤ-model | M | L | Phase E confirms `Nontrivial ℤ` and the order-preservation clause end-to-end before assembling `openBranch_branchSat` |
| Since (Phase D) does not collapse to Until via `swapTemporal` duality | M | M | Investigate duality first (report §7 lever); if it does not reduce, budget a full symmetric re-proof mirroring Phase C |
| Final `instDecidableValid` registration blocked on tasks 423/424 | L | H | Phase F exposes the instance and flags the cross-task dependency in the handoff; does not attempt task-301 closure |
| Pigeonhole / subset-blocking Mathlib lemma names unverified at plan time | L | M | Implementer verifies exact names via `lean_leansearch` / `lean_loogle` during Phase A/B (report §7 lists candidates: `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`, `List.Subset`) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | A, B | -- |
| 2 | C | B |
| 3 | D | C |
| 4 | E | C, D |
| 5 | F | A, E |

Phases within the same wave can execute in parallel. Phases A (soundness) and B (countermodel
redesign) are mutually independent and are the two Wave-1 entry points. Recommended start order:
begin A (lowest risk, independently valuable — it alone closes the soundness gate) while spiking
B's core definition before committing to the full B build.

### Phase A: Soundness half — eventualityDefect_unsat and temporalTableau_sound [BLOCKED]

**BLOCKER** (Phase A, found during implementation spike, 2026-07-24):

- **What failed**: Attempting to prove `eventualityDefect_unsat (b : TBranch Atom) (ord :
  TimeOrdering) (tracker : EventualityTracker Atom) (hblocked : findEventualityDefect b ord
  tracker = some t) : ¬branchSat b ord` exactly as sketched in `Soundness.lean:189-192` / this
  plan's Phase A task list, via the report's §3 "pumping / no-least-witness" argument.
- **What was tried**: Traced the exact semantics of every static predicate involved
  (`isSubsetBlocked`, `allEventualitiesFulfilledOrDuplicated`, `ancestorTimes`,
  `EventualityTracker.pending`) against `branchSat`'s definition (`Soundness.lean:79-87`,
  `∃ (D) [LinearOrder D] [Nontrivial D] ...`) and `untl_iff`/`snce_iff`
  (`Semantics/Satisfies.lean:104,113`), by hand, before writing any Lean. No lemma statement was
  attempted in the file (no edits were made to any `.lean` file in this dispatch).
- **Why it's stuck** — three independent, cross-checked findings, each individually sufficient to
  block a direct proof of the lemma as stated:
  1. **The bare hypotheses under-determine the argument.** `findEventualityDefect b ord tracker =
     some t` only asserts (a) `tracker.hasPending = true` *globally* (some pending entry
     *somewhere*, not necessarily connected to `t`), and (b) `isSubsetBlocked b t t_anc` plus
     `allEventualitiesFulfilledOrDuplicated tracker t_anc t` for *some* `t_anc ∈ ancestorTimes ord
     t`. Nothing in the lemma's hypotheses ties `tracker`'s entries back to actual `T(φ)@label`
     members of `b` (that link only holds by construction, via `registerEventualities` /
     `fulfillEventualities`, during an actual `temporalStepBranch` run — it is not part of the
     static lemma signature). Without that link, `e ∈ tracker.pending` does not give
     `⟨.pos, e.formula, e.label⟩ ∈ b`, so `branchSat`'s `hb` clause cannot be invoked on `e` at
     all.
  2. **Even granting branch-faithfulness, two labeled points are not enough.** With
     `T(φ)@t_anc, T(φ)@t ∈ b` (φ = `U(guard,event)`) and `isSubsetBlocked b t t_anc`, `branchSat`
     only yields *two* existential Until-witnesses (one from each label) via `untl_iff` — both
     consistently satisfiable simultaneously (e.g. `D = ℤ`, `f(t_anc) = 0`, `f(t) = 1`, witness for
     `t_anc` at `5`, witness for `t` at `7`, guard holding throughout both gaps). Deriving a
     genuine contradiction needs either (i) an actual infinite-regress/pigeonhole construction over
     the branch's finite time-type space (not just one ancestor pair), or (ii) negative
     information (`F(event)@r` at every intermediate labeled point) that the bare subset-blocking
     condition does not supply. Confirmed by direct calculation — no 2-point contradiction exists
     under `branchSat`'s definition as literally written.
  3. **A deeper, independent mismatch: `branchSat`'s domain is too general for this argument
     regardless.** `branchSat` (`Soundness.lean:79-87`) quantifies over *arbitrary*
     `[LinearOrder D] [Nontrivial D]` — no seriality, density, or discreteness constraint. But
     `temporalApplyPos`'s `untlPos` rule (`Rules.lean:264-272`) branches into `branch1 = T(event)@t'`
     with *no* accompanying guard-on-`(t,t')` assertion — this is only sound if `(t,t')` is
     provably *empty* in the model, i.e. `t'` is the immediate successor of `t` (discreteness).
     Cross-checked against the rest of the Temporal metalogic layer: `Metalogic/Soundness.lean:74`
     (`axiom_sound`) and `Metalogic/Completeness.lean:101` (`completeness`) both use
     `[LinearOrder D] [NoMaxOrder D] [NoMinOrder D]` — i.e. `Temporal.validSerial`
     (`Semantics/Validity.lean:82-86`), not the fully general `Temporal.valid` this plan's Phase F
     targets, and `validSerial`/`validDense`/`validDiscrete` are documented as an *incomparable*
     hierarchy (`Validity.lean:19-39`). The tableau's `TimeOrdering.instant` design (`+1`/`-1`
     successor steps, `TimeOrdering.lean:60-91`) matches `validDiscrete`
     (`SuccOrder`/`PredOrder`/`IsSuccArchimedean`), not `valid` or even `validSerial`. This means
     `branchSat`'s existing signature and this plan's Phase F goal
     (`Decidable (Temporal.valid φ)`) are very likely the *wrong validity notion* for what this
     tableau's rules actually decide.
- **What is needed**: A dedicated research/design pass (recommend `--lit` with the cited
  [Reynolds1994] source, plus a close read of `Metalogic/Completeness.lean` and
  `Metalogic/Soundness.lean`'s exact frame-class hypotheses) to determine, *before* further
  implementation: (a) which validity notion (`valid`, `validSerial`, or `validDiscrete`) this
  tableau actually decides, given its successor-based `TimeOrdering` design; (b) the correct
  domain hypothesis for `branchSat` (likely needs `SuccOrder`/`PredOrder`/`IsSuccArchimedean` or
  similar, not bare `LinearOrder`/`Nontrivial`); (c) the correct run-level invariant
  (branch/tracker faithfulness, analogous to the existing `WorklistInv`/`OrdFreshWRT` machinery in
  `Saturation.lean`/`Rules.lean`) needed to make `eventualityDefect_unsat` provable; and (d) the
  corresponding correction to Phase F's target (likely `Temporal.validDiscrete`, not
  `Temporal.valid`). This is very likely a larger, separate research+plan-revision effort, not a
  same-dispatch implementation fix.
- **Prohibited workarounds**: Did NOT use `sorry`, `def X := True`, or any vacuous placeholder. No
  `.lean` file was edited in this dispatch — the finding was made analytically before any edit, to
  avoid landing an incorrect or unsound lemma.

**Original phase content below (unchanged, for reference):**

**Goal**: Prove that a branch closed by eventuality-defect is unsatisfiable, then glue with the
existing classical soundness half to obtain `temporalTableau_sound` (`.closed → ¬ satisfiable`).
This is the independent, lowest-risk milestone and closes the `.closed` half of decidability.

**Tasks**:
- [ ] Prove `eventualityDefect_unsat` in `Soundness.lean` by the pumping / König-style argument
  (report §3): a subset-blocked loop with a pending eventuality that recurs but is never witnessed
  admits no least witness instant, contradicting `U` semantics. Consume `findEventualityDefect`,
  `isSubsetBlocked`, `allEventualitiesFulfilledOrDuplicated` (`Branch.lean:146-167`).
- [ ] Verify the pigeonhole/loop-existence Mathlib lemma name (candidate
  `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`) via `lean_loogle` / `lean_leansearch`.
- [ ] Assemble `temporalTableau_sound` by gluing `eventualityDefect_unsat` with
  `classicallyClosed_unsat` (`Soundness.lean:97`) over the fuel-induction loop invariant, reusing
  the `processNext` / strong-fuel-induction skeleton from `temporalTableau_instantStrict`
  (`Saturation.lean:366-547`).
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Soundness` green; confirm no sorry / no new axiom
  (`lean_verify`).

**Timing**: ~4 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` — add `eventualityDefect_unsat` and
  `temporalTableau_sound` (currently docstring obligations near L169-198).

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Soundness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for both new declarations.

---

### Phase B: Countermodel redesign — periodic (lasso) extractModelℤ [NOT STARTED]

**Cross-reference note (added during Phase A spike, 2026-07-24)**: Phase A's blocker (see above)
found that `Temporal.valid`'s quantifier ranges over *arbitrary* `LinearOrder`/`Nontrivial` D,
while this tableau's rules (and `extractModelℤ`'s own ℤ/successor design) appear to match
`Temporal.validDiscrete` instead. Before committing to the Phase B periodic-model redesign,
confirm which validity notion Phase F should target — it affects whether `openBranch_branchSat`'s
existential witness (`D = ℤ`) is asserting *just* `Temporal.satisfiable` (fine, matches this
plan's Phase E/F as long as Phase F's target is corrected to `validDiscrete`) or is expected to
also support the (much stronger, likely unneeded) fully general `valid`/`satisfiable` used
verbatim by `branchSat`'s current signature.

**Goal**: Replace the "island" `extractModelℤ` with an ultimately-periodic (lasso) ℤ-model built
from the branch's subset-block structure so that every ℤ-instant carries a complete Hintikka
time-type, and re-prove the `extractModelℤ_*` atom/bot property lemmas against the new definition.
This is the crux (report §4) and the schedule risk. Spike the core definition + one property
lemma before Phase C commits.

**Tasks**:
- [ ] **Spike first**: define the periodic valuation and prove one atom property lemma against it;
  confirm tractability before building the rest of the phase.
- [ ] Add a loop-extraction helper: from `isSubsetBlocked` recover the subset-blocked ancestor pair
  `(t_anc, t_new)`, giving prefix `[min .. t_anc]` and loop body `(t_anc .. t_new]`.
- [ ] Add a periodic-index reduction helper: for `z` beyond the populated range, reduce `z` modulo
  the loop length back into the loop body (forward tail; symmetric backward loop for the past tail
  since BX is bidirectional).
- [ ] Redefine `extractModelℤ` (`Completeness.lean:133-135`) so instants interior to the populated
  prefix keep their branch time-type and all other instants read the periodically-reduced loop-body
  time-type.
- [ ] Add and prove the "every instant carries a complete Hintikka time-type" helper (report §8.3);
  confirm `temporalHintikkaSet` saturation + G/H persistence force the guard onto every intermediate
  branch time.
- [ ] Re-prove the `extractModelℤ_*` atom/bot property lemmas (`extractModel_atom_sat_iff`,
  `extractModel_bot_false`, `openBranch_noBotPos`, `openBranch_noContradiction`,
  `extractModel_atom_neg_notSat` and ℤ analogues, `Completeness.lean:99-330`) against the new
  definition; the `Nat`-model versions and proof structure transfer.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green; no sorry / no new axiom.

**Timing**: ~6 hours (largest phase; schedule risk)

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — redesign `extractModelℤ` (L133-135) plus
  helper lemmas and re-proved property lemmas (touch L99-330).

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds with the redesigned model and
  all re-proved property lemmas.
- `lean_verify` reports no `sorryAx` / no new axioms.
- Spike checkpoint: one property lemma proven against the new definition before the full phase
  commits.

---

### Phase C: Until truth lemma — temporalTruthLemma_untl [NOT STARTED]

**Goal**: Prove `temporalTruthLemma_untl` over the Phase-B periodic model: `T(U(g,e))@t` on an open
branch is satisfied in the countermodel.

**Tasks**:
- [ ] Prove `temporalTruthLemma_untl` by strong induction on `Formula.complexity`, reusing the
  propositional cases from `temporalTruthLemma_propositional_aux` verbatim and adding the untl case.
- [ ] Use `untl_iff` (`Satisfies.lean:104`) as the entry point; derive fulfilment from openness
  (`findEventualityDefect = none` ⇒ every pending Until fulfilled-or-recurring, report §3).
- [ ] Mirror `tUntilEventualityResolution`'s forward-witness structure (`Frame.lean:234`) — argument
  template only, not a callable import.
- [ ] Discharge the guard-between obligation using the Phase-B "every instant carries a complete
  Hintikka time-type" helper.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green; no sorry / no new axiom.

**Timing**: ~4 hours

**Depends on**: B

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `temporalTruthLemma_untl`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for `temporalTruthLemma_untl`.

---

### Phase D: Since truth lemma — temporalTruthLemma_snce [NOT STARTED]

**Goal**: Prove `temporalTruthLemma_snce` (past direction), ideally as a corollary of Phase C via
the `swapTemporal` duality rather than a full symmetric re-proof.

**Tasks**:
- [ ] **Investigate duality first**: check whether `swapTemporal` (`Formula.lean:384-386`) plus the
  Satisfies mirror collapse `temporalTruthLemma_snce` into a corollary of `temporalTruthLemma_untl`.
- [ ] If duality applies: prove a mirror/transport lemma and derive `_snce` from `_untl`.
- [ ] If not: prove `temporalTruthLemma_snce` symmetrically using `snce_iff` (`Satisfies.lean:113`)
  and the backward-loop periodic extension from Phase B.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green; no sorry / no new axiom.

**Timing**: ~2 hours (if duality applies; ~4 hours if full re-proof needed)

**Depends on**: C

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `temporalTruthLemma_snce` (and a
  `swapTemporal` transport lemma if the duality route is taken).

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for `temporalTruthLemma_snce`.

---

### Phase E: Assemble completeness — openBranch_branchSat and temporalTableau_complete [NOT STARTED]

**Goal**: Combine the full truth lemma (propositional + untl + snce) with the already-landed
order-preservation (`temporalTableau_instantStrict`) to prove `openBranch_branchSat`, then
`temporalTableau_complete` (`.openBranch → satisfiable`).

**Tasks**:
- [ ] Prove `openBranch_branchSat`: assemble `branchSat b ord` from the complete truth lemma over
  the Phase-B model plus order preservation from `temporalTableau_instantStrict`
  (`Saturation.lean:545`).
- [ ] Confirm the periodic ℤ-model satisfies the `branchSat` domain obligations: `Nontrivial ℤ`
  and the `LinearOrder` order-preservation clause end-to-end (report §8.2).
- [ ] Prove `temporalTableau_complete` from `openBranch_branchSat`.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green; no sorry / no new axiom.

**Timing**: ~3 hours

**Depends on**: C, D

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `openBranch_branchSat` and
  `temporalTableau_complete`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for both declarations.

---

### Phase F: Decidability instance — instDecidableValid [NOT STARTED]

**Goal**: Expose `instDecidableValid : Decidable (Temporal.valid φ)` via
`valid φ ↔ temporalTableau (¬φ) = .closed` and `decidable_of_iff`, using `temporalTableau_sound`
(Phase A) and `temporalTableau_complete` (Phase E). Flag the task-301 registration dependency on
sibling tasks 423/424 rather than attempting task-301 closure.

**Tasks**:
- [ ] Prove the bridge biconditional `valid φ ↔ temporalTableau (¬φ) = .closed` from
  `temporalTableau_sound` + `temporalTableau_complete`.
- [ ] Introduce `instDecidableValid` via `decidable_of_iff` over the bridge (noncomputable is
  acceptable, mirroring the task-421 pattern).
- [ ] Scope check: do NOT wire final task-301 registration — that also needs sibling tasks 423/424
  landed. Expose the instance and record the cross-task dependency in the implementation summary
  and orchestrator handoff.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.*` green (full module); no sorry / no new axiom;
  full CI green.

**Timing**: ~1 hour

**Depends on**: A, E

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` (or a new
  `Cslib/Logics/Temporal/Tableau/DecisionProcedure.lean`) — add the bridge biconditional and
  `instDecidableValid`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.*` succeeds across the whole tableau module.
- `lean_verify` reports no `sorryAx` / no new axioms for `instDecidableValid` and the bridge.
- Cross-task dependency on tasks 423/424 for task-301 registration recorded in the handoff.

## Testing & Validation

- [ ] Each phase ends green under `lake build Cslib.Logics.Temporal.Tableau.<Module>`.
- [ ] Zero-debt gate after every phase: no `sorry`, no new axioms (`lean_verify` on each new
  declaration), no vacuous `def _ := True`.
- [ ] Full-module build `lake build Cslib.Logics.Temporal.Tableau.*` green after Phase F.
- [ ] Full CI green as the terminal acceptance condition.
- [ ] Phase B spike checkpoint passed (core periodic definition + one property lemma) before Phase C
  commits.
- [ ] `temporalTableau_sound` and `temporalTableau_complete` cross-checked for consistency against
  the independent Chronicle Hilbert completeness (`Metalogic/Completeness.lean`, oracle only — not a
  dependency).

## Artifacts & Outputs

- plans/01_ptl-fmp-decidability-plan.md (this file)
- summaries/01_ptl-fmp-decidability-summary.md (on implementation completion)
- Modified `Cslib/Logics/Temporal/Tableau/Soundness.lean` (Phase A)
- Modified `Cslib/Logics/Temporal/Tableau/Completeness.lean` (Phases B–F), or a new
  `Cslib/Logics/Temporal/Tableau/DecisionProcedure.lean` for the `instDecidableValid` surface
- Seven new sorry-free declarations: `eventualityDefect_unsat`, `temporalTableau_sound`,
  `temporalTruthLemma_untl`, `temporalTruthLemma_snce`, `openBranch_branchSat`,
  `temporalTableau_complete`, `instDecidableValid`

## Rollback/Contingency

- Each phase is an additive, independently-buildable increment; revert the offending phase's commit
  to return to the last green state without disturbing earlier phases (Phase A alone is a valid,
  landable soundness milestone).
- **Phase B contingency**: if the periodic-ℤ redesign proves intractable, fall back to the finite
  `ZMod k` cyclic-order domain route (report §4 alternative). This changes the `branchSat` /
  countermodel interface (`D` fixed to a `Fintype` cyclic order) and requires re-checking
  `InstantStrict`'s ℤ-valued `instant` — a larger blast radius; snapshot before attempting via
  `bash .claude/scripts/git-snapshot.sh`.
- The original `extractModelℤ` definition and its property lemmas are preserved in git history; the
  redesign is a replace-in-place whose predecessor is recoverable if the new route is abandoned.
- No new axioms are introduced at any point, so rollback never leaves the module in an
  axiom-polluted state.
