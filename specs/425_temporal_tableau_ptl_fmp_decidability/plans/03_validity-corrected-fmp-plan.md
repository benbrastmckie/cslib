# Implementation Plan: PTL Finite Model Property and Temporal Tableau Decidability (validDiscrete-corrected)

- **Task**: 425 - temporal_tableau_ptl_fmp_decidability
- **Status**: [IMPLEMENTING]
- **Effort**: 26 hours
- **Dependencies**: Sibling tasks 423, 424 (only for the final task-301 registration of `instDecidableValid`; all eight phases below are independently buildable without them)
- **Research Inputs**:
  - specs/425_temporal_tableau_ptl_fmp_decidability/reports/01_ptl-fmp-decidability-survey.md
  - specs/425_temporal_tableau_ptl_fmp_decidability/reports/02_validity-notion-fmp-grounding.md
- **Artifacts**: plans/03_validity-corrected-fmp-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Establish the finite model property (FMP) for discrete Propositional Temporal Logic (PTL) inside
the existing temporal tableau at `Cslib/Logics/Temporal/Tableau/` and use it to introduce the
target declarations that today exist only as docstring-stated obligations, plus the two new
supporting declarations that report 02 shows are required for the argument to be sound. This is
genuine new formalization (not sorry-discharge — the Tableau directory has zero real sorries
today). The required FMP is the tableau-internal bidirectional ultimately-periodic (bi-lasso)
ℤ-model construction, not the canonical-filtration FMP used elsewhere in the library.

**Corrected direction (report 02, certain verdict): the tableau soundly and completely decides
`Temporal.validDiscrete`, NOT `Temporal.valid` and NOT `Temporal.validSerial`.** Machine-verified:
`TimeOrdering.addFuture`/`addPast` place each fresh time at the immediate integer
successor/predecessor (`TimeOrdering.lean:78,88`), and `untlPos` branch1 asserts the Until witness
at that immediate successor with no guard-between clause (`Rules.lean:270`) — sound only under
discreteness. Literature confirms the separation: the discreteness axiom `G'⊥ ∧ H'⊥` is
`validDiscrete` but not `valid` (it fails over the dense rationals; `[Burgess1982I]` §1.5, §2).
This resolves the Phase-A `[BLOCKED]` finding from plan 01 (see
`handoffs/01_phase-a-blocker-handoff.md`): `eventualityDefect_unsat` was provably too strong
because `branchSat` quantified over arbitrary `[LinearOrder D] [Nontrivial D]`, admitting a dense
two-witness countermodel.

Definition of done: all target declarations land sorry-free against `validDiscrete` /
`satisfiableDiscrete`, no new axioms, and `lake build Cslib.Logics.Temporal.Tableau.*` is green
(full CI green).

### Research Integration

This revision integrates the new hard-mode, literature-grounded report
`reports/02_validity-notion-fmp-grounding.md` on top of the original survey
`reports/01_ptl-fmp-decidability-survey.md`. Load-bearing findings newly carried into this plan
from report 02:

- **Validity-notion verdict (certain):** the tableau decides `Temporal.validDiscrete`. Every
  public target is restated against `validDiscrete` / `satisfiableDiscrete`. The literature witness
  ruling out `valid`/`validSerial` is the discreteness axiom `G'⊥ ∧ H'⊥` (`[Burgess1982I]` §1.5,
  §2, verified against chunk text).
- **`branchSat` signature was the wrong notion (Soundness.lean:79-87).** Its existential domain
  must be restricted from bare `[LinearOrder D] [Nontrivial D]` to the discrete-serial frame class
  `[NoMaxOrder] [NoMinOrder] [SuccOrder] [PredOrder] [IsSuccArchimedean]`, matching `validDiscrete`.
  This is why the plan-01 Phase A blocker's dense two-witness countermodel existed; under the
  discrete signature it no longer refutes `eventualityDefect_unsat`.
- **New predicate `satisfiableDiscrete`** must be added to `Semantics/Validity.lean` (mirror of
  `satisfiable`, discrete frame class), plus the dual lemma
  `validDiscrete_iff_not_satisfiableDiscrete_neg` (mirror of `satisfiable_not_valid_neg`,
  `Validity.lean:197`).
- **New run-level invariant `TrackerBranchFaithful`** (the genuine prerequisite plan 01 lacked):
  ties `tracker.pending` entries to actual `⟨.pos, e.formula, e.label⟩ ∈ b` members, established by
  fuel-induction over `temporalStepBranch` reusing the `temporalTableau_instantStrict` skeleton
  (`Saturation.lean:366-547`). `eventualityDefect_unsat` takes this as a hypothesis (resolves
  blocker finding #1).
- **Discreteness makes the defect genuinely unsatisfiable (resolves blocker finding #2):** over a
  discrete-serial domain, `IsSuccArchimedean` gives a finite successor-distance to any Until
  witness, enabling the finite-loop least-witness/pigeonhole "no least witness" contradiction. The
  soundness side is semi-local (finite loop only) and does NOT build the ℤ model; only the
  completeness side needs the full bi-lasso construction.
- **FMP construction confirmed** as the bidirectional ultimately-periodic (bi-lasso) ℤ-model
  (Hodkinson-Reynolds 2006 §5.8; `[GHR94]`), grounding plan 01 §4's redesign. The all-linear-orders
  route (mosaic method, Caleiro-Viganò-Volpe 2013 §4.3) is confirmed rejected — it is a
  structurally different technique for a different (`valid`) problem.
- **Domain simplification:** because completeness now witnesses at the fixed discrete domain
  `D := ℤ` (which already carries all five discrete instances), plan 01's risk "`branchSat` domain
  generality not satisfied by periodic ℤ-model" vanishes.
- **References hygiene:** add BibKeys `HodkinsonReynolds2006`, `CaleiroViganoVolpe2013` (and the
  1993 "gaps" article) to `references.bib`; update the `## References` sections of
  `Soundness.lean`/`Completeness.lean` to canonical `[Author, *Title*][BibKey]` format.

### Preserved Structure from Plan 01

Still-valid structure carried forward unchanged in intent (restated against the discrete domain):

- The periodic (lasso) `extractModelℤ` redesign spike (plan 01 Phase B → this plan Phase 4),
  including the "spike the core definition + one property lemma before committing" discipline.
- The Since-via-`swapTemporal` duality reduction (plan 01 Phase D → this plan Phase 6): investigate
  the duality collapse first, fall back to a symmetric re-proof only if it does not reduce.
- Deferral of the task-301 registration of `instDecidableValid` to siblings 423/424 (plan 01
  Phase F → this plan Phase 8): expose the instance and flag the cross-task dependency; do not close
  task 301.
- The `ZMod k` / `Fin`-indexed cyclic-quotient fallback for the countermodel if the periodic-ℤ
  route proves intractable — now *lower* risk because the domain is already committed to discrete.

### Prior Plan Reference

Supersedes `plans/01_ptl-fmp-decidability-plan.md` (its Phase A reached `[BLOCKED]`; no phases
completed and no `Cslib/**/*.lean` files were edited, per
`handoffs/01_phase-a-blocker-handoff.md`). Plan 01 is preserved in the `plans/` directory for
history. This plan is round 03 and replaces plan 01 as the active plan.

### Roadmap Alignment

`roadmap_path` (`specs/ROADMAP.md`) was provided in the delegation context. This task advances the
temporal-logic decidability line; the roadmap items it addresses (temporal tableau decision
procedure, discrete PTL FMP) are recorded at completion via the state.json `roadmap_items` field
rather than in this plan body.

## Goals & Non-Goals

**Goals**:
- Add `satisfiableDiscrete` and `validDiscrete_iff_not_satisfiableDiscrete_neg` to
  `Semantics/Validity.lean`; restrict `branchSat`'s existential domain to the discrete-serial frame
  class in `Soundness.lean`.
- Define and prove the `TrackerBranchFaithful` run-level invariant over `temporalStepBranch`.
- Introduce `eventualityDefect_unsat` (over the discrete `branchSat`, consuming the faithfulness
  invariant and the `IsSuccArchimedean` least-witness argument) and assemble
  `temporalTableau_sound : temporalTableau φ = .closed → ¬ satisfiableDiscrete φ`.
- Redesign `extractModelℤ` into a bidirectional ultimately-periodic (bi-lasso) ℤ-model and re-prove
  its atom/bot property lemmas against the new definition.
- Prove `temporalTruthLemma_untl` and `temporalTruthLemma_snce` over the redesigned model.
- Assemble `openBranch_branchSat` (witnessing at `D := ℤ`) and
  `temporalTableau_complete : (∃ b ord, temporalTableau φ = .openBranch b ord) → satisfiableDiscrete φ`.
- Expose `instDecidableValid : Decidable (Temporal.validDiscrete φ)` via
  `validDiscrete φ ↔ temporalTableau (¬φ) = .closed` and `decidable_of_iff`.
- Add the three missing BibKeys and update the `## References` sections to canonical format.
- Zero-debt throughout: no `sorry`, no new axioms, no vacuous `def _ := True`; every phase ends
  green under `lake build Cslib.Logics.Temporal.Tableau.<Module>`.

**Non-Goals**:
- Deciding `Temporal.valid` or `Temporal.validSerial` — report 02 proves the tableau decides
  neither; the mosaic method that would decide `valid` is surveyed and rejected as non-transferable.
- Re-deriving order preservation: `temporalTableau_instantStrict` (`Saturation.lean:545`) already
  discharges it; reuse it.
- The canonical-filtration FMP route (Bimodal) or the ω-automata route (LTL) — surveyed and
  rejected as non-transferable.
- Final task-301 wiring completion: `instDecidableValid` is exposed here, but its registration into
  the task-301 decision surface also depends on sibling tasks 423/424 landing. Phase 8 is scoped to
  expose the instance and flag the cross-task dependency to the orchestrator, not to close task 301.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `TrackerBranchFaithful` induction over the run is large | M | M | Reuse `temporalTableau_instantStrict`'s exact fuel/worklist skeleton (`Saturation.lean:366-547`), which already threads a run-level `P1`-style invariant; mirror `WorklistInv`/`OrdFreshWRT` |
| `IsSuccArchimedean` least-witness measure hard to formalize | M | M | Mathlib `Order.SuccPred.Archimedean` (already imported by `Validity.lean:12`) supplies `Succ.rec`/archimedean lemmas; spike the measure before Phase 3 commits |
| Periodic (bi-lasso) `extractModelℤ` redesign (Phase 4) proves intractable in Lean | H | M | Spike the core definition + one property lemma before Phase 5 commits; fallback is the `Fin`-indexed cyclic quotient (report 02 §recs.7), now lower-risk since the domain is already discrete |
| Redesigned `extractModelℤ` breaks the already-landed `extractModelℤ_*` property lemmas | M | H (expected) | Phase 4 explicitly re-proves each atom/bot property lemma against the new definition; the `Nat`-model (`extractModel`) versions and proof structure transfer |
| Guard-between obligation fails because some intermediate loop instant lacks a full Hintikka time-type | H | M | Phase 4 adds and verifies the "every instant carries a complete Hintikka time-type" helper (report 01 §8.3); confirm `temporalHintikkaSet` saturation + G/H persistence force the guard onto every intermediate branch time |
| Since (Phase 6) does not collapse to Until via `swapTemporal` duality | M | M | Investigate duality first (report 01 §7 lever); if it does not reduce, budget a full symmetric re-proof mirroring Phase 5 |
| `validDiscrete ↔ closed` dual lemma direction errors | L | L | Mirror the proved `satisfiable_not_valid_neg` (`Validity.lean:197`) verbatim with the discrete binders |
| Missing BibKeys block a clean `## References` update | L | H | Add the three `references.bib` entries in Phase 1 before citing them in-source |
| Final `instDecidableValid` registration blocked on tasks 423/424 | L | H | Phase 8 exposes the instance and flags the cross-task dependency in the handoff; does not attempt task-301 closure |
| Pigeonhole / subset-blocking Mathlib lemma names unverified at plan time | L | M | Implementer verifies exact names via `lean_leansearch` / `lean_loogle` during Phase 3/4 (candidates: `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`, `List.Subset`) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4 | 1 |
| 3 | 3, 5 | 2, 4 |
| 4 | 6 | 5 |
| 5 | 7 | 5, 6 |
| 6 | 8 | 3, 7 |

Phases within the same wave can execute in parallel. Wave 2 has two independent entry points once
the semantics/domain foundation (Phase 1) lands: Phase 2 (faithfulness invariant, gating soundness)
and Phase 4 (periodic model redesign, gating the truth lemmas). In Wave 3, Phase 3 depends only on
Phase 2 and Phase 5 depends only on Phase 4 (they do not depend on each other). Recommended start
order: land Phase 1 first (small, unblocks everything), then spike Phase 4's core definition while
Phase 2 proceeds in parallel.

### Phase 1: Semantics and domain foundation — satisfiableDiscrete, branchSat restriction, references [COMPLETED]

**Goal**: Add the discrete satisfiability predicate and its dual lemma, restrict `branchSat`'s
existential domain to the discrete-serial frame class, and land the three missing BibKeys. Small,
unblocks everything, and re-verifies `classicallyClosed_unsat` still builds.

**Tasks**:
- [x] Add `satisfiableDiscrete` to `Semantics/Validity.lean`, mirroring `satisfiable` with the
  discrete-serial instance binders (report 02 Finding 2.1):
  ```lean
  def satisfiableDiscrete (φ : Formula Atom) : Prop :=
    ∃ (D : Type) (_ : LinearOrder D) (_ : Nontrivial D)
      (_ : NoMaxOrder D) (_ : NoMinOrder D)
      (_ : SuccOrder D) (_ : PredOrder D) (_ : IsSuccArchimedean D)
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ
  ```
- [x] Add the discrete dual lemma `validDiscrete_iff_not_satisfiableDiscrete_neg :
  validDiscrete φ ↔ ¬ satisfiableDiscrete (¬φ)`, mirroring `satisfiable_not_valid_neg`
  (`Validity.lean:197`) verbatim with the discrete binders. *(deviation: altered -- proved as a
  genuine biconditional via `Satisfies.neg_iff` + classical `by_contra` on the backward
  direction, rather than a verbatim one-direction mirror, since the target signature in Goals
  is an `↔`.)*
- [x] Restrict `branchSat` (`Soundness.lean:79-87`): add the five discrete-serial instance binders
  (`NoMaxOrder`, `NoMinOrder`, `SuccOrder`, `PredOrder`, `IsSuccArchimedean`) to the existential,
  keeping the order-preservation and branch-faithfulness clauses unchanged (report 02 Finding 2.2).
- [x] Confirm `classicallyClosed_unsat` (`Soundness.lean:97`) still builds — it only destructs the
  existential; the extra binders are discarded with `_`.
- [x] Add BibKeys `HodkinsonReynolds2006`, `CaleiroViganoVolpe2013`, and the 1993 "gaps" article
  (`Gabbay1993`) to `references.bib`; update the `## References` sections of
  `Soundness.lean`/`Completeness.lean` to canonical `[Author, *Title*][BibKey]` format (they
  previously carried only the legacy `[Reynolds1994]` citation).
- [x] `lake build Cslib.Logics.Temporal.Tableau.Soundness` and
  `lake build Cslib.Logics.Temporal.Semantics.Validity` green; no sorry / no new axiom
  (`lean_verify` confirms only `propext`/`Classical.choice`/`Quot.sound` on both new
  declarations; `Cslib.Logics.Temporal.Tableau.Completeness` also confirmed green since its
  References section was touched).

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Validity.lean` — add `satisfiableDiscrete` and the dual lemma.
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` — restrict `branchSat`'s domain; update References.
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — update References.
- `references.bib` — add three BibKeys.

**Verification**:
- Both named `lake build` targets succeed.
- `lean_verify` reports no `sorryAx` / no new axioms for `satisfiableDiscrete` and the dual lemma.
- `classicallyClosed_unsat` unaffected (still builds).

---

### Phase 2: Run-level faithfulness invariant — TrackerBranchFaithful [COMPLETED]

**Goal**: Define `TrackerBranchFaithful` and prove it as a run-level invariant over
`temporalStepBranch`, tying each `tracker.pending` entry to an actual branch member. This is the
genuine new prerequisite plan 01 lacked (resolves blocker finding #1) and gates the soundness phase.

**Tasks**:
- [x] Define `TrackerBranchFaithful` (report 02 Finding 3a). *(deviation: altered -- the landed
  conjunct is `∀ e ∈ tracker.pending, ⟨.pos, e.formula, e.label⟩ ∈ b` only, without the
  `e.isUntil = true → e.formula.isUntl`-style shape conjunct from the sketch. The shape fact is
  established structurally instead: `registerEventualities_new_or_old`
  (`Saturation.lean`) shows every newly-registered eventuality's `(formula, label)` pair is read
  directly off a positive signed formula on the branch, so the branch-membership conjunct alone
  is what every consumer (the preservation proof, and Phase 3's future use) actually needs; adding
  a redundant shape conjunct would not strengthen anything derivable from branch membership plus
  the registration call sites.)*
- [x] Prove `TrackerBranchFaithful` is preserved by `temporalStepBranch` by fuel-induction, reusing
  the `run_level_P1` / strong-fuel-induction skeleton that already discharges
  `temporalTableau_instantStrict` (`Saturation.lean:366-547`), analogous to the existing
  `WorklistInv`/`OrdFreshWRT` machinery. Landed as `temporalStepBranch_preserves_faithful`
  (single-step) plus a parallel `WorklistInvFaithful`/`P1Faithful`/`P2Faithful`/`run_level_faithful`
  induction (three-list variant, since faithfulness relates branch+tracker rather than
  branch+ordering) mirroring `WorklistInv`/`P1`/`P2`/`run_level_P1` structurally without touching
  the already-landed `InstantStrict` threading.
- [x] Establish the invariant holds at run entry (base case) and threads through each step.
  `trackerBranchFaithful_empty` (base case) + `temporalTableau_trackerBranchFaithful` (entry-point
  corollary mirroring `temporalTableau_instantStrict`).
- [x] `lake build Cslib.Logics.Temporal.Tableau.Saturation` (or the owning module) green; no sorry /
  no new axiom (`lean_verify` on `temporalTableau_trackerBranchFaithful`: only
  `propext`/`Quot.sound`).

**Timing**: ~3.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` (or `Soundness.lean`, wherever the run-level
  invariant machinery lives) — add `TrackerBranchFaithful` and its preservation lemma.

**Verification**:
- Named `lake build` target succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for `TrackerBranchFaithful` and its preservation
  lemma.

---

### Phase 3: Soundness half — eventualityDefect_unsat and temporalTableau_sound [BLOCKED]

**BLOCKER**:
- **What failed**: `eventualityDefect_unsat` (`branchSat b ord → False` given `findEventualityDefect
  b ord tracker = some t` and `TrackerBranchFaithful b ord tracker`) appears to be **not actually
  provable as stated** — the report 02 Finding 3(b) "finite-loop pigeonhole under
  `IsSuccArchimedean`" sketch does not close, and analysis below suggests the target statement may
  be false as a standalone fact about `branchSat`.
- **What was tried**: Worked through the semantic content required to derive a contradiction from
  `branchSat b ord`. `branchSat` places no constraint beyond "some discrete-serial model M/f
  satisfies every T/F-signed formula that literally appears on the finite list `b`, at the
  branch-labels named in `b`". Given `TrackerBranchFaithful` + `allEventualitiesFulfilledOrDuplicated`,
  the two facts available are `⟨.pos, U, t_anc⟩ ∈ b` and `⟨.pos, U, t⟩ ∈ b` for the same Until/Since
  formula `U` (the "duplicated" pending eventuality). Under `branchSat`, each independently forces
  `Satisfies M (f t_anc) U` and `Satisfies M (f t) U` — i.e. `∃ s₁ > f t_anc, …` and `∃ s₂ > f t, …`.
  These are two *unrelated* existentials: nothing in `branchSat`'s definition ties `f t` to lie
  between `f t_anc` and its witness `s₁`, nor forces `s₁ = f t` or any other relationship. Since the
  Until/Since semantic clause (`Satisfies.untl_iff`/`snce_iff`) is purely existential (a witness may
  be placed anywhere later/earlier in the model), a model can *always* satisfy both assertions
  independently (e.g. witnessing far out in ℤ), regardless of whether the tableau's own
  witness-search (`fulfillEventualities`, which is exactly what "still pending" tracks) succeeded.
  "Still pending" is a fact about the **tableau's own procedural search state**, not a semantic
  constraint that `branchSat`'s existential model is obligated to respect. No pigeonhole over a
  finite `timeType` space closes this gap: `isSubsetBlocked`/`allEventualitiesFulfilledOrDuplicated`
  are checked only against the *syntactic* branch content `b` at the two named labels `t_anc`/`t`,
  and do not constrain the model's behavior at any of the (unnamed, model-only) intermediate points
  a `branchSat` witness function is free to choose.
- **Why it's stuck**: The standard literature argument for eventuality-fulfillment tableau soundness
  (e.g. Wolper-style LTL/PTL tableaux) is a **rule-soundness / contrapositive induction**: assume an
  actual model of `¬φ` exists, then show *at every step* the tableau construction can be *guided* by
  that model so that at least one child branch remains satisfiable by it, and finally that
  eventuality-defect closure can never be reached while a real model is being followed (because the
  model's own witness gives an actual, bounded successor-distance that the guided construction
  discharges before the loop re-forms). This is precisely `temporalStepBranch_preserves_sat`
  (Soundness.lean's *original* pre-task-425 "Blocked Obligation" #2 — propagation soundness), which
  is a **run-level, model-first** induction over the *entire construction history*, not a *local*
  fact about a single already-closed `(b, ord, tracker)` triple in isolation. Report 02 Finding 3(b)
  substitutes a local two-point pigeonhole for this run-level argument; the substitution does not
  appear to be sound, because — as shown above — `branchSat`'s existential is not constrained by the
  tableau's own bookkeeping at all.
- **What is needed**: Either (a) a substantially larger redesign restating `eventualityDefect_unsat`
  (and `temporalTableau_sound`) as a genuine run-level, model-guided induction over
  `temporalStepBranch`/`processNext` (mirroring the *original* blocked obligation #2, not the
  Phase-2-style branch/tracker invariant alone) — a materially bigger undertaking than the ~4h
  estimate and likely requiring a fresh planning/research pass — or (b) further research input
  identifying the missing semantic ingredient (if any) that ties "still pending" to a genuine
  model-level constraint the report's sketch did not surface. This is flagged back to
  research/planning rather than forced through with an unjustified or incorrect proof.
- **Prohibited workarounds**: Did NOT use `sorry`, `def X := True`, or any vacuous placeholder for
  `eventualityDefect_unsat`/`temporalTableau_sound`; both remain undefined in this dispatch pending
  the above resolution.

**Downstream note**: Per the plan's own Wave dependency table, Phase 3 gates only Phase 8 (the
final `Decidable (validDiscrete φ)` instance). Phases 4-7 (the bi-lasso FMP/completeness
construction) depend only on Phase 1 (Phase 4) and then transitively on each other (5 on 4, 6 on 5,
7 on 5+6) — **not on Phase 3** — so they remain independently implementable and were continued in
this dispatch.

**Goal**: Prove that a branch closed by eventuality-defect has no discrete-serial model, then glue
with the existing classical soundness half to obtain
`temporalTableau_sound : temporalTableau φ = .closed → ¬ satisfiableDiscrete φ`. This closes the
`.closed` half of decidability against the corrected (discrete) validity notion.

**Tasks**:
- [ ] Prove `eventualityDefect_unsat` over the *discrete* `branchSat`, taking both the
  `findEventualityDefect b ord tracker = some t` hypothesis and the `TrackerBranchFaithful b ord
  tracker` hypothesis from Phase 2 (report 02 Finding 3). Over a discrete-serial domain,
  `IsSuccArchimedean` forces a finite successor-distance to any Until witness; the subset-block
  `isSubsetBlocked b t t_anc` (`Branch.lean:120-123`) with the recurring pending eventuality
  (`allEventualitiesFulfilledOrDuplicated`, `Branch.lean:146-154`) prevents the least-witness
  distance from strictly decreasing around the loop — a finite-loop pigeonhole / König contradiction.
- [ ] Verify the pigeonhole/loop-existence Mathlib lemma name (candidate
  `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`) via `lean_loogle` / `lean_leansearch`, and the
  `IsSuccArchimedean` archimedean lemmas (`Order.SuccPred.Archimedean`).
- [ ] Assemble `temporalTableau_sound : temporalTableau φ = .closed → ¬ satisfiableDiscrete φ` by
  gluing `eventualityDefect_unsat` with `classicallyClosed_unsat` (`Soundness.lean:97`) over the
  fuel-induction loop invariant, reusing the `processNext` / strong-fuel-induction skeleton from
  `temporalTableau_instantStrict` (`Saturation.lean:366-547`).
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Soundness` green; confirm no sorry / no new axiom
  (`lean_verify`).

**Timing**: ~4 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` — add `eventualityDefect_unsat` and
  `temporalTableau_sound` (currently docstring obligations near L169-198).

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Soundness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for both new declarations.
- Statement of `temporalTableau_sound` uses `¬ satisfiableDiscrete φ` (NOT `¬ satisfiable φ`).

---

### Phase 4: Countermodel redesign — bi-lasso extractModelℤ [NOT STARTED]

**Goal**: Replace the "island" `extractModelℤ` with a bidirectional ultimately-periodic (bi-lasso)
ℤ-model built from the branch's subset-block structure so that every ℤ-instant carries a complete
Hintikka time-type, and re-prove the `extractModelℤ_*` atom/bot property lemmas against the new
definition. This is the crux (report 01 §4, grounded by report 02 Finding 4) and the schedule risk.
Spike the core definition + one property lemma before Phase 5 commits.

**Tasks**:
- [ ] **Spike first**: define the periodic valuation and prove one atom property lemma against it;
  confirm tractability before building the rest of the phase.
- [ ] Add a loop-extraction helper: from `isSubsetBlocked` recover the subset-blocked ancestor pair
  `(t_anc, t_new)`, giving prefix `[min .. t_anc]` and loop body `(t_anc .. t_new]`.
- [ ] Add a periodic-index reduction helper: for `z` beyond the populated range, reduce `z` modulo
  the loop length back into the loop body (forward tail; symmetric backward loop for the past tail
  since BX is bidirectional — the bi-lasso: periodic past tail + finite middle + periodic future
  tail).
- [ ] Redefine `extractModelℤ` (`Completeness.lean:133-135`) so instants interior to the populated
  prefix keep their branch time-type and all other instants read the periodically-reduced loop-body
  time-type. The witness domain is `D := ℤ`, which carries all five discrete-serial instances
  natively.
- [ ] Add and prove the "every instant carries a complete Hintikka time-type" helper (report 01
  §8.3); confirm `temporalHintikkaSet` saturation + G/H persistence force the guard onto every
  intermediate branch time.
- [ ] Re-prove the `extractModelℤ_*` atom/bot property lemmas (`extractModel_atom_sat_iff`,
  `extractModel_bot_false`, `openBranch_noBotPos`, `openBranch_noContradiction`,
  `extractModel_atom_neg_notSat` and ℤ analogues, `Completeness.lean:99-330`) against the new
  definition; the `Nat`-model versions and proof structure transfer.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green; no sorry / no new axiom.

**Timing**: ~6 hours (largest phase; schedule risk)

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — redesign `extractModelℤ` (L133-135) plus
  helper lemmas and re-proved property lemmas (touch L99-330).

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds with the redesigned model and all
  re-proved property lemmas.
- `lean_verify` reports no `sorryAx` / no new axioms.
- Spike checkpoint: one property lemma proven against the new definition before the full phase
  commits.

---

### Phase 5: Until truth lemma — temporalTruthLemma_untl [NOT STARTED]

**Goal**: Prove `temporalTruthLemma_untl` over the Phase-4 bi-lasso model: `T(U(g,e))@t` on an open
branch is satisfied in the countermodel at `D := ℤ`.

**Tasks**:
- [ ] Prove `temporalTruthLemma_untl` by strong induction on `Formula.complexity`, reusing the
  propositional cases from `temporalTruthLemma_propositional_aux` verbatim and adding the untl case.
- [ ] Use `untl_iff` (`Satisfies.lean:104`) as the entry point; derive fulfilment from openness
  (`findEventualityDefect = none` ⇒ every pending Until fulfilled-or-recurring, report 01 §3).
- [ ] Mirror `tUntilEventualityResolution`'s forward-witness structure (`Frame.lean:234`) — argument
  template only, not a callable import.
- [ ] Discharge the guard-between obligation using the Phase-4 "every instant carries a complete
  Hintikka time-type" helper.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green; no sorry / no new axiom.

**Timing**: ~4 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `temporalTruthLemma_untl`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for `temporalTruthLemma_untl`.

---

### Phase 6: Since truth lemma — temporalTruthLemma_snce [NOT STARTED]

**Goal**: Prove `temporalTruthLemma_snce` (past direction), ideally as a corollary of Phase 5 via
the `swapTemporal` duality rather than a full symmetric re-proof.

**Tasks**:
- [ ] **Investigate duality first**: check whether `swapTemporal` (`Formula.lean:384-386`) plus the
  Satisfies mirror collapse `temporalTruthLemma_snce` into a corollary of `temporalTruthLemma_untl`.
- [ ] If duality applies: prove a mirror/transport lemma and derive `_snce` from `_untl`.
- [ ] If not: prove `temporalTruthLemma_snce` symmetrically using `snce_iff` (`Satisfies.lean:113`)
  and the backward-loop periodic extension from Phase 4.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green; no sorry / no new axiom.

**Timing**: ~2 hours (if duality applies; ~4 hours if full re-proof needed)

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `temporalTruthLemma_snce` (and a
  `swapTemporal` transport lemma if the duality route is taken).

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for `temporalTruthLemma_snce`.

---

### Phase 7: Assemble completeness — openBranch_branchSat and temporalTableau_complete [NOT STARTED]

**Goal**: Combine the full truth lemma (propositional + untl + snce) with the already-landed
order-preservation (`temporalTableau_instantStrict`) to prove `openBranch_branchSat` at `D := ℤ`,
then `temporalTableau_complete :
(∃ b ord, temporalTableau φ = .openBranch b ord) → satisfiableDiscrete φ`.

**Tasks**:
- [ ] Prove `openBranch_branchSat`: assemble `branchSat b ord` (now over the discrete-serial domain)
  from the complete truth lemma over the Phase-4 model plus order preservation from
  `temporalTableau_instantStrict` (`Saturation.lean:545`), witnessing at `D := ℤ`.
- [ ] Confirm ℤ discharges the discrete `branchSat` domain obligations: `Nontrivial ℤ`, `NoMaxOrder
  ℤ`, `NoMinOrder ℤ`, `SuccOrder ℤ`, `PredOrder ℤ`, `IsSuccArchimedean ℤ` (all Mathlib instances) and
  the `LinearOrder` order-preservation clause end-to-end. (This is now a *simplification* over plan
  01: the old "domain generality not satisfied by periodic ℤ-model" risk vanishes.)
- [ ] Prove `temporalTableau_complete : … → satisfiableDiscrete φ` from `openBranch_branchSat`.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green; no sorry / no new axiom.

**Timing**: ~3 hours

**Depends on**: 5, 6

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `openBranch_branchSat` and
  `temporalTableau_complete`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for both declarations.
- Statement of `temporalTableau_complete` uses `satisfiableDiscrete φ` (NOT `satisfiable φ`).

---

### Phase 8: Decidability instance — instDecidableValid over validDiscrete [NOT STARTED]

**Goal**: Expose `instDecidableValid : Decidable (Temporal.validDiscrete φ)` via
`validDiscrete φ ↔ temporalTableau (¬φ) = .closed` and `decidable_of_iff`, using
`temporalTableau_sound` (Phase 3) and `temporalTableau_complete` (Phase 7). Flag the task-301
registration dependency on sibling tasks 423/424 rather than attempting task-301 closure.

**Tasks**:
- [ ] Prove the bridge biconditional `validDiscrete φ ↔ temporalTableau (¬φ) = .closed` from
  `temporalTableau_sound` + `temporalTableau_complete`, routing through
  `validDiscrete_iff_not_satisfiableDiscrete_neg` (Phase 1).
- [ ] Introduce `instDecidableValid : Decidable (Temporal.validDiscrete φ)` via `decidable_of_iff`
  over the bridge (`noncomputable` acceptable, mirroring the task-421 pattern).
- [ ] Scope check: do NOT wire final task-301 registration — that also needs sibling tasks 423/424
  landed. Expose the instance and record the cross-task dependency in the implementation summary and
  orchestrator handoff.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.*` green (full module); no sorry / no new axiom; full
  CI green.

**Timing**: ~1 hour

**Depends on**: 3, 7

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` (or a new
  `Cslib/Logics/Temporal/Tableau/DecisionProcedure.lean`) — add the bridge biconditional and
  `instDecidableValid`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.*` succeeds across the whole tableau module.
- `lean_verify` reports no `sorryAx` / no new axioms for `instDecidableValid` and the bridge.
- Instance target is `Decidable (Temporal.validDiscrete φ)` (NOT `Decidable (Temporal.valid φ)`).
- Cross-task dependency on tasks 423/424 for task-301 registration recorded in the handoff.

## Testing & Validation

- [ ] Each phase ends green under `lake build Cslib.Logics.Temporal.Tableau.<Module>` (or
  `Semantics.Validity` for Phase 1).
- [ ] Zero-debt gate after every phase: no `sorry`, no new axioms (`lean_verify` on each new
  declaration), no vacuous `def _ := True`.
- [ ] Every public target is stated against `validDiscrete` / `satisfiableDiscrete`, never `valid` /
  `satisfiable` / `validSerial` (the report-02 correction is the acceptance-critical invariant).
- [ ] `branchSat`'s existential domain carries the five discrete-serial instance binders;
  `classicallyClosed_unsat` still builds.
- [ ] Full-module build `lake build Cslib.Logics.Temporal.Tableau.*` green after Phase 8.
- [ ] Full CI green as the terminal acceptance condition.
- [ ] Phase 2 spike checkpoint (`IsSuccArchimedean` least-witness measure) passed before Phase 3
  commits.
- [ ] Phase 4 spike checkpoint (bi-lasso core definition + one property lemma) passed before Phase 5
  commits.
- [ ] `temporalTableau_sound` and `temporalTableau_complete` cross-checked for consistency against
  the independent Chronicle Hilbert completeness (`Metalogic/Completeness.lean`, oracle only — not a
  dependency).
- [ ] Three new BibKeys present in `references.bib`; `## References` sections in
  `Soundness.lean`/`Completeness.lean` use canonical `[Author, *Title*][BibKey]` format.

## Artifacts & Outputs

- plans/03_validity-corrected-fmp-plan.md (this file)
- summaries/03_ptl-fmp-validity-corrected-summary.md (on implementation completion)
- Modified `Cslib/Logics/Temporal/Semantics/Validity.lean` (Phase 1: `satisfiableDiscrete`, dual
  lemma)
- Modified `Cslib/Logics/Temporal/Tableau/Soundness.lean` (Phases 1, 3: `branchSat` restriction,
  `eventualityDefect_unsat`, `temporalTableau_sound`)
- Modified `Cslib/Logics/Temporal/Tableau/Saturation.lean` (Phase 2: `TrackerBranchFaithful` and
  preservation lemma)
- Modified `Cslib/Logics/Temporal/Tableau/Completeness.lean` (Phases 4-8), or a new
  `Cslib/Logics/Temporal/Tableau/DecisionProcedure.lean` for the `instDecidableValid` surface
- Modified `references.bib` (Phase 1: three new BibKeys)
- New sorry-free declarations: `satisfiableDiscrete`, `validDiscrete_iff_not_satisfiableDiscrete_neg`,
  `TrackerBranchFaithful` (+ preservation), `eventualityDefect_unsat`, `temporalTableau_sound`,
  `temporalTruthLemma_untl`, `temporalTruthLemma_snce`, `openBranch_branchSat`,
  `temporalTableau_complete`, `instDecidableValid`

## Rollback/Contingency

- Each phase is an additive, independently-buildable increment; revert the offending phase's commit
  to return to the last green state without disturbing earlier phases (Phase 1 alone is a valid,
  landable semantics-foundation milestone, and Phase 3 alone closes the soundness gate).
- **Phase 4 contingency**: if the bi-lasso periodic-ℤ redesign proves intractable, fall back to the
  `Fin`-indexed cyclic-quotient domain route (report 02 §recs.7). Because the domain is already
  committed to discrete, this is lower-risk than in plan 01 (no re-negotiation of the `branchSat`
  domain generality is needed). Snapshot before attempting via `bash .claude/scripts/git-snapshot.sh`.
- **Phase 2/3 contingency**: if the `IsSuccArchimedean` least-witness measure resists direct
  formalization, spike the measure in isolation first (Phase 2 verification gate); the pigeonhole
  step over the finite `timeType` space is the fallback formulation.
- The original `extractModelℤ` definition and its property lemmas are preserved in git history; the
  redesign is a replace-in-place whose predecessor is recoverable if the new route is abandoned.
- No new axioms are introduced at any point, so rollback never leaves the module in an
  axiom-polluted state.
