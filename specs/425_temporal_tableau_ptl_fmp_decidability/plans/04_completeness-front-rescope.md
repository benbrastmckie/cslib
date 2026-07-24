# Implementation Plan: PTL Temporal Tableau — Completeness Front (bi-lasso FMP), soundness re-scoped

- **Task**: 425 - temporal_tableau_ptl_fmp_decidability
- **Status**: [IMPLEMENTING]
- **Effort**: ~15 hours (active Phases 4-7 only; the soundness/decidability deliverable is
  deferred to a separate research task, see "Re-Scope Decision" below)
- **Dependencies**: Sibling tasks 423, 424 (only for the eventual task-301 registration of
  `instDecidableValid`, which is itself gated behind the deferred soundness work — not reachable
  within this plan). A NEW soundness research task (to be spawned) gates the final decidability
  instance.
- **Research Inputs**:
  - specs/425_temporal_tableau_ptl_fmp_decidability/reports/01_ptl-fmp-decidability-survey.md
  - specs/425_temporal_tableau_ptl_fmp_decidability/reports/02_validity-notion-fmp-grounding.md
- **Artifacts**: plans/04_completeness-front-rescope.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is round 04, a blocker-driven revision of `plans/03_validity-corrected-fmp-plan.md`. Plan 03
established the corrected validity notion (the tableau decides `Temporal.validDiscrete`, not
`valid`/`validSerial`) and landed Phases 1-2 zero-debt. Its Phase 3 (soundness half,
`eventualityDefect_unsat`) reached `[BLOCKED]` during implementation with a well-analyzed finding:
the report-02 "local two-point pigeonhole" sketch is not sound, because `branchSat`'s existential
model is not constrained by the tableau's own procedural pending-bookkeeping (full analysis
preserved below and in `plans/03_validity-corrected-fmp-plan.md` under its Phase 3 `[BLOCKED]`
heading, plus `summaries/03_ptl-fmp-validity-corrected-summary.md`).

This plan **restructures the remaining work so the unblocked completeness front (bi-lasso FMP,
plan-03 Phases 4-7) comes first**, drawing concrete steps from the Phase-4 spike that already
landed and the implementer's continuation notes. It **re-scopes the soundness half (plan-03
Phase 3) and the decidability instance (plan-03 Phase 8) out of this plan**, recording them as a
separate research task with an exactly-stated open goal rather than planning hand-wavy phases over
an argument that is not yet specified concretely enough to execute.

Definition of done for THIS plan: `temporalTableau_complete : (∃ b ord, temporalTableau φ =
.openBranch b ord) → satisfiableDiscrete φ` lands sorry-free over the bi-lasso ℤ-model, together
with its supporting truth lemmas and the re-proved model property lemmas; every touched module is
green under a **scoped** `lake build` (see "Verification note on bare `lake build`" below); no new
axioms, no `sorry`, no vacuous definitions.

### Re-Scope Decision (Phase 3 / Phase 8): Option B — separate research task

The team-lead delegation offered two options for the blocked soundness half: (A) a concrete
restructured route for a run-level model-guided induction if one is well-defined enough to phase
out, or (B) explicitly re-scope this plan to the completeness front and mark the soundness /
decidability deliverable as requiring a separate research task, stating the exact open goal.

**This plan chooses Option B.** Reading the blocker writeup critically, the correct soundness
argument is a *run-level, model-guided contrapositive induction* over the entire construction
history (Wolper-style rule-soundness) — this is the tableau's *original* pre-task "Blocked
Obligation #2" (`temporalStepBranch_preserves_sat`), not the local `branchSat`-only fact the
report sketched. The implementer's own assessment ("materially bigger than the ~4h estimate and
likely requiring a fresh planning/research pass") is correct: the invariant statement itself (a
`Satisfies`-preserving run-level predicate relating an M-guided branch to a fixed model M) is not
yet specified, so any phase written now would be hand-wavy. Per the delegation's explicit
prohibition on hand-wavy phases, the soundness half is deferred. The **exact open goal** for the
new research task is stated in "Deferred Deliverable" below.

Consequence: this plan's terminus is `temporalTableau_complete` (Phase 7). The task's ultimate
public deliverable, `instDecidableValid : Decidable (Temporal.validDiscrete φ)`, is NOT reached
here — it needs both `temporalTableau_sound` (from the deferred soundness research) and
`temporalTableau_complete` (this plan). The task remains open after this plan lands, pending the
soundness research task.

### Completed Assets (plan-03 Phases 1-2 — preserved, never re-planned)

These landed sorry-free and committed on `main`; this plan builds on them and does not touch them:

- **Phase 1 [COMPLETED]** — Semantics/domain foundation. `satisfiableDiscrete` +
  `validDiscrete_iff_not_satisfiableDiscrete_neg` in `Cslib/Logics/Temporal/Semantics/Validity.lean`;
  `branchSat`'s existential domain restricted to the discrete-serial frame class (`NoMaxOrder`,
  `NoMinOrder`, `SuccOrder`, `PredOrder`, `IsSuccArchimedean`) in
  `Cslib/Logics/Temporal/Tableau/Soundness.lean`; `classicallyClosed_unsat` re-verified; three
  BibKeys (`HodkinsonReynolds2006`, `CaleiroViganoVolpe2013`, `Gabbay1993`) added to
  `references.bib` with canonical `## References` sections. `lean_verify`: only
  `propext`/`Classical.choice`/`Quot.sound`.
- **Phase 2 [COMPLETED]** — Run-level faithfulness invariant. `TrackerBranchFaithful` +
  its preservation threading (`temporalStepBranch_preserves_faithful`, the
  `WorklistInvFaithful`/`P1Faithful`/`P2Faithful`/`run_level_faithful` induction, and the
  entry-point corollary `temporalTableau_trackerBranchFaithful`) in
  `Cslib/Logics/Temporal/Tableau/Saturation.lean`. `lean_verify`: only `propext`/`Quot.sound`.
  (This invariant was built as a prerequisite for the blocked soundness half; it is a genuine,
  reusable asset the deferred soundness research will consume.)

### Landed Phase-4 Spike (plan-03 Phase 4, partial — the starting point for Phase 4 here)

The bi-lasso periodic-reduction core is already spiked and confirmed tractable in
`Cslib/Logics/Temporal/Tableau/Completeness.lean`:

- `periodicReduce (instAnc instNew : ℤ) (hL : instAnc < instNew) (z : ℤ) : ℤ` — folds instants
  beyond `instNew` back into the loop window `[instAnc, instNew)` via Mathlib's `toIcoMod`
  (`Mathlib.Algebra.Order.ToIntervalMod`); identity at or below `instNew`.
- `periodicReduce_mem_Ico_of_gt` — the load-bearing wraparound-lands-in-window fact, via
  `toIcoMod_mem_Ico`.
- `extractModelℤPeriodic (b) (ord) (instAnc instNew) (hL)` — the periodic model parameterized by
  an explicit loop witness (not yet derived from `isSubsetBlocked`).
- `extractModelℤPeriodic_atom_sat_iff_of_le`, `extractModelℤPeriodic_atomPos_sat_of_le`,
  `extractModelℤPeriodic_bot_false` — property lemmas over the populated range.

**Spike verdict: tractable.** `noncomputable` is required throughout (`toIcoMod` is
noncomputable), matching the accepted task-421 `Decidable`-instance precedent.

### Preserved Phase-3 Blocker Analysis (verbatim intent, carried for the soundness research task)

`eventualityDefect_unsat` as stated — `branchSat b ord → False` given `findEventualityDefect b ord
tracker = some t` and `TrackerBranchFaithful b ord tracker` — is **not provable as a local fact**.
`branchSat` places no constraint beyond "some discrete-serial model M/f satisfies every signed
formula literally on the finite list `b`, at the labels named in `b`". A duplicated pending
Until/Since formula `U` at two branch labels `t_anc`, `t` gives `Satisfies M (f t_anc) U` and
`Satisfies M (f t) U` — two *independent* existentials (each witness may be placed anywhere
later/earlier in ℤ), with nothing in `branchSat` tying them together or to the tableau's own
witness-search state. "Still pending" is a fact about the tableau's *procedural* search, not a
semantic constraint the `branchSat` model must respect; no finite `timeType` pigeonhole closes the
gap. The standard soundness argument is a run-level, model-first contrapositive induction over the
whole construction (the original "Blocked Obligation #2", `temporalStepBranch_preserves_sat`), not
the local invariant report 02 sketched. See "Deferred Deliverable" for the exact open goal handed
to research.

### Research Integration

No new research report is integrated in this round (this is a blocker-driven structural revision).
The load-bearing new input is the implementation dispatch's own findings, captured in
`.orchestrator-handoff.json` and `summaries/03_ptl-fmp-validity-corrected-summary.md`:
- The Phase-3 local-statement-is-false analysis (drives the Option-B re-scope).
- The Phase-4 spike tractability confirmation and the enumerated remaining sub-tasks (drives the
  concrete Phase-4 steps here).
- The decision that Phases 4-7 do not depend on Phase 3 (per plan-03's own wave table), which is
  what makes the completeness front independently landable now.

reports_integrated: reports/02_validity-notion-fmp-grounding.md (carried from plan 03; no new
report added this round).

### Prior Plan Reference

Supersedes `plans/03_validity-corrected-fmp-plan.md` as the active plan (round 04). Plan 03 is
preserved in `plans/` for history; its Phases 1-2 remain the authoritative record of the completed
foundation work, and its Phase-3 `[BLOCKED]` heading holds the full soundness analysis.

## Goals & Non-Goals

**Goals**:
- Derive the loop witness `(t_anc, t_new : TimeIndex)` and `hL : ord.instant t_anc <
  ord.instant t_new` from a genuine `isSubsetBlocked` witness, so `extractModelℤPeriodic` is driven
  by the tableau's own termination structure rather than free parameters.
- Complete the bi-lasso model: add the symmetric backward (past-tail) periodic reduction, wire
  `extractModelℤPeriodic` in to replace `extractModelℤ` at real call sites, and add the "every
  instant carries a complete Hintikka time-type" helper.
- Re-prove the `extractModelℤ_*` atom/bot property lemmas against the bi-lasso definition.
- Prove `temporalTruthLemma_untl` and `temporalTruthLemma_snce` over the bi-lasso model.
- Assemble `openBranch_branchSat` (witnessing at `D := ℤ`) and `temporalTableau_complete :
  (∃ b ord, temporalTableau φ = .openBranch b ord) → satisfiableDiscrete φ`.
- Zero-debt throughout: no `sorry`, no new axioms, no vacuous definitions; each phase ends green
  under a scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness`.

**Non-Goals**:
- **The soundness half** (`eventualityDefect_unsat`, `temporalTableau_sound`) — deferred to a
  separate research task; see "Deferred Deliverable". Not attempted in this plan.
- **The decidability instance** (`instDecidableValid`) and the task-301 registration — gated behind
  the deferred soundness half plus siblings 423/424; not reachable here.
- Deciding `Temporal.valid` / `Temporal.validSerial`, the mosaic method, canonical-filtration FMP,
  or the ω-automata route — all surveyed and rejected as non-transferable (report 02).
- Re-deriving order preservation: `temporalTableau_instantStrict` (`Saturation.lean`) already
  discharges it; reuse it.

## Deferred Deliverable (spun out to a new soundness research task)

The following is NOT planned here and must be raised as a new research task before it can be
phased. Stated as the exact open goal so the research task has a precise target:

**Open goal (soundness half).** Prove
```
temporalTableau_sound : temporalTableau φ = .closed → ¬ satisfiableDiscrete φ
```
The blocked sub-lemma `eventualityDefect_unsat` (local `branchSat b ord → False`) is *not* the
right target — it is false as a standalone fact (see "Preserved Phase-3 Blocker Analysis"). The
research task must instead specify and justify a **run-level, model-guided contrapositive
invariant**, of the shape:

> Fix a discrete-serial model `M` and labeling `f` satisfying the initial branch. Then
> `temporalStepBranch`/`processNext` can be *guided by `M`* so that at every step at least one
> child branch remains satisfied by `(M, f)`, and along the `M`-guided branch an eventuality-defect
> closure is never reached — because `M`'s own Until/Since witness has a finite successor-distance
> (`IsSuccArchimedean`) that is discharged before the `isSubsetBlocked` loop can re-form.

Equivalently, this is the tableau's original pre-task "Blocked Obligation #2"
(`temporalStepBranch_preserves_sat` in `Soundness.lean`'s docstring), threaded through the
`run_level_P1`/`WorklistInv` fuel-induction skeleton (`Saturation.lean`) exactly as
`temporalTableau_instantStrict` and the landed `run_level_faithful` (Phase 2) already are.

**What the research task must resolve before it can be planned:**
1. The exact statement of the `Satisfies`-preserving run-level predicate (analogue of `WorklistInv`
   / `P1` / the landed `WorklistInvFaithful`, but relating branch+tracker to a fixed `(M, f)`).
2. Whether the `M`-guided child-selection composes with the existing single-step
   `temporalStepBranch_preserves`/`processNext` skeleton without re-deriving it, reusing the
   Phase-2 `TrackerBranchFaithful` asset.
3. The precise `IsSuccArchimedean` least-witness / finite-successor-distance lemma that rules out
   defect closure along the guided branch (candidate Mathlib area: `Order.SuccPred.Archimedean`).

Once resolved, a follow-on plan can phase `temporalTableau_sound` and then `instDecidableValid`
(`validDiscrete φ ↔ temporalTableau (¬φ) = .closed` via `decidable_of_iff`, routing through the
landed `validDiscrete_iff_not_satisfiableDiscrete_neg`), plus the task-301 registration gated on
siblings 423/424.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Loop-witness extraction from `isSubsetBlocked` (Phase 4a) harder than the spike's free-parameter form | H | M | Reuse `temporalTableau_instantStrict`/`InstantStrict` to supply `hL : ord.instant t_anc < ord.instant t_new`; the subset-block predicate already names the ancestor pair. Spike the extraction against one concrete `isSubsetBlocked … = true` witness before wiring |
| Backward (past-tail) periodic reduction doubles the modular-arithmetic work | M | M | Mirror `periodicReduce`/`periodicReduce_mem_Ico_of_gt` with a `toIcoMod`-based past fold; the forward spike is the template, `toIcoMod_mem_Ico` transfers |
| Wiring `extractModelℤPeriodic` over `extractModelℤ` breaks landed `extractModelℤ_*` property lemmas | M | H (expected) | Phase 4c explicitly re-proves each atom/bot property lemma against the bi-lasso definition; the spike's three `extractModelℤPeriodic_*` lemmas are the transfer template |
| "Every instant carries a complete Hintikka time-type" helper fails on an intermediate loop instant | H | M | Confirm `temporalHintikkaSet` saturation + G/H persistence force the guard onto every intermediate branch time (report 01 §8.3); this is the guard-between obligation the truth lemma consumes |
| Since (Phase 6) does not collapse to Until via `swapTemporal` duality | M | M | Investigate duality first (report 01 §7 lever, `Formula.lean` `swapTemporal`); fall back to a symmetric re-proof mirroring Phase 5, using the backward-tail reduction from Phase 4 |
| Pigeonhole / subset-blocking Mathlib lemma names unverified at plan time | L | M | Implementer verifies via `lean_loogle`/`lean_leansearch` during the phase (`toIcoMod`, `toIcoMod_mem_Ico` already verified in the spike) |
| Task terminates without the public decidability instance (re-scope consequence) | M | Certain | Explicitly recorded: `temporalTableau_complete` is this plan's terminus; the decidability instance is handed to the deferred soundness research task with an exact open goal, not silently dropped |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 4 | (Phase 1 — completed asset) |
| 2 | 5 | 4 |
| 3 | 6 | 5 |
| 4 | 7 | 5, 6 |

The completed-asset Phase 1 unblocks Phase 4; Phases 5-7 chain from Phase 4 as in plan 03. Phase 4
is the crux and the schedule risk. There is no parallel front in this re-scoped plan (the soundness
branch that used to run in parallel is deferred), so execution is a straight chain 4 → 5 → 6 → 7.

Phase numbering is kept aligned with plan 03 (Phases 4-7) so the landed spike, the summary, and the
handoff continue to refer to the same phase identities. Phases 1-2 are completed assets (above);
Phases 3 and 8 are deferred (see "Deferred Deliverable").

### Phase 4: Complete the bi-lasso countermodel — extractModelℤPeriodic wired and re-proved [NOT STARTED]

**Goal**: Turn the landed Phase-4 spike into the real bi-lasso `extractModelℤ`: derive the loop
witness from `isSubsetBlocked`, add the backward past-tail reduction, wire the periodic model in at
real call sites, add the complete-Hintikka-time-type helper, and re-prove the `extractModelℤ_*`
property lemmas. This is the crux (report 01 §4, report 02 Finding 4) and the schedule risk.

**Tasks**:
- [ ] **(4a) Loop-witness extraction.** Add a helper that, from a genuine `isSubsetBlocked b t_new
  t_anc = true` witness, recovers the ancestor pair `(t_anc, t_new : TimeIndex)` as actual branch
  labels and establishes `hL : ord.instant t_anc < ord.instant t_new` via `InstantStrict` /
  `temporalTableau_instantStrict` (`Saturation.lean`). This replaces the spike's free
  `instAnc`/`instNew`/`hL` parameters with tableau-derived values. Spike the extraction against one
  concrete witness first (verify `isSubsetBlocked`'s exact signature at `Branch.lean:120-123`).
- [ ] **(4b) Backward past-tail reduction.** Add `periodicReduce`'s symmetric past-tail analogue
  (fold instants below `instAnc` back into the loop window) so the model is a full bi-lasso
  (periodic past + finite middle + periodic future), mirroring `periodicReduce` /
  `periodicReduce_mem_Ico_of_gt` with a `toIcoMod`-based past fold.
- [ ] **(4c) Wire and re-prove.** Redefine `extractModelℤ` (`Completeness.lean:142`) to route
  interior-populated instants to their branch time-type and all other instants to the
  periodically-reduced loop-body time-type — i.e. make `extractModelℤPeriodic` the real
  `extractModelℤ` at call sites, not a parallel definition. Re-prove `extractModelℤ_atom_sat_iff`,
  `extractModelℤ_atomPos_sat`, `extractModelℤ_bot_false`, `extractModelℤ_atom_neg_notSat`,
  `openBranch_noBotPos`, `openBranch_noContradiction` (`Completeness.lean:99-360`) against the new
  definition; the spike's three `extractModelℤPeriodic_*` lemmas plus the `Nat`-model versions
  transfer.
- [ ] **(4d) Complete-Hintikka-time-type helper.** Add and prove "every ℤ-instant carries a
  complete Hintikka time-type" (report 01 §8.3): confirm `temporalHintikkaSet` saturation + G/H
  persistence force the guard onto every intermediate loop instant. This is the guard-between
  obligation Phases 5-6 consume.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green (scoped); `lean_verify` reports
  no `sorryAx` / no new axioms on every new/redefined declaration.

**Timing**: ~5 hours (largest phase; schedule risk)

**Depends on**: Phase 1 (completed asset)

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — loop-witness extraction, backward reduction,
  redefined `extractModelℤ` + re-proved property lemmas, Hintikka-time-type helper.

**Verification**:
- Scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms.
- `extractModelℤPeriodic` is the definition actually used by `extractModelℤ` call sites (no
  orphaned parallel definition).

---

### Phase 5: Until truth lemma — temporalTruthLemma_untl [NOT STARTED]

**Goal**: Prove `temporalTruthLemma_untl` over the Phase-4 bi-lasso model: `T(U(g,e))@t` on an open
branch is satisfied in the countermodel at `D := ℤ`.

**Tasks**:
- [ ] Prove `temporalTruthLemma_untl` by strong induction on `Formula.complexity`, reusing the
  propositional cases from `temporalTruthLemma_propositional_aux` (`Completeness.lean:510`) verbatim
  and adding the untl case.
- [ ] Use `untl_iff` (`Satisfies.lean:104`) as the entry point; derive fulfilment from openness
  (`findEventualityDefect = none` ⇒ every pending Until fulfilled-or-recurring, report 01 §3).
- [ ] Mirror `tUntilEventualityResolution`'s forward-witness structure (`Frame.lean:234`) as an
  argument template (not a callable import).
- [ ] Discharge the guard-between obligation using the Phase-4d complete-Hintikka-time-type helper.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green (scoped); no sorry / no new
  axiom.

**Timing**: ~4 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `temporalTruthLemma_untl`.

**Verification**:
- Scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
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
  and the Phase-4b backward-tail periodic reduction.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green (scoped); no sorry / no new
  axiom.

**Timing**: ~2 hours if duality applies; ~4 hours if a full symmetric re-proof is needed

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `temporalTruthLemma_snce` (and a
  `swapTemporal` transport lemma if the duality route is taken).

**Verification**:
- Scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for `temporalTruthLemma_snce`.

---

### Phase 7: Assemble completeness — openBranch_branchSat and temporalTableau_complete [NOT STARTED]

**Goal**: Combine the full truth lemma (propositional + untl + snce) with the already-landed
order-preservation (`temporalTableau_instantStrict`) to prove `openBranch_branchSat` at `D := ℤ`,
then `temporalTableau_complete : (∃ b ord, temporalTableau φ = .openBranch b ord) →
satisfiableDiscrete φ`. This is this plan's terminus.

**Tasks**:
- [ ] Prove `openBranch_branchSat`: assemble `branchSat b ord` (over the discrete-serial domain)
  from the complete truth lemma over the Phase-4 model plus order preservation from
  `temporalTableau_instantStrict` (`Saturation.lean`), witnessing at `D := ℤ`.
- [ ] Confirm ℤ discharges the discrete `branchSat` domain obligations: `Nontrivial ℤ`,
  `NoMaxOrder ℤ`, `NoMinOrder ℤ`, `SuccOrder ℤ`, `PredOrder ℤ`, `IsSuccArchimedean ℤ` (all Mathlib
  instances) plus the `LinearOrder` order-preservation clause end-to-end.
- [ ] Prove `temporalTableau_complete : … → satisfiableDiscrete φ` from `openBranch_branchSat`.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green (scoped); no sorry / no new
  axiom.

**Timing**: ~3 hours

**Depends on**: 5, 6

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `openBranch_branchSat` and
  `temporalTableau_complete`.

**Verification**:
- Scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lean_verify` reports no `sorryAx` / no new axioms for both declarations.
- Statement of `temporalTableau_complete` uses `satisfiableDiscrete φ` (NOT `satisfiable φ`).

## Testing & Validation

**Verification note on bare `lake build`**: a bare `lake build` is currently RED on an unrelated
in-progress file, `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (a concurrent task's territory,
not touched here). All phase verification therefore uses the **scoped** target
`lake build Cslib.Logics.Temporal.Tableau.Completeness` (and its transitive Temporal deps), which
excludes `LoopChecking.lean`. Do NOT gate any phase on a bare `lake build` while that file is red.

- [ ] Each phase ends green under scoped `lake build Cslib.Logics.Temporal.Tableau.Completeness`.
- [ ] Zero-debt gate after every phase: no `sorry`, no new axioms (`lean_verify` on each new
  declaration), no vacuous `def _ := True`.
- [ ] Every public target is stated against `satisfiableDiscrete`, never `satisfiable` /
  `validSerial` (the report-02 correction remains the acceptance-critical invariant).
- [ ] Phase-4 checkpoint: loop-witness extraction (4a) proven against one concrete `isSubsetBlocked`
  witness before the full redefinition (4c) commits.
- [ ] `extractModelℤPeriodic` is wired in as the real `extractModelℤ` (no orphaned parallel def).
- [ ] `temporalTableau_complete` cross-checked for consistency against the independent Chronicle
  Hilbert completeness (`Metalogic/Completeness.lean`, oracle only — not a dependency).
- [ ] **Soundness / decidability explicitly out of scope**: this plan does NOT introduce
  `temporalTableau_sound` or `instDecidableValid`; those are handed to the deferred soundness
  research task with the exact open goal recorded above.

## Artifacts & Outputs

- plans/04_completeness-front-rescope.md (this file)
- summaries/04_*-summary.md (on implementation completion)
- Modified `Cslib/Logics/Temporal/Tableau/Completeness.lean` (Phases 4-7: bi-lasso `extractModelℤ`,
  loop-witness extraction, backward reduction, Hintikka-time-type helper, re-proved property
  lemmas, `temporalTruthLemma_untl`, `temporalTruthLemma_snce`, `openBranch_branchSat`,
  `temporalTableau_complete`)
- New sorry-free declarations: loop-witness extraction helper, backward periodic reduction,
  redefined `extractModelℤ` (+ re-proved property lemmas), complete-Hintikka-time-type helper,
  `temporalTruthLemma_untl`, `temporalTruthLemma_snce`, `openBranch_branchSat`,
  `temporalTableau_complete`
- A NEW soundness research task (to be spawned) carrying the "Deferred Deliverable" open goal

## Rollback/Contingency

- Each phase is an additive, independently-buildable increment; revert the offending phase's commit
  to return to the last green state. Phase 4 alone (bi-lasso model + re-proved property lemmas) is a
  valid landable milestone even if Phases 5-7 slip.
- **Phase 4 contingency**: if the loop-witness extraction (4a) or the full bi-lasso redefinition
  (4c) proves intractable, fall back to the `Fin`-indexed cyclic-quotient domain route (report 02
  §recs.7) — lower-risk than in plan 01 since the domain is already committed to discrete. Snapshot
  before attempting via `bash .claude/scripts/git-snapshot.sh`.
- **Phase 6 contingency**: if `swapTemporal` duality does not collapse Since to Until, budget the
  full symmetric re-proof (timing already reflects this).
- The original "island" `extractModelℤ` and its property lemmas are preserved in git history; the
  redesign is a replace-in-place whose predecessor is recoverable.
- No new axioms are introduced at any point, so rollback never leaves the module axiom-polluted.
- **Soundness deferral is not a rollback**: it is an explicit re-scope. The soundness/decidability
  deliverable is recovered by executing the new research task's follow-on plan, not by reverting.
