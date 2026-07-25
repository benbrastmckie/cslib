# Implementation Plan: Task #552

- **Task**: 552 - Tableau calculus conformance and rule-completeness repair
- **Status**: [IMPLEMENTING]
- **Effort**: 15 hours
- **Dependencies**: None
- **Research Inputs**: specs/552_tableau_calculus_conformance_rule_completeness_repair/reports/01_tableau-conformance-rule-completeness.md
- **Artifacts**: plans/01_tableau-conformance-rule-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

The temporal and intuitionistic tableau calculi are rule-incomplete: 12 of 44 executed conformance
verdicts disagree with the semantics. This plan lands an executable conformance harness first (as a
gate, red on those 12 rows), then repairs the propositional `T(→)` gap and the temporal
seriality/duality/transitivity/cap/fuel gaps on two independent fronts, closing with the soundness
re-audit obligations named lemma-by-lemma. Every rule-behavior phase is gated on specific
conformance verdict flips — never on `lake build` alone.

### Research Integration

Report 01 executed all 44 verdicts against unmodified `Cslib/` at HEAD, so the red/green baseline is
measured rather than assumed. Its Decisions D1-D5 are encoded as hard constraints below: the harness
is a gate (D5), Deliverables 2+3+4 are one wave (D3), the fuel remedy is a constant raise (D4), the
propositional remedy is the Fitting `T(→)` split (D2), and every temporal theorem statement targets
`validDiscrete` (D1). Finding 5's seven call sites and Finding 7's two soundness tables are used
verbatim; no line numbers are re-derived here.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task.

## Goals & Non-Goals

**Goals**:
- Land `CslibTests/TableauConformance.lean` as a permanent, executable conformance gate over the
  44-row corpus, registered in `CslibTests.lean`.
- Flip the three red propositional rows to CLOSED via the Fitting `T(→)` split, keeping the five
  IPC-invalid rows OPEN.
- Flip all 12 red rows (3 propositional + 9 temporal families) to their semantically correct
  verdicts, including the Finding 2b rows (`𝐆p → 𝐆𝐆p`, `¬𝐆p → 𝐅¬p`) that the original
  Deliverable 2 scoping does not cover.
- Discharge the soundness re-audit by the named lemmas of Finding 7, re-proving the two currently
  sorry-free propositional theorems.
- Record the seventh defect (Finding 2b/2c) as first-class scope, not a Deliverable 2 footnote.

**Non-Goals**:
- **Standing constraint (D1)**: no theorem introduced or restated by this task may target
  `Temporal.valid`. Every temporal statement says `validDiscrete`/`satisfiableDiscrete`. Seriality
  is sound *only* because `branchSat` (`Soundness.lean:95-106`) restricts to a
  `NoMaxOrder`/`NoMinOrder` frame class; `𝐆p → 𝐅p` is false on a two-point linear order and is
  therefore not `Temporal.valid`. The harness carries `𝐆p → 𝐅p` as an explicitly
  `validDiscrete`-labelled row so the distinction is visible in the test file itself.
- No Lindenbaum / `Sub(φ0)` completion rule for the propositional calculus (D2 rejects it).
- No branch-deduplication pass as a fuel remedy (D4 reclassifies dedup as the Deliverable 2
  termination gate).
- No new temporal soundness theorem (`temporalTableau_sound` does not exist at HEAD and is not
  created here).
- No proof-term-based assertions in the harness (`decide`/`native_decide`/`rfl` stall on
  `WellFounded.fix`; `#guard_msgs in #eval` is the only open route).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: Per-branch tracker registration makes `findEventualityDefect` start firing, silently changing which branches close | H | H | Phase 5's acceptance gate is *zero verdict change* on all 32 green rows; the harness from Phase 1 makes any change loud |
| R2: Transitive `𝐆`/`𝐇` propagation interacts with seriality to produce non-termination | H | M | Settle (iii) as option (iii)-a (single non-recursive transitive lookup, no seriality re-fire); gate seriality on `¬isTemporallyBlocked b t ord tracker` (`Branch.lean:160-167`) |
| R3: Fuel bound mis-sized. Report 04's `1.5·2^k−2` fit was **not reproduced** — its scratch file was never committed — so it must not be relied on | H | M | Use the independently measured `9·2^k−4` from Finding 4 as the empirical anchor; ship the safety margin `2^(2*subformulaCount φ + 2)` per D4 |
| R4: Transitive `𝐆` propagation blows up branch size and forces a *second* fuel raise. **Unmeasured** | M | M | Phase 7 contains an explicit fuel-headroom measurement step; do not assume one raise suffices |
| R5: Re-proving `intExpandBranches_closed_unsat` (`Soundness.lean:1039`) and `intuitionisticTableau_sound` (`Soundness.lean:1714`) — sorry-free today — is the heaviest proof burden in the task | H | H | Isolated into its own phase (Phase 4) with no other work competing for the run; Phase 3 lands `sat_timp`/`truthLemma` first so Phase 4 starts from a stable saturation record |
| R6: Harness fails to elaborate (`#eval` does not elaborate inside `Cslib/.../Tableau/`; dual-import requirement is non-obvious) | M | M | Harness lives in `CslibTests/`, uses both `import X` and `public meta import X` for all four modules, and lands standalone in Phase 1 before any rule work |
| R7: Cap removal at only one of the two duplicated gates (`Rules.lean:312` and `:338`) | M | M | Phase 7 task list names both sites explicitly; the `k=4` cut persisting at fuel `20000` is the detector |
| R8: D3's indivisible wave is split for run-size reasons and a deliverable lands half-applied | M | M | The split (Phases 6/7) is by *verification checkpoint*, not by deliverable; neither phase is a landable end state on its own and Phase 8 re-runs the full corpus |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3, 6 | 2 (for 3); 5 (for 6) |
| 4 | 4, 7 | 3 (for 4); 6 (for 7) |
| 5 | 8 | 4, 7 |

Phases within the same wave can execute in parallel.

The two columns are file-disjoint: Phases 2-4 touch only
`Cslib/Logics/Propositional/Tableau/Intuitionistic/*`, Phases 5-7 touch only
`Cslib/Logics/Temporal/Tableau/*`. This realizes the research ordering `P0 → {P1 ∥ (P2 → P3)}`.

---

### Phase 1: Conformance harness gate (P0 / Deliverable 1) [COMPLETED]

**Goal**: Land the 44-row executable conformance corpus as a permanent test file that is green on
32 rows and **red on 12**. Per D5 this is a gate, not a peer deliverable: no other phase can be
validated until it exists.

**Tasks**:
- [x] Create `CslibTests/TableauConformance.lean` with the **dual-import header**: both plain
      `import X` and `public meta import X` for each of `Cslib.Logics.Temporal.Tableau.Saturation`,
      `Cslib.Logics.Temporal.Syntax.Formula`,
      `Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion`, `Cslib.Logics.Propositional.Defs`.
      Without the plain form: `Invalid definition 'p', may not access declaration 'Formula.atom'
      imported as 'meta'`. Without the meta form: `Invalid 'meta' definition '_eval',
      'temporalTableau' is not accessible here`. Verified via a throwaway `lake env lean` scratch
      probe before landing the full file, matching the report's own reproduction method.
- [x] Define two `String`-valued verdict adapters **in the harness file only** (never in `Cslib/`):
      `temporalVerdict : TemporalTableauResult Nat → String` and
      `intVerdict : IntTableauResult Nat → String`. `TemporalTableauResult` (`Saturation.lean:63-67`)
      and `IntTableauResult` (`Expansion.lean:75-79`) derive neither `Repr` nor `BEq`, so plain
      `#guard` is unusable.
- [x] Encode all rows as `#guard_msgs in #eval` assertions (the in-repo idiom, cf.
      `CslibTests/LTS.lean:125-139`). Do **not** use `decide`, `native_decide`, or `rfl` — they stall
      on `WellFounded.fix` via the nested `let rec` in `intExpandBranches` (`Expansion.lean:357`).
      *(deviation: altered — expanding Finding 0's two `k`-indexed families into individually
      asserted formulas yields 43 rows (27 green / 16 red), not the plan summary's rounded "44 rows
      / 32 green / 12 red"; see the harness's own "Corpus provenance" docstring section for the
      reconciliation. The set of which formulas are defective is unchanged — only the row count
      arithmetic differs, and per-`k` assertions are required for Phase 7's `k = 4` cut to be its
      own detector.)*
- [x] Label the `𝐆p → 𝐅p` row explicitly as `validDiscrete` (not `Temporal.valid`) in a comment
      adjacent to the assertion, per D1.
- [x] Annotate each red row with the expected verdict and the phase that will flip it, so
      the file documents the defect rather than hiding it.
- [x] Register in `CslibTests.lean` as `public import CslibTests.TableauConformance`, alphabetically
      after `CslibTests.Reduction` (last entry in the barrel, so also last overall).

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `CslibTests/TableauConformance.lean` - new file; 44 assertions + 2 verdict adapters
- `CslibTests.lean` - barrel registration

**Verification**:
- `lake test` runs the harness. **Result**: 27 of 43 rows pass; 16 fail, matching Finding 0
  exactly — the 3 propositional rows (`((a→b)→(a→c)) → (a→(b→c))`, `¬¬¬a → ¬a`,
  `((a→b)→c) → (b→c)`) and the 13 temporal rows (`𝐆p → 𝐅p`, `𝐇p → 𝐏p`, `𝐆p → 𝐆𝐆p`, `𝐇p → 𝐇𝐇p`,
  `p → 𝐆𝐏p`, `p → 𝐇𝐅p`, `𝐆¬p → (𝐆p → 𝐆⊥)`, `¬𝐆p → 𝐅¬p`, and `𝐆p → 𝐅^k p` for each `k = 1..5`
  individually). This is the row-count deviation recorded above — same defect set as the plan's
  "12 rows fail" language, counted per-formula instead of per-family.
- `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`, and `lake exe mk_all --module` all ran
  clean against the new file (zero warnings/findings attributable to it; the pre-existing
  project-wide `lake shake` backlog and pre-existing `sorry`s elsewhere are unrelated to this
  phase and unchanged by it).
- No file under `Cslib/` is modified by this phase (confirmed: `CslibTests/TableauConformance.lean`
  new, `CslibTests.lean` one-line barrel addition only).

---

### Phase 2: Propositional `T(→)` branching arm (P1-a / Deliverable 6) [NOT STARTED]

**Goal**: Add the Fitting `T(→)` split to `intApplyRuleFull` and re-derive the termination
measure, so the three red propositional rows flip. Proof obligations are deferred to Phases 3-4;
this phase is the behavioral change plus whatever is needed to keep the file compiling.

**Settled question (Finding 6d — replace vs. coexist)**: the new `.pos, .imp` arm **coexists** with
`applyPersistenceFixpoint`; it does not replace it. Persistence propagates T-formulas forward along
`≤` (Kripke monotonicity), an obligation the `T(→)` split does not subsume — removing it would
regress the 12 currently-green propositional rows and force a rewrite of `IBranchSaturation`'s five
existing fields. The arm is additive and carries its own `sat_timp` field. Ordering: the `T(→)` arm
fires only on worlds where `applyPersistenceFixpoint` has already reached fixpoint, so the split
never re-branches on formulas persistence is about to add. The "replace" alternative is recorded in
Rollback/Contingency.

**Tasks**:
- [ ] Add a `.pos, .imp` arm to `intApplyRuleFull`
      (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean:245-268`) producing the two
      branches `[F(φ)@w'] | [T(ψ)@w']`.
- [ ] Use the existing `IntRuleResult.branchingResult` constructor — no new constructor is needed.
- [ ] Confirm `intStepBranch_result_ne_notApplicable` (`Expansion.lean:163-180`) still compiles
      unchanged: its `cases hint : intApplyRuleFull` is over the three *constructors*, not the cases,
      so `.branchingResult` needs no new bullet.
- [ ] Re-derive `intFuel` (`Expansion.lean:468`) and the `intExpMeasure_*` chain for the enlarged
      rule set; the split adds one branching step per T-implication per world.
- [ ] Guard the arm so it fires at most once per `(implication, world)` pair, so the enlarged rule
      set does not reintroduce a fuel blow-up.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` - new `.pos, .imp` arm at `:245-268`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - `intFuel` re-derivation at `:468`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - `intExpMeasure_*` chain

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` green.
- Conformance gate: `((a→b)→(a→c)) → (a→(b→c))`, `¬¬¬a → ¬a`, and `((a→b)→c) → (b→c)` all report
  **CLOSED**.
- Conformance gate: `((a→b)→a) → a` (Peirce), `(a→b) ∨ (b→a)` (Dummett), `¬(a∧b) → (¬a ∨ ¬b)`,
  `¬a ∨ ¬¬a`, and Kreisel-Putnam all still report **OPEN**.
- Conformance gate: all 12 currently-green propositional rows still report CLOSED (the
  coexistence check for `applyPersistenceFixpoint`).
- No new `sorry` introduced; any newly-unproved goal is surfaced, not admitted.

---

### Phase 3: Propositional saturation record and truth lemma (P1-b) [NOT STARTED]

**Goal**: Extend the saturation record with `sat_timp`, prove the new rule case of
`intRule_preserves_sat`, and close `truthLemma`'s T-implication case. This is the semantic half of
Deliverable 6 that the truth lemma actually blocks on.

**Tasks**:
- [ ] Add `sat_timp` as a **6th field** to `IBranchSaturation` (`Scheme.lean:74`), stating that for
      every `T(φ→ψ)@w` on the branch and every `w' ≥ w`, either `F(φ)@w'` or `T(ψ)@w'` is present.
- [ ] Extend `intRule_preserves_sat` (`Soundness.lean:83-107`) with the new case. The
      `.branchingResult` case already has the right shape (`∃ br ∈ branches, intBranchSatisfied …`);
      the new obligation is the classical meta-disjunction "`¬(w' ⊩ φ)` or `w' ⊩ ψ`" at `w'`.
- [ ] Close `truthLemma`'s T-imp case (`Scheme.lean:556`) using `sat_timp`.
- [ ] Update every construction site of `IBranchSaturation` to supply the new field; do not weaken
      the record to make old sites compile.
- [ ] Confirm `intClosed_unsatisfiable` (`Soundness.lean:284`) is untouched — it is rule-independent.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - `IBranchSaturation` at `:74`, `truthLemma` at `:556`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - `intRule_preserves_sat` at `:83-107`

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` green with no `sorry` in
  `truthLemma` or `intRule_preserves_sat`.
- Conformance gate: the three flipped rows from Phase 2 remain CLOSED and the five IPC-invalid rows
  remain OPEN (the record change must not alter verdicts at all).
- `sat_timp` is discharged, not assumed, at every `IBranchSaturation` construction site.

---

### Phase 4: Propositional soundness re-proof (P1-c) [NOT STARTED]

**Goal**: Re-prove the two currently sorry-free propositional soundness theorems against the
enlarged rule set. Per Finding 7 this is the heaviest proof burden in the task and gets a phase to
itself with nothing else competing for the run.

**Tasks**:
- [ ] Re-prove `intExpandBranches_closed_unsat` (`Soundness.lean:1039`) with the `.pos, .imp` arm in
      scope. It is sorry-free at HEAD; it must be sorry-free after.
- [ ] Re-prove `intuitionisticTableau_sound` (`Soundness.lean:1714`), likewise sorry-free before and
      after.
- [ ] Do not introduce `sorry`, `admit`, or an axiom to close either theorem. If a genuine gap
      appears, stop and record it rather than admitting it.
- [ ] Re-run the full 19-row propositional corpus after the re-proof to confirm the proofs did not
      require a behavioral concession.

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - `:1039`, `:1714`

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` green.
- `grep -c sorry` on `Soundness.lean` is unchanged from HEAD (no new admissions).
- Conformance gate: all 19 propositional rows report their expected verdicts — 14 CLOSED
  (11 originally green + 3 flipped) and 5 OPEN.

---

### Phase 5: Per-branch eventuality tracker (P2 / Deliverable 5) [NOT STARTED]

**Goal**: Change `temporalStepBranch` to return a per-branch tracker list so the `.branching` arm
stops returning the tracker unchanged. This must land before Phase 6, because Phase 6's termination
gate (`isTemporallyBlocked`) reads the tracker and is untrustworthy until the tracker is correct.

**Tasks**:
- [ ] Change the return type at `Saturation.lean:139-144` to
      `Option (List (TBranch Atom) × List (TBranch Atom) × TimeOrdering × List (EventualityTracker Atom))`.
- [ ] Fix the `.branching` arm (`Saturation.lean:156-158`), which currently returns `tracker`
      unchanged; because `untlPos`/`sncePos` are branching (`Rules.lean:265-282`), the recurring copy
      `⟨.pos, φ, t'⟩` emitted as `branch2`'s second element (`Rules.lean:271`, `:281`) is never
      registered pending. Run `registerEventualities … |> fulfillEventualities …` per branch, as
      `.linear` (`:150-155`) and `.persistent` (`:159-165`) already do. `branch1` fulfils the
      eventuality and `branch2` defers it, so their pending sets genuinely differ.
- [ ] Replace the replication `newBs.map (fun _ => newTracker)` in `processNext`
      (`Saturation.lean:300-303`) with the returned list.
- [ ] Update the remaining call sites from Finding 5: `temporalStepBranch_preserves` (`:181-221`,
      hypothesis shape and the `obtain ⟨rfl, -, rfl, -⟩` destructuring in all four `cases result`
      arms), `run_level_P1` (`:504-509`), `temporalStepBranch_preserves_faithful` (`:703-776`),
      `WorklistInvFaithful`/`ResultInvFaithful` (`:777-791`), and
      `processNext_mismatch_closed_faithful`/`run_level_faithful`/`temporalTableau_trackerBranchFaithful`
      (`:885-1006`).
- [ ] Update the docstring-only references at `Soundness.lean:36,44` and
      `Completeness.lean:69,78,87,102,646` — text edits, not proof work.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` - signature at `:139-144` plus the seven call sites
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` - docstrings at `:36,44`
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` - docstrings at `:69,78,87,102,646`

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Saturation` green, no new `sorry`.
- Conformance gate: **zero verdict change** across all 32 green rows. This is the specific detector
  for R1 — registering eventualities makes `findEventualityDefect` (`Closure.lean`) start firing,
  which can change which branches close.
- Conformance gate: the 12 red rows remain red (this phase fixes no rule, only the tracker).

---

### Phase 6: Temporal rule arms — seriality, `𝐆`/`𝐇` duality, transitive propagation (P3-a) [NOT STARTED]

**Goal**: Land the three coordinated `Rules.lean` edits of Deliverable 2 plus the Finding 2b/2c
seventh defect, and re-prove the two `_preserves` lemmas.

**Wave note (D3)**: Deliverables 2 + 3 + 4 are one indivisible wave. Phases 6 and 7 are a split of
that wave **by verification checkpoint, not by deliverable** — neither is a landable end state on
its own. Phase 6 is the checkpoint "new arms fire correctly under the existing `timeCount < 4` cap";
Phase 7 is the checkpoint "the cap and fuel bound no longer truncate them". Do not mark Deliverable
2, 3, or 4 complete until Phase 7 passes.

**Settled question (transitive propagation, option (iii)-a vs (iii)-b)**: adopt **(iii)-a** —
replace the direct-step `futureOf`/`pastOf` lookup in the `allFuturePosAt`/`allPastPosAt`
propagation (`Rules.lean:124-139`) with the transitive-closure helper `ancestorTimes`
(`TimeOrdering.lean:117-122`) in the appropriate orientation. Reasoning: it is the smaller change,
it keeps propagation a single non-recursive pass so the existing termination measure still decreases,
and it decouples transitivity from seriality. Option (iii)-b (make seriality re-fire so `𝐆` reaches
transitively via chained direct steps) is rejected because the report flags it as risking
non-termination and it couples two independent defects into one failure mode; it is recorded in
Rollback/Contingency.

**Tasks**:
- [ ] (i) Add the seriality arm to `temporalApplyPos` (`Rules.lean`), firing when
      `ord.futureOf t = []` (resp. `ord.pastOf t = []`), via `addFuture`/`addPast` followed by
      `propagateToFuture`/`propagateToPast`.
- [ ] (i) Gate the seriality arm on `¬isTemporallyBlocked b t ord tracker` (`Branch.lean:160-167`)
      for termination. This is the dedup-as-termination-gate reclassification from D4, not a fuel fix.
- [ ] (ii) Add the missing `asAllFuture?`/`asAllPast?` arms to `temporalApplyNeg`
      (`Rules.lean:287-349`), which currently falls through to `.notApplicable` at `:349`, breaking
      the duality its own rule table advertises at `Rules.lean:27-28`.
- [ ] (iii) Switch `allFuturePosAt`/`allPastPosAt` propagation (`Rules.lean:124-139`) to
      `ancestorTimes` per the settled option (iii)-a above.
- [ ] Re-prove `temporalApplyPos_preserves` (`Rules.lean:502-593`): the
      `split at h <;> try split at h …` chain at `:520-521` currently produces exactly 9 bullets; the
      new arms add bullets that surface as unproved goals. This is mechanically checkable and never
      silent.
- [ ] Re-prove `temporalApplyNeg_preserves` (`Rules.lean:601-668`), currently 7 bullets.
- [ ] Confirm `temporalApplyOne_preserves` (`Rules.lean:675-705`) needs no new bullets — it is
      dispatch only.
- [ ] Confirm no theorem statement introduced here mentions `Temporal.valid` (D1). Forward soundness
      for the seriality arm is discharged by construction: `branchSat` (`Soundness.lean:95-106`)
      already quantifies over a domain with `NoMaxOrder D` and `NoMinOrder D`, so "every time has a
      successor and a predecessor" is given by the frame class and no new semantic assumption enters.

**Timing**: 2 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Rules.lean` - `:124-139`, `:287-349`, seriality arm in `temporalApplyPos`, `:502-593`, `:601-668`
- `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` - `ancestorTimes` at `:117-122` (read/reuse; extend only if the opposite orientation is missing)
- `Cslib/Logics/Temporal/Tableau/Branch.lean` - `isTemporallyBlocked` at `:160-167` (read/reuse)

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Rules` green; `temporalApplyPos_preserves` and
  `temporalApplyNeg_preserves` sorry-free.
- Conformance gate (shallow rows, reachable under the existing cap): `𝐆p → 𝐅p` (seriality),
  `𝐇p → 𝐏p` (past seriality), `¬𝐆p → 𝐅¬p` (duality), and `𝐆¬p → (𝐆p → 𝐆⊥)` (K) all flip to
  **CLOSED**.
- Conformance gate: `𝐆p → 𝐅^1 p` flips to CLOSED.
- Conformance gate: all 32 green rows unchanged — in particular `𝐆p → p` stays **OPEN** (`𝐆` is over
  *strictly* future) and `𝐅^k p → 𝐅^k p` stays CLOSED for `k = 0..6`.
- Deep rows (`𝐆p → 𝐆𝐆p`, `𝐇p → 𝐇𝐇p`, `p → 𝐆𝐏p`, `p → 𝐇𝐅p`, `𝐆p → 𝐅^k p` for `k ≥ 2`) may still be
  red at this checkpoint; that is expected and is Phase 7's gate.

---

### Phase 7: Cap removal, fuel raise, and headroom measurement (P3-b / Deliverables 3 + 4) [NOT STARTED]

**Goal**: Remove the time-creation cap at both duplicated sites and raise the fuel constant, then
**measure** headroom rather than assuming one raise suffices. Completes the D3 wave.

**Tasks**:
- [ ] Remove the `timeCount < 4` cap at **both** `Rules.lean:312` **and** `Rules.lean:338`
      (`snceNeg`) — the gate is duplicated and removing only one leaves the truncation in place.
- [ ] Raise `temporalFuel` to `2^(2*subformulaCount φ + 2)` at `Saturation.lean:78`.
- [ ] Rewrite the `temporalFuel` docstring at `Saturation.lean:71-75`, which currently justifies a
      quadratic bound by a `2^n` argument — the justification does not match the constant it defends.
- [ ] Correct the fuel references at `Completeness.lean:93` and `Completeness.lean:124`.
- [ ] Confirm the three fuel consumers still typecheck: `temporalTableau` (`Saturation.lean:538`),
      `temporalTableau_instantStrict` (`:551`), and `temporalTableau_trackerBranchFaithful`
      (`:1002`). The latter two pass fuel as an opaque `Nat` to inductions that are numerically
      agnostic, so the raise is proof-safe.
- [ ] **Measurement step (R4)**: for `𝐆p → 𝐅^k p` at `k = 1..5` and for `𝐆p → 𝐆𝐆p`, record the
      actual step count consumed against the new bound. Compare to the independently measured
      `9·2^k−4` growth from Finding 4. Do **not** use report 04's `1.5·2^k−2` fit — it was not
      reproduced and its scratch file was never committed.
- [ ] If any row consumes more than half the new bound, raise the constant again and re-measure
      before closing the phase. Record the measured table in the phase's completion notes.

**Timing**: 2 hours

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Rules.lean` - cap removal at `:312` and `:338`
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` - `temporalFuel` at `:78`, docstring at `:71-75`
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` - `:93`, `:124`

**Verification**:
- Conformance gate (D3, verdict flip): all remaining red temporal rows flip to **CLOSED** —
  `𝐆p → 𝐆𝐆p`, `𝐇p → 𝐇𝐇p`, `p → 𝐆𝐏p`, `p → 𝐇𝐅p`, and `𝐆p → 𝐅^k p` for `k = 1..5` (the `k = 4`
  cut is the specific detector that both cap sites were removed).
- Conformance gate (D4, independent from D3): the measured headroom table shows every row completing
  at under half the new fuel bound. A verdict flip alone does not discharge D4, and a fuel raise
  alone does not discharge D3.
- Conformance gate: all 32 green rows still green.
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` green.

---

### Phase 8: Scope record update and full-corpus close-out (P4) [NOT STARTED]

**Goal**: Promote the seventh defect to first-class scope and confirm the whole 44-row corpus is
green in one run.

**Tasks**:
- [ ] Update the six-deliverable scope record in the task description so Finding 2b/2c (the missing
      `asAllFuture?`/`asAllPast?` negative arms and transitive propagation) is recorded as
      first-class work, not a footnote of Deliverable 2. As written, Deliverable 2 would be marked
      complete while `𝐆p → 𝐆𝐆p` and `¬𝐆p → 𝐅¬p` remain OPEN.
- [ ] Remove the per-row "expected red, will be flipped by Phase N" annotations from
      `CslibTests/TableauConformance.lean`, converting the file into a pure regression guard.
- [ ] Run the full corpus once, both fronts together, on a clean build.
- [ ] Record the final fuel-headroom table and the D1 validity-class note as comments in the harness
      header so future readers do not re-litigate `validDiscrete` vs `Temporal.valid`.

**Timing**: 1 hour

**Depends on**: 4, 7

**Files to modify**:
- `CslibTests/TableauConformance.lean` - annotation cleanup, header notes
- `specs/552_tableau_calculus_conformance_rule_completeness_repair/` - scope record update

**Verification**:
- `lake test` green: **44 of 44** rows report their expected verdicts, zero red.
- `lake build` green across the whole library.
- No new `sorry` anywhere relative to HEAD.

## Testing & Validation

The conformance harness is the primary validation instrument. `lake build` being green is **never**
sufficient acceptance for a rule-behavior phase — every one of the 12 defects in scope is invisible
to the build and visible only as a verdict. That is the central lesson of the research.

- [ ] Phase 1: 32 rows green, 12 rows red-and-documented; no `Cslib/` file touched.
- [ ] Phase 2: 3 propositional rows flip to CLOSED; 5 IPC-invalid rows stay OPEN; 12 green
      propositional rows stay CLOSED.
- [ ] Phase 3: no verdict change relative to Phase 2; `sat_timp` discharged at every construction site.
- [ ] Phase 4: `intExpandBranches_closed_unsat` and `intuitionisticTableau_sound` sorry-free; all 19
      propositional rows correct.
- [ ] Phase 5: zero verdict change on all 32 green rows (R1 detector); 12 red rows still red.
- [ ] Phase 6: `𝐆p → 𝐅p`, `𝐇p → 𝐏p`, `¬𝐆p → 𝐅¬p`, `𝐆¬p → (𝐆p → 𝐆⊥)`, `𝐆p → 𝐅^1 p` flip;
      `𝐆p → p` stays OPEN; `temporalApplyPos_preserves`/`temporalApplyNeg_preserves` sorry-free.
- [ ] Phase 7 (D3 gate): remaining 8 temporal rows flip, `k = 4` included.
- [ ] Phase 7 (D4 gate, independent): measured headroom table shows every row under half the new
      fuel bound.
- [ ] Phase 8: 44/44 green in a single clean `lake test` run.
- [ ] Cross-cutting: no theorem statement anywhere in the diff targets `Temporal.valid` (D1).
- [ ] Cross-cutting: `sorry` count unchanged from HEAD in every modified `Cslib/` file.

## Artifacts & Outputs

- `CslibTests/TableauConformance.lean` — new, permanent 44-row conformance harness with two
  `String`-valued verdict adapters and a dual-import header.
- `CslibTests.lean` — barrel registration.
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Rules,Expansion,Scheme,Soundness}.lean` —
  Fitting `T(→)` split, `sat_timp`, re-proved soundness.
- `Cslib/Logics/Temporal/Tableau/{Rules,Saturation,Soundness,Branch,TimeOrdering,Completeness}.lean` —
  per-branch tracker, seriality/duality/transitivity arms, cap removal, fuel raise.
- Measured fuel-headroom table (Phase 7), recorded in the harness header and the task summary.
- Updated six-deliverable scope record promoting Finding 2b/2c to first-class work.

## Rollback/Contingency

**Per-phase revert boundaries.** Each phase is a separate commit and each front is file-disjoint, so
either column can be reverted without touching the other. Phase 1 touches nothing under `Cslib/` and
should never need reverting; keeping it while reverting a repair phase is the preferred degraded
state, because it leaves the defects documented rather than hidden.

**Losing option for transitive propagation ((iii)-b).** If option (iii)-a proves insufficient —
specifically if `ancestorTimes` does not reach the times that seriality creates during the same
saturation level, leaving `𝐆p → 𝐆𝐆p` OPEN after Phase 7 — fall back to (iii)-b: make the seriality
arm re-fire so `𝐆` reaches transitively via chained direct steps. This was rejected as the primary
option because the research flags it as risking non-termination. If adopted, the
`¬isTemporallyBlocked b t ord tracker` gate becomes load-bearing for termination rather than merely
prudent, and Phase 7's headroom measurement must be re-run from scratch with an explicit
step-count ceiling.

**Losing option for `applyPersistenceFixpoint` (replace instead of coexist).** If the coexisting
`T(→)` arm and the persistence fixpoint interact badly — detected by any of the 12 currently-green
propositional rows flipping to OPEN in Phase 2 — the fallback is to subsume persistence into the new
arm and delete `applyPersistenceFixpoint`. This is a larger change: it rewrites `IBranchSaturation`'s
five existing fields and invalidates the Phase 4 soundness proofs, so it should only be taken with
Phases 3-4 not yet started.

**Fuel raise insufficient (R4).** If the Phase 7 measurement shows a row above half the bound, raise
the exponent and re-measure rather than accepting the pass. Do not fall back to branch dedup as a
fuel remedy — D4 reclassifies dedup as the Deliverable 2 termination gate, and using it as a fuel
fix would re-entangle the two.

**Tracker change regresses closures (R1).** If Phase 5 changes any of the 32 green verdicts,
`findEventualityDefect` has begun firing where it previously did not. Revert Phase 5 and re-scope it
to register eventualities on the `.branching` arm only after `fulfillEventualities` has run on both
branches, rather than restructuring the tracker plumbing wholesale.
