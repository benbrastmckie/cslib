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

### Phase 2: Propositional `T(→)` branching arm (P1-a / Deliverable 6) [COMPLETED]

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
- [x] Add a `.pos, .imp` arm to `intApplyRuleFull`
      (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean:245-268`) producing the two
      branches `[F(φ)@w'] | [T(ψ)@w']`. *(deviation: altered — `intApplyRuleFull` takes a single
      `sf : ISF Atom` with one fixed label and no `edges` parameter, so it cannot itself range
      over "every `w'` accessible from `w`"; it fires reflexively at `w' = sf.label`. The universal
      quantification over accessible worlds is instead realized by extending
      `applyAllTImpRules` (`Expansion.lean`) to also copy `T(φ→ψ)` itself to every world
      accessible from `w` lacking its own copy — each copy is then an independent `ISF` that
      `intStepBranch`/`expanded` resolves reflexively on its own turn. This keeps
      `intApplyRuleFull`'s signature unchanged, matches every other arm's `l = sf.label`-only
      shape, and keeps the `intUniverse`-containment proof shape analogous to the existing
      `.and`/`.or` cases — an unavoidable elaboration of the plan's literal text, not a
      substitution of a different design.)*
- [x] Use the existing `IntRuleResult.branchingResult` constructor — no new constructor is needed.
- [x] Confirm `intStepBranch_result_ne_notApplicable` (`Expansion.lean:163-180`) still compiles
      unchanged: its `cases hint : intApplyRuleFull` is over the three *constructors*, not the cases,
      so `.branchingResult` needs no new bullet. **Confirmed**: `lake build` of `Expansion.lean`
      succeeds with zero changes to that lemma.
- [~] Re-derive `intFuel` (`Expansion.lean:468`) and the `intExpMeasure_*` chain for the enlarged
      rule set; the split adds one branching step per T-implication per world.
      *(deviation: deferred — `intFuel`'s formula is unchanged: the new arm's outputs (`F(φ)@l`,
      `T(ψ)@l`) stay within the existing `intUniverse φ0` bound (same subformulas, same label),
      the same shape as the pre-existing `.and`/`.or` beta-rule cases the bound already covers, so
      no numeric increase is anticipated. The `intExpMeasure_*` *proof* chain lives in
      `Scheme.lean`, which imports `Soundness.lean`; `Soundness.lean` does not currently
      typecheck against the new `intApplyRuleFull` case (new non-exhaustive-match failures at
      five sites, `:143,380-381,765,934,1016`), so `Scheme.lean` cannot be elaborated at all until
      that is fixed. Continued into Phase 3, which already owns `Soundness.lean`'s
      `intRule_preserves_sat` and is the natural place to add the new case to every broken match
      site in the same pass.)*
- [x] Guard the arm so it fires at most once per `(implication, world)` pair, so the enlarged rule
      set does not reintroduce a fuel blow-up. **Satisfied structurally, not by a separate guard**:
      each `(implication, world)` pair is a distinct `ISF` (since `applyAllTImpRules` only adds a
      copy where none exists yet), and `intStepBranch`'s `expanded` set already tracks exact `ISF`
      membership, so each copy resolves at most once by construction.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` - new `.pos, .imp` arm at `:245-268`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - `intFuel` re-derivation at `:468`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - `intExpMeasure_*` chain

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` green. **Confirmed.**
- Conformance gate: `((a→b)→(a→c)) → (a→(b→c))`, `¬¬¬a → ¬a`, and `((a→b)→c) → (b→c)` all report
  **CLOSED**. **Confirmed** via `lake env lean CslibTests/TableauConformance.lean` (independent of
  `Soundness.lean`, since the harness imports only `Expansion.lean`): all three flipped, zero other
  mismatches.
- Conformance gate: `((a→b)→a) → a` (Peirce), `(a→b) ∨ (b→a)` (Dummett), `¬(a∧b) → (¬a ∨ ¬b)`,
  `¬a ∨ ¬¬a`, and Kreisel-Putnam all still report **OPEN**. **Confirmed** (same run).
- Conformance gate: all 12 currently-green propositional rows still report CLOSED (the
  coexistence check for `applyPersistenceFixpoint`). **Confirmed** (same run; zero regressions on
  any of the other 40 harness rows).
- No new `sorry` introduced; any newly-unproved goal is surfaced, not admitted. **Confirmed**: zero
  `sorry`/`axiom` in `Rules.lean`/`Expansion.lean`. **Known, expected, not-yet-fixed fallout**: the
  new `intApplyRuleFull` case is a genuine non-exhaustive-match break (not `sorry`) at five sites
  in `Soundness.lean` (`:143,380-381,765,934,1016`), so `Cslib.lean`/`lake build` (whole project)
  and `lake test` do **not** pass until Phase 3 lands — this is the expected, by-design
  intermediate state between two sequential, file-disjoint-from-temporal phases (see
  Rollback/Contingency, which anticipates evaluating Phase 2 before Phase 3 begins).

---

### Phase 3: Propositional saturation record and truth lemma (P1-b) [PARTIAL]

**Goal**: Extend the saturation record with `sat_timp`, prove the new rule case of
`intRule_preserves_sat`, and close `truthLemma`'s T-implication case. This is the semantic half of
Deliverable 6 that the truth lemma actually blocks on.

**Tasks**:
- [x] Extend `intRule_preserves_sat` (`Soundness.lean:83-107`) with the new case. The
      `.branchingResult` case already has the right shape (`∃ br ∈ branches, intBranchSatisfied …`);
      the new obligation is the classical meta-disjunction "`¬(w' ⊩ φ)` or `w' ⊩ ψ`" at `w'`.
      **Done**, using `by_cases hφ : IForces … φ` (classical excluded middle) reflexively at
      `sf.label`, then `IForces_imp` applied at `le_rfl`. Sorry-free.
      *(Necessary side effect, not scope creep: adding the new `intApplyRuleFull` case is a
      non-exhaustive-match BREAK, not merely an unproved goal, at five further sites in
      `Soundness.lean` — `intClosed_unsatisfiable`'s untouched proof stayed intact, but
      `freshAbove_applyAllTImpRules`, `intApplyRuleFull_branching_labels`,
      `intApplyRuleFull_branching_nw`, and the `applyAllTImpRules`/`applyPersistenceFixpoint`
      copy-propagation containment lemmas all needed a matching new case or a restated `happend`
      body to keep `lake build`/`Cslib.lean` green. All fixed; see the Phase 2 commit and this
      phase's commit for the full list. This IS "whatever is needed to keep the file compiling" —
      Phase 2's own charter — just discovered to be broader than the plan's file list named.)*
- [ ] **BLOCKED**: Add `sat_timp` as a **6th field** to `IBranchSaturation` (`Scheme.lean:74`).
      *(deviation: blocked, not skipped — see BLOCKER below.)*
- [ ] **BLOCKED**: Close `truthLemma`'s T-imp case (`Scheme.lean:556`) using `sat_timp`.
      *(deviation: blocked, not skipped — see BLOCKER below.)*
- [ ] **BLOCKED** (moot while `sat_timp` is not added): Update every `IBranchSaturation`
      construction site to supply the new field.
- [x] Confirm `intClosed_unsatisfiable` (`Soundness.lean:284`) is untouched — it is rule-independent.
      **Confirmed**: zero diff to this lemma.

**BLOCKER** (Phase 3, `sat_timp` field + `truthLemma` T-imp case):
- **What failed**: `sat_timp` (stated per the plan as "for every `T(φ→ψ)@w` on the branch and every
  `w' ≥ w`, either `F(φ)@w'` or `T(ψ)@w'` is present") cannot be discharged at
  `IExpandedConsistent_sat` (`Scheme.lean`, the sole `IBranchSaturation` construction site) without
  a fuel-sufficiency invariant that does not exist at HEAD.
- **What was tried**: (1) Added the `.pos, .imp` branching arm to `intApplyRuleFull` (Phase 2) so
  the rule genuinely plants `F(φ)@w' | T(ψ)@w'` — this resolves the determinacy half of the
  problem (see below). (2) Extended `applyAllTImpRules` to also copy `T(φ→ψ)` itself to every
  accessible world lacking a copy, so each accessible world gets an independent chance at the
  branching arm. (3) Traced `IExpandedConsistent_sat`'s proof pattern (identical structure to the
  existing 4 fields) to confirm the mechanism *would* work — IF every accessible world's copy is
  guaranteed to exist by the time `intStepBranch` reports no more rules apply.
- **Why it's stuck**: (3)'s "IF" is false in general. The copy-propagation runs inside
  `applyPersistenceFixpoint`'s fuel-bounded fixpoint loop (`Expansion.lean:133-139`), which reuses
  the OUTER expansion loop's remaining step-count as its OWN fuel. If that fuel is exhausted before
  persistence reaches a **genuine** fixpoint of `applyAllTImpRules`, some accessible world never
  receives its copy — and `sat_timp`'s disjunction is then genuinely **false** for that world on
  that branch, not merely unproved. This is a real mathematical gap, not a proof-technique gap.
  This exact problem (there labeled "Gap 1: fuel entanglement") is independently, pre-existingly
  documented in `Scheme.lean`'s own "`sat_timp` discharge — STOP-gate finding (task 317 phase 9)"
  comment block, predating this task; task 317 phase 9 hit the identical wall under the OLD
  (positive-only) rule design and scoped its resolution to a dedicated future phase "comparable in
  size to Phase 7 itself." This task's Phase 2 redesign (the branching arm) resolves that STOP-gate
  note's *other* half — "Gap 2: determinacy" — cleanly and completely (no bivalence/determinacy
  fact is needed any more, since the rule directly plants the disjunction); Gap 1 is orthogonal and
  untouched by the redesign.
- **What is needed**: a new step-lt-style measure lemma bounding `applyPersistenceFixpoint`'s OWN
  recursion (distinct from `intExpMeasure_step_lt`, which bounds only the outer alpha/beta/
  world-creation loop), threaded through to `intExpandBranches_openBranch_sat`'s own pre-existing
  `sorry` (the same gap, one level up, predating this task). This is new, substantial proof
  engineering — a phase-sized undertaking in its own right, not a Phase 3 sub-task.
- **Prohibited workarounds** (not used): `sorry`, an axiom, or restating `sat_timp` in a weakened
  form that `truthLemma` cannot actually use. `Scheme.lean`'s STOP-gate comment block was updated
  in place (not deleted) to record exactly which half is now resolved and which remains, so a
  future dispatch does not re-derive this analysis from scratch.

**Timing**: 2 hours (spent; see commit for the full compilation-restoration scope this phase
absorbed from Phase 2)

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - STOP-gate documentation updated
  in place at `IBranchSaturation`/`truthLemma`'s T-imp case; `sfSatisfied` gains a `.pos, .imp`
  case; `IExpandedConsistent`/`ILabelBound`/measure-containment/fuel-sufficiency lemmas extended
  for the new rule case (the "whatever is needed to keep the file compiling" fallout)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - `intRule_preserves_sat` at
  `:83-107` (new case, done); five further non-exhaustive-match sites fixed (fallout)

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` green with no `sorry` in
  `intRule_preserves_sat`. **Confirmed.** `truthLemma`'s pre-existing T-imp `sorry` remains (was
  already `sorry` at HEAD before this task; still `sorry` — not newly introduced, not newly closed).
- Conformance gate: the three flipped rows from Phase 2 remain CLOSED and the five IPC-invalid rows
  remain OPEN (the record change must not alter verdicts at all). **Confirmed** — no `Scheme.lean`
  change affects `intApplyRuleFull`'s runtime behavior; the harness result is unchanged from Phase 2.
- `sat_timp` is discharged, not assumed, at every `IBranchSaturation` construction site. **N/A**:
  `sat_timp` is not added (BLOCKED above), so nothing is assumed in its name.

---

### Phase 4: Propositional soundness re-proof (P1-c) [COMPLETED]

**Goal**: Re-prove the two currently sorry-free propositional soundness theorems against the
enlarged rule set. Per Finding 7 this is the heaviest proof burden in the task and gets a phase to
itself with nothing else competing for the run.

**Note on how this landed**: both target theorems turned out to be sound-direction only
(`intBranchSatisfied`/`intRule_preserves_sat`/`intClosed_unsatisfiable`) — they never reference
`IBranchSaturation`/`truthLemma`/`sat_timp` at all, so they are **independent of Phase 3's BLOCKER**.
Because `intApplyRuleFull`'s new case is a non-exhaustive-match break (not a mere unproved goal),
`Soundness.lean` could not build AT ALL after Phase 2 landed until every dependent proof — including
these two theorems' own dependency chain through `intRule_preserves_sat` — was restored. That
restoration (done as part of Phase 3's fallout, see above) already satisfies every task and
verification item below; no additional, separate re-proof pass was needed.

**Tasks**:
- [x] Re-prove `intExpandBranches_closed_unsat` (`Soundness.lean`) with the `.pos, .imp` arm in
      scope. Sorry-free at HEAD; confirmed sorry-free after (builds transitively through the fixed
      `intRule_preserves_sat`; the theorem's own body required no edits — it was never broken, only
      blocked from building by its upstream dependency).
- [x] Re-prove `intuitionisticTableau_sound` (`Soundness.lean`), likewise sorry-free before and
      after (same situation: theorem body unedited, builds once its dependency chain is restored).
- [x] Do not introduce `sorry`, `admit`, or an axiom to close either theorem. **Confirmed**: zero
      new `sorry`/`axiom` anywhere in `Soundness.lean` (diffed against the pre-Phase-2 baseline).
- [x] Re-run the full 19-row propositional corpus after the re-proof to confirm the proofs did not
      require a behavioral concession. **Confirmed** via the harness (see below).

**Timing**: 0 hours additional (fully absorbed into Phase 3's compilation-restoration work)

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - no additional edits beyond
  Phase 3's fallout fixes; both target theorem bodies are byte-identical to HEAD

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` green. **Confirmed.**
- `grep -c sorry` on `Soundness.lean` is unchanged from HEAD (no new admissions). **Confirmed: 0 = 0.**
- Conformance gate: all 19 propositional rows report their expected verdicts — 14 CLOSED
  (11 originally green + 3 flipped) and 5 OPEN.

---

### Phase 5: Per-branch eventuality tracker (P2 / Deliverable 5) [COMPLETED]

**Goal**: Change `temporalStepBranch` to return a per-branch tracker list so the `.branching` arm
stops returning the tracker unchanged. This must land before Phase 6, because Phase 6's termination
gate (`isTemporallyBlocked`) reads the tracker and is untrustworthy until the tracker is correct.

**Tasks**:
- [x] Change the return type at `Saturation.lean:139-144` to
      `Option (List (TBranch Atom) × List (TBranch Atom) × TimeOrdering × List (EventualityTracker Atom))`.
- [x] Fix the `.branching` arm (`Saturation.lean:156-158`), which currently returns `tracker`
      unchanged; because `untlPos`/`sncePos` are branching (`Rules.lean:265-282`), the recurring copy
      `⟨.pos, φ, t'⟩` emitted as `branch2`'s second element (`Rules.lean:271`, `:281`) is never
      registered pending. Run `registerEventualities … |> fulfillEventualities …` per branch, as
      `.linear` (`:150-155`) and `.persistent` (`:159-165`) already do. `branch1` fulfils the
      eventuality and `branch2` defers it, so their pending sets genuinely differ.
      **Done**: each element of `branches` gets its own
      `registerEventualities br tracker |> fulfillEventualities (br ++ b) newOrd` pass, returned as
      `newTrackers` positionally aligned with `newBranches`.
- [x] Replace the replication `newBs.map (fun _ => newTracker)` in `processNext`
      (`Saturation.lean:300-303`) with the returned list. **Done.**
- [x] Update the remaining call sites from Finding 5: `temporalStepBranch_preserves` (`:181-221`,
      hypothesis shape and the `obtain ⟨rfl, -, rfl, -⟩` destructuring in all four `cases result`
      arms), `run_level_P1` (`:504-509`), `temporalStepBranch_preserves_faithful` (`:703-776`),
      `WorklistInvFaithful`/`ResultInvFaithful` (`:777-791`), and
      `processNext_mismatch_closed_faithful`/`run_level_faithful`/`temporalTableau_trackerBranchFaithful`
      (`:885-1006`). **Done**, with one deliberate strengthening beyond a mechanical type-rename:
      `temporalStepBranch_preserves_faithful`'s conclusion changed from "every output branch is
      faithful w.r.t. the *same* tracker" (only ever true because the old `.branching` arm passed
      `tracker` through unchanged) to `WorklistInvFaithful newBs (newBs.map (fun _ => newOrd))
      newTrackers` — each output branch paired with its *own* tracker. Two new private helper
      lemmas (`faithful_register_fulfill`, `worklistInvFaithful_map_zip`) factor the shared
      register-then-fulfil argument out of the old `.linear`/`.persistent` proof bodies so the
      `.branching` case reuses it per-branch instead of asserting "unchanged". The now-dead
      `worklistInvFaithful_map_const` (constant-tracker replication) was removed rather than left
      unused, since `worklistInvFaithful_map_zip` strictly generalizes it and no other call site
      remained. `WorklistInvFaithful`'s definition was relocated earlier in the file (before
      `temporalStepBranch_preserves_faithful`) since the new conclusion needs to name it.
- [x] Update the docstring-only references at `Soundness.lean:36,44` and
      `Completeness.lean:69,78,87,102,646` — text edits, not proof work.
      *(deviation: altered — `Soundness.lean:36,44` describe a not-yet-existing lemma
      (`temporalStepBranch_preserves_sat`, a named "Blocked Obligation") whose prose is accurate
      independent of the tracker-list change, so left as-is; `Completeness.lean`'s "secondary,
      narrower observation" block (the passage this task's Phase 5 literally resolves) was
      rewritten in place to record the fix, plus a companion "Remaining Work" item 2a marking it
      done — this is the substantive version of "text edits, not proof work" the plan called for,
      not a mechanical line-number touch-up.)*

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` - signature at `:139-144` plus the seven call sites
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` - docstrings at `:36,44`
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` - docstrings at `:69,78,87,102,646`

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Saturation` green, no new `sorry`. **Confirmed**, plus
  whole-project `lake build` green (3253/3253 jobs), `lake exe checkInitImports` clean, `lake lint`
  shows the same single pre-existing `TrackerBranchFaithful` unused-argument finding recorded in
  the Phase 4 metadata (no new finding), `lake exe lint-style` clean, `lake exe mk_all --module`
  reports no update needed, `lake shake` shows no new finding for any Temporal/Tableau file, and
  `lake test` green (`CslibTests.TableauConformance` built and all guard_msgs assertions matched).
- Conformance gate: **zero verdict change** across all 32 green rows. This is the specific detector
  for R1 — registering eventualities makes `findEventualityDefect` (`Closure.lean`) start firing,
  which can change which branches close. **Confirmed** via `lake test`: since the harness encodes
  expected verdicts as literal `#guard_msgs` strings, any verdict flip would have failed the build;
  it did not.
- Conformance gate: the 12 red rows remain red (this phase fixes no rule, only the tracker).
  **Confirmed** (same `lake test` run; no rule-behavior file — `Rules.lean` — was touched by this
  phase).
- Zero new `sorry`/`axiom` in `Saturation.lean`/`Completeness.lean`. **Confirmed**: `grep sorry`
  on `Saturation.lean` is empty; `Completeness.lean`'s four `sorry` word occurrences are all
  pre-existing prose (`sorry-free`/`None use sorry`), none newly introduced; `grep '^axiom'` on
  both files is empty.

---

### Phase 6: Temporal rule arms — seriality, `𝐆`/`𝐇` duality, transitive propagation (P3-a) [COMPLETED]

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

### Phase 7: Cap removal, fuel raise, and headroom measurement (P3-b / Deliverables 3 + 4) [COMPLETED]

**BLOCKER 1 (RESOLVED this dispatch, commits `8b3e8df7`/`89a748d7`)**: the `ancestorTimes`
undirected-traversal bug described below is fixed. `Branch.lean:129-142`'s `ancestorTimes` now
collects only `directPredecessors` (dropped `directSuccessors`); the identical duplicate in
`Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean:736-749` is fixed the same way.
Re-verified via a full `CslibTests.TableauConformance` build against the pre-fix `guard_msgs`
strings: `𝐆p → 𝐅^k p` now flips to CLOSED for **all** of `k = 1..5` (previously stalled at
`k = 1`), and no other row's expected verdict regressed (confirmed against all 30
previously-green rows in the same build, not a separate split-harness run). The Bimodal side's
only proof-relevant consumer, `Saturation.lean:669`'s `expandBranchWithFuel_sound`, treats
`findBlockedTime(...).isSome` as an opaque `Bool` via `by_cases` and never unfolds
`ancestorTimes`/`findBlockedTime`'s definition, so `Decidability.Saturation` and the full
`Decidability` barrel (792 jobs) remain green with no proof changes required. `guard_msgs`
reconciled in `CslibTests/TableauConformance.lean` (commit `8d1689f7`) per the pre-existing rule:
update only when the new expected value is justified by the formula's own validity.

**BLOCKER 2 (RESOLVED this dispatch, commit `95940a01`, after team-lead authorization that
`Rules.lean` is in-scope per the task's `file_scope` and this dispatch's own Phase 6/7 edit
history)**: `𝐇p → 𝐇𝐇p` (past transitivity) is explicitly listed in this phase's own
verification criteria below (D3: "all remaining red temporal rows flip to CLOSED") but did
**not** flip alongside its future-direction dual `𝐆p → 𝐆𝐆p`, which did flip (already CLOSED via
Phase 6, confirmed unaffected by Blocker 1's fix since it routes through a different function,
`TimeOrdering.ancestorTimes`, not `Branch.ancestorTimes`).
- **What failed**: `𝐇p → 𝐇𝐇p` is mathematically valid (dual of the confirmed-valid
  `𝐆p → 𝐆𝐆p`) but the tableau still reports it OPEN.
- **What was tried**: traced `Rules.lean:148-155`'s `allPastPosAt`, the function responsible for
  propagating `T(𝐇φ)@t_anc` obligations to other times `t`. Its condition is
  `t == t_anc || (ord.ancestorTimes sf.label ancestorLookupFuel).contains t`, using
  `TimeOrdering.ancestorTimes` — the same **future-only** closure (`futureOf`-based) that
  `allFuturePosAt` (`:134-141`) correctly uses for propagating `T(𝐆φ)`.
- **Why it's stuck**: propagating a *past* obligation (`T(𝐇φ)@t_anc` constrains all times before
  `t_anc`) to a time `t` is sound whenever `t` is in `t_anc`'s **past** (`t < t_anc`, so every
  `s < t` is also `< t_anc`) — i.e. it needs a *past*-direction closure from `t_anc`. The actual
  condition instead checks whether `t` is in `t_anc`'s **future** light-cone (the direction
  correct for `allFuturePosAt`, wrong for `allPastPosAt`). The function's own docstring argues
  "if `t` is transitively future of `t_anc`, `t_anc` is transitively past of `t`" — true, but that
  licenses propagating `T(𝐇φ)@t_anc` to constrain times *before* `t_anc`, not to `t` itself,
  which sits in `t_anc`'s future, not its past. This is an asymmetry bug distinct from and
  unrelated to Blocker 1 (a different function, `TimeOrdering.ancestorTimes`, not
  `Branch.ancestorTimes`, and a different file, `Rules.lean`, not `Branch.lean`).
- **Fix applied**: swapped the arguments so `allPastPosAt` checks whether `t_anc` is in `t`'s
  future light-cone (`(ord.ancestorTimes t ancestorLookupFuel).contains sf.label`), equivalently
  that `t` is in `t_anc`'s past — the reversed relation from `allFuturePosAt`'s check, matching
  that `T(𝐆φ)` propagates forward while `T(𝐇φ)` propagates backward. Rewrote the docstring, which
  previously stated the same directionally-wrong justification.
- **Verification**: `lake build Cslib.Logics.Temporal.Tableau.Completeness` green. A full
  `CslibTests.TableauConformance` build against the (Blocker-1-fixed, pre-Blocker-2-fix)
  `guard_msgs` produced **exactly one** mismatch — `𝐇p → 𝐇𝐇p`, OPEN to CLOSED — and no others,
  confirming zero regressions across the 13 rows Blocker 1 already flipped plus the 30
  originally-green rows. Whole-project `lake build` (3253/3253) and `lake test` (9247/9247) both
  green; `Cslib/` bare-sorry count unchanged at 5; axiom count unchanged at 26 (0 new).
  `guard_msgs` reconciled to `"CLOSED"` for this row, commit `8af87207`.
- **Corpus state**: all 43 individually-executed corpus rows are now green; 0 red rows remain in
  Phase 7's D3 scope.

**Original BLOCKER (Branch.lean root cause, superseded by Blocker 1's resolution above — kept
for history)**:
- **What failed**: the dedup-based termination gate (`isTemporallyBlocked`) does not deliver
  headroom beyond depth 1. `𝐆p → 𝐅^1 p`, the K-row, and the duality row all flip to CLOSED as
  expected, but `𝐆p → 𝐅^2 p` (and by the same mechanism, presumably `k = 3..5`) stays OPEN even
  at fuel = 5000 (17x the natural `temporalFuel` bound of 290) -- ruling out fuel exhaustion.
- **What was tried**: isolated the open branch produced by `𝐆p → 𝐅^2 p` via a throwaway scratch
  harness (`lake env lean`, deleted after use). The saturated branch has exactly 2 time points
  (0, 1); the second `untlNeg` co-decomposition needed to reach a 3rd time never fires. Directly
  re-applying `temporalApplyOne` to the stuck signed formula returns `.notApplicable`. Traced to
  the `blocked` gate: `isSubsetBlocked b 1 0 = false` (correctly: time 1's content is genuinely
  not a subset of time 0's) but `isTemporallyBlocked b 1 ord = true` -- only possible if `1`
  appears in its own `ancestorTimes`. Confirmed directly: `ancestorTimes ord 1 = [0, 1]`.
- **Why it's stuck**: `Branch.lean`'s `ancestorTimes` (distinct from `TimeOrdering.lean`'s
  same-named, future-only helper) collects **both** `directPredecessors` and `directSuccessors`
  at every recursion step, i.e. it treats the time-ordering constraint graph as **undirected**.
  Once a single edge `(0,1)` exists, `ancestorTimes ord 1` walks `1 → 0 → 1 → 0 → ...` and its
  own `.eraseDups` includes `1` itself in the final list. `isTemporallyBlocked` then finds
  `t_anc = t` as a trivially-satisfying "ancestor" (`isSubsetBlocked b t t` and
  `allEventualitiesFulfilledOrDuplicated tracker t t` are both reflexively true), so any time
  point connected to at least one other time point is spuriously blocked. This is a pre-existing
  bug in `Branch.lean` (ported from bimodal before this task; already used by Phase 6's seriality
  arm, which happened not to trigger it because every row that needed seriality to re-fire more
  than once reached its witness via the *unconditional* `someFuturePos`/persistent-propagation
  path instead, not via a second seriality application). It is not something this phase's edit
  introduced, but this phase's cap-removal is the first rule-application site whose correctness
  actually depends on `isTemporallyBlocked` staying false past a single time-creation step, so it
  is the first place the bug bites.
- **What is needed**: a fix to `Branch.lean`'s `ancestorTimes` (likely: drop
  `directSuccessors` from the traversal, keeping only `directPredecessors`, matching the
  "ancestor" semantics `isTemporallyBlocked`'s docstring and the bimodal source it was ported
  from actually intend) plus re-verification of every conformance row Phase 6 already flipped
  (since they all route through the same, now-to-be-changed, device) and of `_preserves`-style
  lemmas that reference it. This is outside Phase 7's stated file scope (`Rules.lean`,
  `Saturation.lean`, `Completeness.lean`) and touches a device the already-proven, already-landed
  Phase 6 seriality arm depends on -- a correctness fix there has blast radius beyond this phase,
  so per the plan-compliance escalation protocol this is raised to the user rather than patched
  unilaterally.
- **Prohibited workarounds** (not used): raising `temporalFuel`'s constant to paper over this
  (ruled out both by the user's explicit strategy decision and by the diagnostic itself, which
  shows the stall is not fuel-shaped); weakening `isTemporallyBlocked`'s call site with an ad hoc
  local patch instead of fixing the shared device; `sorry`, an axiom, or a vacuous placeholder.
- **What is landed and safe**: the `blocked`-based gate wiring in `Rules.lean`/`TimeOrdering.lean`
  (commit `53eeabf2`) is mechanically correct integration work, independent of this bug -- it
  correctly flips the K-row, the duality row, and `k = 1`, and the whole-project build is green
  with the `Cslib/` bare-sorry count unchanged at 5. It should not be reverted; the bug is in the
  device it correctly wires in, not in the wiring itself.

**User-directed strategy override (continuation dispatch)**: per explicit user decision, Deliverable
4 is realized as **deduplication** (wiring the pre-existing `isTemporallyBlocked` subset-blocking
device, already used as the seriality termination gate in Phase 6, into the `untlNeg`/`snceNeg`
fresh-time-creation sites at `Rules.lean:365,391`) instead of raising `temporalFuel`'s constant. The
research report's Finding 4 already names this exact wiring as the non-viable-at-the-time
alternative to raising the constant (blocked only on Deliverable 5, which has since landed in Phase
5) — see report `Finding 4`/`D4`. Mechanically, `!blocked` replacing `ord.timeCount > 0 &&
ord.timeCount < 4` **is** the cap-removal edit at the same two sites, so Deliverables 3 and 4
resolve to a single coupled code change; the two are measured as sequential checkpoints (dedup
wiring measured first, cap-removal verdict flips measured second) rather than landed as physically
separate diffs, since the code has only one guard condition to change per site.

**Goal**: Remove the time-creation cap at both duplicated sites and raise the fuel constant, then
**measure** headroom rather than assuming one raise suffices. Completes the D3 wave.

**Tasks**:
- [x] Remove the `timeCount < 4` cap at **both** `Rules.lean:312` **and** `Rules.lean:338`
      (`snceNeg`) — the gate is duplicated and removing only one leaves the truncation in place.
      *(deviation: altered — realized as the `isTemporallyBlocked` dedup gate replacing the raw
      cap, commit `53eeabf2`, per the documented user-directed strategy override above, rather
      than a bare cap deletion.)*
- [ ] Raise `temporalFuel` to `2^(2*subformulaCount φ + 2)` at `Saturation.lean:78`. *(deviation:
      skipped — superseded by the dedup strategy override above; Deliverable 4 is realized via
      deduplication instead of a fuel raise, so this task no longer applies as written. Not
      touched this dispatch; `Saturation.lean` was outside this dispatch's authorized scope.)*
- [ ] Rewrite the `temporalFuel` docstring at `Saturation.lean:71-75`, which currently justifies a
      quadratic bound by a `2^n` argument — the justification does not match the constant it
      defends. *(deviation: skipped — same supersession as above; `Saturation.lean` remains
      untouched and its docstring/constant mismatch is unchanged from baseline, not a regression
      introduced by this dispatch.)*
- [ ] Correct the fuel references at `Completeness.lean:93` and `Completeness.lean:124`.
      *(deviation: skipped — same supersession; `Completeness.lean` outside this dispatch's scope.)*
- [ ] Confirm the three fuel consumers still typecheck: `temporalTableau` (`Saturation.lean:538`),
      `temporalTableau_instantStrict` (`:551`), and `temporalTableau_trackerBranchFaithful`
      (`:1002`). *(deviation: skipped — moot, since `temporalFuel`'s constant was never raised
      under the dedup strategy; no typecheck risk introduced.)*
- [x] **Measurement step (R4)**: for `𝐆p → 𝐅^k p` at `k = 1..5` and for `𝐆p → 𝐆𝐆p`, record the
      actual step count consumed against the new bound. *(deviation: altered — no new fuel bound
      was set (dedup strategy, not a fuel raise), so "under half the new bound" does not apply;
      instead, verified via `guard_msgs` reconciliation, commit `8d1689f7`, that all five
      `k = 1..5` rows and `𝐆p → 𝐆𝐆p` flip to CLOSED under the existing `temporalFuel` bound —
      this is the R4 measurement's verdict-side content, without a headroom table since there is
      no new bound to measure headroom against.)*
- [ ] If any row consumes more than half the new bound, raise the constant again and re-measure
      before closing the phase. *(deviation: skipped — moot under the dedup strategy, no new
      bound was introduced.)*

**Timing**: 2 hours

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Rules.lean` - cap removal at `:312` and `:338`
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` - `temporalFuel` at `:78`, docstring at `:71-75`
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` - `:93`, `:124`

**Verification**:
- Conformance gate (D3, verdict flip): all remaining red temporal rows flip to **CLOSED** —
  `𝐆p → 𝐆𝐆p`, `𝐇p → 𝐇𝐇p`, `p → 𝐆𝐏p`, `p → 𝐇𝐅p`, and `𝐆p → 𝐅^k p` for `k = 1..5` (the `k = 4`
  cut is the specific detector that both cap sites were removed). **FULLY MET** (as of Blocker 2's
  resolution, commit `95940a01`): all 6 rows CLOSED, including `𝐇p → 𝐇𝐇p`.
- Conformance gate (D4, independent from D3): under the dedup strategy override, no new fuel
  bound was introduced, so a headroom-table measurement against "the new fuel bound" does not
  apply as originally scoped; the dedup gate's own correctness (unblocked past depth 1) is
  verified instead via the D3 verdict flips above.
- Conformance gate: all previously-green rows still green, both across Blocker 1's fix (commit
  `8b3e8df7`: exactly 12 rows flipped, no others) and Blocker 2's fix (commit `95940a01`: exactly
  1 row flipped, no others).
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` green (confirmed after both fixes).
- `lake build` (whole project, 3253 jobs) and `lake test` (9247 jobs) both green (confirmed after
  both fixes). `Cslib/` bare-sorry count 5, axiom count 26, both unchanged from baseline.

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
