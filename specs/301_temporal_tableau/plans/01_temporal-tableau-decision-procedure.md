# Implementation Plan: Task #301 — Temporal Tableau Decision Procedure

- **Task**: 301 - temporal_tableau
- **Status**: [NOT STARTED]
- **Effort**: 22 hours
- **Dependencies**: None (all upstream temporal Syntax/Semantics/ProofSystem and Foundations tableau kernel already exist and are proven)
- **Research Inputs**: specs/301_temporal_tableau/reports/01_temporal-tableau-decision-procedure.md
- **Artifacts**: plans/01_temporal-tableau-decision-procedure.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - CONTRIBUTING.md, NOTATION.md, ORGANISATION.md (CSLib)
- **Type**: cslib
- **Lean Intent**: false

## Overview

Build a tableau decision procedure for the existing temporal logic `Cslib.Logic.Temporal.Formula` (primitives `atom, bot, imp, untl, snce`, Burgess event-guard convention, Łukasiewicz encoding), with until/since decomposition rules, `Nat` time labels, a `TimeOrdering` constraint store, density/discreteness frame-class rules, and the `Valid/ValidSerial/ValidDense/ValidDiscrete` soundness hierarchy as the semantic target. The procedure is built by **instantiating the proven Foundations generic kernel** (`Cslib.Logic.Tableau`, `SignedFormula F L`, `Branch F L`, `RuleResult` with the `persistent` variant) at `F = Temporal.Formula Atom, L = Nat`, **porting algorithms (not types)** from the ~6,000-line bimodal `Decidability` system, imitating `Modal/Tableau` for label-introduction structure, and following the `Propositional/Tableau/Classical` proof skeleton. Definition of done: 8 files under `Cslib/Logics/Temporal/Tableau/` building sorry-free with the full CSLib CI pipeline green; **zero-debt** (no `sorry`, no new axioms) — if completeness cannot be closed sorry-free within scope, mark the task `[BLOCKED]` rather than defer.

### Research Integration

Integrated from `reports/01_temporal-tableau-decision-procedure.md`:
- **Substrate**: Foundations kernel `Cslib/Foundations/Logic/Tableau/*` (`Sign`, `SignedFormula F L`, `Branch F L`, `ClosureReason`/`ClosureCondition`/`ClassicalClosure`, `RuleResult.persistent`, `PropTableauRule`/`applyPropRule`/`tryAllPropRules`) instantiated at `F = Temporal.Formula Atom, L = Nat`. Reuse directly — do **not** reuse bimodal types (they carry a `box` constructor temporal logic lacks).
- **Algorithms to port** (retyped, box/diamond machinery dropped): bimodal `TimeOrdering` (`SignedFormula.lean:684`), `untlPos/sncePos` event-witness/guard-continue bodies (`Tableau.lean:688/732`), `untlNeg/snceNeg` Reynolds co-decomposition (`Tableau.lean:774/836`), `as*?` decomposition family (`Tableau.lean:197–286`), `Eventuality`/`EventualityTracker` (`SignedFormula.lean:585–635`), `timeType`/`isSubsetBlocked`/`isTemporallyBlocked`/`findBlockedTime`, `subformula_property`, `densityRule`/`denseIndicatorClosure`/`priorUZ`/`priorSZ`/`z1Rule`, `allRulesForFC` gating idiom, `sat_*`/`truthLemma_*`/`branchTruthLemma` proof shapes.
- **Reuse directly (temporal, already proven)**: `FrameClass{Base,Dense,Discrete}` (+ `LE`, `DecidableRel (≤)`, `minFrameClass`, `Axiom.density`), `Formula.complexity`, `Subformulas` API (`untl_left/right_mem_subformulas`, `snce_left/right_mem_subformulas`, `subformulas_trans`, `self_mem_subformulas`), `Context`, `TemporalModel`, `Satisfies` (+ `@[simp]` constructor lemmas `untl_iff`/`snce_iff`/etc.), `Valid/ValidSerial/ValidDense/ValidDiscrete`, `swapTemporal` + duality lemmas (halves since-from-until proofs).
- **Must reimplement (no direct reuse)**: `Hashable (Temporal.Formula Atom)` instance; temporal `as*?`/`*Of?` decomposition functions; the `untl`/`snce`/G/H/F/P rule cases; **eventuality-defect closure + time-subset blocking** (the one genuinely new closure mode); temporal `extractModel` over recorded time points.
- **Riskiest obligations** (sequenced to surface early where possible): #1 until/since completeness via eventuality fulfilment (highest — bimodal defers FMP-completeness, no inheritable proof); #2 termination/blocking soundness; #3 density/discreteness rule soundness; #4 Reynolds co-decomposition termination.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md consultation performed. Task 301 is the most complex member of the 299–301 tableau batch (modal K / temporal) for which the Foundations `RuleResult.persistent` kernel was explicitly built.

## Goals & Non-Goals

**Goals**:
- A sorry-free, axiom-free tableau decision procedure for temporal logic across 8 files under `Cslib/Logics/Temporal/Tableau/`.
- Until/since event-witness/guard-continue branching and Reynolds co-decomposition over a `TimeOrdering`, ported from the bimodal algorithms.
- Frame-class rules (`Base`/`Dense`/`Discrete`) gated by `decide (FrameClass.X ≤ fc)`, connected to the existing `Valid/ValidSerial/ValidDense/ValidDiscrete` hierarchy.
- Soundness proven against `Satisfies`; completeness (truth lemma + countermodel extraction) proven sorry-free, or `[BLOCKED]` with a decomposition recommendation if intractable in scope.
- Each new file passes `lake build`, `lake exe lint-style`, and `lake shake` incrementally; full `lake test` green at the end.

**Non-Goals**:
- Re-typing or modifying the bimodal `Decidability` system (it is reused only as an algorithm/proof template).
- Adding box/diamond/world machinery — temporal logic has a single time-line; `Label` collapses to a bare `Nat` time index.
- Changing existing temporal `Syntax`/`Semantics`/`ProofSystem` files, except adding the one required `Hashable (Formula Atom)` instance.
- Deferring any obligation with `sorry` or new axioms (zero-debt policy).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Until/since completeness via eventuality fulfilment cannot be closed sorry-free (bimodal defers FMP-completeness; no inheritable proof) | H | M | Sequence as the final phase so all machinery is in place; port `sat_*`/`truthLemma`/`branchTruthLemma` shapes; **if intractable, mark task `[BLOCKED]` with decomposition recommendation — never sorry/axiom** |
| Termination/blocking soundness (worklist + time-subset blocking + eventuality fulfilment) | H | M | Lean on existing `Subformulas` transitivity lemmas + ported `subformula_property` and `expandBranchWithFuel_sound` template; fuel = `soundFuel φ` from `Formula.complexity` |
| Density/discreteness rule soundness over `DenselyOrdered`/`SuccOrder`/`PredOrder`/`IsSuccArchimedean` | M | M | Temporal `Validity` hierarchy already supplies the exact typeclasses; prove one soundness lemma per rule; `swapTemporal` duality halves the past-mirror proofs |
| Reynolds co-decomposition (`untlNeg`/`snceNeg`) nontermination via persistent re-firing | M | M | Port the bimodal `timeCount`-gated future-creation (`0 < timeCount < 4`) verbatim; carry its termination argument |
| `TimeOrdering` direct-successor vs transitive/dense-closure design choice blocks completeness over genuine dense models | M | M | Default to bimodal direct-successor semantics (matches ported `branchTruth`); only add transitive closure if a completeness sub-goal demands it — decide in Phase 8, document in plan |
| `Hashable (Formula Atom)` deriving requirement breaks `SignedFormula`/`Branch` instantiation | M | L | Add instance first (Phase 1), mirroring `Modal` `instHashableModalProposition` / bimodal `Formula.hashFormula`; `DecidableEq` already derived |
| CSLib lint/shake violations accumulate (unused imports, style) | L | M | Run `lake build` + `lake exe lint-style` + `lake shake` per phase, not just at the end |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 1, 2 |
| 4 | 5 | 1, 4 |
| 5 | 6 | 3, 4, 5 |
| 6 | 7 | 3, 5, 6 |
| 7 | 8 | 6, 7 |

Phases within the same wave can execute in parallel. Phases 1 and 2 are independent foundational files; Phases 3 (Rules) and 4 (Branch) both depend only on the foundations and could in principle run in parallel, but Phase 5 (Closure) depends on Branch, and Saturation (6) depends on Rules + Branch + Closure, so the critical path is 1→3→6→7→8.

---

### Phase 1: Defs.lean — kernel instantiation, Hashable, decomposition functions [COMPLETED]

**Goal**: Instantiate the Foundations tableau kernel at `F = Temporal.Formula Atom, L = Nat`, supplying the `Hashable` instance, the decomposition functions, and the fuel measure that everything downstream needs.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Tableau/Defs.lean`; import Foundations `Cslib.Logic.Tableau.*`, temporal `Syntax.Formula`, `Syntax.Subformulas`.
- [ ] Add `instance : Hashable (Temporal.Formula Atom)` (mirror `Modal` `instHashableModalProposition` / bimodal `Formula.hashFormula`); confirm `DecidableEq` is already derived.
- [ ] Define the time label as `L = Nat` (time index); document the collapse of bimodal `Label.{world,time}` to a bare `Nat`.
- [ ] Define classical decomposition functions `tempImpOf?`, `tempNegOf?`, `tempOrOf?`, `tempAndOf?` over the Łukasiewicz encoding (consumed by `applyPropRule`).
- [ ] Define the temporal eventuality decomposition family `asUntil?`, `asSince?`, `asSomeFuture?`, `asSomePast?`, `asAllFuture?`, `asAllPast?` (port bimodal `as*?`, dropping `asDiamond?`); honor the Burgess `(event, guard)` convention and the `guard == ⊤` filter for generic-until-from-someFuture.
- [ ] Define the fuel measure `soundFuel φ` seeded from `Formula.complexity` (and/or `subformulaCount`).

**Timing**: ~2 hours (~250 lines)

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Defs.lean` — new
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — add `Hashable` instance only (if not better placed in Defs.lean per ORGANISATION.md; prefer Defs.lean to avoid touching Syntax)

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Defs`
- `lake exe lint-style` and `lake shake --add-public --keep-implied --keep-prefix` clean for the new file.
- Decomposition functions reduce as expected on small sample formulas (`#eval`/example checks).

---

### Phase 2: TimeOrdering.lean — strict-before constraint store [COMPLETED]

**Goal**: Port the bimodal `TimeOrdering` (dropping the world coordinate) — the standalone strict-before store threaded through the rules.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean`; define `structure TimeOrdering where constraints : List (Nat × Nat)` (`(a,b)` means `a < b`).
- [ ] Port API: `empty`, `addFuture t t_new` (adds `(t, t_new)`), `addPast t t_new` (adds `(t_new, t)`), `futureOf t`, `pastOf t`, `timeCount`, `ancestorTimes t fuel` (fuelled transitive closure).
- [ ] Prove basic lemmas: membership after `addFuture`/`addPast`, `futureOf`/`pastOf` characterization, monotonicity of `timeCount`.
- [ ] Decide and document direct-successor vs transitive-closure semantics (default: direct-successor, matching ported `branchTruth`); leave a clearly-marked hook if Phase 8 needs closure.

**Timing**: ~1.5 hours (~150 lines)

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` — new

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.TimeOrdering`; `lint-style` + `shake` clean.
- Lemma examples confirm `addFuture`/`futureOf` round-trips.

---

### Phase 3: Rules.lean — temporalApplyOne (propositional, G/H/F/P, until/since, frame-class) [COMPLETED]

**Goal**: Implement `temporalApplyOne : SignedFormula → Branch → TimeOrdering → RuleResult × TimeOrdering` — the procedural core, including the highest-risk until/since branching. (Modal `modalApplyOne` pair signature is the structural template.)

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Tableau/Rules.lean`.
- [ ] Propositional rules via `tryAllPropRules` wired to the Phase-1 `temp*Of?` functions (all preserve the input time-label — no new time point).
- [ ] G/H/F/P rules: universal (G/H, `allFuture`/`allPast`) as `.persistent` (propagate only along recorded `TimeOrdering` successors/predecessors); existential (F/P, `someFuture`/`somePast`) as `.linear` (fresh time + `addFuture`/`addPast` + propagate existing universals).
- [ ] Until/since event-witness/guard-continue branching: port `untlPos` (`Tableau.lean:688`) and `sncePos` (`Tableau.lean:732`), retyped; drop box/diamond auto-propagation, keep G/H/F/P-universal + U/S-negative propagation to the fresh time.
- [ ] Reynolds co-decomposition: port `untlNeg` (`Tableau.lean:774`) and `snceNeg` (`Tableau.lean:836`) as `.persistent` over `futureOf`/`pastOf`, re-including the source on both branches, with the `0 < timeCount < 4` gated future-creation.
- [ ] Frame-class rules gated by `decide (FrameClass.X ≤ fc)` and assembled `allRulesForFC fc`: `denseIndicatorClosure` (`T(U(⊤,⊥))` closes, `fc ≥ .Dense`), `densityRule` (insert intermediate `t''` with `t < t'' < t'`, `fc ≥ .Dense`), `priorUZ`/`priorSZ` (`fc ≥ .Discrete`), `z1Rule` (`fc ≥ .Discrete`).
- [ ] Use `swapTemporal` duality where it halves past-mirror code.

**Timing**: ~3.5 hours (~400 lines). High risk — the core.

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Rules.lean` — new

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Rules`; `lint-style` + `shake` clean.
- `#eval`/example: `temporalApplyOne` on `T(U(event,guard))` produces the two-branch result with correct fresh time and `TimeOrdering` update; frame-class gates fire only at the right `fc`.

---

### Phase 4: Branch.lean — collectors, Eventuality tracking, blocking [COMPLETED]

**Goal**: Temporal `Branch` collectors plus the eventuality-tracking and time-blocking machinery that termination and the new closure mode depend on.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Tableau/Branch.lean` (reuse Foundations `Branch F L` API directly: `contains`, `extend`, `extendMany`, `positives/negatives`, `hasPosAt/hasNegAt`, `formulasAt`, `labels`, `findContradiction`, `hasContradiction`, `hasBotPos`).
- [ ] Port `Eventuality` / `EventualityTracker` (`SignedFormula.lean:585–635`) retyped to temporal: track unfulfilled positive `until`/`since` eventualities per time.
- [ ] Port `Branch.timeType`, `isSubsetBlocked`, `isTemporallyBlocked`, `findBlockedTime` (`SignedFormula.lean:645–784`) — the time-subset blocking device.
- [ ] Provide fresh-time generator + freshness lemma (imitate Modal `modalNextWorld` / `modalNextWorld_gt`, retyped to time).

**Timing**: ~2.5 hours (~250 lines). Medium risk.

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Branch.lean` — new

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Branch`; `lint-style` + `shake` clean.
- Examples: `isSubsetBlocked` detects a looping time; `EventualityTracker` records/clears a fulfilled `until`.

---

### Phase 5: Closure.lean — classical + eventuality-defect closure, monotonicity [COMPLETED]

**Goal**: Closure conditions = Foundations `ClassicalClosure` (`T(⊥)` + same-label `T(φ)/F(φ)`) **extended with the genuinely new eventuality-defect closure**, plus the monotonicity suite the soundness loop invariant needs.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Tableau/Closure.lean`; alias Foundations `ClassicalClosure` for `T(⊥)`/contradiction (as Modal `Closure.lean` does).
- [ ] Define **eventuality-defect closure**: a saturated, time-subset-blocked branch with an unfulfilled positive `until`/`since` eventuality closes. Extend `ClosureReason`/`ClosureCondition` accordingly (Foundations does not model this).
- [ ] Prove the `*_mono` monotonicity suite, `closed_extend_closed`, `add_neg_causes_closure` (follow Propositional Classical / bimodal templates).

**Timing**: ~2 hours (~200 lines). Medium risk — eventuality-defect is the new mode.

**Depends on**: 1, 4

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Closure.lean` — new

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Closure`; `lint-style` + `shake` clean.
- Examples: classical contradiction closes; an unfulfilled-eventuality blocked branch closes; a fulfilled one does not.

---

### Phase 6: Saturation.lean — worklist, fuel, blocking, Hintikka, subformula property [COMPLETED]

**Goal**: Drive `temporalApplyOne` to a fixpoint with terminating fuel and time-subset blocking, build the Hintikka set, and prove the subformula property — establishing termination/blocking soundness.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Tableau/Saturation.lean` (imitate `Modal/Tableau/Saturation.lean`).
- [ ] Define `stepBranch` / `expandBranches` / `buildTableau` worklist with result type `closed | openBranch branch timeOrd`; `persistent` results keep the source `sf` off the expanded set so it re-fires (mirror Modal `Saturation.lean:117`).
- [ ] Fuel `= soundFuel φ` (Phase 1); incorporate time-subset blocking + eventuality fulfilment as the termination device.
- [ ] Define `temporalHintikkaSet`.
- [ ] Prove `subformula_property` using the existing temporal `Subformulas` lemmas (`untl_left/right_mem_subformulas`, `snce_left/right_mem_subformulas`, `subformulas_trans`, `self_mem_subformulas`).
- [ ] Prove `expandBranch_sound` (port bimodal `expandBranchWithFuel_sound` template).

**Timing**: ~3 hours (~350 lines). High risk — termination + blocking soundness.

**Depends on**: 3, 4, 5

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` — new

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Saturation`; `lint-style` + `shake` clean.
- `subformula_property` and `expandBranch_sound` build sorry-free; `buildTableau` terminates on sample formulas.

---

### Phase 7: Soundness.lean — per-rule preservation, frame-class soundness, main theorem [BLOCKED]

**Goal**: Prove the tableau sound against `Satisfies`: closed ⇒ valid in the targeted frame class, including density/discreteness rule soundness. Follow the Propositional Classical soundness template.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Tableau/Soundness.lean`; define `branchConsistent`/`branchSatisfiable` against `TemporalModel`/`Satisfies`.
- [ ] Per-rule `*_preserves_sat` lemmas for propositional, G/H/F/P, and until/since rules (use the `@[simp]` `untl_iff`/`snce_iff`/`someFuture_iff`/`allFuture_iff` constructor lemmas).
- [ ] Frame-class rule soundness: `densityRule` sound over `DenselyOrdered D`; `priorUZ`/`priorSZ`/`z1Rule` sound over `SuccOrder D`/`PredOrder D`/`IsSuccArchimedean D`; `denseIndicatorClosure` sound (`¬U(⊤,⊥)` is a Dense axiom). Use `swapTemporal` duality to halve past-mirror lemmas.
- [ ] `classically_closed_unsatisfiable` (eventuality-defect-aware); loop invariant `expandBranches_closed_unsat` by fuel induction + inner list induction.
- [ ] Main `temporalTableau_sound : tableau = .closed → Valid(fc) φ`, connecting `FrameClass.Dense/Discrete` to `ValidDense/ValidDiscrete` and `FrameClass.Base` to `Valid`/`ValidSerial`.

**Timing**: ~3.5 hours (~350 lines). High risk — until/since + density/discreteness soundness.

**Depends on**: 3, 5, 6

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` — new

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Soundness`; `lint-style` + `shake` clean.
- `temporalTableau_sound` builds sorry-free; `lean_verify` confirms no new axioms in the soundness theorem's axiom set.

---

### Phase 8: Completeness.lean — model extraction, truth lemma, decidability [NOT STARTED]

**Goal**: Prove completeness (open ⇒ countermodel) and assemble the decision procedure: `extractModel`, the temporal truth lemma with until/since eventuality-fulfilment cases, and the `Decidable` instance. **Highest risk** — if a sorry-free completeness proof over genuine `DenselyOrdered`/discrete models proves intractable in scope, mark the task `[BLOCKED]` with a decomposition recommendation rather than deferring with sorry/axioms.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Tableau/Completeness.lean`; define `extractModel` building a `TemporalModel`/`Satisfies` over recorded time points (port bimodal `SemanticCountermodel`/`branchTruth`/`extractSemanticCountermodel` shape, retyped; not a flat valuation).
- [ ] Prove the `sat_*` saturation-invariant family with `*_not_expanded` companions for until/since/F/P (port `sat_untl_pos`/`untlPos_not_expanded`, `sat_untl_neg`, `sat_someFuture_neg`, `sat_snce_pos`, …).
- [ ] Prove `temporalTruthLemma` (`truthLemma_pos`/`truthLemma_neg`) by induction on φ — including the **until/since eventuality-fulfilment cases** (the single highest risk: an open saturated non-blocked branch yields a model where every positive `until` is genuinely satisfied, not deferred forever).
- [ ] Prove `openBranch_countermodel` and `temporalTableau_complete`.
- [ ] Assemble `temporalTableau_decides : closed ↔ Valid(fc)` and the `Decidable (Valid(fc) φ)` instance (follow Propositional Classical `*_decides` + `instDecidableTautology`).
- [ ] Resolve the `TimeOrdering` direct-successor vs transitive-closure question concretely here; document the decision.
- [ ] **Zero-debt gate**: if completeness cannot be closed sorry-free within scope, do **not** add sorry/axioms — record the precise blocking sub-goal and recommend `[BLOCKED]` + plan decomposition.

**Timing**: ~4 hours (~400 lines). Highest risk.

**Depends on**: 6, 7

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — new

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness`; `lint-style` + `shake` clean.
- `temporalTableau_complete`, `temporalTableau_decides`, and the `Decidable` instance build sorry-free; `lean_verify` confirms no new axioms.
- Full pipeline: `lake build`, `lake test`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` all green.

---

## Testing & Validation

- [ ] Per phase: `lake build <module>`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` clean for the new file.
- [ ] Final: full `lake build` of the whole `Cslib.Logics.Temporal.Tableau.*` namespace.
- [ ] `lake test` (CslibTests suite) green.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lean_verify` on `temporalTableau_sound`, `temporalTableau_complete`, `temporalTableau_decides` confirms **no new axioms** and no `sorry`.
- [ ] `grep -rn "sorry\|admit\|axiom" Cslib/Logics/Temporal/Tableau/` returns nothing (zero-debt confirmation).
- [ ] Sample decidability checks: a known valid temporal formula reports closed; a known invalid one reports an open countermodel; frame-class-specific validities (dense/discrete) discriminate correctly.

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Tableau/Defs.lean` (~250 ln)
- `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` (~150 ln)
- `Cslib/Logics/Temporal/Tableau/Rules.lean` (~400 ln)
- `Cslib/Logics/Temporal/Tableau/Branch.lean` (~250 ln)
- `Cslib/Logics/Temporal/Tableau/Closure.lean` (~200 ln)
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` (~350 ln)
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` (~350 ln)
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` (~400 ln)
- Possible 1-line addition: `Hashable (Formula Atom)` instance (preferably in Defs.lean).
- Execution summary at `specs/301_temporal_tableau/summaries/01_*-summary.md` (at /implement time).

## Rollback/Contingency

- All work is additive (new files under a new directory `Cslib/Logics/Temporal/Tableau/`). Rollback = delete the directory and any `Hashable` instance addition; nothing existing is overwritten.
- Phases are committed incrementally (`task 301 phase {P}: {file}`), so a failing phase reverts only its own file.
- **Zero-debt contingency**: if Phase 8 completeness (or any obligation) cannot be closed sorry-free within scope, leave the foundational/soundness phases committed and green, do **not** introduce sorry/axioms, and mark the task `[BLOCKED]` with the precise blocking sub-goal and a recommended decomposition (e.g., split completeness into Base-class first, dense/discrete later) for user review.
