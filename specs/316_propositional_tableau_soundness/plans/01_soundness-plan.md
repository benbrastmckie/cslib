# Implementation Plan: Task #316 - Propositional Tableau Soundness

- **Task**: 316 - Fill sorry instances in propositional tableau soundness proofs
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None
- **Research Inputs**: specs/316_propositional_tableau_soundness/reports/01_soundness-research.md
- **Artifacts**: plans/01_soundness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Fill the 7 sorry instances (S1-S7) across three propositional tableau soundness files in
CSLib. S8 (minimalTableau_complete) is excluded as it belongs to task 317 (completeness).
The work decomposes into four phases following dependency order: closure unsatisfiability
lemmas first (simplest, no dependencies), then rule preservation lemmas (depend on semantic
unfolding), then main theorems (depend on both closure and preservation lemmas via loop
invariant induction on fuel).

### Research Integration

The research report identified 8 sorry instances (S1-S8) with exact line numbers and goal
states. It recommended starting with closure unsatisfiability (S2, S5) as simplest, then
rule preservation (S1, S4), then main theorems (S3, S6, S7). Two blockers were identified:
B1 (F(imp) worldOf issue in S4) and B2 (fuel-based loop induction in S3/S6/S7). This plan
adopts the research ordering and addresses both blockers with concrete resolution strategies.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the "Logics/Propositional" module within the CSLib roadmap, specifically
the tableau-based decision procedures for propositional logics. Filling soundness sorries
enables sorry-free `Decidable` instances that depend on soundness via `minimalTableau_decides`.

## Goals & Non-Goals

**Goals**:
- Fill all 7 soundness-direction sorry instances (S1-S7) across the three files
- Each proof compiles without sorry and passes `lean_verify` axiom check
- Build succeeds: `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness`,
  `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`,
  `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure`
- Add any necessary helper lemmas (e.g., `minClosed_unsatisfiable` for S7)

**Non-Goals**:
- Filling S8 (`minimalTableau_complete`) -- belongs to task 317
- Refactoring the expansion loop structure or closure instances
- Adding new simp lemmas to upstream files (use existing API only)
- Performance optimization of the proofs

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| B1: F(imp) worldOf mismatch in S4 | H | M | Restructure S4 to return existential over worldOf, or fold F(imp) argument directly into S6 |
| B2: let-rec processNext/go blocks induction | H | H | Extract loop invariant as separate lemma; induct on fuel with nested list induction for inner loop |
| tryAllPropRules unfolds into 8-element List.find? | M | M | Pre-prove @[simp] lemmas for classicalApplyOne on each sign/formula case, or use native_decide |
| Intuitionistic persistence adds proof complexity | M | L | iforces_persistence is already proven; use it directly in S4 for world-creating case |
| MValid universal quantification over botForces | M | M | S7 needs separate minClosed_unsatisfiable helper accounting for arbitrary botForces |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Closure Unsatisfiability Lemmas (S2, S5, + new helper for S7) [COMPLETED]


**Goal**: Prove that closed branches are unsatisfiable under the appropriate semantics for
all three logics. These are the simplest proofs (pure case analysis on closure conditions)
and have no dependencies on other sorry instances.

**Tasks**:
- [ ] Prove S2: `classically_closed_unsatisfiable` in `Classical/Soundness.lean` (line 100)
  - Unfold `isClassicallyClosed` -> `ClosureCondition.isClosed` -> `findClosure`
  - Case split on closure reason: `.botPos` (T(bot) present) or `.contradiction` (T(phi)/F(phi) pair)
  - For botPos: extract sf with `sf.isPos && sf.formula == bot`; derive `BoolEvaluate v bot = true` from `branchConsistent`; contradict with `BoolEvaluate_bot` (@[simp]: bot = false)
  - For contradiction: extract T(phi) and F(phi); `branchConsistent` forces `BoolEvaluate v phi = true` AND `= false`; contradiction
  - Key API: `List.find?_some`, `Bool.and_eq_true`, `BoolEvaluate_bot`, `List.findContradiction` semantics
- [ ] Prove S5: `intClosed_unsatisfiable` in `Intuitionistic/Soundness.lean` (line 112)
  - Unfold `isIntuitionisticallyClosed` -> only checks for T(bot)
  - Extract sf with `sf.isPos && sf.formula == bot`; from `intBranchSatisfied` with `botForces = fun _ => False`, the pos case gives `IForces val (fun _ => False) (worldOf sf.label) bot`
  - But `IForces val (fun _ => False) w bot = (fun _ => False) w = False` by `IForces_bot` (@[simp])
  - Key API: `IForces_bot`, `List.find?_some`
- [ ] Add and prove `minClosed_unsatisfiable` helper in `Minimal/DecisionProcedure.lean`
  - Needed for S7; not currently stated in the file
  - Statement: given `isMinimallyClosed b = true`, show `¬ minBranchSatisfied val botForces worldOf b`
  - MinimalClosure finds T(atom p) and F(atom p) at same label; from `minBranchSatisfied`, the T case gives `IForces val botForces (worldOf l) (atom p) = val (worldOf l) p` and F case gives `¬ val (worldOf l) p`; contradiction
  - Key API: `IForces` on `.atom`, `List.findSome?`, `Bool.and_eq_true`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - fill S2 sorry
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - fill S5 sorry
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - add + prove minClosed_unsatisfiable

**Verification**:
- `lean_verify` on each lemma (no sorry, no exotic axioms)
- `lean_goal` after each proof to confirm no remaining goals
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness`
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`

---

### Phase 2: Rule Preservation Lemmas (S1, S4) [COMPLETED]

**Goal**: Prove that each tableau rule application preserves branch satisfiability. These
are moderate-difficulty proofs requiring case analysis on all formula/sign combinations.

**Tasks**:
- [ ] Prove S1: `classicalRule_preserves_sat` in `Classical/Soundness.lean` (line 92)
  - Case split on `sf.sign` (pos/neg) then `sf.formula` (atom/bot/imp/and/or) = 10 subcases
  - For atom/bot cases: `classicalApplyOne` returns `.notApplicable`, goal becomes `True`, use `trivial`
  - For alpha-rule cases (e.g., T(and)): same valuation `v` works; `BoolEvaluate v (and a b) = true` implies `BoolEvaluate v a = true` and `BoolEvaluate v b = true`; membership in extended branch via `List.mem_append`
  - For beta-rule cases (e.g., F(and)): `BoolEvaluate v (and a b) = false` implies `BoolEvaluate v a = false` OR `BoolEvaluate v b = false`; pick the satisfiable branch via `Exists.intro`
  - Potential issue: `tryAllPropRules` unfolding through List.find? on 8 rules; may need to unfold `applyPropRule`, `propAndOf?`, etc., or prove simp lemmas for `classicalApplyOne` per case
  - Strategy: `cases sf.sign <;> cases sf.formula <;> simp [classicalApplyOne, tryAllPropRules, ...]`; then handle each remaining goal
- [ ] Prove S4: `intRule_preserves_sat` in `Intuitionistic/Soundness.lean` (line 99)
  - Case split on `sf.sign` and `sf.formula`; `intApplyRuleFull` is a direct pattern match (easier to unfold than `tryAllPropRules`)
  - Standard cases (T(and), F(and), T(or), F(or)): parallel to classical but using `IForces` instead of `BoolEvaluate`; use `IForces_and`, `IForces_or` simp lemmas
  - F(imp) world-creating case (Blocker B1):
    - The lemma requires the *same* `worldOf` to work for the extended branch
    - Resolution strategy: If the existing `worldOf nw` happens to be the needed witness world, the proof works. If not, the lemma as stated may be too strong.
    - Fallback: If S4 cannot be proven as stated for the F(imp) case, restructure the proof to fold the F(imp) argument directly into S6 (the main theorem), where model construction gives control over `worldOf`. Leave S4 with a restricted version that handles all cases except F(imp), and mark F(imp) as handled in S6.
    - Alternative: Check if the lemma statement can be weakened to existentially quantify over `worldOf'` in the conclusion for the F(imp) case
  - T(imp) persistent case: `intApplyRuleFull` returns `.notApplicable` for T(imp) (persistence is handled separately in the expansion loop via `applyPersistenceFixpoint`), so this case falls through to `True`
  - Key API: `IForces_and`, `IForces_or`, `IForces_imp`, `IForces_bot`, `iforces_persistence`, `List.mem_append`

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - fill S1 sorry
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - fill S4 sorry

**Verification**:
- `lean_goal` at each case split to verify all subcases are covered
- `lean_multi_attempt` for testing tactic combinations on specific subcases
- `lean_verify` on completed lemmas
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness`
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`

---

### Phase 3: Classical Main Theorem (S3) [IN PROGRESS]

**Goal**: Prove `classicalTableau_sound`: if the classical tableau closes on phi, then phi
is a tautology. This is the hardest classical proof, requiring loop invariant induction over
the fuel-based `classicalExpandBranches` function.

**Tasks**:
- [ ] Design and prove the loop invariant lemma for `classicalExpandBranches`
  - Statement (contrapositive form): if some branch in `branches` is satisfiable, then `classicalExpandBranches branches expandedSets fuel` is not `.closed`
  - Proof by induction on `fuel`:
    - Base case (fuel = 0): satisfiable branch is not closed (by S2 / `classically_closed_unsatisfiable`), so `findSome?` finds it and returns `.openBranch`
    - Inductive step (fuel + 1): the `processNext` inner loop processes branches sequentially. Need a nested lemma about `processNext`: if any branch in `pending ++ done` is satisfiable, then `processNext` does not return `.closed`. Case analysis:
      - If current branch is closed: by S2, it cannot be satisfiable; the satisfiable branch is elsewhere, recurse on rest
      - If current branch is saturated (no rule applies): returns `.openBranch`, not `.closed`
      - If a rule applies: by S1, at least one sub-branch is satisfiable; the recursive call to `classicalExpandBranches` with `fuel'` returns non-closed by IH
  - Key challenge: `processNext` is defined via `let rec`, so direct induction is awkward. May need to:
    a. Extract processNext to a top-level definition for induction, OR
    b. Prove the invariant by well-founded induction on the combined fuel + pending list length, OR
    c. Use the approach: unfold processNext once, case-split, and use the fuel IH
- [ ] Prove S3: `classicalTableau_sound` using the loop invariant
  - Contrapositive: assume `¬ Tautology φ`
  - Obtain valuation `v` with `BoolEvaluate v φ = false` (via `tautology_iff_boolEvaluate_true` or direct unfolding)
  - The initial branch `[⟨.neg, φ, ()⟩]` is satisfiable: `v` is consistent since `sf.sign = .neg` and `BoolEvaluate v φ = false`
  - Apply the loop invariant: `classicalExpandBranches [initialBranch] [[]] fuel` is not `.closed`
  - This contradicts `h : classicalTableau φ = .closed`
  - Alternative approach: if contrapositive is awkward, try direct induction and show that if the result is `.closed`, every initial branch must be unsatisfiable

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - add loop invariant lemma + fill S3 sorry

**Verification**:
- `lean_goal` throughout the induction to track proof state
- `lean_verify Cslib.Logic.PL.classicalTableau_sound` -- no sorry, no exotic axioms
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness`

---

### Phase 4: Intuitionistic and Minimal Main Theorems (S6, S7) [NOT STARTED]

**Goal**: Prove `intuitionisticTableau_sound` and `minimalTableau_sound`. These share the
same expansion loop (`intExpandBranches`) but differ in closure predicate and semantic target.

**Tasks**:
- [ ] Design and prove the generic loop invariant for `intExpandBranches`
  - The `intExpandBranches` function is parameterized by `closurePred`, so a single invariant lemma can serve both intuitionistic and minimal logic
  - Statement: for any `closurePred`, if the semantics satisfy certain properties (rule preservation + closure unsatisfiability under that predicate), then: if some branch is "semantically satisfiable", `intExpandBranches` does not return `.closed`
  - This requires abstracting over the specific semantic relation; alternatively, prove separate but structurally identical invariants for each logic
  - The `go` inner loop has the same nested induction challenge as `processNext` in Phase 3
  - Additional complication: `applyPersistenceFixpoint` is applied before checking closure; must show it preserves satisfiability (persistence is sound for Kripke models)
- [ ] Prove S6: `intuitionisticTableau_sound` using the loop invariant
  - Contrapositive: assume `¬ IValid φ`
  - `IValid φ = ∀ World [Preorder] val v_uc w, IForces val (fun _ => False) w φ`
  - Negation gives a specific Kripke model (World, val, w0) with `¬ IForces val (fun _ => False) w0 φ`
  - Initial branch `[⟨.neg, φ, 0⟩]` is satisfied with `worldOf 0 = w0` and `botForces = fun _ => False`
  - Apply invariant: `intExpandBranches` does not return `.closed` (using S4 for rule preservation and S5 for closure unsatisfiability)
  - Contradicts `h : intuitionisticTableau φ = .closed`
  - F(imp) world-creation: if S4 was not fully proven for this case, handle it inline in the invariant proof where we control `worldOf`
- [ ] Prove S7: `minimalTableau_sound` using the same loop invariant (or a separate one)
  - Contrapositive: assume `¬ MValid φ`
  - `MValid φ = ∀ World [Preorder] val bot_forces v_uc bf_uc w, IForces val bot_forces w φ`
  - Negation gives a Kripke model with arbitrary `botForces` where φ fails
  - Initial branch `[⟨.neg, φ, 0⟩]` is satisfied under this model
  - Apply invariant with `closurePred = isMinimallyClosed` and `minClosed_unsatisfiable` from Phase 1
  - Need rule preservation for minimal logic: the rules are identical to intuitionistic (same `intApplyRuleFull`), and `minBranchSatisfied` has the same structure as `intBranchSatisfied`. Either reuse S4 (if proven generically) or prove a `minRule_preserves_sat` parallel lemma
  - If adding `minRule_preserves_sat`: it is nearly identical to S4 since `minBranchSatisfied = intBranchSatisfied` (same definition modulo name)

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - add loop invariant + fill S6 sorry
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - add rule preservation helper (if needed) + fill S7 sorry

**Verification**:
- `lean_verify Cslib.Logic.PL.intuitionisticTableau_sound` -- no sorry
- `lean_verify Cslib.Logic.PL.minimalTableau_sound` -- no sorry
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure`
- Confirm that `instDecidableMValid` and `instDecidableDerivableMinPropAxiom` still compile (they depend on S7 and S8; S8 remains sorry but the instances should still build)

---

## Testing & Validation

- [ ] All 7 sorry instances (S1-S7) replaced with complete proofs
- [ ] `lean_verify` passes for each lemma/theorem with no sorry and no exotic axioms
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness` succeeds
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` succeeds
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` succeeds
- [ ] S8 (`minimalTableau_complete`) remains as sorry (task 317 scope)
- [ ] `Decidable` instances in `Minimal/DecisionProcedure.lean` still compile
- [ ] `lake test` passes (no regression)

## Artifacts & Outputs

- `specs/316_propositional_tableau_soundness/plans/01_soundness-plan.md` (this file)
- Modified files:
  - `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` (S1, S2, S3 + loop invariant)
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (S4, S5, S6 + loop invariant)
  - `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (S7 + minClosed_unsatisfiable + optional minRule_preserves_sat)

## Rollback/Contingency

If the loop invariant approach (Phases 3-4) proves intractable due to `let rec` inner
functions blocking induction:
1. Try `Nat.rec` / `Nat.strongRecOn` instead of structural induction on fuel
2. If `processNext`/`go` cannot be reasoned about at all, consider adding a sorry-free
   wrapper that restates the loop as a top-level recursive function (requires modifying
   Expansion.lean, which is a non-goal but may be necessary)
3. As a last resort, leave S3/S6/S7 with sorry and document the blocker for future work

If B1 (worldOf mismatch in S4 F(imp) case) cannot be resolved:
1. Restructure S4 to skip the F(imp) case with a sorry
2. Handle F(imp) inline within S6's loop invariant proof where worldOf is under control
3. Document the API limitation for future refactoring of the lemma statement
