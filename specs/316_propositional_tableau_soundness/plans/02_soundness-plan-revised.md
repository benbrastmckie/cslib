# Implementation Plan: Task #316 - Propositional Tableau Soundness (Revised)

- **Task**: 316 - Fill sorry instances in propositional tableau soundness proofs
- **Status**: [IMPLEMENTING]
- **Effort**: 10 hours
- **Dependencies**: None
- **Research Inputs**:
  - specs/316_propositional_tableau_soundness/reports/01_soundness-research.md
  - specs/316_propositional_tableau_soundness/reports/03_blocker-solutions.md
- **Artifacts**: plans/02_soundness-plan-revised.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Revised plan for filling the remaining sorry instances in the propositional tableau soundness
proofs. The previous implementation attempt completed Phases 1-2 (closure unsatisfiability and
rule preservation lemmas, 3 of 6 in-scope sorry resolved) but stalled on Phase 3 (classical
main theorem) and Phase 4 (intuitionistic/minimal main theorems) due to three structural
blockers. The blocker research (report 03) provides concrete, verified solutions for all three.

This revision reorders the remaining work to prioritize fixing 9 build errors in the classical
file (the proof structure is already correct), then addresses the `intRule_preserves_sat_ext`
refactoring (B2) and persistence fixpoint lemma (B3) before tackling the intuitionistic/minimal
main theorems (B1).

### Research Integration

- **Report 01** (01_soundness-research.md): Initial sorry inventory, type signatures, proof
  strategies, blocker identification. Integrated in plan v01.
- **Report 03** (03_blocker-solutions.md): Concrete solutions for B1 (loop induction pattern),
  B2 (existential worldOf extension), B3 (persistence fixpoint). Integrated in this revision.

**reports_integrated**: [01_soundness-research.md, 03_blocker-solutions.md]

### Prior Plan Reference

Plan v01 (01_soundness-plan.md): 4 phases, 8 hours. Phases 1-2 completed. Phase 3 in progress
with 9 build errors. Phase 4 not started. This revision replaces Phases 3-4 with three new
phases (3-5) incorporating blocker solutions.

### Roadmap Alignment

This task advances the "Logics/Propositional" module within the CSLib roadmap, specifically
the tableau-based decision procedures for propositional logics. Filling soundness sorries
enables sorry-free `Decidable` instances that depend on soundness via `minimalTableau_decides`.

## Goals & Non-Goals

**Goals**:
- Fix 9 build errors in Classical/Soundness.lean (proof structure correct, tactics need updating)
- Refactor `intRule_preserves_sat` to `intRule_preserves_sat_ext` with existential worldOf for F(imp)
- Prove `applyPersistenceFixpoint_preserves_sat` supporting lemma
- Prove `intExpandBranches_closed_unsat` loop invariant following the classical pattern
- Fill S3 (classicalTableau_sound), S6 (intuitionisticTableau_sound), S7 (minimalTableau_sound)
- All proofs compile without sorry and pass `lean_verify` axiom check

**Non-Goals**:
- Filling S8 (`minimalTableau_complete`) -- belongs to task 317
- Refactoring the expansion loop structure or closure instances
- Adding new simp lemmas to upstream files (use existing API only)
- Performance optimization of the proofs

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Classical build errors cascade beyond the 4 identified fix sites | M | L | The blocker research identified specific root causes at lines 522, 586, 566-581, 644-647; cascading errors resolve once roots are fixed |
| `Function.update` breaks order-preservation for persistence fixpoint | M | M | Weaken `h_order` to only require order-preservation on labels appearing on the current branch; `applyPersistenceFixpoint` only adds formulas at existing labels |
| `intExpandBranches.go` does not unfold as cleanly as `processNext` | M | L | Classical case demonstrates `let rec` unfolding works; if `go` differs, extract to top-level definition |
| Three-list length invariant for intExpandBranches adds proof burden | M | M | Use the alternative contrapositive formulation that universally quantifies over models, absorbing worldOf construction |
| Persistence fixpoint requires worldOf ordering after Function.update | M | M | After update, all branch labels < nw agree with original worldOf; for nw itself, worldOf label <= w' from IForces_imp witness |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 2 |
| 5 | 5 | 3, 4 |

Phases within the same wave can execute in parallel. Note that Phases 3 and 4 are independent
and could execute in parallel (Wave 3-4), though in practice they will likely run sequentially.

---

### Phase 1: Closure Unsatisfiability Lemmas (S2, S5, + helper for S7) [COMPLETED]

**Goal**: Prove that closed branches are unsatisfiable under the appropriate semantics for
all three logics.

**Tasks**:
- [x] Prove S2: `classically_closed_unsatisfiable` in `Classical/Soundness.lean`
- [x] Prove S5: `intClosed_unsatisfiable` in `Intuitionistic/Soundness.lean`
- [x] Add and prove `minClosed_unsatisfiable` helper in `Minimal/DecisionProcedure.lean`

**Timing**: 1.5 hours

**Depends on**: none

**Files modified**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`

**Completed**: 2026-06-23

---

### Phase 2: Rule Preservation Lemmas (S1, S4) [COMPLETED]

**Goal**: Prove that each tableau rule application preserves branch satisfiability. S4
(`intRule_preserves_sat`) was proved for all cases except F(imp), which was left with sorry
pending the B2 resolution in Phase 4.

**Tasks**:
- [x] Prove S1: `classicalRule_preserves_sat` in `Classical/Soundness.lean`
- [x] Prove S4: `intRule_preserves_sat` in `Intuitionistic/Soundness.lean` (partial -- F(imp) sorry remains)

**Timing**: 2.5 hours

**Depends on**: 1

**Files modified**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`

**Completed**: 2026-06-23

---

### Phase 3: Fix Classical Build Errors and Complete S3 [COMPLETED]

**Goal**: Fix the 9 build errors in Classical/Soundness.lean so the existing proof structure
compiles. The proof for `classicalExpandBranches_closed_unsat` (loop invariant) and
`classicalTableau_sound` (S3) already has the correct structure (outer fuel induction +
suffices + inner pending-list induction); only tactical adjustments are needed for the
current Lean 4 / Mathlib API.

**Tasks**:
- [ ] Fix line 522: Remove `simp only at hsfeq` in `classicalStepBranch_preserves_sat` (the
  hypothesis already has the right form for `split_ifs at hsfeq`; the simp is a no-op that errors)
- [ ] Fix line 586: Correct `induction pending generalizing with` syntax in
  `classicalExpandBranches_closed_unsat`. In current Lean 4.31.0, either drop `generalizing`
  and generalize in the `intro` step, or provide explicit variable names
- [ ] Fix lines 566-581: These are cascading type mismatches from the above two errors. After
  fixing lines 522 and 586, verify these resolve automatically. If not, adjust the induction
  body to match current API types
- [ ] Fix lines 644-647: Adjust argument order/types in the `classicalExpandBranches_closed_unsat`
  application within `classicalTableau_sound`. The length invariant `List.length [[]] = List.length [_]`
  should be provable by `rfl`; check argument position matches the updated lemma signature
- [ ] Run `lean_diagnostic_messages` on Classical/Soundness.lean to confirm 0 errors
- [ ] Run `lean_verify` on `classicalExpandBranches_closed_unsat` and `classicalTableau_sound`

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`

**Verification**:
- `lean_diagnostic_messages` on Classical/Soundness.lean: 0 errors
- `lean_verify classicalExpandBranches_closed_unsat`: no sorry, no exotic axioms
- `lean_verify classicalTableau_sound`: no sorry, no exotic axioms
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness`

---

### Phase 4: intRule_preserves_sat_ext Refactoring + Persistence Fixpoint (B2, B3) [IN PROGRESS]

**Goal**: Replace `intRule_preserves_sat` with `intRule_preserves_sat_ext` that returns
`exists worldOf'` for the F(imp) case, and prove `applyPersistenceFixpoint_preserves_sat`.
These are the two supporting lemmas needed by the intuitionistic loop invariant in Phase 5.

**Tasks**:
- [ ] Define `intRule_preserves_sat_ext` with the new signature:
  ```
  match intApplyRuleFull sf nw b with
  | .linearResult newForms _ =>
    exists worldOf' : Nat -> World,
      (forall n, n < nw -> worldOf' n = worldOf n) /\
      intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms)
  | .branchingResult branches _ =>
    exists br in branches,
      intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
  | .notApplicable => True
  ```
  Additional parameters: `v_uc` (valuation upward-closed), `bf_uc` (botForces upward-closed),
  `h_fresh` (all existing labels < nw)
- [ ] Adapt existing proved cases (T(and), F(and), T(or), F(or)) to wrap in `exists worldOf'`:
  for non-world-creating `.linearResult` cases, witness `worldOf' = worldOf` with
  `fun n _ => rfl` for the agreement proof
- [ ] Prove the F(imp) case:
  1. Extract witness from `not IForces(phi -> psi)` via `IForces_imp` + `push_neg`:
     obtain `w'` with `worldOf label <= w'`, `IForces val bf w' phi`, `not IForces val bf w' psi`
  2. Define `worldOf' = Function.update worldOf nw w'`
  3. Agreement: `Function.update_of_ne` for `n < nw`
  4. New formulas at label `nw`: `Function.update_self` gives `worldOf' nw = w'`;
     T(phi) satisfied by `hphi`, F(psi) satisfied by `hpsi`
  5. Propagated T(alpha) at nw: from `hsat` get `IForces val bf (worldOf label) alpha`;
     by `hw_le` and `iforces_persistence`, `IForces val bf w' alpha`
  6. Old formulas: `sf'.label < nw` so `worldOf' sf'.label = worldOf sf'.label`; use `hsat`
- [ ] Remove or deprecate the old `intRule_preserves_sat` (or keep as a corollary for non-F(imp) cases)
- [ ] Prove `applyAllTImpRules_preserves_sat`:
  - `applyAllTImpRules b = b ++ newForms.flatten`
  - For each new `T(psi) at w'`: there exists `T(phi -> psi) at w` on `b` with `w <= w'` and
    `T(phi) at w'` on `b`
  - From `hsat`: `IForces val bf (worldOf w) (phi -> psi)` gives
    `forall u, worldOf w <= u -> IForces ... u phi -> IForces ... u psi`
  - From `h_order`: `w <= w'` implies `worldOf w <= worldOf w'`
  - Instantiate to get `IForces val bf (worldOf w') psi`
- [ ] Prove `applyPersistenceFixpoint_preserves_sat`:
  - By induction on fuel parameter
  - Base case: identity (no rules applied)
  - Inductive step: `applyAllTImpRules_preserves_sat` + IH
  - Requires `h_order : forall w1 w2 : Nat, w1 <= w2 -> worldOf w1 <= worldOf w2`
  - After `Function.update` from B2: order-preservation holds because all branch labels < nw
    agree with original `worldOf`, and `worldOf label <= w'` ensures the nw case is ordered
- [ ] Run `lean_verify` on all new lemmas

**Timing**: 3 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`

**Verification**:
- `lean_goal` at each case split to verify all subcases covered
- `lean_verify intRule_preserves_sat_ext`: no sorry, no exotic axioms
- `lean_verify applyPersistenceFixpoint_preserves_sat`: no sorry, no exotic axioms
- `lean_diagnostic_messages` on Intuitionistic/Soundness.lean: 0 errors (except remaining sorry in S6)

---

### Phase 5: Intuitionistic and Minimal Main Theorems (S6, S7) [IN PROGRESS]

**Goal**: Prove `intuitionisticTableau_sound` (S6) and `minimalTableau_sound` (S7) using the
loop invariant pattern validated in the classical case, the `intRule_preserves_sat_ext` from
Phase 4, and the `applyPersistenceFixpoint_preserves_sat` from Phase 4.

**Tasks**:
- [ ] Prove `intExpandBranches_closed_unsat` loop invariant following the classical pattern:
  - Outer induction on `fuel`
  - Zero case: all branches closed by `closurePred` -> use `h_closed_unsat` parameter
  - Succ case: `suffices` for inner lemma about `intExpandBranches.go`
    (accessible as `intExpandBranches.go`, same pattern as `classicalExpandBranches.processNext`)
  - Inner induction on pending list
  - Closed branch: `h_closed_unsat` -> contradiction with satisfiability
  - Saturated: returns `.openBranch` -> contradiction with `.closed`
  - Rule fires: use `intRule_preserves_sat_ext` to get `worldOf'`, then
    `applyPersistenceFixpoint_preserves_sat` to show persistence preserves satisfaction,
    then apply IH with updated `worldOf'`
  - State the invariant in contrapositive form with universal quantification over models
    to absorb worldOf updates:
    ```
    forall (branches ...) (worldOf : Nat -> World),
      intExpandBranches ... = .closed ->
      forall b in branches, not intBranchSatisfied val botForces worldOf b
    ```
  - Thread three length invariants (`expandedSets.length = branches.length`,
    `nextWorlds.length = branches.length`) and label freshness invariant
- [ ] Prove S6: `intuitionisticTableau_sound`
  - Contrapositive: assume `not IValid phi`
  - Obtain Kripke model (World, Preorder, val, w0) with `not IForces val (fun _ => False) w0 phi`
  - Initial branch `[F(phi) at 0]` is satisfied with `worldOf 0 = w0` and `botForces = fun _ => False`
  - Apply `intExpandBranches_closed_unsat` with `closurePred = isIntuitionisticallyClosed`,
    `h_closed_unsat = intClosed_unsatisfiable` (Phase 1)
  - Result: `intExpandBranches` does not return `.closed` -> contradicts hypothesis
- [ ] Prove S7: `minimalTableau_sound`
  - Same structure as S6 but with `MValid` (universal over `botForces`) and
    `closurePred = isMinimallyClosed`, `h_closed_unsat = minClosed_unsatisfiable` (Phase 1)
  - The expansion loop is the same `intExpandBranches` parameterized by `closurePred`,
    so `intExpandBranches_closed_unsat` serves both S6 and S7
  - Rule preservation: `intRule_preserves_sat_ext` works for both intuitionistic and minimal
    since `intBranchSatisfied` has the same structure (same `intApplyRuleFull` rules)
  - If `minBranchSatisfied` differs from `intBranchSatisfied`: prove a parallel
    `minRule_preserves_sat_ext` (structurally identical) or verify they share definitions
- [ ] Run full verification suite

**Timing**: 3 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (loop invariant + S6)
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (S7)

**Verification**:
- `lean_verify intuitionisticTableau_sound`: no sorry, no exotic axioms
- `lean_verify minimalTableau_sound`: no sorry, no exotic axioms
- `lean_diagnostic_messages` on Intuitionistic/Soundness.lean: 0 errors
- `lean_diagnostic_messages` on Minimal/DecisionProcedure.lean: only S8 sorry remains
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure`
- Confirm `instDecidableMValid` and `instDecidableDerivableMinPropAxiom` still compile

---

## Testing & Validation

- [ ] All 7 soundness-direction sorry instances (S1-S7) replaced with complete proofs
- [ ] `lean_verify` passes for each lemma/theorem with no sorry and no exotic axioms
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness` succeeds
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` succeeds
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` succeeds
- [ ] S8 (`minimalTableau_complete`) remains as sorry (task 317 scope)
- [ ] `Decidable` instances in `Minimal/DecisionProcedure.lean` still compile
- [ ] `lake test` passes (no regression)
- [ ] No new sorry introduced in any file

## Artifacts & Outputs

- `specs/316_propositional_tableau_soundness/plans/02_soundness-plan-revised.md` (this file)
- Modified files:
  - `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` (build error fixes for S3 + loop invariant)
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (intRule_preserves_sat_ext + persistence fixpoint + loop invariant + S6)
  - `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (S7 + optional minRule_preserves_sat_ext)

## Rollback/Contingency

If Phase 3 (classical build fixes) reveals that the proof structure is fundamentally wrong
(not just tactical mismatches):
1. Rewrite `classicalExpandBranches_closed_unsat` from scratch using the pattern from the
   blocker research (report 03, lines 73-97)
2. Use `Nat.rec` / `Nat.strongRecOn` if structural induction on fuel fails

If Phase 4 (intRule_preserves_sat_ext) F(imp) case encounters unexpected difficulties with
`Function.update` and `iforces_persistence`:
1. Try `Function.update_apply` with `if-then-else` splitting instead of `Function.update_of_ne`
2. If the propagated T-formulas case is too complex, split the F(imp) proof into sub-lemmas
   for each formula type in the propagation

If Phase 5 (loop invariant) has issues with the three-list length invariant:
1. Use a combined record type for the three parallel lists
2. Prove a weaker invariant that does not require exact length matching (the expansion loop
   has a fallback for mismatched lengths)
3. Alternatively, prove the invariant for a single branch at a time and lift to the list level

If `intExpandBranches.go` does not unfold cleanly:
1. Check if `simp [intExpandBranches]` unfolds the fuel match (as `simpa [classicalExpandBranches]` does)
2. If `go` is not accessible as `intExpandBranches.go`, extract it as a top-level definition
