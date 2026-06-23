# Research Report: Task #266

**Task**: Research Propositional/ and Foundations/ Improvements
**Date**: 2026-06-22
**Mode**: Team Research (4 teammates)
**Session**: sess_1782181780_55aebb

## Summary

CSLib's `Propositional/` is structurally complete and sorry-free across all three logic tiers (MPL, IPL, CPL), with Hilbert systems, natural deduction, soundness, strong completeness, compactness, algebraic semantics, Kripke semantics, Glivenko's theorem, and conservativity results. The most actionable gaps are: (1) composing the existing Hilbert-ND bridge with algebraic completeness to produce Hilbert-tier corollaries, (2) fixing stale documentation in `ProofSystem.lean`, (3) adding propositional test coverage, and (4) building new proof systems (sequent calculus, tableau extraction) that would be firsts in the Lean 4 ecosystem.

## Key Findings

### 1. Propositional/ Is Sorry-Free and Substantively Complete

All four teammates independently confirmed: zero sorry declarations exist in `Cslib/Logics/Propositional/` or `Cslib/Foundations/Logic/`. The prior research (round 1) Gap 1 (`ipl_conservative_over_mpl` sorry) was resolved by Task 265. All three logic tiers have full Hilbert + ND + soundness + strong completeness + compactness + algebraic completeness. This is rare for a research library at CSLib's maturity level.

### 2. The Hilbert-Algebraic Completeness Bridge Is the Top Priority Gap

All four teammates identified this independently. `Algebra/Completeness.lean:28-32` explicitly defers Hilbert-level corollaries. The components exist:
- `hilbert_iff_nd_{min,int,cl}` (in `NaturalDeduction/Equivalence.lean`)
- `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical` (in `Algebra/Completeness.lean`)

Composing these produces:
- `Derivable MinPropAxiom φ ↔ GHAValid φ`
- `Derivable IntPropAxiom φ ↔ HAValid φ`
- `Derivable PropositionalAxiom φ ↔ BAValid φ`

**Estimated effort**: 50-100 lines, 1-2 days.

### 3. ProofSystem.lean Documentation Is Stale

`Foundations/Logic/ProofSystem.lean:50` says "derivation trees (not yet ported) and are future work." This is wrong — `Instances.lean` and `IntMinInstances.lean` already register full concrete instances for all three propositional tag types (`HilbertCl`, `HilbertInt`, `HilbertMin`). The comment misleads contributors.

### 4. No Sequent Calculus Exists for Propositional Logic

CSLib has Hilbert + ND but no Gentzen LK/LJ. The `LinearLogic/CLL/Basic.lean` provides a sequent calculus template (one-sided, `Multiset`-based). A propositional LK would use two-sided `Finset × Finset` sequents, compatible with the ND system's existing `Finset` contexts.

Key metatheoretic results a sequent calculus would enable:
- Cut elimination (Gentzen's Hauptsatz) — a fundamental consistency result
- Bridge to existing systems (`hilbert_iff_lk`, `nd_iff_lk`)
- Template for modal sequent systems (Fitting-style for K, S4, S5)

**Note**: Teammate C argued sequent calculus has no clear consumer and should be deprioritized. However, Teammates B and D make a strong case for community value — this would be a first in Lean 4. Resolution: include as a medium-priority item, not the top priority.

### 5. Modal/Temporal/Bimodal ProofSystem Tags Are Stubs

While propositional tags (`HilbertCl`, `HilbertInt`, `HilbertMin`) are fully instantiated, all 16 modal/temporal/bimodal tags remain empty stubs. Providing `Modal.HilbertK` instances would unlock `GenericMCS`'s free MCS infrastructure for modal completeness proofs, eliminating ~200-300 lines of custom MCS code per logic.

### 6. Zero Test Coverage for Propositional/

13 test files exist in `CslibTests/` but none covers `Cslib.Logics.Propositional.*`. `BoolEvaluate`, `Proposition.subst`, and `DerivationTree` all have computable functions that could be tested.

### 7. BimodalLogic Report 16 Is Strategically Irrelevant

The `16_witness-count-restructure.md` report concerns NF-depth vs. witness-count induction for temporal expressive completeness on Prior structures — a BimodalLogic-specific problem about first-order temporal model theory, not propositional proof systems. The "tableau" reference in the task description refers to the bimodal signed-formula tableau already ported to CSLib.

### 8. Propositional Tableau Rules Exist Inside the Bimodal Tableau

The 8 propositional tableau rules (andPos/Neg, orPos/Neg, impPos/Neg, negPos/Neg) are defined inside `Bimodal/Metalogic/Decidability/Tableau.lean` but not extracted to a standalone module. These could be factored up to `Foundations/Logic/` without new mathematics — just code reorganization.

### 9. `HasDia` Primitive Is Missing

`Foundations/Logic/Axioms.lean` encodes diamond classically as `◇φ = ¬□¬φ`. This breaks for non-classical modal logics (intuitionistic modal logic). Adding `HasDia` is documented as a TODO (linked to task 173, now tombstoned). Low effort, high correctness payoff.

### 10. `BoolEvaluate` Is 90% of a Decidability Instance

`Semantics/Bool.lean` has `BoolEvaluate` with `instDecidableBoolEvaluate` and `BoolEvaluate_eq_iff`. For `[Fintype Atom] [DecidableEq Atom]`, an `instance : Decidable (Tautology φ)` is nearly within reach.

## Synthesis

### Conflicts Resolved

| Conflict | Teammate Views | Resolution |
|----------|---------------|------------|
| Sequent calculus priority | B, D: high priority; C: do not pursue | Include as P4 — community value is real but no roadmap blocker |
| Kripke completeness gap | D (round 2): "real but addressable"; C: already exists | C is correct — `MinStrongCompleteness.lean` and `IntStrongCompleteness.lean` contain full Kripke completeness; D's finding was based on incomplete module coverage |
| Capture-avoidance TODO | D: downstream implications; C: non-issue (no binders in PL) | C's analysis is more thorough — `subs` has zero external call sites, PL has no binding operators; clarify or remove the TODO |
| Scope of Foundations/ | C: too broad (66 files, only ~10 relevant); A: analyzed broadly | C is correct — scope should be `Propositional/` + `Foundations/Logic/` only |

### Gaps Identified

1. **No unified view of proof system equivalences**: Hilbert ↔ ND bridge exists, but no documentation or module shows the full picture (Hilbert ↔ ND ↔ LK ↔ Algebraic ↔ Kripke)
2. **No `Decidable (Tautology φ)` instance**: Infrastructure exists but not assembled
3. **CLL cut elimination is also incomplete**: `CutElimination.lean` has TODOs — cannot serve as a complete template

### Prior Research Corrections

The round-1 team research report (01_team-research.md) contained several inaccuracies now corrected:
- **Gap 1** (sorry in `ipl_conservative_over_mpl`): Resolved by Task 265
- **Gap 8** (no Kripke completeness for IPL/MPL): Wrong — both exist in `Min/IntStrongCompleteness.lean`
- **ProofSystem "not ported"**: Stale — instances exist in `Instances.lean` and `IntMinInstances.lean`

## Recommendations

### Priority 1: Hilbert-Tier Algebraic Completeness Corollaries (Low effort, High value)

Create `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` composing the existing Hilbert-ND bridge with algebraic completeness. ~50-100 lines, 1-2 days.

### Priority 2: Fix Stale Documentation (Minimal effort)

Update `ProofSystem.lean:50` to remove "not yet ported" comment. Clarify or remove the `subs` capture-avoidance TODO in `NaturalDeduction/Basic.lean:275`.

### Priority 3: Add Propositional Test Coverage (Low effort, Quick win)

Create `CslibTests/Propositional.lean` with `#eval` tests for `BoolEvaluate`, `decide` tests for `IsBotFree`, example derivations, and smoke tests.

### Priority 4: Propositional Sequent Calculus LK (High effort, High community value)

Two-sided `Finset × Finset` LK with cut elimination. Use CLL as template. ~600-1000 lines, 2-4 weeks. Would be the first LK/LJ formalization in Lean 4.

### Priority 5: Concretize Modal Tag Instances (Medium effort, High downstream impact)

Provide `InferenceSystem` + `ModalHilbert` instances for `Modal.HilbertK` (and ideally `Temporal.HilbertBX`, `Bimodal.HilbertTM`). Unlocks `GenericMCS` reuse, eliminating ~200-300 lines of custom MCS code per logic.

### Priority 6: Extract Propositional Tableau to Foundations/ (Medium effort)

Factor the 8 propositional tableau rules from `Bimodal/Decidability/Tableau.lean` into `Foundations/Logic/PropositionalTableau.lean`. ~200-400 lines. Enables propositional decidability via tableau and templates modal tableau.

### Priority 7: `HasDia` Primitive (Low effort)

Add `class HasDia (F : Type*) where dia : F → F` with duality axiom. Update `AxiomB`, `Axiom5`, `AxiomD`.

### Priority 8: `Decidable (Tautology φ)` Instance (Low effort)

Connect `BoolEvaluate_eq_iff` with `Fintype` enumeration to produce a `Decidable` instance for tautology checking.

### Deferred / Not Recommended

- **BimodalLogic witness-count restructure**: Irrelevant to this task
- **Craig interpolation**: High difficulty, no consumer identified
- **CNF/DNF normal forms**: Useful but not blocking anything
- **Abstract completeness extraction** (ROADMAP item): High value but depends on modal tag instances (P5) being done first
- **Generic `SequentCalculus` typeclass**: Over-engineering risk; start with concrete LK first

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|------------------|
| A | Primary / Current State | completed | high | Comprehensive file inventory, 7-gap analysis, BimodalLogic comparison |
| B | Alternatives / Prior Art | completed | high | Mathlib G4ip patterns, CLL template analysis, LK design proposal |
| C | Critic | completed | high | Corrected 3 stale findings from round 1, identified test gap, scoping |
| D | Strategic Horizons | completed | high | Modal tag instance strategy, roadmap alignment, tableau extraction idea |

## References

### Key Source Files
- `Cslib/Logics/Propositional/Defs.lean` — Formula type, 3-tier theory definitions
- `Cslib/Logics/Propositional/ProofSystem/` — Hilbert axioms, derivation trees, tag instances
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` — Hilbert ↔ ND bridge
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` — Algebraic completeness (ND tier)
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` — CPL strong completeness
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` — MPL Kripke completeness
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` — IPL Kripke completeness
- `Cslib/Foundations/Logic/ProofSystem.lean` — Typeclass hierarchy + tag definitions
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — Generic MCS infrastructure
- `Cslib/Logics/LinearLogic/CLL/Basic.lean` — Sequent calculus template
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` — Bimodal tableau (includes PL rules)

### External Prior Art
- Mathlib `itauto` (G4ip implementation) — design pattern for terminating sequent calculus
- FormalizedFormalLogic/Foundation — Lean 4 Tait calculus + first-order cut elimination
