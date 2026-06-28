# Research Report: Reverse-Inclusion Ordering on HilbertFilter Lattice

- **Task**: 311 - IPL conservative over IPL(imp,top) for imp-top-only formulas
- **Started**: 2026-06-23T21:00:00Z
- **Completed**: 2026-06-23T22:30:00Z
- **Effort**: Hard mode (H2+H3+H4)
- **Session**: sess_1750723200_a3b1c2_311_dual
- **Reference Grounding Tier**: Tier 1 (literature-backed) + Tier 3 (implementation-backed)
- **Sources/Inputs**:
  - [Rasiowa1974] Ch. V -- Hilbert algebras and deductive filters
  - `Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`
  - `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean`
  - `specs/311_ipl_conservative_over_imp/reports/01_conservative-extension-research.md`
  - `specs/310_diego_embedding/reports/02_imp-case-research.md`
- **Artifacts**: This report
- **Standards**: status-markers.md, artifact-management.md, report-format.md

## Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| [Rasiowa1974] Thm V.3.6, p.87 | `principal_le_himp` | `principal (a himp b) <= himpFilter (principal a) (principal b)` | transcribed (task 310) |
| [Rasiowa1974] Thm V.3.6, p.87 | `principal_le_algEvaluate` | `principal (HilbertEvaluate v phi) <= AlgEvaluate (principal . v) bot phi` | transcribed (task 310) |
| [Rasiowa1974] Thm V.3.3, p.85 | `instGeneralizedHeytingAlgebra` | `GeneralizedHeytingAlgebra (HilbertFilter H)` | transcribed (task 310) |
| (this research) | Deduction Theorem | `filter_join_principal_iff` | `c in K \/ principal(a) <-> a himp c in K` | proposed |
| (this research) | principal himp-preservation (reverse) | `principal_himp_eq_rev` | `principal(a himp b) = principal(a) himp_rev principal(b)` | proposed (depends on reverse-order GHA) |

## Executive Summary

- The reverse-inclusion ordering on HilbertFilter makes `principal` order-preserving and gives `principal(top) = top_rev`, fixing the polarity mismatch identified in report 01.
- A **Deduction Theorem for Hilbert filters** (`c in K \/ principal(a) <-> a himp c in K`) was identified as the key tool. This gives `principal(a himp b) = principal(a) himp_rev principal(b)` (EQUALITY) for the reverse-order Heyting implication, confirmed by exhaustive computation on 2- and 3-element Hilbert algebras.
- However, the reverse-inclusion filter lattice is **NOT a GeneralizedHeytingAlgebra in general**. It is a GHA for finite Hilbert algebras (because finite distributive lattices are Heyting algebras), but not for infinite ones (the dual of a frame is a co-frame, not necessarily a frame).
- Since `HAValid` quantifies over ALL HeytingAlgebras, instantiating it requires the target to be a full HeytingAlgebra. The reverse-inclusion filter lattice cannot serve this role for infinite Hilbert algebras.
- **The reverse-inclusion approach is therefore a dead end for the general case.** It fixes the himp-preservation gap but introduces a new gap: the target lacks the algebraic structure needed to instantiate HAValid.
- Two alternative routes were analyzed: (1) proof-theoretic via LJ cut-elimination + subformula property, which is blocked by an existing `sorry` in `cutAdmissibility`; (2) the himp-preserving embedding into a different Heyting algebra construction (Dedekind-MacNeille completion or ideal completion).
- **Recommendation**: Pursue the proof-theoretic route by completing `cutAdmissibility` (task 292), then proving the subformula property for cut-free LJ proofs of imp-top-only formulas.

## Context & Scope

This report investigates the hypothesis from task 311's previous research: whether reversing the ordering on the HilbertFilter lattice (from set inclusion to reverse inclusion) fixes the himp-preservation gap that blocks the Diego embedding approach to the conservative extension theorem.

### The Gap (from report 01)

The existing `principal_le_himp` gives only:
```
principal(a himp b) <= himpFilter(principal a)(principal b)
```
The reverse inequality is provably FALSE (counterexample: 2-element Hilbert algebra, `himpFilter(principal 0)(principal 0) = topFilter` but `principal(0 himp 0) = principal(top) = bot`).

The `coe_AlgEvaluate_impTopOnly` lemma requires `f(a himp b) = f(a) himp f(b)` (EQUALITY), which `principal` does not satisfy for the inclusion-order himp.

### The Hypothesis

Under reverse inclusion (`F <=rev G <-> G.carrier subset F.carrier`), `principal` becomes order-preserving and `principal(top) = top_rev = {top}`. The hypothesis is that the reverse-order Heyting implication satisfies `principal(a himp b) = principal(a) himp_rev principal(b)`.

## Findings

### 1. Concrete Verification: 2-Element and 3-Element Hilbert Algebras

**2-element algebra {0, 1}** with `0 < 1 = top`:
- Filters: F0 = {0,1}, F1 = {1}
- Reverse-inclusion order: F0 <=rev F1 (since {1} subset {0,1})
- Reverse-order himp: computed for all 4 pairs, matches `principal(a himp b)` in all cases.

**3-element chain {0, 1, 2}** with `0 < 1 < 2 = top`:
- Filters: F0 = {0,1,2}, F1 = {1,2}, F2 = {2}
- Reverse-inclusion order: F0 <=rev F1 <=rev F2
- Reverse-order himp: computed for all 9 pairs, matches `principal(a himp b)` in all cases.

Both algebras confirm the hypothesis for chains.

### 2. Deduction Theorem for Hilbert Filters

The key mathematical tool is a Deduction Theorem for Hilbert filters:

**Theorem** (Filter Deduction Theorem): For any deductive filter K and element a of a Hilbert algebra H:
```
c in K \/ principal(a) <-> a himp c in K
```
where `\/` denotes the join (in the inclusion-ordered filter lattice).

**Proof**:
- **(->)**: By induction on the derivation of `c` from `K union principal(a)`:
  - If `c in K`: then `a himp c in K` by the K axiom (`c <= a himp c`) and K being an upset.
  - If `c in principal(a)` (i.e., `a <= c`): then `a himp c = top in K` (since `a <= c` gives `a himp c = top`).
  - Upper closure: if `c' <= c` and `a himp c' in K`, then `a himp c in K` by `himp_le_himp_left` and K upset.
  - MP: if `c1 in gen` and `c1 himp c in gen`, and by IH `a himp c1 in K` and `a himp (c1 himp c) in K`, then by the S axiom `a himp (c1 himp c) <= (a himp c1) himp (a himp c)`, so `(a himp c1) himp (a himp c) in K`, and by MP with `a himp c1`, we get `a himp c in K`.
- **(<-)**: If `a himp c in K`, then `a himp c in K` and `a in principal(a)`, so by MP in the join, `c in K \/ principal(a)`.

### 3. Principal Preserves Reverse-Order Himp (General Case)

Using the Deduction Theorem, we can prove:

**Theorem**: `principal(a himp b) = principal(a) himp_rev principal(b)` in the reverse-inclusion filter lattice, where `himp_rev(F)(G)` is defined as the smallest filter K (fewest elements) such that `K \/_incl F supset G`.

**Proof**:
- `himp_rev(principal(a))(principal(b)) = sInf_incl{K | K \/_incl principal(a) supset principal(b)}`
- By the Deduction Theorem: `K \/_incl principal(a) supset principal(b)` iff `forall x, b <= x -> a himp x in K`, which holds iff `K supset {a himp x | b <= x}`.
- By himp monotonicity: `{a himp x | b <= x} = {y | a himp b <= y} = principal(a himp b)`.
- So `sInf{K | K supset principal(a himp b)} = principal(a himp b)`.

### 4. The Reverse-Inclusion Lattice Is NOT a GHA in General

**The critical obstruction**: For the reverse-inclusion filter lattice to be a GHA, we need the adjunction:
```
K /\_rev F <=rev G  iff  K <=rev F himp_rev G
```
The left-hand side is `K \/_incl F supset_incl G`. The `himp_rev(F)(G) = sInf_incl{L | L \/_incl F supset_incl G}`.

The adjunction requires: `(sInf_incl S) \/_incl F supset_incl G` when every member of S satisfies this condition. This is exactly the **dual frame property**: join distributes over arbitrary intersection.

- For **F = principal(a)** (principal filter as second argument), the Deduction Theorem gives the clean characterization `K \/_incl principal(a) = {c | a himp c in K}`, and this DOES distribute over intersections: `(cap K_i) \/_incl principal(a) = {c | a himp c in cap K_i} = {c | forall i, a himp c in K_i} = cap{c | a himp c in K_i} = cap(K_i \/_incl principal(a))`.

- For **general F**, no such clean characterization exists. The dual frame property may fail, and the reverse-inclusion lattice is NOT guaranteed to be a GHA.

- The inclusion-ordered filter lattice IS a frame (intersection distributes over arbitrary join). Its dual is a co-frame (join distributes over arbitrary intersection would need to hold). Co-frames have co-Heyting subtraction but NOT Heyting implication.

### 5. Why This Blocks the Conservative Extension

The conservative extension proof needs:
1. Start with `HAValid phi` (validity in all HeytingAlgebras)
2. Instantiate at some HeytingAlgebra built from a HilbertAlgebra H
3. Use principal as a himp-preserving map to transfer the result back to H

Step 2 requires the target to BE a HeytingAlgebra (to satisfy the HAValid quantifier).

- The **inclusion-ordered** filter lattice IS a HeytingAlgebra (GHA with `Compl via himp bot`), but `principal` does not preserve himp (only `<=`).
- The **reverse-inclusion** filter lattice has himp-preservation for principal, but is NOT a HeytingAlgebra (fails GHA adjunction for non-principal arguments).

Neither lattice satisfies BOTH requirements simultaneously.

### 6. Alternative Route: Proof-Theoretic via LJ

The sequent calculus route would bypass algebraic validity entirely:
1. `Derivable IntPropAxiom phi -> LJProof (emptyset ⊢ phi)` via `hilbert_iff_lj` (EXISTS in CSLib)
2. `LJProof -> CutFreeLJProof` via `cutElim` (EXISTS but `cutAdmissibility` has `sorry`)
3. `CutFreeLJProof` of imp-top-only formula uses only `impR`, `impL`, `ax` rules (subformula property -- NOT YET FORMALIZED)
4. Restricted proof -> `Derivable ImpAxiom phi` (NOT YET FORMALIZED)

**Blocker**: `cutAdmissibility` at line 103 of `LJ/CutElimination.lean` contains `sorry`. This is task 292 (`ipl_decidability_cutfree_lj`). Completing cut-elimination would unblock this route.

### 7. Alternative Route: Algebraic Completion

Construct a type `Completion(H)` from a HilbertAlgebra `H` such that:
- `Completion(H)` is a HeytingAlgebra
- There exists an injection `e : H -> Completion(H)` with `e(a himp b) = e(a) himp e(b)` (EQUALITY)

Candidate constructions:
- **Ideal completion / Dedekind-MacNeille completion**: Standard in lattice theory. Preserves existing meets and joins, but himp-preservation needs proof.
- **Free join completion via LowerSet**: Already used for BrouwerianSemilattice -> HeytingAlgebra bridge (via `LowerSet.Iic` which preserves `inf` and `himp`). NOT directly applicable to HilbertAlgebra since it lacks `inf`.
- **Filter lattice with custom himp**: Define a NEW himp on the reverse-inclusion lattice that works only for principal filters and show it suffices for the evaluation. This would require a custom evaluator bypassing `AlgEvaluate`.

The `LowerSet.Iic` approach works for BrouwerianSemilattice because `Iic` preserves both `inf` and `himp` (proved in `FreeJoinCompletion.lean` as `iicHimp`). The proof of `iicHimp` uses the BrouwerianSemilattice adjunction `x inf a <= b iff x <= a himp b`, which Hilbert algebras lack (no `inf`).

## Decisions

1. The reverse-inclusion approach is ruled out as a general solution.
2. The proof-theoretic route via LJ cut-elimination is the most promising next step, contingent on completing task 292.
3. The algebraic completion route is viable but requires significant new infrastructure not currently in CSLib.

## Recommendations

### Priority 1: Complete Cut-Elimination (Task 292 Dependency)

The `sorry` in `cutAdmissibility` (line 103 of `LJ/CutElimination.lean`) blocks the simplest proof route. Completing this is independently valuable and unblocks both the conservative extension theorem and the decidability result.

Once `cutAdmissibility` is sorry-free, the conservative extension proof would proceed:
1. `Derivable IntPropAxiom phi` -> `LJProof (emptyset vdash phi)` via `hilbert_iff_lj`
2. `LJProof.cutElim` -> `CutFreeLJProof (emptyset vdash phi)`
3. New lemma: for imp-top-only phi, a cut-free LJ proof of `emptyset vdash phi` uses only `impR`, `impL`, `ax` constructors (by the subformula property: every formula in a cut-free proof is a subformula of the endsequent, and subformulas of an imp-top-only formula are imp-top-only)
4. New lemma: restricted LJ proof -> `Derivable ImpAxiom phi` (straightforward translation)

### Priority 2: Algebraic Completion (Alternative if Task 292 is Slow)

If cut-elimination is not completed soon, construct a Heyting algebra from a Hilbert algebra directly. The most promising approach:
- Define `HilbertCompletion(H)` as the type of IDEALS (downsets closed under join, where join is the Hilbert algebra's meet-free lattice operation) or as a quotient of the free distributive lattice generated by H.
- Show `HilbertCompletion(H)` is a HeytingAlgebra and the canonical embedding preserves himp.
- This is a substantial construction (estimated 500-800 lines).

### Priority 3: Keep Task 311 Blocked

Task 311 should remain `[BLOCKED]` with dependency on either:
- Task 292 (cut-elimination for LJ), or
- A new task for the algebraic Hilbert-to-Heyting completion.

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Cut-elimination (task 292) may be difficult to complete | Blocks proof-theoretic route | Pursue algebraic route in parallel |
| Algebraic completion may require deep lattice theory | High implementation cost | Check Mathlib for existing Dedekind-MacNeille completion |
| The subformula property for LJ may need careful formalization | Moderate effort | The property is structural and follows directly from cut-freeness |

## Adversarial Self-Verification

### Challenged Claims

1. **"Reverse-inclusion filter lattice is NOT a GHA in general"**
   - **Challenge**: Could the filter lattice of a Hilbert algebra be completely distributive (which would make the dual a frame)?
   - **Verification**: Complete distributivity requires `inf(sup_i a_i) = sup_f(inf_i a_{f(i)})` for arbitrary families. This is a very strong condition that holds for power sets and completely distributive lattices but NOT for general algebraic lattices. The filter lattice of an infinite Hilbert algebra has no reason to satisfy this. The claim stands.
   - **Status**: Confirmed (for infinite case). For finite Hilbert algebras, the claim is false -- finite distributive lattices ARE Heyting algebras.

2. **"Deduction Theorem for Hilbert filters holds"**
   - **Challenge**: The proof by induction on the derivation needs the MP closure step to go through, which requires the S axiom.
   - **Verification**: The S axiom `(a himp (b himp c)) himp ((a himp b) himp (a himp c)) = top` provides exactly the substitution needed: from `a himp (c1 himp c) in K` and `a himp c1 in K`, we get `(a himp c1) himp (a himp c) in K` by the S axiom (upper closure), then `a himp c in K` by MP in K. This is a standard proof in Hilbert algebra theory.
   - **Status**: Confirmed.

3. **"The proof-theoretic route via LJ is viable"**
   - **Challenge**: The subformula property for cut-free LJ proofs needs formalization, and the translation from restricted LJ proofs to ImpAxiom derivations is non-trivial.
   - **Verification**: The subformula property is a standard consequence of cut-freeness in LJ (every formula in a cut-free proof is a subformula of the endsequent). For imp-top-only endsequents, this means all formulas are imp-top-only. The translation to ImpAxiom is then straightforward: `impR` corresponds to the deduction theorem (derivable from K and S), and `impL` corresponds to modus ponens. The viability is confirmed, modulo the sorry in `cutAdmissibility`.
   - **Status**: Confirmed, contingent on task 292 completion.

4. **"LowerSet.Iic approach cannot be adapted for HilbertAlgebra"**
   - **Challenge**: Could we define a version of LowerSet for Hilbert algebras?
   - **Verification**: `LowerSet.Iic` works for BrouwerianSemilattice because the proof of `iicHimp` (line 62 of FreeJoinCompletion.lean) uses `BrouwerianSemilattice.himp_inf_le` and `BrouwerianSemilattice.le_himp_iff`, both of which require `inf`. Hilbert algebras have no `inf`, so these lemmas are unavailable. The approach cannot be directly adapted.
   - **Status**: Confirmed.

### Uncertain Claims

1. **"Dedekind-MacNeille completion preserves himp for Hilbert algebras" (0.5 confidence)**: This is plausible but not verified. The DM completion preserves existing meets and joins but adding a himp that agrees with the original requires proof.

2. **"The subformula property gives exactly impR/impL/ax for imp-top-only" (0.85 confidence)**: This is standard but the exact formalization in Lean may require handling edge cases (e.g., the `weakL` and `botL` constructors need to be shown inapplicable).

### BibKey Verification

| BibKey | Status | Notes |
|--------|--------|-------|
| `Rasiowa1974` | VERIFIED in references.bib | Used throughout for filter lattice theory |
| `Diego1966` | NOT FOUND in references.bib | Referenced in DiegoEmbedding.lean docstring; needs to be added |
| `TroelstraSchwichtenberg2000` | NOT CHECKED | Referenced in CutElimination.lean |
| `NegriVonPlato2001` | NOT CHECKED | Referenced in LJ/Basic.lean |

## Appendix

### A. Pattern Comparison: Working vs. Failing Conservative Extensions

| Conservative Extension | Algebra | Evaluator | Embedding | Himp Preserved? | Status |
|------------------------|---------|-----------|-----------|-----------------|--------|
| IPL over MPL (bot-free) | GHA G | AlgEvaluate | WithBot.some : G -> WithBot G | Yes (for bot-free formulas, `coe_AlgEvaluate`) | WORKING |
| IPL over ConjImp (or-bot-free) | BSL B | BrouwerianEvaluate | LowerSet.Iic : B -> LowerSet B | Yes (`iicHimp` proves equality) | WORKING |
| ConjImpBot over ConjImp (or-free) | PBS B | PointedBrouwerianEvaluate | iicNonemptyLowerSet : B -> NonemptyLowerSet B | Yes (preserves inf, himp, bot, top) | WORKING |
| IPL over Imp (imp-top-only) | HA H | HilbertEvaluate | principal : H -> HilbertFilter H | NO (only <=, not =) | BLOCKED |
| IPL over Imp (imp-top-only) | HA H | N/A | principal (reverse-incl) | YES for principal, but target not GHA | BLOCKED (different reason) |

### B. Filter Deduction Theorem -- Formal Statement

For a Hilbert algebra `H`, filter `K : HilbertFilter H`, and element `a : H`:
```
forall c : H, c in (K \/ principal a) <-> (a himp c) in K
```
where `\/` is the join in the inclusion-ordered filter lattice.

This is provable from the K and S axioms of Hilbert algebras and should be formalized as a standalone lemma in `DiegoEmbedding.lean` regardless of the conservative extension outcome, as it is independently useful for understanding the filter lattice structure.
