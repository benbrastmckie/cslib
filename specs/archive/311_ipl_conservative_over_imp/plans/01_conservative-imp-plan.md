# Implementation Plan: IPL Conservative over IPL(->,%top)

- **Task**: 311 - IPL conservative over IPL(->,%top) for imp-top-only formulas
- **Status**: [COMPLETED]
- **Effort**: 8 hours
- **Dependencies**: 309, 310
- **Research Inputs**: specs/311_ipl_conservative_over_imp/reports/03_blocker-unblock-research.md
- **Artifacts**: plans/01_conservative-imp-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prove that IPL is conservative over its implicational fragment IPL(->,%top) for imp-top-only
formulas: if `Derivable IntPropAxiom phi` and `phi.IsImpTopOnly = true`, then
`Derivable ImpAxiom phi`. The proof decomposes into two steps: (1) IPL -> ConjImp conservativity
(already proven via `hilbertIplConservativeOverConjImp`), and (2) ConjImp -> Imp conservativity
for imp-top-only formulas (the new content). Step 2 requires constructing a free
BrouwerianSemilattice over any HilbertAlgebra, showing the singleton embedding preserves himp
(via the Hilbert deduction theorem already in the codebase), then composing with LowerSet.Iic
(whose himp-preservation for BSLs is proven in `iicHimp`) to get a HeytingAlgebra embedding.

### Research Integration

Key findings from report 03 integrated into this plan:
- Two-step decomposition: IPL -> ConjImp (done) -> Imp (gap to fill)
- Free BSL construction using Multiset H with Hilbert deducibility ordering
- Deduction theorem (`hilbertImpIDeriv`/`hilbertImpEDeriv`) provides BSL adjunction
- Composition with `LowerSet.Iic` via `iicHimp` gives HeytingAlgebra embedding
- `coe_AlgEvaluate_impTopOnly` transfers evaluation along himp-preserving maps

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Construct the free BrouwerianSemilattice over a HilbertAlgebra (FreeMeetExtension)
- Prove the singleton embedding preserves himp and reflects top
- Prove `Derivable ConjImpAxiom phi -> Derivable ImpAxiom phi` for IsImpTopOnly formulas
- Prove the full conservativity theorem composing Steps 1 and 2
- Derive the ND corollary

**Non-Goals**:
- Proving conservativity for formulas outside the imp-top-only fragment
- Proving cut-elimination for LJ (blocked by sorry in `cutAdmissibility`)
- Adding new axiom systems or fragments
- Modifying existing algebraic completeness theorems

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Multiset ordering on FreeMeetExtension is hard to formalize | H | M | Use `List H` with explicit equivalence relation instead of `Multiset`; alternatively use `Finset` if duplicates are not needed |
| BSL adjunction proof (le_himp_iff) is more complex than expected | H | M | The adjunction for singletons reduces to the deduction theorem (proven); general case extends by induction on multiset structure |
| `coe_AlgEvaluate_impTopOnly` requires `GeneralizedHeytingAlgebra` but FreeMeetExtension is only a BSL | M | L | The lemma is used on LowerSet(FreeMeetExtension H), which is a GHA; FreeMeetExtension itself is not evaluated directly |
| Universe polymorphism issues in Multiset/LowerSet composition | M | M | Keep universe parameters explicit; follow patterns from `ConjImpConservative.lean` |
| Defining himp on FreeMeetExtension constructively | H | M | Use the adjunction definition (exists by completeness of the semilattice partial order); alternatively define explicitly via deduction |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: FreeMeetExtension - Definition and Preorder [IN PROGRESS]

**Goal**: Define the `FreeMeetExtension H` type and its ordering for a HilbertAlgebra H,
and prove it forms a Preorder.

**Tasks**:
- [ ] Create file `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean`
- [ ] Add module docstring with references to Kohler1981 and the deduction theorem approach
- [ ] Import `Cslib.Foundations.Order.HilbertAlgebra` and `Mathlib.Data.Multiset.Basic`
- [ ] Define `FreeMeetExtension (H : Type*) [HilbertAlgebra H] := Multiset H`
- [ ] Define the ordering: `S <= T` iff for each `t` in `T`, `HilbertAlgebra.himp_eq_top_iff` witnesses that `t` is "derivable from S" using the Hilbert algebra operations. Concretely: `S.le T := forall t in T, exists a in S, a <= t` (the Smyth/lower preorder)
- [ ] Alternatively, define ordering as: `S <= T` iff `forall t in T, Multiset.fold (fun x y => x himp y) top S himp t = top` -- choose whichever formalization is cleaner
- [ ] Prove `FreeMeetExtension.le_refl` and `FreeMeetExtension.le_trans`
- [ ] Prove that the empty multiset is top: `forall S, S <= {}`
- [ ] Prove `{a} <= {b} iff a <= b` in H (singleton embedding reflects and preserves order)

**Design decision**: The ordering should be chosen to make the BSL adjunction `U ++ {a} <= {b} iff U <= {a himp_H b}` hold. The research recommends using Hilbert deducibility: `S <= T` iff for each `t` in `T`, there is a derivation from S to `t` using K, S, and modus ponens at the algebra level. The simplest formalization: `S <= T := forall t in T, there exists a multiset folding path from S to t`. However, the concrete definition needs to be checked against what makes the adjunction provable.

**Critical insight**: The Smyth ordering `S <= T := forall t in T, exists s in S, s <=_H t` does NOT give the BSL adjunction. The correct ordering must account for "multi-premise derivation" from S. Consider defining it as: `FreeMeetExtensionLe S T := forall t in T, foldr (fun a acc => a himp acc) t S = top` -- this says each element of T is derivable from S using iterated application of the K/S axioms.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` (new file, ~150-200 lines)

**Verification**:
- `lake build Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension` compiles without errors
- Ordering satisfies `{a} <= {b} iff a <=_H b`
- Empty multiset is greatest element

---

### Phase 2: FreeMeetExtension - BrouwerianSemilattice Instance [COMPLETED]

**Goal**: Equip `FreeMeetExtension H` with meet and himp operations, and prove the
BrouwerianSemilattice instance.

**Tasks**:
- [ ] Define `SemilatticeInf` instance: `S inf T = S + T` (multiset append/union)
- [ ] Prove `inf_le_left`, `inf_le_right`, and `le_inf` for multiset append
- [ ] Define `OrderTop` instance with `top = {}` (empty multiset)
- [ ] Define `HImp` on `FreeMeetExtension H`: `S himp T` is defined via the adjunction or explicitly. For singletons: `{a} himp {b} = {a himp_H b}`. General case by extension.
- [ ] Prove the BSL adjunction `le_himp_iff`: `U <= S himp T iff U + S <= T`
- [ ] The key proof obligation for singletons: `U + {a} <= {b} iff U <= {a himp_H b}`. Forward: if `U + {a} <= {b}`, then by the deduction theorem (`hilbertImpIDeriv` at the algebra level), `U` derives `a himp_H b`. Backward: if `U <= {a himp_H b}`, then `U + {a}` derives `b` by modus ponens (`hilbertImpEDeriv`).
- [ ] Prove `le_antisymm` to get `PartialOrder` (quotient by the generated equivalence, or prove antisymmetry directly on the chosen ordering)
- [ ] Assemble the `BrouwerianSemilattice (FreeMeetExtension H)` instance

**Key mathematical note**: Defining himp for general multisets (not just singletons) requires
care. The simplest approach: define `S himp T` as the multiset `{s1 himp (s2 himp ... (sn himp t1) ...)}` for each `t` in `T`, where `s1, ..., sn` are elements of `S`. This definition needs to match what the adjunction produces. An alternative: since we only need the embedding to work for singletons, we might define himp only for the image of the embedding and use the free BSL universal property for the general case.

**Fallback**: If defining himp for general multisets proves too complex, consider using a
quotient type or a different representation (e.g., `List H` modulo permutation and the
derivability equivalence).

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` (extend, ~200-300 additional lines)

**Verification**:
- `BrouwerianSemilattice (FreeMeetExtension H)` instance compiles
- `le_himp_iff` for singletons reduces to the deduction theorem
- `lake build Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension` succeeds

---

### Phase 3: HimpPreserving Embedding and ImpConservative Theorem [COMPLETED]

**Goal**: Prove the singleton embedding `eta : H -> FreeMeetExtension H` preserves himp and
reflects top, compose with `LowerSet.Iic` to get a HeytingAlgebra embedding, and prove the
conservativity theorem `Derivable ConjImpAxiom phi -> Derivable ImpAxiom phi` for
IsImpTopOnly formulas.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean`
- [ ] Import `Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension`, `Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion`, `Cslib.Logics.Propositional.Semantics.Algebra.HilbertAlgCompleteness`, `Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative`
- [ ] Define `freeMeetEmbed (a : H) : FreeMeetExtension H := {a}` (singleton multiset)
- [ ] Prove `freeMeetEmbed_himp`: `freeMeetEmbed (a himp b) = freeMeetEmbed a himp freeMeetEmbed b`
  - This is the key lemma: `{a himp_H b} = {a} himp_{BSL} {b}`
  - Follows from the BSL adjunction on singletons and the Hilbert deduction theorem
- [ ] Prove `freeMeetEmbed_top_iff`: `freeMeetEmbed a = top iff a = top`
  - Forward: `{a} = {} (empty multiset)` is impossible (cardinality mismatch)
  - Actually: `{a} <= {} and {} <= {a}` means `{a}` is top in the order, which by the ordering means `a` is derivable from nothing, i.e., `a = top` in H
- [ ] Define `hilbertToHeyting : H -> LowerSet (FreeMeetExtension H) := LowerSet.Iic . freeMeetEmbed`
- [ ] Prove `hilbertToHeyting_himp`: `hilbertToHeyting (a himp b) = hilbertToHeyting a himp hilbertToHeyting b`
  - Compose `freeMeetEmbed_himp` and `iicHimp`
- [ ] Prove `hilbertToHeyting_eq_top_iff`: `hilbertToHeyting a = top iff a = top`
  - Compose `freeMeetEmbed_top_iff` and `iicEqTopIff`
- [ ] Prove `hilbertAlgEmbeddingLemma` (analogue of `brouwerianEmbeddingLemma`):
  For IsImpTopOnly formulas, `HilbertEvaluate v phi = top iff AlgEvaluate (hilbertToHeyting . v) bot phi = top`
  - Use `coe_AlgEvaluate_impTopOnly` with `f = hilbertToHeyting` and `h_himp = hilbertToHeyting_himp`
  - Then `hilbertToHeyting_eq_top_iff` converts between top in LowerSet and top in H
- [ ] Prove `hilbertConjImpConservativeOverImp`:
  `IsImpTopOnly phi -> Derivable ConjImpAxiom phi -> Derivable ImpAxiom phi`
  - Following the pattern of `hilbertIplConservativeOverConjImp`:
    1. `conjImp_brouwerian_complete.mp h` gives `BrouwerianValid phi` (soundness direction, actually `conjImp_brouwerian_soundness_derivable`)
    2. For any HilbertAlgebra H and v : Atom -> H, instantiate BrouwerianValid at `FreeMeetExtension H` with `freeMeetEmbed . v`
    3. `hilbertAlgEmbeddingLemma` (or direct computation) gives `HilbertEvaluate v phi = top`
    4. `imp_hilbert_complete` converts to `Derivable ImpAxiom phi`

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean` (new file, ~150-200 lines)

**Verification**:
- `hilbertConjImpConservativeOverImp` compiles with the correct type signature
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.ImpConservative` succeeds
- `lean_verify` confirms no sorry axioms

---

### Phase 4: Full Conservativity Theorem and ND Corollary [COMPLETED]

**Goal**: Compose Steps 1 and 2 into the final theorem and derive the ND corollary.
Add the new files to `Cslib.lean` barrel import and verify CI.

**Tasks**:
- [ ] Prove `hilbertIplConservativeOverImp`:
  `IsImpTopOnly phi -> Derivable IntPropAxiom phi -> Derivable ImpAxiom phi`
  - Step 1: `hilbertIplConservativeOverConjImp (IsImpTopOnly_implies_IsOrBotFree phi hITO) h` gives `Derivable ConjImpAxiom phi`
  - Step 2: `hilbertConjImpConservativeOverImp hITO` gives `Derivable ImpAxiom phi`
- [ ] Prove subsumption direction `derivableImpOfDerivableInt`:
  `Derivable ImpAxiom phi -> Derivable IntPropAxiom phi`
  - Use `liftDerivationTree` with `ImpAxiom.toConjImpAxiom` then `ConjImpAxiom.toMinPropAxiom` then `.toIntPropAxiom`
- [ ] Prove biconditional `hilbertIplConservativeOverImp_iff`:
  `IsImpTopOnly phi -> (Derivable IntPropAxiom phi <-> Derivable ImpAxiom phi)`
- [ ] Prove ND corollary `ipl_conservative_over_imp` (with `[DecidableEq Atom]`):
  `IsImpTopOnly A -> DerivableIn IPL A -> Derivable ImpAxiom A`
  - Via `derivableInIplIffDerivableInt` bridge
- [ ] Run `lake exe mk_all --module` to update barrel import
- [ ] Run `lake build` (full project) to verify no regressions
- [ ] Run `lake exe checkInitImports` to verify Cslib.Init imports
- [ ] Run `lake exe lint-style` for style compliance

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean` (extend, ~50-80 additional lines)
- `Cslib.lean` (barrel import update via `mk_all`)

**Verification**:
- `hilbertIplConservativeOverImp` type-checks with no sorry
- `lean_verify Cslib.Logic.PL.hilbertIplConservativeOverImp` confirms axiom safety
- `lake build` succeeds (full project)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension` -- Phase 1-2 verification
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.ImpConservative` -- Phase 3-4 verification
- [ ] `lake build` -- full project, no regressions
- [ ] `lean_verify` on `hilbertIplConservativeOverImp` -- no sorry, no additional axioms
- [ ] `lake exe checkInitImports` -- all files import Cslib.Init
- [ ] `lake exe lint-style` -- style compliance
- [ ] `lake test` -- CslibTests suite passes

## Artifacts & Outputs

- `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` -- Free BSL over HilbertAlgebra
- `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean` -- Conservativity theorem
- `specs/311_ipl_conservative_over_imp/plans/01_conservative-imp-plan.md` -- This plan

## Rollback/Contingency

If the `FreeMeetExtension` construction proves intractable:
1. **Fallback A**: Use `List H` instead of `Multiset H` with explicit permutation equivalence
2. **Fallback B**: Define the ordering differently (e.g., pointwise rather than deducibility-based), accepting a weaker BSL instance
3. **Fallback C**: Pursue Approach 7 from research (direct derivation tree transformation to eliminate conjunction axioms) -- uncertain but potentially simpler
4. All new files can be deleted without affecting existing code (no modifications to existing files except barrel import)
