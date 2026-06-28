# Research Report: MPL Conservative Extension Chain

- **Task**: 322 - MPL Conservative Extension Chain
- **Started**: 2026-06-24T00:00:00Z
- **Completed**: 2026-06-24T00:30:00Z
- **Effort**: 0.5 hours
- **Dependencies**: None (all building blocks exist)
- **Sources/Inputs**:
  - `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` -- target file (191 lines)
  - `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` -- IPL chain for comparison
  - `Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean` -- `brouwerianEmbeddingLemma`
  - `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` -- `MPL.hilbert_alg_complete`
  - `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` -- `conjImp_brouwerian_complete`
  - `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` -- fragment predicates
  - `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean` -- `hilbertConjImpConservativeOverImp`
  - `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` -- `liftDerivationTree`, `hilbertIplConservativeOverConjImp`
  - `Cslib/Logics/Propositional/Semantics/Algebra.lean` -- `GHAValid`, `HAValid`, `BAValid`, `AlgEvaluate`
  - `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean` -- `BrouwerianValid`, `BrouwerianEvaluate`
  - `Cslib/Logics/Propositional/Semantics/Algebra/Hilbert.lean` -- `HilbertValid`, `HilbertEvaluate`
  - `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` -- `imp_hilbert_complete`
  - `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` -- `ImpAxiom`, `ConjImpAxiom`, coercions
  - `Cslib/Foundations/Order/HilbertAlgebra.lean` -- `BrouwerianSemilattice.toHilbertAlgebra`, `HilbertAlgebra.instPartialOrder`
  - `references.bib` -- BibKey verification
- **Artifacts**: `specs/322_mpl_conservative_extension_chain/reports/01_mpl-chain-research.md` (this file)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The target file `MplConservativeChain.lean` already contains all 5 core theorems (hilbertMplConservativeOverConjImp_direct, mplAxiom_iff_conjImpAxiom, hilbertMplConservativeOverImp_direct, mplAxiom_iff_impAxiom, plus the direct `attribute [-instance]` workaround). The docstring also references `GHAValid_implies_BrouwerianValid_direct` which does not exist as a standalone theorem.
- **CRITICAL BLOCKER**: The file does NOT build. `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain` fails with a typeclass diamond error between `HilbertAlgebra.instPartialOrder` and `BrouwerianSemilattice.toPartialOrder` when resolving `LowerSet.Iic`.
- The `attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra in` approach on line 131 is not sufficient to resolve the diamond. The error persists because `HilbertAlgebra.instPartialOrder` is synthesized through a path that the local instance suppression does not reach.
- The existing plan (01_mpl-chain-plan.md) incorrectly assumes "The file already contains 4 sorry-free theorems" -- the file actually has 4 theorem statements but they do not compile.
- Two BibKeys (`Nemitz1965`, `Kohler1981`) cited in the module docstring are missing from `references.bib` and should be added.

## Context & Scope

### What This Task Requires

The task asks for three categories of work:
1. **MPL-to-ConjImp conservativity** for or-bot-free formulas (GHAValid to BrouwerianValid via LowerSet.Iic embedding)
2. **MPL-to-Imp conservativity** for imp-top-only formulas as a composition
3. **Algebraic picture organization**: state the MPL chain independently of IPL, and relate to the IPL chain

### What Exists

The file already attempts all of these. The algebraic proof strategy is correct (GHAValid at LowerSet B, then brouwerianEmbeddingLemma). The sole remaining issue is the typeclass diamond that prevents compilation.

### Constraint: Independence from IPL

The module must NOT use `IntPropAxiom`, `IPL`, `HAValid`, `hilbertIplConservativeOverMpl`, or `derivableMinOfDerivableInt` in any proof term. The direct route goes: `MPL.hilbert_alg_complete` (GHA completeness) then `brouwerianEmbeddingLemma` (LowerSet embedding) then `conjImp_brouwerian_complete` (BSL completeness). This constraint is satisfied by the existing code.

## Source-to-Implementation Mapping

This is a Tier 3 (implementation-backed) task -- not literature-backed. No literature-level mapping table is required.

## Findings

### Finding 1: Typeclass Diamond is the Sole Blocker

The build error at line 133 is:

```
Type mismatch
  LowerSet.Iic
has type
  B -> @LowerSet B (@Preorder.toLE B (@PartialOrder.toPreorder B hBSL.toPartialOrder))
but is expected to have type
  B -> @LowerSet B (@Preorder.toLE B (@PartialOrder.toPreorder B HilbertAlgebra.instPartialOrder))
```

**Root cause**: `BrouwerianSemilattice.toHilbertAlgebra` (priority 100, defined in `Cslib/Foundations/Order/HilbertAlgebra.lean:224`) creates a `HilbertAlgebra B` instance from any `BrouwerianSemilattice B`. `HilbertAlgebra` defines its own `instPartialOrder` (line 133 of HilbertAlgebra.lean) where `a <= b iff a ==> b = top`. This creates two competing `PartialOrder B` instances:
  - Path 1: `BrouwerianSemilattice B -> SemilatticeInf B -> PartialOrder B`
  - Path 2: `BrouwerianSemilattice B -> HilbertAlgebra B -> PartialOrder B`

When `brouwerianEmbeddingLemma` is proved in `FreeJoinCompletion.lean` (which does NOT import `ImpConservative`), only Path 1 exists. But `MplConservativeChain.lean` imports `ImpConservative`, which transitively imports `HilbertAlgebra`, bringing Path 2 into scope.

**Why `attribute [-instance]` fails**: The `attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra in` suppresses the forgetful instance locally, but by this point the `HilbertAlgebra.instPartialOrder` may already be cached in the environment from other imports. The `LowerSet.Iic` resolution happens at a point where Lean still sees the competing instance.

### Finding 2: Three Proven Approaches to Fix the Diamond

**Approach A (Recommended): Explicit `@`-annotation for `LowerSet.Iic`**

The original code (seen in an earlier version of the file) used:
```lean
let iic : B -> LowerSet B := @LowerSet.Iic B hBSL.toSemilatticeInf.toPartialOrder.toPreorder
```
This manually specifies which `Preorder`/`PartialOrder` instance `LowerSet.Iic` should use, bypassing the diamond. This approach was present in a prior version of the file but appears to have been replaced with the `attribute [-instance]` approach.

However, the earlier version ALSO had a type mismatch (the build error message at line 137 shows `brouwerianEmbeddingLemma` expects `LowerSet.Iic` not `iic`). The fix requires ensuring `brouwerianEmbeddingLemma` is applied with the SAME `LowerSet.Iic` that `hGHA` uses, which means the `@` annotation must also be threaded through the embedding lemma call.

**Approach B: Use `haveI : BrouwerianSemilattice B := _` to reset the instance**

Inside the proof, add:
```lean
haveI : PartialOrder B := hBSL.toSemilatticeInf.toPartialOrder
```
This pins the `PartialOrder` instance before any `LowerSet.Iic` resolution.

**Approach C: Move `hilbertMplConservativeOverConjImp_direct` to a file that does NOT import `ImpConservative`**

Since the diamond only arises when `HilbertAlgebra` is in scope, proving this theorem in `FreeJoinCompletion.lean` or a new intermediate file that sits between `FreeJoinCompletion` and `MplConservativeChain` would avoid the diamond entirely. Then `MplConservativeChain` can re-export the result.

**Assessment**: Approach A is simplest and most local. The key insight is that the `@` annotation must be applied consistently: both in the `MPL.hilbert_alg_complete.mp` instantiation AND in the `brouwerianEmbeddingLemma` call. Specifically, one should rewrite `brouwerianEmbeddingLemma` to use the `@`-annotated `LowerSet.Iic` or convert between the two using a proof that the two `PartialOrder` instances agree (`eq_mpr` or `cast`).

### Finding 3: Existing Theorems and Signatures

All building blocks exist and are verified (they build in their home files):

| Theorem | File | Signature |
|---------|------|-----------|
| `MPL.hilbert_alg_complete` | `HilbertCompleteness.lean` | `Derivable MinPropAxiom phi <-> GHAValid phi` |
| `conjImp_brouwerian_complete` | `BrouwerianCompleteness.lean` | `IsOrBotFree phi -> BrouwerianValid phi -> Derivable ConjImpAxiom phi` |
| `brouwerianEmbeddingLemma` | `FreeJoinCompletion.lean` | `BrouwerianEvaluate v phi = top <-> AlgEvaluate (LowerSet.Iic . v) bot phi = top` (requires `IsOrBotFree`) |
| `hilbertConjImpConservativeOverImp` | `ImpConservative.lean` | `IsImpTopOnly phi -> Derivable ConjImpAxiom phi -> Derivable ImpAxiom phi` |
| `IsImpTopOnly_implies_IsOrBotFree` | `FragmentPredicates.lean` | `A.IsImpTopOnly = true -> A.IsOrBotFree = true` |
| `liftDerivationTree` | `ConjImpConservative.lean` | Lifts derivation trees across axiom subsumption |
| `ImpAxiom.toConjImpAxiom` | `FragmentAxioms.lean` | `ImpAxiom phi -> ConjImpAxiom phi` |
| `ConjImpAxiom.toMinPropAxiom` | `FragmentAxioms.lean` | `ConjImpAxiom phi -> MinPropAxiom phi` |

### Finding 4: Validity Definitions (Exact Signatures and Locations)

| Definition | Location | Signature |
|------------|----------|-----------|
| `GHAValid` | `Algebra.lean:126` | `forall (H : Type*) [GeneralizedHeytingAlgebra H] (v : Atom -> H) (bot_val : H), AlgEvaluate v bot_val phi = top` |
| `HAValid` | `Algebra.lean:133` | `forall (H : Type*) [HeytingAlgebra H] (v : Atom -> H), AlgEvaluate v (bot : H) phi = top` |
| `BAValid` | `Algebra.lean:140` | `forall (H : Type*) [BooleanAlgebra H] (v : Atom -> H), AlgEvaluate v (bot : H) phi = top` |
| `BrouwerianValid` | `Brouwerian.lean:106` | `forall (H : Type*) [BrouwerianSemilattice H] (v : Atom -> H), BrouwerianEvaluate v phi = top` |
| `HilbertValid` | `Hilbert.lean:100` | `forall (H : Type*) [HilbertAlgebra H] (v : Atom -> H), HilbertEvaluate v phi = top` |

### Finding 5: Plan Items Not Yet Needed

The existing plan proposes adding three new declarations:
1. `GHAValid_implies_BrouwerianValid_direct` -- referenced in the module docstring but not yet a standalone theorem
2. `derivableConjImpOfDerivableMin` -- subsumption Imp -> MinProp (reverse direction)
3. `derivableImpOfDerivableMin` -- subsumption Imp -> MinProp composed

These are secondary concerns. The **primary task** is fixing the build error. Once the 4 existing theorems compile, the 3 additions are each 1-3 lines using existing building blocks.

### Finding 6: BibKey Verification

| BibKey | Status | Notes |
|--------|--------|-------|
| `Rasiowa1974` | VERIFIED in `references.bib` | `@book{Rasiowa1974, ...}` |
| `Nemitz1965` | MISSING from `references.bib` | Cited in docstring but no entry. Needs to be added. |
| `Kohler1981` | MISSING from `references.bib` | Cited in docstring but no entry. Needs to be added. |
| `Glivenko1929` | VERIFIED in `references.bib` | Used in `ConservativeChain.lean`, not this file |
| `RasiowaSikorski1963` | VERIFIED in `references.bib` | Used in `ConservativeChain.lean`, not this file |

### Finding 7: Relationship Between MPL Chain and IPL Chain

The `ConservativeChain.lean` file proves the same conservativity results but routes through IPL:

**IPL Chain** (in `ConservativeChain.lean`):
- `hilbertMplConservativeOverConjImp`: MPL -> ConjImp via `derivableMinOfDerivableInt` then `hilbertIplConservativeOverConjImp`
- `hilbertMplConservativeOverImp`: MPL -> Imp via `derivableMinOfDerivableInt` then `hilbertIplConservativeOverImp`

**MPL Chain** (in `MplConservativeChain.lean`):
- `hilbertMplConservativeOverConjImp_direct`: MPL -> ConjImp via GHAValid at LowerSet B then brouwerianEmbeddingLemma
- `hilbertMplConservativeOverImp_direct`: MPL -> Imp by composing the direct MPL -> ConjImp with hilbertConjImpConservativeOverImp

The MPL chain is strictly independent of IPL machinery. It uses only:
- GHA-level completeness (`MPL.hilbert_alg_complete`)
- BSL-level completeness (`conjImp_brouwerian_complete`)
- The LowerSet embedding (`brouwerianEmbeddingLemma`)
- HA-level conservativity for the second step (`hilbertConjImpConservativeOverImp`)

## Decisions

- **D1**: The typeclass diamond must be resolved before any new declarations are added.
- **D2**: Approach A (explicit `@`-annotation) is recommended as the most surgical fix. If that proves intractable, Approach C (moving the proof to a diamond-free file) is the fallback.
- **D3**: The plan should be revised to prioritize the build fix as Phase 0, with the 3 new declarations as Phase 1.

## Recommendations

1. **[PRIORITY: CRITICAL] Fix the typeclass diamond in `hilbertMplConservativeOverConjImp_direct`**.
   The recommended approach: within the proof, after `intro B _ v`, use explicit `@` annotations to pin the `Preorder` instance used by `LowerSet.Iic`, and use `show`/`change`/`conv` to unify the types. The `attribute [-instance]` approach should be removed since it does not work. Alternatively, try `set_option synthInstance.maxHeartbeats` or restructure the proof to go through an intermediate lemma proved in a file without the diamond.

2. **[PRIORITY: HIGH] Add `GHAValid_implies_BrouwerianValid_direct` as a standalone theorem**.
   This extracts the algebraic core from the proof of `hilbertMplConservativeOverConjImp_direct`. Signature: `{phi : PL.Proposition Atom} -> (hOBF : phi.IsOrBotFree = true) -> GHAValid phi -> BrouwerianValid phi`. The proof is the inner loop of the existing proof (instantiate at LowerSet B, apply brouwerianEmbeddingLemma). This also inherits the typeclass diamond and should use the same fix.

3. **[PRIORITY: MEDIUM] Add subsumption lemmas `derivableConjImpOfDerivableMin` and `derivableImpOfDerivableMin`**.
   These are 1-3 lines each using `liftDerivationTree` with the coercion chains `.toMinPropAxiom` and `.toConjImpAxiom.toMinPropAxiom`.

4. **[PRIORITY: LOW] Add missing BibKey entries to `references.bib`**.
   - `Nemitz1965`: W. Nemitz, "Implicative semi-lattices", Trans. Amer. Math. Soc. 117 (1965), 128-142.
   - `Kohler1981`: P. Kohler, "Brouwerian semilattices", Trans. Amer. Math. Soc. 268 (1981), 103-126.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Typeclass diamond cannot be resolved with `@`-annotation alone | H | M | Fall back to Approach C: extract the diamond-sensitive proof to a file that does not import HilbertAlgebra |
| `brouwerianEmbeddingLemma` needs different `LowerSet.Iic` types to unify | M | M | Use `show` or `change` to rewrite the goal type, or use `congr`/`convert` to bridge the two `PartialOrder` instances |
| Adding `attribute [-instance]` globally would break other files | H | L | Never add it globally; use only local `in` scope or explicit `@` |

## Adversarial Self-Verification

### Challenge 1: "Is the typeclass diamond really the only issue?"

**Verified**: Yes. The build log shows exactly two errors, both on lines 133 and 137 of the same function, both caused by `HilbertAlgebra.instPartialOrder` vs `hBSL.toPartialOrder` disagreement. No other errors appear. The downstream theorems (`mplAxiom_iff_conjImpAxiom`, `hilbertMplConservativeOverImp_direct`, `mplAxiom_iff_impAxiom`) fail only because `hilbertMplConservativeOverConjImp_direct` fails.

### Challenge 2: "Could the `attribute [-instance]` approach work with different syntax?"

**Uncertain (medium confidence)**: The `attribute [-instance] ... in` syntax is the standard Lean 4 way to locally suppress instances. If it's not working, it may be because the instance is being synthesized during elaboration of the theorem statement (before the `in` scope takes effect) or because a cached instance from imports is being used. This needs empirical testing during implementation.

### Challenge 3: "Does the existing `ConservativeChain.lean` already provide everything this task needs?"

**Verified**: `ConservativeChain.lean` provides `hilbertMplConservativeOverConjImp` and `hilbertMplConservativeOverImp` but they route through IPL (`derivableMinOfDerivableInt`). The task explicitly requires a **direct algebraic route** that does not pass through IPL, which is what `MplConservativeChain.lean` provides. The two files are complementary, not duplicative.

### Challenge 4: "Are the Reuse Check Protocol steps exhausted?"

**Verified**:
- Step 1 (CSLib Foundations): Checked `HilbertAlgebra.lean` for the diamond source.
- Step 2 (Typeclass hierarchy): Verified `BrouwerianSemilattice.toHilbertAlgebra` and `HilbertAlgebra.instPartialOrder`.
- Step 3 (Notation typeclasses): Not applicable.
- Step 4 (Mathlib): `LowerSet.Iic` is from Mathlib; its behavior with competing instances is the issue.
- Step 5 (Logics/Languages): All relevant files in the Algebra directory checked.

### BibKey Verification Status

- `Rasiowa1974`: Confirmed present
- `Nemitz1965`: Confirmed MISSING -- needs to be added
- `Kohler1981`: Confirmed MISSING -- needs to be added

## Appendix

### Complete Theorem Inventory of MplConservativeChain.lean

| # | Theorem | Status |
|---|---------|--------|
| 1 | `hilbertMplConservativeOverConjImp_direct` | FAILS TO BUILD (typeclass diamond) |
| 2 | `mplAxiom_iff_conjImpAxiom` | FAILS (depends on #1) |
| 3 | `hilbertMplConservativeOverImp_direct` | FAILS (depends on #1) |
| 4 | `mplAxiom_iff_impAxiom` | FAILS (depends on #3) |
| 5 | `GHAValid_implies_BrouwerianValid_direct` | NOT YET ADDED (referenced in docstring) |
| 6 | `derivableConjImpOfDerivableMin` | NOT YET ADDED (proposed in plan) |
| 7 | `derivableImpOfDerivableMin` | NOT YET ADDED (proposed in plan) |

### Import Graph (Simplified)

```
MplConservativeChain
  |-- FreeJoinCompletion (brouwerianEmbeddingLemma)
  |     |-- Brouwerian (BrouwerianEvaluate, BrouwerianValid)
  |     |-- FragmentPredicates (IsOrBotFree, IsImpTopOnly)
  |-- HilbertCompleteness (MPL.hilbert_alg_complete)
  |-- BrouwerianCompleteness (conjImp_brouwerian_complete)
  |-- ImpConservative (hilbertConjImpConservativeOverImp)  <-- brings HilbertAlgebra into scope
  |     |-- HilbertAlgCompleteness (imp_hilbert_complete)
  |     |     |-- Hilbert (HilbertEvaluate, HilbertValid)
  |     |     |     |-- HilbertAlgebra <-- SOURCE OF DIAMOND
  |-- ConjImpConservative (liftDerivationTree)
```

### References

- [Rasiowa1974] A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*, North-Holland, 1974.
- Nemitz1965 (NOT in references.bib): W. Nemitz, "Implicative semi-lattices", Trans. Amer. Math. Soc. 117 (1965), 128-142.
- Kohler1981 (NOT in references.bib): P. Kohler, "Brouwerian semilattices", Trans. Amer. Math. Soc. 268 (1981), 103-126.
