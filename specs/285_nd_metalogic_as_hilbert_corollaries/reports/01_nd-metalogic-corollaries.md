# Research Report: Refactor ND Metalogic API to Hilbert-Primary Corollaries

**Task**: 285
**Session**: sess_1782187168_2b1b69_285
**Date**: 2026-06-22

## 1. Current State of ND Metalogic Files

### 1.1 Completeness.lean — ND Algebraic Completeness

**Path**: `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean`

**Declarations** (all in namespace `Cslib.Logic.PL`):

| Declaration | Kind | Signature Summary | Used By |
|---|---|---|---|
| `Theory.canonicalV` | def | `Theory Atom → Atom → LindenbaumAlgebra T` | Completeness proofs |
| `Theory.canonicalBotVal` | def | `Theory Atom → LindenbaumAlgebra T` | Completeness proofs |
| `Theory.canonicalBotVal_eq` | theorem | `[IsIntuitionistic T] → T.canonicalBotVal = ⊥` | `IPL.alg_complete` |
| `Theory.canonicalV_spec` | theorem | `AlgEvaluate T.canonicalV T.canonicalBotVal A = lindenbaumMk T A` | All completeness proofs |
| `Theory.tValid_canonicalV` | theorem | `AlgTValid T T.canonicalV T.canonicalBotVal` | `Theory.alg_complete` |
| `nd_alg_sound_aux` | theorem | Meet-formulation soundness (induction on derivation) | `nd_alg_sound` |
| `nd_alg_sound` | theorem | `DerivableIn T A → AlgEvaluate v bot_val A = ⊤` | All ND completeness |
| `lindenbaumMk_eq_top_iff` | theorem | `lindenbaumMk T A = ⊤ ↔ DerivableIn T A` | All ND completeness |
| `Theory.alg_complete` | theorem | `DerivableIn T A ↔ ∀ GHA ...` | Bridge theorems |
| `MPL.alg_complete` | theorem | `DerivableIn ∅ A ↔ ∀ GHA v bot_val, ...` | Bridge: `derivableInMplIffDerivableMin` |
| `IPL.alg_complete` | theorem | `DerivableIn IPL A ↔ ∀ HA v, ...` | Bridge: `derivableInIplIffDerivableInt`, and `ipl_conservative_over_mpl` |
| `alg_complete_classical` | theorem | `[IsIntuitionistic T] [IsClassical T] → DerivableIn T A ↔ ∀ BA v, ...` | Bridge: `derivableInCplIffDerivableProp`, and `glivenko` |

**Note**: All ND completeness theorems require `[DecidableEq Atom]`.

### 1.2 Conservative.lean — Bot-Free Analysis and Conservative Extension

**Path**: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`

**Declarations**:

| Declaration | Kind | Category | Used By |
|---|---|---|---|
| `Proposition.IsBotFree` | def | Algebraic infrastructure | `hilbertIplConservativeOverMpl`, `ipl_conservative_over_mpl` |
| `AlgEvaluate_botFree_independent` | theorem | Algebraic infrastructure | (available for downstream) |
| `GHAValid_implies_HAValid` | theorem | Validity subsumption | (available for downstream) |
| `HAValid_implies_BAValid` | theorem | Validity subsumption | (available for downstream) |
| `withBotHimp` | def | WithBot construction | `instHeytingAlgebraWithBot` |
| `instHeytingAlgebraWithBot` | instance | WithBot construction | `hilbertIplConservativeOverMpl`, `ipl_conservative_over_mpl` |
| `coe_AlgEvaluate` | theorem | Embedding lemma | `hilbertIplConservativeOverMpl`, `ipl_conservative_over_mpl` |
| `ipl_conservative_over_mpl` | theorem | **ND-primary** | **Target for replacement** |

**Key observation**: The algebraic infrastructure (`IsBotFree`, `instHeytingAlgebraWithBot`, `coe_AlgEvaluate`) is NOT ND-specific. These are used by both the ND and Hilbert proofs. Only `ipl_conservative_over_mpl` is the ND-primary theorem that should be replaced.

### 1.3 Glivenko.lean — Glivenko's Theorem

**Path**: `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`

**Declarations**:

| Declaration | Kind | Category | Used By |
|---|---|---|---|
| `evalR` (private) | abbrev | Algebraic infrastructure | `eval_regular_val` |
| `eval_regular_val` (private) | theorem | Algebraic infrastructure | `glivenko_algebraic` |
| `glivenko_algebraic` | theorem | Algebraic core | `hilbertGlivenko`, `glivenko` |
| `IsIntuitionistic (IPL ∪ CPL)` | instance | Theory instance | `glivenko`, `alg_complete_classical` |
| `IsClassical (IPL ∪ CPL)` | instance | Theory instance | `glivenko`, `alg_complete_classical` |
| `glivenko` | theorem | **ND-primary** | **Target for replacement** |

**Key observation**: The algebraic core (`glivenko_algebraic`) and the theory instances are NOT ND-specific. Only `glivenko` is the ND-primary theorem.

## 2. Downstream Dependencies

### 2.1 Import Graph

Files that import the three ND modules (excluding `Cslib.lean` barrel file):

| Module | Imported By |
|---|---|
| `Completeness.lean` | `Conservative.lean`, `Glivenko.lean`, `HilbertConservativeGlivenko.lean` |
| `Conservative.lean` | `HilbertConservativeGlivenko.lean` |
| `Glivenko.lean` | `HilbertConservativeGlivenko.lean` |

**No external downstream consumers**: No modal, temporal, bimodal, or other logic modules import any of the three ND files. The only file that imports them (beyond each other) is `HilbertConservativeGlivenko.lean`.

### 2.2 Theorem Name References

Outside `Semantics/Algebra/`:
- `Algebra.lean` (the parent module) mentions `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical` in documentation comments only.
- No Lean code outside the Algebra directory references any ND theorem by name.

### 2.3 Risk Assessment

**Zero external breakage risk**: Since no external modules import or reference these files, the refactoring is completely self-contained within the `Semantics/Algebra/` directory.

## 3. Bridge Availability Analysis

### 3.1 Task 284 Bridges

The algebraic bridges from `HilbertConservativeGlivenko.lean`:

| Bridge | Type | Dependencies |
|---|---|---|
| `derivableInMplIffDerivableMin` | `DerivableIn ∅ φ ↔ Derivable MinPropAxiom φ` | `MPL.alg_complete`, `MPL.hilbert_alg_complete` |
| `derivableInIplIffDerivableInt` | `DerivableIn IPL φ ↔ Derivable IntPropAxiom φ` | `IPL.alg_complete`, `IPL.hilbert_alg_complete` |
| `derivableInCplIffDerivableProp` | `DerivableIn (IPL ∪ CPL) φ ↔ Derivable PropositionalAxiom φ` | `alg_complete_classical`, `CPL.hilbert_alg_complete` |

**All three bridges depend on ND completeness**. They route through algebra as the common intermediate: ND completeness converts `DerivableIn T φ` to algebraic validity, and Hilbert completeness converts back.

### 3.2 Sufficiency for Corollary Derivation

Given these bridges, every existing ND theorem can be derived as a corollary:

| ND Theorem | Corollary Via | Already Exists? |
|---|---|---|
| `ipl_conservative_over_mpl` | `derivableInIplIffDerivableInt` + `hilbertIplConservativeOverMpl` + `derivableInMplIffDerivableMin` | Yes: `iplConservativeOverMpl'` |
| `glivenko` | `derivableInCplIffDerivableProp` + `hilbertGlivenko` + `derivableInIplIffDerivableInt` | Yes: `glivenko'` |

### 3.3 ND Completeness as Internal Dependency

The ND completeness theorems (`MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical`) are used ONLY by:
1. The bridge theorems themselves (to connect `DerivableIn` to `Derivable`)
2. The original ND-primary conservative/Glivenko proofs (which will be replaced)

The ND completeness theorems CANNOT be removed because the bridges depend on them. However, the ND completeness theorems are valuable in their own right as characterizations of the ND system.

## 4. Replacement Strategy

### 4.1 What Changes

| File | Action | Details |
|---|---|---|
| `Conservative.lean` | **Replace ND-primary proof** | `ipl_conservative_over_mpl` gets corollary proof body routing through bridges |
| `Glivenko.lean` | **Replace ND-primary proof** | `glivenko` gets corollary proof body routing through bridges |
| `HilbertConservativeGlivenko.lean` | **Promote as primary** | `iplConservativeOverMpl'` and `glivenko'` become the authoritative corollary names; the prime-suffixed versions become aliases or are removed |
| `Completeness.lean` | **Keep (unchanged)** | ND completeness theorems needed by bridge proofs |
| `Algebra.lean` | **Update documentation** | Reflect Hilbert-primary architecture |

### 4.2 Signature Compatibility

The corollary versions have identical signatures to the originals:

**Conservative extension**:
- Original: `ipl_conservative_over_mpl {A} (hBF : A.IsBotFree = true) (h : DerivableIn IPL A) : DerivableIn ∅ A`
- Corollary: `iplConservativeOverMpl' {A} (hBF : A.IsBotFree = true) (h : DerivableIn IPL A) : DerivableIn ∅ A`

Both require `[DecidableEq Atom]` (section variable). The signatures are type-compatible; `MPL` is definitionally `∅`.

**Glivenko**:
- Original: `glivenko {A} (h : DerivableIn (IPL ∪ CPL) A) : DerivableIn IPL (¬¬A)`
- Corollary: `glivenko' {A} (h : DerivableIn (IPL ∪ CPL) A) : DerivableIn IPL (¬¬A)`

Identical signatures. Both require `[DecidableEq Atom]`.

**Conclusion**: The replacement is signature-compatible. No downstream breakage possible since no external modules reference these names.

### 4.3 Naming Strategy

Two options:

**Option A (Recommended): In-Place Replacement**
- Replace the proof body of `ipl_conservative_over_mpl` in Conservative.lean with the corollary proof (routing through bridges)
- Replace the proof body of `glivenko` in Glivenko.lean with the corollary proof
- Remove `iplConservativeOverMpl'` and `glivenko'` from HilbertConservativeGlivenko.lean (they become the originals)
- Update docstrings to indicate "derived as corollary of Hilbert-primary version"

**Option B: Rename and Redirect**
- Keep original names as deprecated aliases pointing to the Hilbert-derived versions
- More complex, no clear benefit since no external consumers exist

### 4.4 Import Changes

For Option A:
- **Conservative.lean** must add `import HilbertConservativeGlivenko` (for bridge + Hilbert theorem) -- BUT this creates a circular import since HilbertConservativeGlivenko already imports Conservative
- **Resolution**: Move the bridge theorems to a separate module, OR keep the algebraic infrastructure in Conservative.lean and move `ipl_conservative_over_mpl` to HilbertConservativeGlivenko.lean

**Better approach**: Keep the algebraic infrastructure (IsBotFree, coe_AlgEvaluate, etc.) in Conservative.lean, remove `ipl_conservative_over_mpl` from Conservative.lean, and place the corollary version in HilbertConservativeGlivenko.lean. Similarly for Glivenko: keep `glivenko_algebraic` in Glivenko.lean, remove `glivenko`, place corollary in HilbertConservativeGlivenko.lean.

This avoids circular imports entirely.

### 4.5 Revised Module Layout

After refactoring:

| Module | Contains | Role |
|---|---|---|
| `Completeness.lean` | ND soundness, canonical valuation, ND completeness (`alg_complete`, etc.) | ND completeness (unchanged, needed by bridges) |
| `Conservative.lean` | `IsBotFree`, `AlgEvaluate_botFree_independent`, `GHAValid_implies_HAValid`, `HAValid_implies_BAValid`, `instHeytingAlgebraWithBot`, `coe_AlgEvaluate` | Algebraic infrastructure only (remove `ipl_conservative_over_mpl`) |
| `Glivenko.lean` | `glivenko_algebraic`, `IsIntuitionistic (IPL ∪ CPL)`, `IsClassical (IPL ∪ CPL)` | Algebraic core + theory instances (remove `glivenko`) |
| `HilbertConservativeGlivenko.lean` | Hilbert-primary theorems + bridges + ND corollaries (`ipl_conservative_over_mpl`, `glivenko`) | Unified Hilbert-primary + corollary module |

### 4.6 Naming in Unified Module

In `HilbertConservativeGlivenko.lean`:
- `hilbertIplConservativeOverMpl` (Hilbert-primary, already exists)
- `hilbertGlivenko` (Hilbert-primary, already exists)
- `derivableInMplIffDerivableMin` (bridge, already exists)
- `derivableInIplIffDerivableInt` (bridge, already exists)
- `derivableInCplIffDerivableProp` (bridge, already exists)
- `ipl_conservative_over_mpl` (ND corollary, MOVED here, replaces `iplConservativeOverMpl'`)
- `glivenko` (ND corollary, MOVED here, replaces `glivenko'`)

The original `iplConservativeOverMpl'` and `glivenko'` are removed. The canonical ND names (`ipl_conservative_over_mpl`, `glivenko`) now live in HilbertConservativeGlivenko.lean with corollary proofs.

## 5. Documentation Updates

### 5.1 ProofSystem.lean

`Cslib/Foundations/Logic/ProofSystem.lean` contains the typeclass hierarchy documentation. It currently says:

> This module defines the **interface** only. Concrete instances require derivation trees (not yet ported) and are future work.

This should be updated to note that:
- Tasks 281-284 have established Hilbert-level completeness, conservative extension, and Glivenko
- The Hilbert system is now the primary derivation system with ND results derived as corollaries
- The proof system hierarchy (MinimalHilbert, IntuitionisticHilbert, ClassicalHilbert) has working instances

### 5.2 Algebra.lean (Parent Module)

The documentation in `Cslib/Logics/Propositional/Semantics/Algebra.lean` at lines 49-53 references `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical` as the tier-specific results. After refactoring:
- These ND completeness theorems still exist (unchanged)
- Add mention of the Hilbert-primary counterparts: `MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete`
- Note the architectural decision: Hilbert-primary theorems do not require `[DecidableEq Atom]`

### 5.3 Conservative.lean and Glivenko.lean

Update module docstrings to:
- Remove the ND-primary theorem from the "Main Results" section
- Note that the conservative extension / Glivenko theorems are now in `HilbertConservativeGlivenko.lean`
- Keep the algebraic infrastructure documentation

### 5.4 HilbertConservativeGlivenko.lean

Update module docstring to:
- Add the ND corollaries to the main results section
- Note the Hilbert-primary architecture: theorems proved directly in Hilbert, ND versions as corollaries
- Document the import relationship

## 6. Completeness Corollaries

### 6.1 Can ND Completeness Be Derived from Hilbert Completeness?

The ND completeness theorems (`MPL.alg_complete`, `IPL.alg_complete`, etc.) are NOT directly derivable from Hilbert completeness alone, because:
1. The ND Lindenbaum algebra is a different construction from the Hilbert Lindenbaum algebra
2. ND soundness (`nd_alg_sound`) requires structural induction on ND derivation trees
3. The canonical valuation for ND uses `LindenbaumAlgebra T` (ND quotient), not `HilbertLindenbaumAlgebra Axioms`

However, they COULD be derived via: Hilbert completeness + the `hilbert_iff_nd_*` direct bridges from `Equivalence.lean`, but this would require showing that `AxiomTheory Axioms` equals the relevant named theory (e.g., `AxiomTheory MinPropAxiom = ∅`), which may not hold definitionally.

**Recommendation**: Keep ND completeness as independently proved. The goal of task 285 is to make the conservative extension and Glivenko results Hilbert-derived corollaries, not to eliminate ND completeness entirely.

### 6.2 ND Completeness Theorems Not Targeted for Replacement

These ND completeness theorems should be kept unchanged:
- `Theory.alg_complete` (general ND completeness)
- `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical` (tier-specific ND completeness)
- `nd_alg_sound`, `nd_alg_sound_aux` (ND soundness)
- `lindenbaumMk_eq_top_iff` (Lindenbaum characterization)

They are needed by the bridge theorems and are valuable in their own right.

## 7. CI Verification Plan

After refactoring, run:
1. `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` -- verify truncated module compiles
2. `lake build Cslib.Logics.Propositional.Semantics.Algebra.Glivenko` -- verify truncated module compiles
3. `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko` -- verify unified module compiles
4. `lake build` -- full project build
5. `lake test` -- run test suite
6. `lake exe checkInitImports` -- verify all imports
7. `lake exe lint-style` -- style check

## 8. Risk Assessment

| Risk | Likelihood | Mitigation |
|---|---|---|
| Circular import | Low | Move ND theorems to HilbertConservativeGlivenko (imports flow one way) |
| Signature mismatch | None | Signatures verified identical |
| External breakage | None | No external consumers found |
| Name collision | Low | Use canonical names (`ipl_conservative_over_mpl`, `glivenko`) |
| `[DecidableEq Atom]` mismatch | None | All ND corollaries already require it |
| Documentation staleness | Medium | Explicit documentation update phase in plan |

## 9. Summary of Recommended Refactoring

1. **Remove** `ipl_conservative_over_mpl` from `Conservative.lean`
2. **Remove** `glivenko` from `Glivenko.lean`
3. **Remove** `iplConservativeOverMpl'` and `glivenko'` from `HilbertConservativeGlivenko.lean`
4. **Add** `ipl_conservative_over_mpl` to `HilbertConservativeGlivenko.lean` with corollary proof body (routing through bridges)
5. **Add** `glivenko` to `HilbertConservativeGlivenko.lean` with corollary proof body
6. **Update** docstrings in `Conservative.lean`, `Glivenko.lean`, `HilbertConservativeGlivenko.lean`, `Algebra.lean`
7. **Update** `ProofSystem.lean` documentation to reflect Hilbert-primary architecture
8. **Keep** `Completeness.lean` unchanged (needed by bridges)
9. **Run** full CI pipeline to verify
