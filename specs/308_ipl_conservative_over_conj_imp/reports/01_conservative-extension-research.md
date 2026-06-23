# Research Report: IPL Conservative over IPL⟨∧,→,⊤⟩

## Task

Prove that IPL is a conservative extension of IPL⟨∧,→,⊤⟩ for or-bot-free formulas:

```
if Derivable IntPropAxiom φ and φ.IsOrBotFree = true, then Derivable ConjImpAxiom φ
```

File: `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean`

## Template Analysis: `hilbertIplConservativeOverMpl`

The existing IPL-over-MPL conservative extension (`HilbertConservativeGlivenko.lean` L81-88) provides the exact proof template. Its structure:

```lean
theorem hilbertIplConservativeOverMpl {Atom : Type u} {φ : PL.Proposition Atom}
    (hBF : φ.IsBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@MinPropAxiom Atom) φ := by
  rw [MPL.hilbert_alg_complete]
  intro G _ v bot_val
  have hIPL := IPL.hilbert_alg_complete.mp h (H := WithBot G) (fun x => (v x : WithBot G))
  rw [coe_AlgEvaluate v bot_val φ hBF] at hIPL
  exact WithBot.coe_eq_coe.mp hIPL
```

Our theorem mirrors this exactly, replacing:

| IPL-over-MPL | IPL-over-ConjImp |
|---|---|
| `IsBotFree` | `IsOrBotFree` |
| `MinPropAxiom` | `ConjImpAxiom` |
| `GHAValid` (via `MPL.hilbert_alg_complete`) | `BrouwerianValid` (via `conjImp_brouwerian_iff`) |
| `WithBot G` free completion | `LowerSet B` free join completion |
| `coe_AlgEvaluate` embedding lemma | `brouwerianEmbeddingLemma` |
| `WithBot.coe_eq_coe.mp` injectivity | (embedded in `brouwerianEmbeddingLemma`) |

## Proof Chain

### Main Theorem: `hilbertIplConservativeOverConjImp`

**Statement:**
```lean
theorem hilbertIplConservativeOverConjImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@ConjImpAxiom Atom) φ
```

**Proof route (4 steps):**

1. **IPL completeness**: `IPL.hilbert_alg_complete.mp h` converts `Derivable IntPropAxiom φ` to `HAValid.{u,u} φ`. This means: for all `H : Type u` with `[HeytingAlgebra H]` and `v : Atom → H`, `AlgEvaluate v ⊥ φ = ⊤`.

2. **Show `BrouwerianValid.{u,u} φ`**: For any `B : Type u` with `[BrouwerianSemilattice B]` and `v : Atom → B`:
   - `LowerSet B : Type u` has `HeytingAlgebra` instance (via `CompletelyDistribLattice`)
   - Instantiate `HAValid` at `H := LowerSet B`, valuation `LowerSet.Iic ∘ v`
   - Get `AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = ⊤`
   - Apply `brouwerianEmbeddingLemma v φ hOBF` backward: `BrouwerianEvaluate v φ = ⊤`

3. **Brouwerian completeness**: `conjImp_brouwerian_complete hOBF` converts `BrouwerianValid.{u,u} φ` to `Derivable ConjImpAxiom φ`.

**Approximate Lean proof:**
```lean
theorem hilbertIplConservativeOverConjImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@ConjImpAxiom Atom) φ := by
  apply conjImp_brouwerian_complete hOBF
  intro B _ v
  have hHA := IPL.hilbert_alg_complete.mp h (H := LowerSet B) (LowerSet.Iic ∘ v)
  exact (brouwerianEmbeddingLemma v φ hOBF).mpr hHA
```

### Subsumption: `derivableConjImpOfDerivableInt` (reverse direction)

**Statement:**
```lean
theorem derivableConjImpOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ConjImpAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ
```

**Approach:** Axiom monotonicity. Each `ConjImpAxiom` constructor maps to a `MinPropAxiom` constructor (via `ConjImpAxiom.toMinPropAxiom`), and each `MinPropAxiom` constructor maps to an `IntPropAxiom` constructor (via `MinPropAxiom.toIntPropAxiom`). We need a generic `PL.liftDerivation` combinator (analogous to the modal `liftDerivation` in `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean`).

**Required helper (new):**
```lean
def PL.liftDerivation
    {Axioms1 Axioms2 : PL.Proposition Atom → Prop}
    (h_sub : ∀ φ, Axioms1 φ → Axioms2 φ)
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree Axioms1 Γ φ) :
    DerivationTree Axioms2 Γ φ :=
  match d with
  | .ax Γ φ h => .ax Γ φ (h_sub φ h)
  | .assumption Γ φ h => .assumption Γ φ h
  | .modus_ponens Γ φ ψ d₁ d₂ =>
      .modus_ponens Γ φ ψ (PL.liftDerivation h_sub d₁) (PL.liftDerivation h_sub d₂)
  | .weakening Γ Δ φ d h => .weakening Γ Δ φ (PL.liftDerivation h_sub d) h
```

Then:
```lean
theorem derivableConjImpOfDerivableInt {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@ConjImpAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) φ := by
  obtain ⟨d⟩ := h
  exact ⟨PL.liftDerivation (fun ψ hψ => hψ.toMinPropAxiom.toIntPropAxiom) d⟩
```

### Biconditional (optional but recommended)

```lean
theorem hilbertIplConservativeOverConjImp_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@ConjImpAxiom Atom) φ :=
  ⟨hilbertIplConservativeOverConjImp hOBF,
   derivableConjImpOfDerivableInt⟩
```

This parallels the `conjImp_brouwerian_iff` biconditional pattern.

### ND Corollary: `ipl_conservative_over_conjImp`

**Statement:**
```lean
theorem ipl_conservative_over_conjImp {Atom : Type u} [DecidableEq Atom]
    {A : PL.Proposition Atom}
    (hOBF : A.IsOrBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    Derivable (@ConjImpAxiom Atom) A :=
  hilbertIplConservativeOverConjImp hOBF (derivableInIplIffDerivableInt.mp h)
```

This follows the exact pattern of `ipl_conservative_over_mpl` (L188-192).

Note: `[DecidableEq Atom]` is required because `derivableInIplIffDerivableInt` requires it (same as the IPL-over-MPL corollary).

## Infrastructure Dependencies

All dependencies are complete:

| Component | Location | Status |
|---|---|---|
| `IPL.hilbert_alg_complete` | `HilbertCompleteness.lean` | Exists |
| `brouwerianEmbeddingLemma` | `FreeJoinCompletion.lean` (task 307) | Complete |
| `conjImp_brouwerian_complete` | `BrouwerianCompleteness.lean` (task 306) | Complete |
| `ConjImpAxiom` | `FragmentAxioms.lean` (task 305) | Complete |
| `IsOrBotFree` | `FragmentPredicates.lean` (task 302) | Complete |
| `ConjImpAxiom.toMinPropAxiom` | `FragmentAxioms.lean` | Exists |
| `MinPropAxiom.toIntPropAxiom` | `Axioms.lean` | Exists |
| `derivableInIplIffDerivableInt` | `HilbertConservativeGlivenko.lean` | Exists |
| `LowerSet.completelyDistribLattice` | Mathlib | Exists |
| `LowerSet.Iic_injective` | Mathlib | Exists |

## Import Analysis

The new file needs:
```lean
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion
```

`HilbertCompleteness` brings in `IPL.hilbert_alg_complete` and the Hilbert Lindenbaum infrastructure.
`BrouwerianCompleteness` brings in `conjImp_brouwerian_complete`, `ConjImpAxiom`, and `FragmentAxioms`.
`FreeJoinCompletion` brings in `brouwerianEmbeddingLemma`, `LowerSet`, and `FragmentPredicates`.

For the ND corollary, we additionally need the algebraic bridges:
```lean
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko
```

This brings in `derivableInIplIffDerivableInt`.

**Alternative:** The ConjImpConservative module could be structured as an additional import in the existing `HilbertConservativeGlivenko.lean` module (which already imports both `HilbertCompleteness` and `Conservative`). However, since the task specifies a separate file, we should create `ConjImpConservative.lean`.

## File Structure Plan

```lean
-- ConjImpConservative.lean

module

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.FreeJoinCompletion
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko

/-! # Conservative Extension: IPL over IPL⟨∧,→,⊤⟩ -/

-- Section 1: PL.liftDerivation (generic axiom monotonicity)
-- Section 2: hilbertIplConservativeOverConjImp (main theorem)
-- Section 3: derivableConjImpOfDerivableInt (subsumption direction)
-- Section 4: hilbertIplConservativeOverConjImp_iff (biconditional)
-- Section 5: ipl_conservative_over_conjImp (ND corollary)
```

## Universe Considerations

The proof chain requires careful universe alignment:

- `Atom : Type u` throughout
- `HAValid.{u, u}` quantifies over `H : Type u`
- `LowerSet B : Type u` when `B : Type u` (preserves universe)
- `BrouwerianValid.{u, u}` quantifies over `B : Type u`
- `conjImp_brouwerian_complete` has universe `{Atom : Type u}` and uses `BrouwerianValid.{u, u}`

Everything is universe-consistent.

## Potential Issues

1. **`LowerSet B` HeytingAlgebra instance path**: `LowerSet B` gets `HeytingAlgebra` through `CompletelyDistribLattice → Frame → HeytingAlgebra`. Lean's typeclass inference should handle this automatically. If it doesn't, we might need `@HeytingAlgebra.toGeneralizedHeytingAlgebra` or explicit instance annotations. The existing `FreeJoinCompletion.lean` already uses this chain without issues (it has `AlgEvaluate` over `LowerSet B`), so this is safe.

2. **`liftDerivation` namespace**: The PL `DerivationTree` has 4 constructors (no necessitation), unlike the modal one (5 constructors). The function is simpler but needs to be defined fresh since the types differ. It could be placed in the new file or as a general utility. Placing it in the new file is simpler for this task.

3. **Noncomputability**: `conjImp_brouwerian_complete` is in a `noncomputable section` (in `BrouwerianCompleteness.lean`). Our main theorem may need `noncomputable` too, depending on how Lean handles the transitivity. If so, wrap the theorem in a `noncomputable section`.

## Estimated Complexity

- **Main theorem** (`hilbertIplConservativeOverConjImp`): ~5 lines, straightforward chaining
- **Subsumption** (`derivableConjImpOfDerivableInt`): ~15 lines (including `liftDerivation` helper)
- **Biconditional**: ~3 lines
- **ND corollary**: ~3 lines
- **Module docstring + boilerplate**: ~40 lines
- **Total**: ~70-80 lines

This is a low-risk task. All building blocks exist and are verified. The proof is a direct chain of existing lemmas with no novel proof obligations.

## Tactic Survey

The main theorem proof uses only:
- `apply` (to invoke `conjImp_brouwerian_complete`)
- `intro` (to universally quantify over B, v)
- `have` (to chain `IPL.hilbert_alg_complete.mp`)
- `exact` (to close via `brouwerianEmbeddingLemma.mpr`)

No `simp`, `omega`, `aesop`, or `decide` needed. The `liftDerivation` helper uses structural recursion (`match`).
