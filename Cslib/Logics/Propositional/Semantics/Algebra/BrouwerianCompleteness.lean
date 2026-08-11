/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.Brouwerian
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompletenessGeneric

/-! # Brouwerian Algebraic Soundness and Completeness for IPL⟨∧,→,⊤⟩

This module proves soundness and completeness of the conjunctive-implicational fragment
IPL⟨∧,→,⊤⟩ with respect to Brouwerian semilattices.

**Soundness** (`conjImp_brouwerian_soundness_derivable`): Every `ConjImpAxiom`-derivable
formula evaluates to `⊤` in every Brouwerian semilattice under every variable assignment.

**Completeness** (`conjImp_brouwerian_completeness`): Restricted to `IsOrBotFree` formulas, if
a formula evaluates to `⊤` in every Brouwerian semilattice then it is `ConjImpAxiom`-derivable.
The restriction is necessary because `BrouwerianEvaluate` maps `bot` and `or` to `⊤`, making
those connectives vacuously valid, while `ConjImpAxiom` has no EFQ or disjunction axioms.

## Proof Strategy

**Soundness** follows by case analysis on `ConjImpAxiom` constructors using
`BrouwerianSemilattice` lemmas (`le_himp_iff`, `himp_eq_top_iff`, `inf_le_left`, etc.),
then by induction on the derivation tree.

**Completeness** uses the **Hilbert Lindenbaum algebra** `HilbertLindenbaumAlgebra ConjImpAxiom`,
which carries a `BrouwerianSemilattice` instance. The truth lemma
`brouwerianCanonicalV_spec_generic` (from `BrouwerianCompletenessGeneric`) supplies the key
equation `BrouwerianEvaluate (canonicalV ConjImpAxiom) φ = hilbertLindenbaumMk φ` for
`IsOrBotFree` formulas.

## Main Results

- `conjImp_brouwerian_soundness_derivable`: `Derivable ConjImpAxiom φ → BrouwerianValid φ`
- `conjImp_brouwerian_completeness`: `IsOrBotFree φ → BrouwerianValid φ → Derivable ConjImpAxiom φ`
- `conjImp_brouwerian_iff`: `IsOrBotFree φ → (Derivable ConjImpAxiom φ ↔ BrouwerianValid φ)`

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type*}

/-! ## Brouwerian Soundness -/

/-- Every axiom of the conjunctive-implicational fragment is valid in every Brouwerian
semilattice: each `ConjImpAxiom` constructor evaluates to `⊤` under any assignment. -/
theorem conjImp_brouwerian_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : ConjImpAxiom φ) : BrouwerianValid φ := by
  intro H _ v
  cases h_ax with
  | implyK φ ψ =>
    -- implyK: φ → (ψ → φ); need φ_h ⇨ (ψ_h ⇨ φ_h) = ⊤
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
    exact inf_le_left
  | implyS φ ψ χ =>
    -- implyS: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff,
        BrouwerianSemilattice.le_himp_iff]
    -- Goal: ((a ⇨ b ⇨ c) ⊓ (a ⇨ b)) ⊓ a ≤ c
    have hb : (BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ ⇨ BrouwerianEvaluate v χ) ⊓
              (BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ) ⊓
              BrouwerianEvaluate v φ ≤ BrouwerianEvaluate v ψ :=
      (inf_le_inf_right _ inf_le_right).trans BrouwerianSemilattice.himp_inf_le
    have hbc : (BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ ⇨ BrouwerianEvaluate v χ) ⊓
               (BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ) ⊓
               BrouwerianEvaluate v φ ≤
               BrouwerianEvaluate v ψ ⇨ BrouwerianEvaluate v χ :=
      (inf_le_inf_right _ inf_le_left).trans BrouwerianSemilattice.himp_inf_le
    exact (le_inf hbc hb).trans BrouwerianSemilattice.himp_inf_le
  | andI φ ψ =>
    -- andI: φ → (ψ → φ ∧ ψ); need φ_h ⇨ (ψ_h ⇨ φ_h ⊓ ψ_h) = ⊤
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
  | andE1 φ ψ =>
    -- andE1: (φ ∧ ψ) → φ; need φ_h ⊓ ψ_h ⇨ φ_h = ⊤
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact inf_le_left
  | andE2 φ ψ =>
    -- andE2: (φ ∧ ψ) → ψ; need φ_h ⊓ ψ_h ⇨ ψ_h = ⊤
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact inf_le_right

/-- Soundness at the derivation tree level: if `Γ ⊢ φ` via `ConjImpAxiom` and every formula
in `Γ` evaluates to `⊤`, then `φ` evaluates to `⊤` in every Brouwerian semilattice. -/
theorem conjImp_brouwerian_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree ConjImpAxiom Γ φ)
    {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BrouwerianEvaluate v ψ = ⊤) :
    BrouwerianEvaluate v φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact conjImp_brouwerian_axiom_sound h_ax H v
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := conjImp_brouwerian_soundness d₁ v h_ctx
    have h2 := conjImp_brouwerian_soundness d₂ v h_ctx
    simp only [← Proposition.imp_def, BrouwerianEvaluate] at h1
    rw [BrouwerianSemilattice.himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact conjImp_brouwerian_soundness d' v
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Brouwerian Soundness for IPL⟨∧,→,⊤⟩**: Every `ConjImpAxiom`-derivable formula is
Brouwerian-valid. -/
theorem conjImp_brouwerian_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable ConjImpAxiom φ) : BrouwerianValid φ := by
  intro H _ v
  obtain ⟨d⟩ := h
  exact conjImp_brouwerian_soundness d v (fun _ h => nomatch h)

/-! ## Completeness Theorem -/

/-- **Brouwerian Completeness for IPL⟨∧,→,⊤⟩** (restricted to `IsOrBotFree` formulas):
if an or-bot-free formula is valid in every Brouwerian semilattice, then it is
`ConjImpAxiom`-derivable.

The proof instantiates `BrouwerianValid` at the generic `HilbertLindenbaumAlgebra ConjImpAxiom`,
which carries a `BrouwerianSemilattice` instance. The truth lemma
`brouwerianCanonicalV_spec_generic` rewrites the evaluation into a Lindenbaum quotient class,
and `hilbertLindenbaumMk_eq_top_iff` extracts derivability.

The restriction to `IsOrBotFree` is necessary: `bot` is vacuously Brouwerian-valid
(since `BrouwerianEvaluate v bot = ⊤` by definition) but not derivable in `ConjImpAxiom`
(no EFQ axiom is available).

This theorem is public and is the completeness result for the `IsOrBotFree` fragment,
complementing the `FragmentConservativity` instance `fragmentConservativityConjImp`
(`FragmentConservativityInstances.lean`). -/
theorem conjImp_brouwerian_completeness {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrBotFree = true)
    (h : BrouwerianValid.{u, u} φ) :
    Derivable ConjImpAxiom φ := by
  have hLind : BrouwerianEvaluate (canonicalV ConjImpAxiom) φ = ⊤ :=
    h (HilbertLindenbaumAlgebra ConjImpAxiom) (canonicalV ConjImpAxiom)
  rw [brouwerianCanonicalV_spec_generic φ hfrag] at hLind
  exact hilbertLindenbaumMk_eq_top_iff.mp hLind

/-- **Brouwerian Biconditional for IPL⟨∧,→,⊤⟩**: For or-bot-free formulas, derivability and
Brouwerian validity coincide. -/
theorem conjImp_brouwerian_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrBotFree = true) :
    Derivable ConjImpAxiom φ ↔ BrouwerianValid.{u, u} φ :=
  ⟨conjImp_brouwerian_soundness_derivable,
   conjImp_brouwerian_completeness hfrag⟩

end Cslib.Logic.PL

end

end
