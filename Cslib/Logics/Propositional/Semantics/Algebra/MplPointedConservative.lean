/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module


public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianBot
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompletenessGeneric

/-! # Arbitrary-Point Brouwerian Algebraic Soundness and Completeness for MPL⟨∧,→,⊥,⊤⟩

This module proves soundness and completeness of the conjunctive-implicational-bot fragment
MPL⟨∧,→,⊥,⊤⟩ with respect to Brouwerian semilattices with an **arbitrary distinguished
element** (`BrouwerianSemilattice` + free `bot_val : H`, no `OrderBot`).

The key distinction from `PointedBrouwerianCompleteness.lean` is that `ConjImpBotMinAxiom`
has **no ex falso** (`efq`) axiom. Therefore `⊥` is a free constant — no axiom governs it
— and its semantic image is a universally-quantified free element `bot_val : H` rather than
the algebraic `OrderBot` least element.

**Soundness** (`conjImpBotMin_brouwerianBot_soundness_derivable`): Every
`ConjImpBotMinAxiom`-derivable formula evaluates to `⊤` in every Brouwerian semilattice
under every variable assignment and every choice of `bot_val`.

**Completeness** (`conjImpBotMin_brouwerianBot_completeness`): Restricted to `IsOrFree` formulas,
if a formula evaluates to `⊤` in every Brouwerian semilattice with every `bot_val`, then it
is `ConjImpBotMinAxiom`-derivable.

## Proof Strategy

**Soundness** dispatches each `ConjImpBotMinAxiom` constructor to the generic per-schema
lemmas `brouwerianBot_implyK_sound`, `brouwerianBot_implyS_sound`, `brouwerianBot_andI_sound`,
`brouwerianBot_andE1_sound`, `brouwerianBot_andE2_sound` from `BrouwerianCompletenessGeneric`.
There are five cases (no efq case since `ConjImpBotMinAxiom` has no ex falso axiom).

**Completeness** delegates directly to the generic `brouwerianBot_completeness` from
`BrouwerianCompletenessGeneric`, which uses the `HilbertLindenbaumAlgebra ConjImpBotMinAxiom`
as the canonical model (with `canonicalBotVal = [⊥]`). The `ConjImpAxioms` instance for
`ConjImpBotMinAxiom` (from `FragmentAxioms`) unlocks the generic machinery.

## Main Results

- `conjImpBotMin_brouwerianBot_axiom_sound`: every `ConjImpBotMinAxiom` evaluates to `⊤`.
- `conjImpBotMin_brouwerianBot_soundness`: derivation-tree soundness.
- `conjImpBotMin_brouwerianBot_soundness_derivable`: soundness.
- `conjImpBotMin_brouwerianBot_completeness`: completeness for `IsOrFree` formulas.
- `conjImpBotMin_brouwerianBot_iff`: biconditional for `IsOrFree` formulas.

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

/-! ## ConjImpBotMin Brouwerian Soundness -/

/-- Every axiom of the conjunctive-implicational-bot-min fragment is valid in every Brouwerian
semilattice with any choice of `bot_val`: each `ConjImpBotMinAxiom` constructor evaluates to
`⊤`. There is no efq case since `ConjImpBotMinAxiom` has no ex falso.

The five cases are dispatched to the generic per-schema lemmas
`brouwerianBot_implyK_sound`, `brouwerianBot_implyS_sound`, `brouwerianBot_andI_sound`,
`brouwerianBot_andE1_sound`, `brouwerianBot_andE2_sound` from `BrouwerianCompletenessGeneric`. -/
theorem conjImpBotMin_brouwerianBot_axiom_sound {Atom : Type*} {φ : PL.Proposition Atom}
    (h_ax : ConjImpBotMinAxiom φ) : BrouwerianBotValid φ := by
  intro H _ v bot_val
  cases h_ax with
  | implyK φ ψ => exact brouwerianBot_implyK_sound v bot_val φ ψ
  | implyS φ ψ χ => exact brouwerianBot_implyS_sound v bot_val φ ψ χ
  | andI φ ψ => exact brouwerianBot_andI_sound v bot_val φ ψ
  | andE1 φ ψ => exact brouwerianBot_andE1_sound v bot_val φ ψ
  | andE2 φ ψ => exact brouwerianBot_andE2_sound v bot_val φ ψ

/-- Soundness at the derivation tree level for `ConjImpBotMinAxiom`. -/
theorem conjImpBotMin_brouwerianBot_soundness
    {Atom : Type*}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree ConjImpBotMinAxiom Γ φ)
    {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BrouwerianBotEvaluate v bot_val ψ = ⊤) :
    BrouwerianBotEvaluate v bot_val φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact conjImpBotMin_brouwerianBot_axiom_sound h_ax H v bot_val
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := conjImpBotMin_brouwerianBot_soundness d₁ v bot_val h_ctx
    have h2 := conjImpBotMin_brouwerianBot_soundness d₂ v bot_val h_ctx
    simp only [← Proposition.imp_def, BrouwerianBotEvaluate_imp] at h1
    rw [BrouwerianSemilattice.himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact conjImpBotMin_brouwerianBot_soundness d' v bot_val
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Free-Bot Brouwerian Soundness for MPL⟨∧,→,⊥,⊤⟩**: Every `ConjImpBotMinAxiom`-derivable
formula is valid in every Brouwerian semilattice with any choice of `bot_val`. -/
theorem conjImpBotMin_brouwerianBot_soundness_derivable {Atom : Type*}
    {φ : PL.Proposition Atom}
    (h : Derivable ConjImpBotMinAxiom φ) : BrouwerianBotValid φ := by
  intro H _ v bot_val
  obtain ⟨d⟩ := h
  exact conjImpBotMin_brouwerianBot_soundness d v bot_val (fun _ h => nomatch h)

/-! ## Completeness Theorem -/

/-- **Free-Bot Brouwerian Completeness for MPL⟨∧,→,⊥,⊤⟩** (restricted to `IsOrFree` formulas):
if an or-free formula is valid in every Brouwerian semilattice with every choice of `bot_val`,
then it is `ConjImpBotMinAxiom`-derivable.

The proof is a corollary of the generic `brouwerianBot_completeness` from
`BrouwerianCompletenessGeneric`, which instantiates `BrouwerianBotValid` at the
`HilbertLindenbaumAlgebra ConjImpBotMinAxiom` (with `canonicalBotVal = [⊥]`), applies the
truth lemma `brouwerianBotCanonicalV_spec`, and closes with `hilbertLindenbaumMk_eq_top_iff`.
The `ConjImpAxioms` instance for `ConjImpBotMinAxiom` (from `FragmentAxioms`) unlocks this.

The restriction to `IsOrFree` is necessary: `a ∨ b` is vacuously valid (since
`BrouwerianBotEvaluate v bot_val (or a b) = ⊤` by definition) but `ConjImpBotMinAxiom`
has no disjunction axioms. -/
theorem conjImpBotMin_brouwerianBot_completeness {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrFree = true)
    (h : BrouwerianBotValid.{u, u} φ) :
    Derivable ConjImpBotMinAxiom φ :=
  brouwerianBot_completeness hfrag h

/-- **Free-Bot Brouwerian Biconditional for MPL⟨∧,→,⊥,⊤⟩**: For or-free formulas,
derivability and free-bot Brouwerian validity coincide. -/
theorem conjImpBotMin_brouwerianBot_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrFree = true) :
    Derivable ConjImpBotMinAxiom φ ↔ BrouwerianBotValid.{u, u} φ :=
  ⟨conjImpBotMin_brouwerianBot_soundness_derivable,
   conjImpBotMin_brouwerianBot_completeness hfrag⟩

end Cslib.Logic.PL

end

end
