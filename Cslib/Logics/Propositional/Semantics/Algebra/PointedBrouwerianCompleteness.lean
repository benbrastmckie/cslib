/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module


public import Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerian
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompletenessGeneric

/-! # Pointed Brouwerian Algebraic Soundness and Completeness for IPL⟨∧,→,⊥,⊤⟩

This module proves soundness and completeness of the conjunctive-implicational-bot fragment
IPL⟨∧,→,⊥,⊤⟩ with respect to pointed Brouwerian semilattices (`BrouwerianSemilattice +
OrderBot`).

**Soundness** (`conjImpBot_pointedBrouwerian_soundness_derivable`): Every
`ConjImpBotAxiom`-derivable formula evaluates to `⊤` in every pointed Brouwerian semilattice
under every variable assignment.

**Completeness** (`conjImpBot_pointedBrouwerian_completeness`): Restricted to `IsOrFree` formulas,
if a formula evaluates to `⊤` in every pointed Brouwerian semilattice then it is
`ConjImpBotAxiom`-derivable. The restriction to `IsOrFree` is necessary because
`PointedBrouwerianEvaluate` maps `or` to `⊤`, making disjunction vacuously valid, while
`ConjImpBotAxiom` has no disjunction axioms.

## Proof Strategy

**Soundness** follows by case analysis on `ConjImpBotAxiom` constructors. The five
ConjImp cases are dispatched via the generic schema lemmas
(`brouwerianBot_implyK_sound`, etc.) using the bridge
`PointedBrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊥ φ`
(`pointedBrouwerianEvaluate_eq_botBot`). The efq case uses `HasInitialBot.initialArrow`,
making explicit that ex falso quodlibet is the universal property of the initial object
(the canonical `⊥` is initial via `instHasInitialBotOfHasLeastBot`).

**Completeness** instantiates `PointedBrouwerianValid` at the **Hilbert Lindenbaum algebra**
`HilbertLindenbaumAlgebra ConjImpBotAxiom`, which carries both a `BrouwerianSemilattice`
instance (from `hilbertLindenbaumBSL`) and a local `OrderBot` instance (built inline via the
EFQ axiom: `bot_le = hilbertBotEDeriv (.efq ·)`). The truth lemma
`brouwerianBotCanonicalV_spec` (from `BrouwerianCompletenessGeneric`) rewrites the evaluation
into a Lindenbaum quotient class, and `hilbertLindenbaumMk_eq_top_iff` extracts derivability.

## Main Results

- `conjImpBot_pointedBrouwerian_axiom_sound`: every `ConjImpBotAxiom` evaluates to `⊤`
- `conjImpBot_pointedBrouwerian_soundness_derivable`: soundness
- `conjImpBot_pointedBrouwerian_completeness`: completeness for `IsOrFree` formulas
- `conjImpBot_pointedBrouwerian_iff`: biconditional for `IsOrFree` formulas

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

/-! ## Pointed Brouwerian Soundness -/

/-- Every axiom of the conjunctive-implicational-bot fragment is valid in every pointed
Brouwerian semilattice: each `ConjImpBotAxiom` constructor evaluates to `⊤`.

The five ConjImp cases are routed through the generic schema soundness lemmas
(`brouwerianBot_implyK_sound`, etc.) via the bridge
`PointedBrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊥ φ`. The efq case is handled
separately: `⊥ ⇨ φ_val = ⊤` follows from `HasInitialBot.initialArrow` — the canonical `⊥`
is an initial object (via `instHasInitialBotOfHasLeastBot ∘ instHasLeastBotOrderBot`), and
EFQ is the universal property: the unique arrow `⊥ → a` exists for every `a`. -/
theorem conjImpBot_pointedBrouwerian_axiom_sound {Atom : Type*} {φ : PL.Proposition Atom}
    (h_ax : ConjImpBotAxiom φ) : PointedBrouwerianValid φ := by
  intro H _ _ v
  rw [pointedBrouwerianEvaluate_eq_botBot]
  cases h_ax with
  | implyK φ ψ => exact brouwerianBot_implyK_sound v ⊥ φ ψ
  | implyS φ ψ χ => exact brouwerianBot_implyS_sound v ⊥ φ ψ χ
  | andI φ ψ => exact brouwerianBot_andI_sound v ⊥ φ ψ
  | andE1 φ ψ => exact brouwerianBot_andE1_sound v ⊥ φ ψ
  | andE2 φ ψ => exact brouwerianBot_andE2_sound v ⊥ φ ψ
  | efq φ =>
    -- efq: ⊥ → φ; the canonical ⊥ is an initial object (HasInitialBot (⊥ : H) via
    -- instHasInitialBotOfHasLeastBot ∘ instHasLeastBotOrderBot), and
    -- HasInitialBot.initialArrow _ provides the unique arrow ⊥ → φ_val.
    -- This realizes "ex falso quodlibet = universal property of the initial object".
    simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_bot]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact HasInitialBot.initialArrow _

/-- Soundness at the derivation tree level for `ConjImpBotAxiom`. -/
theorem conjImpBot_pointedBrouwerian_soundness
    {Atom : Type*}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree ConjImpBotAxiom Γ φ)
    {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → PointedBrouwerianEvaluate v ψ = ⊤) :
    PointedBrouwerianEvaluate v φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact conjImpBot_pointedBrouwerian_axiom_sound h_ax H v
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := conjImpBot_pointedBrouwerian_soundness d₁ v h_ctx
    have h2 := conjImpBot_pointedBrouwerian_soundness d₂ v h_ctx
    simp only [← Proposition.imp_def, PointedBrouwerianEvaluate_imp] at h1
    rw [BrouwerianSemilattice.himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact conjImpBot_pointedBrouwerian_soundness d' v
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Pointed Brouwerian Soundness for IPL⟨∧,→,⊥,⊤⟩**: Every `ConjImpBotAxiom`-derivable
formula is pointed Brouwerian-valid. -/
theorem conjImpBot_pointedBrouwerian_soundness_derivable {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable ConjImpBotAxiom φ) : PointedBrouwerianValid φ := by
  intro H _ _ v
  obtain ⟨d⟩ := h
  exact conjImpBot_pointedBrouwerian_soundness d v (fun _ h => nomatch h)

/-! ## Completeness Theorem -/

/-- **Pointed Brouwerian Completeness for IPL⟨∧,→,⊥,⊤⟩** (restricted to `IsOrFree` formulas):
if an or-free formula is valid in every pointed Brouwerian semilattice, then it is
`ConjImpBotAxiom`-derivable.

The proof instantiates `PointedBrouwerianValid` at the generic
`HilbertLindenbaumAlgebra ConjImpBotAxiom`, endowed with a local `OrderBot` instance:
`bot = canonicalBotVal ConjImpBotAxiom = [⊥]` and `bot_le` by EFQ.
The bridge `pointedBrouwerianEvaluate_eq_botBot` rewrites the evaluation to
`BrouwerianBotEvaluate (canonicalV _) (canonicalBotVal _) φ`, which the truth lemma
`brouwerianBotCanonicalV_spec` identifies as `hilbertLindenbaumMk φ`. Derivability follows
via `hilbertLindenbaumMk_eq_top_iff`.

The restriction to `IsOrFree` is necessary: `a ∨ b` is vacuously pointed Brouwerian-valid
(since `PointedBrouwerianEvaluate v (or a b) = ⊤` by definition) but `ConjImpBotAxiom`
has no disjunction axioms. -/
theorem conjImpBot_pointedBrouwerian_completeness {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrFree = true)
    (h : PointedBrouwerianValid.{u, u} φ) :
    Derivable ConjImpBotAxiom φ := by
  -- Build OrderBot on HilbertLindenbaumAlgebra ConjImpBotAxiom via the EFQ axiom.
  -- bot = [⊥] = canonicalBotVal ConjImpBotAxiom; bot_le is ex falso quodlibet.
  letI : OrderBot (HilbertLindenbaumAlgebra (@ConjImpBotAxiom Atom)) :=
    { bot := canonicalBotVal (@ConjImpBotAxiom Atom)
      bot_le := fun x => by
        obtain ⟨A, rfl⟩ := Quotient.exists_rep x
        exact hilbertBotEDeriv (fun φ => .efq φ) (assumption_deriv List.mem_cons_self) }
  -- Instantiate PointedBrouwerianValid at the Lindenbaum algebra
  have hLind : PointedBrouwerianEvaluate (canonicalV ConjImpBotAxiom) φ = ⊤ :=
    h (HilbertLindenbaumAlgebra ConjImpBotAxiom) (canonicalV ConjImpBotAxiom)
  -- Bridge: ⊥ = canonicalBotVal ConjImpBotAxiom by the OrderBot definition above
  have hbot : (⊥ : HilbertLindenbaumAlgebra (@ConjImpBotAxiom Atom)) =
      canonicalBotVal (@ConjImpBotAxiom Atom) := rfl
  rw [pointedBrouwerianEvaluate_eq_botBot, hbot, brouwerianBotCanonicalV_spec φ hfrag] at hLind
  exact hilbertLindenbaumMk_eq_top_iff.mp hLind

/-- **Pointed Brouwerian Biconditional for IPL⟨∧,→,⊥,⊤⟩**: For or-free formulas,
derivability and pointed Brouwerian validity coincide. -/
theorem conjImpBot_pointedBrouwerian_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrFree = true) :
    Derivable ConjImpBotAxiom φ ↔ PointedBrouwerianValid.{u, u} φ :=
  ⟨conjImpBot_pointedBrouwerian_soundness_derivable,
   conjImpBot_pointedBrouwerian_completeness hfrag⟩

end Cslib.Logic.PL

end

end
