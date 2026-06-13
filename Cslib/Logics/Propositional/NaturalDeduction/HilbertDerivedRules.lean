/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.FromHilbert

/-! # Derived Rules for the Hilbert System

This module provides derived introduction and elimination rules for the
propositional connectives in the Hilbert-style proof system
(`DerivationTree` with `List` contexts).

Rules are organized into three layers:

## Minimal Layer (K, S only)
Introduction rules that require only the K and S axioms:
- `hilbertNegI`, `hilbertNegE`
- `hilbertIffI`

## Intuitionistic Layer (K, S, EFQ)
Rules that additionally require EFQ:
- `hilbertTopI`, `hilbertBotE`
- `hilbertAndI`, `hilbertAndE1`, `hilbertAndE2`
- `hilbertOrI1`, `hilbertOrI2`, `hilbertOrE`

## Classical Layer (K, S, EFQ, Peirce)
Rules that additionally require Peirce's law:
- `hilbertDne` (double negation elimination)
- `hilbertIffE1`, `hilbertIffE2`

Since `and` and `or` are now primitive constructors with axioms, the corresponding
introduction and elimination rules are simple one or two modus-ponens applications.

### Prop-level Wrappers
All rules have `Deriv`-level versions with the suffix `Deriv`.

## Design

Rules that use `impI` (the deduction theorem) are `noncomputable`.
All definitions are parameterized over a generic axiom predicate `Axioms`
with explicit axiom witnesses, following the pattern from `DeductionTheorem.lean`.

## References

* `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` -- ND wrappers
* `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- Hilbert system
* `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- axiom schemata
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Minimal Layer (K, S only) -/

/-! ### Negation Rules -/

/-- **Negation Introduction** (negI): From `A :: Gamma |- bot`, derive `Gamma |- neg A`.

Since `neg A := A -> bot`, this is `impI`. Requires K and S axioms. -/
noncomputable def hilbertNegI
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Axioms (A :: Γ) ⊥) :
    DerivationTree Axioms Γ (¬A) :=
  impI h_K h_S d

/-- **Negation Elimination** (negE): From `Gamma |- neg A` and `Gamma |- A`,
derive `Gamma |- bot`.

Since `neg A := A -> bot`, this is `impE`. No axiom parameters needed. -/
def hilbertNegE
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (¬A))
    (d₂ : DerivationTree Axioms Γ A) :
    DerivationTree Axioms Γ ⊥ :=
  impE d₁ d₂

/-! ### Biconditional Introduction -/

/-- **Biconditional Introduction** (iffI): From `Gamma |- A -> B` and
`Gamma |- B -> A`, derive `Gamma |- A iff B`.

Since `A iff B := (A -> B) and (B -> A)`, uses the AndI axiom. -/
def hilbertIffI
    {Axioms : PL.Proposition Atom → Prop}
    (h_andI : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp (φ.and ψ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (A → B))
    (d₂ : DerivationTree Axioms Γ (B → A)) :
    DerivationTree Axioms Γ (A ↔ B) :=
  -- Use andI axiom: (A → B) → ((B → A) → (A → B) ∧ (B → A))
  DerivationTree.modus_ponens Γ _ _
    (DerivationTree.modus_ponens Γ _ _
      (DerivationTree.ax Γ _ (h_andI (A.imp B) (B.imp A)))
      d₁)
    d₂

/-! ## Intuitionistic Layer (K, S, EFQ) -/

/-! ### Verum and Falsum -/

/-- **Top Introduction** (topI): `Gamma |- top` for any context.

Since `top := bot -> bot`, use EFQ at `bot` and weaken. Requires EFQ axiom. -/
def hilbertTopI
    {Axioms : PL.Proposition Atom → Prop}
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)} :
    DerivationTree Axioms Γ (Proposition.top : PL.Proposition Atom) :=
  DerivationTree.weakening [] Γ _
    (DerivationTree.ax [] _ (h_EFQ Proposition.bot))
    (fun _ h => nomatch h)

/-- **Bottom Elimination** (botE): From `Gamma |- bot`, derive `Gamma |- A`.

Uses the EFQ axiom `⊥ → A`. -/
def hilbertBotE
    {Axioms : PL.Proposition Atom → Prop}
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ ⊥) :
    DerivationTree Axioms Γ A :=
  botE h_EFQ d

/-! ### Conjunction Rules -/

/-- **Conjunction Introduction** (andI): From `Gamma |- A` and `Gamma |- B`,
derive `Gamma |- A ∧ B`.

Uses the AndI axiom: `A → (B → A ∧ B)`. Two modus ponens applications. -/
def hilbertAndI
    {Axioms : PL.Proposition Atom → Prop}
    (h_andI : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp (φ.and ψ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ A)
    (d₂ : DerivationTree Axioms Γ B) :
    DerivationTree Axioms Γ (A ∧ B) :=
  DerivationTree.modus_ponens Γ _ _
    (DerivationTree.modus_ponens Γ _ _
      (DerivationTree.ax Γ _ (h_andI A B))
      d₁)
    d₂

/-- **Left Conjunction Elimination** (andE1): From `Gamma |- A ∧ B`,
derive `Gamma |- A`.

Uses the AndE1 axiom: `A ∧ B → A`. One modus ponens application. -/
def hilbertAndE1
    {Axioms : PL.Proposition Atom → Prop}
    (h_andE1 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A ∧ B)) :
    DerivationTree Axioms Γ A :=
  DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _ (h_andE1 A B))
    d

/-- **Right Conjunction Elimination** (andE2): From `Gamma |- A ∧ B`,
derive `Gamma |- B`.

Uses the AndE2 axiom: `A ∧ B → B`. One modus ponens application. -/
def hilbertAndE2
    {Axioms : PL.Proposition Atom → Prop}
    (h_andE2 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp ψ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A ∧ B)) :
    DerivationTree Axioms Γ B :=
  DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _ (h_andE2 A B))
    d

/-! ### Disjunction Rules -/

/-- **Left Disjunction Introduction** (orI1): From `Gamma |- A`,
derive `Gamma |- A ∨ B`.

Uses the OrI1 axiom: `A → A ∨ B`. One modus ponens application. -/
def hilbertOrI1
    {Axioms : PL.Proposition Atom → Prop}
    (h_orI1 : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (φ.or ψ)))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ A) :
    DerivationTree Axioms Γ (A ∨ B) :=
  DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _ (h_orI1 A B))
    d

/-- **Right Disjunction Introduction** (orI2): From `Gamma |- B`,
derive `Gamma |- A ∨ B`.

Uses the OrI2 axiom: `B → A ∨ B`. One modus ponens application. -/
def hilbertOrI2
    {Axioms : PL.Proposition Atom → Prop}
    (h_orI2 : ∀ (φ ψ : PL.Proposition Atom), Axioms (ψ.imp (φ.or ψ)))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ B) :
    DerivationTree Axioms Γ (A ∨ B) :=
  DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _ (h_orI2 A B))
    d

/-- **Disjunction Elimination** (orE): From `Gamma |- A ∨ B`,
`A :: Gamma |- C`, and `B :: Gamma |- C`, derive `Gamma |- C`.

Uses the OrE axiom: `(A → C) → ((B → C) → ((A ∨ B) → C))`.
Three modus ponens applications (after building A → C and B → C via impI). -/
noncomputable def hilbertOrE
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B C : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A ∨ B))
    (dA : DerivationTree Axioms (A :: Γ) C)
    (dB : DerivationTree Axioms (B :: Γ) C) :
    DerivationTree Axioms Γ C := by
  -- Gamma |- A -> C
  have hAC : DerivationTree Axioms Γ (A → C) := impI h_K h_S dA
  -- Gamma |- B -> C
  have hBC : DerivationTree Axioms Γ (B → C) := impI h_K h_S dB
  -- Apply OrE axiom: (A → C) → ((B → C) → ((A ∨ B) → C))
  -- Three MP: get (A ∨ B) → C, then apply to d
  have h1 := DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _ (h_orE A B C))
    hAC
  have h2 := DerivationTree.modus_ponens Γ _ _ h1 hBC
  exact DerivationTree.modus_ponens Γ _ _ h2 d

/-! ## Classical Layer (K, S, EFQ, Peirce) -/

/-! ### Double Negation Elimination -/

/-- **Double Negation Elimination** (dne): From `Gamma |- neg neg A`,
derive `Gamma |- A`.

Uses Peirce(A, bot) to get ((A -> bot) -> A) -> A, then EFQ to get
bot -> A, then composes neg neg A = (A -> bot) -> bot with (bot -> A)
via the B-combinator to get (A -> bot) -> A, and applies Peirce.
Requires K, S, EFQ, and Peirce axioms. -/
def hilbertDne
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (¬¬A)) :
    DerivationTree Axioms Γ A := by
  -- d : Gamma |- (A -> bot) -> bot
  -- Peirce(A, bot): ((A -> bot) -> A) -> A
  have peirce := DerivationTree.ax Γ _ (h_Peirce A Proposition.bot)
  -- EFQ(A): bot -> A
  have efq := DerivationTree.ax Γ _ (h_EFQ A)
  -- ImplyK: (bot -> A) -> ((A -> bot) -> (bot -> A))
  have k_efq := DerivationTree.modus_ponens Γ _ _
    (DerivationTree.ax Γ _
      (h_K (Proposition.bot.imp A)
        (A.imp Proposition.bot)))
    efq
  -- ImplyS at ((A -> bot) -> (bot -> A)) -> (((A -> bot) -> bot) -> ((A -> bot) -> A))
  have s_ax := DerivationTree.ax Γ _
    (h_S (A.imp Proposition.bot) Proposition.bot A)
  -- Apply S to k_efq: ((A -> bot) -> bot) -> ((A -> bot) -> A)
  have composed := DerivationTree.modus_ponens Γ _ _ s_ax k_efq
  -- Apply to d: (A -> bot) -> A
  have imp_peirce := DerivationTree.modus_ponens Γ _ _ composed d
  -- Apply Peirce: A
  exact DerivationTree.modus_ponens Γ _ _ peirce imp_peirce

/-! ### Biconditional Elimination (Classical) -/

/-- **Left Biconditional Elimination** (iffE1): From `Gamma |- A iff B`,
derive `Gamma |- A -> B`.

Since `A iff B := (A -> B) ∧ (B -> A)`, uses the AndE1 axiom.
Requires AndE1. -/
def hilbertIffE1
    {Axioms : PL.Proposition Atom → Prop}
    (h_andE1 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A ↔ B)) :
    DerivationTree Axioms Γ (A → B) :=
  hilbertAndE1 h_andE1 d

/-- **Right Biconditional Elimination** (iffE2): From `Gamma |- A iff B`,
derive `Gamma |- B -> A`.

Since `A iff B := (A -> B) ∧ (B -> A)`, uses the AndE2 axiom.
Requires AndE2. -/
def hilbertIffE2
    {Axioms : PL.Proposition Atom → Prop}
    (h_andE2 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp ψ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ (A ↔ B)) :
    DerivationTree Axioms Γ (B → A) :=
  hilbertAndE2 h_andE2 d

/-! ### Deriv-level Wrappers -/

/-- Negation introduction at the `Deriv` level. -/
theorem hilbertNegIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv Axioms (A :: Γ) ⊥) :
    Deriv Axioms Γ (¬A) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertNegI h_K h_S d⟩

/-- Negation elimination at the `Deriv` level. -/
theorem hilbertNegEDeriv
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ (¬A))
    (h₂ : Deriv Axioms Γ A) :
    Deriv Axioms Γ ⊥ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertNegE d₁ d₂⟩

/-- Top introduction at the `Deriv` level. -/
theorem hilbertTopIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)} :
    Deriv Axioms Γ (Proposition.top : PL.Proposition Atom) :=
  ⟨hilbertTopI h_EFQ⟩

/-- Conjunction introduction at the `Deriv` level. -/
theorem hilbertAndIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_andI : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp (φ.and ψ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ A)
    (h₂ : Deriv Axioms Γ B) :
    Deriv Axioms Γ (A ∧ B) := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertAndI h_andI d₁ d₂⟩

/-- Left conjunction elimination at the `Deriv` level. -/
theorem hilbertAndE1Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_andE1 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A ∧ B)) : Deriv Axioms Γ A := by
  obtain ⟨d⟩ := h; exact ⟨hilbertAndE1 h_andE1 d⟩

/-- Right conjunction elimination at the `Deriv` level. -/
theorem hilbertAndE2Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_andE2 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp ψ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A ∧ B)) : Deriv Axioms Γ B := by
  obtain ⟨d⟩ := h; exact ⟨hilbertAndE2 h_andE2 d⟩

/-- Left disjunction introduction at the `Deriv` level. -/
theorem hilbertOrI1Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_orI1 : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (φ.or ψ)))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ A) : Deriv Axioms Γ (A ∨ B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertOrI1 h_orI1 d⟩

/-- Right disjunction introduction at the `Deriv` level. -/
theorem hilbertOrI2Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_orI2 : ∀ (φ ψ : PL.Proposition Atom), Axioms (ψ.imp (φ.or ψ)))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ B) : Deriv Axioms Γ (A ∨ B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertOrI2 h_orI2 d⟩

/-- Disjunction elimination at the `Deriv` level. -/
theorem hilbertOrEDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B C : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A ∨ B))
    (hA : Deriv Axioms (A :: Γ) C)
    (hB : Deriv Axioms (B :: Γ) C) :
    Deriv Axioms Γ C := by
  obtain ⟨d⟩ := h; obtain ⟨dA⟩ := hA; obtain ⟨dB⟩ := hB
  exact ⟨hilbertOrE h_K h_S h_orE d dA dB⟩

/-- Double negation elimination at the `Deriv` level. -/
theorem hilbertDneDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_Peirce : ∀ (φ ψ : PL.Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv Axioms Γ (¬¬A)) :
    Deriv Axioms Γ A := by
  obtain ⟨d⟩ := h; exact ⟨hilbertDne h_K h_S h_EFQ h_Peirce d⟩

/-- Biconditional introduction at the `Deriv` level. -/
theorem hilbertIffIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_andI : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp (φ.and ψ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ (A → B))
    (h₂ : Deriv Axioms Γ (B → A)) :
    Deriv Axioms Γ (A ↔ B) := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨hilbertIffI h_andI d₁ d₂⟩

/-- Left biconditional elimination at the `Deriv` level. -/
theorem hilbertIffE1Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_andE1 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A ↔ B)) :
    Deriv Axioms Γ (A → B) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertIffE1 h_andE1 d⟩

/-- Right biconditional elimination at the `Deriv` level. -/
theorem hilbertIffE2Deriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_andE2 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp ψ))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms Γ (A ↔ B)) :
    Deriv Axioms Γ (B → A) := by
  obtain ⟨d⟩ := h; exact ⟨hilbertIffE2 h_andE2 d⟩

end Cslib.Logic.PL
