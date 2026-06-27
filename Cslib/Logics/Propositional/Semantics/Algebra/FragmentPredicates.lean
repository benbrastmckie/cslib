/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.Conservative

/-! # Fragment Syntactic Predicates and Independence Lemmas

This module defines three syntactic fragment predicates on `Proposition Atom`, following the
established `IsBotFree` Bool-valued recursive pattern from `Conservative.lean`:

- `IsOrFree`: no disjunction (only `atom`, `bot`, `imp`, `and`)
- `IsOrBotFree`: no disjunction or falsum (only `atom`, `imp`, `and`)
- `IsImpTopOnly`: only implication and atoms (no conjunction, disjunction, or falsum)

For each predicate, we prove:
1. **Subsumption hierarchy**: `IsImpTopOnly → IsOrBotFree → IsOrFree` and
   `IsOrBotFree → IsBotFree`, with `IsOrBotFree ↔ IsOrFree ∧ IsBotFree`.
2. **Connective closure**: each predicate is preserved by the connectives in its fragment.
3. **Substitution closure**: each predicate is preserved by substitution when all images
   are in the fragment.
4. **Independence lemmas**: `AlgEvaluate` is independent of the operations excluded by the
   predicate, stated as morphism lemmas. For an algebra morphism `f : H₁ → H₂` preserving the
   fragment's operations, `f (AlgEvaluate v b A) = AlgEvaluate (f ∘ v) b' A` when `A` is in
   the fragment and any additional hypotheses (e.g. `f b = b'` for or-free) hold.

These predicates are used by downstream tasks to characterize the conjunctive-implicational
and implicational fragments for Brouwerian and Hilbert algebra completeness proofs.
-/

@[expose] public section

universe u v

namespace Cslib.Logic.PL

open Proposition

/-! ## Fragment Predicates -/

/-- A proposition is or-free if it contains no disjunction. -/
def Proposition.IsOrFree : Proposition Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp a b => a.IsOrFree && b.IsOrFree
  | .and a b => a.IsOrFree && b.IsOrFree
  | .or _ _ => false

/-- A proposition is or-bot-free if it contains neither disjunction nor falsum. -/
def Proposition.IsOrBotFree : Proposition Atom → Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.IsOrBotFree && b.IsOrBotFree
  | .and a b => a.IsOrBotFree && b.IsOrBotFree
  | .or _ _ => false

/-- A proposition is imp-top-only if it contains only implication and atoms
(no conjunction, disjunction, or falsum). -/
def Proposition.IsImpTopOnly : Proposition Atom → Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.IsImpTopOnly && b.IsImpTopOnly
  | .and _ _ => false
  | .or _ _ => false

/-- A proposition is and-bot-free if it contains no conjunction and no falsum
(only `atom`, `imp`, `or`). This characterizes the disjunctive-implicational
fragment IPL⟨∨,→,⊤⟩. -/
def Proposition.IsAndBotFree : Proposition Atom → Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.IsAndBotFree && b.IsAndBotFree
  | .and _ _ => false
  | .or a b => a.IsAndBotFree && b.IsAndBotFree

/-! ## Subsumption Hierarchy -/

/-- Every imp-top-only formula is and-bot-free. -/
lemma IsImpTopOnly_implies_IsAndBotFree {Atom : Type*} (A : Proposition Atom) :
    A.IsImpTopOnly = true → A.IsAndBotFree = true := by
  induction A with
  | atom _ => simp [Proposition.IsImpTopOnly, Proposition.IsAndBotFree]
  | bot => simp [Proposition.IsImpTopOnly]
  | imp a b iha ihb =>
    simp only [Proposition.IsImpTopOnly, Proposition.IsAndBotFree, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨iha h1, ihb h2⟩
  | and _ _ _ _ => simp [Proposition.IsImpTopOnly]
  | or _ _ _ _ => simp [Proposition.IsImpTopOnly]

/-- Every imp-top-only formula is or-bot-free. -/
lemma IsImpTopOnly_implies_IsOrBotFree {Atom : Type*} (A : Proposition Atom) :
    A.IsImpTopOnly = true → A.IsOrBotFree = true := by
  induction A with
  | atom _ => simp [Proposition.IsImpTopOnly, Proposition.IsOrBotFree]
  | bot => simp [Proposition.IsImpTopOnly]
  | imp a b iha ihb =>
    simp only [Proposition.IsImpTopOnly, Proposition.IsOrBotFree, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨iha h1, ihb h2⟩
  | and _ _ _ _ => simp [Proposition.IsImpTopOnly]
  | or _ _ _ _ => simp [Proposition.IsImpTopOnly]

/-- Every or-bot-free formula is or-free. -/
lemma IsOrBotFree_implies_IsOrFree {Atom : Type*} (A : Proposition Atom) :
    A.IsOrBotFree = true → A.IsOrFree = true := by
  induction A with
  | atom _ => simp [Proposition.IsOrBotFree, Proposition.IsOrFree]
  | bot => simp [Proposition.IsOrBotFree]
  | imp a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Proposition.IsOrFree, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨iha h1, ihb h2⟩
  | and a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Proposition.IsOrFree, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨iha h1, ihb h2⟩
  | or _ _ _ _ => simp [Proposition.IsOrBotFree]

/-- Every or-bot-free formula is bot-free. -/
lemma IsOrBotFree_implies_IsBotFree {Atom : Type*} (A : Proposition Atom) :
    A.IsOrBotFree = true → A.IsBotFree = true := by
  induction A with
  | atom _ => simp [Proposition.IsOrBotFree, Proposition.IsBotFree]
  | bot => simp [Proposition.IsOrBotFree]
  | imp a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Proposition.IsBotFree, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨iha h1, ihb h2⟩
  | and a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Proposition.IsBotFree, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨iha h1, ihb h2⟩
  | or _ _ _ _ => simp [Proposition.IsOrBotFree]

/-- A formula is or-bot-free iff it is both or-free and bot-free. -/
lemma IsOrBotFree_iff {Atom : Type*} (A : Proposition Atom) :
    A.IsOrBotFree = true ↔ A.IsOrFree = true ∧ A.IsBotFree = true := by
  induction A with
  | atom _ => simp [Proposition.IsOrBotFree, Proposition.IsOrFree, Proposition.IsBotFree]
  | bot => simp [Proposition.IsOrBotFree, Proposition.IsOrFree, Proposition.IsBotFree]
  | imp a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Proposition.IsOrFree, Proposition.IsBotFree,
      Bool.and_eq_true]
    rw [iha, ihb]
    constructor
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
  | and a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Proposition.IsOrFree, Proposition.IsBotFree,
      Bool.and_eq_true]
    rw [iha, ihb]
    constructor
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
  | or _ _ _ _ => simp [Proposition.IsOrBotFree, Proposition.IsOrFree, Proposition.IsBotFree]

/-! ## Connective Closure -/

/-- Implication of or-free formulas is or-free. -/
lemma imp_isOrFree {Atom : Type*} {A B : Proposition Atom}
    (hA : A.IsOrFree = true) (hB : B.IsOrFree = true) :
    (A.imp B).IsOrFree = true := by
  simp only [Proposition.IsOrFree, Bool.and_eq_true, hA, hB, and_self]

/-- Conjunction of or-free formulas is or-free. -/
lemma and_isOrFree {Atom : Type*} {A B : Proposition Atom}
    (hA : A.IsOrFree = true) (hB : B.IsOrFree = true) :
    (A.and B).IsOrFree = true := by
  simp only [Proposition.IsOrFree, Bool.and_eq_true, hA, hB, and_self]

/-- Implication of or-bot-free formulas is or-bot-free. -/
lemma imp_isOrBotFree {Atom : Type*} {A B : Proposition Atom}
    (hA : A.IsOrBotFree = true) (hB : B.IsOrBotFree = true) :
    (A.imp B).IsOrBotFree = true := by
  simp only [Proposition.IsOrBotFree, Bool.and_eq_true, hA, hB, and_self]

/-- Conjunction of or-bot-free formulas is or-bot-free. -/
lemma and_isOrBotFree {Atom : Type*} {A B : Proposition Atom}
    (hA : A.IsOrBotFree = true) (hB : B.IsOrBotFree = true) :
    (A.and B).IsOrBotFree = true := by
  simp only [Proposition.IsOrBotFree, Bool.and_eq_true, hA, hB, and_self]

/-- Implication of imp-top-only formulas is imp-top-only. -/
lemma imp_isImpTopOnly {Atom : Type*} {A B : Proposition Atom}
    (hA : A.IsImpTopOnly = true) (hB : B.IsImpTopOnly = true) :
    (A.imp B).IsImpTopOnly = true := by
  simp only [Proposition.IsImpTopOnly, Bool.and_eq_true, hA, hB, and_self]

/-- Implication of and-bot-free formulas is and-bot-free. -/
lemma imp_isAndBotFree {Atom : Type*} {A B : Proposition Atom}
    (hA : A.IsAndBotFree = true) (hB : B.IsAndBotFree = true) :
    (A.imp B).IsAndBotFree = true := by
  simp only [Proposition.IsAndBotFree, Bool.and_eq_true, hA, hB, and_self]

/-- Disjunction of and-bot-free formulas is and-bot-free. -/
lemma or_isAndBotFree {Atom : Type*} {A B : Proposition Atom}
    (hA : A.IsAndBotFree = true) (hB : B.IsAndBotFree = true) :
    (A.or B).IsAndBotFree = true := by
  simp only [Proposition.IsAndBotFree, Bool.and_eq_true, hA, hB, and_self]

/-! ## Substitution Closure -/

/-- Substitution preserves IsOrFree when all substitution images are or-free. -/
theorem subst_preserves_isOrFree {Atom Atom' : Type u} (A : Proposition Atom)
    (hA : A.IsOrFree = true) (f : Atom → Proposition Atom')
    (hf : ∀ x, (f x).IsOrFree = true) :
    (A.subst f).IsOrFree = true := by
  induction A with
  | atom x => exact hf x
  | bot => simp [Proposition.subst, Proposition.IsOrFree]
  | imp a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [Proposition.subst, Proposition.IsOrFree, Bool.and_eq_true]
    exact ⟨iha hA.1, ihb hA.2⟩
  | and a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [Proposition.subst, Proposition.IsOrFree, Bool.and_eq_true]
    exact ⟨iha hA.1, ihb hA.2⟩
  | or _ _ _ _ => simp [Proposition.IsOrFree] at hA

/-- Substitution preserves IsOrBotFree when all substitution images are or-bot-free. -/
theorem subst_preserves_isOrBotFree {Atom Atom' : Type u} (A : Proposition Atom)
    (hA : A.IsOrBotFree = true) (f : Atom → Proposition Atom')
    (hf : ∀ x, (f x).IsOrBotFree = true) :
    (A.subst f).IsOrBotFree = true := by
  induction A with
  | atom x => exact hf x
  | bot => simp [Proposition.IsOrBotFree] at hA
  | imp a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hA
    simp only [Proposition.subst, Proposition.IsOrBotFree, Bool.and_eq_true]
    exact ⟨iha hA.1, ihb hA.2⟩
  | and a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hA
    simp only [Proposition.subst, Proposition.IsOrBotFree, Bool.and_eq_true]
    exact ⟨iha hA.1, ihb hA.2⟩
  | or _ _ _ _ => simp [Proposition.IsOrBotFree] at hA

/-- Substitution preserves IsImpTopOnly when all substitution images are imp-top-only. -/
theorem subst_preserves_isImpTopOnly {Atom Atom' : Type u} (A : Proposition Atom)
    (hA : A.IsImpTopOnly = true) (f : Atom → Proposition Atom')
    (hf : ∀ x, (f x).IsImpTopOnly = true) :
    (A.subst f).IsImpTopOnly = true := by
  induction A with
  | atom x => exact hf x
  | bot => simp [Proposition.IsImpTopOnly] at hA
  | imp a b iha ihb =>
    simp only [Proposition.IsImpTopOnly, Bool.and_eq_true] at hA
    simp only [Proposition.subst, Proposition.IsImpTopOnly, Bool.and_eq_true]
    exact ⟨iha hA.1, ihb hA.2⟩
  | and _ _ _ _ => simp [Proposition.IsImpTopOnly] at hA
  | or _ _ _ _ => simp [Proposition.IsImpTopOnly] at hA

/-- Substitution preserves IsAndBotFree when all substitution images are and-bot-free. -/
theorem subst_preserves_isAndBotFree {Atom Atom' : Type u} (A : Proposition Atom)
    (hA : A.IsAndBotFree = true) (f : Atom → Proposition Atom')
    (hf : ∀ x, (f x).IsAndBotFree = true) :
    (A.subst f).IsAndBotFree = true := by
  induction A with
  | atom x => exact hf x
  | bot => simp [Proposition.IsAndBotFree] at hA
  | imp a b iha ihb =>
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hA
    simp only [Proposition.subst, Proposition.IsAndBotFree, Bool.and_eq_true]
    exact ⟨iha hA.1, ihb hA.2⟩
  | and _ _ _ _ => simp [Proposition.IsAndBotFree] at hA
  | or a b iha ihb =>
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hA
    simp only [Proposition.subst, Proposition.IsAndBotFree, Bool.and_eq_true]
    exact ⟨iha hA.1, ihb hA.2⟩

/-! ## Independence Lemmas

For each fragment predicate, `AlgEvaluate` is independent of the algebraic operations
excluded by that predicate. We state this as a morphism property: given an algebra morphism
`f : H₁ → H₂` that preserves the fragment's operations, `f` commutes with evaluation on
formulas in the fragment. This is the natural generalization of `coe_AlgEvaluate`.
-/

/-- For or-free formulas, `AlgEvaluate` depends only on `⊓`, `⇨`, `⊤`, and `bot_val` --
not on `⊔`. Given a morphism `f : H₁ → H₂` preserving `⊓`, `⇨`, and mapping `b` to `b'`,
evaluation of or-free formulas commutes with `f`. -/
theorem coe_AlgEvaluate_orFree
    {Atom : Type*} {H₁ H₂ : Type*} [GeneralizedHeytingAlgebra H₁] [GeneralizedHeytingAlgebra H₂]
    (f : H₁ → H₂)
    (h_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (h_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (v : Atom → H₁) (b : H₁) (b' : H₂)
    (h_bot : f b = b')
    (A : Proposition Atom) (hA : A.IsOrFree = true) :
    f (AlgEvaluate v b A) = AlgEvaluate (f ∘ v) b' A := by
  induction A with
  | atom _ => rfl
  | bot => simpa [AlgEvaluate_bot]
  | imp a c iha ihc =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [AlgEvaluate_imp, h_himp, iha hA.1, ihc hA.2]
  | and a c iha ihc =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [AlgEvaluate_and, h_inf, iha hA.1, ihc hA.2]
  | or _ _ _ _ => simp [Proposition.IsOrFree] at hA

/-- For or-bot-free formulas, `AlgEvaluate` depends only on `⊓`, `⇨`, and `⊤` --
not on `⊔` or `bot_val`. Given a morphism `f : H₁ → H₂` preserving `⊓` and `⇨`,
evaluation of or-bot-free formulas commutes with `f` regardless of `bot_val`. -/
theorem coe_AlgEvaluate_orBotFree
    {Atom : Type*} {H₁ H₂ : Type*} [GeneralizedHeytingAlgebra H₁] [GeneralizedHeytingAlgebra H₂]
    (f : H₁ → H₂)
    (h_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (h_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (v : Atom → H₁) (b : H₁) (b' : H₂)
    (A : Proposition Atom) (hA : A.IsOrBotFree = true) :
    f (AlgEvaluate v b A) = AlgEvaluate (f ∘ v) b' A := by
  induction A with
  | atom _ => rfl
  | bot => simp [Proposition.IsOrBotFree] at hA
  | imp a c iha ihc =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hA
    simp only [AlgEvaluate_imp, h_himp, iha hA.1, ihc hA.2]
  | and a c iha ihc =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hA
    simp only [AlgEvaluate_and, h_inf, iha hA.1, ihc hA.2]
  | or _ _ _ _ => simp [Proposition.IsOrBotFree] at hA

/-- For and-bot-free formulas, `AlgEvaluate` depends only on `⊔`, `⇨`, and `⊤` --
not on `⊓` or `bot_val`. Given a morphism `f : H₁ → H₂` preserving `⊔` and `⇨`,
evaluation of and-bot-free formulas commutes with `f` regardless of `bot_val`. -/
theorem coe_AlgEvaluate_andBotFree
    {Atom : Type*} {H₁ H₂ : Type*} [GeneralizedHeytingAlgebra H₁] [GeneralizedHeytingAlgebra H₂]
    (f : H₁ → H₂)
    (h_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (h_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (v : Atom → H₁) (b : H₁) (b' : H₂)
    (A : Proposition Atom) (hA : A.IsAndBotFree = true) :
    f (AlgEvaluate v b A) = AlgEvaluate (f ∘ v) b' A := by
  induction A with
  | atom _ => rfl
  | bot => simp [Proposition.IsAndBotFree] at hA
  | imp a c iha ihc =>
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hA
    simp only [AlgEvaluate_imp, h_himp, iha hA.1, ihc hA.2]
  | and _ _ _ _ => simp [Proposition.IsAndBotFree] at hA
  | or a c iha ihc =>
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hA
    simp only [AlgEvaluate_or, h_sup, iha hA.1, ihc hA.2]

/-- For imp-top-only formulas, `AlgEvaluate` depends only on `⇨` --
not on `⊓`, `⊔`, or `bot_val`. Given a morphism `f : H₁ → H₂` preserving `⇨`,
evaluation of imp-top-only formulas commutes with `f` regardless of `bot_val`. -/
theorem coe_AlgEvaluate_impTopOnly
    {Atom : Type*} {H₁ H₂ : Type*} [GeneralizedHeytingAlgebra H₁] [GeneralizedHeytingAlgebra H₂]
    (f : H₁ → H₂)
    (h_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (v : Atom → H₁) (b : H₁) (b' : H₂)
    (A : Proposition Atom) (hA : A.IsImpTopOnly = true) :
    f (AlgEvaluate v b A) = AlgEvaluate (f ∘ v) b' A := by
  induction A with
  | atom _ => rfl
  | bot => simp [Proposition.IsImpTopOnly] at hA
  | imp a c iha ihc =>
    simp only [Proposition.IsImpTopOnly, Bool.and_eq_true] at hA
    simp only [AlgEvaluate_imp, h_himp, iha hA.1, ihc hA.2]
  | and _ _ _ _ => simp [Proposition.IsImpTopOnly] at hA
  | or _ _ _ _ => simp [Proposition.IsImpTopOnly] at hA

end Cslib.Logic.PL
