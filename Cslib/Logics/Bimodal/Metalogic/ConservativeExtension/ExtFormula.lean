/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.Syntax.Formula

/-!
# Extended Formula Type for Conservative Extension

This module defines the extended formula type `ExtFormula` with atoms `ExtAtom Atom := Atom ⊕ Unit`.
The key property is that the fresh atom `Sum.inr ()` does not appear in any embedded
formula from the original language, enabling the standard Goldblatt/BdRV naming argument.

## Main Definitions

- `ExtAtom`: Extended atom type `Atom ⊕ Unit`
- `ExtFormula`: Formula type over `ExtAtom Atom`
- `embedAtom`: Embedding `Atom → ExtAtom Atom` via `Sum.inl`
- `embedFormula`: Structural embedding `Formula Atom → ExtFormula Atom`

## Main Results

- `embedFormula_injective`: The embedding is injective
- `fresh_not_in_embedFormula_atoms`: `Sum.inr () ∉ (embedFormula φ).atoms` for all φ

## References

- Goldblatt 1992, Logics of Time and Computation
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.ConservativeExtension

open Cslib.Logic.Bimodal

variable {Atom : Type u}

/-- Extended atom type: original Atom atoms plus one fresh Unit atom. -/
abbrev ExtAtom (Atom : Type u) := Atom ⊕ Unit

instance [Hashable Atom] : Hashable (ExtAtom Atom) where
  hash
    | Sum.inl a => mixHash 0 (hash a)
    | Sum.inr () => mixHash 1 0

/-- The fresh atom not appearing in any embedded formula. -/
def freshAtom : ExtAtom Atom := Sum.inr ()

/--
Extended formula type mirroring `Formula` but with `ExtAtom Atom` atoms.
-/
inductive ExtFormula (Atom : Type u) : Type u where
  | atom : ExtAtom Atom → ExtFormula Atom
  | bot : ExtFormula Atom
  | imp : ExtFormula Atom → ExtFormula Atom → ExtFormula Atom
  | box : ExtFormula Atom → ExtFormula Atom
  | untl : ExtFormula Atom → ExtFormula Atom → ExtFormula Atom
  | snce : ExtFormula Atom → ExtFormula Atom → ExtFormula Atom
  deriving Repr, DecidableEq, BEq, Hashable

namespace ExtFormula

/-- Top: ⊤ := ⊥ → ⊥ -/
def top : ExtFormula Atom := ExtFormula.bot.imp ExtFormula.bot

/-- Negation: ¬φ := φ → ⊥ -/
def neg (φ : ExtFormula Atom) : ExtFormula Atom := φ.imp bot

/-- Conjunction: φ ∧ ψ := ¬(φ → ¬ψ) -/
def and (φ ψ : ExtFormula Atom) : ExtFormula Atom := (φ.imp ψ.neg).neg

/-- Disjunction: φ ∨ ψ := ¬φ → ψ -/
def or (φ ψ : ExtFormula Atom) : ExtFormula Atom := φ.neg.imp ψ

/-- Modal diamond: ◇φ := ¬□¬φ -/
def diamond (φ : ExtFormula Atom) : ExtFormula Atom := φ.neg.box.neg

/-- Existential future: Fφ := U(φ, ⊤) -/
def someFuture (φ : ExtFormula Atom) : ExtFormula Atom := ExtFormula.untl top φ

/-- Existential past: Pφ := S(φ, ⊤) -/
def somePast (φ : ExtFormula Atom) : ExtFormula Atom := ExtFormula.snce top φ

/-- Universal future: Gφ := ¬F(¬φ) -/
def allFuture (φ : ExtFormula Atom) : ExtFormula Atom := (someFuture φ.neg).neg

/-- Universal past: Hφ := ¬P(¬φ) -/
def allPast (φ : ExtFormula Atom) : ExtFormula Atom := (somePast φ.neg).neg

/-- Always: △φ := Hφ ∧ φ ∧ Gφ -/
def always (φ : ExtFormula Atom) : ExtFormula Atom := allPast φ |>.and (φ.and (allFuture φ))

/-- Sometimes: ▽φ := ¬△¬φ -/
def sometimes (φ : ExtFormula Atom) : ExtFormula Atom := φ.neg.always.neg

/-- Swap temporal operators (past ↔ future). -/
def swapTemporal : ExtFormula Atom → ExtFormula Atom
  | atom s => atom s
  | bot => bot
  | imp φ ψ => imp φ.swapTemporal ψ.swapTemporal
  | box φ => box φ.swapTemporal
  | untl ψ φ => snce ψ.swapTemporal φ.swapTemporal
  | snce ψ φ => untl ψ.swapTemporal φ.swapTemporal

section DecEq

variable [DecidableEq Atom]

/-- The set of atoms appearing in an extended formula. -/
def atoms : ExtFormula Atom → Finset (ExtAtom Atom)
  | atom s => {s}
  | bot => ∅
  | imp φ ψ => φ.atoms ∪ ψ.atoms
  | box φ => φ.atoms
  | untl ψ φ => φ.atoms ∪ ψ.atoms
  | snce ψ φ => φ.atoms ∪ ψ.atoms

end DecEq

/-- Structural complexity measure. -/
def complexity : ExtFormula Atom → Nat
  | atom _ => 1
  | bot => 1
  | imp φ ψ => 1 + φ.complexity + ψ.complexity
  | box φ => 1 + φ.complexity
  | untl ψ φ => 1 + φ.complexity + ψ.complexity
  | snce ψ φ => 1 + φ.complexity + ψ.complexity

end ExtFormula

/-!
## Embedding Functions
-/

/-- Embed an Atom into ExtAtom. -/
def embedAtom : Atom → ExtAtom Atom := Sum.inl

/-- Embed a Formula (Atom atoms) into ExtFormula (ExtAtom atoms). -/
def embedFormula : Formula Atom → ExtFormula Atom
  | Formula.atom a => ExtFormula.atom (embedAtom a)
  | Formula.bot => ExtFormula.bot
  | Formula.imp φ ψ => ExtFormula.imp (embedFormula φ) (embedFormula ψ)
  | Formula.box φ => ExtFormula.box (embedFormula φ)
  | Formula.untl ψ φ => ExtFormula.untl (embedFormula ψ) (embedFormula φ)
  | Formula.snce ψ φ => ExtFormula.snce (embedFormula ψ) (embedFormula φ)

/-!
## Embedding Preservation Lemmas

Primitive constructors commute by `rfl`; derived operators commute by unfolding.
-/

theorem embedFormula_neg (φ : Formula Atom) :
    embedFormula (Formula.neg φ) = ExtFormula.neg (embedFormula φ) := rfl

theorem embedFormula_and (φ ψ : Formula Atom) :
    embedFormula (Formula.and φ ψ) = ExtFormula.and (embedFormula φ) (embedFormula ψ) := rfl

theorem embedFormula_or (φ ψ : Formula Atom) :
    embedFormula (Formula.or φ ψ) = ExtFormula.or (embedFormula φ) (embedFormula ψ) := rfl

@[simp]
theorem embedFormula_imp (φ ψ : Formula Atom) :
    embedFormula (Formula.imp φ ψ) = ExtFormula.imp (embedFormula φ) (embedFormula ψ) := rfl

@[simp]
theorem embedFormula_box (φ : Formula Atom) :
    embedFormula (Formula.box φ) = ExtFormula.box (embedFormula φ) := rfl

@[simp]
theorem embedFormula_untl (φ ψ : Formula Atom) :
    embedFormula (Formula.untl ψ φ) = ExtFormula.untl (embedFormula ψ) (embedFormula φ) := rfl

@[simp]
theorem embedFormula_snce (φ ψ : Formula Atom) :
    embedFormula (Formula.snce ψ φ) = ExtFormula.snce (embedFormula ψ) (embedFormula φ) := rfl

theorem embedFormula_diamond (φ : Formula Atom) :
    embedFormula (Formula.diamond φ) = ExtFormula.diamond (embedFormula φ) := rfl

theorem embedFormula_someFuture (φ : Formula Atom) :
    embedFormula (Formula.someFuture φ) = ExtFormula.someFuture (embedFormula φ) := rfl

theorem embedFormula_somePast (φ : Formula Atom) :
    embedFormula (Formula.somePast φ) = ExtFormula.somePast (embedFormula φ) := rfl

theorem embedFormula_allFuture (φ : Formula Atom) :
    embedFormula (Formula.allFuture φ) = ExtFormula.allFuture (embedFormula φ) := rfl

theorem embedFormula_allPast (φ : Formula Atom) :
    embedFormula (Formula.allPast φ) = ExtFormula.allPast (embedFormula φ) := rfl

theorem embedFormula_always (φ : Formula Atom) :
    embedFormula (Formula.always φ) = ExtFormula.always (embedFormula φ) := rfl

@[simp]
theorem embedFormula_swapTemporal (φ : Formula Atom) :
    embedFormula (Formula.swapTemporal φ) = ExtFormula.swapTemporal (embedFormula φ) := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ih1 ih2 => simp [Formula.swapTemporal, ExtFormula.swapTemporal, embedFormula, ih1, ih2]
  | box _ ih => simp [Formula.swapTemporal, ExtFormula.swapTemporal, embedFormula, ih]
  | untl _ _ ih2 ih1 =>
    simp [Formula.swapTemporal, ExtFormula.swapTemporal, embedFormula, ih2, ih1]
  | snce _ _ ih2 ih1 =>
    simp [Formula.swapTemporal, ExtFormula.swapTemporal, embedFormula, ih2, ih1]

/-!
## Injectivity
-/

theorem embedAtom_injective : Function.Injective (embedAtom : Atom → ExtAtom Atom) :=
  Sum.inl_injective

theorem embedFormula_injective :
    Function.Injective (embedFormula : Formula Atom → ExtFormula Atom) := by
  intro φ ψ h
  induction φ generalizing ψ with
  | atom s =>
    cases ψ with
    | atom t =>
      simp only [embedFormula, embedAtom, ExtFormula.atom.injEq, Sum.inl.injEq] at h
      exact congrArg Formula.atom h
    | bot => simp [embedFormula] at h
    | imp _ _ => simp [embedFormula] at h
    | box _ => simp [embedFormula] at h
    | untl _ _ => simp [embedFormula] at h
    | snce _ _ => simp [embedFormula] at h
  | bot =>
    cases ψ with
    | bot => rfl
    | atom _ => simp [embedFormula] at h
    | imp _ _ => simp [embedFormula] at h
    | box _ => simp [embedFormula] at h
    | untl _ _ => simp [embedFormula] at h
    | snce _ _ => simp [embedFormula] at h
  | imp a b iha ihb =>
    cases ψ with
    | imp c d =>
      simp only [embedFormula, ExtFormula.imp.injEq] at h
      exact congrArg₂ Formula.imp (iha h.1) (ihb h.2)
    | atom _ => simp [embedFormula] at h
    | bot => simp [embedFormula] at h
    | box _ => simp [embedFormula] at h
    | untl _ _ => simp [embedFormula] at h
    | snce _ _ => simp [embedFormula] at h
  | box a ih =>
    cases ψ with
    | box c =>
      simp only [embedFormula, ExtFormula.box.injEq] at h
      exact congrArg Formula.box (ih h)
    | atom _ => simp [embedFormula] at h
    | bot => simp [embedFormula] at h
    | imp _ _ => simp [embedFormula] at h
    | untl _ _ => simp [embedFormula] at h
    | snce _ _ => simp [embedFormula] at h
  | untl b a ihb iha =>
    cases ψ with
    | untl d c =>
      simp only [embedFormula, ExtFormula.untl.injEq] at h
      exact congrArg₂ Formula.untl (ihb h.1) (iha h.2)
    | atom _ => simp [embedFormula] at h
    | bot => simp [embedFormula] at h
    | imp _ _ => simp [embedFormula] at h
    | box _ => simp [embedFormula] at h
    | snce _ _ => simp [embedFormula] at h
  | snce b a ihb iha =>
    cases ψ with
    | snce d c =>
      simp only [embedFormula, ExtFormula.snce.injEq] at h
      exact congrArg₂ Formula.snce (ihb h.1) (iha h.2)
    | atom _ => simp [embedFormula] at h
    | bot => simp [embedFormula] at h
    | imp _ _ => simp [embedFormula] at h
    | box _ => simp [embedFormula] at h
    | untl _ _ => simp [embedFormula] at h

/-!
## Freshness: The Critical Lemma

`Sum.inr ()` does not appear in any embedded formula. This is because `embedFormula`
maps atoms via `Sum.inl`, and `Sum.inr () ≠ Sum.inl s` for any `s`.
-/

section Freshness

variable [DecidableEq Atom]

theorem fresh_not_in_embedFormula_atoms (φ : Formula Atom) :
    freshAtom ∉ (embedFormula φ).atoms := by
  induction φ with
  | atom s =>
    simp [embedFormula, ExtFormula.atoms, embedAtom, freshAtom]
  | bot =>
    simp [embedFormula, ExtFormula.atoms]
  | imp a b iha ihb =>
    simp only [embedFormula_imp, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha, ihb⟩
  | box a ih =>
    simp only [embedFormula_box, ExtFormula.atoms]
    exact ih
  | untl b a ihb iha =>
    simp only [embedFormula_untl, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha, ihb⟩
  | snce b a ihb iha =>
    simp only [embedFormula_snce, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha, ihb⟩

/-- Variant: all atoms in an embedded formula are of the form Sum.inl. -/
theorem embedFormula_atoms_subset_inl (φ : Formula Atom) :
    ∀ a ∈ (embedFormula φ).atoms, ∃ s : Atom, a = Sum.inl s := by
  induction φ with
  | atom s =>
    intro a ha
    simp only [embedFormula, embedAtom, ExtFormula.atoms, Finset.mem_singleton] at ha
    exact ⟨s, ha⟩
  | bot =>
    intro a ha
    simp [embedFormula, ExtFormula.atoms] at ha
  | imp a b iha ihb =>
    intro x hx
    simp only [embedFormula, ExtFormula.atoms, Finset.mem_union] at hx
    cases hx with
    | inl h => exact iha x h
    | inr h => exact ihb x h
  | box a ih =>
    intro x hx
    simp only [embedFormula_box, ExtFormula.atoms] at hx
    exact ih x hx
  | untl b a ihb iha =>
    intro x hx
    simp only [embedFormula, ExtFormula.atoms, Finset.mem_union] at hx
    cases hx with
    | inl h => exact iha x h
    | inr h => exact ihb x h
  | snce b a ihb iha =>
    intro x hx
    simp only [embedFormula, ExtFormula.atoms, Finset.mem_union] at hx
    cases hx with
    | inl h => exact iha x h
    | inr h => exact ihb x h

/-- Key lemma for IRR embedding: atom membership is preserved under embedding. -/
theorem embedAtom_mem_embedFormula_atoms_iff (p : Atom) (φ : Formula Atom) :
    embedAtom p ∈ (embedFormula φ).atoms ↔ p ∈ φ.atoms := by
  induction φ with
  | atom s =>
    simp [embedFormula, ExtFormula.atoms, embedAtom, Formula.atoms]
  | bot =>
    simp [embedFormula, ExtFormula.atoms, Formula.atoms]
  | imp a b iha ihb =>
    simp [embedFormula, ExtFormula.atoms, Formula.atoms, Finset.mem_union, iha, ihb]
  | box a ih =>
    simp [embedFormula, ExtFormula.atoms, Formula.atoms, ih]
  | untl b a ihb iha =>
    simp [embedFormula, ExtFormula.atoms, Formula.atoms, Finset.mem_union, iha, ihb]
  | snce b a ihb iha =>
    simp [embedFormula, ExtFormula.atoms, Formula.atoms, Finset.mem_union, iha, ihb]

/-- Corollary: freshAtom is not in atoms of any formula in an embedded set. -/
theorem fresh_not_in_embedded_set_atoms (Φ : Set (Formula Atom)) (ψ : ExtFormula Atom)
    (h : ψ ∈ embedFormula '' Φ) :
    freshAtom ∉ ψ.atoms := by
  obtain ⟨φ, _, rfl⟩ := h
  exact fresh_not_in_embedFormula_atoms φ

end Freshness

end Cslib.Logic.Bimodal.Metalogic.ConservativeExtension
