/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Foundations.Order.HilbertAlgebra
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.MapFold

/-! # Free BrouwerianSemilattice over a HilbertAlgebra

Given a `HilbertAlgebra` `H`, this module constructs the **free BrouwerianSemilattice** over `H`
as a quotient of `Multiset H`. Multisets represent formal finite meets; the ordering uses
Hilbert deducibility.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

noncomputable section

namespace HilbertAlgebra

variable {H : Type*} [HilbertAlgebra H]

/-! ## Left-commutativity of himp -/

theorem himp_left_comm (a b c : H) : a ⇨ (b ⇨ c) = b ⇨ (a ⇨ c) := by
  apply himp_antisymm
  · have : b ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) ≤ b ⇨ (a ⇨ c) := by
      have := himp_S b (a ⇨ b) (a ⇨ c); rw [himp_K b a, top_himp] at this; exact this
    exact le_trans (le_trans (himp_S a b c) le_himp) this
  · have : a ⇨ ((b ⇨ a) ⇨ (b ⇨ c)) ≤ a ⇨ (b ⇨ c) := by
      have := himp_S a (b ⇨ a) (b ⇨ c); rw [himp_K a b, top_himp] at this; exact this
    exact le_trans (le_trans (himp_S b a c) le_himp) this

instance instHImpLeftCommutative : LeftCommutative ((· ⇨ ·) : H → H → H) :=
  ⟨himp_left_comm⟩

/-! ## Foldr lemmas -/

/-- Right-fold of `⇨` over a multiset: `fld S t = s₁ ⇨ (s₂ ⇨ (... ⇨ t))`.
Used to represent derivability of `t` from the multiset `S` in a Hilbert algebra. -/
abbrev fld (S : Multiset H) (t : H) : H := Multiset.foldr (· ⇨ ·) t S

theorem fld_zero (t : H) : fld (0 : Multiset H) t = t := Multiset.foldr_zero _ t

theorem fld_cons (a : H) (S : Multiset H) (t : H) :
    fld (a ::ₘ S) t = a ⇨ fld S t := Multiset.foldr_cons _ t a S

theorem fld_add (S T : Multiset H) (t : H) :
    fld (S + T) t = fld S (fld T t) := Multiset.foldr_add _ t S T

theorem fld_singleton (a t : H) : fld ({a} : Multiset H) t = a ⇨ t :=
  Multiset.foldr_singleton _ t a

theorem fld_mono {S : Multiset H} {t₁ t₂ : H} (h : t₁ ≤ t₂) :
    fld S t₁ ≤ fld S t₂ := by
  induction S using Multiset.induction_on with
  | empty => rwa [fld_zero, fld_zero]
  | cons a s ih => rw [fld_cons, fld_cons]; exact himp_le_himp_left ih

theorem fld_top (S : Multiset H) : fld S ⊤ = ⊤ := by
  induction S using Multiset.induction_on with
  | empty => exact fld_zero ⊤
  | cons a s ih => rw [fld_cons, ih, himp_top]

theorem le_fld (T : Multiset H) (u : H) : u ≤ fld T u := by
  induction T using Multiset.induction_on with
  | empty => rw [fld_zero]
  | cons t T' ih => rw [fld_cons]; exact le_trans ih (himp_K _ _)

theorem fld_himp_le (S : Multiset H) (a b : H) :
    fld S (a ⇨ b) ≤ fld S a ⇨ fld S b := by
  induction S using Multiset.induction_on with
  | empty => rw [fld_zero, fld_zero, fld_zero]
  | cons s S' ih =>
    rw [fld_cons, fld_cons, fld_cons]
    exact le_trans (himp_le_himp_left ih) (himp_S s _ _)

theorem fld_mp (S : Multiset H) {a b : H}
    (h1 : fld S (a ⇨ b) = ⊤) (h2 : fld S a = ⊤) : fld S b = ⊤ := by
  have : fld S a ⇨ fld S b = ⊤ :=
    le_antisymm le_top (le_trans (h1 ▸ le_rfl) (fld_himp_le S a b))
  exact himp_mp this h2

theorem fld_absorb (S T : Multiset H) (u : H)
    (hfoldr : fld S (fld T u) = ⊤)
    (hST : ∀ t ∈ T, fld S t = ⊤) :
    fld S u = ⊤ := by
  induction T using Multiset.induction_on with
  | empty => rwa [fld_zero] at hfoldr
  | cons t₀ T' ih =>
    rw [fld_cons] at hfoldr
    exact ih (fld_mp S hfoldr (hST t₀ (Multiset.mem_cons_self t₀ T')))
      (fun t' ht' => hST t' (Multiset.mem_cons.mpr (Or.inr ht')))

/-! ## Preorder and setoid on `Multiset H` -/

/-- Pre-order on multisets: `fmeLe S T` holds when every element of `T` is derivable from `S`,
i.e. `∀ t ∈ T, fld S t = ⊤`. This is the entailment relation that defines the Free Meet Extension
quotient. -/
def fmeLe (S T : Multiset H) : Prop := ∀ t ∈ T, fld S t = ⊤

theorem fmeLe_refl (S : Multiset H) : fmeLe S S := by
  intro t ht
  induction S using Multiset.induction_on with
  | empty => exact absurd ht (by simp)
  | cons a s ih =>
    rw [fld_cons]
    rcases Multiset.mem_cons.mp ht with rfl | ht'
    · rw [himp_eq_top_iff]; exact le_fld s t
    · rw [ih ht', himp_top]

theorem fmeLe_trans {S T U : Multiset H}
    (hST : fmeLe S T) (hTU : fmeLe T U) : fmeLe S U := by
  intro u hu
  exact fld_absorb S T u (by rw [hTU u hu]; exact fld_top S) hST

/-- Antisymmetric closure of `fmeLe`: `fmeEquiv S T` iff `S` and `T` derive each other.
This is the equivalence relation used to form the Free Meet Extension quotient type. -/
def fmeEquiv (S T : Multiset H) : Prop := fmeLe S T ∧ fmeLe T S

/-- The setoid on `Multiset H` induced by `fmeEquiv`.
Used as the quotient data for `FreeMeetExtension H`. -/
def fmeSetoid (H : Type*) [HilbertAlgebra H] : Setoid (Multiset H) where
  r := fmeEquiv
  iseqv := ⟨fun S => ⟨fmeLe_refl S, fmeLe_refl S⟩,
             fun h => ⟨h.2, h.1⟩,
             fun hST hTU => ⟨fmeLe_trans hST.1 hTU.1, fmeLe_trans hTU.2 hST.2⟩⟩

/-! ## Helper: substituting equivalent S in fmeLe(A + S, T) -/

theorem fmeLe_add_right_of_le {A S₁ S₂ T : Multiset H}
    (h : fmeLe (A + S₁) T) (hS : fmeLe S₂ S₁) : fmeLe (A + S₂) T := by
  intro t ht
  have h1 : fld A (fld S₁ t) = ⊤ := by rw [← fld_add]; exact h t ht
  exact fld_absorb (A + S₂) S₁ t
    (by rw [fld_add]; exact le_antisymm le_top (le_trans (h1 ▸ le_rfl) (fld_mono (le_fld S₂ _))))
    (fun s hs => by rw [fld_add, hS s hs]; exact fld_top A)

theorem fmeLe_add_iff_map {U S T : Multiset H} :
    fmeLe (U + S) T ↔ fmeLe U (T.map (fld S)) := by
  constructor
  · intro h v hv
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hv
    rw [← fld_add]; exact h t ht
  · intro h t ht
    rw [fld_add]; exact h (fld S t) (Multiset.mem_map_of_mem (fld S) ht)

/-! ## FreeMeetExtension type -/

/-- The Free Meet Extension of a Hilbert algebra `H`: the quotient of `Multiset H` by the
entailment equivalence `fmeEquiv`. Elements represent (equivalence classes of) finite conjunctions
of elements of `H`. -/
def FreeMeetExtension (H : Type*) [HilbertAlgebra H] :=
  Quotient (fmeSetoid H)

namespace FreeMeetExtension

variable {H : Type*} [HilbertAlgebra H]

/-- The canonical quotient map: sends a multiset `S : Multiset H` to its equivalence class
in `FreeMeetExtension H`. -/
def mk (S : Multiset H) : FreeMeetExtension H :=
  Quotient.mk (fmeSetoid H) S

@[simp]
theorem mk_eq_iff {S T : Multiset H} :
    mk S = mk T ↔ fmeEquiv S T :=
  Quotient.eq (r := fmeSetoid H)

instance instLE : LE (FreeMeetExtension H) :=
  ⟨Quotient.lift₂ fmeLe (by
    intro S₁ T₁ S₂ T₂ ⟨hS1, hS2⟩ ⟨hT1, hT2⟩
    simp only [eq_iff_iff]
    exact ⟨fun h => fmeLe_trans hS2 (fmeLe_trans h hT1),
           fun h => fmeLe_trans hS1 (fmeLe_trans h hT2)⟩)⟩

@[simp]
theorem mk_le_mk {S T : Multiset H} : mk S ≤ mk T ↔ fmeLe S T := Iff.rfl

instance instPartialOrder : PartialOrder (FreeMeetExtension H) where
  le_refl x := Quotient.inductionOn x fmeLe_refl
  le_trans x y z := Quotient.inductionOn₃ x y z (fun _ _ _ => fmeLe_trans)
  le_antisymm x y hxy hyx :=
    Quotient.inductionOn₂ x y (fun _ _ h1 h2 => Quotient.sound ⟨h1, h2⟩) hxy hyx

instance instTop : Top (FreeMeetExtension H) := ⟨mk 0⟩

theorem top_def : (⊤ : FreeMeetExtension H) = mk 0 := rfl

instance instOrderTop : OrderTop (FreeMeetExtension H) where
  le_top x := Quotient.inductionOn x (fun S t ht =>
    absurd ht (by simp))

/-! ## BrouwerianSemilattice -/

theorem inf_wd (S₁ T₁ S₂ T₂ : Multiset H) (hS : @Setoid.r _ (fmeSetoid H) S₁ S₂)
    (hT : @Setoid.r _ (fmeSetoid H) T₁ T₂) : mk (S₁ + T₁) = mk (S₂ + T₂) := by
  apply Quotient.sound; change fmeEquiv _ _
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩ <;> rw [fld_add]
  · rcases Multiset.mem_add.mp hu with hs | ht
    · exact le_antisymm le_top (hS.1 u hs ▸ fld_mono (le_fld _ u))
    · rw [hT.1 u ht]; exact fld_top _
  · rcases Multiset.mem_add.mp hu with hs | ht
    · exact le_antisymm le_top (hS.2 u hs ▸ fld_mono (le_fld _ u))
    · rw [hT.2 u ht]; exact fld_top _

theorem himp_wd (S₁ T₁ S₂ T₂ : Multiset H) (hS : @Setoid.r _ (fmeSetoid H) S₁ S₂)
    (hT : @Setoid.r _ (fmeSetoid H) T₁ T₂) :
    mk (T₁.map (fld S₁)) = mk (T₂.map (fld S₂)) := by
  apply Quotient.sound; change fmeEquiv _ _
  have hS' : fmeEquiv S₁ S₂ := hS
  have hT' : fmeEquiv T₁ T₂ := hT
  constructor
  · -- fmeLe (T₁.map (fld S₁)) (T₂.map (fld S₂))
    -- By adjunction: ↔ fmeLe ((T₁.map (fld S₁)) + S₂) T₂
    rw [← fmeLe_add_iff_map]
    -- From refl + adjunction: fmeLe ((T₁.map (fld S₁)) + S₁) T₁
    -- Replace S₁ by S₂, compose with T₁ ≤ T₂
    exact fmeLe_trans
      (fmeLe_add_right_of_le
        (fmeLe_add_iff_map.mpr (fmeLe_refl _) : fmeLe (_ + S₁) T₁)
        hS'.2)
      hT'.1
  · rw [← fmeLe_add_iff_map]
    exact fmeLe_trans
      (fmeLe_add_right_of_le
        (fmeLe_add_iff_map.mpr (fmeLe_refl _) : fmeLe (_ + S₂) T₂)
        hS'.1)
      hT'.2

instance instSemilatticeInf : SemilatticeInf (FreeMeetExtension H) where
  inf := Quotient.lift₂ (fun S T => mk (S + T))
    (fun _ _ _ _ hS hT => inf_wd _ _ _ _ hS hT)
  inf_le_left a b := Quotient.inductionOn₂ a b (fun S T u hu => by
    rw [fld_add]; exact le_antisymm le_top (fmeLe_refl S u hu ▸ fld_mono (le_fld T u)))
  inf_le_right a b := Quotient.inductionOn₂ a b (fun S T u hu => by
    rw [fld_add, fmeLe_refl T u hu]; exact fld_top S)
  le_inf {a b c} hab hac := by
    revert hab hac
    exact Quotient.inductionOn₃ a b c (fun S T U hST hSU v hv => by
      rcases Multiset.mem_add.mp hv with ht | hu
      · exact hST v ht
      · exact hSU v hu)

instance instBrouwerianSemilattice : BrouwerianSemilattice (FreeMeetExtension H) :=
  { instSemilatticeInf, instOrderTop with
    himp := Quotient.lift₂ (fun S T => mk (T.map (fld S)))
      (fun _ _ _ _ hS hT => himp_wd _ _ _ _ hS hT)
    le_himp_iff := fun U S T =>
      Quotient.inductionOn₃ U S T (fun _ _ _ => fmeLe_add_iff_map.symm) }

@[simp]
theorem mk_himp_mk {S T : Multiset H} :
    mk S ⇨ mk T = mk (T.map (fld S)) := rfl

end FreeMeetExtension

/-! ## Singleton embedding -/

/-- Singleton embedding `a ↦ mk {a}` from `H` into `FreeMeetExtension H`.
Sends each element to the class of the singleton multiset `{a}`. -/
def freeMeetEmbed (a : H) : FreeMeetExtension H := FreeMeetExtension.mk {a}

theorem freeMeetEmbed_eq_top_iff {a : H} :
    freeMeetEmbed a = (⊤ : FreeMeetExtension H) ↔ a = ⊤ := by
  simp only [freeMeetEmbed, FreeMeetExtension.mk_eq_iff, FreeMeetExtension.top_def]
  constructor
  · intro ⟨_, h2⟩
    have := h2 a (Multiset.mem_singleton_self a)
    rwa [fld_zero] at this
  · intro h; subst h
    exact ⟨fun t ht => absurd ht (by simp),
           fun t ht => by rw [fld_zero]; exact (Multiset.mem_singleton.mp ht).symm ▸ rfl⟩

theorem freeMeetEmbed_himp (a b : H) :
    freeMeetEmbed (a ⇨ b) = freeMeetEmbed a ⇨ freeMeetEmbed b := by
  change FreeMeetExtension.mk _ = FreeMeetExtension.mk _
  congr 1

end HilbertAlgebra

end

end
