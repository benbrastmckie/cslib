/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # Generic Prime Exclusion Lemma

This module provides a generic prime-exclusion framework parameterized over an abstract
`DerivationSystem F`. The main result is `prime_exclusion`: given an admissible set `S`
with `phi ∉ S`, there exists a prime admissible superset `T ⊇ S` with `phi ∉ T`.

The framework is parameterized over:
- A consistency predicate `Cons : Set F → Prop` (use `fun _ => True` for the minimal case)
- A deductive-closure operator `cl : Set F → Set F`
- An EFQ-bridge witness `phi_mem_cl_of_not_cons` (vacuous when `Cons = fun _ => True`)

This mirrors the `set_lindenbaum` template in `Consistency.lean` and is instantiated by
`MinLindenbaum.lean` (with `Cons = fun _ => True`) and `IntLindenbaum.lean` (with
`Cons = SetConsistent D`).

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5
-/

@[expose] public section

open Cslib.Logic

namespace Cslib.Logic.Metalogic

variable {F : Type*} [HasImp F] [HasOr F]

/-! ## Generic Predicates -/

/-- A set `S` is deductively closed for derivation system `D` if any formula derivable
from a finite subset of `S` is itself in `S`. -/
def DeductivelyClosed (D : DerivationSystem F) (S : Set F) : Prop :=
  ∀ (L : List F) (φ : F), (∀ x ∈ L, x ∈ S) → D.Deriv L φ → φ ∈ S

/-- A set `S` is admissible for derivation system `D` under consistency predicate `Cons`
if it satisfies `Cons` and is deductively closed.

Setting `Cons := fun _ => True` recovers the minimal (unconstrained) case, where
`Admissible D (fun _ => True) S` reduces to `DeductivelyClosed D S`. -/
def Admissible (D : DerivationSystem F) (Cons : Set F → Prop) (S : Set F) : Prop :=
  Cons S ∧ DeductivelyClosed D S

/-- The collection of `phi`-excluding admissible supersets of `S`. This is the Zorn domain
for the prime exclusion lemma. -/
def PrimeExcludingSupersets (D : DerivationSystem F) (Cons : Set F → Prop)
    (S : Set F) (phi : F) : Set (Set F) :=
  {T | S ⊆ T ∧ Admissible D Cons T ∧ phi ∉ T}

/-- A set `S` is prime admissible if it is admissible and satisfies the disjunction property:
whenever `A ⊔ B ∈ S`, either `A ∈ S` or `B ∈ S`. -/
def PrimeAdmissible (D : DerivationSystem F) (Cons : Set F → Prop) (S : Set F) : Prop :=
  Admissible D Cons S ∧ ∀ A B : F, HasOr.or A B ∈ S → A ∈ S ∨ B ∈ S

/-! ## Supporting Lemmas -/

omit [HasOr F] in
/-- Base membership: if `S` is admissible and `phi ∉ S`, then `S` is in its own
`phi`-excluding admissible supersets. -/
theorem prime_excluding_base_mem (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} (hS : Admissible D Cons S) {phi : F}
    (h_not : phi ∉ S) : S ∈ PrimeExcludingSupersets D Cons S phi :=
  ⟨Set.Subset.refl S, hS, h_not⟩

omit [HasOr F] in
/-- Deductive closure is preserved by nonempty chain unions.

If every set in a nonempty chain `C` is deductively closed under `D`, then so is `⋃₀ C`.
Uses `finite_list_in_chain_member` to find a single chain member containing any
finite set of premises. -/
theorem deductivelyClosed_chain_union (D : DerivationSystem F)
    {C : Set (Set F)} (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
    (h : ∀ T ∈ C, DeductivelyClosed D T) : DeductivelyClosed D (⋃₀ C) := by
  intro L phi hL hd
  obtain ⟨T, hTC, hLT⟩ := finite_list_in_chain_member hchain hCne L hL
  exact Set.mem_sUnion.mpr ⟨T, hTC, h T hTC L phi hLT hd⟩

omit [HasOr F] in
/-- The union of a nonempty chain of `phi`-excluding admissible sets is itself
`phi`-excluding admissible, provided `Cons` is preserved under chain unions.

This is the key chain condition for Zorn's lemma in `prime_exclusion`. -/
theorem prime_excluding_chain_union (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} {phi : F} {C : Set (Set F)}
    (hCsub : C ⊆ PrimeExcludingSupersets D Cons S phi)
    (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
    (hConsChain : Cons (⋃₀ C)) :
    (⋃₀ C) ∈ PrimeExcludingSupersets D Cons S phi := by
  refine ⟨?_, ⟨hConsChain, ?_⟩, ?_⟩
  · -- S ⊆ ⋃₀ C
    intro x hx
    obtain ⟨T, hT⟩ := hCne
    exact Set.mem_sUnion.mpr ⟨T, hT, (hCsub hT).1 hx⟩
  · -- DeductivelyClosed D (⋃₀ C)
    exact deductivelyClosed_chain_union D hchain hCne
      (fun T hTC => (hCsub hTC).2.1.2)
  · -- phi ∉ ⋃₀ C
    rintro ⟨T, hTC, hphi⟩
    exact (hCsub hTC).2.2 hphi

/-! ## Main Generic Lemmas -/

/-- If `T` is maximal in `PrimeExcludingSupersets D Cons S phi`, then `T` is prime admissible.

Proof: Assume `A ⊔ B ∈ T`, `A ∉ T`, `B ∉ T`. For each disjunct `X ∈ {A, B}`, we show
`phi ∈ cl (insert X T)` via a consistency case split (`by_cases hc : Cons (insert X T)`):
- Consistent: `cl (insert X T)` is admissible by `cl_admissible_of_cons`; by maximality of `T`
  the closure equals `T`, but `X ∈ cl (insert X T)` contradicts `X ∉ T`.
- Inconsistent: `phi_mem_cl_of_not_cons hc` gives `phi ∈ cl (insert X T)` directly.

Using `cl_mem_imp` and `hCut`, we extract `L' ⊆ T` with `L' ⊢ A → phi` and `L'' ⊆ T` with
`L'' ⊢ B → phi`. The orE axiom then derives `phi` from `L' ++ L'' ++ [A ⊔ B] ⊆ T`, and
deductive closure gives `phi ∈ T`, contradicting `hmax.prop.2.2`. -/
theorem prime_maximal_is_prime
    (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} {phi : F} {T : Set F}
    -- orE schema as an empty-context derivation
    (hOrE : ∀ A B χ : F,
        D.Deriv [] (HasImp.imp (HasImp.imp A χ)
          (HasImp.imp (HasImp.imp B χ) (HasImp.imp (HasOr.or A B) χ))))
    -- deductive-closure operator and its laws
    (cl : Set F → Set F)
    (cl_subset : ∀ X, X ⊆ cl X)
    (cl_mem_imp : ∀ {X ψ}, ψ ∈ cl X → ∃ L, (∀ x ∈ L, x ∈ X) ∧ D.Deriv L ψ)
    (cl_admissible_of_cons : ∀ {X}, Cons X → Admissible D Cons (cl X))
    -- EFQ bridge: vacuous when Cons = fun _ => True
    (phi_mem_cl_of_not_cons : ∀ {X}, ¬ Cons X → phi ∈ cl X)
    -- cut / deduction witness
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    (hmax : Maximal (· ∈ PrimeExcludingSupersets D Cons S phi) T) :
    PrimeAdmissible D Cons T := by
  obtain ⟨h_sub, h_adm, h_not_phi⟩ := hmax.prop
  refine ⟨h_adm, ?_⟩
  intro A B h_or
  by_contra h_not
  push Not at h_not
  obtain ⟨hA, hB⟩ := h_not
  -- phi ∈ cl (insert A T)
  have hTA_phi : phi ∈ cl (insert A T) := by
    have hTA_sup : T ⊆ cl (insert A T) :=
      Set.Subset.trans (Set.subset_insert A T) (cl_subset _)
    have hA_in : A ∈ cl (insert A T) :=
      cl_subset _ (Set.mem_insert A T)
    by_cases hc : Cons (insert A T)
    · -- Consistent: cl(T ∪ {A}) is admissible; maximality forces T = cl(T ∪ {A})
      by_contra hnp
      have hmem : cl (insert A T) ∈ PrimeExcludingSupersets D Cons S phi :=
        ⟨h_sub.trans hTA_sup, cl_admissible_of_cons hc, hnp⟩
      exact hA ((hmax.eq_of_ge hmem hTA_sup) ▸ hA_in)
    · exact phi_mem_cl_of_not_cons hc
  -- Extract L' ⊆ T with L' ⊢ A → phi
  obtain ⟨LTA, hLTA_sub, hLTA_deriv⟩ := cl_mem_imp hTA_phi
  obtain ⟨L', hL'_sub, hL'_deriv⟩ := hCut hLTA_sub hLTA_deriv
  -- phi ∈ cl (insert B T)
  have hTB_phi : phi ∈ cl (insert B T) := by
    have hTB_sup : T ⊆ cl (insert B T) :=
      Set.Subset.trans (Set.subset_insert B T) (cl_subset _)
    have hB_in : B ∈ cl (insert B T) :=
      cl_subset _ (Set.mem_insert B T)
    by_cases hc : Cons (insert B T)
    · by_contra hnp
      have hmem : cl (insert B T) ∈ PrimeExcludingSupersets D Cons S phi :=
        ⟨h_sub.trans hTB_sup, cl_admissible_of_cons hc, hnp⟩
      exact hB ((hmax.eq_of_ge hmem hTB_sup) ▸ hB_in)
    · exact phi_mem_cl_of_not_cons hc
  -- Extract L'' ⊆ T with L'' ⊢ B → phi
  obtain ⟨LTB, hLTB_sub, hLTB_deriv⟩ := cl_mem_imp hTB_phi
  obtain ⟨L'', hL''_sub, hL''_deriv⟩ := hCut hLTB_sub hLTB_deriv
  -- orE combination: L' ++ L'' ++ [A ⊔ B] ⊢ phi, all from T
  let ctx := L' ++ L'' ++ [HasOr.or A B]
  have h_ctx_T : ∀ x ∈ ctx, x ∈ T := by
    intro x hx
    simp only [ctx, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with (hx | hx) | rfl
    · exact hL'_sub x hx
    · exact hL''_sub x hx
    · exact h_or
  -- Weaken orE to ctx
  have h_orE_w : D.Deriv ctx (HasImp.imp (HasImp.imp A phi)
      (HasImp.imp (HasImp.imp B phi) (HasImp.imp (HasOr.or A B) phi))) :=
    D.weakening (hOrE A B phi) (fun _ h => nomatch h)
  -- Weaken A → phi and B → phi to ctx
  have dA_w : D.Deriv ctx (HasImp.imp A phi) :=
    D.weakening hL'_deriv
      (fun x hx => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx))))
  have dB_w : D.Deriv ctx (HasImp.imp B phi) :=
    D.weakening hL''_deriv
      (fun x hx => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx))))
  -- Use assumption for A ⊔ B in ctx
  have d_or : D.Deriv ctx (HasOr.or A B) :=
    D.assumption (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  -- Three modus ponens
  have d_step1 := D.mp h_orE_w dA_w
  have d_step2 := D.mp d_step1 dB_w
  have d_phi := D.mp d_step2 d_or
  -- phi ∈ T by deductive closure of T
  obtain ⟨_, h_dc⟩ := h_adm
  exact h_not_phi (h_dc ctx phi h_ctx_T d_phi)

/-- **Generic Prime Exclusion Lemma**: given an admissible set `S` with `phi ∉ S`, there
exists a prime admissible `T ⊇ S` with `phi ∉ T`.

The proof applies Zorn's lemma to `PrimeExcludingSupersets D Cons S phi`, using
`prime_excluding_chain_union` for the chain condition and `prime_maximal_is_prime` for
primality. The caller supplies:
- `hConsChain`: that `Cons` is preserved under admissible chain unions
- orE schema `hOrE`, closure operator `cl`, and the cut witness `hCut`

Instantiated by `min_prime_exclusion` (with `Cons = fun _ => True`) and
`int_prime_exclusion` (with `Cons = SetConsistent D`).

See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5. -/
theorem prime_exclusion
    (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} (hS : Admissible D Cons S) {phi : F} (h_not : phi ∉ S)
    (hOrE : ∀ A B χ : F,
        D.Deriv [] (HasImp.imp (HasImp.imp A χ)
          (HasImp.imp (HasImp.imp B χ) (HasImp.imp (HasOr.or A B) χ))))
    (cl : Set F → Set F)
    (cl_subset : ∀ X, X ⊆ cl X)
    (cl_mem_imp : ∀ {X ψ}, ψ ∈ cl X → ∃ L, (∀ x ∈ L, x ∈ X) ∧ D.Deriv L ψ)
    (cl_admissible_of_cons : ∀ {X}, Cons X → Admissible D Cons (cl X))
    (phi_mem_cl_of_not_cons : ∀ {X}, ¬ Cons X → phi ∈ cl X)
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    (hConsChain : ∀ C, IsChain (· ⊆ ·) C → C.Nonempty →
        C ⊆ PrimeExcludingSupersets D Cons S phi → Cons (⋃₀ C)) :
    ∃ T, S ⊆ T ∧ PrimeAdmissible D Cons T ∧ phi ∉ T := by
  have ⟨T, hST, hmax⟩ := zorn_subset_nonempty (PrimeExcludingSupersets D Cons S phi)
    (fun C hCsub hchain hCne =>
      ⟨⋃₀ C,
       prime_excluding_chain_union D Cons hCsub hchain hCne (hConsChain C hchain hCne hCsub),
       fun s hs => Set.subset_sUnion_of_mem hs⟩)
    S (prime_excluding_base_mem D Cons hS h_not)
  exact ⟨T, hST,
         prime_maximal_is_prime D Cons hOrE cl cl_subset cl_mem_imp
           cl_admissible_of_cons phi_mem_cl_of_not_cons hCut hmax,
         hmax.prop.2.2⟩

end Cslib.Logic.Metalogic
