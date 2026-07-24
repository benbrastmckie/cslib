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

/-! ## Set (Lindenbaum-Pair) Exclusion Lemma

This section generalizes `prime_exclusion` from excluding a single formula `phi` to excluding
an entire set `Σ`: given an admissible `S` that derives no finite disjunction of `Σ`, there is
a prime admissible `T ⊇ S` that still derives no finite disjunction of `Σ`. This is the
"Lindenbaum-pair" construction needed by the intuitionistic modal canonical-model box/diamond
witnesses, which must extend a set to a prime theory avoiding an entire set of
formulas, not just one.

`prime_exclusion` is NOT refactored to route through this generalization (kept independent to
hold blast radius at zero; `bigOr [phi] = phi ⊔ ⊥ ≠ phi`, so it is a corollary only modulo
added hypotheses -- not a literal drop-in).

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5
  (the single-formula Zorn argument this generalizes)
* ianshil/CK, `theories/Completeness_th/general_th_completeness.v`,
  `Lindenbaum_pair`/`pair_extCKH_prv` (github.com/ianshil/CK) -- the reference mechanization of
  exactly this set-exclusion construction
-/

omit [HasOr F] in
/-- Empty-context implication transitivity: from `⊢ a → b` and `⊢ b → c`, derive `⊢ a → c`.
Internal "MP-composition glue" used to compose the `bigOr` monotonicity steps below. Builds a
derivation in context `[a]` via two `mp`/`assumption` steps, then discharges the assumption of
`a` back down to the empty context using the generic cut witness `hCut`. -/
theorem empty_imp_trans (D : DerivationSystem F)
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    {a b c : F} (h1 : D.Deriv [] (HasImp.imp a b)) (h2 : D.Deriv [] (HasImp.imp b c)) :
    D.Deriv [] (HasImp.imp a c) := by
  have haa : D.Deriv [a] a := D.assumption (List.mem_cons.mpr (Or.inl rfl))
  have hb : D.Deriv [a] b := D.mp (D.weakening h1 (fun _ h => nomatch h)) haa
  have hc : D.Deriv [a] c := D.mp (D.weakening h2 (fun _ h => nomatch h)) hb
  obtain ⟨L', hL'_sub, hL'_deriv⟩ := hCut (U := (∅ : Set F)) (L := [a])
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]
      exact Set.mem_insert a ∅) hc
  exact D.weakening hL'_deriv (fun x hx => absurd (hL'_sub x hx) (Set.mem_empty_iff_false x).mp)

omit [HasOr F] in
/-- Empty-context implication identity: `⊢ a → a`. Internal glue for the base case of
`bigOr_append_right`, obtained the same way as `empty_imp_trans`: build `[a] ⊢ a` via
`assumption`, then discharge to `[] ⊢ a → a` via `hCut`. -/
theorem empty_imp_id (D : DerivationSystem F)
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    (a : F) : D.Deriv [] (HasImp.imp a a) := by
  have haa : D.Deriv [a] a := D.assumption (List.mem_cons.mpr (Or.inl rfl))
  obtain ⟨L', hL'_sub, hL'_deriv⟩ := hCut (U := (∅ : Set F)) (L := [a])
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]
      exact Set.mem_insert a ∅) haa
  exact D.weakening hL'_deriv (fun x hx => absurd (hL'_sub x hx) (Set.mem_empty_iff_false x).mp)

section SetExclusion
variable [HasBot F]

/-- Object-level iterated disjunction of a finite list of formulas; `bigOr [] = ⊥` and
`bigOr (x :: xs) = x ⊔ bigOr xs`. Used to state "no finite disjunction of `Σ` is derivable"
(`DerivExcludes`), the key precondition of `prime_set_exclusion`. -/
def bigOr : List F → F
  | [] => HasBot.bot
  | x :: xs => HasOr.or x (bigOr xs)

/-- `T` derives no finite disjunction of `E`: for every finite list `l` drawn from `E`,
`bigOr l ∉ T`. When `T` is deductively closed this is equivalent to "no finite disjunction of
`E` is derivable from `T`" -- the Lindenbaum-pair exclusion condition (cf. ianshil/CK
`pair_extCKH_prv`). The `l = []` case (`bigOr [] = ⊥`) recovers ordinary consistency of `T`. -/
-- `_D` is retained to match the sibling signatures (`DeductivelyClosed D S`,
-- `Admissible D Cons S`, `SetExcludingSupersets D Cons S E`) even though the body only
-- references `E`, `T`, and `bigOr`.
@[nolint unusedArguments]
def DerivExcludes (_D : DerivationSystem F) (E : Set F) (T : Set F) : Prop :=
  ∀ l : List F, (∀ x ∈ l, x ∈ E) → bigOr l ∉ T

/-- The collection of admissible, `E`-excluding supersets of `S`. This is the Zorn domain for
`prime_set_exclusion`, generalizing `PrimeExcludingSupersets` from a single excluded formula to
an excluded set. -/
def SetExcludingSupersets (D : DerivationSystem F) (Cons : Set F → Prop)
    (S : Set F) (E : Set F) : Set (Set F) :=
  {T | S ⊆ T ∧ Admissible D Cons T ∧ DerivExcludes D E T}

omit [HasBot F] in
/-- Right-monotonicity of disjunction: if `⊢ b → b'` then `⊢ (x ⊔ b) → (x ⊔ b')`. Used by
`bigOr_append_left`'s inductive step. -/
theorem or_right_mono (D : DerivationSystem F)
    (hOrI1 : ∀ A B : F, D.Deriv [] (HasImp.imp A (HasOr.or A B)))
    (hOrI2 : ∀ A B : F, D.Deriv [] (HasImp.imp B (HasOr.or A B)))
    (hOrE : ∀ A B χ : F,
        D.Deriv [] (HasImp.imp (HasImp.imp A χ)
          (HasImp.imp (HasImp.imp B χ) (HasImp.imp (HasOr.or A B) χ))))
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    {x b b' : F} (h : D.Deriv [] (HasImp.imp b b')) :
    D.Deriv [] (HasImp.imp (HasOr.or x b) (HasOr.or x b')) :=
  D.mp (D.mp (hOrE x b (HasOr.or x b')) (hOrI1 x b'))
    (empty_imp_trans D hCut h (hOrI2 x b'))

/-- `⊢ bigOr l₂ → bigOr (l₁ ++ l₂)`: appending formulas on the left only weakens the
disjunction. Proved by induction on `l₁`: the base case is the identity implication
(`empty_imp_id`); the step composes `hOrI2` with the inductive hypothesis via
`empty_imp_trans`. -/
theorem bigOr_append_right (D : DerivationSystem F)
    (hOrI2 : ∀ A B : F, D.Deriv [] (HasImp.imp B (HasOr.or A B)))
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b)) :
    ∀ l₁ l₂ : List F, D.Deriv [] (HasImp.imp (bigOr l₂) (bigOr (l₁ ++ l₂)))
  | [], l₂ => empty_imp_id D hCut (bigOr l₂)
  | x :: xs, l₂ =>
      empty_imp_trans D hCut (bigOr_append_right D hOrI2 hCut xs l₂) (hOrI2 x (bigOr (xs ++ l₂)))

/-- `⊢ bigOr l₁ → bigOr (l₁ ++ l₂)`: appending formulas on the right only weakens the
disjunction. Proved by induction on `l₁`: the base case is `hEFQ` (`bigOr [] = ⊥`); the step
applies `or_right_mono` to the inductive hypothesis. -/
theorem bigOr_append_left (D : DerivationSystem F)
    (hOrI1 : ∀ A B : F, D.Deriv [] (HasImp.imp A (HasOr.or A B)))
    (hOrI2 : ∀ A B : F, D.Deriv [] (HasImp.imp B (HasOr.or A B)))
    (hOrE : ∀ A B χ : F,
        D.Deriv [] (HasImp.imp (HasImp.imp A χ)
          (HasImp.imp (HasImp.imp B χ) (HasImp.imp (HasOr.or A B) χ))))
    (hEFQ : ∀ A : F, D.Deriv [] (HasImp.imp HasBot.bot A))
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b)) :
    ∀ l₁ l₂ : List F, D.Deriv [] (HasImp.imp (bigOr l₁) (bigOr (l₁ ++ l₂)))
  | [], _l₂ => hEFQ _
  | _x :: xs, l₂ =>
      or_right_mono D hOrI1 hOrI2 hOrE hCut
        (bigOr_append_left D hOrI1 hOrI2 hOrE hEFQ hCut xs l₂)

/-- Base membership: if `S` is admissible and derives no finite disjunction of `E`, then `S` is
in its own `E`-excluding admissible supersets. Analogue of `prime_excluding_base_mem`. -/
theorem set_excluding_base_mem (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} (hS : Admissible D Cons S) {E : Set F}
    (h_excl : DerivExcludes D E S) : S ∈ SetExcludingSupersets D Cons S E :=
  ⟨Set.Subset.refl S, hS, h_excl⟩

/-- The union of a nonempty chain of `E`-excluding admissible sets is itself `E`-excluding
admissible, provided `Cons` is preserved under the chain union. Analogue of
`prime_excluding_chain_union`: the "`phi ∉ ⋃₀ C`" clause becomes "`DerivExcludes D E (⋃₀ C)`",
proved by the same single-chain-member argument (a finite `bigOr l` derivation lands in one
chain member, contradicting that member's `DerivExcludes`). -/
theorem set_excluding_chain_union (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} {E : Set F} {C : Set (Set F)}
    (hCsub : C ⊆ SetExcludingSupersets D Cons S E)
    (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
    (hConsChain : Cons (⋃₀ C)) :
    (⋃₀ C) ∈ SetExcludingSupersets D Cons S E := by
  refine ⟨?_, ⟨hConsChain, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨T, hT⟩ := hCne
    exact Set.mem_sUnion.mpr ⟨T, hT, (hCsub hT).1 hx⟩
  · exact deductivelyClosed_chain_union D hchain hCne
      (fun T hTC => (hCsub hTC).2.1.2)
  · rintro l hl ⟨T, hTC, hlT⟩
    exact (hCsub hTC).2.2 l hl hlT

/-- If `T` is maximal in `SetExcludingSupersets D Cons S E`, then `T` is prime admissible.

Mirrors `prime_maximal_is_prime`, replacing the fixed excluded formula `phi` by the per-branch
finite disjunction `χ := bigOr (lₐ ++ l_b)` of `E`. Assume `A ⊔ B ∈ T`, `A ∉ T`, `B ∉ T`. For
each disjunct `X ∈ {A, B}`, `cl (insert X T)` fails to be `E`-excluding (else maximality of `T`
forces `T = cl (insert X T)`, contradicting `X ∉ T`), so by a `Cons`-case split either
(a) `cl (insert X T)` is admissible and its `DerivExcludes` fails -- giving `lX ⊆ E` with
`bigOr lX ∈ cl (insert X T)` -- or (b) `insert X T` is inconsistent, so (via
`bot_mem_cl_of_not_cons`) `⊥ ∈ cl (insert X T)`, and we take `lX := []` (`bigOr [] = ⊥`). Either
way `cl_mem_imp`/`hCut` give `LX ⊆ T` with `LX ⊢ X → bigOr lX`, hence (composing with the NEW
`bigOr_append_left`/`bigOr_append_right`) `LA' ⊢ A → χ` and `LB' ⊢ B → χ`. The `hOrE`
combination step (copied verbatim from `prime_maximal_is_prime`) derives `T ⊢ χ`, so `χ ∈ T` by
deductive closure, contradicting `DerivExcludes D E T` applied to `lₐ ++ l_b`. -/
theorem set_maximal_is_prime
    (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} {E : Set F} {T : Set F}
    (hOrI1 : ∀ A B : F, D.Deriv [] (HasImp.imp A (HasOr.or A B)))
    (hOrI2 : ∀ A B : F, D.Deriv [] (HasImp.imp B (HasOr.or A B)))
    (hOrE : ∀ A B χ : F,
        D.Deriv [] (HasImp.imp (HasImp.imp A χ)
          (HasImp.imp (HasImp.imp B χ) (HasImp.imp (HasOr.or A B) χ))))
    (hEFQ : ∀ A : F, D.Deriv [] (HasImp.imp HasBot.bot A))
    (cl : Set F → Set F)
    (cl_subset : ∀ X, X ⊆ cl X)
    (cl_mem_imp : ∀ {X ψ}, ψ ∈ cl X → ∃ L, (∀ x ∈ L, x ∈ X) ∧ D.Deriv L ψ)
    (cl_admissible_of_cons : ∀ {X}, Cons X → Admissible D Cons (cl X))
    -- inconsistency bridge, analogue of `prime_exclusion`'s `phi_mem_cl_of_not_cons`, but
    -- targeting `⊥` (the canonical `bigOr []`) rather than a fixed formula:
    (bot_mem_cl_of_not_cons : ∀ {X}, ¬ Cons X → HasBot.bot ∈ cl X)
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    (hmax : Maximal (· ∈ SetExcludingSupersets D Cons S E) T) :
    PrimeAdmissible D Cons T := by
  obtain ⟨h_sub, h_adm, h_excl⟩ := hmax.prop
  refine ⟨h_adm, ?_⟩
  intro A B h_or
  by_contra h_not
  push Not at h_not
  obtain ⟨hA, hB⟩ := h_not
  -- For X ∈ {A, B}: get lX ⊆ E and LX0 ⊆ insert X T with LX0 ⊢ bigOr lX.
  have branch : ∀ X : F, X ∉ T →
      ∃ (lX : List F) (LX0 : List F),
        (∀ x ∈ lX, x ∈ E) ∧ (∀ x ∈ LX0, x ∈ insert X T) ∧ D.Deriv LX0 (bigOr lX) := by
    intro X hXT
    have hTX_sup : T ⊆ cl (insert X T) :=
      Set.Subset.trans (Set.subset_insert X T) (cl_subset _)
    have hX_in : X ∈ cl (insert X T) := cl_subset _ (Set.mem_insert X T)
    have hnotmem : cl (insert X T) ∉ SetExcludingSupersets D Cons S E := by
      intro hmem
      exact hXT ((hmax.eq_of_ge hmem hTX_sup) ▸ hX_in)
    by_cases hc : Cons (insert X T)
    · have h_adm_cl : Admissible D Cons (cl (insert X T)) := cl_admissible_of_cons hc
      have h_sub_cl : S ⊆ cl (insert X T) := h_sub.trans hTX_sup
      have h_fail : ¬ DerivExcludes D E (cl (insert X T)) := fun hexcl =>
        hnotmem ⟨h_sub_cl, h_adm_cl, hexcl⟩
      simp only [DerivExcludes, not_forall, not_not] at h_fail
      obtain ⟨lX, hlX_sub, hlX_mem⟩ := h_fail
      obtain ⟨LX0, hLX0_sub, hLX0_deriv⟩ := cl_mem_imp hlX_mem
      exact ⟨lX, LX0, hlX_sub, hLX0_sub, hLX0_deriv⟩
    · have hbot : HasBot.bot ∈ cl (insert X T) := bot_mem_cl_of_not_cons hc
      obtain ⟨LX0, hLX0_sub, hLX0_deriv⟩ := cl_mem_imp hbot
      exact ⟨[], LX0, (fun x hx => nomatch hx), hLX0_sub, hLX0_deriv⟩
  obtain ⟨lA, LA0, hlA_sub, hLA0_sub, hLA0_deriv⟩ := branch A hA
  obtain ⟨lB, LB0, hlB_sub, hLB0_sub, hLB0_deriv⟩ := branch B hB
  -- A → χ and B → χ (χ := bigOr (lA ++ lB)), each discharged to a sublist of T via hCut.
  have hAchi : ∃ LA', (∀ x ∈ LA', x ∈ T) ∧ D.Deriv LA' (HasImp.imp A (bigOr (lA ++ lB))) := by
    have d1w : D.Deriv (A :: LA0) (bigOr lA) :=
      D.weakening hLA0_deriv (fun x hx => List.mem_cons.mpr (Or.inr hx))
    have d2 : D.Deriv [] (HasImp.imp (bigOr lA) (bigOr (lA ++ lB))) :=
      bigOr_append_left D hOrI1 hOrI2 hOrE hEFQ hCut lA lB
    have d2w : D.Deriv (A :: LA0) (HasImp.imp (bigOr lA) (bigOr (lA ++ lB))) :=
      D.weakening d2 (fun _ h => nomatch h)
    have d3 : D.Deriv (A :: LA0) (bigOr (lA ++ lB)) := D.mp d2w d1w
    exact hCut (U := T) (L := A :: LA0) (a := A) (b := bigOr (lA ++ lB))
      (fun x hx => by
        rcases List.mem_cons.mp hx with heq | hx'
        · rw [heq]; exact Set.mem_insert A T
        · exact hLA0_sub x hx')
      d3
  have hBchi : ∃ LB', (∀ x ∈ LB', x ∈ T) ∧ D.Deriv LB' (HasImp.imp B (bigOr (lA ++ lB))) := by
    have d1w : D.Deriv (B :: LB0) (bigOr lB) :=
      D.weakening hLB0_deriv (fun x hx => List.mem_cons.mpr (Or.inr hx))
    have d2 : D.Deriv [] (HasImp.imp (bigOr lB) (bigOr (lA ++ lB))) :=
      bigOr_append_right D hOrI2 hCut lA lB
    have d2w : D.Deriv (B :: LB0) (HasImp.imp (bigOr lB) (bigOr (lA ++ lB))) :=
      D.weakening d2 (fun _ h => nomatch h)
    have d3 : D.Deriv (B :: LB0) (bigOr (lA ++ lB)) := D.mp d2w d1w
    exact hCut (U := T) (L := B :: LB0) (a := B) (b := bigOr (lA ++ lB))
      (fun x hx => by
        rcases List.mem_cons.mp hx with heq | hx'
        · rw [heq]; exact Set.mem_insert B T
        · exact hLB0_sub x hx')
      d3
  obtain ⟨LA', hLA'_sub, hLA'_deriv⟩ := hAchi
  obtain ⟨LB', hLB'_sub, hLB'_deriv⟩ := hBchi
  -- orE combination: LA' ++ LB' ++ [A ⊔ B] ⊢ χ, all from T. Copied verbatim from
  -- `prime_maximal_is_prime`, with `phi` replaced by `χ := bigOr (lA ++ lB)`.
  let ctx := LA' ++ LB' ++ [HasOr.or A B]
  have h_ctx_T : ∀ x ∈ ctx, x ∈ T := by
    intro x hx
    simp only [ctx, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with (hx | hx) | rfl
    · exact hLA'_sub x hx
    · exact hLB'_sub x hx
    · exact h_or
  have h_orE_w : D.Deriv ctx (HasImp.imp (HasImp.imp A (bigOr (lA ++ lB)))
      (HasImp.imp (HasImp.imp B (bigOr (lA ++ lB)))
        (HasImp.imp (HasOr.or A B) (bigOr (lA ++ lB))))) :=
    D.weakening (hOrE A B (bigOr (lA ++ lB))) (fun _ h => nomatch h)
  have dA_w : D.Deriv ctx (HasImp.imp A (bigOr (lA ++ lB))) :=
    D.weakening hLA'_deriv
      (fun x hx => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx))))
  have dB_w : D.Deriv ctx (HasImp.imp B (bigOr (lA ++ lB))) :=
    D.weakening hLB'_deriv
      (fun x hx => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx))))
  have d_or : D.Deriv ctx (HasOr.or A B) :=
    D.assumption (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have d_step1 := D.mp h_orE_w dA_w
  have d_step2 := D.mp d_step1 dB_w
  have d_chi := D.mp d_step2 d_or
  -- χ ∈ T by deductive closure of T, contradicting DerivExcludes D E T on lA ++ lB.
  obtain ⟨_, h_dc⟩ := h_adm
  have hchi_mem : bigOr (lA ++ lB) ∈ T := h_dc ctx (bigOr (lA ++ lB)) h_ctx_T d_chi
  exact h_excl (lA ++ lB)
    (fun x hx => by
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hlA_sub x hx'
      · exact hlB_sub x hx')
    hchi_mem

/-- **Generic Set (Lindenbaum-Pair) Exclusion Lemma**: given an admissible set `S` deriving no
finite disjunction of `E`, there exists a prime admissible `T ⊇ S` still deriving no finite
disjunction of `E` (in particular `T ∩ E = ∅`). Generalizes `prime_exclusion` from a single
excluded formula to an excluded set `E`.

The proof applies Zorn's lemma to `SetExcludingSupersets D Cons S E`, using
`set_excluding_chain_union` for the chain condition and `set_maximal_is_prime` for primality.
This is the "Lindenbaum-pair" construction consumed by the intuitionistic modal canonical-model
box/diamond witnesses.

See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5, and
ianshil/CK `Lindenbaum_pair`/`pair_extCKH_prv`. -/
theorem prime_set_exclusion
    (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} (hS : Admissible D Cons S)
    {E : Set F} (h_excl : DerivExcludes D E S)
    (hOrI1 : ∀ A B : F, D.Deriv [] (HasImp.imp A (HasOr.or A B)))
    (hOrI2 : ∀ A B : F, D.Deriv [] (HasImp.imp B (HasOr.or A B)))
    (hOrE : ∀ A B χ : F,
        D.Deriv [] (HasImp.imp (HasImp.imp A χ)
          (HasImp.imp (HasImp.imp B χ) (HasImp.imp (HasOr.or A B) χ))))
    (hEFQ : ∀ A : F, D.Deriv [] (HasImp.imp HasBot.bot A))
    (cl : Set F → Set F)
    (cl_subset : ∀ X, X ⊆ cl X)
    (cl_mem_imp : ∀ {X ψ}, ψ ∈ cl X → ∃ L, (∀ x ∈ L, x ∈ X) ∧ D.Deriv L ψ)
    (cl_admissible_of_cons : ∀ {X}, Cons X → Admissible D Cons (cl X))
    (bot_mem_cl_of_not_cons : ∀ {X}, ¬ Cons X → HasBot.bot ∈ cl X)
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    (hConsChain : ∀ C, IsChain (· ⊆ ·) C → C.Nonempty →
        C ⊆ SetExcludingSupersets D Cons S E → Cons (⋃₀ C)) :
    ∃ T, S ⊆ T ∧ PrimeAdmissible D Cons T ∧ DerivExcludes D E T := by
  have ⟨T, hST, hmax⟩ := zorn_subset_nonempty (SetExcludingSupersets D Cons S E)
    (fun C hCsub hchain hCne =>
      ⟨⋃₀ C,
       set_excluding_chain_union D Cons hCsub hchain hCne (hConsChain C hchain hCne hCsub),
       fun s hs => Set.subset_sUnion_of_mem hs⟩)
    S (set_excluding_base_mem D Cons hS h_excl)
  exact ⟨T, hST,
         set_maximal_is_prime D Cons hOrI1 hOrI2 hOrE hEFQ cl cl_subset cl_mem_imp
           cl_admissible_of_cons bot_mem_cl_of_not_cons hCut hmax,
         hmax.prop.2.2⟩

end SetExclusion

end Cslib.Logic.Metalogic
