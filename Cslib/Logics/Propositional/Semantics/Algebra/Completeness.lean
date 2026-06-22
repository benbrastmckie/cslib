/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra.Lindenbaum

/-! # Algebraic Completeness for Propositional Logic

This module proves algebraic completeness for propositional logic across three tiers:
- **MPL** (Minimal Propositional Logic) is complete w.r.t. `GeneralizedHeytingAlgebra`.
- **IPL** (Intuitionistic Propositional Logic) is complete w.r.t. `HeytingAlgebra`.
- **CPL** (Classical Propositional Logic) is complete w.r.t. `BooleanAlgebra`.

The completeness theorems are stated using `AlgTValid` (Thomas Waring's `v ⊨ T` parametric
completeness style), which quantifies over all valuations that model the theory.

The soundness proof uses the "universal lower bound" formulation:
`T ⊢ Γ ⊢ A → ∀ Φ, (∀ B ∈ Γ, Φ ≤ eval B) → Φ ≤ eval A`

This handles the `orE` case via distributivity of `GeneralizedHeytingAlgebra`.

## Future Work

Hilbert-level corollaries (`Derivable MinPropAxiom φ ↔ GHAValid φ`, etc.) require bridging
the Hilbert axiomatic system (`DerivationTree`/`Derivable`) with the natural deduction system
(`Theory.Derivation`/`DerivableIn`). This equivalence is nontrivial and deferred.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Heyting

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

/-! ## Canonical Valuation -/

/-- The canonical valuation for the Lindenbaum algebra: maps each atom `x` to the equivalence
class of the atomic formula `atom x` in the Lindenbaum–Tarski algebra of `T`. -/
def Theory.canonicalV (T : Theory Atom) : Atom → LindenbaumAlgebra T :=
  fun x => lindenbaumMk T (.atom x)

/-- The canonical bottom value for the Lindenbaum algebra: the equivalence class of `⊥`.
For intuitionistic and classical theories (`[IsIntuitionistic T]`), this equals the
algebraic bottom element `⊥` of the Heyting algebra (see `canonicalBotVal_eq`). -/
def Theory.canonicalBotVal (T : Theory Atom) : LindenbaumAlgebra T :=
  lindenbaumMk T .bot

/-- For intuitionistic theories, the canonical bottom value equals the Heyting algebra bottom `⊥`.
This relies on `lindenbaumBot`, which identifies `[⊥]` with `⊥` when `[IsIntuitionistic T]`. -/
theorem Theory.canonicalBotVal_eq [IsIntuitionistic T] :
    T.canonicalBotVal = (⊥ : LindenbaumAlgebra T) := by
  simp [Theory.canonicalBotVal, lindenbaumBot]

/-! ## Truth Lemma -/

/-- Truth lemma: evaluating any formula `A` under the canonical valuation and canonical bottom value
gives exactly the equivalence class `[A]` in the Lindenbaum algebra.
This is the key fact linking syntax and semantics in the completeness proof. -/
theorem Theory.canonicalV_spec (T : Theory Atom) (A : Proposition Atom) :
    AlgEvaluate (T.canonicalV) (T.canonicalBotVal) A = lindenbaumMk T A := by
  induction A with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb =>
    simp only [AlgEvaluate_imp, iha, ihb, lindenbaumMk_himp]
  | and a b iha ihb =>
    simp only [AlgEvaluate_and, iha, ihb, lindenbaumMk_inf]
  | or a b iha ihb =>
    simp only [AlgEvaluate_or, iha, ihb, lindenbaumMk_sup]

/-! ## Canonical Valuation Models the Theory -/

/-- The canonical valuation models the theory `T`: every axiom `B ∈ T` evaluates to the top
element `⊤` of the Lindenbaum algebra under the canonical valuation and canonical bottom value.
This ensures the canonical model is a valid algebraic model of `T`. -/
theorem Theory.tValid_canonicalV (T : Theory Atom) :
    AlgTValid T (T.canonicalV) (T.canonicalBotVal) := by
  intro B hB
  rw [canonicalV_spec, lindenbaumTop]
  apply le_antisymm
  · rw [lindenbaumMk_le_mk]; exact ⟨Theory.derivationTop.weakCtx (by simp)⟩
  · rw [lindenbaumMk_le_mk]; exact ⟨Derivation.ax hB⟩

/-! ## ND-Level Soundness (Meet Formulation) -/

/-- Auxiliary soundness lemma (meet / universal-lower-bound formulation). Given a derivation `d`
of `Γ ⊢ A` and a lower bound `Φ` below each formula in `Γ`, we have `Φ ≤ eval A`.

This "meet formulation" of soundness handles the `orE` case cleanly: distributivity of
`GeneralizedHeytingAlgebra` (`inf_sup_left`) gives `Φ ⊓ (a ⊔ b) ≤ c` from
`Φ ⊓ a ≤ c` and `Φ ⊓ b ≤ c`. -/
theorem nd_alg_sound_aux
    {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H)
    (hT : AlgTValid T v bot_val)
    {Γ : Finset (Proposition Atom)} {A : Proposition Atom}
    (d : T.Derivation Γ A) :
    ∀ (Φ : H), (∀ B ∈ Γ, Φ ≤ AlgEvaluate v bot_val B) → Φ ≤ AlgEvaluate v bot_val A := by
  induction d with
  | ax hA =>
    intro Φ _
    rw [hT _ hA]
    exact le_top
  | ass hA =>
    intro Φ hΓ
    exact hΓ _ hA
  | andI G dL dR ihL ihR =>
    intro Φ hΓ
    simp only [AlgEvaluate_and]
    exact le_inf (ihL Φ hΓ) (ihR Φ hΓ)
  | andE1 G dAB ih =>
    intro Φ hΓ
    calc Φ ≤ AlgEvaluate v bot_val _ ⊓ AlgEvaluate v bot_val _ := by
              simpa [AlgEvaluate_and] using ih Φ hΓ
         _ ≤ AlgEvaluate v bot_val _ := inf_le_left
  | andE2 G dAB ih =>
    intro Φ hΓ
    calc Φ ≤ AlgEvaluate v bot_val _ ⊓ AlgEvaluate v bot_val _ := by
              simpa [AlgEvaluate_and] using ih Φ hΓ
         _ ≤ AlgEvaluate v bot_val _ := inf_le_right
  | orI1 G dA ih =>
    intro Φ hΓ
    simp only [AlgEvaluate_or]
    exact (ih Φ hΓ).trans le_sup_left
  | orI2 G dB ih =>
    intro Φ hΓ
    simp only [AlgEvaluate_or]
    exact (ih Φ hΓ).trans le_sup_right
  | orE G dDisj dLeft dRight ihDisj ihLeft ihRight =>
    intro Φ hΓ
    have h1 := ihDisj Φ hΓ
    simp only [AlgEvaluate_or] at h1
    have h2 : Φ ⊓ AlgEvaluate v bot_val _ ≤ AlgEvaluate v bot_val _ :=
      ihLeft (Φ ⊓ _) (fun B hB => by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact inf_le_right
        · exact (inf_le_left).trans (hΓ B hB))
    have h3 : Φ ⊓ AlgEvaluate v bot_val _ ≤ AlgEvaluate v bot_val _ :=
      ihRight (Φ ⊓ _) (fun B hB => by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact inf_le_right
        · exact (inf_le_left).trans (hΓ B hB))
    have key : Φ ⊓ _ ⊔ Φ ⊓ _ ≤ _ := sup_le h2 h3
    rw [← inf_sup_left] at key
    exact le_trans (le_inf le_rfl h1) key
  | impI Γ d ih =>
    intro Φ hΓ
    simp only [AlgEvaluate_imp]
    rw [le_himp_iff]
    apply ih (Φ ⊓ AlgEvaluate v bot_val _)
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact inf_le_right
    · exact (inf_le_left).trans (hΓ C hC)
  | impE dAB dA ihAB ihA =>
    intro Φ hΓ
    simp only [AlgEvaluate_imp] at ihAB
    have hAB : Φ ≤ AlgEvaluate v bot_val _ ⇨ AlgEvaluate v bot_val _ := ihAB Φ hΓ
    have hA : Φ ≤ AlgEvaluate v bot_val _ := ihA Φ hΓ
    exact (le_inf hAB hA).trans himp_inf_le

/-! ## ND-Level Soundness (Consequence Form) -/

/-- ND-level algebraic soundness (consequence form). If `A` is derivable in `T` then for every
`GeneralizedHeytingAlgebra H`, every valuation `v : Atom → H`, and every `bot_val : H` such that
`AlgTValid T v bot_val` holds, we have `AlgEvaluate v bot_val A = ⊤`. -/
theorem nd_alg_sound {A : Proposition Atom}
    (h : DerivableIn T A)
    {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H)
    (hT : AlgTValid T v bot_val) :
    AlgEvaluate v bot_val A = ⊤ := by
  obtain ⟨d⟩ := h
  apply top_le_iff.mp
  apply nd_alg_sound_aux v bot_val hT d ⊤
  intro B hB
  simp at hB

/-! ## General Algebraic Completeness -/

/-- A formula `A` maps to `⊤` in the Lindenbaum algebra if and only if `A` is derivable in `T`.
This is the central algebraic characterization of derivability used in the completeness proof. -/
theorem lindenbaumMk_eq_top_iff {A : Proposition Atom} :
    lindenbaumMk T A = ⊤ ↔ DerivableIn T A := by
  rw [lindenbaumTop]
  constructor
  · intro h
    have heq := Quotient.exact h
    have hBot : DerivableIn T ({.imp .bot .bot} ⊢ A) := Equiv.mpr heq
    have hCut : DerivableIn T ((∅ ∪ ∅) ⊢ A) :=
      DerivableIn.cut ⟨Theory.derivationTop⟩ hBot
    exact DerivableIn.weakCtx (by simp) hCut
  · intro ⟨d⟩
    exact Quotient.sound (Theory.equiv_iff.mpr ⟨
      ⟨Theory.derivationTop.weakCtx (by grind)⟩,
      ⟨d.weakCtx (by grind)⟩⟩)

/-- General algebraic completeness for propositional logic. A formula `A` is derivable in `T`
(w.r.t. the natural deduction system) if and only if it evaluates to `⊤` in every
`GeneralizedHeytingAlgebra` under every valuation that models `T`.

The completeness direction uses the Lindenbaum algebra as a canonical countermodel:
if `A` is not derivable then `[A] ≠ ⊤` in `LindenbaumAlgebra T`. -/
theorem Theory.alg_complete {A : Proposition Atom} :
    DerivableIn T A ↔
      ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
        AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤ := by
  constructor
  · intro hDeriv _ _ v bot_val hT
    exact nd_alg_sound hDeriv v bot_val hT
  · intro hValid
    have hLind : AlgEvaluate (T.canonicalV) (T.canonicalBotVal) A = ⊤ :=
      hValid (T.canonicalV) (T.canonicalBotVal) (T.tValid_canonicalV)
    rw [canonicalV_spec] at hLind
    exact lindenbaumMk_eq_top_iff.mp hLind

/-! ## Tier-Specific Completeness -/

/-- MPL algebraic completeness: a formula `A` is derivable in MPL (empty theory) if and only if
`AlgEvaluate v bot_val A = ⊤` for every `GeneralizedHeytingAlgebra`, every valuation `v`, and
every `bot_val`. In MPL there are no theory axioms to satisfy, so no `AlgTValid` hypothesis
is needed. -/
theorem MPL.alg_complete {Atom : Type u} [DecidableEq Atom] {A : Proposition Atom} :
    DerivableIn (∅ : Theory Atom) A ↔
      ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
        AlgEvaluate v bot_val A = ⊤ := by
  constructor
  · intro hDeriv _ _ v bot_val
    exact nd_alg_sound hDeriv v bot_val (fun _ hB => (Set.mem_empty_iff_false _).mp hB |>.elim)
  · intro hValid
    exact Theory.alg_complete.mpr fun v bot_val _ =>
      hValid v bot_val

/-- IPL algebraic completeness: a formula `A` is derivable in IPL if and only if
`AlgEvaluate v ⊥ A = ⊤` for every `HeytingAlgebra H` and every valuation `v`.
The `bot_val` is fixed to `⊥ : H` because IPL requires that the interpretation of `⊥`
is the bottom element (the efq axiom forces this). -/
theorem IPL.alg_complete {Atom : Type u} [DecidableEq Atom] {A : Proposition Atom} :
    DerivableIn (IPL : Theory Atom) A ↔
      ∀ {H : Type u} [HeytingAlgebra H] (v : Atom → H),
        AlgEvaluate v (⊥ : H) A = ⊤ := by
  constructor
  · intro hDeriv _ _ v
    apply nd_alg_sound hDeriv v ⊥
    intro B hB
    obtain ⟨C, rfl⟩ := Set.mem_range.mp hB
    simp [AlgEvaluate]
  · intro hValid
    have h := hValid (H := LindenbaumAlgebra (IPL : Theory Atom))
        (IPL (Atom := Atom)).canonicalV
    rw [← (IPL (Atom := Atom)).canonicalBotVal_eq,
        canonicalV_spec, lindenbaumMk_eq_top_iff] at h
    exact h

/-- Algebraic completeness for classical theories: if `T` is both intuitionistic
(`[IsIntuitionistic T]`) and classical (`[IsClassical T]`, i.e., includes DNE), then `A` is
derivable in `T` if and only if `AlgEvaluate v ⊥ A = ⊤` for every `BooleanAlgebra H` and every
valuation `v` that models `T`. This covers CPL as the canonical instance. -/
theorem alg_complete_classical [IsIntuitionistic T] [IsClassical T] {A : Proposition Atom} :
    DerivableIn T A ↔
      ∀ {H : Type u} [BooleanAlgebra H] (v : Atom → H),
        (∀ B ∈ T, AlgEvaluate v (⊥ : H) B = ⊤) → AlgEvaluate v (⊥ : H) A = ⊤ := by
  constructor
  · intro hDeriv _ _ v hT
    exact nd_alg_sound hDeriv v ⊥ hT
  · intro hValid
    have h := hValid (H := LindenbaumAlgebra T) T.canonicalV (fun B hB => by
        rw [← T.canonicalBotVal_eq, canonicalV_spec, lindenbaumMk_eq_top_iff]
        exact ⟨Derivation.ax hB⟩)
    rw [← T.canonicalBotVal_eq, canonicalV_spec, lindenbaumMk_eq_top_iff] at h
    exact h

end Cslib.Logic.PL
