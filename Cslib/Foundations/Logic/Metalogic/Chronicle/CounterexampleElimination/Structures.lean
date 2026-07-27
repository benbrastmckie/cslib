/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.Chronicle.RRelation
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith

/-! # Generic CEE Foundation — Fresh-Rational Helpers and `BurgessR3Maximal` Helper Lemmas

Generic version of the fresh-rational Finset helpers and the MCS-level `BurgessR3Maximal`
helper lemmas shared verbatim (modulo `fc`) between
`Logics/Bimodal/.../Chronicle/CounterexampleElimination/{Structures,BurgessHelpers}.lean`
and `Logics/Temporal/.../Chronicle/CounterexampleElimination/Structures.lean`.
Both trees instantiate this module and re-export its declarations under their existing
names.

## Kept logic-local (NOT lifted here)

`C5Counterexample`/`C5'Counterexample` are `structure`s indexed by `Chronicle F`, whose
fields (`.f`/`.dom`) this generalization effort deliberately kept logic-local (a
`toGeneric` bridge broke downstream `rcases`/`simp` proofs — see `ChronicleTypes.lean`'s
"Chronicle Structure" section). Genericizing these two ~15-line structures would require
either reintroducing that bridge (same regression risk, since these structures are
pattern-matched constantly by the walk/elimination proofs) or a new second bridge layer
for near-zero duplication savings; both trees keep them verbatim instead, per the
sanctioned "keep logic-local rather than risk the abstraction" contingency.

`c2'_preserved_on_old_adjacent` has the same `Chronicle`-locality issue (it pattern-matches
`χ.f`/`χ.g` values against `Adjacent`) and stays logic-local in both trees.

`burgessR3Maximal_from_h_content_sub` depends on the duality theorem
`g_content_sub_imp_h_content_sub'`/`h_content_sub_imp_g_content_sub'`, which is already
earmarked as logic-local ("add to temporal only if the same axioms are available there").
To avoid a forward dependency onto that earmarking decision,
`burgessR3Maximal_from_h_content_sub` also stays logic-local in both trees (it is
`private` in both, so no cross-tree naming-conflict risk either way).

## References

* Ported from `Bimodal/.../Chronicle/CounterexampleElimination/{Structures,BurgessHelpers}.lean`
  and `Temporal/.../Chronicle/CounterexampleElimination/Structures.lean`.
* Burgess 1982: "Axioms for tense logic II: Time periods", Section 2.
-/

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Metalogic.Chronicle

attribute [local instance] Classical.propDecidable

variable {F : Type*}

/-! ## Helper: Finding Fresh Rationals

Zero `ChronicleInterface`/`Formula` dependency — pure `Finset Rat` lemmas, identical in
both trees. -/

/--
There exists a rational strictly greater than all elements of a finite set
of rationals. (The rationals are unbounded above.)
-/
theorem exists_rat_gt_finset (fs : Finset Rat) :
    ∃ q : Rat, (∀ s ∈ fs, s < q) ∧ q ∉ fs := by
  by_cases h : fs.Nonempty
  · refine ⟨fs.max' h + 1, ?_, ?_⟩
    · intro s hs
      calc s ≤ fs.max' h := Finset.le_max' fs s hs
        _ < fs.max' h + 1 := lt_add_one _
    · intro hmem
      have h1 := Finset.le_max' fs _ hmem
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact ⟨0, fun s hs => absurd hs (by simp), (by simp)⟩

/--
There exists a rational strictly less than all elements of a finite set
of rationals. (The rationals are unbounded below.)
-/
theorem exists_rat_lt_finset (fs : Finset Rat) :
    ∃ q : Rat, (∀ s ∈ fs, q < s) ∧ q ∉ fs := by
  by_cases h : fs.Nonempty
  · refine ⟨fs.min' h - 1, ?_, ?_⟩
    · intro s hs
      calc fs.min' h - 1 < fs.min' h := sub_one_lt _
        _ ≤ s := Finset.min'_le fs s hs
    · intro hmem
      have h1 := Finset.min'_le fs _ hmem
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact ⟨0, fun s hs => absurd hs (by simp), (by simp)⟩

/--
There exists a rational strictly between x and y that is NOT in a finite set fs.
Since fs is finite and Q is dense, the open interval (x,y) is infinite while
fs ∩ (x,y) is finite, so there must be a point outside fs.

We construct it explicitly: take z = (x + y) / 2. If z ∉ fs, done. Otherwise,
the interval (x, z) still has no elements of fs strictly between x and z that
block finding a midpoint — but we use a simpler argument: among the finitely
many points of fs in [x,y], there must be a gap, and the midpoint of that gap
works. We use the simpler approach: (x + y) / 2 works when Adjacent, and for
the general case we find any gap in the finite set fs within (x,y).
-/
theorem exists_rat_between_not_in_finset (fs : Finset Rat) (x y : Rat) (hxy : x < y) :
    ∃ z : Rat, x < z ∧ z < y ∧ z ∉ fs := by
  -- The set of fs-elements strictly between x and y
  set T := fs.filter (fun s => x < s ∧ s < y) with hT_def
  by_cases hT : T.Nonempty
  · -- There are fs-elements between x and y. Find the minimum, take midpoint with x.
    set t := T.min' hT with ht_def
    have ht_mem : t ∈ T := Finset.min'_mem T hT
    have ht_prop : x < t ∧ t < y := by
      rw [hT_def] at ht_mem; exact (Finset.mem_filter.mp ht_mem).2
    -- z = (x + t) / 2 is strictly between x and t, hence between x and y
    set z := (x + t) / 2 with hz_def
    have hxz : x < z := by linarith
    have hzt : z < t := by linarith
    have hzy : z < y := lt_trans hzt ht_prop.2
    refine ⟨z, hxz, hzy, ?_⟩
    -- z ∉ fs because z < t = min of fs-elements in (x,y), and z > x
    intro hz_mem
    have hz_in_T : z ∈ T := by
      rw [hT_def]; exact Finset.mem_filter.mpr ⟨hz_mem, hxz, hzy⟩
    have : t ≤ z := Finset.min'_le T z hz_in_T
    linarith
  · -- No fs-elements between x and y. Midpoint works.
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    set z := (x + y) / 2 with hz_def
    have hxz : x < z := by linarith
    have hzy : z < y := by linarith
    refine ⟨z, hxz, hzy, ?_⟩
    intro hz_mem
    have : z ∈ T := by
      rw [hT_def]; exact Finset.mem_filter.mpr ⟨hz_mem, hxz, hzy⟩
    rw [hT] at this
    exact absurd this (by simp)

/-! ## `BurgessR3Maximal` MCS-Level Helper Lemmas -/

/--
**`BurgessR3Maximal` implies `gContent` subset**: If `BurgessR3Maximal(A, B, C)` holds with
`A` and `C` both MCS, then `gContent A ⊆ C`.

Proof: Suppose `G(φ) ∈ A` but `φ ∉ C`. Then `φ.neg ∈ C` (MCS). Since `B` is CUD, `⊤ ∈ B` (a
theorem is in any CUD set). From `burgessRSet(A, B, C)`: `untl(⊤, φ.neg) ∈ A`. By BX10
(`until_F`), `F(φ.neg) ∈ A`. But `G(φ) ∈ A` gives `¬F(φ.neg) ∈ A` (by `G = ¬F¬` equivalence
in MCS), contradicting consistency of `A`.
-/
theorem burgessR3Maximal_g_content_sub (I : ChronicleInterface F) {A B C : Set F}
    (h_r3m : CIBurgessR3Maximal I A B C)
    (h_mcs_A : CISetMaximalConsistent I A) (h_mcs_C : CISetMaximalConsistent I C) :
    ciGContent I A ⊆ C := by
  intro φ hφ
  -- hφ : G(φ) ∈ A, i.e., allFuture(φ) ∈ A
  change I.allFuture φ ∈ A at hφ
  -- Suppose φ ∉ C, derive contradiction
  by_contra h_not_C
  have h_neg_C : I.imp φ I.bot ∈ C := by
    rcases I.negationComplete h_mcs_C φ with h | h
    · exact absurd h h_not_C
    · exact h
  -- ⊤ ∈ B (CUD contains all theorems)
  set top := I.imp I.bot I.bot with top_def
  have h_top_B : top ∈ B :=
    cud_contains_theorems I h_r3m.1 (I.identity' I.bot)
  -- burgessRSet(A, B, C): ∀ β ∈ B, ∀ γ ∈ C, untl(β, γ) ∈ A
  have hUntl : I.untl top (I.imp φ I.bot) ∈ A :=
    h_r3m.2.1.1 top h_top_B (I.imp φ I.bot) h_neg_C
  -- BX10: untl(γ, δ) ∈ A → F(δ) ∈ A, here F(φ.neg) ∈ A
  have h_F_neg : I.someFuture (I.imp φ I.bot) ∈ A :=
    until_implies_F_in_mcs I h_mcs_A hUntl
  -- G(φ) ∈ A implies F(φ.neg) ∉ A
  -- F(φ.neg) = someFuture(φ.neg) = (allFuture(φ.neg.neg)).neg
  -- G(φ) ∈ A → G(φ.neg.neg) ∈ A (by φ → ¬¬φ inside G) → F(φ.neg) ∉ A
  -- Derive ⊢ φ → ¬¬φ, i.e., ⊢ φ → ((φ → ⊥) → ⊥)
  -- This is ⊢ φ → ((φ → ⊥) → ⊥), which follows from prop_s, prop_k, identity
  have h_dni : I.Deriv [] (I.imp φ (I.imp (I.imp φ I.bot) I.bot)) := by
    -- φ.neg.neg = (φ.imp bot).imp bot
    -- Need: ⊢ φ → ((φ → ⊥) → ⊥)
    -- Proof: by deduction, assume φ.neg and φ, apply to get ⊥
    have h1 : I.Deriv [I.imp φ I.bot, φ] I.bot :=
      I.modusPonens
        (I.assumption (Γ := [I.imp φ I.bot, φ]) (φ := I.imp φ I.bot) (by simp))
        (I.assumption (Γ := [I.imp φ I.bot, φ]) (φ := φ) (by simp))
    have h2 : I.Deriv [φ] (I.imp (I.imp φ I.bot) I.bot) :=
      I.deductionTheorem [φ] (I.imp φ I.bot) I.bot h1
    exact I.deductionTheorem [] φ (I.imp (I.imp φ I.bot) I.bot) h2
  -- G(φ → ¬¬φ) and temp_k_dist give G(φ) → G(¬¬φ)
  have h_G_dni : I.Deriv [] (I.allFuture (I.imp φ (I.imp (I.imp φ I.bot) I.bot))) :=
    I.futureNecessitation _ h_dni
  have h_kd : I.Deriv [] (I.imp (I.allFuture (I.imp φ (I.imp (I.imp φ I.bot) I.bot)))
      (I.imp (I.allFuture φ) (I.allFuture (I.imp (I.imp φ I.bot) I.bot)))) :=
    I.futureKDist φ (I.imp (I.imp φ I.bot) I.bot)
  have h1 := I.theoremInMcs h_mcs_A h_G_dni
  have h2 := I.theoremInMcs h_mcs_A h_kd
  have h3 := dcs_modus_ponens I (mcs_is_dcs I h_mcs_A) h2 h1
  have h_G_nn : I.allFuture (I.imp (I.imp φ I.bot) I.bot) ∈ A :=
    dcs_modus_ponens I (mcs_is_dcs I h_mcs_A) h3 hφ
  -- F(¬φ) and G(¬¬φ) = G(neg(φ.neg)) are contradictory in MCS A
  exact I.someFutureAllFutureNegAbsurd h_mcs_A (I.imp φ I.bot) h_F_neg h_G_nn

/--
**`BurgessR3Maximal` implies `SetDeductivelyClosed`** when some formula is not in `B`.
Since `B` is CUD (from `BurgessR3Maximal`) and `phi` not in `B`, `B` is not `Set.univ`,
hence consistent.
-/
theorem burgessR3Maximal_sdc (I : ChronicleInterface F) {A B C : Set F}
    (h_r3m : CIBurgessR3Maximal I A B C)
    {phi : F} (h_not_mem : phi ∉ B) :
    SetDeductivelyClosed I B :=
  cud_not_mem_is_sdc I h_r3m.1 h_not_mem

/--
**`BurgessR3Maximal` excludes `⊥` when `B` is consistent**: In Burgess's framework,
g-values are DCS (deductively closed sets = consistent + CUD). When `B` is
known to be `CISetConsistent`, `⊥ ∉ B` follows directly: if `⊥ ∈ B`, then
the singleton list `[⊥]` witnesses inconsistency via the identity derivation.

The consistency hypothesis `h_cons` must be discharged at call sites.
In the omega chain, g-value consistency is established through the
chronicle construction in `ChronicleConstruction.lean`.

See Burgess 1982, Section 2: "g is a function from {(x,y) : x,y ∈ dom f,
x < y} to the set of all DCSs" where DCS = deductively closed set
(consistent + CUD).
-/
theorem burgessR3Maximal_bot_not_mem (I : ChronicleInterface F) {A B C : Set F}
    (_h_r3m : CIBurgessR3Maximal I A B C)
    (h_cons : CISetConsistent I B) :
    I.bot ∉ B := by
  intro h_bot
  exact h_cons [I.bot] (fun φ hφ => by simp at hφ; rw [hφ]; exact h_bot)
    ⟨I.assumption (by simp)⟩

end Cslib.Logic.Metalogic.Chronicle

end
