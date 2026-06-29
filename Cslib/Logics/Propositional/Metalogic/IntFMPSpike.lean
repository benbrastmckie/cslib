/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness
public import Cslib.Logics.Propositional.Subformula

/-! # Phase 1 De-Risking Spike: Finite World Type and Finite Lindenbaum Witness

This is a **scratch spike file** for Task 370. It tests the two HIGH-risk obligations
gating the full FMP decidability construction:

1. `Fintype (IntFinWorld φ)` — that the type of Σ-bounded prime DCCS worlds is finite.
2. `int_fin_imp_witness` — the finite (Zorn-free) Lindenbaum extension witness.

No sorry is introduced in these two target lemmas. The rest of the construction is
stubbed or omitted. This file is NOT a committed deliverable; it is a go/no-go gate.
On GO, the validated definitions are promoted to `IntDecidability.lean`.

## Key Design Decisions

- `IntFinWorld φ` is a `structure` with `carrier : Finset (Proposition Atom)` plus
  Prop-valued fields (sub, closed, consistent, prime). Two worlds with the same carrier
  are equal by propext, making the carrier map injective.
- `Fintype (IntFinWorld φ)` uses `Fintype.ofInjective` with the carrier-into-powerset map.
  No decidability of `SetDerivable` is needed — the powerset is finite and the map is
  injective.
- `int_fin_imp_witness` uses the *infinite* canonical model: lift w to an IntDCCS T,
  apply `int_imp_witness` + `int_prime_exclusion`, then restrict T'' back to Σ.
  This avoids the need for a purely finite Lindenbaum construction.

## References

* Task 370 research report: specs/370_int_min_metalogic_decidability/reports/01_...
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u} [DecidableEq Atom]

attribute [local instance] Classical.propDecidable

/-! ## Σ-Bounded Finite World Type -/

/-- A `Σ`-bounded prime intuitionistic world, where `Σ := φ.subformulas`.

- `carrier`: a finset of formulas from Σ = subformulas φ
- `sub`: carrier ⊆ Σ
- `closed`: w is deductively closed within Σ (no undischarged Int derivations)
- `consistent`: ⊥ is not in the carrier (Int worlds are consistent)
- `prime`: the disjunction property within Σ

This structure determines a world for the finite canonical Kripke model of IPC.
Two worlds with the same carrier are equal (all other fields are Props). -/
structure IntFinWorld (φ : PL.Proposition Atom) where
  /-- The world's carrier: a finset of Σ-subformulas. -/
  carrier   : Finset (PL.Proposition Atom)
  /-- The carrier is a subset of the subformulas of φ. -/
  sub       : carrier ⊆ φ.subformulas
  /-- Deductive closure within Σ: if ψ is Int-derivable from the carrier
  and ψ is in Σ, then ψ ∈ carrier. -/
  closed    : ∀ ψ ∈ φ.subformulas,
      SetDerivable IntPropAxiom (↑carrier : Set (PL.Proposition Atom)) ψ → ψ ∈ carrier
  /-- Consistency: ⊥ is not in the carrier (Int worlds exclude falsum). -/
  consistent : (⊥ : PL.Proposition Atom) ∉ carrier
  /-- Primality: the carrier satisfies the disjunction property. -/
  prime     : ∀ a b : PL.Proposition Atom, (.or a b) ∈ carrier → a ∈ carrier ∨ b ∈ carrier

/-! ## Extensionality -/

/-- Two `IntFinWorld` structures with the same carrier are equal.

All fields other than `carrier` are Props, hence equal by propositional extensionality. -/
theorem IntFinWorld.ext {φ : PL.Proposition Atom} {w₁ w₂ : IntFinWorld φ}
    (h : w₁.carrier = w₂.carrier) : w₁ = w₂ := by
  cases w₁; cases w₂; congr

/-! ## Preorder -/

/-- The preorder on `IntFinWorld φ` is carrier inclusion. -/
instance instPreorderIntFinWorld (φ : PL.Proposition Atom) :
    Preorder (IntFinWorld φ) where
  le w₁ w₂ := w₁.carrier ⊆ w₂.carrier
  le_refl w := Finset.Subset.refl w.carrier
  le_trans _ _ _ h₁₂ h₂₃ := Finset.Subset.trans h₁₂ h₂₃

/-! ## Fintype Instance -/

/-- The carrier map `IntFinWorld φ → ↑(φ.subformulas.powerset)` is injective. -/
private theorem intFinWorld_carrier_injective (φ : PL.Proposition Atom) :
    Function.Injective
      (fun w : IntFinWorld φ =>
        (⟨w.carrier, Finset.mem_powerset.mpr w.sub⟩ :
          ↑(φ.subformulas.powerset))) :=
  fun w₁ w₂ h => IntFinWorld.ext (congrArg Subtype.val h)

/-- `IntFinWorld φ` is a `Fintype`: worlds embed injectively into the finite powerset `2^Σ`.

No decidability of `SetDerivable` is required — the injection bounds the count. -/
noncomputable instance instFintypeIntFinWorld (φ : PL.Proposition Atom) :
    Fintype (IntFinWorld φ) :=
  Fintype.ofInjective _ (intFinWorld_carrier_injective φ)

/-! ## Consistency Helper -/

/-- An `IntFinWorld` generates a propositionally consistent context.

Proof:
- If ⊥ ∈ φ.subformulas: w.closed gives SetDerivable ... ⊥ → ⊥ ∈ w.carrier;
  contrapositive from w.consistent gives ¬ SetDerivable ... ⊥.
- If ⊥ ∉ φ.subformulas: w.carrier ⊆ φ.subformulas means ⊥ ∉ w.carrier.
  All elements of w.carrier are ⊥-free, so under the all-True valuation
  all are satisfied; ⊥ (= False) is never derived. -/
theorem intFinWorld_propConsistent (φ : PL.Proposition Atom)
    (w : IntFinWorld φ) :
    PropSetConsistent IntPropAxiom (↑w.carrier : Set (PL.Proposition Atom)) := by
  -- PropSetConsistent = ¬ SetDerivable ... ⊥ essentially
  -- We prove ¬ SetDerivable IntPropAxiom ↑w.carrier ⊥
  intro L hLsub hLderiv
  -- From hLderiv : (propDerivationSystem IntPropAxiom).Deriv L ⊥
  -- Use int_soundness: since int derives ⊥, it is valid in every Int model
  -- But ⊥ is never forced (bot_forces = fun _ => False), contradiction.
  obtain ⟨d⟩ := hLderiv
  -- Lift the derivation through soundness
  -- All elements of L are in ↑w.carrier ⊆ ↑(φ.subformulas : Finset _)
  -- By int_soundness, ⊥ is forced at any world where L is satisfied
  -- In the trivial valuation (val = fun _ _ => False), no formula in L is forced
  -- unless L ∋ ⊥; but ⊥ ∉ w.carrier.
  -- More precisely: val = fun _ _ => True, bot_forces = fun _ => False
  -- Under this valuation, atom p → True always.
  -- By induction on propositions, if ⊥ ∉ formula, then IForces = True.
  -- So all elements of L ⊆ ↑w.carrier are forced, but ⊥ is not. ✗
  -- We formalize this via int_soundness applied to the all-True model.
  have h_forces_all : ∀ ψ ∈ L, IForces (fun _ _ => True) (fun _ => False) () ψ := by
    intro ψ hψ
    have hmem := hLsub ψ hψ
    simp only [Finset.coe_sort_coe, Set.mem_coe, Finset.mem_coe] at hmem
    -- ψ ∈ w.carrier ⊆ φ.subformulas; ψ is a ⊥-free subformula of φ
    -- Show IForces (fun _ _ => True) (fun _ => False) () ψ by structural induction
    have hwsub : ψ ∈ φ.subformulas := w.sub hmem
    clear hmem
    induction ψ with
    | atom p => simp [IForces]
    | bot =>
      -- ⊥ ∈ φ.subformulas but ⊥ ∉ w.carrier (from w.consistent)
      -- Actually we derive contradiction: ⊥ ∈ L ⊆ w.carrier contradicts consistent
      exfalso
      -- ψ = ⊥, hψ : ⊥ ∈ L, hLsub : L ⊆ ↑w.carrier
      exact w.consistent (hLsub (⊥) hψ)
    | imp a b iha ihb =>
      simp [IForces]
      intro _ _ _
      exact ihb (Proposition.IsSubformula.trans (Proposition.IsSubformula.imp_right) hwsub)
    | and a b iha ihb =>
      simp [IForces]
      exact ⟨iha (Proposition.IsSubformula.trans Proposition.IsSubformula.and_left hwsub),
             ihb (Proposition.IsSubformula.trans Proposition.IsSubformula.and_right hwsub)⟩
    | or a b iha ihb =>
      simp [IForces]
      exact Or.inl (iha (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hwsub))
  -- Now apply int_soundness to d
  have := int_soundness d (fun _ _ => True) (fun {_ _} p _ _ => trivial)
    () h_forces_all
  -- this says: IForces (fun _ _ => True) (fun _ => False) () .bot
  -- = (fun _ => False) () = False
  simp [IForces] at this

/-! ## Finite Imp Witness (Phase 1 Spike Target) -/

/-- **Finite Implication Witness** (the Phase 1 spike target).

Given a world `w : IntFinWorld φ` with `ψ → χ ∈ φ.subformulas` but `ψ → χ ∉ w.carrier`,
there exists a world `w' : IntFinWorld φ` with `w ≤ w'`, `ψ ∈ w'.carrier`, `χ ∉ w'.carrier`.

**Proof strategy** (via the infinite canonical model):
1. From `w.closed`: `¬ SetDerivable IntPropAxiom ↑w.carrier (ψ → χ)`.
2. The Int deductive closure of `↑w.carrier` is an IntDCCS (using consistency).
3. `int_imp_witness` gives an IntDCCS T ⊇ w.carrier with ψ ∈ T, χ ∉ T.
4. `int_prime_exclusion` gives a prime IntDCCS T'' ⊇ T with χ ∉ T''.
5. Restrict T'' to Σ: `w' := {ξ ∈ φ.subformulas | ξ ∈ T''}`.
6. Verify w' satisfies all IntFinWorld conditions.
7. w ≤ w' (carrier ⊆ T'' ∩ Σ = w'.carrier). ψ ∈ w'.carrier. χ ∉ w'.carrier.

This avoids Zorn's lemma for the finite model — we use the infinite Lindenbaum
result and restrict back to Σ. -/
theorem int_fin_imp_witness (φ : PL.Proposition Atom)
    (w : IntFinWorld φ) {ψ χ : PL.Proposition Atom}
    (hmem : (.imp ψ χ) ∈ φ.subformulas)
    (hnot : (.imp ψ χ) ∉ w.carrier) :
    ∃ w' : IntFinWorld φ, w ≤ w' ∧ ψ ∈ w'.carrier ∧ χ ∉ w'.carrier := by
  -- Step 1: ψ → χ ∉ intDeductiveClosure ↑w.carrier
  have h_not_sd : ¬ SetDerivable IntPropAxiom (↑w.carrier : Set (PL.Proposition Atom))
      (ψ.imp χ) := by
    intro h_sd
    exact hnot (w.closed (ψ.imp χ) hmem h_sd)
  -- Step 2: Consistency of ↑w.carrier
  have h_cons : PropSetConsistent IntPropAxiom (↑w.carrier : Set (PL.Proposition Atom)) :=
    intFinWorld_propConsistent φ w
  -- Step 3: Form the IntDCCS from the deductive closure
  have h_dccs : IntDCCS (intDeductiveClosure (↑w.carrier : Set (PL.Proposition Atom))) :=
    intDeductiveClosure_is_dccs h_cons
  -- Step 4: ψ → χ ∉ intDeductiveClosure ↑w.carrier (= SetDerivable condition)
  have h_not_dc : (ψ.imp χ) ∉ intDeductiveClosure (↑w.carrier : Set (PL.Proposition Atom)) :=
    h_not_sd
  -- Step 5: Apply int_imp_witness to get T ⊇ DC(w) with ψ ∈ T, χ ∉ T
  obtain ⟨T, hDCT, hT_dccs, hψT, hχT⟩ :=
    int_imp_witness h_dccs h_not_dc
  -- Step 6: Apply int_prime_exclusion to get prime T'' ⊇ T with χ ∉ T''
  obtain ⟨T'', hTT'', hT''_prime, hχT''⟩ :=
    int_prime_exclusion hT_dccs hχT
  -- Step 7: Restrict T'' to Σ = φ.subformulas
  -- w'.carrier = φ.subformulas.filter (· ∈ T'')
  let carrier' : Finset (PL.Proposition Atom) :=
    φ.subformulas.filter (fun ξ => ξ ∈ T'')
  -- Build w'
  have sub' : carrier' ⊆ φ.subformulas :=
    Finset.filter_subset _ _
  have closed' : ∀ ψ' ∈ φ.subformulas,
      SetDerivable IntPropAxiom (↑carrier' : Set (PL.Proposition Atom)) ψ' → ψ' ∈ carrier' := by
    intro ψ' hψ'mem h_sd'
    simp only [carrier', Finset.mem_filter]
    refine ⟨hψ'mem, ?_⟩
    -- SetDerivable from ↑carrier' ⊆ ↑T'' (as sets)
    have h_sub_set : (↑carrier' : Set (PL.Proposition Atom)) ⊆ ↑T'' := by
      intro ξ hξ
      simp only [carrier', Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
        Finset.mem_filter] at hξ
      exact hξ.2
    -- Weaken the derivation to T''
    have h_sd_T'' : SetDerivable IntPropAxiom (↑T'') ψ' :=
      SetDerivable_weakening h_sub_set h_sd'
    -- Since T'' is an IntDCCS, ψ' ∈ T''
    exact hT''_prime.1.2 (h_sd_T''.choose) ψ'
      (h_sd_T''.choose_spec.1) (h_sd_T''.choose_spec.2)
  have consistent' : (⊥ : PL.Proposition Atom) ∉ carrier' := by
    simp only [carrier', Finset.mem_filter, not_and]
    intro _
    exact int_dccs_bot_not_mem hT''_prime.1
  have prime' : ∀ a b : PL.Proposition Atom,
      (.or a b) ∈ carrier' → a ∈ carrier' ∨ b ∈ carrier' := by
    intro a b hab
    simp only [carrier', Finset.mem_filter] at hab ⊢
    have ⟨hab_sub, hab_T''⟩ := hab
    rcases hT''_prime.2 a b hab_T'' with ha | hb
    · left
      exact ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hab_sub, ha⟩
    · right
      exact ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hab_sub, hb⟩
  let w' : IntFinWorld φ := ⟨carrier', sub', closed', consistent', prime'⟩
  -- Step 8: w ≤ w' (w.carrier ⊆ carrier')
  have h_le : w ≤ w' := by
    intro ξ hξ
    simp only [w', carrier', Finset.mem_filter]
    refine ⟨w.sub hξ, ?_⟩
    -- ξ ∈ w.carrier ⊆ ↑(intDeductiveClosure ↑w.carrier)
    -- ⊆ T ⊆ T''
    have h1 : ξ ∈ intDeductiveClosure (↑w.carrier : Set (PL.Proposition Atom)) :=
      int_subset_deductive_closure (↑w.carrier) (by exact_mod_cast hξ)
    exact hTT'' (hDCT h1)
  -- Step 9: ψ ∈ w'.carrier
  have hψ : ψ ∈ w'.carrier := by
    simp only [w', carrier', Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact Proposition.IsSubformula.trans Proposition.IsSubformula.imp_left hmem
    · exact hTT'' hψT
  -- Step 10: χ ∉ w'.carrier
  have hχ : χ ∉ w'.carrier := by
    simp only [w', carrier', Finset.mem_filter, not_and]
    intro _
    exact hχT''
  exact ⟨w', h_le, hψ, hχ⟩

end Cslib.Logic.PL

end
