/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness
public import Cslib.Logics.Propositional.Subformula
public import Mathlib.Data.Finset.Powerset

/-! # Finite Model Property and Decidability for Intuitionistic Propositional Logic

This module establishes sorry-free decidability of `Derivable IntPropAxiom φ` via the
finite model property (FMP). The key insight is a direct finite canonical Kripke model
construction: worlds are `Σ`-bounded prime deductively-closed sets where `Σ := φ.subformulas`.

## Main Results

- `IntFinWorld φ`: The type of `Σ`-bounded prime intuitionistic worlds.
- `instFintypeIntFinWorld`: `IntFinWorld φ` is a `Fintype` (worlds embed injectively into
  the finite powerset `2^Σ`).
- `int_fin_imp_witness`: Finite Lindenbaum implication witness, constructed by lifting to
  the infinite canonical model and restricting back to `Σ`.
- `int_fin_truth_lemma`: Truth lemma for the finite canonical model.
- `int_fmp`: `Derivable IntPropAxiom φ ↔ ∀ w : IntFinWorld φ, φ ∈ w.carrier`.
- `decidableDerivableIntPropAxiomFMP`: A sorry-free `noncomputable def` (not a registered
  instance) for `Derivable IntPropAxiom φ` via the FMP, independent of the tableau completeness
  witnesses. The canonical registered `Decidable` instance is in
  `Tableau/Intuitionistic/DecisionProcedure.lean` (`instDecidableDerivableIntPropAxiom`).

## Design Decisions

- The `closed` field references `SetDerivable` (a Prop over unbounded derivations). To keep
  `Fintype` we do NOT decide `SetDerivable`; instead, worlds embed injectively into the
  finite powerset via the carrier map.
- The finite Lindenbaum witness uses the **infinite** canonical model: lift to an infinite
  prime DCCS via `int_imp_witness` + `int_prime_exclusion`, then restrict back to `Σ`. This
  avoids Zorn's lemma for finite models entirely.

## Two Decision Routes — Distinct Roles

CSLib contains **two independent decision procedures** for `Derivable IntPropAxiom φ`:

### Route 1 (FMP — this module)
- **Module**: `Metalogic/IntDecidability.lean`
- **Mechanism**: Finite model property via a `Σ`-bounded finite canonical Kripke model
  (`IntFinWorld φ`). Decides by checking `∀ w : IntFinWorld φ, φ ∈ w.carrier`.
- **Axiom profile**: `{propext, Classical.choice, Quot.sound}` — **sorry-free**.
- **Exposed as**: `decidableDerivableIntPropAxiomFMP` (`noncomputable def`, not a registered
  instance). Also see `int_fmp` (the FMP biconditional) and `int_fin_truth_lemma`.
- **Role**: Independent theoretical result; the FMP route does not use tableaux or
  branch-saturation. Useful as a correctness witness for the tableau approach.
- **Companion**: `decidableDerivableMinPropAxiomFMP` in `Metalogic/MinDecidability.lean`.

### Route 2 (Tableau — canonical registered instance)
- **Module**: `Tableau/Intuitionistic/DecisionProcedure.lean`
- **Mechanism**: Constructive signed-tableau proof-search with countermodel extraction.
  Decides via `instDecidableIValid` composed with `int_soundness_completeness`.
- **Axiom profile**: `{propext, Classical.choice, Quot.sound}` — **sorry-free**. The completeness
  chain this route rests on (`openBranch_countermodel`'s existential in `Scheme.lean`,
  `intuitionisticTableau_complete` in `Intuitionistic/Completeness.lean`, and
  `minimalTableau_complete` in `Minimal/Completeness.lean`) is fully discharged.
- **Exposed as**: `instDecidableDerivableIntPropAxiom` (the **sole registered `Decidable`
  instance** for `Derivable IntPropAxiom φ`).
- **Role**: Canonical extension-facing instance. The modal, temporal, and bimodal extensions
  import the propositional embedding layer and rely on this instance for automation.

The two routes have **disjoint carrier types** (`IntFinWorld` vs signed-branch world machinery)
and independent proof lineages. Factoring a common truth-lemma abstraction is explicitly
deferred (high risk, low payoff while 317 is open). See `int_fin_truth_lemma` vs the
parametric `truthLemma` in `Tableau/Intuitionistic/Scheme.lean` for the parallel statements.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u} [DecidableEq Atom]

attribute [local instance] Classical.propDecidable

/-! ## Σ-Bounded Finite World Type -/

/-- A `Σ`-bounded prime intuitionistic world, where `Σ := φ.subformulas`.

Fields:
- `carrier`: a finset of formulas from `Σ`
- `sub`: carrier ⊆ Σ
- `closed`: deductively closed within Σ — if ψ is Int-derivable from the carrier and ψ ∈ Σ,
  then ψ ∈ carrier
- `consistent`: ⊥ is not in the carrier
- `prime`: the disjunction property within Σ

Two worlds with the same carrier are equal by propext; this makes the carrier map injective
and enables the `Fintype` instance via `Fintype.ofInjective`. -/
structure IntFinWorld (φ : PL.Proposition Atom) where
  /-- The world's carrier: a finset of Σ-subformulas. -/
  carrier : Finset (PL.Proposition Atom)
  /-- The carrier is a subset of the subformulas of φ. -/
  sub : carrier ⊆ φ.subformulas
  /-- Deductive closure within Σ: if ψ is Int-derivable from the carrier and ψ ∈ Σ,
  then ψ ∈ carrier. -/
  closed : ∀ ψ ∈ φ.subformulas,
      SetDerivable IntPropAxiom (↑carrier : Set (PL.Proposition Atom)) ψ → ψ ∈ carrier
  /-- Consistency: ⊥ is not in the carrier. -/
  consistent : (⊥ : PL.Proposition Atom) ∉ carrier
  /-- Primality: the disjunction property. -/
  prime : ∀ a b : PL.Proposition Atom, (.or a b) ∈ carrier → a ∈ carrier ∨ b ∈ carrier

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
theorem intFinWorld_carrier_injective (φ : PL.Proposition Atom) :
    Function.Injective
      (fun w : IntFinWorld φ =>
        (⟨w.carrier, Finset.mem_powerset.mpr w.sub⟩ :
          ↑(φ.subformulas.powerset))) :=
  fun _w₁ _w₂ h => IntFinWorld.ext (congrArg Subtype.val h)

/-- `IntFinWorld φ` is a `Fintype`: worlds embed injectively into the finite powerset `2^Σ`.

The powerset `φ.subformulas.powerset : Finset (Finset _)` has a canonical `Fintype` for its
subtype, and the carrier map is injective (by `IntFinWorld.ext`). No decidability of
`SetDerivable` is required. -/
noncomputable instance instFintypeIntFinWorld (φ : PL.Proposition Atom) :
    Fintype (IntFinWorld φ) :=
  Fintype.ofInjective _ (intFinWorld_carrier_injective φ)

/-! ## Consistency Helper -/

/-- An `IntFinWorld` generates a propositionally consistent context.

The proof uses the all-True model: `World = Unit`, `val = always True`,
`bot_forces = False`. Every subformula of φ other than ⊥ is forced at `()` by structural
induction; the assumption ⊥ ∈ w.carrier contradicts `w.consistent`. Applying soundness then
derives a contradiction. -/
theorem intFinWorld_propConsistent {φ : PL.Proposition Atom}
    (w : IntFinWorld φ) :
    PropSetConsistent IntPropAxiom (↑w.carrier : Set (PL.Proposition Atom)) := by
  intro L hLsub hLderiv
  obtain ⟨d⟩ := hLderiv
  by_cases hbot : (⊥ : PL.Proposition Atom) ∈ φ.subformulas
  · -- Case: ⊥ ∈ φ.subformulas. Use w.closed to derive ⊥ ∈ w.carrier, contradicting w.consistent.
    exact w.consistent (w.closed ⊥ hbot ⟨L, hLsub, ⟨d⟩⟩)
  · -- Case: ⊥ ∉ φ.subformulas. All elements of L ⊆ ↑w.carrier ⊆ φ.subformulas are ⊥-free.
    -- Use all-true model via an auxiliary induction on φ.subformulas (not on L membership)
    -- so that the IH has the correct type: ξ ∈ φ.subformulas → IForces ... ξ.
    have h_forces_all : ∀ ψ ∈ L, IForces (fun _ _ => True) (fun _ => False) () ψ := by
      intro ψ hψ
      have hmem : ψ ∈ w.carrier := Finset.mem_coe.mp (hLsub ψ hψ)
      -- Reduce to the subformula closure: prove all subformulas of φ are forced.
      suffices h_subs : ∀ ξ : PL.Proposition Atom, ξ ∈ φ.subformulas →
                        IForces (fun _ _ => True) (fun _ => False) () ξ from
        h_subs ψ (w.sub hmem)
      intro ξ hξ
      induction ξ with
      | atom p => simp [IForces]
      | bot =>
        -- ξ = ⊥ but ⊥ ∉ φ.subformulas, contradiction.
        exact absurd hξ hbot
      | imp a b iha ihb =>
        -- After simp, IH shape: a/b ∈ φ.subformulas → IForces ... (matching subformulas of φ).
        simp only [IForces_imp]
        intro w' _ _
        cases w'
        exact ihb (Proposition.IsSubformula.trans Proposition.IsSubformula.imp_right hξ)
      | and a b iha ihb =>
        simp only [IForces_and]
        exact ⟨iha (Proposition.IsSubformula.trans Proposition.IsSubformula.and_left hξ),
               ihb (Proposition.IsSubformula.trans Proposition.IsSubformula.and_right hξ)⟩
      | or a b iha ihb =>
        simp only [IForces_or]
        exact Or.inl
              (iha (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hξ))
    exact int_soundness d (fun _ _ => True) (fun {_ _} _ _ _ => trivial) () h_forces_all

/-! ## Finite Implication Witness -/

/-- **Finite Implication Witness**.

Given a world `w : IntFinWorld φ` with `ψ → χ ∈ φ.subformulas` but `ψ → χ ∉ w.carrier`,
there exists `w' : IntFinWorld φ` with `w ≤ w'`, `ψ ∈ w'.carrier`, `χ ∉ w'.carrier`.

**Proof strategy** (via the infinite canonical model):
1. From `w.closed`: `¬ SetDerivable IntPropAxiom ↑w.carrier (ψ → χ)`.
2. The deductive closure of `↑w.carrier` is an IntDCCS.
3. `int_imp_witness` gives an IntDCCS T ⊇ DC(w) with ψ ∈ T, χ ∉ T.
4. `int_prime_exclusion` gives a prime IntDCCS T'' ⊇ T with χ ∉ T''.
5. Restrict T'' to Σ: `w'.carrier := {ξ ∈ φ.subformulas | ξ ∈ T''}`.
6. Verify w' satisfies all `IntFinWorld` conditions and w ≤ w', ψ ∈ w'.carrier, χ ∉ w'.carrier.

This sidesteps Zorn's lemma for finite models. -/
theorem int_fin_imp_witness {φ : PL.Proposition Atom}
    (w : IntFinWorld φ) {ψ χ : PL.Proposition Atom}
    (hmem : (.imp ψ χ) ∈ φ.subformulas)
    (hnot : (.imp ψ χ) ∉ w.carrier) :
    ∃ w' : IntFinWorld φ, w ≤ w' ∧ ψ ∈ w'.carrier ∧ χ ∉ w'.carrier := by
  -- Step 1: ψ → χ is not derivable from w.carrier
  have h_not_sd : ¬ SetDerivable IntPropAxiom (↑w.carrier : Set (PL.Proposition Atom)) (ψ.imp χ) :=
    fun h_sd => hnot (w.closed (ψ.imp χ) hmem h_sd)
  -- Step 2: Consistency of ↑w.carrier
  have h_cons : PropSetConsistent IntPropAxiom (↑w.carrier : Set (PL.Proposition Atom)) :=
    intFinWorld_propConsistent w
  -- Step 3: Form the IntDCCS from the deductive closure
  have h_dccs : IntDCCS (intDeductiveClosure (↑w.carrier : Set (PL.Proposition Atom))) :=
    intDeductiveClosure_is_dccs h_cons
  -- Step 4: ψ → χ ∉ intDeductiveClosure ↑w.carrier (= SetDerivable condition)
  have h_not_dc : (ψ.imp χ) ∉ intDeductiveClosure (↑w.carrier : Set (PL.Proposition Atom)) :=
    h_not_sd
  -- Step 5: Apply int_imp_witness to get T ⊇ DC(w) with ψ ∈ T, χ ∉ T
  obtain ⟨T, hDCT, hT_dccs, hψT, hχT⟩ := int_imp_witness h_dccs h_not_dc
  -- Step 6: Apply int_prime_exclusion to get prime T'' ⊇ T with χ ∉ T''
  obtain ⟨T'', hTT'', hT''_prime, hχT''⟩ := int_prime_exclusion hT_dccs hχT
  -- Step 7: Restrict T'' to Σ = φ.subformulas
  let carrier' : Finset (PL.Proposition Atom) :=
    φ.subformulas.filter (fun ξ => ξ ∈ T'')
  have sub' : carrier' ⊆ φ.subformulas := Finset.filter_subset _ _
  have h_sub_set : (↑carrier' : Set _) ⊆ (T'' : Set _) := by
    intro ξ hξ
    have := Finset.mem_coe.mp hξ
    simp only [carrier', Finset.mem_filter] at this
    exact this.2
  have closed' : ∀ ψ' ∈ φ.subformulas,
      SetDerivable IntPropAxiom (↑carrier' : Set _) ψ' → ψ' ∈ carrier' := by
    intro ψ' hψ'mem h_sd'
    simp only [carrier', Finset.mem_filter]
    refine ⟨hψ'mem, ?_⟩
    obtain ⟨L, hLsub, hLderiv⟩ := SetDerivable_weakening h_sub_set h_sd'
    exact hT''_prime.1.2 L ψ' hLsub hLderiv
  have consistent' : (⊥ : PL.Proposition Atom) ∉ carrier' := by
    simp only [carrier', Finset.mem_filter, not_and]
    intro _; exact int_dccs_bot_not_mem hT''_prime.1
  have prime' : ∀ a b : PL.Proposition Atom,
      (.or a b) ∈ carrier' → a ∈ carrier' ∨ b ∈ carrier' := by
    intro a b hab
    simp only [carrier', Finset.mem_filter] at hab ⊢
    rcases hT''_prime.2 a b hab.2 with ha | hb
    · exact Or.inl ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hab.1, ha⟩
    · exact Or.inr ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hab.1, hb⟩
  let w' : IntFinWorld φ := ⟨carrier', sub', closed', consistent', prime'⟩
  -- Step 8: w ≤ w' (w.carrier ⊆ carrier')
  have h_le : w ≤ w' := fun ξ hξ => by
    simp only [w', carrier', Finset.mem_filter]
    exact ⟨w.sub hξ, hTT'' (hDCT (int_subset_deductive_closure _ (by exact_mod_cast hξ)))⟩
  -- Step 9: ψ ∈ w'.carrier
  have hψ : ψ ∈ w'.carrier := by
    simp only [w', carrier', Finset.mem_filter]
    exact ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.imp_left hmem,
           hTT'' hψT⟩
  -- Step 10: χ ∉ w'.carrier
  have hχ : χ ∉ w'.carrier := by
    simp only [w', carrier', Finset.mem_filter, not_and]
    intro _; exact hχT''
  exact ⟨w', h_le, hψ, hχ⟩

/-! ## Finite Canonical Valuation -/

/-- The canonical valuation for `IntFinWorld φ`: atom `p` is true at world `w` iff
`Proposition.atom p ∈ w.carrier`. -/
def intFinVal {φ : PL.Proposition Atom} (w : IntFinWorld φ) (p : Atom) : Prop :=
  (.atom p) ∈ w.carrier

/-- The finite canonical valuation is upward-closed with respect to the carrier inclusion
preorder. -/
theorem intFinVal_upward_closed {φ : PL.Proposition Atom}
    {w w' : IntFinWorld φ} (p : Atom) (hw : w ≤ w') (hv : intFinVal w p) :
    intFinVal w' p :=
  hw hv

/-! ## Finite Truth Lemma -/

/-- **Finite Truth Lemma (FMP route)**: For any `w : IntFinWorld φ` and formula
`ψ ∈ φ.subformulas`, `IForces intFinVal (fun _ => False) w ψ ↔ ψ ∈ w.carrier`.

Proof by structural induction on `ψ` with `w` fixed:
- **atom**: `IForces ... w (.atom p) = intFinVal w p = (.atom p) ∈ w.carrier`. `Iff.rfl`.
- **bot**: ⊥ is never forced (`bot_forces = fun _ => False`) and ⊥ ∉ w.carrier.
- **imp**: backward direction uses `int_fin_imp_witness`; forward direction uses the `closed`
  field with modus ponens.
- **and**, **or**: direct from IHs + DCCS closure field / primality field.

**Infrastructure relationship** (factoring deferred):
This lemma is the FMP analogue of the parametric `truthLemma S b …` in
`Tableau/Intuitionistic/Scheme.lean` (declaration `truthLemma`). Both prove a "forcing ↔
membership" statement, but over **disjoint carrier types**:
- `int_fin_truth_lemma`: world type `IntFinWorld φ` (Finset-carrier `Σ`-bounded prime DCCS,
  resting on the `IntLindenbaum.lean` substrate: `int_imp_witness`, `int_prime_exclusion`,
  `intDeductiveClosure`). Carrier is a `Finset (Proposition Atom)`. **Sorry-free.**
- `truthLemma`: world type `Nat` (tableau branch labels from `IBranch`). Carrier is a
  signed-branch occurrence predicate. **Sorry-free** (takes an explicit `hpers`
  positive-persistence hypothesis).

Factoring a common truth-lemma or world-type abstraction spanning these two carrier systems
is **explicitly deferred**: the carriers remain structurally incompatible regardless of either
lemma's sorry status, and the payoff is low. This is unrelated to completeness: both
`truthLemma` and `openBranch_countermodel` (`Tableau/Intuitionistic/Scheme.lean`) are sorry-free
and axiom-clean; nothing in this dependency chain remains open. Cross-reference:
`min_fin_truth_lemma` for the analogous minimal FMP lemma. -/
theorem int_fin_truth_lemma {φ : PL.Proposition Atom}
    (w : IntFinWorld φ) :
    ∀ {ψ : PL.Proposition Atom}, ψ ∈ φ.subformulas →
    (IForces intFinVal (fun _ => False) w ψ ↔ ψ ∈ w.carrier) := by
  intro ψ hψ
  -- Use tactic mode with `cases` so that the IH for recursive calls
  -- (e.g. `int_fin_truth_lemma v ha_sub`) infers the formula from the membership type,
  -- while `hψ` has the correct specialized type in each case.
  cases ψ with
  | atom p => exact Iff.rfl
  | bot => exact ⟨False.elim, w.consistent⟩
  | imp a b =>
    have ha_sub : a ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.imp_left hψ
    have hb_sub : b ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.imp_right hψ
    constructor
    · -- Forward: IForces ... w (a → b) → (a → b) ∈ w.carrier
      intro h_forces
      by_contra h_not_mem
      obtain ⟨v, hle, ha_v, hb_v⟩ := int_fin_imp_witness w hψ h_not_mem
      have hfa := (int_fin_truth_lemma v ha_sub).mpr ha_v
      exact hb_v ((int_fin_truth_lemma v hb_sub).mp (h_forces v hle hfa))
    · -- Backward: (a → b) ∈ w.carrier → IForces ... w (a → b)
      intro h_mem v hle hfa
      have ha_v := (int_fin_truth_lemma v ha_sub).mp hfa
      have hab_v := hle h_mem
      have hb_v := v.closed b hb_sub
        (SetDerivable_mp
          (SetDerivable_of_mem (Finset.mem_coe.mpr hab_v))
          (SetDerivable_of_mem (Finset.mem_coe.mpr ha_v)))
      exact (int_fin_truth_lemma v hb_sub).mpr hb_v
  | and a b =>
    have ha_sub : a ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.and_left hψ
    have hb_sub : b ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.and_right hψ
    constructor
    · -- Forward: IForces ... w (a ∧ b) → (a ∧ b) ∈ w.carrier
      intro ⟨hfa, hfb⟩
      have ha_mem := (int_fin_truth_lemma w ha_sub).mp hfa
      have hb_mem := (int_fin_truth_lemma w hb_sub).mp hfb
      apply w.closed (a.and b) hψ
      exact SetDerivable_mp
        (SetDerivable_mp
          (SetDerivable_of_Derivable ⟨.ax [] _ (IntPropAxiom.andI a b)⟩ (↑w.carrier))
          (SetDerivable_of_mem (Finset.mem_coe.mpr ha_mem)))
        (SetDerivable_of_mem (Finset.mem_coe.mpr hb_mem))
    · -- Backward: (a ∧ b) ∈ w.carrier → IForces ... w (a ∧ b)
      intro h_mem
      exact ⟨(int_fin_truth_lemma w ha_sub).mpr
          (w.closed a ha_sub
            (SetDerivable_mp
              (SetDerivable_of_Derivable ⟨.ax [] _ (IntPropAxiom.andE1 a b)⟩ (↑w.carrier))
              (SetDerivable_of_mem (Finset.mem_coe.mpr h_mem)))),
        (int_fin_truth_lemma w hb_sub).mpr
          (w.closed b hb_sub
            (SetDerivable_mp
              (SetDerivable_of_Derivable ⟨.ax [] _ (IntPropAxiom.andE2 a b)⟩ (↑w.carrier))
              (SetDerivable_of_mem (Finset.mem_coe.mpr h_mem))))⟩
  | or a b =>
    have ha_sub : a ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hψ
    have hb_sub : b ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hψ
    constructor
    · -- Forward: IForces ... w (a ∨ b) → (a ∨ b) ∈ w.carrier
      intro h_or
      rcases h_or with hfa | hfb
      · exact w.closed (a.or b) hψ
          (SetDerivable_mp
            (SetDerivable_of_Derivable ⟨.ax [] _ (IntPropAxiom.orI1 a b)⟩ (↑w.carrier))
            (SetDerivable_of_mem (Finset.mem_coe.mpr ((int_fin_truth_lemma w ha_sub).mp hfa))))
      · exact w.closed (a.or b) hψ
          (SetDerivable_mp
            (SetDerivable_of_Derivable ⟨.ax [] _ (IntPropAxiom.orI2 a b)⟩ (↑w.carrier))
            (SetDerivable_of_mem (Finset.mem_coe.mpr ((int_fin_truth_lemma w hb_sub).mp hfb))))
    · -- Backward: (a ∨ b) ∈ w.carrier → IForces ... w (a ∨ b)
      intro h_mem
      rcases w.prime a b h_mem with ha | hb
      · exact Or.inl ((int_fin_truth_lemma w ha_sub).mpr ha)
      · exact Or.inr ((int_fin_truth_lemma w hb_sub).mpr hb)

/-! ## Finite Model Property -/

/-- Helper: the set `{ξ ∈ φ.subformulas | ξ ∈ T}` forms an `IntFinWorld φ` when
`T` is a prime IntDCCS. -/
private noncomputable def intFinWorldOfPrimeDCCS {φ : PL.Proposition Atom}
    {T : Set (PL.Proposition Atom)} (hT : IntPrimeDCCS T) : IntFinWorld φ where
  carrier := φ.subformulas.filter (fun ξ => ξ ∈ T)
  sub := Finset.filter_subset _ _
  closed ψ' hψ'mem h_sd' := by
    simp only [Finset.mem_filter]
    refine ⟨hψ'mem, ?_⟩
    have h_sub_set : (↑(φ.subformulas.filter (fun ξ => ξ ∈ T)) : Set _) ⊆ T := by
      intro ξ hξ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hξ
      exact hξ.2
    obtain ⟨L, hLsub, hLderiv⟩ := SetDerivable_weakening h_sub_set h_sd'
    exact hT.1.2 L ψ' hLsub hLderiv
  consistent := by
    simp only [Finset.mem_filter, not_and]
    intro _; exact int_dccs_bot_not_mem hT.1
  prime a b hab := by
    simp only [Finset.mem_filter] at hab ⊢
    rcases hT.2 a b hab.2 with ha | hb
    · exact Or.inl ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hab.1, ha⟩
    · exact Or.inr ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hab.1, hb⟩

/-- **Finite Model Property for Intuitionistic Propositional Logic**:
`φ` is derivable iff `φ` is in the carrier of every `Σ`-bounded prime intuitionistic world.

- **(→) Soundness**: Any derivable formula is valid in every Int Kripke model; the finite
  canonical model (`IntFinWorld φ`) is a valid Int model.
- **(←) Completeness**: If `φ` is not derivable, we construct a countermodel in `IntFinWorld φ`
  using the prime exclusion lemma to build a prime DCCS omitting `φ`, then restrict to Σ. -/
theorem int_fmp (φ : PL.Proposition Atom) :
    Derivable IntPropAxiom φ ↔ ∀ w : IntFinWorld φ, φ ∈ w.carrier := by
  constructor
  · -- Forward: soundness
    intro h w
    rw [← int_fin_truth_lemma w (Proposition.self_mem_subformulas φ)]
    exact int_soundness_derivable h (IntFinWorld φ) intFinVal intFinVal_upward_closed w
  · -- Backward: contrapositive; build a counterworld when φ is not derivable
    intro h_all
    by_contra h_not
    -- ∅ is consistent
    have h_cons : PropSetConsistent IntPropAxiom (∅ : Set (PL.Proposition Atom)) := by
      intro L hL hd
      have hL_nil : L = [] := by
        rcases L with _ | ⟨a, L'⟩
        · rfl
        · exact absurd (hL a (List.mem_cons.mpr (Or.inl rfl))) (Set.notMem_empty a)
      subst hL_nil; exact int_consistent hd
    -- φ ∉ intDeductiveClosure ∅
    have h_not_mem : φ ∉ intDeductiveClosure ∅ := by
      rw [intDeductiveClosure_iff_SetDerivable, SetDerivable_empty_iff]
      exact h_not
    -- Build a prime IntDCCS T with φ ∉ T
    obtain ⟨T, _, hT_prime, hφT⟩ :=
      int_prime_exclusion (intDeductiveClosure_is_dccs h_cons) h_not_mem
    -- The finite world built from T omits φ
    have hφ : φ ∉ (intFinWorldOfPrimeDCCS hT_prime (φ := φ)).carrier := by
      simp only [intFinWorldOfPrimeDCCS, Finset.mem_filter, not_and]
      intro _; exact hφT
    exact hφ (h_all (intFinWorldOfPrimeDCCS hT_prime))

/-! ## Decidability Instance -/

/-- **Sorry-free `Decidable` decision procedure for `Derivable IntPropAxiom φ`** via the
finite model property (FMP route).

The decision procedure checks `∀ w : IntFinWorld φ, φ ∈ w.carrier` by enumerating all
worlds in the finite type `IntFinWorld φ` (which is a `Fintype` via `instFintypeIntFinWorld`).
This definition is independent of `intuitionisticTableau_complete` and carries no `sorryAx`
(axiom profile: `{propext, Classical.choice, Quot.sound}`).

This is a **named `noncomputable def`**, not a registered `instance`. The canonical registered
`Decidable` instance for `Derivable IntPropAxiom φ` is `instDecidableDerivableIntPropAxiom` in
`Tableau/Intuitionistic/DecisionProcedure.lean` (tableau route). See also
`decidableDerivableMinPropAxiomFMP` in `Metalogic/MinDecidability.lean` for the analogous Min
FMP decision procedure. -/
noncomputable def decidableDerivableIntPropAxiomFMP (φ : PL.Proposition Atom) :
    Decidable (Derivable IntPropAxiom φ) :=
  decidable_of_iff (∀ w : IntFinWorld φ, φ ∈ w.carrier) (int_fmp φ).symm

end Cslib.Logic.PL

end
