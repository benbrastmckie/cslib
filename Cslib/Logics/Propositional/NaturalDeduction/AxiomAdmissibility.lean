/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
public import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules

/-! # Axiom Admissibility for Propositional Logic

This module proves equivalences between ND derivability with concrete theories (MPL, IPL, IPL∪CPL)
and ND derivability with Hilbert-axiom theories (`AxiomTheory MinPropAxiom`, etc.). These
equivalences underpin the syntactic bridge theorems in `HilbertConservativeGlivenko.lean`.

The central tool is `Theory.Derivation.replaceAxioms`, a structural induction principle that
replaces each axiom use in a derivation with an ND derivation of that axiom from an alternate
theory. Using this, we prove:

- `axiomTheory_min_iff_mpl`: `DerivableIn (∅ : Theory Atom) φ ↔`
  `DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)`
- `axiomTheory_int_iff_ipl`: `DerivableIn (IPL : Theory Atom) φ ↔`
  `DerivableIn (AxiomTheory IntPropAxiom) (∅ ⊢ φ)`
- `axiomTheory_cl_iff_cpl`: `DerivableIn (IPL ∪ CPL : Theory Atom) φ ↔`
  `DerivableIn (AxiomTheory PropositionalAxiom) (∅ ⊢ φ)`

These equivalences are used in `HilbertConservativeGlivenko.lean` to provide syntactic
(proof-theoretic) proofs of the bridge theorems, replacing the earlier algebraic approach.

## Architecture

The forward direction `T → AxiomTheory Axioms` uses `DerivableIn.replaceAxioms` with ND
derivations showing each formula in T is derivable from `AxiomTheory Axioms`.

The backward direction `AxiomTheory Axioms → T` uses `replaceAxioms` to eliminate each Hilbert
axiom use in the derivation, replacing it with a direct ND derivation of that axiom schema from T.

## References

* `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` — `hilbert_iff_nd` family
* `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` — axiom inductive types
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]

/-! ## General Axiom Replacement Principle -/

/-- Replace every axiom use in a derivation `d : T.Derivation Γ A` with derivations from
theory `T'`, given that every formula in `T` is derivable from `T'` with empty context.

This is the key structural induction used to transfer derivability between theories when one
theory's axioms are ND-admissible in the other. -/
def Theory.Derivation.replaceAxioms {T T' : Theory Atom}
    (h : ∀ {B : Proposition Atom}, B ∈ T → T'.Derivation ∅ B)
    {Γ : Ctx Atom} {A : Proposition Atom} :
    T.Derivation Γ A → T'.Derivation Γ A
  | ax hA => (h hA).weakCtx (Finset.empty_subset _)
  | ass hA => ass hA
  | andI G d₁ d₂ => andI G (d₁.replaceAxioms h) (d₂.replaceAxioms h)
  | andE1 G d => andE1 G (d.replaceAxioms h)
  | andE2 G d => andE2 G (d.replaceAxioms h)
  | orI1 G d => orI1 G (d.replaceAxioms h)
  | orI2 G d => orI2 G (d.replaceAxioms h)
  | orE G d dA dB =>
    orE G (d.replaceAxioms h) (dA.replaceAxioms h) (dB.replaceAxioms h)
  | impI Γ d => impI Γ (d.replaceAxioms h)
  | impE d₁ d₂ => impE (d₁.replaceAxioms h) (d₂.replaceAxioms h)

/-- Prop-level wrapper for `replaceAxioms`: transfer `DerivableIn T (Γ ⊢ A)` to
`DerivableIn T' (Γ ⊢ A)` when all of T's axioms are derivable from T'. -/
theorem DerivableIn.replaceAxioms {T T' : Theory Atom}
    (h : ∀ {B : Proposition Atom}, B ∈ T → DerivableIn T' (∅ ⊢ B))
    {Γ : Ctx Atom} {A : Proposition Atom}
    (hD : DerivableIn T (Γ ⊢ A)) : DerivableIn T' (Γ ⊢ A) :=
  ⟨hD.some.replaceAxioms fun hB => (h hB).some⟩

/-! ## ND Derivations of Hilbert Axiom Schemata -/

/-- K axiom `A → (B → A)` is derivable in any ND theory from empty context. -/
lemma nd_derivable_K (A B : Proposition Atom) {T : Theory Atom} :
    DerivableIn T (∅ ⊢ A.imp (B.imp A)) :=
  ⟨Derivation.impI ∅ (Derivation.impI {A}
    (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))⟩

/-- S axiom `(A → B → C) → ((A → B) → (A → C))` is derivable in any ND theory. -/
lemma nd_derivable_S (A B C : Proposition Atom) {T : Theory Atom} :
    DerivableIn T (∅ ⊢ (A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C))) :=
  ⟨Derivation.impI ∅
    (Derivation.impI {A.imp (B.imp C)}
      (Derivation.impI {A.imp B, A.imp (B.imp C)}
        (Derivation.impE
          (Derivation.impE
            (Derivation.ass (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
            (Derivation.ass (Finset.mem_insert_self _ _)))
          (Derivation.impE
            (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
            (Derivation.ass (Finset.mem_insert_self _ _))))))⟩

/-- `andI` axiom `A → (B → A ∧ B)` is derivable in any ND theory. -/
lemma nd_derivable_andI (A B : Proposition Atom) {T : Theory Atom} :
    DerivableIn T (∅ ⊢ A.imp (B.imp (A.and B))) :=
  ⟨Derivation.impI ∅ (Derivation.impI {A}
    (Derivation.andI {B, A}
      (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      (Derivation.ass (Finset.mem_insert_self _ _))))⟩

/-- `andE1` axiom `A ∧ B → A` is derivable in any ND theory. -/
lemma nd_derivable_andE1 (A B : Proposition Atom) {T : Theory Atom} :
    DerivableIn T (∅ ⊢ (A.and B).imp A) :=
  ⟨Derivation.impI ∅
    (Derivation.andE1 {A.and B} (Derivation.ass (Finset.mem_singleton_self _)))⟩

/-- `andE2` axiom `A ∧ B → B` is derivable in any ND theory. -/
lemma nd_derivable_andE2 (A B : Proposition Atom) {T : Theory Atom} :
    DerivableIn T (∅ ⊢ (A.and B).imp B) :=
  ⟨Derivation.impI ∅
    (Derivation.andE2 {A.and B} (Derivation.ass (Finset.mem_singleton_self _)))⟩

/-- `orI1` axiom `A → A ∨ B` is derivable in any ND theory. -/
lemma nd_derivable_orI1 (A B : Proposition Atom) {T : Theory Atom} :
    DerivableIn T (∅ ⊢ A.imp (A.or B)) :=
  ⟨Derivation.impI ∅
    (Derivation.orI1 {A} (Derivation.ass (Finset.mem_singleton_self _)))⟩

/-- `orI2` axiom `B → A ∨ B` is derivable in any ND theory. -/
lemma nd_derivable_orI2 (A B : Proposition Atom) {T : Theory Atom} :
    DerivableIn T (∅ ⊢ B.imp (A.or B)) :=
  ⟨Derivation.impI ∅
    (Derivation.orI2 {B} (Derivation.ass (Finset.mem_singleton_self _)))⟩

/-- `orE` axiom `(A → C) → ((B → C) → (A ∨ B → C))` is derivable in any ND theory.

The three outer `impI`s introduce `A→C`, `B→C`, and `A∨B` into the context.
The `orE` in context `{A∨B, B→C, A→C}` dispatches on `A∨B`. -/
lemma nd_derivable_orE (A B C : Proposition Atom) {T : Theory Atom} :
    DerivableIn T (∅ ⊢ (A.imp C).imp ((B.imp C).imp ((A.or B).imp C))) := by
  -- Context {A→C} → {B→C, A→C} → orE on {A∨B, B→C, A→C}
  apply DerivableIn.weakTheory (Set.empty_subset _)
  -- Use empty theory (no axioms needed)
  exact ⟨Derivation.impI ∅
    (Derivation.impI {A.imp C}
      (Derivation.impI {B.imp C, A.imp C}
        (Derivation.orE (G := {A.or B, B.imp C, A.imp C})
          (Derivation.ass (Finset.mem_insert_self _ _))
          (Derivation.impE
            (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
            (Derivation.ass (Finset.mem_insert_self _ _)))
          (Derivation.impE
            (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_self _ _))))
            (Derivation.ass (Finset.mem_insert_self _ _))))))⟩

omit [DecidableEq Atom] in
/-- The EFQ formula `⊥ → A` is a member of `IPL`. -/
lemma ipl_contains_efq (A : Proposition Atom) :
    (Proposition.bot.imp A) ∈ (IPL : Theory Atom) :=
  Set.mem_range.mpr ⟨A, rfl⟩

/-- DNE `¬¬A → A` is derivable from `AxiomTheory PropositionalAxiom` using Peirce and EFQ.

Proof: assume `¬¬A` (i.e., `(A → ⊥) → ⊥`). Apply Peirce `((A → ⊥) → A) → A`.
Need `(A → ⊥) → A`. Proof: assume `¬A = A → ⊥`, then apply EFQ to `⊥`,
where `⊥` comes from `¬¬A` applied to `¬A`. -/
lemma nd_derivable_dne_from_axiomTheory_cl (A : Proposition Atom) :
    DerivableIn (AxiomTheory (@PropositionalAxiom Atom))
      (∅ ⊢ (Proposition.neg (Proposition.neg A)).imp A) :=
  ⟨Derivation.impI ∅
    -- Apply Peirce ((A→⊥)→A)→A to a proof of (A→⊥)→A
    (Derivation.impE
      (Derivation.ax (mem_axiomTheory.mpr (PropositionalAxiom.peirce A .bot)))
      -- Derive (A→⊥)→A: assume ¬A, apply EFQ to ⊥ (from ¬¬A applied to ¬A)
      (Derivation.impI {Proposition.neg (Proposition.neg A)}
        (Derivation.impE
          -- EFQ: ⊥ → A
          (Derivation.ax (mem_axiomTheory.mpr (PropositionalAxiom.efq A)))
          -- Derive ⊥: apply ¬¬A to ¬A
          (Derivation.impE
            -- ¬¬A is in outer context (2nd element after insert ¬A)
            (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
            -- ¬A is in inner context (1st element)
            (Derivation.ass (Finset.mem_insert_self _ _))))))⟩

/-! ## Admissibility Lemmas for Backward Direction -/

/-- Every `MinPropAxiom` schema is ND-derivable from the empty theory. -/
lemma minPropAxiom_admissible {φ : Proposition Atom} (h : MinPropAxiom φ) :
    DerivableIn (∅ : Theory Atom) (∅ ⊢ φ) := by
  cases h with
  | implyK A B => exact nd_derivable_K A B
  | implyS A B C => exact nd_derivable_S A B C
  | andI A B => exact nd_derivable_andI A B
  | andE1 A B => exact nd_derivable_andE1 A B
  | andE2 A B => exact nd_derivable_andE2 A B
  | orI1 A B => exact nd_derivable_orI1 A B
  | orI2 A B => exact nd_derivable_orI2 A B
  | orE A B C => exact nd_derivable_orE A B C

/-- Every `IntPropAxiom` schema is ND-derivable from IPL. -/
lemma intPropAxiom_admissible {φ : Proposition Atom} (h : IntPropAxiom φ) :
    DerivableIn (IPL : Theory Atom) (∅ ⊢ φ) := by
  cases h with
  | implyK A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_K A B)
  | implyS A B C => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_S A B C)
  | efq A => exact ⟨Derivation.ax (ipl_contains_efq A)⟩
  | andI A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_andI A B)
  | andE1 A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_andE1 A B)
  | andE2 A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_andE2 A B)
  | orI1 A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_orI1 A B)
  | orI2 A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_orI2 A B)
  | orE A B C => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_orE A B C)

/-- Every `PropositionalAxiom` schema is ND-derivable from IPL ∪ CPL. -/
lemma propositionalAxiom_admissible {φ : Proposition Atom} (h : PropositionalAxiom φ) :
    DerivableIn (IPL ∪ CPL : Theory Atom) (∅ ⊢ φ) := by
  haveI : IsIntuitionistic (IPL ∪ CPL : Theory Atom) :=
    instIsIntuitionisticExtention Set.subset_union_left
  haveI : IsClassical (IPL ∪ CPL : Theory Atom) :=
    instIsClassicalExtention Set.subset_union_right
  cases h with
  | implyK A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_K A B)
  | implyS A B C => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_S A B C)
  | efq A => exact ⟨Derivation.ax (Set.mem_union_left _ (ipl_contains_efq A))⟩
  | peirce A B =>
    -- Peirce `((A → B) → A) → A` from IPL∪CPL via DNE + EFQ:
    -- impI (assume h : (A→B)→A), dne (¬¬A via negI: assume ¬A, derive ⊥
    --   by applying h to (A→B), where A→B comes from: impI (assume A), botE (⊥ from ¬A+A))
    refine ⟨Derivation.impI ∅ (Derivation.dne (Derivation.negI ?_))⟩
    -- Context: {¬A, (A→B)→A}. Goal: ⊥
    apply Derivation.negE
    · exact Derivation.ass (Finset.mem_insert_self _ _)
    apply Derivation.impE
    · exact Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    apply Derivation.impI
    apply Derivation.botE
    apply Derivation.negE
    · exact Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · exact Derivation.ass (Finset.mem_insert_self _ _)
  | andI A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_andI A B)
  | andE1 A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_andE1 A B)
  | andE2 A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_andE2 A B)
  | orI1 A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_orI1 A B)
  | orI2 A B => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_orI2 A B)
  | orE A B C => exact DerivableIn.weakTheory (Set.empty_subset _) (nd_derivable_orE A B C)

/-- IPL ∪ CPL formulas are all derivable from `AxiomTheory PropositionalAxiom`:
- IPL: `⊥ → A` maps to `PropositionalAxiom.efq A`
- CPL: `¬¬A → A` is derivable via Peirce + EFQ (see `nd_derivable_dne_from_axiomTheory_cl`) -/
lemma ipl_union_cpl_admissible_in_axiomTheory_cl
    {φ : Proposition Atom} (h : φ ∈ (IPL ∪ CPL : Theory Atom)) :
    DerivableIn (AxiomTheory (@PropositionalAxiom Atom)) (∅ ⊢ φ) := by
  rcases (Set.mem_union φ IPL CPL).mp h with hIPL | hCPL
  · obtain ⟨A, rfl⟩ := Set.mem_range.mp hIPL
    exact ⟨Derivation.ax (mem_axiomTheory.mpr (PropositionalAxiom.efq A))⟩
  · obtain ⟨A, rfl⟩ := Set.mem_range.mp hCPL
    exact nd_derivable_dne_from_axiomTheory_cl A

/-! ## Main Admissibility Equivalences -/

/-- **MPL axiom-theory equivalence**: derivability from the empty theory (MPL) is equivalent to
derivability from `AxiomTheory MinPropAxiom` (both with empty sequent context).

Forward: since `∅ ⊆ AxiomTheory MinPropAxiom`, no axiom rules can fire; `replaceAxioms`
with the vacuous handler handles this.
Backward: `replaceAxioms` with `minPropAxiom_admissible`. -/
theorem axiomTheory_min_iff_mpl {φ : Proposition Atom} :
    DerivableIn (∅ : Theory Atom) φ ↔
    DerivableIn (AxiomTheory (@MinPropAxiom Atom)) (∅ ⊢ φ) := by
  constructor
  · intro ⟨d⟩
    exact ⟨d.replaceAxioms fun hB => (Set.mem_empty_iff_false _ |>.mp hB).elim⟩
  · intro ⟨d⟩
    exact ⟨d.replaceAxioms fun hB =>
      (minPropAxiom_admissible (mem_axiomTheory.mp hB)).some⟩

/-- **IPL axiom-theory equivalence**: derivability from `IPL` is equivalent to derivability from
`AxiomTheory IntPropAxiom` (both with empty sequent context).

Forward: each IPL formula `⊥ → A` maps to `IntPropAxiom.efq A` in `AxiomTheory IntPropAxiom`.
Backward: `replaceAxioms` with `intPropAxiom_admissible`. -/
theorem axiomTheory_int_iff_ipl {φ : Proposition Atom} :
    DerivableIn (IPL : Theory Atom) φ ↔
    DerivableIn (AxiomTheory (@IntPropAxiom Atom)) (∅ ⊢ φ) := by
  constructor
  · intro ⟨d⟩
    refine ⟨d.replaceAxioms ?_⟩
    intro B hB
    -- hB : B ∈ IPL = ∃ A, ⊥ → A = B (Prop-valued existence)
    -- Use Classical.choose to extract A; then rewrite B = ⊥ → A
    have hR := Set.mem_range.mp hB
    set A := Classical.choose hR
    have hA : Proposition.imp Proposition.bot A = B := Classical.choose_spec hR
    rw [← hA]
    exact Derivation.ax (mem_axiomTheory.mpr (IntPropAxiom.efq A))
  · intro ⟨d⟩
    exact ⟨d.replaceAxioms fun hB =>
      (intPropAxiom_admissible (mem_axiomTheory.mp hB)).some⟩

/-- **CPL axiom-theory equivalence**: derivability from `IPL ∪ CPL` is equivalent to derivability
from `AxiomTheory PropositionalAxiom` (both with empty sequent context).

Forward: `replaceAxioms` using `ipl_union_cpl_admissible_in_axiomTheory_cl`.
Backward: `replaceAxioms` with `propositionalAxiom_admissible`. -/
theorem axiomTheory_cl_iff_cpl {φ : Proposition Atom} :
    DerivableIn (IPL ∪ CPL : Theory Atom) φ ↔
    DerivableIn (AxiomTheory (@PropositionalAxiom Atom)) (∅ ⊢ φ) := by
  constructor
  · intro ⟨d⟩
    exact ⟨d.replaceAxioms fun hB => (ipl_union_cpl_admissible_in_axiomTheory_cl hB).some⟩
  · intro ⟨d⟩
    exact ⟨d.replaceAxioms fun hB =>
      (propositionalAxiom_admissible (mem_axiomTheory.mp hB)).some⟩

end Cslib.Logic.PL
