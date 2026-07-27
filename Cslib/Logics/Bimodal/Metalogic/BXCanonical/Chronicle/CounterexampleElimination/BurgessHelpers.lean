/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleTypes
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.RRelation
public import Cslib.Foundations.Logic.Metalogic.Chronicle.CounterexampleElimination.Structures
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Tactic.NormNum

/-! # BurgessR3Maximal fc Helper Lemmas

Helper lemmas for `BurgessR3Maximal fc`: g-content subset, SetDeductivelyClosed,
bot exclusion, adjacency preservation, and backward h-content construction.

## Status

`BurgessR3Maximal_g_content_sub`/`_sdc`/`_bot_not_mem` are now thin re-exports of
`Cslib.Foundations.Logic.Metalogic.Chronicle.CounterexampleElimination.Structures`.
`c2'_preserved_on_old_adjacent` and `burgessR3Maximal_from_h_content_sub` stay logic-local,
verbatim (`Chronicle`-locality and a forward dependency on an earmarking decision
respectively — see the generic module's docstring).
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Theorems.Combinators

/-! ## BurgessR3Maximal fc Helper Lemmas -/

/--
**BurgessR3Maximal fc implies gContent subset**: If BurgessR3Maximal(A, B, C) holds with
A and C both MCS, then gContent(A) ⊆ C.

Proof: Suppose G(φ) ∈ A but φ ∉ C. Then φ.neg ∈ C (MCS). Since B is CUD, ⊤ ∈ B (a
theorem is in any CUD set). From burgessRSet(A, B, C): untl(⊤, φ.neg) ∈ A. By BX10
(until_F), F(φ.neg) ∈ A. But G(φ) ∈ A gives ¬F(φ.neg) ∈ A (by G = ¬F¬ equivalence
in MCS), contradicting consistency of A.
-/
theorem BurgessR3Maximal_g_content_sub {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C) :
    gContent A ⊆ C :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_g_content_sub
    (bimodalChronicleInterface fc) h_r3m h_mcs_A h_mcs_C

/--
**BurgessR3Maximal fc implies SetDeductivelyClosed** when some formula is not in B.
Since B is CUD (from BurgessR3Maximal) and phi not in B, B is not Set.univ, hence consistent.
-/
theorem BurgessR3Maximal_sdc {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal fc A B C)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) :
    SetDeductivelyClosed fc B :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_sdc
    (bimodalChronicleInterface fc) h_r3m h_not_mem

/--
**BurgessR3Maximal fc excludes ⊥ when B is consistent**: In Burgess's framework,
g-values are DCS (deductively closed sets = consistent + CUD). When `B` is
known to be `SetConsistent`, `⊥ ∉ B` follows directly: if `⊥ ∈ B`, then
the singleton list `[⊥]` witnesses inconsistency via the identity derivation.

The consistency hypothesis `h_cons` must be discharged at call sites.
In the omega chain, g-value consistency is established through the
chronicle construction in ChronicleConstruction.lean.

See Burgess 1982, Section 2: "g is a function from {(x,y) : x,y ∈ dom f,
x < y} to the set of all DCSs" where DCS = deductively closed set
(consistent + CUD). -/
private theorem BurgessR3Maximal_bot_not_mem {fc : FrameClass} {A B C : Set (Formula Atom)}
    (_h_r3m : BurgessR3Maximal fc A B C)
    (h_cons : SetConsistent fc B) :
    Formula.bot ∉ B :=
  Cslib.Logic.Metalogic.Chronicle.burgessR3Maximal_bot_not_mem
    (bimodalChronicleInterface fc) _h_r3m h_cons

/--
Helper: for adjacent pairs in a chronicle satisfying c2', when inserting a new point
that splits an existing adjacent pair, the old adjacent pairs that don't involve the
split are preserved. Adjacent pairs involving the split point need BurgessR3Maximal
from lemma_2_6_splitting or lemma_2_7.
-/
private theorem c2'_preserved_on_old_adjacent {fc : FrameClass} {χ χ' : Chronicle Atom}
    (h_c2' : χ.c2' fc)
    (h_f_agrees : ∀ x ∈ χ.dom, χ'.f x = χ.f x)
    (h_g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b)
    (_h_dom_sub : χ.dom ⊆ χ'.dom)
    {a b : Rat}
    (_h_adj' : Adjacent χ'.dom a b)
    (h_a_old : a ∈ χ.dom) (h_b_old : b ∈ χ.dom)
    (h_adj_old : Adjacent χ.dom a b) :
    BurgessR3Maximal fc (χ'.f a) (χ'.g a b) (χ'.f b) := by
  rw [h_f_agrees a h_a_old, h_g_agrees a b h_a_old h_b_old, h_f_agrees b h_b_old]
  exact h_c2' a b h_adj_old

/--
**BurgessR3Maximal fc from hContent subset (backward direction)**:
If hContent(C) ⊆ A (i.e., H(φ) ∈ C → φ ∈ A), then ∃ B, BurgessR3Maximal(A, B, C).

This is the backward mirror of `burgessR3Maximal_from_g_content_sub`:
- Forward: gContent(A) ⊆ C gives BurgessR3Maximal(A, _, C)
- Backward: hContent(C) ⊆ A gives BurgessR3Maximal(A, _, C)

Proof: Use η = ⊤ as the seed element.
- burgessR(A, ⊤, C): F(γ) ∈ A for all γ ∈ C.
  Proof: By BX4' (connect_past), γ → H(F(γ)), so γ ∈ C → H(F(γ)) ∈ C → F(γ) ∈ hContent(C) ⊆ A.
  Then F(γ) → U(⊤, γ) by F_until_equiv.
- burgessRSince(C, ⊤, A): P(α) ∈ C for all α ∈ A.
  Proof: If H(α.neg) ∈ C, then α.neg ∈ hContent(C) ⊆ A, contradicting α ∈ A. So P(α) ∈ C.
  Then P(α) → S(⊤, α) by P_since_equiv.
-/
private theorem burgessR3Maximal_from_h_content_sub {fc : FrameClass} {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_hc : hContent C ⊆ A) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal fc A B C := by
  set top := Formula.bot.imp Formula.bot with top_def
  have h_top_A : top ∈ A :=
    theoremInMcsFc h_mcs_A (Cslib.Logic.Bimodal.Theorems.Combinators.identity Formula.bot)
  -- burgessR(A, ⊤, C): ∀ γ ∈ C, U(⊤, γ) ∈ A
  have h_bR : burgessR A top C := by
    intro γ hγ
    -- BX4': γ → H(F(γ))
    have h_ax_cp : DerivationTree fc [] (γ.imp (Formula.allPast (Formula.someFuture γ))) :=
      DerivationTree.axiom [] _ (Axiom.connect_past γ) trivial
    have h_HF : Formula.allPast (Formula.someFuture γ) ∈ C :=
      SetMaximalConsistent.implication_property h_mcs_C
        (theoremInMcsFc h_mcs_C h_ax_cp) hγ
    -- H(F(γ)) ∈ C → F(γ) ∈ hContent(C) ⊆ A
    have h_F : Formula.someFuture γ ∈ A := h_hc h_HF
    -- F(γ) → U(⊤, γ) by F_until_equiv
    have h_bx12 : DerivationTree fc [] ((Formula.someFuture γ).imp (Formula.untl top γ)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact SetMaximalConsistent.implication_property h_mcs_A
      (theoremInMcsFc h_mcs_A h_bx12) h_F
  -- burgessRSince(C, ⊤, A): ∀ α ∈ A, S(⊤, α) ∈ C
  have h_bRS : burgessRSince C top A := by
    intro α hα
    -- If H(α.neg) ∈ C, then α.neg ∈ hContent(C) ⊆ A, contradicting α ∈ A
    have h_P : Formula.somePast α ∈ C := by
      by_contra h_not_P
      have h_neg_P : (Formula.somePast α).neg ∈ C :=
        (SetMaximalConsistent.negation_complete h_mcs_C _).resolve_left h_not_P
      have h_H_neg : Formula.allPast α.neg ∈ C :=
        neg_somePast_to_allPast_neg h_mcs_C α h_neg_P
      have h_neg_A : α.neg ∈ A := h_hc h_H_neg
      exact SetMaximalConsistent.neg_excludes h_mcs_A α h_neg_A hα
    -- P(α) → S(⊤, α) by P_since_equiv
    have h_bx12' : DerivationTree fc [] ((Formula.somePast α).imp (Formula.snce top α)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact SetMaximalConsistent.implication_property h_mcs_C
      (theoremInMcsFc h_mcs_C h_bx12') h_P
  exact burgessR3Maximal_exists_from_seed fc A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

end
