/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.ProofSystem.SchemaTags

/-! # Completeness for Normal Modal Logics

This module provides the shared infrastructure for proving completeness
(both weak and strong) for all 15 systems in the modal cube:

1. **Canonical model construction**: `CanonicalWorld`, `CanonicalModel`,
   canonical frame properties (`canonical_refl`, `canonical_trans`,
   `canonical_symm`, `canonical_eucl`, `canonical_eucl_from_5`),
   and the `truth_lemma`.

2. **Set-based derivability and semantic entailment**:
   `ModalSetDerivable`, `ModalSemanticEntails`, and supporting lemmas
   (`ModalSetDerivable_of_Derivable`, `ModalSetDerivable_empty_iff`,
   `ModalSemanticEntails_of_Valid`,
   `modal_not_SetDerivable_union_neg_consistent`).

## Design

The parameterized canonical model and truth lemma take explicit axiom hypotheses
for the propositional axioms (implyK, implyS, efq, peirce) and modal axioms
(K, T, 4, B) as needed. Per-system completeness theorems instantiate these
at the appropriate axiom predicate.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Canonical Models)
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

-- Universe constraint: canonical worlds live at the same universe as `Atom`
-- because `CanonicalWorld Axioms` is a subtype of `Set (Proposition Atom)`.
-- This means worlds and atoms share universe `u` in the completeness proof.
universe u
variable {Atom : Type u}

/-! ## Canonical Model Definition -/

/-- A canonical world is a maximally consistent set of the parameterized
modal derivation system. -/
def CanonicalWorld (Axioms : Proposition Atom → Prop) :=
  { S : Set (Proposition Atom) // SetMaximalConsistent Axioms S }

/-- The canonical model parameterized over an axiom predicate.

- Accessibility: `R S T <-> forall psi, box psi in S -> psi in T`.
- Valuation: `v S p <-> atom p in S`. -/
noncomputable def CanonicalModel (Axioms : Proposition Atom → Prop) :
    Model (CanonicalWorld Axioms) Atom where
  r := fun S T => ∀ φ, (□φ) ∈ S.val → φ ∈ T.val
  v := fun S p => Proposition.atom p ∈ S.val

/-! ## Canonical Frame Properties -/

/-- The canonical accessibility relation is reflexive (from axiom T). -/
theorem canonical_refl
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_T : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp φ))
    (S : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S S := by
  intro φ h_box
  exact mcs_box_closure h_implyK h_implyS h_T S.property h_box

/-- The canonical accessibility relation is transitive (from axiom 4). -/
theorem canonical_trans
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_4 : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp (Proposition.box (Proposition.box φ))))
    (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r T U →
    (CanonicalModel Axioms).r S U := by
  intro hST hTU φ h_box
  have h_box_box := mcs_box_box h_implyK h_implyS h_4 S.property h_box
  have h_box_T := hST (□φ) h_box_box
  exact hTU φ h_box_T

/-- The canonical accessibility relation is symmetric (from axiom B).

This is the canonicity of axiom B (BRV Theorem 4.28 clause 2):
if `R S T` and `□φ ∈ T`, then `φ ∈ S` by contradiction using axiom B
and the double-negation introduction derivation. -/
theorem canonical_symm
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_B : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomB φ))
    (S T : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r T S := by
  intro hST φ h_box_T
  by_contra h_phi_not_S
  have h_neg_S := mcs_neg_of_not_mem h_implyK h_implyS S.property h_phi_not_S
  have h_bd_S := mcs_box_diamond h_implyK h_implyS h_B S.property h_neg_S
  have h_diam_T := hST _ h_bd_S
  let bp := φ
  have d_bot : DerivationTree Axioms [bp.imp .bot, bp] Proposition.bot :=
    .modus_ponens [bp.imp .bot, bp] bp .bot
      (.assumption _ (bp.imp .bot) (by simp [List.mem_cons]))
      (.assumption _ bp (by simp [List.mem_cons]))
  have d_dne := deductionTheorem h_implyK h_implyS [bp] (bp.imp .bot) .bot d_bot
  have d_dni := deductionTheorem h_implyK h_implyS [] bp
    ((bp.imp .bot).imp .bot) d_dne
  have d_nec := DerivationTree.necessitation _ d_dni
  have h_box_dni_T :
      Proposition.box (bp.imp ((bp.imp .bot).imp .bot)) ∈ T.val :=
    modal_closed_under_derivation h_implyK h_implyS T.property
      (L := []) (fun _ h => nomatch h) ⟨d_nec⟩
  have h_box_dne_T := mcs_box_mp h_implyK h_implyS h_K T.property
    h_box_dni_T h_box_T
  exact mcs_bot_not_mem T.property
    (modal_implication_property h_implyK h_implyS T.property h_diam_T h_box_dne_T)

/-- The canonical accessibility relation is Euclidean (from axioms B, T, 4). -/
theorem canonical_eucl
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_4 : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp (Proposition.box (Proposition.box φ))))
    (h_B : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomB φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r S U →
    (CanonicalModel Axioms).r T U := by
  intro hST hSU φ h_box_T
  have h_bb_T := mcs_box_box h_implyK h_implyS h_4 T.property h_box_T
  by_contra h_phi_not_U
  apply h_phi_not_U
  apply hSU
  by_contra h_box_not_S
  have h_neg_box := mcs_neg_of_not_mem h_implyK h_implyS S.property h_box_not_S
  have h_bd := mcs_box_diamond h_implyK h_implyS h_B S.property h_neg_box
  have h_diam_T := hST _ h_bd
  have h_box_dne_not_T :
      (□¬¬□φ)
        ∉ T.val :=
    mcs_not_mem_of_neg h_implyK h_implyS T.property h_diam_T
  let bp := Proposition.box φ
  have d_bot : DerivationTree Axioms [bp.imp .bot, bp] Proposition.bot :=
    .modus_ponens [bp.imp .bot, bp] bp .bot
      (.assumption _ (bp.imp .bot) (by simp [List.mem_cons]))
      (.assumption _ bp (by simp [List.mem_cons]))
  have d_dne := deductionTheorem h_implyK h_implyS [bp] (bp.imp .bot) .bot d_bot
  have d_dni := deductionTheorem h_implyK h_implyS [] bp
    ((bp.imp .bot).imp .bot) d_dne
  have d_nec := DerivationTree.necessitation _ d_dni
  have h_box_dni_T :
      Proposition.box (bp.imp ((bp.imp .bot).imp .bot)) ∈ T.val :=
    modal_closed_under_derivation h_implyK h_implyS T.property
      (L := []) (fun _ h => nomatch h) ⟨d_nec⟩
  have h_box_dne_T := mcs_box_mp h_implyK h_implyS h_K T.property
    h_box_dni_T h_bb_T
  exact h_box_dne_not_T h_box_dne_T

/-- The canonical accessibility relation is Euclidean (from axiom 5 alone).

If a normal logic contains axiom 5 (`◇φ → □◇φ`), then its canonical frame
is Euclidean. This is stronger than `canonical_eucl` which requires B + T + 4. -/
theorem canonical_eucl_from_5
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_5 : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.Axiom5 φ))
    (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r S U →
    (CanonicalModel Axioms).r T U := by
  intro hST hSU φ h_box_T
  by_contra h_phi_not_U
  have h_neg_U := mcs_neg_of_not_mem h_implyK h_implyS U.property h_phi_not_U
  -- Raw shape (`¬(□¬¬φ)`), matching `Axioms.Axiom5`'s LHS -- NOT native `◇¬φ` (`diamond` is a
  -- native constructor, not defeq to this raw shape).
  have h_diam_S : (¬(□¬¬φ)) ∈ S.val := by
    by_contra h_diam_not_S
    have h_neg_diam := mcs_neg_of_not_mem h_implyK h_implyS S.property h_diam_not_S
    have h_box_dne_S : (□¬¬φ) ∈ S.val := by
      rcases modal_negation_complete h_implyK h_implyS S.property
        (□¬¬φ) with h | h
      · exact h
      · exact absurd h h_diam_not_S
    have h_dne_U := hSU _ h_box_dne_S
    exact mcs_bot_not_mem U.property
      (modal_implication_property h_implyK h_implyS U.property h_dne_U h_neg_U)
  have h_box_diam_S := mcs_mp_axiom h_implyK h_implyS S.property h_diam_S
    (h_5 (¬φ))
  have h_diam_T := hST _ h_box_diam_S
  let bp := φ
  have d_bot : DerivationTree Axioms [bp.imp .bot, bp] Proposition.bot :=
    .modus_ponens [bp.imp .bot, bp] bp .bot
      (.assumption _ (bp.imp .bot) (by simp [List.mem_cons]))
      (.assumption _ bp (by simp [List.mem_cons]))
  have d_dne := deductionTheorem h_implyK h_implyS [bp] (bp.imp .bot) .bot d_bot
  have d_dni := deductionTheorem h_implyK h_implyS [] bp
    ((bp.imp .bot).imp .bot) d_dne
  have d_nec := DerivationTree.necessitation _ d_dni
  have h_box_dni_T :
      Proposition.box (bp.imp ((bp.imp .bot).imp .bot)) ∈ T.val :=
    modal_closed_under_derivation h_implyK h_implyS T.property
      (L := []) (fun _ h => nomatch h) ⟨d_nec⟩
  have h_box_dne_T := mcs_box_mp h_implyK h_implyS h_K T.property
    h_box_dni_T h_box_T
  exact mcs_bot_not_mem T.property
    (modal_implication_property h_implyK h_implyS T.property h_diam_T h_box_dne_T)

/-- **Canonical Seriality**: The canonical model for any DAxiom-containing system
is serial.

This is Blackburn Theorem 4.28 clause 3: "it suffices to show that the canonical model
for KD is right-unbounded [serial]." Lives here (rather than `Systems/D/Completeness.lean`)
so it remains available to all 5 D-family `d_canonical_FC` consumers via their existing
`import Metalogic.Completeness`.

The proof shows {psi | box psi in S} is consistent using a D+NEC contradiction argument,
then extends to MCS via Lindenbaum. -/
theorem d_canonical_serial
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_D : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp
        ((Proposition.box (φ.imp .bot)).imp .bot)))
    (S : CanonicalWorld Axioms) :
    ∃ T : CanonicalWorld Axioms, (CanonicalModel Axioms).r S T := by
  let W := {ψ : Proposition Atom | (□ψ) ∈ S.val}
  have hW : SetConsistent Axioms W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    have h_all_box : ∀ x ∈ L, (□x) ∈ S.val := fun x hx => hL x hx
    have h_box_bot : (□⊥) ∈ S.val :=
      derive_box_from_box_context h_implyK h_implyS h_K S.property d_bot h_all_box
    -- Raw shape (`diamond` is native, not defeq to `Axioms.AxiomD`'s RHS).
    have h_diamond_bot :
        ((Proposition.box (Proposition.bot.imp Proposition.bot)).imp Proposition.bot) ∈ S.val :=
      mcs_mp_axiom h_implyK h_implyS S.property h_box_bot (h_D ⊥)
    have d_top : DerivationTree Axioms [] (Proposition.imp .bot .bot) :=
      .ax [] _ (h_efq Proposition.bot)
    have d_box_top : DerivationTree Axioms []
        (Proposition.box (Proposition.imp .bot .bot)) :=
      .necessitation _ d_top
    have h_box_top : (Proposition.box (Proposition.bot.imp Proposition.bot)) ∈ S.val :=
      modal_closed_under_derivation h_implyK h_implyS S.property
        (L := []) (fun _ h => nomatch h) ⟨d_box_top⟩
    have h_bot : ⊥ ∈ S.val :=
      modal_implication_property h_implyK h_implyS S.property
        h_diamond_bot h_box_top
    exact mcs_bot_not_mem S.property h_bot
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  let T' : CanonicalWorld Axioms := ⟨T, hT_mcs⟩
  refine ⟨T', ?_⟩
  intro φ h_box
  exact hWT h_box

/-! ## Truth Lemma

**There is a single generic route.** `truth_lemma` below is THE truth lemma for all 15
classical systems in the modal cube (K, T, D, B, K4, K5, K45, S4, S5, TB, KB5, D4, D5, D45,
DB), since the box case genuinely needs only `EFQ + K` from `kCore` and never axiom T or D.
This works because every one of the 15 systems' axiom predicates is `SchemaUnion sysTags` with
`kCore ⊆ sysTags`: enlarging a schema-union tag set only weakens the resulting predicate
(`SchemaUnion.subsumption`, `ProofSystem/SchemaUnion.lean`), so a proof that only needs the 13
`kCore` tags transfers to any superset. Each system wires `truth_lemma` in via the
`canonicalTruthLemmaOfKCore` convenience wrapper below, feeding a single
`(h : kCore ⊆ sysTags)` subset fact through the 13 `holds*` witness helpers
(`ProofSystem/SchemaTags.lean`) rather than restating each witness by hand.

The name `truth_lemma` here is distinct from `canonical_truth_lemma`, the intuitionistic truth
lemma at `Metalogic/Intuitionistic/TruthLemma.lean` in the same namespace. The
intuitionistic/constructive subtrees are unrelated to this classical consolidation and keep
their own separate `canonical_truth_lemma` / `ck_truth_lemma`.

All 15 systems share the same canonical model definition (`CanonicalModel`) from this file.
Logics differ only in which frame properties are provable for the canonical accessibility
relation (`canonical_refl`, `canonical_trans`, `canonical_symm`, `canonical_eucl`,
`canonical_eucl_from_5`, `d_canonical_serial`), never in the truth lemma itself. -/

/-- From `L |- bot` where `L <= {psi | box psi in S} union {neg phi}`, derive `False`, without
axiom T. The generic route this file's `truth_lemma` uses for every one of the 15 classical
systems, since `kCore ⊆ sysTags` for all of them.

When `neg phi not in L`, all elements of L have box-versions in S. From `L |- bot`,
we derive `L |- phi` via EFQ, then use `derive_box_from_box_context` to get
`box phi in S`, contradicting `h_not_box`. -/
theorem k_derive_box_from_inconsistency
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : (□φ) ∉ S)
    {L : List (Proposition Atom)}
    (hL : ∀ x ∈ L, x ∈ {ψ | (□ψ) ∈ S} ∪ {(¬φ)})
    (d_bot : DerivationTree Axioms L ⊥) : False := by
  classical
  let L' := L.filter (· ≠ (¬φ))
  have h_L'_box : ∀ ψ ∈ L', (□ψ) ∈ S := by
    intro ψ hψ
    simp only [L', List.mem_filter, decide_eq_true_eq] at hψ
    rcases hL ψ hψ.1 with h | h
    · exact h
    · exact absurd h hψ.2
  by_cases h_neg_in_L : (¬φ) ∈ L
  · -- Case: neg phi in L -- identical to existing code (does not use h_T)
    have h_perm : ∀ x, x ∈ L → x ∈ (¬φ) :: L' := by
      intro x hx
      by_cases hxn : x = (¬φ)
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by
          simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
    have d_reord := DerivationTree.weakening L ((¬φ) :: L')
      ⊥ d_bot h_perm
    have d_dne := deductionTheorem h_implyK h_implyS L' (¬φ)
      ⊥ d_reord
    let neg_phi := (¬φ)
    have efq_ax : DerivationTree Axioms L' (Proposition.bot.imp φ) :=
      .weakening [] L' _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h)
    have ik : DerivationTree Axioms L'
        ((Proposition.bot.imp φ).imp (neg_phi.imp (Proposition.bot.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (h_implyK (Proposition.bot.imp φ) neg_phi))
        (fun _ h => nomatch h)
    have step_k := DerivationTree.modus_ponens L' _ _ ik efq_ax
    have is_ax : DerivationTree Axioms L'
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (h_implyS neg_phi Proposition.bot φ))
        (fun _ h => nomatch h)
    have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
    have peirce_ax : DerivationTree Axioms L'
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .weakening [] L' _ (.ax [] _ (h_peirce φ Proposition.bot))
        (fun _ h => nomatch h)
    have d_phi := DerivationTree.modus_ponens L' _ _ peirce_ax step3
    exact h_not_box (derive_box_from_box_context h_implyK h_implyS h_K h_mcs
      d_phi h_L'_box)
  · have h_all_box : ∀ x ∈ L, (□x) ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (h ▸ hx) h_neg_in_L
    have efq_ax : DerivationTree Axioms L (Proposition.bot.imp φ) :=
      .weakening [] L _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h)
    have d_phi : DerivationTree Axioms L φ :=
      .modus_ponens L .bot φ efq_ax d_bot
    exact h_not_box (derive_box_from_box_context h_implyK h_implyS h_K h_mcs
      d_phi h_all_box)

/-- **Box Witness** (BRV Lemma 4.20, generic route): If `box phi not in S` and `S` is MCS, then
there exists an MCS `T` such that `forall psi, box psi in S -> psi in T` and `phi not in T`. No
axiom T hypothesis needed. -/
theorem k_mcs_box_witness
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : (□φ) ∉ S) :
    ∃ T : Set (Proposition Atom), SetMaximalConsistent Axioms T ∧
      (∀ ψ, (□ψ) ∈ S → ψ ∈ T) ∧ φ ∉ T := by
  let W := {ψ : Proposition Atom | (□ψ) ∈ S} ∪ {(¬φ)}
  have hW : SetConsistent Axioms W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    exact k_derive_box_from_inconsistency h_implyK h_implyS h_efq h_peirce h_K
      h_mcs h_not_box hL d_bot
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_box
    exact hWT (Set.mem_union_left _ h_box)
  · have h_neg : (¬φ) ∈ T :=
      hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg h_implyK h_implyS hT_mcs h_neg

/-- **Truth Lemma**: For any canonical world `S` and formula `phi`,
`Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val`.

This is THE single generic truth lemma for all 15 classical systems: the box case needs only
`EFQ + K` from `kCore` (`k_mcs_box_witness` above), and since every one of the 15 systems'
axiom predicates is `SchemaUnion sysTags` with `kCore ⊆ sysTags`, this one route serves all of
them (no axiom T or D needed). This is distinct from `canonical_truth_lemma`, which is the
intuitionistic truth lemma in the same namespace (`Metalogic/Intuitionistic/TruthLemma.lean`).

Covers `.and`/`.or`/`.diamond` cases (native constructors). The `.and`/`.or` cases use the
`mcs_and_mem_iff`/`mcs_or_mem_iff` MCS closure lemmas (`MCS.lean`) plus the structural-recursion
IHs at the immediate subformulas -- the payoff of native constructors: no Lukasiewicz-bridge
lemma is needed. The `.diamond` case reuses `k_mcs_box_witness` (the same box-witness
consistency lemma the `.box` case uses) applied to `¬φ` instead of `φ`, bridging to native `◇`
membership via `mcs_dia_to_raw`/`mcs_raw_to_dia` (`MCS.lean`). -/
theorem truth_lemma
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_dualFwd : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomDiamondDualityFwd φ))
    (h_dualBack : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomDiamondDualityBack φ))
    (S : CanonicalWorld Axioms) :
    (φ : Proposition Atom) →
    (Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
  | .atom p => by
    constructor
    · intro h; exact h
    · intro h; exact h
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h; exact absurd h (mcs_bot_not_mem S.property)
  | .imp φ ψ => by
    constructor
    · intro h_sat
      rcases modal_negation_complete h_implyK h_implyS S.property (φ.imp ψ)
        with h | h
      · exact h
      · exfalso
        have h_phi_S : φ ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          have d_bot' : DerivationTree Axioms
              [φ.imp ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_efq' : DerivationTree Axioms
              [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
            .modus_ponens _ .bot φ
              (.weakening [] _ _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h))
              d_bot'
          have d_dt := deductionTheorem h_implyK h_implyS
            [(φ.imp ψ).imp .bot] (φ.imp ψ) φ d_efq'
          have d_peirce' : DerivationTree Axioms
              [(φ.imp ψ).imp .bot] (((φ.imp ψ).imp φ).imp φ) :=
            .weakening [] _ _ (.ax [] _ (h_peirce φ ψ)) (fun _ h => nomatch h)
          exact ⟨.modus_ponens _ _ _ d_peirce' d_dt⟩
        have h_sat_phi :=
          (truth_lemma h_implyK h_implyS h_efq h_peirce h_K
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mpr h_phi_S
        have h_psi_S :=
          (truth_lemma h_implyK h_implyS h_efq h_peirce h_K
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mp
            (h_sat h_sat_phi)
        have h_neg_psi_S : (¬ψ) ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          have d_imp : DerivationTree Axioms
              [ψ, (φ.imp ψ).imp .bot] (φ.imp ψ) :=
            .modus_ponens _ ψ (φ.imp ψ)
              (.weakening [] _ _ (.ax [] _ (h_implyK ψ φ))
                (fun _ h => nomatch h))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_bot'' : DerivationTree Axioms
              [ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              d_imp
          exact ⟨deductionTheorem h_implyK h_implyS
            [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
        exact mcs_bot_not_mem S.property
          (modal_implication_property h_implyK h_implyS S.property
            h_neg_psi_S h_psi_S)
    · intro h_mem h_sat_phi
      exact (truth_lemma h_implyK h_implyS h_efq h_peirce h_K
        h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mpr
        (modal_implication_property h_implyK h_implyS S.property h_mem
          ((truth_lemma h_implyK h_implyS h_efq h_peirce h_K
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mp
            h_sat_phi))
  | .and φ ψ => by
    constructor
    · intro h_sat
      exact (mcs_and_mem_iff h_implyK h_implyS h_andI h_andE1 h_andE2 S.property).mpr
        ⟨(truth_lemma h_implyK h_implyS h_efq h_peirce h_K
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mp h_sat.1,
         (truth_lemma h_implyK h_implyS h_efq h_peirce h_K
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mp h_sat.2⟩
    · intro h_mem
      obtain ⟨h1, h2⟩ :=
        (mcs_and_mem_iff h_implyK h_implyS h_andI h_andE1 h_andE2 S.property).mp h_mem
      exact ⟨(truth_lemma h_implyK h_implyS h_efq h_peirce h_K
                h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mpr h1,
             (truth_lemma h_implyK h_implyS h_efq h_peirce h_K
                h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mpr h2⟩
  | .or φ ψ => by
    constructor
    · intro h_sat
      apply (mcs_or_mem_iff h_implyK h_implyS h_orI1 h_orI2 h_orE S.property).mpr
      cases h_sat with
      | inl h1 => exact Or.inl ((truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mp h1)
      | inr h2 => exact Or.inr ((truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mp h2)
    · intro h_mem
      rcases (mcs_or_mem_iff h_implyK h_implyS h_orI1 h_orI2 h_orE S.property).mp h_mem
        with h1 | h2
      · exact Or.inl ((truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mpr h1)
      · exact Or.inr ((truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mpr h2)
  | .box φ => by
    constructor
    · intro h_sat
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ :=
        k_mcs_box_witness h_implyK h_implyS h_efq h_peirce h_K
          S.property h_not_box
      exact h_phi_not_T
        ((truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack
          ⟨T, hT_mcs⟩ φ).mp (h_sat ⟨T, hT_mcs⟩ hST))
    · intro h_box T hST
      exact (truth_lemma h_implyK h_implyS h_efq h_peirce h_K
        h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack T φ).mpr
        (hST φ h_box)
  | .diamond φ => by
    constructor
    · rintro ⟨T', hR, hSatT'⟩
      have h_phi_T' : φ ∈ T'.val :=
        (truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack T' φ).mp hSatT'
      by_contra h_not_dia
      have h_box_neg : (□¬φ) ∈ S.val := by
        by_contra h_not_box_neg
        exact h_not_dia (mcs_raw_to_dia h_implyK h_implyS h_dualBack S.property
          (mcs_neg_of_not_mem h_implyK h_implyS S.property h_not_box_neg))
      exact absurd h_phi_T'
        (mcs_not_mem_of_neg h_implyK h_implyS T'.property (hR _ h_box_neg))
    · intro h_dia
      have h_box_neg_not_S : (□¬φ) ∉ S.val :=
        mcs_not_mem_of_neg h_implyK h_implyS S.property
          (mcs_dia_to_raw h_implyK h_implyS h_dualFwd S.property h_dia)
      obtain ⟨T, hT_mcs, hST, h_neg_not_T⟩ :=
        k_mcs_box_witness h_implyK h_implyS h_efq h_peirce h_K
          S.property h_box_neg_not_S
      have h_phi_T : φ ∈ T :=
        (mcs_mem_iff_neg_not_mem h_implyK h_implyS hT_mcs).mpr h_neg_not_T
      exact ⟨⟨T, hT_mcs⟩, hST,
        (truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack
          ⟨T, hT_mcs⟩ φ).mpr h_phi_T⟩

/-- **Convenience Wrapper**: `truth_lemma` pre-applied to any `SchemaUnion S` whose tag set `S`
contains `kCore`, via a single `(h : kCore ⊆ S)` subset fact.

Every one of the 15 classical systems' axiom predicates is `SchemaUnion sysTags` with
`kCore ⊆ sysTags`, so this one wrapper -- fed by the 13 `holds*` helpers in
`ProofSystem.SchemaTags` -- replaces each system's bespoke 13-witness `*_truth_lemma_applied`
block with a single `canonicalTruthLemmaOfKCore (by decide) S φ` call. -/
theorem canonicalTruthLemmaOfKCore {S : Finset ModalSchemaTag} (h : kCore ⊆ S)
    (w : CanonicalWorld (SchemaUnion S)) (φ : Proposition Atom) :
    Satisfies (CanonicalModel (SchemaUnion S)) w φ ↔ φ ∈ w.val :=
  truth_lemma
    (holdsImplyK h) (holdsImplyS h) (holdsEfq h) (holdsPeirce h) (holdsModalK h)
    (holdsAndI h) (holdsAndE1 h) (holdsAndE2 h) (holdsOrI1 h) (holdsOrI2 h) (holdsOrE h)
    (holdsDiaDualityFwd h) (holdsDiaDualityBack h)
    w φ

/-! ## Consistency of Negation -/

/-- If `phi` is not derivable from `Axioms`, then `{neg phi}` is consistent
with respect to the `Axioms` derivation system. This is the standard
Peirce-based double-negation elimination argument factored out from all
completeness theorems.

The proof constructs a derivation `[] |- phi` from any hypothetical
derivation `L |- bot` where `L` is drawn from `{neg phi}`, contradicting
the assumption that `phi` is not derivable. -/
theorem neg_consistent_of_not_derivable
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    {φ : Proposition Atom} (h_not_deriv : ¬Derivable Axioms φ) :
    SetConsistent Axioms ({(¬φ)} : Set (Proposition Atom)) := by
  intro L hL
  unfold Metalogic.Consistent
  intro ⟨d⟩
  have d_weak : DerivationTree Axioms [(¬φ)]
      ⊥ :=
    .weakening L [(¬φ)] ⊥ d (fun x hx => by
      have := hL x hx; simp only [Set.mem_singleton_iff] at this
      exact List.mem_cons.mpr (Or.inl this))
  have d_dne := deductionTheorem h_implyK h_implyS
    [] (¬φ) ⊥ d_weak
  let neg_phi := (¬φ)
  have efq_ax : DerivationTree Axioms (Atom := Atom) []
      (Proposition.bot.imp φ) :=
    .ax [] _ (h_efq φ)
  have ik : DerivationTree Axioms (Atom := Atom) []
      ((Proposition.bot.imp φ).imp
        (neg_phi.imp (Proposition.bot.imp φ))) :=
    .ax [] _ (h_implyK (Proposition.bot.imp φ) neg_phi)
  have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
  have is_ax : DerivationTree Axioms (Atom := Atom) []
      ((neg_phi.imp (Proposition.bot.imp φ)).imp
       ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
    .ax [] _ (h_implyS neg_phi Proposition.bot φ)
  have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
  have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
  have peirce_ax : DerivationTree Axioms (Atom := Atom) []
      (((φ.imp Proposition.bot).imp φ).imp φ) :=
    .ax [] _ (h_peirce φ Proposition.bot)
  have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
  exact h_not_deriv ⟨d_phi⟩

/-! ## Set-Based Derivability -/

open Cslib.Logic.Helpers

attribute [local instance] Classical.propDecidable

/-- `phi` is set-derivable from `Gamma` if there exists a finite list `L ⊆ Gamma`
such that `L ⊢ phi` in the modal derivation system for `Axioms`.

This is the "finitary" version of derivability: derivations use only finitely
many assumptions even when `Gamma` is infinite. -/
def ModalSetDerivable (Axioms : Proposition Atom → Prop)
    (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) : Prop :=
  ∃ L : List (Proposition Atom),
    (∀ x ∈ L, x ∈ Gamma) ∧ (modalDerivationSystem Axioms).Deriv L phi

/-- Any theorem (derivable from the empty context) is set-derivable from any set. -/
theorem ModalSetDerivable_of_Derivable {Axioms : Proposition Atom → Prop}
    {phi : Proposition Atom} (h : Derivable Axioms phi)
    (Gamma : Set (Proposition Atom)) : ModalSetDerivable Axioms Gamma phi :=
  ⟨[], fun _ hx => by simp only [List.mem_nil_iff] at hx, by
    obtain ⟨d⟩ := h
    exact ⟨d⟩⟩

/-- Set-derivability from the empty set is equivalent to ordinary derivability. -/
theorem ModalSetDerivable_empty_iff {Axioms : Proposition Atom → Prop}
    {phi : Proposition Atom} :
    ModalSetDerivable Axioms ∅ phi ↔ Derivable Axioms phi := by
  constructor
  · intro ⟨L, hL_sub, hL_deriv⟩
    have hL_nil : L = [] := by
      by_contra h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L h
      exact absurd (hL_sub a ha) (fun h => h)
    rw [hL_nil] at hL_deriv
    exact hL_deriv
  · intro h
    exact ModalSetDerivable_of_Derivable h ∅

/-! ## Modal Semantic Entailment -/

/-- `phi` is a semantic consequence of `Gamma` over the frame class `FC`:
every world of every model satisfying `FC` and all formulas in `Gamma` also
satisfies `phi`.

The frame class predicate `FC` takes a model and returns a `Prop`, allowing
it to express arbitrary frame conditions (reflexivity, transitivity, etc.). -/
def ModalSemanticEntails
    (FC : ∀ {World : Type u}, Model World Atom → Prop)
    (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) : Prop :=
  ∀ (World : Type u) (m : Model World Atom) (w : World),
    FC m →
    (∀ γ ∈ Gamma, Satisfies m w γ) →
    Satisfies m w phi

/-- Formulas valid over all `FC`-frames are semantic consequences of any set. -/
theorem ModalSemanticEntails_of_Valid
    {FC : ∀ {World : Type u}, Model World Atom → Prop}
    {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom), FC m →
      ∀ w, Satisfies m w phi)
    (Gamma : Set (Proposition Atom)) :
    ModalSemanticEntails FC Gamma phi :=
  fun World m w hFC _ => h World m hFC w

/-! ## DNE Helper -/

/-- Given a derivation `ctx ⊢ (¬phi) → ⊥`, produce `ctx ⊢ phi`
via EFQ + implyS composition + Peirce's law. -/
private noncomputable def modal_dne_from_neg_neg
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    {phi : Proposition Atom}
    {ctx : List (Proposition Atom)}
    (d_neg_neg : DerivationTree Axioms ctx ((¬phi).imp Proposition.bot)) :
    DerivationTree Axioms ctx phi :=
  let d_efq : DerivationTree Axioms ctx (Proposition.bot.imp phi) :=
    .weakening [] ctx _ (.ax [] _ (h_efq phi)) (fun _ h => nomatch h)
  let d_k : DerivationTree Axioms ctx
      ((Proposition.bot.imp phi).imp ((¬phi).imp (Proposition.bot.imp phi))) :=
    .weakening [] ctx _ (.ax [] _ (h_implyK (Proposition.bot.imp phi) (¬phi)))
      (fun _ h => nomatch h)
  let d_step2 := DerivationTree.modus_ponens ctx _ _ d_k d_efq
  let d_s2 : DerivationTree Axioms ctx
      (((¬phi).imp (Proposition.bot.imp phi)).imp
        (((¬phi).imp Proposition.bot).imp ((¬phi).imp phi))) :=
    .weakening [] ctx _ (.ax [] _ (h_implyS (¬phi) Proposition.bot phi))
      (fun _ h => nomatch h)
  let d_step3 := DerivationTree.modus_ponens ctx _ _ d_s2 d_step2
  let d_neg_to_phi : DerivationTree Axioms ctx ((¬phi).imp phi) :=
    DerivationTree.modus_ponens ctx _ _ d_step3 d_neg_neg
  let d_peirce : DerivationTree Axioms ctx (((¬phi).imp phi).imp phi) :=
    .weakening [] ctx _ (.ax [] _ (h_peirce phi Proposition.bot)) (fun _ h => nomatch h)
  DerivationTree.modus_ponens ctx _ _ d_peirce d_neg_to_phi

/-! ## Key Consistency Lemma -/

/-- If `phi` is not set-derivable from `Gamma`, then `Gamma ∪ {¬phi}` is
`SetConsistent Axioms`.

Proof: by contradiction. If some finite `L ⊆ Gamma ∪ {¬phi}` derives `⊥`,
use `deductionWithMem` to eliminate `¬phi` from `L` and get `L' ⊆ Gamma` with
`L' ⊢ (¬phi) → ⊥`. Then EFQ + Peirce gives `L' ⊢ phi`, contradicting
`¬ ModalSetDerivable Axioms Gamma phi`. -/
theorem modal_not_SetDerivable_union_neg_consistent
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h_not : ¬ ModalSetDerivable Axioms Gamma phi) :
    SetConsistent Axioms (Gamma ∪ {(¬phi)}) := by
  intro L hL
  unfold Metalogic.Consistent
  intro ⟨d_bot⟩
  by_cases h_neg_in_L : (¬phi) ∈ L
  · have d_neg_neg := deductionWithMem
        h_implyK h_implyS L (¬phi) Proposition.bot d_bot h_neg_in_L
    have h_rem_sub : ∀ x ∈ removeAll L (¬phi), x ∈ Gamma := by
      intro x hx
      simp only [removeAll, ne_eq, decide_not, List.mem_filter,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hx
      obtain ⟨hx_in, hx_ne⟩ := hx
      rcases hL x hx_in with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hx_ne
    let ctx := removeAll L (¬phi)
    exact h_not ⟨ctx, h_rem_sub,
      ⟨modal_dne_from_neg_neg h_implyK h_implyS h_efq h_peirce d_neg_neg⟩⟩
  · have hL_Gamma : ∀ x ∈ L, x ∈ Gamma := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hx) h_neg_in_L
    have d_ext : DerivationTree Axioms ((¬phi) :: L) Proposition.bot :=
      .weakening L ((¬phi) :: L) _ d_bot
        (fun x hx => List.mem_cons.mpr (Or.inr hx))
    have d_dt := deductionTheorem h_implyK h_implyS L (¬phi)
        Proposition.bot d_ext
    exact h_not ⟨L, hL_Gamma,
      ⟨modal_dne_from_neg_neg h_implyK h_implyS h_efq h_peirce d_dt⟩⟩

/-! ## Parametric Strong Soundness and Completeness -/

/-- **Parametric Strong Soundness**: Given a soundness callback for the axiom
system `Axioms` over the frame class `FC`, lift set-derivability to semantic
entailment over `FC`.

The callback `sound` takes any list-derivation `L ⊢ phi` and a satisfaction
witness for all of `L`, and returns satisfaction of `phi`. This decouples the
parametric infrastructure from any particular axiom system.

Instantiate at K with `k_soundness`; at T/S4/S5/TB/B/K4/K5/K45/KB5/D/D4/D5/D45/DB
with the respective per-system soundness theorem. -/
theorem strong_soundness
    {Axioms : Proposition Atom → Prop}
    {FC : ∀ {World : Type u}, Model World Atom → Prop}
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (sound : ∀ {World : Type u} (m : Model World Atom) (w : World)
             (L : List (Proposition Atom)),
             FC m → DerivationTree Axioms L phi →
             (∀ γ ∈ L, Satisfies m w γ) → Satisfies m w phi)
    (h : ModalSetDerivable Axioms Gamma phi) :
    ModalSemanticEntails FC Gamma phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  intro World m w hFC h_sat
  exact sound m w L hFC d (fun γ hγ => h_sat γ (hL_sub γ hγ))

/-- **Parametric Strong Completeness**: Given the four propositional axiom
callbacks, a pre-applied truth lemma for the canonical model, and a proof
that the canonical model satisfies the frame condition `FC`, derive
set-derivability from semantic entailment.

Proof by contrapositive: if `phi` is not set-derivable from `Gamma`, then
`Gamma ∪ {¬phi}` is consistent by `modal_not_SetDerivable_union_neg_consistent`.
By `modal_lindenbaum`, extend to an MCS `M ⊇ Gamma ∪ {¬phi}`. The truth lemma
witnesses that all of `Gamma` is satisfied at `M` in the canonical model but
`phi` is not (since `¬phi ∈ M`). This contradicts the semantic entailment
hypothesis instantiated at the canonical model. -/
theorem strong_completeness
    {Axioms : Proposition Atom → Prop}
    {FC : ∀ {World : Type u}, Model World Atom → Prop}
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (truthLemma : ∀ (S : CanonicalWorld Axioms) (φ : Proposition Atom),
      Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
    (canonical_FC : FC (CanonicalModel Axioms))
    (h : ModalSemanticEntails FC Gamma phi) :
    ModalSetDerivable Axioms Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    h_implyK h_implyS h_efq h_peirce h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld Axioms := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel Axioms) w γ :=
    fun γ hγ => (truthLemma w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld Axioms) (CanonicalModel Axioms) w
    canonical_FC h_gamma_sat
  have h_phi_M := (truthLemma w phi).mp h_phi_sat
  exact mcs_bot_not_mem hM_mcs
    (modal_implication_property h_implyK h_implyS hM_mcs h_neg_phi h_phi_M)

/-- **Parametric Biconditional Wrapper**: `phi` is a semantic consequence of `Gamma`
over all `FC`-frames iff `phi` is set-derivable from `Gamma`.

This combines `strong_soundness` and `strong_completeness` into a single iff, given
the same propositional axiom callbacks, truth lemma, and canonical frame-condition proof
used by `strong_completeness`. Instantiate at each system by providing system-specific
arguments to recover the system's biconditional completeness theorem. -/
theorem strong_completeness_iff
    {Axioms : Proposition Atom → Prop}
    {FC : ∀ {World : Type u}, Model World Atom → Prop}
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (sound : ∀ {World : Type u} (m : Model World Atom) (w : World)
             (L : List (Proposition Atom)),
             FC m → DerivationTree Axioms L phi →
             (∀ γ ∈ L, Satisfies m w γ) → Satisfies m w phi)
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (truthLemma : ∀ (S : CanonicalWorld Axioms) (φ : Proposition Atom),
      Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
    (canonical_FC : FC (CanonicalModel Axioms)) :
    ModalSemanticEntails FC Gamma phi ↔ ModalSetDerivable Axioms Gamma phi :=
  ⟨strong_completeness h_implyK h_implyS h_efq h_peirce truthLemma canonical_FC,
   strong_soundness sound⟩

/-- **Parametric Compactness**: If `phi` is a semantic consequence of `Gamma` over all
`FC`-frames, there exists a finite list `L ⊆ Gamma` such that `phi` is a semantic
consequence of (members of) `L` over all `FC`-frames.

Proof: `strong_completeness` produces a finite derivation witness; `strong_soundness`
lifts it back to semantic entailment restricted to the finite list. -/
theorem compactness
    {Axioms : Proposition Atom → Prop}
    {FC : ∀ {World : Type u}, Model World Atom → Prop}
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (sound : ∀ {World : Type u} (m : Model World Atom) (w : World)
             (L : List (Proposition Atom)),
             FC m → DerivationTree Axioms L phi →
             (∀ γ ∈ L, Satisfies m w γ) → Satisfies m w phi)
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (truthLemma : ∀ (S : CanonicalWorld Axioms) (φ : Proposition Atom),
      Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
    (canonical_FC : FC (CanonicalModel Axioms))
    (h : ModalSemanticEntails FC Gamma phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ModalSemanticEntails FC {ψ | ψ ∈ L} phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ :=
    strong_completeness h_implyK h_implyS h_efq h_peirce truthLemma canonical_FC h
  exact ⟨L, hL_sub,
    strong_soundness sound ⟨L, fun x hx => Set.mem_ofPred_eq.mpr hx, hL_deriv⟩⟩

/-- **Parametric Weak Completeness**: If `phi` is valid over all `FC`-frames
(satisfies at every world of every model satisfying `FC`), then `phi` is derivable
from the empty context.

This is a corollary of `strong_completeness` instantiated at `Gamma = ∅`, lifting
validity (universally quantified satisfaction) to derivability. -/
theorem weak_completeness
    {Axioms : Proposition Atom → Prop}
    {FC : ∀ {World : Type u}, Model World Atom → Prop}
    {phi : Proposition Atom}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (truthLemma : ∀ (S : CanonicalWorld Axioms) (φ : Proposition Atom),
      Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
    (canonical_FC : FC (CanonicalModel Axioms))
    (h_valid : ∀ (World : Type u) (m : Model World Atom), FC m → ∀ w, Satisfies m w phi) :
    Derivable Axioms phi :=
  ModalSetDerivable_empty_iff.mp
    (strong_completeness h_implyK h_implyS h_efq h_peirce truthLemma canonical_FC
      (ModalSemanticEntails_of_Valid h_valid ∅))

end Cslib.Logic.Modal
