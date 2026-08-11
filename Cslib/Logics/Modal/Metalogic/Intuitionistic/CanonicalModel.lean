/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory
public import Cslib.Logics.Modal.Metalogic.GenericMCSBridge
public import Cslib.Foundations.Logic.Theorems.DerivationCombinators

/-! # Canonical Model for Intuitionistic Modal Logic

This module lays down the birelational canonical-frame data for intuitionistic modal logic:
worlds are prime modal theories (`PrimeTheory.lean`), `≤` is set inclusion, `canonicalVal` is
the atom-membership valuation, and `canonicalR` is the two-clause canonical accessibility
relation required because `◇` is primitive (not `□`-definable) in this framework's
`Modal.Proposition` datatype.

This file starts with **definitions only**, no witness proofs. `canonical_box_witness`,
`canonical_diamond_witness`, and the frame conditions `canonical_f1`/`canonical_f2` are added by
subsequent sections in this same file.

## `Birelational.lean` API

- `BFrame World` (requires `[Preorder World]`) bundles `r : World → World → Prop`,
  `f1 : ∀ {w w' v}, w ≤ w' → r w v → ∃ v', r w' v' ∧ v ≤ v'` (up-confluence), and
  `f2 : ∀ {w v v'}, r w v → v ≤ v' → ∃ w', w ≤ w' ∧ r w' v'` (down-confluence).
- `BModel World Atom extends BFrame World` adds `v : World → Atom → Prop`,
  `botForces : World → Prop`, `v_upward_closed`, `bf_upward_closed`.
- `BForces r v botForces w φ` is the forcing relation; `@[simp]` unfolds exist for every
  constructor, in particular `BForces_box` (`∀ w' ≥ w, ∀ u, r w' u → BForces … u φ`) and
  `BForces_diamond` (`∃ u, r w u ∧ BForces … u φ`).
- `IValid`/`MValid` universally quantify over `World`/`r`/`f1`/`f2`/valuation (and, for
  `MValid`, `botForces`).

These names and shapes are used verbatim by `canonicalR` below and by the later sections
(`canonical_f1`/`canonical_f2` must match `BFrame.f1`/`BFrame.f2` exactly).

## Main Definitions

- `CanonicalPrimeWorld`: canonical worlds, i.e. prime modal theories (`ModalPrimeTheory`).
- The canonical `Preorder` instance: `≤` is set inclusion on the underlying theory.
- `canonicalVal`: the canonical valuation, `atom p` forced at `w` iff `atom p ∈ w`.
- `canonicalR`: the two-clause canonical accessibility relation (Simpson 1994, clauses 3.2/3.5;
  Wijesekera 1990 on the primitive-`◇` box condition):
  - box clause: `□φ ∈ w → φ ∈ v`;
  - diamond clause: `φ ∈ v → ◇φ ∈ w`.

  Both clauses are required (unlike the classical single-clause canonical relation) because `◇`
  is a primitive connective here, not defined as `¬□¬`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3, clauses 3.2/3.5.
* D. Wijesekera, *Constructive Modal Logics I*, Annals of Pure and Applied Logic, 1990 --
  primitive-`◇` canonical accessibility (the diamond clause has no classical analogue).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Metalogic.GenericMCS

variable {Atom : Type*}

/-! ## Canonical Worlds -/

/-- A canonical world for intuitionistic modal logic is a prime modal theory
(`ModalPrimeTheory Axioms`), parametric over the axiom predicate `Axioms`. Worlds are prime
(rather than maximal-consistent, as in the classical `MCS.lean` canonical model) so that the
disjunction property is available for the `or` case of the truth lemma (`TruthLemma.lean`). -/
def CanonicalPrimeWorld (Axioms : Proposition Atom → Prop) :=
  { S : Set (Proposition Atom) // ModalPrimeTheory Axioms S }

/-- The canonical preorder on `CanonicalPrimeWorld Axioms`: set inclusion of the underlying
prime theories. Mirrors the propositional canonical preorder
(`Cslib.Logic.PL.instPreorderIntCanonicalWorld` in `IntStrongCompleteness.lean`). -/
instance {Axioms : Proposition Atom → Prop} : Preorder (CanonicalPrimeWorld Axioms) where
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/-! ## Canonical Valuation -/

/-- The canonical valuation: atom `p` is forced at world `w` iff `atom p` is a member of the
prime theory underlying `w`. Mirrors `intCanonicalVal` (`IntStrongCompleteness.lean`). -/
def canonicalVal {Axioms : Proposition Atom → Prop} (w : CanonicalPrimeWorld Axioms) (p : Atom) :
    Prop :=
  Proposition.atom p ∈ w.val

/-- The canonical valuation is upward-closed with respect to the canonical preorder, as required
by `BModel.v_upward_closed`. -/
theorem canonicalVal_upward_closed {Axioms : Proposition Atom → Prop}
    {w w' : CanonicalPrimeWorld Axioms} (p : Atom) (hw : w ≤ w') (hv : canonicalVal w p) :
    canonicalVal w' p :=
  hw hv

/-! ## Canonical Accessibility Relation -/

/-- The canonical accessibility relation `canonicalR w v`, carrying **both** a box clause and a
diamond clause since `◇` is primitive and not `□`-definable (Wijesekera 1990):

- box clause (`□φ ∈ w → φ ∈ v`): every boxed formula true at `w` is true at `v`
  ([Simpson1994], clause 3.2's accessibility side);
- diamond clause (`φ ∈ v → ◇φ ∈ w`): every formula true at `v` is possible at `w`
  ([Simpson1994], clause 3.5's accessibility side).

The witness lemmas establishing that this relation actually exists between suitable worlds
(`canonical_box_witness`, `canonical_diamond_witness`) are proved below. -/
def canonicalR {Axioms : Proposition Atom → Prop} (w v : CanonicalPrimeWorld Axioms) : Prop :=
  (∀ φ, (□φ) ∈ w.val → φ ∈ v.val) ∧ (∀ φ, φ ∈ v.val → (◇φ) ∈ w.val)

/-! ## Box Witness Consistency Sub-Lemma

This section proves `box_witness_pair_underivable`, the modal consistency sub-lemma
establishing the `DerivExcludes` precondition needed by the seeded prime-extension `w'` below:
no finite disjunction of `Σ := {□B | B ∉ u.val}` is derivable from
`Γ := w.val ∪ {◇A | A ∈ u.val}`, given `{ψ | □ψ ∈ w.val} ⊆ u.val`.

Transliterated from ianshil/CK `general_th_completeness.v`, box case (~L211-249; the `Idb`
selector at ~L231). The argument needs three modal-axiom hypotheses beyond the intuitionistic
base -- `h_K` (Kb), `h_Kdia` (Kd), and `h_Idb` (the Fischer-Servi box bridge) -- plus
`h_andI`/`h_andE1`/`h_andE2` to combine the finitely many diamond hypotheses a derivation may
use into a single `◇(bigAnd …)` antecedent before `h_Idb` applies. The conjunction hypotheses
are a standard part of the intuitionistic `and`/`or` base (already axiomatized elsewhere in this
framework, e.g. `MCS.lean`'s `mcs_and_mem_iff`); they introduce no new axiom, only additional
parametric hypotheses in the same style as `h_implyK`/`h_implyS`/etc. -/

section BoxWitnessSublemma

variable {Axioms : Proposition Atom → Prop}

/-- Finite conjunction of a list of formulas; `bigAnd [] = ⊥ → ⊥` (a trivial, EFQ-derivable
tautology) and `bigAnd (A :: As) = A ∧ bigAnd As`. Dual of `Metalogic.bigOr`. -/
private def bigAnd : List (Proposition Atom) → Proposition Atom
  | [] => Proposition.bot.imp Proposition.bot
  | A :: As => A.and (bigAnd As)

/-- Splits a derivation context `L` (drawn from `w.val ∪ {◇A | A ∈ u.val}`) into the sublist of
`w.val`-members `Lw` and the bare diamond witnesses `As` (each `A ∈ u.val`, contributing `◇A`
to `L`), such that every element of `L` lies in `(As.map diamond) ++ Lw`. -/
private theorem extract_split (w u : CanonicalPrimeWorld Axioms) :
    ∀ (L : List (Proposition Atom)),
      (∀ x ∈ L, x ∈ w.val ∨ ∃ A, x = (◇A) ∧ A ∈ u.val) →
      ∃ Lw As : List (Proposition Atom),
        (∀ y ∈ Lw, y ∈ w.val) ∧ (∀ A ∈ As, A ∈ u.val) ∧
        (∀ x ∈ L, x ∈ (As.map Proposition.diamond) ++ Lw)
  | [], _ => by
      refine ⟨[], [], ?_, ?_, ?_⟩ <;> exact fun _ h => nomatch h
  | x :: xs, hL => by
      obtain ⟨Lw', As', hLw', hAs', hsub'⟩ :=
        extract_split w u xs (fun y hy => hL y (List.mem_cons.mpr (Or.inr hy)))
      rcases hL x (List.mem_cons.mpr (Or.inl rfl)) with hxw | ⟨A, hxeq, hAu⟩
      · refine ⟨x :: Lw', As', ?_, hAs', ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hxw
          · exact hLw' y hy'
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
          · rcases List.mem_append.mp (hsub' z hz') with h1 | h2
            · exact List.mem_append.mpr (Or.inl h1)
            · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h2)))
      · refine ⟨Lw', A :: As', hLw', ?_, ?_⟩
        · intro B hB
          rcases List.mem_cons.mp hB with rfl | hB'
          · exact hAu
          · exact hAs' B hB'
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · rw [hxeq]
            exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))
          · rcases List.mem_append.mp (hsub' z hz') with h1 | h2
            · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h1)))
            · exact List.mem_append.mpr (Or.inr h2)

/-- Extracts the bare witnesses `l''` of a list `l` drawn from `Σ = {□B | B ∉ u.val}`, so that
`l = l''.map box` with every element of `l''` excluded from `u.val`. -/
private theorem extract_box_list (u : CanonicalPrimeWorld Axioms) :
    ∀ (l : List (Proposition Atom)), (∀ x ∈ l, ∃ B, x = (□B) ∧ B ∉ u.val) →
      ∃ l'' : List (Proposition Atom), l = l''.map Proposition.box ∧ ∀ B ∈ l'', B ∉ u.val
  | [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | x :: xs, hl => by
      obtain ⟨B, hxeq, hBnu⟩ := hl x (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨l'', heq, hl''⟩ :=
        extract_box_list u xs (fun y hy => hl y (List.mem_cons.mpr (Or.inr hy)))
      refine ⟨B :: l'', ?_, ?_⟩
      · rw [hxeq, heq, List.map_cons, Proposition.box_def]
      · intro C hC
        rcases List.mem_cons.mp hC with rfl | hC'
        · exact hBnu
        · exact hl'' C hC'

/-- `□`-monotonicity: from an axiom instance `Axioms (A → B)`, derive `⊢ (□A) → (□B)` via
necessitation of the empty-context axiom instance, followed by `h_K`. -/
private def box_mono
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    {A B : Proposition Atom} (hAB : Axioms (A.imp B)) :
    DerivationTree Axioms [] ((Proposition.box A).imp (Proposition.box B)) :=
  .modus_ponens [] _ _ (.ax [] _ (h_K A B)) (.necessitation _ (.ax [] _ hAB))

/-- `◇`-monotonicity: from an axiom instance `Axioms (A → B)`, derive `⊢ (◇A) → (◇B)` via
necessitation of the empty-context axiom instance, followed by `h_Kdia`. -/
private def dia_mono
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    {A B : Proposition Atom} (hAB : Axioms (A.imp B)) :
    DerivationTree Axioms [] ((◇A).imp (◇B)) :=
  .modus_ponens [] _ _ (.ax [] _ (h_Kdia A B)) (.necessitation _ (.ax [] _ hAB))

/-- Empty-context implication composition: from `⊢ A → B` and `⊢ B → C`, derive `⊢ A → C`.

Routes through the generic `Theorems.DerivationCombinators.impTransD` combinator at
`ClosedHilbert (DerivationTree Axioms)`, made available by locally supplying
`HasMinimalAxioms Axioms` from the `h_implyK`/`h_implyS` witnesses (which activates the
existing `[HasMinimalAxioms Axioms] → HilbertTree (DerivationTree Axioms)` instance in
`GenericMCSBridge.lean`, used here read-only). -/
private noncomputable def imp_trans0
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {A B C : Proposition Atom}
    (d1 : DerivationTree Axioms [] (A.imp B)) (d2 : DerivationTree Axioms [] (B.imp C)) :
    DerivationTree Axioms [] (A.imp C) :=
  haveI : HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩
  @Cslib.Logic.Theorems.DerivationCombinators.impTransD
    _ _ _ (ClosedHilbert (DerivationTree Axioms)) _ _ A B C d1 d2

/-- **Box-of-disjuncts**: `⊢ (bigOr (l'.map box)) → (□ (bigOr l'))` -- a disjunction of already
-boxed formulas implies the box of the (unboxed) disjunction. Proved by induction on `l'` via
`box_mono` (K + necessitation of the `OrI1`/`OrI2` tautologies) combined through `h_orE`. -/
private noncomputable def boxOr_of_boxDisj
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))) :
    ∀ (l' : List (Proposition Atom)),
      DerivationTree Axioms []
        ((Metalogic.bigOr (l'.map Proposition.box)).imp (Proposition.box (Metalogic.bigOr l')))
  | [] =>
      .ax [] _ (h_efq (Proposition.box (Metalogic.bigOr ([] : List (Proposition Atom)))))
  | B :: rest => by
      have f1 : DerivationTree Axioms []
          ((Proposition.box B).imp (Proposition.box (Metalogic.bigOr (B :: rest)))) :=
        box_mono h_K (h_orI1 B (Metalogic.bigOr rest))
      have f2a : DerivationTree Axioms []
          ((Proposition.box (Metalogic.bigOr rest)).imp
            (Proposition.box (Metalogic.bigOr (B :: rest)))) :=
        box_mono h_K (h_orI2 B (Metalogic.bigOr rest))
      have ih := boxOr_of_boxDisj h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE h_K rest
      have f2 : DerivationTree Axioms []
          ((Metalogic.bigOr (rest.map Proposition.box)).imp
            (Proposition.box (Metalogic.bigOr (B :: rest)))) :=
        imp_trans0 h_implyK h_implyS ih f2a
      have step1 := DerivationTree.modus_ponens [] _ _
        (DerivationTree.ax [] _
          (h_orE (Proposition.box B) (Metalogic.bigOr (rest.map Proposition.box))
            (Proposition.box (Metalogic.bigOr (B :: rest)))))
        f1
      exact DerivationTree.modus_ponens [] _ _ step1 f2

/-- Combines a list of separately-used hypotheses `Ds` (with leftover context `Lw`) into a
single conjunction hypothesis: `Ds ++ Lw ⊢ ψ` implies `bigAnd Ds :: Lw ⊢ ψ`. Uses `h_andE1`/
`h_andE2` to recover each `Ds`-member from the single `bigAnd Ds` assumption. -/
private noncomputable def unpack_conj_partial
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ)) :
    ∀ (Ds Lw : List (Proposition Atom)) (ψ : Proposition Atom),
      DerivationTree Axioms (Ds ++ Lw) ψ → DerivationTree Axioms (bigAnd Ds :: Lw) ψ
  | [], Lw, ψ, d =>
      .weakening Lw (bigAnd ([] : List (Proposition Atom)) :: Lw) ψ d
        (fun x hx => List.mem_cons.mpr (Or.inr hx))
  | D :: Ds', Lw, ψ, d => by
      have dt := deductionTheorem h_implyK h_implyS (Ds' ++ Lw) D ψ d
      have ihres := unpack_conj_partial h_implyK h_implyS h_andE1 h_andE2 Ds' Lw (D.imp ψ) dt
      have ihres0 : DerivationTree Axioms Lw ((bigAnd Ds').imp (D.imp ψ)) :=
        deductionTheorem h_implyK h_implyS Lw (bigAnd Ds') (D.imp ψ) ihres
      have hmem : DerivationTree Axioms (bigAnd (D :: Ds') :: Lw) (bigAnd (D :: Ds')) :=
        .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
      have hD : DerivationTree Axioms (bigAnd (D :: Ds') :: Lw) D :=
        .modus_ponens _ (bigAnd (D :: Ds')) D
          (.weakening [] _ _ (.ax [] _ (h_andE1 D (bigAnd Ds'))) (fun _ h => nomatch h))
          hmem
      have hConjRest : DerivationTree Axioms (bigAnd (D :: Ds') :: Lw) (bigAnd Ds') :=
        .modus_ponens _ (bigAnd (D :: Ds')) (bigAnd Ds')
          (.weakening [] _ _ (.ax [] _ (h_andE2 D (bigAnd Ds'))) (fun _ h => nomatch h))
          hmem
      have hDimpψ : DerivationTree Axioms (bigAnd (D :: Ds') :: Lw) (D.imp ψ) :=
        .modus_ponens _ (bigAnd Ds') (D.imp ψ)
          (.weakening Lw _ _ ihres0 (fun x hx => List.mem_cons.mpr (Or.inr hx)))
          hConjRest
      exact .modus_ponens _ D ψ hDimpψ hD

/-- **Diamond/conjunction bridge**: `⊢ (◇(bigAnd As)) → (bigAnd (As.map diamond))` -- the
diamond of a conjunction implies the conjunction of the diamonds (the VALID monotonicity
direction; the converse is not generally valid). Proved by induction on `As` via `dia_mono`
(K◇ + necessitation of the `AndE1`/`AndE2` tautologies) combined through `h_andI`. Analogue of
ianshil/CK's `list_conj_Diam_obj`. -/
private noncomputable def dia_bigAnd_to_bigAnd_dia
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ)) :
    ∀ (As : List (Proposition Atom)),
      DerivationTree Axioms [] ((◇ (bigAnd As)).imp (bigAnd (As.map Proposition.diamond)))
  | [] =>
      .modus_ponens [] _ _
        (.ax [] _ (h_implyK (bigAnd ([] : List (Proposition Atom)))
          (Proposition.diamond (bigAnd ([] : List (Proposition Atom))))))
        (.ax [] _ (h_efq Proposition.bot))
  | A :: As' => by
      have f1 : DerivationTree Axioms [] ((◇ (bigAnd (A :: As'))).imp (◇A)) :=
        dia_mono h_Kdia (h_andE1 A (bigAnd As'))
      have f2 : DerivationTree Axioms [] ((◇ (bigAnd (A :: As'))).imp (◇ (bigAnd As'))) :=
        dia_mono h_Kdia (h_andE2 A (bigAnd As'))
      have ih := dia_bigAnd_to_bigAnd_dia h_implyK h_implyS h_Kdia h_andI h_andE1 h_andE2 h_efq As'
      have f2' : DerivationTree Axioms []
          ((◇ (bigAnd (A :: As'))).imp (bigAnd (As'.map Proposition.diamond))) :=
        imp_trans0 h_implyK h_implyS f2 ih
      have hXmem : DerivationTree Axioms [◇ (bigAnd (A :: As'))] (◇ (bigAnd (A :: As'))) :=
        .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
      have hdiaA : DerivationTree Axioms [◇ (bigAnd (A :: As'))] (◇A) :=
        .modus_ponens _ _ _ (.weakening [] _ _ f1 (fun _ h => nomatch h)) hXmem
      have hrest : DerivationTree Axioms [◇ (bigAnd (A :: As'))]
          (bigAnd (As'.map Proposition.diamond)) :=
        .modus_ponens _ _ _ (.weakening [] _ _ f2' (fun _ h => nomatch h)) hXmem
      have andI_ax : DerivationTree Axioms [◇ (bigAnd (A :: As'))]
          ((◇A).imp ((bigAnd (As'.map Proposition.diamond)).imp
            ((◇A).and (bigAnd (As'.map Proposition.diamond))))) :=
        .weakening [] _ _ (.ax [] _ (h_andI (◇A) (bigAnd (As'.map Proposition.diamond))))
          (fun _ h => nomatch h)
      have step1 := DerivationTree.modus_ponens _ _ _ andI_ax hdiaA
      have step2 := DerivationTree.modus_ponens _ _ _ step1 hrest
      exact deductionTheorem h_implyK h_implyS [] (◇ (bigAnd (A :: As'))) _ step2

/-- `bigAnd As ∈ u.val` whenever every element of `As` is in `u.val` (using `h_andI` and the
deductive closure of the prime theory `u.val`). -/
private theorem bigAnd_mem_u
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (u : CanonicalPrimeWorld Axioms) :
    ∀ (As : List (Proposition Atom)), (∀ A ∈ As, A ∈ u.val) → bigAnd As ∈ u.val
  | [], _ =>
      u.2.1.2 [] _ (fun _ h => nomatch h) ⟨.ax [] _ (h_efq Proposition.bot)⟩
  | A :: As', hAs => by
      have hA : A ∈ u.val := hAs A (List.mem_cons.mpr (Or.inl rfl))
      have hRest : bigAnd As' ∈ u.val :=
        bigAnd_mem_u h_efq h_andI u As' (fun B hB => hAs B (List.mem_cons.mpr (Or.inr hB)))
      have h1 : DerivationTree Axioms [A, bigAnd As'] A :=
        .assumption _ A (List.mem_cons.mpr (Or.inl rfl))
      have h2 : DerivationTree Axioms [A, bigAnd As'] (bigAnd As') :=
        .assumption _ (bigAnd As') (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      have hax : DerivationTree Axioms [A, bigAnd As']
          (A.imp ((bigAnd As').imp (A.and (bigAnd As')))) :=
        .weakening [] _ _ (.ax [] _ (h_andI A (bigAnd As'))) (fun _ h => nomatch h)
      have hderiv : DerivationTree Axioms [A, bigAnd As'] (A.and (bigAnd As')) :=
        .modus_ponens _ _ _ (.modus_ponens _ _ _ hax h1) h2
      exact u.2.1.2 [A, bigAnd As'] _
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hA
          · rcases List.mem_cons.mp hx' with rfl | hx''
            · exact hRest
            · nomatch hx'')
        ⟨hderiv⟩

/-- `bigOr [] = ⊥`, spelled out explicitly since the definitional unfold is occasionally not
picked up automatically by the elaborator at use sites. -/
private theorem bigOr_nil_eq_bot :
    Metalogic.bigOr ([] : List (Proposition Atom)) = Proposition.bot := rfl

/-- If `u.val` is prime and consistent, `bigOr l'' ∈ u.val` forces some disjunct into
`u.val`. -/
private theorem bigOr_mem_disjunct (u : CanonicalPrimeWorld Axioms) :
    ∀ (l'' : List (Proposition Atom)), Metalogic.bigOr l'' ∈ u.val → ∃ B ∈ l'', B ∈ u.val
  | [], hmem => by
      exfalso
      rw [bigOr_nil_eq_bot] at hmem
      have hbot : (modalDerivationSystem Axioms).Deriv [Proposition.bot] Proposition.bot :=
        ⟨.assumption [Proposition.bot] Proposition.bot (List.mem_cons.mpr (Or.inl rfl))⟩
      exact u.2.1.1 [Proposition.bot]
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hmem
          · exact absurd hx' (by simp))
        hbot
  | B :: rest, hmem => by
      have hdisj : B ∈ u.val ∨ Metalogic.bigOr rest ∈ u.val := u.2.2 B (Metalogic.bigOr rest) hmem
      rcases hdisj with hB | hrest
      · exact ⟨B, List.mem_cons.mpr (Or.inl rfl), hB⟩
      · obtain ⟨B', hB'mem, hB'u⟩ := bigOr_mem_disjunct u rest hrest
        exact ⟨B', List.mem_cons.mpr (Or.inr hB'mem), hB'u⟩

/-- **Box Witness Consistency Sub-Lemma**: no finite disjunction of `Σ := {□B | B ∉ u.val}` is
derivable from `Γ := w.val ∪ {◇A | A ∈ u.val}`, given `{ψ | □ψ ∈ w.val} ⊆ u.val`. Discharges the
`DerivExcludes` precondition that the seeded prime extension `w'` below needs.

Proof sketch (ianshil/CK `general_th_completeness.v` box case ~L211-249): suppose
`Γ ⊢ □B₁ ⊔ … ⊔ □Bₙ` via a finite subset using `g₁,…,g_k ∈ w.val` and `◇A₁,…,◇A_m` with each
`Aⱼ ∈ u.val` (`extract_split`). First convert the boxed-disjuncts disjunction into a boxed
disjunction (`boxOr_of_boxDisj`, K + necessitation + OrE), then combine the `m` diamond
hypotheses into one (`unpack_conj_partial`), discharge it via the deduction theorem, and use
`w.val`'s deductive closure to place `(bigAnd Aⱼ → □(bigOr Bᵢ)) ∈ w.val`. Bridge the antecedent
to a single diamond via `h_Kdia` (`dia_bigAnd_to_bigAnd_dia`), then apply `h_Idb` to obtain
`□(bigAnd Aⱼ → bigOr Bᵢ) ∈ w.val`. The hypothesis `{ψ | □ψ ∈ w.val} ⊆ u.val` places this
implication in `u.val`; since `u.val` is deductively closed and contains each `Aⱼ`
(`bigAnd_mem_u`), `bigOr Bᵢ ∈ u.val`. Finally `u.val`'s disjunction property
(`bigOr_mem_disjunct`) forces some `Bᵢ ∈ u.val`, contradicting `Bᵢ ∉ u.val` (from `Σ`). -/
theorem box_witness_pair_underivable
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w u : CanonicalPrimeWorld Axioms}
    (h_wu : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ u.val) :
    Metalogic.DerivExcludes (modalDerivationSystem Axioms)
      {χ | ∃ B, χ = (□B) ∧ B ∉ u.val}
      (modalDeductiveClosure Axioms (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ u.val})) := by
  intro l hlSig hmem
  obtain ⟨L, hLΓ, hd⟩ := hmem
  obtain ⟨l'', hl''eq, hl''u⟩ := extract_box_list u l hlSig
  obtain ⟨d⟩ := hd
  rw [hl''eq] at d
  have bridge0 := boxOr_of_boxDisj h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE h_K l''
  have d_box : DerivationTree Axioms L (Proposition.box (Metalogic.bigOr l'')) :=
    .modus_ponens L _ _ (.weakening [] L _ bridge0 (fun _ h => nomatch h)) d
  have hLΓ' : ∀ x ∈ L, x ∈ w.val ∨ ∃ A, x = (◇A) ∧ A ∈ u.val := fun x hx => hLΓ x hx
  obtain ⟨Lw, As, hLw, hAs, hsub⟩ := extract_split w u L hLΓ'
  have d_box' : DerivationTree Axioms ((As.map Proposition.diamond) ++ Lw)
      (Proposition.box (Metalogic.bigOr l'')) :=
    .weakening L _ _ d_box hsub
  have d_unpack : DerivationTree Axioms (bigAnd (As.map Proposition.diamond) :: Lw)
      (Proposition.box (Metalogic.bigOr l'')) :=
    unpack_conj_partial h_implyK h_implyS h_andE1 h_andE2 (As.map Proposition.diamond) Lw _ d_box'
  have d_disch : DerivationTree Axioms Lw
      ((bigAnd (As.map Proposition.diamond)).imp (Proposition.box (Metalogic.bigOr l''))) :=
    deductionTheorem h_implyK h_implyS Lw (bigAnd (As.map Proposition.diamond))
      (Proposition.box (Metalogic.bigOr l'')) d_unpack
  have hM : (bigAnd (As.map Proposition.diamond)).imp (Proposition.box (Metalogic.bigOr l''))
      ∈ w.val :=
    w.2.1.2 Lw _ hLw ⟨d_disch⟩
  have bridge1 := dia_bigAnd_to_bigAnd_dia h_implyK h_implyS h_Kdia h_andI h_andE1 h_andE2 h_efq As
  set X : Proposition Atom := ◇ (bigAnd As) with hXdef
  set M : Proposition Atom :=
    (bigAnd (As.map Proposition.diamond)).imp (Proposition.box (Metalogic.bigOr l'')) with hMdef
  have step : DerivationTree Axioms [X, M] (Proposition.box (Metalogic.bigOr l'')) := by
    have hXmem : DerivationTree Axioms [X, M] X :=
      .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
    have hMmem : DerivationTree Axioms [X, M] M :=
      .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    have hBD : DerivationTree Axioms [X, M] (bigAnd (As.map Proposition.diamond)) :=
      .modus_ponens _ _ _ (.weakening [] _ _ bridge1 (fun _ h => nomatch h)) hXmem
    exact .modus_ponens _ _ _ hMmem hBD
  have step_disch : DerivationTree Axioms [M] (X.imp (Proposition.box (Metalogic.bigOr l''))) :=
    deductionTheorem h_implyK h_implyS [M] X (Proposition.box (Metalogic.bigOr l'')) step
  have hXimpBOX : X.imp (Proposition.box (Metalogic.bigOr l'')) ∈ w.val :=
    w.2.1.2 [M] _
      (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hM
        · exact absurd hy' (by simp))
      ⟨step_disch⟩
  have hBoxImp : Proposition.box ((bigAnd As).imp (Metalogic.bigOr l'')) ∈ w.val :=
    w.2.1.2 [X.imp (Proposition.box (Metalogic.bigOr l''))] _
      (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hXimpBOX
        · exact absurd hy' (by simp))
      ⟨.modus_ponens _ _ _ (.ax _ _ (h_Idb (bigAnd As) (Metalogic.bigOr l'')))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  have hInU : (bigAnd As).imp (Metalogic.bigOr l'') ∈ u.val := h_wu _ hBoxImp
  have hBigAndAsU : bigAnd As ∈ u.val := bigAnd_mem_u h_efq h_andI u As hAs
  have hBigOrU : Metalogic.bigOr l'' ∈ u.val :=
    u.2.1.2 [(bigAnd As).imp (Metalogic.bigOr l''), bigAnd As] _
      (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hInU
        · rcases List.mem_cons.mp hy' with rfl | hy''
          · exact hBigAndAsU
          · nomatch hy'')
      ⟨.modus_ponens _ _ _
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
        (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
  obtain ⟨B, hBmem, hBu⟩ := bigOr_mem_disjunct u l'' hBigOrU
  exact (hl''u B hBmem) hBu

end BoxWitnessSublemma

/-! ## Box Witness

This section proves `canonical_box_witness`, the corrected PAIR-shaped box witness: from
`(□φ) ∉ w.val`, it produces `w' ≥ w` and a prime world `u` with `canonicalR w' u` and
`φ ∉ u.val`. It also introduces `modal_set_exclusion`, a thin wrapper around
`Metalogic.prime_set_exclusion` (placed here, NOT in `PrimeTheory.lean`, to keep that file
unmodified).

**Construction** (ianshil/CK `general_th_completeness.v`, box case):
- **Step 1**: `u` is the prime extension (`modal_prime_exclusion`) of `{ψ | □ψ ∈ w.val}`
  excluding `φ`. `{ψ | □ψ ∈ w.val}` is admissible: deductively closed via the K-closure
  argument (`box_context_deriv`), and consistent because an inconsistency would force
  `□⊥ ∈ w.val`, hence (via EFQ necessitated + K) `□φ ∈ w.val`, contradicting the hypothesis.
- **Step 2**: `w'` is the prime extension (`modal_set_exclusion`) of the deductive closure of
  `Γ := w.val ∪ {◇A | A ∈ u.val}`, excluding `Σ := {□B | B ∉ u.val}`. The `DerivExcludes Σ Γ`
  precondition is exactly `box_witness_pair_underivable` above.
- The three witness obligations (`w ≤ w'`, `canonicalR w' u`, `φ ∉ u.val`) then hold **by
  construction**: `w ≤ w'` and the diamond clause follow from the seeding
  (`Γ ⊆ closure Γ ⊆ w'.val`); the box clause follows from `Σ`-exclusion (contrapositive,
  via `DerivExcludes` on the singleton `[□ψ]`); `φ ∉ u.val` is Step 1. -/

section CanonicalBoxWitness

variable {Axioms : Proposition Atom → Prop}

/-- **K-closure**: if `Γ ⊢ ψ`, then `(Γ.map □) ⊢ □ψ` -- pushing necessitation through a whole
derivation context via the deduction theorem and `h_K`, one hypothesis at a time. Used to show
`{ψ | □ψ ∈ w.val}` is deductively closed (Step 1 of `canonical_box_witness`). -/
private noncomputable def box_context_deriv
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))) :
    ∀ (L : List (Proposition Atom)) (ψ : Proposition Atom),
      DerivationTree Axioms L ψ →
      DerivationTree Axioms (L.map Proposition.box) (Proposition.box ψ)
  | [], ψ, d => .necessitation ψ d
  | A :: L', ψ, d => by
      have dt : DerivationTree Axioms L' (A.imp ψ) := deductionTheorem h_implyK h_implyS L' A ψ d
      have ihres : DerivationTree Axioms (L'.map Proposition.box) (Proposition.box (A.imp ψ)) :=
        box_context_deriv h_implyK h_implyS h_K L' (A.imp ψ) dt
      have hKax : DerivationTree Axioms (L'.map Proposition.box)
          ((Proposition.box (A.imp ψ)).imp ((Proposition.box A).imp (Proposition.box ψ))) :=
        .weakening [] _ _ (.ax [] _ (h_K A ψ)) (fun _ h => nomatch h)
      have hstep : DerivationTree Axioms (L'.map Proposition.box)
          ((Proposition.box A).imp (Proposition.box ψ)) :=
        .modus_ponens _ _ _ hKax ihres
      have hstep_w : DerivationTree Axioms (Proposition.box A :: L'.map Proposition.box)
          ((Proposition.box A).imp (Proposition.box ψ)) :=
        .weakening _ _ _ hstep (fun x hx => List.mem_cons.mpr (Or.inr hx))
      have hboxA : DerivationTree Axioms (Proposition.box A :: L'.map Proposition.box)
          (Proposition.box A) :=
        .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
      exact .modus_ponens _ _ _ hstep_w hboxA

/-- **Set (Lindenbaum-Pair) Exclusion Lemma for Modal Theories**: given an admissible set `S`
deriving no finite disjunction of `E`, there exists a prime modal theory `T ⊇ S` still deriving
no finite disjunction of `E`. Thin wrapper around `Metalogic.prime_set_exclusion`, mirroring
`modal_prime_exclusion` (`PrimeTheory.lean`) but for the generalized set-exclusion condition
needed by the seeded box witness below. Placed here (NOT `PrimeTheory.lean`) so that file stays
unmodified. -/
theorem modal_set_exclusion
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    {S : Set (Proposition Atom)}
    (h_adm : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms) S)
    {E : Set (Proposition Atom)}
    (h_excl : Metalogic.DerivExcludes (modalDerivationSystem Axioms) E S) :
    ∃ T, S ⊆ T ∧ ModalPrimeTheory Axioms T ∧
      Metalogic.DerivExcludes (modalDerivationSystem Axioms) E T :=
  Metalogic.prime_set_exclusion
    (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
    h_adm h_excl
    (fun A B => ⟨.ax [] _ (h_orI1 A B)⟩)
    (fun A B => ⟨.ax [] _ (h_orI2 A B)⟩)
    (fun A B χ => ⟨.ax [] _ (h_orE A B χ)⟩)
    (fun A => ⟨.ax [] _ (h_efq A)⟩)
    (modalDeductiveClosure Axioms)
    (modal_subset_deductive_closure Axioms)
    (fun {_X _ψ} h => h)
    (fun {_X} hX => modalDeductiveClosure_is_admissible h_implyK h_implyS hX)
    -- bot bridge: ⊥ ∈ cl X directly witnesses the inconsistency (no EFQ bridge needed, unlike
    -- `modal_prime_exclusion`'s `phi_mem_cl_of_not_cons`)
    (fun {X} h_not_cons => by
      classical
      simp only [ModalSetConsistent, Metalogic.SetConsistent, Metalogic.Consistent,
        not_forall, not_not] at h_not_cons
      obtain ⟨Linc, hLinc_sub, hLinc_bot⟩ := h_not_cons
      exact ⟨Linc, hLinc_sub, hLinc_bot⟩)
    (fun {U _L a _b} hL hd =>
      modal_deriv_imp_of_union h_implyK h_implyS
        (fun x hx => by
          rcases Set.mem_insert_iff.mp (hL x hx) with rfl | hu
          · exact Set.mem_union_right U (Set.mem_singleton_iff.mpr rfl)
          · exact Set.mem_union_left _ hu)
        hd)
    (fun C hchain hCne hCsub L hL hd =>
      let ⟨T', hT'C, hLT'⟩ := Metalogic.finite_list_in_chain_member hchain hCne L hL
      (hCsub hT'C).2.1.1 L hLT' hd)

/-- **Box Witness**: the corrected PAIR-shaped box witness. From `(□φ) ∉ w.val`, produces
`w' ≥ w` (a seeded prime extension) and a prime `u` with `canonicalR w' u` and `φ ∉ u.val`. The
outer `w ≤ w'` is load-bearing, consumed by `BForces_box` in `TruthLemma.lean`'s box case.

See [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
Ch. 3; ianshil/CK `general_th_completeness.v`, box case. -/
theorem canonical_box_witness
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w : CanonicalPrimeWorld Axioms} {φ : Proposition Atom} (h_notbox : (□φ) ∉ w.val) :
    ∃ w' u : CanonicalPrimeWorld Axioms, w ≤ w' ∧ canonicalR w' u ∧ φ ∉ u.val := by
  -- Step 1: u := prime extension of {ψ | □ψ ∈ w.val} excluding φ.
  have hS1_closed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms)
      {ψ | (□ψ) ∈ w.val} := by
    intro L ψ hL hd
    obtain ⟨d⟩ := hd
    exact w.2.1.2 (L.map Proposition.box) (Proposition.box ψ)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact hL y hy)
      ⟨box_context_deriv h_implyK h_implyS h_K L ψ d⟩
  have hS1_cons : ModalSetConsistent Axioms {ψ | (□ψ) ∈ w.val} := by
    intro L hL hd
    obtain ⟨d⟩ := hd
    have hboxbot_mem : (□(Proposition.bot : Proposition Atom)) ∈ w.val :=
      w.2.1.2 (L.map Proposition.box) (Proposition.box Proposition.bot)
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact hL y hy)
        ⟨box_context_deriv h_implyK h_implyS h_K L Proposition.bot d⟩
    have hbox_efq : DerivationTree Axioms [] ((Proposition.box Proposition.bot).imp (□φ)) :=
      box_mono h_K (h_efq φ)
    have hbox_phi : (□φ) ∈ w.val :=
      w.2.1.2 [Proposition.box Proposition.bot] (□φ)
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hboxbot_mem
          · nomatch hx')
        ⟨.modus_ponens _ _ _ (.weakening [] _ _ hbox_efq (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    exact h_notbox hbox_phi
  have h_phi_not_S1 : φ ∉ {ψ | (□ψ) ∈ w.val} := h_notbox
  obtain ⟨Uval, hS1_sub_U, hprimeU, hphi_not_U⟩ :=
    modal_prime_exclusion h_implyK h_implyS h_efq h_orE ⟨hS1_cons, hS1_closed⟩ h_phi_not_S1
  let u : CanonicalPrimeWorld Axioms := ⟨Uval, hprimeU⟩
  have hSu : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ u.val := fun ψ hψ => hS1_sub_U hψ
  -- Step 2: w' := seeded prime extension of w.val ∪ {◇A | A ∈ u.val} excluding {□B | B ∉ u.val}.
  have hbwu := box_witness_pair_underivable h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
    h_andI h_andE1 h_andE2 h_K h_Kdia h_Idb (w := w) (u := u) hSu
  have h_cons_raw : ModalSetConsistent Axioms
      (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ u.val}) := by
    intro L hL hd
    have hbot_not_mem := hbwu [] (fun _ h => nomatch h)
    rw [bigOr_nil_eq_bot] at hbot_not_mem
    exact hbot_not_mem ⟨L, hL, hd⟩
  have h_adm_raw : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
      (modalDeductiveClosure Axioms (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ u.val})) :=
    modalDeductiveClosure_is_admissible h_implyK h_implyS h_cons_raw
  obtain ⟨Tval, hclosure_sub_T, hprimeT, hexclT⟩ :=
    modal_set_exclusion h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE h_adm_raw hbwu
  let w' : CanonicalPrimeWorld Axioms := ⟨Tval, hprimeT⟩
  have hw_le_w' : w ≤ w' := by
    intro x hx
    exact hclosure_sub_T (modal_subset_deductive_closure Axioms _ (Set.mem_union_left _ hx))
  have hdia_clause : ∀ ψ, ψ ∈ u.val → (◇ψ) ∈ w'.val := by
    intro ψ hψ
    exact hclosure_sub_T (modal_subset_deductive_closure Axioms _
      (Set.mem_union_right _ ⟨ψ, rfl, hψ⟩))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w'.val → ψ ∈ u.val := by
    intro ψ hψ_mem
    by_contra hψ_notU
    have hsig : ∀ x ∈ [(□ψ)], x ∈ {χ | ∃ B, χ = (□B) ∧ B ∉ u.val} := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨ψ, rfl, hψ_notU⟩
      · nomatch hx'
    have hOrI1_deriv : DerivationTree Axioms [(□ψ)] (Metalogic.bigOr [(□ψ)]) :=
      .modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (h_orI1 (□ψ) (Metalogic.bigOr ([] : List (Proposition Atom)))))
          (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
    have hbigOr_mem : Metalogic.bigOr [(□ψ)] ∈ w'.val :=
      w'.2.1.2 [(□ψ)] _
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hψ_mem
          · nomatch hx')
        ⟨hOrI1_deriv⟩
    exact hexclT [(□ψ)] hsig hbigOr_mem
  exact ⟨w', u, hw_le_w', ⟨hbox_clause, hdia_clause⟩, hphi_not_U⟩

end CanonicalBoxWitness

/-! ## Diamond Witness

This section proves `canonical_diamond_witness`: from `(◇φ) ∈ w.val`, it produces a single
prime world `v` with `canonicalR w v` and `φ ∈ v.val`. Unlike the box witness above, no
extension of `w` itself is needed -- `BForces_diamond` is a bare `∃ v, r w v ∧ …`, so the
construction is a single seeded prime extension, not a pair.

The reference mechanization's `cexpl` ("Case A", `◇⊥ ∈ w.val`) branch is **not** reachable for
our consistent-only `CanonicalPrimeWorld` once a parametric hypothesis `h_dbot : Axioms
((◇⊥).imp ⊥)` (the IK axiom `◇⊥ → ⊥`, dropped by bare CK) is threaded in. Rather than a
top-level case split, `h_dbot` slots in as the **base case** of `diaOr_of_diaDisj` (the lemma
dual to `boxOr_of_boxDisj`, distributing `◇` out over an arbitrary-length disjunction): for the
empty list, `⊢ (◇⊥).imp ⊥` is exactly `h_dbot`, playing the same structural role there that
`h_efq` plays in `boxOr_of_boxDisj`'s empty case (`⊢ ⊥.imp (□⊥)`). This absorbs the "Case A"
concern entirely into the induction, with no separate branch needed in
`canonical_diamond_witness` itself.

**Construction** (dual of `canonical_box_witness`, ianshil/CK `general_th_completeness.v`
diamond case): `v` is the prime extension (`modal_set_exclusion`) of the deductive closure of
`Γ := {ψ | □ψ ∈ w.val} ∪ {φ}`, excluding `Σ := {ψ | (◇ψ) ∉ w.val}`. The `DerivExcludes Σ Γ`
precondition is `diamond_witness_underivable`. The three witness obligations then hold by
construction: `φ ∈ v.val` and the box clause (`□ψ ∈ w.val → ψ ∈ v.val`) follow from the seeding
(`Γ ⊆ closure Γ ⊆ v.val`); the diamond clause (`ψ ∈ v.val → ◇ψ ∈ w.val`) follows from
`Σ`-exclusion (contrapositive, mirroring `canonical_box_witness`'s `hbox_clause`). -/

section CanonicalDiamondWitness

variable {Axioms : Proposition Atom → Prop}

/-- **Diamond-of-disjuncts, hard direction**: `⊢ (◇(bigOr l')) → (bigOr (l'.map diamond))` -- the
diamond of a disjunction implies the disjunction of the diamonds. Unlike `boxOr_of_boxDisj`
(the dual, "free" direction, needing only `h_K` + necessitated `OrI1`/`OrI2`), this direction is
**not** valid for bare K◇ alone: it requires `h_Cd` (Fischer-Servi diamond bridge, ◇-over-∨) at
each inductive step, and, for the empty list (`bigOr [] = ⊥`), `h_dbot` (`◇⊥ → ⊥`) -- this is
precisely where "Case A" (`◇⊥` reachable) would obstruct the construction if `h_dbot` were
unavailable; IK supplies it, bare CK does not. Analogue of ianshil/CK's `Diam_distrib_list_disj`.
-/
private noncomputable def diaOr_of_diaDisj
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_Cd : ∀ (φ ψ : Proposition Atom),
      Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_dbot : Axioms ((◇Proposition.bot).imp Proposition.bot)) :
    ∀ (l' : List (Proposition Atom)),
      DerivationTree Axioms []
        ((◇ (Metalogic.bigOr l')).imp (Metalogic.bigOr (l'.map Proposition.diamond)))
  | [] => by
      simp only [List.map_nil, bigOr_nil_eq_bot]
      exact .ax [] _ h_dbot
  | B :: rest => by
      have hCd : DerivationTree Axioms []
          ((◇ (B.or (Metalogic.bigOr rest))).imp ((◇B).or (◇ (Metalogic.bigOr rest)))) :=
        .ax [] _ (h_Cd B (Metalogic.bigOr rest))
      have ih := diaOr_of_diaDisj h_implyK h_implyS h_orI1 h_orI2 h_orE h_Cd h_dbot rest
      have branch1 : DerivationTree Axioms []
          ((◇B).imp ((◇B).or (Metalogic.bigOr (rest.map Proposition.diamond)))) :=
        .ax [] _ (h_orI1 (◇B) (Metalogic.bigOr (rest.map Proposition.diamond)))
      have branch2 : DerivationTree Axioms []
          ((◇ (Metalogic.bigOr rest)).imp
            ((◇B).or (Metalogic.bigOr (rest.map Proposition.diamond)))) :=
        imp_trans0 h_implyK h_implyS ih
          (.ax [] _ (h_orI2 (◇B) (Metalogic.bigOr (rest.map Proposition.diamond))))
      have step1 := DerivationTree.modus_ponens [] _ _
        (.ax [] _ (h_orE (◇B) (◇ (Metalogic.bigOr rest))
          ((◇B).or (Metalogic.bigOr (rest.map Proposition.diamond)))))
        branch1
      have step2 := DerivationTree.modus_ponens [] _ _ step1 branch2
      exact imp_trans0 h_implyK h_implyS hCd step2

/-- Splits a derivation context `L` (drawn from `{ψ|□ψ∈w.val} ∪ {φ}`) into the sublist `Lw` of
`{ψ|□ψ∈w.val}`-members, such that every element of `L` lies in `φ :: Lw`. Simpler than the box
witness's `extract_split`, since the seed adds only the single extra formula `φ`, not a family
indexed by a second prime theory. -/
private theorem extract_split_dia (w : CanonicalPrimeWorld Axioms) (φ : Proposition Atom) :
    ∀ (L : List (Proposition Atom)),
      (∀ x ∈ L, (□x) ∈ w.val ∨ x = φ) →
      ∃ Lw : List (Proposition Atom), (∀ y ∈ Lw, (□y) ∈ w.val) ∧ (∀ x ∈ L, x ∈ φ :: Lw)
  | [], _ => by refine ⟨[], ?_, ?_⟩ <;> exact fun _ h => nomatch h
  | x :: xs, hL => by
      obtain ⟨Lw', hLw', hsub'⟩ :=
        extract_split_dia w φ xs (fun y hy => hL y (List.mem_cons.mpr (Or.inr hy)))
      rcases hL x (List.mem_cons.mpr (Or.inl rfl)) with hxbox | hxeq
      · refine ⟨x :: Lw', ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hxbox
          · exact hLw' y hy'
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
          · rcases List.mem_cons.mp (hsub' z hz') with rfl | hz''
            · exact List.mem_cons.mpr (Or.inl rfl)
            · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hz'')))
      · refine ⟨Lw', hLw', ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · rw [hxeq]; exact List.mem_cons.mpr (Or.inl rfl)
        · exact hsub' z hz'

/-- **Diamond Witness Underivability Sub-Lemma**: no finite disjunction of
`Σ := {ψ | (◇ψ) ∉ w.val}` is derivable from the deductive closure of
`Γ := {ψ | □ψ ∈ w.val} ∪ {φ}`, given `(◇φ) ∈ w.val`. Dual of `box_witness_pair_underivable`, but
simpler: the seed's extra element is the single formula `φ` (not a family indexed by a second
prime theory), so no `bigAnd`/`h_andI` packing is needed. Consumes only `h_K` (via
`box_context_deriv`), `h_Kdia` (K-diamond bridge), and (through `diaOr_of_diaDisj`) `h_Cd` and
`h_dbot`; **`h_Idb` is not consumed**. -/
theorem diamond_witness_underivable
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_dbot : Axioms ((◇Proposition.bot).imp Proposition.bot))
    {w : CanonicalPrimeWorld Axioms} {φ : Proposition Atom} (h_diaphi : (◇φ) ∈ w.val) :
    Metalogic.DerivExcludes (modalDerivationSystem Axioms)
      {χ | (◇χ) ∉ w.val}
      (modalDeductiveClosure Axioms ({ψ | (□ψ) ∈ w.val} ∪ {φ})) := by
  intro l hlSig hmem
  obtain ⟨L, hLΓ, hd⟩ := hmem
  obtain ⟨d⟩ := hd
  have hLΓ' : ∀ x ∈ L, (□x) ∈ w.val ∨ x = φ := fun x hx => hLΓ x hx
  obtain ⟨Lw, hLw, hsub⟩ := extract_split_dia w φ L hLΓ'
  have d' : DerivationTree Axioms (φ :: Lw) (Metalogic.bigOr l) := .weakening L _ _ d hsub
  have d_disch : DerivationTree Axioms Lw (φ.imp (Metalogic.bigOr l)) :=
    deductionTheorem h_implyK h_implyS Lw φ (Metalogic.bigOr l) d'
  have d_box : DerivationTree Axioms (Lw.map Proposition.box)
      (Proposition.box (φ.imp (Metalogic.bigOr l))) :=
    box_context_deriv h_implyK h_implyS h_K Lw (φ.imp (Metalogic.bigOr l)) d_disch
  have hM : Proposition.box (φ.imp (Metalogic.bigOr l)) ∈ w.val :=
    w.2.1.2 (Lw.map Proposition.box) _
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact hLw y hy)
      ⟨d_box⟩
  have hbridge : DerivationTree Axioms [Proposition.box (φ.imp (Metalogic.bigOr l))]
      ((◇φ).imp (◇ (Metalogic.bigOr l))) :=
    .modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (h_Kdia φ (Metalogic.bigOr l))) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
  have hImp : (◇φ).imp (◇ (Metalogic.bigOr l)) ∈ w.val :=
    w.2.1.2 [Proposition.box (φ.imp (Metalogic.bigOr l))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hM
        · nomatch hx')
      ⟨hbridge⟩
  have hDiaBigOr : (◇ (Metalogic.bigOr l)) ∈ w.val :=
    w.2.1.2 [(◇φ).imp (◇ (Metalogic.bigOr l)), (◇φ)] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hImp
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · exact h_diaphi
          · nomatch hx'')
      ⟨.modus_ponens _ _ _ (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
        (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
  have hDistrib := diaOr_of_diaDisj h_implyK h_implyS h_orI1 h_orI2 h_orE h_Cd h_dbot l
  have hBigOrDia : Metalogic.bigOr (l.map Proposition.diamond) ∈ w.val :=
    w.2.1.2 [(◇ (Metalogic.bigOr l))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hDiaBigOr
        · nomatch hx')
      ⟨.modus_ponens _ _ _ (.weakening [] _ _ hDistrib (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  obtain ⟨B, hBmem, hBu⟩ := bigOr_mem_disjunct w (l.map Proposition.diamond) hBigOrDia
  obtain ⟨B', hB'mem, rfl⟩ := List.mem_map.mp hBmem
  exact (hlSig B' hB'mem) hBu

/-- **Diamond Witness**: from `(◇φ) ∈ w.val`, produces a single prime world `v` with
`canonicalR w v` and `φ ∈ v.val`. No extension of `w` is needed (unlike the box witness), since
`BForces_diamond` is a bare existential over successors of `w` itself.

See [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
Ch. 3; ianshil/CK `general_th_completeness.v`, diamond case. -/
theorem canonical_diamond_witness
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_dbot : Axioms ((◇Proposition.bot).imp Proposition.bot))
    {w : CanonicalPrimeWorld Axioms} {φ : Proposition Atom} (h_diaphi : (◇φ) ∈ w.val) :
    ∃ v : CanonicalPrimeWorld Axioms, canonicalR w v ∧ φ ∈ v.val := by
  have hdwu := diamond_witness_underivable h_implyK h_implyS h_orI1 h_orI2 h_orE
    h_K h_Kdia h_Cd h_dbot (w := w) h_diaphi
  have h_cons_raw : ModalSetConsistent Axioms ({ψ | (□ψ) ∈ w.val} ∪ {φ}) := by
    intro L hL hd
    have hbot_not_mem := hdwu [] (fun _ h => nomatch h)
    rw [bigOr_nil_eq_bot] at hbot_not_mem
    exact hbot_not_mem ⟨L, hL, hd⟩
  have h_adm_raw : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
      (modalDeductiveClosure Axioms ({ψ | (□ψ) ∈ w.val} ∪ {φ})) :=
    modalDeductiveClosure_is_admissible h_implyK h_implyS h_cons_raw
  obtain ⟨Tval, hclosure_sub_T, hprimeT, hexclT⟩ :=
    modal_set_exclusion h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE h_adm_raw hdwu
  let v : CanonicalPrimeWorld Axioms := ⟨Tval, hprimeT⟩
  have hphi_v : φ ∈ v.val :=
    hclosure_sub_T (modal_subset_deductive_closure Axioms _ (Set.mem_union_right _ rfl))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ v.val := by
    intro ψ hψ
    exact hclosure_sub_T (modal_subset_deductive_closure Axioms _ (Set.mem_union_left _ hψ))
  have hdia_clause : ∀ ψ, ψ ∈ v.val → (◇ψ) ∈ w.val := by
    intro ψ hψ_mem
    by_contra hψ_notdia
    have hsig : ∀ x ∈ [ψ], x ∈ {χ | (◇χ) ∉ w.val} := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hψ_notdia
      · nomatch hx'
    have hOrI1_deriv : DerivationTree Axioms [ψ] (Metalogic.bigOr [ψ]) :=
      .modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (h_orI1 ψ (Metalogic.bigOr ([] : List (Proposition Atom)))))
          (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
    have hbigOr_mem : Metalogic.bigOr [ψ] ∈ v.val :=
      v.2.1.2 [ψ] _
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hψ_mem
          · nomatch hx')
        ⟨hOrI1_deriv⟩
    exact hexclT [ψ] hsig hbigOr_mem
  exact ⟨v, ⟨hbox_clause, hdia_clause⟩, hphi_v⟩

end CanonicalDiamondWitness

/-! ## Frame Confluence Conditions

This section proves `canonical_f1` (up-confluence, matching `BFrame.f1`) and `canonical_f2`
(down-confluence, matching `BFrame.f2`), completing the birelational frame data for the
canonical model. Confirmed against `Cslib/Logics/Modal/Semantics/Birelational.lean`:

- `BFrame.f1 : ∀ {w w' v}, w ≤ w' → r w v → ∃ v', r w' v' ∧ v ≤ v'` (up-confluence);
- `BFrame.f2 : ∀ {w v v'}, r w v → v ≤ v' → ∃ w', w ≤ w' ∧ r w' v'` (down-confluence).

**`canonical_f2` (down-confluence)** transports the box witness above along the inclusion
`v ≤ v'`: `canonicalR w v`'s box clause gives `{ψ|□ψ∈w.val}⊆v.val⊆v'.val`, exactly the `h_wu`
precondition `box_witness_pair_underivable` needs (with `u := v'`), so `w'` is built by the same
seeded prime extension as `canonical_box_witness`'s Step 2, with `u` already given instead of
freshly constructed. Threads `h_K`, `h_Kdia`, `h_Idb` via `box_witness_pair_underivable`.

**`canonical_f1` (up-confluence)** is the dual construction, generalizing the diamond witness
above from a singleton seed `{φ}` to the full prime theory `v.val` as seed: `v'` is the prime
extension of `Γ := v.val ∪ {ψ|□ψ∈w'.val}` excluding `Σ := {χ|◇χ∉w'.val}`
(`canonical_f1_underivable`). The key bridging step packs the finitely many `v.val`-drawn
hypotheses into a single conjunction (`bigAnd`, `unpack_conj_partial`, reused from the box
witness consistency sub-lemma above) so that `canonicalR w v`'s diamond clause applies to the
SINGLE formula `bigAnd Lv` (via `bigAnd_mem_u`), avoiding the invalid "conjunction of diamonds
implies diamond of conjunction" direction. Threads `h_K` (via `box_context_deriv`), `h_Kdia`,
`h_Cd`, `h_dbot` (via `diaOr_of_diaDisj`, reused from the diamond witness above).

Reference: [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*]
[Simpson1994], Ch. 3, F1/F2 confluence; ianshil/CK `CF_strong_Cd_weak_Idb`/`CF_CdIdb`. -/

section CanonicalFrameConditions

variable {Axioms : Proposition Atom → Prop}

/-- Partitions a derivation context `L` into two sublists according to a pointwise disjunction of
predicates `P`/`Q`: every element of `L` lies in `Lp ++ Lq` with `Lp`-elements satisfying `P` and
`Lq`-elements satisfying `Q`. Generic 2-way analogue of `extract_split`/`extract_split_dia`, used
by `canonical_f1_underivable` to split the up-confluence seed `v.val ∪ {ψ|□ψ∈w'.val}`. -/
private theorem extract_split_union {P Q : Proposition Atom → Prop} :
    ∀ (L : List (Proposition Atom)), (∀ x ∈ L, P x ∨ Q x) →
      ∃ Lp Lq : List (Proposition Atom),
        (∀ y ∈ Lp, P y) ∧ (∀ y ∈ Lq, Q y) ∧ (∀ x ∈ L, x ∈ Lp ++ Lq)
  | [], _ => by
      refine ⟨[], [], ?_, ?_, ?_⟩ <;> exact fun _ h => nomatch h
  | x :: xs, hL => by
      obtain ⟨Lp', Lq', hLp', hLq', hsub'⟩ :=
        extract_split_union xs (fun y hy => hL y (List.mem_cons.mpr (Or.inr hy)))
      rcases hL x (List.mem_cons.mpr (Or.inl rfl)) with hxP | hxQ
      · refine ⟨x :: Lp', Lq', ?_, hLq', ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hxP
          · exact hLp' y hy'
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))
          · rcases List.mem_append.mp (hsub' z hz') with h1 | h2
            · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h1)))
            · exact List.mem_append.mpr (Or.inr h2)
      · refine ⟨Lp', x :: Lq', hLp', ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hxQ
          · exact hLq' y hy'
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
          · rcases List.mem_append.mp (hsub' z hz') with h1 | h2
            · exact List.mem_append.mpr (Or.inl h1)
            · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h2)))

/-- **Up-confluence underivability**: no finite disjunction of `Σ := {χ|◇χ∉w'.val}` is
derivable from `Γ := v.val ∪ {ψ|□ψ∈w'.val}`, given `w ≤ w'` and `canonicalR w v`'s diamond clause.
Generalizes `diamond_witness_underivable` from a singleton seed `{φ}` to the full prime theory
`v.val`, packing the finitely many `v.val`-hypotheses into `bigAnd Lv` (`unpack_conj_partial`) so
`canonicalR w v`'s diamond clause (`hdia_wv`) applies to this single formula. -/
private theorem canonical_f1_underivable
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_dbot : Axioms ((◇Proposition.bot).imp Proposition.bot))
    {w w' v : CanonicalPrimeWorld Axioms} (hww' : w ≤ w')
    (hdia_wv : ∀ ψ, ψ ∈ v.val → (◇ψ) ∈ w.val) :
    Metalogic.DerivExcludes (modalDerivationSystem Axioms)
      {χ | (◇χ) ∉ w'.val}
      (modalDeductiveClosure Axioms (v.val ∪ {ψ | (□ψ) ∈ w'.val})) := by
  intro l hlSig hmem
  obtain ⟨L, hLΓ, hd⟩ := hmem
  obtain ⟨d⟩ := hd
  have hLΓ' : ∀ x ∈ L, x ∈ v.val ∨ (□x) ∈ w'.val := fun x hx => hLΓ x hx
  obtain ⟨Lv, Lbox, hLv, hLbox, hsub⟩ := extract_split_union L hLΓ'
  have d' : DerivationTree Axioms (Lv ++ Lbox) (Metalogic.bigOr l) := .weakening L _ _ d hsub
  have d_unpack : DerivationTree Axioms (bigAnd Lv :: Lbox) (Metalogic.bigOr l) :=
    unpack_conj_partial h_implyK h_implyS h_andE1 h_andE2 Lv Lbox _ d'
  have d_disch : DerivationTree Axioms Lbox ((bigAnd Lv).imp (Metalogic.bigOr l)) :=
    deductionTheorem h_implyK h_implyS Lbox (bigAnd Lv) (Metalogic.bigOr l) d_unpack
  have d_box : DerivationTree Axioms (Lbox.map Proposition.box)
      (Proposition.box ((bigAnd Lv).imp (Metalogic.bigOr l))) :=
    box_context_deriv h_implyK h_implyS h_K Lbox _ d_disch
  have hM : Proposition.box ((bigAnd Lv).imp (Metalogic.bigOr l)) ∈ w'.val :=
    w'.2.1.2 (Lbox.map Proposition.box) _
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact hLbox y hy)
      ⟨d_box⟩
  have hbridge : DerivationTree Axioms [Proposition.box ((bigAnd Lv).imp (Metalogic.bigOr l))]
      ((◇ (bigAnd Lv)).imp (◇ (Metalogic.bigOr l))) :=
    .modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (h_Kdia (bigAnd Lv) (Metalogic.bigOr l))) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
  have hImp : (◇ (bigAnd Lv)).imp (◇ (Metalogic.bigOr l)) ∈ w'.val :=
    w'.2.1.2 [Proposition.box ((bigAnd Lv).imp (Metalogic.bigOr l))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hM
        · nomatch hx')
      ⟨hbridge⟩
  have hBigAndV : bigAnd Lv ∈ v.val := bigAnd_mem_u h_efq h_andI v Lv hLv
  have hDiaBigAndV_w : (◇ (bigAnd Lv)) ∈ w.val := hdia_wv (bigAnd Lv) hBigAndV
  have hDiaBigAndV_w' : (◇ (bigAnd Lv)) ∈ w'.val := hww' hDiaBigAndV_w
  have hDiaBigOr : (◇ (Metalogic.bigOr l)) ∈ w'.val :=
    w'.2.1.2 [(◇ (bigAnd Lv)).imp (◇ (Metalogic.bigOr l)), (◇ (bigAnd Lv))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hImp
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · exact hDiaBigAndV_w'
          · nomatch hx'')
      ⟨.modus_ponens _ _ _ (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
        (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
  have hDistrib := diaOr_of_diaDisj h_implyK h_implyS h_orI1 h_orI2 h_orE h_Cd h_dbot l
  have hBigOrDia : Metalogic.bigOr (l.map Proposition.diamond) ∈ w'.val :=
    w'.2.1.2 [(◇ (Metalogic.bigOr l))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hDiaBigOr
        · nomatch hx')
      ⟨.modus_ponens _ _ _ (.weakening [] _ _ hDistrib (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  obtain ⟨B, hBmem, hBu⟩ := bigOr_mem_disjunct w' (l.map Proposition.diamond) hBigOrDia
  obtain ⟨B', hB'mem, rfl⟩ := List.mem_map.mp hBmem
  exact (hlSig B' hB'mem) hBu

/-- **`canonical_f1`**: up-confluence, matching `BFrame.f1` exactly. From `w ≤ w'` and
`canonicalR w v`, produces `v' ≥ v` with `canonicalR w' v'`. See the module docstring above for
the construction (`canonical_f1_underivable` + `modal_set_exclusion`). -/
theorem canonical_f1
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_dbot : Axioms ((◇Proposition.bot).imp Proposition.bot))
    {w w' v : CanonicalPrimeWorld Axioms} (hww' : w ≤ w') (hwv : canonicalR w v) :
    ∃ v' : CanonicalPrimeWorld Axioms, canonicalR w' v' ∧ v ≤ v' := by
  obtain ⟨_hbox_wv, hdia_wv⟩ := hwv
  have hu := canonical_f1_underivable h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
    h_andI h_andE1 h_andE2 h_K h_Kdia h_Cd h_dbot (w := w) (w' := w') (v := v) hww' hdia_wv
  have h_cons_raw : ModalSetConsistent Axioms (v.val ∪ {ψ | (□ψ) ∈ w'.val}) := by
    intro L hL hd
    have hbot_not_mem := hu [] (fun _ h => nomatch h)
    rw [bigOr_nil_eq_bot] at hbot_not_mem
    exact hbot_not_mem ⟨L, hL, hd⟩
  have h_adm_raw : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
      (modalDeductiveClosure Axioms (v.val ∪ {ψ | (□ψ) ∈ w'.val})) :=
    modalDeductiveClosure_is_admissible h_implyK h_implyS h_cons_raw
  obtain ⟨Tval, hclosure_sub_T, hprimeT, hexclT⟩ :=
    modal_set_exclusion h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE h_adm_raw hu
  let v' : CanonicalPrimeWorld Axioms := ⟨Tval, hprimeT⟩
  have hv_le_v' : v ≤ v' := fun x hx =>
    hclosure_sub_T (modal_subset_deductive_closure Axioms _ (Set.mem_union_left _ hx))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w'.val → ψ ∈ v'.val := fun ψ hψ =>
    hclosure_sub_T (modal_subset_deductive_closure Axioms _ (Set.mem_union_right _ hψ))
  have hdia_clause : ∀ ψ, ψ ∈ v'.val → (◇ψ) ∈ w'.val := by
    intro ψ hψ_mem
    by_contra hψ_notdia
    have hsig : ∀ x ∈ [ψ], x ∈ {χ | (◇χ) ∉ w'.val} := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hψ_notdia
      · nomatch hx'
    have hOrI1_deriv : DerivationTree Axioms [ψ] (Metalogic.bigOr [ψ]) :=
      .modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (h_orI1 ψ (Metalogic.bigOr ([] : List (Proposition Atom)))))
          (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
    have hbigOr_mem : Metalogic.bigOr [ψ] ∈ v'.val :=
      v'.2.1.2 [ψ] _
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hψ_mem
          · nomatch hx')
        ⟨hOrI1_deriv⟩
    exact hexclT [ψ] hsig hbigOr_mem
  exact ⟨v', ⟨hbox_clause, hdia_clause⟩, hv_le_v'⟩

/-- **`canonical_f2`**: down-confluence, matching `BFrame.f2` exactly. From
`canonicalR w v` and `v ≤ v'`, produces `w' ≥ w` with `canonicalR w' v'`. Transports the box
witness's Step 2 construction (`canonical_box_witness`) along the inclusion `v ≤ v'`: since
`canonicalR w v`'s box clause gives `{ψ|□ψ∈w.val}⊆v.val⊆v'.val`, `v'` already satisfies the
`h_wu` precondition `box_witness_pair_underivable` needs (no fresh `u` construction required, `u`
is `v'`, already given). -/
theorem canonical_f2
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w v v' : CanonicalPrimeWorld Axioms} (hwv : canonicalR w v) (hvv' : v ≤ v') :
    ∃ w' : CanonicalPrimeWorld Axioms, w ≤ w' ∧ canonicalR w' v' := by
  obtain ⟨hbox_wv, _hdia_wv⟩ := hwv
  have h_wu : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ v'.val := fun ψ hψ => hvv' (hbox_wv ψ hψ)
  have hbwu := box_witness_pair_underivable h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
    h_andI h_andE1 h_andE2 h_K h_Kdia h_Idb (w := w) (u := v') h_wu
  have h_cons_raw : ModalSetConsistent Axioms
      (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ v'.val}) := by
    intro L hL hd
    have hbot_not_mem := hbwu [] (fun _ h => nomatch h)
    rw [bigOr_nil_eq_bot] at hbot_not_mem
    exact hbot_not_mem ⟨L, hL, hd⟩
  have h_adm_raw : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
      (modalDeductiveClosure Axioms (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ v'.val})) :=
    modalDeductiveClosure_is_admissible h_implyK h_implyS h_cons_raw
  obtain ⟨Tval, hclosure_sub_T, hprimeT, hexclT⟩ :=
    modal_set_exclusion h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE h_adm_raw hbwu
  let w' : CanonicalPrimeWorld Axioms := ⟨Tval, hprimeT⟩
  have hw_le_w' : w ≤ w' := fun x hx =>
    hclosure_sub_T (modal_subset_deductive_closure Axioms _ (Set.mem_union_left _ hx))
  have hdia_clause : ∀ ψ, ψ ∈ v'.val → (◇ψ) ∈ w'.val := fun ψ hψ =>
    hclosure_sub_T (modal_subset_deductive_closure Axioms _
      (Set.mem_union_right _ ⟨ψ, rfl, hψ⟩))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w'.val → ψ ∈ v'.val := by
    intro ψ hψ_mem
    by_contra hψ_notV'
    have hsig : ∀ x ∈ [(□ψ)], x ∈ {χ | ∃ B, χ = (□B) ∧ B ∉ v'.val} := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨ψ, rfl, hψ_notV'⟩
      · nomatch hx'
    have hOrI1_deriv : DerivationTree Axioms [(□ψ)] (Metalogic.bigOr [(□ψ)]) :=
      .modus_ponens _ _ _
        (.weakening [] _ _
          (.ax [] _ (h_orI1 (□ψ) (Metalogic.bigOr ([] : List (Proposition Atom)))))
          (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
    have hbigOr_mem : Metalogic.bigOr [(□ψ)] ∈ w'.val :=
      w'.2.1.2 [(□ψ)] _
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hψ_mem
          · nomatch hx')
        ⟨hOrI1_deriv⟩
    exact hexclT [(□ψ)] hsig hbigOr_mem
  exact ⟨w', hw_le_w', ⟨hbox_clause, hdia_clause⟩⟩

end CanonicalFrameConditions

end Cslib.Logic.Modal
