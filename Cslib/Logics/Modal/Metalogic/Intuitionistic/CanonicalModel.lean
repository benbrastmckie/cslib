/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory
public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.Semantics.Birelational

/-! # Canonical Model for Intuitionistic Modal Logic

This module lays down the birelational canonical-frame data for intuitionistic modal logic:
worlds are prime modal theories (`PrimeTheory.lean`), `≤` is set inclusion, `canonicalVal` is
the atom-membership valuation, and `canonicalR` is the two-clause canonical accessibility
relation required because `◇` is primitive (not `□`-definable) in this framework's
`Modal.Proposition` datatype.

This file is Phase 2a of a multi-phase construction (task 480 plan v2): it contains
**definitions only**, no witness proofs. `canonical_box_witness` (Phase 2b),
`canonical_diamond_witness` (Phase 2c), and the frame conditions `canonical_f1`/`canonical_f2`
(Phase 2d) are added by subsequent phases in this same file.

## Confirmed `Birelational.lean` API (read during Phase 2a, task 480)

- `BFrame World` (requires `[Preorder World]`) bundles `r : World → World → Prop`,
  `f1 : ∀ {w w' v}, w ≤ w' → r w v → ∃ v', r w' v' ∧ v ≤ v'` (up-confluence), and
  `f2 : ∀ {w v v'}, r w v → v ≤ v' → ∃ w', w ≤ w' ∧ r w' v'` (down-confluence).
- `BModel World Atom extends BFrame World` adds `v : World → Atom → Prop`,
  `botForces : World → Prop`, `v_upward_closed`, `bf_upward_closed`.
- `BForces r v botForces w φ` is the forcing relation; `@[simp]` unfolds exist for every
  constructor, in particular `BForces_box` (`∀ w' ≥ w, ∀ u, r w' u → BForces … u φ`) and
  `BForces_diamond` (`∃ u, r w u ∧ BForces … u φ`).
- `IValid`/`MValid` universally quantify over `World`/`r`/`f1`/`f2`/valuation (and, for
  `MValid`, `botForces`), matching the report's §7 parametricity requirement.

These names and shapes are used verbatim by `canonicalR` below and by the later phases
(`canonical_f1`/`canonical_f2` in 2d must match `BFrame.f1`/`BFrame.f2` exactly).

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

variable {Atom : Type*}

/-! ## Canonical Worlds -/

/-- A canonical world for intuitionistic modal logic is a prime modal theory
(`ModalPrimeTheory Axioms`), parametric over the axiom predicate `Axioms`. Worlds are prime
(rather than maximal-consistent, as in the classical `MCS.lean` canonical model) so that the
disjunction property is available for the `or` case of the truth lemma (`TruthLemma.lean`,
Phase 3). -/
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
diamond clause since `◇` is primitive and not `□`-definable (Wijesekera 1990; report §6.4):

- box clause (`□φ ∈ w → φ ∈ v`): every boxed formula true at `w` is true at `v`
  ([Simpson1994], clause 3.2's accessibility side);
- diamond clause (`φ ∈ v → ◇φ ∈ w`): every formula true at `v` is possible at `w`
  ([Simpson1994], clause 3.5's accessibility side).

The witness lemmas establishing that this relation actually exists between suitable worlds
(`canonical_box_witness`, `canonical_diamond_witness`) are proved in Phases 2b/2c. -/
def canonicalR {Axioms : Proposition Atom → Prop} (w v : CanonicalPrimeWorld Axioms) : Prop :=
  (∀ φ, (□φ) ∈ w.val → φ ∈ v.val) ∧ (∀ φ, φ ∈ v.val → (◇φ) ∈ w.val)

/-! ## Box Witness Consistency Sub-Lemma (Phase 2b-sublemma)

This section proves `box_witness_pair_underivable`, the modal consistency sub-lemma
establishing the `DerivExcludes` precondition needed by Phase 2b's seeded prime-extension
`w'`: no finite disjunction of `Σ := {□B | B ∉ u.val}` is derivable from
`Γ := w.val ∪ {◇A | A ∈ u.val}`, given `{ψ | □ψ ∈ w.val} ⊆ u.val`.

Transliterated from ianshil/CK `general_th_completeness.v`, box case (~L211-249; the `Idb`
selector at ~L231, confirmed verbatim by report 03). The argument needs three modal-axiom
hypotheses beyond the intuitionistic base -- `h_K` (Kb), `h_Kdia` (Kd), and `h_Idb`
(Fischer-Servi box bridge, the load-bearing addition resolving the v3 STOP contingency) --
plus `h_andI`/`h_andE1`/`h_andE2` to combine the finitely many diamond hypotheses a
derivation may use into a single `◇(bigAnd …)` antecedent before `h_Idb` applies. The
conjunction hypotheses are a standard part of the intuitionistic `and`/`or` base (already
axiomatized elsewhere in this framework, e.g. `MCS.lean`'s `mcs_and_mem_iff`) that report 03's
per-lemma table did not separately enumerate; they introduce no new axiom, only additional
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
      · rw [hxeq, heq, List.map_cons]
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

/-- Empty-context implication composition: from `⊢ A → B` and `⊢ B → C`, derive `⊢ A → C`. -/
private noncomputable def imp_trans0
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {A B C : Proposition Atom}
    (d1 : DerivationTree Axioms [] (A.imp B)) (d2 : DerivationTree Axioms [] (B.imp C)) :
    DerivationTree Axioms [] (A.imp C) := by
  have hA : DerivationTree Axioms [A] A := .assumption [A] A (List.mem_cons.mpr (Or.inl rfl))
  have hB : DerivationTree Axioms [A] B :=
    .modus_ponens [A] A B (.weakening [] [A] _ d1 (fun _ h => nomatch h)) hA
  have hC : DerivationTree Axioms [A] C :=
    .modus_ponens [A] B C (.weakening [] [A] _ d2 (fun _ h => nomatch h)) hB
  exact deductionTheorem h_implyK h_implyS [] A C hC

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

/-- **Box Witness Consistency Sub-Lemma** (Phase 2b-sublemma, task 480): no finite disjunction
of `Σ := {□B | B ∉ u.val}` is derivable from `Γ := w.val ∪ {◇A | A ∈ u.val}`, given
`{ψ | □ψ ∈ w.val} ⊆ u.val`. Discharges the `DerivExcludes` precondition that Phase 2b's seeded
prime extension `w'` needs.

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

end Cslib.Logic.Modal
