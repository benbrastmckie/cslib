/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Semantics.Birelational
public import Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum

/-! # Frame-Condition-Parametrized, Axioms-Generic Extensions of the Minimal Canonical Model

This module is the shared scaffold for the minimal-base modal extensions `MT`/`MS4`/`MS5`
of `MK`, mirroring `IK`'s `IT`/`IS4`/`IS5` extension. It generalizes the birelational
quasi-prime canonical-model framework (`MValid`, `mk_completeness`,
`MinCanonicalModel.lean`/`MinTruthLemma.lean`/`MinCompleteness.lean`, all hard-coded to
`MKModalAxiom`) to validity/completeness over an **arbitrary** axiom set `Axioms` that extends
`MK`'s 12 core schemata (`implyK`/`implyS`/`andI`/`andE1`/`andE2`/`orI1`/`orI2`/`orE`/`k`/`kdia`/
`cd`/`idb`), restricted to a frame-condition class `FC` on the modal relation.

**Why this file is larger than a typical `Extension.lean`.** `IK`'s own `Extension.lean` is a
~150-line wrapper because `IK`'s *base* canonical-model files (`Intuitionistic/CanonicalModel.lean`,
`PrimeTheory.lean`, `TruthLemma.lean`) were **already** written generically over an abstract
`Axioms : Proposition Atom → Prop`, each constructor-witness (`h_implyK`, `h_implyS`, ...,
`h_dbot`) threaded explicitly through every canonical-model theorem (e.g. `canonical_f1`,
`canonical_box_witness`, both ~14-hypothesis theorems in `CanonicalModel.lean`). `MK`'s files,
in contrast, were written **specifically** for `MKModalAxiom` (every axiom-instance is
`MKModalAxiom.foo args`, not a threaded hypothesis), because at the time only `MK` itself needed
them. This module performs the same genericization `IK`'s base already had: every place `MK`'s
files invoke `MKModalAxiom.foo args` becomes a threaded hypothesis `h_foo args`
(`Axioms (...)` instead of `MKModalAxiom (...)`), exactly mirroring `IK`'s
`canonical_f1`/`canonical_box_witness` convention. The efq-free "nonempty Lindenbaum-pair"
combinators (`bigOr1`/`bigAnd1` and friends) are otherwise transcribed verbatim from
`MinCanonicalModel.lean` (same proof scripts, only the axiom-instance sites are threaded).

All declarations here live under the `MinExt` namespace (nested inside `Cslib.Logic.Modal`) to
avoid colliding with `MK`'s `MKModalAxiom`-specific declarations of the same short name
(`MinCanonicalPrimeWorld`, `minCanonicalR`, `min_canonical_f1`, ... already public in
`Cslib.Logic.Modal`). Four names are unqualified in `Cslib.Logic.Modal` itself (`MValidFC`,
`mkvalidFC_completeness`, `min_axiom_mem`, `min_imp_property`); they are defined outside
`MinExt`, referencing `MinExt.*` internally.

## Main Definitions

- `MValidFC`: a copy of `MValid` (`Birelational.lean:205`) with one extra hypothesis `FC r`
  threaded alongside `f1`/`f2`, **retaining** the `botForces`/`bf_uc` binders (unlike `IValidFC`,
  which hardcodes `fun _ => False`). `MValid` itself is untouched; `MValidFC`/`MValid` coexist.
- `MinExt.MinCanonicalPrimeWorld Axioms`: quasi-prime `Axioms`-theories, generic canonical worlds.
- `MinExt.minCanonicalR`, `MinExt.min_canonical_f1`/`f2`, `MinExt.min_canonical_truth_lemma`,
  `MinExt.min_head_realization`: the `Axioms`-generic canonical model, box/diamond witnesses,
  F1/F2 confluence, and truth lemma (efq-free Lindenbaum-pair construction, generalized).
- `min_axiom_mem`/`min_imp_property`: axiom-instance and MP-closure membership helpers for any
  `MinExt.MinCanonicalPrimeWorld Axioms` (fully `Axioms`-generic, no MK-core hypotheses needed --
  deductive closure does not care which axiom system it closes under).
- `mkvalidFC_completeness`: `Axioms`-generic, single-branch (no `efq`, no consistency case split)
  completeness over `FC`-frames, generalizing `mk_completeness` (`MinCompleteness.lean:55`).

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational frame classes for `T`/`S4`/`S5`, `MValid`).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Metalogic

universe u v

variable {Atom : Type u}

/-! ## Frame-Condition-Parametrized Validity -/

/-- A formula is `FC`-frame-valid (`MValidFC`) if it is forced at every world in every
birelational model whose modal relation `r` additionally satisfies the frame condition `FC`
(e.g. reflexivity/transitivity/symmetry), on top of the usual up/down-confluence conditions
`f1`/`f2` and an **arbitrary** upward-closed `botForces` predicate (the minimal-base convention,
as in `MValid`, `Birelational.lean:205`). `MValid` itself is the special case
`FC := fun _ => True`; it is left untouched, and `MValidFC`/`MValid` coexist. -/
def MValidFC (FC : {World : Type v} → (World → World → Prop) → Prop)
    (φ : Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (r : World → World → Prop) (_fc : FC r)
    (_f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (_f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop) (botForces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → botForces w → botForces w') →
    ∀ w, BForces r val botForces w φ

/-- **`MValid` is the `FC := fun _ => True` instance of `MValidFC`**: the two notions coincide
when the frame condition is vacuous. Justifies treating `MValidFC` as a strict generalization of
`MValid` (`Birelational.lean:205`) rather than a separate, unrelated definition. -/
theorem mvalid_iff_mvalidFC_true {φ : Proposition Atom} :
    MValid.{u, v} φ ↔ MValidFC.{u, v} (fun {_} _ => True) φ := by
  constructor
  · intro h World _ r _fc f1 f2 val botForces v_uc bf_uc
    exact h World r f1 f2 val botForces v_uc bf_uc
  · intro h World _ r f1 f2 val botForces v_uc bf_uc
    exact h World r trivial f1 f2 val botForces v_uc bf_uc

/-! ## `MinExt`: the `Axioms`-generic quasi-prime canonical model -/

namespace MinExt

variable {Axioms : Proposition Atom → Prop}
  (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
  (h_implyS : ∀ (φ ψ χ : Proposition Atom),
    Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
  (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
  (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
  (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
  (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
  (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
  (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
  (h_k : ∀ (φ ψ : Proposition Atom),
    Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
  (h_kdia : ∀ (φ ψ : Proposition Atom),
    Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
  (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
  (h_idb : ∀ (φ ψ : Proposition Atom),
    Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))

/-! ### Canonical Worlds -/

/-- A canonical world for `Axioms` is a quasi-prime `Axioms`-theory: deductively closed with the
disjunction property, **not** required consistent (fallible worlds admitted). Generic analogue of
`MinCanonicalPrimeWorld` (`MinPrimeTheory.lean:58`). -/
def MinCanonicalPrimeWorld (Axioms : Proposition Atom → Prop) :=
  { S : Set (Proposition Atom) // QuasiPrime (Axioms) S }

/-- The canonical preorder: set inclusion of the underlying quasi-prime theories. -/
instance : Preorder (MinCanonicalPrimeWorld Axioms) where
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

theorem MinCanonicalPrimeWorld.le_iff {w w' : MinCanonicalPrimeWorld Axioms} :
    w ≤ w' ↔ w.val ⊆ w'.val := Iff.rfl

/-! ### Canonical Valuation and `botForces` -/

/-- The canonical valuation: atom `p` is forced at `w` iff `atom p ∈ w.val`. -/
def minCanonicalVal (w : MinCanonicalPrimeWorld Axioms) (p : Atom) : Prop :=
  Proposition.atom p ∈ w.val

theorem minCanonicalVal_upward_closed
    {w w' : MinCanonicalPrimeWorld Axioms} (p : Atom) (hw : w ≤ w')
    (hv : minCanonicalVal w p) : minCanonicalVal w' p := hw hv

/-- `⊥` is forced at `w` iff `⊥ ∈ w.val`, a genuine (non-trivial) predicate. -/
def minBotForces (w : MinCanonicalPrimeWorld Axioms) : Prop :=
  (Proposition.bot : Proposition Atom) ∈ w.val

theorem minBotForces_upward_closed
    {w w' : MinCanonicalPrimeWorld Axioms} (hw : w ≤ w') (hbf : minBotForces w) :
    minBotForces w' := hw hbf

/-! ### Head Realization -/

/-- Any `Axioms`-underivable formula is omitted by some quasi-prime `Axioms`-theory. Thin wrapper
over `quasi_head_realization` (`Constructive/SegmentLindenbaum.lean:242`, already
`Axioms`-generic). -/
theorem min_head_realization
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    {φ : Proposition Atom}
    (h_nd : ¬ Derivable Axioms φ) :
    ∃ T, QuasiPrime (Axioms) T ∧ φ ∉ T :=
  quasi_head_realization h_implyK h_implyS h_orE h_nd

/-! ### Canonical Accessibility Relation -/

/-- The canonical accessibility relation, generic analogue of `minCanonicalR`
(`MinCanonicalModel.lean:75`). -/
def minCanonicalR (w v : MinCanonicalPrimeWorld Axioms) : Prop :=
  (∀ φ, (□φ) ∈ w.val → φ ∈ v.val) ∧ (∀ φ, φ ∈ v.val → (◇φ) ∈ w.val)

/-! ### Nonempty Disjunction / Conjunction (efq-free Lindenbaum-pair machinery, generic) -/

section NonemptyCombinators

/-- Nonempty iterated disjunction, terminating at the head. Generic analogue of `bigOr1`
(`MinCanonicalModel.lean:89`). -/
private def bigOr1 : Proposition Atom → List (Proposition Atom) → Proposition Atom
  | x, [] => x
  | x, y :: ys => x.or (bigOr1 y ys)

/-- Nonempty iterated conjunction, terminating at the head. Generic analogue of `bigAnd1`. -/
private def bigAnd1 : Proposition Atom → List (Proposition Atom) → Proposition Atom
  | x, [] => x
  | x, y :: ys => x.and (bigAnd1 y ys)

/-- The shared "cut" witness. Generic analogue of `hCutMK`. -/
private theorem hCutMK
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))) :
    ∀ {U : Set (Proposition Atom)} {L : List (Proposition Atom)} {a b : Proposition Atom},
      (∀ x ∈ L, x ∈ insert a U) → (modalDerivationSystem Axioms).Deriv L b →
      ∃ L', (∀ x ∈ L', x ∈ U) ∧ (modalDerivationSystem Axioms).Deriv L' (a.imp b) :=
  fun {U _L a _b} hL hd =>
    modal_deriv_imp_of_union h_implyK h_implyS
      (fun x hx => by
        rcases Set.mem_insert_iff.mp (hL x hx) with rfl | hu
        · exact Set.mem_union_right U (Set.mem_singleton_iff.mpr rfl)
        · exact Set.mem_union_left _ hu)
      hd

/-- `⊢ bigOr1 x xs → bigOr1 x (xs ++ ys)`. Generic analogue of `bigOr1_append_left`. -/
private theorem bigOr1_append_left
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ)) :
    ∀ (x : Proposition Atom) (xs ys : List (Proposition Atom)),
      (modalDerivationSystem Axioms).Deriv [] ((bigOr1 x xs).imp (bigOr1 x (xs ++ ys)))
  | x, [], [] =>
      ⟨deductionTheorem h_implyK h_implyS
        [] x x (.assumption [x] x (List.mem_cons.mpr (Or.inl rfl)))⟩
  | x, [], y :: ys => ⟨.ax [] _ (h_orI1 x (bigOr1 y ys))⟩
  | _x, z :: zs, ys =>
      or_right_mono (modalDerivationSystem Axioms)
        (fun A B => ⟨.ax [] _ (h_orI1 A B)⟩)
        (fun A B => ⟨.ax [] _ (h_orI2 A B)⟩)
        (fun A B χ => ⟨.ax [] _ (h_orE A B χ)⟩)
        (hCutMK h_implyK h_implyS)
        (bigOr1_append_left h_implyK h_implyS h_orI1 h_orI2 h_orE z zs ys)

/-- `⊢ bigOr1 y ys → bigOr1 x (xs ++ (y :: ys))`. Generic analogue of `bigOr1_append_right`. -/
private theorem bigOr1_append_right
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ)) :
    ∀ (x : Proposition Atom) (xs : List (Proposition Atom)) (y : Proposition Atom)
      (ys : List (Proposition Atom)),
      (modalDerivationSystem Axioms).Deriv []
        ((bigOr1 y ys).imp (bigOr1 x (xs ++ (y :: ys))))
  | x, [], y, ys => ⟨.ax [] _ (h_orI2 x (bigOr1 y ys))⟩
  | x, z :: zs, y, ys =>
      empty_imp_trans (modalDerivationSystem Axioms) (hCutMK h_implyK h_implyS)
        (bigOr1_append_right h_implyK h_implyS h_orI1 h_orI2 h_orE z zs y ys)
        ⟨.ax [] _ (h_orI2 x (bigOr1 z (zs ++ (y :: ys))))⟩

/-- Empty-context box monotonicity for a *derived* implication. Generic analogue of
`boxMonoDeriv`. -/
private def boxMonoDeriv
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    {A B : Proposition Atom}
    (d : DerivationTree Axioms [] (A.imp B)) :
    DerivationTree Axioms [] ((Proposition.box A).imp (Proposition.box B)) :=
  .modus_ponens [] _ _ (.ax [] _ (h_k A B)) (.necessitation _ d)

/-- Empty-context diamond monotonicity for a *derived* implication. Generic analogue of
`diaMonoDeriv`. -/
private def diaMonoDeriv
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    {A B : Proposition Atom}
    (d : DerivationTree Axioms [] (A.imp B)) :
    DerivationTree Axioms [] ((◇A).imp (◇B)) :=
  .modus_ponens [] _ _ (.ax [] _ (h_kdia A B)) (.necessitation _ d)

/-- The empty-context identity derivation `⊢ φ → φ`. Generic analogue of `idDeriv`. -/
private noncomputable def idDeriv
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (φ : Proposition Atom) :
    DerivationTree Axioms [] (φ.imp φ) :=
  deductionTheorem h_implyK h_implyS
    [] φ φ (.assumption [φ] φ (List.mem_cons.mpr (Or.inl rfl)))

/-- **Box-of-disjuncts, nonempty**. Generic analogue of `boxOr1_of_boxDisj`. -/
private noncomputable def boxOr1_of_boxDisj
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    (base : Proposition Atom) :
    ∀ (rest : List (Proposition Atom)),
      DerivationTree Axioms []
        ((bigOr1 (Proposition.box base) (rest.map Proposition.box)).imp
          (Proposition.box (bigOr1 base rest)))
  | [] => boxMonoDeriv h_k (idDeriv h_implyK h_implyS base)
  | C :: rest' => by
      have f1 : DerivationTree Axioms []
          ((Proposition.box base).imp (Proposition.box (bigOr1 base (C :: rest')))) :=
        boxMonoDeriv h_k (.ax [] _ (h_orI1 base (bigOr1 C rest')))
      have f2a : DerivationTree Axioms []
          ((Proposition.box (bigOr1 C rest')).imp
            (Proposition.box (bigOr1 base (C :: rest')))) :=
        boxMonoDeriv h_k (.ax [] _ (h_orI2 base (bigOr1 C rest')))
      have ih := boxOr1_of_boxDisj h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE
        h_k h_kdia h_cd h_idb C rest'
      have f2 : DerivationTree Axioms []
          ((bigOr1 (Proposition.box C) (rest'.map Proposition.box)).imp
            (Proposition.box (bigOr1 base (C :: rest')))) :=
        Classical.choice
          (empty_imp_trans (modalDerivationSystem Axioms) (hCutMK h_implyK h_implyS) ⟨ih⟩ ⟨f2a⟩)
      have step1 := DerivationTree.modus_ponens [] _ _
        (DerivationTree.ax [] _
          (h_orE (Proposition.box base)
            (bigOr1 (Proposition.box C) (rest'.map Proposition.box))
            (Proposition.box (bigOr1 base (C :: rest')))))
        f1
      exact DerivationTree.modus_ponens [] _ _ step1 f2

/-- **Diamond-of-disjuncts, nonempty**. Generic analogue of `diaOr1_of_diaDisj`. -/
private noncomputable def diaOr1_of_diaDisj
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    (base : Proposition Atom) :
    ∀ (rest : List (Proposition Atom)),
      DerivationTree Axioms []
        ((◇ (bigOr1 base rest)).imp (bigOr1 (◇base) (rest.map Proposition.diamond)))
  | [] => diaMonoDeriv h_kdia (idDeriv h_implyK h_implyS base)
  | C :: rest' => by
      have hCd : DerivationTree Axioms []
          ((◇ (bigOr1 base (C :: rest'))).imp ((◇base).or (◇ (bigOr1 C rest')))) :=
        .ax [] _ (h_cd base (bigOr1 C rest'))
      have ih := diaOr1_of_diaDisj h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE
        h_k h_kdia h_cd h_idb C rest'
      have branch1 : DerivationTree Axioms []
          ((◇base).imp (bigOr1 (◇base) ((◇C) :: (rest'.map Proposition.diamond)))) :=
        .ax [] _ (h_orI1 (◇base) (bigOr1 (◇C) (rest'.map Proposition.diamond)))
      have branch2 : DerivationTree Axioms []
          ((◇ (bigOr1 C rest')).imp
            (bigOr1 (◇base) ((◇C) :: (rest'.map Proposition.diamond)))) :=
        Classical.choice
          (empty_imp_trans (modalDerivationSystem Axioms) (hCutMK h_implyK h_implyS) ⟨ih⟩
            ⟨.ax [] _ (h_orI2 (◇base) (bigOr1 (◇C) (rest'.map Proposition.diamond)))⟩)
      have step1 := DerivationTree.modus_ponens [] _ _
        (DerivationTree.ax [] _
          (h_orE (◇base) (◇ (bigOr1 C rest'))
            (bigOr1 (◇base) ((◇C) :: (rest'.map Proposition.diamond)))))
        branch1
      have step2 := DerivationTree.modus_ponens [] _ _ step1 branch2
      exact Classical.choice
        (empty_imp_trans (modalDerivationSystem Axioms) (hCutMK h_implyK h_implyS) ⟨hCd⟩ ⟨step2⟩)

/-- Combines a *nonempty* list of hypotheses into a single conjunction hypothesis. Generic
analogue of `unpackConj1`. -/
private noncomputable def unpackConj1
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ)) :
    ∀ (x : Proposition Atom) (xs Lw : List (Proposition Atom)) (ψ : Proposition Atom),
      DerivationTree Axioms ((x :: xs) ++ Lw) ψ →
      DerivationTree Axioms (bigAnd1 x xs :: Lw) ψ
  | _x, [], _Lw, _ψ, d => d
  | x, y :: ys, Lw, ψ, d => by
      have dt : DerivationTree Axioms ((y :: ys) ++ Lw) (x.imp ψ) :=
        deductionTheorem h_implyK h_implyS ((y :: ys) ++ Lw) x ψ d
      have ihres : DerivationTree Axioms (bigAnd1 y ys :: Lw) (x.imp ψ) :=
        unpackConj1 h_implyK h_implyS h_andE1 h_andE2 y ys Lw (x.imp ψ) dt
      have ihres0 : DerivationTree Axioms Lw ((bigAnd1 y ys).imp (x.imp ψ)) :=
        deductionTheorem h_implyK h_implyS Lw (bigAnd1 y ys) (x.imp ψ) ihres
      have hmem : DerivationTree Axioms (bigAnd1 x (y :: ys) :: Lw) (bigAnd1 x (y :: ys)) :=
        .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
      have hx : DerivationTree Axioms (bigAnd1 x (y :: ys) :: Lw) x :=
        .modus_ponens _ (bigAnd1 x (y :: ys)) x
          (.weakening [] _ _ (.ax [] _ (h_andE1 x (bigAnd1 y ys))) (fun _ h => nomatch h))
          hmem
      have hRest : DerivationTree Axioms (bigAnd1 x (y :: ys) :: Lw) (bigAnd1 y ys) :=
        .modus_ponens _ (bigAnd1 x (y :: ys)) (bigAnd1 y ys)
          (.weakening [] _ _ (.ax [] _ (h_andE2 x (bigAnd1 y ys))) (fun _ h => nomatch h))
          hmem
      have hximpψ : DerivationTree Axioms (bigAnd1 x (y :: ys) :: Lw) (x.imp ψ) :=
        .modus_ponens _ (bigAnd1 y ys) (x.imp ψ)
          (.weakening Lw _ _ ihres0 (fun z hz => List.mem_cons.mpr (Or.inr hz)))
          hRest
      exact .modus_ponens _ x ψ hximpψ hx

/-- **Diamond/conjunction bridge, nonempty**. Generic analogue of `diaBigAnd1ToBigAnd1Dia`. -/
private noncomputable def diaBigAnd1ToBigAnd1Dia
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    (x : Proposition Atom) :
    ∀ (xs : List (Proposition Atom)),
      DerivationTree Axioms []
        ((◇ (bigAnd1 x xs)).imp (bigAnd1 (◇x) (xs.map Proposition.diamond)))
  | [] => diaMonoDeriv h_kdia (idDeriv h_implyK h_implyS x)
  | y :: ys => by
      have f1 : DerivationTree Axioms [] ((◇ (bigAnd1 x (y :: ys))).imp (◇x)) :=
        diaMonoDeriv h_kdia (.ax [] _ (h_andE1 x (bigAnd1 y ys)))
      have f2 : DerivationTree Axioms []
          ((◇ (bigAnd1 x (y :: ys))).imp (◇ (bigAnd1 y ys))) :=
        diaMonoDeriv h_kdia (.ax [] _ (h_andE2 x (bigAnd1 y ys)))
      have ih := diaBigAnd1ToBigAnd1Dia h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2
        h_orE h_k h_kdia h_cd h_idb y ys
      have f2' : DerivationTree Axioms []
          ((◇ (bigAnd1 x (y :: ys))).imp (bigAnd1 (◇y) (ys.map Proposition.diamond))) :=
        Classical.choice (empty_imp_trans (modalDerivationSystem Axioms) (hCutMK h_implyK h_implyS)
          ⟨f2⟩ ⟨ih⟩)
      have hXmem :
          DerivationTree Axioms [◇ (bigAnd1 x (y :: ys))] (◇ (bigAnd1 x (y :: ys))) :=
        .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
      have hdiaX : DerivationTree Axioms [◇ (bigAnd1 x (y :: ys))] (◇x) :=
        .modus_ponens _ _ _ (.weakening [] _ _ f1 (fun _ h => nomatch h)) hXmem
      have hrest : DerivationTree Axioms [◇ (bigAnd1 x (y :: ys))]
          (bigAnd1 (◇y) (ys.map Proposition.diamond)) :=
        .modus_ponens _ _ _ (.weakening [] _ _ f2' (fun _ h => nomatch h)) hXmem
      have andI_ax : DerivationTree Axioms [◇ (bigAnd1 x (y :: ys))]
          ((◇x).imp ((bigAnd1 (◇y) (ys.map Proposition.diamond)).imp
            ((◇x).and (bigAnd1 (◇y) (ys.map Proposition.diamond))))) :=
        .weakening [] _ _
          (.ax [] _ (h_andI (◇x) (bigAnd1 (◇y) (ys.map Proposition.diamond))))
          (fun _ h => nomatch h)
      have step1 := DerivationTree.modus_ponens _ _ _ andI_ax hdiaX
      have step2 := DerivationTree.modus_ponens _ _ _ step1 hrest
      exact deductionTheorem h_implyK h_implyS [] (◇ (bigAnd1 x (y :: ys))) _ step2

/-- `bigAnd1 x xs ∈ u.val` whenever `x` and every element of `xs` are in `u.val`. Generic
analogue of `bigAnd1_mem_u`. -/
private theorem bigAnd1_mem_u
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    {u : MinCanonicalPrimeWorld Axioms} (x : Proposition Atom) :
    ∀ (xs : List (Proposition Atom)), x ∈ u.val → (∀ A ∈ xs, A ∈ u.val) →
      bigAnd1 x xs ∈ u.val
  | [], hx, _ => hx
  | y :: ys, hx, hxs => by
      have hy : y ∈ u.val := hxs y (List.mem_cons.mpr (Or.inl rfl))
      have hRest : bigAnd1 y ys ∈ u.val :=
        bigAnd1_mem_u h_andI y ys hy
          (fun B hB => hxs B (List.mem_cons.mpr (Or.inr hB)))
      have h1 : DerivationTree Axioms [x, bigAnd1 y ys] x :=
        .assumption _ x (List.mem_cons.mpr (Or.inl rfl))
      have h2 : DerivationTree Axioms [x, bigAnd1 y ys] (bigAnd1 y ys) :=
        .assumption _ (bigAnd1 y ys) (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      have hax : DerivationTree Axioms [x, bigAnd1 y ys]
          (x.imp ((bigAnd1 y ys).imp (x.and (bigAnd1 y ys)))) :=
        .weakening [] _ _ (.ax [] _ (h_andI x (bigAnd1 y ys))) (fun _ h => nomatch h)
      have hderiv : DerivationTree Axioms [x, bigAnd1 y ys] (x.and (bigAnd1 y ys)) :=
        .modus_ponens _ _ _ (.modus_ponens _ _ _ hax h1) h2
      exact u.property.closed [x, bigAnd1 y ys] _
        (fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact hx
          · rcases List.mem_cons.mp hz' with rfl | hz''
            · exact hRest
            · nomatch hz'')
        ⟨hderiv⟩

end NonemptyCombinators

/-! ### Nonempty Lindenbaum-Pair Exclusion (generic) -/

section NonemptyPairExclusion

/-- `T` derives no *nonempty* finite disjunction of `E`. Generic analogue of `DerivExcludes1`. -/
private def DerivExcludes1 (T E : Set (Proposition Atom)) : Prop :=
  ∀ (x : Proposition Atom) (xs : List (Proposition Atom)),
    x ∈ E → (∀ y ∈ xs, y ∈ E) → bigOr1 x xs ∉ T

/-- The Zorn domain for `quasi_prime_set_exclusion1`. Generic analogue of
`QPExcludingSupersets`. -/
private def QPExcludingSupersets (S E : Set (Proposition Atom)) : Set (Set (Proposition Atom)) :=
  {T | S ⊆ T ∧ Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) T ∧
    DerivExcludes1 T E}

private theorem qp_excluding_base_mem {S E : Set (Proposition Atom)}
    (hS : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) S)
    (h_excl : DerivExcludes1 S E) : S ∈ QPExcludingSupersets (Axioms := Axioms) S E :=
  ⟨Set.Subset.refl S, hS, h_excl⟩

private theorem qp_excluding_chain_union {S E : Set (Proposition Atom)}
    {C : Set (Set (Proposition Atom))}
    (hCsub : C ⊆ QPExcludingSupersets (Axioms := Axioms) S E)
    (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty) :
    (⋃₀ C) ∈ QPExcludingSupersets (Axioms := Axioms) S E := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨T, hT⟩ := hCne
    exact Set.mem_sUnion.mpr ⟨T, hT, (hCsub hT).1 hx⟩
  · exact deductivelyClosed_chain_union (modalDerivationSystem Axioms) hchain hCne
      (fun T hTC => (hCsub hTC).2.1)
  · intro x xs hxE hxsE hmem
    obtain ⟨T, hTC, hTmem⟩ := Set.mem_sUnion.mp hmem
    exact (hCsub hTC).2.2 x xs hxE hxsE hTmem

/-- **Nonempty Lindenbaum-pair exclusion** (efq-free), generic over `Axioms`. Analogue of
`quasi_prime_set_exclusion1`. -/
private theorem quasi_prime_set_exclusion1
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    {S E : Set (Proposition Atom)}
    (hS : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) S)
    (h_excl : DerivExcludes1 S E) :
    ∃ T, S ⊆ T ∧ QuasiPrime Axioms T ∧ DerivExcludes1 T E := by
  obtain ⟨T, hST, hTmax⟩ := zorn_subset_nonempty (QPExcludingSupersets (Axioms := Axioms) S E)
    (fun C hCsub hchain hCne =>
      ⟨⋃₀ C, qp_excluding_chain_union hCsub hchain hCne,
        fun s hs => Set.subset_sUnion_of_mem hs⟩)
    S (qp_excluding_base_mem hS h_excl)
  obtain ⟨_, hTclosed, hTexcl⟩ := hTmax.prop
  refine ⟨T, hST, ⟨⟨trivial, hTclosed⟩, ?_⟩, hTexcl⟩
  -- Disjunction property of `T`.
  intro A B h_or
  by_contra h_not
  push Not at h_not
  obtain ⟨hA, hB⟩ := h_not
  have branch : ∀ X : Proposition Atom, X ∉ T →
      ∃ (x0 : Proposition Atom) (xs0 L0 : List (Proposition Atom)),
        x0 ∈ E ∧ (∀ y ∈ xs0, y ∈ E) ∧ (∀ z ∈ L0, z ∈ insert X T) ∧
        (modalDerivationSystem Axioms).Deriv L0 (bigOr1 x0 xs0) := by
    intro X hXT
    have hTX_sup : T ⊆ modalDeductiveClosure Axioms (insert X T) :=
      Set.Subset.trans (Set.subset_insert X T) (modal_subset_deductive_closure Axioms _)
    have hX_in : X ∈ modalDeductiveClosure Axioms (insert X T) :=
      modal_subset_deductive_closure Axioms _ (Set.mem_insert X T)
    have hnotmem :
        modalDeductiveClosure Axioms (insert X T) ∉
          QPExcludingSupersets (Axioms := Axioms) S E := by
      intro hmem
      exact hXT ((hTmax.eq_of_ge hmem hTX_sup) ▸ hX_in)
    have h_sub_cl : S ⊆ modalDeductiveClosure Axioms (insert X T) :=
      hST.trans hTX_sup
    have h_closed_cl : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms)
        (modalDeductiveClosure Axioms (insert X T)) :=
      fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd
    have h_fail : ¬ DerivExcludes1 (modalDeductiveClosure Axioms (insert X T)) E := by
      intro hexcl; exact hnotmem ⟨h_sub_cl, h_closed_cl, hexcl⟩
    unfold DerivExcludes1 at h_fail
    push Not at h_fail
    obtain ⟨x0, xs0, hx0E, hxs0E, hmemcl⟩ := h_fail
    obtain ⟨L0, hL0_sub, hL0_deriv⟩ := hmemcl
    exact ⟨x0, xs0, L0, hx0E, hxs0E, hL0_sub, hL0_deriv⟩
  obtain ⟨xA, xsA, LA0, hxAE, hxsAE, hLA0_sub, hLA0_deriv⟩ := branch A hA
  obtain ⟨xB, xsB, LB0, hxBE, hxsBE, hLB0_sub, hLB0_deriv⟩ := branch B hB
  obtain ⟨dLA0⟩ := hLA0_deriv
  obtain ⟨dLB0⟩ := hLB0_deriv
  set χ : Proposition Atom := bigOr1 xA (xsA ++ (xB :: xsB)) with hχdef
  have hAchi : ∃ LA', (∀ x ∈ LA', x ∈ T) ∧
      (modalDerivationSystem Axioms).Deriv LA' (A.imp χ) := by
    have d1w : DerivationTree Axioms (A :: LA0) (bigOr1 xA xsA) :=
      DerivationTree.weakening LA0 _ _ dLA0 (fun x hx => List.mem_cons.mpr (Or.inr hx))
    obtain ⟨d2⟩ : (modalDerivationSystem Axioms).Deriv [] ((bigOr1 xA xsA).imp χ) :=
      bigOr1_append_left h_implyK h_implyS h_orI1 h_orI2 h_orE xA xsA (xB :: xsB)
    have d2w : DerivationTree Axioms (A :: LA0) ((bigOr1 xA xsA).imp χ) :=
      DerivationTree.weakening [] _ _ d2 (fun _ h => nomatch h)
    have d3 : DerivationTree Axioms (A :: LA0) χ :=
      DerivationTree.modus_ponens _ _ _ d2w d1w
    exact hCutMK h_implyK h_implyS (U := T) (L := A :: LA0) (a := A) (b := χ)
      (fun x hx => by
        rcases List.mem_cons.mp hx with heq | hx'
        · exact heq ▸ Set.mem_insert A T
        · exact hLA0_sub x hx')
      ⟨d3⟩
  have hBchi : ∃ LB', (∀ x ∈ LB', x ∈ T) ∧
      (modalDerivationSystem Axioms).Deriv LB' (B.imp χ) := by
    have d1w : DerivationTree Axioms (B :: LB0) (bigOr1 xB xsB) :=
      DerivationTree.weakening LB0 _ _ dLB0 (fun x hx => List.mem_cons.mpr (Or.inr hx))
    obtain ⟨d2⟩ : (modalDerivationSystem Axioms).Deriv [] ((bigOr1 xB xsB).imp χ) :=
      bigOr1_append_right h_implyK h_implyS h_orI1 h_orI2 h_orE xA xsA xB xsB
    have d2w : DerivationTree Axioms (B :: LB0) ((bigOr1 xB xsB).imp χ) :=
      DerivationTree.weakening [] _ _ d2 (fun _ h => nomatch h)
    have d3 : DerivationTree Axioms (B :: LB0) χ :=
      DerivationTree.modus_ponens _ _ _ d2w d1w
    exact hCutMK h_implyK h_implyS (U := T) (L := B :: LB0) (a := B) (b := χ)
      (fun x hx => by
        rcases List.mem_cons.mp hx with heq | hx'
        · exact heq ▸ Set.mem_insert B T
        · exact hLB0_sub x hx')
      ⟨d3⟩
  obtain ⟨LA', hLA'_sub, hLA'_deriv⟩ := hAchi
  obtain ⟨LB', hLB'_sub, hLB'_deriv⟩ := hBchi
  obtain ⟨dA'⟩ := hLA'_deriv
  obtain ⟨dB'⟩ := hLB'_deriv
  have hOrMem : DerivationTree Axioms (A.or B :: LA' ++ LB') (A.or B) :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hAchi' : DerivationTree Axioms (A.or B :: LA' ++ LB') (A.imp χ) :=
    .weakening LA' _ _ dA'
      (fun x hx => List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl hx))))
  have hBchi' : DerivationTree Axioms (A.or B :: LA' ++ LB') (B.imp χ) :=
    .weakening LB' _ _ dB'
      (fun x hx => List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hx))))
  have hOrEax : DerivationTree Axioms (A.or B :: LA' ++ LB')
      ((A.imp χ).imp ((B.imp χ).imp ((A.or B).imp χ))) :=
    .weakening [] _ _ (.ax [] _ (h_orE A B χ)) (fun _ h => nomatch h)
  have hstep1 : DerivationTree Axioms (A.or B :: LA' ++ LB')
      ((B.imp χ).imp ((A.or B).imp χ)) :=
    .modus_ponens _ _ _ hOrEax hAchi'
  have hstep2 : DerivationTree Axioms (A.or B :: LA' ++ LB') ((A.or B).imp χ) :=
    .modus_ponens _ _ _ hstep1 hBchi'
  have hχderiv : DerivationTree Axioms (A.or B :: LA' ++ LB') χ :=
    .modus_ponens _ _ _ hstep2 hOrMem
  have hχmem : χ ∈ T :=
    hTclosed (A.or B :: LA' ++ LB') χ
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_or
        · rcases List.mem_append.mp hx' with h1 | h2
          · exact hLA'_sub x h1
          · exact hLB'_sub x h2)
      ⟨hχderiv⟩
  refine hTexcl xA (xsA ++ (xB :: xsB)) hxAE ?_ hχmem
  intro y hy
  rcases List.mem_append.mp hy with h1 | h2
  · exact hxsAE y h1
  · rcases List.mem_cons.mp h2 with rfl | h3
    · exact hxBE
    · exact hxsBE y h3

end NonemptyPairExclusion

/-! ### Box Witness (generic) -/

section CanonicalBoxWitness

private theorem extract_box_list1 (u : MinCanonicalPrimeWorld Axioms) :
    ∀ (xs : List (Proposition Atom)), (∀ x ∈ xs, ∃ B, x = (□B) ∧ B ∉ u.val) →
      ∃ bs : List (Proposition Atom), xs = bs.map Proposition.box ∧ ∀ B ∈ bs, B ∉ u.val
  | [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | x :: xs, hl => by
      obtain ⟨B, hxeq, hBnu⟩ := hl x (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨bs, heq, hbs⟩ :=
        extract_box_list1 u xs (fun y hy => hl y (List.mem_cons.mpr (Or.inr hy)))
      refine ⟨B :: bs, ?_, ?_⟩
      · rw [hxeq, heq, List.map_cons, Proposition.box_def]
      · intro C hC
        rcases List.mem_cons.mp hC with rfl | hC'
        · exact hBnu
        · exact hbs C hC'

private theorem extract_split1 (w u : MinCanonicalPrimeWorld Axioms) :
    ∀ (L : List (Proposition Atom)),
      (∀ x ∈ L, x ∈ w.val ∨ ∃ A, x = (◇A) ∧ A ∈ u.val) →
      ∃ Lw As : List (Proposition Atom),
        (∀ y ∈ Lw, y ∈ w.val) ∧ (∀ A ∈ As, A ∈ u.val) ∧
        (∀ x ∈ L, x ∈ (As.map Proposition.diamond) ++ Lw)
  | [], _ => by
      refine ⟨[], [], ?_, ?_, ?_⟩ <;> exact fun _ h => nomatch h
  | x :: xs, hL => by
      obtain ⟨Lw', As', hLw', hAs', hsub'⟩ :=
        extract_split1 w u xs (fun y hy => hL y (List.mem_cons.mpr (Or.inr hy)))
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

private theorem bigOr1_mem_disjunct (u : MinCanonicalPrimeWorld Axioms) :
    ∀ (x0 : Proposition Atom) (xs0 : List (Proposition Atom)), bigOr1 x0 xs0 ∈ u.val →
      x0 ∈ u.val ∨ ∃ C ∈ xs0, C ∈ u.val
  | x0, [], hmem => Or.inl hmem
  | x0, y :: ys, hmem => by
      rcases u.property.disj hmem with h | h
      · exact Or.inl h
      · rcases bigOr1_mem_disjunct u y ys h with h' | ⟨C, hC, hCu⟩
        · exact Or.inr ⟨y, List.mem_cons.mpr (Or.inl rfl), h'⟩
        · exact Or.inr ⟨C, List.mem_cons.mpr (Or.inr hC), hCu⟩

/-- **Box witness underivability, nonempty**, generic over `Axioms`. -/
private theorem box_witness_pair_underivable1
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w u : MinCanonicalPrimeWorld Axioms}
    (h_wu : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ u.val) :
    DerivExcludes1
      (modalDeductiveClosure Axioms (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ u.val}))
      {χ | ∃ B, χ = (□B) ∧ B ∉ u.val} := by
  intro x0 xs0 hx0Sig hxs0Sig hmem
  obtain ⟨B0, hB0eq, hB0nu⟩ := hx0Sig
  obtain ⟨bs, hbseq, hbsnu⟩ := extract_box_list1 u xs0 hxs0Sig
  obtain ⟨L, hLΓ, hd⟩ := hmem
  obtain ⟨d⟩ := hd
  subst hB0eq
  have bridge0 := boxOr1_of_boxDisj h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE
    h_k h_kdia h_cd h_idb B0 bs
  rw [hbseq] at d
  have d_box : DerivationTree Axioms L (Proposition.box (bigOr1 B0 bs)) :=
    DerivationTree.modus_ponens L _ _
      (DerivationTree.weakening [] L _ bridge0 (fun _ h => nomatch h)) d
  have hLΓ' : ∀ x ∈ L, x ∈ w.val ∨ ∃ A, x = (◇A) ∧ A ∈ u.val := fun x hx => hLΓ x hx
  obtain ⟨Lw, As, hLw, hAs, hsub⟩ := extract_split1 w u L hLΓ'
  have d_box' : DerivationTree Axioms ((As.map Proposition.diamond) ++ Lw)
      (Proposition.box (bigOr1 B0 bs)) :=
    DerivationTree.weakening L _ _ d_box hsub
  have hcontra : bigOr1 B0 bs ∈ u.val → False := by
    intro hmemU
    rcases bigOr1_mem_disjunct u B0 bs hmemU with h | ⟨C, hC, hCu⟩
    · exact hB0nu h
    · exact hbsnu C hC hCu
  cases As with
  | nil =>
      have d_box'' : DerivationTree Axioms Lw (Proposition.box (bigOr1 B0 bs)) := d_box'
      exact hcontra (h_wu _ (w.property.closed Lw _ hLw ⟨d_box''⟩))
  | cons x xs =>
      have d_box'' : DerivationTree Axioms (((◇x) :: xs.map Proposition.diamond) ++ Lw)
          (Proposition.box (bigOr1 B0 bs)) := d_box'
      have d_unpack : DerivationTree Axioms (bigAnd1 (◇x) (xs.map Proposition.diamond) :: Lw)
          (Proposition.box (bigOr1 B0 bs)) :=
        unpackConj1 h_implyK h_implyS h_andE1 h_andE2 (◇x) (xs.map Proposition.diamond) Lw _
          d_box''
      have d_disch : DerivationTree Axioms Lw
          ((bigAnd1 (◇x) (xs.map Proposition.diamond)).imp (Proposition.box (bigOr1 B0 bs))) :=
        deductionTheorem h_implyK h_implyS Lw
          (bigAnd1 (◇x) (xs.map Proposition.diamond)) (Proposition.box (bigOr1 B0 bs)) d_unpack
      have hM : (bigAnd1 (◇x) (xs.map Proposition.diamond)).imp (Proposition.box (bigOr1 B0 bs))
          ∈ w.val :=
        w.property.closed Lw _ hLw ⟨d_disch⟩
      have bridge1 := diaBigAnd1ToBigAnd1Dia h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1
        h_orI2 h_orE h_k h_kdia h_cd h_idb x xs
      set X : Proposition Atom := ◇ (bigAnd1 x xs) with hXdef
      set M : Proposition Atom :=
        (bigAnd1 (◇x) (xs.map Proposition.diamond)).imp (Proposition.box (bigOr1 B0 bs))
        with hMdef
      have step : DerivationTree Axioms [X, M] (Proposition.box (bigOr1 B0 bs)) := by
        have hXmem : DerivationTree Axioms [X, M] X :=
          .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
        have hMmem : DerivationTree Axioms [X, M] M :=
          .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        have hBD : DerivationTree Axioms [X, M]
            (bigAnd1 (◇x) (xs.map Proposition.diamond)) :=
          .modus_ponens _ _ _ (.weakening [] _ _ bridge1 (fun _ h => nomatch h)) hXmem
        exact .modus_ponens _ _ _ hMmem hBD
      have step_disch : DerivationTree Axioms [M]
          (X.imp (Proposition.box (bigOr1 B0 bs))) :=
        deductionTheorem h_implyK h_implyS [M] X (Proposition.box (bigOr1 B0 bs)) step
      have hXimpBOX : X.imp (Proposition.box (bigOr1 B0 bs)) ∈ w.val :=
        w.property.closed [M] _
          (fun y hy => by
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hM
            · exact absurd hy' (by simp))
          ⟨step_disch⟩
      have hBoxImp : Proposition.box ((bigAnd1 x xs).imp (bigOr1 B0 bs)) ∈ w.val :=
        w.property.closed [X.imp (Proposition.box (bigOr1 B0 bs))] _
          (fun y hy => by
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hXimpBOX
            · exact absurd hy' (by simp))
          ⟨.modus_ponens _ _ _
            (.ax _ _ (h_idb (bigAnd1 x xs) (bigOr1 B0 bs)))
            (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
      have hInU : (bigAnd1 x xs).imp (bigOr1 B0 bs) ∈ u.val := h_wu _ hBoxImp
      have hBigAndXsU : bigAnd1 x xs ∈ u.val :=
        bigAnd1_mem_u h_andI x xs (hAs x (List.mem_cons.mpr (Or.inl rfl)))
          (fun A hA => hAs A (List.mem_cons.mpr (Or.inr hA)))
      have hBigOrU : bigOr1 B0 bs ∈ u.val :=
        u.property.closed [(bigAnd1 x xs).imp (bigOr1 B0 bs), bigAnd1 x xs] _
          (fun y hy => by
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hInU
            · rcases List.mem_cons.mp hy' with rfl | hy''
              · exact hBigAndXsU
              · nomatch hy'')
          ⟨.modus_ponens _ _ _
            (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
            (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
      exact hcontra hBigOrU

/-- **Box Witness**, generic over `Axioms`. -/
theorem min_canonical_box_witness
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w : MinCanonicalPrimeWorld Axioms} {φ : Proposition Atom}
    (h_notbox : (□φ) ∉ w.val) :
    ∃ w' u : MinCanonicalPrimeWorld Axioms, w ≤ w' ∧ minCanonicalR w' u ∧ φ ∉ u.val := by
  obtain ⟨Uval, hUsup, hUqp, hUphi⟩ :=
    box_refuting_theory h_implyK h_implyS h_orE h_k w.property h_notbox
  let u : MinCanonicalPrimeWorld Axioms := ⟨Uval, hUqp⟩
  have hSu : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ u.val := fun ψ hψ => hUsup hψ
  have hexcl := box_witness_pair_underivable1 h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1
    h_orI2 h_orE h_k h_kdia h_cd h_idb hSu
  have hSclosed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms)
      (modalDeductiveClosure Axioms (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ u.val})) :=
    fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd
  obtain ⟨Tval, hTsup, hTqp, hTexcl⟩ := quasi_prime_set_exclusion1 h_implyK h_implyS h_orI1 h_orI2
    h_orE hSclosed hexcl
  let w' : MinCanonicalPrimeWorld Axioms := ⟨Tval, hTqp⟩
  have hw_le_w' : w ≤ w' := fun x hx =>
    hTsup (modal_subset_deductive_closure Axioms _ (Set.mem_union_left _ hx))
  have hdia_clause : ∀ ψ, ψ ∈ u.val → (◇ψ) ∈ w'.val := fun ψ hψ =>
    hTsup (modal_subset_deductive_closure Axioms _
      (Set.mem_union_right _ ⟨ψ, rfl, hψ⟩))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w'.val → ψ ∈ u.val := by
    intro ψ hψ_mem
    by_contra hψ_notU
    exact (hTexcl (□ψ) [] ⟨ψ, rfl, hψ_notU⟩ (fun _ h => nomatch h)) hψ_mem
  exact ⟨w', u, hw_le_w', ⟨hbox_clause, hdia_clause⟩, hUphi⟩

end CanonicalBoxWitness

/-! ### Diamond Witness (generic) -/

section CanonicalDiamondWitness

private noncomputable def boxContextDeriv
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))) :
    ∀ (L : List (Proposition Atom)) (ψ : Proposition Atom),
      DerivationTree Axioms L ψ →
      DerivationTree Axioms (L.map Proposition.box) (Proposition.box ψ)
  | [], ψ, d => .necessitation ψ d
  | A :: L', ψ, d => by
      have dt : DerivationTree Axioms L' (A.imp ψ) :=
        deductionTheorem h_implyK h_implyS L' A ψ d
      have ihres : DerivationTree Axioms (L'.map Proposition.box)
          (Proposition.box (A.imp ψ)) :=
        boxContextDeriv h_implyK h_implyS h_k L' (A.imp ψ) dt
      have hKax : DerivationTree Axioms (L'.map Proposition.box)
          ((Proposition.box (A.imp ψ)).imp
            ((Proposition.box A).imp (Proposition.box ψ))) :=
        .weakening [] _ _ (.ax [] _ (h_k A ψ)) (fun _ h => nomatch h)
      have hstep : DerivationTree Axioms (L'.map Proposition.box)
          ((Proposition.box A).imp (Proposition.box ψ)) :=
        .modus_ponens _ _ _ hKax ihres
      have hstep_w : DerivationTree Axioms
          (Proposition.box A :: L'.map Proposition.box)
          ((Proposition.box A).imp (Proposition.box ψ)) :=
        .weakening _ _ _ hstep (fun x hx => List.mem_cons.mpr (Or.inr hx))
      have hboxA : DerivationTree Axioms (Proposition.box A :: L'.map Proposition.box)
          (Proposition.box A) :=
        .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
      exact .modus_ponens _ _ _ hstep_w hboxA

private theorem extract_split_dia1 (w : MinCanonicalPrimeWorld Axioms) (φ : Proposition Atom) :
    ∀ (L : List (Proposition Atom)),
      (∀ x ∈ L, (□x) ∈ w.val ∨ x = φ) →
      ∃ Lw : List (Proposition Atom), (∀ y ∈ Lw, (□y) ∈ w.val) ∧ (∀ x ∈ L, x ∈ φ :: Lw)
  | [], _ => by refine ⟨[], ?_, ?_⟩ <;> exact fun _ h => nomatch h
  | x :: xs, hL => by
      obtain ⟨Lw', hLw', hsub'⟩ :=
        extract_split_dia1 w φ xs (fun y hy => hL y (List.mem_cons.mpr (Or.inr hy)))
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

/-- **Diamond witness underivability, nonempty**, generic over `Axioms`. -/
private theorem diamond_witness_underivable1
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w : MinCanonicalPrimeWorld Axioms}
    {φ : Proposition Atom} (h_diaphi : (◇φ) ∈ w.val) :
    DerivExcludes1
      (modalDeductiveClosure Axioms ({ψ | (□ψ) ∈ w.val} ∪ {φ}))
      {χ | (◇χ) ∉ w.val} := by
  intro x0 xs0 hx0Sig hxs0Sig hmem
  obtain ⟨L, hLΓ, hd⟩ := hmem
  obtain ⟨d⟩ := hd
  have hLΓ' : ∀ x ∈ L, (□x) ∈ w.val ∨ x = φ := fun x hx => hLΓ x hx
  obtain ⟨Lw, hLw, hsub⟩ := extract_split_dia1 w φ L hLΓ'
  have d' : DerivationTree Axioms (φ :: Lw) (bigOr1 x0 xs0) :=
    .weakening L _ _ d hsub
  have d_disch : DerivationTree Axioms Lw (φ.imp (bigOr1 x0 xs0)) :=
    deductionTheorem h_implyK h_implyS Lw φ (bigOr1 x0 xs0) d'
  have d_box : DerivationTree Axioms (Lw.map Proposition.box)
      (Proposition.box (φ.imp (bigOr1 x0 xs0))) :=
    boxContextDeriv h_implyK h_implyS h_k Lw (φ.imp (bigOr1 x0 xs0)) d_disch
  have hM : Proposition.box (φ.imp (bigOr1 x0 xs0)) ∈ w.val :=
    w.property.closed (Lw.map Proposition.box) _
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact hLw y hy)
      ⟨d_box⟩
  have hbridge : DerivationTree Axioms [Proposition.box (φ.imp (bigOr1 x0 xs0))]
      ((◇φ).imp (◇ (bigOr1 x0 xs0))) :=
    .modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (h_kdia φ (bigOr1 x0 xs0))) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
  have hImp : (◇φ).imp (◇ (bigOr1 x0 xs0)) ∈ w.val :=
    w.property.closed [Proposition.box (φ.imp (bigOr1 x0 xs0))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hM
        · nomatch hx')
      ⟨hbridge⟩
  have hDiaBigOr : (◇ (bigOr1 x0 xs0)) ∈ w.val :=
    w.property.closed [(◇φ).imp (◇ (bigOr1 x0 xs0)), (◇φ)] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hImp
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · exact h_diaphi
          · nomatch hx'')
      ⟨.modus_ponens _ _ _ (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
        (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
  have hDistrib := diaOr1_of_diaDisj h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE
    h_k h_kdia h_cd h_idb x0 xs0
  have hBigOrDia : bigOr1 (◇x0) (xs0.map Proposition.diamond) ∈ w.val :=
    w.property.closed [(◇ (bigOr1 x0 xs0))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hDiaBigOr
        · nomatch hx')
      ⟨.modus_ponens _ _ _ (.weakening [] _ _ hDistrib (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  rcases bigOr1_mem_disjunct w (◇x0) (xs0.map Proposition.diamond) hBigOrDia with h | ⟨C, hC, hCu⟩
  · exact hx0Sig h
  · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    exact (hxs0Sig D hD) hCu

/-- **Diamond Witness**, generic over `Axioms`. -/
theorem min_canonical_diamond_witness
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w : MinCanonicalPrimeWorld Axioms} {φ : Proposition Atom}
    (h_diaphi : (◇φ) ∈ w.val) :
    ∃ v : MinCanonicalPrimeWorld Axioms, minCanonicalR w v ∧ φ ∈ v.val := by
  have hdwu := diamond_witness_underivable1 h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2
    h_orE h_k h_kdia h_cd h_idb h_diaphi
  have hSclosed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms)
      (modalDeductiveClosure Axioms ({ψ | (□ψ) ∈ w.val} ∪ {φ})) :=
    fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd
  obtain ⟨Tval, hTsup, hTqp, hTexcl⟩ := quasi_prime_set_exclusion1 h_implyK h_implyS h_orI1 h_orI2
    h_orE hSclosed hdwu
  let v : MinCanonicalPrimeWorld Axioms := ⟨Tval, hTqp⟩
  have hphi_v : φ ∈ v.val :=
    hTsup (modal_subset_deductive_closure Axioms _ (Set.mem_union_right _ rfl))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ v.val := fun ψ hψ =>
    hTsup (modal_subset_deductive_closure Axioms _ (Set.mem_union_left _ hψ))
  have hdia_clause : ∀ ψ, ψ ∈ v.val → (◇ψ) ∈ w.val := by
    intro ψ hψ_mem
    by_contra hψ_notdia
    exact (hTexcl ψ [] hψ_notdia (fun _ h => nomatch h)) hψ_mem
  exact ⟨v, ⟨hbox_clause, hdia_clause⟩, hphi_v⟩

end CanonicalDiamondWitness

/-! ### Frame Confluence Conditions (F1/F2, generic) -/

section CanonicalFrameConditions

private theorem extract_split_union1 {P Q : Proposition Atom → Prop} :
    ∀ (L : List (Proposition Atom)), (∀ x ∈ L, P x ∨ Q x) →
      ∃ Lp Lq : List (Proposition Atom),
        (∀ y ∈ Lp, P y) ∧ (∀ y ∈ Lq, Q y) ∧ (∀ x ∈ L, x ∈ Lp ++ Lq)
  | [], _ => by
      refine ⟨[], [], ?_, ?_, ?_⟩ <;> exact fun _ h => nomatch h
  | x :: xs, hL => by
      obtain ⟨Lp', Lq', hLp', hLq', hsub'⟩ :=
        extract_split_union1 xs (fun y hy => hL y (List.mem_cons.mpr (Or.inr hy)))
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

/-- **Up-confluence underivability, nonempty**, generic over `Axioms`. -/
private theorem canonical_f1_underivable1
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w w' v : MinCanonicalPrimeWorld Axioms}
    (hww' : w ≤ w') (hdia_wv : ∀ ψ, ψ ∈ v.val → (◇ψ) ∈ w.val) :
    DerivExcludes1
      (modalDeductiveClosure Axioms (v.val ∪ {ψ | (□ψ) ∈ w'.val}))
      {χ | (◇χ) ∉ w'.val} := by
  intro x0 xs0 hx0Sig hxs0Sig hmem
  obtain ⟨L, hLΓ, hd⟩ := hmem
  obtain ⟨d⟩ := hd
  have hLΓ' : ∀ x ∈ L, x ∈ v.val ∨ (□x) ∈ w'.val := fun x hx => hLΓ x hx
  obtain ⟨Lv, Lbox, hLv, hLbox, hsub⟩ := extract_split_union1 L hLΓ'
  set θ : Proposition Atom := Proposition.bot.imp Proposition.bot with hθdef
  have hθv : θ ∈ v.val :=
    v.property.closed [] _ (fun _ h => nomatch h) ⟨idDeriv h_implyK h_implyS Proposition.bot⟩
  have d' : DerivationTree Axioms (Lv ++ Lbox) (bigOr1 x0 xs0) :=
    .weakening L _ _ d hsub
  have d'' : DerivationTree Axioms (θ :: (Lv ++ Lbox)) (bigOr1 x0 xs0) :=
    .weakening _ _ _ d' (fun x hx => List.mem_cons.mpr (Or.inr hx))
  have d''' : DerivationTree Axioms ((θ :: Lv) ++ Lbox) (bigOr1 x0 xs0) := d''
  have d_unpack : DerivationTree Axioms (bigAnd1 θ Lv :: Lbox) (bigOr1 x0 xs0) :=
    unpackConj1 h_implyK h_implyS h_andE1 h_andE2 θ Lv Lbox _ d'''
  have d_disch : DerivationTree Axioms Lbox ((bigAnd1 θ Lv).imp (bigOr1 x0 xs0)) :=
    deductionTheorem h_implyK h_implyS Lbox (bigAnd1 θ Lv) (bigOr1 x0 xs0) d_unpack
  have d_box : DerivationTree Axioms (Lbox.map Proposition.box)
      (Proposition.box ((bigAnd1 θ Lv).imp (bigOr1 x0 xs0))) :=
    boxContextDeriv h_implyK h_implyS h_k Lbox _ d_disch
  have hM : Proposition.box ((bigAnd1 θ Lv).imp (bigOr1 x0 xs0)) ∈ w'.val :=
    w'.property.closed (Lbox.map Proposition.box) _
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact hLbox y hy)
      ⟨d_box⟩
  have hbridge : DerivationTree Axioms
      [Proposition.box ((bigAnd1 θ Lv).imp (bigOr1 x0 xs0))]
      ((◇ (bigAnd1 θ Lv)).imp (◇ (bigOr1 x0 xs0))) :=
    .modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (h_kdia (bigAnd1 θ Lv) (bigOr1 x0 xs0))) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
  have hImp : (◇ (bigAnd1 θ Lv)).imp (◇ (bigOr1 x0 xs0)) ∈ w'.val :=
    w'.property.closed [Proposition.box ((bigAnd1 θ Lv).imp (bigOr1 x0 xs0))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hM
        · nomatch hx')
      ⟨hbridge⟩
  have hBigAndV : bigAnd1 θ Lv ∈ v.val := bigAnd1_mem_u h_andI θ Lv hθv hLv
  have hDiaBigAndV_w : (◇ (bigAnd1 θ Lv)) ∈ w.val := hdia_wv (bigAnd1 θ Lv) hBigAndV
  have hDiaBigAndV_w' : (◇ (bigAnd1 θ Lv)) ∈ w'.val := hww' hDiaBigAndV_w
  have hDiaBigOr : (◇ (bigOr1 x0 xs0)) ∈ w'.val :=
    w'.property.closed
      [(◇ (bigAnd1 θ Lv)).imp (◇ (bigOr1 x0 xs0)), (◇ (bigAnd1 θ Lv))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hImp
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · exact hDiaBigAndV_w'
          · nomatch hx'')
      ⟨.modus_ponens _ _ _ (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
        (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
  have hDistrib := diaOr1_of_diaDisj h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE
    h_k h_kdia h_cd h_idb x0 xs0
  have hBigOrDia : bigOr1 (◇x0) (xs0.map Proposition.diamond) ∈ w'.val :=
    w'.property.closed [(◇ (bigOr1 x0 xs0))] _
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hDiaBigOr
        · nomatch hx')
      ⟨.modus_ponens _ _ _ (.weakening [] _ _ hDistrib (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  rcases bigOr1_mem_disjunct w' (◇x0) (xs0.map Proposition.diamond) hBigOrDia with
    h | ⟨C, hC, hCu⟩
  · exact hx0Sig h
  · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    exact (hxs0Sig D hD) hCu

/-- **`min_canonical_f1`**: up-confluence, generic over `Axioms`. -/
theorem min_canonical_f1
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w w' v : MinCanonicalPrimeWorld Axioms}
    (hww' : w ≤ w') (hwv : minCanonicalR w v) :
    ∃ v' : MinCanonicalPrimeWorld Axioms, minCanonicalR w' v' ∧ v ≤ v' := by
  obtain ⟨_hbox_wv, hdia_wv⟩ := hwv
  have hu := canonical_f1_underivable1 h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2
    h_orE h_k h_kdia h_cd h_idb hww' hdia_wv
  have hSclosed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms)
      (modalDeductiveClosure Axioms (v.val ∪ {ψ | (□ψ) ∈ w'.val})) :=
    fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd
  obtain ⟨Tval, hTsup, hTqp, hTexcl⟩ := quasi_prime_set_exclusion1 h_implyK h_implyS h_orI1 h_orI2
    h_orE hSclosed hu
  let v' : MinCanonicalPrimeWorld Axioms := ⟨Tval, hTqp⟩
  have hv_le_v' : v ≤ v' := fun x hx =>
    hTsup (modal_subset_deductive_closure Axioms _ (Set.mem_union_left _ hx))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w'.val → ψ ∈ v'.val := fun ψ hψ =>
    hTsup (modal_subset_deductive_closure Axioms _ (Set.mem_union_right _ hψ))
  have hdia_clause : ∀ ψ, ψ ∈ v'.val → (◇ψ) ∈ w'.val := by
    intro ψ hψ_mem
    by_contra hψ_notdia
    exact (hTexcl ψ [] hψ_notdia (fun _ h => nomatch h)) hψ_mem
  exact ⟨v', ⟨hbox_clause, hdia_clause⟩, hv_le_v'⟩

/-- **`min_canonical_f2`**: down-confluence, generic over `Axioms`. -/
theorem min_canonical_f2
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w v v' : MinCanonicalPrimeWorld Axioms}
    (hwv : minCanonicalR w v) (hvv' : v ≤ v') :
    ∃ w' : MinCanonicalPrimeWorld Axioms, w ≤ w' ∧ minCanonicalR w' v' := by
  obtain ⟨hbox_wv, _hdia_wv⟩ := hwv
  have h_wu : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ v'.val := fun ψ hψ => hvv' (hbox_wv ψ hψ)
  have hexcl := box_witness_pair_underivable1 h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1
    h_orI2 h_orE h_k h_kdia h_cd h_idb h_wu
  have hSclosed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms)
      (modalDeductiveClosure Axioms (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ v'.val})) :=
    fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd
  obtain ⟨Tval, hTsup, hTqp, hTexcl⟩ := quasi_prime_set_exclusion1 h_implyK h_implyS h_orI1 h_orI2
    h_orE hSclosed hexcl
  let w' : MinCanonicalPrimeWorld Axioms := ⟨Tval, hTqp⟩
  have hw_le_w' : w ≤ w' := fun x hx =>
    hTsup (modal_subset_deductive_closure Axioms _ (Set.mem_union_left _ hx))
  have hdia_clause : ∀ ψ, ψ ∈ v'.val → (◇ψ) ∈ w'.val := fun ψ hψ =>
    hTsup (modal_subset_deductive_closure Axioms _
      (Set.mem_union_right _ ⟨ψ, rfl, hψ⟩))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w'.val → ψ ∈ v'.val := by
    intro ψ hψ_mem
    by_contra hψ_notV'
    exact (hTexcl (□ψ) [] ⟨ψ, rfl, hψ_notV'⟩ (fun _ h => nomatch h)) hψ_mem
  exact ⟨w', hw_le_w', ⟨hbox_clause, hdia_clause⟩⟩

end CanonicalFrameConditions

/-! ### Truth Lemma (generic) -/

section TruthLemma

/-- Modus ponens closure, generic (no MK-core hypotheses needed -- deductive closure only). -/
theorem min_canonical_imp_property {w : MinCanonicalPrimeWorld Axioms} {φ ψ : Proposition Atom}
    (h_imp : (φ.imp ψ) ∈ w.val) (h_phi : φ ∈ w.val) : ψ ∈ w.val := by
  apply w.property.closed [φ.imp ψ, φ] ψ
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h_imp
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · exact h_phi
      · nomatch hx''
  · exact ⟨.modus_ponens _ _ _
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
      (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩

private theorem min_truth_atom_case (w : MinCanonicalPrimeWorld Axioms) (p : Atom) :
    BForces minCanonicalR minCanonicalVal minBotForces w (Proposition.atom p) ↔
      (Proposition.atom p) ∈ w.val :=
  Iff.rfl

private theorem min_truth_bot_case (w : MinCanonicalPrimeWorld Axioms) :
    BForces minCanonicalR minCanonicalVal minBotForces w Proposition.bot ↔
      (Proposition.bot : Proposition Atom) ∈ w.val :=
  Iff.rfl

private theorem min_truth_and_case
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    {w : MinCanonicalPrimeWorld Axioms} {φ ψ : Proposition Atom}
    (ihφ : BForces minCanonicalR minCanonicalVal minBotForces w φ ↔ φ ∈ w.val)
    (ihψ : BForces minCanonicalR minCanonicalVal minBotForces w ψ ↔ ψ ∈ w.val) :
    BForces minCanonicalR minCanonicalVal minBotForces w (φ.and ψ) ↔ (φ.and ψ) ∈ w.val := by
  constructor
  · intro ⟨hφ, hψ⟩
    have h_phi_w := ihφ.mp hφ
    have h_psi_w := ihψ.mp hψ
    apply w.property.closed [φ, ψ] (φ.and ψ)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h_phi_w
      · rcases List.mem_cons.mp hx' with rfl | hx''
        · exact h_psi_w
        · nomatch hx''
    · exact ⟨.modus_ponens _ _ _
        (.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_andI φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))))
        (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
  · intro h_mem
    have hφ_mem : φ ∈ w.val := by
      apply w.property.closed [φ.and ψ] φ
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_mem
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_andE1 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    have hψ_mem : ψ ∈ w.val := by
      apply w.property.closed [φ.and ψ] ψ
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_mem
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_andE2 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    exact ⟨ihφ.mpr hφ_mem, ihψ.mpr hψ_mem⟩

private theorem min_truth_or_case
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    {w : MinCanonicalPrimeWorld Axioms} {φ ψ : Proposition Atom}
    (ihφ : BForces minCanonicalR minCanonicalVal minBotForces w φ ↔ φ ∈ w.val)
    (ihψ : BForces minCanonicalR minCanonicalVal minBotForces w ψ ↔ ψ ∈ w.val) :
    BForces minCanonicalR minCanonicalVal minBotForces w (φ.or ψ) ↔ (φ.or ψ) ∈ w.val := by
  constructor
  · intro h_or
    rcases h_or with hφ | hψ
    · have h_phi_w := ihφ.mp hφ
      apply w.property.closed [φ] (φ.or ψ)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_phi_w
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_orI1 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    · have h_psi_w := ihψ.mp hψ
      apply w.property.closed [ψ] (φ.or ψ)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_psi_w
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_orI2 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  · intro h_mem
    rcases w.property.disj h_mem with h | h
    · exact Or.inl (ihφ.mpr h)
    · exact Or.inr (ihψ.mpr h)

private theorem min_truth_imp_case
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    {w : MinCanonicalPrimeWorld Axioms} {φ ψ : Proposition Atom}
    (ihφ : ∀ T : MinCanonicalPrimeWorld Axioms,
      BForces minCanonicalR minCanonicalVal minBotForces T φ ↔ φ ∈ T.val)
    (ihψ : ∀ T : MinCanonicalPrimeWorld Axioms,
      BForces minCanonicalR minCanonicalVal minBotForces T ψ ↔ ψ ∈ T.val) :
    BForces minCanonicalR minCanonicalVal minBotForces w (φ.imp ψ) ↔ (φ.imp ψ) ∈ w.val := by
  constructor
  · intro h_forces
    by_contra h_not_mem
    obtain ⟨T_set, hwT, hT_qp, hφT, hψT⟩ :=
      imp_refuting_theory h_implyK h_implyS h_orE w.property h_not_mem
    let T : MinCanonicalPrimeWorld Axioms := ⟨T_set, hT_qp⟩
    have hle : w ≤ T := hwT
    have hf_φ := (ihφ T).mpr hφT
    have hf_ψ := h_forces T hle hf_φ
    exact hψT ((ihψ T).mp hf_ψ)
  · intro h_mem T hle hf_φ
    have h_imp_T : (φ.imp ψ) ∈ T.val := hle h_mem
    have h_φ_T : φ ∈ T.val := (ihφ T).mp hf_φ
    have h_ψ_T : ψ ∈ T.val := min_canonical_imp_property h_imp_T h_φ_T
    exact (ihψ T).mpr h_ψ_T

private theorem min_truth_box_case
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w : MinCanonicalPrimeWorld Axioms} {φ : Proposition Atom}
    (ih : ∀ T : MinCanonicalPrimeWorld Axioms,
      BForces minCanonicalR minCanonicalVal minBotForces T φ ↔ φ ∈ T.val) :
    BForces minCanonicalR minCanonicalVal minBotForces w (Proposition.box φ) ↔
      (Proposition.box φ) ∈ w.val := by
  simp only [BForces_box]
  constructor
  · intro h_forces
    by_contra h_notbox
    obtain ⟨w', u, hww', hRw'u, hphi_notU⟩ := min_canonical_box_witness h_implyK h_implyS h_andI
      h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_k h_kdia h_cd h_idb h_notbox
    exact hphi_notU ((ih u).mp (h_forces w' hww' u hRw'u))
  · intro h_mem w' hww' u hRw'u
    have hbox_w' : (Proposition.box φ) ∈ w'.val := hww' h_mem
    have hphi_u : φ ∈ u.val := hRw'u.1 φ hbox_w'
    exact (ih u).mpr hphi_u

private theorem min_truth_diamond_case
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    {w : MinCanonicalPrimeWorld Axioms} {φ : Proposition Atom}
    (ih : ∀ T : MinCanonicalPrimeWorld Axioms,
      BForces minCanonicalR minCanonicalVal minBotForces T φ ↔ φ ∈ T.val) :
    BForces minCanonicalR minCanonicalVal minBotForces w (Proposition.diamond φ) ↔
      (Proposition.diamond φ) ∈ w.val := by
  simp only [BForces_diamond]
  constructor
  · rintro ⟨u, hRwu, hforces_u⟩
    exact hRwu.2 φ ((ih u).mp hforces_u)
  · intro h_mem
    obtain ⟨v, hRwv, hphi_v⟩ := min_canonical_diamond_witness h_implyK h_implyS h_andI h_andE1
      h_andE2 h_orI1 h_orI2 h_orE h_k h_kdia h_cd h_idb h_mem
    exact ⟨v, hRwv, (ih v).mpr hphi_v⟩

/-- **The canonical truth lemma**, generic over `Axioms` extending MK's 12 core schemata. -/
theorem min_canonical_truth_lemma
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    (φ : Proposition Atom) (w : MinCanonicalPrimeWorld Axioms) :
    BForces minCanonicalR minCanonicalVal minBotForces w φ ↔ φ ∈ w.val := by
  induction φ generalizing w with
  | atom p => exact min_truth_atom_case w p
  | bot => exact min_truth_bot_case w
  | and φ ψ ihφ ihψ => exact min_truth_and_case h_andI h_andE1 h_andE2 (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => exact min_truth_or_case h_orI1 h_orI2 (ihφ w) (ihψ w)
  | imp φ ψ ihφ ihψ => exact min_truth_imp_case h_implyK h_implyS h_orE ihφ ihψ
  | box φ ihφ => exact (min_truth_box_case h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1 h_orI2
      h_orE h_k h_kdia h_cd h_idb ihφ)
  | diamond φ ihφ => exact (min_truth_diamond_case h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1
      h_orI2 h_orE h_k h_kdia h_cd h_idb ihφ)

end TruthLemma

end MinExt

/-! ## Axiom Membership Helpers (fully generic -- no MK-core hypotheses needed) -/

/-- **Axiom membership**: any axiom instance `Axioms φ` belongs to every canonical prime world's
underlying theory, via the theory's deductive closure. Fully generic (works for *any* `Axioms`,
not just MK-core extensions -- deductive closure does not inspect which axioms are present).
Mirrors IK's `axiom_mem` (`Extension.lean:181`). -/
theorem min_axiom_mem {Axioms : Proposition Atom → Prop}
    {w : MinExt.MinCanonicalPrimeWorld Axioms}
    {φ : Proposition Atom} (h : Axioms φ) : φ ∈ w.val :=
  w.property.1.2 [] φ (fun _ h => nomatch h) ⟨.ax [] _ h⟩

/-- **Modus-ponens closure membership**: alias for `MinExt.min_canonical_imp_property`, exposed
unqualified per the plan. -/
theorem min_imp_property {Axioms : Proposition Atom → Prop}
    {w : MinExt.MinCanonicalPrimeWorld Axioms}
    {φ ψ : Proposition Atom} (h_imp : (φ.imp ψ) ∈ w.val) (h_phi : φ ∈ w.val) : ψ ∈ w.val :=
  MinExt.min_canonical_imp_property h_imp h_phi

/-! ## Parametric Completeness over `FC`-Frames -/

/-- **Parametric completeness over `FC`-frames, generic over `Axioms`**: any formula `φ` that is
`MValidFC FC` is derivable from `Axioms` (extending MK's 12 core schemata), given that the
canonical relation `MinExt.minCanonicalR` (over `Axioms`) itself satisfies `FC` (`h_canonFC`).
Single-branch generalization of `mk_completeness` (`MinCompleteness.lean:55`) -- quasi-prime
worlds carry no consistency predicate, so there is no inconsistent case to split on (unlike IK's
`ivalidFC_completeness`, which `by_cases` on consistency and uses `efq`). -/
theorem mkvalidFC_completeness {Axioms : Proposition Atom → Prop}
    (FC : {World : Type u} → (World → World → Prop) → Prop)
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    (h_canonFC : FC (@MinExt.minCanonicalR Atom Axioms))
    {φ : Proposition Atom} (h_valid : MValidFC.{u, u} FC φ) :
    Derivable Axioms φ := by
  by_contra h_not_deriv
  obtain ⟨T, hT_qp, hT_excl⟩ := MinExt.min_head_realization h_implyK h_implyS h_orE h_not_deriv
  let w0 : MinExt.MinCanonicalPrimeWorld Axioms := ⟨T, hT_qp⟩
  have h_forces : BForces MinExt.minCanonicalR MinExt.minCanonicalVal MinExt.minBotForces w0 φ :=
    h_valid (MinExt.MinCanonicalPrimeWorld Axioms) MinExt.minCanonicalR h_canonFC
      (fun {w w' v} hww' hwv => MinExt.min_canonical_f1 h_implyK h_implyS h_andI h_andE1 h_andE2
        h_orI1 h_orI2 h_orE h_k h_kdia h_cd h_idb hww' hwv)
      (fun {w v v'} hwv hvv' => MinExt.min_canonical_f2 h_implyK h_implyS h_andI h_andE1 h_andE2
        h_orI1 h_orI2 h_orE h_k h_kdia h_cd h_idb hwv hvv')
      MinExt.minCanonicalVal MinExt.minBotForces
      (fun {_ _} p hw hv => MinExt.minCanonicalVal_upward_closed p hw hv)
      (fun {_ _} hw hbf => MinExt.minBotForces_upward_closed hw hbf) w0
  exact hT_excl ((MinExt.min_canonical_truth_lemma h_implyK h_implyS h_andI h_andE1 h_andE2 h_orI1
    h_orI2 h_orE h_k h_kdia h_cd h_idb φ w0).mp h_forces)

end Cslib.Logic.Modal
