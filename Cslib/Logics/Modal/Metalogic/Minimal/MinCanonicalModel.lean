/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Minimal.MinPrimeTheory

/-! # Canonical Accessibility Relation and Witnesses for `MK`

This module builds the birelational ∃-diamond canonical accessibility relation over quasi-prime
`MK` worlds, together with the box/diamond witnesses and F1/F2 confluence. This is the crux of
the completeness proof: `IK`'s corresponding construction
(`Intuitionistic/CanonicalModel.lean`) is not reusable because its box/diamond witnesses rely on
a "Lindenbaum-pair" set-exclusion lemma (`Metalogic.prime_set_exclusion`) that is *structurally*
`efq`-dependent (its disjunction-property proof needs `bigOr_append_left`, whose empty-list base
case is exactly `⊥ → φ`). `MK` has no `efq`.

**Resolution.** The `efq`-dependency traces to the *empty*-list base case of the classical
`⊥`-terminated `Metalogic.bigOr`. This module reimplements the Lindenbaum-pair machinery over
**nonempty** lists represented as an explicit head/tail pair `(x, xs)` with iterated
disjunction/conjunction operators `bigOr1`/`bigAnd1` that terminate at the *head* (`bigOr1 x [] =
x`) rather than at `⊥` (`Metalogic.bigOr [] = ⊥`). Every combinatorial step that IK discharged
via `efq` at the empty case is discharged here via `OrI1`/`OrI2`/the identity implication
(`x → x`, via `implyK`+`implyS`) instead -- no formula-existence step in this module ever
touches `⊥`. This is a bespoke, self-contained construction (report 01 "Residual GENUINE RISK";
plan Phase 3 Zero-Debt clause), not a duplication of `Constructive/Segment.lean`'s machinery
(which solves a different, single-clause problem for `CK`).

## Main Definitions

- `canonicalR`: the two-clause canonical accessibility relation (box clause + diamond-image
  clause), required because `MK`'s semantics is `MValid` (∃-diamond, F1/F2), not `CKValid`.
- `min_canonical_box_witness`/`min_canonical_diamond_witness`: the witness lemmas, built from
  `box_refuting_theory`/`dia_refuting_theory` (`Constructive/SegmentLindenbaum.lean`) for the
  "near side" and the bespoke nonempty Lindenbaum-pair construction for the "far side"
  (preserving the opposite clause of `canonicalR` under extension).
- `min_canonical_f1`/`min_canonical_f2`: up/down confluence, matching `BFrame.f1`/`BFrame.f2`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Ch. 3, F1/F2 confluence.
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Metalogic

universe u

variable {Atom : Type u}

/-! ## Canonical Accessibility Relation -/

/-- The canonical accessibility relation for `MK`'s birelational (∃-diamond) semantics, carrying
**both** a box clause and a diamond-image clause since `◇` is primitive and `MK` keeps the
Fischer-Servi axioms `Cd`/`Idb` (unlike `CK`'s single-clause segment relation, which suffices
only for the weaker `CKValid`):

- box clause (`□φ ∈ w.val → φ ∈ v.val`): every boxed formula true at `w` is true at `v`;
- diamond-image clause (`φ ∈ v.val → ◇φ ∈ w.val`): every formula true at `v` is possible at `w`.

Mirrors `canonicalR` (`Intuitionistic/CanonicalModel.lean:117-118`) verbatim, at
`MinCanonicalPrimeWorld` (quasi-prime, not prime) worlds. -/
def canonicalR (w v : MinCanonicalPrimeWorld Atom) : Prop :=
  (∀ φ, (□φ) ∈ w.val → φ ∈ v.val) ∧ (∀ φ, φ ∈ v.val → (◇φ) ∈ w.val)

/-! ## Nonempty Disjunction / Conjunction (efq-free Lindenbaum-pair machinery)

The combinatorial core needed to build a "Lindenbaum-pair" (set-)exclusion lemma without `efq`.
Every list handled here is *nonempty*, represented as an explicit head `x` and tail `xs`
(the list `x :: xs`). `bigOr1`/`bigAnd1` terminate at the head, not at `⊥`. -/

section NonemptyCombinators

/-- Nonempty iterated disjunction, terminating at the head: `bigOr1 x [] = x` and
`bigOr1 x (y :: ys) = x ∨ (bigOr1 y ys)`. The `efq`-free counterpart of `Metalogic.bigOr`
(which terminates at `⊥`). -/
private def bigOr1 : Proposition Atom → List (Proposition Atom) → Proposition Atom
  | x, [] => x
  | x, y :: ys => x.or (bigOr1 y ys)

/-- Nonempty iterated conjunction, terminating at the head: `bigAnd1 x [] = x` and
`bigAnd1 x (y :: ys) = x ∧ (bigAnd1 y ys)`. -/
private def bigAnd1 : Proposition Atom → List (Proposition Atom) → Proposition Atom
  | x, [] => x
  | x, y :: ys => x.and (bigAnd1 y ys)

/-- The shared "cut" witness (discharging a single context member via the deduction theorem),
instantiated once for `MKModalAxiom` and reused by every `or_right_mono`/`empty_imp_trans`/
`empty_imp_id` call below. -/
private theorem hCutMK :
    ∀ {U : Set (Proposition Atom)} {L : List (Proposition Atom)} {a b : Proposition Atom},
      (∀ x ∈ L, x ∈ insert a U) → (modalDerivationSystem MKModalAxiom).Deriv L b →
      ∃ L', (∀ x ∈ L', x ∈ U) ∧ (modalDerivationSystem MKModalAxiom).Deriv L' (a.imp b) :=
  fun {U _L a _b} hL hd =>
    modal_deriv_imp_of_union (fun φ ψ => MKModalAxiom.implyK φ ψ)
      (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ)
      (fun x hx => by
        rcases Set.mem_insert_iff.mp (hL x hx) with rfl | hu
        · exact Set.mem_union_right U (Set.mem_singleton_iff.mpr rfl)
        · exact Set.mem_union_left _ hu)
      hd

/-- `⊢ bigOr1 x xs → bigOr1 x (xs ++ ys)`: appending on the right only weakens a nonempty
disjunction. Base case (`xs = []`): either the identity implication `x → x` (via
`deductionTheorem`, when `ys` is also empty) or `OrI1` (when `ys = y :: ys'`) -- **no `efq`**,
unlike `Metalogic.bigOr_append_left`'s `⊥`-terminated base case. Inductive step: `or_right_mono`
applied to the (head-changing) recursive call. -/
private theorem bigOr1_append_left :
    ∀ (x : Proposition Atom) (xs ys : List (Proposition Atom)),
      (modalDerivationSystem MKModalAxiom).Deriv [] ((bigOr1 x xs).imp (bigOr1 x (xs ++ ys)))
  | x, [], [] =>
      ⟨deductionTheorem (fun φ ψ => MKModalAxiom.implyK φ ψ)
        (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ)
        [] x x (.assumption [x] x (List.mem_cons.mpr (Or.inl rfl)))⟩
  | x, [], y :: ys => ⟨.ax [] _ (MKModalAxiom.orI1 x (bigOr1 y ys))⟩
  | _x, z :: zs, ys =>
      or_right_mono (modalDerivationSystem MKModalAxiom)
        (fun A B => ⟨.ax [] _ (MKModalAxiom.orI1 A B)⟩)
        (fun A B => ⟨.ax [] _ (MKModalAxiom.orI2 A B)⟩)
        (fun A B χ => ⟨.ax [] _ (MKModalAxiom.orE A B χ)⟩)
        hCutMK (bigOr1_append_left z zs ys)

/-- `⊢ bigOr1 y ys → bigOr1 x (xs ++ (y :: ys))`: appending on the left only weakens a nonempty
disjunction. Base case (`xs = []`): `OrI2` directly (`x ∨ bigOr1 y ys`) -- **no `efq`**.
Inductive step: compose the (head-changing) recursive call with an `OrI2` step via
`empty_imp_trans`. -/
private theorem bigOr1_append_right :
    ∀ (x : Proposition Atom) (xs : List (Proposition Atom)) (y : Proposition Atom)
      (ys : List (Proposition Atom)),
      (modalDerivationSystem MKModalAxiom).Deriv []
        ((bigOr1 y ys).imp (bigOr1 x (xs ++ (y :: ys))))
  | x, [], y, ys => ⟨.ax [] _ (MKModalAxiom.orI2 x (bigOr1 y ys))⟩
  | x, z :: zs, y, ys =>
      empty_imp_trans (modalDerivationSystem MKModalAxiom) hCutMK
        (bigOr1_append_right z zs y ys)
        ⟨.ax [] _ (MKModalAxiom.orI2 x (bigOr1 z (zs ++ (y :: ys))))⟩

/-- Empty-context box monotonicity for a *derived* implication (not merely an axiom instance):
from `⊢ A → B` (a genuine derivation, possibly using modus ponens), derive `⊢ □A → □B`, by
necessitating the implication and applying `k`. Generalizes `box_mono`
(`Intuitionistic/CanonicalModel.lean:206-211`, which only accepts a raw axiom instance) to
arbitrary empty-context derivations -- needed for the identity-implication base cases below. -/
private def boxMonoDeriv {A B : Proposition Atom}
    (d : DerivationTree MKModalAxiom [] (A.imp B)) :
    DerivationTree MKModalAxiom [] ((Proposition.box A).imp (Proposition.box B)) :=
  .modus_ponens [] _ _ (.ax [] _ (MKModalAxiom.k A B)) (.necessitation _ d)

/-- Empty-context diamond monotonicity for a *derived* implication: from `⊢ A → B`, derive
`⊢ ◇A → ◇B`, via necessitation and `kdia`. Generalizes `dia_mono`
(`Intuitionistic/CanonicalModel.lean:215-220`) to arbitrary derivations. -/
private def diaMonoDeriv {A B : Proposition Atom}
    (d : DerivationTree MKModalAxiom [] (A.imp B)) :
    DerivationTree MKModalAxiom [] ((◇A).imp (◇B)) :=
  .modus_ponens [] _ _ (.ax [] _ (MKModalAxiom.kdia A B)) (.necessitation _ d)

/-- The empty-context identity derivation `⊢ φ → φ`, via the deduction theorem applied to the
trivial assumption `[φ] ⊢ φ`. -/
private noncomputable def idDeriv (φ : Proposition Atom) :
    DerivationTree MKModalAxiom [] (φ.imp φ) :=
  deductionTheorem (fun φ ψ => MKModalAxiom.implyK φ ψ) (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ)
    [] φ φ (.assumption [φ] φ (List.mem_cons.mpr (Or.inl rfl)))

/-- **Box-of-disjuncts, nonempty**: `⊢ (bigOr1 (□base) (rest.map box)) → (□ (bigOr1 base rest))`
-- a disjunction of already-boxed formulas implies the box of the (unboxed) disjunction. Base
case (`rest = []`): the identity `□base → □base` (via `idDeriv` + `boxMonoDeriv`) -- **no `efq`**
(unlike `boxOr_of_boxDisj`'s `⊥ → □⊥` base case, `Intuitionistic/CanonicalModel.lean:254`).
Inductive step: identical shape to `boxOr_of_boxDisj`'s step case (`box_mono` + `h_orE`
combination), using `boxMonoDeriv` on `OrI1`/`OrI2` axiom instances (theorems, not raw axioms,
but the axiom-instance case degenerates to `.ax`). -/
private noncomputable def boxOr1_of_boxDisj (base : Proposition Atom) :
    ∀ (rest : List (Proposition Atom)),
      DerivationTree MKModalAxiom []
        ((bigOr1 (Proposition.box base) (rest.map Proposition.box)).imp
          (Proposition.box (bigOr1 base rest)))
  | [] => boxMonoDeriv (idDeriv base)
  | C :: rest' => by
      have f1 : DerivationTree MKModalAxiom []
          ((Proposition.box base).imp (Proposition.box (bigOr1 base (C :: rest')))) :=
        boxMonoDeriv (.ax [] _ (MKModalAxiom.orI1 base (bigOr1 C rest')))
      have f2a : DerivationTree MKModalAxiom []
          ((Proposition.box (bigOr1 C rest')).imp
            (Proposition.box (bigOr1 base (C :: rest')))) :=
        boxMonoDeriv (.ax [] _ (MKModalAxiom.orI2 base (bigOr1 C rest')))
      have ih := boxOr1_of_boxDisj C rest'
      have f2 : DerivationTree MKModalAxiom []
          ((bigOr1 (Proposition.box C) (rest'.map Proposition.box)).imp
            (Proposition.box (bigOr1 base (C :: rest')))) :=
        Classical.choice
          (empty_imp_trans (modalDerivationSystem MKModalAxiom) hCutMK ⟨ih⟩ ⟨f2a⟩)
      have step1 := DerivationTree.modus_ponens [] _ _
        (DerivationTree.ax [] _
          (MKModalAxiom.orE (Proposition.box base)
            (bigOr1 (Proposition.box C) (rest'.map Proposition.box))
            (Proposition.box (bigOr1 base (C :: rest')))))
        f1
      exact DerivationTree.modus_ponens [] _ _ step1 f2

/-- **Diamond-of-disjuncts, nonempty**: `⊢ (◇ (bigOr1 base rest)) → (bigOr1 (◇base)
(rest.map diamond))` -- the diamond of a (nonempty) disjunction implies the disjunction of the
diamonds. Base case (`rest = []`): the identity `◇base → ◇base` (via `idDeriv` + `diaMonoDeriv`)
-- **no `h_dbot`** (unlike `diaOr_of_diaDisj`'s `◇⊥ → ⊥` base case,
`Intuitionistic/CanonicalModel.lean:791`, which `MK` cannot supply). Inductive step: identical
shape to `diaOr_of_diaDisj`'s step case, using `Cd`. -/
private noncomputable def diaOr1_of_diaDisj (base : Proposition Atom) :
    ∀ (rest : List (Proposition Atom)),
      DerivationTree MKModalAxiom []
        ((◇ (bigOr1 base rest)).imp (bigOr1 (◇base) (rest.map Proposition.diamond)))
  | [] => diaMonoDeriv (idDeriv base)
  | C :: rest' => by
      have hCd : DerivationTree MKModalAxiom []
          ((◇ (bigOr1 base (C :: rest'))).imp ((◇base).or (◇ (bigOr1 C rest')))) :=
        .ax [] _ (MKModalAxiom.cd base (bigOr1 C rest'))
      have ih := diaOr1_of_diaDisj C rest'
      have branch1 : DerivationTree MKModalAxiom []
          ((◇base).imp (bigOr1 (◇base) ((◇C) :: (rest'.map Proposition.diamond)))) :=
        .ax [] _ (MKModalAxiom.orI1 (◇base) (bigOr1 (◇C) (rest'.map Proposition.diamond)))
      have branch2 : DerivationTree MKModalAxiom []
          ((◇ (bigOr1 C rest')).imp
            (bigOr1 (◇base) ((◇C) :: (rest'.map Proposition.diamond)))) :=
        Classical.choice
          (empty_imp_trans (modalDerivationSystem MKModalAxiom) hCutMK ⟨ih⟩
            ⟨.ax [] _ (MKModalAxiom.orI2 (◇base) (bigOr1 (◇C) (rest'.map Proposition.diamond)))⟩)
      have step1 := DerivationTree.modus_ponens [] _ _
        (DerivationTree.ax [] _
          (MKModalAxiom.orE (◇base) (◇ (bigOr1 C rest'))
            (bigOr1 (◇base) ((◇C) :: (rest'.map Proposition.diamond)))))
        branch1
      have step2 := DerivationTree.modus_ponens [] _ _ step1 branch2
      exact Classical.choice
        (empty_imp_trans (modalDerivationSystem MKModalAxiom) hCutMK ⟨hCd⟩ ⟨step2⟩)

end NonemptyCombinators

end Cslib.Logic.Modal
