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

/-- Combines a *nonempty* list of separately-derived hypotheses `x :: xs` (with leftover context
`Lw`) into a single conjunction hypothesis: `(x::xs) ++ Lw ⊢ ψ` implies
`bigAnd1 x xs :: Lw ⊢ ψ`. Base case (`xs = []`): `bigAnd1 x [] = x`, so the goal is definitionally
the hypothesis itself -- no weakening needed (contrast `unpack_conj_partial`'s base case, which
weakens in an unused `bigAnd []` hypothesis). Inductive step mirrors `unpack_conj_partial`'s. -/
private noncomputable def unpackConj1 :
    ∀ (x : Proposition Atom) (xs Lw : List (Proposition Atom)) (ψ : Proposition Atom),
      DerivationTree MKModalAxiom ((x :: xs) ++ Lw) ψ →
      DerivationTree MKModalAxiom (bigAnd1 x xs :: Lw) ψ
  | _x, [], _Lw, _ψ, d => d
  | x, y :: ys, Lw, ψ, d => by
      have dt : DerivationTree MKModalAxiom ((y :: ys) ++ Lw) (x.imp ψ) :=
        deductionTheorem (fun φ ψ => MKModalAxiom.implyK φ ψ)
          (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) ((y :: ys) ++ Lw) x ψ d
      have ihres : DerivationTree MKModalAxiom (bigAnd1 y ys :: Lw) (x.imp ψ) :=
        unpackConj1 y ys Lw (x.imp ψ) dt
      have ihres0 : DerivationTree MKModalAxiom Lw ((bigAnd1 y ys).imp (x.imp ψ)) :=
        deductionTheorem (fun φ ψ => MKModalAxiom.implyK φ ψ)
          (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) Lw (bigAnd1 y ys) (x.imp ψ) ihres
      have hmem : DerivationTree MKModalAxiom (bigAnd1 x (y :: ys) :: Lw) (bigAnd1 x (y :: ys)) :=
        .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
      have hx : DerivationTree MKModalAxiom (bigAnd1 x (y :: ys) :: Lw) x :=
        .modus_ponens _ (bigAnd1 x (y :: ys)) x
          (.weakening [] _ _ (.ax [] _ (MKModalAxiom.andE1 x (bigAnd1 y ys)))
            (fun _ h => nomatch h))
          hmem
      have hRest : DerivationTree MKModalAxiom (bigAnd1 x (y :: ys) :: Lw) (bigAnd1 y ys) :=
        .modus_ponens _ (bigAnd1 x (y :: ys)) (bigAnd1 y ys)
          (.weakening [] _ _ (.ax [] _ (MKModalAxiom.andE2 x (bigAnd1 y ys)))
            (fun _ h => nomatch h))
          hmem
      have hximpψ : DerivationTree MKModalAxiom (bigAnd1 x (y :: ys) :: Lw) (x.imp ψ) :=
        .modus_ponens _ (bigAnd1 y ys) (x.imp ψ)
          (.weakening Lw _ _ ihres0 (fun z hz => List.mem_cons.mpr (Or.inr hz)))
          hRest
      exact .modus_ponens _ x ψ hximpψ hx

/-- **Diamond/conjunction bridge, nonempty**: `⊢ (◇ (bigAnd1 x xs)) → (bigAnd1 (◇x)
(xs.map diamond))` -- the diamond of a conjunction implies the conjunction of the diamonds (the
VALID monotonicity direction). Base case (`xs = []`): the identity `◇x → ◇x` (via `idDeriv` +
`diaMonoDeriv`) -- **no `efq`** (unlike `dia_bigAnd_to_bigAnd_dia`'s `⊤`-via-`efq` base case,
`Intuitionistic/CanonicalModel.lean:327-331`; report 01 confirmed this base case is not a true
obstruction). Inductive step: identical shape, via `Kdia` + `AndE1`/`AndE2`/`AndI`. -/
private noncomputable def diaBigAnd1ToBigAnd1Dia (x : Proposition Atom) :
    ∀ (xs : List (Proposition Atom)),
      DerivationTree MKModalAxiom []
        ((◇ (bigAnd1 x xs)).imp (bigAnd1 (◇x) (xs.map Proposition.diamond)))
  | [] => diaMonoDeriv (idDeriv x)
  | y :: ys => by
      have f1 : DerivationTree MKModalAxiom [] ((◇ (bigAnd1 x (y :: ys))).imp (◇x)) :=
        diaMonoDeriv (.ax [] _ (MKModalAxiom.andE1 x (bigAnd1 y ys)))
      have f2 : DerivationTree MKModalAxiom []
          ((◇ (bigAnd1 x (y :: ys))).imp (◇ (bigAnd1 y ys))) :=
        diaMonoDeriv (.ax [] _ (MKModalAxiom.andE2 x (bigAnd1 y ys)))
      have ih := diaBigAnd1ToBigAnd1Dia y ys
      have f2' : DerivationTree MKModalAxiom []
          ((◇ (bigAnd1 x (y :: ys))).imp (bigAnd1 (◇y) (ys.map Proposition.diamond))) :=
        Classical.choice (empty_imp_trans (modalDerivationSystem MKModalAxiom) hCutMK ⟨f2⟩ ⟨ih⟩)
      have hXmem :
          DerivationTree MKModalAxiom [◇ (bigAnd1 x (y :: ys))] (◇ (bigAnd1 x (y :: ys))) :=
        .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
      have hdiaX : DerivationTree MKModalAxiom [◇ (bigAnd1 x (y :: ys))] (◇x) :=
        .modus_ponens _ _ _ (.weakening [] _ _ f1 (fun _ h => nomatch h)) hXmem
      have hrest : DerivationTree MKModalAxiom [◇ (bigAnd1 x (y :: ys))]
          (bigAnd1 (◇y) (ys.map Proposition.diamond)) :=
        .modus_ponens _ _ _ (.weakening [] _ _ f2' (fun _ h => nomatch h)) hXmem
      have andI_ax : DerivationTree MKModalAxiom [◇ (bigAnd1 x (y :: ys))]
          ((◇x).imp ((bigAnd1 (◇y) (ys.map Proposition.diamond)).imp
            ((◇x).and (bigAnd1 (◇y) (ys.map Proposition.diamond))))) :=
        .weakening [] _ _
          (.ax [] _ (MKModalAxiom.andI (◇x) (bigAnd1 (◇y) (ys.map Proposition.diamond))))
          (fun _ h => nomatch h)
      have step1 := DerivationTree.modus_ponens _ _ _ andI_ax hdiaX
      have step2 := DerivationTree.modus_ponens _ _ _ step1 hrest
      exact deductionTheorem (fun φ ψ => MKModalAxiom.implyK φ ψ)
        (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) [] (◇ (bigAnd1 x (y :: ys))) _ step2

/-- `bigAnd1 x xs ∈ u.val` whenever `x` and every element of `xs` are in `u.val` (using `AndI`
and the deductive closure of the quasi-prime theory `u.val`). Base case (`xs = []`) is
definitional (`bigAnd1 x [] = x`) -- no `AndI`/`efq` step needed, unlike `bigAnd_mem_u`'s
`efq`-based `⊤`-membership base case. -/
private theorem bigAnd1_mem_u {u : MinCanonicalPrimeWorld Atom} (x : Proposition Atom) :
    ∀ (xs : List (Proposition Atom)), x ∈ u.val → (∀ A ∈ xs, A ∈ u.val) →
      bigAnd1 x xs ∈ u.val
  | [], hx, _ => hx
  | y :: ys, hx, hxs => by
      have hy : y ∈ u.val := hxs y (List.mem_cons.mpr (Or.inl rfl))
      have hRest : bigAnd1 y ys ∈ u.val :=
        bigAnd1_mem_u y ys hy (fun B hB => hxs B (List.mem_cons.mpr (Or.inr hB)))
      have h1 : DerivationTree MKModalAxiom [x, bigAnd1 y ys] x :=
        .assumption _ x (List.mem_cons.mpr (Or.inl rfl))
      have h2 : DerivationTree MKModalAxiom [x, bigAnd1 y ys] (bigAnd1 y ys) :=
        .assumption _ (bigAnd1 y ys) (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      have hax : DerivationTree MKModalAxiom [x, bigAnd1 y ys]
          (x.imp ((bigAnd1 y ys).imp (x.and (bigAnd1 y ys)))) :=
        .weakening [] _ _ (.ax [] _ (MKModalAxiom.andI x (bigAnd1 y ys))) (fun _ h => nomatch h)
      have hderiv : DerivationTree MKModalAxiom [x, bigAnd1 y ys] (x.and (bigAnd1 y ys)) :=
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

/-! ## Nonempty Lindenbaum-Pair Exclusion

The efq-free "Lindenbaum-pair" set-exclusion lemma: given a deductively-closed `S` deriving no
*nonempty* finite disjunction of `E`, there is a quasi-prime `T ⊇ S` still deriving no nonempty
finite disjunction of `E`. This is the direct, `efq`-free analogue of
`Metalogic.prime_set_exclusion`/`modal_set_exclusion` (`Intuitionistic/CanonicalModel.lean:585`),
specialized to `Cons := fun _ => True` (no consistency predicate is threaded -- quasi-prime
worlds carry none, so the Zorn argument below never needs a `¬Cons` case split, unlike the
generic framework). -/

section NonemptyPairExclusion

/-- `T` derives no *nonempty* finite disjunction of `E`: for every `x ∈ E` and every list `xs`
drawn from `E`, `bigOr1 x xs ∉ T`. The nonempty-list analogue of `Metalogic.DerivExcludes`
(`Foundations/Logic/Metalogic/PrimeExclusion.lean:328`), which never touches the empty-list
(`⊥`) case. -/
private def DerivExcludes1 (T E : Set (Proposition Atom)) : Prop :=
  ∀ (x : Proposition Atom) (xs : List (Proposition Atom)),
    x ∈ E → (∀ y ∈ xs, y ∈ E) → bigOr1 x xs ∉ T

/-- The collection of deductively-closed, `E`-excluding (nonempty-disjunction) supersets of `S`.
The Zorn domain for `quasi_prime_set_exclusion1`. -/
private def QPExcludingSupersets (S E : Set (Proposition Atom)) : Set (Set (Proposition Atom)) :=
  {T | S ⊆ T ∧ Metalogic.DeductivelyClosed (modalDerivationSystem MKModalAxiom) T ∧
    DerivExcludes1 T E}

private theorem qp_excluding_base_mem {S E : Set (Proposition Atom)}
    (hS : Metalogic.DeductivelyClosed (modalDerivationSystem MKModalAxiom) S)
    (h_excl : DerivExcludes1 S E) : S ∈ QPExcludingSupersets S E :=
  ⟨Set.Subset.refl S, hS, h_excl⟩

private theorem qp_excluding_chain_union {S E : Set (Proposition Atom)}
    {C : Set (Set (Proposition Atom))}
    (hCsub : C ⊆ QPExcludingSupersets S E)
    (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty) :
    (⋃₀ C) ∈ QPExcludingSupersets S E := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨T, hT⟩ := hCne
    exact Set.mem_sUnion.mpr ⟨T, hT, (hCsub hT).1 hx⟩
  · exact deductivelyClosed_chain_union (modalDerivationSystem MKModalAxiom) hchain hCne
      (fun T hTC => (hCsub hTC).2.1)
  · intro x xs hxE hxsE hmem
    obtain ⟨T, hTC, hTmem⟩ := Set.mem_sUnion.mp hmem
    exact (hCsub hTC).2.2 x xs hxE hxsE hTmem

/-- **Nonempty Lindenbaum-pair exclusion** (efq-free): given a deductively-closed `S` with
`DerivExcludes1 S E`, there is a quasi-prime `T ⊇ S` with `DerivExcludes1 T E`. Proved by Zorn's
lemma over `QPExcludingSupersets`; the disjunction property of the maximal element `T` is proved
exactly as `set_maximal_is_prime`'s (`PrimeExclusion.lean:428`) but combining the two branches'
witnesses via `bigOr1_append_left`/`bigOr1_append_right` instead of
`bigOr_append_left`/`bigOr_append_right` -- no `efq`, and no `Cons`/inconsistency case split
(quasi-prime worlds carry no consistency predicate, so `insert X T`'s closure is *always*
admissible; the generic framework's `¬Cons` branch never arises here). -/
private theorem quasi_prime_set_exclusion1 {S E : Set (Proposition Atom)}
    (hS : Metalogic.DeductivelyClosed (modalDerivationSystem MKModalAxiom) S)
    (h_excl : DerivExcludes1 S E) :
    ∃ T, S ⊆ T ∧ QuasiPrime (MKModalAxiom (Atom := Atom)) T ∧ DerivExcludes1 T E := by
  obtain ⟨T, hST, hTmax⟩ := zorn_subset_nonempty (QPExcludingSupersets S E)
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
        (modalDerivationSystem MKModalAxiom).Deriv L0 (bigOr1 x0 xs0) := by
    intro X hXT
    have hTX_sup : T ⊆ modalDeductiveClosure MKModalAxiom (insert X T) :=
      Set.Subset.trans (Set.subset_insert X T) (modal_subset_deductive_closure MKModalAxiom _)
    have hX_in : X ∈ modalDeductiveClosure MKModalAxiom (insert X T) :=
      modal_subset_deductive_closure MKModalAxiom _ (Set.mem_insert X T)
    have hnotmem :
        modalDeductiveClosure MKModalAxiom (insert X T) ∉ QPExcludingSupersets S E := by
      intro hmem
      exact hXT ((hTmax.eq_of_ge hmem hTX_sup) ▸ hX_in)
    have h_sub_cl : S ⊆ modalDeductiveClosure MKModalAxiom (insert X T) :=
      hST.trans hTX_sup
    have h_closed_cl : Metalogic.DeductivelyClosed (modalDerivationSystem MKModalAxiom)
        (modalDeductiveClosure MKModalAxiom (insert X T)) :=
      fun L φ hL hd =>
        modalDeductiveClosure_closed (fun φ ψ => MKModalAxiom.implyK φ ψ)
          (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) L φ hL hd
    have h_fail : ¬ DerivExcludes1 (modalDeductiveClosure MKModalAxiom (insert X T)) E := by
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
      (modalDerivationSystem MKModalAxiom).Deriv LA' (A.imp χ) := by
    have d1w : DerivationTree MKModalAxiom (A :: LA0) (bigOr1 xA xsA) :=
      DerivationTree.weakening LA0 _ _ dLA0 (fun x hx => List.mem_cons.mpr (Or.inr hx))
    obtain ⟨d2⟩ : (modalDerivationSystem MKModalAxiom).Deriv [] ((bigOr1 xA xsA).imp χ) :=
      bigOr1_append_left xA xsA (xB :: xsB)
    have d2w : DerivationTree MKModalAxiom (A :: LA0) ((bigOr1 xA xsA).imp χ) :=
      DerivationTree.weakening [] _ _ d2 (fun _ h => nomatch h)
    have d3 : DerivationTree MKModalAxiom (A :: LA0) χ :=
      DerivationTree.modus_ponens _ _ _ d2w d1w
    exact hCutMK (U := T) (L := A :: LA0) (a := A) (b := χ)
      (fun x hx => by
        rcases List.mem_cons.mp hx with heq | hx'
        · exact heq ▸ Set.mem_insert A T
        · exact hLA0_sub x hx')
      ⟨d3⟩
  have hBchi : ∃ LB', (∀ x ∈ LB', x ∈ T) ∧
      (modalDerivationSystem MKModalAxiom).Deriv LB' (B.imp χ) := by
    have d1w : DerivationTree MKModalAxiom (B :: LB0) (bigOr1 xB xsB) :=
      DerivationTree.weakening LB0 _ _ dLB0 (fun x hx => List.mem_cons.mpr (Or.inr hx))
    obtain ⟨d2⟩ : (modalDerivationSystem MKModalAxiom).Deriv [] ((bigOr1 xB xsB).imp χ) :=
      bigOr1_append_right xA xsA xB xsB
    have d2w : DerivationTree MKModalAxiom (B :: LB0) ((bigOr1 xB xsB).imp χ) :=
      DerivationTree.weakening [] _ _ d2 (fun _ h => nomatch h)
    have d3 : DerivationTree MKModalAxiom (B :: LB0) χ :=
      DerivationTree.modus_ponens _ _ _ d2w d1w
    exact hCutMK (U := T) (L := B :: LB0) (a := B) (b := χ)
      (fun x hx => by
        rcases List.mem_cons.mp hx with heq | hx'
        · exact heq ▸ Set.mem_insert B T
        · exact hLB0_sub x hx')
      ⟨d3⟩
  obtain ⟨LA', hLA'_sub, hLA'_deriv⟩ := hAchi
  obtain ⟨LB', hLB'_sub, hLB'_deriv⟩ := hBchi
  obtain ⟨dA'⟩ := hLA'_deriv
  obtain ⟨dB'⟩ := hLB'_deriv
  have hOrMem : DerivationTree MKModalAxiom (A.or B :: LA' ++ LB') (A.or B) :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hAchi' : DerivationTree MKModalAxiom (A.or B :: LA' ++ LB') (A.imp χ) :=
    .weakening LA' _ _ dA'
      (fun x hx => List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl hx))))
  have hBchi' : DerivationTree MKModalAxiom (A.or B :: LA' ++ LB') (B.imp χ) :=
    .weakening LB' _ _ dB'
      (fun x hx => List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hx))))
  have hOrEax : DerivationTree MKModalAxiom (A.or B :: LA' ++ LB')
      ((A.imp χ).imp ((B.imp χ).imp ((A.or B).imp χ))) :=
    .weakening [] _ _ (.ax [] _ (MKModalAxiom.orE A B χ)) (fun _ h => nomatch h)
  have hstep1 : DerivationTree MKModalAxiom (A.or B :: LA' ++ LB')
      ((B.imp χ).imp ((A.or B).imp χ)) :=
    .modus_ponens _ _ _ hOrEax hAchi'
  have hstep2 : DerivationTree MKModalAxiom (A.or B :: LA' ++ LB') ((A.or B).imp χ) :=
    .modus_ponens _ _ _ hstep1 hBchi'
  have hχderiv : DerivationTree MKModalAxiom (A.or B :: LA' ++ LB') χ :=
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

/-! ## Box Witness -/

section CanonicalBoxWitness

/-- Extracts the bare witnesses `bs` of a nonempty list `xs` drawn from
`{χ | ∃ B, χ = □B ∧ B ∉ u.val}`, so that `xs = bs.map box` with every element of `bs` excluded
from `u.val`. List-only, `efq`-free by construction (mirrors `extract_box_list`,
`Intuitionistic/CanonicalModel.lean:189-202`). -/
private theorem extract_box_list1 (u : MinCanonicalPrimeWorld Atom) :
    ∀ (xs : List (Proposition Atom)), (∀ x ∈ xs, ∃ B, x = (□B) ∧ B ∉ u.val) →
      ∃ bs : List (Proposition Atom), xs = bs.map Proposition.box ∧ ∀ B ∈ bs, B ∉ u.val
  | [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | x :: xs, hl => by
      obtain ⟨B, hxeq, hBnu⟩ := hl x (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨bs, heq, hbs⟩ :=
        extract_box_list1 u xs (fun y hy => hl y (List.mem_cons.mpr (Or.inr hy)))
      refine ⟨B :: bs, ?_, ?_⟩
      · rw [hxeq, heq, List.map_cons]
      · intro C hC
        rcases List.mem_cons.mp hC with rfl | hC'
        · exact hBnu
        · exact hbs C hC'

/-- Splits a derivation context `L` (drawn from `w.val ∪ {◇A | A ∈ u.val}`) into the sublist of
`w.val`-members `Lw` and the bare diamond witnesses `As` (each `A ∈ u.val`), such that every
element of `L` lies in `(As.map diamond) ++ Lw`. List-only, `efq`-free by construction (mirrors
`extract_split`, `Intuitionistic/CanonicalModel.lean:151-185`). -/
private theorem extract_split1 (w u : MinCanonicalPrimeWorld Atom) :
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

/-- If `u.val` has the disjunction property and `bigOr1 x0 xs0 ∈ u.val`, some disjunct
(`x0` or a member of `xs0`) is in `u.val`. -/
private theorem bigOr1_mem_disjunct (u : MinCanonicalPrimeWorld Atom) :
    ∀ (x0 : Proposition Atom) (xs0 : List (Proposition Atom)), bigOr1 x0 xs0 ∈ u.val →
      x0 ∈ u.val ∨ ∃ C ∈ xs0, C ∈ u.val
  | x0, [], hmem => Or.inl hmem
  | x0, y :: ys, hmem => by
      rcases u.property.disj hmem with h | h
      · exact Or.inl h
      · rcases bigOr1_mem_disjunct u y ys h with h' | ⟨C, hC, hCu⟩
        · exact Or.inr ⟨y, List.mem_cons.mpr (Or.inl rfl), h'⟩
        · exact Or.inr ⟨C, List.mem_cons.mpr (Or.inr hC), hCu⟩

/-- **Box witness underivability, nonempty** (efq-free analogue of
`box_witness_pair_underivable`, `Intuitionistic/CanonicalModel.lean:431`): no nonempty
`bigOr1`-disjunction of `Σ := {χ | ∃ B, χ = □B ∧ B ∉ u.val}` is a member of the deductive
closure of `Γ := w.val ∪ {χ | ∃ A, χ = ◇A ∧ A ∈ u.val}`, given the box clause
`∀ψ, □ψ ∈ w.val → ψ ∈ u.val`. Case-splits on whether the diamond-witness list `As`
(extracted from a hypothetical derivation) is empty (direct via `h_wu`) or nonempty (combine via
`unpackConj1` + `diaBigAnd1ToBigAnd1Dia` + `Idb`, exactly as `box_witness_pair_underivable`'s
single-combined-diamond step, but never touching `efq`/`bigAnd []`). -/
private theorem box_witness_pair_underivable1 {w u : MinCanonicalPrimeWorld Atom}
    (h_wu : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ u.val) :
    DerivExcludes1
      (modalDeductiveClosure MKModalAxiom (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ u.val}))
      {χ | ∃ B, χ = (□B) ∧ B ∉ u.val} := by
  intro x0 xs0 hx0Sig hxs0Sig hmem
  obtain ⟨B0, hB0eq, hB0nu⟩ := hx0Sig
  obtain ⟨bs, hbseq, hbsnu⟩ := extract_box_list1 u xs0 hxs0Sig
  obtain ⟨L, hLΓ, hd⟩ := hmem
  obtain ⟨d⟩ := hd
  subst hB0eq
  have bridge0 := boxOr1_of_boxDisj B0 bs
  rw [hbseq] at d
  have d_box : DerivationTree MKModalAxiom L (Proposition.box (bigOr1 B0 bs)) :=
    DerivationTree.modus_ponens L _ _
      (DerivationTree.weakening [] L _ bridge0 (fun _ h => nomatch h)) d
  have hLΓ' : ∀ x ∈ L, x ∈ w.val ∨ ∃ A, x = (◇A) ∧ A ∈ u.val := fun x hx => hLΓ x hx
  obtain ⟨Lw, As, hLw, hAs, hsub⟩ := extract_split1 w u L hLΓ'
  have d_box' : DerivationTree MKModalAxiom ((As.map Proposition.diamond) ++ Lw)
      (Proposition.box (bigOr1 B0 bs)) :=
    DerivationTree.weakening L _ _ d_box hsub
  have hcontra : bigOr1 B0 bs ∈ u.val → False := by
    intro hmemU
    rcases bigOr1_mem_disjunct u B0 bs hmemU with h | ⟨C, hC, hCu⟩
    · exact hB0nu h
    · exact hbsnu C hC hCu
  cases As with
  | nil =>
      have d_box'' : DerivationTree MKModalAxiom Lw (Proposition.box (bigOr1 B0 bs)) := d_box'
      exact hcontra (h_wu _ (w.property.closed Lw _ hLw ⟨d_box''⟩))
  | cons x xs =>
      have d_box'' : DerivationTree MKModalAxiom (((◇x) :: xs.map Proposition.diamond) ++ Lw)
          (Proposition.box (bigOr1 B0 bs)) := d_box'
      have d_unpack : DerivationTree MKModalAxiom (bigAnd1 (◇x) (xs.map Proposition.diamond) :: Lw)
          (Proposition.box (bigOr1 B0 bs)) :=
        unpackConj1 (◇x) (xs.map Proposition.diamond) Lw _ d_box''
      have d_disch : DerivationTree MKModalAxiom Lw
          ((bigAnd1 (◇x) (xs.map Proposition.diamond)).imp (Proposition.box (bigOr1 B0 bs))) :=
        deductionTheorem (fun φ ψ => MKModalAxiom.implyK φ ψ)
          (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) Lw
          (bigAnd1 (◇x) (xs.map Proposition.diamond)) (Proposition.box (bigOr1 B0 bs)) d_unpack
      have hM : (bigAnd1 (◇x) (xs.map Proposition.diamond)).imp (Proposition.box (bigOr1 B0 bs))
          ∈ w.val :=
        w.property.closed Lw _ hLw ⟨d_disch⟩
      have bridge1 := diaBigAnd1ToBigAnd1Dia x xs
      set X : Proposition Atom := ◇ (bigAnd1 x xs) with hXdef
      set M : Proposition Atom :=
        (bigAnd1 (◇x) (xs.map Proposition.diamond)).imp (Proposition.box (bigOr1 B0 bs))
        with hMdef
      have step : DerivationTree MKModalAxiom [X, M] (Proposition.box (bigOr1 B0 bs)) := by
        have hXmem : DerivationTree MKModalAxiom [X, M] X :=
          .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
        have hMmem : DerivationTree MKModalAxiom [X, M] M :=
          .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        have hBD : DerivationTree MKModalAxiom [X, M]
            (bigAnd1 (◇x) (xs.map Proposition.diamond)) :=
          .modus_ponens _ _ _ (.weakening [] _ _ bridge1 (fun _ h => nomatch h)) hXmem
        exact .modus_ponens _ _ _ hMmem hBD
      have step_disch : DerivationTree MKModalAxiom [M]
          (X.imp (Proposition.box (bigOr1 B0 bs))) :=
        deductionTheorem (fun φ ψ => MKModalAxiom.implyK φ ψ)
          (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) [M] X (Proposition.box (bigOr1 B0 bs)) step
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
            (.ax _ _ (MKModalAxiom.idb (bigAnd1 x xs) (bigOr1 B0 bs)))
            (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
      have hInU : (bigAnd1 x xs).imp (bigOr1 B0 bs) ∈ u.val := h_wu _ hBoxImp
      have hBigAndXsU : bigAnd1 x xs ∈ u.val :=
        bigAnd1_mem_u x xs (hAs x (List.mem_cons.mpr (Or.inl rfl)))
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

/-- **Box Witness**: from `(□φ) ∉ w.val`, produces `w' ≥ w` (a seeded quasi-prime extension)
and a quasi-prime `u` with `canonicalR w' u` and `φ ∉ u.val`. Step 1 builds `u` directly via
`box_refuting_theory` (`SegmentLindenbaum.lean:168`, efq-free) as the quasi-prime extension of
`boxInv w.val` omitting `φ`; Step 2 builds `w'` via `quasi_prime_set_exclusion1`
(this file), seeded with `w.val ∪ {◇A | A ∈ u.val}` and excluded from `{□B | B ∉ u.val}` via
`box_witness_pair_underivable1`. Mirrors `canonical_box_witness`
(`Intuitionistic/CanonicalModel.lean:636`) but with neither `efq` nor a consistency
side-condition. -/
theorem min_canonical_box_witness {w : MinCanonicalPrimeWorld Atom} {φ : Proposition Atom}
    (h_notbox : (□φ) ∉ w.val) :
    ∃ w' u : MinCanonicalPrimeWorld Atom, w ≤ w' ∧ canonicalR w' u ∧ φ ∉ u.val := by
  obtain ⟨Uval, hUsup, hUqp, hUphi⟩ :=
    box_refuting_theory (fun φ ψ => MKModalAxiom.implyK φ ψ)
      (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) (fun A B χ => MKModalAxiom.orE A B χ)
      (fun φ ψ => MKModalAxiom.k φ ψ) w.property h_notbox
  let u : MinCanonicalPrimeWorld Atom := ⟨Uval, hUqp⟩
  have hSu : ∀ ψ, (□ψ) ∈ w.val → ψ ∈ u.val := fun ψ hψ => hUsup hψ
  have hexcl := box_witness_pair_underivable1 hSu
  have hSclosed : Metalogic.DeductivelyClosed (modalDerivationSystem MKModalAxiom)
      (modalDeductiveClosure MKModalAxiom (w.val ∪ {χ | ∃ A, χ = (◇A) ∧ A ∈ u.val})) :=
    fun L φ' hL hd =>
      modalDeductiveClosure_closed (fun φ ψ => MKModalAxiom.implyK φ ψ)
        (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) L φ' hL hd
  obtain ⟨Tval, hTsup, hTqp, hTexcl⟩ := quasi_prime_set_exclusion1 hSclosed hexcl
  let w' : MinCanonicalPrimeWorld Atom := ⟨Tval, hTqp⟩
  have hw_le_w' : w ≤ w' := fun x hx =>
    hTsup (modal_subset_deductive_closure MKModalAxiom _ (Set.mem_union_left _ hx))
  have hdia_clause : ∀ ψ, ψ ∈ u.val → (◇ψ) ∈ w'.val := fun ψ hψ =>
    hTsup (modal_subset_deductive_closure MKModalAxiom _
      (Set.mem_union_right _ ⟨ψ, rfl, hψ⟩))
  have hbox_clause : ∀ ψ, (□ψ) ∈ w'.val → ψ ∈ u.val := by
    intro ψ hψ_mem
    by_contra hψ_notU
    exact (hTexcl (□ψ) [] ⟨ψ, rfl, hψ_notU⟩ (fun _ h => nomatch h)) hψ_mem
  exact ⟨w', u, hw_le_w', ⟨hbox_clause, hdia_clause⟩, hUphi⟩

end CanonicalBoxWitness

end Cslib.Logic.Modal
