/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5
public import Cslib.Foundations.Logic.Metalogic.ProofSystemMorphism
public import Cslib.Logics.Modal.Metalogic.InterSystem.LiftViaMorphism

/-! # `CS5` Box-Backward via a Doubled-Atom Combined System

This module attempts to close the one open sub-problem left by `CS5.lean` — the truth lemma's
box-backward case, `cs5_box_backward` — via the *doubled-atom combined-system* repair designed in
`probes/cs5-pair-primeness.lean` (task 509 Phase 8) and assessed in
`specs/512_cs5_box_backward_atom_sum_completeness/reports/01_box-backward-atom-sum.md`.

## Design

The box-backward case needs a *simultaneous* pair `(H', T)` of quasi-prime theories with
`H ⊆ H'`, `boxInv H' ⊆ T`, `boxInv T ⊆ H'`, `□A ∉ H'`, `A ∉ T`. Rather than building `H'` and `T`
as two interacting Zorn constructions (task 509 Phase 8-10's blocker: the cross-condition
invariant `boxInv X ⊆ Y` is not closure-stable for a single-set primeness engine), this module
encodes the pair as a **single** prime theory over the doubled atom space `Atom ⊕ Atom`.
`H'`-formulas are tagged via `τL := Proposition.map Sum.inl`, `T`-formulas via
`τR := Proposition.map Sum.inr`, under a combined axiom system `CS5Combined` that adds the two
cross-condition implications as **axioms**, so deductive closure preserves them by construction.

## Main Definitions (Phase 2)

- `CS5Combined`: the combined axiom system over `Proposition (Atom ⊕ Atom)` — all 17
  `CS5ModalAxiom` schemata (via `base`) plus `crossLR`/`crossRL`.
- `cs5_axiom_relabel`: `CS5ModalAxiom φ → CS5ModalAxiom (φ.map f)` for any atom relabeling `f`.
- `τL`/`τR`: the `ProofSigHom`s tagging a `CS5ModalAxiom`-derivation as `CS5Combined`-derivable
  after relabeling via `Sum.inl`/`Sum.inr`.
- `cs5_lift_toDerivationTree_L`/`_R`: the `DerivationTree` transport corollaries, obtained as
  `ofDeriv (Metalogic.Deriv.map τL (toDeriv d))` — a corollary of the task-419
  `Metalogic.Deriv.map` machinery, not new infrastructure.

## References

* [L. Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics*][Pacheco2024] — source of
  the pair-construction *technique* (Lemma 18's Zorn skeleton only; its primeness step, Lemma 16,
  is unsound for a quasi-prime poset-maximal set and is **not** transcribed here — see
  `probes/cs5-pair-primeness.lean` and the task 512 research report for the confirmation).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Metalogic

universe u

variable {Atom : Type u}

/-! ## The Combined Axiom System -/

/-- The combined derivation system on the doubled atom space `Atom ⊕ Atom`: all 17
`CS5ModalAxiom` schemata (via `base`, re-declared at `Atom ⊕ Atom`) plus two cross-condition
axioms internalizing the box-backward pair invariants:
- `crossLR B : □(τL B) → τR B` (internalizes `boxInv H' ⊆ T`);
- `crossRL B : □(τR B) → τL B` (internalizes `boxInv T ⊆ H'`).

Because these are **axioms** (not external set inclusions), deductive closure preserves them
by construction (via modus ponens) — this is what kills the task 509 Phase 8 blocker that
`Cons_Y(Z) := boxInv Z ⊆ Y` was not closure-stable for a single-set primeness engine. -/
inductive CS5Combined : Proposition (Atom ⊕ Atom) → Prop where
  /-- Every `CS5ModalAxiom` instance (over the doubled atom space) is a `CS5Combined` instance. -/
  | base {φ : Proposition (Atom ⊕ Atom)} (h : CS5ModalAxiom φ) : CS5Combined φ
  /-- Cross-condition axiom internalizing `boxInv H' ⊆ T`. -/
  | crossLR (B : Proposition Atom) :
      CS5Combined ((Proposition.box (B.map Sum.inl)).imp (B.map Sum.inr))
  /-- Cross-condition axiom internalizing `boxInv T ⊆ H'`. -/
  | crossRL (B : Proposition Atom) :
      CS5Combined ((Proposition.box (B.map Sum.inr)).imp (B.map Sum.inl))

/-! ## Atom Relabeling Commutes with `CS5ModalAxiom` -/

/-- Relabeling the atoms of a `CS5ModalAxiom` instance along any `f : Atom → Atom'` yields another
`CS5ModalAxiom` instance. Each of the 17 cases is discharged definitionally: `Proposition.map f`
commutes with every connective (Phase 1's `@[simp]` lemmas, all `rfl`), so the relabeled formula is
*syntactically* the same axiom schema instantiated at the relabeled sub-formulas. -/
theorem cs5_axiom_relabel {Atom' : Type u} (f : Atom → Atom') {φ : Proposition Atom}
    (h : CS5ModalAxiom φ) : CS5ModalAxiom (φ.map f) := by
  cases h with
  | implyK φ ψ => exact CS5ModalAxiom.implyK (φ.map f) (ψ.map f)
  | implyS φ ψ χ => exact CS5ModalAxiom.implyS (φ.map f) (ψ.map f) (χ.map f)
  | efq φ => exact CS5ModalAxiom.efq (φ.map f)
  | andI φ ψ => exact CS5ModalAxiom.andI (φ.map f) (ψ.map f)
  | andE1 φ ψ => exact CS5ModalAxiom.andE1 (φ.map f) (ψ.map f)
  | andE2 φ ψ => exact CS5ModalAxiom.andE2 (φ.map f) (ψ.map f)
  | orI1 φ ψ => exact CS5ModalAxiom.orI1 (φ.map f) (ψ.map f)
  | orI2 φ ψ => exact CS5ModalAxiom.orI2 (φ.map f) (ψ.map f)
  | orE φ ψ χ => exact CS5ModalAxiom.orE (φ.map f) (ψ.map f) (χ.map f)
  | k φ ψ => exact CS5ModalAxiom.k (φ.map f) (ψ.map f)
  | kdia φ ψ => exact CS5ModalAxiom.kdia (φ.map f) (ψ.map f)
  | tBox φ => exact CS5ModalAxiom.tBox (φ.map f)
  | tDia φ => exact CS5ModalAxiom.tDia (φ.map f)
  | fourBox φ => exact CS5ModalAxiom.fourBox (φ.map f)
  | fourDia φ => exact CS5ModalAxiom.fourDia (φ.map f)
  | bBox φ => exact CS5ModalAxiom.bBox (φ.map f)
  | bDia φ => exact CS5ModalAxiom.bDia (φ.map f)

/-! ## The `τL`/`τR` Proof-System Morphisms -/

/-- The `τL` proof-system morphism: tags a `CS5ModalAxiom`-derivation with `Sum.inl`, landing in
`CS5Combined`. Corollary of `Metalogic.Deriv.map` (task 419) — the formula map `g` changes the
underlying atom type, exactly as the Bimodal `liftFormula`-based morphism does. -/
def τL : ProofSigHom (modalSig (@CS5ModalAxiom Atom)) (modalSig (@CS5Combined Atom)) where
  g := Proposition.map Sum.inl
  g_imp := fun _ _ => rfl
  axMap := fun _ h => ⟨CS5Combined.base (cs5_axiom_relabel Sum.inl h.down)⟩
  clMap := fun m hm => by
    obtain rfl := List.mem_singleton.mp hm
    exact ⟨Proposition.box, List.mem_singleton.mpr rfl, fun _ => rfl⟩

/-- The `τR` proof-system morphism: tags a `CS5ModalAxiom`-derivation with `Sum.inr`, landing in
`CS5Combined`. Symmetric to `τL`. -/
def τR : ProofSigHom (modalSig (@CS5ModalAxiom Atom)) (modalSig (@CS5Combined Atom)) where
  g := Proposition.map Sum.inr
  g_imp := fun _ _ => rfl
  axMap := fun _ h => ⟨CS5Combined.base (cs5_axiom_relabel Sum.inr h.down)⟩
  clMap := fun m hm => by
    obtain rfl := List.mem_singleton.mp hm
    exact ⟨Proposition.box, List.mem_singleton.mpr rfl, fun _ => rfl⟩

/-! ## `DerivationTree` Transport -/

/-- Transport a `CS5ModalAxiom`-derivation to its `τL`-tagged `CS5Combined`-derivation, via
`ofDeriv (Metalogic.Deriv.map τL (toDeriv d))` — the universal lift, not new infrastructure. -/
noncomputable def cs5_lift_toDerivationTree_L {Γ : List (Proposition Atom)}
    {φ : Proposition Atom} (d : DerivationTree CS5ModalAxiom Γ φ) :
    DerivationTree CS5Combined (Γ.map (Proposition.map Sum.inl)) (φ.map Sum.inl) :=
  ofDeriv (Metalogic.Deriv.map τL (toDeriv d))

/-- Transport a `CS5ModalAxiom`-derivation to its `τR`-tagged `CS5Combined`-derivation. -/
noncomputable def cs5_lift_toDerivationTree_R {Γ : List (Proposition Atom)}
    {φ : Proposition Atom} (d : DerivationTree CS5ModalAxiom Γ φ) :
    DerivationTree CS5Combined (Γ.map (Proposition.map Sum.inr)) (φ.map Sum.inr) :=
  ofDeriv (Metalogic.Deriv.map τR (toDeriv d))

/-- `Deriv`-level (Prop wrapper) transport of the `τL`-tagged lift, for use with
`modalDeductiveClosure`/`DerivExcludes`, which are stated at the `Deriv` (not `DerivationTree`)
level. -/
theorem cs5_lift_deriv_L {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : Deriv CS5ModalAxiom Γ φ) :
    Deriv CS5Combined (Γ.map (Proposition.map Sum.inl)) (φ.map Sum.inl) :=
  let ⟨d⟩ := h
  ⟨cs5_lift_toDerivationTree_L d⟩

/-- `Deriv`-level (Prop wrapper) transport of the `τR`-tagged lift. -/
theorem cs5_lift_deriv_R {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : Deriv CS5ModalAxiom Γ φ) :
    Deriv CS5Combined (Γ.map (Proposition.map Sum.inr)) (φ.map Sum.inr) :=
  let ⟨d⟩ := h
  ⟨cs5_lift_toDerivationTree_R d⟩

end Cslib.Logic.Modal

end
