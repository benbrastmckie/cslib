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
- `cs5LiftToDerivationTreeL`/`_R`: the `DerivationTree` transport corollaries, obtained as
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
noncomputable def cs5LiftToDerivationTreeL {Γ : List (Proposition Atom)}
    {φ : Proposition Atom} (d : DerivationTree CS5ModalAxiom Γ φ) :
    DerivationTree CS5Combined (Γ.map (Proposition.map Sum.inl)) (φ.map Sum.inl) :=
  ofDeriv (Metalogic.Deriv.map τL (toDeriv d))

/-- Transport a `CS5ModalAxiom`-derivation to its `τR`-tagged `CS5Combined`-derivation. -/
noncomputable def cs5LiftToDerivationTreeR {Γ : List (Proposition Atom)}
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
  ⟨cs5LiftToDerivationTreeL d⟩

/-- `Deriv`-level (Prop wrapper) transport of the `τR`-tagged lift. -/
theorem cs5_lift_deriv_R {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : Deriv CS5ModalAxiom Γ φ) :
    Deriv CS5Combined (Γ.map (Proposition.map Sum.inr)) (φ.map Sum.inr) :=
  let ⟨d⟩ := h
  ⟨cs5LiftToDerivationTreeR d⟩

/-! ## The Atom-Collapse Projection (Phase 3, route 2)

The `τL`/`τR` morphisms *tag* a `CS5ModalAxiom`-derivation into `CS5Combined`. The **collapse**
morphism `τ0` goes the other way: it identifies both copies of `Atom` in `Atom ⊕ Atom` via
`Sum.elim id id`, projecting any `CS5Combined`-derivation back down to a `CS5ModalAxiom`-
derivation. Crucially, `crossLR`/`crossRL` project onto the *same* target `CS5ModalAxiom.tBox`
instance (`□B → B`): once the `τL`/`τR` tagging is erased, both cross axioms collapse to the
reflexivity axiom `T`. This gives, for free, the two easiest of the four seed-exclusion
obligations of `cs5Combined_seed_excludes` (report 02 §5's "naive collapse" finding, sharpened
here into a landed morphism reusing the `τL`/`τR` `Deriv.map` machinery, not new
infrastructure): `⊥` and `τL(□A)` cannot leak into the combined closure of `τL '' H`, since
collapsing any such derivation yields `⊥ ∈ H` / `□A ∈ H` directly, contradicting `H`'s
consistency / `h_not`. The harder obligation (`τR A` excluded, and the mixed `bigOr`
disjunction) needs the bespoke non-homomorphic invariant report 02 §5 describes; report 02 §5
also proves NO homomorphic atom-substitution translation (which this collapse morphism is an
instance of) can witness that harder direction, so the collapse tool below is deliberately
scoped to the two obligations it can honestly discharge. -/

/-- Identifies both copies of `Atom` in the doubled atom space `Atom ⊕ Atom`. (Parameter-style
signature, not `Atom ⊕ Atom → Atom`: this file lives inside `namespace Cslib.Logic.Modal`, where
`Basic.lean`'s `scoped infix:30 " → " => Proposition.imp` notation shadows the core function
arrow, so a bare `→` in a type ascription here would parse as `Proposition.imp`.) -/
def cs5Collapse (x : Atom ⊕ Atom) : Atom := Sum.elim id id x

@[simp] theorem cs5Collapse_inl (p : Atom) : cs5Collapse (Sum.inl p) = p := rfl

@[simp] theorem cs5Collapse_inr (p : Atom) : cs5Collapse (Sum.inr p) = p := rfl

/-- Collapsing a `τL`-tagged formula erases the tag. -/
@[simp] theorem cs5Collapse_map_inl (φ : Proposition Atom) :
    (φ.map Sum.inl).map cs5Collapse = φ := by
  rw [Proposition.map_map]
  exact Proposition.map_id φ

/-- Collapsing a `τR`-tagged formula erases the tag. -/
@[simp] theorem cs5Collapse_map_inr (φ : Proposition Atom) :
    (φ.map Sum.inr).map cs5Collapse = φ := by
  rw [Proposition.map_map]
  exact Proposition.map_id φ

/-- The atom-collapse proof-system morphism: erases the `τL`/`τR` tagging, projecting any
`CS5Combined`-derivation to a `CS5ModalAxiom`-derivation. Both `crossLR`/`crossRL` axiom
instances collapse onto the *same* `tBox` instance (`□B → B`). -/
def τ0 : ProofSigHom (modalSig (@CS5Combined Atom)) (modalSig (@CS5ModalAxiom Atom)) where
  g := Proposition.map cs5Collapse
  g_imp := fun _ _ => rfl
  axMap := fun φ h => ⟨by
    -- `CS5Combined` has three constructors, so `cases h.down` cannot eliminate directly into
    -- the `Type`-sorted `PLift` goal (large-elimination restriction); prove the `Prop`-sorted
    -- `CS5ModalAxiom` statement first (Prop-to-Prop elimination is unrestricted), then wrap.
    have hax : CS5ModalAxiom (Proposition.map cs5Collapse φ) := by
      cases h.down with
      | base h => exact cs5_axiom_relabel cs5Collapse h
      | crossLR B =>
          show CS5ModalAxiom
            (((Proposition.box (B.map Sum.inl)).imp (B.map Sum.inr)).map cs5Collapse)
          simp only [Proposition.map_imp, Proposition.map_box, cs5Collapse_map_inl,
            cs5Collapse_map_inr]
          exact CS5ModalAxiom.tBox B
      | crossRL B =>
          show CS5ModalAxiom
            (((Proposition.box (B.map Sum.inr)).imp (B.map Sum.inl)).map cs5Collapse)
          simp only [Proposition.map_imp, Proposition.map_box, cs5Collapse_map_inl,
            cs5Collapse_map_inr]
          exact CS5ModalAxiom.tBox B
    exact hax⟩
  clMap := fun m hm => by
    obtain rfl := List.mem_singleton.mp hm
    exact ⟨Proposition.box, List.mem_singleton.mpr rfl, fun _ => rfl⟩

/-- `DerivationTree` transport of the collapse projection. -/
noncomputable def cs5LiftToDerivationTreeCollapse {Γ : List (Proposition (Atom ⊕ Atom))}
    {φ : Proposition (Atom ⊕ Atom)} (d : DerivationTree CS5Combined Γ φ) :
    DerivationTree CS5ModalAxiom (Γ.map (Proposition.map cs5Collapse)) (φ.map cs5Collapse) :=
  ofDeriv (Metalogic.Deriv.map τ0 (toDeriv d))

/-- `Deriv`-level transport of the collapse projection. -/
theorem cs5_lift_deriv_collapse {Γ : List (Proposition (Atom ⊕ Atom))}
    {φ : Proposition (Atom ⊕ Atom)} (h : Deriv CS5Combined Γ φ) :
    Deriv CS5ModalAxiom (Γ.map (Proposition.map cs5Collapse)) (φ.map cs5Collapse) :=
  let ⟨d⟩ := h
  ⟨cs5LiftToDerivationTreeCollapse d⟩

/-- Specialization of the collapse projection to a purely `τL`-tagged derivation: any
`CS5Combined`-derivation from an `L`-tagged context concluding an `L`-tagged formula collapses
to a `CS5ModalAxiom`-derivation of the untagged formula from the untagged context. -/
theorem cs5_collapse_of_L_deriv {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : Deriv CS5Combined (Γ.map (Proposition.map Sum.inl)) (φ.map Sum.inl)) :
    Deriv CS5ModalAxiom Γ φ := by
  have h' := cs5_lift_deriv_collapse h
  simp only [cs5Collapse_map_inl, List.map_map, Function.comp_def, List.map_id'] at h'
  exact h'

/-- If every element of a list `Γ` lies in the image `τL '' H`, there is a list `Γ₀ ⊆ H` with
`Γ = Γ₀.map τL.g`. Choice-style list-unzip helper feeding `cs5_collapse_of_L_deriv` from the
`Set`-level membership `modalDeductiveClosure` uses. -/
theorem exists_preimage_list_of_forall_mem_image {H : Set (Proposition Atom)}
    {Γ : List (Proposition (Atom ⊕ Atom))}
    (hΓ : ∀ x ∈ Γ, x ∈ (Proposition.map Sum.inl) '' H) :
    ∃ Γ₀ : List (Proposition Atom), (∀ y ∈ Γ₀, y ∈ H) ∧ Γ = Γ₀.map (Proposition.map Sum.inl) := by
  induction Γ with
  | nil =>
      refine ⟨[], ?_, rfl⟩
      exact fun _ h => nomatch h
  | cons x xs ih =>
      obtain ⟨y, hyH, hyx⟩ := hΓ x (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨Γ₀, hΓ₀H, hΓ₀eq⟩ := ih (fun z hz => hΓ z (List.mem_cons.mpr (Or.inr hz)))
      refine ⟨y :: Γ₀, fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.mp hz with rfl | hz'
        · exact hyH
        · exact hΓ₀H z hz'
      · rw [List.map_cons, ← hΓ₀eq, hyx]

/-- **Collapse-projection at the `Set`/`modalDeductiveClosure` level.** If a `τL`-tagged
formula lies in the `CS5Combined`-deductive closure of `τL '' H`, the untagged formula lies in
the `CS5ModalAxiom`-deductive closure of `H`. -/
theorem cs5Combined_collapse_mem_L {H : Set (Proposition Atom)} {ψ : Proposition Atom}
    (h : (ψ.map Sum.inl) ∈ modalDeductiveClosure CS5Combined ((Proposition.map Sum.inl) '' H)) :
    ψ ∈ modalDeductiveClosure CS5ModalAxiom H := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  obtain ⟨Γ₀, hΓ₀H, rfl⟩ := exists_preimage_list_of_forall_mem_image hΓ
  exact ⟨Γ₀, hΓ₀H, cs5_collapse_of_L_deriv hd⟩

/-- **`⊥` cannot leak into the combined seed closure.** If `H` is quasi-prime with `□A ∉ H`
(so `H` is consistent -- `mem_of_bot_mem` would otherwise force `□A ∈ H` via `efq`), then `⊥` is
not `CS5Combined`-derivable from `τL '' H`. Via the collapse projection: `⊥ = (⊥ : Proposition
Atom).map Sum.inl`, so a derivation of `⊥` collapses to `⊥ ∈ modalDeductiveClosure CS5ModalAxiom
H = H`, contradicting `h_not` (`efq`) once `□A ∉ H` rules out `⊥ ∈ H`. -/
theorem cs5Combined_bot_excluded {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) {A : Proposition Atom}
    (h_not : Proposition.box A ∉ H) :
    (Proposition.bot : Proposition (Atom ⊕ Atom)) ∉
      modalDeductiveClosure CS5Combined ((Proposition.map Sum.inl) '' H) := by
  intro hmem
  have hmem' : ((Proposition.bot : Proposition Atom).map Sum.inl) ∈
      modalDeductiveClosure CS5Combined ((Proposition.map Sum.inl) '' H) := by
    simpa using hmem
  obtain ⟨L, hL, hd⟩ := cs5Combined_collapse_mem_L hmem'
  have hbotH : (Proposition.bot : Proposition Atom) ∈ H := hH.closed L _ hL hd
  exact h_not (mem_of_bot_mem (fun φ => .efq φ) hH.closed hbotH (Proposition.box A))

/-- **`τL(□A)` cannot leak into the combined seed closure.** Via the collapse projection:
`τL(□A) = (□A).map Sum.inl`, so a derivation of `τL(□A)` from `τL '' H` collapses to `□A ∈
modalDeductiveClosure CS5ModalAxiom H = H` (`H` closed), directly contradicting `h_not`. -/
theorem cs5Combined_boxA_excluded {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) {A : Proposition Atom}
    (h_not : Proposition.box A ∉ H) :
    ((Proposition.box A).map Sum.inl : Proposition (Atom ⊕ Atom)) ∉
      modalDeductiveClosure CS5Combined ((Proposition.map Sum.inl) '' H) := by
  intro hmem
  obtain ⟨L, hL, hd⟩ := cs5Combined_collapse_mem_L hmem
  exact h_not (hH.closed L _ hL hd)

/-! ## Seed-Pair Facts for `HR` (Phase 3, Step 1 — mechanical port)

Direct port of the sorry-free `cs5_pair_seed_mem` (`probes/cs5-pair-primeness.lean:98`, task 509
Phase 8): with `HR := modalDeductiveClosure CS5ModalAxiom (boxInv H)`, the four seed-pair facts
that the pair `(H, HR)` needs already hold. Landed here for reuse by the remainder of Phase 3's
route-2 argument and by Phase 4's pair recovery (report 02 §5 step 1). -/

/-- `boxInv H ⊆ HR` (the `crossLR` cross-condition): trivial, `HR` is the closure of `boxInv H`. -/
theorem cs5Combined_boxInv_subset_HR {H : Set (Proposition Atom)} :
    boxInv H ⊆ modalDeductiveClosure CS5ModalAxiom (boxInv H) :=
  modal_subset_deductive_closure _ _

/-- `HR ⊆ H`: since `boxInv H ⊆ H` (axiom `T`, `cs5_boxInv_subset`) and `H` is deductively
closed, the closure of `boxInv H` stays inside `H`. Port of `cs5_pair_seed_mem`'s `h_cl_sub_H`. -/
theorem cs5Combined_HR_subset_H {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) :
    modalDeductiveClosure CS5ModalAxiom (boxInv H) ⊆ H := by
  rintro φ ⟨L, hL, ⟨d⟩⟩
  exact hH.closed L φ (fun x hx => cs5_boxInv_subset hH (hL x hx)) ⟨d⟩

/-- `boxInv HR ⊆ H` (the `crossRL` cross-condition): since `HR ⊆ H`, `boxInv HR ⊆ boxInv H ⊆ H`.
Port of `cs5_pair_seed_mem`'s second cross-condition clause. -/
theorem cs5Combined_boxInv_HR_subset_H {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) :
    boxInv (modalDeductiveClosure CS5ModalAxiom (boxInv H)) ⊆ H :=
  fun _B hB => cs5_boxInv_subset hH (cs5Combined_HR_subset_H hH hB)

/-- `A ∉ HR` whenever `□A ∉ H`: a derivation of `A` from `boxInv H` would place `□A ∈ H` via
`box_mem_of_boxed_context`. Port of `cs5_pair_seed_mem`'s final clause. -/
theorem cs5Combined_A_notMem_HR {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) {A : Proposition Atom}
    (h_not : Proposition.box A ∉ H) :
    A ∉ modalDeductiveClosure CS5ModalAxiom (boxInv H) := by
  rintro ⟨L, hL, ⟨d⟩⟩
  exact h_not (box_mem_of_boxed_context (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .k φ ψ) hH.closed L d hL)

/-! ## Box-Equivalence Across the Cross Axioms

`□(τL B) ↔ □(τR B)` is `CS5Combined`-derivable for every `B` (empty context). Necessitating
`crossLR`/`crossRL` and combining with `K` (`.k`) and axiom `4` (`.fourBox`) transfers the box
past the cross axiom: this is the syntactic form of report 02's "crossRL-conservativity" lever
(the two sorts agree on all *boxed* content, though not necessarily on bare content) -- a
standalone, verified fact left here for the continuation of Phase 3's still-open `τR A`
obligation (see the plan/handoff for the remaining gap). -/

/-- Empty-context implication transitivity for `CS5Combined`, via the deduction theorem (the
`CS5Combined` analogue of `CS5.lean`'s private `cs5_impTrans`). -/
noncomputable def cs5CombinedImpTrans {a b c : Proposition (Atom ⊕ Atom)}
    (h1 : DerivationTree (@CS5Combined Atom) [] (a.imp b))
    (h2 : DerivationTree (@CS5Combined Atom) [] (b.imp c)) :
    DerivationTree (@CS5Combined Atom) [] (a.imp c) :=
  deductionTheorem (fun φ ψ => .base (.implyK φ ψ)) (fun φ ψ χ => .base (.implyS φ ψ χ)) [] a c
    (.modus_ponens _ _ _ (.weakening [] [a] _ h2 (fun _ h => nomatch h))
      (.modus_ponens _ _ _ (.weakening [] [a] _ h1 (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))))

/-- `⊢ □(τL B) → □(τR B)`: necessitate `crossLR B`, `K`-distribute, and compose with axiom `4`
on `τL B`. -/
noncomputable def cs5CombinedBoxLImpBoxR (B : Proposition Atom) :
    DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (B.map Sum.inl)).imp (Proposition.box (B.map Sum.inr))) := by
  have hnec : DerivationTree (@CS5Combined Atom) []
      (Proposition.box ((Proposition.box (B.map Sum.inl)).imp (B.map Sum.inr))) :=
    .necessitation _ (.ax [] _ (.crossLR B))
  have hk : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box ((Proposition.box (B.map Sum.inl)).imp (B.map Sum.inr))).imp
        ((Proposition.box (Proposition.box (B.map Sum.inl))).imp
          (Proposition.box (B.map Sum.inr)))) :=
    .ax [] _ (.base (.k (Proposition.box (B.map Sum.inl)) (B.map Sum.inr)))
  have hstep : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (Proposition.box (B.map Sum.inl))).imp
        (Proposition.box (B.map Sum.inr))) :=
    .modus_ponens _ _ _ hk hnec
  have hfour : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (B.map Sum.inl)).imp
        (Proposition.box (Proposition.box (B.map Sum.inl)))) :=
    .ax [] _ (.base (.fourBox (B.map Sum.inl)))
  exact cs5CombinedImpTrans hfour hstep

/-- `⊢ □(τR B) → □(τL B)`: symmetric to `cs5CombinedBoxLImpBoxR`, via `crossRL`. -/
noncomputable def cs5CombinedBoxRImpBoxL (B : Proposition Atom) :
    DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (B.map Sum.inr)).imp (Proposition.box (B.map Sum.inl))) := by
  have hnec : DerivationTree (@CS5Combined Atom) []
      (Proposition.box ((Proposition.box (B.map Sum.inr)).imp (B.map Sum.inl))) :=
    .necessitation _ (.ax [] _ (.crossRL B))
  have hk : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box ((Proposition.box (B.map Sum.inr)).imp (B.map Sum.inl))).imp
        ((Proposition.box (Proposition.box (B.map Sum.inr))).imp
          (Proposition.box (B.map Sum.inl)))) :=
    .ax [] _ (.base (.k (Proposition.box (B.map Sum.inr)) (B.map Sum.inl)))
  have hstep : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (Proposition.box (B.map Sum.inr))).imp
        (Proposition.box (B.map Sum.inl))) :=
    .modus_ponens _ _ _ hk hnec
  have hfour : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (B.map Sum.inr)).imp
        (Proposition.box (Proposition.box (B.map Sum.inr)))) :=
    .ax [] _ (.base (.fourBox (B.map Sum.inr)))
  exact cs5CombinedImpTrans hfour hstep

/-! ## Necessitation-Transfer (Phase 3 continuation — necessity-transfer conjecture, attempted)

The continuation handoff's most promising untested lead was the **necessity-transfer
conjecture**: does `⊢CS5Combined τL(Ψ) → τR(A)` imply `⊢CS5 Ψ → □A`? If so, `Ψ ∈ H`
(deductively closed) would give `□A ∈ H` directly, contradicting `h_not` — closing
`cs5Combined_seed_excludes`'s remaining obligation immediately.

**Finding this dispatch: the conjecture, AS STATED, is not reachable via the natural
proof-algebra route (necessitation + `K` + the cross axioms + the box-equivalence lemmas
above), and the byproduct that route DOES yield is provably INSUFFICIENT.** Concretely,
`cs5Combined_necTransfer` below derives the WEAKER consequence `⊢CS5 □Ψ → □A` (not the hoped-for
`⊢CS5 Ψ → □A`, unboxed antecedent). This weaker form is **vacuous exactly in the hardest case**:
taking `Ψ := A` (the case `A ∈ H`, which is the whole difficulty — necessity does not follow
from truth) makes the conclusion `⊢CS5 □A → □A`, which is *trivially* true (reflexivity of
`→`) regardless of anything about `A` or `H`. So this consequence can never rule out
`Ψ := A`, and hence cannot by itself refute `cs5Combined_seed_excludes`'s obligation.

The root cause: `necessitation` in `CS5Combined`'s derivation system only applies to
EMPTY-CONTEXT derivations, and boxes the WHOLE hypothesis `τLΨ → τRA` uniformly — there is no
way to introduce a box selectively on `Ψ` alone while leaving `A` unboxed using only
`necessitation`/`K`/`crossLR`/`crossRL`/box-equivalence algebra. Every combination explored
(chaining through `crossRL A`, through the box-equivalence lemmas, through the `crossLR`/`crossRL`
duality automorphism swapping `Sum.inl ↔ Sum.inr`) lands on a **boxed-antecedent** consequence
of this shape, never on a bare-`Ψ` consequent. This is recorded as a genuine, sorry-free,
navigational finding: **the necessity-transfer conjecture, if true, needs a fundamentally
different argument** (the derivation-height induction of report 02 §5, or equivalent
canonical-scale semantics) — re-attempting this exact algebraic route in a future dispatch
would not make further progress. -/

/-- **Necessitation-transfer** (insufficient, see module docstring above for why): if
`τL(Ψ) → τR(A)` is `CS5Combined`-derivable (empty context), then `□Ψ → □A` is `CS5`-derivable.
Obtained via necessitation of the hypothesis, `K`-distribution, and the box-equivalence lemmas
`cs5CombinedBoxRImpBoxL`, landing on a purely `τL`-tagged empty-context theorem that collapses
via `cs5_collapse_of_L_deriv`. Too weak to close `cs5Combined_seed_excludes` (vacuous at
`Ψ := A` via `→`-reflexivity `□A → □A`), but a genuine, reusable fact. -/
theorem cs5Combined_necTransfer {Ψ A : Proposition Atom}
    (h : Deriv (@CS5Combined Atom) [] ((Ψ.map Sum.inl).imp (A.map Sum.inr))) :
    Deriv (@CS5ModalAxiom Atom) [] ((Proposition.box Ψ).imp (Proposition.box A)) := by
  obtain ⟨d⟩ := h
  have hnec : DerivationTree (@CS5Combined Atom) []
      (Proposition.box ((Ψ.map Sum.inl).imp (A.map Sum.inr))) :=
    .necessitation _ d
  have hk : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box ((Ψ.map Sum.inl).imp (A.map Sum.inr))).imp
        ((Proposition.box (Ψ.map Sum.inl)).imp (Proposition.box (A.map Sum.inr)))) :=
    .ax [] _ (.base (.k (Ψ.map Sum.inl) (A.map Sum.inr)))
  have hstep : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (Ψ.map Sum.inl)).imp (Proposition.box (A.map Sum.inr))) :=
    .modus_ponens _ _ _ hk hnec
  have hboxRL : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (A.map Sum.inr)).imp (Proposition.box (A.map Sum.inl))) :=
    cs5CombinedBoxRImpBoxL A
  have hcomb : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (Ψ.map Sum.inl)).imp (Proposition.box (A.map Sum.inl))) :=
    cs5CombinedImpTrans hstep hboxRL
  have hcomb' : DerivationTree (@CS5Combined Atom) []
      (((Proposition.box Ψ).imp (Proposition.box A)).map Sum.inl) := by
    simpa [Proposition.map_imp, Proposition.map_box] using hcomb
  exact cs5_collapse_of_L_deriv (Γ := []) ⟨hcomb'⟩

/-! ## The `CS5Combined` Canonical Model (Phase 3 Reframe, per continuation handoff 03)

Per the third continuation dispatch's finding (both the necessitation/K/cross-axiom algebra and
every atom-indexed semantic model are exhausted dead ends), this section builds the
**genuinely canonical** model for `CS5Combined` — mirroring `CS5.lean`'s own `cs5Tail`/`CS5Segment`/
`cs5Mreach`/`cs5FC''_cs5Mreach` construction verbatim, but over the doubled atom space `Atom ⊕
Atom` and the `CS5Combined` axiom system, so that `cs5Combined_seed_excludes` can eventually be
read off a genuine truth-lemma-grade argument rather than a bespoke algebraic shortcut.

**Reuse finding (this dispatch):** almost all of `CS5.lean`'s canonical-model plumbing
(`mem_head_mp`, `mem_of_axiom`, `box_mem_of_boxed_context`, `quasi_prime_exclusion`,
`box_refuting_theory`, `list_split_union`, `bigAnd`/`bigAnd_mem_of_forall_mem`,
`derivImpBigAndOfAppend`, `modal_deriv_imp_of_union`, `modalDeductiveClosure_closed`,
`modal_subset_deductive_closure`, `Metalogic.prime_set_exclusion`, `CKSegment`, `cmreach`,
`QuasiPrime`) is **already generic over an arbitrary axiom predicate `Axioms`**, not
CS5-specific — confirmed by reading each declaration's signature. Only the genuinely
`CS5ModalAxiom`-hardcoded layer (`cs5_box_four`, `cs5_boxInv_subset`, `cs5Tail` + its
refl/symm/trans, `cs5_dia_bot_imp_bot`, the `bigOr`/`box` combinatorics,
`quasi_prime_set_exclusion`, `cs5_diam_witness`, `cs5Seg`/`CS5Segment`/`cs5Mreach`,
`cs5_fcsymbox_theory`/`cs5_fc4_theory`, and
`cs5FC''_cs5Mreach`) needs re-proving for `CS5Combined`, and every one of those re-proofs is a
direct mechanical port (swap `CS5ModalAxiom.X` for `CS5Combined.base (.X)`, `Atom` for
`Atom ⊕ Atom`), landed below.

**Open structural question flagged for the next dispatch** (not yet resolved): `CS5.lean`'s own
`cs5_symmetric_tail_box_gap` is proved using *only* primality of a tail member and the two tail
clauses — "no `CS5` axiom" (see its docstring) — so it is expected to apply *verbatim* to
`cs5CombinedTail` too. If so, `CS5Combined`'s own canonical model has the identical box-backward
gap that `CS5`'s does, meaning a *fully general* `cs5Combined` truth lemma is NOT easier than the
original problem — the value of this section is not "avoid box-backward via a bigger language"
but "have the tail/accessibility/frame-condition scaffolding available so that
`cs5Combined_seed_excludes` can be attacked as a *specific*, designated-world existence claim
(using the already-landed `HR`/pair facts above as the seed) rather than needing the fully
general truth lemma for arbitrary worlds." This distinction is left as the concrete next step. -/

/-- `□B ∈ H → □□B ∈ H` for `CS5Combined` — axiom `4` (box form). Port of `cs5_box_four`. -/
theorem cs5Combined_box_four {H : Set (Proposition (Atom ⊕ Atom))}
    (hH : QuasiPrime (@CS5Combined Atom) H) {B : Proposition (Atom ⊕ Atom)}
    (h : Proposition.box B ∈ H) :
    Proposition.box (Proposition.box B) ∈ H :=
  mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5Combined.base (.fourBox B))) h

/-- `boxInv H ⊆ H` for `CS5Combined` — axiom `T` (box form). Port of `cs5_boxInv_subset`. -/
theorem cs5Combined_boxInv_subset {H : Set (Proposition (Atom ⊕ Atom))}
    (hH : QuasiPrime (@CS5Combined Atom) H) : boxInv H ⊆ H :=
  fun B hB => mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5Combined.base (.tBox B))) hB

/-- **The `CS5Combined` symmetric tail.** Port of `cs5Tail`. -/
def cs5CombinedTail (H : Set (Proposition (Atom ⊕ Atom))) :
    Set (Set (Proposition (Atom ⊕ Atom))) :=
  {t | QuasiPrime (@CS5Combined Atom) t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}

/-- **Reflexivity**: `H ∈ cs5CombinedTail H`. Port of `cs5Tail_refl`. -/
theorem cs5CombinedTail_refl {H : Set (Proposition (Atom ⊕ Atom))}
    (hH : QuasiPrime (@CS5Combined Atom) H) : H ∈ cs5CombinedTail H :=
  ⟨hH, cs5Combined_boxInv_subset hH, cs5Combined_boxInv_subset hH⟩

/-- **Symmetry, definitional.** Port of `cs5Tail_symm`. -/
theorem cs5CombinedTail_symm {H T : Set (Proposition (Atom ⊕ Atom))}
    (hH : QuasiPrime (@CS5Combined Atom) H) (h : T ∈ cs5CombinedTail H) :
    H ∈ cs5CombinedTail T :=
  ⟨hH, h.2.2, h.2.1⟩

/-- **Transitivity.** Port of `cs5Tail_trans`. -/
theorem cs5CombinedTail_trans {H U T : Set (Proposition (Atom ⊕ Atom))}
    (hH : QuasiPrime (@CS5Combined Atom) H) (hT : QuasiPrime (@CS5Combined Atom) T)
    (h1 : U ∈ cs5CombinedTail H) (h2 : T ∈ cs5CombinedTail U) : T ∈ cs5CombinedTail H :=
  ⟨hT,
   fun _B hB => h2.2.1 (h1.2.1 (cs5Combined_box_four hH hB)),
   fun _B hB => h1.2.2 (h2.2.2 (cs5Combined_box_four hT hB))⟩

/-- **The `CS5Combined` symmetric tail has the identical box-backward gap as `CS5`'s.** Port of
`cs5_symmetric_tail_box_gap`, mechanically confirming the "open structural question" flagged in
this section's docstring: the argument uses *only* primality of `T` and the two tail clauses
(`hsub`/`hsym`), no axiom-system-specific fact, so it transfers verbatim from `CS5ModalAxiom` to
`CS5Combined`. Consequence: a fully general `cs5Combined` truth lemma (covering *arbitrary*
`CS5Combined`-quasi-prime heads `H`) is NOT easier than `CS5`'s own open box-backward case — the
value of this section's canonical-model scaffolding is to support attacking
`cs5Combined_seed_excludes` as a *specific*, designated-pair existence claim (using the seed
`τL '' H` and the already-landed `HR` facts above), not to sidestep box-backward via a bigger
language. -/
theorem cs5Combined_symmetric_tail_box_gap {H T : Set (Proposition (Atom ⊕ Atom))}
    (hT : QuasiPrime (@CS5Combined Atom) T) {p q : Proposition (Atom ⊕ Atom)}
    (hbox : Proposition.box (p.or (Proposition.box q)) ∈ H)
    (hsub : boxInv H ⊆ T) (hsym : boxInv T ⊆ H) (hq : q ∉ H) : p ∈ T := by
  rcases hT.disj (hsub hbox) with h | h
  · exact h
  · exact absurd (hsym h) hq

/-- **`CS5Combined ⊢ ◇⊥ → ⊥`**. Port of `cs5_dia_bot_imp_bot`. -/
theorem cs5Combined_dia_bot_imp_bot :
    Derivable (@CS5Combined Atom)
      ((◇(Proposition.bot : Proposition (Atom ⊕ Atom))).imp Proposition.bot) := by
  have d1 : DerivationTree (@CS5Combined Atom) []
      ((Proposition.bot : Proposition (Atom ⊕ Atom)).imp
        (Proposition.box Proposition.bot)) :=
    .ax [] _ (.base (.efq (Proposition.box Proposition.bot)))
  have d2 : DerivationTree (@CS5Combined Atom) []
      (Proposition.box ((Proposition.bot : Proposition (Atom ⊕ Atom)).imp
        (Proposition.box Proposition.bot))) :=
    .necessitation _ d1
  have d3 : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box ((Proposition.bot : Proposition (Atom ⊕ Atom)).imp
        (Proposition.box Proposition.bot))).imp
        ((◇(Proposition.bot : Proposition (Atom ⊕ Atom))).imp
          (◇(Proposition.box (Proposition.bot : Proposition (Atom ⊕ Atom)))))) :=
    .ax [] _ (.base (.kdia Proposition.bot (Proposition.box Proposition.bot)))
  have d4 : DerivationTree (@CS5Combined Atom) []
      ((◇(Proposition.bot : Proposition (Atom ⊕ Atom))).imp
        (◇(Proposition.box (Proposition.bot : Proposition (Atom ⊕ Atom))))) :=
    .modus_ponens _ _ _ d3 d2
  have d5 : DerivationTree (@CS5Combined Atom) []
      ((◇(Proposition.box (Proposition.bot : Proposition (Atom ⊕ Atom)))).imp
        Proposition.bot) :=
    .ax [] _ (.base (.bDia Proposition.bot))
  have hctx : DerivationTree (@CS5Combined Atom)
      [◇(Proposition.bot : Proposition (Atom ⊕ Atom))]
      (Proposition.bot : Proposition (Atom ⊕ Atom)) := by
    have a0 : DerivationTree (@CS5Combined Atom)
        [◇(Proposition.bot : Proposition (Atom ⊕ Atom))]
        (◇(Proposition.bot : Proposition (Atom ⊕ Atom))) :=
      .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
    have w4 := DerivationTree.weakening [] [◇(Proposition.bot : Proposition (Atom ⊕ Atom))] _ d4
      (fun _ h => nomatch h)
    have w5 := DerivationTree.weakening [] [◇(Proposition.bot : Proposition (Atom ⊕ Atom))] _ d5
      (fun _ h => nomatch h)
    exact .modus_ponens _ _ _ w5 (.modus_ponens _ _ _ w4 a0)
  exact ⟨deductionTheorem (fun φ ψ => .base (.implyK φ ψ)) (fun φ ψ χ => .base (.implyS φ ψ χ)) []
    (◇(Proposition.bot : Proposition (Atom ⊕ Atom))) Proposition.bot hctx⟩

/-- `⊢ □B → □(bigOr (B :: rest))` for `CS5Combined`. Port of the private `cs5_box_mono`. -/
private def cs5Combined_box_mono {A B : Proposition (Atom ⊕ Atom)}
    (hAB : CS5Combined (A.imp B)) :
    DerivationTree (@CS5Combined Atom) [] ((Proposition.box A).imp (Proposition.box B)) :=
  .modus_ponens [] _ _ (.ax [] _ (.base (.k A B))) (.necessitation _ (.ax [] _ hAB))

/-- **Box-of-disjuncts, n-ary**, for `CS5Combined`. Port of the private `or_box_imp_box_bigOr`. -/
private noncomputable def cs5Combined_or_box_imp_box_bigOr :
    ∀ (Bs : List (Proposition (Atom ⊕ Atom))),
      DerivationTree (@CS5Combined Atom) []
        ((Metalogic.bigOr (Bs.map Proposition.box)).imp (Proposition.box (Metalogic.bigOr Bs)))
  | [] =>
      .ax [] _ (.base (.efq
        (Proposition.box (Metalogic.bigOr ([] : List (Proposition (Atom ⊕ Atom)))))))
  | B :: rest => by
      have f1 : DerivationTree (@CS5Combined Atom) []
          ((Proposition.box B).imp (Proposition.box (Metalogic.bigOr (B :: rest)))) :=
        cs5Combined_box_mono (.base (.orI1 B (Metalogic.bigOr rest)))
      have f2a : DerivationTree (@CS5Combined Atom) []
          ((Proposition.box (Metalogic.bigOr rest)).imp
            (Proposition.box (Metalogic.bigOr (B :: rest)))) :=
        cs5Combined_box_mono (.base (.orI2 B (Metalogic.bigOr rest)))
      have ih := cs5Combined_or_box_imp_box_bigOr rest
      have f2 : DerivationTree (@CS5Combined Atom) []
          ((Metalogic.bigOr (rest.map Proposition.box)).imp
            (Proposition.box (Metalogic.bigOr (B :: rest)))) :=
        cs5CombinedImpTrans ih f2a
      have step1 := DerivationTree.modus_ponens [] _ _
        (DerivationTree.ax [] _
          (CS5Combined.base (.orE (Proposition.box B) (Metalogic.bigOr (rest.map Proposition.box))
            (Proposition.box (Metalogic.bigOr (B :: rest))))))
        f1
      exact DerivationTree.modus_ponens [] _ _ step1 f2

/-- **`⊢ ◇(bigOr (Bs.map box)) → bigOr Bs`** for `CS5Combined`. Port of the private
`dia_or_box_imp_bigOr`. -/
private noncomputable def cs5Combined_dia_or_box_imp_bigOr (Bs : List (Proposition (Atom ⊕ Atom))) :
    DerivationTree (@CS5Combined Atom) []
      ((◇(Metalogic.bigOr (Bs.map Proposition.box))).imp (Metalogic.bigOr Bs)) :=
  cs5CombinedImpTrans
    (.modus_ponens [] _ _
      (.ax [] _ (.base (.kdia (Metalogic.bigOr (Bs.map Proposition.box))
        (Proposition.box (Metalogic.bigOr Bs)))))
      (.necessitation _ (cs5Combined_or_box_imp_box_bigOr Bs)))
    (.ax [] _ (.base (.bDia (Metalogic.bigOr Bs))))

/-- Extracts the bare witnesses `Bs` of a list `l` drawn from `{□B | B ∉ H}`, over `Atom ⊕ Atom`.
Port of the private `extract_box_list` (purely list-theoretic, no axiom dependency; copied rather
than imported since the original is `private` to `CS5.lean`). -/
private theorem cs5Combined_extract_box_list {H : Set (Proposition (Atom ⊕ Atom))} :
    ∀ (l : List (Proposition (Atom ⊕ Atom))),
      (∀ x ∈ l, ∃ B, x = Proposition.box B ∧ B ∉ H) →
      ∃ Bs : List (Proposition (Atom ⊕ Atom)), l = Bs.map Proposition.box ∧ ∀ B ∈ Bs, B ∉ H
  | [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | x :: xs, hl => by
      obtain ⟨B, hxeq, hBH⟩ := hl x (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨Bs', hBs'eq, hBs'H⟩ :=
        cs5Combined_extract_box_list (H := H) xs (fun y hy => hl y (List.mem_cons.mpr (Or.inr hy)))
      refine ⟨B :: Bs', by rw [hxeq, hBs'eq]; rfl, ?_⟩
      intro B' hB'
      rcases List.mem_cons.mp hB' with rfl | h
      · exact hBH
      · exact hBs'H B' h

/-- **Prime disjunction property, n-ary, nonempty case**, for `CS5Combined`. Port of the private
`quasiPrime_bigOr_mem`. -/
private theorem cs5Combined_quasiPrime_bigOr_mem {S : Set (Proposition (Atom ⊕ Atom))}
    (hS : QuasiPrime (@CS5Combined Atom) S) :
    ∀ (B : Proposition (Atom ⊕ Atom)) (rest : List (Proposition (Atom ⊕ Atom))),
      Metalogic.bigOr (B :: rest) ∈ S → ∃ C ∈ B :: rest, C ∈ S
  | B, [], hmem => by
      rcases hS.disj hmem with h | h
      · exact ⟨B, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨B, List.mem_cons.mpr (Or.inl rfl),
          mem_of_bot_mem (fun φ => .base (.efq φ)) hS.closed h B⟩
  | B, B' :: rest', hmem => by
      rcases hS.disj hmem with h | h
      · exact ⟨B, List.mem_cons.mpr (Or.inl rfl), h⟩
      · obtain ⟨C, hC, hCS⟩ := cs5Combined_quasiPrime_bigOr_mem hS B' rest' h
        exact ⟨C, List.mem_cons.mpr (Or.inr hC), hCS⟩

/-- **Set exclusion at the trivially-true consistency predicate**, for `CS5Combined`. Port of the
private `quasi_prime_set_exclusion`. -/
private theorem cs5Combined_quasi_prime_set_exclusion
    {S : Set (Proposition (Atom ⊕ Atom))}
    (h_closed : Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5Combined Atom)) S)
    {E : Set (Proposition (Atom ⊕ Atom))}
    (h_excl : Metalogic.DerivExcludes (modalDerivationSystem (@CS5Combined Atom)) E S) :
    ∃ T, S ⊆ T ∧ QuasiPrime (@CS5Combined Atom) T ∧
      Metalogic.DerivExcludes (modalDerivationSystem (@CS5Combined Atom)) E T :=
  Metalogic.prime_set_exclusion
    (modalDerivationSystem (@CS5Combined Atom)) (fun _ => True)
    ⟨trivial, h_closed⟩ h_excl
    (fun A B => ⟨.ax [] _ (.base (.orI1 A B))⟩)
    (fun A B => ⟨.ax [] _ (.base (.orI2 A B))⟩)
    (fun A B χ => ⟨.ax [] _ (.base (.orE A B χ))⟩)
    (fun A => ⟨.ax [] _ (.base (.efq A))⟩)
    (modalDeductiveClosure CS5Combined)
    (modal_subset_deductive_closure CS5Combined)
    (fun {_X _ψ} h => h)
    (fun {_X} _ => ⟨trivial,
      fun L φ' hL hd => modalDeductiveClosure_closed (fun φ ψ => .base (.implyK φ ψ))
        (fun φ ψ χ => .base (.implyS φ ψ χ)) L φ' hL hd⟩)
    (fun {_X} h_not_cons => absurd trivial h_not_cons)
    (fun {U _L a _b} hL hd =>
      modal_deriv_imp_of_union (fun φ ψ => .base (.implyK φ ψ))
        (fun φ ψ χ => .base (.implyS φ ψ χ))
        (fun x hx => by
          rcases Set.mem_insert_iff.mp (hL x hx) with rfl | hu
          · exact Set.mem_union_right U (Set.mem_singleton_iff.mpr rfl)
          · exact Set.mem_union_left _ hu)
        hd)
    (fun _ _ _ _ => trivial)

/-- **The diamond witness for the `CS5Combined` symmetric tail.** Port of `cs5_diam_witness`. -/
theorem cs5Combined_diam_witness {H : Set (Proposition (Atom ⊕ Atom))}
    (hH : QuasiPrime (@CS5Combined Atom) H)
    {A : Proposition (Atom ⊕ Atom)} (hA : (◇A) ∈ H) : ∃ t ∈ cs5CombinedTail H, A ∈ t := by
  by_cases hex : (Proposition.bot : Proposition (Atom ⊕ Atom)) ∈ H
  · refine ⟨Set.univ, ⟨quasiPrime_univ, Set.subset_univ _, ?_⟩, Set.mem_univ _⟩
    intro B _
    exact mem_of_bot_mem (fun φ => .base (.efq φ)) hH.closed hex B
  · have hExcl : Metalogic.DerivExcludes (modalDerivationSystem (@CS5Combined Atom))
        {x | ∃ B, x = Proposition.box B ∧ B ∉ H}
        (modalDeductiveClosure CS5Combined (boxInv H ∪ {A})) := by
      intro l hl hmem
      obtain ⟨Lctx, hLctx, hd⟩ := hmem
      obtain ⟨L', hL'sub, hL'd⟩ :=
        modal_deriv_imp_of_union (fun φ ψ => .base (.implyK φ ψ))
          (fun φ ψ χ => .base (.implyS φ ψ χ)) hLctx hd
      obtain ⟨d'⟩ := hL'd
      have hbox : Proposition.box (A.imp (Metalogic.bigOr l)) ∈ H :=
        box_mem_of_boxed_context (fun φ ψ => .base (.implyK φ ψ))
          (fun φ ψ χ => .base (.implyS φ ψ χ)) (fun φ ψ => .base (.k φ ψ)) hH.closed L' d' hL'sub
      have hdiaBigOr : (◇(Metalogic.bigOr l)) ∈ H :=
        mem_head_mp hH.closed
          (mem_head_mp hH.closed (mem_of_axiom hH.closed
            (CS5Combined.base (.kdia A (Metalogic.bigOr l)))) hbox) hA
      rcases l with _ | ⟨x, xs⟩
      · have hdbot : ((◇(Proposition.bot : Proposition (Atom ⊕ Atom))).imp Proposition.bot) ∈ H :=
          hH.closed [] _ (fun _ h => nomatch h) cs5Combined_dia_bot_imp_bot
        exact hex (mem_head_mp hH.closed hdbot hdiaBigOr)
      · obtain ⟨Bs, hBseq, hBsH⟩ := cs5Combined_extract_box_list (H := H) (x :: xs) hl
        have hdiaBigOr' : (◇(Metalogic.bigOr (Bs.map Proposition.box))) ∈ H := hBseq ▸ hdiaBigOr
        have hchain : ((◇(Metalogic.bigOr (Bs.map Proposition.box))).imp
            (Metalogic.bigOr Bs)) ∈ H :=
          hH.closed [] _ (fun _ h => nomatch h) ⟨cs5Combined_dia_or_box_imp_bigOr Bs⟩
        have hBigOrBs : Metalogic.bigOr Bs ∈ H := mem_head_mp hH.closed hchain hdiaBigOr'
        rcases Bs with _ | ⟨B, rest⟩
        · exact absurd hBseq (List.cons_ne_nil x xs)
        · obtain ⟨C, hCmem, hCH⟩ := cs5Combined_quasiPrime_bigOr_mem hH B rest hBigOrBs
          exact absurd hCH (hBsH C hCmem)
    obtain ⟨T, hST, hTprime, hTexcl⟩ :=
      cs5Combined_quasi_prime_set_exclusion
        (modalDeductiveClosure_closed (fun φ ψ => .base (.implyK φ ψ))
          (fun φ ψ χ => .base (.implyS φ ψ χ)))
        hExcl
    refine ⟨T, ⟨hTprime, ?_, ?_⟩, ?_⟩
    · exact fun B hB => hST (modal_subset_deductive_closure _ _ (Or.inl hB))
    · intro B hBT
      by_contra hBH
      have hBoxBmemE : Proposition.box B ∈ {x | ∃ B, x = Proposition.box B ∧ B ∉ H} :=
        ⟨B, rfl, hBH⟩
      have hdisjT : Proposition.box B ∈ T :=
        hTprime.closed [Proposition.box B] _
          (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hBT, nomatch h])
          ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩
      refine hTexcl [Proposition.box B]
        (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hBoxBmemE, nomatch h])
        (hTprime.closed [Proposition.box B] _
          (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hdisjT, nomatch h])
          ⟨.modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.base (.orI1 (Proposition.box B)
            (Proposition.bot)))) (fun _ h => nomatch h))
            (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩)
    · exact hST (modal_subset_deductive_closure _ _ (Or.inr rfl))

/-! ## The `CS5Combined` World Type -/

/-- The `CS5Combined` canonical segment at head `H`: tail is exactly `cs5CombinedTail H`. Port of
`cs5Seg`. -/
def cs5CombinedSeg {H : Set (Proposition (Atom ⊕ Atom))}
    (hH : QuasiPrime (@CS5Combined Atom) H) : CKSegment (@CS5Combined Atom) where
  head := H
  tail := cs5CombinedTail H
  head_qprime := hH
  tail_qprime := fun _ ht => ht.1
  box_reflect := fun _ hB _ ht => ht.2.1 hB
  diam_witness := fun _A hA => cs5Combined_diam_witness hH hA

/-- `CS5Combined` canonical worlds: segments whose tail is exactly the symmetric tail of their
head. Port of `CS5Segment`. -/
structure CS5CombinedSegment (Atom : Type u) where
  /-- The underlying segment. -/
  seg : CKSegment (@CS5Combined Atom)
  /-- The tail is exactly the symmetric tail of the head. -/
  tail_eq : seg.tail = cs5CombinedTail seg.head

instance : Preorder (CS5CombinedSegment Atom) :=
  Preorder.lift (fun s : CS5CombinedSegment Atom => s.seg)

/-- Canonical accessibility for `CS5Combined`. Port of `cs5Mreach`. -/
def cs5CombinedMreach (P Q : CS5CombinedSegment Atom) : Prop := cmreach P.seg Q.seg

/-- The canonical `CS5Combined` world at head `H`. Port of `CS5Segment.ofHead`. -/
def CS5CombinedSegment.ofHead {H : Set (Proposition (Atom ⊕ Atom))}
    (hH : QuasiPrime (@CS5Combined Atom) H) : CS5CombinedSegment Atom where
  seg := cs5CombinedSeg hH
  tail_eq := rfl

/-- `cs5CombinedMreach` is reflexive. Port of `cs5_refl`. -/
theorem cs5Combined_refl (P : CS5CombinedSegment Atom) : cs5CombinedMreach P P := by
  change P.seg.head ∈ P.seg.tail
  rw [P.tail_eq]
  exact cs5CombinedTail_refl P.seg.head_qprime

/-- `cs5CombinedMreach` is transitive. Port of `cs5_trans`. -/
theorem cs5Combined_trans {P Q R : CS5CombinedSegment Atom} (hPQ : cs5CombinedMreach P Q)
    (hQR : cs5CombinedMreach Q R) : cs5CombinedMreach P R := by
  change R.seg.head ∈ P.seg.tail
  rw [P.tail_eq]
  have hPQ' : Q.seg.head ∈ cs5CombinedTail P.seg.head := P.tail_eq ▸ hPQ
  have hQR' : R.seg.head ∈ cs5CombinedTail Q.seg.head := Q.tail_eq ▸ hQR
  exact cs5CombinedTail_trans P.seg.head_qprime R.seg.head_qprime hPQ' hQR'

/-- `cs5CombinedMreach` is symmetric — definitional, not derived. Port of `cs5_symm`. -/
theorem cs5Combined_symm {P Q : CS5CombinedSegment Atom} (hPQ : cs5CombinedMreach P Q) :
    cs5CombinedMreach Q P := by
  change P.seg.head ∈ Q.seg.tail
  rw [Q.tail_eq]
  have hPQ' : Q.seg.head ∈ cs5CombinedTail P.seg.head := P.tail_eq ▸ hPQ
  exact cs5CombinedTail_symm P.seg.head_qprime hPQ'

/-! ## `cs5CombinedFC''_cs5CombinedMreach`: the Combined Canonical Model Satisfies `cs5FC''` -/

/-- Theory-level content of `bBox`'s canonical clause, for `CS5Combined`. Port of
`cs5_fcsymbox_theory`. -/
theorem cs5Combined_fcsymbox_theory {w u u' : Set (Proposition (Atom ⊕ Atom))}
    (hw : QuasiPrime (@CS5Combined Atom) w) (hu' : QuasiPrime (@CS5Combined Atom) u')
    (hwu_sub : boxInv w ⊆ u) (hle : u ⊆ u') :
    ∃ t, t ∈ cs5CombinedTail u' ∧ w ⊆ t := by
  by_cases hex : (Proposition.bot : Proposition (Atom ⊕ Atom)) ∈ u'
  · exact ⟨Set.univ, ⟨quasiPrime_univ, Set.subset_univ _,
      fun B _ => mem_of_bot_mem (fun φ => .base (.efq φ)) hu'.closed hex B⟩, Set.subset_univ _⟩
  · have hExcl : Metalogic.DerivExcludes (modalDerivationSystem (@CS5Combined Atom))
        {x | ∃ B, x = Proposition.box B ∧ B ∉ u'}
        (modalDeductiveClosure CS5Combined (boxInv u' ∪ w)) := by
      intro l hl hmem
      obtain ⟨Lctx, hLctx, hd⟩ := hmem
      obtain ⟨L₁, L₂, hL₁, hL₂, hsub⟩ := list_split_union (X := boxInv u') (Y := w) Lctx hLctx
      obtain ⟨d⟩ := hd
      have d' : DerivationTree (@CS5Combined Atom) (L₁ ++ L₂) (Metalogic.bigOr l) :=
        .weakening Lctx (L₁ ++ L₂) _ d hsub
      have dC : DerivationTree (@CS5Combined Atom) L₁
          ((bigAnd L₂).imp (Metalogic.bigOr l)) :=
        derivImpBigAndOfAppend (fun φ ψ => .base (.implyK φ ψ)) (fun φ ψ χ => .base (.implyS φ ψ χ))
          (fun φ ψ => .base (.andE1 φ ψ)) (fun φ ψ => .base (.andE2 φ ψ)) L₁ L₂
          (Metalogic.bigOr l) d'
      have hboxC : Proposition.box ((bigAnd L₂).imp (Metalogic.bigOr l)) ∈ u' :=
        box_mem_of_boxed_context (fun φ ψ => .base (.implyK φ ψ))
          (fun φ ψ χ => .base (.implyS φ ψ χ)) (fun φ ψ => .base (.k φ ψ)) hu'.closed L₁ dC hL₁
      have hCmem : bigAnd L₂ ∈ w :=
        bigAnd_mem_of_forall_mem (fun φ => .base (.efq φ)) (fun φ ψ => .base (.andI φ ψ))
          hw.closed L₂ hL₂
      have hboxDiaC : Proposition.box (◇(bigAnd L₂)) ∈ w :=
        mem_head_mp hw.closed
          (mem_of_axiom hw.closed (CS5Combined.base (.bBox (bigAnd L₂)))) hCmem
      have hdiaC_u' : (◇(bigAnd L₂)) ∈ u' := hle (hwu_sub hboxDiaC)
      have hdiaBigOr : (◇(Metalogic.bigOr l)) ∈ u' :=
        mem_head_mp hu'.closed
          (mem_head_mp hu'.closed (mem_of_axiom hu'.closed
            (CS5Combined.base (.kdia (bigAnd L₂) (Metalogic.bigOr l)))) hboxC) hdiaC_u'
      rcases l with _ | ⟨x, xs⟩
      · have hdbot : ((◇(Proposition.bot : Proposition (Atom ⊕ Atom))).imp Proposition.bot) ∈ u' :=
          hu'.closed [] _ (fun _ h => nomatch h) cs5Combined_dia_bot_imp_bot
        exact hex (mem_head_mp hu'.closed hdbot hdiaBigOr)
      · obtain ⟨Bs, hBseq, hBsH⟩ := cs5Combined_extract_box_list (H := u') (x :: xs) hl
        have hdiaBigOr' : (◇(Metalogic.bigOr (Bs.map Proposition.box))) ∈ u' :=
          hBseq ▸ hdiaBigOr
        have hchain : ((◇(Metalogic.bigOr (Bs.map Proposition.box))).imp
            (Metalogic.bigOr Bs)) ∈ u' :=
          hu'.closed [] _ (fun _ h => nomatch h) ⟨cs5Combined_dia_or_box_imp_bigOr Bs⟩
        have hBigOrBs : Metalogic.bigOr Bs ∈ u' := mem_head_mp hu'.closed hchain hdiaBigOr'
        rcases Bs with _ | ⟨B, rest⟩
        · exact absurd hBseq (List.cons_ne_nil x xs)
        · obtain ⟨C, hCmem, hCu'⟩ := cs5Combined_quasiPrime_bigOr_mem hu' B rest hBigOrBs
          exact absurd hCu' (hBsH C hCmem)
    obtain ⟨T, hST, hTprime, hTexcl⟩ :=
      cs5Combined_quasi_prime_set_exclusion
        (modalDeductiveClosure_closed (fun φ ψ => .base (.implyK φ ψ))
          (fun φ ψ χ => .base (.implyS φ ψ χ)))
        hExcl
    refine ⟨T, ⟨hTprime, ?_, ?_⟩, fun B hB => hST (modal_subset_deductive_closure _ _ (Or.inr hB))⟩
    · exact fun B hB => hST (modal_subset_deductive_closure _ _ (Or.inl hB))
    · intro B hBT
      by_contra hBu'
      have hBoxBmemE : Proposition.box B ∈ {x | ∃ B, x = Proposition.box B ∧ B ∉ u'} :=
        ⟨B, rfl, hBu'⟩
      have hdisjT : Proposition.box B ∈ T :=
        hTprime.closed [Proposition.box B] _
          (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hBT, nomatch h])
          ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩
      refine hTexcl [Proposition.box B]
        (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hBoxBmemE, nomatch h])
        (hTprime.closed [Proposition.box B] _
          (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hdisjT, nomatch h])
          ⟨.modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.base (.orI1 (Proposition.box B)
            (Proposition.bot)))) (fun _ h => nomatch h))
            (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩)

/-- Theory-level content of `fourBox`'s re-basing clause, for `CS5Combined`. Port of
`cs5_fc4_theory`. -/
theorem cs5Combined_fc4_theory {w u u' t : Set (Proposition (Atom ⊕ Atom))}
    (hw : QuasiPrime (@CS5Combined Atom) w) (ht : QuasiPrime (@CS5Combined Atom) t)
    (hwu_sub : boxInv w ⊆ u) (hle : u ⊆ u')
    (hu't_sub1 : boxInv u' ⊆ t) (_hu't_sub2 : boxInv t ⊆ u') :
    ∃ v, QuasiPrime (@CS5Combined Atom) v ∧ w ⊆ v ∧ t ∈ cs5CombinedTail v := by
  by_cases hex : (Proposition.bot : Proposition (Atom ⊕ Atom)) ∈ t
  · exact ⟨Set.univ, quasiPrime_univ, Set.subset_univ _, ht,
      fun B _ => mem_of_bot_mem (fun φ => .base (.efq φ)) ht.closed hex B, Set.subset_univ _⟩
  · have hExcl : Metalogic.DerivExcludes (modalDerivationSystem (@CS5Combined Atom))
        {x | ∃ B, x = Proposition.box B ∧ B ∉ t}
        (modalDeductiveClosure CS5Combined (boxInv t ∪ w)) := by
      intro l hl hmem
      obtain ⟨Lctx, hLctx, hd⟩ := hmem
      obtain ⟨L₁, L₂, hL₁, hL₂, hsub⟩ := list_split_union (X := boxInv t) (Y := w) Lctx hLctx
      obtain ⟨d⟩ := hd
      have d' : DerivationTree (@CS5Combined Atom) (L₁ ++ L₂) (Metalogic.bigOr l) :=
        .weakening Lctx (L₁ ++ L₂) _ d hsub
      have dC : DerivationTree (@CS5Combined Atom) L₁
          ((bigAnd L₂).imp (Metalogic.bigOr l)) :=
        derivImpBigAndOfAppend (fun φ ψ => .base (.implyK φ ψ)) (fun φ ψ χ => .base (.implyS φ ψ χ))
          (fun φ ψ => .base (.andE1 φ ψ)) (fun φ ψ => .base (.andE2 φ ψ)) L₁ L₂
          (Metalogic.bigOr l) d'
      have hboxC : Proposition.box ((bigAnd L₂).imp (Metalogic.bigOr l)) ∈ t :=
        box_mem_of_boxed_context (fun φ ψ => .base (.implyK φ ψ))
          (fun φ ψ χ => .base (.implyS φ ψ χ)) (fun φ ψ => .base (.k φ ψ)) ht.closed L₁ dC hL₁
      have hCmem : bigAnd L₂ ∈ w :=
        bigAnd_mem_of_forall_mem (fun φ => .base (.efq φ)) (fun φ ψ => .base (.andI φ ψ))
          hw.closed L₂ hL₂
      have hboxDiaC : Proposition.box (◇(bigAnd L₂)) ∈ w :=
        mem_head_mp hw.closed
          (mem_of_axiom hw.closed (CS5Combined.base (.bBox (bigAnd L₂)))) hCmem
      have hboxboxDiaC : Proposition.box (Proposition.box (◇(bigAnd L₂))) ∈ w :=
        cs5Combined_box_four hw hboxDiaC
      have hdiaC_t : (◇(bigAnd L₂)) ∈ t := hu't_sub1 (hle (hwu_sub hboxboxDiaC))
      have hdiaBigOr : (◇(Metalogic.bigOr l)) ∈ t :=
        mem_head_mp ht.closed
          (mem_head_mp ht.closed (mem_of_axiom ht.closed
            (CS5Combined.base (.kdia (bigAnd L₂) (Metalogic.bigOr l)))) hboxC) hdiaC_t
      rcases l with _ | ⟨x, xs⟩
      · have hdbot : ((◇(Proposition.bot : Proposition (Atom ⊕ Atom))).imp Proposition.bot) ∈ t :=
          ht.closed [] _ (fun _ h => nomatch h) cs5Combined_dia_bot_imp_bot
        exact hex (mem_head_mp ht.closed hdbot hdiaBigOr)
      · obtain ⟨Bs, hBseq, hBsH⟩ := cs5Combined_extract_box_list (H := t) (x :: xs) hl
        have hdiaBigOr' : (◇(Metalogic.bigOr (Bs.map Proposition.box))) ∈ t :=
          hBseq ▸ hdiaBigOr
        have hchain : ((◇(Metalogic.bigOr (Bs.map Proposition.box))).imp
            (Metalogic.bigOr Bs)) ∈ t :=
          ht.closed [] _ (fun _ h => nomatch h) ⟨cs5Combined_dia_or_box_imp_bigOr Bs⟩
        have hBigOrBs : Metalogic.bigOr Bs ∈ t := mem_head_mp ht.closed hchain hdiaBigOr'
        rcases Bs with _ | ⟨B, rest⟩
        · exact absurd hBseq (List.cons_ne_nil x xs)
        · obtain ⟨C, hCmem, hCt⟩ := cs5Combined_quasiPrime_bigOr_mem ht B rest hBigOrBs
          exact absurd hCt (hBsH C hCmem)
    obtain ⟨V, hSV, hVprime, hVexcl⟩ :=
      cs5Combined_quasi_prime_set_exclusion
        (modalDeductiveClosure_closed (fun φ ψ => .base (.implyK φ ψ))
          (fun φ ψ χ => .base (.implyS φ ψ χ)))
        hExcl
    refine ⟨V, hVprime, fun B hB => hSV (modal_subset_deductive_closure _ _ (Or.inr hB)), ht,
      ?_, fun B hB => hSV (modal_subset_deductive_closure _ _ (Or.inl hB))⟩
    intro B hBV
    by_contra hBt
    have hBoxBmemE : Proposition.box B ∈ {x | ∃ B, x = Proposition.box B ∧ B ∉ t} := ⟨B, rfl, hBt⟩
    have hdisjV : Proposition.box B ∈ V :=
      hVprime.closed [Proposition.box B] _
        (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hBV, nomatch h])
        ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩
    refine hVexcl [Proposition.box B]
      (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hBoxBmemE, nomatch h])
      (hVprime.closed [Proposition.box B] _
        (fun x hx => by rcases List.mem_cons.mp hx with rfl | h; exacts [hdisjV, nomatch h])
        ⟨.modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.base (.orI1 (Proposition.box B)
          (Proposition.bot)))) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩)

/-- Segment lift of `cs5Combined_fcsymbox_theory`. Port of `cs5_fcsymbox`. -/
theorem cs5Combined_fcsymbox {w u u' : CS5CombinedSegment Atom} (hwu : cs5CombinedMreach w u)
    (hle : u ≤ u') :
    ∃ t : CS5CombinedSegment Atom, cs5CombinedMreach u' t ∧ w ≤ t := by
  have hwu' : u.seg.head ∈ cs5CombinedTail w.seg.head := w.tail_eq ▸ hwu
  obtain ⟨T, hTmem, hwT⟩ :=
    cs5Combined_fcsymbox_theory w.seg.head_qprime u'.seg.head_qprime hwu'.2.1 hle
  refine ⟨CS5CombinedSegment.ofHead hTmem.1, ?_, hwT⟩
  change T ∈ u'.seg.tail
  rw [u'.tail_eq]
  exact hTmem

/-- Segment lift of `cs5Combined_fc4_theory`. Port of `cs5_fc4`. -/
theorem cs5Combined_fc4 {w u u' t : CS5CombinedSegment Atom} (hwu : cs5CombinedMreach w u)
    (hle : u ≤ u') (hu't : cs5CombinedMreach u' t) :
    ∃ v : CS5CombinedSegment Atom, w ≤ v ∧ cs5CombinedMreach v t := by
  have hwu' : u.seg.head ∈ cs5CombinedTail w.seg.head := w.tail_eq ▸ hwu
  have hu't' : t.seg.head ∈ cs5CombinedTail u'.seg.head := u'.tail_eq ▸ hu't
  obtain ⟨V, hVprime, hwV, hVmem⟩ :=
    cs5Combined_fc4_theory w.seg.head_qprime t.seg.head_qprime hwu'.2.1 hle hu't'.2.1 hu't'.2.2
  refine ⟨CS5CombinedSegment.ofHead hVprime, ?_, hVmem⟩
  change w.seg.head ⊆ V
  exact hwV

/-- **The canonical `CS5Combined` model satisfies the weakened frame condition `cs5FC''`.** Port
of `cs5FC''_cs5Mreach`. -/
theorem cs5CombinedFC''_cs5CombinedMreach : cs5FC'' (@cs5CombinedMreach Atom) :=
  ⟨cs5Combined_refl, fun h1 h2 => cs5Combined_trans h1 h2, fun h => cs5Combined_symm h,
   fun h1 h2 h3 => cs5Combined_fc4 h1 h2 h3, fun h1 h2 => cs5Combined_fcsymbox h1 h2⟩

end Cslib.Logic.Modal

end
