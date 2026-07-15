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
noncomputable def cs5_lift_toDerivationTree_collapse {Γ : List (Proposition (Atom ⊕ Atom))}
    {φ : Proposition (Atom ⊕ Atom)} (d : DerivationTree CS5Combined Γ φ) :
    DerivationTree CS5ModalAxiom (Γ.map (Proposition.map cs5Collapse)) (φ.map cs5Collapse) :=
  ofDeriv (Metalogic.Deriv.map τ0 (toDeriv d))

/-- `Deriv`-level transport of the collapse projection. -/
theorem cs5_lift_deriv_collapse {Γ : List (Proposition (Atom ⊕ Atom))}
    {φ : Proposition (Atom ⊕ Atom)} (h : Deriv CS5Combined Γ φ) :
    Deriv CS5ModalAxiom (Γ.map (Proposition.map cs5Collapse)) (φ.map cs5Collapse) :=
  let ⟨d⟩ := h
  ⟨cs5_lift_toDerivationTree_collapse d⟩

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
noncomputable def cs5Combined_impTrans {a b c : Proposition (Atom ⊕ Atom)}
    (h1 : DerivationTree (@CS5Combined Atom) [] (a.imp b))
    (h2 : DerivationTree (@CS5Combined Atom) [] (b.imp c)) :
    DerivationTree (@CS5Combined Atom) [] (a.imp c) :=
  deductionTheorem (fun φ ψ => .base (.implyK φ ψ)) (fun φ ψ χ => .base (.implyS φ ψ χ)) [] a c
    (.modus_ponens _ _ _ (.weakening [] [a] _ h2 (fun _ h => nomatch h))
      (.modus_ponens _ _ _ (.weakening [] [a] _ h1 (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))))

/-- `⊢ □(τL B) → □(τR B)`: necessitate `crossLR B`, `K`-distribute, and compose with axiom `4`
on `τL B`. -/
noncomputable def cs5Combined_boxL_imp_boxR (B : Proposition Atom) :
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
  exact cs5Combined_impTrans hfour hstep

/-- `⊢ □(τR B) → □(τL B)`: symmetric to `cs5Combined_boxL_imp_boxR`, via `crossRL`. -/
noncomputable def cs5Combined_boxR_imp_boxL (B : Proposition Atom) :
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
  exact cs5Combined_impTrans hfour hstep

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
`cs5Combined_boxR_imp_boxL`, landing on a purely `τL`-tagged empty-context theorem that collapses
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
    cs5Combined_boxR_imp_boxL A
  have hcomb : DerivationTree (@CS5Combined Atom) []
      ((Proposition.box (Ψ.map Sum.inl)).imp (Proposition.box (A.map Sum.inl))) :=
    cs5Combined_impTrans hstep hboxRL
  have hcomb' : DerivationTree (@CS5Combined Atom) []
      (((Proposition.box Ψ).imp (Proposition.box A)).map Sum.inl) := by
    simpa [Proposition.map_imp, Proposition.map_box] using hcomb
  exact cs5_collapse_of_L_deriv (Γ := []) ⟨hcomb'⟩

end Cslib.Logic.Modal

end
