/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5

/-! # `CS5 ⊆ IS5` and Why the Product-Model-Over-`IS5` Route Is Not Adopted

This module lands the easy schema-inclusion direction `CS5 ⊆ IS5` and the machine-checked
closure argument showing why a product model over `IS5` cannot discharge the `CS5` pair-seed
obligation (`CS5Completeness.lean`) without adopting the unadopted `CS5 = IS5` collapse.

## Main Results

- `cs5Axiom_to_is5Axiom`/`cs5_deriv_to_is5`/`cs5_closure_subset_is5_closure`: every `CS5ModalAxiom`
  constructor is literally an `IS5ModalAxiom` constructor (`IS5ModalAxiom` additionally has
  `kdisj`, `kfs`, `kbot`), so `CS5`-derivability transports to `IS5`-derivability, context and all,
  and `cl_CS5(S) ⊆ cl_IS5(S)` for every `S`.
- `is5_derivable_of_boxNotMem_transport`: the route-closure theorem. If the box-backward residual
  `∀ S A, □A ∉ cl_CS5(S) → □A ∉ cl_IS5(S)` holds, then every `IS5`-derivable formula is already
  `CS5`-derivable.
- `is5_iff_cs5_derivable_of_boxNotMem_transport`: combined with the schema-inclusion direction
  above, that same residual gives `Derivable IS5ModalAxiom φ ↔ Derivable CS5ModalAxiom φ` for
  every `φ` -- i.e. the residual is exactly the `CS5 = IS5` collapse.

## Why the Product-Model-Over-`IS5` Route Is Not Adopted

The governing plan's round-2 analysis proposed a product model over `IS5` with two residuals:
R-a (the base `is5FC` model's accessibility must be total) and R-b (`H` `CS5`-closed, `□A ∉ H`
implies `□A ∉ cl_IS5(H)` -- exactly the hypothesis of `is5_derivable_of_boxNotMem_transport`
above). Instantiating R-b at `H := cl_CS5(∅)` and unfolding through
`is5_iff_cs5_derivable_of_boxNotMem_transport` yields `Derivable IS5ModalAxiom φ ↔
Derivable CS5ModalAxiom φ` for every `φ`, i.e. `IS5 = CS5` as Hilbert systems. So R-b is not a
residual gap of the product-model route -- it *is* the collapse route, whose only published basis
is Pacheco's Lemma 16/18 (the unsound argument `CS5Completeness.lean` repairs), and whose adoption
remains reserved for explicit user authorisation. R-a is independently unverified and belongs to
the frame-condition family that already produced `cs5Incest` being mechanically false on every
world type tried in `CS5Canonical.lean`; it is not separately probed here because R-b already
closes the route. The collapse's only published basis is Pacheco's `CKB = IKB` (§4), which rests
on the same unsound Lemma 16 that `CS5Completeness.lean` repairs. The cut-free nested-sequent
route (`Constructive/Nested/`) is the adopted alternative. -/

@[expose] public section

namespace Cslib.Logic.Modal

universe u
variable {Atom : Type u}

/-! ## Schema Inclusion and Derivability Transport -/

/-- **Schema inclusion.** Every `CS5` axiom instance is an `IS5` axiom instance: `IS5ModalAxiom`
is `IS4ModalAxiom`'s 18 constructors (which already cover every `CS5ModalAxiom` constructor)
plus `bBox`/`bDia`, plus the strictly intuitionistic `kdisj`/`kfs`/`kbot` absent from `CS5`. -/
theorem cs5Axiom_to_is5Axiom {φ : Proposition Atom} (h : CS5ModalAxiom φ) : IS5ModalAxiom φ := by
  cases h with
  | implyK φ ψ => exact .implyK φ ψ
  | implyS φ ψ χ => exact .implyS φ ψ χ
  | efq φ => exact .efq φ
  | andI φ ψ => exact .andI φ ψ
  | andE1 φ ψ => exact .andE1 φ ψ
  | andE2 φ ψ => exact .andE2 φ ψ
  | orI1 φ ψ => exact .orI1 φ ψ
  | orI2 φ ψ => exact .orI2 φ ψ
  | orE φ ψ χ => exact .orE φ ψ χ
  | k φ ψ => exact .k φ ψ
  | kdia φ ψ => exact .kdia φ ψ
  | tBox φ => exact .tBox φ
  | tDia φ => exact .tDia φ
  | fourBox φ => exact .fourBox φ
  | fourDia φ => exact .fourDia φ
  | bBox φ => exact .bBox φ
  | bDia φ => exact .bDia φ

/-- **Derivability transport.** `CS5`-derivability implies `IS5`-derivability, context and all. -/
theorem cs5_deriv_to_is5 {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : Deriv (@CS5ModalAxiom Atom) Γ φ) : Deriv (@IS5ModalAxiom Atom) Γ φ := by
  obtain ⟨t⟩ := d
  have h := t.map id (fun ψ hψ => by simpa using cs5Axiom_to_is5Axiom hψ)
  rw [List.map_congr_left (fun ψ _ => Proposition.map_id ψ), List.map_id_fun',
    Proposition.map_id] at h
  exact ⟨h⟩

/-- Corollary at the level of deductive closures: `cl_{CS5} S ⊆ cl_{IS5} S`. -/
theorem cs5_closure_subset_is5_closure (S : Set (Proposition Atom)) :
    modalDeductiveClosure (@CS5ModalAxiom Atom) S ⊆ modalDeductiveClosure (@IS5ModalAxiom Atom) S :=
  fun _ ⟨L, hL, hd⟩ => ⟨L, hL, cs5_deriv_to_is5 hd⟩

/-! ## The Route-Closure Theorem -/

/-- **Route closure.** If the box-backward residual `∀ S A, □A ∉ cl_CS5(S) → □A ∉ cl_IS5(S)`
holds, every `IS5`-derivable formula is already `CS5`-derivable.

Proof: given `⊢_{IS5} φ`, necessitation gives `⊢_{IS5} □φ`, i.e. `□φ ∈ cl_IS5(∅)` (since
`modalDeductiveClosure Axioms ∅` unfolds to exactly the empty-context derivations). The
contrapositive of the residual at `S := ∅`, `A := φ` then gives `□φ ∈ cl_CS5(∅)`, i.e.
`⊢_{CS5} □φ`; `tBox` and `modus_ponens` in `CS5` close `⊢_{CS5} φ`. -/
theorem is5_derivable_of_boxNotMem_transport
    (hR : ∀ (S : Set (Proposition Atom)) (A : Proposition Atom),
      Proposition.box A ∉ modalDeductiveClosure (@CS5ModalAxiom Atom) S →
        Proposition.box A ∉ modalDeductiveClosure (@IS5ModalAxiom Atom) S)
    {φ : Proposition Atom} (h : Derivable (@IS5ModalAxiom Atom) φ) :
    Derivable (@CS5ModalAxiom Atom) φ := by
  obtain ⟨d⟩ := h
  have hbox_is5 : Derivable (@IS5ModalAxiom Atom) (Proposition.box φ) := ⟨.necessitation _ d⟩
  have hmem_is5 : Proposition.box φ ∈ modalDeductiveClosure (@IS5ModalAxiom Atom) (∅ : Set _) :=
    ⟨[], fun x hx => absurd hx (List.not_mem_nil), hbox_is5⟩
  have hmem_cs5 : Proposition.box φ ∈ modalDeductiveClosure (@CS5ModalAxiom Atom) (∅ : Set _) := by
    by_contra hnot
    exact hR (∅ : Set (Proposition Atom)) φ hnot hmem_is5
  obtain ⟨L, hL, dbox⟩ := hmem_cs5
  have hLnil : L = [] :=
    List.eq_nil_iff_forall_not_mem.mpr (fun x hx => absurd (hL x hx) (Set.notMem_empty x))
  subst hLnil
  have htBox : Deriv (@CS5ModalAxiom Atom) [] ((Proposition.box φ).imp φ) :=
    ⟨.ax [] _ (CS5ModalAxiom.tBox φ)⟩
  exact mp_deriv htBox dbox

/-- **Corollary: the residual is exactly the `CS5 = IS5` collapse.** Combined with
`cs5_closure_subset_is5_closure`, the box-backward residual gives full derivability equivalence
between `IS5` and `CS5` as Hilbert systems -- this is why the product-model-over-`IS5` route is
not adopted (see the module docstring). -/
theorem is5_iff_cs5_derivable_of_boxNotMem_transport
    (hR : ∀ (S : Set (Proposition Atom)) (A : Proposition Atom),
      Proposition.box A ∉ modalDeductiveClosure (@CS5ModalAxiom Atom) S →
        Proposition.box A ∉ modalDeductiveClosure (@IS5ModalAxiom Atom) S)
    {φ : Proposition Atom} :
    Derivable (@IS5ModalAxiom Atom) φ ↔ Derivable (@CS5ModalAxiom Atom) φ :=
  ⟨is5_derivable_of_boxNotMem_transport hR,
    fun ⟨d⟩ => cs5_deriv_to_is5 (Γ := []) ⟨d⟩⟩

end Cslib.Logic.Modal
