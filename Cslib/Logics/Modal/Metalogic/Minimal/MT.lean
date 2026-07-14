/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Minimal.MinExtension

/-! # MT: Minimal Modal Logic T (Soundness + Completeness)

This module instantiates the task-496 frame-condition-parametrized, `Axioms`-generic scaffold
(`MinExtension.lean`) at `MT`, the minimal-base analogue of Simpson's `IT` ([Simpson1994] Ch. 3):
`MT` = `MK` (`MK.lean`) + reflexivity (`T` axiom). `MTModalAxiom` extends `MKModalAxiom` with
**both** a box-form and a diamond-form `T` axiom, `tBox : □A → A` and `tDia : A → ◇A`; both are
needed because `◇` is primitive and not `□`-definable (Wijesekera 1990), mirroring the two-clause
shape of `minCanonicalR` (`MinCanonicalModel.lean:75`) and `IT`'s own `tBox`/`tDia` split
(`Intuitionistic/IT.lean`).

The frame condition corresponding to `{tBox, tDia}` is reflexivity of the modal accessibility
relation `r`, expressed here via a LOCAL predicate `mtFC` on the raw relation -- **not** Mathlib's
`Reflexive` (deprecated in the pinned Mathlib; see `IT.lean`'s module docstring for the same
rationale).

All `MinExtension.lean` assets (`MValidFC`, `MinExt.minCanonicalR`, `MinExt.min_canonical_f1`/`f2`,
`MinExt.min_canonical_truth_lemma`, `min_axiom_mem`, `min_imp_property`, `mkvalidFC_completeness`)
are reused unchanged, instantiated at `Axioms := MTModalAxiom`; the only new work is the two
`tBox`/`tDia` soundness cases and the canonical-reflexivity closure proof
(`min_canonical_reflexive_mt`), both fully positive (no `by_contra`, no negation).

## Main Definitions

- `MTModalAxiom`: `MKModalAxiom`'s 12 constructors plus `tBox`/`tDia`.
- `mtFC`: the reflexivity frame condition on a raw relation `r`.
- `mt_axiom_sound`/`mt_soundness`/`mt_soundness_derivable`: birelational soundness for `MT` over
  reflexive frames (`MValidFC mtFC`).
- `min_canonical_reflexive_mt`: the canonical relation `MinExt.minCanonicalR` (over `MTModalAxiom`)
  is reflexive -- proved positively via `min_axiom_mem`/`min_imp_property`, no negation.
- `mt_completeness`/`mt_consistent`/`mt_soundness_completeness`: instantiation of the task-496
  parametric `mkvalidFC_completeness` at `Axioms := MTModalAxiom`, `FC := mtFC`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational frame classes for `T`, `MValid`).
* D. Wijesekera, *Constructive Modal Logics I*, Annals of Pure and Applied Logic, 1990 --
  primitive-`◇` canonical accessibility (both box/diamond `T`-forms are required).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `MT` Axiom Schemata -/

/-- Axiom schemata for minimal modal logic `MT`: the 12 `MKModalAxiom` constructors verbatim,
plus the two `T` schemata `tBox`/`tDia`. Both box and diamond forms are required since `◇` is
primitive (not `□`-definable) in this framework's `Modal.Proposition` datatype (Wijesekera 1990;
`minCanonicalR`'s two-clause shape). -/
inductive MTModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      MTModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      MTModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      MTModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      MTModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      MTModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      MTModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      MTModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      MTModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- `k1` / Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      MTModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- `k2` / Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      MTModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `k3` / Cd (Fischer-Servi): `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`. -/
  | cd (φ ψ : Proposition Atom) :
      MTModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- `k4` / Idb (Fischer-Servi): `(◇φ → □ψ) → □(φ → ψ)`. -/
  | idb (φ ψ : Proposition Atom) :
      MTModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      MTModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      MTModalAxiom (φ.imp (◇φ))

/-! ## `MT` Frame Condition -/

/-- The `MT` frame condition: reflexivity of the modal accessibility relation `r`. LOCAL
predicate, **not** Mathlib's `Reflexive` (deprecated in the pinned Mathlib -- see `IT.lean`'s
module docstring). -/
def mtFC {World : Type*} (r : World → World → Prop) : Prop := ∀ w, r w w

/-! ## Soundness -/

/-- Every `MTModalAxiom` instance is `MValidFC mtFC` (birelational validity over reflexive
frames, with an *arbitrary* upward-closed `botForces` predicate).

The 12 non-`T` cases mirror `mk_axiom_sound`'s cases verbatim (`MK.lean:116`), with `hrefl`
threaded through unused. The two new cases:
- `tDia` (`A → ◇A`): after the single `imp`-unfold, the successor world `w'` and the forced `A`
  already coincide with the diamond witness needed, via `hrefl w'` -- no relocation needed.
- `tBox` (`□A → A`): `hbox` (forced at `□A`) instantiated at `w'` (`≤`-refl) and `w'` itself
  (`hrefl w'`) directly yields `A` at `w'`. -/
theorem mt_axiom_sound {φ : Proposition Atom} (h_ax : MTModalAxiom φ) :
    MValidFC.{u, v} mtFC φ := by
  intro World _ r hrefl f1 f2 val botForces v_uc bf_uc w
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | andI φ ψ =>
    intro w₁ _ hφ w₂ hw₂ hψ
    exact ⟨bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw₂ hφ, hψ⟩
  | andE1 φ ψ =>
    intro _ _ h; exact h.1
  | andE2 φ ψ =>
    intro _ _ h; exact h.2
  | orI1 φ ψ =>
    intro _ _ h; exact Or.inl h
  | orI2 φ ψ =>
    intro _ _ h; exact Or.inr h
  | orE φ ψ χ =>
    intro w₁ _ h_pq w₂ hw₂ h_rq w₃ hw₃ h_pr
    have hw₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pr.elim (fun hp => h_pq w₃ hw₁₃ hp) (fun hr => h_rq w₃ hw₃ hr)
  | k φ ψ =>
    intro w' _ hbox_imp w'' hw' hbox_phi w1 hw1 u hru
    exact hbox_imp w1 (le_trans hw' hw1) u hru u (le_refl u) (hbox_phi w1 hw1 u hru)
  | kdia φ ψ =>
    intro w' _ hbox_imp w'' hw' hdia_phi
    obtain ⟨u, hru, hφu⟩ := hdia_phi
    exact ⟨u, hru, hbox_imp w'' hw' u hru u (le_refl u) hφu⟩
  | cd φ ψ =>
    intro w' _ hdia
    obtain ⟨u, hru, hor⟩ := hdia
    cases hor with
    | inl hφ => exact Or.inl ⟨u, hru, hφ⟩
    | inr hψ => exact Or.inr ⟨u, hru, hψ⟩
  | idb φ ψ =>
    intro w' _ h_hyp w1 hw1 u hru v hv hφv
    obtain ⟨w1', hw1w1', hrw1'v⟩ := f2 hru hv
    have hdia_w1' : BForces r val botForces w1' (◇φ) := ⟨v, hrw1'v, hφv⟩
    exact h_hyp w1' (le_trans hw1 hw1w1') hdia_w1' w1' (le_refl w1') v hrw1'v
  | tBox φ =>
    intro w' _ hbox
    exact hbox w' (le_refl w') w' (hrefl w')
  | tDia φ =>
    intro w' _ hφ
    exact ⟨w', hrefl w', hφ⟩

/-- **Soundness**: if `DerivationTree MTModalAxiom Γ φ`, then for any birelational frame (with
*arbitrary* upward-closed `botForces`) whose relation `r` is reflexive, and world `w` where all
formulas in `Γ` are forced, `φ` is also forced at `w`. Structural analogue of `mk_soundness`
(`MK.lean:170`), threading `hrefl` through unused except at the `.ax` case. -/
theorem mt_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree MTModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (hrefl : ∀ w, r w w)
    (f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BForces r val botForces w ψ) :
    BForces r val botForces w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact mt_axiom_sound h_ax World r hrefl f1 f2 val botForces v_uc bf_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact mt_soundness d₁ r hrefl f1 f2 val botForces v_uc bf_uc w h_ctx w (le_refl w)
      (mt_soundness d₂ r hrefl f1 f2 val botForces v_uc bf_uc w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact mt_soundness d' r hrefl f1 f2 val botForces v_uc bf_uc u (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact mt_soundness d' r hrefl f1 f2 val botForces v_uc bf_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable MTModalAxiom φ`, then `φ` is
`MValidFC mtFC`. -/
theorem mt_soundness_derivable {φ : Proposition Atom}
    (h : Derivable MTModalAxiom φ) : MValidFC.{u, v} mtFC φ := by
  intro World _ r hrefl f1 f2 val botForces v_uc bf_uc w
  obtain ⟨d⟩ := h
  exact mt_soundness d r hrefl f1 f2 val botForces v_uc bf_uc w (fun _ h => nomatch h)

/-! ## Completeness and Consistency -/

/-- **Canonical reflexivity**: the canonical relation `MinExt.minCanonicalR` (over `MTModalAxiom`)
is reflexive. Both clauses are discharged positively via `min_axiom_mem`/`min_imp_property`
(no `by_contra`, no negation):
- box clause `□φ ∈ w.val → φ ∈ w.val`: `min_axiom_mem (tBox φ)` places `(□φ → φ) ∈ w.val`;
  `min_imp_property` (MP) closes it.
- dia clause `φ ∈ w.val → ◇φ ∈ w.val`: `min_axiom_mem (tDia φ)` places `(φ → ◇φ) ∈ w.val`;
  `min_imp_property` (MP) closes it. -/
theorem min_canonical_reflexive_mt :
    mtFC (@MinExt.minCanonicalR Atom MTModalAxiom) := by
  intro w
  refine ⟨?_, ?_⟩
  · intro φ hbox
    exact min_imp_property (min_axiom_mem (MTModalAxiom.tBox φ)) hbox
  · intro φ hφ
    exact min_imp_property (min_axiom_mem (MTModalAxiom.tDia φ)) hφ

/-- **Completeness for `MT`**: any formula that is `MValidFC mtFC` (forced at every world of
every reflexive birelational model, arbitrary `botForces`) is derivable from `MTModalAxiom`.
Instantiation of the task-496 parametric `mkvalidFC_completeness` at `Axioms := MTModalAxiom`,
`FC := mtFC`, `h_canonFC := min_canonical_reflexive_mt`. -/
theorem mt_completeness {φ : Proposition Atom} (h_valid : MValidFC.{u, u} mtFC φ) :
    Derivable MTModalAxiom φ :=
  mkvalidFC_completeness mtFC
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .cd φ ψ) (fun φ ψ => .idb φ ψ)
    min_canonical_reflexive_mt
    h_valid

/-- **Consistency of `MT`**: `⊥` is not derivable from `MTModalAxiom`. Corollary of soundness,
via the trivial reflexive one-point birelational frame on `ℕ` (any world, e.g. `0`), with a
*non-fallible* `botForces := fun _ => False`, mirroring `mt_soundness`'s consequence-free shape
(`mk_consistent`, `MK.lean:212`). -/
theorem mt_consistent : ¬ Derivable MTModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  have hforces : BForces (fun _ _ : ℕ => True) (fun (_ : ℕ) (_ : Atom) => False)
      (fun _ : ℕ => False) 0 (Proposition.bot : Proposition Atom) :=
    mt_soundness_derivable h ℕ (fun _ _ => True) (fun _ => trivial)
      (fun {_ _ u} _ _ => ⟨u, trivial, le_refl u⟩)
      (fun {w0 _ _} _ _ => ⟨w0, le_refl w0, trivial⟩)
      (fun _ _ => False) (fun _ : ℕ => False) (fun _ _ h => h) (fun _ h => h.elim) 0
  exact hforces

/-- **Soundness-completeness biconditional for `MT`**: `φ` is `MValidFC mtFC` iff `φ` is
derivable from `MTModalAxiom`. -/
theorem mt_soundness_completeness {φ : Proposition Atom} :
    MValidFC.{u, u} mtFC φ ↔ Derivable MTModalAxiom φ :=
  ⟨mt_completeness, mt_soundness_derivable⟩

end Cslib.Logic.Modal
