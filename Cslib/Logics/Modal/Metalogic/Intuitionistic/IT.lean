/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.Extension

/-! # IT: Intuitionistic Modal Logic T (Soundness + Completeness)

This module instantiates the task-494 frame-condition-parametrized scaffold (`Extension.lean`)
at Simpson's `IT` ([Simpson1994] Ch. 3), the intuitionistic analogue of classical `T`: `IT` = `IK`
+ reflexivity. `ITModalAxiom` extends `IKModalAxiom` (`IK.lean`) with **both** a box-form and a
diamond-form `T` axiom, `tBox : □A → A` and `tDia : A → ◇A`; both are needed because `◇` is
primitive and not `□`-definable intuitionistically (Wijesekera 1990), mirroring the two-clause
shape of `canonicalR` (`CanonicalModel.lean:117`).

The frame condition corresponding to `{tBox, tDia}` is reflexivity of the modal accessibility
relation `r`, expressed here via a local predicate `itFC` on the raw relation (matching the shape
`IValidFC`/`ivalidFC_completeness` require: `{World : Type*} → (World → World → Prop) → Prop`).
`itFC` mirrors the classical file's own `tFC` (`Systems/T/Completeness.lean:52`, which is stated
over a bundled `Model`); it is **not** Mathlib's `Reflexive` (which is `@[deprecated]` in the
Mathlib version pinned by this project's `lake-manifest.json` -- using it would produce a
deprecation warning on every use site, violating the zero-warnings build gate) -- same semantic
content (`∀ w, r w w`), different (undeprecated, local) name.

All task-480/492/Extension assets (`canonicalR`, `canonical_f1`/`canonical_f2`,
`canonical_imp_property`, `axiom_mem`, `IValidFC`, `ivalidFC_completeness`) are reused unchanged;
the only new work is the two `tBox`/`tDia` soundness cases and the canonical-reflexivity closure
proof (`it_canonical_reflexive`), both fully positive (no `by_contra`, no negation).

## Main Definitions

- `ITModalAxiom`: `IKModalAxiom`'s 14 constructors plus `tBox`/`tDia`.
- `itFC`: the reflexivity frame condition on a raw relation `r`.
- `it_axiom_sound`/`it_soundness`/`it_soundness_derivable`: birelational soundness for `IT` over
  reflexive frames (`IValidFC itFC`).
- `it_canonical_reflexive`: the canonical relation `canonicalR` (over `ITModalAxiom`) is
  reflexive -- proved positively via `axiom_mem`/`canonical_imp_property`, no negation.
- `it_completeness`/`it_consistent`/`it_soundness_completeness`: instantiations of the task-494
  parametric `ivalidFC_completeness` at `Axioms := ITModalAxiom`, `FC := itFC`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational frame classes for `T`, `IValid`).
* D. Wijesekera, *Constructive Modal Logics I*, Annals of Pure and Applied Logic, 1990 --
  primitive-`◇` canonical accessibility (both box/diamond `T`-forms are required).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `IT` Axiom Schemata -/

/-- Axiom schemata for intuitionistic modal logic `IT` ([Simpson1994], Ch. 3): the 14
`IKModalAxiom` constructors verbatim, plus the two `T` schemata `tBox`/`tDia`. Both box and
diamond forms are required since `◇` is primitive (not `□`-definable) in this framework's
`Modal.Proposition` datatype (Wijesekera 1990; `canonicalR`'s two-clause shape). -/
inductive ITModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      ITModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      ITModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      ITModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      ITModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      ITModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      ITModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      ITModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      ITModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      ITModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- `k1` / Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      ITModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- `k2` / Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      ITModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `k3` / Cd (Fischer-Servi): `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`. -/
  | cd (φ ψ : Proposition Atom) :
      ITModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- `k4` / Idb (Fischer-Servi): `(◇φ → □ψ) → □(φ → ψ)`. -/
  | idb (φ ψ : Proposition Atom) :
      ITModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
  /-- `k5` / Nd: `◇⊥ → ⊥`. -/
  | dbot :
      ITModalAxiom ((◇Proposition.bot).imp Proposition.bot)
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      ITModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      ITModalAxiom (φ.imp (◇φ))

/-! ## `IT` Frame Condition -/

/-- The `IT` frame condition: reflexivity of the modal accessibility relation `r`. Mirrors the
classical `tFC` (`Systems/T/Completeness.lean:52`), adapted from a bundled `Model` argument to the
raw relation `IValidFC`/`canonicalR` operate on. Defined locally rather than reusing Mathlib's
`Reflexive` (deprecated in the pinned Mathlib -- see module docstring). -/
def itFC {World : Type*} (r : World → World → Prop) : Prop := ∀ w, r w w

/-! ## Soundness -/

/-- Every `ITModalAxiom` instance is `IValidFC itFC` (birelational validity over reflexive frames,
intuitionistic falsum semantics `botForces := fun _ => False`).

The 14 non-`T` cases are `ik_axiom_sound`'s cases verbatim (`IK.lean:136-189`), with `hrefl`
threaded through unused. The two new cases:
- `tDia` (`A → ◇A`): after the single `imp`-unfold, the successor world `w'` and the forced `A`
  already coincide with the diamond witness needed, via `hrefl w'` -- no relocation needed.
- `tBox` (`□A → A`): `hbox` (forced at `□A`) instantiated at `w'` (`≤`-refl) and `w'` itself
  (`hrefl w'`) directly yields `A` at `w'`. -/
theorem it_axiom_sound {φ : Proposition Atom} (h_ax : ITModalAxiom φ) : IValidFC.{u, v} itFC φ := by
  intro World _ r hrefl f1 f2 val v_uc w
  have bf_uc : ∀ {w w' : World}, w ≤ w' →
      (fun _ : World => False) w → (fun _ : World => False) w' :=
    fun _ h => h.elim
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | efq φ =>
    intro _ _ hbot
    exact hbot.elim
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
    have hdia_w1' : BForces r val (fun _ => False) w1' (◇φ) := ⟨v, hrw1'v, hφv⟩
    exact h_hyp w1' (le_trans hw1 hw1w1') hdia_w1' w1' (le_refl w1') v hrw1'v
  | dbot =>
    intro w' _ hdia
    obtain ⟨_, _, hfalse⟩ := hdia
    exact hfalse.elim
  | tBox φ =>
    -- Goal: ∀ w' ≥ w, □φ@w' → φ@w'; `□φ@w'` unfolds to `∀ w'' ≥ w', ∀ u, r w'' u → φ@u`.
    intro w' _ hbox
    exact hbox w' (le_refl w') w' (hrefl w')
  | tDia φ =>
    -- Goal: ∀ w' ≥ w, φ@w' → ◇φ@w'; witness u := w' via `hrefl w'`.
    intro w' _ hφ
    exact ⟨w', hrefl w', hφ⟩

/-- **Soundness**: if `DerivationTree ITModalAxiom Γ φ`, then for any birelational frame (with
`botForces := fun _ => False`) whose relation `r` is reflexive, and world `w` where all formulas
in `Γ` are forced, `φ` is also forced at `w`. Structural analogue of `ik_soundness`
(`IK.lean:197-222`), threading `hrefl` through unused except at the `.ax` case. -/
theorem it_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree ITModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (hrefl : ∀ w, r w w)
    (f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BForces r val (fun _ => False) w ψ) :
    BForces r val (fun _ => False) w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact it_axiom_sound h_ax World r hrefl f1 f2 val v_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact it_soundness d₁ r hrefl f1 f2 val v_uc w h_ctx w (le_refl w)
      (it_soundness d₂ r hrefl f1 f2 val v_uc w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact it_soundness d' r hrefl f1 f2 val v_uc u (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact it_soundness d' r hrefl f1 f2 val v_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable ITModalAxiom φ`, then `φ` is
`IValidFC itFC`. -/
theorem it_soundness_derivable {φ : Proposition Atom}
    (h : Derivable ITModalAxiom φ) : IValidFC.{u, v} itFC φ := by
  intro World _ r hrefl f1 f2 val v_uc w
  obtain ⟨d⟩ := h
  exact it_soundness d r hrefl f1 f2 val v_uc w (fun _ h => nomatch h)

/-! ## Completeness and Consistency -/

/-- **Canonical reflexivity**: the canonical relation `canonicalR` (over `ITModalAxiom`) is
reflexive. Both clauses are discharged positively via `axiom_mem`/`canonical_imp_property`
(no `by_contra`, no negation):
- box clause `□φ ∈ w.val → φ ∈ w.val`: `axiom_mem (tBox φ)` places `(□φ → φ) ∈ w.val`;
  `canonical_imp_property` (MP) closes it.
- dia clause `φ ∈ w.val → ◇φ ∈ w.val`: `axiom_mem (tDia φ)` places `(φ → ◇φ) ∈ w.val`;
  `canonical_imp_property` (MP) closes it. -/
theorem it_canonical_reflexive : itFC (@canonicalR Atom ITModalAxiom) := by
  intro w
  refine ⟨?_, ?_⟩
  · intro φ hbox
    exact canonical_imp_property (axiom_mem (ITModalAxiom.tBox φ)) hbox
  · intro φ hφ
    exact canonical_imp_property (axiom_mem (ITModalAxiom.tDia φ)) hφ

/-- **Completeness for `IT`**: any formula that is `IValidFC itFC` (forced at every world of
every reflexive birelational model) is derivable from `ITModalAxiom`. Instantiation of the
task-494 parametric `ivalidFC_completeness` at `Axioms := ITModalAxiom`, `FC := itFC`,
`h_canonFC := it_canonical_reflexive`. -/
theorem it_completeness {φ : Proposition Atom} (h_valid : IValidFC.{u, u} itFC φ) :
    Derivable ITModalAxiom φ :=
  ivalidFC_completeness itFC
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) (fun φ => .efq φ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .idb φ ψ)
    (fun φ ψ => .cd φ ψ) .dbot
    it_canonical_reflexive
    h_valid

/-- **Consistency of `IT`**: `⊥` is not derivable from `ITModalAxiom`. Corollary of soundness,
via the trivial reflexive one-point birelational frame on `ℕ` (any world, e.g. `0`), mirroring
`ik_consistent` (`IK.lean:248-256`). -/
theorem it_consistent : ¬ Derivable ITModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  have hforces : BForces (fun _ _ : ℕ => True) (fun (_ : ℕ) (_ : Atom) => False)
      (fun _ : ℕ => False) 0 (Proposition.bot : Proposition Atom) :=
    it_soundness_derivable h ℕ (fun _ _ => True) (fun _ => trivial)
      (fun {_ _ u} _ _ => ⟨u, trivial, le_refl u⟩)
      (fun {w0 _ _} _ _ => ⟨w0, le_refl w0, trivial⟩)
      (fun _ _ => False) (fun _ _ h => h) 0
  exact hforces

/-- **Soundness-completeness biconditional for `IT`**: `φ` is `IValidFC itFC` iff `φ` is
derivable from `ITModalAxiom`. -/
theorem it_soundness_completeness {φ : Proposition Atom} :
    IValidFC.{u, u} itFC φ ↔ Derivable ITModalAxiom φ :=
  ⟨it_completeness, it_soundness_derivable⟩

end Cslib.Logic.Modal
