/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IT

/-! # IS4: Intuitionistic Modal Logic S4 (Soundness + Completeness)

This module instantiates the frame-condition-parametrized scaffold (`Extension.lean`) at
Simpson's `IS4` ([Simpson1994] Ch. 3), the intuitionistic analogue of classical `S4`: `IS4` = `IT`
(`IT.lean`) + the `4` axiom schemata. As with `T`, `4` needs **both** a box-form and a
diamond-form schema, `fourBox : □A → □□A` and `fourDia : ◇◇A → ◇A`, since `◇` is primitive and not
`□`-definable intuitionistically (Wijesekera 1990), mirroring the two-clause shape of
`canonicalR` (`CanonicalModel.lean:117`) and `IT`'s `tBox`/`tDia` split.

The frame condition corresponding to `{tBox, tDia, fourBox, fourDia}` is reflexivity **and**
transitivity of the modal accessibility relation `r`, expressed here via a local predicate
`is4FC` on the raw relation (matching the shape `IValidFC`/`ivalidFC_completeness` require:
`{World : Type*} → (World → World → Prop) → Prop`). `is4FC` mirrors `IT`'s own `itFC`
(`IT.lean:128`) and the classical file's `s4FC` (`Systems/S4/Completeness.lean`, stated over a
bundled `Model`); it is **not** Mathlib's `Reflexive`/`Transitive` (deprecated in the pinned
Mathlib -- see `IT.lean`'s module docstring) -- same semantic content
(`(∀ w, r w w) ∧ (∀ w x y, r w x → r x y → r w y)`), different (undeprecated, local) name.

All `Extension.lean`/`IT.lean` assets (`canonicalR`, `canonical_f1`/`canonical_f2`,
`canonical_imp_property`, `axiom_mem`, `IValidFC`, `ivalidFC_completeness`) are reused unchanged;
the only new work is the two `fourBox`/`fourDia` soundness cases and the canonical-transitivity
closure proof (`is4_canonical_transitive`), both fully positive (no `by_contra`, no negation).

## Main Definitions

- `IS4ModalAxiom`: `ITModalAxiom`'s 16 constructors plus `fourBox`/`fourDia`.
- `is4FC`: the reflexivity-and-transitivity frame condition on a raw relation `r`.
- `is4_axiom_sound`/`is4_soundness`/`is4_soundness_derivable`: birelational soundness for `IS4`
  over reflexive-and-transitive frames (`IValidFC is4FC`).
- `is4_canonical_reflexive`/`is4_canonical_transitive`: the canonical relation `canonicalR` (over
  `IS4ModalAxiom`) is reflexive and transitive -- both proved positively via
  `axiom_mem`/`canonical_imp_property`, no negation.
- `is4_completeness`/`is4_consistent`/`is4_soundness_completeness`: instantiations of
  `Extension.lean`'s parametric `ivalidFC_completeness` at `Axioms := IS4ModalAxiom`, `FC := is4FC`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational frame classes for `S4`, `IValid`).
* D. Wijesekera, *Constructive Modal Logics I*, Annals of Pure and Applied Logic, 1990 --
  primitive-`◇` canonical accessibility (both box/diamond `4`-forms are required).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `IS4` Axiom Schemata -/

/-- Axiom schemata for intuitionistic modal logic `IS4` ([Simpson1994], Ch. 3): the 16
`ITModalAxiom` constructors verbatim, plus the two `4` schemata `fourBox`/`fourDia`. Both box and
diamond forms are required since `◇` is primitive (not `□`-definable) in this framework's
`Modal.Proposition` datatype (Wijesekera 1990; `canonicalR`'s two-clause shape). -/
inductive IS4ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      IS4ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      IS4ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      IS4ModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      IS4ModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      IS4ModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      IS4ModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      IS4ModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      IS4ModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      IS4ModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- `k1` / Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      IS4ModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- `k2` / Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      IS4ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `k3` / Cd (Fischer-Servi): `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`. -/
  | cd (φ ψ : Proposition Atom) :
      IS4ModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- `k4` / Idb (Fischer-Servi): `(◇φ → □ψ) → □(φ → ψ)`. -/
  | idb (φ ψ : Proposition Atom) :
      IS4ModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
  /-- `k5` / Nd: `◇⊥ → ⊥`. -/
  | dbot :
      IS4ModalAxiom ((◇Proposition.bot).imp Proposition.bot)
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      IS4ModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      IS4ModalAxiom (φ.imp (◇φ))
  /-- `4` box form: `□A → □□A`. -/
  | fourBox (φ : Proposition Atom) :
      IS4ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- `4` diamond form: `◇◇A → ◇A`. -/
  | fourDia (φ : Proposition Atom) :
      IS4ModalAxiom ((◇◇φ).imp (◇φ))

/-! ## `IS4` Frame Condition -/

/-- The `IS4` frame condition: reflexivity **and** transitivity of the modal accessibility
relation `r`. Mirrors `IT`'s `itFC` (`IT.lean:128`) and the classical `s4FC`
(`Systems/S4/Completeness.lean`), adapted from a bundled `Model` argument to the raw relation
`IValidFC`/`canonicalR` operate on. Defined locally rather than reusing Mathlib's
`Reflexive`/`Transitive` (deprecated in the pinned Mathlib -- see `IT.lean`'s module docstring). -/
def is4FC {World : Type*} (r : World → World → Prop) : Prop :=
  (∀ w, r w w) ∧ (∀ {w x y}, r w x → r x y → r w y)

/-! ## Soundness -/

/-- Every `IS4ModalAxiom` instance is `IValidFC is4FC` (birelational validity over reflexive and
transitive frames, intuitionistic falsum semantics `botForces := fun _ => False`).

The 16 non-`4` cases are `it_axiom_sound`'s cases verbatim (`IT.lean:141-201`), with `htrans`
threaded through unused. The two new cases:
- `fourDia` (`◇◇A → ◇A`): after the single `imp`-unfold, the two diamond witnesses `u`/`t`
  compose into a single accessible world `t` via `htrans hru hut` -- no relocation needed.
- `fourBox` (`□A → □□A`): the nested box goal introduces `w''`/`u`/`w'''`/`v` with `r w'' u` and
  `u ≤ w'''`; `f2` (down-confluence) relocates to a world `w2 ≥ w''` with `r w2 w'''`, then
  `htrans` composes `r w2 w'''` with `r w''' v` into `r w2 v`, closing via `hbox` at `w2`
  (exactly the `idb` pattern, `IK.lean:178-184`). -/
theorem is4_axiom_sound {φ : Proposition Atom} (h_ax : IS4ModalAxiom φ) :
    IValidFC.{u, v} is4FC φ := by
  intro World _ r hfc f1 f2 val v_uc w
  obtain ⟨hrefl, htrans⟩ := hfc
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
    intro w' _ hbox
    exact hbox w' (le_refl w') w' (hrefl w')
  | tDia φ =>
    intro w' _ hφ
    exact ⟨w', hrefl w', hφ⟩
  | fourBox φ =>
    -- Goal: ∀ w' ≥ w, □φ@w' → □□φ@w'.
    intro w' _ hbox w'' hw'' u hru w''' hw''' v hrv
    -- Relocate `r w'' u`/`u ≤ w'''` upward via F2 (down-confluence) to `r w2 w'''`.
    obtain ⟨w2, hw''w2, hrw2w'''⟩ := f2 hru hw'''
    exact hbox w2 (le_trans hw'' hw''w2) v (htrans hrw2w''' hrv)
  | fourDia φ =>
    -- Goal: ∀ w' ≥ w, ◇◇φ@w' → ◇φ@w'.
    intro w' _ hdia
    obtain ⟨u, hru, t, hut, hφt⟩ := hdia
    exact ⟨t, htrans hru hut, hφt⟩

/-- **Soundness**: if `DerivationTree IS4ModalAxiom Γ φ`, then for any birelational frame (with
`botForces := fun _ => False`) whose relation `r` is reflexive and transitive, and world `w`
where all formulas in `Γ` are forced, `φ` is also forced at `w`. Structural analogue of
`it_soundness` (`IT.lean:207-234`), threading `hrefl`/`htrans` through unused except at the
`.ax` case. -/
theorem is4_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree IS4ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (hrefl : ∀ w, r w w)
    (htrans : ∀ {w x y}, r w x → r x y → r w y)
    (f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BForces r val (fun _ => False) w ψ) :
    BForces r val (fun _ => False) w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact is4_axiom_sound h_ax World r ⟨hrefl, htrans⟩ f1 f2 val v_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact is4_soundness d₁ r hrefl htrans f1 f2 val v_uc w h_ctx w (le_refl w)
      (is4_soundness d₂ r hrefl htrans f1 f2 val v_uc w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact is4_soundness d' r hrefl htrans f1 f2 val v_uc u (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact is4_soundness d' r hrefl htrans f1 f2 val v_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable IS4ModalAxiom φ`, then `φ` is
`IValidFC is4FC`. -/
theorem is4_soundness_derivable {φ : Proposition Atom}
    (h : Derivable IS4ModalAxiom φ) : IValidFC.{u, v} is4FC φ := by
  intro World _ r hfc f1 f2 val v_uc w
  obtain ⟨hrefl, htrans⟩ := hfc
  obtain ⟨d⟩ := h
  exact is4_soundness d r hrefl htrans f1 f2 val v_uc w (fun _ h => nomatch h)

/-! ## Completeness and Consistency -/

/-- **Canonical reflexivity**: the canonical relation `canonicalR` (over `IS4ModalAxiom`) is
reflexive. Identical proof to `it_canonical_reflexive` (`IT.lean:252-258`), using the `tBox`/
`tDia` constructors inherited by `IS4ModalAxiom`. Both clauses are discharged positively via
`axiom_mem`/`canonical_imp_property` (no `by_contra`, no negation). -/
theorem is4_canonical_reflexive : (∀ w, @canonicalR Atom IS4ModalAxiom w w) := by
  intro w
  refine ⟨?_, ?_⟩
  · intro φ hbox
    exact canonical_imp_property (axiom_mem (IS4ModalAxiom.tBox φ)) hbox
  · intro φ hφ
    exact canonical_imp_property (axiom_mem (IS4ModalAxiom.tDia φ)) hφ

/-- **Canonical transitivity**: the canonical relation `canonicalR` (over `IS4ModalAxiom`) is
transitive. Both clauses are discharged positively via `axiom_mem`/`canonical_imp_property`
(no `by_contra`, no negation):
- box clause (given `canonicalR w u`, `canonicalR u v`, `□φ ∈ w.val`, show `φ ∈ v.val`):
  `axiom_mem (fourBox φ)` places `(□φ → □□φ) ∈ w.val`; MP with `□φ ∈ w.val` gives
  `□□φ ∈ w.val`; `hwu.1 (□φ)` gives `□φ ∈ u.val`; `huv.1 φ` gives `φ ∈ v.val`.
- dia clause (given `canonicalR w u`, `canonicalR u v`, `φ ∈ v.val`, show `◇φ ∈ w.val`):
  `huv.2 φ` gives `◇φ ∈ u.val`; `hwu.2 (◇φ)` gives `◇◇φ ∈ w.val`; `axiom_mem (fourDia φ)` places
  `(◇◇φ → ◇φ) ∈ w.val`; MP closes it. -/
theorem is4_canonical_transitive :
    (∀ {w x y : CanonicalPrimeWorld IS4ModalAxiom},
      @canonicalR Atom IS4ModalAxiom w x → @canonicalR Atom IS4ModalAxiom x y →
      @canonicalR Atom IS4ModalAxiom w y) := by
  intro w u v hwu huv
  refine ⟨?_, ?_⟩
  · intro φ hbox
    have hboxbox : (Proposition.box (Proposition.box φ)) ∈ w.val :=
      canonical_imp_property (axiom_mem (IS4ModalAxiom.fourBox φ)) hbox
    have hbox_u : (Proposition.box φ) ∈ u.val := hwu.1 (Proposition.box φ) hboxbox
    exact huv.1 φ hbox_u
  · intro φ hφ
    have hdia_u : (◇φ) ∈ u.val := huv.2 φ hφ
    have hdiadia_w : (◇◇φ) ∈ w.val := hwu.2 (◇φ) hdia_u
    exact canonical_imp_property (axiom_mem (IS4ModalAxiom.fourDia φ)) hdiadia_w

/-- **Canonical frame condition for `IS4`**: bundles `is4_canonical_reflexive` and
`is4_canonical_transitive` into `is4FC (@canonicalR Atom IS4ModalAxiom)`. -/
theorem is4_canonical_fc : is4FC (@canonicalR Atom IS4ModalAxiom) :=
  ⟨is4_canonical_reflexive, is4_canonical_transitive⟩

/-- **Completeness for `IS4`**: any formula that is `IValidFC is4FC` (forced at every world of
every reflexive-and-transitive birelational model) is derivable from `IS4ModalAxiom`.
Instantiation of `Extension.lean`'s parametric `ivalidFC_completeness` at
`Axioms := IS4ModalAxiom`, `FC := is4FC`, `h_canonFC := is4_canonical_fc`. -/
theorem is4_completeness {φ : Proposition Atom} (h_valid : IValidFC.{u, u} is4FC φ) :
    Derivable IS4ModalAxiom φ :=
  ivalidFC_completeness is4FC
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) (fun φ => .efq φ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .idb φ ψ)
    (fun φ ψ => .cd φ ψ) .dbot
    is4_canonical_fc
    h_valid

/-- **Consistency of `IS4`**: `⊥` is not derivable from `IS4ModalAxiom`. Corollary of soundness,
via the trivial reflexive-and-transitive one-point birelational frame on `ℕ` (any world, e.g.
`0`), mirroring `it_consistent` (`IT.lean:278-286`). -/
theorem is4_consistent : ¬ Derivable IS4ModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  have hforces : BForces (fun _ _ : ℕ => True) (fun (_ : ℕ) (_ : Atom) => False)
      (fun _ : ℕ => False) 0 (Proposition.bot : Proposition Atom) :=
    is4_soundness_derivable h ℕ (fun _ _ => True) ⟨fun _ => trivial, fun _ _ => trivial⟩
      (fun {_ _ u} _ _ => ⟨u, trivial, le_refl u⟩)
      (fun {w0 _ _} _ _ => ⟨w0, le_refl w0, trivial⟩)
      (fun _ _ => False) (fun _ _ h => h) 0
  exact hforces

/-- **Soundness-completeness biconditional for `IS4`**: `φ` is `IValidFC is4FC` iff `φ` is
derivable from `IS4ModalAxiom`. -/
theorem is4_soundness_completeness {φ : Proposition Atom} :
    IValidFC.{u, u} is4FC φ ↔ Derivable IS4ModalAxiom φ :=
  ⟨is4_completeness, is4_soundness_derivable⟩

end Cslib.Logic.Modal
