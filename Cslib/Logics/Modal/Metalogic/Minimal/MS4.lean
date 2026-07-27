/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Minimal.MinExtension

/-! # MS4: Minimal Modal Logic S4 (Soundness + Completeness)

This module instantiates the frame-condition-parametrized, `Axioms`-generic scaffold
(`MinExtension.lean`) at `MS4`, the minimal-base analogue of Simpson's `IS4` ([Simpson1994]
Ch. 3): `MS4` = `MT` (`MT.lean`) + the `4` axiom schemata. As with `T`, `4` needs **both** a
box-form and a diamond-form schema, `fourBox : □A → □□A` and `fourDia : ◇◇A → ◇A`, since `◇` is
primitive (Wijesekera 1990). `MS4ModalAxiom` copies `MTModalAxiom`'s 14 constructors verbatim (not
by import-reference -- `shake` decides, per the plan's import-chain caveat) plus `fourBox`/
`fourDia`.

The frame condition corresponding to `{tBox, tDia, fourBox, fourDia}` is reflexivity **and**
transitivity of `r`, expressed here via a LOCAL predicate `ms4FC` -- **not** Mathlib's
`Reflexive`/`Transitive` (deprecated in the pinned Mathlib; see `MT.lean`'s module docstring).

All `MinExtension.lean` assets are reused unchanged, instantiated at `Axioms := MS4ModalAxiom`;
the only new work is the two `fourBox`/`fourDia` soundness cases and the canonical-transitivity
closure proof (`min_canonical_transitive_ms4`), both fully positive.

## Main Definitions

- `MS4ModalAxiom`: `MT`'s 14 schemata plus `fourBox`/`fourDia`.
- `ms4FC`: the reflexivity-and-transitivity frame condition on a raw relation `r`.
- `ms4_axiom_sound`/`ms4_soundness`/`ms4_soundness_derivable`: birelational soundness for `MS4`
  over reflexive-and-transitive frames (`MValidFC ms4FC`).
- `min_canonical_reflexive_ms4`/`min_canonical_transitive_ms4`/`min_canonical_ms4FC`: the
  canonical relation `MinExt.minCanonicalR` (over `MS4ModalAxiom`) is reflexive and transitive.
- `ms4_completeness`/`ms4_consistent`/`ms4_soundness_completeness`: instantiation of
  `MinExtension.lean`'s parametric `mkvalidFC_completeness` at `Axioms := MS4ModalAxiom`,
  `FC := ms4FC`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational frame classes for `S4`, `MValid`).
* D. Wijesekera, *Constructive Modal Logics I*, Annals of Pure and Applied Logic, 1990 --
  primitive-`◇` canonical accessibility (both box/diamond `4`-forms are required).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `MS4` Axiom Schemata -/

/-- Axiom schemata for minimal modal logic `MS4` ([Simpson1994], Ch. 3): the 14 `MTModalAxiom`
constructors verbatim, plus the two `4` schemata `fourBox`/`fourDia`. Both box and diamond forms
are required since `◇` is primitive (not `□`-definable) in this framework's `Modal.Proposition`
datatype (Wijesekera 1990; `minCanonicalR`'s two-clause shape). -/
inductive MS4ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      MS4ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      MS4ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      MS4ModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      MS4ModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      MS4ModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      MS4ModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      MS4ModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      MS4ModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- `k1` / Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      MS4ModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- `k2` / Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      MS4ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `k3` / Cd (Fischer-Servi): `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`. -/
  | cd (φ ψ : Proposition Atom) :
      MS4ModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- `k4` / Idb (Fischer-Servi): `(◇φ → □ψ) → □(φ → ψ)`. -/
  | idb (φ ψ : Proposition Atom) :
      MS4ModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      MS4ModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      MS4ModalAxiom (φ.imp (◇φ))
  /-- `4` box form: `□A → □□A`. -/
  | fourBox (φ : Proposition Atom) :
      MS4ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- `4` diamond form: `◇◇A → ◇A`. -/
  | fourDia (φ : Proposition Atom) :
      MS4ModalAxiom ((◇◇φ).imp (◇φ))

/-! ## `MS4` Frame Condition -/

/-- The `MS4` frame condition: reflexivity **and** transitivity of the modal accessibility
relation `r`. LOCAL predicate, **not** Mathlib's `Reflexive`/`Transitive` (deprecated in the
pinned Mathlib -- see `MT.lean`'s module docstring). -/
def ms4FC {World : Type*} (r : World → World → Prop) : Prop :=
  (∀ w, r w w) ∧ (∀ {w x y}, r w x → r x y → r w y)

/-! ## Soundness -/

/-- Every `MS4ModalAxiom` instance is `MValidFC ms4FC` (birelational validity over reflexive and
transitive frames, arbitrary `botForces`).

The 14 non-`4` cases are `mt_axiom_sound`'s cases verbatim (`MT.lean`), with `htrans` threaded
through unused. The two new cases:
- `fourDia` (`◇◇A → ◇A`): the two diamond witnesses compose via `htrans`.
- `fourBox` (`□A → □□A`): `f2` (down-confluence) relocates, then `htrans` composes, closing via
  `hbox` (the `idb` pattern). -/
theorem ms4_axiom_sound {φ : Proposition Atom} (h_ax : MS4ModalAxiom φ) :
    MValidFC.{u, v} ms4FC φ := by
  intro World _ r hfc f1 f2 val botForces v_uc bf_uc w
  obtain ⟨hrefl, htrans⟩ := hfc
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
  | fourBox φ =>
    intro w' _ hbox w'' hw'' u hru w''' hw''' v hrv
    obtain ⟨w2, hw''w2, hrw2w'''⟩ := f2 hru hw'''
    exact hbox w2 (le_trans hw'' hw''w2) v (htrans hrw2w''' hrv)
  | fourDia φ =>
    intro w' _ hdia
    obtain ⟨u, hru, t, hut, hφt⟩ := hdia
    exact ⟨t, htrans hru hut, hφt⟩

/-- **Soundness**: if `DerivationTree MS4ModalAxiom Γ φ`, then for any birelational frame
(arbitrary `botForces`) whose relation `r` is reflexive and transitive, and world `w` where all
formulas in `Γ` are forced, `φ` is also forced at `w`. -/
theorem ms4_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree MS4ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (hrefl : ∀ w, r w w)
    (htrans : ∀ {w x y}, r w x → r x y → r w y)
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
    exact ms4_axiom_sound h_ax World r ⟨hrefl, htrans⟩ f1 f2 val botForces v_uc bf_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact ms4_soundness d₁ r hrefl htrans f1 f2 val botForces v_uc bf_uc w h_ctx w (le_refl w)
      (ms4_soundness d₂ r hrefl htrans f1 f2 val botForces v_uc bf_uc w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact ms4_soundness d' r hrefl htrans f1 f2 val botForces v_uc bf_uc u (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact ms4_soundness d' r hrefl htrans f1 f2 val botForces v_uc bf_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable MS4ModalAxiom φ`, then `φ` is
`MValidFC ms4FC`. -/
theorem ms4_soundness_derivable {φ : Proposition Atom}
    (h : Derivable MS4ModalAxiom φ) : MValidFC.{u, v} ms4FC φ := by
  intro World _ r hfc f1 f2 val botForces v_uc bf_uc w
  obtain ⟨hrefl, htrans⟩ := hfc
  obtain ⟨d⟩ := h
  exact ms4_soundness d r hrefl htrans f1 f2 val botForces v_uc bf_uc w (fun _ h => nomatch h)

/-! ## Completeness and Consistency -/

/-- **Canonical reflexivity**: identical proof to `min_canonical_reflexive_mt` (`MT.lean`), using
the `tBox`/`tDia` constructors inherited by `MS4ModalAxiom`. Positive closure via
`min_axiom_mem`/`min_imp_property`. -/
theorem min_canonical_reflexive_ms4 :
    (∀ w, @MinExt.minCanonicalR Atom MS4ModalAxiom w w) := by
  intro w
  refine ⟨?_, ?_⟩
  · intro φ hbox
    exact min_imp_property (min_axiom_mem (MS4ModalAxiom.tBox φ)) hbox
  · intro φ hφ
    exact min_imp_property (min_axiom_mem (MS4ModalAxiom.tDia φ)) hφ

/-- **Canonical transitivity**: the canonical relation `MinExt.minCanonicalR` (over
`MS4ModalAxiom`) is transitive. Both clauses are discharged positively via
`min_axiom_mem`/`min_imp_property` (no `by_contra`, no negation):
- box clause (given `minCanonicalR w u`, `minCanonicalR u v`, `□φ ∈ w.val`, show `φ ∈ v.val`):
  `min_axiom_mem (fourBox φ)` places `(□φ → □□φ) ∈ w.val`; MP with `□φ ∈ w.val` gives
  `□□φ ∈ w.val`; `hwu.1 (□φ)` gives `□φ ∈ u.val`; `huv.1 φ` gives `φ ∈ v.val`.
- dia clause (given `minCanonicalR w u`, `minCanonicalR u v`, `φ ∈ v.val`, show `◇φ ∈ w.val`):
  `huv.2 φ` gives `◇φ ∈ u.val`; `hwu.2 (◇φ)` gives `◇◇φ ∈ w.val`; `min_axiom_mem (fourDia φ)`
  places `(◇◇φ → ◇φ) ∈ w.val`; MP closes it. -/
theorem min_canonical_transitive_ms4 :
    (∀ {w x y : MinExt.MinCanonicalPrimeWorld MS4ModalAxiom},
      @MinExt.minCanonicalR Atom MS4ModalAxiom w x → @MinExt.minCanonicalR Atom MS4ModalAxiom x y →
      @MinExt.minCanonicalR Atom MS4ModalAxiom w y) := by
  intro w u v hwu huv
  refine ⟨?_, ?_⟩
  · intro φ hbox
    have hboxbox : (Proposition.box (Proposition.box φ)) ∈ w.val :=
      min_imp_property (min_axiom_mem (MS4ModalAxiom.fourBox φ)) hbox
    have hbox_u : (Proposition.box φ) ∈ u.val := hwu.1 (Proposition.box φ) hboxbox
    exact huv.1 φ hbox_u
  · intro φ hφ
    have hdia_u : (◇φ) ∈ u.val := huv.2 φ hφ
    have hdiadia_w : (◇◇φ) ∈ w.val := hwu.2 (◇φ) hdia_u
    exact min_imp_property (min_axiom_mem (MS4ModalAxiom.fourDia φ)) hdiadia_w

/-- **Canonical frame condition for `MS4`**: bundles `min_canonical_reflexive_ms4` and
`min_canonical_transitive_ms4` into `ms4FC (@MinExt.minCanonicalR Atom MS4ModalAxiom)`. -/
theorem min_canonical_ms4FC : ms4FC (@MinExt.minCanonicalR Atom MS4ModalAxiom) :=
  ⟨min_canonical_reflexive_ms4, min_canonical_transitive_ms4⟩

/-- **Completeness for `MS4`**: any formula that is `MValidFC ms4FC` (forced at every world of
every reflexive-and-transitive birelational model) is derivable from `MS4ModalAxiom`.
Instantiation of `MinExtension.lean`'s parametric `mkvalidFC_completeness` at
`Axioms := MS4ModalAxiom`, `FC := ms4FC`, `h_canonFC := min_canonical_ms4FC`. -/
theorem ms4_completeness {φ : Proposition Atom} (h_valid : MValidFC.{u, u} ms4FC φ) :
    Derivable MS4ModalAxiom φ :=
  mkvalidFC_completeness ms4FC
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .cd φ ψ) (fun φ ψ => .idb φ ψ)
    min_canonical_ms4FC
    h_valid

/-- **Consistency of `MS4`**: `⊥` is not derivable from `MS4ModalAxiom`. Corollary of soundness,
via the trivial reflexive-and-transitive one-point birelational frame on `ℕ` (any world, e.g.
`0`), mirroring `mt_consistent` (`MT.lean`). -/
theorem ms4_consistent : ¬ Derivable MS4ModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  have hforces : BForces (fun _ _ : ℕ => True) (fun (_ : ℕ) (_ : Atom) => False)
      (fun _ : ℕ => False) 0 (Proposition.bot : Proposition Atom) :=
    ms4_soundness_derivable h ℕ (fun _ _ => True) ⟨fun _ => trivial, fun _ _ => trivial⟩
      (fun {_ _ u} _ _ => ⟨u, trivial, le_refl u⟩)
      (fun {w0 _ _} _ _ => ⟨w0, le_refl w0, trivial⟩)
      (fun _ _ => False) (fun _ : ℕ => False) (fun _ _ h => h) (fun _ h => h.elim) 0
  exact hforces

/-- **Soundness-completeness biconditional for `MS4`**: `φ` is `MValidFC ms4FC` iff `φ` is
derivable from `MS4ModalAxiom`. -/
theorem ms4_soundness_completeness {φ : Proposition Atom} :
    MValidFC.{u, u} ms4FC φ ↔ Derivable MS4ModalAxiom φ :=
  ⟨ms4_completeness, ms4_soundness_derivable⟩

end Cslib.Logic.Modal
