/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Minimal.MinExtension

/-! # MS5: Minimal Modal Logic S5 (Soundness + Completeness)

This module instantiates the task-496 frame-condition-parametrized, `Axioms`-generic scaffold
(`MinExtension.lean`) at `MS5`, the minimal-base analogue of Simpson's `IS5` ([Simpson1994]
Ch. 3): `MS5` = `MS4` (`MS4.lean`) + the `B` axiom schemata. As with `T`/`4`, `B` needs **both** a
box-form and a diamond-form schema, `bBox : A → □◇A` and `bDia : ◇□A → A`, since `◇` is primitive
(Wijesekera 1990).

**`MS5` is axiomatized here via `B` (symmetry), NOT via the classical euclidean/`5` axiom
`◇A → □◇A`** (mirroring `IS5`, `Intuitionistic/IS5.lean`, and the research report's Deliverable 6
finding). The classical canonical euclideanness proof is a `by_contra` + negation-completeness
argument that has no analogue for quasi-prime (non-negation-complete) worlds. Symmetry closure
from `B` is fully positive/constructive (MP-closure only, `min_imp_property`) and transfers
cleanly. Reflexivity (`T`) + transitivity (`4`) + symmetry (`B`) together give an **equivalence
relation**, Simpson's `S5` birelational frame class.

The frame condition corresponding to `{tBox, tDia, fourBox, fourDia, bBox, bDia}` is reflexivity,
transitivity, **and** symmetry of `r`, expressed here via a LOCAL predicate `ms5FC` -- **not**
Mathlib's `Reflexive`/`Transitive`/`Symmetric` (deprecated in the pinned Mathlib; see `MT.lean`'s
module docstring).

All `MinExtension.lean` assets are reused unchanged, instantiated at `Axioms := MS5ModalAxiom`;
the only new work is the two `bBox`/`bDia` soundness cases and the canonical-symmetry closure
proof (`min_canonical_symmetric_ms5`), both fully positive -- a verbatim port of
`is5_canonical_symmetric` (`Intuitionistic/IS5.lean:341`) onto the generic `MinExt` scaffold.

## Main Definitions

- `MS5ModalAxiom`: `MS4`'s 16 schemata plus `bBox`/`bDia`.
- `ms5FC`: the reflexivity-transitivity-symmetry frame condition on a raw relation `r`.
- `ms5_axiom_sound`/`ms5_soundness`/`ms5_soundness_derivable`: birelational soundness for `MS5`
  over reflexive-transitive-symmetric frames (`MValidFC ms5FC`).
- `min_canonical_symmetric_ms5`/`min_canonical_ms5FC`: the canonical relation
  `MinExt.minCanonicalR` (over `MS5ModalAxiom`) is symmetric (bundled with refl/trans).
- `ms5_completeness`/`ms5_consistent`/`ms5_soundness_completeness`: instantiation of the task-496
  parametric `mkvalidFC_completeness` at `Axioms := MS5ModalAxiom`, `FC := ms5FC`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational frame classes for `S5`, `MValid`).
* D. Wijesekera, *Constructive Modal Logics I*, Annals of Pure and Applied Logic, 1990 --
  primitive-`◇` canonical accessibility (both box/diamond `B`-forms are required).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `MS5` Axiom Schemata -/

/-- Axiom schemata for minimal modal logic `MS5` ([Simpson1994], Ch. 3): the 16 `MS4ModalAxiom`
constructors verbatim, plus the two `B` schemata `bBox`/`bDia`. Both box and diamond forms are
required since `◇` is primitive (not `□`-definable) in this framework's `Modal.Proposition`
datatype (Wijesekera 1990; `minCanonicalR`'s two-clause shape). Deliberately **not** the classical
euclidean/`5` axiom `◇A → □◇A` (see module docstring: its canonical proof is non-transferable to
quasi-prime theories). -/
inductive MS5ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      MS5ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      MS5ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      MS5ModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      MS5ModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      MS5ModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      MS5ModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      MS5ModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      MS5ModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- `k1` / Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      MS5ModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- `k2` / Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      MS5ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `k3` / Cd (Fischer-Servi): `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`. -/
  | cd (φ ψ : Proposition Atom) :
      MS5ModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- `k4` / Idb (Fischer-Servi): `(◇φ → □ψ) → □(φ → ψ)`. -/
  | idb (φ ψ : Proposition Atom) :
      MS5ModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      MS5ModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      MS5ModalAxiom (φ.imp (◇φ))
  /-- `4` box form: `□A → □□A`. -/
  | fourBox (φ : Proposition Atom) :
      MS5ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- `4` diamond form: `◇◇A → ◇A`. -/
  | fourDia (φ : Proposition Atom) :
      MS5ModalAxiom ((◇◇φ).imp (◇φ))
  /-- `B` box form: `A → □◇A`. -/
  | bBox (φ : Proposition Atom) :
      MS5ModalAxiom (φ.imp (Proposition.box (◇φ)))
  /-- `B` diamond form: `◇□A → A`. -/
  | bDia (φ : Proposition Atom) :
      MS5ModalAxiom ((◇(Proposition.box φ)).imp φ)

/-! ## `MS5` Frame Condition -/

/-- The `MS5` frame condition: reflexivity, transitivity, **and** symmetry of the modal
accessibility relation `r` (an equivalence relation). LOCAL predicate, **not** Mathlib's
`Reflexive`/`Transitive`/`Symmetric` (deprecated in the pinned Mathlib -- see `MT.lean`'s module
docstring). -/
def ms5FC {World : Type*} (r : World → World → Prop) : Prop :=
  (∀ w, r w w) ∧ (∀ {w x y}, r w x → r x y → r w y) ∧ (∀ {w x}, r w x → r x w)

/-! ## Soundness -/

/-- Every `MS5ModalAxiom` instance is `MValidFC ms5FC` (birelational validity over
reflexive-transitive-symmetric frames, arbitrary `botForces`).

The 16 non-`B` cases are `ms4_axiom_sound`'s cases verbatim (`MS4.lean`), with `hsymm` threaded
through unused. The two new cases:
- `bDia` (`◇□A → A`): the diamond witness `u` for `◇□A@w'` carries `r w' u` and `□A@u`; symmetry
  gives `r u w'`, so instantiating the box at `u' := u` (`≤`-refl) and successor `w'`
  (`hsymm hru`) directly yields `A@w'` -- no relocation needed.
- `bBox` (`A → □◇A`): the nested box goal introduces `w''`/`u` with `r w'' u`; persistence carries
  `A` from `w'` (where it is forced by hypothesis) up to `w''` (`w' ≤ w''`); symmetry gives
  `r u w''`, so `w''` itself is the diamond witness for `◇A@u`. -/
theorem ms5_axiom_sound {φ : Proposition Atom} (h_ax : MS5ModalAxiom φ) :
    MValidFC.{u, v} ms5FC φ := by
  intro World _ r hfc f1 f2 val botForces v_uc bf_uc w
  obtain ⟨hrefl, htrans, hsymm⟩ := hfc
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
  | bBox φ =>
    intro w' _ hφ w'' hw'' u hru
    have hφw'' : BForces r val botForces w'' φ :=
      bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw'' hφ
    exact ⟨w'', hsymm hru, hφw''⟩
  | bDia φ =>
    intro w' _ hdia
    obtain ⟨u, hru, hboxA⟩ := hdia
    exact hboxA u (le_refl u) w' (hsymm hru)

/-- **Soundness**: if `DerivationTree MS5ModalAxiom Γ φ`, then for any birelational frame
(arbitrary `botForces`) whose relation `r` is reflexive, transitive, and symmetric, and world `w`
where all formulas in `Γ` are forced, `φ` is also forced at `w`. -/
theorem ms5_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree MS5ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (hrefl : ∀ w, r w w)
    (htrans : ∀ {w x y}, r w x → r x y → r w y)
    (hsymm : ∀ {w x}, r w x → r x w)
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
    exact ms5_axiom_sound h_ax World r ⟨hrefl, htrans, hsymm⟩ f1 f2 val botForces v_uc bf_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact ms5_soundness d₁ r hrefl htrans hsymm f1 f2 val botForces v_uc bf_uc w h_ctx w
      (le_refl w) (ms5_soundness d₂ r hrefl htrans hsymm f1 f2 val botForces v_uc bf_uc w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact ms5_soundness d' r hrefl htrans hsymm f1 f2 val botForces v_uc bf_uc u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact ms5_soundness d' r hrefl htrans hsymm f1 f2 val botForces v_uc bf_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable MS5ModalAxiom φ`, then `φ` is
`MValidFC ms5FC`. -/
theorem ms5_soundness_derivable {φ : Proposition Atom}
    (h : Derivable MS5ModalAxiom φ) : MValidFC.{u, v} ms5FC φ := by
  intro World _ r hfc f1 f2 val botForces v_uc bf_uc w
  obtain ⟨hrefl, htrans, hsymm⟩ := hfc
  obtain ⟨d⟩ := h
  exact ms5_soundness d r hrefl htrans hsymm f1 f2 val botForces v_uc bf_uc w (fun _ h => nomatch h)

/-! ## Completeness and Consistency -/

/-- **Canonical reflexivity**: identical proof to `min_canonical_reflexive_mt`/`_ms4` (`MT.lean`/
`MS4.lean`), using the `tBox`/`tDia` constructors inherited by `MS5ModalAxiom`. -/
theorem min_canonical_reflexive_ms5 :
    (∀ w, @MinExt.minCanonicalR Atom MS5ModalAxiom w w) := by
  intro w
  refine ⟨?_, ?_⟩
  · intro φ hbox
    exact min_imp_property (min_axiom_mem (MS5ModalAxiom.tBox φ)) hbox
  · intro φ hφ
    exact min_imp_property (min_axiom_mem (MS5ModalAxiom.tDia φ)) hφ

/-- **Canonical transitivity**: identical proof to `min_canonical_transitive_ms4` (`MS4.lean`),
using the `fourBox`/`fourDia` constructors inherited by `MS5ModalAxiom`. -/
theorem min_canonical_transitive_ms5 :
    (∀ {w x y : MinExt.MinCanonicalPrimeWorld MS5ModalAxiom},
      @MinExt.minCanonicalR Atom MS5ModalAxiom w x → @MinExt.minCanonicalR Atom MS5ModalAxiom x y →
      @MinExt.minCanonicalR Atom MS5ModalAxiom w y) := by
  intro w u v hwu huv
  refine ⟨?_, ?_⟩
  · intro φ hbox
    have hboxbox : (Proposition.box (Proposition.box φ)) ∈ w.val :=
      min_imp_property (min_axiom_mem (MS5ModalAxiom.fourBox φ)) hbox
    have hbox_u : (Proposition.box φ) ∈ u.val := hwu.1 (Proposition.box φ) hboxbox
    exact huv.1 φ hbox_u
  · intro φ hφ
    have hdia_u : (◇φ) ∈ u.val := huv.2 φ hφ
    have hdiadia_w : (◇◇φ) ∈ w.val := hwu.2 (◇φ) hdia_u
    exact min_imp_property (min_axiom_mem (MS5ModalAxiom.fourDia φ)) hdiadia_w

/-- **Canonical symmetry (HIGHEST-RISK closure of task 496 -- the crux)**: the canonical relation
`MinExt.minCanonicalR` (over `MS5ModalAxiom`) is symmetric. Verbatim port of
`is5_canonical_symmetric` (`Intuitionistic/IS5.lean:341`) onto the generic `MinExt` scaffold, both
clauses discharged positively via `min_axiom_mem`/`min_imp_property` (no `by_contra`, no
negation):
- box clause of `v → w` (given `minCanonicalR w v`, `□φ ∈ v.val`, show `φ ∈ w.val`): this is the
  step that routes a *box* membership back through the *diamond* clause of `w → v` (`hwv.2`,
  instantiated at `ψ := □φ`) to get `◇□φ ∈ w.val`; `min_axiom_mem (bDia φ)` places
  `(◇□φ → φ) ∈ w.val`; `min_imp_property` (MP) closes it.
- dia clause of `v → w` (given `minCanonicalR w v`, `φ ∈ w.val`, show `◇φ ∈ v.val`):
  `min_axiom_mem (bBox φ)` places `(φ → □◇φ) ∈ w.val`; MP with `φ ∈ w.val` gives
  `□◇φ ∈ w.val`; the box clause of `w → v` (`hwv.1`, instantiated at `ψ := ◇φ`) gives
  `◇φ ∈ v.val`. -/
theorem min_canonical_symmetric_ms5 :
    (∀ {w v : MinExt.MinCanonicalPrimeWorld MS5ModalAxiom},
      @MinExt.minCanonicalR Atom MS5ModalAxiom w v →
        @MinExt.minCanonicalR Atom MS5ModalAxiom v w) := by
  intro w v hwv
  refine ⟨?_, ?_⟩
  · intro φ hboxφ_v
    have hdiaboxφ_w : (◇(Proposition.box φ)) ∈ w.val := hwv.2 (Proposition.box φ) hboxφ_v
    exact min_imp_property (min_axiom_mem (MS5ModalAxiom.bDia φ)) hdiaboxφ_w
  · intro φ hφ_w
    have hboxdiaφ_w : (Proposition.box (◇φ)) ∈ w.val :=
      min_imp_property (min_axiom_mem (MS5ModalAxiom.bBox φ)) hφ_w
    exact hwv.1 (◇φ) hboxdiaφ_w

/-- **Canonical frame condition for `MS5`**: bundles `min_canonical_reflexive_ms5`,
`min_canonical_transitive_ms5`, and `min_canonical_symmetric_ms5` into
`ms5FC (@MinExt.minCanonicalR Atom MS5ModalAxiom)`. -/
theorem min_canonical_ms5FC : ms5FC (@MinExt.minCanonicalR Atom MS5ModalAxiom) :=
  ⟨min_canonical_reflexive_ms5, min_canonical_transitive_ms5, min_canonical_symmetric_ms5⟩

/-- **Completeness for `MS5`**: any formula that is `MValidFC ms5FC` (forced at every world of
every reflexive-transitive-symmetric birelational model) is derivable from `MS5ModalAxiom`.
Instantiation of the task-496 parametric `mkvalidFC_completeness` at `Axioms := MS5ModalAxiom`,
`FC := ms5FC`, `h_canonFC := min_canonical_ms5FC`. -/
theorem ms5_completeness {φ : Proposition Atom} (h_valid : MValidFC.{u, u} ms5FC φ) :
    Derivable MS5ModalAxiom φ :=
  mkvalidFC_completeness ms5FC
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .cd φ ψ) (fun φ ψ => .idb φ ψ)
    min_canonical_ms5FC
    h_valid

/-- **Consistency of `MS5`**: `⊥` is not derivable from `MS5ModalAxiom`. Corollary of soundness,
via the trivial reflexive-transitive-symmetric one-point birelational frame on `ℕ` (any world,
e.g. `0`), mirroring `ms4_consistent` (`MS4.lean`). -/
theorem ms5_consistent : ¬ Derivable MS5ModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  have hforces : BForces (fun _ _ : ℕ => True) (fun (_ : ℕ) (_ : Atom) => False)
      (fun _ : ℕ => False) 0 (Proposition.bot : Proposition Atom) :=
    ms5_soundness_derivable h ℕ (fun _ _ => True)
      ⟨fun _ => trivial, fun _ _ => trivial, fun _ => trivial⟩
      (fun {_ _ u} _ _ => ⟨u, trivial, le_refl u⟩)
      (fun {w0 _ _} _ _ => ⟨w0, le_refl w0, trivial⟩)
      (fun _ _ => False) (fun _ : ℕ => False) (fun _ _ h => h) (fun _ h => h.elim) 0
  exact hforces

/-- **Soundness-completeness biconditional for `MS5`**: `φ` is `MValidFC ms5FC` iff `φ` is
derivable from `MS5ModalAxiom`. -/
theorem ms5_soundness_completeness {φ : Proposition Atom} :
    MValidFC.{u, u} ms5FC φ ↔ Derivable MS5ModalAxiom φ :=
  ⟨ms5_completeness, ms5_soundness_derivable⟩

end Cslib.Logic.Modal
