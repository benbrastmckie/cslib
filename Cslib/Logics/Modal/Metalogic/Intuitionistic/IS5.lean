/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Intuitionistic.Extension

/-! # IS5: Intuitionistic Modal Logic S5 (Soundness + Completeness)

This module instantiates the frame-condition-parametrized scaffold (`Extension.lean`) at
Simpson's `IS5` ([Simpson1994] Ch. 3), the intuitionistic analogue of classical `S5`: `IS5` = `IS4`
(`IS4.lean`) + the `B` axiom schemata. As with `T`/`4`, `B` needs **both** a box-form and a
diamond-form schema, `bBox : A → □◇A` and `bDia : ◇□A → A`, since `◇` is primitive and not
`□`-definable intuitionistically (Wijesekera 1990), mirroring the two-clause shape of `canonicalR`
(`CanonicalModel.lean:117`) and `IT`/`IS4`'s own box/diamond splits.

**Adversarial finding (research report, Deliverable 6): `IS5` is axiomatized here via `B`
(symmetry), NOT via the classical euclidean/`5` axiom `◇A → □◇A`.** The classical canonical
euclideanness proofs (`Metalogic/Completeness.lean`'s `canonical_eucl`/`canonical_eucl_from_5`)
are `by_contra` + `mcs_neg_of_not_mem` + double-negation arguments that depend on
negation-completeness of maximal-consistent sets. Canonical *prime* theories (this framework's
worlds, `CanonicalModel.lean:76-80`) are deliberately **not** negation-complete, so that route has
no intuitionistic analogue. Symmetry closure from `B`, by contrast, is fully positive/constructive
(MP-closure only, `canonical_imp_property`) and transfers cleanly. Reflexivity (`T`) + transitivity
(`4`) + symmetry (`B`) together give an **equivalence relation**, exactly Simpson's `IS5` frame
class.

The frame condition corresponding to `{tBox, tDia, fourBox, fourDia, bBox, bDia}` is reflexivity,
transitivity, **and** symmetry of the modal accessibility relation `r`, expressed here via a local
predicate `is5FC` on the raw relation (matching the shape `IValidFC`/`ivalidFC_completeness`
require). `is5FC` mirrors `IS4`'s `is4FC` (`IS4.lean:136`) and the classical file's `s5FC`
(`Systems/S5/Completeness.lean`, stated over a bundled `Model`); it is **not** Mathlib's
`Reflexive`/`Transitive`/`Symmetric` (deprecated in the pinned Mathlib -- see `IT.lean`'s module
docstring) -- same semantic content, different (undeprecated, local) name.

All `Extension.lean`/`IT.lean`/`IS4.lean` assets (`canonicalR`, `canonical_f1`/`canonical_f2`,
`canonical_imp_property`, `axiom_mem`, `IValidFC`, `ivalidFC_completeness`) are reused unchanged;
the only new work is the two `bBox`/`bDia` soundness cases and the canonical-symmetry closure
proof (`is5_canonical_symmetric`), both fully positive (no `by_contra`, no negation).

## Main Definitions

- `IS5ModalAxiom`: `IS4ModalAxiom`'s 18 constructors plus `bBox`/`bDia`.
- `is5FC`: the reflexivity-transitivity-symmetry frame condition on a raw relation `r`.
- `is5_axiom_sound`/`is5_soundness`/`is5_soundness_derivable`: birelational soundness for `IS5`
  over reflexive-transitive-symmetric frames (`IValidFC is5FC`).
- `is5_canonical_reflexive`/`is5_canonical_transitive`/`is5_canonical_symmetric`: the canonical
  relation `canonicalR` (over `IS5ModalAxiom`) is reflexive, transitive, and symmetric -- all
  proved positively via `axiom_mem`/`canonical_imp_property`, no negation.
- `is5_completeness`/`is5_consistent`/`is5_soundness_completeness`: instantiations of
  `Extension.lean`'s parametric `ivalidFC_completeness` at `Axioms := IS5ModalAxiom`, `FC := is5FC`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational frame classes for `S5`, `IValid`).
* D. Wijesekera, *Constructive Modal Logics I*, Annals of Pure and Applied Logic, 1990 --
  primitive-`◇` canonical accessibility (both box/diamond `B`-forms are required).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `IS5` Axiom Schemata -/

/-- Axiom schemata for intuitionistic modal logic `IS5` ([Simpson1994], Ch. 3): the 18
`IS4ModalAxiom` constructors verbatim, plus the two `B` schemata `bBox`/`bDia`. Both box and
diamond forms are required since `◇` is primitive (not `□`-definable) in this framework's
`Modal.Proposition` datatype (Wijesekera 1990; `canonicalR`'s two-clause shape). Deliberately
**not** the classical euclidean/`5` axiom `◇A → □◇A` (see module docstring: its canonical proof is
non-transferable to prime theories). -/
inductive IS5ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      IS5ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      IS5ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      IS5ModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      IS5ModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      IS5ModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      IS5ModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      IS5ModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      IS5ModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      IS5ModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- `k1` / Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      IS5ModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- `k2` / Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      IS5ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `k3` / Cd (Fischer-Servi): `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`. -/
  | cd (φ ψ : Proposition Atom) :
      IS5ModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- `k4` / Idb (Fischer-Servi): `(◇φ → □ψ) → □(φ → ψ)`. -/
  | idb (φ ψ : Proposition Atom) :
      IS5ModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
  /-- `k5` / Nd: `◇⊥ → ⊥`. -/
  | dbot :
      IS5ModalAxiom ((◇Proposition.bot).imp Proposition.bot)
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      IS5ModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      IS5ModalAxiom (φ.imp (◇φ))
  /-- `4` box form: `□A → □□A`. -/
  | fourBox (φ : Proposition Atom) :
      IS5ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- `4` diamond form: `◇◇A → ◇A`. -/
  | fourDia (φ : Proposition Atom) :
      IS5ModalAxiom ((◇◇φ).imp (◇φ))
  /-- `B` box form: `A → □◇A`. -/
  | bBox (φ : Proposition Atom) :
      IS5ModalAxiom (φ.imp (Proposition.box (◇φ)))
  /-- `B` diamond form: `◇□A → A`. -/
  | bDia (φ : Proposition Atom) :
      IS5ModalAxiom ((◇(Proposition.box φ)).imp φ)

/-! ## `IS5` Frame Condition -/

/-- The `IS5` frame condition: reflexivity, transitivity, **and** symmetry of the modal
accessibility relation `r` (an equivalence relation). Mirrors `IS4`'s `is4FC` (`IS4.lean:136`) and
the classical `s5FC` (`Systems/S5/Completeness.lean`), adapted from a bundled `Model` argument to
the raw relation `IValidFC`/`canonicalR` operate on. Defined locally rather than reusing Mathlib's
`Reflexive`/`Transitive`/`Symmetric` (deprecated in the pinned Mathlib -- see `IT.lean`'s module
docstring). -/
def is5FC {World : Type*} (r : World → World → Prop) : Prop :=
  (∀ w, r w w) ∧ (∀ {w x y}, r w x → r x y → r w y) ∧ (∀ {w x}, r w x → r x w)

/-! ## Soundness -/

/-- Every `IS5ModalAxiom` instance is `IValidFC is5FC` (birelational validity over
reflexive-transitive-symmetric frames, intuitionistic falsum semantics `botForces := fun _ =>
False`).

The 18 non-`B` cases are `is4_axiom_sound`'s cases verbatim (`IS4.lean:159-223`), with `hsymm`
threaded through unused. The two new cases:
- `bDia` (`◇□A → A`): the diamond witness `u` for `◇□A@w'` carries `r w' u` and `□A@u`; symmetry
  gives `r u w'`, so instantiating the box at `u' := u` (`≤`-refl) and successor `w'`
  (`hsymm hru`) directly yields `A@w'` -- no relocation needed.
- `bBox` (`A → □◇A`): the nested box goal introduces `w''`/`u` with `r w'' u`; persistence carries
  `A` from `w'` (where it is forced by hypothesis) up to `w''` (`w' ≤ w''`); symmetry gives
  `r u w''`, so `w''` itself is the diamond witness for `◇A@u`. -/
theorem is5_axiom_sound {φ : Proposition Atom} (h_ax : IS5ModalAxiom φ) :
    IValidFC.{u, v} is5FC φ := by
  intro World _ r hfc f1 f2 val v_uc w
  obtain ⟨hrefl, htrans, hsymm⟩ := hfc
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
    intro w' _ hbox w'' hw'' u hru w''' hw''' v hrv
    obtain ⟨w2, hw''w2, hrw2w'''⟩ := f2 hru hw'''
    exact hbox w2 (le_trans hw'' hw''w2) v (htrans hrw2w''' hrv)
  | fourDia φ =>
    intro w' _ hdia
    obtain ⟨u, hru, t, hut, hφt⟩ := hdia
    exact ⟨t, htrans hru hut, hφt⟩
  | bBox φ =>
    -- Goal: ∀ w' ≥ w, φ@w' → □◇φ@w'; i.e. ∀ w'' ≥ w', ∀ u, r w'' u → ◇φ@u.
    intro w' _ hφ w'' hw'' u hru
    have hφw'' : BForces r val (fun _ => False) w'' φ :=
      bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw'' hφ
    exact ⟨w'', hsymm hru, hφw''⟩
  | bDia φ =>
    -- Goal: ∀ w' ≥ w, ◇□φ@w' → φ@w'.
    intro w' _ hdia
    obtain ⟨u, hru, hboxA⟩ := hdia
    exact hboxA u (le_refl u) w' (hsymm hru)

/-- **Soundness**: if `DerivationTree IS5ModalAxiom Γ φ`, then for any birelational frame (with
`botForces := fun _ => False`) whose relation `r` is reflexive, transitive, and symmetric, and
world `w` where all formulas in `Γ` are forced, `φ` is also forced at `w`. Structural analogue of
`is4_soundness` (`IS4.lean:230-257`), threading `hrefl`/`htrans`/`hsymm` through unused except at
the `.ax` case. -/
theorem is5_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree IS5ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (hrefl : ∀ w, r w w)
    (htrans : ∀ {w x y}, r w x → r x y → r w y)
    (hsymm : ∀ {w x}, r w x → r x w)
    (f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BForces r val (fun _ => False) w ψ) :
    BForces r val (fun _ => False) w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact is5_axiom_sound h_ax World r ⟨hrefl, htrans, hsymm⟩ f1 f2 val v_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact is5_soundness d₁ r hrefl htrans hsymm f1 f2 val v_uc w h_ctx w (le_refl w)
      (is5_soundness d₂ r hrefl htrans hsymm f1 f2 val v_uc w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact is5_soundness d' r hrefl htrans hsymm f1 f2 val v_uc u (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact is5_soundness d' r hrefl htrans hsymm f1 f2 val v_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable IS5ModalAxiom φ`, then `φ` is
`IValidFC is5FC`. -/
theorem is5_soundness_derivable {φ : Proposition Atom}
    (h : Derivable IS5ModalAxiom φ) : IValidFC.{u, v} is5FC φ := by
  intro World _ r hfc f1 f2 val v_uc w
  obtain ⟨hrefl, htrans, hsymm⟩ := hfc
  obtain ⟨d⟩ := h
  exact is5_soundness d r hrefl htrans hsymm f1 f2 val v_uc w (fun _ h => nomatch h)

/-! ## Completeness and Consistency -/

/-- **Canonical reflexivity**: the canonical relation `canonicalR` (over `IS5ModalAxiom`) is
reflexive. Identical proof to `is4_canonical_reflexive` (`IS4.lean:274-280`), using the `tBox`/
`tDia` constructors inherited by `IS5ModalAxiom`. Both clauses are discharged positively via
`axiom_mem`/`canonical_imp_property` (no `by_contra`, no negation). -/
theorem is5_canonical_reflexive : (∀ w, @canonicalR Atom IS5ModalAxiom w w) := by
  intro w
  refine ⟨?_, ?_⟩
  · intro φ hbox
    exact canonical_imp_property (axiom_mem (IS5ModalAxiom.tBox φ)) hbox
  · intro φ hφ
    exact canonical_imp_property (axiom_mem (IS5ModalAxiom.tDia φ)) hφ

/-- **Canonical transitivity**: the canonical relation `canonicalR` (over `IS5ModalAxiom`) is
transitive. Identical proof to `is4_canonical_transitive` (`IS4.lean:291-305`), using the
`fourBox`/`fourDia` constructors inherited by `IS5ModalAxiom`. Both clauses are discharged
positively via `axiom_mem`/`canonical_imp_property` (no `by_contra`, no negation). -/
theorem is5_canonical_transitive :
    (∀ {w x y : CanonicalPrimeWorld IS5ModalAxiom},
      @canonicalR Atom IS5ModalAxiom w x → @canonicalR Atom IS5ModalAxiom x y →
      @canonicalR Atom IS5ModalAxiom w y) := by
  intro w u v hwu huv
  refine ⟨?_, ?_⟩
  · intro φ hbox
    have hboxbox : (Proposition.box (Proposition.box φ)) ∈ w.val :=
      canonical_imp_property (axiom_mem (IS5ModalAxiom.fourBox φ)) hbox
    have hbox_u : (Proposition.box φ) ∈ u.val := hwu.1 (Proposition.box φ) hboxbox
    exact huv.1 φ hbox_u
  · intro φ hφ
    have hdia_u : (◇φ) ∈ u.val := huv.2 φ hφ
    have hdiadia_w : (◇◇φ) ∈ w.val := hwu.2 (◇φ) hdia_u
    exact canonical_imp_property (axiom_mem (IS5ModalAxiom.fourDia φ)) hdiadia_w

/-- **Canonical symmetry**: the canonical relation `canonicalR`
(over `IS5ModalAxiom`) is symmetric. Both clauses are discharged positively via
`axiom_mem`/`canonical_imp_property` (no `by_contra`, no negation):
- box clause of `v → w` (given `canonicalR w v`, `□φ ∈ v.val`, show `φ ∈ w.val`): this is the
  step that routes a *box* membership back through the *diamond* clause of `w → v`
  (`hwv.2`, instantiated at `ψ := □φ`) to get `◇□φ ∈ w.val`; `axiom_mem (bDia φ)` places
  `(◇□φ → φ) ∈ w.val`; `canonical_imp_property` (MP) closes it.
- dia clause of `v → w` (given `canonicalR w v`, `φ ∈ w.val`, show `◇φ ∈ v.val`): `axiom_mem
  (bBox φ)` places `(φ → □◇φ) ∈ w.val`; MP with `φ ∈ w.val` gives `□◇φ ∈ w.val`; the box clause
  of `w → v` (`hwv.1`, instantiated at `ψ := ◇φ`) gives `◇φ ∈ v.val`. -/
theorem is5_canonical_symmetric :
    (∀ {w v : CanonicalPrimeWorld IS5ModalAxiom},
      @canonicalR Atom IS5ModalAxiom w v → @canonicalR Atom IS5ModalAxiom v w) := by
  intro w v hwv
  refine ⟨?_, ?_⟩
  · intro φ hboxφ_v
    have hdiaboxφ_w : (◇(Proposition.box φ)) ∈ w.val := hwv.2 (Proposition.box φ) hboxφ_v
    exact canonical_imp_property (axiom_mem (IS5ModalAxiom.bDia φ)) hdiaboxφ_w
  · intro φ hφ_w
    have hboxdiaφ_w : (Proposition.box (◇φ)) ∈ w.val :=
      canonical_imp_property (axiom_mem (IS5ModalAxiom.bBox φ)) hφ_w
    exact hwv.1 (◇φ) hboxdiaφ_w

/-- **Canonical frame condition for `IS5`**: bundles `is5_canonical_reflexive`,
`is5_canonical_transitive`, and `is5_canonical_symmetric` into
`is5FC (@canonicalR Atom IS5ModalAxiom)`. -/
theorem is5_canonical_fc : is5FC (@canonicalR Atom IS5ModalAxiom) :=
  ⟨is5_canonical_reflexive, is5_canonical_transitive, is5_canonical_symmetric⟩

/-- **Completeness for `IS5`**: any formula that is `IValidFC is5FC` (forced at every world of
every reflexive-transitive-symmetric birelational model) is derivable from `IS5ModalAxiom`.
Instantiation of `Extension.lean`'s parametric `ivalidFC_completeness` at
`Axioms := IS5ModalAxiom`, `FC := is5FC`, `h_canonFC := is5_canonical_fc`. -/
theorem is5_completeness {φ : Proposition Atom} (h_valid : IValidFC.{u, u} is5FC φ) :
    Derivable IS5ModalAxiom φ :=
  ivalidFC_completeness is5FC
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) (fun φ => .efq φ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .idb φ ψ)
    (fun φ ψ => .cd φ ψ) .dbot
    is5_canonical_fc
    h_valid

/-- **Consistency of `IS5`**: `⊥` is not derivable from `IS5ModalAxiom`. Corollary of soundness,
via the trivial reflexive-transitive-symmetric one-point birelational frame on `ℕ` (any world,
e.g. `0`), mirroring `is4_consistent` (`IS4.lean:330-338`). -/
theorem is5_consistent : ¬ Derivable IS5ModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  have hforces : BForces (fun _ _ : ℕ => True) (fun (_ : ℕ) (_ : Atom) => False)
      (fun _ : ℕ => False) 0 (Proposition.bot : Proposition Atom) :=
    is5_soundness_derivable h ℕ (fun _ _ => True)
      ⟨fun _ => trivial, fun _ _ => trivial, fun _ => trivial⟩
      (fun {_ _ u} _ _ => ⟨u, trivial, le_refl u⟩)
      (fun {w0 _ _} _ _ => ⟨w0, le_refl w0, trivial⟩)
      (fun _ _ => False) (fun _ _ h => h) 0
  exact hforces

/-- **Soundness-completeness biconditional for `IS5`**: `φ` is `IValidFC is5FC` iff `φ` is
derivable from `IS5ModalAxiom`. -/
theorem is5_soundness_completeness {φ : Proposition Atom} :
    IValidFC.{u, u} is5FC φ ↔ Derivable IS5ModalAxiom φ :=
  ⟨is5_completeness, is5_soundness_derivable⟩

end Cslib.Logic.Modal
