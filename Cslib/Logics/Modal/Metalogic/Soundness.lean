/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Logics.Modal.Metalogic.FrameCorrespondence -- shake: keep

/-! # Soundness Theorem for Normal Modal Logics

This module proves soundness parameterized over an axiom predicate
`Axioms : Proposition Atom -> Prop` with a generic axiom soundness callback.
The parameterized infrastructure supports all normal modal logics; an
S5-specific wrapper instantiates at `S5Axiom`.

## Main Results

- `s5_axiom_sound`: Each of the 8 S5 axiom schemata is valid over S5 frames.
- `soundness`: Parameterized soundness -- if `Gamma |- phi` (via `DerivationTree Axioms`),
  then `phi` is satisfied at every world where all of `Gamma` is satisfied, given a
  soundness callback for `Axioms`.
- `s5_soundness`: S5-specific wrapper combining `s5_axiom_sound` with `soundness`.

## Design

The parameterized `soundness` theorem takes a callback `h_ax_sound` that proves
each axiom of `Axioms` is valid in the given model. The S5-specific `s5_axiom_sound`
theorem handles the concrete `S5Axiom` cases.

## References

* Cslib/Logics/Modal/Basic.lean -- semantic definitions and axiom validity proofs
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Shared Propositional and Modal K Axiom Soundness Lemmas -/

/-- Propositional axiom K (weakening) is valid on all frames. -/
lemma Satisfies.implyK_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp φ (Proposition.imp ψ φ)) := by
  intro hφ _; exact hφ

/-- Propositional axiom S (distribution) is valid on all frames. -/
lemma Satisfies.implyS_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ χ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
      (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ))) := by
  intro h₁ h₂ h₃; exact h₁ h₃ (h₂ h₃)

/-- Ex falso quodlibet is valid on all frames. -/
lemma Satisfies.efq_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp Proposition.bot φ) := by
  intro h; exact absurd h id

/-- Peirce's law / double negation elimination is valid on all frames. -/
lemma Satisfies.peirce_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ) := by
  intro h; by_contra h_not; exact h_not (h (fun hφ => absurd hφ h_not))

/-- Modal axiom K (distribution) is valid on all frames. -/
lemma Satisfies.modalK_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
      (Proposition.imp (Proposition.box φ) (Proposition.box ψ))) := by
  intro h_box_imp h_box_phi w' hr; exact h_box_imp w' hr (h_box_phi w' hr)

/-! ## Shared And/Or/Diamond-Duality Characterization Axiom Soundness Lemmas

Semantic soundness for the 8 characterization schemata for the native `and`/`or`/`diamond`
constructors. Factored out here so every `Systems/*/Soundness.lean` file can reuse a single
proof per schema rather than re-deriving it per system. -/

/-- Conjunction introduction (`Axioms.AndI`) is valid on all frames. -/
lemma Satisfies.andI_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp φ (Proposition.imp ψ (Proposition.and φ ψ))) := by
  intro hφ hψ; exact ⟨hφ, hψ⟩

/-- Left conjunction elimination (`Axioms.AndE1`) is valid on all frames. -/
lemma Satisfies.andE1_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.and φ ψ) φ) := by
  intro ⟨h1, _⟩; exact h1

/-- Right conjunction elimination (`Axioms.AndE2`) is valid on all frames. -/
lemma Satisfies.andE2_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.and φ ψ) ψ) := by
  intro ⟨_, h2⟩; exact h2

/-- Left disjunction introduction (`Axioms.OrI1`) is valid on all frames. -/
lemma Satisfies.orI1_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp φ (Proposition.or φ ψ)) := by
  intro h; exact Or.inl h

/-- Right disjunction introduction (`Axioms.OrI2`) is valid on all frames. -/
lemma Satisfies.orI2_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp ψ (Proposition.or φ ψ)) := by
  intro h; exact Or.inr h

/-- Disjunction elimination (`Axioms.OrE`) is valid on all frames. -/
lemma Satisfies.orE_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ ψ χ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.imp φ χ)
      (Proposition.imp (Proposition.imp ψ χ) (Proposition.imp (Proposition.or φ ψ) χ))) := by
  intro h1 h2 h3
  cases h3 with
  | inl h => exact h1 h
  | inr h => exact h2 h

/-- Diamond duality, forward direction (`Axioms.AxiomDiamondDualityFwd`): `◇φ → ¬□¬φ`, valid on all
frames. -/
lemma Satisfies.diamondDualityFwd_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.diamond φ)
      (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot)) := by
  intro ⟨w', hr, hs⟩ hbox
  exact hbox w' hr hs

/-- Diamond duality, backward direction (`Axioms.AxiomDiamondDualityBack`): `¬□¬φ → ◇φ`, valid on
all frames (uses excluded middle, as diamond is classically the dual of box). -/
lemma Satisfies.diamondDualityBack_axiom {World : Type*} (m : Model World Atom) (w : World)
    (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp
      (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot)
      (Proposition.diamond φ)) := by
  intro h
  by_contra hc
  simp only [Satisfies] at hc
  push Not at hc
  exact h fun w' hr hs => hc w' hr hs

/-! ## Parameterized Soundness Theorem -/

/-- **Parameterized Soundness**: If `Gamma |- phi` (via `DerivationTree Axioms`), then
for any model `m` and any world `w` where all formulas in `Gamma` are satisfied,
`phi` is also satisfied at `w`, given that all axioms in `Axioms` are valid. -/
theorem soundness {Axioms : Proposition Atom → Prop} {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ)
    (m : Model World Atom)
    (h_ax_sound : ∀ (ψ : Proposition Atom), Axioms ψ → ∀ (w : World),
      Satisfies m w ψ)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact h_ax_sound ψ h_ax w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact soundness d₁ m h_ax_sound w h_ctx
      (soundness d₂ m h_ax_sound w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hr
    exact soundness d' m h_ax_sound w' (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact soundness d' m h_ax_sound w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Parameterized Soundness for derivable formulas**: If `phi` is derivable from
the empty context, then `phi` is satisfied at every world. -/
theorem soundness_derivable {Axioms : Proposition Atom → Prop} {World : Type*}
    {φ : Proposition Atom} (h : Derivable Axioms φ)
    (m : Model World Atom)
    (h_ax_sound : ∀ (ψ : Proposition Atom), Axioms ψ → ∀ (w : World),
      Satisfies m w ψ)
    (w : World) : Satisfies m w φ := by
  obtain ⟨d⟩ := h
  exact soundness d m h_ax_sound w (fun _ h => nomatch h)

end Cslib.Logic.Modal
