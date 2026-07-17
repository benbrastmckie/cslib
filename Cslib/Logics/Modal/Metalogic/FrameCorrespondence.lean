/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Axioms
public import Cslib.Logics.Modal.Basic

/-! # Frame-Condition-to-Axiom Correspondence Lemmas

This module collects the modal-axiom correspondence lemmas that pair a frame condition
(reflexivity, transitivity, symmetry, seriality, right-Euclideanness) with the semantic
validity of the corresponding modal axiom schema (T, 4, B, D, 5). Each lemma is an
explicit-hypothesis primary form -- it takes the raw frame-condition hypothesis (`h_refl`,
`h_trans`, `h_symm`, `h_serial`, `h_eucl`) that the per-system `Systems/*/Soundness.lean`
files already thread through their public `<sys>_axiom_sound` / `<sys>_soundness` signatures,
so consumer signatures stay byte-stable when they are rewired to delegate to these lemmas.

## Main Results

- `Satisfies.modalT_axiom`: T / reflexivity correspondence.
- `Satisfies.modalFour_axiom`: 4 / transitivity correspondence.
- `Satisfies.modalB_axiom`: B / symmetry correspondence.
- `Satisfies.modalD_axiom`: D / seriality correspondence.
- `Satisfies.modalFive_axiom`: 5 / Euclideanness correspondence.

## Design

Each lemma body is copied verbatim from the corresponding verified inline case in a
`Systems/*/Soundness.lean` file (see individual docstrings for provenance). This module is
purely additive: it introduces no new frame-property predicates (reusing the raw
`∀`-quantified hypotheses and `Relation.Serial` already in use) and changes no existing proof.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- shared propositional/K/and-or/dia-duality
  correspondence lemmas
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Modal Frame-Condition Correspondence Lemmas -/

/-- T / reflexivity axiom (`□φ → φ`) is valid on reflexive frames. Copies the `modalT` case
from `Systems/T/Soundness.lean`. -/
lemma Satisfies.modalT_axiom {World : Type*} (m : Model World Atom)
    (h_refl : ∀ w, m.r w w) (w : World) (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box φ) φ) := by
  intro h_box
  exact h_box w (h_refl w)

/-- 4 / transitivity axiom (`□φ → □□φ`) is valid on transitive frames. Copies the `modalFour`
case from `Systems/K4/Soundness.lean`. -/
lemma Satisfies.modalFour_axiom {World : Type*} (m : Model World Atom)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) (w : World)
    (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ))) := by
  intro h_box w₁ hr₁ w₂ hr₂
  exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)

/-- B / symmetry axiom (`φ → □◇φ`, raw-encoded as `Axioms.AxiomB`) is valid on symmetric
frames. Copies the `modalB` case from `Systems/B/Soundness.lean`. -/
lemma Satisfies.modalB_axiom {World : Type*} (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) (w : World) (φ : Proposition Atom) :
    Satisfies m w (Axioms.AxiomB φ) := by
  intro hφ w' hr h_box_neg
  exact h_box_neg w (h_symm w w' hr) hφ

/-- D / seriality axiom (`□φ → ◇φ`) is valid on serial frames. Copies the `modalD` case from
`Systems/D/Soundness.lean`. -/
lemma Satisfies.modalD_axiom {World : Type*} (m : Model World Atom)
    (h_serial : Relation.Serial m.r) (w : World) (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box φ)
      (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot)) := by
  intro h_box h_box_neg
  obtain ⟨w', hr⟩ := h_serial.serial w
  exact h_box_neg w' hr (h_box w' hr)

/-- 5 / Euclideanness axiom (`◇φ → □◇φ`) is valid on right-Euclidean frames. Copies the
`modalFive` case from `Systems/K5/Soundness.lean`. -/
lemma Satisfies.modalFive_axiom {World : Type*} (m : Model World Atom)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) (w : World)
    (φ : Proposition Atom) :
    Satisfies m w (((Proposition.box (φ.imp .bot)).imp .bot).imp
      (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot))) := by
  intro h_diam w' hr h_box_neg_w'
  exact h_diam (fun w'' hr' h_phi => h_box_neg_w' w'' (h_eucl w w' w'' hr hr') h_phi)

end Cslib.Logic.Modal
