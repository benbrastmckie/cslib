/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module


public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.DB.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Completeness

/-! # Strong Completeness for Modal Logic DB

This module proves strong soundness and strong completeness for modal logic DB:
semantic entailment from a set of premises `Gamma` (over all serial, symmetric frames)
is equivalent to set-derivability using `DBAxiom`.

## Main Results

- `db_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all serial, symmetric frames.
- `db_strong_completeness`: Semantic entailment over serial, symmetric frames implies
  set-derivability from `Gamma`.
- `db_strong_completeness_iff`: Biconditional combining the above.
- `db_completeness`: Weak completeness (corollary of strong completeness).
- `db_compactness`: If `phi` is a DB-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a DB-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
* Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean -- D completeness
  (canonical serial, d_truth_lemma)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## DB Strong Soundness -/

/-- **Strong Soundness for DB**: If `phi` is set-derivable from `Gamma` using `DBAxiom`,
then `phi` is a semantic consequence of `Gamma` over all serial, symmetric frames.

For any serial, symmetric model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem db_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@DBAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact db_soundness d m h_serial h_symm w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## DB Strong Completeness -/

/-- **Strong Completeness for DB**: If `phi` is a semantic consequence of `Gamma`
over all serial, symmetric frames, then `phi` is set-derivable from `Gamma`
using `DBAxiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `d_truth_lemma` in the canonical serial, symmetric
frame, derive contradiction. -/
theorem db_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@DBAxiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@DBAxiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_serial : Relation.Serial (CanonicalModel (@DBAxiom Atom)).r := by
    constructor
    intro S
    exact d_canonical_serial
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      S
  have h_symm : ∀ (S T : CanonicalWorld (@DBAxiom Atom)),
      (CanonicalModel (@DBAxiom Atom)).r S T →
      (CanonicalModel (@DBAxiom Atom)).r T S :=
    canonical_symm
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalB φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@DBAxiom Atom)) w γ :=
    fun γ hγ => (d_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@DBAxiom Atom)) (CanonicalModel (@DBAxiom Atom))
    w h_serial (fun S T hST => h_symm S T hST) h_gamma_sat
  have h_phi_M := (d_truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalD φ)
    w phi).mp h_phi_sat
  exact mcs_bot_not_mem hM_mcs
    (modal_implication_property
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      hM_mcs h_neg_phi h_phi_M)

/-! ## DB Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for DB**:
`phi` is a semantic consequence of `Gamma` over all serial, symmetric frames iff `phi` is
set-derivable from `Gamma` using `DBAxiom`. -/
theorem db_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@DBAxiom Atom) Gamma phi :=
  ⟨db_strong_completeness, fun h World m w h_serial h_symm h_sat =>
    db_strong_soundness h World m w h_serial h_symm h_sat⟩

/-! ## DB Compactness -/

/-- **Compactness for DB Semantics**: If `phi` is a semantic consequence of `Gamma`
over all serial, symmetric frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all serial, symmetric frames. -/
theorem db_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := db_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_serial h_symm h_sat =>
    db_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_serial h_symm h_sat⟩

/-! ## DB Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic DB** (corollary of strong completeness):

If `phi` is valid over all serial, symmetric frames, then `phi` is DB-derivable
from the empty context.

This is a corollary of `db_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem db_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      ∀ w, Satisfies m w φ) :
    Derivable (@DBAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (db_strong_completeness (fun W m w hSer hSymm _ => h_valid W m hSer hSymm w))

end Cslib.Logic.Modal
