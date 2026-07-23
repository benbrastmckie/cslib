/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.DB.Soundness

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
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- `d_canonical_serial` (relocated, task 539)
  and the generic `truth_lemma` / `canonicalTruthLemmaOfKCore` wrapper
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## DB Frame Condition and Canonical Witness -/

/-- The DB frame condition: every model whose accessibility relation is serial and
symmetric. -/
def dbFC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => Relation.Serial m.r ∧ (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)

/-- The canonical DB model satisfies `dbFC`: its accessibility relation is serial
and symmetric. -/
private theorem db_canonical_FC : dbFC (CanonicalModel (@DBAxiom Atom)) := by
  constructor
  · constructor
    intro S
    exact d_canonical_serial
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
      (fun φ => ⟨.modalD, by decide, φ, rfl⟩) S
  · exact canonical_symm
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
      (fun φ => ⟨.modalB, by decide, φ, rfl⟩)

/-- Pre-applied DB truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem db_truth_lemma_applied (S : CanonicalWorld (@DBAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@DBAxiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- DB soundness adapter matching the `strong_soundness` callback shape. -/
private theorem db_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : dbFC m)
    (d : DerivationTree (@DBAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  db_soundness d m hFC.1 hFC.2 w h_ctx

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
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @DBAxiom Atom) (FC := dbFC)
    db_sound_cb h World m w ⟨h_serial, h_symm⟩ h_sat

/-! ## DB Strong Completeness -/

/-- **Strong Completeness for DB**: If `phi` is a semantic consequence of `Gamma`
over all serial, symmetric frames, then `phi` is set-derivable from `Gamma`
using `DBAxiom`.

Delegates to the parametric `strong_completeness` with `db_truth_lemma_applied`
and `db_canonical_FC`. -/
theorem db_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@DBAxiom Atom) Gamma phi :=
  strong_completeness (Axioms := @DBAxiom Atom) (FC := dbFC)
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
    db_truth_lemma_applied
    db_canonical_FC
    (fun World m w ⟨hSer, hSymm⟩ h_sat => h World m w hSer hSymm h_sat)

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
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @DBAxiom Atom) (FC := dbFC)
      db_sound_cb
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
      db_truth_lemma_applied
      db_canonical_FC
      (fun World m w ⟨hSer, hSymm⟩ h_sat => h World m w hSer hSymm h_sat)
  exact ⟨L, hL_sub, fun World m w h_serial h_symm h_sat =>
    hL_sem World m w ⟨h_serial, h_symm⟩ h_sat⟩

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
