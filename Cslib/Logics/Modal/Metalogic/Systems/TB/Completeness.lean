/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic TB

This module proves completeness for TB modal logic (= KTB) via the canonical Kripke
model construction: if a formula is valid on all reflexive, symmetric frames, then
it is TB-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.28, clause 1** (reflexivity is canonical): Uses axiom T (`□φ → φ`)
  via `canonical_refl` and `mcs_box_closure`.

- **Theorem 4.28, clause 2** (symmetry is canonical): Uses axiom B (`φ → □◇φ`)
  via `canonical_symm`.

## Main Results

- `tb_canonical_refl`: The canonical frame for TB is reflexive (BRV Thm 4.28 cl.1).
- `tb_canonical_symm`: The canonical frame for TB is symmetric (BRV Thm 4.28 cl.2).
- `tb_truth_lemma`: TB-specific Truth Lemma (reuses existing `truth_lemma`).

The weak completeness theorem `tb_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.TB.StrongCompleteness`, where it is derived as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- parameterized canonical model
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## TB Canonical Frame Properties (BRV Theorem 4.28) -/

/-- **TB Canonical Frame Reflexivity** (BRV Theorem 4.28, clause 1):
The canonical frame for TB is reflexive. -/
theorem tb_canonical_refl
    (S : CanonicalWorld (@TBAxiom Atom)) :
    (CanonicalModel (@TBAxiom Atom)).r S S :=
  canonical_refl
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .modalT φ)
    S

/-- **TB Canonical Frame Symmetry** (BRV Theorem 4.28, clause 2):
The canonical frame for TB is symmetric. -/
theorem tb_canonical_symm
    (S T : CanonicalWorld (@TBAxiom Atom)) :
    (CanonicalModel (@TBAxiom Atom)).r S T →
    (CanonicalModel (@TBAxiom Atom)).r T S :=
  canonical_symm
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalB φ)
    S T

/-! ## TB Truth Lemma (BRV Lemma 4.21 for TB) -/

/-- **TB Truth Lemma** (BRV Lemma 4.21 for TB):
Reuses the existing parameterized `truth_lemma` instantiated at `TBAxiom`. -/
theorem tb_truth_lemma
    (S : CanonicalWorld (@TBAxiom Atom))
    (φ : Proposition Atom) :
    (Satisfies (CanonicalModel (@TBAxiom Atom)) S φ ↔ φ ∈ S.val) :=
  truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalT φ)
    S φ

end Cslib.Logic.Modal
