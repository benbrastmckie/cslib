/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic T

This module proves completeness for modal logic T via the canonical Kripke model
construction, following Blackburn, de Rijke, Venema "Modal Logic" (2002),
Theorem 4.28, clause 1.

The key insight is that the canonical frame for T is reflexive (Thm 4.28 cl.1),
and the existing parameterized `truth_lemma` and `mcs_box_witness` work directly
for T since `TAxiom` includes axiom T.

## Main Results

- `t_canonical_refl`: The canonical frame for T is reflexive (BRV Thm 4.28 cl.1).
- `t_truth_lemma`: T-specific Truth Lemma (reuses existing `truth_lemma`).

The weak completeness theorem `t_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.T.StrongCompleteness`, where it is derived as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## T Canonical Frame Reflexivity (BRV Theorem 4.28, clause 1) -/

/-- **T Canonical Frame Reflexivity** (BRV Theorem 4.28, clause 1):
The canonical frame for T is reflexive. If `phi in w` and `w` is a T-MCS,
then `phi -> diamond(phi) in w` (axiom T), so `diamond(phi) in w`, thus R^T ww. -/
theorem t_canonical_refl
    (S : CanonicalWorld (@TAxiom Atom)) :
    (CanonicalModel (@TAxiom Atom)).r S S :=
  canonical_refl
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .modalT φ)
    S

/-! ## T Truth Lemma (BRV Lemma 4.21 for T) -/

/-- **T Truth Lemma** (BRV Lemma 4.21 for T):
Reuses the existing parameterized `truth_lemma` instantiated at `TAxiom`. -/
theorem t_truth_lemma
    (S : CanonicalWorld (@TAxiom Atom))
    (φ : Proposition Atom) :
    (Satisfies (CanonicalModel (@TAxiom Atom)) S φ ↔ φ ∈ S.val) :=
  truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalT φ)
    S φ

end Cslib.Logic.Modal
