/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for KB5 Modal Logic

This module proves completeness for KB5 modal logic (= K + B + 5) via the canonical
Kripke model construction: if a formula is valid on all symmetric, Euclidean frames,
then it is KB5-derivable.

KB5 is the first logic in the modal cube that combines BOTH new canonical lemmas
from task 100: `canonical_symm` (symmetry from axiom B alone) and
`canonical_eucl_from_5` (Euclideanness from axiom 5 alone).

**Key distinction**: KB5 does NOT contain axiom T, so the completeness proof uses
`k_truth_lemma` (K-style, no reflexivity hypothesis) rather than `truth_lemma`
(which requires axiom T for the box witness / existence lemma).

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.28, clause 2** (symmetry is canonical): Uses axiom B (`φ → □◇φ`)
  via `canonical_symm`.

- **Axiom 5 canonicity** (Euclideanness is canonical): Uses axiom 5 (`◇φ → □◇φ`)
  via `canonical_eucl_from_5`.

## Main Results

The weak completeness theorem `kb5_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.KB5.StrongCompleteness`, where it is derived as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.23, 4.28)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- canonical_symm, canonical_eucl_from_5
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- k_truth_lemma (no axiom T)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

end Cslib.Logic.Modal
