/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Completeness

/-! # Completeness Theorem for Modal Logic D45 (KD45)

This module proves completeness for modal logic D45 over serial + transitive +
Euclidean Kripke frames via the canonical model construction
(completeness-via-canonicity).

D45 = K + D + 4 + 5 contains axiom D (seriality), axiom 4 (transitivity), and
axiom 5 (Euclideanness) but NOT axiom T (reflexivity). Therefore this proof uses:
- `truth_lemma_d` (D-specific truth lemma, NOT `truth_lemma` which requires T)
- `canonical_serial` (from DCompleteness.lean, using axiom D)
- `canonical_trans` (from Completeness.lean, using axiom 4)
- `canonical_eucl_from_5` (from Completeness.lean, using axiom 5)

## Main Results

The weak completeness theorem `d45_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.D45.StrongCompleteness`, where it is derived as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
  - Theorem 4.27 (axiom 4 canonical for transitivity)
  - Theorem 4.28 clause 3 (axiom D canonical for seriality)
  - Axiom 5 canonical for Euclideanness (via `canonical_eucl_from_5`)
  - Theorem 4.29 pattern (combining canonical properties)
  - Lemma 4.21 (Truth Lemma)
  - Proposition 4.12 (Completeness criterion)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

end Cslib.Logic.Modal
