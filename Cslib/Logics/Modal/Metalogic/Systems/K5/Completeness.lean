/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness

/-! # Completeness Theorem for Modal Logic K5

This module proves completeness for modal logic K5 (K + axiom 5) over Euclidean
Kripke frames via the canonical model construction (completeness-via-canonicity).

This module provides import infrastructure for modal logic K5.
The canonical model construction and supporting lemmas are imported transitively.

The weak completeness theorem `k5_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.K5.StrongCompleteness`, where it is derived as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## Strategy

K5 has NO axiom T, so it uses `k_truth_lemma` (from KCompleteness.lean), not
`truth_lemma` (which requires axiom T). The canonical frame is shown Euclidean
via `canonical_eucl_from_5` (from Completeness.lean), which uses only axiom 5.

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
  - Theorem 4.29 pattern (completeness-via-canonicity with frame property proof)
  - Lemma 4.21 (Truth Lemma)
  - Proposition 4.12 (Completeness criterion)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

end Cslib.Logic.Modal
