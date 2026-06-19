/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for K4 Modal Logic

This module proves completeness for K4 modal logic (= K + axiom 4) via the canonical
Kripke model construction: if a formula is valid on all transitive frames, then it is
K4-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.27** (transitivity is canonical): Uses axiom 4 (`□φ → □□φ`) via
  `canonical_trans` and `mcs_box_box`.

The key insight is that K4 lacks axiom T, so completeness must use `k_truth_lemma`
(from `KCompleteness.lean`) rather than `truth_lemma` (from `Completeness.lean`),
combined with `canonical_trans` (from `Completeness.lean`) for transitivity of
the canonical frame.

This module provides import infrastructure for modal logic K4.
The canonical model construction and supporting lemmas are imported transitively.

The weak completeness theorem `k4_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.K4.StrongCompleteness`, where it is derived as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.27)
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- k_truth_lemma (no axiom T)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- canonical_trans (axiom 4)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

end Cslib.Logic.Modal
