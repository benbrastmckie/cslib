/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for K45 Modal Logic

This module proves completeness for K45 modal logic (= K + 4 + 5) via the canonical
Kripke model construction: if a formula is valid on all transitive, Euclidean frames,
then it is K45-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.27** (transitivity is canonical): The canonical frame of any normal
  logic containing the 4 axiom is transitive, via `canonical_trans`.

- **Axiom 5 canonical for Euclideanness**: The canonical frame of any normal logic
  containing axiom 5 is Euclidean, via `canonical_eucl_from_5`.

- Since K45 has NO axiom T, the proof uses `k_truth_lemma` (BRV Lemma 4.21 for K)
  instead of `truth_lemma` (which requires axiom T).

## Main Results

The weak completeness theorem `k45_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.K45.StrongCompleteness`, where it is derived as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.27, Definition 4.30)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- canonical model, canonical_trans,
  canonical_eucl_from_5
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- k_truth_lemma (no axiom T)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

end Cslib.Logic.Modal
