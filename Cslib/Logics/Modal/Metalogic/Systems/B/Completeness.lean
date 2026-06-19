/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # B Completeness Infrastructure

This module provides import infrastructure for modal logic B.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `b_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.B.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

end Cslib.Logic.Modal
