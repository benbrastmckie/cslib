/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Syntax.Formula

/-!
# FMCS: Family of Maximal Consistent Sets

Defines the `FMCS` (Family of Maximal Consistent Sets) structure that assigns
an MCS to each time point, with temporal coherence conditions.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/FMCSDef.lean
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*}

/-- A family of maximal consistent sets indexed by a preordered type, respecting G and
H propagation. -/
structure FMCS (Atom : Type*) (D : Type*) [Preorder D]
    (fc : FrameClass := FrameClass.Base) where
  /-- The function assigning an MCS to each time point. -/
  mcs : D → Set (Formula Atom)
  is_mcs : ∀ t, SetMaximalConsistent fc (mcs t)
  forward_G : ∀ t t' phi, t < t' → Formula.allFuture phi ∈ mcs t → phi ∈ mcs t'
  backward_H : ∀ t t' phi, t' < t → Formula.allPast phi ∈ mcs t → phi ∈ mcs t'

end Cslib.Logic.Bimodal.Metalogic.Bundle
