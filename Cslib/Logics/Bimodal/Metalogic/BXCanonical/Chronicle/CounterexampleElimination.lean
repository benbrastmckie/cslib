/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.CounterexampleElimination.Structures
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.CounterexampleElimination.BurgessHelpers
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.CounterexampleElimination.Elimination
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.CounterexampleElimination.Interface

/-!
# Counterexample Elimination (Burgess 2.9-2.10)

Barrel module re-exporting the counterexample elimination machinery split across four submodules.

The construction proceeds in four phases:

1. **Structures** (`CounterexampleElimination.Structures`): C5/C5' counterexample structures
   and fresh-rational helpers (lines 66-183 of the original file).

2. **BurgessHelpers** (`CounterexampleElimination.BurgessHelpers`): BurgessR3Maximal fc
   helper lemmas — gContent subset, SetDeductivelyClosed, bot exclusion, adjacency
   preservation, backward h-content construction (lines 184-355).

3. **Elimination** (`CounterexampleElimination.Elimination`): Lemma 2.10 C5/C5' elimination
   and G/H-propagation counterexample elimination (lines 356-547).

4. **Interface** (`CounterexampleElimination.Interface`): Potential counterexample interface —
   PotentialCounterexampleKind, PotentialCounterexample, EliminationResult, C5ForwardWalkResult,
   C5BackwardWalkResult, c5ForwardWalk, c5BackwardWalk, eliminatePotentialCounterexample
   (lines 548-3544 of the original file).

## References

- Burgess 1982: "Axioms for tense logic II: Time periods", Section 2
-/
