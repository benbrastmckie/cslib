/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.Structures
public import Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.Elimination
public import Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.RecursiveWalks
public import Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.MainElimination

/-!
# Counterexample Elimination (Burgess 2.9-2.10)

Barrel module re-exporting the counterexample elimination machinery split across four submodules.

The construction proceeds in four phases:

1. **Structures** (`CounterexampleElimination.Structures`): C5/C5' counterexample structures,
   fresh-rational helpers, and BurgessR3Maximal helper lemmas (lines 62-291 of the original file).

2. **Elimination** (`CounterexampleElimination.Elimination`): Lemma 2.10 C5/C5' counterexample
   elimination, potential counterexample interface (PotentialCounterexampleKind,
   PotentialCounterexample, EliminationResult), and walk result structures
   (C5ForwardWalkResult, C5BackwardWalkResult) (lines 292-520 of the original file).

3. **RecursiveWalks** (`CounterexampleElimination.RecursiveWalks`): The recursive walk functions
   `c5ForwardWalk` and `c5BackwardWalk` implementing Burgess 2.10 induction with well-founded
   termination on chronicle domain size (lines 521-1613 of the original file).

4. **MainElimination** (`CounterexampleElimination.MainElimination`): The main
   `eliminatePotentialCounterexample` function dispatching across all counterexample kinds
   (C5 forward/backward, C4 forward/backward) and chaining the recursive walks
   (lines 1614-end of the original file).

## References

- Burgess 1982: "Axioms for tense logic II: Time periods", Section 2
-/
