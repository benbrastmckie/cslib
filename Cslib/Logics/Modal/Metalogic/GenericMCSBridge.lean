/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module  -- shake: keep-all

public import Cslib.Foundations.Logic.Metalogic.GenericMCS
public import Cslib.Logics.Modal.Metalogic.DerivationTree

/-! # GenericMCS Bridge for Normal Modal Logics (status note)

This module documents the relationship between the two derivation systems available for
normal modal logics and records why the generic tree↔algebraic bridge is not yet proved
here. It contains no Lean declarations.

1. **`algebraicDerivationSystem (S := Modal.HilbertK)`**: built from `ListDeriv` via the
   generic MCS framework. Available for any `MinimalHilbert` proof system.
2. **`modalDerivationSystem (@KAxiom Atom)`**: built from explicit `DerivationTree`
   induction, parameterised by an axiom predicate `Axioms : Proposition Atom → Prop`.

## The bridge IS buildable

A temporal-style bidirectional bridge
`modalDerivationSystem.Deriv Γ φ ↔ algebraicDerivationSystem.Deriv Γ φ` is constructible by
exactly the same proof used for the Temporal and Bimodal logics:

* `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`
* `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`

Both prove `*_deriv_iff_algebraic`, `*_setConsistent_iff_algebraic`, and
`*_setMaxConsistent_iff_algebraic` by structural induction on `DerivationTree` (forward) and
`listImp`-peeling (backward). For any *concrete* modal system the same proof transfers
directly: `Modal.HilbertK` already carries `InferenceSystem`, `ModusPonens`, `Necessitation`,
the `HasAxiom*` instances, and `ModalHilbert` (see
`Cslib/Logics/Modal/ProofSystem/Instances/K.lean`), with
`derivation φ := DerivationTree (@KAxiom Atom) [] φ` — the same structural pattern as
`HilbertT`/`HilbertTM`.

(The old `□(φ → φ)` "counterexample" claiming this formula was not algebraically derivable
from `[]` was mistaken: at empty context `algDS.Deriv [] φ` unfolds to
`Nonempty (DerivationTree KAxiom [] φ)`, which includes necessitation, so
`DerivationTree.necessitation (φ→φ) ⋯` witnesses `□(φ → φ)`.)

## Why it is not proved here yet (infrastructure gap)

`modalDerivationSystem` is parameterised by a value-level predicate
`Axioms : Proposition Atom → Prop`, whereas `algebraicDerivationSystem` is parameterised by a
*type* `S` carrying `[InferenceSystem S F]` and `[MinimalHilbert S]` instances. For an
arbitrary `Axioms` there is no single type `S` to instantiate `algebraicDerivationSystem` at,
so the one-bridge-covers-all-systems form requires a wrapper type
`HilbertOf Axioms : Type` whose `InferenceSystem` maps derivability to
`Nonempty (DerivationTree Axioms [] φ)` and whose `Necessitation` instance lifts the
tree-level necessitation constructor. This is an infrastructure gap, not a semantic one.

## What modal logics can already use today

The propositional MCS path works with no new code: the instance chain
`Modal.HilbertK → MinimalHilbert → algebraicDerivationSystem` makes all
`SetMaximalConsistent` properties from the generic MCS framework available for propositional
reasoning. For modal-specific MCS properties (box closure, box-box, …) the tree-based
`modalDerivationSystem` path is used because necessitation is required.

```lean
-- Already works (no new code needed):
#check @algebraicDerivationSystem (Modal.Proposition Atom) _ _ (S := Modal.HilbertK) _
#check @algebraic_mcs_negation_complete (Modal.Proposition Atom) _ _ (S := Modal.HilbertK) _
```

## Follow-up task

Build the `HilbertOf Axioms` wrapper type with `InferenceSystem` + `MinimalHilbert` +
`Necessitation` instances synthesised from the axiom constructors, prove the modal and
propositional bridges (mirroring the Temporal/Bimodal files), and re-implement both
`deductionTheorem` defs without WF-recursion. Roughly 25 raw call sites across
`Modal/Completeness`, `MCS`, `Systems/{K,D}`, `Propositional/StrongCompleteness`,
`Min/IntLindenbaum`, and `NaturalDeduction` must keep compiling. See the task 350 summary for
full scope.
-/
