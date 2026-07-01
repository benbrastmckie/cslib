/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.Sign
public import Cslib.Foundations.Logic.Tableau.SignedFormula
public import Cslib.Foundations.Logic.Tableau.RuleResult
public import Cslib.Foundations.Logic.Tableau.Branch
public import Cslib.Foundations.Logic.Tableau.Closure
public import Cslib.Foundations.Logic.Tableau.ClosureCondition
public import Cslib.Foundations.Logic.Tableau.Measure
public import Cslib.Foundations.Logic.Tableau.PropositionalRules

/-! # Shared Tableau Infrastructure

This module re-exports all components of the `Cslib.Foundations.Logic.Tableau` module,
providing logic-neutral tableau infrastructure shared across classical, intuitionistic,
minimal, modal, and temporal tableau calculi.

## Contents

- `Sign`: Unified two-valued sign type.
- `SignedFormula`: Generic signed formula type parameterized over formula and label types.
- `RuleResult`: Four-variant rule result type (linear/branching/persistent/notApplicable).
- `Branch`: Branch type with label-generic operations.
- `ClosureReason`: Inductive type explaining why a branch is closed.
- `ClosureCondition`: Typeclass for branch closure with classical/intuitionistic/minimal instances.
- `Measure`: Logic-agnostic termination-measure arithmetic (`geomCap`, base-3 decrease lemmas)
  shared across tableau calculi.
- `PropTableauRule`, `applyPropRule`, `tryAllPropRules`: Classical propositional rules.
-/
