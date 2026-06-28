/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LK.Basic
public import Cslib.Logics.Propositional.SequentCalculus.LK.Completeness
-- CutElimination is available transitively via SubformulaProperty and CutFreeCompleteness
public import Cslib.Logics.Propositional.SequentCalculus.LK.Soundness
public import Cslib.Logics.Propositional.SequentCalculus.LK.SubformulaProperty
public import Cslib.Logics.Propositional.SequentCalculus.LK.Decidability
public import Cslib.Logics.Propositional.SequentCalculus.LK.CutFreeCompleteness

/-! # LK Classical Propositional Sequent Calculus

Barrel import for all LK files. -/
