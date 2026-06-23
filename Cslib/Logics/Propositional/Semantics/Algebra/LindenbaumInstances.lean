/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Algebra.Lindenbaum

/-! # Named Lindenbaum-Tarski Algebra Instances

This module exports named, standalone declarations making explicit the algebraic structure of
the Lindenbaum-Tarski algebras for the three standard propositional logics:

- **MPL** (minimal propositional logic, `Theory.MPL = ∅`): its Lindenbaum algebra is a
  `GeneralizedHeytingAlgebra`.
- **IPL** (intuitionistic propositional logic, `Theory.IPL`): its Lindenbaum algebra is a
  `HeytingAlgebra`.
- **CPL** (classical propositional logic, `Theory.IPL ∪ Theory.CPL`): its Lindenbaum algebra
  is a `BooleanAlgebra`.

Note on CPL: The ND-level classical theory is `Theory.IPL ∪ Theory.CPL` (explosion + DNE),
consistent with the bridge theorems in `HilbertConservativeGlivenko.lean`. The theory
`Theory.CPL` alone does not contain the explosion principle, so it does not satisfy
`IsIntuitionistic` on its own.

The generic instances exist in `Lindenbaum.lean` parameterized over any `T : Theory Atom`
with appropriate typeclass constraints. This module specializes and names them for direct use
by downstream reasoning about these specific logics.

## Main Definitions

- `MPL.LindenbaumAlgebra Atom`: the Lindenbaum-Tarski algebra of MPL.
- `IPL.LindenbaumAlgebra Atom`: the Lindenbaum-Tarski algebra of IPL.
- `CPL.LindenbaumAlgebra Atom`: the Lindenbaum-Tarski algebra of CPL (using `IPL ∪ CPL`).

## Main Instances

- `MPL.instGHA`: `GeneralizedHeytingAlgebra (MPL.LindenbaumAlgebra Atom)`
- `IPL.instHA`: `HeytingAlgebra (IPL.LindenbaumAlgebra Atom)`
- `CPL.instBA`: `BooleanAlgebra (CPL.LindenbaumAlgebra Atom)`

## Future Directions

The free Boolean algebra universal property for `CPL.LindenbaumAlgebra Atom` (showing it is
the free Boolean algebra on generators `Atom`) is deferred to a separate task.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Theory

variable (Atom : Type u) [DecidableEq Atom]

/-! ## Named Type Abbreviations -/

/-- The Lindenbaum-Tarski algebra of MPL (minimal propositional logic).
MPL is the empty theory (`Theory.MPL = ∅`), and its Lindenbaum algebra is a
`GeneralizedHeytingAlgebra`. -/
abbrev MPL.LindenbaumAlgebra : Type u :=
  Cslib.Logic.PL.LindenbaumAlgebra (Theory.MPL : Theory Atom)

/-- The Lindenbaum-Tarski algebra of IPL (intuitionistic propositional logic).
IPL adds the explosion principle to MPL, making its Lindenbaum algebra a `HeytingAlgebra`. -/
abbrev IPL.LindenbaumAlgebra : Type u :=
  Cslib.Logic.PL.LindenbaumAlgebra (Theory.IPL : Theory Atom)

/-- The Lindenbaum-Tarski algebra of CPL (classical propositional logic).
Uses `Theory.IPL ∪ Theory.CPL` as the full ND-level classical theory, consistent with the
bridge theorems in `HilbertConservativeGlivenko.lean`. The union ensures both explosion
(`IsIntuitionistic`) and double-negation elimination (`IsClassical`) hold,
enabling the `BooleanAlgebra` instance. -/
abbrev CPL.LindenbaumAlgebra : Type u :=
  Cslib.Logic.PL.LindenbaumAlgebra (Theory.IPL ∪ Theory.CPL : Theory Atom)

/-! ## Auxiliary Instances for the Union Theory

The theories `Theory.IPL` and `Theory.CPL` each satisfy one half of the requirements for a
`BooleanAlgebra`. The union `Theory.IPL ∪ Theory.CPL` satisfies both. These instances are
needed to synthesize `HeytingAlgebra` and `BooleanAlgebra` for `CPL.LindenbaumAlgebra`. -/

/-- The theory `Theory.IPL ∪ Theory.CPL` is intuitionistic, because `Theory.IPL ⊆ Theory.IPL ∪
Theory.CPL` and `Theory.IPL` is intuitionistic. -/
instance instIsIntuitionisticIPLUnionCPL :
    IsIntuitionistic (Theory.IPL ∪ Theory.CPL : Theory Atom) :=
  instIsIntuitionisticExtention Set.subset_union_left

/-- The theory `Theory.IPL ∪ Theory.CPL` is classical, because `Theory.CPL ⊆ Theory.IPL ∪
Theory.CPL` and `Theory.CPL` is classical. -/
instance instIsClassicalIPLUnionCPL :
    IsClassical (Theory.IPL ∪ Theory.CPL : Theory Atom) :=
  instIsClassicalExtention Set.subset_union_right

/-! ## Named Algebra Instances -/

/-- The Lindenbaum-Tarski algebra of MPL is a `GeneralizedHeytingAlgebra`.
This instance is named for direct use; the proof delegates to the generic instance in
`Lindenbaum.lean` which holds for any theory. -/
instance MPL.instGHA : GeneralizedHeytingAlgebra (MPL.LindenbaumAlgebra Atom) :=
  inferInstance

/-- The Lindenbaum-Tarski algebra of IPL is a `HeytingAlgebra`.
IPL satisfies `IsIntuitionistic`, enabling the bottom element `⊥ = [⊥]` and
the `HeytingAlgebra` structure. -/
instance IPL.instHA : HeytingAlgebra (IPL.LindenbaumAlgebra Atom) :=
  inferInstance

/-- The Lindenbaum-Tarski algebra of CPL is a `BooleanAlgebra`.
The full classical theory `Theory.IPL ∪ Theory.CPL` satisfies both `IsIntuitionistic` and
`IsClassical`, enabling the `BooleanAlgebra` instance via `BooleanAlgebra.ofRegular`.
This instance is noncomputable because `BooleanAlgebra.ofRegular` is noncomputable. -/
noncomputable instance CPL.instBA : BooleanAlgebra (CPL.LindenbaumAlgebra Atom) :=
  inferInstance

/-! ## Characterization Lemmas -/

/-- The Lindenbaum-Tarski algebra of MPL is a `GeneralizedHeytingAlgebra`.
This lemma makes explicit the algebraic characterization as a standalone named fact. -/
lemma MPL.lindenbaumIsGHA :
    Nonempty (GeneralizedHeytingAlgebra (MPL.LindenbaumAlgebra Atom)) :=
  ⟨inferInstance⟩

/-- The Lindenbaum-Tarski algebra of IPL is a `HeytingAlgebra`.
This lemma makes explicit the algebraic characterization as a standalone named fact. -/
lemma IPL.lindenbaumIsHA :
    Nonempty (HeytingAlgebra (IPL.LindenbaumAlgebra Atom)) :=
  ⟨inferInstance⟩

/-- The Lindenbaum-Tarski algebra of CPL (as `Theory.IPL ∪ Theory.CPL`) is a `BooleanAlgebra`.
This lemma makes explicit the algebraic characterization as a standalone named fact. -/
lemma CPL.lindenbaumIsBA :
    Nonempty (BooleanAlgebra (CPL.LindenbaumAlgebra Atom)) :=
  ⟨CPL.instBA Atom⟩

end Cslib.Logic.PL
