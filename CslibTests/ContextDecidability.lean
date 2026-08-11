/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability
import Cslib.Logics.Propositional.SequentCalculus.LK.Decidability
public meta import Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability
public meta import Cslib.Logics.Propositional.SequentCalculus.LK.Decidability

/-! # Context Decidability Conformance Tests

Executable conformance checks for the four context-based `Decidable` instances for the
propositional sequent calculi: `instDecidableLJDerivable`, `instDecidableDerivableInIPL`,
`instDecidableLKDerivable`, and `instDecidableDerivableInCPL`. These instances were made
computable (see `LJ.Decidability` and `LK.Decidability`) by eliminating a context's underlying
`Multiset` via `Quotient.recOnSubsingleton` into a computable list-level helper
(`ljListDerivableDecidable` / `lkListDerivableDecidable`), instead of routing through the
inherently `noncomputable` `ctxToImp`. This file exercises that construction on **non-empty**
contexts, the case that previously could not evaluate at all.

## Why `#eval`, not `decide`

`by decide` stalls on these instances, but **not** because of anything introduced by the
`Quotient.recOnSubsingleton` construction. The kernel unfolds cleanly *through*
`decidable_of_decidable_of_iff`, `decidable_of_iff`, `instDecidableLJDerivable`, and
`ljListDerivableDecidable` (or their LK counterparts), and only gets stuck at the pre-existing
`WellFounded.fix` inside the tableau decision procedure driver -- the same obstruction
`CslibTests/TableauConformance.lean`'s header documents for the tableau drivers generally. The
new construction adds no new kernel obstruction; it inherits the existing one. `#eval`, which
runs via the compiler rather than the kernel, is therefore the right and only available idiom
here, matching the task's own verification requirement.

## Header requirement

This file needs **both** `import X` and `public meta import X` for each Decidability module:
without the plain form, referencing a constructor (e.g. `Proposition.atom`) at the term level
fails; without the `meta` form, referencing the `Decidable` instances at `#eval` time fails with
"may not access declaration ... imported as 'meta'". This mirrors
`CslibTests/TableauConformance.lean`'s header.

This file does not import `Cslib.Init`; `CslibTests/*.lean` files never do (confirmed against
`CslibTests/Propositional.lean`), so `checkInitImports` does not apply here.

## Atom Type

`Atom := Bool`, matching `CslibTests/Propositional.lean`'s convention: `false` plays the role of
atom `p`, `true` plays the role of atom `q`.
-/

namespace CslibTests.ContextDecidability

open Cslib.Logic.PL Cslib.Logic.InferenceSystem

/-! ## LJ (intuitionistic), non-empty context -/

-- `{p, p → q} ⊢ q` -- the task's target case: a non-empty-context LJ decision that now
-- evaluates.
/-- info: true -/
#guard_msgs in
#eval decide (Nonempty (LJProof
  (({Proposition.atom false,
      Proposition.imp (Proposition.atom false) (Proposition.atom true)} : Ctx Bool) ⊢
    Proposition.atom true)))

-- `{q} ⊢ p` is not LJ-derivable.
/-- info: false -/
#guard_msgs in
#eval decide (Nonempty (LJProof (({Proposition.atom true} : Ctx Bool) ⊢ Proposition.atom false)))

/-! ## LK (classical), non-empty context -/

-- `{p, p → q} ⊢ q` is LK-derivable.
/-- info: true -/
#guard_msgs in
#eval decide (Nonempty (LKProof
  (({Proposition.atom false,
      Proposition.imp (Proposition.atom false) (Proposition.atom true)} : Ctx Bool) ⊢ₛ
    {Proposition.atom true})))

-- `{q} ⊢ p` is not LK-derivable.
/-- info: false -/
#guard_msgs in
#eval decide (Nonempty (LKProof (({Proposition.atom true} : Ctx Bool) ⊢ₛ {Proposition.atom false})))

/-! ## Excluded middle: the LJ/LK intuitionistic/classical contrast

`∅ ⊢ p ∨ (p → ⊥)` is classically but not intuitionistically valid. This is the strongest single
check that the two instances are wired to their own decision procedures and not accidentally to
each other. -/

-- LJ: excluded middle is not intuitionistically valid.
/-- info: false -/
#guard_msgs in
#eval decide (Nonempty (LJProof
  ((∅ : Ctx Bool) ⊢
    Proposition.or (Proposition.atom false)
      (Proposition.imp (Proposition.atom false) Proposition.bot))))

-- LK: excluded middle is classically valid.
/-- info: true -/
#guard_msgs in
#eval decide (Nonempty (LKProof
  ((∅ : Ctx Bool) ⊢ₛ
    {Proposition.or (Proposition.atom false)
      (Proposition.imp (Proposition.atom false) Proposition.bot)})))

/-! ## `DerivableIn` forms

Exercises `instDecidableDerivableInIPL` and `instDecidableDerivableInCPL` directly, rather than
`instDecidableLJDerivable`/`instDecidableLKDerivable`. -/

-- IPL: `{p} ⊢ p` is derivable.
/-- info: true -/
#guard_msgs in
#eval decide (DerivableIn (AxiomTheory (@IntPropAxiom Bool) : Theory Bool)
  (({Proposition.atom false} : Ctx Bool) ⊢ Proposition.atom false))

-- IPL: `{q} ⊢ p` is not derivable.
/-- info: false -/
#guard_msgs in
#eval decide (DerivableIn (AxiomTheory (@IntPropAxiom Bool) : Theory Bool)
  (({Proposition.atom true} : Ctx Bool) ⊢ Proposition.atom false))

-- CPL: `{p} ⊢ p` is derivable.
/-- info: true -/
#guard_msgs in
#eval decide (DerivableIn (AxiomTheory (@PropositionalAxiom Bool) : Theory Bool)
  (({Proposition.atom false} : Ctx Bool) ⊢ Proposition.atom false))

end CslibTests.ContextDecidability
