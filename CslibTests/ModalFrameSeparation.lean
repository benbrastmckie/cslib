/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Modal.Tableau.FrameCompleteness

/-! # Modal Frame-Class Separation Regression Test

Live regression check for the S5 vs 5/KB5 frame-class separation: `□p → p` is `s5Valid` but
**not** `fiveValid` and **not** `kb5Valid`.

All three checks are proved via the ported separation theorems in `FrameSoundness.lean`
(`boxImp_s5Valid`, `boxImp_not_fiveValid`, `boxImp_not_kb5Valid`), confirming these theorems
genuinely separate `s5FC` from `fiveFC`/`kb5FC`, not silently collapsing onto one another.
None of the three routes through `decide`: `instDecidableS5Valid`/`instDecidableFiveValid`
reduce through `modalExpandBranchesGen`'s nested `let rec`, which compiles to `WellFounded.fix`
and does not reduce in the kernel, so `decide` gets stuck on those two; `kb5Valid` has no
`Decidable` instance at all yet (`instDecidableKb5Valid` is not landed --
`modalTableauKb5_complete`'s completeness direction is blocked, see `FrameCompleteness.lean`'s
dedicated blocker note beside `extractModelKb5`). -/

namespace CslibTests.ModalFrameSeparation

open Cslib.Logic.Modal.Tableau

/-- `□p → p` is `s5Valid`: reflexivity (the `T` axiom) makes it valid on every equivalence frame.
Proved directly via the ported separation theorem `boxImp_s5Valid` (`FrameSoundness.lean`),
consistent with the `kb5Valid` case below -- `s5Valid`'s `Decidable` instance
(`instDecidableS5Valid`) is not exercised here since it does not reduce in the kernel (its
tableau driver routes through `WellFounded.fix`). -/
example : s5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) :=
  boxImp_s5Valid ()

/-- `□p → p` is **not** `fiveValid`: `fiveFC` (right-Euclidean, no reflexivity) admits the
one-world empty frame as a countermodel. Proved directly via the ported separation theorem
`boxImp_not_fiveValid` (`FrameSoundness.lean`), consistent with the `kb5Valid` case below --
`instDecidableFiveValid` is not exercised here since it does not reduce in the kernel. -/
example : ¬ fiveValid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) :=
  boxImp_not_fiveValid

/-- `□p → p` is **not** `kb5Valid` either -- the same empty-frame countermodel is symmetric, so
moving from 5 to KB5 does not repair the gap. Proved directly via the ported separation theorem
`boxImp_not_kb5Valid` (`FrameSoundness.lean`), since `kb5Valid` has no `Decidable` instance yet. -/
example : ¬ kb5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) :=
  boxImp_not_kb5Valid

end CslibTests.ModalFrameSeparation
