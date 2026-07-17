/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Modal.Tableau.FrameCompleteness

/-! # Modal Frame-Class Separation Regression Test (task 515 Phase 23)

Live regression check for the S5 vs 5/KB5 frame-class separation: `□p → p` is `s5Valid` but
**not** `fiveValid` and **not** `kb5Valid`. Confirms `instDecidableS5Valid`/`instDecidableFiveValid`
genuinely route through their respective frame conditions (`s5FC`/`fiveFC`), not silently
collapsing onto one another.

`kb5Valid`'s negation is checked via the proven theorem `boxImp_not_kb5Valid`
(`FrameSoundness.lean`) rather than `decide`: `instDecidableKb5Valid` is not yet landed
(`modalTableauKb5_complete`'s completeness direction is blocked, see `FrameCompleteness.lean`'s
dedicated blocker note beside `extractModelKb5`), so `kb5Valid` has no computable `Decidable`
instance to `decide` against. -/

namespace CslibTests.ModalFrameSeparation

open Cslib.Logic.Modal.Tableau

/-- `□p → p` is `s5Valid`: reflexivity (the `T` axiom) makes it valid on every equivalence frame.
Checked via the tableau's `Decidable` instance (`instDecidableS5Valid`), not the semantic proof
directly -- this exercises the actual decision procedure, not just the frame-class argument. -/
example : decide (s5Valid (Atom := Bool) (.imp (.box (.atom false)) (.atom false))) = true := by
  decide

/-- `□p → p` is **not** `fiveValid`: `fiveFC` (right-Euclidean, no reflexivity) admits the
one-world empty frame as a countermodel. Checked via `instDecidableFiveValid`. -/
example : decide (fiveValid (Atom := Bool) (.imp (.box (.atom false)) (.atom false))) = false := by
  decide

/-- `□p → p` is **not** `kb5Valid` either -- the same empty-frame countermodel is symmetric, so
moving from 5 to KB5 does not repair the gap. Proved directly via the ported separation theorem
`boxImp_not_kb5Valid` (`FrameSoundness.lean`), since `kb5Valid` has no `Decidable` instance yet. -/
example : ¬ kb5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) :=
  boxImp_not_kb5Valid

end CslibTests.ModalFrameSeparation
