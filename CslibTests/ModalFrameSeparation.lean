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
and does not reduce in the kernel, so `decide` gets stuck on those two.

`kb5Valid` now HAS a `Decidable` instance (`instDecidableKb5Valid`, `FrameCompleteness.lean`,
backed by the corrected-gate full-cluster rule `modalApplyOneKb5''` and its completeness theorem
`modalTableauKb5''_complete`) -- but it shares the identical kernel-reduction stall the other two
instances already have, confirmed directly: `set_option maxHeartbeats 8000 in example : ¬ kb5Valid
(Atom := Unit) (.imp (.box (.atom ())) (.atom ())) := by decide` fails with reduction stuck at
`modalTableauKb5''`'s own `match`, the same `WellFounded.fix`-via-nested-`let rec` failure mode as
`instDecidableS5Valid`/`instDecidableFiveValid` -- landing `instDecidableKb5Valid` neither
resolves nor sidesteps this pre-existing, orthogonal issue; it is a driver-level limitation
unrelated to which frame condition the rule targets. The instance is still useful (it typechecks,
composes with `kb5Valid_decides`, and is exercised below via `inferInstance`/direct proof terms
rather than `decide`), and correctness is independently confirmed by the separation examples
below plus the corrected-gate completeness examples, none of which need kernel reduction of the
tableau driver itself. -/

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
`boxImp_not_kb5Valid` (`FrameSoundness.lean`); still proved directly rather than via `decide`,
since `instDecidableKb5Valid` (below) shares the kernel-reduction stall documented in the module
docstring above. -/
example : ¬ kb5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) :=
  boxImp_not_kb5Valid

/-- `instDecidableKb5Valid` exists and typechecks: exercised via `inferInstance`, not `decide`,
per the module docstring's kernel-reduction-stall diagnosis above. -/
example : Decidable (kb5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ()))) :=
  inferInstance

/-- `p → p` is trivially `kb5Valid` (no modal content, holds on every frame regardless of the
frame condition). -/
example : kb5Valid (Atom := Unit) (.imp (.atom ()) (.atom ())) :=
  fun _ _ _ _ hsat => hsat

/-- **Regression for the corrected-gate KB5 completeness delivery**: `modalTableauKb5''_complete`
concretely closes the tableau on a genuine `kb5Valid` formula. This exercises the completeness
direction end-to-end (validity proof in, `.closed` result out) without needing kernel `decide`. -/
example : modalTableauKb5'' (Atom := Unit) (.imp (.atom ()) (.atom ())) = .closed :=
  modalTableauKb5''_complete _ (fun _ _ _ _ hsat => hsat)

end CslibTests.ModalFrameSeparation
