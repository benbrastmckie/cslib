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
open Cslib.Logic.Modal (Satisfies Model)

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

/-! ## TB Smoke Checks

Direct semantic proof-term checks for `tbValid` (reflexive-symmetric-frame validity),
consistent with the S5/5/KB5 checks above: `modalTableauTB` routes through the same
`modalExpandBranchesGen` nested-`let rec` driver, which stalls `decide`/`native_decide`/`rfl`
in the kernel, so these are proved directly against `tbValid`'s semantic definition
(`frameValid tbFC`) rather than by evaluating `instDecidableTBValid`. -/

/-- The T axiom `□p → p` is `tbValid`: reflexivity alone (the `.1` conjunct of `tbFC`) makes it
valid on every reflexive-symmetric frame. -/
example : tbValid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) := by
  intro World m hfc w hbox
  exact hbox w (hfc.1.refl w)

/-- The B axiom `p → □◇p` is `tbValid`: symmetry alone (the `.2` conjunct of `tbFC`) makes it
valid on every reflexive-symmetric frame -- for any `r`-successor `w'` of `w`, symmetry gives
`r w' w`, and `w` itself witnesses `◇p` there since `p` holds at `w` by hypothesis. -/
example : tbValid (Atom := Unit) (.imp (.atom ()) (.box (.diamond (.atom ())))) := by
  intro World m hfc w hp w' hww'
  exact ⟨w, hfc.2.symm w w' hww', hp⟩

/-- The raw adjacency relation for the three-world path countermodel `0 -- 1 -- 2` (reflexive
loops at each world, symmetric edges `0↔1` and `1↔2`, no edge `0↔2`): reflexive and symmetric,
but not transitive (`0 -- 1` and `1 -- 2` do not give `0 -- 2`). Proved manually via literal
`Fin 3` case terms (mirroring `boxImp_not_fiveValid`'s `emptyFrame` idiom above), not `decide`:
`Satisfies` has no general `Decidable` instance for `decide` to discharge these through. -/
private def tbCounterR : Fin 3 → Fin 3 → Prop
  | 0, 0 | 1, 1 | 2, 2 | 0, 1 | 1, 0 | 1, 2 | 2, 1 => True
  | _, _ => False

/-- The countermodel: three worlds `Fin 3`, `tbCounterR` above, atom `()` true everywhere except
world `2`. -/
private def tbCounterModel : Model (Fin 3) Unit := ⟨tbCounterR, fun w _ => w ≠ 2⟩

private lemma tbCounterR_refl : Std.Refl tbCounterR where
  refl a := by match a with
    | 0 => trivial
    | 1 => trivial
    | 2 => trivial

private lemma tbCounterR_symm : Std.Symm tbCounterR where
  symm a b hab := by match a, b with
    | 0, 0 => trivial
    | 1, 1 => trivial
    | 2, 2 => trivial
    | 0, 1 => trivial
    | 1, 0 => trivial
    | 1, 2 => trivial
    | 2, 1 => trivial
    | 0, 2 => exact hab.elim
    | 2, 0 => exact hab.elim

/-- `□p` holds at world `0` of `tbCounterModel`: `0`'s only `r`-neighbors are `0` and `1`, and
`p` holds at both. -/
private theorem tb_box_atom_holds : Satisfies tbCounterModel (0 : Fin 3) (.box (.atom ())) := by
  intro w' hw'
  match w' with
  | 0 => change (0 : Fin 3) ≠ 2; decide
  | 1 => change (1 : Fin 3) ≠ 2; decide
  | 2 => exact hw'.elim

/-- `□□p` fails at world `0` of `tbCounterModel`: `1`'s neighbor `2` fails `p`, so `□p` fails at
`1`, so `□□p` fails at `0`. -/
private theorem tb_box_box_atom_fails :
    ¬ Satisfies tbCounterModel (0 : Fin 3) (.box (.box (.atom ()))) := by
  intro h
  have h1 : Satisfies tbCounterModel (1 : Fin 3) (.box (.atom ())) := h 1 trivial
  have h2 : Satisfies tbCounterModel (2 : Fin 3) (.atom ()) := h1 2 trivial
  exact h2 rfl

/-- The 4 axiom `□p → □□p` is **not** `tbValid`: TB frames need not be transitive. -/
example : ¬ tbValid (Atom := Unit) (.imp (.box (.atom ())) (.box (.box (.atom ())))) := by
  intro hv
  exact tb_box_box_atom_fails
    (hv (Fin 3) tbCounterModel ⟨tbCounterR_refl, tbCounterR_symm⟩ 0 tb_box_atom_holds)

end CslibTests.ModalFrameSeparation
