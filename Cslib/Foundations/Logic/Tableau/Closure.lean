/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

/-! # Closure Reason Type

This module defines `ClosureReason F L`, which explains why a tableau branch is closed.
The two constructors correspond to the two closure criteria used in classical and
intuitionistic logics.

## Main Definitions

- `ClosureReason F L`: Inductive type with two closure modes.
  - `botPos l`: Branch contains T(bot) at label `l` (classical and intuitionistic).
  - `contradiction phi l`: Branch contains both T(phi) and F(phi) at label `l` (classical).

## Closure Modes

| Logic | Closes on |
|-------|-----------|
| Classical | T(bot) OR T(phi)/F(phi) for any phi |
| Intuitionistic | T(bot) only |
| Minimal | T(phi)/F(phi) at the same label (via `Branch.hasContradiction`, not this type) |

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Tableau

/-! ## ClosureReason -/

/-- An explanation of why a tableau branch is closed.

Two closure modes are supported, corresponding to different logic strengths:

- `botPos l`: The branch contains the positively signed falsum T(bot) at label `l`.
  Valid in classical and intuitionistic logic.
- `contradiction phi l`: The branch contains both T(phi) and F(phi) at label `l`.
  Valid in classical logic only.

The minimal closure criterion (T(phi)/F(phi) at the same label) is computed directly
via `Branch.hasContradiction` rather than through this type. -/
inductive ClosureReason (F : Type*) (L : Type*) where
  /-- Branch contains T(bot) at label `l`. -/
  | botPos (l : L) : ClosureReason F L
  /-- Branch contains both T(phi) and F(phi) at the same label `l`. -/
  | contradiction (phi : F) (l : L) : ClosureReason F L

end Cslib.Logic.Tableau

end
