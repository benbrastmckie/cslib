/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Syntax.Formula
public import Cslib.Logics.Temporal.Syntax.Formula

/-! # LTL-to-Temporal Embedding

This module defines the canonical embedding of `LTL.Formula` into `Temporal.Formula`.
LTL uses the standard convention `untl guard event`, while Temporal uses the Burgess
convention `untl event guard`. The embedding bridges the two by swapping arguments.

## Main definitions

- `Formula.toTemporal` : Embedding of `LTL.Formula` into `Temporal.Formula`

## Semantic correspondence

`LTL.Satisfies` uses reflexive (non-strict) until: `∃ j ≥ i, ...`. The BX tense
logic uses strict until: `∃ s > t, ...`. To preserve semantics, `untl` maps to
`reflexiveUntl` (the derived non-strict operator), while `next` maps to the strict
`untl · bot` which forces the witness to be the immediate successor on ℕ.

## References

* [A. Pnueli, *The Temporal Logic of Programs*][Pnueli1977]
* [J. P. Burgess, *Basic Tense Logic*][Burgess1984]
-/

@[expose] public section

namespace Cslib.Logic.LTL

/-- Embed `LTL.Formula` into `Temporal.Formula`.

`LTL.Satisfies` uses reflexive (non-strict) until: `∃ j ≥ i, ...`. The BX tense logic
uses strict until: `∃ s > t, ...`. To preserve semantics, `untl` maps to
`reflexiveUntl` (the derived non-strict operator), while `next` maps to the strict
`untl · bot` which forces the witness to be the immediate successor on ℕ. -/
def Formula.toTemporal : Formula Atom → Temporal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ ψ => .imp (toTemporal φ) (toTemporal ψ)
  | .next φ => .untl .bot (toTemporal φ)
  | .untl φ₁ φ₂ => (toTemporal φ₂).reflexiveUntl (toTemporal φ₁)

end Cslib.Logic.LTL

end
