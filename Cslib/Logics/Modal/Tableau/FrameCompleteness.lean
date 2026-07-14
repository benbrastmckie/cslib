/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Completeness

/-! # Frame-Relativized Modal Tableau Completeness (Shared Extractor Skeleton)

This module fixes the shared **closure-at-extraction** helper used by every frame-specific
completeness proof (T, S4, S5, B, 5): given an open saturated branch `b` and accessibility
relation `acc`, extract a Kripke model whose relation is a *closure* `Cl acc.hasEdge` of the
raw tableau accessibility relation, rather than `acc.hasEdge` itself (as `extractModel` does
for K, `Completeness.lean:59`).

## Strategy (Strategy B, closure-at-extraction)

Per-system phases instantiate `Cl` with a Mathlib closure operator so the frame-condition
instance comes free:

| System | Closure operator `Cl` | Frame instance (free) |
|--------|------------------------|------------------------|
| T      | `Relation.ReflGen`     | `Std.Refl` |
| S4     | `Relation.ReflTransGen`| `Std.Refl`, `IsTrans` |
| B      | `Relation.SymmGen`     | `Std.Symm` |
| S5     | universal (`fun _ _ => True`) or `Relation.EqvGen` | `IsEquiv` |

No new frame predicates are defined here — the per-system files reuse the `Cube.lean` frame
classes (`Std.Refl`, `IsTrans`, `Std.Symm`, `Relation.RightEuclidean`) and the
`Satisfies.t`/`Satisfies.b`/`Satisfies.four`/`Satisfies.five` semantic validity theorems for
their soundness arms.

## Main Definitions

- `extractModelWith`: parameterized model extractor over a closure operator `Cl`, mirroring
  `extractModel` (`Completeness.lean:59`) but with `r := Cl acc.hasEdge` instead of
  `r := acc.hasEdge`. The valuation clause is preserved verbatim.

## Notes

This file intentionally does **not** commit to a truth lemma or Hintikka-set characterization:
those are frame-specific (each system's saturation rules determine what Hintikka property the
open branch enjoys, hence what the truth lemma needs to bridge across the closure's extra
edges). Per-system phases add their own `extractModel{T,S4,B,...}` (specialized instances of
`extractModelWith`) and truth lemmas in `FrameCompleteness.lean` / their own dedicated file
(`S5Simplification.lean`, `LoopChecking.lean`), reusing this module's docstring conventions.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v
variable {Atom : Type v} [DecidableEq Atom] [Hashable Atom]

/-! ## Shared Closure-at-Extraction Helper -/

/-- Extract a Kripke model from an open saturated branch `b` and accessibility relation `acc`,
using the closure `Cl acc.hasEdge` as the model's relation instead of `acc.hasEdge` itself
(Strategy B, closure-at-extraction). The world type is `WorldIndex` (= `Nat`), matching
`extractModel` (`Completeness.lean:59`); the valuation clause is preserved verbatim: atom `p`
holds at world `w` iff `T(atom p)@w ∈ b`.

Per-system phases instantiate `Cl` with a Mathlib closure operator
(`Relation.ReflGen`/`ReflTransGen`/`SymmGen`, or the universal relation for S5) so that the
frame-condition instance (`Std.Refl`, `IsTrans`, `Std.Symm`, `IsEquiv`) comes free off the
closure operator — see the module docstring table. -/
def extractModelWith
    (Cl : (WorldIndex → WorldIndex → Prop) → (WorldIndex → WorldIndex → Prop))
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom where
  r := Cl (fun w w' => acc.hasEdge w w' = true)
  v w p := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true

omit [Hashable Atom] in
/-- `extractModelWith` with the identity closure operator is exactly `extractModel` (K). -/
lemma extractModelWith_id (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    extractModelWith (Atom := Atom) id b acc = extractModel b acc := rfl

end Cslib.Logic.Modal.Tableau

end
