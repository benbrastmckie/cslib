/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Basic

/-! # Nested Sequent Syntax and the `fm` Translation

This module encodes Arisaka–Das–Straßburger's nested-sequent syntax (`doc_id:
arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`, §2, eq. (2.1)) and the
corresponding-formula translation `fm`, the base of the cut-free proof system for `CS5` built in
the sibling modules of this directory. Verified against the recovered source PDF (cross-checked
via both direct rendering and `pdftotext -layout`) rather than the `unverified_summary`
literature-search index chunks.

## Grammar (eq. (2.1))

```
Φ ::= ∅ | A• | [Φ] | Φ, Φ        (LHS sequents)
Ψ ::= A◦ | [Φ, Ψ]                 (RHS sequents)
```

A full sequent is a structure of the form `Φ, Ψ`; "associativity and commutativity of the comma
`,` is implicit in [the] systems, and `∅` acts as its unit" (source, directly below eq. (2.1)).
This definition entails that exactly one formula in a full sequent has output polarity.

## Two Ordinary Inductives, Not a Lean `mutual` Block

`Ψ`'s production `[Φ, Ψ]` depends on `Φ`, but `Φ`'s productions never mention `Ψ`. So
`NestedLhs`/`NestedRhs` below are two ordinary (successively-declared) inductives, not a genuine
Lean `mutual` block, despite the source presenting the grammar as a simultaneous BNF pair.

## Comma Treatment

`Φ, Φ` is encoded as the explicit binary constructor `NestedLhs.comma`, not as a `List` or a
quotient by associativity/commutativity/unit. Where the calculus needs two comma-permuted
sequents to be treated as interchangeable, that is supplied by explicit lemmas at the point of
use (mirroring how `Deriv`'s `List` contexts are handled elsewhere in the modal library, e.g.
`weakening_deriv`'s explicit `∀ x ∈ Γ, x ∈ Δ` side condition rather than a `Γ ≈ Δ` quotient) --
not landed speculatively in this module, since no downstream phase yet consumes them. -/

@[expose] public section

namespace Cslib.Logic.Modal

universe u
variable {Atom : Type u}

/-! ## The Nested Sequent Types -/

/-- LHS (input-tagged) nested sequent structures, `Φ` in eq. (2.1): `Φ ::= ∅ | A• | [Φ] | Φ, Φ`.
`dia` is the `[Φ]` diamond-tagged bracket (no output formula inside, hence purely `NestedLhs`
recursive); `comma` is the explicit binary comma constructor (see the module docstring's "Comma
Treatment" note). -/
inductive NestedLhs (Atom : Type u) : Type u where
  /-- `∅`: the empty LHS sequent. -/
  | empty : NestedLhs Atom
  /-- `A•`: an input-tagged formula leaf. -/
  | atom (φ : Proposition Atom) : NestedLhs Atom
  /-- `[Φ]`: the diamond-tagged bracket. -/
  | dia (Φ : NestedLhs Atom) : NestedLhs Atom
  /-- `Φ, Φ`: comma concatenation. -/
  | comma (Φ₁ Φ₂ : NestedLhs Atom) : NestedLhs Atom
  deriving DecidableEq

/-- RHS (output-tagged) nested sequent structures, `Ψ` in eq. (2.1): `Ψ ::= A◦ | [Φ, Ψ]`. `box`
is the `[Φ, Ψ]` box-tagged bracket, pairing an `NestedLhs` context with a nested `NestedRhs`. By
construction every `NestedRhs` term has exactly one output (`atom`) leaf, so the "exactly one
output formula in a full sequent" invariant of eq. (2.1) holds definitionally rather than as a
separately-proved well-formedness side condition. -/
inductive NestedRhs (Atom : Type u) : Type u where
  /-- `A◦`: the unique output-tagged formula leaf. -/
  | atom (φ : Proposition Atom) : NestedRhs Atom
  /-- `[Φ, Ψ]`: the box-tagged bracket. -/
  | box (Φ : NestedLhs Atom) (Ψ : NestedRhs Atom) : NestedRhs Atom
  deriving DecidableEq

/-- A full sequent, `Φ, Ψ` in the source: an `NestedLhs` context paired with the unique
`NestedRhs` output. Encoded as a genuine product (not a separate inductive), since `NestedRhs`
already carries the "exactly one output" invariant by construction. -/
abbrev NestedFull (Atom : Type u) : Type u := NestedLhs Atom × NestedRhs Atom

/-! ## The `fm` Translation -/

/-- The corresponding-formula translation `fm` on LHS contexts: `fm(∅) = ⊤`, `fm(A•) = A`,
`fm([Φ]) = ◇fm(Φ)`, `fm(Φ₁, Φ₂) = fm(Φ₁) ∧ fm(Φ₂)`. -/
def NestedLhs.fm : NestedLhs Atom → Proposition Atom
  | .empty => Proposition.top
  | .atom φ => φ
  | .dia Φ => ◇(Φ.fm)
  | .comma Φ₁ Φ₂ => Φ₁.fm.and Φ₂.fm

/-- The corresponding-formula translation `fm` on RHS contexts: `fm(A◦) = A`,
`fm([Φ, Ψ]) = □(fm(Φ) ⊃ fm(Ψ))` (the box clause composed with the full-sequent clause
`fm(Φ, Ψ) = fm(Φ) ⊃ fm(Ψ)`, inlined here since `[Φ, Ψ]` is the only place a full sequent
appears nested inside a `NestedRhs`). -/
def NestedRhs.fm : NestedRhs Atom → Proposition Atom
  | .atom φ => φ
  | .box Φ Ψ => Proposition.box (Φ.fm.imp Ψ.fm)

/-- The corresponding-formula translation on a full sequent: `fm(Φ, Ψ) = fm(Φ) ⊃ fm(Ψ)`. -/
def NestedFull.fm (ΦΨ : NestedFull Atom) : Proposition Atom := ΦΨ.1.fm.imp ΦΨ.2.fm

/-! ## Example 2.1 (source, §2)

The source builds `Γ₁{Δ₁}` and `Γ₂{Δ₂}` as full sequents, and observes that the *other* pairing
(`Γ₁{Δ₂}`, `Γ₂{Δ₁}`) is not well-formed: the former would carry no output formula, the latter
two. This module has not yet built the generic "context with a hole" apparatus (`Γ{ }`,
Observation 2.2 -- the next module in this directory), so the well-formed pairing is exhibited
directly as concrete `NestedFull` terms (below), and the ill-formed pairing is exhibited as a
type-level impossibility (see the comment after). -/

/-- `Γ₁{Δ₁} = C•, [A•, [B◦], [B•, C•]]` (source notation), built directly. -/
example (A B C : Proposition Atom) : NestedFull Atom :=
  (.atom C,
    .box (.comma (.atom A) (.dia (.comma (.atom B) (.atom C))))
      (.box .empty (.atom B)))

/-- `fm(Γ₁{Δ₁}) = C ⊃ □((A ∧ ◇(B ∧ C)) ⊃ □(⊤ ⊃ B))`, computed mechanically from the `fm`
clauses above. The source's prose rendering of this example (§2) informally simplifies the
innermost `□(⊤ ⊃ B)` to `□B` (equivalently: it treats `⊤ ⊃ B` and `B` as interchangeable, a valid
propositional identity but not one the `fm` clauses themselves perform) -- confirmed by
cross-checking both a direct PDF render and a `pdftotext -layout` extraction of the same page,
neither of which shows a `⊤` character or an un-parenthesized `⊃` at that position. The `rfl`
below computes the literal, unsimplified `fm` output; the mechanical result is definitionally
what the stated clauses give, not the source's simplified prose gloss on it. -/
example (A B C : Proposition Atom) :
    NestedFull.fm
      ((.atom C,
        .box (.comma (.atom A) (.dia (.comma (.atom B) (.atom C))))
          (.box .empty (.atom B))) : NestedFull Atom) =
    C.imp (.box (((A.and (◇(B.and C))).imp (.box (Proposition.top.imp B))))) := rfl

/-- `Γ₂{Δ₂} = C•, [A•, [B•], [B•, C◦]]` (source notation), built directly. -/
example (A B C : Proposition Atom) : NestedFull Atom :=
  (.atom C, .box (.comma (.atom A) (.dia (.atom B))) (.box (.atom B) (.atom C)))

/-- `fm(Γ₂{Δ₂}) = C ⊃ □((A ∧ ◇B) ⊃ □(B ⊃ C))`, matching the source exactly once the `□` glyphs
(dropped by `pdftotext` in the raw extraction of this example, confirmed present in the direct
PDF render) are restored. -/
example (A B C : Proposition Atom) :
    NestedFull.fm
      ((.atom C, .box (.comma (.atom A) (.dia (.atom B))) (.box (.atom B) (.atom C))) :
        NestedFull Atom) =
    C.imp (.box ((A.and (◇B)).imp (.box (B.imp C)))) := rfl

/-! ### The Ill-Formed Pairing Is Not Expressible

`Γ₁{Δ₂}` would need content `A•, [B•], [B•, C•]` at the box position -- every summand is
`NestedLhs`-typed (no `atom`-output leaf anywhere), so there is no candidate `Ψ : NestedRhs`
to supply as `NestedRhs.box`'s second argument. `Γ₂{Δ₁}` would need content `A•, [B◦], [B•, C◦]`
-- *two* summands (`[B◦]` and `[B•, C◦]`) are themselves `NestedRhs`-typed, and `NestedLhs` has
no constructor accepting a `NestedRhs` argument, so at most one of the two can ever be placed;
the other has no well-typed home. Both failures are structural (a type error), not a side
condition to prove:

```
-- Γ₁{Δ₂}: no NestedRhs summand exists to supply as the box's second argument.
-- example (A B C : Proposition Atom) : NestedFull Atom :=
--   (.atom C,
--     .box (.comma (.atom A) (.comma (.dia (.atom B)) (.dia (.comma (.atom B) (.atom C))))) ?)
-- Γ₂{Δ₁}: both `.box .empty (.atom B)` and `.box (.atom B) (.atom C)` are `NestedRhs`, and
-- `NestedLhs` has no constructor that accepts a `NestedRhs` argument, so one of the two cannot
-- be placed anywhere in the term.
```
-/

end Cslib.Logic.Modal
