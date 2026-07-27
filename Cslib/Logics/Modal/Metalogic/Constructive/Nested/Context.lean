/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.Nested.Syntax

/-! # Nested Sequent Contexts: Hole Filling and Output Pruning

This module encodes Arisaka–Das–Straßburger's context apparatus (`doc_id:
arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`, §2, Observation 2.2 and
Definition 2.3), following `Nested/Syntax.lean`'s `NestedLhs`/`NestedRhs`/`NestedFull` encoding
of eq. (2.1) and its `fm` translation. Verified against the recovered source PDF (cross-checked
via both direct rendering and `pdftotext -layout`, page 5).

## Output Contexts (eq. (2.2))

Observation 2.2: "Every output context `Γ{ }` is of the shape `Γ•₁, [Γ•₂, […, [Γ•ₙ, { }] …]]` for
some `n ≥ 0`." This is encoded as `OutputCtx Atom := List (NestedLhs Atom)`, read outer-to-inner
(`Γ₁` first, the hole innermost); well-formedness of the shape is then definitional (no separate
side condition), matching this file's design choice for `NestedLhs`/`NestedRhs`.

Four filler operations are defined, matching the source's stated typing (Observation 2.2: "Filling
the hole of an output context with a RHS or full sequent yields a full sequent, and filling it
with a LHS sequent yields a LHS sequent") plus the separately-introduced `∅`-filling ("We can
choose to fill the hole of a context `Γ{ }` with nothing, denoted `Γ{∅}`, which means we simply
remove the occurrence of `{ }`"). **`fillEmpty` is not the special case `fillLhs · ∅`**: removing
the hole collapses one nesting level entirely, whereas substituting the LHS value `∅` for the hole
leaves that level's comma/diamond structure in place (verified: for a two-layer context
`[Γ₁, Γ₂]`, `fillEmpty` gives `Γ₁, [Γ₂]` but `fillLhs · ∅` gives `Γ₁, [Γ₂, ∅]` — these are
different `NestedLhs` terms, not merely different presentations of the same one, since `,` is a
raw non-quotiented constructor here per `Syntax.lean`'s "Comma Treatment" design note). Both
operations are landed as separate primitives, exactly as the source presents them.

## Input Contexts (eq. (2.3))

Observation 2.2 continues: "Every input context `Γ{ }` is of the shape `Γ'{Λ{ }, Π◦}` where
`Γ'{ }` and `Λ{ }` are output contexts... Note that `Γ'{ }` and `Λ{ }` and `Π` are uniquely
determined by the position of the hole `{ }` in `Γ{ }`."

**Deviation from the plan's `Π : Proposition` sketch**: this module types `Π : NestedRhs Atom`,
not `Proposition`. The source's own notational convention (§2, directly below eq. (2.1)) draws an
explicit distinction: *italic roman* letters with a superscript (`A•`, `A◦`) denote atomic
*formulas*, while *capital Greek* letters with a superscript (`Γ•`, `Δ◦`, `Π◦`, …) denote
*arbitrary sequents* of that polarity — "We use capital Greek letters `Γ, ∆, Σ, …` to denote
arbitrary sequents, LHS, RHS or full, and may decorate them with a `•` or `◦` superscript to
indicate that they are LHS or RHS, respectively." `Π` is Greek, so `Π◦` denotes an arbitrary RHS
*sequent*, not necessarily an atomic formula. This is forced, not a stylistic choice: Example
2.1's `Γ₂{ } = C•, [{ }, [B•, C◦]]` is explicitly named an input context by the source itself
("Γ2{∅} = C•,[[B•,C◦]] is a full sequent... whenever `Γ{∅}` is a full sequent, then `Γ{ }` is an
input context"), and decomposing it per eq. (2.3) forces `Γ' = [C]`, `Λ = []` (the hole sits
directly at the outer box's LHS slot, with nothing further nested), and therefore
`Π = [B•, C◦] = box(B, C)` — a genuinely compound `NestedRhs` term, not a bare atom. Typing `Π`
as `Proposition` would make this cited example (which `Nested/Rules.lean`'s own verification
criterion requires to be expressible) inexpressible.

(The Lean field itself is spelled `π`, lowercase, not `Π`: Mathlib's `Delaborators.lean` binds
capital `Π` as a delaborator token for Pi-types, which makes it unusable as a plain identifier —
confirmed by a parse failure when first attempted. Lowercase `π` has only `scoped`/`local`
notations elsewhere in Mathlib (e.g. `Real.pi`), none open in this file, so it is safe here.)

Verified: the resulting `InputCtx.fillEmpty` and
`InputCtx.fillLhs` computations below reproduce Example 2.1's `Γ2{∅}` and (independently) this
file's already-`rfl`-verified `Γ2{Δ2}` term exactly (see the examples at the end of this
file), which is strong corroborating evidence the decomposition is right.

## Output Pruning (Definition 2.3)

"For every input context `Γ{ } = Γ'{Λ{ }, Π◦}`, we define its *output pruning* `Γ⇓{ }` to be the
context `Γ'{Λ{ }}`... Thus, `Γ⇓{ }` is an output context." Since both `Γ'{ }` and `Λ{ }` are
output contexts (`List`s of `NestedLhs` layers) and `Γ'{Λ{ }}` substitutes `Λ{ }`'s own
(still-open) template directly into `Γ'{ }`'s hole, the naive reading is list append, `Γ' ++ Λ`.
**This naive reading is off by one nesting level when `Λ = []`**: `InputCtx.fillLhs` (below)
unconditionally wraps its hole-filling in one `.box` regardless of `Λ`'s length
(`.box (ctx.Λ.fillLhs Δ) ctx.π`), but plain `Γ' ++ []` contributes zero layers at that position —
concretely, `impL`'s premise 1 (`Nested/Rules.lean`) and its conclusion (via `fillLhs`) then
disagree about how many `□`s separate `Γ'` from the hole, making `nested_sound_impL` false as
stated (counterexample: `ctx = ⟨[C•], [], P°⟩`, `C := A`, `B := ⊥`; both premises derivable, the
conclusion `A ⊃ □((A ⊃ ⊥) ⊃ P)` fails in a 2-world classical S5 model). The correct definition is
`Γ' ++ (Λ.headD ∅ :: Λ.tail)`: the identity on non-empty `Λ` (retaining `Λ`'s own first layer
unchanged), and `Γ' ++ [∅]` on `Λ = []` — inserting exactly the one retained box layer `fillLhs`
always supplies, keeping the hole where `Γ{ }` had it (Observation 2.2's `Γ'{Λ{ }}`) rather than
collapsing it away. Verified against Example 2.1's `Γ2{ }` (`Γ' = [C]`, `Λ = []`, so
`Γ2⇓{ } = [C] ++ [∅] = [C, ∅]`), reproducing the source's own two-layer `[C•, ∅]` decomposition —
"same context with the `Π`-branch removed", *not* collapsed to a single layer.

## Basic Equational Lemmas

`buildRhsChain_append` (chain-building distributes over list append) and the derived
`OutputCtx.fillRhs_append` are landed, since they are both simple to state/prove now and are
exactly the "nesting/associativity of filling" facts the plan calls for. The further relationship
between `(Γ⇓){∆}` and `Γ{∆}` in general is **deferred to the `fm`-compositionality-over-contexts
development**: the natural candidate equations (e.g. relating `ctx.outputPruning.fillRhs ctx.π` to
`ctx.fillEmpty`) do not hold as bare structural equalities — they differ by exactly the
`box ∅ ·`-vs-direct-substitution distinction documented above for `fillEmpty` — and that
development is where the `fm`-level (rather than raw-term) compositionality apparatus needed to
state the correct relationship is built. Landing a mis-stated placeholder lemma now would be worse
than deferring.
-/

@[expose] public section

namespace Cslib.Logic.Modal

universe u
variable {Atom : Type u}

/-! ## Output Contexts (Observation 2.2, eq. (2.2)) -/

/-- An output context `Γ{ }`, in Observation 2.2 normal form: the list `[Γ₁, …, Γₙ]` represents
`Γ•₁, [Γ•₂, […, [Γ•ₙ, { }] …]]`, read outer-to-inner with the hole innermost. `n = 0` is the
trivial/identity context `{ }`. -/
abbrev OutputCtx (Atom : Type u) : Type u := List (NestedLhs Atom)

/-- Fill an output context's hole with nothing (`Γ{∅}`): removes the occurrence of `{ }`,
collapsing the innermost level rather than substituting a value for it (see the module docstring
for why this differs from `fillLhs · NestedLhs.empty`). Result: a `NestedLhs` sequent, matching
`Γ1{∅} = C•,[[B•,C•]]` (Example 2.1) being a LHS sequent. -/
def OutputCtx.fillEmpty : OutputCtx Atom → NestedLhs Atom
  | [] => .empty
  | [Γ] => Γ
  | Γ :: (Γ₂ :: rest) => .comma Γ (.dia (OutputCtx.fillEmpty (Γ₂ :: rest)))

/-- Fill an output context's hole with a LHS sequent `Δ`, yielding a LHS sequent (Observation
2.2: "filling it with a LHS sequent yields a LHS sequent"). -/
def OutputCtx.fillLhs : OutputCtx Atom → NestedLhs Atom → NestedLhs Atom
  | [], Δ => Δ
  | [Γ], Δ => .comma Γ Δ
  | Γ :: (Γ₂ :: rest), Δ => .comma Γ (.dia (OutputCtx.fillLhs (Γ₂ :: rest) Δ))

/-- Build the nested box chain `[Γ₁, [Γ₂, […, [Γₙ, Ψ] …]]]` from a list of LHS layers, ending in
a fixed RHS filler `Ψ`. The recursive engine behind `OutputCtx.fillRhs`. -/
def buildRhsChain : List (NestedLhs Atom) → NestedRhs Atom → NestedRhs Atom
  | [], Ψ => Ψ
  | Γ :: rest, Ψ => .box Γ (buildRhsChain rest Ψ)

/-- Fill an output context's hole with a RHS sequent `Ψ`, yielding a full sequent (Observation
2.2: "filling the hole of an output context with a RHS... sequent yields a full sequent"). The
`n = 0` case (`Γ{ } = { }`) uses `∅` as the implicit LHS part, giving `(∅, Ψ)`. -/
def OutputCtx.fillRhs : OutputCtx Atom → NestedRhs Atom → NestedFull Atom
  | [], Ψ => (.empty, Ψ)
  | Γ :: rest, Ψ => (Γ, buildRhsChain rest Ψ)

/-- Build the nested box chain ending in a full-sequent filler `(Φ, Ψ)`, merging `Φ` (via comma,
using the source's assumed associativity/commutativity of `,`) into the deepest LHS layer and
placing `Ψ` as that box's output. The recursive engine behind `OutputCtx.fillFull`; verified to
reproduce this file's `Γ1{Δ1}` term exactly (see the examples below). -/
def buildFullChain : List (NestedLhs Atom) → NestedFull Atom → NestedRhs Atom
  | [], (Φ, Ψ) => .box Φ Ψ
  | [Γ], (Φ, Ψ) => .box (.comma Φ Γ) Ψ
  | Γ :: (Γ₂ :: rest), ΦΨ => .box Γ (buildFullChain (Γ₂ :: rest) ΦΨ)

/-- Fill an output context's hole with a full sequent `(Φ, Ψ)`, yielding a full sequent
(Observation 2.2: "filling the hole of an output context with... a full sequent yields a full
sequent"). -/
def OutputCtx.fillFull : OutputCtx Atom → NestedFull Atom → NestedFull Atom
  | [], ΦΨ => ΦΨ
  | [Γ], (Φ, Ψ) => (.comma Φ Γ, Ψ)
  | Γ :: (Γ₂ :: rest), ΦΨ => (Γ, buildFullChain (Γ₂ :: rest) ΦΨ)

/-! ## Input Contexts (Observation 2.2, eq. (2.3)) -/

/-- An input context `Γ{ } = Γ'{Λ{ }, Π◦}`: `Γ'` and `Λ` are output contexts (eq. (2.2)-shaped),
and `Π` is the fixed RHS sequent occupying the position of "the unique output formula" (Definition
2.3) once the hole (nested inside `Λ`) is filled with something LHS-typed. See the module
docstring for why `Π : NestedRhs Atom`, not `Proposition`. -/
structure InputCtx (Atom : Type u) : Type u where
  /-- The outer output-context shell, `Γ'{ }` in eq. (2.3). -/
  Γ' : OutputCtx Atom
  /-- The inner output-context shell carrying the actual hole, `Λ{ }` in eq. (2.3). -/
  Λ : OutputCtx Atom
  /-- The fixed RHS sequent at the "unique output formula" position, `Π◦` in eq. (2.3). Spelled
  `π` (lowercase) rather than `Π`: see the module docstring for why. -/
  π : NestedRhs Atom

/-- Fill an input context's hole with a LHS sequent `Δ`, yielding a full sequent (the defining
property of an input context, from the introductory paragraph preceding Example 2.1: "an input
context [yields a full sequent] ... for a LHS sequent [filler]"). -/
def InputCtx.fillLhs (ctx : InputCtx Atom) (Δ : NestedLhs Atom) : NestedFull Atom :=
  ctx.Γ'.fillRhs (.box (ctx.Λ.fillLhs Δ) ctx.π)

/-- Fill an input context's hole with nothing (`Γ{∅}`), yielding a full sequent whenever `Γ{∅}`
is well-formed (Observation 2.2's remark: "whenever `Γ{∅}` is a full sequent, then `Γ{ }` is an
input context"). Verified against Example 2.1's `Γ2{∅} = C•,[[B•,C◦]]` below. -/
def InputCtx.fillEmpty (ctx : InputCtx Atom) : NestedFull Atom :=
  ctx.Γ'.fillRhs (.box ctx.Λ.fillEmpty ctx.π)

/-! ## Output Pruning (Definition 2.3) -/

/-- The output pruning `Γ⇓{ }` of an input context: "the same context with the subtree containing
the unique output formula and sharing the same root as `{ }` removed", i.e. `Γ'{Λ{ }}` with `Π`
dropped, keeping the hole exactly where `Γ{ }` had it. `headD ∅ :: tail` is the identity on
non-empty `Λ` (both are the eq. (2.2)-shaped list `Λ` itself), so this reduces to the naive
`Γ' ++ Λ` append whenever `Λ ≠ []`. On `Λ = []` it instead yields `Γ' ++ [∅]`: a single retained
`∅`-layer standing in for the vanished `Λ{ }`, which is exactly the one `.box` layer
`InputCtx.fillLhs` unconditionally supplies at this position (`.box (ctx.Λ.fillLhs Δ) ctx.π`)
regardless of `Λ`'s length. Dropping that layer (the naive `Γ' ++ []= Γ'` reading) makes
`nested_sound_impL`'s premise 1 one `□` shallower than its conclusion demands — see the module
docstring's counterexample. This reproduces the source's own `[C•, ∅]` two-layer decomposition of
Example 2.1's `Γ₂⇓{ }`. -/
def InputCtx.outputPruning (ctx : InputCtx Atom) : OutputCtx Atom :=
  ctx.Γ' ++ (ctx.Λ.headD NestedLhs.empty :: ctx.Λ.tail)

/-! ## Basic Equational Lemmas -/

/-- Chain-building distributes over list append: filling the box chain for `l1 ++ l2` ending in
`Ψ` is the same as filling `l1`'s chain ending in `l2`'s chain ending in `Ψ`. The
"nesting/associativity of filling" fact underlying `OutputCtx.outputPruning`'s correctness. -/
theorem buildRhsChain_append (l1 l2 : List (NestedLhs Atom)) (Ψ : NestedRhs Atom) :
    buildRhsChain (l1 ++ l2) Ψ = buildRhsChain l1 (buildRhsChain l2 Ψ) := by
  induction l1 with
  | nil => rfl
  | cons Γ rest ih => simp [buildRhsChain, ih]

/-- `OutputCtx.fillRhs` distributes over list append at a nonempty first list: filling the
combined context `(Γ :: rest) ++ l2` with `Ψ` is the same as filling `Γ :: rest` with `l2`'s chain
ending in `Ψ`. -/
theorem OutputCtx.fillRhs_append (Γ : NestedLhs Atom) (rest l2 : List (NestedLhs Atom))
    (Ψ : NestedRhs Atom) :
    OutputCtx.fillRhs ((Γ :: rest) ++ l2) Ψ =
      OutputCtx.fillRhs (Γ :: rest) (buildRhsChain l2 Ψ) := by
  simp [OutputCtx.fillRhs, buildRhsChain_append]

/-! ## Example 2.1, Revisited via the Generic Context Apparatus -/

/-- `Γ₁{ } = C•, [{ }, [B•, C•]]` (Example 2.1), as an `OutputCtx`: using the source's assumed
commutativity of `,` to read `[{ }, [B•, C•]]` as `[[B•, C•], { }]`, this is the two-layer list
`[C•, [B•, C•]]`. -/
def γ₁Ctx (B C : Proposition Atom) : OutputCtx Atom :=
  [.atom C, .dia (.comma (.atom B) (.atom C))]

/-- `Γ1{∅} = C•,[[B•,C•]]` (Example 2.1, Observation 2.2 discussion), computed via the generic
`OutputCtx.fillEmpty`. -/
example (B C : Proposition Atom) :
    (γ₁Ctx B C).fillEmpty =
      (.comma (.atom C) (.dia (.dia (.comma (.atom B) (.atom C)))) : NestedLhs Atom) := rfl

/-- `Γ1{Δ1} = C•,[A•,[B◦],[B•,C•]]` (Example 2.1), computed via the generic `OutputCtx.fillFull`
from `γ₁Ctx` and `Δ1 = A•,[B◦]`. Reproduces this file's independently-landed, `rfl`-
verified concrete term exactly, cross-validating both constructions. -/
example (A B C : Proposition Atom) :
    (γ₁Ctx B C).fillFull (.atom A, .box .empty (.atom B)) =
      ((.atom C,
        .box (.comma (.atom A) (.dia (.comma (.atom B) (.atom C))))
          (.box .empty (.atom B))) : NestedFull Atom) := rfl

/-- `Γ₂{ } = C•, [{ }, [B•, C◦]]` (Example 2.1), as an `InputCtx`: the hole sits directly at the
outer box's LHS slot (`Γ' = [C•]`, `Λ = []`), with `[B•, C◦]` fixed as `Π`. See the module
docstring for why this forces `Π : NestedRhs Atom` rather than a bare formula. -/
def γ₂Ctx (B C : Proposition Atom) : InputCtx Atom :=
  ⟨[.atom C], [], .box (.atom B) (.atom C)⟩

/-- `Γ2{∅} = C•,[[B•,C◦]]` (Example 2.1, Observation 2.2 discussion), computed via the generic
`InputCtx.fillEmpty`. -/
example (B C : Proposition Atom) :
    (γ₂Ctx B C).fillEmpty =
      ((.atom C, .box .empty (.box (.atom B) (.atom C))) : NestedFull Atom) := rfl

/-- `Γ2{Δ2} = C•,[A•,[B•],[B•,C◦]]` (Example 2.1), computed via the generic `InputCtx.fillLhs`
from `γ₂Ctx` and `Δ2 = A•,[B•]`. Reproduces this file's independently-landed, `rfl`-
verified concrete term exactly. -/
example (A B C : Proposition Atom) :
    (γ₂Ctx B C).fillLhs (.comma (.atom A) (.dia (.atom B))) =
      ((.atom C,
        .box (.comma (.atom A) (.dia (.atom B))) (.box (.atom B) (.atom C))) : NestedFull Atom) :=
  rfl

/-- `Γ1{∆2}` (Example 2.1) is not a well-formed full sequent: filling the *output* context `γ₁Ctx`
with the *LHS* sequent `Δ2` yields a LHS sequent (Observation 2.2), matching the source's "would
contain no output formula". -/
example (A B C : Proposition Atom) :
    (γ₁Ctx B C).fillLhs (.comma (.atom A) (.dia (.atom B))) =
      (.comma (.atom C) (.dia (.comma (.dia (.comma (.atom B) (.atom C)))
        (.comma (.atom A) (.dia (.atom B))))) : NestedLhs Atom) := rfl

/-! ### `Γ2{∆1}` Is Not Expressible Through `InputCtx.fillLhs`

The source's other ill-formed pairing, `Γ2{∆1}` ("would contain two [output formulas]"), is not
landed as an `example` here: `InputCtx.fillLhs` only accepts a bare LHS filler, and `Δ1 = A•,
[B◦]` is itself a full sequent (already carrying an output formula, `B`), so plugging it into
`γ₂Ctx`'s hole is a type error against `InputCtx.fillLhs`'s signature, not a value this module's
API can even construct -- exactly the ill-typedness the source is pointing at. This mirrors
`Syntax.lean`'s "Ill-Formed Pairing Is Not Expressible" section: the failure is structural, caught
by Lean's elaborator, not a side condition to prove. -/

end Cslib.Logic.Modal
