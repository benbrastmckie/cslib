# PR Description: feat(Logics/Propositional): five-primitive formula type with connective typeclasses

## Title

`feat(Logics/Propositional): five-primitive formula type with connective typeclasses`

## Summary

This PR refactors the propositional logic foundations with three changes:

1. **New file `Cslib/Foundations/Logic/Connectives.lean`**: Introduces a typeclass hierarchy
   for propositional connectives — `HasBot`, `HasImp`, `HasAnd`, `HasOr` (atomic classes) and
   `PropositionalConnectives` (bundled class extending `HasBot` and `HasImp`). This enables
   polymorphic axiom definitions that work across any formula type providing these connectives.

2. **Refactored `Cslib/Logics/Propositional/Defs.lean`**: The `Proposition` type now uses
   five primitives `{atom, bot, imp, and, or}` instead of four `{atom, and, or, impl}`.
   Key changes:
   - Added `bot` as a primitive constructor (previously simulated via `[Bot Atom]` constraint)
   - Renamed `impl` to `imp` (matching CSLib's existing convention in Bimodal and Temporal
     formula types, and aligning constructor names with rule name prefixes: `impI`/`impE`)
   - Negation `¬A := A → ⊥` and verum `⊤ := ⊥ → ⊥` are now constraint-free derived connectives
   - Added biconditional `↔` as a derived connective
   - Registered `PropositionalConnectives`, `HasAnd`, `HasOr` instances

3. **Updated `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`**: Adapted to the new
   `Proposition` signature:
   - Renamed `implI`/`implE` to `impI`/`impE`
   - Renamed `andE₁`/`andE₂`/`orI₁`/`orI₂` to ASCII-safe `andE1`/`andE2`/`orI1`/`orI2`
   - Removed `[Inhabited Atom]` constraints from `derivationTop`, `derivableIn_top`,
     `derivable_iff_equiv_top` (now constraint-free with primitive `bot`)

## Why `bot` Should Be Primitive

The `[Bot Atom]` approach embedded ⊥ as a special atom (`.atom ⊥`). This has three concrete
defects:

1. **Substitution breaks `⊥`**: `Proposition.subst f` replaces all atoms, including the
   "bottom atom" — `(.atom ⊥).subst f = f ⊥`. Substitution should preserve `⊥`; with
   primitive `bot` it does so by construction.
2. **`⊤` depends on an arbitrary `Inhabited` instance**: The previous `Proposition.top` was
   `impl (.atom default) (.atom default)` — i.e., `a → a` for an arbitrary atom, not the
   standard `⊥ → ⊥`. Different `Inhabited` instances give definitionally different `⊤` terms.
3. **`Bot Atom` conflates logical bottom with atomic data**: `neg`, `top`, `IPL`,
   `IsIntuitionistic`, `IsClassical` all required `[Bot Atom]` constraints, making definitions
   needlessly complex.

With primitive `bot`, all derived connectives (`neg`, `top`, `iff`) and logic definitions
(`IPL`, `IsIntuitionistic`, `IsClassical`) are constraint-free. The five-primitive signature
`{atom, bot, imp, and, or}` is the standard one for intuitionistic and minimal logic in
[TroelstraVanDalen1988] Chapter 2. Primitive `⊥` is required for Johansson's minimal logic
[Johansson1937], which defines negation `¬A := A → ⊥` using `⊥` as an undefined primitive
symbol ("undefiniertes Grundzeichen").

## Naming: `imp` vs `impl`

The name `imp` is used for consistency with CSLib's existing formula types (e.g., Bimodal and
Temporal), where `imp` is the constructor name for implication. It also aligns constructor
names with natural deduction rule name prefixes (`impI`/`impE`, cf. `andI`/`andE1`).

## Zulip Discussion

See [CSLib > Propositional Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/with/603087026) for the motivation discussion around making `bot` primitive.

## Relationship to Other PRs

### PR #607

PR #607 by @fmontesi introduces per-operator typeclass files under `Operators/`, covering both
propositional and modal connectives. Our `Connectives.lean` overlaps in the propositional case
(`HasBot`, `HasImp`, `HasAnd`, `HasOr`). If PR #607 merges first, we can align our definitions
with its typeclass names and file structure; if ours merges first, #607 can import from
`Connectives.lean` for the propositional operators. I am happy to coordinate on the final
structure.

### PR #536

PR #536 by @thomaskwaring refactors `IsClassical` and `IsIntuitionistic` to refer to inference
systems. Both PRs modify `Defs.lean` and `NaturalDeduction/Basic.lean`. The changes are
conceptually independent — #536 restructures inference system predicates while this PR changes
the primitive connective set.

### PR #587

PR #587 by @thomaskwaring proposes model and semantics typeclasses and also modifies
`Connectives.lean`. We should coordinate to avoid conflicting changes to this file.

### Mathlib `Bot`/`HImp` Classes

Mathlib defines `Bot` (`Mathlib.Order.Notation`) and `HImp` (`Mathlib.Order.Notation`) as
pure notation classes with no order-theoretic requirements. We use a uniform `Has*` naming
convention (`HasBot`, `HasImp`, `HasAnd`, `HasOr`) for the generic polymorphic layer, where
these classes parameterize proof system infrastructure (`ProofSystem.lean`, `Consistency.lean`,
`BigConj.lean`). A bridge instance `[HasBot F] : Bot F` in `Connectives.lean` provides
Mathlib's `⊥` notation to any type with `HasBot`, so concrete formula code can use `⊥`
directly. We kept `HasImp` rather than Mathlib's `HImp` because `HImp` uses the field name
`himp` and notation `⇨`, which differ from CSLib's `imp`/`→` convention across all four
formula types.

## Contribution Roadmap

This PR is the first in a planned series contributing our propositional logic foundations upstream:

1. **This PR**: Connective typeclasses + five-primitive formula type + natural deduction update
2. **PR 2**: Hilbert proof system (`ProofSystem/`) with minimal/intuitionistic/classical axiom
   predicates and sequent derivability
3. **PR 3**: ND-Hilbert equivalence for all three logic strengths
4. **PR 4**: Semantics (valuation-based, Kripke frames) with soundness
5. **PR 5**: Completeness for CPL (truth table argument)
6. **PR 6**: Completeness for IPL (canonical model construction)

The planned roadmap draws from the development in Troelstra & van Dalen [TroelstraVanDalen1988]
Chapter 2, with PR 5-6 following the completeness proof strategy there.

## Changed Files

- [`Cslib/Foundations/Logic/Connectives.lean`](Cslib/Foundations/Logic/Connectives.lean) — **New**: connective typeclass hierarchy (`HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`)
- [`Cslib/Logics/Propositional/Defs.lean`](Cslib/Logics/Propositional/Defs.lean) — **Modified**: five-primitive `Proposition` type, constraint-free derived connectives, typeclass instances
- [`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`](Cslib/Logics/Propositional/NaturalDeduction/Basic.lean) — **Modified**: renamed constructors (`impl`→`imp`, subscript→ASCII), removed type constraints
- [`Cslib.lean`](Cslib.lean) — **Modified**: added `Connectives` import

## Breaking Changes

- `Proposition.impl` renamed to `Proposition.imp`
- `andE₁`/`andE₂`/`orI₁`/`orI₂` renamed to `andE1`/`andE2`/`orI1`/`orI2`
- `[Bot Atom]` constraints removed from `IPL`, `IsIntuitionistic`, `IsClassical`, and
  related instances and theorems
- `[Inhabited Atom]` constraint removed from `Proposition.top`, `derivationTop`,
  `derivableIn_top`, `derivable_iff_equiv_top`
- `instBotProposition` and `instInhabitedOfBot` removed; new constraint-free instances added

Files affected upstream: `Defs.lean`, `NaturalDeduction/Basic.lean` (only consumers)

## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and extracting files from a development branch to create a clean PR branch
- Running CI verification commands
- Literature verification and citation checking

The mathematical content, proof architecture, and design decisions were verified by the author.
All Lean code compiles with no sorries.
