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
   - Renamed `impl` to `imp` (standard notation per Gentzen/Prawitz)
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
(`IPL`, `IsIntuitionistic`, `IsClassical`) are constraint-free. The choice of primitive
connectives for propositional logic is discussed in [Church1956] §24; the five-primitive
signature with `⊥` is the standard one for intuitionistic and minimal logic in
[TroelstraVanDalen1988] Chapter 2. Primitive `⊥` is required for Johansson's minimal logic
[Johansson1937], which defines negation `¬A := A → ⊥` using `⊥` as an undefined primitive
symbol ("undefiniertes Grundzeichen").

## Naming: `imp` vs `impl`

The name `imp` is standard in Lean formalization practice (e.g., Lean's own `Prop` operations
and modal logic formalizations). The previous `impl` was non-standard — no major proof theory
reference uses this abbreviation for implication.

## Zulip Discussion

See [CSLib > Propositional Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/with/603087026) for the motivation discussion around making `bot` primitive.

## Relationship to PR #607

PR #607 by @fmontesi introduces `HasAnd`/`HasOr` typeclasses. Our `Connectives.lean` follows
the same operator-typeclass approach and is compatible: we define `HasBot`, `HasImp`, `HasAnd`,
`HasOr` as atomic classes and `PropositionalConnectives` as a bundled class. Our PR is a
superset of PR #607 for the propositional case, while PR #607 focuses on conjunctive/disjunctive
operators. If PR #607 merges first, our `Connectives.lean` can absorb its definitions.

## Contribution Roadmap

This PR is the first in a planned series contributing our propositional logic foundations upstream:

1. **This PR**: Connective typeclasses + five-primitive formula type + natural deduction update
2. **PR 2**: Hilbert proof system (`ProofSystem/`) with minimal/intuitionistic/classical axiom
   predicates and sequent derivability
3. **PR 3**: ND-Hilbert equivalence for all three logic strengths
4. **PR 4**: Semantics (valuation-based, Kripke frames) with soundness
5. **PR 5**: Completeness for CPL (truth table argument)
6. **PR 6**: Completeness for IPL (canonical model construction)

The planned roadmap mirrors the structure of Troelstra & van Dalen [TroelstraVanDalen1988]
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
