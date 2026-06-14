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

## Resolving PR #635: Functional Completeness

PR #635 reviewer ctchou raised the question of functional completeness. The four-primitive
`{atom, and, or, impl}` type is *not* functionally complete for classical logic: one cannot
express unsatisfiable formulas (there is no way to say "contradiction") without special-casing
the atom type.

The five-primitive `{atom, bot, imp, and, or}` type resolves this objection:
- `bot` is now a genuine formula constructor, not an atomic formula encoding of bottom
- `¬A := A → ⊥` is uniformly available without any typeclass constraint on `Atom`
- The formula type is the standard propositional signature studied in [Church1956] §24 and
  [TroelstraVanDalen1988] Chapter 2
- Tautological constants ⊥ and ⊤ are available at all logic levels (MPL, IPL, CPL) without
  additional assumptions

## Literature Justification for Primitive `bot`

**Why `bot` must be a primitive, not simulated via `[Bot Atom]`**:

Johansson's minimal logic (1937, [Johansson1937]) is the standard foundation for
proof-relevant propositional logic and the weakest sensible propositional logic for which
the Curry-Howard correspondence works in its standard form. Minimal logic requires a
distinguishable bottom formula ⊥ with no further axioms about it. Without primitive ⊥:
- The formula type represents only the *positive fragment* (purely positive logic: no ⊥, no ¬)
- Negation cannot be defined; `¬A := A → ⊥` requires a specific ⊥ term, not just a class
- The correspondence between the logic hierarchy MPL ⊂ IPL ⊂ CPL breaks down

The `[Bot Atom]` approach in the previous version was a workaround that embedded ⊥ as a
special atom. This has the following problems:
1. `Bot Atom` conflates the logical bottom with atomic data
2. `neg` and `top` required separate typeclass constraints `[Bot Atom]` and `[Inhabited Atom]`
3. `IPL`, `IsIntuitionistic`, `IsClassical` all required `[Bot Atom]` constraints, making
   definitions needlessly complex

With primitive `bot`:
- `neg`, `top`, and `iff` are constraint-free `abbrev`s
- `IPL`, `IsIntuitionistic`, `IsClassical` have no typeclass constraints
- `derivationTop`, `derivableIn_top`, `derivable_iff_equiv_top` are constraint-free

## Naming Rationale: `imp` vs `impl`

The constructor name `impl` was non-standard. The standard notation in the proof theory
literature is:

- Gentzen (1935, [Gentzen1935]): writes implication as `⊃`
- Prawitz (1965, [Prawitz1965]): writes implication as `⊃`
- Troelstra & van Dalen (1988, [TroelstraVanDalen1988]): write implication as `→`
- Church (1956, [Church1956]): writes implication as `⊃`

None of these sources use `impl` as the name for the implication constructor. The name
`imp` (short for implication) is standard in Lean formalization practice (see e.g., Lean's
own `Prop` operations and modal logic formalizations). We adopt `imp` for consistency with
both the literature and Lean conventions.

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

## Breaking Changes

- `Proposition.impl` renamed to `Proposition.imp`
- `andE₁`/`andE₂`/`orI₁`/`orI₂` renamed to `andE1`/`andE2`/`orI1`/`orI2`
- `[Bot Atom]` constraints removed from `IPL`, `IsIntuitionistic`, `IsClassical`, and
  related instances and theorems
- `[Inhabited Atom]` constraint removed from `Proposition.top`, `derivationTop`,
  `derivableIn_top`, `derivable_iff_equiv_top`
- `instBotProposition` and `instInhabitedOfBot` removed; new constraint-free instances added

Files affected upstream: `Defs.lean`, `NaturalDeduction/Basic.lean` (only consumers)

## CI Verification

All checks pass on the feature branch `feat/propositional-five-primitive`:
- `lake build` succeeds (all modules compile)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes (all three files)
- `lake exe mk_all --module` confirms barrel file is correct

## AI Tools Used

- **Claude (claude-sonnet-4-6 via Claude Code)**: Used for research, implementation planning,
  literature review, and code assistance. The implementation follows the plan in
  `specs/188_first_propositional_upstream_pr/plans/01_implementation-plan.md`. All
  mathematical content (logic literature justifications, typeclass hierarchy design, naming
  conventions) was verified against primary sources. Code was reviewed and tested with
  `lake build` before submission.
