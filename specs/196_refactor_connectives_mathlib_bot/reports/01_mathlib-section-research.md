# Research Report: Mathlib Section Rewrite for PR Description

**Task**: 196 - refactor_connectives_mathlib_bot
**Date**: 2026-06-14
**Session**: sess_1781463892_2cf03f

## Executive Summary

The pr-description.md Mathlib section (lines 88-96 of `specs/188_first_propositional_upstream_pr/pr-description.md`) has already been updated by two prior task 196 commits (ad0adde3 and ed23a7e6). The current text is accurate and concise. This report verifies each claim in the current section against the codebase and documents the design rationale for future reference.

## Current Mathlib Section Text (lines 88-96)

```markdown
### Mathlib `Bot`/`HImp` Classes

Mathlib defines `Bot` and `HImp` (both in `Mathlib.Order.Notation`) as pure notation classes.
We use a uniform `Has*` naming convention (`HasBot`, `HasImp`, `HasAnd`, `HasOr`) for the
generic polymorphic layer, where these classes parameterize proof system infrastructure
(`Axioms.lean`, `ProofSystem.lean`, `Consistency.lean`, `BigConj.lean`). Concrete formula
types separately provide direct `Bot` instances for `⊥` notation. We kept `HasImp` rather
than Mathlib's `HImp` because `HImp` uses the field name `himp` and notation `⇨`, which
differ from CSLib's `imp`/`→` convention across all four formula types.
```

## Verification of Each Claim

### Claim 1: "Mathlib defines `Bot` and `HImp` (both in `Mathlib.Order.Notation`) as pure notation classes"

**Verified.** Both are defined in `Mathlib/Order/Notation.lean`:

- `Bot` (line 183): `class Bot (α : Type*) where bot : α` with notation `⊥ => Bot.bot`
- `HImp` (line 148): `class HImp (α : Type*) where himp : α → α → α` with notation `⇨ => himp`

Both are tagged `@[notation_class]`, confirming they are pure notation/syntax typeclasses with no mathematical content beyond providing a symbol.

### Claim 2: "uniform `Has*` naming convention (`HasBot`, `HasImp`, `HasAnd`, `HasOr`) for the generic polymorphic layer"

**Verified.** All four classes are defined in `Cslib/Foundations/Logic/Connectives.lean`:

| Class | Line | Field | Signature |
|-------|------|-------|-----------|
| `HasBot` | 61 | `bot : F` | `class HasBot (F : Type*) where` |
| `HasImp` | 66 | `imp : F → F → F` | `class HasImp (F : Type*) where` |
| `HasAnd` | 93 | `and : F → F → F` | `class HasAnd (F : Type*) where` |
| `HasOr` | 98 | `or : F → F → F` | `class HasOr (F : Type*) where` |

The `Has*` prefix is also used consistently for modal and temporal connectives: `HasBox` (line 78), `HasUntil` (line 84), `HasSince` (line 89). This naming symmetry extends across the entire typeclass hierarchy.

### Claim 3: "these classes parameterize proof system infrastructure (`Axioms.lean`, `ProofSystem.lean`, `Consistency.lean`, `BigConj.lean`)"

**Verified.** Usage counts and representative examples:

- **Axioms.lean**: 30+ occurrences. All axiom definitions (`axK`, `axS`, `exFalso`, `peirce`, `dne`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `axDistK`, `axT`) are parameterized over `[HasBot F] [HasImp F]` (and `[HasBox F]`, `[HasAnd F]`, `[HasOr F]` where needed).
- **ProofSystem.lean**: 25+ class definitions use `[HasBot F] [HasImp F]` as typeclass constraints. Every Hilbert system class (`MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert`, `ModalHilbert`, etc.) uses these.
- **Consistency.lean**: `DerivationSystem` structure and all consistency theorems are parameterized over `[HasBot F] [HasImp F]`.
- **BigConj.lean**: `bigconj` is defined using `HasBot.bot` and `HasImp.imp` to work across all formula types regardless of whether they have `HasAnd`.

Total: 833 occurrences of `Has*.field` references across `Cslib/Foundations/Logic/`.

### Claim 4: "Concrete formula types separately provide direct `Bot` instances for `⊥` notation"

**Verified.** Four concrete formula types provide direct `Bot` instances:

| Formula Type | File | Line | Instance |
|-------------|------|------|----------|
| `PL.Proposition Atom` | `Cslib/Logics/Propositional/Defs.lean` | 102 | `instance : Bot (Proposition Atom) := ⟨.bot⟩` |
| `Modal.Proposition Atom` | `Cslib/Logics/Modal/Basic.lean` | 103 | `instance : Bot (Proposition Atom) := ⟨.bot⟩` |
| `Temporal.Formula Atom` | `Cslib/Logics/Temporal/Syntax/Formula.lean` | 116 | `instance : Bot (Formula Atom) := ⟨.bot⟩` |
| `CLL.Proposition Atom` | `Cslib/Logics/LinearLogic/CLL/Basic.lean` | 58 | `instance : Bot (Proposition Atom) := ⟨.bot⟩` |

**Notable**: `Bimodal.Formula` does NOT have a direct `Bot` instance. It only has a `BimodalConnectives` instance (which provides `HasBot` via the typeclass hierarchy). This means `⊥` notation is not available for `Bimodal.Formula` through Mathlib's `Bot` class -- the bimodal code uses `.bot` constructor directly.

**Design**: No bridge instance `[HasBot F] : Bot F` exists. Concrete types get `⊥` notation via direct `Bot` instances. Generic code in Foundations uses `HasBot.bot` explicitly, which is intentional -- it makes the polymorphic layer independent of Mathlib's notation classes.

### Claim 5: "We kept `HasImp` rather than Mathlib's `HImp` because `HImp` uses the field name `himp` and notation `⇨`"

**Verified.** The mismatches between Mathlib's `HImp` and CSLib's `HasImp` are:

| Property | Mathlib `HImp` | CSLib `HasImp` |
|----------|---------------|----------------|
| Field name | `himp` | `imp` |
| Notation symbol | `⇨` (Heyting arrow) | `→` (standard arrow, scoped on concrete types) |
| Fixity | `infixr:60` | `infix:30` (on concrete types) |
| Semantic origin | Heyting algebras (order-theoretic) | Classical/intuitionistic logic (proof-theoretic) |

All four concrete formula types (`Propositional`, `Modal`, `Temporal`, `Bimodal`) use `imp` as their implication constructor name and `→` as the notation, making `HasImp` with field `imp` the natural choice. Replacing `HasImp` with `HImp` would require renaming the field across 833+ generic uses and changing notation from `→` to `⇨`.

### Claim 6: "differ from CSLib's `imp`/`→` convention across all four formula types"

**Verified.** All four formula types use the same constructor-and-notation convention:

| Formula Type | Constructor | Notation |
|-------------|-------------|----------|
| `PL.Proposition` | `.imp` | `scoped infix:30 " → " => Proposition.imp` |
| `Modal.Proposition` | `.imp` | `scoped infix:30 " → " => Proposition.imp` |
| `Temporal.Formula` | `.imp` | `scoped infix:30 " → " => Formula.imp` |
| `Bimodal.Formula` | `.imp` | `scoped infix:30 " → " => Formula.imp` |

## Analysis: Is the Current Mathlib Section Complete?

The current text is accurate and addresses all relevant design choices. The section covers:

1. What Mathlib offers (Bot, HImp as notation classes)
2. Why CSLib uses its own classes (uniform Has* naming for the generic layer)
3. Where these classes are used (four infrastructure files)
4. How notation works (direct Bot instances on concrete types)
5. Why HImp replacement is impractical (field name and notation mismatch)

**One potential addition** (optional): The section could mention that Mathlib has no equivalents for `HasAnd`/`HasOr` in the logical connective sense (Mathlib's `Sup`/`Inf` are order-theoretic), which further motivates keeping the uniform `Has*` family rather than mixing Mathlib and custom classes. However, this may be unnecessary detail for a PR description.

## Conclusion

The pr-description.md Mathlib section is accurate and complete as written. No further rewrite is needed. The two prior task 196 commits (ad0adde3 and ed23a7e6) have already addressed the original task goal: replacing the inaccurate "order-theoretic connotations" rationale with the correct reasoning (uniform Has* naming, direct Bot instances, HImp notation mismatch) and removing the bridge instance discussion.

## Tactic Survey Results

Not applicable -- this is a documentation-only task with no proof goals.

## Reuse Check

Not applicable -- no new definitions or abstractions are being introduced.
