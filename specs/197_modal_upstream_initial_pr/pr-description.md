# PR Description: feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}

## Title

`feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}`

## Summary

This PR refactors `Cslib/Logics/Modal/Basic.lean` to use four classical primitives
`{atom, bot, imp, box}` instead of the current `{atom, not, and, diamond}`. Negation,
conjunction, disjunction, and diamond (possibility) become derived connectives via the
Lukasiewicz encoding (`¬φ := φ → ⊥`, `φ ∧ ψ := ¬(φ → ¬ψ)`, `φ ∨ ψ := ¬φ → ψ`,
`◇φ := ¬□¬φ`). Three files are modified in total: `Basic.lean` (the formula type),
`Denotation.lean` (updates `atom`/`bot`/`imp`/`box` match cases), and
`LogicalEquivalence.lean` (`Context` constructors updated from `{notC, andL, andR, diamondC}`
to `{impL, impR, box}`). A fourth file, `Cslib/Foundations/Logic/Connectives.lean` (introduced
by PR #648), is extended with a new `HasBox` atomic class and a new `ModalConnectives` bundled
class extending `PropositionalConnectives`.

This PR stacks on PR #648 (`feat/propositional-v2`), following the same stacking pattern used
by PR #649 (`feat/temporal-formula-propositional`).

## Design Rationale

### Why box, not diamond?

CSLib takes box (`□`) as the sole primitive modal operator for two complementary reasons.

**Proof-theoretic**: The necessitation rule (`if ⊢ φ then ⊢ □φ`) and the K axiom
(`□(φ → ψ) → (□φ → □ψ)`) are pure proof rules on a single primitive. With diamond primitive,
necessitation becomes the interaction law `¬◇¬`, requiring negation as infrastructure; with box
primitive, necessitation and K involve only box. [ChagrovZakharyaschev1997] Section 3.1 adopts
the box-first presentation; [Blackburn2001] Chapter 1 takes the diamond-first alternative.
[Burgess1984] uses the box primitive throughout its treatment of normal modal logics.

**Semantic**: Box corresponds to universal quantification over accessible worlds
(`□φ` is true at `w` iff `∀ w', r w w' → φ` holds at `w'`), and distributes over implication
(the K axiom). Universal quantification over sets is natural to define and compose; existential
quantification (for diamond) would require a separate case.

Diamond is derived as `◇φ := ¬□¬φ`, which in the Lukasiewicz encoding expands to
`(□(φ → ⊥)) → ⊥`. This derivation uses excluded middle (`¬¬p ↔ p`) and is therefore specific
to classical modal logic. Non-classical modal logics (intuitionistic, minimal) require box and
diamond as independent primitives; `HasDia` should be added as a separate typeclass class once
non-classical modal logics are formalized in CSLib.

### Why bot and imp as primitives?

This follows the rationale established in PR #648 for propositional logic: bot and imp are
the classical minimal signature from which all other connectives can be derived classically.
With primitive `bot` and `imp`, negation (`¬φ := φ → ⊥`) and verum (`⊤ := ⊥ → ⊥`) are
constraint-free derived connectives. The Lukasiewicz encodings of conjunction and disjunction
are classically equivalent to their natural counterparts; see [Johansson1937] for the
minimal-logic role of `⊥`, and [Wajsberg1938] and [McKinsey1939] for classical equivalence
results. The note in `Connectives.lean` explains that propositional conjunction and disjunction
are primitive in `PL.Proposition` (via `HasAnd`/`HasOr`), while the Modal formula type uses
the Lukasiewicz encodings.

## Main Definitions

- `Proposition (Atom)` — inductive formula type with constructors `{atom, bot, imp, box}`
- `Proposition.neg` — derived negation `¬φ := φ → ⊥` (abbrev)
- `Proposition.top` — derived verum `⊤ := ⊥ → ⊥` (abbrev)
- `Proposition.and` — derived conjunction via Lukasiewicz (abbrev)
- `Proposition.or` — derived disjunction via Lukasiewicz (abbrev)
- `Proposition.diamond` — derived possibility `◇φ := ¬□¬φ` (abbrev)
- `Proposition.iff` — derived biconditional (abbrev)
- `Proposition.Context` — one-hole context type with constructors `{hole, impL, impR, box}`
- `LogicallyEquivalent` — semantic equivalence across all models and worlds
- `ModalConnectives` — bundled typeclass extending `PropositionalConnectives` with `HasBox`
  (defined in `Connectives.lean`)

## Notation

All notation is scoped to `Cslib.Logic.Modal`:

| Symbol | Precedence | Definition |
|--------|-----------|-----------|
| `¬` | prefix:40 | `Proposition.neg` |
| `∧` | infix:36 | `Proposition.and` |
| `∨` | infix:35 | `Proposition.or` |
| `→` | infix:30 | `Proposition.imp` |
| `□` | prefix:40 | `Proposition.box` |
| `◇` | prefix:40 | `Proposition.diamond` |
| `↔` | infix:30 | `Proposition.iff` |
| `Modal[m,w ⊨ φ]` | — | `Judgement.mk m w φ` |

## Relationship to Other PRs

### PR #648: Stacking Dependency

This PR stacks on PR #648 (`feat(Logics/Propositional): five-primitive formula type with
connective typeclasses`). The branch is created from `feat/propositional-v2` and carries all
of #648's changes, including `Connectives.lean` with `PropositionalConnectives`. The Modal PR
extends `Connectives.lean` with `HasBox` and `ModalConnectives`. Review and merge in order:
PR #648 first, then this PR.

### PR #649: Sibling

PR #649 (`feat(Logics/Temporal): temporal formula type`) is a sibling: both PRs stack on #648
independently and can be reviewed in either order. This PR does not depend on #649 and #649
does not depend on this PR.

### PR #607: Coordination Note

PR #607 by @fmontesi introduces per-operator typeclass files under `Foundations/Logic/Operators/`
(one file per connective: `And.lean`, `Box.lean`, `Diamond.lean`, `Impl.lean`, etc.). The
reviewer feedback from @chenson2018 on PR #607 asked "Would it be better to just have one file
for these?" — our `Connectives.lean` single-file approach directly addresses that comment.

The only naming difference between PR #607 and our approach is `HasImpl`/`impl` (PR #607) vs
`HasImp`/`imp` (our PRs). The `imp` naming is used consistently across CSLib's Bimodal and
Temporal formula types and aligns constructor names with rule name prefixes (`impI`/`impE`). The
`HasBox`/`box` field name is identical in both PRs. If PR #607 moves forward, aligning to `HasImp`
is a one-line change. We are happy to coordinate on the final naming if reviewers prefer a
different convention.

This PR's refactoring of `Modal/Basic.lean` from `{atom, not, and, diamond}` to
`{atom, bot, imp, box}` changes the constructor set that PR #607 wraps. The two approaches are
structurally incompatible at the constructor level, so they require coordination before one can
merge. We offer this PR as the substantive refactoring; PR #607's typeclass instances can then
be updated to match the new `{bot, imp, box}` constructors straightforwardly.

### PRs #528 and #535: Foundational Work

PR #528 and PR #535 by @fmontesi introduced the original `Modal/Basic.lean` and
`Modal/LogicalEquivalence.lean` to CSLib. This PR builds directly on that foundation. The
`Model`/`Satisfies`/`Judgement` structure from PR #528 is retained unchanged; we add only the
`ModalConnectives` instance to hook into the shared typeclass hierarchy. The `Context` type
from PR #535 is updated to match the new constructors (`{impL, impR, box}` instead of
`{notC, andL, andR, diamondC}`), and `LogicallyEquivalent.congruence` is updated accordingly.
The induction cases for `impL`, `impR`, and `box` closely follow the structure of the original
`notC`, `andL`, `andR`, `diamondC` cases.

## Breaking Changes

### Removed Constructors

- `Proposition.not` — replaced by derived `Proposition.neg` (`abbrev`)
- `Proposition.and` constructor — replaced by derived `Proposition.and` (`abbrev`)
- `Proposition.diamond` constructor — replaced by derived `Proposition.diamond` (`abbrev`)

Note: `Proposition.and` and `Proposition.diamond` are now `abbrev`s with the same name, so
call sites that use these names without constructor syntax (`| .and`, `| .diamond`) continue to
work for pattern-matching. Code that explicitly pattern-matches `| .not` or `| .diamond` in
the constructor position must be updated.

### Context Constructor Renames

`Proposition.Context` constructors:

| Old | New |
|-----|-----|
| `notC` | (removed — `neg` is now derived; no context position for it) |
| `andL` | `impL` (left of `imp` subsumes negation-of-left) |
| `andR` | `impR` (right of `imp` subsumes conjunction-right) |
| `diamondC` | `box` (box context replaces diamond context) |

Files affected: `LogicalEquivalence.lean` (the only consumer of `Proposition.Context`).

### Added Primitives

- `Proposition.bot` — new constructor (falsum/bottom)
- `Proposition.imp` — new constructor (implication, replaces derived `impl`-style encoding)
- `Proposition.box` — new constructor (necessity, was previously absent from `Basic.lean`)

## Changed Files

- [`Cslib/Foundations/Logic/Connectives.lean`](Cslib/Foundations/Logic/Connectives.lean) — **Modified**: added `HasBox` class and `ModalConnectives` bundled class (stacks on PR #648)
- [`Cslib/Logics/Modal/Basic.lean`](Cslib/Logics/Modal/Basic.lean) — **Modified**: refactored `Proposition` from `{atom, not, and, diamond}` to `{atom, bot, imp, box}`; derived connectives updated; added `ModalConnectives` instance; `Satisfies` match cases updated; modal cube axioms retained
- [`Cslib/Logics/Modal/Denotation.lean`](Cslib/Logics/Modal/Denotation.lean) — **Modified**: `Proposition.denotation` match cases updated for `{atom, bot, imp, box}` primitives
- [`Cslib/Logics/Modal/LogicalEquivalence.lean`](Cslib/Logics/Modal/LogicalEquivalence.lean) — **Modified**: `Proposition.Context` constructors renamed from `{notC, andL, andR, diamondC}` to `{impL, impR, box}`; `LogicallyEquivalent.congruence` proof updated

Approximate diff: ~355 insertions, ~222 deletions across the four files (three in `Logics/Modal/`,
one in `Foundations/Logic/`).

## Contribution Roadmap

This PR is part of a planned series contributing our Modal logic formalization upstream:

1. **PR #648**: Connective typeclasses + five-primitive propositional formula type *(open)*
2. **This PR**: Classical modal formula type with `{atom, bot, imp, box}` primitives
3. **PR 3**: Modal proof system (Hilbert axiomatization, completeness for K)
4. **PR 4**: Modal Kripke semantics with soundness

The temporal formula type (PR #649) is a sibling series that may proceed in parallel.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]
* [J. P. Burgess, *Basic Tense Logic*][Burgess1984]
* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
* [M. Wajsberg, *Untersuchungen über den Aussagenkalkül von A. Heyting*][Wajsberg1938]
* [J. C. C. McKinsey, *Proof of the Independence of the Primitive Symbols of Heyting's Calculus*][McKinsey1939]

## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and reviewing the PR description and rationale
- Analyzing the upstream PR landscape (PRs #528, #535, #607, #648, #649) for coordination strategy
- Running CI verification commands during development
- Literature verification and BibKey citation checking

The mathematical content, proof architecture, and design decisions were verified by the author.
All Lean code compiles with no sorries.
