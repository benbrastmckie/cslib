# Engaging PR #607 — connective typeclass refactor

**Task**: 400 — reconcile_connectives_pr607
**Date**: 2026-06-29
**Source**: Waring, CSLib Zulip "Propositional Logic" thread, msg 606970606 — "the addition of
connective typeclasses is a separate development, perhaps you could just leave a review on the
existing PR on the subject &/or help that get merged — the design seems very similar."

PR #607 = `fmontesi/connectives`, "feat(Logic): logical operators" (OPEN, +296/−33, 15 files).
It introduces operator typeclasses and refactors Modal/Propositional/Linear to use them.

## Status of the CSLib-side prerequisite (DONE)
Our parallel `Cslib/Foundations/Logic/Connectives.lean` has been **removed from PR #648**
(commit `85db79a6` on branch `feat/propositional-ipl-base`): deleted the file, dropped its import
+ the 3 registration instances from `Defs.lean`, and removed the barrel import. So #648 no longer
ships a competing typeclass module — the propositional connective typeclasses are now meant to land
via #607. Remaining work = the human-authored review on #607 below.

## Design comparison

| Aspect | #607 (fmontesi) | Ours (removed Connectives.lean / #648 `Proposition`) |
|---|---|---|
| Granularity | one class per operator (à la carte) | one class per operator + bundled `PropositionalConnectives` |
| Operators | `HasAnd HasOr HasImpl HasNot HasIff HasBox HasDiamond HasTensor` | `HasBot HasImp HasAnd HasOr` (+ derived neg/top/iff) |
| **Falsum** | **no `HasBot`; `HasNot` is primitive** | **`HasBot` primitive; `¬φ := φ → ⊥`, `⊤ := ⊥ → ⊥` derived** |
| impl name | `HasImpl` / `impl` | `HasImp` / `imp` |
| Notation prec | `→` 25, `∨` 30, `∧` 36, `¬` 40 | `→` 30, `∨` 35, `∧` 36, `¬` 40 |
| Notation source | typeclass notation + `@[scoped grind =]` def-lemmas | notation declared directly on `Proposition` |
| Scope | propositional + modal + linear | propositional |

## The substantive point to raise (primary)

**#607 makes negation primitive (`HasNot`) and has no `HasBot`.** In intuitionistic and minimal
propositional logic, negation is *definitionally* `¬φ := φ → ⊥`; a free-standing `HasNot` with no
link to `⊥` cannot represent IPL/MPL faithfully (it detaches `¬` from explosion/⊥). To register the
five-primitive `Proposition` (with primitive `⊥`), #607 should:
- add a `HasBot` (and probably `HasTop`) class, and
- treat `¬` and `⊤` as *derived* over `HasImp`+`HasBot` (or at least support the bot-primitive
  convention) rather than a primitive `HasNot`.

This is the design constraint that motivated our `HasBot` + derived-neg/top layout.

## Secondary alignment nits
1. Name: `HasImpl`/`impl` vs `HasImp`/`imp` — pick one.
2. Notation precedence conflicts (`→`: 25 vs 30; `∨`: 30 vs 35) — must be reconciled or formulas
   parse differently across logics.
3. Bundling: decide whether a convenience bundle (`PropositionalConnectives = HasBot + HasImp`) is
   wanted for polymorphic axiom definitions, or stay purely à la carte.
4. Notation ownership: #607 routes `∧ ∨ → ¬` through typeclasses + bridge `_def` lemmas; our
   `Proposition` declares them directly. One path must win (likely #607's) so there is no duplicate
   notation; `Proposition` then registers instances + the `_def` `@[scoped grind =]` lemmas.

## Deliverable
A human-authored review on #607 (CSLib Zulip AI policy — no AI-drafted prose posted) raising the
`HasBot`/derived-`¬` point as the main item, plus the naming/precedence/bundling nits, and offering
to register `Proposition`'s instances through #607 once the falsum question is settled.
Then, once #607 merges, register the propositional instances and drop any remaining local notation
that #607 supersedes.
