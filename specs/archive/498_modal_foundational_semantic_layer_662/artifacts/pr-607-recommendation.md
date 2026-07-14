# DRAFT -- comment-only recommendation for PR #607

> **DRAFT -- comment-only; requires explicit user approval before posting.**
> **Re-verify live PR/CI state at post time** (fmontesi back 23 July).
> **Never push to `fmontesi/connectives`.** This is a plain PR review comment, not a suggested
> change, not a push, not a rebase. Nothing in this file has been posted anywhere.

---

## Context

This comment is prepared in support of stacking PR #662 ("make box primitive alongside diamond")
on top of #607 ("feat(Logic): logical operators"). Task 441 (a parallel, independent modal-logic
development) already prototyped and CI-verified a fully-native `Proposition` primitive set for
modal logic, and the results suggest #607's `Operators.lean` would benefit from adopting the same
approach before #662 stacks on it.

## Recommendation

Adopt a fully-native 7-constructor `Proposition` for modal logic --
`{atom, bot, imp, and, or, box, diamond}` -- in place of the current `{atom, not, and, diamond}`
(with `or`/`imp` De Morgan-derived from `not`/`and`, and `box := ¬◇¬φ` defined in terms of
`diamond`). Concretely: make `bot`, `imp`, `and`, `or`, `box`, and `diamond` all primitive
constructors, independent of one another, with `neg`/`top` recovered as derived abbreviations
(`¬φ := φ → ⊥`, `⊤ := ⊥ → ⊥`) rather than primitive constructors.

## Justification

1. **One `Iff.rfl` decomposition lemma per connective, no bridge lemmas.** With every connective
   primitive, `Satisfies.and_iff`, `Satisfies.or_iff`, `Satisfies.box_iff_forall`,
   `Satisfies.diamond_iff_exists`, etc. are all `Iff.rfl` -- the satisfaction clause for a
   constructor unfolds directly by `rfl`, since `Satisfies` pattern-matches on the constructor. When
   `or`/`box` are defined in terms of `not`/`and`/`diamond`, their decomposition lemmas instead
   require an unfolding proof through the defining equation (`Proposition.box_def`,
   `Proposition.or_def`, ...) composed with `grind`/`simp`, and every downstream proof by structural
   induction on `Proposition` needs an extra case-bridging step for each derived connective. This
   compounds across the tableau expansion rules, the truth lemma, and canonical-model constructions,
   where one case per *primitive* constructor is strictly less code than one case per primitive
   constructor plus an unfolding lemma per derived one.

2. **Reuse for intuitionistic / minimal modal systems (IK, CK) where `□`/`◇` are independent.**
   Classically, `◇φ := ¬□¬φ` (or the converse) is sound, but in intuitionistic and minimal modal
   logics (see [Blackburn2001] Chapter 1 on classical vs. constructive presentations;
   [ChagrovZakharyaschev1997] Section 3.1 on modal system hierarchies) `□` and `◇` are genuinely
   independent operators -- neither is definable from the other without classical duality. A
   `Proposition` type that bakes in `box := ¬◇¬φ` (or vice versa) cannot be reused as the formula
   type for IK/CK without a redefinition; a `Proposition` type with both as independent primitives
   can be reused as-is, with the classical duality recovered as an *additional* theorem that simply
   does not hold (or is replaced by a one-directional entailment) in the non-classical semantics.

3. **Duality becomes a genuine theorem, not a definitional identity.** With `box`/`diamond` both
   primitive, `◇φ ↔ ¬□¬φ` is proved *semantically* (using excluded middle over the accessibility
   relation) as `Satisfies.dual`, rather than holding by `rfl` because one connective is literally
   defined as `¬ · ¬` of the other. This makes the classical assumption explicit and inspectable at
   the theorem level (its axiom footprint shows `Classical.choice`/`propext`/`Quot.sound`), rather
   than silently baked into the formula type's definition where it cannot be selectively withheld
   for non-classical systems. At the Hilbert-system level, the same duality is recovered via
   `AxiomDiaDualityFwd`/`AxiomDiaDualityBack` characterization schemata
   (`Foundations/Logic/Axioms.lean`), instantiated per-system in `ProofSystem/Instances/*.lean` --
   so classical systems still get the duality axiom/theorem where they need it; non-classical
   systems simply omit that instantiation.

## Typeclass instances entailed

Making all seven constructors native means registering (or reusing) one typeclass instance per
connective, mirroring the existing pattern in `Operators.lean`:

- `HasBot`, `HasImp`, `HasAnd`, `HasOr` -- for `bot`, `imp`, `and`, `or`.
- `HasBox`, `HasDia`/`HasDiamond` -- for `box`, `diamond` (see naming note below).
- `neg`/`top` -- derived `abbrev`s (`¬φ := φ → ⊥`, `⊤ := ⊥ → ⊥`), not separate typeclasses; no
  `HasNot` instance needed if `neg` is only ever used as notation over the derived `abbrev`.

## Naming reconciliation (flagged, not resolved here)

Two naming divergences exist between #607's `Cslib/Foundations/Logic/Operators.lean` and the
typeclass set used by the task-441 prototype (`Cslib/Foundations/Logic/Connectives.lean`):

- **`HasDia` vs `HasDiamond`**: #607's `Operators.lean` uses `HasDiamond`; the task-441 prototype
  uses `HasDia`. Both name the same concept (a diamond/possibility modality field). This comment
  does not propose which name wins -- that is left to the #607 owner / task 497.
- **`HasBot` absent in `Operators.lean`**: #607's current typeclass set has no `HasBot` (bottom is
  presumably folded into `HasNot`'s derived `⊥`/`⊤` today). Adopting native `bot` as a primitive
  constructor would need a `HasBot` instance registered, following the same pattern as `HasAnd`/
  `HasOr`/`HasImp` already in `Operators.lean`.

Both of these, along with the `imp`/`impl` field-naming question, are deliberately left to the
#607 owner's judgment and/or task 497's dedicated naming-reconciliation work -- **this comment
does not propose specific renames**.

## Reassurance: proof-theoretic weight is unchanged

Necessitation and the K axiom only ever touch `□` (never `◇` directly), so making `◇` primitive
alongside `□` does not add any new proof obligation to the Hilbert/tableau proof theory for K and
its extensions -- `Satisfies.k` is exactly as many lines with native primitives as with a derived
`diamond`. The extra primitive constructor is purely a *semantic-layer* and *formula-type* change;
it does not require additional axioms or inference rules at the proof-system level.

---

*Prepared for task 498 (CSLib). Not posted. Awaiting explicit user approval and a live
PR-state/CI re-check before any posting to https://github.com/leanprover/cslib/pull/607.*
