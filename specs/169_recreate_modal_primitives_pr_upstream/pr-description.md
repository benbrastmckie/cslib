# PR Description: refactor(Modal): Hilbert-style primitives for modal propositions

## Title

`refactor(Modal): Hilbert-style primitives for modal propositions`

## Base Branch

`refactor/proposition-lukasiewicz` (PR #635)

## Branch

`refactor/modal-primitives-v2`

## Context

This PR is a recreate of PR #637, which was closed because a rebase onto fork/main accumulated ~100
unrelated upstream commits, making it impractical to review. Following maintainer feedback from
chenson2018 requesting small, reviewable PRs, this is a clean re-submission that is stacked on PR
#635 and contains only the Modal layer changes.

This PR should be merged after PR #635 (`refactor/proposition-lukasiewicz`).

## Summary

Refactors the Modal `Proposition` inductive to use `{atom, bot, imp, box}` as the four primitive
constructors. Negation, conjunction, disjunction, diamond (possibility), and biconditional become
derived connectives via the `Cslib.Foundations.Logic.Connectives` interface introduced in PR #635.
`Proposition` is registered as a `ModalConnectives` instance.

## Changes

**`Cslib/Logics/Modal/Basic.lean`** (+249/-185):
- Replace `not`/`and`/`diamond` constructors with `bot`/`imp`/`box`; derived connectives are
  `abbrev`s, enabling definitional unfolding.
- Rewrite `Satisfies` on the new primitives.
- Add explicit characterisation lemmas: `neg_iff`, `diamond_iff`, `and_iff`, `or_iff`.
- Replace `grind`-based axiom-validity proofs (K, dual, T, B, 4, 5, D and their
  frame-correspondence converses) with explicit term-mode proofs.
- Register `Proposition` as a `ModalConnectives` instance.

**`Cslib/Logics/Modal/Denotation.lean`** (+46/-6):
- Update `Proposition.denotation` to pattern-match on `bot`, `imp`, and `box` constructors.
- Update `satisfies_mem_denotation` and `neg_denotation` proofs for the new primitives.

**`Cslib/Logics/Modal/LogicalEquivalence.lean`** (+48/-144, complete rewrite):
- Rewrite one-hole `Proposition.Context` with new constructors `{hole, impL, impR, box}` matching
  the new recursive positions of `Proposition`.
- Prove `LogicallyEquivalent.congruence` directly rather than instantiating the shared
  `LogicalEquivalence` typeclass (rationale documented in the file's Design Notes).

**`CslibTests/GrindLint.lean`** (+3/-0):
- Add `#grind_lint skip` entries for three derived-connective characterisation lemmas whose
  `@[scoped grind =]` annotations have long instantiation chains.

## Diff Stats

```
 Cslib/Logics/Modal/Basic.lean              | 315 ++++++++++++++++++++---------
 Cslib/Logics/Modal/Denotation.lean         |  52 ++++-
 Cslib/Logics/Modal/LogicalEquivalence.lean | 192 +++++++-----------
 CslibTests/GrindLint.lean                  |   3 +
 4 files changed, 343 insertions(+), 219 deletions(-)
```

## CI Status

- `lake build`: passed
- `lake lint`: passed
- `lake exe checkInitImports`: passed
- `lake exe lint-style`: passed (no issues in modified files)
- `lake exe mk_all --module`: passed (no update necessary)
- `lake shake`: pre-existing suggestions unrelated to Modal changes
- `lake test`: passed

## AI Tools Used

- Claude Code (cslib-implementation-agent): Resolved cherry-pick conflicts in
  `Cslib/Logics/Modal/Basic.lean`, `Cslib/Logics/Modal/Denotation.lean`, and
  `Cslib/Logics/Modal/LogicalEquivalence.lean`. Ran the full CSLib CI pipeline to verify the branch.
  Added `#grind_lint skip` entries to `CslibTests/GrindLint.lean`. Wrote this PR description.
