# Research Report: nolint unusedArguments on KB5 Univ Rules

**Task**: 529 — Add `@[nolint unusedArguments]` to `modalKb5BoxAllUniv` and `modalKb5DiaNegAllUniv`
**Type**: cslib (lint-fix)
**Session**: sess_1784402996_48ad02_529

## Summary

Two definitions in `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` each take a fifth
argument `_w : WorldIndex` that is genuinely unused by design. The corrected-gate KB5 rule
fires unconditionally on cluster-nonemptiness regardless of the trigger world, so the `w == 0`
conjunct that the frozen `*Full` helpers used was intentionally dropped. CSLib's `unusedArguments`
environment linter does not honor the underscore-prefix suppression convention, so `lake lint`
reports both as errors. The fix is the standard `@[nolint unusedArguments]` attribute, already
used at two established precedents in the codebase.

## Verified Findings

### Target 1: `modalKb5BoxAllUniv` (currently at line 2179)

Current source (docstring lines 2172-2178, def line 2179):

```lean
Sound because ... . -/
def modalKb5BoxAllUniv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (_w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
```

The `_w : WorldIndex` binder (line 2180) is not referenced anywhere in the body — the body
branches only on `modalKnownWorlds b` cluster-nonemptiness, never on `_w`.

### Target 2: `modalKb5DiaNegAllUniv` (currently at line 2196)

Current source (docstring lines 2194-2195, def line 2196):

```lean
`modalKb5BoxAllUniv`. -/
def modalKb5DiaNegAllUniv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (_w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
```

Same situation: `_w : WorldIndex` (line 2197) is unused; the body is the `.neg` dual of Target 1.

### Precedent 1: `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean:204`

```lean
@[nolint unusedArguments]
def extractCountermodelSimple (φ : Formula Atom) (b : Branch Atom)
    {ord : TimeOrdering} {applied : AppliedSet Atom}
    (_hSaturated : ... = none)
    : SimpleCountermodel Atom :=
```

Attribute is placed on its own line, immediately after the closing docstring `-/`, directly
above `def`.

### Precedent 2: `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean:202`

```lean
@[nolint unusedArguments]
noncomputable def deductionWithMemFc {fc : FrameClass}
    (Γ' : Context Atom) (A φ : Formula Atom)
    (d : DerivationTree fc Γ' φ) (_hA : A ∈ Γ') :
```

Same placement convention (attribute line directly above the `def`/`noncomputable def` keyword,
after any docstring). Confirms `unusedArguments` is the exact linter name and that the
underscore-prefixed unused binder is the exact pattern this attribute is meant to silence.

## Reuse Check

This is a mechanical lint annotation, not a new abstraction. No CSLib Foundations abstraction,
typeclass, or Mathlib lemma is relevant. The `@[nolint unusedArguments]` attribute is the
established, in-repo idiom for exactly this case (two precedents above). No new definition,
notation, or axiom is introduced. Zero-debt compliant: the fix is a pure attribute addition with
no `sorry`, no axiom, no placeholder.

## Recommended Fix (exact edits)

Insert one line — `@[nolint unusedArguments]` — immediately above each `def` keyword, matching
the precedent placement (after the closing docstring `-/`, no blank line between attribute and
`def`).

1. In `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`, before
   `def modalKb5BoxAllUniv` (currently line 2179), add:
   ```lean
   @[nolint unusedArguments]
   ```

2. Before `def modalKb5DiaNegAllUniv` (currently line 2196, line number shifts by +1 after the
   first edit), add:
   ```lean
   @[nolint unusedArguments]
   ```

Both edits target uniquely-named `def` lines, so an exact-string Edit on
`def modalKb5BoxAllUniv (b : List` / `def modalKb5DiaNegAllUniv (b : List` is unambiguous.

## Verification

- **Build**: `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` — attribute addition must
  not break compilation (attribute is inert w.r.t. elaboration of the body).
- **Lint (authoritative gate)**: `lake lint` must pass clean; specifically the two
  `unusedArguments` errors on these declarations must disappear and no new lint error may appear.
  The task states these are the sole CI failure attributable to the corrected-gate KB5 rule work.

## Risk / Notes

- Trivial, mechanical change. No proof obligations, no semantic change to the definitions.
- Do NOT touch the frozen `modalKb5BoxAllFull` / `modalKb5DiaNegAllFull` helpers or any other
  declaration — scope is exactly these two attribute insertions.
- The `_w` binder must be retained (it is part of the rule dispatcher's uniform signature); the
  attribute is the correct resolution, not binder removal.
