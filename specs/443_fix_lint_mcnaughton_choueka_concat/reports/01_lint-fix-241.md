# Research Report: Task 443 — Fix 2 lake lint violations from task 241

Task type: cslib | Session: sess_1782882476_455d76 | Scope: mechanical lint fix (2 sites)

## Summary

Two environment-linter violations were introduced by task 241:

1. `defsWithUnderscore` on the `Monoid` instance `buchiCongruence_instMonoid`
   (`Cslib/Computability/Languages/Congruences/BuchiCongruence.lean:268`).
2. `unusedArguments` on `mullerAccConcat`
   (`Cslib/Computability/Automata/DA/Concat.lean:162`).

Both have established, low-risk fixes with direct codebase precedent. No new definitions,
axioms, or sorries are required. Reuse-first check: N/A (renaming + attribute only; no new
abstractions proposed).

## Finding 1 — defsWithUnderscore: `buchiCongruence_instMonoid`

### Current code (BuchiCongruence.lean:268)

```lean
instance buchiCongruence_instMonoid : Monoid (Quotient na.BuchiCongruence.eq) where
```

Declared inside `namespace Cslib.Automata.NA.Buchi` (opened at line 22; `variable {na : Buchi
State Symbol}` at line 57). It is a non-Prop `def`-like declaration, so the `defsWithUnderscore`
linter applies (lemmas/theorems are exempt, which is why the sibling `buchiCongruence_left_cov`,
`buchiCongruence_mk_append`, `buchiCongruence_pow_succ` snake_case lemmas are NOT flagged).

### Reference check (downstream call sites)

`grep -rn "buchiCongruence_instMonoid" Cslib/ CslibTests/` returns **only the declaration line
268**. There are no direct references anywhere — as expected, the instance is found by typeclass
resolution (e.g. via `Monoid`/`*`/`^`/`1` on `Quotient na.BuchiCongruence.eq`), never by name.
**Renaming is safe with zero call-site updates.**

### Convention and recommended name

CSLib/Mathlib require instance names in lowerCamelCase with no underscores. The fix is to remove
the underscore. Recommended primary name (minimal change, consistent with the file's
`buchiCongruence*` naming family):

```lean
instance buchiCongruenceMonoid : Monoid (Quotient na.BuchiCongruence.eq) where
```

Acceptable alternative following Mathlib's `inst`-prefix instance convention (cf. sibling
instances elsewhere in the tree such as `instSemilatticeInf`, `instPartialOrder`):
`instMonoidBuchiCongruence`.

Recommendation: use `buchiCongruenceMonoid`. It is lowerCamelCase, underscore-free, and mirrors
the surrounding `buchiCongruence*` declarations. Note: `dupNamespace` is not triggered (the
lowercase `buchi` prefix is not the capitalized namespace component `Buchi`), and `topNamespace`
is not triggered (the instance sits inside a named namespace).

## Finding 2 — unusedArguments: `mullerAccConcat`

### Current code (Concat.lean:162-167)

```lean
noncomputable def mullerAccConcat (_ : DA State1 Symbol) (_ : Set State1)
    (_ : DA State2 Symbol) (accSet2 : Set (Set State2)) :
    Set (Set (State1 × (Fin (Nat.card State2 + 2) → Option State2))) :=
  {acc | ∃ i : Fin (Nat.card State2 + 2),
    {s2 | ∃ s ∈ acc, s.2 i = some s2} ∈ accSet2 ∧
    ∀ s ∈ acc, (s.2 i).isSome}
```

The first three binders are the automaton/acceptance data `da1 : DA State1 Symbol`,
`acc1 : Set State1`, `da2 : DA State2 Symbol`. They are **genuinely unused in the body** (already
written as `_`), and only `accSet2` is consumed.

### Are the arguments removable?

No. They are part of the intended public API and are supplied at every call site:

- `Cslib/Computability/Automata/DA/Concat.lean:722` — `mullerAccConcat da1 acc1 da2 accSet2`
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean:109` —
  `DA.mullerAccConcat dfa.toDA dfa.accept da2.toDA da2.accept`
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean:422` —
  `DA.mullerAccConcat dfa1.toDA dfa1.accept da2.toDA da2.accept`

The signature deliberately parallels `concat da1 acc1 da2` for API uniformity, so the arguments
are kept for interface consistency even though the acceptance family only depends on the state
types (via the return type) and `accSet2`. Removing them would break all three call sites and
diverge from `concat`'s shape.

### Recommended fix

Bare `_` binders do **not** silence the environment `unusedArguments` linter (evidenced by the
fact that the current `_`-named args are what triggered the warning). The canonical CSLib
mechanism for "intentionally unused but API-required" arguments is the `@[nolint unusedArguments]`
attribute. There is strong precedent in this repository (10+ sites), e.g.:

- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean:114`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean:204,214`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Splitting.lean:125,130,160`

Apply the attribute to the definition:

```lean
/-- The Muller acceptance family for the concat automaton. ... -/
@[nolint unusedArguments]
noncomputable def mullerAccConcat (_ : DA State1 Symbol) (_ : Set State1)
    (_ : DA State2 Symbol) (accSet2 : Set (Set State2)) :
    ...
```

The binders may be left as `_` (recommended — makes the "unused" intent explicit) or optionally
given descriptive names; the `nolint` attribute is what silences the linter either way. Do NOT
restructure the signature or drop arguments — that would break the three call sites and the
parallelism with `concat`. No lint suppression beyond the standard `@[nolint unusedArguments]`
attribute is needed.

## Verification commands (for implementation phase)

Run from repo root `/home/benjamin/Projects/cslib`:

```bash
# 1. Scoped builds of the two edited modules + downstream consumer of mullerAccConcat
lake build Cslib.Computability.Languages.Congruences.BuchiCongruence
lake build Cslib.Computability.Automata.DA.Concat
lake build Cslib.Computability.Languages.OmegaRegularLanguage

# 2. Full environment linter (confirms both categories cleared)
lake lint

# 3. Final full build (CI parity)
lake build
```

Expected result: `lake lint` reports zero `defsWithUnderscore` and zero `unusedArguments`
warnings for these two declarations, and all builds succeed. Because the instance rename has no
external references and the `nolint` attribute changes no term-level content, no other module
should require edits.

## Zero-debt / constraints compliance

- No sorry, no new axioms, no vacuous definitions.
- Instance rename: pure rename, 1 edit, 0 call-site updates (verified by grep).
- `mullerAccConcat`: 1 attribute line added, 0 signature/body changes, 0 call-site updates.
