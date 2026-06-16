# Teammate A Findings: PR #649 CI Failure and Rebase on PR #648

## Key Findings

1. **CI fails with warnings-as-errors** in `Cslib.Logics.Propositional.Defs` due to two theorems
   (`Proposition.instBot_eq`, `Proposition.instTop_eq`) that have the `[DecidableEq Atom]` section
   variable auto-included but unused. The CI uses `--wfail` (warnings-as-errors), so these
   warnings terminate the build.

2. **PR #649 is stacked on an OLD version of PR #648.** PR #648 was subsequently updated with a new
   commit (`7cc09612`) that removed exactly these two theorems. PR #649 has not yet rebased to pick
   up that change, so its version of `Defs.lean` still carries the problematic theorems.

3. **What the CI is doing:** GitHub merges PR #649 (`feat/temporal-formula-propositional` HEAD
   `5785ebbd`) into upstream `main` HEAD (`70c5bf58`, the PR #536 merge). This merge commit is
   `2f21317f`. The merged result includes the old PR #649 `Defs.lean` (with the bad theorems), not
   the updated PR #648 `Defs.lean`.

4. **The fix is a rebase**, not a new commit: PR #649 needs to rebase onto the updated PR #648
   (`feat/propositional-v2` at `7cc09612`), which will pull in the correct `Defs.lean` that lacks
   the two offending theorems. No other code change is needed.

---

## PR #648 Status

**Branch**: `feat/propositional-v2`  
**Title**: `feat(Logics/Propositional): five-primitive formula type with primitive bot`  
**Base**: `main` (upstream)  
**State**: OPEN  
**Recent update**: Rebased with a single new commit `7cc09612` that supersedes all previous
commits in the PR:
- Adds `Cslib/Foundations/Logic/Connectives.lean` with `HasBot`, `HasImp`, `HasAnd`, `HasOr`,
  `PropositionalConnectives`
- Revises `Defs.lean`: `Proposition` with primitive `bot`; `imp`/`impI`/`impE` naming; removes
  `[Bot Atom]` constraints; reconciles with merged PR #536 (InferenceSystem-parameterized
  typeclasses)
- Key: PR #648 `Defs.lean` does **NOT** contain `Proposition.instBot_eq` or
  `Proposition.instTop_eq`
- References: uses `[Avigad2022]` instead of multi-reference docstring style
- `IsIntuitionistic` / `IsClassical` are now parameterized over `InferenceSystem S` rather than
  `Theory Atom`
- `IPL`, `CPL` use `{⊥ → A | A : Proposition Atom}` set-builder notation (not `Set.range`)

---

## PR #649 Status

**Branch**: `feat/temporal-formula-propositional`  
**Title**: `feat(Logics/Temporal): temporal formula type with propositional structure`  
**Base**: declared as `main`, but effectively stacked on PR #648  
**State**: OPEN  
**Current commits** (3):
1. `5700fedb` — `feat(Logics/Temporal, Propositional): temporal formula type with propositional structure`
2. `0afc9d6c` — `feat(references, Propositional): restore 7 bib entries and architecture docstring`
3. `5785ebbd` — `feat(Logics): add FutureTemporalConnectives typeclass layer and LTL.Formula type`

**Changed files** (unique to PR #649 beyond PR #648):
- `Cslib.lean` — 4 new imports (Temporal/Formula, LTL/Formula, LTL/Satisfies, Connectives)
- `Cslib/Foundations/Logic/Connectives.lean` — PR #649 version has temporal additions
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` — new file
- `Cslib/Logics/LTL/Syntax/Formula.lean` — new file
- `Cslib/Logics/Propositional/Defs.lean` — has extra Architecture docblock, extra references,
  extra `instBot_eq` / `instTop_eq` theorems **← root cause of CI failure**
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — some changes
- `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` — some changes
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — new file
- `references.bib` — additional entries

---

## CI Failure Analysis

**Run**: https://github.com/leanprover/cslib/actions/runs/27633080931/job/81712989982?pr=649  
**Failing target**: `Cslib.Logics.Propositional.Defs`

**Exact warnings that cause failure** (treated as errors via `--wfail`):

```
warning: Cslib/Logics/Propositional/Defs.lean:107:0: automatically included section variable(s)
unused in theorem `Cslib.Logic.PL.Proposition.instBot_eq`:
  [DecidableEq Atom]
consider restructuring your `variable` declarations so that the variables are not in scope or
explicitly omit them:
  omit [DecidableEq Atom] in theorem ...

warning: Cslib/Logics/Propositional/Defs.lean:106:0: `Proposition.instBot_eq` does not use the
following hypothesis in its type:
  • [DecidableEq Atom] (#2)
Consider removing this hypothesis and using `classical` in the proof instead.

warning: Cslib/Logics/Propositional/Defs.lean:110:0: automatically included section variable(s)
unused in theorem `Cslib.Logic.PL.Proposition.instTop_eq`:
  [DecidableEq Atom]
...

warning: Cslib/Logics/Propositional/Defs.lean:109:0: `Proposition.instTop_eq` does not use the
following hypothesis in its type:
  • [DecidableEq Atom] (#2)
```

**Root cause**: The two theorems
```lean
@[simp, grind =]
theorem Proposition.instBot_eq : (⊥ : Proposition Atom) = Proposition.bot := rfl

@[simp, grind =]
theorem Proposition.instTop_eq : (⊤ : Proposition Atom) = Proposition.top := rfl
```
are in `feat/temporal-formula-propositional:Cslib/Logics/Propositional/Defs.lean` (lines 106-111),
but are NOT in `feat/propositional-v2:Cslib/Logics/Propositional/Defs.lean` (the updated PR #648).

The section variable `[DecidableEq Atom]` declared at line 75 is automatically included in these
theorems because they are in scope, but neither theorem's type uses `DecidableEq`. This triggers
both `unusedSectionVars` and `unusedDecidableInType` linter warnings.

**All other modules built successfully** (2733/2734). Only `Cslib.Logics.Propositional.Defs`
logged a failure.

---

## Recommended Fix Approach

### Option A (Recommended): Rebase PR #649 onto updated PR #648

This is the correct approach since PR #649 is meant to stack on PR #648:

```bash
git checkout feat/temporal-formula-propositional
git rebase feat/propositional-v2
# Resolve any conflicts (mainly in Defs.lean and Connectives.lean)
git push origin feat/temporal-formula-propositional --force-with-lease
```

**What this achieves:**
- PR #649's base becomes the updated PR #648 commit (`7cc09612`)
- The `Defs.lean` in the merged result will be PR #648's version (no `instBot_eq`/`instTop_eq`)
- PR #649's unique additions (Temporal/LTL files) layer cleanly on top
- When CI merges PR #649 onto upstream `main`, it should now include PR #648's changes without
  the problematic theorems

**Potential conflicts to resolve during rebase:**
- `Cslib/Logics/Propositional/Defs.lean`: PR #649 adds Architecture docblock, additional
  references, and the two bad theorems. After rebase, the `Defs.lean` base will be PR #648's
  version (which already has a different reference style). Resolution: keep PR #648's version
  as-is, drop `instBot_eq`/`instTop_eq`, optionally preserve the Architecture docblock additions
  from PR #649.
- `Cslib/Foundations/Logic/Connectives.lean`: PR #649 adds temporal typeclasses
  (`HasUntil`, `HasSince`, `HasNext`, `FutureTemporalConnectives`, `LTLConnectives`,
  `TemporalConnectives`) on top of PR #648's propositional-only classes. These additions are
  non-conflicting.

### Option B (Alternative): Add `omit` annotations to PR #649

If rebase is not desired, the minimal fix is to add `omit [DecidableEq Atom] in` before each
theorem:

```lean
omit [DecidableEq Atom] in
@[simp, grind =]
theorem Proposition.instBot_eq : (⊥ : Proposition Atom) = Proposition.bot := rfl

omit [DecidableEq Atom] in
@[simp, grind =]
theorem Proposition.instTop_eq : (⊤ : Proposition Atom) = Proposition.top := rfl
```

However, this is a workaround, not the right fix. The real issue is that these theorems should
not exist in PR #649 at all (PR #648's updated version doesn't have them). A rebase is cleaner.

### Why Not Just Delete the Theorems Directly?

The theorems `instBot_eq` and `instTop_eq` exist in PR #649 to support simp/grind reasoning about
`⊥` and `⊤` notation unfolding. After rebasing onto updated PR #648, we need to verify whether
any downstream files in PR #649 (Temporal/Formula.lean, LTL/Formula.lean, LTL/Satisfies.lean)
use these simp lemmas. If they don't reference `⊥`/`⊤` in goals that need unfolding, removing
them is safe.

**Preliminary check**: The new files added by PR #649 are:
- `Temporal/Syntax/Formula.lean` — uses `bot`, `imp` constructors directly, not `⊥`/`⊤` notation
- `LTL/Syntax/Formula.lean` — same
- `LTL/Semantics/Satisfies.lean` — uses `.bot` constructor directly

So removing `instBot_eq`/`instTop_eq` is likely safe for PR #649's own code.

---

## Confidence Level: **HIGH**

The CI failure root cause is unambiguous:
- The failing target is identified in CI logs: `Cslib.Logics.Propositional.Defs`
- The exact warning messages are present in the logs with file/line numbers
- The diff between PR #648 and PR #649 branches shows exactly these two theorems as unique to
  PR #649
- PR #648's updated commit already fixed this by removing both theorems
- The fix (rebase PR #649 onto updated PR #648) directly addresses the root cause
