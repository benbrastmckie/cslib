# Research Report: Rebase PR #649 onto PR #648

## Task Context

PR #649 (`feat/temporal-formula-propositional`) is stacked on PR #648 (`feat/propositional-v2`).
Reviewer ctchou requested:
1. Rebase onto `feat/propositional-v2` so the diff shows only temporal-specific changes
2. Remove all unrelated file changes

## Branch Topology

```
main (70c5bf58)
  |
  +-- feat/propositional-v2 (194f0c3d, 2 commits ahead: 7cc09612, 194f0c3d)
  |
  +-- feat/temporal-formula-propositional (d2ad8c74, 1 commit ahead)
```

Both branches share the same parent: `70c5bf58` (refactor(Logics/Propositional) on main).
The temporal branch has a single monolithic commit (d2ad8c74) that bundles:
- All propositional-v2 changes (duplicated, not based on that branch)
- Temporal-specific new work
- Unrelated import/shake fixup changes across 10+ other files

## Diff Analysis: `feat/propositional-v2..feat/temporal-formula-propositional`

16 files differ. Classification:

### KEEP: Temporal-specific changes (5 files)

| File | Type | Notes |
|------|------|-------|
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | New | 119 lines. Temporal.Formula inductive type with TemporalConnectives instance |
| `Cslib/Logics/LTL/Syntax/Formula.lean` | New | 139 lines. LTL.Formula inductive type with LTLConnectives instance, toTemporal embedding |
| `Cslib/Foundations/Logic/Connectives.lean` | Modified | Adds HasUntil, HasSince, HasNext, FutureTemporalConnectives, LTLConnectives, TemporalConnectives. Also updates docstring and references list |
| `Cslib.lean` | Modified | Adds 2 imports: Cslib.Logics.LTL.Syntax.Formula, Cslib.Logics.Temporal.Syntax.Formula |
| `references.bib` | Modified | Adds temporal references: Kamp1968, GPSS1980, Burgess1982I, Burgess1982II, Burgess1984, Xu1988, Venema1993SinceUntil, GHR94, Reynolds1996, Pnueli1977, VardiWolper1986 |

### DROP: Unrelated changes (11 files)

| File | Change | Nature |
|------|--------|--------|
| `Cslib/Foundations/Data/HasFresh.lean` | Removed `meta import Lean.Elab.ConfigEval` and `import Qq` | Shake/import cleanup |
| `Cslib/Foundations/Semantics/LTS/Notation.lean` | Added `public import Cslib.Foundations.Semantics.LTS.Basic` | Shake/import fixup |
| `Cslib/Languages/CCS/Semantics.lean` | Rewired imports: changed `public meta import` to explicit `public import` for LTS modules; added Mathlib tactic imports | Shake/import fixup |
| `Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/Congruence.lean` | Changed import from Properties to LcAt | Shake/import fixup |
| `Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/FullBetaEta.lean` | Rewired imports: FullBetaConfluence+FullEtaConfluence -> FullEta+FullBeta+Confluence | Shake/import fixup |
| `Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/FullEtaConfluence.lean` | Changed import from Confluence to Defs | Shake/import fixup |
| `Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/MultiSubst.lean` | Changed imports: Stlc.Basic+FullBeta -> Properties+Context | Shake/import fixup |
| `Cslib/Logics/Modal/Basic.lean` | Rewired imports (Set.Basic, Euclidean -> granular Mathlib modules); removed `Set.setOf_true` from grind hint | Shake/import fixup + proof adjustment |
| `Cslib/Logics/Modal/Cube.lean` | Added `public import Cslib.Foundations.Relation.Euclidean` | Shake/import fixup (moved from Basic) |
| `Cslib/Logics/Modal/Denotation.lean` | Added `public import Mathlib.Data.Set.Basic` | Shake/import fixup (moved from Basic) |
| `Cslib/Logics/Propositional/Defs.lean` | Changed imports (removed FunLike, Set.Basic; added Finiteness.Attr, Set.Operations); added Architecture docstring section; changed intuitionisticCompletion docstring | Mixed: import fixup + docstring changes |

### Borderline Cases Requiring Judgment

**Connectives.lean** -- This is the most complex case. When diffed against propositional-v2, the
changes include:
- **Temporal additions** (KEEP): HasUntil, HasSince, HasNext classes; FutureTemporalConnectives,
  LTLConnectives, TemporalConnectives bundled classes
- **Docstring/reference updates** (KEEP): Updated module docstring to mention temporal; added
  reference citations for Wajsberg1938, McKinsey1939, Johansson1937, Prawitz1965,
  TroelstraVanDalen1988, Church1956, Gentzen1935

**references.bib** -- Contains both temporal-specific and propositional-adjacent references:
- **Temporal** (KEEP): Kamp1968, GPSS1980, Burgess1982I, Burgess1982II, Burgess1984, Xu1988,
  Venema1993SinceUntil, GHR94, Reynolds1996, Pnueli1977, VardiWolper1986
- **Propositional/logic foundations** (JUDGMENT CALL): Church1956, Gentzen1935, Johansson1937,
  McKinsey1939, Wajsberg1938, Prawitz1965, TroelstraVanDalen1988, vanDalen2013
  - These are referenced in the updated Connectives.lean docstring that mentions them.
  - Since the Connectives.lean modifications are temporal-specific changes (extending the file
    PR #648 created), these references should be KEPT.

**Propositional/Defs.lean** -- Mixed changes:
- Import rewiring (Finiteness.Attr, Set.Operations instead of FunLike.Basic, Set.Basic): This
  looks like a shake/import cleanup -- should be DROPPED
- Architecture docstring section addition: This documents the propositional proof system layers,
  which is propositional-v2 work -- should be DROPPED or deferred to PR #648
- Changed intuitionisticCompletion docstring: Minor rewording -- should be DROPPED

## PR Description Cross-Reference

The PR #649 description claims these changes:

### New files (matches)
- `Cslib/Logics/Temporal/Syntax/Formula.lean` -- present on branch, confirmed
- `Cslib/Logics/LTL/Syntax/Formula.lean` -- present on branch, confirmed

### Modified files (matches with caveats)
- `Cslib/Foundations/Logic/Connectives.lean` -- HasUntil, HasSince, HasNext, FutureTemporalConnectives, LTLConnectives, TemporalConnectives -- confirmed, but diff also includes docstring/reference updates beyond what PR description mentions
- `Cslib.lean` -- temporal and LTL imports -- confirmed, but current diff also adds Connectives import (which is a propositional-v2 change)
- `references.bib` -- Kamp1968, Pnueli1977, Burgess1984, VardiWolper1986, GPSS1980 -- confirmed, but also includes Church1956, Gentzen1935, Johansson1937, McKinsey1939, Wajsberg1938, Prawitz1965, TroelstraVanDalen1988, vanDalen2013, Burgess1982I, Burgess1982II, Xu1988, Venema1993SinceUntil, GHR94, Reynolds1996

### Extra changes NOT in PR description (should be dropped)
- `Cslib/Foundations/Data/HasFresh.lean`
- `Cslib/Foundations/Semantics/LTS/Notation.lean`
- `Cslib/Languages/CCS/Semantics.lean`
- 4x LambdaCalculus files (Congruence, FullBetaEta, FullEtaConfluence, MultiSubst)
- 3x Modal files (Basic, Cube, Denotation)
- `Cslib/Logics/Propositional/Defs.lean`

### Changes described but absent from branch-to-branch diff
- NaturalDeduction/Basic.lean and NaturalDeduction/Theory.lean are modified by the temporal
  commit (d2ad8c74) but these changes are also present in propositional-v2 so they cancel out
  in the branch-to-branch diff. This is correct behavior.

## Dependency Analysis

The temporal files only depend on:
1. `Cslib.Init` (available on all branches)
2. `Cslib.Foundations.Logic.Connectives` (created by PR #648, extended by PR #649)
3. `Mathlib.Order.Notation` (Mathlib, always available)
4. `Cslib.Logics.Temporal.Syntax.Formula` (LTL depends on Temporal -- both new in PR #649)

None of the temporal files import from:
- HasFresh, LTS/Notation, CCS, LambdaCalculus, Modal, or Propositional/Defs

Therefore all 11 "unrelated" files can be safely dropped with zero dependency risk.

## Recommended Git Strategy

**Option A: Clean checkout + selective file copy (RECOMMENDED)**

1. Create a new branch from `feat/propositional-v2`:
   ```bash
   git checkout feat/propositional-v2
   git checkout -b feat/temporal-formula-propositional-v2
   ```

2. Copy the temporal-specific file contents from the old branch:
   ```bash
   # New files (just checkout from old branch)
   git checkout feat/temporal-formula-propositional -- Cslib/Logics/Temporal/Syntax/Formula.lean
   git checkout feat/temporal-formula-propositional -- Cslib/Logics/LTL/Syntax/Formula.lean

   # Modified files: cherry-pick specific content
   git checkout feat/temporal-formula-propositional -- Cslib/Foundations/Logic/Connectives.lean
   git checkout feat/temporal-formula-propositional -- references.bib
   ```

3. For `Cslib.lean`, manually add only the 2 temporal import lines to the propositional-v2 version:
   ```
   public import Cslib.Logics.LTL.Syntax.Formula
   public import Cslib.Logics.Temporal.Syntax.Formula
   ```

4. Commit, force-push to `feat/temporal-formula-propositional`

**Option B: Cherry-pick + selective reset**

Cherry-pick d2ad8c74 onto feat/propositional-v2, then `git checkout feat/propositional-v2 -- <each unrelated file>` to revert them. More error-prone due to the large number of files to revert.

**Recommendation**: Option A is cleaner and less error-prone. It produces a single commit on top of propositional-v2 with exactly the described changes.

### Detailed Implementation Steps for Option A

```bash
# 1. Start from propositional-v2
git checkout feat/propositional-v2

# 2. Update the existing temporal branch to point here
# (or create new and force-push)
git branch -f feat/temporal-formula-propositional feat/propositional-v2

# 3. Switch to the branch
git checkout feat/temporal-formula-propositional

# 4. Copy new files from old commit
git show d2ad8c74:Cslib/Logics/Temporal/Syntax/Formula.lean > Cslib/Logics/Temporal/Syntax/Formula.lean
git show d2ad8c74:Cslib/Logics/LTL/Syntax/Formula.lean > Cslib/Logics/LTL/Syntax/Formula.lean

# 5. Copy modified Connectives.lean (temporal version has the full content we want)
git show d2ad8c74:Cslib/Foundations/Logic/Connectives.lean > Cslib/Foundations/Logic/Connectives.lean

# 6. Copy references.bib (temporal version has all needed entries)
# NOTE: This includes propositional-adjacent refs (Church, Gentzen, etc.) that are
# referenced in the Connectives.lean docstring. They should stay.
git show d2ad8c74:references.bib > references.bib

# 7. Manually edit Cslib.lean to add only the 2 temporal imports
# (propositional-v2 version already has Connectives import)

# 8. Create directories if needed
mkdir -p Cslib/Logics/Temporal/Syntax
mkdir -p Cslib/Logics/LTL/Syntax

# 9. Stage and commit
git add Cslib/Logics/Temporal/Syntax/Formula.lean \
       Cslib/Logics/LTL/Syntax/Formula.lean \
       Cslib/Foundations/Logic/Connectives.lean \
       Cslib.lean \
       references.bib
git commit -m "feat(Logics/Temporal): temporal formula type with propositional structure"

# 10. Force-push to update the PR
git push --force origin feat/temporal-formula-propositional
```

### Post-Rebase Verification

After rebasing, the diff `feat/propositional-v2..feat/temporal-formula-propositional` should show exactly:
- 2 new files (Temporal/Formula.lean, LTL/Formula.lean)
- 3 modified files (Connectives.lean, Cslib.lean, references.bib)
- 0 unrelated files

### Connectives.lean Diff Details

The diff against propositional-v2 should show only temporal additions:
- +3 new typeclasses: HasUntil, HasSince, HasNext
- +3 new bundled classes: FutureTemporalConnectives, LTLConnectives, TemporalConnectives
- Updated module docstring (propositional -> propositional and temporal)
- Added reference citations in docstring

### references.bib Diff Details

All bib entries added by the temporal commit that are NOT in propositional-v2 should remain.
This includes both temporal-specific entries (Kamp, Pnueli, Burgess, etc.) and
propositional-adjacent entries (Church, Gentzen, Johansson, etc.) that are referenced
in the updated Connectives.lean docstring.

Entries from propositional-v2 (Avigad2022) will already be present on the base branch.
