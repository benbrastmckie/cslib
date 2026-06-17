# Teammate C Findings: Critic Analysis — PR #649 CI Failure and Rebase Risks

## Key Findings

### 1. CI Failure Root Cause (Confirmed, Unambiguous)

The CI failure is in `Cslib.Logics.Propositional.Defs` (job 81712989982). The build completes
2733/2734 targets successfully and then fails because:

- `Proposition.instBot_eq` (line 106 in PR #649 `Defs.lean`) includes `[DecidableEq Atom]` from
  section variable `variable {Atom : Type u} [DecidableEq Atom]` at line 75, but this theorem
  is just `rfl` — `DecidableEq` is never used.
- Same issue for `Proposition.instTop_eq` (line 109).
- CI uses `--wfail` (warnings-as-errors), so the `unusedSectionVars` and
  `unusedDecidableInType` lint warnings become build errors.

The fix is `omit [DecidableEq Atom] in` before each theorem, OR removing the theorems
(PR #648's updated `Defs.lean` has neither), OR rebasing onto updated PR #648.

### 2. PR #648 Is NOT Approved

Teammate A's analysis assumes PR #648's update (`7cc09612`) resolves all reviewer concerns.
**This assumption is wrong.** PR #648's GitHub review status is still `CHANGES_REQUESTED`
from ctchou (submitted 2026-06-15). The update addressed some concerns (Avigad reference,
removed semantics files) but ctchou has not re-reviewed. Rebasing PR #649 onto an
unapproved PR #648 may require re-doing the rebase again after PR #648 is further revised.

### 3. PR #649 Has Unaddressed Reviewer Requests

ctchou's PR #649 review (`CHANGES_REQUESTED`) explicitly requests:

1. **Remove past-time operators**: "We should start with a temporal logic with only future-time
   temporal operators. Past-time temporal operators are not very useful."
   
   **Current PR #649 still has `snce` (since) in `Temporal.Formula`** — this must be removed
   regardless of any rebase.

2. **LTS-based semantics**: "I would like to have a temporal logic that can talk about the
   (omega-)executions of LTS, not just a sequence of states."
   
   Current `LTL.Satisfies` uses `v : ℕ → (Atom → Prop)` (omega-words), NOT LTS executions.

3. **Remove irrelevant instances**: Encodable/Countable/Infinite/Denumerable — the PR
   description says these are "deferred," but the reviewer flagged them as "completely irrelevant."

These are **substantive code changes**, not just a rebase. A clean rebase that passes CI does
NOT address the reviewer concerns.

### 4. The Rebase Will Produce Extensive Merge Conflicts

Both PRs diverge from the same base commit `70c5bf58` and both heavily modify the same files.
File-by-file conflict analysis:

| File | PR #648 changes | PR #649 changes | Conflict Risk |
|------|----------------|-----------------|---------------|
| `Defs.lean` | Rewrites entire file (bot primitive, imp rename, IPL/MPL/CPL style) | Also rewrites entire file (same changes + Architecture docblock + instBot_eq/instTop_eq) | **HIGH** |
| `NaturalDeduction/Basic.lean` | impl→imp rename, context + [Bot Atom] removal | Same impl→imp + different reference list + `(MPL Atom).Equiv` style | **MEDIUM** |
| `NaturalDeduction/Theory.lean` | impl→imp + adds `instIsIntuitionisticIntuitionisticCompletion` instance | impl→imp + [Bot Atom] removal + does NOT have the new instance | **HIGH** |
| `Connectives.lean` | NEW file (71 lines, propositional only) | SUPERSET (116 lines, adds temporal classes) | **LOW** (additive) |
| `Cslib.lean` | Adds `Connectives` import (line 72) | Same `Connectives` import + 3 new LTL/Temporal imports | **LOW** (additive) |
| `references.bib` | Adds `Avigad2022` at TOP of file | Does NOT have `Avigad2022`; adds temporal refs | **MEDIUM** (Avigad2022 insertion point conflicts) |

The most dangerous conflicts:

**`Defs.lean` conflict**: PR #648 uses `IPL (Atom := Atom)` (named argument style with
`Set.range`), while PR #649 uses `IPL Atom` (positional) with set-builder notation
`{⊥ → A | A : Proposition Atom}`. After PR #648's Defs.lean becomes the base, PR #649's
commit patches will likely conflict at every IPL/MPL/CPL reference.

**`Theory.lean` conflict**: PR #648 inserts `instIsIntuitionisticIntuitionisticCompletion`
between `instIsIntuitionisticIPL` and `efqCtx`. PR #649 does not add this instance — its
commit patches the same region with different content (removing `[Bot Atom]`, renaming
`impl`→`imp`). When git tries to apply PR #649's patch against the new base (which has
the inserted instance), the context won't match cleanly.

**`references.bib` conflict**: PR #648 adds `Avigad2022` at the very start (lines 1-8).
PR #649's commit adds different refs elsewhere but doesn't include `Avigad2022`. The
insertion at position 1 changes line numbers for everything PR #649 touches, and may
conflict if git's heuristics misfire.

### 5. Post-Rebase Semantic Consistency Risks

Even if the rebase succeeds without textual conflicts:

- **MPL/IPL/CPL API divergence**: PR #648 uses `abbrev MPL : Theory Atom := ∅` (section
  variable style), while PR #649's Basic.lean uses `(MPL Atom).Equiv`. After rebase, Basic.lean
  in PR #649 will reference `(MPL Atom)` but Defs.lean (from PR #648) will define
  `MPL : Theory Atom` (no explicit Atom parameter). This will cause a Lean elaboration error.

- **`instIsIntuitionisticIntuitionisticCompletion` preservation**: If the rebase preserves
  PR #648's Theory.lean (with the new instance), the instance refers to
  `IPL (Atom := Atom)` style, but PR #649's Defs.lean commit changes IPL to positional.
  Type mismatch at `IPL (Atom := Atom)` vs `IPL Atom` depending on which version of Defs.lean
  is active.

- **`Avigad2022` orphan reference**: After rebase, `Avigad2022` from PR #648 would appear in
  `references.bib`, but PR #649's version of Defs.lean and Basic.lean REMOVED all `[Avigad2022]`
  citations, replacing them with newer refs. The orphan bib entry is not itself a build error,
  but it is inconsistent.

### 6. Force-Push Risks

Rebasing PR #649 requires a force-push to `feat/temporal-formula-propositional`:

- The PR has an active review in `CHANGES_REQUESTED` state. Force-pushing invalidates the
  review diff context — reviewers may need to re-examine changed files.
- GitHub caches CI results per commit SHA. After force-push, CI runs from scratch (no cache),
  which given the 2733-target build is ~5 minutes of compute.
- If PR #648 is later revised again (e.g., ctchou re-reviews and requests more changes),
  PR #649 would need to rebase AGAIN.

### 7. Alternative Not Considered: Direct Patch Without Rebase

Teammate A correctly identifies Option B (add `omit` annotations) as a minimal fix, then
dismisses it as a "workaround." But consider the full picture:

- The minimal fix (2 `omit` lines) immediately unblocks CI
- The reviewer changes (remove Since, redesign semantics) are independent of the rebase
- A full rebase forces resolution of 4+ files of merge conflicts, risking introducing new
  Lean elaboration errors that could be hard to debug
- After the reviewer changes are made AND PR #648 is approved, the rebase will be MUCH
  CLEANER (PR #649 will have fewer overlapping changes with the finalized PR #648)

**Recommendation divergence from Teammate A**: Do NOT attempt a full rebase now. Instead:
1. Fix the 2 lint errors with `omit [DecidableEq Atom] in`  
2. Address ctchou's reviewer requests (remove `snce`, redesign semantics for LTS)
3. Wait for PR #648 to be approved
4. Rebase at that point (much cleaner, correct final base)

---

## Identified Risks

1. **Rebase creates 4+ file conflicts** that may introduce Lean elaboration errors harder to
   diagnose than the original 2-warning lint fix.
2. **PR #648 is not approved** — rebasing onto an unapproved moving target means double-work
   if PR #648 changes again.
3. **Reviewer requests for PR #649 are substantial** — CI passing is necessary but not
   sufficient; `CHANGES_REQUESTED` status blocks merge regardless.
4. **MPL/IPL/CPL API inconsistency** between PRs will cause post-rebase elaboration errors.
5. **Force-push** invalidates review state and wastes CI cache.
6. **`instIsIntuitionisticIntuitionisticCompletion`** may be silently dropped during rebase
   if conflict resolution keeps PR #649's Theory.lean version.

---

## Assumptions to Validate

1. **Is PR #648 the correct base?** The task says "rebase onto updated PR #648" — but ctchou
   hasn't re-approved PR #648 after its update. Is PR #648's current state the intended base,
   or should we wait for re-approval?

2. **Will ctchou's PR #649 review be addressed by the rebase?** No — the rebase does not
   remove `snce` or redesign semantics. The rebase only fixes CI.

3. **Is `instBot_eq`/`instTop_eq` used downstream?** Teammate A concludes they're "likely safe"
   to remove because new files use `.bot` directly. But this should be verified against ALL
   downstream imports, not just the 3 new files.

4. **What does the task owner (benbrastmckie) consider the scope of "fix PR #649"?** Just CI?
   Or full reviewer response?

5. **Does the upstream `hopscotch/lkg-bump` branch matter?** It has a commit `1c0eba77` bumping
   mathlib (after `70c5bf58`). If this gets merged to upstream/main before PR #648/#649 are
   merged, another rebase will be needed.

---

## Potential Pitfalls During Fix

### If doing a full rebase:

1. **Defs.lean conflict auto-resolution**: git may choose PR #648's version (losing
   `instBot_eq`/`instTop_eq` AND the Architecture docblock). Need to manually verify which
   content to keep.

2. **Theory.lean silent regression**: If rebase drops `instIsIntuitionisticIntuitionisticCompletion`
   silently (no Lean error at that exact site), downstream code that relies on it will fail
   later.

3. **3 commits on PR #649 must ALL be rebased**: Each of `5700fedb`, `0afc9d6c`, `5785ebbd`
   touches overlapping files. Commit-by-commit conflict resolution is necessary — the second
   and third commits may introduce NEW conflicts even after the first is resolved.

4. **Lake build time**: After rebase + push, CI takes ~5 minutes. If conflicts were resolved
   incorrectly, finding the error requires re-reading CI logs.

### If doing the minimal fix (omit annotations):

1. Very low risk — `omit [DecidableEq Atom] in` is a well-understood pattern already used
   in `Defs.lean` for `efq_mem_ipl` and `dne_mem_cpl`.
2. Still requires addressing reviewer's substantive concerns before merge is possible.

---

## Overlap Analysis (Files Modified in Both PRs)

All shared-file changes between PR #648 and PR #649 relative to common base `70c5bf58`:

| File | #648 net | #649 net | Same lines touched? |
|------|---------|---------|----------------------|
| `Cslib.lean` | +1 line (Connectives import) | +4 lines (Connectives + 3 new) | Overlap: Connectives import |
| `Connectives.lean` | NEW (+71 lines) | NEW (+116 lines, superset) | Total overlap: PR #649 contains all of PR #648's content plus temporal classes |
| `Defs.lean` | +67/-38 | +85/-28 | Massive overlap: same structural changes to same regions |
| `Basic.lean` | +78/-71 | +82/-70 | Moderate overlap: same impl→imp renames |
| `Theory.lean` | +55/-36 | +23/-23 | Overlap: same removals + PR #648 adds instance PR #649 lacks |
| `references.bib` | +8 | +193 | Minimal: different entries, but Avigad2022 position matters |

**New files unique to PR #649** (no conflict risk):
- `Cslib/Logics/Temporal/Syntax/Formula.lean`
- `Cslib/Logics/LTL/Syntax/Formula.lean`  
- `Cslib/Logics/LTL/Semantics/Satisfies.lean`

---

## Questions That Need Answering

1. **Has benbrastmckie decided to address ctchou's reviewer requests or is this task
   just about CI?** The task description says "resolve CI failure" — if that's all,
   the `omit` fix is sufficient and rebase is not required now.

2. **Will PR #648 be revised further?** ctchou's review of PR #648 is still open. If
   PR #648 changes (e.g., ctchou asks for more reference style changes), rebasing PR #649
   now wastes effort.

3. **Should `Temporal.Formula` keep `snce`?** Reviewer said no. If this is to be removed,
   the temporal formula type changes substantially, which changes what conflicts would exist
   during rebase.

4. **Is `instBot_eq`/`instTop_eq` needed at all?** These are `@[simp, grind =]` lemmas for
   notation unfolding. If no goals in the temporal/LTL files use `⊥`/`⊤` notation
   (they use `.bot` directly), these theorems serve no purpose and should be dropped.

5. **What is the relationship to PR #607 (fmontesi's operator typeclasses)?** The PR
   description mentions coordination with #607. Is there overlap with `Connectives.lean`?

---

## Confidence Level: HIGH

- The CI root cause is precisely identified (lint warnings-as-errors in `Defs.lean`)
- The conflict risk assessment is based on actual `git diff` analysis of both branches
- The PR #648 and #649 review statuses are confirmed via `gh pr view`
- The reviewer's specific requests are documented in the review JSON
- The potential for `instIsIntuitionisticIntuitionisticCompletion` to be silently dropped
  during rebase is a concrete risk from the `git diff` analysis of Theory.lean

One uncertainty: exact git conflict behavior depends on git's 3-way merge algorithm applied
to specific line contexts, which can only be confirmed by actually running the rebase.
