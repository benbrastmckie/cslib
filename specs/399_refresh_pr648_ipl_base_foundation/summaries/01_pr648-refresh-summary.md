# Implementation Summary: Task #399 — Refresh PR #648 (IPL-Base Foundation)

- **Task**: 399
- **Status**: [PR READY]
- **Date**: 2026-06-29
- **Session**: sess_1782673164_f5576d_399
- **Phases**: 4/4 completed

---

## What Was Done

### Phase 1: Cherry-Pick Recipe and Precise File Subset

Confirmed the following against live repo state:

- Upstream/main HEAD: `2772f421` — 11 commits ahead of merge base `70c5bf58`, none
  touching propositional files
- Theory.lean in upstream uses the OLD `IsIntuitionistic Atom (S : InferenceSystem)
  [Bot Atom]` API — incompatible with new Defs.lean (confirmed deletion target)
- Exact import to remove from Defs.lean: `public import Cslib.Foundations.Logic.Connectives`
  (line 10)
- Exact instance block to remove from Defs.lean: lines 113–124
  (`PropositionalConnectives`, `HasAnd`, `HasOr` instances)
- Basic.lean: taken as-is from fork main (Zulip link confirmed at line 78)
- Theory.lean import in upstream barrel: confirmed at line 158 of Cslib.lean
- 7 bib entries absent from upstream: Church1956, ChagrovZakharyaschev1997,
  Johansson1937, Gentzen1935, Prawitz1965, TroelstraVanDalen1988, SorensenUrzyczyn2006
  (note: Avigad2022 is in fork main bib but is NOT cited in the cherry-pick files)

Artifacts created:
- `cherry-pick-recipe.md` — exact change list + Option A rationale + local verification results
- `prepare-foundation-branch.sh` — executable, idempotent, no-push, no-remote-CI script

### Phase 2: Local Build Verification

Created throwaway git worktree at `../cslib-foundation-verify` from upstream/main,
applied all 5 recipe steps manually, ran full build:

| Check | Result |
|-------|--------|
| `lake build Cslib.Logics.Propositional.Defs` | GREEN (497 jobs) |
| `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` | GREEN (592 jobs) |
| `lake build Cslib` (full barrel) | GREEN (2741 jobs) |
| `lake exe checkInitImports` | GREEN (exit 0) |
| `lake exe lint-style` on touched files | GREEN (exit 0) |

Worktree and `verify/propositional-foundation` branch removed after verification.
Fork main unchanged.

### Phase 3: PR Description and Zulip Response Drafts

- `pr-description.md`: PR body draft with HUMAN-AUTHOR-REQUIRED banner. Covers:
  - Waring flag (a): connective typeclasses excluded, coordination with PR #607
  - Waring flag (b): references restored, Zulip link present
  - Theory.lean deletion decision (reviewer-visible, Option A rationale)
  - IPL-as-base design note reference
  - Deferred scope table (derived rules, Hilbert, semantics, sequent, tableau)
  - Namespace note (task 387, pending)
  - Build verification claims (reconciled with Phase 2 results)
  - User Next Steps block
- `zulip-response.md`: Zulip reply draft with HUMAN-AUTHOR-REQUIRED banner.
  - Addresses efq implementation (task 398 complete, CI green)
  - Confirms connective typeclasses removed (Waring flag a)
  - Confirms references + Zulip link present (Waring flag b)
  - Notes Theory.lean deletion
  - Welcomes Waring's formal review

### Phase 4: Final Verification and [PR READY] Transition

- All 4 artifacts confirmed present and consistent
- Build claims in pr-description.md reconciled with Phase 2 results
- Script verified: no `git push`, no `gh`, no remote CI invocation
- Task 399 transitioned to [PR READY]

---

## Artifacts Produced

| Artifact | Path | Purpose |
|----------|------|---------|
| Cherry-pick recipe | `cherry-pick-recipe.md` | Exact file changes, Option A rationale, build results |
| Preparation script | `prepare-foundation-branch.sh` | Creates local branch, applies changes, stages (no push) |
| PR description | `pr-description.md` | GitHub PR body draft (HUMAN-AUTHOR-REQUIRED) |
| Zulip response | `zulip-response.md` | Zulip reply draft (HUMAN-AUTHOR-REQUIRED, Zulip AI policy) |

---

## Key Findings

- The foundation diff builds cleanly off upstream/main with the new toolchain (v4.32.0-rc1)
- Theory.lean deletion (Option A) is the only viable path — the old `[Bot Atom]` API is
  fundamentally incompatible with the new `IsIntuitionistic (T : Theory Atom)` API
- 7 bib entries are needed (not 6 as originally estimated); Church1956 and
  ChagrovZakharyaschev1997 are cited in the trimmed Defs.lean
- Avigad2022 is NOT cited in the cherry-pick files (though present in fork main bib)
- The impl→imp rename has no upstream consumers outside Theory.lean (which is deleted)

---

## User Next Steps

1. Review and finalize `pr-description.md` and `zulip-response.md` in your own words
   (Zulip AI policy — see banners in both files)
2. Run `bash specs/399_refresh_pr648_ipl_base_foundation/prepare-foundation-branch.sh`
   to create `feat/propositional-foundation` branch locally
3. Verify the staged diff (`git diff --staged`), commit, then run `/pr 399`
4. Post Zulip response to thread 606970606 in your own words after the PR is live
