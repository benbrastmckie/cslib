# Research Report: Task #170

**Task**: 170 - Submit Sub-PR 3.1+3.2: Temporal syntax (Formula + utilities)
**Started**: 2026-06-12T22:30:00Z
**Completed**: 2026-06-12T23:00:00Z
**Effort**: ~1.5 hours (branch creation + CI + PR submission)
**Dependencies**: Task 138 (Connectives.lean / PR #635 must merge upstream first)
**Sources/Inputs**: Codebase (fork main, pr1/foundations-logic, pr3/temporal-formula, upstream/main), GitHub API (PRs #633, #635, #607), CONTRIBUTING.md, CI workflow
**Artifacts**: specs/170_submit_subpr_3_1_3_2_temporal_syntax/reports/01_pr-submission-research.md
**Standards**: report-format.md, subagent-return.md

---

## Executive Summary

- **Connectives.lean (PR #635) is NOT yet merged upstream** — the temporal formula PR has a hard dependency that must be resolved first or the branch must stack on PR #635's branch
- **Formula.lean imports `Cslib.Foundations.Logic.Connectives`** for `TemporalConnectives`; without it the file will not compile on upstream/main
- **Branch strategy**: Create `pr3/temporal-syntax` from `refactor/proposition-lukasiewicz` (the PR #635 branch) so the dependency is satisfied, and mark in the PR description that it depends on PR #635
- **Scope clarification**: State.json describes Sub-PR 3.1+3.2 (all 4 syntax files: Formula + Context + BigConj + Subformulas); the user task instruction text says "Sub-PR 3.1: Formula.lean only" — recommend submitting all 4 as a single PR since Context/BigConj/Subformulas only depend on Formula.lean and add 401 lines, keeping the PR under ~1000 lines
- **references.bib needs 2 new entries**: Kamp1968 and Gabbay1980 (Formula.lean cites both informally; the citation format must be updated to BibKey format `[Author, *Title*][BibKey]`)
- **CI**: lake shake is disabled in CI; the 4 required checks are lake build (wfail/iofail), mk_all --check --module, checkInitImports, and lint-style-action

---

## Context & Scope

This task covers preparing and submitting a clean PR for the Temporal logic syntax files from the fork's `Cslib/Logics/Temporal/Syntax/` directory. The scope is:

- **Formula.lean** (582 lines): Core temporal formula inductive type, BEq/Countable/Denumerable instances, complexity/depth measures, derived operators, swap duality, atoms function
- **Context.lean** (131 lines): Formula lists for proof contexts
- **BigConj.lean** (52 lines): Big conjunction fold over formula lists
- **Subformulas.lean** (218 lines): Subformula closure

Total: ~983 lines across 4 files.

The research decision whether to submit all 4 vs Formula only is resolved in the Recommendations section.

---

## Findings

### 1. Upstream State

**Confirmed**: `upstream/main` does NOT contain:
- `Cslib/Foundations/Logic/Connectives.lean`
- `Cslib/Logics/Temporal/Syntax/Formula.lean` (or any Logics/Temporal/Syntax files)

`upstream/main` Cslib.lean contains only 1 Temporal reference: `Cslib.Foundations.Data.OmegaSequence.Temporal`. The Logics/Temporal namespace is entirely absent from upstream.

The upstream/main Cslib.lean (149 lines) ends with:
```
public import Cslib.Logics.Modal.Basic ... (4 Modal entries)
public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.MachineLearning.PACLearning.Defs ... (3 ML entries)
public import Cslib.Probability.PMF
```

### 2. PR #635 (Connectives.lean / Sub-PR 1.1.1) Status

**State**: OPEN (not merged)
**Branch**: `benbrastmckie:refactor/proposition-lukasiewicz`
**URL**: https://github.com/leanprover/cslib/pull/635
**Reviewers**: fmontesi, arademaker, chenson2018 (all Requested), eric-wieser (Commented)
**Review comment from eric-wieser**: "Here you could co-opt mathlib's `Bot` and `HImp` classes" (file: Connectives.lean, line 56 — the `HasBot` class definition)

This is a blocking dependency. Formula.lean imports `Cslib.Foundations.Logic.Connectives` and uses `TemporalConnectives` from it. Without Connectives.lean on the base branch, Formula.lean will not compile.

**Risk**: PR #607 (`fmontesi/connectives`) adds its own operator typeclass files under `Cslib/Foundations/Logic/Operators/` (And.lean, Box.lean, Diamond.lean, Iff.lean, Impl.lean, Not.lean, Or.lean, Tensor.lean). If #607 merges before #635, there could be a naming/interface conflict. However, #607 has not been approved either and has comments from multiple reviewers requesting changes.

### 3. PR #633 (pr1/foundations-logic) Status

**State**: OPEN (not merged)
**Branch**: `benbrastmckie:pr1/foundations-logic`
**Note**: PR #633 is the large "everything" PR (7,894 additions). Reviewers have asked for smaller PRs. This is the context for the sub-PR decomposition strategy. It does NOT need to be merged for the temporal syntax PR to work — only Connectives.lean (PR #635) needs to merge first.

### 4. Formula.lean Dependencies

```lean
public import Cslib.Init                              -- ✓ on upstream/main
public import Cslib.Foundations.Logic.Connectives     -- ✗ NOT on upstream/main (PR #635)
public import Mathlib.Logic.Encodable.Basic           -- ✓ available (Mathlib)
public import Mathlib.Logic.Denumerable               -- ✓ available (Mathlib)
public import Mathlib.Data.Finset.Basic               -- ✓ available (Mathlib)
```

Formula.lean uses from Connectives.lean:
- `TemporalConnectives` typeclass (extends `PropositionalConnectives`, `HasUntil`, `HasSince`)
- Used in: `instance : TemporalConnectives (Formula Atom) where`

The 3 utility files (Context.lean, BigConj.lean, Subformulas.lean) only import `Cslib.Logics.Temporal.Syntax.Formula` — no additional external dependencies.

### 5. Branch Strategy

**Recommended approach**: Create `pr3/temporal-syntax` from `refactor/proposition-lukasiewicz` (the PR #635 branch), NOT from upstream/main.

Rationale:
- `refactor/proposition-lukasiewicz` is the clean sub-PR branch that already has Connectives.lean in its minimal form (6 files changed: Connectives.lean NEW, InferenceSystem.lean, Defs.lean, NaturalDeduction/Basic.lean, Cslib.lean, references.bib)
- The PR description for the temporal syntax PR should state it depends on PR #635 and link to it
- Alternative: Include Connectives.lean directly in the temporal PR, but this would duplicate the changes from PR #635 and is cleaner to keep them separate
- Alternative rejected: Create from upstream/main is not viable because Connectives.lean is required

**What the PR diff will show** (against upstream/main):
- Changes from PR #635 base + temporal syntax additions
- GitHub shows the diff against the base branch; if the PR is set to depend on PR #635, the diff would ideally show only the temporal additions

**Note on dependency PRs in cslib**: CSLib accepts stacked PRs where one PR's base is another open PR's branch. The PR description should clearly state "Depends on PR #635."

### 6. Cslib.lean Barrel Entries

The PR should add 4 entries to Cslib.lean in alphabetical position after `Logics.Propositional.NaturalDeduction.Basic` and before `MachineLearning.PACLearning.Defs` (since "T" comes after "P" but before "M" is already passed — actually T > P > M alphabetically so Temporal goes between Propositional and MachineLearning):

```lean
public import Cslib.Logics.Temporal.Syntax.BigConj
public import Cslib.Logics.Temporal.Syntax.Context
public import Cslib.Logics.Temporal.Syntax.Formula
public import Cslib.Logics.Temporal.Syntax.Subformulas
```

Position in upstream Cslib.lean: after line 145 (`Logics.Propositional.NaturalDeduction.Basic`), before line 146 (`MachineLearning.PACLearning.Defs`).

If the base branch is `refactor/proposition-lukasiewicz`, that branch's Cslib.lean already has `Cslib.Foundations.Logic.Connectives` added, so only the 4 Temporal entries need to be inserted.

### 7. references.bib Entries Needed

Formula.lean's `## References` section uses **informal format** (plain text, no BibKey brackets):
```
- Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
- Gabbay, D., Pnueli, A., Shelah, S., and Stavi, J. (1980). On the temporal analysis of fairness.
  In *Proceedings of the 7th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages*,
  pp. 163–173. ACM.
```

**Required actions**:
1. Add BibTeX entries `Kamp1968` and `GabbayPnueliShelahStavi1980` to `references.bib`
2. Update the `## References` section in Formula.lean to use BibKey format:
   ```
   * [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]
   * [D. Gabbay, A. Pnueli, S. Shelah, J. Stavi, *On the temporal analysis of fairness*][GabbayPnueliShelahStavi1980]
   ```

The CSLib citation standard (confirmed from existing files like Connectives.lean, Modal/Basic.lean, Propositional/Defs.lean) requires `* [Author, *Title*][BibKey]` format in `## References` sections.

Neither `Kamp1968` nor `GabbayPnueliShelahStavi1980` (nor any Gabbay/Kamp/Pnueli entry) exists in `references.bib`. All need to be added.

**Context, BigConj, Subformulas**: None of these files have a `## References` section — no bib changes needed for them.

### 8. CI Requirements

From `.github/workflows/lean_action_ci.yml`:
```yaml
- lean-action with build-args: "--wfail --iofail"   # lake build, warnings = error
- lean-action with test-args: "--wfail --iofail"    # lake test
- lake exe mk_all --check --module                  # barrel completeness check
- lake exe checkInitImports                         # Init imports check
- lint-style-action (mode: check)                   # style linting
# lake shake is COMMENTED OUT in CI
```

**Key gotcha**: `--wfail --iofail` means any Lean warning fails the build. Formula.lean must produce zero warnings.

**mk_all check**: The barrel file Cslib.lean must list exactly the files in the Cslib.* glob (no missing, no extra). Adding the 4 Syntax entries to Cslib.lean satisfies this.

**checkInitImports**: Each file must `import Cslib.Init` (or `public import`). Formula.lean has `public import Cslib.Init` via `public import Cslib.Foundations.Logic.Connectives` which re-exports it — needs verification that this satisfies the check. Context/BigConj/Subformulas have it via `public import Cslib.Logics.Temporal.Syntax.Formula`.

**lint-style**: Line length, copyright headers, docstring format. Formula.lean's 582-line file should be fine but the `## References` section needs BibKey format.

### 9. Existing pr3/temporal-formula Branch Assessment

The local branch `pr3/temporal-formula` (also pushed to `origin/pr3/temporal-formula`) carries the **entire fork diff** from upstream/main — 80+ files including all of pr1/foundations-logic, all temporal and bimodal work. This branch is **unsuitable** as a PR submission branch.

A fresh clean branch is required.

---

## Decisions

1. **Scope**: Submit all 4 syntax files (Formula + Context + BigConj + Subformulas) as a single PR. All utility files have exactly one dependency (Formula.lean), keeping the diff clean and reviewable at ~983 lines.

2. **Base branch**: Use `refactor/proposition-lukasiewicz` as the base (PR #635's branch). This is the minimal base that satisfies the Connectives.lean dependency.

3. **Branch name**: `pr3/temporal-syntax` (as specified in state.json) — cleaner than the current `pr3/temporal-formula`.

4. **Citation format**: Update Formula.lean references from informal text to BibKey format and add Kamp1968 and GabbayPnueliShelahStavi1980 to references.bib.

5. **PR title**: `feat(Logics/Temporal/Syntax): temporal formula type and syntax utilities` (follows `feat` category pattern, under 70 chars).

---

## Risks & Mitigations

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| PR #635 blocked by eric-wieser's Bot/HImp suggestion | Medium | Address comment by either co-opting Mathlib's Bot/HImp or explaining why our approach is preferred. This affects `Connectives.lean` not `Formula.lean`. |
| PR #607 merges before #635 creating interface conflict | Low | #607 uses per-operator files, not a single Connectives.lean; if it merges, we'd need to update Formula.lean imports. Monitor #607 status. |
| --wfail fails due to warnings in Formula.lean | Low | Formula.lean is currently on main branch compiling cleanly. Verify on the PR branch. |
| checkInitImports fails | Low | All files either directly import Cslib.Init or transitively via public imports. Verify on PR branch. |
| PR #633 reviewer feedback about AI usage | Medium | PR description must include clear AI disclosure per CONTRIBUTING.md section on AI. |
| Alphabetical order in Cslib.lean wrong | Low | Temporal (T) goes after Propositional (P) alphabetically; double-check position. |
| Connectives.lean not approved before temporal PR is reviewed | High | Temporal PR will not be mergeable until #635 merges. This is expected and should be stated in the PR. |

---

## Context Extension Recommendations

None needed — the PR submission workflow is well-documented in existing task specs.

---

## Appendix

### Search queries used
- `git show remotes/upstream/main:Cslib.lean`
- `git show remotes/upstream/main:Cslib/Foundations/Logic/Connectives.lean`
- `git diff remotes/upstream/main pr3/temporal-formula --name-only`
- `git diff remotes/upstream/main refactor/proposition-lukasiewicz --name-only`
- `gh pr list --repo leanprover/cslib`
- `gh pr view 635 --repo leanprover/cslib`
- `gh api repos/leanprover/cslib/pulls/635/comments`
- `grep -rn "\[.*\]\[" /home/benjamin/Projects/cslib/Cslib/`

### Key file paths
- Formula.lean: `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Formula.lean` (582 lines)
- Context.lean: `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Context.lean` (131 lines)
- BigConj.lean: `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/BigConj.lean` (52 lines)
- Subformulas.lean: `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Subformulas.lean` (218 lines)
- Connectives.lean: `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Connectives.lean`
- references.bib: `/home/benjamin/Projects/cslib/references.bib`
- CI workflow: `/home/benjamin/Projects/cslib/.github/workflows/lean_action_ci.yml`

### PR #635 Connectives.lean diff size: 6 files, 292 lines

### BibTeX entries needed

**Kamp1968**:
```bibtex
@phdthesis{Kamp1968,
  author    = {Hans Kamp},
  title     = {Tense Logic and the Theory of Linear Order},
  school    = {University of California, Los Angeles},
  year      = {1968},
}
```

**GabbayPnueliShelahStavi1980**:
```bibtex
@inproceedings{GabbayPnueliShelahStavi1980,
  author    = {Dov Gabbay and Amir Pnueli and Saharon Shelah and Jonathan Stavi},
  title     = {On the Temporal Analysis of Fairness},
  booktitle = {Proceedings of the 7th Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages},
  pages     = {163--173},
  year      = {1980},
  publisher = {ACM},
}
```
