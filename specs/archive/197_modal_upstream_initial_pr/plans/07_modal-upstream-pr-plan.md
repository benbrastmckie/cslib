# Implementation Plan: Scope initial Modal/ upstream PR (~300 LOC)

- **Task**: 197 - Scope initial Modal/ upstream PR (~300 LOC)
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: PR #648 (`feat/propositional-v2`, OPEN) for Connectives.lean foundation
- **Research Inputs**: reports/01_modal-upstream-pr-scope.md, reports/02_literature-grounded-analysis.md, reports/03_team-research.md, reports/04_pr649-comparison-classical-signature.md, reports/06_modal-pr-landscape.md
- **Artifacts**: plans/07_modal-upstream-pr-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Prepare and submit an upstream PR to leanprover/cslib that refactors `Modal/` from the `{atom, not, and, diamond}` signature to the classical-only `{atom, bot, imp, box}` signature, stacking on PR #648 (`feat/propositional-v2`). The PR scope covers four files: `Connectives.lean` (~25 LOC addition of `HasBox`/`ModalConnectives`), `Basic.lean` (formula type refactoring with derived connectives), `Denotation.lean` (updated match cases), and `LogicalEquivalence.lean` (updated `Context` constructors from `{not, andL, andR, diamond}` to `{impL, impR, box}`). Total diff: ~355 insertions / ~222 deletions. PR #648 quality conventions (`## Main definitions`, `## Notation`, BibKey references) are applied proactively to avoid a quality-fix follow-up. The plan is defined as done when the PR is created on GitHub with all CI checks passing and a complete PR description that diplomatically coordinates with all related upstream PRs.

### Research Integration

Five research reports inform this plan (version 4):

- **Report 01** (01_modal-upstream-pr-scope.md): Established the ~291 insertion / ~110 deletion scope for Basic.lean + Denotation.lean. Identified the `ModalConnectives` dependency on Connectives.lean.
- **Report 02** (02_literature-grounded-analysis.md): Discovered PR #647 was CLOSED. Confirmed all 7 BibKeys verified in `references.bib`. Provided Burgess 1984 evidence supporting box-as-primitive.
- **Report 03** (03_team-research.md): Team research confirmed three-file scope (Basic + Denotation + LogicalEquivalence = ~355 LOC). Established that LogicalEquivalence.lean MUST be included because changing Basic.lean constructors breaks upstream's `Context` type. Identified PR #607 alignment opportunity.
- **Report 04** (04_pr649-comparison-classical-signature.md): Compared PR #649 patterns and conventions. Confirmed `Connectives.lean` must be extended with `HasBox`/`ModalConnectives` (~25 LOC). Extracted quality convention requirements (BibKey format, `## Main definitions`, `## Notation` sections). Established the stacking pattern used by PR #649.
- **Report 06** (06_modal-pr-landscape.md, new in v4): Audited the upstream PR landscape as of 2026-06-15. Found no competing modal signature-change PRs. Confirmed PR #607 (fmontesi) is stalled with CHANGES_REQUESTED since 2026-05-29. Recommended stacking on PR #648 directly (not #649) for a two-PR dependency chain. Identified `HasImpl` vs `HasImp` naming conflict with PR #607, noting `HasBox` is compatible. Established diplomatic framing strategy for PR description.

### Revision Notes (v3 to v4)

This revision incorporates three critical changes:

1. **Stacking target changed from PR #649 to PR #648**. The Modal PR now stacks on `feat/propositional-v2` (PR #648) rather than `feat/temporal-formula-propositional` (PR #649). This follows the same pattern as PR #649 itself -- branching from #648's head and carrying its Connectives.lean changes. The result is a two-PR dependency chain (#648 -> Modal) instead of three (#648 -> #649 -> Modal), keeping the Modal PR independent of temporal additions and simpler to review.

2. **PR description is a first-class deliverable**. Report 06 and the revision reason emphasize that the PR description must deftly coordinate between multiple active PRs. PR #648's description provides the tone model -- structured, literature-backed, diplomatic about competing approaches, with clear sections for design rationale, relationship to other PRs, and contribution roadmap. The description must explicitly frame the relationship to PRs #607, #648, #649, and the merged PRs #528/#535.

3. **Citation fixes from task 201 are already merged**. The Blackburn2001 and ChagrovZakharyaschev1997 BibKey corrections are now in main. The PR description should reference the proof-theoretic argument for box-as-primitive (necessitation and K are pure proof rules on box) without needing separate citation fix work.

### Prior Plan Reference

Prior plan v3 (plans/05_modal-upstream-pr-plan.md) had 4 phases with 3 hours effort. It stacked on PR #649 and treated the PR description as a subtask within Phase 4. This revision changes the stacking target to PR #648, elevates the PR description to its own phase with detailed diplomatic requirements, and integrates findings from the PR landscape audit (Report 06).

### Roadmap Alignment

This plan advances the following from `specs/ROADMAP.md`:
- Modal module (`Logics/Modal/`) upstream contribution -- the formula type refactoring is a prerequisite for all subsequent Modal/ PRs
- Foundations/Logic/Connectives.lean extension with modal typeclass hierarchy

## Goals & Non-Goals

**Goals**:
- Extend `Connectives.lean` with `HasBox` and `ModalConnectives` (~25 LOC)
- Refactor `Basic.lean` to `{atom, bot, imp, box}` primitives with derived connectives
- Update `Denotation.lean` match cases for new primitives
- Update `LogicalEquivalence.lean` Context constructors to `{impL, impR, box}`
- Apply PR #648 quality conventions proactively (docstring sections, BibKey refs)
- Fix import path `Cslib.Foundations.Data.Relation` -> `Cslib.Foundations.Relation.Euclidean`
- Pass all CI checks on the PR branch
- Create `pr-description.md` with diplomatic coordination language modeled on PR #648's tone
- Submit PR stacked on PR #648's branch (`feat/propositional-v2`)

**Non-Goals**:
- Including `FromPropositional.lean` (deferred to follow-up PR)
- Including `Modal/Metalogic/` files (separate contribution track)
- Modifying upstream's `Cube.lean` (no changes needed; verify it still compiles)
- Fully resolving the PR #607 conflict (requires community consensus via Zulip)
- Adding `BimodalConnectives` to Connectives.lean (deferred until temporal PR merges)
- Stacking on PR #649 (temporal additions are independent of this PR)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #648 not merged when Modal PR is ready | H | M | Stack on `feat/propositional-v2` branch; note dependency in PR description; Modal PR can merge as soon as #648 merges without waiting for #649 |
| LogicalEquivalence instance regression (upstream downstream imports) | M | L | Search all upstream `Cslib/Logics/Modal/*.lean` for imports of `LogicalEquivalence`; verify no downstream breakage |
| Missing `## Main definitions`/`## Notation` sections triggers quality review | M | H | Apply proactively following PR #648 template before submission |
| `grind =_` vs `grind =` on `derivation_def` breaks Cube.lean | L | L | Build `Cslib.Logics.Modal.Cube` on PR branch before submission |
| PR #607 (fmontesi) activity resumes with incompatible `HasImpl` naming | H | L | PR #607 is stalled with CHANGES_REQUESTED since May 29; frame Modal PR description to address chenson2018's consolidation feedback proactively |
| PR description tone perceived as dismissive of fmontesi's work | H | M | Model tone on PR #648; explicitly acknowledge fmontesi's foundational PRs #528/#535; frame refactoring as building on his work, not replacing it |
| Connectives.lean addition conflicts with PR #648 changes | M | L | Stack on PR #648 branch directly; addition is purely additive (new classes only) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Create PR Branch and Prepare Connectives.lean Extension [NOT STARTED]

**Goal**: Create a feature branch stacked on PR #648's branch (`feat/propositional-v2`) and add `HasBox`/`ModalConnectives` to `Connectives.lean`.

**Tasks**:
- [ ] Fetch upstream and origin remotes: `git fetch upstream && git fetch origin`
- [ ] Create branch `feat/modal-formula-classical` from `origin/feat/propositional-v2` (PR #648's branch)
- [ ] Verify `Cslib/Foundations/Logic/Connectives.lean` exists on the base branch with `HasBot`, `HasImp`, `PropositionalConnectives`
- [ ] Add `HasBox` class (~8 LOC) with docstring citing Blackburn2001 Ch. 1 and ChagrovZakharyaschev1997 S. 1.1
- [ ] Add `ModalConnectives` class extending `PropositionalConnectives` and `HasBox` (~6 LOC) with docstring explaining classical-only signature rationale (necessitation and K are pure proof rules on box)
- [ ] Verify `Connectives.lean` compiles: `lake build Cslib.Foundations.Logic.Connectives`
- [ ] Fix import path in `Basic.lean`: replace `Cslib.Foundations.Data.Relation` with `Cslib.Foundations.Relation.Euclidean`
- [ ] Add `import Cslib.Foundations.Logic.Connectives` to `Basic.lean` if not already present
- [ ] Copy local `Basic.lean`, `Denotation.lean`, `LogicalEquivalence.lean` to the branch (overwriting upstream versions)
- [ ] Verify `Basic.lean` has `ModalConnectives` instance registering `{bot, imp, box}`
- [ ] Check `grind =_` vs `grind =` attribute on `derivation_def` -- use whichever matches upstream convention

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` -- add `HasBox`, `ModalConnectives` (~25 LOC)
- `Cslib/Logics/Modal/Basic.lean` -- import path fix, overwrite with local version
- `Cslib/Logics/Modal/Denotation.lean` -- overwrite with local version
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- overwrite with local version

**Verification**:
- Branch exists based on PR #648's `feat/propositional-v2` branch (not #649)
- `Connectives.lean` contains `HasBox` and `ModalConnectives`
- No references to `Cslib.Foundations.Data.Relation` remain in modal files

---

### Phase 2: Apply Quality Conventions and Docstring Polish [NOT STARTED]

**Goal**: Ensure all four files meet PR #648 quality conventions: `## Main definitions`, `## Notation`, `## References` sections with BibKey format, and Unicode in derived operator docs.

**Tasks**:
- [ ] Verify `Basic.lean` module docstring contains `## Main definitions` section listing: `Proposition`, `Model`, `Satisfies`, `Judgement`, `TheoryEq`, axiom theorems (K, T, B, 4, 5, D)
- [ ] Verify `Basic.lean` module docstring contains `## Notation` section listing all scoped operators with precedence
- [ ] Verify `Basic.lean` module docstring contains `## References` section using BibKey format: `* [Author, *Title*][BibKey]`
- [ ] Verify all inline references use BibKey format (e.g., `[Blackburn2001]` not prose)
- [ ] Verify derived operator docstrings include Unicode notation (e.g., `diamond phi`, `neg phi`)
- [ ] Apply same quality conventions to `Denotation.lean`: add `## Main definitions` section listing `Proposition.denotation`, `satisfies_mem_denotation`, `theoryEq_denotation_eq`
- [ ] Apply same quality conventions to `LogicalEquivalence.lean`: verify existing `## Main Definitions` and `## Design Notes` sections
- [ ] Add `## Main definitions` to `Connectives.lean` addition (list `HasBox`, `ModalConnectives`)
- [ ] Verify copyright headers: Basic.lean has "Fabrizio Montesi, Benjamin Brast-McKie" (co-authored); Denotation.lean has "Fabrizio Montesi, Benjamin Brast-McKie"; LogicalEquivalence.lean has "Benjamin Brast-McKie"
- [ ] Check that `references.bib` contains all cited BibKeys: `Blackburn2001`, `ChagrovZakharyaschev1997`, `Johansson1937`

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- docstring sections if missing
- `Cslib/Logics/Modal/Denotation.lean` -- docstring sections if missing
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- docstring sections if needed
- `Cslib/Foundations/Logic/Connectives.lean` -- docstring additions for new classes

**Verification**:
- All four files have `## Main definitions` in module docstrings
- `Basic.lean` has `## Notation` and `## References` sections
- No prose-style references remain (all converted to BibKey format)

---

### Phase 3: CI Verification and Cube.lean Compatibility [NOT STARTED]

**Goal**: Run the full CI pipeline on the PR branch to confirm all files compile and pass checks.

**Tasks**:
- [ ] Run `lake build Cslib.Foundations.Logic.Connectives` -- must succeed
- [ ] Run `lake build Cslib.Logics.Modal.Basic` -- must succeed
- [ ] Run `lake build Cslib.Logics.Modal.Denotation` -- must succeed
- [ ] Run `lake build Cslib.Logics.Modal.LogicalEquivalence` -- must succeed
- [ ] Run `lake build Cslib.Logics.Modal.Cube` -- must still compile unchanged
- [ ] Run `lake test` -- CslibTests suite must pass
- [ ] Run `lake exe checkInitImports` -- verify root import file is correct
- [ ] Run `lake exe lint-style` -- pass style linting
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` on modified files
- [ ] If `Cube.lean` fails: investigate `grind =_` vs `grind =` direction; fix `derivation_def` attribute
- [ ] If any lint failures: fix style issues
- [ ] If import issues: adjust paths to match upstream conventions
- [ ] Search upstream `Cslib/Logics/Modal/*.lean` for imports of `LogicalEquivalence` to verify no regression
- [ ] Create clean commit(s) with message: `feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}`

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- Any file requiring CI fixes (import paths, lint issues, style fixes)
- `Cslib.lean` -- may need import line adjustments if `checkInitImports` requires it

**Verification**:
- `lake build` for all four modified files exits 0
- `lake build Cslib.Logics.Modal.Cube` exits 0
- `lake exe checkInitImports` exits 0
- `lake exe lint-style` exits 0
- `lake test` passes
- No downstream `LogicalEquivalence` import regressions

---

### Phase 4: PR Description and Submission [NOT STARTED]

**Goal**: Write a diplomatically crafted PR description and submit the PR via GitHub CLI, stacked on PR #648.

The PR description is a critical deliverable. It must coordinate between multiple active PRs using a tone modeled on PR #648's description -- structured, literature-backed, and diplomatic about competing approaches.

**Tasks**:
- [ ] Create `specs/197_modal_upstream_initial_pr/pr-description.md` with the following sections:

  **Title**: `feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}`

  **Summary section**: Three-sentence description of what the PR does (refactors Modal/Proposition to classical primitives, updates Denotation and LogicalEquivalence, extends Connectives.lean with HasBox/ModalConnectives).

  **"Design Rationale" section**:
  - "Why box, not diamond?" subsection: The proof-theoretic justification -- necessitation (if provable phi then provable box phi) and the K axiom (box (phi -> psi) -> box phi -> box psi) are pure proof rules stated directly over box. Diamond is definable as `neg (box (neg phi))`. This mirrors the propositional case where `{bot, imp}` are primitive and `{neg, or, and}` are derived. Cite Blackburn2001, ChagrovZakharyaschev1997, and note that classical modal logic textbooks universally treat box as the fundamental modality.
  - "Why bot and imp as primitives?" subsection: Same argument as PR #648 -- substitution stability, constraint-free derived connectives.
  - Literature citations: Blackburn2001, ChagrovZakharyaschev1997, Burgess1984.

  **"Relationship to Other PRs" section** (critical -- must be diplomatic):
  - **PR #648** (`feat/propositional-v2`): "This PR stacks on #648, which introduces the `Connectives.lean` typeclass hierarchy (`HasBot`, `HasImp`, `PropositionalConnectives`). We extend `Connectives.lean` with `HasBox` and `ModalConnectives` for the modal layer." Note the dependency and request sequential review.
  - **PR #649** (`feat/temporal-formula-propositional`): "PR #649 extends the same `Connectives.lean` with temporal connectives (`HasUntil`, `HasSince`, `TemporalConnectives`). This Modal PR and #649 are siblings -- both stack independently on #648, and neither depends on the other." Clarify the independent relationship.
  - **PR #607** (`feat(Logic): logical operators`, fmontesi): Frame diplomatically. Acknowledge that #607 introduces per-operator typeclasses covering similar ground. Note that our `Connectives.lean` consolidates this into a single file (as suggested in chenson2018's review comment on #607). The only naming difference is `HasImpl`/`impl` vs `HasImp`/`imp`; `HasBox`/`box` is identical. Note the `imp` naming aligns with CSLib's Bimodal and Temporal formula types and with constructor/rule-name prefixes (`impI`/`impE`). If #607 moves forward, updating `HasImpl` to `HasImp` is a one-line change.
  - **PRs #528 and #535** (fmontesi, MERGED): Acknowledge fmontesi's foundational work establishing the Modal/ module. Frame our refactoring as building on PRs #528/#535 -- preserving all axiom theorems, model/satisfaction infrastructure, and logical equivalence results while modernizing the primitive set.

  **"Breaking Changes" section**: Exact constructor renames (`not` -> derived `neg`, `and` -> derived `and`, `diamond` -> derived `diamond`; Context constructors `{notC, andL, andR, diamondC}` -> `{impL, impR, box}`).

  **"Changed Files" section**: Per-file summaries.

  **"Contribution Roadmap" section**: Show planned follow-up PRs (FromPropositional, Metalogic, etc.).

  **"AI Tools Used" section**: Same disclosure as PR #648.

- [ ] Push branch to origin: `git push -u origin feat/modal-formula-classical`
- [ ] Submit PR via `gh pr create` with base branch set to `feat/propositional-v2` (PR #648's branch)
- [ ] Verify PR description renders correctly on GitHub
- [ ] Record the PR URL in pr-description.md

**Timing**: 60 minutes

**Depends on**: 3

**Files to modify**:
- `specs/197_modal_upstream_initial_pr/pr-description.md` -- create PR description artifact

**Verification**:
- PR is created and visible on GitHub
- PR description contains all required sections including diplomatic "Relationship to Other PRs"
- Base branch is set to `feat/propositional-v2` (PR #648's branch, NOT #649)
- PR description tone matches PR #648 (structured, literature-backed, acknowledges fmontesi)
- All CI checks pass on the PR
- PR URL is recorded in task artifacts

---

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Connectives` succeeds on PR branch
- [ ] `lake build Cslib.Logics.Modal.Basic` succeeds on PR branch
- [ ] `lake build Cslib.Logics.Modal.Denotation` succeeds on PR branch
- [ ] `lake build Cslib.Logics.Modal.LogicalEquivalence` succeeds on PR branch
- [ ] `lake build Cslib.Logics.Modal.Cube` succeeds (unchanged file still compiles)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `lake shake` reports no unused imports in modified files
- [ ] `ModalConnectives` instance resolves correctly with `HasBox` from extended Connectives.lean
- [ ] No references to local-only import paths remain (especially `Cslib.Foundations.Data.Relation`)
- [ ] PR description is complete and accurately reflects the diff
- [ ] PR description diplomatically coordinates with PRs #607, #648, #649, #528, #535
- [ ] All BibKey citations in Lean files have corresponding entries in `references.bib`

## Artifacts & Outputs

- `specs/197_modal_upstream_initial_pr/plans/07_modal-upstream-pr-plan.md` (this plan)
- `specs/197_modal_upstream_initial_pr/pr-description.md` (PR description for submission)
- Feature branch `feat/modal-formula-classical` stacked on PR #648's branch
- GitHub PR URL (recorded in task artifacts after submission)

## Rollback/Contingency

If PR #648 has not merged and the stacking causes issues:
1. Rebase the Modal PR branch onto `upstream/main` directly
2. Bundle the `HasBox`/`ModalConnectives` additions into the PR (already additive, ~25 LOC)
3. Note in PR description that `Connectives.lean` additions depend on PR #648's `PropositionalConnectives`

If CI fails on the PR branch:
1. Check import path mismatches -- ensure `Cslib.Foundations.Relation.Euclidean` is used
2. Check if `DecidableEq`/`BEq` deriving fails on upstream's Lean version -- remove deriving clause if needed
3. If `Cube.lean` fails, investigate `grind =_` vs `grind =` direction change on `derivation_def`

If PR #607 merges before this PR with incompatible primitives:
1. Rebase onto PR #607's merged state
2. Adapt formula type to coexist with PR #607's operator typeclasses
3. Present our approach as an alternative refactoring in the Zulip discussion

If PR description tone is criticized:
1. Revise diplomatic language per reviewer feedback
2. Strengthen acknowledgment of fmontesi's contributions
3. Seek direct feedback from fmontesi on the consolidation approach via Zulip
