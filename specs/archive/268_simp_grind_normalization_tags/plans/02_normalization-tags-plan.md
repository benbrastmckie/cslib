# Implementation Plan: Task #268

- **Task**: 268 - simp_grind_normalization_tags
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/268_simp_grind_normalization_tags/reports/01_team-research.md
- **Artifacts**: plans/02_normalization-tags-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add `@[simp, scoped grind =]` co-tags to 16 definitional/structural lemmas across 4 files in the Foundations, Temporal, and Bimodal layers. Additionally, optionally add `@[scoped grind =]` to 4 unwrapped iff characterization lemmas in Modal/Basic.lean. All changes are purely additive (no existing simp behavior changes) and follow the established three-tier co-tagging convention. The GrindLint test may require new skip entries.

### Research Integration

The team research report (4 teammates, 3 completed) established:
- **Three-tier convention**: `@[simp, scoped grind =]` for structural equalities, `@[scoped grind =]` for iff characterizations, `@[scoped grind]` for inductive case-splits
- **16 confirmed upgrade targets** across ListImplication, BigConj, FromPropositional, and TemporalEmbedding (all rfl-proved structural equalities currently tagged `@[simp]` only)
- **4 optional targets** in Modal/Basic.lean (unwrapped iff lemmas with no current tags; wrapped versions already tagged)
- **Zero simp loop risk**: all derived connectives are `abbrev` (kernel-transparent), no inverse lemma pairs exist
- **GrindLint risk**: new `scoped grind =` annotations may trigger lint failures requiring `#grind_lint skip` entries

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Upgrade all structural equality lemmas in the normalization/definitional layer from `@[simp]` to `@[simp, scoped grind =]`
- Follow the established three-tier co-tagging convention consistently
- Pass the full CI pipeline (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake)

**Non-Goals**:
- Tagging derivability constructors (Derivable.ax, Derivable.mp, etc.) -- reserved for proof-search tactic
- Tagging substitution lemmas or targeted simp lemmas in Bimodal metalogic internals
- Tagging swapTemporal_* lemmas (used only in targeted `simp only [...]` calls)
- Simplifying existing proofs that use these lemmas (that is task 278)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| GrindLint test failures from new `scoped grind =` tags | M | H | Run `lake test` after each batch; add `#grind_lint skip` entries as needed |
| simpNF lint warnings on newly co-tagged lemmas | L | L | All targets are clean structural LHS; `nolint simpNF` precedent exists in BuchiClosure.lean if needed |
| Wrapped Modal iff versions conflict with unwrapped tags | L | L | Unwrapped iff tags are marked optional; skip if redundant |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4 | -- |
| 3 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Foundations Layer Tags [COMPLETED]

**Goal**: Upgrade `@[simp]` to `@[simp, scoped grind =]` on 6 structural equality lemmas in the Foundations metalogic layer.

**Tasks**:
- [ ] In `Cslib/Foundations/Logic/Metalogic/ListImplication.lean`, change `@[simp]` to `@[simp, scoped grind =]` for:
  - `listImp_nil` (line 51): `listImp [] phi = phi`
  - `listImp_cons` (line 54): `listImp (psi :: Psi) phi = HasImp.imp psi (listImp Psi phi)`
- [ ] In `Cslib/Foundations/Logic/Theorems/BigConj.lean`, change `@[simp]` to `@[simp, scoped grind =]` for:
  - `bigconj_nil` (line 72): `bigconj [] = HasBot.bot`
  - `bigconj_singleton` (line 76)
  - `bigconj_cons_cons` (line 79)
  - `negBigconj_def` (line 87)
- [ ] Run `lake build` to verify no simpNF or lint warnings

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` - upgrade 2 lemma tags
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` - upgrade 4 lemma tags

**Verification**:
- `lake build` succeeds with no new warnings
- `grep -n "scoped grind" Cslib/Foundations/Logic/Metalogic/ListImplication.lean` shows 2 matches
- `grep -n "scoped grind" Cslib/Foundations/Logic/Theorems/BigConj.lean` shows 4 matches

---

### Phase 2: Temporal and Bimodal Embedding Tags [COMPLETED]

**Goal**: Upgrade `@[simp]` to `@[simp, scoped grind =]` on 10 structural equality lemmas in the Temporal and Bimodal embedding layers.

**Tasks**:
- [ ] In `Cslib/Logics/Temporal/FromPropositional.lean`, change `@[simp]` to `@[simp, scoped grind =]` for:
  - `PL.Proposition.toTemporal_atom` (line 69)
  - `PL.Proposition.toTemporal_bot` (line 74)
  - `PL.Proposition.toTemporal_imp` (line 79)
  - `PL.Proposition.toTemporal_and` (line 84)
  - `PL.Proposition.toTemporal_or` (line 90)
- [ ] In `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean`, change `@[simp]` to `@[simp, scoped grind =]` for:
  - `toBimodal_atom` (line 40-42)
  - `toBimodal_bot` (line 45-47)
  - `toBimodal_imp` (line 50-53)
  - `toBimodal_untl` (line 56-59)
  - `toBimodal_snce` (line 62-65)
- [ ] Run `lake build` to verify no simpNF or lint warnings

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/FromPropositional.lean` - upgrade 5 lemma tags
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` - upgrade 5 lemma tags

**Verification**:
- `lake build` succeeds with no new warnings
- `grep -n "scoped grind" Cslib/Logics/Temporal/FromPropositional.lean` shows 5 matches
- `grep -n "scoped grind" Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` shows 5 matches

---

### Phase 3: Modal Iff Characterization Tags (Optional) [COMPLETED]

**Goal**: Add `@[scoped grind =]` to 4 unwrapped iff characterization lemmas in Modal/Basic.lean that currently have no tags. These are optional because the wrapped `downMacro Modal[...]` versions at lines 199-232 already carry `@[scoped grind =]`.

**Tasks**:
- [ ] Assess whether grind encounters the unwrapped forms by checking if any proof in the codebase references `Satisfies.neg_iff`, `Satisfies.diamond_iff`, `Satisfies.and_iff`, or `Satisfies.or_iff` directly
- [ ] If beneficial, add `@[scoped grind =]` (NOT `@[simp]` -- these are iff characterizations) to:
  - `Satisfies.neg_iff` (line 137)
  - `Satisfies.diamond_iff` (line 141)
  - `Satisfies.and_iff` (line 153)
  - `Satisfies.or_iff` (line 163)
- [ ] If deemed redundant with the wrapped versions, skip and document the decision
- [ ] Run `lake build` to verify no warnings

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` - optionally add `@[scoped grind =]` to 4 iff lemmas

**Verification**:
- `lake build` succeeds
- If tags added: `grep -n "scoped grind" Cslib/Logics/Modal/Basic.lean` shows new matches beyond the existing wrapped versions

---

### Phase 4: GrindLint Skip Entries [COMPLETED]

**Goal**: Run `lake test` to check if new `scoped grind =` annotations trigger GrindLint failures, and add `#grind_lint skip` entries as needed.

**Tasks**:
- [ ] Run `lake test` and check output for grind lint failures
- [ ] For each failing lemma, add a `#grind_lint skip` entry in `CslibTests/GrindLint.lean` following the pattern of existing skip entries (e.g., `#grind_lint skip Cslib.Logic.Modal.neg_denotation`)
- [ ] Re-run `lake test` to confirm all tests pass

**Timing**: 30 minutes

**Depends on**: none (can run after any phase that adds tags; all phases are independent but this should run after 1, 2, and 3 are done)

**Files to modify**:
- `CslibTests/GrindLint.lean` - add `#grind_lint skip` entries for any newly-tagged lemmas that trigger lint failures

**Verification**:
- `lake test` passes with zero failures
- All new skip entries follow existing naming convention

---

### Phase 5: Full CI Verification [COMPLETED]

**Goal**: Run the complete CI pipeline to verify all changes pass.

**Tasks**:
- [ ] Run `lake build` -- full project build
- [ ] Run `lake test` -- test suite including GrindLint
- [ ] Run `lake exe checkInitImports` -- verify Cslib.Init imports
- [ ] Run `lake exe lint-style` -- style linting
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` -- dependency analysis
- [ ] Fix any failures found and re-run

**Timing**: 1 hour (includes build time and potential fixes)

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- Any files requiring fixes from CI failures

**Verification**:
- All 5 CI commands pass with zero errors
- `git diff --stat` shows only the expected files modified

## Testing & Validation

- [ ] `lake build` succeeds with no new warnings
- [ ] `lake test` passes (including GrindLint)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes
- [ ] All 16 mandatory lemma tags upgraded from `@[simp]` to `@[simp, scoped grind =]`
- [ ] No derivability constructors tagged
- [ ] No substitution or targeted simp lemmas tagged

## Artifacts & Outputs

- `specs/268_simp_grind_normalization_tags/plans/02_normalization-tags-plan.md` (this file)
- Modified Lean source files (4 mandatory + 1 optional + 1 test file)
- `specs/268_simp_grind_normalization_tags/summaries/02_normalization-tags-summary.md` (post-implementation)

## Rollback/Contingency

All changes are purely additive attribute annotations. Rollback is trivial:
- Revert `@[simp, scoped grind =]` back to `@[simp]` on each modified lemma
- Remove any added `@[scoped grind =]` tags from Modal iff lemmas
- Remove any added `#grind_lint skip` entries from GrindLint.lean
- `git checkout -- <modified files>` restores original state
