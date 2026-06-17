# Implementation Plan: Revise PR #648 (feat/propositional-v2) Bot Refactor

- **Task**: 221 - revise_pr649_reviewer_feedback
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: Merged PR #536 (inference-system-based IsIntuitionistic/IsClassical)
- **Research Inputs**: reports/01_team-research.md, reports/02_pr648-branch-analysis.md
- **Artifacts**: plans/04_revise-pr648-bot-refactor.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr

## Overview

PR #648 (feat/propositional-v2) adds bot as a primitive constructor to the propositional formula type, eliminating `[Bot Atom]` constraints. Since PR #536 merged (refactoring IsIntuitionistic/IsClassical to inference-system-based), the branch has 3 merge conflicts and requires reconciliation of the Theory section. Additionally, reviewers requested removing Semantics files to a follow-up PR, replacing German references with English alternatives, and keeping the `imp` constructor naming. Definition of done: branch rebased on upstream/main, all conflicts resolved, Semantics files removed, German references replaced, Theory.lean updated to use `impI`/`impE` constructor names matching the branch's `imp` convention, `lake build` passes, PR description revised addressing ctchou and thomaskwaring feedback.

### Research Integration

- **reports/01_team-research.md** (v1): Identified that three of ctchou's four PR #649 objections are already addressed, reference replacement scope is larger than expected (14 citations across 4 files), and IsClassical/IsIntuitionistic may be inconsistent with #536.
- **reports/02_pr648-branch-analysis.md** (v2): Detailed branch diff analysis of feat/propositional-v2 vs upstream/main post-#536. Identified 3 merge conflicts (Cslib.lean imports, Defs.lean imports, Defs.lean Theory section), documented the bot refactor specifics, and produced a step-by-step reconciliation plan. Note: the report recommended adopting upstream's `impl` naming, but the user has decided to keep `imp` naming instead.

## Goals & Non-Goals

**Goals**:
- Rebase feat/propositional-v2 on upstream/main, resolving all 3 merge conflicts
- Remove Semantics/Basic.lean and Semantics/Bool.lean from PR scope (follow-up PR)
- Keep `imp`/`impI`/`impE` constructor naming and update Theory.lean to match (replace upstream's `implI`/`implE` with `impI`/`impE`)
- Reconcile IsIntuitionistic/IsClassical with #536's inference-system-based pattern, minus `[Bot Atom]` constraints
- Adapt Theory.lean (from #536) to work with primitive bot (remove `[Bot Atom]` from all signatures)
- Replace German-language references in docstrings with Avigad2022 and Prawitz1965
- Add Avigad2022 bib entry to references.bib
- Revise PR description with balanced bot-as-primitive rationale addressing thomaskwaring's concerns
- Verify clean build with full CI pipeline

**Non-Goals**:
- Implementing LTL semantics (separate task, PR #649 scope)
- Resolving the and/or primitives inconsistency between Connectives.lean and formula types
- Changing the bot-as-primitive design decision itself
- Coordinating PR #607 overlap (note in PR description only)
- Adopting upstream's `impl` naming (keeping `imp` instead, with independent justifications)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Rebase produces additional unexpected conflicts | H | L | Run `git rebase --abort` and retry with `git merge` if conflicts exceed expected 3 |
| Theory.lean adaptation breaks derived rules (efqCtx, contra, byContra) | H | M | Build incrementally after each signature change; reference #536's Theory.lean as ground truth |
| Constructor rename in Theory.lean misses references | M | L | grep for `implI`/`implE`/`andE₁`/`andE₂`/`orI₁`/`orI₂` after rename to catch stragglers |
| thomaskwaring objects to keeping `imp` naming instead of `impl` | M | M | Independent justifications: upstream merged Propositional/Defs.lean uses `imp` as constructor, FormalizedFormalLogic uses `imp` for constructors, and `imp` distinguishes the constructor from derived `impl` connective |
| PR #607 merges before this PR, breaking Connectives.lean | M | L | Note coordination in PR description; Connectives.lean overlap is minimal |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases are sequential because each depends on the previous phase's file state.

### Phase 1: Rebase and Resolve Merge Conflicts [NOT STARTED]

**Goal**: Rebase feat/propositional-v2 on upstream/main and resolve the 3 known merge conflicts.

**Tasks**:
- [ ] Fetch upstream/main to ensure it includes merged PR #536 (commit `70c5bf58`)
- [ ] Run `git rebase upstream/main` on feat/propositional-v2
- [ ] Resolve Conflict 1 (`Cslib.lean`): keep Theory import from upstream, keep Semantics imports from branch (will be removed in Phase 2)
- [ ] Resolve Conflict 2 (`Defs.lean` imports): keep both `Cslib.Init` + `Connectives` from branch and `InferenceSystem` from upstream
- [ ] Resolve Conflict 3 (`Defs.lean` Theory section): adopt upstream's inference-system-parameterized `IsIntuitionistic`/`IsClassical` but remove `[Bot Atom]` constraints since bot is now primitive
- [ ] Verify auto-merged `NaturalDeduction/Basic.lean` accepted branch's constructor names (`impI`, `impE`, etc.)
- [ ] Run `lake build` to check rebase result compiles (may have errors from naming mismatch with Theory.lean)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib.lean` - resolve import conflict
- `Cslib/Logics/Propositional/Defs.lean` - resolve imports and Theory section conflicts

**Verification**:
- `git rebase` completes without unresolved conflicts
- `git log --oneline` shows branch commits on top of upstream/main

---

### Phase 2: Remove Semantics Files and Update Theory.lean Constructor Names [NOT STARTED]

**Goal**: Remove Semantics files from PR scope per reviewer request, and update Theory.lean to use `impI`/`impE` constructor names matching the branch's `imp` convention.

**Tasks**:
- [ ] Delete `Cslib/Logics/Propositional/Semantics/Basic.lean` from the working tree
- [ ] Delete `Cslib/Logics/Propositional/Semantics/Bool.lean` from the working tree
- [ ] Remove Semantics imports from `Cslib.lean` (`Cslib.Logics.Propositional.Semantics.Basic`, `Cslib.Logics.Propositional.Semantics.Bool`)
- [ ] In `Defs.lean`: verify `imp` is the constructor name in the `Proposition` inductive type (keep as-is)
- [ ] In `Defs.lean`: verify all references use `.imp` (derived connectives `neg`, `top`, `iff`, `subst`) -- keep as-is
- [ ] In `NaturalDeduction/Theory.lean` (from #536): rename upstream's `implI`->`impI`, `implE`->`impE`, `andE₁`->`andE1`, `andE₂`->`andE2`, `orI₁`->`orI1`, `orI₂`->`orI2` to match branch convention
- [ ] Verify `NaturalDeduction/Basic.lean` already uses `impI`/`impE`/`andE1`/`andE2`/`orI1`/`orI2` (branch convention)
- [ ] In `Connectives.lean`: keep `HasImp` naming (consistent with `imp` convention)
- [ ] Run `lake build` to verify naming consistency

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Basic.lean` - delete
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - delete
- `Cslib.lean` - remove Semantics imports
- `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` - rename constructor references to match `imp` convention

**Verification**:
- Semantics files no longer exist on branch
- `grep -r "Semantics.Basic\|Semantics.Bool" Cslib/` returns no matches
- `grep -r "implI\|implE\|andE₁\|andE₂\|orI₁\|orI₂" Cslib/Logics/Propositional/` returns no matches (all converted to `impI`/`impE`/`andE1`/`andE2`/`orI1`/`orI2`)
- `lake build` succeeds

---

### Phase 3: Adapt IsIntuitionistic/IsClassical and Theory.lean to Primitive Bot [NOT STARTED]

**Goal**: Ensure the inference-system-parameterized IsIntuitionistic/IsClassical from #536 work correctly with primitive bot, and adapt Theory.lean to remove all `[Bot Atom]` constraints.

**Tasks**:
- [ ] In `Defs.lean`: verify IsIntuitionistic/IsClassical use inference-system-based signatures (from #536) without `[Bot Atom]`
- [ ] Verify `Bot` instance on `Proposition Atom` is `⟨.bot⟩` (not `⟨.atom ⊥⟩`), requiring no `[Bot Atom]` constraint
- [ ] In `Defs.lean`: verify `IPL`, `MPL`, `CPL` definitions do not carry `[Bot Atom]` constraints
- [ ] In `NaturalDeduction/Theory.lean` (from #536): remove `[Bot Atom]` from all instance signatures (`instIsIntuitionisticIPL`, `instIsClassicalCPL`, etc.)
- [ ] In `Theory.lean`: verify derived rules (`efqCtx`, `efqRule`, `contra`, `byContra`) work with primitive bot
- [ ] In `Theory.lean`: verify alternative axiom systems (`LEM`, `Pierce`) compile without `[Bot Atom]`
- [ ] In `NaturalDeduction/Basic.lean`: verify `derivationTop`, `derivableIn_top`, `derivable_iff_equiv_top` have no `[Inhabited Atom]` constraint (since top = imp bot bot, no constraint needed)
- [ ] Run `lake build` to confirm all adaptations compile

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - verify/fix IsIntuitionistic/IsClassical signatures
- `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` - remove `[Bot Atom]` constraints
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - verify constraint removal

**Verification**:
- `grep -r "Bot Atom" Cslib/Logics/Propositional/` returns no matches in type signatures
- `grep -r "Inhabited Atom" Cslib/Logics/Propositional/` returns no matches in derivation-related signatures
- `lake build` succeeds with no errors

---

### Phase 4: Replace German References and Add Avigad2022 [NOT STARTED]

**Goal**: Replace all German-language citations in Lean file docstrings with modern English alternatives, and add the Avigad2022 bib entry.

**Tasks**:
- [ ] Add Avigad2022 entry to `references.bib`: Avigad, Jeremy. "Mathematical Logic and Computation." Cambridge University Press, 2022. ISBN 978-1-108-84072-1
- [ ] In `Connectives.lean` docstrings: replace `[Johansson1937]` with `[Avigad2022]`, `[Wajsberg1938]` with `[Avigad2022]`, `[Gentzen1935]` with `[Prawitz1965]` or `[Avigad2022]`
- [ ] In `Defs.lean` docstrings: replace `[Johansson1937]` with `[Avigad2022]`, `[Gentzen1935]` with `[Prawitz1965]`
- [ ] In `NaturalDeduction/Basic.lean` docstrings: replace `[Johansson1937]` with `[Avigad2022]`, `[Gentzen1935]` with `[Prawitz1965]`
- [ ] Check `Axioms.lean` for any German references and replace if found
- [ ] Retain German reference entries in `references.bib` (historical record)
- [ ] Retain `[McKinsey1939]` references (English-language paper, not a German reference)
- [ ] Verify upstream post-#536 NaturalDeduction/Basic.lean already uses English references (Prawitz, Troelstra & van Dalen, Sorensen & Urzyczyn) -- align with those where applicable

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- `references.bib` - add Avigad2022 entry
- `Cslib/Foundations/Logic/Connectives.lean` - replace German refs in docstrings
- `Cslib/Logics/Propositional/Defs.lean` - replace German refs in docstrings
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - replace German refs in docstrings
- `Cslib/Logics/Propositional/Axioms.lean` - replace German refs if present

**Verification**:
- `grep -r "Johansson1937\|Gentzen1935\|Wajsberg1938\|Heyting1930" Cslib/` returns no matches in docstrings
- Avigad2022 entry present in references.bib with correct metadata
- `[McKinsey1939]` retained where used (English-language)

---

### Phase 5: Build Verification and CI Checks [NOT STARTED]

**Goal**: Run the full CI verification pipeline to confirm all changes compile and pass quality checks.

**Tasks**:
- [ ] Run `lake build` for full compilation check
- [ ] Run `lake test` to verify CslibTests suite passes
- [ ] Run `lake exe checkInitImports` to verify Cslib.Init imports
- [ ] Run `lake exe lint-style` for style compliance
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` for dependency analysis
- [ ] Final grep verification: no German BibKeys in docstrings, no Semantics file references, no `[Bot Atom]` constraints in Propositional/ signatures
- [ ] Review all changed files for consistency and completeness
- [ ] If any check fails, fix the issue and re-run

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- Any files with build errors or lint issues discovered during verification

**Verification**:
- All CI checks pass: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- `lake shake` produces no unexpected dependency issues

---

### Phase 6: Revise PR Description [NOT STARTED]

**Goal**: Write a comprehensive PR description addressing all reviewer feedback, with a balanced bot-as-primitive rationale.

**Tasks**:
- [ ] Draft PR description structure: title, summary, motivation, changes included, changes deferred, design discussion
- [ ] Document stacking relationship: PR #648 rebased on upstream/main including merged PR #536
- [ ] Note semantics split: Semantics/Basic.lean and Semantics/Bool.lean removed per thomaskwaring's request, follow-up PR planned
- [ ] Write balanced bot-as-primitive rationale:
  - Constraint elimination: no more `[Bot Atom]` everywhere
  - Uniform treatment across classical/intuitionistic/minimal logics
  - Substitution preserves structure (bot maps to bot, not to an atom)
  - Literature precedent (Avigad2022, Bentzen2023, Trufas2024)
  - Acknowledge thomaskwaring's trade-offs: additional constructor cases in proofs, non-bottom-preserving maps excluded
- [ ] Explain `imp` constructor naming decision: kept `imp` naming from branch (consistent with upstream's merged Propositional/Defs.lean which uses `imp`, FormalizedFormalLogic convention, and distinguishes constructor from derived connective); updated Theory.lean to use `impI`/`impE` to match
- [ ] Note coordination context: PR #607 (fmontesi) logical operators, PR #587 (thomaskwaring) Models typeclass
- [ ] List deferred items: LTS transitions, omega-executions, LTL semantics, Heyting algebra semantics
- [ ] List updated references: German -> English replacement summary
- [ ] Acknowledge ctchou's already-addressed review points
- [ ] Write the PR description as `specs/221_revise_pr649_reviewer_feedback/pr-description.md`

**Timing**: 0.5 hours

**Depends on**: 5

**Files to modify**:
- `specs/221_revise_pr649_reviewer_feedback/pr-description.md` - new file, PR description draft

**Verification**:
- PR description addresses all reviewer feedback categories
- Bot-as-primitive rationale acknowledges trade-offs without conceding design
- Constructor naming justified by `imp` convention with independent supporting evidence
- All deferred items explicitly listed
- No German-language references cited in description

## Testing & Validation

- [ ] `lake build` succeeds with no errors after all changes
- [ ] `lake test` passes the CslibTests suite
- [ ] `lake exe checkInitImports` verifies Cslib.Init imports
- [ ] `lake exe lint-style` passes style checks
- [ ] No German-language BibKeys remain in Lean file docstrings
- [ ] No references to deleted Semantics files anywhere in codebase
- [ ] No `[Bot Atom]` constraints remain in Propositional/ type signatures
- [ ] Constructor naming consistent: `imp`/`impI`/`impE` throughout (no `implI`/`implE` references)
- [ ] PR description covers all reviewer feedback categories
- [ ] Avigad2022 entry present in references.bib with correct metadata

## Artifacts & Outputs

- `specs/221_revise_pr649_reviewer_feedback/plans/04_revise-pr648-bot-refactor.md` (this plan)
- `specs/221_revise_pr649_reviewer_feedback/pr-description.md` (PR description draft)
- Modified Lean files with reconciled bot refactor
- Updated `references.bib` with Avigad2022
- Updated GitHub PR #648 description

## Rollback/Contingency

- All changes are on the feat/propositional-v2 feature branch; `git rebase --abort` reverts the rebase if conflicts are unresolvable
- If Theory.lean adaptation causes cascading failures, the branch can be restored to pre-rebase state via `git reflog`
- If the bot-as-primitive rationale does not satisfy reviewers, only the PR description needs further revision -- the code changes stand on their own merit
- German references remain in `references.bib` even after docstring replacement, so no historical information is lost
- Semantics files are only removed from this branch; they remain available for the follow-up PR
