# Implementation Plan: Task #188

- **Task**: 188 - first_propositional_upstream_pr
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/188_first_propositional_upstream_pr/reports/01_team-research.md, specs/188_first_propositional_upstream_pr/reports/02_bot-primitive-justification.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prepare a first upstream PR (~285 LOC) contributing propositional logic foundations to CSLib. The PR adds a connective typeclass hierarchy (`Connectives.lean`, new file), refactors the `Proposition` type to use five primitives `{atom, bot, imp, and, or}` with derived negation and verum (`Defs.lean`), and updates the natural deduction system for the new signature (`NaturalDeduction/Basic.lean`). All work is done on a feature branch based on upstream `main`, verified against upstream's Mathlib dependency, and accompanied by a draft PR description addressing the ctchou objection, contribution roadmap, and AI disclosure.

### Research Integration

The team research report (01_team-research.md) established:
- Upstream has exactly 4 relevant files; only `Defs.lean` and `NaturalDeduction/Basic.lean` need modification
- Our fork's `{atom, bot, imp, and, or}` type resolves ctchou's PR #635 objection about functional completeness
- The `imp` vs `impl` naming follows standard notation (Gentzen, Prawitz); upstream's `impl` is non-standard
- Two open PRs conflict (#536 by thomaskwaring modifies Defs.lean; #607 by fmontesi introduces HasAnd/HasOr) -- our PR supersedes both approaches
- Only `Cslib.lean` (barrel file) and `NaturalDeduction/Basic.lean` import from `Defs.lean` upstream, so the impact radius is minimal
- ~300 LOC budget fits: Connectives.lean (~115 LOC) + Defs.lean modifications (~70 LOC net) + Basic.lean modifications (~100 LOC net)

The bot justification report (02_bot-primitive-justification.md) confirmed:
- Primitive `bot` is required by Johansson's minimal logic (1937) -- removing it yields the positive fragment, not standard minimal logic
- Our ND system correctly gates `botE` behind `[IsIntuitionistic T]`, so minimal logic is exact
- Upstream's `[Bot Atom]` constraint approach forces negation behind a typeclass constraint; our approach makes it uniformly available

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the upstream contribution track. The ROADMAP.md focuses on porting from BimodalLogic to CSLib; this task opens the reverse direction -- contributing our Propositional work back upstream. No specific roadmap items are directly addressed, but success here unblocks future upstream PRs for the entire Hilbert system and completeness results.

## Goals & Non-Goals

**Goals**:
- Create a feature branch based on upstream `main` (not our fork's `main`)
- Add `Connectives.lean` as a new file in `Cslib/Foundations/Logic/`
- Modify `Defs.lean` to use five-primitive `Proposition` type with `bot` constructor and `imp` naming
- Modify `NaturalDeduction/Basic.lean` to match the new `Proposition` signature
- Update `Cslib.lean` barrel file to include `Connectives`
- Verify `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test` all pass
- Draft a complete PR description with literature justification, ctchou resolution, roadmap, and AI disclosure

**Non-Goals**:
- Actually submitting the PR (requires Zulip discussion first)
- Adding Hilbert proof system files (that is PR 2+)
- Adding semantics files (that is PR 2+)
- Modifying any files beyond Connectives.lean, Defs.lean, NaturalDeduction/Basic.lean, and Cslib.lean
- Reconciling with PR #536 or #607 (our PR supersedes them; reviewer coordination happens on Zulip)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Upstream Mathlib version differs from our fork | H | M | Rebase on upstream main, run `lake update`, resolve any API breakage |
| `impl` to `imp` rename breaks downstream upstream code | M | L | Verified: only NaturalDeduction/Basic.lean and Cslib.lean import Defs.lean upstream |
| Reviewers prefer `impl` over `imp` naming | M | M | PR description cites Gentzen/Prawitz standard; offer to adopt reviewer preference |
| PR #536 or #607 merge before ours, creating conflicts | H | M | Monitor PRs; our approach is a superset that can absorb either |
| `grind` tactic behavior differs on upstream Mathlib version | M | L | Test all `grind` calls; fallback to explicit proofs if needed |
| `Connectives.lean` scope questioned (why not use Mathlib's `Bot`/`HImp`?) | M | M | PR description explains: Mathlib classes are for algebraic structures, not formula-level connectives; our classes enable polymorphic axiom definitions across logic levels |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Create Feature Branch and Upstream Workspace [NOT STARTED]

**Goal**: Establish a clean working branch based on upstream `main` for PR preparation.

**Tasks**:
- [ ] Create feature branch `feat/propositional-five-primitive` from `upstream/main`
- [ ] Verify the branch compiles cleanly: `lake build`
- [ ] Record upstream HEAD commit SHA for reference
- [ ] Verify which files exist under `Cslib/Foundations/Logic/` and `Cslib/Logics/Propositional/` on this branch

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- (none -- branch setup only)

**Verification**:
- `git log --oneline -1` shows upstream HEAD
- `lake build` succeeds on the clean upstream branch

---

### Phase 2: Add Connectives.lean [NOT STARTED]

**Goal**: Introduce the connective typeclass hierarchy as a new file in Foundations/Logic/.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Connectives.lean` with the connective typeclass hierarchy
- [ ] Include: `HasBot`, `HasImp`, `HasAnd`, `HasOr` atomic classes
- [ ] Include: `PropositionalConnectives` bundled class extending `HasBot` and `HasImp`
- [ ] Omit modal/temporal connectives (`HasBox`, `HasUntil`, `HasSince`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`) -- those belong in future PRs
- [ ] Include proper module docstring with design rationale and literature references
- [ ] Include `import Cslib.Init` as first import
- [ ] Use `@[expose] public section` and `namespace Cslib.Logic` per CSLib conventions
- [ ] Add `public import Cslib.Foundations.Logic.Connectives` to `Cslib.lean` barrel file
- [ ] Run `lake exe checkInitImports` to verify import compliance
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake build Cslib.Foundations.Logic.Connectives` to verify module compiles

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - New file (~70 LOC, propositional connectives only)
- `Cslib.lean` - Add import line

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` succeeds
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

**Note on scope**: The Connectives.lean contributed upstream should contain ONLY the propositional connectives needed by this PR: `HasBot`, `HasImp`, `HasAnd`, `HasOr`, and `PropositionalConnectives`. The modal/temporal connectives are deferred to future PRs where they are needed. This keeps the PR focused and reviewable.

---

### Phase 3: Refactor Defs.lean [NOT STARTED]

**Goal**: Modify `Defs.lean` to use the five-primitive Proposition type with derived negation and verum.

**Tasks**:
- [ ] Add `public import Cslib.Foundations.Logic.Connectives` to imports (replacing `Cslib.Init` since `Connectives` already imports it transitively)
- [ ] Modify `Proposition` inductive to add `bot` constructor and rename `impl` to `imp`:
  ```
  | atom (x : Atom) | bot | imp (a b) | and (a b) | or (a b)
  ```
- [ ] Add docstrings to each constructor (atom, bot, imp, and, or)
- [ ] Update `Proposition.neg` to remove `[Bot Atom]` constraint (now uses `.bot` directly)
- [ ] Update `Proposition.top` to remove `[Inhabited Atom]` constraint (now `⊥ → ⊥`)
- [ ] Remove `instBotProposition` (had `[Bot Atom]` constraint) and `instInhabitedOfBot`
- [ ] Add constraint-free instances: `instance : Bot (Proposition Atom) := ⟨.bot⟩` and `instance : Top (Proposition Atom) := ⟨.top⟩`
- [ ] Add `Proposition.iff` as a derived connective: `A ↔ B := (A → B) ∧ (B → A)`
- [ ] Update notation block: add `↔` notation, rename `→` from `impl` to `imp`
- [ ] Register typeclass instances: `PropositionalConnectives`, `HasAnd`, `HasOr`
- [ ] Update `Proposition.subst` for the new type (add `bot` case, rename `impl` to `imp`)
- [ ] Remove all `[Bot Atom]` constraints from `IPL`, `CPL`, `IsIntuitionistic`, `IsClassical`, and related theorems/instances
- [ ] Update module docstring to describe the five-primitive design, architecture, and references
- [ ] Add BibKey citations: `[Johansson1937]`, `[Gentzen1935]`, `[Prawitz1965]`, `[TroelstraVanDalen1988]`, `[Church1956]`, `[ChagrovZakharyaschev1997]`
- [ ] Run `lake build Cslib.Logics.Propositional.Defs` to verify compilation

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Refactor Proposition type, remove Bot Atom constraints, add typeclass instances

**Verification**:
- `lake build Cslib.Logics.Propositional.Defs` succeeds
- `Proposition` type has exactly 5 constructors: `atom`, `bot`, `imp`, `and`, `or`
- No `[Bot Atom]` constraints remain in the file
- All typeclass instances registered

---

### Phase 4: Update NaturalDeduction/Basic.lean [NOT STARTED]

**Goal**: Update the natural deduction system for the new Proposition signature.

**Tasks**:
- [ ] Rename all `implI` occurrences to `impI` in the `Derivation` inductive and all downstream usage
- [ ] Rename all `implE` occurrences to `impE` in the `Derivation` inductive and all downstream usage
- [ ] Rename `andE₁`/`andE₂`/`orI₁`/`orI₂` to `andE1`/`andE2`/`orI1`/`orI2` (ASCII-safe names matching our convention)
- [ ] Update `weak` function: adjust pattern matching for renamed constructors; add explicit context parameters (`G`) to match our fork's style if needed for readability
- [ ] Update `subs` function for renamed constructors
- [ ] Update `substAtom` function for renamed constructors
- [ ] Remove `[Inhabited Atom]` constraints from `derivationTop`, `derivableIn_top`, `derivable_iff_equiv_top`
- [ ] Remove `[Bot Atom]` constraints if any remain
- [ ] Update module docstring to document all 10 primitive constructors, logic strength control, and references with BibKey format
- [ ] Add BibKey citations: `[Johansson1937]`, `[Prawitz1965]`, `[TroelstraVanDalen1988]`, `[Gentzen1935]`
- [ ] Run full `lake build` to verify no breakage
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`
- [ ] Run `lake test`

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - Rename constructors, remove type constraints, update docstrings

**Verification**:
- `lake build` succeeds (full project, since this is the last file and barrel imports everything)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- No `impl` naming remains; all uses are `imp`
- No `[Bot Atom]` or `[Inhabited Atom]` constraints remain

---

### Phase 5: Draft PR Description and Final Verification [NOT STARTED]

**Goal**: Write the PR description and run complete CI verification.

**Tasks**:
- [ ] Run complete CI pipeline in order:
  1. `lake build`
  2. `lake exe checkInitImports`
  3. `lake exe lint-style`
  4. `lake test`
  5. `lake exe mk_all --module` (update barrel file if needed)
  6. `lake shake --add-public --keep-implied --keep-prefix` (import hygiene)
- [ ] Draft PR description in `specs/188_first_propositional_upstream_pr/pr-description.md` containing:
  - Title: `feat(Logics/Propositional): five-primitive formula type with connective typeclasses`
  - Summary: what changed and why
  - ctchou resolution: explain how `{atom, bot, imp, and, or}` resolves PR #635 objection
  - Literature justification for primitive `bot` (Johansson 1937, Prawitz 1965, Troelstra & van Dalen 1988)
  - `imp` vs `impl` naming rationale (Gentzen/Prawitz standard)
  - Contribution roadmap: 6-PR sequence toward completeness + ND equivalence
  - Relationship to PR #607 (Connectives.lean adopts the operator-typeclass approach)
  - AI disclosure (Claude used for research, planning, and code assistance)
  - Breaking changes: `impl` renamed to `imp`, `[Bot Atom]` constraints removed
- [ ] Generate diff statistics: `git diff --stat upstream/main`
- [ ] Verify total LOC is within ~300 LOC budget
- [ ] Commit all changes on the feature branch

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `specs/188_first_propositional_upstream_pr/pr-description.md` - New file with PR description draft
- Possibly `Cslib.lean` - If `mk_all` or `shake` requires updates

**Verification**:
- All 6 CI steps pass
- `git diff --stat upstream/main` shows ~285 LOC of changes
- PR description covers all required sections
- Feature branch has clean commit history

## Testing & Validation

- [ ] `lake build` passes on the feature branch (against upstream's Mathlib)
- [ ] `lake exe checkInitImports` confirms all files import `Cslib.Init`
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake shake --add-public --keep-implied --keep-prefix` shows no import issues
- [ ] No `sorry` in any modified or new file (`grep -r sorry` on changed files)
- [ ] No `[Bot Atom]` constraints remain in modified files
- [ ] `Proposition` type has exactly 5 constructors
- [ ] All ND constructors use `imp` (not `impl`) naming
- [ ] Total LOC within ~300 budget

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Connectives.lean` - New file: propositional connective typeclass hierarchy
- `Cslib/Logics/Propositional/Defs.lean` - Modified: five-primitive Proposition type
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - Modified: updated ND system
- `Cslib.lean` - Modified: added Connectives import
- `specs/188_first_propositional_upstream_pr/pr-description.md` - PR description draft
- Feature branch `feat/propositional-five-primitive` ready for PR submission after Zulip discussion

## Rollback/Contingency

The feature branch is isolated from our fork's `main`. If the approach is rejected:
1. Delete the feature branch: `git branch -D feat/propositional-five-primitive`
2. No changes to our fork's working code
3. Adjust approach based on reviewer feedback and create a new branch

If upstream Mathlib version causes build failures:
1. Check `lake-manifest.json` for version differences
2. Run `lake update` to align dependencies
3. Fix any API breakage in the affected files
4. If breakage is extensive, defer to a later upstream Mathlib bump
