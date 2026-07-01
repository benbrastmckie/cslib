# Implementation Plan: Task #392

- **Task**: 392 - Remove dead code and fix naming (Propositional logic)
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Task 386 (completed, owns LK/LJ cutAdm renames — OUT of scope here)
- **Research Inputs**: specs/392_remove_deadcode_fix_naming/reports/01_deadcode-and-naming-verification.md
- **Artifacts**: plans/01_deadcode-and-naming-fixes.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Mechanical hygiene pass over `Cslib/Logics/Propositional/` and `Cslib/Foundations/`: delete
21 grep-verified 0-reference declarations, fix one stale comment, apply 5 small underscore/
capitalization renames, fix the `Extention`->`Extension` typo across 3 theorems and their call
sites, and rename the Propositional `DerivationTree.modus_ponens` constructor to `modusPonens`
across 97 sites in 26 files. All edits are deletions or mechanical renames: zero new sorries,
no behavior change. Definition of done: every phase leaves `lake build` green, `lake test`
passing, `lake exe lint-style` clean, and introduces no `sorry`/axiom.

### Research Integration

The research report (01_deadcode-and-naming-verification.md) grep-verified every target with
CURRENT line numbers (the task-description numbers were stale after edits by tasks 389/460). Key
integrated findings:
- All 21 dead decls confirmed 0 external refs (report §2). The `classicalApplyOne_*` block
  carries NO `@[simp]` attribute despite the "Helper simp lemmas" comment, so deletion cannot
  change simp behavior.
- `Intuitionistic/Rules.lean:114/203` has NO dead decls (report §3); the only actionable item
  there is the stale comment at :203 referencing `propImpOrNegOf?`, handled with dead-decl #16.
- Word-boundary hazard on `goodSelection_seq` (must not corrupt `goodSelection_seq_prop`),
  report §4c.
- `Extention` typo is wider than the description: 3 theorems + real call sites in Basic.lean and
  AxiomAdmissibility.lean that break the build if missed (report §5).
- `modus_ponens` rename must be isolated from identically-named constructors in
  Bimodal/Temporal/Modal/ExtDerivation (no cross-imports; naive sed corrupts them). Full
  per-file site list in report Appendix A (report §4a).
- Task 317 owns Classical/Completeness+Soundness but those files carry 0 sorries and no
  working-tree diff, so deletions are safe; conservative fallback = defer only the two
  Completeness.lean decls if the live state differs at implement time (report §6).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation requested for this task (no roadmap_path / roadmap_flag in delegation
context). Task advances library-hygiene / naming-convention cleanup for the Propositional logic
subtree.

## Goals & Non-Goals

**Goals**:
- Delete the 21 confirmed 0-reference declarations and fix the stale `Rules.lean:203` comment.
- Apply 5 small renames: `lift_int_to_cl`, `goodSelection_seq`, `HasFresh.to_infinite`,
  `emptyHrelation_apply` capitalization.
- Fix `Extention`->`Extension` across 3 theorems and all call/comment sites.
- Rename the Propositional `DerivationTree.modus_ponens` constructor to `modusPonens` across all
  97 sites in 26 files, isolated from same-named constructors in other logics.
- Keep the tree green after every phase (build, test, lint-style, zero new sorries).

**Non-Goals**:
- LK/LJ `cutAdm_*` / `ljCutAdm_*` renames (owned by completed task 386).
- Renaming `height_modus_ponens_left` / `height_modus_ponens_right` helpers (remain snake_case;
  out of scope — flag to user as a possible follow-up).
- Deleting or altering any declaration in `Intuitionistic/Rules.lean` (no dead decls there).
- Touching `modus_ponens` constructors in Bimodal/Temporal/Modal/ExtDerivation.
- Any change to `Classical/Completeness.lean` sorries or 317 WIP logic.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Naive string-replace of `modus_ponens` corrupts other-logic constructors | H | M | Per-file edits scoped to `Propositional/` only; never repo-wide sed; verify no Bimodal/Temporal/Modal/ExtDerivation file is touched via `git diff --name-only` |
| `goodSelection_seq` replace corrupts `goodSelection_seq_prop` | M | M | Use word-boundary `\bgoodSelection_seq\b` or edit each of the 11 sites individually; grep for `goodSelectionSeq_prop` after (must be zero) |
| Stale line numbers (files edited by 389/460) | M | M | Re-grep each declaration by name at implement time before editing; do not trust line numbers blindly |
| Task 317 resumes and touches Classical files concurrently | M | L | Re-grep at implement time; conservative fallback = defer only `mem_extendMany_of_mem`/`hintikka_inv_mono` (and optionally the Soundness items), landing everything else independently |
| Missing an `Extention` call site breaks the build | H | L | Rename all 3 theorems + enumerated call sites (Basic.lean:302, AxiomAdmissibility.lean:230/232) in the same phase; `lake build` gate catches any miss |
| `emptyHRelation_apply` exact expected name differs from lint expectation | L | L | Confirm with `lake lint` at implement time; keep `_apply` Mathlib convention |
| Deleting `propImpOrNegOf?` leaves dangling comment reference | L | M | Fix/remove the `Rules.lean:203` comment in the same phase as the deletion |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are sequenced (one wave each) rather than parallelized because several files are touched
by more than one phase (`Defs.lean` by Phases 1 and 3; `NaturalDeduction/Equivalence.lean` by
Phases 1, 3, and 4; `Metalogic/IntLindenbaum.lean` by Phases 2 and 4). Sequential execution
prevents line-number drift and edit conflicts between agent runs. Each phase is one agent run
with its own verification gate.

### Phase 1: Dead-code deletion [COMPLETED]

**Goal**: Delete the 21 grep-verified 0-reference declarations and fix the stale comment at
`Intuitionistic/Rules.lean:203`.

**Tasks**:
- [x] Re-grep each target by name before editing (line numbers may have drifted); confirm 0 refs.
- [x] Delete 12 `classicalApplyOne_*` lemmas in `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` (block ~lines 73-141: pos_atom, pos_bot, pos_and, pos_or, pos_imp, pos_neg, neg_atom, neg_bot, neg_and, neg_or, neg_imp, neg_neg). Do NOT touch `classicalApplyOne` (parent, live) nor the LIVE `classicalApplyOne_output_complexity`/`classicalApplyOne_branching_length` in Completeness.lean.
- [x] Delete `classicalBranchSatisfiable_not_closed` (Classical/Soundness.lean:~486).
- [x] Delete `mem_extendMany_of_mem` (~450) and `hintikka_inv_mono` (~462) in `Classical/Completeness.lean`. Re-grep first; if 317 WIP state differs (nonzero diff or new sorry adjacent), DEFER only these two and note in summary (conservative fallback per report §6). *(Re-grep confirmed 0 external refs, no adjacent sorry, no 317 WIP diff; deleted as planned.)*
- [x] Delete `propImpOrNegOf?` in `Tableau/Defs.lean:~81` AND fix/remove the stale comment referencing it at `Tableau/Intuitionistic/Rules.lean:~203`. Do NOT delete any Rules.lean declaration.
- [x] Delete `closurePred_false_of_sat` (~431) and `isAccessible_go_mono_fuel` (~505) in `Intuitionistic/Soundness.lean`.
- [x] Delete `hilbertAxiomToND` in `NaturalDeduction/Equivalence.lean:~305`.
- [x] Delete `mem_insert_left` (~69) and `mem_insert_right` (~73) in `SequentCalculus/LK/Completeness.lean` (local wrappers over `Finset.mem_insert_self`/`Finset.mem_insert_of_mem`).

**Timing**: ~45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - delete 13 dead decls
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - delete 2 dead decls (with 317 fallback)
- `Cslib/Logics/Propositional/Tableau/Defs.lean` - delete `propImpOrNegOf?`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` - fix stale comment only (no decl deletion)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - delete 2 dead decls
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - delete `hilbertAxiomToND`
- `Cslib/Logics/Propositional/SequentCalculus/LK/Completeness.lean` - delete 2 dead decls

**Verification**:
- `lake build` green (the affected modules and their downstream consumers rebuild cleanly).
- `lake test` passes.
- `lake exe lint-style` clean.
- `git grep -n propImpOrNegOf?` returns zero hits (decl and comment both gone).
- No new `sorry`/axiom introduced (`git grep -n sorry` on touched files unchanged).

---

### Phase 2: Small renames [NOT STARTED]

**Goal**: Apply 4 self-contained renames with word-boundary and capitalization care.

**Tasks**:
- [ ] `lift_int_to_cl` -> `liftIntToCl` in `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` (decl + all uses; report lists ~263/270/272/278). Update every call site; matches sibling `liftMinToCl`.
- [ ] `goodSelection_seq` -> `goodSelectionSeq` in `Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean` (decl + uses ~82,84,89,90,95,98,100,114,115,116,118). USE word-boundary matching `\bgoodSelection_seq\b` or edit each site individually. Do NOT corrupt the separate decl `goodSelection_seq_prop` (~88,118).
- [ ] `HasFresh.to_infinite` -> `HasFresh.toInfinite` in `Cslib/Foundations/Data/HasFresh.lean` (instance decl ~38 + docstring ~44). Used via typeclass resolution so renaming the instance name is safe.
- [ ] `emptyHrelation_apply` -> `emptyHRelation_apply` in `Cslib/Foundations/Relation/Domain.lean:~30` (capitalization fix `Hrelation`->`HRelation` to match `emptyHRelation`; KEEP trailing `_apply` Mathlib convention). Confirm exact expected name with `lake lint`.

**Timing**: ~45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - `lift_int_to_cl` rename
- `Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean` - `goodSelection_seq` rename (word-boundary)
- `Cslib/Foundations/Data/HasFresh.lean` - `to_infinite` rename
- `Cslib/Foundations/Relation/Domain.lean` - `emptyHrelation_apply` capitalization

**Verification**:
- `lake build` green.
- `lake test` passes.
- `lake exe lint-style` clean; targeted `defsWithUnderscore` / capitalization lint entries clear.
- `git grep -n "goodSelectionSeq_prop"` returns zero hits (no corruption of the sibling decl).
- `git grep -n "goodSelection_seq_prop"` still present and intact (unchanged separate decl).
- No new `sorry`/axiom.

---

### Phase 3: `Extention` -> `Extension` typo rename [NOT STARTED]

**Goal**: Fix the misspelled instance-builder theorems and every reference so the build stays green.

**Tasks**:
- [ ] Rename `instIsIntuitionisticExtention` -> `instIsIntuitionisticExtension` (decl `Defs.lean:~190`); update call sites `NaturalDeduction/Basic.lean:~302` and `NaturalDeduction/AxiomAdmissibility.lean:~230`, and comment sites `Basic.lean:~215`, `Equivalence.lean:~256`.
- [ ] Rename `instIsClassicalExtention` -> `instIsClassicalExtension` (decl `Defs.lean:~195`); update call site `AxiomAdmissibility.lean:~232` and comment `Equivalence.lean:~256`.
- [ ] Rename `instIsMinimalExtention` -> `instIsMinimalExtension` (decl `Equivalence.lean:~257`; no external call/comment sites).
- [ ] Re-grep `git grep -n Extention` before finishing; must return zero hits.

**Timing**: ~30 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - decls at ~190/195
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - call ~302, comment ~215
- `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` - calls ~230/232
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - decl ~257, comments ~256

**Verification**:
- `lake build` green (Propositional.Defs consumers and NaturalDeduction rebuild cleanly).
- `lake test` passes.
- `lake exe lint-style` clean.
- `git grep -n "Extention"` returns zero hits.
- No new `sorry`/axiom.

---

### Phase 4: `modus_ponens` constructor rename (large, isolated) [NOT STARTED]

**Goal**: Rename the Propositional `DerivationTree.modus_ponens` constructor to `modusPonens`
across all 97 sites in 26 files, without touching identically-named constructors in other logics.

**Tasks**:
- [ ] Rename the constructor at `Cslib/Logics/Propositional/ProofSystem/Derivation.lean:~77` (declaration).
- [ ] Edit the remaining 96 sites PER FILE (not repo-wide sed), covering all match patterns: `| modus_ponens`, `| .modus_ponens`, `| @modus_ponens` (GenericMCSBridge.lean:~133), `.modus_ponens`, `DerivationTree.modus_ponens`, `PL.DerivationTree.modus_ponens`, unqualified `modus_ponens Γ φ ψ`. Full per-file site list (report Appendix A):
  - ProofSystem/Derivation.lean (decl + L95,102,107,137; docstring L66) — do NOT rename helper lemmas `height_modus_ponens_left`/`right` (L100/105).
  - ProofSystem/Instances.lean (1), ProofSystem/IntMinInstances.lean (2), ProofSystem/FragmentInstances.lean (3).
  - Metalogic/Soundness.lean (1), IntSoundness.lean (1), MinSoundness.lean (1), StrongCompleteness.lean (18), IntStrongCompleteness.lean (7), MinStrongCompleteness.lean (6), IntLindenbaum.lean (6), MinLindenbaum.lean (2), GenericLindenbaum.lean (4), GenericMCSBridge.lean (2 code + comments).
  - Semantics/Algebra/Soundness.lean (4), LiftViaMorphism.lean (5), BrouwerianCompleteness.lean (1), BrouwerianCompletenessGeneric.lean (1), HilbertAlgCompleteness.lean (1), PointedBrouwerianCompleteness.lean (1), MplPointedConservative.lean (1), ConjImpConservative.lean (2).
  - Semantics/SemanticConsequence.lean (4).
  - NaturalDeduction/Equivalence.lean (4 code + comment), FromHilbert.lean (5), HilbertDerivedRules.lean (15).
- [ ] Do NOT rename `height_modus_ponens_left`/`height_modus_ponens_right` (out of scope; remain snake_case — flag to user as follow-up).
- [ ] After edits, run `git diff --name-only` and confirm NO file under Bimodal/Temporal/Modal/ExtDerivation was touched.
- [ ] Re-grep `git grep -n "\bmodus_ponens\b" Cslib/Logics/Propositional/`; only the intended `height_modus_ponens_*` helper names should remain.

**Timing**: ~2 hours

**Depends on**: 3

**Files to modify**: 26 files under `Cslib/Logics/Propositional/` (enumerated above; report Appendix A has the exact line list).

**Verification**:
- `lake build` green — dedicated FULL build gate for this phase.
- `lake test` passes.
- `lake exe checkInitImports` clean.
- `lake exe lint-style` clean; `modus_ponens` constructor no longer flagged by `defsWithUnderscore`.
- `git diff --name-only` contains zero Bimodal/Temporal/Modal/ExtDerivation files.
- Remaining `modus_ponens` textual hits are only the intended `height_modus_ponens_*` helpers.
- No new `sorry`/axiom.

## Testing & Validation

- [ ] `lake build` green after each phase and at the end.
- [ ] `lake test` (CslibTests) passes after each phase.
- [ ] `lake exe checkInitImports` clean (esp. after Phase 4).
- [ ] `lake exe lint-style` clean; targeted `defsWithUnderscore`/capitalization entries clear.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` shows no new issues from deletions.
- [ ] Zero new `sorry` or axiom introduced by any edit (all edits are deletions or renames).
- [ ] No behavior change: no proof term altered beyond identifier renames.

## Artifacts & Outputs

- plans/01_deadcode-and-naming-fixes.md (this plan)
- summaries/01_deadcode-and-naming-fixes-summary.md (on implementation)
- Edited Lean sources under `Cslib/Logics/Propositional/` and `Cslib/Foundations/` (deletions + renames)
- Updated `.orchestrator-handoff.json` (plan handoff)

## Rollback/Contingency

- All edits are on a working branch; each phase is committed separately
  (`task 392 phase P: ...`) so any phase can be reverted with `git revert` independently.
- Phase 1 fallback: if `Classical/Completeness.lean` shows live 317 WIP (nonzero diff or adjacent
  new sorry) at implement time, DEFER only `mem_extendMany_of_mem` and `hintikka_inv_mono`,
  landing the rest; record the deferral in the summary.
- Phase 4 fallback: if the 97-site rename destabilizes the build, revert Phase 4 alone (Phases
  1-3 land independently) and reconsider splitting the constructor rename into its own task.
- If `lake build` fails after a phase, do not commit; re-grep for missed call sites (typically an
  `Extention` or `modus_ponens` site whose line drifted) and fix before the gate.
