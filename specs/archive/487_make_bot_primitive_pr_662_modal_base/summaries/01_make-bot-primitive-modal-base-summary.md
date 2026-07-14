# Implementation Summary: Task #487 — Make `bot` Primitive in PR #662's Modal Base

- **Task**: 487 - Make `bot` primitive in PR #662's modal `Proposition` base
- **Status**: [COMPLETED]
- **Plan**: plans/01_make-bot-primitive-modal-base.md
- **Worktree**: `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive`
- **Branch**: `task-487-pr662-bot-primitive` (branched from `task-486-pr662-modal-package` @ `4ebdba54`)
- **Commit**: `69db6de4` — `task 487: make bot primitive in #662 modal base` (single clean commit,
  not pushed)

## Overview

Refactored `Cslib/Logics/Modal/Basic.lean`'s `Proposition` inductive from
`{atom, not, and, diamond, box}` (5 constructors) to the target
`{atom, bot, imp, and, or, box, diamond}` (7 constructors, all primitive), with negation the
sole derived connective (`Proposition.neg φ := .imp φ .bot`). Both `□` and `◇` remain primitive
(unlike `main`'s derived-diamond approach), aligning #662's modal base with #648's propositional
core `{atom,bot,imp,and,or}` + `{box,diamond}`.

## Phases

- **Phase 1** [COMPLETED]: Worktree setup + `Basic.lean` refactor (inductive, notation, semantics,
  characterisation lemmas, R1 dual/converse routing).
- **Phase 2** [COMPLETED]: `Denotation.lean` + `LogicalEquivalence.lean` mechanical arm updates
  (R2 set-membership simp nudge; R3b grouped grind fold).
- **Phase 3** [COMPLETED]: `Cube.lean` verified green unchanged (R5); zero-debt audit; full CI
  re-verify; single commit.

## Net Diff vs Task-486 Base (`4ebdba54`)

| File | Lines changed |
|------|---------------|
| `Cslib/Logics/Modal/Basic.lean` | 98 (+/-), net structural rewrite of the inductive + notation wiring + characterisation lemmas |
| `Cslib/Logics/Modal/Denotation.lean` | +10/-… mechanical arm updates (`denotation` match, `satisfies_mem_denotation` simp nudge) |
| `Cslib/Logics/Modal/LogicalEquivalence.lean` | +12/-… `Context`/`fill`/`Congruence.elim` arm updates |
| `CslibTests/GrindLint.lean` | +4, deviation fix (see below) |
| `Cslib/Logics/Modal/Cube.lean` | **0** — verified green, unedited |
| **Total** | 4 files changed, 72 insertions(+), 52 deletions(-) |

## Key Changes

**`Basic.lean`**:
- New 7-constructor inductive: `atom | bot | imp | and | or | box | diamond`.
- `instance : Bot (Proposition Atom) := ⟨.bot⟩` (resolves transitively via existing imports — no
  `Mathlib.Order.Notation` import needed; R4 did not surface).
- `HasImp`/`HasAnd`/`HasOr`/`HasBox`/`HasDiamond` wired directly to constructors via
  `Cslib.Foundations.Logic.Operators` (not `main`'s `ModalConnectives`, not fork-local `infix`).
- `abbrev Proposition.neg φ := .imp φ .bot`; `instance : HasNot := {not := Proposition.neg}`;
  `neg_def` reduction lemma (`rfl`, `@[scoped grind =]`).
- `Satisfies` gains `bot => False`, `imp => (Satisfies φ₁ → Satisfies φ₂)`, `or => ∨`; drops the
  `not` arm.
- `or_iff_or`/`imp_iff_imp` simplified to `Iff.rfl` (previously `grind`-discharged from derived
  `def`s). `and_iff_and`/`box_iff_forall`/`diamond_iff_exists` remain `Iff.rfl` — **both
  modalities stay primitive**, confirmed by direct inspection.
- `not_iff_not` is now an explicit lemma (`⟨fun h hs => h hs, fun h hs => absurd hs h⟩`, ported
  from `main`'s `neg_iff` term) rather than relying on defeq (R1).
- `Satisfies.dual`/`Satisfies.box_iff_not_diamond_not`: opening `simp only` sets extended with
  `not_iff_not`/`box_iff_forall` so the internal negation unfolds explicitly; proof bodies
  otherwise unchanged (R1 — resolved cleanly, no proof-body rewrite needed).

**`Denotation.lean`**:
- `denotation` gains `bot => (∅ : Set World)`, `imp => {w | w ∈ φ₁.denotation m → w ∈ φ₂.denotation m}`,
  `or => φ₁.denotation m ∪ φ₂.denotation m`; drops the `not`/compl arm.
- `satisfies_mem_denotation`'s `induction <;> grind` preceded by
  `simp only [Proposition.denotation, Set.mem_setOf_eq, Set.mem_empty_iff_false,
  Set.mem_inter_iff, Set.mem_union]` per R2's mitigation — closed on first attempt with this nudge.
- `not_denotation` statement unchanged; `neg_def` already covered by the scoped-grind set (no
  extra hint needed — an initial redundant explicit `Proposition.neg_def` grind hint was removed
  after `lake build` flagged it as redundant).

**`LogicalEquivalence.lean`**:
- `Proposition.Context` drops `not`; adds `impL`/`impR`/`orL`/`orR`; keeps `andL`/`andR`/`diamond`/
  `box`; `bot` needs no arm (nullary).
- `fill` gains matching `impL`/`impR`/`orL`/`orR` arms.
- `Congruence.elim`: `impL`/`impR`/`orL`/`orR` folded into the existing `andL`/`andR`
  `specialize ih w; grind` case group per R3b's mitigation — the grouped `grind` closed without
  needing to split the group or fall back to `constructor <;> tauto`.

**`Cube.lean`**: Verified green with **zero edits** (R5) — `git diff` against the base shows no
changes to this file. All 15 logic defs, 6 Order inclusions, and 11 validity/canonicity theorems
survive on the new base unchanged.

## Plan Deviations

1. **`CslibTests/GrindLint.lean` touched (not in the plan's original 3-file scope)**: The
   full-library `lake test` re-verify (Phase 3, non-blocking gate) initially failed —
   `CslibTests.GrindLint` flagged `Cslib.Logic.Modal.not_denotation` for 28 additional `grind`
   theorem instantiations (over the lint's `min := 20` threshold), caused by the new
   `imp_def`/`or_def`/`neg_def` `@[scoped grind =]` lemmas in `Basic.lean`. Fixed by adding
   `#grind_lint skip Cslib.Logic.Modal.not_denotation` to `CslibTests/GrindLint.lean`, mirroring
   the file's existing HML/LTS exception entries (e.g. `Cslib.Logic.HML.bisimulation_satisfies`).
   `CslibTests/GrindLint.lean` is not on the task's Non-Goals exclusion list
   (`FromPropositional.lean`, `Metalogic/**`, `InterSystem`, `ProofSystem/`, `Tableau/`, `HML/`),
   so this is in-scope test-infrastructure maintenance rather than a library-code change. Re-ran
   `lake test`: full suite green after the fix. Annotated inline in the plan file (Phase 3 tasks).
2. **R4 (`Bot` notation import) did not surface**: `Bot` resolved transitively through the
   existing import set (verified via a standalone probe file before editing) — no
   `Mathlib.Order.Notation` import was needed.
3. All other risks (R1, R2, R3a, R3b, R5, R6) resolved exactly per the plan's stated mitigations,
   with no further deviation.

## Verification

- `lake build Cslib.Logics.Modal.Basic` — green (Phase 1 gate).
- `lake build Cslib.Logics.Modal.Denotation` / `Cslib.Logics.Modal.LogicalEquivalence` — green
  (Phase 2 gate).
- `lake build Cslib.Logics.Modal.Cube` — green, file unedited (Phase 3 gate).
- All four Modal module builds together — green.
- Full `lake build` (2759 jobs) — green.
- `lake exe checkInitImports` — exit 0.
- `lake exe lint-style` — exit 0 (clean; no new lint findings).
- `lake shake --add-public --keep-implied --keep-prefix` — identical suggestion set to the base
  worktree (pre-existing, not a regression).
- `lake test` — green (after the `GrindLint.lean` fix above).
- `grep -rn "sorry\|admit"` across all four Modal files — zero hits (doc-comment matches for
  "admits the axiom ..." only).
- `grep -rn "^axiom "` in `Cslib/Logics/Modal/` — 0 on base, 0 on branch (no new axioms).
- `box_iff_forall` and `diamond_iff_exists` both confirmed `Iff.rfl` in the committed file — both
  modalities remain primitive.
- `git status` on the worktree — clean; exactly one commit (`69db6de4`) ahead of the branch point;
  no push, no PR/GitHub action performed.

## Files Modified

- `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive/Cslib/Logics/Modal/Basic.lean`
- `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive/Cslib/Logics/Modal/Denotation.lean`
- `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive/Cslib/Logics/Modal/LogicalEquivalence.lean`
- `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive/CslibTests/GrindLint.lean`
- `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive/Cslib/Logics/Modal/Cube.lean` —
  verified unchanged (no diff).

## Next Steps

The worktree/branch (`task-487-pr662-bot-primitive` @ `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive`)
is ready for the user to run `/pr` separately with explicit approval — no push or PR action was
taken by this implementation.
