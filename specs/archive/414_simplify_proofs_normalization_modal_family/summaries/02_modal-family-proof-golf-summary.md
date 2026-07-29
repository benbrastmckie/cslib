# Implementation Summary: Simplify Modal/Temporal/Bimodal Proofs via Existing Normalization Lemmas

- **Task**: 414 - simplify_proofs_normalization_modal_family
- **Plan**: `specs/414_simplify_proofs_normalization_modal_family/plans/02_modal-family-proof-golf.md` (v2)
- **Status**: implemented
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Type**: cslib

## What Was Done

This revision (v2) narrowed the original four-file scope to a single file after a sibling
proof-golf task landed the other three files' changes first (see plan v2's "Research
Integration" section). The remaining executable work was Phase 1 (the `and`/`or` arms of
`bimodal_truthAt_toBimodal_iff_satisfies`) plus Phase 4 (the gate and sorry-freeness audit).
Phases 2 and 3 were already closed `[COMPLETED WITH EXCLUSIONS]` at plan-revision time and were
re-confirmed, not redone, per the resume instructions.

### Phase 1: ModalConservativity `and`/`or` arms [COMPLETED]

File: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`

Collapsed the hand-rolled classical reasoning (`constructor` / `by_contra` / `Classical.em`
case splits, 10 lines each) in both the `and` and `or` arms of
`bimodal_truthAt_toBimodal_iff_satisfies` to single-line forms using backward IH rewrites plus
`tauto`:

- `and` arm: `simp only [Modal.Proposition.toBimodal, Bimodal.Formula.and, truthAt,
  Modal.Satisfies, ← ih1 w, ← ih2 w]; tauto` (matches the plan's verified form exactly).
- `or` arm: `simp only [Modal.Proposition.toBimodal, truthAt, Modal.Satisfies, ← ih1 w,
  ← ih2 w]; tauto` -- this drops `Bimodal.Formula.or` from the plan's literal first-attempt form.
  Both forms were verified via `lean_multi_attempt` to close the goal; the literal form (with
  `Bimodal.Formula.or` included) elaborated with an `unusedSimpArgs` linter warning on that
  argument, and the linter's own suggested fix (omitting it) was independently verified to close
  the goal with zero warnings. This is recorded as a plan deviation in Phase 1's task list.

Both arms confirmed via `lean_goal`: goal state is "no goals" immediately after the tactic line,
with no dangling tactics. The `box` and `diamond` arms (44 lines, lines 186-230) were left
untouched per the plan's explicit Non-Goal, and `git diff` confirms zero hunks in that range.

Net diff for this file: 3 insertions, 20 deletions (18 tactic lines net removed across the two
arms).

### Phases 2 and 3: [COMPLETED WITH EXCLUSIONS] (re-confirmed, not redone)

Re-ran the plan's scope-hypothesis greps against
`Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`,
`Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`, and
`Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` (the sibling proof-golf task's target
files). All zero-match, confirming no residual `listImp_nil` / `unfold ListDeriv` /
`simp only [listImp_*|bigconj_*|toTemporal_*|toBimodal_*]` sites remain. No edits were made to
these three files.

### Phase 4: Gate and sorry-freeness audit [COMPLETED]

File-scoped audit (binding criterion):
- Scoped build (`lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity`):
  green, 712/712 jobs, no warnings.
- `grep -n "sorry"` on all four files this task ever claimed: zero matches.
- `lean_verify` on `bimodal_truthAt_toBimodal_iff_satisfies`: axioms are exactly `propext`,
  `Classical.choice`, `Quot.sound` (the standard three); no warnings.
- `git diff --stat`: exactly one modified source file.
- `git diff`: proof-body hunks only; no statement/attribute/import changes.
- `box`/`diamond` arms confirmed byte-identical (no hunk in that range).
- No hunk under `Tableau/`, `Cslib/Foundations/`, or `Cslib/Logics/Propositional/`.

Repo-wide gate (attribution-gated, all green -- nothing required attribution):
- `lake exe cache get`: already warm (0 files downloaded, 8651 decompressed).
- Full `lake build`: 3309/3309 jobs, exit 0.
- `lake exe checkInitImports`: silent success.
- `lake lint`: exit 0; all findings are pre-existing `unusedArguments` warnings in unrelated
  files (e.g. `NestingDepth.lean`, `FrameSoundness.lean`, `ChronicleConstruction.lean`,
  `DenseSoundness.lean`); zero findings in this task's file or the three excluded bridge files.
- `lake exe lint-style`: silent success.
- `lake test`: 9374/9374 jobs, exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: zero import-shape suggestions for any
  of the four files this task ever claimed; a handful of unrelated pre-existing suggestions in
  other files (`TimeM.lean`, `Deterministic.lean`, `StackTape.lean`, `Defs.lean`,
  `Confluence.lean`, `Free.lean`, `CCS/Basic.lean`, `CombinatoryLogic/Defs.lean`).
- `lake exe mk_all --module`: "No update necessary" (no new files were added).

Sorry-warning attribution: the full build and test runs both reported exactly 5
`declaration uses sorry` warnings, all under `Tableau/` directories --
`Modal/Tableau/FrameSoundness.lean:1252`, two sites in
`Propositional/Tableau/Intuitionistic/Scheme.lean` (observed at drifted line numbers 721/756 and
2638/2673 across the two separate gate runs, consistent with the plan's documented drift
caution -- the concurrent tableau session is actively editing this file),
`Propositional/Tableau/Intuitionistic/Completeness.lean:124`, and
`Propositional/Tableau/Minimal/Completeness.lean:118`. This matches the plan's stated 5-warning
baseline exactly; none of these sites is in this task's territory or attributable to this task's
edit.

## Plan Deviations

- **Phase 1, `or` arm (altered)**: used
  `simp only [Modal.Proposition.toBimodal, truthAt, Modal.Satisfies, ← ih1 w, ← ih2 w]; tauto`
  instead of the plan's literal first-attempt form that additionally included
  `Bimodal.Formula.or` in the simp set. The literal form was verified to close the goal but
  triggered an `unusedSimpArgs` linter hint; the reduced form (the linter's own suggested fix)
  was independently verified via `lean_multi_attempt` and `lean_goal` to close the goal with zero
  warnings. Recorded inline in Phase 1's task checklist. This satisfies rather than violates the
  plan's own "When NOT to Simplify" criterion 2 (elaboration must not gain fragility/noise).
- No task was skipped, deferred, or left incomplete. No site was reverted -- both arms compiled
  on their first verified attempt.

## Verification

- Scoped build: green (712/712).
- Full `lake build`: green (3309/3309).
- `lake exe checkInitImports`: pass.
- `lake lint`: pass (zero findings in touched/excluded files).
- `lake exe lint-style`: pass.
- `lake test`: pass (9374/9374).
- `lake shake --add-public --keep-implied --keep-prefix`: pass (zero suggestions for this task's
  files).
- `lake exe mk_all --module`: no update necessary.
- Sorry count: 0 in all four files this task ever claimed; 5 repo-wide, all attributed to the
  concurrent tableau session and matching the documented baseline.
- Axiom count: no new axioms; the touched theorem's axiom set is exactly the standard
  `propext`/`Classical.choice`/`Quot.sound`.
- Vacuous definitions: none introduced by this task (one pre-existing, unrelated instance exists
  at `Cslib/Computability/URM/Basic.lean:92`, outside this task's scope).

## Files Modified

- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` (the `and`/`or`
  arm proof bodies of `bimodal_truthAt_toBimodal_iff_satisfies`; no statement, attribute, or
  import change)

## Files Not Modified (Confirmed Excluded, Per Plan)

- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`

## Concurrency Note

A concurrent orchestrated session was active under `Cslib/Logics/*/Tableau/*` throughout this
implementation (visible in `git status` as modifications to
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` and unrelated `specs/` files).
No file under any `Tableau/` directory was touched by this task. The repo-wide gate runs picked
up that session's in-flight sorry and its line-number drift, both correctly attributed per the
plan's attribution protocol and not treated as this task's failure (there was no failure to
attribute in the first place -- all seven repo-wide steps exited 0).
