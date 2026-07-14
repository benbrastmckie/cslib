# Task 488: Frame-Correspondence Biconditionals for Cube.lean

## Summary

Added a new `## Correspondence` section to `Cslib/Logics/Modal/Cube.lean`, immediately after
the existing `## Canonicity` section, containing one frame-correspondence biconditional per
axiom that has an associated frame condition (T, B, 4, 5, D — K is excluded per the task spec
since it has no frame condition).

Each new theorem unifies two directions that were already present and green in the file:
- **Backward** (axiom valid on frame ⇒ frame property): the existing `*_canonical` lemma.
- **Forward** (frame property ⇒ axiom valid on frame): the existing per-model `Satisfies.*`
  lemma, instantiated via `haveI` against the frame's relation `r` and re-generalized over the
  canonical lemma's `{v} {w} {φ}` binder shape.

## Theorems Added

| Theorem | Frame condition | Backward (mp) | Forward (mpr) |
|---|---|---|---|
| `T.t_correspondence` | `Std.Refl r` | `T.t_canonical` | `Satisfies.t` |
| `B.b_correspondence` | `Std.Symm r` | `B.b_canonical` | `Satisfies.b` |
| `Four.four_correspondence` | `IsTrans World r` | `Four.four_canonical` | `Satisfies.four` |
| `Five.five_correspondence` | `Relation.RightEuclidean r` | `Five.five_canonical` | `Satisfies.five` |
| `D.d_correspondence` | `Relation.Serial r` | `D.d_canonical` | `Satisfies.d` |

## Implementation Note

An initial term-mode attempt (`⟨_canonical, fun h => haveI ... ; fun {v}{w}{φ} => Satisfies.*⟩`)
failed to elaborate: the anonymous-constructor + inline `haveI`/lambda combination caused Lean to
prematurely instantiate the outer `∀ {v}{w}{φ}` binder with fresh metavariables before the
`Satisfies.*` application, producing type mismatches (`Satisfies.t φ` expected to inhabit a bare
`Prop` rather than the `∀`-quantified statement). Switched to a `by refine ⟨_canonical, fun h =>
?_⟩; haveI ... ; intro v w φ; exact Satisfies.* φ` tactic-block for the `mpr` direction, which
elaborates cleanly with `intro` handling the implicit binders explicitly. All 5 theorems follow
this same shape.

## Verification

- `lake build Cslib.Logics.Modal.Cube` — green (module-scoped).
- `lake build` (full project) — green (2759/2759 jobs).
- `lake exe checkInitImports` — pass (exit 0).
- `lake lint` — pass, no warnings ("Linting passed for Cslib").
- `lake exe lint-style Cslib/Logics/Modal/Cube.lean` — no issues (only a pre-existing,
  unrelated `nolints-style.txt` missing-file warning).
- `lake shake --add-public --keep-implied --keep-prefix` — the one Cube.lean suggestion
  (`add public import Cslib.Foundations.Relation.Euclidean`) was verified **pre-existing**
  (present identically when checked against the unmodified HEAD commit `69db6de4` via
  `git stash`), i.e. not introduced by this change. All other suggestions in the shake output
  are baseline repo-wide noise in unrelated files, untouched by this task.
- `lake exe mk_all --module` — regenerated `CslibTests.lean` with an unrelated pre-existing
  module-header drift (baseline repo noise, not caused by this task); reverted via
  `git checkout -- CslibTests.lean` per the "touch ONLY Cube.lean" constraint. `Cube.lean` was
  already listed in `Cslib.lean` (no new files added, so no listing change was needed).
- `lake test` — full `CslibTests` suite green (8790/8790 jobs).
- `sorry` count in `Cslib/`: **0**.
- New `axiom` count in `Cslib/`: **0** (one pre-existing vacuous-pattern match in
  `Cslib/Computability/URM/Basic.lean:92` is unrelated to this task).
- `mcp__lean-lsp__lean_verify` on all 5 new theorems: axioms = `["propext", "Classical.choice",
  "Quot.sound"]` (standard Mathlib/CSLib baseline, no new axioms), zero warnings.

## Plan Deviations

None. This task had no prior research/plan artifacts (dispatched directly as a fully-specified
capstone); the only adaptation was the term-mode → tactic-mode switch for the `mpr` direction
documented above, which was a mechanical elaboration fix, not a scope change.

## Scope

Touched only `Cslib/Logics/Modal/Cube.lean` (+55 lines, net). No other files in the diff.
`CslibTests.lean` was touched transiently by `mk_all` and reverted before the commit.

## Branch / Commit

- Worktree: `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive`
- Branch: `task-487-pr662-bot-primitive`
- Commit: `b041c6f7` ("task 488: add frame-correspondence biconditionals to Cube.lean"),
  on top of `69db6de4` (the current #662 tip).
- Not pushed; GitHub PR #662 not touched, per instructions.
