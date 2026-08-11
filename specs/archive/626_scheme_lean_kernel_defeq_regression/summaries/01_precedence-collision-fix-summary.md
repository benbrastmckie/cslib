# Implementation Summary: Precedence-Collision Fix for Scheme.lean Non-Termination

- **Task**: 626 - Root-cause and fix the Scheme.lean build non-termination introduced by the Connectives/Operators migration
- **Status**: [COMPLETED]
- **Plan**: specs/626_scheme_lean_kernel_defeq_regression/plans/01_precedence-collision-fix.md
- **Research**: specs/626_scheme_lean_kernel_defeq_regression/reports/02_defeq-mechanism-and-fix.md
- **Branch**: `task-619-phase8-wip` (worktree; NOT merged to main — deliberately deferred, see below)
- **Session**: sess_1786462543_b0741b

## What Was Wrong

`Cslib/Foundations/Logic/Operators.lean` declared `scoped infixr:30 " ∨ " => HasOr.or` and
`scoped infixr:25 " → " => HasImp.imp` — exact token+precedence+associativity collisions with
core `Or` (infixr:30) and the core function arrow (infixr:25). When the Connectives/Operators
migration activated these scoped notations across `Cslib.Logic.*` (branch `task-619-phase8-wip`,
base `1e88ad3e`), every Prop-level `→`/`∨` parsed as a two-way `choice` node and nested chains
cost exponential elaborator backtracking, unbounded by any heartbeat budget (per-alternative
deterministic-timeout exceptions are swallowed by `observing` in choice elaboration).
`Scheme.lean`'s 29-arrow chain went from seconds to >34 min DNF, breaking the `Cslib` barrel.

## What Was Changed

Three commits on `task-619-phase8-wip` (each phase-gated and committed green):

| Commit | Phase | Change |
|--------|-------|--------|
| `128c42ee` | 1 | `Operators.lean`: `∨` `infixr:30` → `infixr:31`; `→` `infixr:25` → `infixr:26` (mirrors `HasAnd`'s pre-existing collision-free `infixr:36` vs core 35) |
| `c331c9e5` | 2 | `LoopChecking.lean`: deleted the `set_option maxHeartbeats 1000000` band-aid and its misattributing comment (builds green at default budget) |
| `3b0caf3b` | 3 | `Connectives.lean` docstring guard + new `CslibTests/OperatorPrecedenceRegression.lean` (72 lines: rfl grouping pins for `a ∧ b ∨ c → a` structure and `a → b → c` right-nesting, plus 24-arrow / 24-`∨` flat-elaboration performance gates) + registration in `CslibTests.lean` |

No other Lean files were touched. Zero `sorry` introduced (repo-wide raw `sorry` grep count is
312 at both base `1e88ad3e` and HEAD — delta 0), zero new `maxHeartbeats`, zero new axioms,
zero task-number citations in Lean files.

## Phase 4 Full-Library Gate (measured results)

Run in the live worktree, clean at `3b0caf3b`:

- **Full `lake build`**: exit 0, exactly **3331 jobs** (the plan-predicted count), wall
  **1.76s** as a warm-cache full replay — the cold compile (~7 min, 3331 jobs) happened during
  phase 1-3 verification and every artifact replayed valid.
- **`Cslib` barrel**: built and present (`.lake/build/lib/lean/Cslib.olean`); `lake build Cslib`
  exits 0. **The barrel is broken on `main`; on this branch it is green** — a load-bearing
  outcome of this work.
- **Regression guard**: `lake build CslibTests.OperatorPrecedenceRegression` exit 0 (519 jobs).
- **`lake exe checkInitImports`**: exit 0. **`lake exe lint-style`**: exit 0.
- **Test driver (`lake test`, testDriver = `CslibTests`)**: exit 1. Nine modules built green
  (including `AncestorRedirectRefutation`, `HilbertSearch`, `ContextDecidability`,
  `S4LoopGuardRegression`, ...); **six modules fail: `BetaSplitRefutation`, `Propositional`,
  `MinProbe`, `TableauConformance`, `WitnessProbe`, `WitnessSearch3`**. See next section — all
  six are pre-existing base breakage, not caused by this task.
- `lake lint`, `lake shake`, `lake exe mk_all` were not run in phase 4: `shake`/`mk_all` mutate
  Lean files (prohibited by the phase's no-Lean-edits territory and would dirty the committed
  worktree handed to the follow-up task); the phase's plan-declared gate is full build + barrel
  + test driver.

## The Six Failing Test Modules Are Pre-Existing (evidence)

1. Base commit `1e88ad3e` (the preserved migration WIP) **deleted the PL-local scoped
   notations** (`scoped infix:36 " ∧ "`, `infix:35 " ∨ "`, `infix:30 " → "` bound to
   `Proposition` constructors) from `Cslib/Logics/Propositional/Defs.lean`; they still exist on
   `main` (lines 107-109). The six failing files consume exactly those notations via
   `open Cslib.Logic.PL`.
2. `open Cslib.Logic.PL` does **not** activate the parent-namespace `Cslib.Logic` scoped
   notations from `Operators.lean` — probe-verified: a minimal file with only
   `open Cslib.Logic.PL` reproduces the identical `Or pr` / "type expected" errors at HEAD,
   independent of the precedence values.
3. All six failing files are **byte-identical between base and HEAD**
   (`git diff 1e88ad3e..HEAD -- CslibTests/` touches only `OperatorPrecedenceRegression.lean`),
   so they were equally red at base, before any fix commit.
4. **Verified repair path** (for the follow-up task): adding `open Cslib.Logic` alongside
   `open Cslib.Logic.PL` makes `(pr ∨ ps)`, nested `→` chains, and the mixed
   `((pr ∨ ps) ∧ ((ps → (ps → pr)) → X)) → pr` shape elaborate via the `HasOr`/`HasImp`/`HasAnd`
   instances with `rfl`-verified constructor grouping (probe with two `example ... := rfl`
   checks passed). Alternatively, restore PL-local notations at collision-free precedences.

## What Is Now Unblocked: Handoff to the Blocked Follow-Up Task (619 phase 8)

Task 619 phase 8 (merge of the Connectives/Operators migration) was blocked on this task. To
consume this fix, it needs to know:

- **Branch**: `task-619-phase8-wip`, tip `3b0caf3b` = base `1e88ad3e` + the three fix commits
  above. Live worktree (clean, warm `.lake`):
  `/tmp/claude-1000/-home-benjamin-Projects-cslib/622a4407-4dc9-4cb5-b6f8-f7c190e5bbfe/scratchpad/wt`
- **Already verified on that tip** (do not re-derive): full `lake build` green at 3331 jobs
  including the `Cslib` barrel; Scheme.lean sentinel bounded (~29s warm); `LoopChecking` green
  at default heartbeats; regression guard module green; `checkInitImports` and `lint-style`
  green; zero sorry delta vs base.
- **Remaining work before merge** (619's own unfinished "downstream repairs", NOT part of this
  task): repair the six pre-existing red test modules named above. The verified minimal repair
  is adding `open Cslib.Logic` to each (evidence item 4 above); after that, re-run `lake test`
  to green, then merge to `main`.
- **Merge-to-main is deliberately deferred** to 619 phase 8 per settled plan decision — nothing
  was rebased, merged, cherry-picked, or pushed by this task.

## Plan Deviations

- **Phase 4 build wall time**: predicted ~7 min cold; observed 1.76s because the worktree's
  `.lake` was fully warm from phase 1-3 gates. Job count matched the prediction exactly (3331).
- **Test driver gate closed as [COMPLETED WITH EXCLUSIONS]** instead of plain green: `lake test`
  exits 1 due to the six pre-existing red modules documented above (full Reasoned Exclusions
  record in the plan's Phase 4 section). The plan's contingency for an unexpected full-gate
  failure ("first suspect the phase-3 test file or a stale `.lake` artifact") was followed: the
  phase-3 test file is green and the failure root-cause was pinned to the base commit's
  notation deletion with a four-item evidence chain.
- No other deviations: all other phase tasks executed as written.
