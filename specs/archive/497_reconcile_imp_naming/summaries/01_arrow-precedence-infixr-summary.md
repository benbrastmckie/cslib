# Implementation Summary: Reconcile `→` Notation Precedence and Associativity with Upstream

- **Task**: 497 - reconcile_imp_naming (retargeted to notation-only)
- **Plan**: specs/497_reconcile_imp_naming/plans/01_arrow-precedence-infixr-reconciliation.md
- **Research**: specs/497_reconcile_imp_naming/reports/01_arrow-notation-precedence-reconciliation.md
- **Status**: Implemented (all 3 phases COMPLETED / COMPLETED WITH EXCLUSIONS, CI green)

## What Changed

Moved the `→` connective notation from the fork's non-associative `infix:30` to upstream's
right-associative `infixr:25` in the four in-scope formula files, and moved the co-declared `↔`
from `infix:30` to `infixr:20` in the three files that declare it (Bimodal declares no `↔`).
Synced the two header docstring precedence tables (LTL, Temporal) to match.

### Files Modified

- `Cslib/Logics/Bimodal/Syntax/Formula.lean` — `→` declaration only (line 101)
- `Cslib/Logics/LTL/Syntax/Formula.lean` — `→`/`↔` declarations (lines 209-210) + docstring rows
  (lines 37-38)
- `Cslib/Logics/Modal/Basic.lean` — `→`/`↔` declarations (lines 234, 237)
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — `→`/`↔` declarations (lines 169-170) + docstring
  rows (lines 37-38)

11 lines changed total across 4 files (7 declaration lines + 4 docstring rows), matching the
plan's declared edit set exactly.

### Files Explicitly NOT Touched

- `Cslib/Logics/Propositional/Defs.lean` — out of scope, owned by a sibling task; confirmed
  untouched (`git status --short` empty for this file throughout).

## Phase Execution

- **Phase 1** (`interface` tier, `atomic-batch`): all 7 declaration lines edited and committed in
  a single commit (`3cd87c03`). Post-edit grep confirmed exactly 4 `infixr:25 " → "` and 3
  `infixr:20 " ↔ "` lines, 0 remaining `infix:30`. Marked `[COMPLETED]`.
- **Phase 2** (`prose` tier): the 2 LTL/Temporal docstring precedence tables synced (4 rows total)
  and committed (`63e91332`). Confirmed no `(infix, 30)` rows remain and `NOTATION.md` needed no
  edit. Marked `[COMPLETED]`.
- **Phase 3** (`full` tier): targeted build of the mechanically-regenerated 372-module dependency
  cone — exact match to the research baseline (module count, 2013 jobs, 0 errors, **32
  warnings**, the hard-gated count). All 8 capability-regression examples (arrow-chain
  elaboration in all 4 namespaces plus both `rfl` associativity/precedence checks) elaborated via
  a scratch file, which was deleted afterward. Marked `[COMPLETED WITH EXCLUSIONS]` because it
  relied on both pre-declared Reasoned Exclusions (targeted build substituting for the
  whole-repository build; `Propositional/Defs.lean` exclusion) — both Evidence cells confirmed
  with implementation-time output in the plan file.

## Verification / CI Pipeline

Full CSLib CI pipeline run after implementation:

| Step | Result |
|---|---|
| 0. Mathlib cache fetch | Already warm, no-op |
| 1. Scoped build | Superseded by Phase 3's 372-module targeted build (superset of the 4 edited modules) |
| 2. `lake exe checkInitImports` | Pass (no output) |
| 3. `lake lint` | 373 total warnings repo-wide; **0** in any of the 4 modified files (all pre-existing, unrelated) |
| 4. `lake exe lint-style` | Pass (no output) |
| 5. `lake shake --add-public --keep-implied --keep-prefix` | Pass — initially failed with "out-of-date oleans" (would have required a bare whole-repo `lake build`, forbidden by the plan's BUILD HAZARD); after `lake test` (step 7) completed a full build cleanly (apparently a concurrent session had already warmed the `Scheme.lean` cache since the research was written), shake was retried and completed in ~12-28s with 0 suggestions touching any of the 4 modified files |
| 6. `lake exe mk_all --module` | Pass ("No update necessary") |
| 7. `lake test` | Pass — 9397/9397 jobs, exit 0 |

Additional checks:
- `sorry` count in modified files: 0
- Vacuous-definition count in modified files: 0
- New axioms in modified files: 0
- `git status --short` for the 4 modified files: clean (committed)

## Plan Deviations

- Phase 3's task checklist item "Confirm `git status --short -- Cslib/` lists only the four
  in-scope files" was satisfied in spirit but not literal text: because Phases 1-2 committed the
  four files before Phase 3 ran, they no longer appear as dirty at Phase 3's verification point.
  The only entry `git status --short -- Cslib/` shows is a pre-existing, unrelated modification
  to `Cslib/Logics/Propositional/Tableau/Intuitionistic.lean` that predates this task and was
  never touched by it. `Propositional/Defs.lean` itself was independently confirmed untouched.
- Phase 3 closed `[COMPLETED WITH EXCLUSIONS]` rather than `[COMPLETED]` per the plan's own
  instruction, since both pre-declared Reasoned Exclusions were relied upon (see plan file for
  the confirmed Evidence cells).
- `lake shake` (CI pipeline step 5, not itself a plan phase) initially could not run to
  completion without triggering a bare whole-repository `lake build` — the exact operation the
  plan's BUILD HAZARD section forbids. Rather than force it, the CI pipeline's own step 7
  (`lake test`) was run first per the pipeline's declared step order, which happened to complete
  a full build cleanly (a concurrent session appears to have warmed the `Scheme.lean` cache in
  the interim). `lake shake` was then retried and passed. No forbidden bare `lake build` or bare
  `lake env lean` command was ever issued by this agent.

## Zero-Debt Posture

No `sorry`, no new axiom, no vacuous definition. Pure notation-declaration and docstring edits, as
anticipated by the research report and plan.
