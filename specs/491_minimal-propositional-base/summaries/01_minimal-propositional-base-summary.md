# Implementation Summary: Task #491

- **Task**: 491 - Minimal propositional base (efq-optional)
- **Plan**: specs/491_minimal-propositional-base/plans/01_minimal-propositional-base.md
- **Type**: cslib (verification-only)
- **Session**: sess_1784044271_09e821_491

## Outcome

**Confirmed: the requested efq-optional minimal propositional base already exists in full on
`main` and builds green.** This was a verification-only task per the research report and plan;
zero new definitions, markers, or `Derivation` clones were created, per the explicit reuse-first
prohibition in the plan's Non-Goals.

## Phase 1: Verify Existing Minimal-Base Infrastructure Compiles — COMPLETED

- Scoped build of the four target modules
  (`Metalogic.MinLindenbaum`, `ProofSystem.IntMinInstances`, `NaturalDeduction.Basic`,
  `NaturalDeduction.Equivalence`) succeeded: **"Build completed successfully (729 jobs)."**
- `min_consistent : ¬ Derivable MinPropAxiom ⊥` confirmed present and type-checked at
  `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean:219`.
  `lean_verify Cslib.Logic.PL.min_consistent` reports only the three standard Mathlib axioms
  (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no unexpected axioms. A targeted
  `grep` for `sorry` across the four target files returned zero matches.
- efq gating spot-confirmed by direct read (no edits):
  - `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:182` — the ND `efq` constructor
    carries `[IsIntuitionistic T]`, so it is structurally unconstructible at `MPL` (minimal)
    strength.
  - `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` — `HasAxiomEFQ` is registered
    only for `Propositional.HilbertInt` (line 67); the `HilbertMin` instance block
    (lines 107-164) has no EFQ instance.
- This matches the research report's findings exactly; no drift detected.

## Phase 2: Documentation Note and Full CI Confirmation — PARTIAL

- **Optional docstring note skipped** (sanctioned by the plan): `Equivalence.lean` already
  documents `minimal`, `IsMinimal`, and the Hilbert/ND bridge extensively (module header
  lines 13-35; `MinimalAxioms`/`IsMinimal` section lines 158-189), substantially overlapping the
  proposed cross-reference content. Adding a redundant note risked a style-lint touch for no
  clear benefit, so the zero-diff outcome was preferred per the plan's own permission
  ("if the implementer judges a doc note redundant... it may add nothing and simply run CI").
- **CI pipeline result — mixed, root cause is out of task 491's scope**:
  - `lake exe lint-style` — ran clean, no output.
  - `lake build` (full project), `lake test`, `lake exe checkInitImports`,
    `lake shake --add-public --keep-implied --keep-prefix` — all fail identically at
    `Cslib/Logics/Modal/Tableau/Defs.lean:244:6` (`split` tactic failure on an `if`/`match`
    expression).
  - **Root cause identified**: `git diff -- Cslib/Logics/Modal/Tableau/Defs.lean` shows 37 lines
    of **uncommitted, in-progress edits** (new `modalNegOf?_eq_some`, `modalOrOf?_eq_some`,
    `modalAndOf?_eq_some`, `modalImpOf?_eq_some` lemmas) that predate this session and belong to
    an unrelated, concurrently in-flight task in the Modal Tableau area — not Propositional, not
    task 491's scope. `git log` confirms the last *committed* change to that file was task 441;
    nothing in task 491's work touches `Cslib/Logics/Modal/`.
  - Per the plan's own guidance ("If Phase 1 build unexpectedly fails, do NOT close the gap by
    adding new definitions -- capture it as a distinct regression for a separate fix task and
    stop"), this was reported, not fixed. The unrelated file was left untouched.
  - **Re-confirmed unaffected**: the scoped Phase 1 build target
    (`MinLindenbaum`, `IntMinInstances`, `NaturalDeduction.Basic`, `NaturalDeduction.Equivalence`)
    was re-run after discovering the blocker and remains green (729 jobs), and
    `git diff --stat -- Cslib/Logics/Propositional/` is empty.

## Plan Deviations

1. **Phase 2 optional docstring note**: skipped, not altered — judged redundant with existing
   documentation (see above). Sanctioned explicitly by the plan text.
2. **Phase 2 full CI confirmation**: partial, not fully green — `lake build` / `lake test` /
   `lake exe checkInitImports` / `lake shake` are all blocked by an unrelated, pre-existing,
   uncommitted change to `Cslib/Logics/Modal/Tableau/Defs.lean` on the shared working tree
   (belongs to a different, concurrently in-flight task). `lint-style` passed. Task 491's own
   verification target (the Propositional minimal-base modules and `min_consistent`) is fully
   confirmed green and was independently re-verified after the blocker was found.

## Zero-Diff Confirmation

`git diff --stat -- Cslib/Logics/Propositional/` is empty. No new declarations, no proof-logic
changes, no new axioms, no `sorry` introduced. Task 491 made no source changes to `Cslib/`.

## Recommendation

Per the research report's Rollback/Contingency section, the user retains two closure options:
1. Treat this verification as sufficient confirmation that task 491's original objective was
   already satisfied by prior tasks (185/187/191/367/409) and close 491 accordingly.
2. Re-run the full CI pipeline (`lake build`, `lake test`, `checkInitImports`, `lake shake`) once
   the unrelated concurrent Modal Tableau work is committed or reverted, to obtain a fully green
   whole-repo confirmation (expected to pass, since the blocker is provably unrelated to the
   Propositional minimal-base area verified here).

`requires_user_review: true` is preserved from the research phase per the orchestrator's
instruction, both for the original already-satisfied-task question and for visibility into the
unrelated full-CI blocker discovered during this session.
