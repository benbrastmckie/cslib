# Implementation Plan: Task #527

- **Task**: 527 - Fix `lake test` failure in `CslibTests/ModalFrameSeparation.lean` (stuck `decide` on S5/Five separation checks)
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/527_fix_modal_frame_separation_decide/.orchestrator-handoff.json (research findings inline)
- **Artifacts**: plans/01_fix-decide-frame-separation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md, plan-compliance.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

`lake build CslibTests.ModalFrameSeparation` fails at lines 32 and 37: the `decide` tactics on
`s5Valid`/`fiveValid` cannot reduce because `instDecidableS5Valid` / `instDecidableFiveValid`
route through `modalExpandBranchesGen`, whose nested `let rec processNext` compiles to
`WellFounded.fix` and does not reduce in the kernel. The fix replaces the two stuck `decide`
examples with the already-proven, already-compiling separation theorems `boxImp_s5Valid` and
`boxImp_not_fiveValid` (both in `FrameSoundness.lean`, transitively imported), exactly mirroring
the `kb5Valid` case at line 42. This is a zero-debt, axiom-free, single-file change. Docstrings are
updated so they no longer claim the checks route through `decide`.

### Research Integration

- **Root cause** (research-confirmed): `instDecidableS5Valid` (FrameCompleteness.lean:2422) and
  `instDecidableFiveValid` (FrameCompleteness.lean:3213) reduce a `match` on
  `modalTableauS5`/`modalTableauFive`, which route through `modalTableauGen` ->
  `modalExpandBranchesGen` (Saturation.lean:201,363). The nested `let rec processNext` compiles to
  `WellFounded.fix`, whose `Acc` proof does not reduce in the kernel, so `decide` gets stuck.
- **Not a regression**: latent since the test landed with `by decide`; not caused by the KB5 work.
  Working tree is clean for the modal area.
- **Fix = Option (b)**: mirror the existing `kb5Valid` pattern (line 42) using proven theorems.
  Both exist and compile: `boxImp_s5Valid (p : Unit) : s5Valid (.imp (.box (.atom p)) (.atom p))`
  (FrameSoundness.lean:1343) and `boxImp_not_fiveValid : ¬ fiveValid (Atom := Unit) (.imp (.box
  (.atom ())) (.atom ()))` (FrameSoundness.lean:1349). Line 43's `boxImp_not_kb5Valid` already
  resolves, proving `FrameSoundness` is transitively imported.
- **Rejected alternatives**: Option (a) — refactoring `modalExpandBranchesGen` to structural
  recursion — is disproportionate and risky (its docstring requires the exact original elaborated
  term to avoid regressing K proofs across `Tableau/`). `native_decide` introduces
  `trustCompiler`/`ofReduceBool` axioms discouraged by CSLib/Mathlib. Neither is to be pursued.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; no roadmap phases added.

## Goals & Non-Goals

**Goals**:
- Make `lake build CslibTests.ModalFrameSeparation` and `lake test` pass green.
- Replace the two stuck `decide` examples with the proven separation theorems, mirroring the
  `kb5Valid` case, with zero new axioms and zero new proof debt.
- Update the module and per-example docstrings so they accurately describe the new approach.

**Non-Goals**:
- Refactoring `modalExpandBranchesGen` or any driver in `Saturation.lean` (Option a — rejected).
- Introducing `native_decide` or any axiom-bearing tactic.
- Any change outside `CslibTests/ModalFrameSeparation.lean`.
- Restoring a computable `decide`-based check for S5/Five (out of scope; the driver limitation is
  inherent).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Theorem signatures differ from what research reported (arg count, implicit `Atom`) | M | L | Verify signatures with `lean_hover_info` before editing; the `kb5Valid` mirror at line 42 confirms the pattern |
| Switching `Atom` from `Bool` to `Unit` misaligns with proven theorems | M | L | Both theorems are stated at `Atom := Unit` with `.atom ()`; the existing kb5 example already uses `Unit`/`.atom ()` |
| Docstring edits leave stale claims about `decide` routing | L | M | Update all three docstrings (module ~11-22, S5 ~28-30, Five ~34-35) in the same phase; grep for "decide"/"Decidable" after editing |
| Full `lake test` surfaces an unrelated failure | L | L | Scope build first (`lake build CslibTests.ModalFrameSeparation`); if `lake test` fails elsewhere, report as out-of-scope, do not expand |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single phase; no parallelism.

### Phase 1: Replace stuck `decide` examples with proven separation theorems [COMPLETED]

**Goal**: Rewrite the two failing examples to use `boxImp_s5Valid` / `boxImp_not_fiveValid`,
switch `Atom` to `Unit`, update the three docstrings, and verify green.

**Tasks**:
- [x] (Optional, recommended) Confirm the two theorem signatures via `lean_hover_info` on
  `boxImp_s5Valid` (FrameSoundness.lean:1343) and `boxImp_not_fiveValid` (FrameSoundness.lean:1349)
  so the replacement terms typecheck as written. *(confirmed via direct source read; both
  signatures matched the plan exactly)*
- [x] Replace lines 31-32 (the S5 `decide` example) with:
  ```lean
  example : s5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) :=
    boxImp_s5Valid ()
  ```
- [x] Replace lines 36-37 (the Five `decide` example) with:
  ```lean
  example : ¬ fiveValid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) :=
    boxImp_not_fiveValid
  ```
- [x] Update the S5 example docstring (~lines 28-30): remove the claim that the check is done "via
  the tableau's `Decidable` instance (`instDecidableS5Valid`) ... exercises the actual decision
  procedure"; state instead it is proved via the ported separation theorem `boxImp_s5Valid`
  (`FrameSoundness.lean`), consistent with the `kb5Valid` case.
- [x] Update the Five example docstring (~lines 34-35): remove "Checked via `instDecidableFiveValid`";
  state it is proved via `boxImp_not_fiveValid` (`FrameSoundness.lean`).
- [x] Update the module docstring (~lines 11-22): remove the sentence asserting the checks confirm
  `instDecidableS5Valid`/`instDecidableFiveValid` "genuinely route through their respective frame
  conditions ... not silently collapsing onto one another" via the decision procedure; reframe so
  all three separation checks (S5-valid, not-5-valid, not-KB5-valid) are described as proved via the
  ported separation theorems in `FrameSoundness.lean`. Keep the copyright header and `module`/`import`
  lines unchanged.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `CslibTests/ModalFrameSeparation.lean` - replace two `decide` examples (lines 31-32, 36-37) with
  proven-theorem terms; switch `Atom` from `Bool`/`.atom false` to `Unit`/`.atom ()`; update three
  docstrings (module ~11-22, S5 ~28-30, Five ~34-35). No other files change.

**Verification**:
- `lake build CslibTests.ModalFrameSeparation` succeeds (no "got stuck" reduction errors).
- `lake test` is green.
- `grep -n -iE 'decide|instDecidable' CslibTests/ModalFrameSeparation.lean` returns no stale
  docstring claims that the S5/Five checks route through `decide`/the `Decidable` instances.
- No new axioms introduced (the replacement terms are plain theorem applications; optionally confirm
  with `lean_verify` on the examples, though `example`s are anonymous).

---

## Testing & Validation

- [x] `lake build CslibTests.ModalFrameSeparation` compiles with no errors.
- [x] `lake test` passes (green).
- [x] The file uses `Atom := Unit` / `.atom ()` consistently across all three examples (matching the
  existing `kb5Valid` example).
- [x] No `native_decide`, no new `axiom`, no `sorry` introduced.
- [x] Docstrings accurately describe the ported-theorem approach; no residual "routes through
  `decide`" claims.

## Artifacts & Outputs

- Modified `CslibTests/ModalFrameSeparation.lean` (two examples rewritten, three docstrings updated).
- Green `lake test` run.

## Rollback/Contingency

- Single-file change; `git checkout -- CslibTests/ModalFrameSeparation.lean` restores the prior
  (failing) committed state if needed.
- If either replacement term fails to typecheck (unexpected signature), use `lean_hover_info` /
  `lean_goal` to inspect the actual theorem type and adjust the argument (e.g. `boxImp_s5Valid ()`
  argument) to match; do NOT fall back to `decide` or `native_decide`.
- If `lake test` reveals an unrelated pre-existing failure elsewhere, report it as out-of-scope for
  this task rather than expanding the change.
