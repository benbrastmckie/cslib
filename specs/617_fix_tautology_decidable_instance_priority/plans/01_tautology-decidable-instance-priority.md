# Implementation Plan: Fix `Decidable (Tautology φ)` Instance Priority Collision

- **Task**: 617 - fix_tautology_decidable_instance_priority
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: `specs/617_fix_tautology_decidable_instance_priority/reports/01_tautology-decidable-instance-priority.md`
- **Artifacts**: plans/01_tautology-decidable-instance-priority.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Two registered instances target `Decidable (Tautology φ)`: the kernel-reducible Boolean
enumeration `instDecidableTautology` (`Semantics/Bool.lean:185`) and the kernel-inert tableau
decider `instDecidableTautologyTableau` (`Tableau/Classical/DecisionProcedure.lean:81`). Both
carry default priority, so the later-declared tableau instance wins wherever both are in scope —
which is every consumer of the `Cslib` barrel — making `decide` on `Tautology` unusable
downstream. The fix is a single `(priority := 100)` token at the tableau declaration site, plus a
regression guard that puts both instances in scope inside `CslibTests/Propositional.lean` so the
7 existing `by decide` tautology tests stop passing by accident of import order. Definition of
done: the red baseline is demonstrated first, the fix flips `#synth` back to
`instDecidableTautology`, a `#guard_msgs in #synth` pin locks that selection, docstrings record
why the priority is lowered, and the full CSLib CI pipeline is green.

### Research Integration

The research report re-verified every claim in the task description against HEAD `212318f2` and
adds three findings that this plan adopts directly:

1. **Declaration-site form verified.** `instance (priority := 100) instDecidableTautologyTableau`
   builds, and all three downstream importers (`ProofSystemEquivalence`,
   `Tableau/Classical.lean`, `SequentCalculus/LK/Decidability.lean`) stay green (988 jobs,
   exit 0). The numeric `100` — not `low` — matches the four existing priority annotations in
   `Cslib/`.
2. **Red baseline is exactly 7.** A copy of `CslibTests/Propositional.lean` with one added
   tableau import produces exactly 7 ``Tactic `decide` failed`` errors and no others; with the
   fix it is exit 0.
3. **`#guard_msgs in #synth` works** and pins instance selection by name, giving a guard whose
   failure message identifies the defect rather than only reporting stuck reduction.

Also adopted: the report's negative finding that the Intuitionistic/Minimal analogues do **not**
collide (their FMP routes are `noncomputable def`s, deliberately unregistered), so nothing is
bundled in; and its consumer audit showing `LK/Decidability.lean` and `StrongCompleteness.lean`
see no selection change.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` carries no line item for this defect — it is a correctness fix, not new
coverage. It protects the already-shipped decidability surface listed under "Shared
infrastructure & propositional bases" (`Logics/Propositional/`) and "Tableau decision procedures
(generic driver)": the classical propositional `Decidable` instances are recorded there as
delivered, and this task restores the property that they are actually usable by a consumer of the
barrel. No ROADMAP.md edit is required or permitted by this plan.

### Scope Decision: `Semantics/Bool.lean`

The research report flagged that `Cslib/Logics/Propositional/Semantics/Bool.lean` lies outside
the task's declared `file_scope`. **Decision: extend scope to include it**, for a prose-only
docstring note at `:181-187` recording that `instDecidableTautology` is the preferred instance
when `Fintype Atom` is available. Rationale: the priority annotation is only half-legible if the
other side of the pair says nothing; the change has zero elaboration surface; and Phase 4 runs a
full build regardless, so the wider recompile it triggers costs nothing beyond time already
budgeted.

## Goals & Non-Goals

**Goals**:
- Lower `instDecidableTautologyTableau` to `(priority := 100)` at its declaration site so the
  kernel-reducible Boolean decider wins whenever both instances apply.
- Demonstrate the red baseline before applying the fix, so the guard is proven meaningful.
- Convert the 7 accidentally-passing `by decide` tautology tests into deliberately-passing ones
  by putting both instances in scope in `CslibTests/Propositional.lean`.
- Add a `#guard_msgs in #synth` pin that fails with a message naming the wrong instance.
- Record the rationale in docstrings so the annotation cannot be "cleaned up" back into the
  defect.
- Full CSLib CI green.

**Non-Goals**:
- Making the tableau decision procedure kernel-reducible. The `#eval`-vs-`decide` split is
  expected and documented at `CslibTests/TableauConformance.lean:30`.
- Removing or deprecating `instDecidableTautologyTableau`. It must remain the sole candidate in
  the `Fintype`-free case (verified by the report).
- Any change to the Intuitionistic or Minimal tableau/FMP modules — verified non-colliding.
- Fixing the two pre-existing `linter.unusedDecidableInType` warnings on
  `ivalid_universe_invariant` and `mvalid_universe_invariant`. Present at HEAD, unrelated.
- Creating a new test file. The guard goes in the existing `CslibTests/Propositional.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Lowering priority breaks a `Fintype`-free consumer that relied on the tableau instance | H | L | Report verified the `Fintype`-free fallback still resolves; `LK/Decidability.lean:175` audited (no `Fintype` in scope, selection unchanged). Phase 1's interface-tier build covers the enumerated dependents |
| `public meta import` alone is insufficient for the test file | M | L | Report empirically confirmed the meta-only form compiles all 7 tests. If a `may not access declaration ... imported as 'meta'` error appears, add the plain `import` alongside, mirroring `CslibTests/TableauConformance.lean:36-40` |
| Red baseline commits a broken tree | M | M | Phase 1 is declared `Commit Mode: atomic-batch`: the red intermediate state is expected and MUST NOT be committed; one commit covers the whole batch once green |
| `#guard_msgs` message text drifts with a Lean/Mathlib bump, making the pin brittle | L | M | The pinned message is a single `#synth` result line, not a proof term; if it drifts, update the expected string — the pin failing loudly is the intended behavior |
| Docstring edits trip `lake exe lint-style` line-length or `lake lint` docBlame | L | M | Phase 3 is prose-tier but Phase 4 runs both linters; keep lines within the file's existing width |
| Full build time (Mathlib cache cold) | M | M | Run `lake exe cache get` before the Phase 4 pipeline, per the CSLib CI verification order |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel. Phases 2 and 3 touch disjoint file sets
(Phase 2: `CslibTests/Propositional.lean`; Phase 3: `DecisionProcedure.lean` and
`Semantics/Bool.lean`), so parallel execution is safe.

---

### Phase 1: Red Baseline, Then Priority Fix [COMPLETED]

**Goal**: Reproduce the defect against a known-red baseline, then apply the one-token
declaration-site fix and confirm the tree returns to green.

**Tasks**:
- [x] Add to `CslibTests/Propositional.lean`, alongside the existing imports at `:9-11`:
      `public meta import Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure`
- [x] Run `lake build CslibTests.Propositional` **before** editing `DecisionProcedure.lean`.
      Record the failure count and the verbatim first error message in the phase notes. Do not
      commit this state.
- [x] Confirm the failures are ``Tactic `decide` failed`` on the tautology `example`s at
      `:64-90` and that no other error class appears.
- [x] Edit `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean:81`, changing
      `instance instDecidableTautologyTableau (φ : Proposition Atom) :` to
      `instance (priority := 100) instDecidableTautologyTableau (φ : Proposition Atom) :`.
      Use the numeric `100`, not `low` — matches the four existing annotations in `Cslib/`.
- [x] Rebuild `CslibTests.Propositional`: expect 0 errors.
- [x] Build the changed module and its enumerated direct dependents (below): expect 0 errors.
- [x] Commit the batch once green.

**Phase Notes**: Red baseline confirmed exactly 7 `` Tactic `decide` failed `` errors at lines
64, 70, 74, 77, 81, 85, 91 (no other error class); first error verbatim:
`` CslibTests/Propositional.lean:66:64: Tactic `decide` failed for proposition
decide (Tautology (Proposition.atom false ∨ (Proposition.atom false → Proposition.bot))) = true ``
(reduction stalls unfolding `instDecidableTautologyTableau`). After the `(priority := 100)` edit,
`lake build CslibTests.Propositional` and the four-target dependent build both exited 0. Direct
importer grep confirmed the enumerated three-file set exactly (no larger set found).

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: The red baseline is hypothesized to produce **exactly 7**
``Tactic `decide` failed`` errors and no errors of any other class, corresponding to the 7
`example`s at `CslibTests/Propositional.lean:64-90`. Confirm by counting error lines in the
Phase 1 pre-fix build output (e.g. piping the build output through a `Tactic .decide. failed`
match and counting). A count other than 7, or the presence of a different error class, means the
blast radius differs from what research measured — record the actual count and message before
proceeding, and do not silently accept the divergence.

The enumerated direct-dependent set for the `interface` tier is hypothesized to be exactly the
three importers of `DecisionProcedure` identified by research:
`Cslib.Logics.Propositional.ProofSystemEquivalence`,
`Cslib.Logics.Propositional.Tableau.Classical`, and
`Cslib.Logics.Propositional.SequentCalculus.LK.Decidability`. Confirm at implementation time
with a grep for importers of `Tableau.Classical.DecisionProcedure` under `Cslib/`; if the set is
larger, build the larger set.

**Files to modify**:
- `CslibTests/Propositional.lean` - add one `public meta import` of the tableau decision
  procedure module
- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` - insert
  `(priority := 100)` on the `instDecidableTautologyTableau` instance at `:81`

**Verification**:
- Pre-fix: `lake build CslibTests.Propositional` fails with the counted `decide` errors
  (Scope Hypothesis above)
- Post-fix: `lake build CslibTests.Propositional` exits 0
- Post-fix: `lake build Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure
  Cslib.Logics.Propositional.ProofSystemEquivalence
  Cslib.Logics.Propositional.Tableau.Classical
  Cslib.Logics.Propositional.SequentCalculus.LK.Decidability` exits 0
- Working tree is committed exactly once for this phase, at the green end state

---

### Phase 2: Instance-Selection Regression Pin [NOT STARTED]

**Goal**: Add a `#guard_msgs in #synth` pin so a future regression fails with a message that
names the wrong instance directly, rather than only reporting stuck reduction.

**Tasks**:
- [ ] Add to `CslibTests/Propositional.lean`, in the `## Decidable Tautology Tests` section
      (immediately before the `example`s at `:64`), with a short docstring explaining that the
      pin exists to keep the kernel-reducible instance selected:
      ```lean
      /-- info: instDecidableTautology (Proposition.atom false → Proposition.atom false) -/
      #guard_msgs in
      #synth Decidable (Tautology (Atom := Bool) (.imp (.atom false) (.atom false)))
      ```
- [ ] Update the file's module docstring (`:13-25`) to mention that the file deliberately imports
      the tableau decision procedure so the `Decidable (Tautology _)` tests exercise the
      both-instances-in-scope configuration.
- [ ] Build the module and confirm the pin passes.
- [ ] Commit.

**Timing**: 0.25 hours

**Depends on**: 1

**Verification Tier**: local

**Files to modify**:
- `CslibTests/Propositional.lean` - one `#guard_msgs in #synth` pin plus a module-docstring note

**Verification**:
- `lake build CslibTests.Propositional` exits 0
- Sanity check (optional, do not commit): temporarily reverting `(priority := 100)` makes the pin
  fail naming `instDecidableTautologyTableau`

---

### Phase 3: Docstring Rationale [NOT STARTED]

**Goal**: Record at both declaration sites why the tableau instance carries a lowered priority,
so the annotation is not removed by a future contributor as apparent noise.

**Tasks**:
- [ ] `DecisionProcedure.lean:74-80` — extend the `instDecidableTautologyTableau` docstring: the
      priority is deliberately lowered because this instance does not reduce in the kernel
      (it stalls on `WellFounded.fix`), so `decide` must fall through to the Boolean enumeration
      whenever `Fintype Atom` is available; it remains the sole candidate in the `Fintype`-free
      case, where priority never comes into play.
- [ ] `DecisionProcedure.lean:16` — soften the module header from "delivers the `Decidable
      (Tautology φ)` instance" to "a `Decidable (Tautology φ)` instance ... at lowered priority",
      which no longer overstates the module's role.
- [ ] `Cslib/Logics/Propositional/Semantics/Bool.lean:181-187` — note that
      `instDecidableTautology` is the preferred instance when `Fintype Atom` is available and is
      the one `decide` uses.
- [ ] Confirm every edited hunk lies inside a docstring/comment region (diff read-through).
- [ ] Commit.

**Timing**: 0.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: Three docstring sites are asserted — `DecisionProcedure.lean:74-80`,
`DecisionProcedure.lean:16`, and `Semantics/Bool.lean:181-187`. Line numbers are from research
against HEAD `212318f2` and are hypotheses: confirm each by reading the surrounding lines before
editing, and locate the declaration by name (`instDecidableTautologyTableau`,
`instDecidableTautology`, the module `/-! # ... -/` header) rather than by line number if it has
drifted.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` - instance docstring and
  module-header wording
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - preferred-instance note (scope extension,
  see Overview)

**Verification**:
- Diff read-through: every changed hunk is inside a `/-- -/`, `/-! -/`, or `--` region; no code
  token is touched
- Line widths stay within the surrounding file's convention (checked properly by `lake exe
  lint-style` in Phase 4)

---

### Phase 4: Full CI Gate [NOT STARTED]

**Goal**: Run the complete CSLib verification pipeline and confirm the whole repository is green
with no new warnings attributable to this change.

**Tasks**:
- [ ] `lake exe cache get` (fetch Mathlib `.olean` cache before the full build)
- [ ] `lake build`
- [ ] `lake exe checkInitImports`
- [ ] `lake lint`
- [ ] `lake exe lint-style`
- [ ] `lake test`
- [ ] Diff the warning set against the HEAD baseline: the two pre-existing
      `linter.unusedDecidableInType` warnings on `ivalid_universe_invariant`
      (`Tableau/Intuitionistic/DecisionProcedure.lean:159`) and `mvalid_universe_invariant`
      (`Tableau/Minimal/DecisionProcedure.lean:173`) are expected and must NOT be fixed here. Any
      other new warning is in scope for this task.
- [ ] Commit.

**Timing**: 0.75 hours

**Depends on**: 2, 3

**Verification Tier**: full

**Files to modify**: none (verification only)

**Verification**:
- All six pipeline commands exit 0
- `lake test` reports no failures; `CslibTests/Propositional.lean` in particular is green with
  both instances in scope
- New-warning diff against HEAD is empty apart from the two documented pre-existing ones

**Notes**:
- `lake exe mk_all --module` is NOT needed: no new file is added.
- `lake shake` is not a risk: it is disabled in CI
  (`.github/workflows/lean_action_ci.yml`, step commented out with a recorded rationale), and the
  local invocation is scoped to the `Cslib` target, which does not cover `CslibTests/`. The
  instance-only test import will therefore not be flagged as unused, and the priority annotation
  changes no imports, so `scripts/check-shake-residue.sh`'s baseline is unaffected.

---

## Testing & Validation

- [ ] Red baseline reproduced and its error count recorded before any fix is applied (Phase 1)
- [ ] `#synth Decidable (Tautology (Atom := Bool) (.imp (.atom false) (.atom false)))` resolves to
      `instDecidableTautology` with both modules in scope
- [ ] All 7 `by decide` tautology `example`s at `CslibTests/Propositional.lean:64-90` compile with
      the tableau module imported
- [ ] The 6 `BoolEvaluate` `decide` theorems and `tautology_soundness` /
      `boolEvaluate_complete` remain green (they do not route through a
      `Decidable (Tautology _)` instance, so they should be unaffected)
- [ ] `#guard_msgs in #synth` pin passes and, under a temporary revert of the priority token,
      fails naming `instDecidableTautologyTableau`
- [ ] `Fintype`-free fallback still resolves: `example {A : Type} [DecidableEq A] [Hashable A]
      (φ : Proposition A) : Decidable (Tautology φ) := inferInstance` elaborates
- [ ] `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`
      all exit 0
- [ ] Zero-debt: no `sorry`, no new axiom, no vacuous definition introduced (structurally
      impossible for this change, but confirmed)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` — `(priority := 100)` on
  `instDecidableTautologyTableau`; instance docstring and module-header rationale
- `CslibTests/Propositional.lean` — one `public meta import` of the tableau decision procedure;
  one `#guard_msgs in #synth` instance pin; module-docstring note
- `Cslib/Logics/Propositional/Semantics/Bool.lean` — preferred-instance docstring note
- `specs/617_fix_tautology_decidable_instance_priority/plans/01_tautology-decidable-instance-priority.md`
  (this file)
- `specs/617_fix_tautology_decidable_instance_priority/summaries/01_tautology-decidable-instance-priority-summary.md`

## Rollback/Contingency

- The change is three files, all additive or single-token; `git revert` of the phase commits
  restores HEAD behavior exactly.
- If the `interface`-tier build in Phase 1 reveals an unanticipated dependent that regresses,
  revert only the `DecisionProcedure.lean` token, keep the test import as a documented red
  marker, and mark Phase 1 `[BLOCKED]` with the failing module and its goal/elaboration error —
  do not paper over it with a consumer-side `attribute [instance 100]`, which would leave the
  barrel defect intact.
- If `public meta import` proves insufficient in the test file, escalate to the dual
  `import X` + `public meta import X` idiom (`CslibTests/TableauConformance.lean:36-40`) before
  treating it as a blocker.
- If the red baseline count diverges from 7, stop and record the actual count and error classes
  in the phase notes before proceeding; a larger blast radius may indicate an additional consumer
  that research did not see.
