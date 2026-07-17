# Implementation Plan: Composite Conservativity Bridges to the Classical Column

- **Task**: 520 - Add missing composite bridges collapsing each non-classical base into the classical column
- **Status**: [COMPLETED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_composite-conservativity-bridges.md
- **Artifacts**: plans/01_composite-conservativity-bridges.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add 8 composite `_implies_` theorems to
`Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean`, each collapsing a non-classical
base (minimal `M*` or constructive `C*`) into the classical column at the same modal rung
(K/T/S4/S5). Every composite is a pure one-line function composition of an existing Axis-B
monotonicity edge (`base -> intuitionistic`, already in scope via
`PropositionalStrengthMonotonicity`) with an existing Intuitionistic->Classical bridge
(`intuitionistic -> classical`, in `IntToClassical.lean`). The only structural change beyond
the theorems is a single new `public import` of `IntToClassical`, which is not currently
reachable (even transitively) from `Modularity.lean`. No new proof content, no `sorry`, no new
axioms — each composite inherits the axiom footprint of its two landed constituents. Definition
of done: file builds, all 8 names are `#print axioms`-clean at the expected classical closure,
and the full CI pipeline passes.

### Research Integration

From `reports/01_composite-conservativity-bridges.md`:
- All 8 composite names confirmed **absent** from the entire `Cslib/` tree (grep — "NONE FOUND").
- Both ingredient edge families exist and are landed: 8 Axis-B edges in
  `PropositionalStrengthMonotonicity.lean`; 4 Int->Classical bridges in `IntToClassical.lean`
  (`ikDerivable_implies_kDerivable` L496, `itDerivable_implies_tDerivable` L539,
  `is4Derivable_implies_s4Derivable` L650, `is5Derivable_implies_s5Derivable` L768).
- THE ONE GAP: `Modularity.lean` does not import `IntToClassical` transitively (verified by a
  full transitive-closure scan). The Axis-B lemmas are already in scope.
- CORRECTNESS NOTE 1 — S5 target: the classical S5 predicate is `ModalAxiom`, NOT `S5Axiom`; the
  two S5 composites conclude `Derivable (@ModalAxiom Atom) φ`, mirroring
  `is5Derivable_implies_s5Derivable`.
- CORRECTNESS NOTE 2 — naming: names MUST use `_implies_`. `Modularity.lean` reserves
  "conservative" strictly for genuine Axis-C results; do NOT name any of these `*conservative*`
  even though the task title says "conservativity bridges" (that is tracker prose, not the lemma
  name).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied to this planning dispatch; roadmap consultation skipped. No roadmap
wrapping phases requested (`roadmap_flag` not set).

## Goals & Non-Goals

**Goals**:
- Add the one required import: `public import Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical` to `Modularity.lean`.
- Add 8 composite theorems (4 minimal-base, 4 constructive-base), each a one-line composition, with a docstring on each (docBlame lint).
- Preserve the file's naming discipline (`_implies_`, never `conservative`) and its subsection organization.
- Verify zero `sorry`, expected axiom closure `[propext, Classical.choice, Quot.sound]`, and green full CI.

**Non-Goals**:
- No new abstraction, helper lemma, or lift — all needed machinery (`Derivable_mono`, the edges, the bridges) pre-exists.
- No changes to `PropositionalStrengthMonotonicity.lean` or `IntToClassical.lean`.
- No Axis-C ("conservative") results; no new rungs or intermediate edges (research confirms none are missing).
- No PR creation or push (agents are prohibited; task terminates at implementation complete).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Wrong S5 target predicate (`S5Axiom` instead of `ModalAxiom`) | M | L | Both S5 composites MUST conclude `Derivable (@ModalAxiom Atom) φ`; copy signatures verbatim from research §3 and mirror `is5Derivable_implies_s5Derivable`. |
| Name uses `conservative` and violates file discipline | M | L | Use `_implies_` exclusively; run a grep for `conservative` in the added block before build. |
| Import placed out of order / duplicated | L | L | Insert `IntToClassical` in the existing import group; it sorts before `IntuitionisticLatticeMonotonicity`. |
| Missing docstring triggers docBlame lint | L | M | Add a one-line docstring to each of the 8 theorems, modeled on existing composite docstrings. |
| Unexpected axiom footprint | L | L | `#print axioms` / `lean_verify` on all 8 fully-qualified names; expected `[propext, Classical.choice, Quot.sound]` inherited from the classical bridges. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Add import and 8 composite theorems [COMPLETED]

- **Goal:** Land the one required import and all 8 documented composite theorems in
  `Modularity.lean`, then confirm the file compiles in isolation.
- **Tasks:**
  - [x] Add `public import Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical` to the import group (sorts before `IntuitionisticLatticeMonotonicity`).
  - [x] Add a new subsection heading after the existing `## Cross-Axis Composites (Axis B then Axis A)` block and before `## Axis C`, e.g. `/-! ## Cross-Axis Composites Into the Classical Column (Axis B then Int->Classical) -/`.
  - [x] Add the 4 minimal-base composites inside `namespace Cslib.Logic.Modal`: `mkDerivable_implies_kDerivable`, `mtDerivable_implies_tDerivable`, `ms4Derivable_implies_s4Derivable`, `ms5Derivable_implies_s5Derivable` (this one concludes `Derivable (@ModalAxiom Atom) φ`).
  - [x] Add the 4 constructive-base composites: `ckDerivable_implies_kDerivable`, `ctDerivable_implies_tDerivable`, `cs4Derivable_implies_s4Derivable`, `cs5Derivable_implies_s5Derivable` (this one concludes `Derivable (@ModalAxiom Atom) φ`).
  - [x] Give each theorem a one-line docstring (docBlame), modeled on existing composite docstrings.
  - [x] Each body is the pure composition `<int->classical> (<base->int> h)` from research §3; make no other edits.
  - [x] Confirm no `conservative` token appears in the added block (grep); confirm all are `theorem` (not `def`).
  - [x] Scoped build: `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Modularity`. *(deviation: a concurrent, uncommitted, unrelated in-flight edit to `Constructive/Segment.lean` by a separate task briefly broke this scoped build's transitive dependency chain; verified green via an isolated `git worktree` + hardlinked build-cache copy while that edit was live, then re-confirmed directly in the main tree once the concurrent edit cleared. See Phase 2 CI verification notes.)*
- **Timing:** ~30 minutes
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean` — add 1 import + 1 subsection heading + 8 documented theorems.
- **Verification:**
  - Scoped `lake build ...Modularity` succeeds with zero errors and zero `sorry`.
  - All 8 names present; S5 composites conclude `ModalAxiom`; no `conservative` naming.

### Phase 2: Axiom check and full CI verification [COMPLETED]

- **Goal:** Confirm the axiom footprint and green the full CI pipeline before handoff.
- **Tasks:**
  - [x] Run `#print axioms` (or `lean_verify`) on all 8 fully-qualified names, e.g. `Cslib.Logic.Modal.ms5Derivable_implies_s5Derivable`; confirm each closes to `[propext, Classical.choice, Quot.sound]`. *(deviation: actual closure is `[propext, Quot.sound]` for all 8 -- a strict subset of the expected set; `Classical.choice` is simply not needed by any of the 8 composites. Not a defect.)*
  - [x] Confirm zero `sorry` across the added declarations.
  - [x] Run full CI in order: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test` (and `lake shake` if desired). All ran; results: `lake build` green (3237 jobs); `checkInitImports` green; `lake lint` shows exactly 1 pre-existing error unrelated to this file (`Foundations/Logic/Metalogic/PrimeExclusion.lean` unusedArguments); `lake exe lint-style` green (0 issues); `lake shake` on this module reports zero suggestions (the single new import is minimal); `lake test` fails only in `CslibTests.ModalFrameSeparation` -- the pre-existing KB5/Five-simplification decidability issue from a separate concurrent task, explicitly out of this task's scope per the implementation dispatch.
  - [x] Address any lint/style feedback (expected: none beyond docstrings already added). None required.
- **Timing:** ~15 minutes (dominated by build/CI wall-clock)
- **Depends on:** 1
- **Files to modify:**
  - None expected (verification only); minor lint fixes to `Modularity.lean` only if CI flags them.
- **Verification:**
  - `#print axioms` closure is exactly `[propext, Classical.choice, Quot.sound]` for all 8.
  - Full CI pipeline passes green.

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Modularity` succeeds (scoped).
- [x] Zero `sorry` in the 8 new theorems.
- [x] `#print axioms` / `lean_verify` on all 8 names yields `[propext, Classical.choice, Quot.sound]` (actual: `[propext, Quot.sound]`, a subset -- see Phase 2 deviation note).
- [x] `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test` all pass (except the pre-existing, out-of-scope `CslibTests.ModalFrameSeparation` KB5/Five failure from a separate concurrent task -- see Phase 2 notes).
- [x] No `conservative` token in the added block; all 8 are `theorem`; S5 composites conclude `Derivable (@ModalAxiom Atom) φ`.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean` (modified: 1 import + 8 theorems + subsection heading)
- `specs/520_composite_conservativity_bridges_to_classical_column/plans/01_composite-conservativity-bridges.md` (this plan)
- `specs/520_composite_conservativity_bridges_to_classical_column/summaries/01_composite-conservativity-bridges-summary.md` (produced at implementation completion)

## Rollback/Contingency

Changes are confined to a single additive block plus one import in `Modularity.lean`. To revert,
remove the new subsection (8 theorems + heading) and the `IntToClassical` import line; the file
returns to its prior state with no cross-file impact (no other file is edited). If the scoped
build or CI fails, fix forward (correct the affected signature/body/docstring in place) rather
than discarding uncommitted work.
