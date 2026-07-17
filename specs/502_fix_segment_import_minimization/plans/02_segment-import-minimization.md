# Implementation Plan: Task #502

- **Task**: 502 - Fix Segment.lean import minimization (replace transitive PrimeTheory import with two direct imports), now consumer-first
- **Status**: [NOT STARTED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/502_fix_segment_import_minimization/reports/01_segment-import-minimization.md
- **Artifacts**: plans/02_segment-import-minimization.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/state-management.md
  - .claude/rules/artifact-formats.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` `public import`s
`Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` (line 10) but consumes zero
PrimeTheory-local declarations. The v1 plan replaced that single line with two direct
`public import`s (PrimeExclusion + DerivationTree). Segment.lean itself built green, but the
edit BROKE the sole downstream consumer,
`Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean`, with 6 `Unknown identifier`
errors: `modalDeductiveClosure` (x4) and `deductionTheorem` (x2). Those two symbols reach
SegmentLindenbaum ONLY through Segment.lean's old transitive `public import` re-export of
PrimeTheory; SegmentLindenbaum never imports their declaring modules directly. The v1
implementation correctly reverted Segment.lean to HEAD (zero delta) per its
Rollback/Contingency section.

This revised plan restructures the work into an ordered, consumer-first sequence: fix
SegmentLindenbaum's imports FIRST (purely additive, independently green), THEN re-apply the
original Segment.lean edit (now safe), THEN verify the whole tree with `lake build` and
`lake shake` and settle the minimal-import set empirically. Definition of done: `lake build`
green for Segment.lean + SegmentLindenbaum.lean + all dependents; `lake shake` no longer flags
the PrimeTheory line on Segment.lean and introduces no new unresolved-import issues; both files
retain `import Cslib.Init`; zero `sorry`.

### Research Integration

Verified symbol-provenance details carried forward from the research report (all confirmed
against the codebase during v1):

- **Segment.lean's own direct consumption** traces to exactly two modules:
  - `PrimeAdmissible` (`QuasiPrime` abbrev) / `DeductivelyClosed`
    -> `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (lines 63, 44)
  - `DerivationTree` + constructors (`.ax`, `.modus_ponens`, `.weakening`, `.assumption`) +
    `modalDerivationSystem` -> `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (lines 134, 234)
  - `Proposition` + `◇`/`□` scoped notation -> `Cslib/Logics/Modal/Basic.lean` (public-imported by
    DerivationTree)
  - `DerivationSystem` -> `Cslib/Foundations/Logic/Metalogic/Consistency.lean` (public-imported by
    both PrimeExclusion and DerivationTree)
- **The v1 blocker's newly-discovered fact** (NOT in the original research, discovered during
  implementation): the downstream consumer SegmentLindenbaum.lean directly consumes two
  PrimeTheory-transitive symbols that Segment.lean itself never uses:
  - `modalDeductiveClosure` (4 uses, SegmentLindenbaum.lean lines 160, 189, 217, 259)
    -> declared in `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean:78`
  - `deductionTheorem` (2 uses, SegmentLindenbaum.lean lines 391, 429)
    -> declared in `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean:64`
  SegmentLindenbaum.lean's only content import is
  `import Cslib.Logics.Modal.Metalogic.Constructive.Segment` (plus `Cslib.Init`); it relied
  entirely on Segment.lean's old `public import ...PrimeTheory` re-export for both symbols.
- **Downstream blast radius** (files that transitively import SegmentLindenbaum.lean and would
  break with it): `MinExtension.lean`, `MinPrimeTheory.lean`, `CKTruthLemma.lean`, and further
  downstream. Verifying SegmentLindenbaum.lean green transitively protects these.
- **`import Cslib.Init` is mandatory** in every Cslib file (CONTRIBUTING.md, enforced by
  `lake exe checkInitImports`). Shake's suggestion to drop it is the known systemic out-of-scope
  false positive and must be ignored in BOTH files.

### Prior Plan Reference

Supersedes `plans/01_segment-import-minimization.md` (single-phase, single-file). That plan
reached `[BLOCKED]` at Phase 1: its prescribed Segment.lean edit was correct in isolation but
broke SegmentLindenbaum.lean because the plan's declared scope forbade touching a second file.
This revision widens scope to two files and orders the edits consumer-first so no intermediate
state is red. The v1 Phase-1 blocker documentation is the authoritative record of the failure
and its root cause.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided). This task advances library-hygiene / import
minimization surfaced by a prior CSLib vet.

## Goals & Non-Goals

**Goals**:
- Add direct `public import`s of PrimeTheory and DeductionTheorem to SegmentLindenbaum.lean so it
  no longer depends on Segment.lean's transitive re-export (Phase 1).
- Replace Segment.lean's transitive `public import ...PrimeTheory` with two direct
  `public import`s (PrimeExclusion + DerivationTree) once the consumer is safe (Phase 2).
- Reach a shake-clean tree where BOTH files import exactly what they directly use, verified by
  `lake build` + `lake shake`, settling the final minimal set empirically (Phase 3).
- Preserve `import Cslib.Init` in both files.

**Non-Goals**:
- No new definitions, abstractions, axioms, or `sorry` -- pure import restructuring.
- No notation changes; existing scoped `◇`/`□` usage is unaffected.
- Do NOT act on shake's project-wide `import Cslib.Init` flag (out of scope, false positive).
- No edits to files other than Segment.lean and SegmentLindenbaum.lean (unless Phase 3's empirical
  shake reconciliation strictly requires an import adjustment in one of these two files -- never a
  third file).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Phase-1 imports written as plain (non-`public`) when SegmentLindenbaum's public signatures need `public` | M | M | Implementer checks whether `modalDeductiveClosure`/`deductionTheorem` appear in SegmentLindenbaum's public signatures; use `public import` if so, verify by shake re-flag if wrong. Empirically settle in Phase 3. |
| Phase 2 re-breaks consumer because Phase 1 was skipped or incomplete | H | L | Strict phase ordering: Phase 2 `Depends on: 1`; Phase 1 must build green (with Segment.lean still at HEAD) before Phase 2 begins. |
| After Phase 2, shake reports Phase-1 imports on SegmentLindenbaum as now-redundant | M | M | Explicit Phase-3 reconciliation step: run shake on both files, settle the minimal set empirically. See caveat below. |
| Accidentally removing `import Cslib.Init` on shake's advice | M | L | Plan forbids in both files; `lake exe checkInitImports` enforces. |
| Build breakage from missing transitive symbol on Segment.lean side | H | L | Research traced full public-import closure; `lake build` gates each phase. |

**Phase-3 shake-reconciliation caveat (must be called out to the implementer)**: After Phase 2,
both `PrimeExclusion+DerivationTree` (on Segment.lean) and `PrimeTheory` (on SegmentLindenbaum.lean)
are in the import graph. `modalDeductiveClosure` reaches SegmentLindenbaum only via PrimeTheory
(unaffected by Segment.lean's change), so PrimeTheory should remain shake-justified there.
However, shake computes justification from the whole graph, so it is possible shake will judge one
of the Phase-1 additions redundant (e.g. if a symbol is now reachable by a shorter path). The
implementer MUST run `lake shake` on both files after Phase 2 and settle the FINAL minimal import
set empirically: keep an import iff shake says it is directly needed and `lake build` stays green
without over-importing. The net target is a shake-clean tree where each file imports exactly what
it directly uses, with `import Cslib.Init` retained in both regardless of what shake says about it.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Fully sequential; no parallelism. Each phase must be green before the next begins.

### Phase 1: Add direct imports to SegmentLindenbaum.lean (consumer-first prerequisite) [NOT STARTED]

**Goal**: Give SegmentLindenbaum.lean its own direct `public import`s of the two modules whose
symbols it currently gets only transitively through Segment.lean, so it no longer depends on
Segment.lean's PrimeTheory re-export. This phase is purely additive and independently green
(Segment.lean is untouched here, still carrying its old transitive re-export).

**Tasks**:
- [ ] Open `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean` and confirm its
      current content imports are `import Cslib.Init` and
      `import Cslib.Logics.Modal.Metalogic.Constructive.Segment` (verify line numbers; do not
      assume).
- [ ] Add two direct imports for the symbols SegmentLindenbaum uses directly:
      `Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` (provides `modalDeductiveClosure`)
      and `Cslib.Logics.Modal.Metalogic.DeductionTheorem` (provides `deductionTheorem`).
- [ ] Determine `public` vs plain for each: inspect whether `modalDeductiveClosure` /
      `deductionTheorem` appear in SegmentLindenbaum's PUBLIC (exported / `@[expose] public
      section`) signatures. If a symbol is referenced only inside proof bodies / private scope, a
      plain `import` suffices; if it appears in a public signature, use `public import`. When
      unsure, start with `public import` (safe, never under-exports) and let Phase 3 shake
      downgrade to plain if shake reports the `public` as unjustified. Record the choice.
- [ ] Keep `import Cslib.Init` exactly as-is; do not remove or reorder it.
- [ ] Do NOT modify Segment.lean in this phase -- it must still carry its original
      `public import ...Intuitionistic.PrimeTheory` line so this phase's greenness is proven
      additively (the new direct imports coexist with the still-present transitive re-export).
- [ ] Build to confirm green: `lake build Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum`
      (and, cheaply if desired, the dependents `MinExtension`, `MinPrimeTheory`, `CKTruthLemma`).

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean` - add two direct imports
  (PrimeTheory + DeductionTheorem); keep `import Cslib.Init`; leave the existing Segment import.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum` succeeds with no errors
  while Segment.lean is still at its original HEAD content.
- The 6 previously-failing identifiers (`modalDeductiveClosure` x4, `deductionTheorem` x2) resolve
  via the new direct imports.
- `import Cslib.Init` still present.

### Phase 2: Re-apply the Segment.lean two-import replacement (now safe) [NOT STARTED]

**Goal**: Execute the original v1 edit -- replace Segment.lean's single transitive
`public import ...Intuitionistic.PrimeTheory` with two direct `public import`s -- which is now
safe because Phase 1 gave the consumer its own direct imports.

**Tasks**:
- [ ] Open `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` and confirm the current import
      block is `import Cslib.Init` (line 9) followed by
      `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` (line 10).
- [ ] Replace the PrimeTheory line with two direct `public import`s, Foundations-before-Logics
      ordering (matching PrimeTheory's own convention):
      `public import Cslib.Foundations.Logic.Metalogic.PrimeExclusion`
      and `public import Cslib.Logics.Modal.Metalogic.DerivationTree`.
- [ ] Both MUST be `public`: Segment's declarations sit under `@[expose] public section` and
      reference these types in public signatures; dropping `public` would re-break shake /
      downstream visibility.
- [ ] Leave `import Cslib.Init` exactly as-is; do NOT remove it (CONTRIBUTING.md mandate; shake
      false positive).
- [ ] Build to confirm the consumer no longer breaks:
      `lake build Cslib.Logics.Modal.Metalogic.Constructive.Segment` then
      `lake build Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum` -- both green. The
      6 `Unknown identifier` errors must NOT reappear (they are now covered by Phase 1's direct
      imports).

**Timing**: 0.25 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` - replace line 10 (one `public import`)
  with two direct `public import`s (PrimeExclusion + DerivationTree); keep line 9 unchanged.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Segment` succeeds.
- `lake build Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum` succeeds (no
  `Unknown identifier` regressions).
- Both new Segment.lean imports are `public`; `import Cslib.Init` remains present.

### Phase 3: Whole-tree build + shake reconciliation (settle minimal import set) [NOT STARTED]

**Goal**: Confirm the full dependent tree builds green and reach a shake-clean state where both
files import exactly what they directly use, settling the final minimal set empirically.

**Tasks**:
- [ ] Run a full `lake build` (or at minimum the Segment / SegmentLindenbaum / MinExtension /
      MinPrimeTheory / CKTruthLemma dependent chain) and confirm zero errors and zero `sorry`.
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` and confirm:
      (a) the PrimeTheory line is NO longer flagged on Segment.lean;
      (b) the imports ADDED to SegmentLindenbaum.lean in Phase 1 are themselves shake-clean --
      i.e. shake does not report them as redundant/unjustified.
- [ ] Reconcile per the Phase-3 caveat: if shake flags a Phase-1 addition on SegmentLindenbaum as
      now-redundant (or a `public` as needlessly public), adjust THAT file's import list
      accordingly (drop a genuinely-redundant import, or downgrade `public import` to plain
      `import`) and re-run `lake build` + `lake shake` until the set is minimal AND green. Keep
      iterating until each file imports exactly what it directly uses. Confine all edits to
      Segment.lean and SegmentLindenbaum.lean.
- [ ] Confirm `import Cslib.Init` remains present in BOTH files regardless of shake's flag on it
      (it is the known out-of-scope false positive; `lake exe checkInitImports` enforces keeping
      it).
- [ ] Confirm zero `sorry` introduced (`grep`/build clean).

**Timing**: 0.25 hours

**Depends on**: 2

**Files to modify**:
- Only if reconciliation requires: `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean`
  and/or `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` (minimal-set adjustment). No
  third file.

**Verification**:
- `lake build` (Segment + SegmentLindenbaum + dependents) green.
- `lake shake --add-public --keep-implied --keep-prefix` shows the PrimeTheory line resolved on
  Segment.lean and no NEW unresolved/redundant-import issues on either edited file (the
  project-wide `import Cslib.Init` flag is expected and out of scope).
- `import Cslib.Init` present in both files; zero `sorry`.

---

## Testing & Validation

- [ ] Phase 1: `lake build ...SegmentLindenbaum` green with Segment.lean still at HEAD.
- [ ] Phase 2: `lake build ...Segment` and `lake build ...SegmentLindenbaum` both green; no
      `Unknown identifier` regressions.
- [ ] Phase 3: full/dependent-chain `lake build` green; `lake shake` clean on both edited files
      (PrimeTheory line resolved on Segment.lean, Phase-1 additions justified on
      SegmentLindenbaum.lean).
- [ ] `import Cslib.Init` present in both files (satisfies `lake exe checkInitImports`).
- [ ] Segment.lean's two replacement imports are `public`.
- [ ] Zero `sorry`, zero new axioms, no vacuous placeholders.

## Artifacts & Outputs

- Modified `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean` (added direct
  imports of PrimeTheory + DeductionTheorem).
- Modified `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` (transitive PrimeTheory import
  replaced by direct PrimeExclusion + DerivationTree imports).
- plans/02_segment-import-minimization.md (this file).
- summaries/02_segment-import-minimization-summary.md (on completion).

## Rollback/Contingency

Two-file change with strict ordering. If Phase 1 fails to build, revert SegmentLindenbaum.lean
(`git checkout` the one file) and re-investigate the symbol paths before retrying; Segment.lean is
untouched at this point so the tree stays green. If Phase 2 fails, revert Segment.lean to its
original single `public import ...PrimeTheory` line (git checkout of the one file) -- Phase 1's
additive imports on SegmentLindenbaum are harmless with the old re-export present, so the tree
remains green. If Phase 3 shake reconciliation cannot reach a clean state, keep the last
build-green import set (correctness over minimality) and document the residual shake flag rather
than leaving the tree red.
