# Implementation Plan: Dedup Minimal Canonical Model onto Generic Extension

- **Task**: 521 - Dedup Minimal Canonical Model onto Generic Extension
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_dedup-minimal-canonical-model.md
- **Artifacts**: plans/01_dedup-minimal-canonical-model.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib (Lean 4)
- **Lean Intent**: false

## Overview

Consolidate the duplicated MK-only minimal canonical-model machinery onto the generic,
frame-condition-parametric `MinExtension.lean`. `mk_completeness` is rewired to delegate to the
already-proved generic `mkvalidFC_completeness` instantiated at `Axioms := MKModalAxiom` and the
trivial frame condition `(fun {_} _ => True)`, preserving its exact public signature
(`MValid φ → Derivable MKModalAxiom φ`). Once `MinCompleteness.lean` no longer imports the bespoke
trio, the now-dead files `MinCanonicalModel.lean` (1089 lines) and `MinTruthLemma.lean` (257 lines)
are deleted, followed — as a separately gated, reversible phase — by the orphaned
`MinPrimeTheory.lean` (125 lines), reaching ~1471 deleted lines. Definition of done: full CSLib CI
green, zero `sorry`/`admit`/new `axiom`, and `mk_completeness`'s axiom set unchanged versus the
pre-refactor baseline.

### Research Integration

Findings from `reports/01_dedup-minimal-canonical-model.md` drive this plan:
- **Instantiation template**: `MT.lean:246-254` — `mkvalidFC_completeness FC` + 12
  anonymous-constructor lambdas (`.implyK … .idb`) + `h_canonFC` + `h_valid`. `MKModalAxiom`'s 12
  constructors (`MK.lean:68-105`) share the same names, so the 12-lambda block transfers verbatim.
- **Trivial frame condition**: MK targets plain `MValid`. Use `FC := (fun {_} _ => True)`, discharge
  `h_canonFC` with `trivial`, convert the hypothesis via `mvalid_iff_mvalidFC_true.mp h_valid`
  (`MinExtension.lean:100`). `mvalidFC_completeness` lives at `MinExtension.lean:1548`.
- **Preserved names**: only `mk_completeness` and `mk_soundness_completeness` have external
  consumers; both kept in place, same names/types/file. `mk_soundness_completeness`
  (`MinCompleteness.lean:71-73`) is `⟨mk_completeness, mk_soundness_derivable⟩` and is unchanged;
  `mk_soundness_derivable` stays in `MK.lean`.
- **Zero external consumers**: whole-`Cslib/`-tree grep confirms `MinCanonicalModel.lean`,
  `MinTruthLemma.lean`, and `MinPrimeTheory.lean` have zero external consumers. `MinExtension.lean`
  imports only `Birelational` + `Constructive.SegmentLindenbaum` and does not depend on any deleted
  file. The base is already sorry-free.
- **Barrel**: `Cslib.lean` lines 397 (`MinCanonicalModel`), 400 (`MinPrimeTheory`),
  401 (`MinTruthLemma`) are removed; 398 (`MinCompleteness`) and 399 (`MinExtension`) are kept.
  Regenerate via `lake exe mk_all --module`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (no roadmap_path/roadmap_flag provided).

## Goals & Non-Goals

**Goals**:
- Rewire `mk_completeness` to delegate to `mkvalidFC_completeness` with the trivial frame condition,
  keeping its exact public signature.
- Delete `MinCanonicalModel.lean` and `MinTruthLemma.lean` (the named trio's canonical-model core).
- Delete the orphaned `MinPrimeTheory.lean` (separately gated, reversible phase).
- Regenerate the `Cslib.lean` barrel to drop only the deleted modules.
- Verify full CSLib CI green with zero new axiom and an unchanged `mk_completeness` axiom set.

**Non-Goals**:
- No change to `mk_soundness_completeness`, `mk_soundness_derivable`, or any `MK.lean` declaration.
- No change to `MinExtension.lean`, `MT.lean`, `MS4.lean`, `MS5.lean` (MT/MS4/MS5 remain untouched).
- No renaming of any public theorem; no signature changes.
- No introduction of any `sorry`/`admit`/`axiom`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `(fun {_} _ => True)` binder mis-elaborates in the `mk_completeness` position | M | L | Same literal already compiles at `MinExtension.lean:101`; confirm via targeted `lake build` in Phase 1 before any deletion. |
| Anonymous-constructor block fails to resolve `.implyK …` against `MKModalAxiom` | M | L | Constructor names match `MK.lean:68-105`; mirror `MT.lean:249-252` verbatim; targeted build in Phase 1 catches any mismatch. |
| Universe mismatch (`MValid.{u,u}` vs `MValidFC.{u,u}`, `v := u`) | M | L | Matches the existing MT instantiation; verified by Phase 1 build. |
| `MinPrimeTheory.lean` has an unexpected dependency surfaced only by CI | L | L | Phase 3 is isolated, cleanly skippable, and reversible: revert its deletion + barrel line if CI regresses, without touching Phases 1-2. |
| Barrel regeneration drops or reorders `MinExtension`/`MinCompleteness` | H | L | Diff `Cslib.lean` after `mk_exe mk_all --module`; confirm 398/399 retained and only deleted-module lines removed. |
| Axiom set of `mk_completeness` changes | M | L | Phase 4 `lean_verify` compares against pre-refactor baseline captured before Phase 1 edits. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase
produces a green, independently committable milestone.

### Phase 1: Capture baseline and rewire mk_completeness [COMPLETED]

**Goal**: Replace `mk_completeness`'s bespoke `by_contra` proof with a delegation to
`mkvalidFC_completeness` at the trivial frame condition, keeping its exact signature — while the
old trio files are still present, so the rewire is proven in isolation.

**Tasks**:
- [x] Capture the pre-refactor axiom-set baseline: `lean_verify` on `mk_completeness` and
      `mk_soundness_completeness` (record the reported axiom set for the Phase 4 comparison).
      *(deviation: altered -- `lean_verify` consistently returned an empty axiom list for this
      project's LSP session even after a full build; used `git stash` to isolate the pre-edit
      file, then `lake env lean` + `#print axioms` for the authoritative check instead. Baseline
      for both `mk_completeness` and `mk_soundness_completeness`:
      `[propext, Classical.choice, Quot.sound]`.)*
- [x] In `MinCompleteness.lean`, swap `public import …Minimal.MinTruthLemma` →
      `public import …Minimal.MinExtension` (keep `import …Minimal.MK`; `open Cslib.Logic` already
      present).
- [x] Replace the `mk_completeness` body (currently `MinCompleteness.lean:55-67`) with the
      delegation form from research §3: `mkvalidFC_completeness (fun {_} _ => True)` + the 12
      anonymous-constructor lambdas (`.implyK … .idb`, mirroring `MT.lean:249-252`) + `trivial`
      (for `h_canonFC`) + `(mvalid_iff_mvalidFC_true.mp h_valid)`. Signature stays
      `MValid.{u, u} φ → Derivable MKModalAxiom φ`.
- [x] Leave `mk_soundness_completeness` (`MinCompleteness.lean:71-73`) untouched.
- [x] Targeted build: `lake build Cslib.Logics.Modal.Metalogic.Minimal.MinCompleteness`; confirm
      zero errors and no `sorry` warnings.

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean` - swap one import; rewrite the
  `mk_completeness` proof body to the delegation form.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Minimal.MinCompleteness` succeeds.
- `lean_verify mk_completeness` reports zero `sorry`/`admit` and the same axiom set as the
  baseline captured at the start of this phase.
- Commit this green milestone before proceeding.

---

### Phase 2: Delete the bespoke trio core and regenerate the barrel [COMPLETED]

**Goal**: Remove the now-dead `MinCanonicalModel.lean` and `MinTruthLemma.lean` and regenerate the
barrel so nothing imports them.

**Tasks**:
- [x] Delete `Cslib/Logics/Modal/Metalogic/Minimal/MinCanonicalModel.lean` (1089 lines).
- [x] Delete `Cslib/Logics/Modal/Metalogic/Minimal/MinTruthLemma.lean` (257 lines).
- [x] Regenerate the barrel: `lake exe mk_all --module`. Diff `Cslib.lean` and confirm exactly the
      lines for `…Minimal.MinCanonicalModel` (was line 397) and `…Minimal.MinTruthLemma` (was line
      401) are removed, and that `…Minimal.MinCompleteness` and `…Minimal.MinExtension` remain.
- [x] Build the Minimal subtree: `lake build Cslib.Logics.Modal.Metalogic.Minimal.MinCompleteness`
      (and the barrel target) to confirm no dangling import.

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinCanonicalModel.lean` - delete.
- `Cslib/Logics/Modal/Metalogic/Minimal/MinTruthLemma.lean` - delete.
- `Cslib.lean` - regenerated barrel with the two deleted-module import lines removed.

**Verification**:
- `Cslib.lean` diff removes only the two named import lines; `MinCompleteness`/`MinExtension`
  retained.
- `lake build` of the Minimal subtree and barrel succeeds with no missing-import errors.
- Commit this green milestone before proceeding.

---

### Phase 3: Delete orphaned MinPrimeTheory (gated, reversible) [NOT STARTED]

**Goal**: Remove `MinPrimeTheory.lean`, which becomes fully orphaned after Phase 2 (imported only
by the deleted `MinCanonicalModel`; zero external consumers per research §4). This phase is the one
scope-decision item and is deliberately isolated so it can be skipped or reverted independently of
Phases 1-2 if CI surfaces any unexpected dependency. DEFAULT: delete it (reaches
1089+257+125 = ~1471 lines, matching the task's "~1500"; the named trio alone is only 1346).

**Tasks**:
- [ ] Confirm no remaining importer: grep the whole `Cslib/` tree for
      `Minimal.MinPrimeTheory` and confirm zero hits after Phase 2 (only the barrel line should
      remain). Note that propositional `MinPrimeTheory` hits in `Logics/Propositional/…` are
      namespace-coincidental (different namespace, no modal import) and are NOT consumers.
- [ ] Delete `Cslib/Logics/Modal/Metalogic/Minimal/MinPrimeTheory.lean` (125 lines).
- [ ] Regenerate the barrel: `lake exe mk_all --module`. Confirm the `…Minimal.MinPrimeTheory`
      line (was line 400) is removed and nothing else changed.
- [ ] Build the barrel/Minimal subtree to confirm no dangling import.

**Timing**: 20 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinPrimeTheory.lean` - delete.
- `Cslib.lean` - regenerated barrel with the `MinPrimeTheory` import line removed.

**Verification**:
- Whole-tree grep confirms zero non-coincidental consumers before deletion.
- `lake build` of the Minimal subtree and barrel succeeds.
- Contingency: if any importer surfaces, restore `MinPrimeTheory.lean` and its barrel line, leave
  Phases 1-2 intact, and record the retained orphan in the summary.
- Commit this green milestone before proceeding.

---

### Phase 4: Full CI and axiom-set verification [NOT STARTED]

**Goal**: Confirm the whole refactor is zero-regression across the full CSLib CI pipeline and that
`mk_completeness`'s axiom set is unchanged.

**Tasks**:
- [ ] Full build: `lake build`.
- [ ] `lake exe checkInitImports`.
- [ ] `lake lint` and `lake exe lint-style`.
- [ ] `lake test`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (import minimization now that
      `MinCompleteness`'s import set changed); apply any suggested trims to `MinCompleteness.lean`
      and rebuild if it edits imports.
- [ ] `lean_verify` on `mk_completeness`, `mk_soundness_completeness`, `mt_completeness`,
      `ms4_completeness`, `ms5_completeness`: confirm zero `sorry` and that `mk_completeness`'s
      axiom set matches the Phase 1 baseline (expected to reduce to the standard
      `propext`/`Classical.choice`/`Quot.sound` set already used by `mt_completeness`; no NEW
      axiom relative to baseline).
- [ ] Confirm no `sorry`/`admit`/`axiom` declarations introduced anywhere in the Minimal directory.

**Timing**: 45 minutes (dominated by Lean build/test time)

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean` - only if `lake shake` recommends
  import trims.
- `Cslib.lean` - only if a shake-driven import change requires barrel regeneration.

**Verification**:
- All CI steps green.
- `lean_verify` shows zero new axiom and unchanged `mk_completeness` axiom set vs. baseline.
- Commit the final green state.

---

## Testing & Validation

- [ ] `lake build` (full CSLib) succeeds.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake lint` and `lake exe lint-style` pass.
- [ ] `lake test` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` produces no un-actioned import debt.
- [ ] `lean_verify` on the five completeness theorems: zero `sorry`; `mk_completeness` axiom set
      unchanged vs. pre-refactor baseline; zero new axiom.
- [ ] Deleted line count ≈ 1471 (MinCanonicalModel 1089 + MinTruthLemma 257 + MinPrimeTheory 125),
      or ≈ 1346 if Phase 3 is reverted.

## Artifacts & Outputs

- `plans/01_dedup-minimal-canonical-model.md` (this file)
- `summaries/01_dedup-minimal-canonical-model-summary.md` (produced at implementation)
- Modified: `Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean`, `Cslib.lean`
- Deleted: `MinCanonicalModel.lean`, `MinTruthLemma.lean`, and (default) `MinPrimeTheory.lean`

## Rollback/Contingency

- Each phase is an independent green commit, enabling `git revert` at phase granularity.
- If the Phase 1 rewire fails to build, revert only `MinCompleteness.lean`; no files have been
  deleted yet, so the tree returns to the pre-refactor state.
- If Phase 3 (`MinPrimeTheory` deletion) regresses CI, restore that single file and its barrel line
  while keeping Phases 1-2; the dedup still lands the named trio (~1346 lines).
- If the Phase 4 axiom-set comparison shows any new axiom, treat as a regression: revert to the
  last green commit and re-examine the delegation rather than accepting the change.
