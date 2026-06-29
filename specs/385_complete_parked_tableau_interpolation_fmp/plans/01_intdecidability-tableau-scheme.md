# Implementation Plan: Task #385

- **Task**: 385 - Complete and integrate IntFMPSpike, LK/Interpolation, Tableau Scheme
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: 395 (reconciliation, satisfied); coordinates with 317 (Phase 5 only)
- **Research Inputs**: reports/01_fmp-tableau-build-blocker-research.md; reports/intfmpspike-verified-patch.diff
- **Artifacts**: plans/01_intdecidability-tableau-scheme.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 385 has two remaining sub-parts after the task-395 reconciliation (the LK/Interpolation
sub-part was DROPPED — task 374 already delivered `LKProof.interpolation` sorry-free). (1) The
**build blocker**: `IntFMPSpike.lean` is the only thing breaking repo-wide `lake build`; its import
is currently commented out at `Cslib.lean:420-422`. Research produced an EXACT build-verified,
sorry-free patch (`intfmpspike-verified-patch.diff`). The file must be patched, renamed to
`IntDecidability.lean`, stripped of spike/specs-370 framing, and rewired into `Cslib.lean`. (2) The
**Scheme.lean sorries**: five live sorries under the committed `intuitionisticTableau_complete`
(`Scheme.lean:242/280/288/296` + `Completeness.lean:112`). 385 closes `:296` and `:280` via
classical templates, attempts `:288` behind a research-or-defer gate, and sequences `:242`/`:112`
after task 317 (their core obligation). **Definition of done**: repo-wide `lake build` green
(import re-enabled), full CI pipeline clean, `:296`/`:280` (and `:288` if bridged) closed
sorry-free, with no new sorries or axioms anywhere.

### Research Integration

The plan is built directly on `reports/01_fmp-tableau-build-blocker-research.md`:
- The 7-row root-cause table and the verified `intFinWorld_propConsistent` rewrite drive Phase 1;
  the build blocker is fully spec'd and verified (scoped `lake build` EXIT 0, sorry-free) with the
  exact patch saved as `intfmpspike-verified-patch.diff`.
- The "wiring inventory" (only `Cslib.lean:420-422` references the module; no Metalogic barrel)
  and the spike-framing strip list drive Phase 2.
- The per-sorry tractability table (`:296` most tractable via
  `classicalExpandBranches_openBranch_initial_mem`; `:280` readable off the loop guards; `:288`
  formulation-bridge risk; `:242`/`:112` are task-317 core) drives Phases 3-5.

### Prior Plan Reference

No prior plan. This is the first plan for task 385.

### Roadmap Alignment

No `roadmap_path` provided to this invocation; ROADMAP.md not consulted. Task 385 advances the
Propositional Logic metalogic track (IPC decidability/FMP + intuitionistic tableau completeness).

## Goals & Non-Goals

**Goals**:
- Eliminate the repo-wide build blocker: apply the verified patch, rename
  `IntFMPSpike.lean` -> `IntDecidability.lean`, strip spike/370 framing, re-enable the `Cslib.lean`
  import, regenerate the barrel via `mk_all`, and confirm full `lake build` green.
- Clear all lint warnings on the renamed module (~8 trivial warnings).
- Close `Scheme.lean:296` (`initial_mem`) and `Scheme.lean:280` (`closed`) sorry-free via the
  Classical-track templates and the existing `intExpandBranches.go` induction patterns.
- Attempt `Scheme.lean:288` (`sat`) behind a research-or-defer gate; defer cleanly if the
  `intStepBranch b [] 0 = none` formulation is unbridgeable from the loop's accumulated-set return.
- Document the task-317 dependency for `Scheme.lean:242` (truthLemma) and `Completeness.lean:112`
  (IValid->forcing bridge) and sequence them after 317 — without blocking 385's completion.
- Pass the full CSLib CI pipeline at every phase boundary.

**Non-Goals**:
- LK/Interpolation work (DROPPED — delivered by task 374, `Interpolation.lean:864`).
- Eliminating `:242`/`:112` inside 385 (task 317's core obligation; would risk scope blowup).
- Introducing ANY sorry or axiom workaround for `:288`, `:242`, or `:112` (zero-debt).
- Renaming any declaration in `IntFMPSpike.lean` (only docstrings/section headers change).
- Repointing the Minimal track at the parametric route (317-coordinated; out of 385 scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Verified patch does not apply cleanly (tree drifted since research) | M | L | Patch is verified against current `IntFMPSpike.lean`; if `git apply` fails, apply the 7 edits by hand from the diff (they are line-anchored in the research table). Re-run scoped build before proceeding. |
| `lake` rejects the `imp` case `() vs PUnit.unit` defeq (LSP/lake divergence) | M | L | The verified patch already uses the world-polymorphic `suffices ∀ u, ...` term form that is robust across both `lake` and LSP; do NOT "simplify" it back to `simp [IForces]; exact ihb`. |
| `mk_all` reorders/duplicates the barrel | L | L | Use `lake exe mk_all --module`; the new import sits alpha-ordered between `GenericMCSBridge` (419) and `IntLindenbaum` (423). Diff the barrel before commit. |
| `:288` `intStepBranch b [] 0 = none` is unbridgeable from the accumulated-`e`/`nw` return | H | M | Research-or-defer gate (Phase 4): attempt via go-induction + `applyPersistenceFixpoint_sat`; if the empty-set/world-0 formulation cannot be reached, mark the sorry [BLOCKED] for user review and coordinate an `hsat` reformulation with task 317. NO sorry/axiom. |
| `:242`/`:112` cannot be closed sorry-free without 317 | H | H (known) | Out of 385 scope by design (Phase 5 is documentation/coordination only). 385 reaches clean completion on P1-P4; these stay sequenced after 317. |
| New structural lemmas balloon past one agent run | M | M | Phase 3 mirrors existing templates (`classicalExpandBranches_openBranch_initial_mem` ~100 lines; `classicalStepBranch_mem_preserved`) and the existing `Soundness.lean` go-inductions; estimate 120-180 lines. If `:296` alone consumes the run, split `:280` into a follow-on dispatch. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is strictly sequential (one phase
per wave): each phase depends on a green build from the prior. Phase 5 is a deferred/coordination
phase and does NOT gate task completion (385 completes on P1-P4).

### Phase 1: Apply verified build-blocker patch + clear lint [COMPLETED]

**Goal**: Make `IntFMPSpike.lean` compile sorry-free (scoped build EXIT 0) by applying the
build-verified patch, then clear the ~8 trivial lint warnings. File is NOT yet renamed or
re-imported in this phase.

**Tasks**:
- [ ] Apply `reports/intfmpspike-verified-patch.diff` (7 edits) to
      `Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean` via `git apply`; if it fails, apply
      the 7 edits by hand per the research root-cause table (add
      `public import Mathlib.Data.Finset.Powerset`; rename `Σ`-bearing hyps `hψ'Σ`/`hab_Σ` ->
      `hψ'mem`/`hab_sub` at all 5 sites; case-split rewrite of `intFinWorld_propConsistent`;
      `exact this` for the `:177` simp; `Finset.mem_coe.mpr` coercion fix at `:269`; drop
      `private` from `intFinWorld_carrier_injective`; drop the unknown `Set.mem_coe`).
- [ ] Verify the world-polymorphic `imp` case term form is preserved exactly (do NOT revert it to
      `simp [IForces]; exact ihb` — `lake` rejects the `() vs PUnit.unit` defeq).
- [ ] Clear the 8 lint warnings on the patched file: `69:10` extra space; `107` unused binders
      `w₁`/`w₂` -> `_`; `153:100` line >100 chars; `156`/`161` flexible `simp [IForces]` ->
      `simp only [...]`; `225`/`226` unused simp args (`Finset.mem_coe`, `Finset.mem_filter`).
      (Line numbers refer to the patched file.)
- [ ] `grep -n "sorry" Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean` — confirm only the
      docstring word, no proof-body sorries.

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean` - apply 7 verified edits + 8 lint fixes.

**Verification** (CI step):
- `lake build Cslib.Logics.Propositional.Metalogic.IntFMPSpike` -> EXIT 0 (errors), warnings cleared.
- `lake exe lint-style` on the file -> clean.

### Phase 2: Rename + rewire + mk_all + full build verify [COMPLETED]

**Goal**: Promote the spike file to a committed module: rename to `IntDecidability.lean`, strip
spike/specs-370 framing (docstrings + section headers only, NO decl renames), re-enable the
`Cslib.lean` import, regenerate the barrel, and confirm repo-wide `lake build` is GREEN.

**Tasks**:
- [ ] `git mv Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean
      Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`.
- [ ] Strip spike/370 framing from the module docstring (lines ~13-40): remove "Phase 1
      De-Risking Spike", "scratch spike file for Task 370", "go/no-go gate", "NOT a committed
      deliverable", "On GO ... promoted to IntDecidability.lean". Rewrite as a normal module
      docstring (finite-world type + finite implication witness for IPC decidability/FMP).
- [ ] Strip section-header spike framing: line ~179 `## Finite Imp Witness (Phase 1 Spike
      Target)` -> drop "(Phase 1 Spike Target)"; line ~181 "(the Phase 1 spike target)" -> remove.
- [ ] Replace the `specs/370_...` reference (lines ~37-39) with the appropriate `references.bib`
      BibKey (verify against `references.bib`; `Fitting1983` is used in `Scheme.lean`) or remove
      if no published source applies. Confirm NO declaration names change.
- [ ] Replace the `Cslib.lean:420-422` stub block with
      `public import Cslib.Logics.Propositional.Metalogic.IntDecidability`, alpha-ordered between
      `GenericMCSBridge` (419) and `IntLindenbaum` (423).
- [ ] Run `lake exe mk_all --module` to regenerate the barrel deterministically; diff the barrel.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean` -> `IntDecidability.lean` (git mv + docstring/header edits).
- `Cslib.lean` - replace stub at 420-422 with the real import.
- Barrel file regenerated by `mk_all`.

**Verification** (CI pipeline):
- `lake build` (repo-wide) -> GREEN.
- `lake exe checkInitImports` -> clean.
- `lake exe lint-style` -> clean.
- `lake shake --add-public --keep-implied --keep-prefix` -> clean.

### Phase 3: Close Scheme.lean :296 then :280 (structural sorries) [NOT STARTED]

**Goal**: Close the two in-scope structural sorries in `openBranch_countermodel` sorry-free:
`:296` (`hFmem`, F(φ)@0 ∈ b) and `:280` (`hopen`, `closurePred b = false`), by mirroring the
Classical-track templates and the existing `intExpandBranches.go` inductions.

**Tasks**:
- [ ] Close `:296`: create `intExpandBranches_openBranch_initial_mem` plus the prerequisite
      `intStepBranch`/persistence membership-preservation helper (analogue of
      `classicalStepBranch_mem_preserved`, Classical:1120). Mirror
      `classicalExpandBranches_openBranch_initial_mem` (Classical/Completeness.lean:1164, ~100
      lines); thread the int-specific `pendingNW`/`pendingEdges`/`doneNW`/`doneEdges` and account
      for `applyPersistenceFixpoint` + `Branch.extendMany` monotonicity (both only ADD formulas).
      Wire the result into `openBranch_countermodel` at the `:296` site.
- [ ] Close `:280`: create `intExpandBranches_openBranch_closed`, reading directly off the loop
      guards — `.openBranch bPers` is returned only inside the `else` of `if closurePred bPers`
      (Expansion.lean:204-208), and the fuel=0 case via
      `findSome? (if closurePred b then none else some b)`. Induction on fuel + the `go` helper,
      mirroring the existing `Soundness.lean` go-inductions (lines 411, 819, 1166, 1212). Wire
      into `openBranch_countermodel` at the `:280` site.
- [ ] `grep -n "sorry"` the touched proof bodies — confirm `:296` and `:280` are eliminated and no
      new sorries introduced.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - close `:296`, `:280`; add new structural lemmas (or place helpers in `Expansion.lean` if scope-appropriate).
- Possibly `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - membership-preservation helper.

**Verification** (CI pipeline):
- `lake build` (repo-wide) -> GREEN.
- `lake exe checkInitImports`; `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix` -> clean.
- Sorry count under `intuitionisticTableau_complete` reduced by 2 (`:296`, `:280` gone).

### Phase 4: Attempt Scheme.lean :288 (sat) — research-or-defer gate [NOT STARTED]

**Goal**: Attempt `:288` (`hsat`, `intStepBranch b [] 0 = none`) sorry-free via
`intExpandBranches_openBranch_sat`. If the empty-set/world-0 formulation proves unbridgeable from
the loop's accumulated-`e`/`nw` return condition, defer cleanly (mark [BLOCKED] for user review,
coordinate `hsat` reformulation with 317) — NO sorry/axiom workaround.

**Tasks**:
- [ ] Attempt `intExpandBranches_openBranch_sat`: `.openBranch bPers` is returned when
      `intStepBranch bPers e nw = none` for the accumulated expanded set `e` / next-world `nw`.
      Try to bridge to the `intStepBranch b [] 0 = none` shape via go-induction +
      expanded-set/world-independence of saturation; `applyPersistenceFixpoint_sat`
      (Soundness.lean:411) is the relevant supporting machinery.
- [ ] **Gate**: if the bridge holds, close `:288` sorry-free and wire into
      `openBranch_countermodel`. If the formulation cannot be reached (the classical proof
      sidesteps this via `classicalHintikkaSet`, not a raw `intStepBranch = none`), STOP: leave
      `:288` as-is, mark it [BLOCKED] in the task notes, and record the proposed `hsat`
      reformulation as a 317-coordination item. Do NOT introduce a sorry or axiom and do NOT block
      385's completion on this.
- [ ] Record the gate outcome (closed vs deferred) in the orchestrator handoff JSON blockers.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - close `:288` if bridged; otherwise no change to the sorry (deferred).

**Verification** (CI pipeline):
- `lake build` (repo-wide) -> GREEN (whether `:288` is closed or left as the pre-existing sorry; sorries warn, not error).
- `lake exe checkInitImports`; `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix` -> clean.
- If closed: sorry count reduced by 1. If deferred: no new debt; outcome documented.

### Phase 5: Coordinate :242 (truthLemma) + Completeness.lean:112 with task 317 [DEFERRED — NOT STARTED]

**Goal**: DEFERRED/COORDINATION ONLY. Document that `Scheme.lean:242` (parametric Kripke
truthLemma) and `Completeness.lean:112` (IValid->forcing bridge + `intExtractValuation` upward
closure) are task-317's core obligation; 385 cannot eliminate them sorry-free without 317. This
phase does NOT gate 385's completion — 385 reaches clean completion on P1-P4.

**Tasks**:
- [ ] Document the dependency in the task notes / handoff: `:242` and `Completeness.lean:112` are
      317-scoped (Kripke truth lemma by formula induction handling persistence/monotonicity across
      Nat-labelled worlds + parametric `modelBot`/`S.bot_truth`; IValid->per-branch forcing bridge
      with upward closure of `intExtractValuation b`).
- [ ] Add a forward reference (code comment near `:242`/`:112` and/or a 317-coordination note) so
      these sorries are clearly sequenced after 317 and not mistaken for 385 debt.
- [ ] Do NOT attempt to force these closed in 385; do NOT introduce sorry/axiom workarounds.
- [ ] Confirm task 317's status (currently `planned`) and flag for sequencing; if 317 later lands
      the truth lemma + upward closure, a follow-on 385 round (or 317 itself) can eliminate these.

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - documentation comment near `:242` (no proof change).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - documentation comment near `:112` (no proof change).

**Verification** (CI pipeline):
- `lake build` (repo-wide) -> GREEN (pre-existing 317-scoped sorries warn, not error).
- `lake exe checkInitImports`; `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix` -> clean.
- No new sorries or axioms; `:242`/`:112` remain as documented, 317-sequenced obligations.

## Testing & Validation

- [ ] `lake build` (repo-wide) GREEN after Phase 2 (import re-enabled) and at every subsequent phase boundary.
- [ ] `lake test` (CslibTests suite) passes.
- [ ] `lake exe checkInitImports` clean.
- [ ] `lake exe lint-style` clean (including the renamed `IntDecidability.lean`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` clean.
- [ ] `grep -rn "sorry"` on touched files: only pre-existing 317-scoped sorries (`:242`, `:112`)
      and — if Phase 4 deferred — `:288` remain; `:296`/`:280` eliminated; ZERO new sorries/axioms.
- [ ] Barrel (`mk_all` output) diff reviewed; `IntDecidability` import alpha-ordered in `Cslib.lean`.

## Artifacts & Outputs

- `plans/01_intdecidability-tableau-scheme.md` (this plan).
- `summaries/01_intdecidability-tableau-scheme-summary.md` (on implementation completion).
- Renamed module `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` (sorry-free).
- Updated `Cslib.lean` (import re-enabled) + regenerated barrel.
- Updated `Tableau/Intuitionistic/Scheme.lean` (`:296`/`:280` closed; `:288` closed or deferred;
  `:242` documented) and `Completeness.lean` (`:112` documented).

## Rollback/Contingency

- Phases 1-2 are a single logical unit (build-blocker fix). If repo-wide `lake build` is not GREEN
  after Phase 2, revert the `Cslib.lean` import re-enable (restore the 420-422 stub) so the repo
  stays green, and re-diagnose the patch application before retrying. `git mv` is reversible.
- Phase 3: if a structural lemma does not close, revert that phase's edits (the sorry returns to
  its pre-Phase-3 state — no worse than baseline) and re-dispatch; do NOT commit a half-proof.
- Phase 4: the research-or-defer gate is itself the contingency — defer (leave the pre-existing
  sorry, mark [BLOCKED], coordinate with 317) rather than introducing debt.
- Phase 5 is documentation-only; nothing to roll back beyond comment edits.
- All changes are git-tracked; revert per-phase via `git checkout` of the touched files. Commit
  only at GREEN phase boundaries (zero-debt: never commit a build-red or half-proof state).
