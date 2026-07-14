# Implementation Plan: Task #462 — Dedup Case-Arms + De-privatize Reused Lemmas (Modal Tableau)

- **Task**: 462 - vet_299_dedup_refactor_reuse
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: None (all target files under `Cslib/Logics/Modal/Tableau/`, disjoint from task 317)
- **Research Inputs**: specs/462_vet_299_dedup_refactor_reuse/reports/01_dedup-refactor-and-deprivatize.md
- **Artifacts**: plans/01_dedup-deprivatize-modal-tableau.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Two non-blocking maintainability items surfaced by the task-299 vet, both confirmed by research as
low-risk, statement-preserving, mechanical refactors. **Item 1**: extract two helper lemmas from
~22 near-verbatim leaf case-arms in `modalStepBranch_preserves_sat` (SoundnessStep.lean), removing
~150 lines. **Item 2**: eliminate three private-lemma re-derivations in CompletenessLoop.lean by
**removing** the `private` keyword on the base lemmas (not adding `protected` — see research
correction) in Completeness.lean and FmpMeasure.lean, then deleting the local copies and repointing
call sites. Definition of done: build green across all four Tableau modules, full CI pipeline
passing, and zero sorry / zero axioms preserved (verified via `lean_verify`).

### Research Integration

Integrated report `01_dedup-refactor-and-deprivatize.md` provides the exact helper-lemma
signatures (including the `branchSatisfiable.{v, u}` universe annotation and the task-461 `omit`
clause), the corrected de-privatization mechanism (remove `private`, do NOT add `protected`), exact
line numbers on HEAD e04a2894, the explicit "leave as-is" carve-outs
(`modalMaxWorld_lt_worldBound_of_phiBound`, `modalLoop_bClosure`), the `docBlame` caveat for
`modalSf_pos`, and a scoped verification order. Line numbers cited below are from that report and
must be re-confirmed at implementation time since edits shift them.

### Prior Plan Reference

No prior plan. This is the first plan for task 462.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided; roadmap_flag not set). This is a maintainability
follow-up from the task-299 vet, not a roadmap feature item.

## Goals & Non-Goals

**Goals**:
- Extract Helper 1 (positive-antecedent) and Helper 2 (negation-antecedent) from the negative-implication
  α-rule family in `modalStepBranch_preserves_sat`; collapse all ~22 arms (18 + 4). Net ~150 lines removed.
- Remove `private` from `modalStepBranch_none_saturated` (Completeness.lean), `modalStepBranch_eClosure`,
  `modalSf_pos`, and `modalSf_one_imp_depth_zero` (FmpMeasure.lean); add a one-line docstring to
  `modalSf_pos`.
- Delete the exact-copy local lemmas in CompletenessLoop.lean and repoint their call sites to the
  now-public originals.
- Preserve every theorem statement; keep zero sorry, zero axioms; pass the full CSLib CI pipeline.

**Non-Goals**:
- Do NOT touch `modalMaxWorld_lt_worldBound_of_phiBound` (CompletenessLoop.lean:160-192) — its base is
  already public and it is a legitimate generalization.
- Do NOT touch `modalLoop_bClosure` (CompletenessLoop.lean:195-244) — a different proof for a different
  statement, not a private-blocked copy.
- Do NOT add `protected` (research-confirmed no-op for cross-module reuse).
- The optional `prop_step` simp-skeleton macro (research "optional") is out of scope unless Phase 1
  completes with time to spare and it demonstrably does not perturb other arm families.
- No changes outside `Cslib/Logics/Modal/Tableau/`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe annotation on `branchSatisfiable.{v, u}` mismatched, `exact` fails to unify | M | M | Carry `W : Type v` and explicit `.{v, u}` on helper conclusion exactly as research spec (report lines 99-104); catch at scoped `lake build`. |
| Wrong `omit [DecidableEq Atom] [Hashable Atom]` clause trips the `unusedSectionVars` linter (task-461 concern) | M | M | Verify `branchSatisfiable`/`Satisfies`/`Model` actually use neither instance before committing the omit; the linter flags a wrong choice at build time. |
| Helper 2's `a = imp a1 bot` decomposition does not match the 4 variant arms | M | L | Confirm the exact `a1` decomposition against the arm bodies before collapsing; build-verified. |
| De-privatized lemma whose proof calls other `private` lemmas fails to compile | L | L | Research confirms `@[expose]` affects `def` bodies only; Prop proofs are never public interface (proof irrelevance) — safe regardless of body. |
| Repointed call sites have mismatched argument order | L | L | Signatures are identical between local copy and original; verify by scoped `lake build` of CompletenessLoop. |
| `docBlame` linter flags newly-public `modalSf_pos` (no docstring) | L | M | Add a one-line docstring in Phase 2 when de-privatizing (cron-only linter, but fixed proactively). |
| FmpMeasure.lean scoped build is slow (~3k lines) | L | H | Expected; budget time. Build in dependency order per research verification plan. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 2 |
| 3 | 4 | 1, 3 |

Phases within the same wave can execute in parallel. Phases 1 and 2 touch disjoint files
(SoundnessStep.lean vs Completeness.lean + FmpMeasure.lean) and are safely parallelizable.

### Phase 1: Item 1 — Extract SoundnessStep α-rule helper lemmas [COMPLETED]

**Goal**: Replace the ~22 duplicated negative-implication α-rule leaf arms in
`modalStepBranch_preserves_sat` with two extracted helper lemmas, removing ~150 lines while
preserving the theorem statement and zero-debt status.

**Tasks**:
- [ ] Re-confirm the duplication on current HEAD: grep the positive-antecedent tail (18 arms) and the
      negation-antecedent variant (`a = imp a1 bot`, 4 arms) in `SoundnessStep.lean`
      (`modalStepBranch_preserves_sat`, ~lines 179-1702).
- [ ] Add **Helper 1** `negImp_alpha_preserved` (positive antecedent) near the theorem's supporting
      lemmas in the same namespace/section, using the exact signature from the report (report lines
      94-114): carry `{W : Type v}`, conclude `branchSatisfiable.{v, u} ([⟨.pos, A, lbl⟩, ⟨.neg, C, lbl⟩] ++ b) acc`,
      and prefix with `omit [DecidableEq Atom] [Hashable Atom] in` after verifying neither instance is used.
- [ ] Add **Helper 2** (negation antecedent, `a = imp a1 bot`): same body shape but pushes
      `⟨.neg, a1, lbl⟩` and derives `hna1 : ¬Satisfies m (f lbl) a1`; conclusion
      `branchSatisfiable ([⟨.neg, a1, lbl⟩, ⟨.neg, C, lbl⟩] ++ b) acc`.
- [ ] Collapse each of the 18 positive-antecedent arms to the 4-line form ending in
      `exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩` (report lines 116-124),
      keeping the per-constructor `simp [...] at hsf; obtain ...; subst ...` prefix.
- [ ] Collapse the 4 negation-antecedent arms to the Helper 2 call.
- [ ] Scoped build: `lake build Cslib.Logics.Modal.Tableau.SoundnessStep`.
- [ ] Confirm zero sorry/axioms preserved: `lean_verify` on `modalStepBranch_preserves_sat`.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` — add 2 helper lemmas (~24 lines); collapse 22 arms
  (~264 lines of tail → ~88 lines of calls). Net ~150 lines removed.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.SoundnessStep` succeeds.
- `unusedSectionVars` linter does not fire (correct `omit` clause).
- `lean_verify` confirms no sorry, no new axioms on the theorem.

---

### Phase 2: Item 2a — De-privatize base lemmas in Completeness + FmpMeasure [COMPLETED]

**Goal**: Make the four re-used base lemmas cross-module accessible by removing the `private`
keyword (files are already in `@[expose] public section`), and add the missing docstring so the
`docBlame` linter stays clean.

**Tasks**:
- [ ] Remove `private` from `modalStepBranch_none_saturated` (Completeness.lean:703).
- [ ] Remove `private` from `modalStepBranch_eClosure` (FmpMeasure.lean:2092).
- [ ] Remove `private` from `modalSf_pos` (FmpMeasure.lean:2331) and add a one-line docstring
      (it currently has none — required to avoid the `docBlame` cron linter).
- [ ] Remove `private` from `modalSf_one_imp_depth_zero` (FmpMeasure.lean:2339) — already has a docstring.
- [ ] Do NOT add `protected` and do NOT touch `modalStepBranch_worldBound` (already public).
- [ ] Scoped builds in dependency order:
      `lake build Cslib.Logics.Modal.Tableau.Completeness` then
      `lake build Cslib.Logics.Modal.Tableau.FmpMeasure`.

**Timing**: ~0.75 hours

**Depends on**: none (disjoint files from Phase 1)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` — remove `private` on line ~703.
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — remove `private` on lines ~2092, ~2331, ~2339; add
  docstring to `modalSf_pos`.

**Verification**:
- Both scoped builds succeed (FmpMeasure is slow, ~3k lines — expected).
- No new linter warnings introduced on the de-privatized declarations.

---

### Phase 3: Item 2b — Delete CompletenessLoop local copies + repoint call sites [COMPLETED]

**Goal**: Remove the now-redundant exact-copy local lemmas in CompletenessLoop.lean and repoint all
call sites to the de-privatized originals from Phase 2.

**Tasks**:
- [ ] Delete `modalLoop_stepBranch_none_saturated` (CompletenessLoop.lean:107-131) and its doc-comment
      (102-106); repoint ~5 call sites (~lines 739, 746, 753, 763, 772):
      `modalLoop_stepBranch_none_saturated` → `modalStepBranch_none_saturated`.
- [ ] Delete `modalLoop_eClosure` (CompletenessLoop.lean:247-295) and its doc-comment (~245-246);
      repoint call site (~line 587): `modalLoop_eClosure` → `modalStepBranch_eClosure`.
- [ ] Delete the bonus duplicate pair `modalLoopSf_pos` / `modalLoopSf_one_imp_depth_zero`
      (CompletenessLoop.lean:133-140+); repoint calls to `modalSf_pos` / `modalSf_one_imp_depth_zero`.
- [ ] Leave `modalMaxWorld_lt_worldBound_of_phiBound` (160-192) and `modalLoop_bClosure` (195-244) untouched.
- [ ] Scoped build: `lake build Cslib.Logics.Modal.Tableau.CompletenessLoop` (consumes all
      de-privatized lemmas).

**Timing**: ~1 hour

**Depends on**: 2 (requires the base lemmas to be public before deletion/repointing)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — delete 3 local copies + bonus pair (~90+ lines
  removed); repoint ~7 call sites.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.CompletenessLoop` succeeds with no undefined-identifier errors.
- Grep confirms no residual references to the deleted local lemma names.

---

### Phase 4: CI verification and zero-debt confirmation [COMPLETED]

**Deviation note**: `lake exe checkInitImports`, `lake test`, `lake shake`, and `lake exe
mk_all --module` require a full-project build. At execution time,
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` had substantial uncommitted,
in-progress changes from a concurrent task-317 agent (215 insertions / 74 deletions, one
active `sorry`, one broken type-mismatch), causing `lake build` (repo-wide) and every tool
that depends on it to fail — entirely outside this task's territory
(`Cslib/Logics/Modal/Tableau/`) and unrelated to these changes. *(deviation: substituted
equivalent scoped/manual verification for the four full-repo-only steps — see below — since
the repo-wide build was blocked by another task's concurrent uncommitted work, not by this
task's changes)*

Scoped/manual equivalents actually run:
- `lake build` for all 11 `Cslib.Logics.Modal.Tableau.*` modules (the full Tableau tree, the
  fully self-contained blast radius — grep confirms no file outside this directory imports it):
  all green, zero errors.
- `checkInitImports` manually verified: all 4 touched files begin with `import Cslib.Init`.
- `lake exe lint-style`: ran repo-wide (a source-text scan, not gated on `lake build`); exit 0,
  zero findings.
- `lake shake --add-public --keep-implied --keep-prefix`: ran repo-wide; processed
  `Completeness.lean` and `CompletenessLoop.lean` fully (replaying their existing lint
  warnings) with zero new unused-import findings before erroring on the unrelated
  out-of-date Propositional target.
- `mk_all` (module listing): trivially satisfied — no files added/removed; grep confirms all
  4 touched files already listed in `Cslib.lean`.
- `lean_verify` on `modalStepBranch_preserves_sat`: axioms = `{propext, Classical.choice,
  Quot.sound}` only (the three standard axioms) — zero new axioms, zero sorry.
- `grep -rn sorry` / `grep -rn "^axiom "` on all 4 touched files: 0 matches each.
- Grep for the 4 deleted lemma names (`modalLoop_stepBranch_none_saturated`,
  `modalLoop_eClosure`, `modalLoopSf_pos`, `modalLoopSf_one_imp_depth_zero`) across all of
  `Cslib/`: 0 residual references.

Not run (blocked by the external issue, not re-attempted to avoid racing the concurrent
agent's working tree): `lake test`, repo-wide `lake exe checkInitImports` binary, repo-wide
`lake exe mk_all --module` binary invocation, full unblocked `lake shake` pass.

**Goal**: Run the full CSLib CI pipeline across all touched modules and confirm the zero-debt
invariant (no sorry, no axioms) holds end-to-end.

**Tasks**:
- [ ] Full build of the Tableau tree (or `lake build` at repo scope covering the four modules).
- [ ] `lake test` (CslibTests suite).
- [ ] `lake exe checkInitImports`.
- [ ] `lake exe lint-style`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (dependency analysis; expect no new
      import issues since de-privatization only exposes existing symbols within the same import graph).
- [ ] Optional (cron-only) `lake lint` to confirm `docBlame` is satisfied on the newly-public `modalSf_pos`.
- [ ] `lean_verify` on `modalStepBranch_preserves_sat` and `modalStep_preserves_invariant` to confirm
      zero sorry / zero axioms.

**Timing**: ~0.75 hours

**Depends on**: 1, 3

**Files to modify**: none (verification only).

**Verification**:
- All CI commands exit clean.
- `lean_verify` reports no sorry and no axiom additions.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Tableau.SoundnessStep` (Phase 1)
- [ ] `lake build Cslib.Logics.Modal.Tableau.Completeness` (Phase 2)
- [ ] `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` (Phase 2)
- [ ] `lake build Cslib.Logics.Modal.Tableau.CompletenessLoop` (Phase 3)
- [ ] `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake ...` (Phase 4)
- [ ] `lean_verify` zero sorry / zero axioms on the two key theorems (Phase 4)
- [ ] Every theorem statement unchanged (pure proof-term / accessibility refactor)

## Artifacts & Outputs

- plans/01_dedup-deprivatize-modal-tableau.md (this file)
- specs/462_vet_299_dedup_refactor_reuse/.orchestrator-handoff.json (planning handoff)
- Modified: `Cslib/Logics/Modal/Tableau/SoundnessStep.lean`, `Completeness.lean`, `FmpMeasure.lean`,
  `CompletenessLoop.lean`
- summaries/01_dedup-deprivatize-modal-tableau-summary.md (produced at /implement time)

## Rollback/Contingency

- Each phase is an isolated, independently buildable change; revert per-phase with `git checkout --`
  on the affected file(s) if a scoped build fails.
- Phase 1 is fully independent — its failure does not block Phases 2-3.
- If Phase 2 de-privatization surfaces an unexpected build issue, restore the `private` keyword and
  leave the CompletenessLoop copies in place (Phase 3 is not started until Phase 2 is green), keeping
  the repository in its current working state.
- Because all changes are statement-preserving, a full revert restores byte-identical proof semantics.
