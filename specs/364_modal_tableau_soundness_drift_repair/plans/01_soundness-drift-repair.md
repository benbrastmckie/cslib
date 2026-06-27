# Implementation Plan: Task #364

- **Task**: 364 - Repair Mathlib/toolchain-drift build failure in `Cslib/Logics/Modal/Tableau/Soundness.lean`
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/364_modal_tableau_soundness_drift_repair/reports/01_drift-diagnosis.md
- **Artifacts**: plans/01_soundness-drift-repair.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`Cslib/Logics/Modal/Tableau/Soundness.lean` (947 lines) is sorry-free but produces ~77 build
errors under `leanprover/lean4:v4.31.0` due to Lean/Mathlib drift. The 77 errors collapse to 4
root fix-families (cases-on-sign no longer substitutes `isPos`; `simp only [Satisfies]` ordering;
`obtain` pattern mismatch after `simp [tryAllPropRules,…]`; `LawfulBEq.eq_of_beq` synth failure).
The repair is mechanical transcription of the fix idioms already worked out in the research
report — not redesign. Three prior single-pass agents overflowed context because `lean_goal` here
returns ~1 KB hypothesis contexts and the file needs many probes. The plan therefore decomposes
the file by declaration so each phase is a single bounded agent run, repairs in chunks, and
commits at each milestone. `lean_diagnostic_messages` MUST NOT be called (it hangs in this repo);
diagnosis uses `lean_goal` plus scoped `lake build Cslib.Logics.Modal.Tableau.Soundness`, reading
the file in <=120-line slices.

### Research Integration

The plan follows the report's recommended order verbatim: (1) fix the self-contained
closed-branch cluster (`modalClosed_unsat`, Families 1/2/4), build+commit; (2) fix the
`modalStepBranch_preserves_sat` Family-3 sites one constructor-case at a time, deriving the
corrected `obtain`/`simp` shape via `lean_goal` at the first site and transcribing to the five
parallel rule-cases (box -> negPos -> orPos -> impPos x2), resolving co-located Family-2 negation
unfolds alongside; (3) handle the F-side (neg-sign) cases later in the file; (4) finalize with a
clean scoped build, `lake exe lint-style`, and an axiom/`sorry` audit. Concrete idioms per family
are reproduced in the relevant phases below so no agent needs to re-derive them from scratch.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap flag/path supplied). This task is a follow-up of the
2026-06-26 CI-failure fix sweep; it restores the last remaining originally-failing CSLib module to
a green build.

## Goals & Non-Goals

**Goals**:
- Restore `Cslib/Logics/Modal/Tableau/Soundness.lean` to a clean scoped and full `lake build`.
- Pass `lake exe lint-style` on the repaired file.
- Preserve every theorem/lemma/def statement exactly (faithful drift repair, proof bodies only).
- Maintain zero `sorry`, zero `admit`, zero new axioms (`#print axioms modalTableau_sound`).

**Non-Goals**:
- Redesigning tableau definitions, rule recognizers, or theorem statements.
- Refactoring proof structure beyond what the drift fixes require.
- Touching any other CSLib module (changes are scoped to this single file).
- Introducing new lemmas to `Sign.lean`, `Modal/Basic.lean`, or other dependencies unless a fix
  family strictly requires a one-line reused-pattern helper already present in sibling files.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `lean_goal` context overflow within a single agent run | H | M | One declaration-cluster per phase; read file in <=120-line slices; cap `lean_goal` probes per phase; never call `lean_diagnostic_messages` |
| `lake build` only reaches green after the *whole* `modalStepBranch_preserves_sat` theorem is fixed, so Phase 2 cannot produce a fully-green build | M | H | Phase 2 milestone is strict monotonic error-count reduction at the targeted sites (verified via scoped build); Phase 2 ends with an intentional WIP checkpoint commit to survive the context boundary; the theorem reaches full green at Phase 3 |
| Family-3 corrected pattern differs across the 5 rule-cases | M | M | Derive pattern at the first site via `lean_goal` placed immediately before the `obtain`; verify each transcribed site individually before moving on |
| Family-2 errors are downstream cascades, inflating perceived work | L | H | Re-count errors after each root fix; treat error count as the progress metric, not raw line 77 |
| A fix accidentally weakens a statement (e.g. via `sorry`/`admit`/vacuous rewrite) | H | L | Final-phase `#print axioms` + `git diff` review confirming only proof-body lines changed |
| `lake exe lint-style` flags reformatted proof lines | L | M | Run lint in the final phase and fix style-only issues without altering proof semantics |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

All phases edit the same file and the build's greenness is cumulative, so phases are strictly
sequential — no parallelism. Each phase is sized to a single bounded agent run.

### Phase 1: Repair closed-branch lemma cluster (Families 1, 2, 4) [COMPLETED]

**Fix approach confirmed via lean_run_code:**
- Family 1: `cases h : sf.sign` + `simp [h, Sign.isPos]` at hpos
- Family 4: Private `Proposition.beqToEq` helper lemma using structural recursion + `nomatch h`
- Family 2: Reorder `rw [hformbot]` before `simp only [Satisfies]`

**Goal**: Make the self-contained cluster `branchSatisfiable`, `modalClosed_unsat`,
`extendBranchSat`, `accFreshInv`/`accFreshInv_empty` (lines ~63-184) build green, eliminating the
Family-1, Family-2 (no-op ordering), and Family-4 root errors. This collapses all error cascades
that originate above `modalStepBranch_preserves_sat`.

**Tasks**:
- [ ] Read lines ~63-184 in <=120-line slices to load only this cluster.
- [ ] Family 1 (lines ~99, ~124): replace `cases sf.sign with …` blocks with the equation form
      `cases h : sf.sign <;> simp_all [Sign.isPos]`, or in a neg case that must derive `False`,
      `rw [h] at hpos; simp [Sign.isPos] at hpos`. Adjust per-site to whether the block proves
      `X.sign = .pos` or derives a contradiction.
- [ ] Family 2 no-op (line ~100): reorder so `rw [hformbot] at hsat` precedes
      `simp only [Satisfies] at hsat`, yielding `hsat : False`, then `exact hsat`.
- [ ] Family 4 (lines ~126, ~129, ~131): replace `LawfulBEq.eq_of_beq hformEq` with the current
      route for `Proposition Atom` — try `by simpa using hformEq` or `(beq_iff_eq …).mp hformEq`;
      use `lean_local_search`/`lean_hover_info` on `eq_of_beq`/`beq_iff_eq` to confirm the
      in-scope instance before editing. Repair the dependent `rw`/`absurd` at ~129/~131.
- [ ] Run scoped `lake build Cslib.Logics.Modal.Tableau.Soundness`; confirm all errors in lines
      <185 are gone and remaining errors are confined to `modalStepBranch_preserves_sat` and below.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — proof bodies in `modalClosed_unsat` (and any
  Family-1/2/4 sites in the surrounding cluster, lines ~63-184). Statements unchanged.

**Verification**:
- Scoped `lake build` reports zero errors at lines <185 (error count strictly lower than baseline;
  residual errors all reside in `modalStepBranch_preserves_sat` and later).
- No `sorry`/`admit`/`axiom` introduced in the edited region.
- Commit: `task 364 phase 1: repair closed-branch lemma cluster (families 1,2,4)`.

---

### Phase 2: Fix `modalStepBranch_preserves_sat` positive-sign (T-side) Family-3 cases [IN PROGRESS]

**Goal**: Eliminate the ~60 `Unknown identifier hnewBs` cascade by re-deriving the corrected
post-`simp` shape and `obtain` pattern at the first Family-3 site, then transcribing it across the
positive-sign (T-side) parallel rule-cases (box -> negPos -> orPos -> impPos x2), resolving
co-located Family-2 negation unfolds. Targets roughly lines ~185-400 of the theorem.

**Tasks**:
- [ ] Read the theorem header and the first Family-3 case (~lines 185-260) in <=120-line slices.
- [ ] Place `lean_goal` immediately BEFORE the first `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩ := hsf`
      (~line 229) to inspect the post-`simp [tryAllPropRules, applyPropRule, modalAndOf?,
      modalOrOf?, modalImpOf?, modalNegOf?, …]` shape of `hsf`.
- [ ] Determine the corrected idiom: either extend the simp set with the missing
      `*.injEq` / recognizer-unfold lemmas (`Option.some.injEq`, `Prod.mk.injEq`, the
      `modalNegOf?`/`modalImpOf?`/`modalOrOf?` unfolds) so `hsf` renormalizes to the nested
      conjunction `((newBs = …) ∧ _) ∧ (newAcc = …)`, OR rewrite the `obtain` pattern to bind
      `newBs`/`newAcc` against the new shape. Prefer the minimal change that restores the bindings.
- [ ] Apply the derived idiom to the T-side parallel sites (~lines 229, 275, 302, 334, 361 that
      fall in the positive-sign block), verifying each with a `lean_goal` probe after the `obtain`
      to confirm `hnewBs`/`hnewAcc` bind and subsequent `subst` succeeds.
- [ ] Resolve Family-2 negation unfolds co-located in these cases using `Satisfies.neg_iff`,
      `Satisfies.diamond_iff`, and/or `Proposition.neg_def` (the `@[simp]` lemma used in the
      sibling `Modal/Denotation.lean` repair) so `¬φ`/`◇φ` reduces before `simp only [Satisfies]`.
- [ ] Run scoped `lake build`; confirm error count strictly decreased and the targeted T-side
      sites no longer report errors (residual errors confined to F-side cases, lines ~400-796).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — proof bodies of the positive-sign rule-cases
  inside `modalStepBranch_preserves_sat` (~lines 185-400). Statement unchanged.

**Verification**:
- `lean_goal` after each repaired `obtain` shows `hnewBs`/`hnewAcc` bound (no `Unknown identifier`).
- Scoped `lake build` error count strictly lower than end-of-Phase-1; all remaining errors lie in
  the F-side region (lines ~400-796) of the same theorem.
- No `sorry`/`admit`/`axiom` introduced.
- The corrected Family-3 idiom is recorded in the commit message / phase notes for reuse in Phase 3.
- Commit (intentional WIP checkpoint — theorem not yet fully green, F-side pending):
  `task 364 phase 2: WIP modalStepBranch T-side family-3 cases (error count N->M)`.

---

### Phase 3: Fix `modalStepBranch_preserves_sat` negative-sign (F-side) cases — theorem green [NOT STARTED]

**Goal**: Apply the Family-3 idiom derived in Phase 2 (plus Family-1/2 fixes) to the negative-sign
(F-side) cases later in the theorem (~lines 400-796), driving the ENTIRE
`modalStepBranch_preserves_sat` theorem to a green scoped build.

**Tasks**:
- [ ] Read the F-side region (~lines 400-796) in <=120-line slices, locating the analogous
      `cases X.sign`, `simp only [Satisfies]`, and `simp […] at hsf` / `obtain` sites.
- [ ] Transcribe the Phase-2 Family-3 idiom to each F-side rule-case; verify each with a
      single `lean_goal` probe after the `obtain`.
- [ ] Apply Family-1 (equation-form `cases h : X.sign <;> simp_all [Sign.isPos]`) and Family-2
      (reorder unfold after `rw`; negation lemmas) fixes to the F-side as needed.
- [ ] Run scoped `lake build Cslib.Logics.Modal.Tableau.Soundness`; confirm
      `modalStepBranch_preserves_sat` now compiles with zero errors (any residual errors must lie
      only in the tail declarations at lines >796).

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — proof bodies of the negative-sign rule-cases
  inside `modalStepBranch_preserves_sat` (~lines 400-796). Statement unchanged.

**Verification**:
- Scoped `lake build` shows `modalStepBranch_preserves_sat` fully green; remaining errors (if any)
  are isolated to lines >796.
- No `sorry`/`admit`/`axiom` introduced.
- Commit (green milestone for the core theorem):
  `task 364 phase 3: complete modalStepBranch_preserves_sat F-side repair`.

---

### Phase 4: Repair tail declarations and reach clean scoped build [NOT STARTED]

**Goal**: Fix any residual drift in `modalExpandBranches_closed_unsat` (lines ~797-903), `kValid`
(~904-915), and `modalTableau_sound` (~916-947), achieving a fully clean scoped
`lake build Cslib.Logics.Modal.Tableau.Soundness`.

**Tasks**:
- [ ] Run scoped `lake build`; read each remaining error site (lines >796) in <=120-line slices.
- [ ] Apply the appropriate fix family (likely Families 1/2 recurrences) to each site; use
      `lean_goal` only where the corrected shape is non-obvious.
- [ ] Re-run scoped `lake build`; iterate until zero errors for the module.

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — proof bodies in `modalExpandBranches_closed_unsat`,
  `modalTableau_sound`, and any residual sites (lines ~797-947). Statements unchanged.

**Verification**:
- Scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` exits clean (zero errors, zero
  warnings beyond pre-existing acceptable ones).
- No `sorry`/`admit`/`axiom` introduced.
- Commit: `task 364 phase 4: repair tail declarations; scoped build green`.

---

### Phase 5: Full-build, lint, and axiom/statement audit [NOT STARTED]

**Goal**: Confirm the repair is complete, faithful, and CI-clean across the whole library.

**Tasks**:
- [ ] Run full `lake build` (whole library) and confirm green.
- [ ] Run `lake exe lint-style` and fix any style-only issues on the edited file without altering
      proof semantics.
- [ ] Run `#print axioms modalTableau_sound` (and key intermediate theorems); confirm only the
      standard axioms appear (no new axioms, no `sorryAx`).
- [ ] `grep -nE 'sorry|admit' Cslib/Logics/Modal/Tableau/Soundness.lean` returns nothing.
- [ ] `git diff` review confirming every change is inside a proof body — no theorem/lemma/def
      signature was altered.

**Timing**: 0.5 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — style-only adjustments if `lint-style` requires.

**Verification**:
- Full `lake build` green; `lake exe lint-style` passes.
- `#print axioms` shows zero new axioms / zero `sorryAx`; no `sorry`/`admit` in the file.
- `git diff` confirms statements preserved.
- Commit: `task 364 phase 5: complete drift repair — full build + lint green, zero new axioms`.

## Testing & Validation

- [ ] Scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` clean (Phase 4).
- [ ] Full `lake build` clean (Phase 5).
- [ ] `lake exe lint-style` passes on the edited file (Phase 5).
- [ ] `#print axioms modalTableau_sound` shows zero new axioms and no `sorryAx` (Phase 5).
- [ ] No `sorry`/`admit` anywhere in the file (Phase 5).
- [ ] `git diff` confirms only proof bodies changed; all statements preserved (Phase 5).

## Artifacts & Outputs

- Repaired `Cslib/Logics/Modal/Tableau/Soundness.lean` (sorry-free, green build).
- Incremental commits, one per phase (Phase 2 is an intentional WIP checkpoint).
- Execution summary at `specs/364_modal_tableau_soundness_drift_repair/summaries/01_*.md`.

## Rollback/Contingency

- All work is confined to one file with per-phase commits, so any phase can be reverted with
  `git revert`/`git checkout` of that commit without affecting other modules.
- If the Phase-2 Family-3 pattern cannot be derived from a single `lean_goal` probe, fall back to
  `lean_multi_attempt` to test candidate simp-set/`obtain` combinations at the site before editing.
- If `lake exe lint-style` conflicts with a required proof construct, prefer the build-green form
  and document the lint exception rather than introducing semantic changes.
- The pre-repair file state is recoverable from git history at any point.
