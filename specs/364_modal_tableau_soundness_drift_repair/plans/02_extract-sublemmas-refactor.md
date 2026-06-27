# Implementation Plan: Task #364

- **Task**: 364 - Repair Mathlib/toolchain-drift build failure in `Cslib/Logics/Modal/Tableau/Soundness.lean` (extract-sub-lemmas refactor)
- **Status**: [NOT STARTED]
- **Effort**: 9 hours
- **Dependencies**: None (closed-branch cluster already repaired in commit `c299dfdc`)
- **Research Inputs**:
  - specs/364_modal_tableau_soundness_drift_repair/reports/01_drift-diagnosis.md
  - specs/364_modal_tableau_soundness_drift_repair/reports/02_refactor-strategy.md
- **Artifacts**: plans/02_extract-sublemmas-refactor.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`Cslib/Logics/Modal/Tableau/Soundness.lean` (948 lines) is sorry-free but broke under
`leanprover/lean4:v4.31.0`. The closed-branch lemma cluster (Families 1/2/4, lines ~63-184)
was already repaired and committed in `c299dfdc` (the `Proposition.beqToEq` helper exists at
line 78). **All ~68 remaining errors are confined to the single monolithic theorem
`modalStepBranch_preserves_sat` (lines 186-787).** Three prior single-pass agents overflowed
context because that theorem's shared prologue (197-207) accumulates ~13 hypotheses, so every
`lean_goal` probe inside it returns a ~1 KB context and the theorem needs far more probes than
one agent context can hold.

Per report 02 (authoritative; orchestrator handoff recommends ADOPT), the fix is a **faithful
structural refactor, not a redesign**: extract each of the **10 non-trivial rule-cases** into an
independently-stated `private lemma` that takes only the hypotheses that case needs, bounding
each sub-lemma's `lean_goal` context to a small, inspectable size. The public signature of
`modalStepBranch_preserves_sat` (lines 186-196) is preserved **byte-for-byte** because it is
load-bearing downstream (`modalExpandBranches_closed_unsat` line 798, `modalTableau_sound` line
917, call site 941). Definition of done: scoped + full `lake build` clean, `lake exe lint-style`
clean, zero `sorry`, zero `admit`, zero new axioms, all statements preserved.

The plan is deliberately chunked: **Phase 0** lands the structure with 10 `sorry` stubs (a
green-but-scaffolded checkpoint that breaks the catch-22), then **one sub-lemma per phase**
strictly reduces the sorry count to zero. Each phase is a single bounded `cslib-implementation-agent`
run referencing exact line numbers and lemma names so the implementer never loads the whole file.

### Research Integration

This plan supersedes the linear T-side/F-side approach of plan `01` with report 02's
extract-sub-lemmas strategy. Key corrections from report 02 integrated here:
- The "5 parallel rule-cases" framing in the task/report 01 is the **positive-sign branch only**.
  The theorem has a **symmetric negative-sign branch** with 5 more cases. There are **10**
  Family-3 `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩ := hsf` sites (pos: 230/276/303/335/362; neg:
  402/625/649/705/729), not 5.
- `boxNeg` (N1, lines 396-616, ~220 lines) carries all four fix-families and is ~5× any other
  case — it is the true bottleneck and gets a dedicated phase with an internal sub-decomposition
  contingency.
- The four drift fix-families and their idioms (report 01): F1 `cases h : sf.sign <;>
  simp_all [Sign.isPos]`; F2 reorder `simp only [Satisfies]` after `rw`, or use
  `Satisfies.neg_iff` / `Satisfies.diamond_iff` / `Proposition.neg_def`; F3 re-derive the
  post-`simp` shape of `hsf` via `lean_goal` and fix the `obtain`/simp-set; F4 route through the
  in-scope `Proposition.beqToEq` (line 78) instead of `LawfulBEq.eq_of_beq`.

### Prior Plan Reference

Prior plan `01_soundness-drift-repair.md` (status [IMPLEMENTING], Phase 1 [COMPLETED], Phase 2
[IN PROGRESS]). Lessons carried forward: (1) Phase 1's closed-branch repair is **already
committed** (`c299dfdc`) and must not be redone — `Proposition.beqToEq` is the validated Family-4
route. (2) The linear "repair the monolith in place" approach is what overflowed context; this
plan replaces it with extraction so each chunk is bounded. (3) The WIP-checkpoint commit
discipline and the strict "scoped build + error-count-as-progress-metric" rhythm are retained.
This plan does **not** copy phases from plan 01; it is a fresh decomposition.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap flag/path supplied). This task restores the last remaining
originally-failing CSLib module from the 2026-06 CI-failure fix sweep to a green build.

## Goals & Non-Goals

**Goals**:
- Restore `Cslib/Logics/Modal/Tableau/Soundness.lean` to a clean scoped and full `lake build`.
- Pass `lake exe lint-style` (and `lake exe checkInitImports`) on the repaired file.
- Preserve the public signature of `modalStepBranch_preserves_sat` (186-196) byte-for-byte and
  every other theorem/lemma/def statement exactly. Faithful drift repair via internal
  re-partitioning only.
- End state: zero `sorry`, zero `admit`, zero new axioms (`#print axioms modalTableau_sound` /
  `lean_verify`).

**Non-Goals**:
- Redesigning tableau definitions, rule recognizers, semantics, or any theorem statement.
- Changing proof structure beyond extraction-into-sub-lemmas plus the drift fixes.
- Touching any other CSLib module (changes scoped to this one file; reuse existing helpers only).
- Adding new public API. Sub-lemmas are `private lemma` in the existing namespace.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `lean_goal` context overflow inside `modalStepBranch_preserves_sat` (the catch-22 that defeated 3 prior agents) | H | H | Phase 0 extracts every case into a sub-lemma with only ~10 binders; all later probes hit small sub-lemma goals, not the monolith. Never call `lean_diagnostic_messages`. Read file in ≤120-line slices. |
| `hsf` boundary unification fails when dispatching skeleton → sub-lemma | M | M | Lock the `hsf` boundary in Phase 0 by probing the small skeleton goal at each `exact`. Fallback: keep `simp only [modalApplyOne] at hsf` in the skeleton and declare each sub-lemma's `hsf` as the *unfolded* equation. Pick one boundary and apply uniformly (report 02 §3). |
| Phase 0 introduces 10 `sorry` stubs (zero-debt tension) | H | L | Stubs are an intermediate scaffold only. Each later phase strictly reduces the sorry count; Phase 11 `lean_verify`/`#print axioms` gate is mandatory and blocking. Task MUST NOT be marked complete while any sorry remains. No axiom may bridge a stuck case. |
| `boxNeg` (N1) re-accumulates a large state internally even after extraction | M | M | Dedicated Phase 10; if `lean_goal` overflows mid-case, sub-decompose into `…_boxNeg_boxProps_sat` (482-530) and `…_boxNeg_diaNegProps_sat` (531-602) helpers before drift-repair (report 02 §5). |
| A fix accidentally weakens a statement (`sorry`/`admit`/vacuous rewrite/signature edit) | H | L | Phase 11 `#print axioms` + `git diff` review confirming the public signature (186-196) is unchanged and only proof bodies / new `private lemma`s were added. |
| `lake exe lint-style` flags the new `private lemma` names or reformatted lines | L | M | Sub-lemma names follow the file's snake_case-with-suffix convention (`lemma`, not `def`) — not flagged by `defsWithUnderscore` (report 02 §2). Resolve any style-only issues in Phase 11 without semantic change. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 | 0 |
| 3 | 11 | 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 |

Phases 1-10 each own exactly one disjoint `private lemma` body (no file conflicts) and are
mutually independent — they may execute in any order, or in parallel under a `--team`
implementation with one territory contract per sub-lemma. Phase 10 (`boxNeg`) is the long pole;
size its run generously. Phase 11 is the blocking zero-debt gate and runs only after every
sub-lemma is sorry-free.

### Phase 0: Structural refactor — extract 10 stubbed sub-lemmas + skeleton [NOT STARTED]

- **Goal:** Land the structure before any drift-repair so no later pass needs the monolith's
  context. Extract all 10 non-trivial rule-cases into `private lemma … := by sorry` stubs with the
  report-02 §2 signatures; rewrite `modalStepBranch_preserves_sat` to the §3 skeleton (prologue +
  per-case `exact` dispatch). Repair the short trivial arms inline (they are 2-4 lines, no
  overflow). **End state: the file builds with exactly 10 `sorry`s and the public signature
  (186-196) byte-for-byte unchanged.**
- **Tasks:**
  - [ ] Read lines 186-787 in ≤120-line slices to capture each case body verbatim before moving it.
  - [ ] Add 10 `private lemma` stubs in `namespace Cslib.Logic.Modal.Tableau` under the existing
        `variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]` (line 54), using the §2 common
        signature template. Names + extra binders: `…_boxPos (φ lbl)`, `…_negPos (a lbl)`,
        `…_orPos (a1 c lbl)`, `…_impPos (a1 a2 c lbl)`, `…_impPosGen (a c lbl)`,
        `…_boxNeg (φ lbl)` **+ `hInv` binder**, `…_negNeg (a lbl)`, `…_orNeg (a1 c lbl)`,
        `…_impNeg (a1 a2 c lbl)`, `…_impNegGen (a c lbl)`. Each body is `by sorry` for now.
  - [ ] Rewrite the theorem body to the §3 skeleton: prologue (197-207) verbatim; `cases sign`
        then `cases formula` (+ nested `cases c/a/a2`) dispatching each non-trivial leaf via
        `exact modalStepBranch_preserves_sat_<RULE> b acc newBs newExps newAcc <binders> m f hacc
        hb hsfmem <hpos|hneg> [hInv] hsf`.
  - [ ] Keep inline: the two trivial `pos` arms (`.atom p` 213-216, `.bot` 217-219), the two
        trivial `neg` arms (`.atom p` 389-391, `.bot` 392-395), and the degenerate `imp φ bot2`
        arm (747-787, closed by `simp at bot2`). Repair these short arms here.
  - [ ] Lock the `hsf` boundary: probe the small skeleton goal with `lean_goal` at each `exact` to
        confirm unification. Decide raw-vs-unfolded `hsf` (report 02 §3) and apply uniformly. If
        raw, move `simp only [modalApplyOne] at hsf` (currently at 211 pos / 387 neg) to be the
        first line of each sub-lemma body in later phases.
  - [ ] Scoped `lake build Cslib.Logics.Modal.Tableau.Soundness`; confirm it builds with exactly
        10 `sorry` warnings and zero errors.
- **Timing:** 1.5 hours
- **Depends on:** none
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — add 10 `private lemma` stubs;
  replace the body of `modalStepBranch_preserves_sat` (197-787) with the skeleton. Signature
  (186-196) unchanged.
- **Verification:** scoped `lake build` green with **exactly 10** `sorry`s; `git diff` shows the
  public signature (186-196) unchanged. Commit:
  `task 364 phase 0: extract modalStepBranch_preserves_sat sub-lemmas (stubbed)`.

---

### Phase 1: Drift-repair `…_boxPos` (P1) [NOT STARTED]

- **Goal:** Replace the `…_boxPos` sorry with the repaired proof transcribed from source lines
  220-266. Fix-families: F3 (obtain @230), F2 (Satisfies unfold @262), F4 (beq @244).
- **Tasks:**
  - [ ] Read source lines 220-266 (the boxPos case body) in one ≤120-line slice.
  - [ ] First body line: `simp only [modalApplyOne] at hsf` (if raw-`hsf` boundary chosen in P0).
  - [ ] F3: place `lean_goal` immediately before the `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩ := hsf`
        (ex-line 230) to read the post-`simp [tryAllPropRules, applyPropRule, modalAndOf?,
        modalOrOf?, modalImpOf?, modalNegOf?, …]` shape; adjust the simp-set (add missing
        `Option.some.injEq`/`Prod.mk.injEq`/recognizer-unfold lemmas) or the `obtain` pattern so
        `hnewBs`/`hnewAcc` bind again.
  - [ ] F4 (ex-line 244): replace `LawfulBEq.eq_of_beq` with `Proposition.beqToEq _ _ <hbeq>`
        (line 78, in scope).
  - [ ] F2 (ex-line 262): reduce `¬φ`/`◇φ` via `Satisfies.neg_iff` / `Satisfies.diamond_iff` /
        `Proposition.neg_def` before/instead of a no-op `simp only [Satisfies]`.
  - [ ] Scoped `lake build`; confirm sorry count is now 9 and `…_boxPos` is error-free.
- **Timing:** 0.75 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_boxPos` only.
- **Verification:** scoped build green, sorry count 9, no new axioms. Commit:
  `task 364 phase 1: drift-repair modalStepBranch_preserves_sat_boxPos`.

---

### Phase 2: Drift-repair `…_negPos` (P2) [NOT STARTED]

- **Goal:** Repair `…_negPos` from source lines 270-290. Families: F3 (obtain @276), F2 (@288).
- **Tasks:**
  - [ ] Read source lines 270-290.
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] F3 @276: `lean_goal` before the `obtain`; restore `hnewBs`/`hnewAcc` binding per P1 idiom.
  - [ ] F2 @288: negation unfold via `Satisfies.neg_iff` / `Proposition.neg_def`.
  - [ ] Scoped `lake build`; sorry count → 8, `…_negPos` error-free.
- **Timing:** 0.5 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_negPos` only.
- **Verification:** scoped build green, sorry count 8, no new axioms. Commit:
  `task 364 phase 2: drift-repair modalStepBranch_preserves_sat_negPos`.

---

### Phase 3: Drift-repair `…_orPos` (P3) [NOT STARTED]

- **Goal:** Repair `…_orPos` from source lines 297-328. Families: F3 (obtain @303), F2 (@307).
- **Tasks:**
  - [ ] Read source lines 297-328.
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] F3 @303: `lean_goal` before the `obtain`; restore binding per P1 idiom.
  - [ ] F2 @307: negation/Satisfies unfold as needed.
  - [ ] Scoped `lake build`; sorry count → 7, `…_orPos` error-free.
- **Timing:** 0.5 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_orPos` only.
- **Verification:** scoped build green, sorry count 7, no new axioms. Commit:
  `task 364 phase 3: drift-repair modalStepBranch_preserves_sat_orPos`.

---

### Phase 4: Drift-repair `…_impPos` (P4) [NOT STARTED]

- **Goal:** Repair `…_impPos` from source lines 329-356. Families: F3 (obtain @335), F2 (@337).
- **Tasks:**
  - [ ] Read source lines 329-356.
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] F3 @335: `lean_goal` before the `obtain`; restore binding per P1 idiom.
  - [ ] F2 @337: negation/Satisfies unfold as needed.
  - [ ] Scoped `lake build`; sorry count → 6, `…_impPos` error-free.
- **Timing:** 0.5 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_impPos` only.
- **Verification:** scoped build green, sorry count 6, no new axioms. Commit:
  `task 364 phase 4: drift-repair modalStepBranch_preserves_sat_impPos`.

---

### Phase 5: Drift-repair `…_impPosGen` (P5) [NOT STARTED]

- **Goal:** Repair `…_impPosGen` from source lines 357-383. Families: F3 (obtain @362), F2 (@364).
- **Tasks:**
  - [ ] Read source lines 357-383.
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] F3 @362: `lean_goal` before the `obtain`; restore binding per P1 idiom.
  - [ ] F2 @364: negation/Satisfies unfold as needed.
  - [ ] Scoped `lake build`; sorry count → 5, `…_impPosGen` error-free.
- **Timing:** 0.5 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_impPosGen` only.
- **Verification:** scoped build green, sorry count 5, no new axioms. Commit:
  `task 364 phase 5: drift-repair modalStepBranch_preserves_sat_impPosGen`.

---

### Phase 6: Drift-repair `…_negNeg` (N2) [NOT STARTED]

- **Goal:** Repair `…_negNeg` from source lines 620-638. Families: F3 (obtain @625), F2 (@635).
- **Tasks:**
  - [ ] Read source lines 620-638.
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] F3 @625: `lean_goal` before the `obtain`; restore binding per P1 idiom.
  - [ ] F2 @635: negation unfold via `Satisfies.neg_iff` / `Proposition.neg_def`.
  - [ ] Scoped `lake build`; sorry count → 4, `…_negNeg` error-free.
- **Timing:** 0.5 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_negNeg` only.
- **Verification:** scoped build green, sorry count 4, no new axioms. Commit:
  `task 364 phase 6: drift-repair modalStepBranch_preserves_sat_negNeg`.

---

### Phase 7: Drift-repair `…_orNeg` (N3) [NOT STARTED]

- **Goal:** Repair `…_orNeg` from source lines 644-699. Families: F3 (obtain @649), F2 (@680/693).
- **Tasks:**
  - [ ] Read source lines 644-699 (two ≤120-line slices not needed; one slice covers it).
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] F3 @649: `lean_goal` before the `obtain`; restore binding per P1 idiom.
  - [ ] F2 @680 and @693: negation/Satisfies unfolds.
  - [ ] Scoped `lake build`; sorry count → 3, `…_orNeg` error-free.
- **Timing:** 0.5 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_orNeg` only.
- **Verification:** scoped build green, sorry count 3, no new axioms. Commit:
  `task 364 phase 7: drift-repair modalStepBranch_preserves_sat_orNeg`.

---

### Phase 8: Drift-repair `…_impNeg` (N4) [NOT STARTED]

- **Goal:** Repair `…_impNeg` from source lines 700-723. Families: F3 (obtain @705), F2 (@715/721).
- **Tasks:**
  - [ ] Read source lines 700-723.
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] F3 @705: `lean_goal` before the `obtain`; restore binding per P1 idiom.
  - [ ] F2 @715 and @721: negation/Satisfies unfolds.
  - [ ] Scoped `lake build`; sorry count → 2, `…_impNeg` error-free.
- **Timing:** 0.5 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_impNeg` only.
- **Verification:** scoped build green, sorry count 2, no new axioms. Commit:
  `task 364 phase 8: drift-repair modalStepBranch_preserves_sat_impNeg`.

---

### Phase 9: Drift-repair `…_impNegGen` (N5) [NOT STARTED]

- **Goal:** Repair `…_impNegGen` from source lines 724-746. Families: F3 (obtain @729), F2 (@738/744).
- **Tasks:**
  - [ ] Read source lines 724-746.
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] F3 @729: `lean_goal` before the `obtain`; restore binding per P1 idiom.
  - [ ] F2 @738 and @744: negation/Satisfies unfolds.
  - [ ] Scoped `lake build`; sorry count → 1, `…_impNegGen` error-free.
- **Timing:** 0.5 hour
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_impNegGen` only.
- **Verification:** scoped build green, sorry count 1, no new axioms. Commit:
  `task 364 phase 9: drift-repair modalStepBranch_preserves_sat_impNegGen`.

---

### Phase 10: Drift-repair `…_boxNeg` (N1) — the bottleneck [NOT STARTED]

- **Goal:** Replace the last sorry (`…_boxNeg`, source lines 396-616, ~220 lines) — the only case
  carrying **all four fix-families**. Drives the file to **zero sorry**.
- **Tasks:**
  - [ ] Read source lines 396-616 in ≤120-line slices (this is ~2 slices); do not load it all at once.
  - [ ] First body line `simp only [modalApplyOne] at hsf` (if raw boundary).
  - [ ] **Overflow contingency (apply FIRST if `lean_goal` mid-case is large):** sub-decompose into
        two further `private lemma` helpers before drift-repair — `…_boxNeg_boxProps_sat`
        (discharges `sf' ∈ boxProps`, source 482-530) and `…_boxNeg_diaNegProps_sat` (discharges
        `sf' ∈ diaNegProps`, source 531-602) — each taking the fresh-world data
        (`w' = modalNextWorld b`, `f'`, `ww`, `hwwr`, relevant membership) as explicit binders so
        its goal stays small. Alternatively scope them with internal `suffices`/`have` blocks.
  - [ ] F3 @402: `lean_goal` before the `obtain`; restore `hnewBs`/`hnewAcc` binding.
  - [ ] F2 @407: Satisfies/diamond-negation unfold (`Satisfies.diamond_iff` / `Proposition.neg_def`).
  - [ ] F4 @441, @499, @506, @534, @560-561: route every `LawfulBEq.eq_of_beq`/`beq_iff_eq` through
        `Proposition.beqToEq _ _ <hbeq>` (line 78).
  - [ ] F1 @509-512 and @553-557: `cases h : sf.sign with | pos => rfl | neg => simp [h, Sign.isPos]
        at hpos` (the validated Phase-1 idiom from `modalClosed_unsat` 119-121).
  - [ ] Freshness: reuse `modalNextWorld_gt` (`Branch.lean:104`) at the four sites 446/523/579/606;
        `hInv` (the boxNeg-only binder) is used at 458/465.
  - [ ] Scoped `lake build`; confirm **sorry count 0** and `…_boxNeg` (+ any helpers) error-free.
- **Timing:** 2 hours
- **Depends on:** 0
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — body of `…_boxNeg` (and up to
  two optional `…_boxNeg_*_sat` private helpers).
- **Verification:** scoped build green with **zero** sorry; no new axioms. If a sorry-free proof
  cannot be reached, mark **this phase** `[BLOCKED]` with the goal state and what is needed — do
  NOT leave the sorry or bridge it with an axiom. Commit:
  `task 364 phase 10: drift-repair modalStepBranch_preserves_sat_boxNeg (zero sorry)`.

---

### Phase 11: Zero-debt verification — full build, lint, axiom/statement audit [NOT STARTED]

- **Goal:** Confirm the repair is complete, faithful, and CI-clean across the whole library.
- **Tasks:**
  - [ ] Scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` clean (zero errors, zero sorry).
  - [ ] Full `lake build` (whole library) green.
  - [ ] `lean_verify Cslib.Logic.Modal.Tableau.modalStepBranch_preserves_sat` (or `#print axioms
        modalTableau_sound`) shows zero `sorryAx` / zero new axioms.
  - [ ] `grep -nE 'sorry|admit' Cslib/Logics/Modal/Tableau/Soundness.lean` returns nothing.
  - [ ] `lake exe lint-style` and `lake exe checkInitImports` pass; fix style-only issues without
        semantic change.
  - [ ] `git diff` review: public signature of `modalStepBranch_preserves_sat` (186-196) unchanged;
        all other statements preserved; only proof bodies + new `private lemma`s added.
- **Timing:** 0.5 hour
- **Depends on:** 1, 2, 3, 4, 5, 6, 7, 8, 9, 10
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Soundness.lean` — style-only adjustments if
  `lint-style` requires.
- **Verification:** full `lake build` + `lake exe lint-style` + `lake exe checkInitImports` green;
  `lean_verify`/`#print axioms` clean; no `sorry`/`admit`; statements preserved. Commit:
  `task 364: complete implementation`.

## Testing & Validation

- [ ] Phase 0: scoped `lake build` green with exactly 10 `sorry`s; signature 186-196 unchanged.
- [ ] Phases 1-10: scoped `lake build` green after each, with the sorry count strictly decreasing
      (10 → 0); never increasing.
- [ ] Phase 11: full `lake build` clean.
- [ ] Phase 11: `lake exe lint-style` and `lake exe checkInitImports` pass.
- [ ] Phase 11: `lean_verify` / `#print axioms modalTableau_sound` shows zero `sorryAx`, zero new
      axioms.
- [ ] Phase 11: no `sorry`/`admit` in the file; `git diff` confirms all statements preserved.

## Artifacts & Outputs

- Repaired `Cslib/Logics/Modal/Tableau/Soundness.lean` (sorry-free, green build, 10 new
  `private lemma`s, public signature preserved).
- Incremental commits, one per phase (Phase 0 is a green-but-scaffolded checkpoint with 10 sorries;
  every later commit strictly reduces the sorry count).
- Execution summary at `specs/364_modal_tableau_soundness_drift_repair/summaries/02_*.md`.

## Rollback/Contingency

- All work is confined to one file with per-phase commits; any phase can be reverted with
  `git revert`/`git checkout` of that commit without affecting other modules.
- The Phase-0 commit is a safe checkpoint: if a later per-case phase cannot reach a sorry-free
  proof, mark that phase `[BLOCKED]` with the goal state — do not leave a stray sorry in a
  "complete" task and do not introduce an axiom.
- If the `hsf` boundary chosen in Phase 0 proves fussy in a per-case phase, switch to the fallback
  boundary (keep `simp only [modalApplyOne]` in the skeleton; sub-lemma takes the unfolded
  equation) — but apply the choice uniformly across all sub-lemmas.
- If `boxNeg` (Phase 10) overflows even after extraction, apply the §5 internal sub-decomposition
  (`_boxProps_sat` / `_diaNegProps_sat`) before drift-repair.
- The pre-repair file state is recoverable from git history at any point (closed-branch repair is
  preserved at `c299dfdc`).
