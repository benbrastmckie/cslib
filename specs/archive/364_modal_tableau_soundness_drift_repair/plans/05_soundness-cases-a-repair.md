# Implementation Plan: Task #364 - Modal Tableau Soundness Drift Repair (Strategy B / cases-`a`)

- **Task**: 364 - modal_tableau_soundness_drift_repair
- **Status**: [IN PROGRESS]
- **Effort**: 6 hours (Phase 1 already complete; ~5 hours remaining)
- **Dependencies**: None
- **Research Inputs**: reports/04_recognizer-reduction-strategy.md (PRIMARY — the strategy decision: adopt Strategy B `cases a`, reject Strategy A and the report-02 10-sub-lemma refactor); reports/03_verified-fix-mapping.md (supplementary, build-grounded; superseded for the recognizer roots by report 04); `.error-digest.md` (UPDATE section) and `.orchestrator-handoff.json` (record what already happened: Root A fixed, 5 agents overflowed).
- **Artifacts**: plans/05_soundness-cases-a-repair.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Repair the remaining Mathlib/toolchain-drift build failure in
`Cslib/Logics/Modal/Tableau/Soundness.lean`. Current state: **61 scoped-build errors, zero
`sorry`** (Root A boxPos `split_ifs` drift already fixed and committed at 425c1c53, 62→61). This
revision supersedes plan 03's "all-mechanical-drift" thesis for the recognizer roots: report 04
proves the `| imp a c => cases c with | bot =>` arms (negPos ~line 269 T-side, negNeg ~line 619
F-side) are **not** mechanical drift but a genuine reduction-order / proof-structure defect that
requires `cases a` restructuring to bounded depth-3. Five autonomous agents have OVERFLOWED on
this file because every state-inspection tool surfaces the ~400-line `hsf` hypothesis; therefore
**the central constraint of this plan is overflow-safe phase sizing** — every phase is one bounded
agent run, and the heavy recognizer leaves are repaired *blind* using shapes pre-verified in
report 04's scratch proofs. Definition of done (unchanged): scoped + full `lake build` clean,
`lake exe lint-style` clean, zero `sorry`, zero new axioms, every public statement byte-for-byte
preserved.

### Research Integration

Report 04 (`reports/04_recognizer-reduction-strategy.md`) is the authoritative source for the
recognizer roots and supersedes plan 03 on this point. Its verified findings drive this plan:

- **Strategy B (cases `a`) is REQUIRED and adopted** for the c = ⊥ arms (negPos `:269`, negNeg
  `:619`). It is the only correctness-complete fix: for `formula = .imp a .bot`, the actually-firing
  prop rule depends on the head of `a` (andPos when `a = p → (q → ⊥)`; orPos when `a = p → ⊥`;
  negPos otherwise — see F2 table). The current uniform-negPos arm is *doubly broken* (stalls for
  abstract `a`, and is semantically wrong for the andPos/orPos heads).
- **Strategy A (standalone `@[simp]` reduction lemmas) is REJECTED** — no unconditional RHS exists
  for `tryAll ⟨.pos, .imp a .bot, l⟩`, and lemmas cannot fix the semantic error. The report-02
  10-sub-lemma refactor is likewise REJECTED (over-engineered; re-encodes the case tree elsewhere).
- **Per-leaf reductions are `rfl`-grade once the head is concrete** and close with the *existing*
  in-file simp set + the **flat** obtain `⟨hnewBs, _, hnewAcc⟩` (report 04 F4 verified all leaves in
  scratch with `lake env lean`, EXIT 0; the abstract-`a2` case provably fails `rfl`, confirming the
  tree bottoms out at depth 3). This is the same flat-obtain idiom committed for Root A (425c1c53).
- **The c ≠ ⊥ arms are already semantically correct** (they already `cases a`); their only defect is
  the stale *nested* obtain `⟨⟨hnewBs, _⟩, hnewAcc⟩` at `:302,334,361,648,704,728` — flatten only.
- **The duplicate-`imp` arm `:746-786` is DEAD CODE** — `F(◇φ) = imp (box (imp φ ⊥)) ⊥` is already
  routed to negNeg; **delete it** (this resolves the `:747` duplicate-alternative error and is
  covered by the negNeg `cases a` `| box _ =>` leaf).
- **Tail items live in two `hsf`-free theorems** (`modalExpandBranches_closed_unsat`,
  `modalTableau_sound`, `:797-962`) and are SAFE for normal `lean_goal` tooling: zip block
  `List.mem_zip`→`List.getElem_zip` (`:819-825`); app-type-mismatch (`:855/869/917`) + `made no
  progress` (`:878-886`) + `unsolved goals` (`:875`); universe inference (`:956/959`).

### Prior Plan Reference

- **plans/01_soundness-drift-repair.md** — report-02-derived 10-sub-lemma refactor. Superseded:
  rejected by plans 03 and 04.
- **plans/02_*** (report-02 refactor strategy) — superseded; explicitly rejected by report 04 F5.
- **plans/03_soundness-drift-repair.md** — the immediate base for this revision. Its in-place,
  commit-per-cluster discipline and its tail-item analysis are RETAINED. **Superseded only on the
  recognizer roots**: plan 03 treated negPos `:276`/negNeg `:625` as "strengthen the simp set so
  recognizers reduce" (Family-3 sub-mode b). Report 04 refutes that — no simp strengthening can
  reduce `tryAllPropRules` for abstract `a`, and even if it could the uniform-negPos refine is
  semantically wrong. This plan replaces that approach with `cases a` restructuring.
- **What already happened (do not redo)**: Root A (boxPos `split_ifs`, line 228) is FIXED and
  committed (425c1c53), 62→61 errors, statements preserved, zero sorry. Five autonomous agents
  overflowed on the recognizer roots (2 prior session + 3 in sess_1782614477_39b09e). The cause is
  process (context overflow on the ~400-line `hsf`), and the fix is overflow-safe sizing plus blind
  edits from report 04's pre-verified shapes.

### Roadmap Alignment

No `roadmap_path` provided; roadmap consultation skipped. This task restores a previously-passing
module to green after a toolchain bump — it advances CI health for the Modal Logic topic area.

## Goals & Non-Goals

**Goals**:
- Restore `Cslib/Logics/Modal/Tableau/Soundness.lean` to a clean scoped + full `lake build`.
- Adopt report-04 Strategy B: restructure the negPos `:269` and negNeg `:619` `| bot =>` arms with
  `cases a` to bounded depth-3, selecting the actually-firing prop rule per head-shape of `a`.
- Preserve every theorem statement byte-for-byte (`git diff` shows only proof-body / `cases`-arm
  internals).
- Keep the file zero-`sorry` and add zero new axioms at every commit boundary (no intermediate
  `sorry`, no scaffolding).
- Land the repair as a sequence of independently committable, strictly-error-reducing chunks.
- Pass `lake exe lint-style` and `lake exe checkInitImports`.

**Non-Goals**:
- Strategy A standalone `@[simp]` reduction lemmas (rejected by report 04 F5).
- The report-02 10-sub-lemma extraction refactor (rejected; not even a fallback for the c = ⊥ arms —
  `cases a` inline is strictly simpler).
- Any change to public APIs, theorem statements, or definitions outside this file.
- The pre-existing `Fitting1983`/`Smullyan1968` BibKey mismatch in `Rules.lean` (orthogonal; flagged
  by report 04 §H4.6 for separate cleanup).
- Performance tuning, restructuring, or stylistic rewrites beyond what the drift repair requires.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Agent overflows on the ~400-line `hsf` (defeated 5 prior agents) | H | H | **THE primary risk.** Never call `lean_diagnostic_messages`/`lean_file_outline`; never run `lean_goal`/`lean_multi_attempt` at any position inside `modalStepBranch_preserves_sat` where `hsf` is in scope. All leaf shapes are pre-verified in report 04 F4 — edit blind. Verify only via the bounded `grep -c "error:"` command. Do experimentation in a tiny scratch file (`lake env lean`), never against the main proof. |
| A phase is too large and overflows mid-run | H | M | One bounded agent run per phase; prefer scoping to ONE `cases a` arm (or one sub-branch). A 5-site region attempt already overflowed; the 1-site Root A succeeded at 9 tool calls. negPos and negNeg are separate phases. |
| A leaf `simp` leaves a residual (e.g. `SignedFormula.neg` unfolded) | M | L | Report 04 F4 showed the existing simp set suffices with no residual. If a residual appears, add `SignedFormula.pos`/`neg` *to that leaf only* and immediately re-check for the `unusedSimpArgs` error (build-FATAL in CSLib — cf. `:131,275,624`). |
| `cases a` explodes / non-terminating | M | L | Report 04 proves the tree is bounded at depth 3 (`cases a; cases a2; cases a4`); andPos `rfl` with abstract `a1,a3`, orPos `rfl` with abstract `a1`. |
| Uncommitted edits from a prior overflowed agent are stale/regressed | M | M | Per handoff `do_not`: do NOT trust uncommitted edits. Start each phase from the committed tree; regenerate the bounded error count first. |
| zip block needs a lemma that does not exist | L | L | Report 04 confirmed via loogle: `List.mem_zip` removed; `List.getElem_zip` (`Init.Data.List.Nat.TakeDrop`) + `List.getElem_mem`/`List.mem_iff_getElem` is the replacement. `List.mem_iff_get` at `:819` still exists. |
| A statement gets altered during repair | H | L | After each phase, `git diff` the public signature lines to confirm no theorem type changed. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3, 6 | 2, 5 |
| 4 | 4 | 3 |
| 5 | 7 | 4, 6 |

Phases 2/3/4 touch `modalStepBranch_preserves_sat` (the `hsf` theorem); phases 5/6 touch the
separate `hsf`-free theorems. The wave table reflects logical independence (the tail is independent
of the recognizer work), **but the RECOMMENDED execution is strictly sequential, one bounded agent
run at a time** — they edit the same file, and the overriding constraint is overflow avoidance and
per-milestone commits. Do NOT dispatch two agents against this file concurrently.

**Global discipline (BINDING on every implementation phase — this is the whole point of the revision)**:
- NEVER call `lean_diagnostic_messages` or `lean_file_outline` (they HANG / overflow in this repo).
- NEVER run `lean_goal` / `lean_multi_attempt` at any position inside `modalStepBranch_preserves_sat`
  where `hsf` is in scope. The leaf shapes are pre-verified in report 04 F4 — edit blind.
- Do any experimentation in a TINY scratch file via `lake env lean scratch_364.lean` (import
  `Cslib.Logics.Modal.Tableau.Rules`); delete it after use. Never experiment against the main proof.
- `lean_goal` is permitted ONLY in Phases 5-6 (the `hsf`-free tail theorems).
- Check builds ONLY via the bounded commands:
  - `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1 | grep -c "error:"` (count)
  - `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1 | grep -nE "error:" | sort -u` (bounded
    locations — never dump the full 1600-line log).
- Read the file in ≤120-line slices.
- Commit per green / strictly-fewer-errors milestone. No intermediate `sorry`, no scaffolding.
- Prefer scoping a phase to ONE `cases a` arm (or one sub-branch) over a whole region.

### Phase 1: Root A — boxPos `split_ifs` drift (line 228) [COMPLETED]

- **Goal:** Fix the boxPos `split_ifs` drift so the empty-`boxPropagation` branch is not
  double-handled and `hsf` flattens.
- **Tasks:**
  - [x] Remove the spurious leading `· simp at hsf` bullet at 227-231, de-indent.
  - [x] Flatten the obtain to `⟨hnewBs, _, hnewAcc⟩` (drift changed `hsf` post-simp shape from nested
    `⟨⟨_,_⟩,_⟩` to flat right-assoc `A ∧ B ∧ C`).
- **Timing:** done
- **Depends on:** none
- **Completed:** committed 425c1c53 (scoped build 62 → 61, zero sorry, statements preserved). This
  established the reusable flat-obtain + plain-simp idiom used by all later recognizer leaves.

---

### Phase 2: c ≠ ⊥ flat-obtain sweep (mechanical, ~6 edits) [IN PROGRESS]

- **Goal:** Flatten the stale nested obtains in the already-correct c ≠ ⊥ arms; remove the largest
  `Unknown identifier hnewBs` cascade and confirm the flat-obtain hypothesis on real code before the
  heavier restructuring phases.
- **Tasks:**
  - [ ] Replace `obtain ⟨⟨hnewBs, _⟩, hnewAcc⟩ := hsf` → `obtain ⟨hnewBs, _, hnewAcc⟩ := hsf` at the
    six sites: `:302, :334, :361` (T-side pos) and `:648, :704, :728` (F-side neg). (Site line
    numbers are pre-drift estimates; locate each by the nested-obtain pattern, not by absolute line.)
  - [ ] No other change. These arms already `cases a` and are semantically correct (report 04 F3).
  - [ ] Verify with the bounded error count only. Expected: clears the `Unknown identifier hnewBs`
    cascades at `:304, :336, :363, :403, :650, :706, :730` (≈ the 46-error cascade shrinks sharply).
- **Timing:** ~0.5 hour
- **Depends on:** 1
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1 | grep -c "error:"` strictly < 61.
  - `git diff` confirms only `obtain` shapes changed; no theorem signature changed.
  - Commit: `task 364 phase 2: flatten c != bot obtains (Mathlib conjunction-shape drift)`.

---

### Phase 3: negPos c = ⊥ restructuring — `cases a` depth-3 (T-side, ~`:269-289`) [NOT STARTED]

- **Goal:** Replace the broken uniform-negPos `| bot =>` arm with a bounded depth-3 `cases a` tree
  that selects the actually-firing rule (negPos / orPos / andPos) per head-shape of `a`.
- **Tasks:**
  - [ ] In the `| imp a c => cases c with | bot =>` arm at ~`:269`, replace the uniform
    `refine ⟨[⟨.neg, a, lbl⟩] ++ b, …⟩` body with the report-04 F-derived tree:
    ```
    cases a
    | bot       => negPos  -- linear [F ⊥]
    | atom p    => negPos  -- linear [F (atom p)]
    | box φ     => negPos  -- linear [F (box φ)]
    | imp a1 a2 =>
        cases a2
        | bot       => orPos   -- branching [[T a1],[T ⊥]]   (a = ¬a1)
        | atom s    => negPos  -- linear [F (imp a1 (atom s))]
        | box ψ     => negPos
        | imp a3 a4 =>
            cases a4
            | bot     => andPos  -- linear [T a1, T a3]      (a = a1 → (a3 → ⊥))
            | atom t  => negPos
            | box χ   => negPos
            | imp _ _ => negPos
    ```
  - [ ] Per leaf (head now concrete), use the report-04 verified idiom — the EXISTING simp set, the
    FLAT obtain, then the correct rule's semantic discharge:
    ```lean
    simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
      modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
      Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨hnewBs, _, hnewAcc⟩ := hsf   -- FLAT, not ⟨⟨_,_⟩,_⟩
    subst hnewBs hnewAcc
    ```
  - [ ] negPos leaves reuse the existing negPos discharge (`linear [F …]`). The orPos leaf reuses the
    existing c ≠ ⊥ orPos `branching` discharge (`:307-327`), adapted for the `T ⊥` member. The andPos
    leaf reuses the `linear [T a1, T a3]` discharge.
  - [ ] Do NOT add `SignedFormula.pos`/`neg` to the simp set unless a specific leaf leaves a residual;
    if added, it must be per-leaf and must not trip the `unusedSimpArgs` build-fatal linter.
  - [ ] OVERFLOW DISCIPLINE: do all leaf shape checks in a scratch file beforehand (report 04 already
    did this — the shapes are in F4); never run `lean_goal`/`lean_multi_attempt` against `hsf`.
- **Timing:** ~1.5 hours (heaviest phase; one `cases a` arm only)
- **Depends on:** 2
- **Verification:**
  - Bounded error count strictly fewer than after Phase 2; the `:275/:276` negPos root and its
    cascade (`:304,:336,:363,:403` were already cleared in P2; `:275` cleared here) gone.
  - `git diff` confirms no theorem signature changed (only `cases`-arm internals).
  - Commit: `task 364 phase 3: restructure negPos c=bot arm with cases a (Strategy B)`.

---

### Phase 4: negNeg c = ⊥ restructuring (F-side, ~`:619-637`) + delete dead duplicate-`imp` arm [NOT STARTED]

- **Goal:** Mirror Phase 3 on the F-side and delete the dead duplicate-`imp` arm that causes the
  `:747` duplicate-alternative error.
- **Tasks:**
  - [ ] In the F-side `| imp a c => cases c with | bot =>` arm at ~`:619`, apply the dual of the
    Phase-3 tree: same head→rule map, swapping pos↔neg (negNeg / orNeg / andNeg). Per leaf use the
    same existing simp set + flat `obtain ⟨hnewBs, _, hnewAcc⟩` idiom; reuse the existing F-side
    discharges.
  - [ ] DELETE the dead `| imp φ bot2 =>` arm at ~`:746-786`: `F(◇φ) = imp (box (imp φ ⊥)) ⊥` is an
    `imp a ⊥` already routed to negNeg via the `| imp a c =>` arm (author's own comments `:756-785`
    confirm). Deletion resolves the `:747` `Duplicate alternative name imp` error and is covered by
    the new negNeg `cases a | box _ =>` leaf.
  - [ ] OVERFLOW DISCIPLINE: same as Phase 3 — edit blind from report-04 shapes; no `hsf` inspection.
- **Timing:** ~1.5 hours (one `cases a` arm + one deletion)
- **Depends on:** 3 (reuse the Phase-3 idiom; serialize to avoid concurrent edits to the same theorem)
- **Verification:**
  - Bounded error count strictly fewer; `:624/:625` negNeg root, the `:650,:706,:730` cascade, and
    the `:747` duplicate-alternative error all gone. After this phase the entire
    `modalStepBranch_preserves_sat` theorem should be error-free.
  - `git diff` confirms no theorem signature changed (only `cases`-arm internals + arm deletion).
  - Commit: `task 364 phase 4: restructure negNeg c=bot arm + delete dead duplicate-imp arm`.

---

### Phase 5: Tail — zip-membership block (`List.mem_zip` removed, ~`:819-825`) [NOT STARTED]

- **Goal:** Repair the zero-fuel zip block in `modalExpandBranches_closed_unsat` (an `hsf`-free
  theorem — normal tooling is SAFE here).
- **Tasks:**
  - [ ] `List.mem_zip` was removed from Mathlib (report 04 loogle: only `List.of_mem_zip` remains).
    Reconstruct `(b, expandedSets.get ⟨i,_⟩) ∈ branches.zip expandedSets` via `List.getElem_zip`
    (`(l.zip l')[i] = (l[i], l'[i])`, `Init.Data.List.Nat.TakeDrop`) + `List.getElem_mem` /
    `List.mem_iff_getElem`. `List.mem_iff_get` at `:819` still exists (not flagged).
  - [ ] Fix the over-destructured `obtain` if present (`:822,:823,:828` — `Unknown identifier` /
    `Unknown constant List.…`).
  - [ ] `lean_goal` is PERMITTED here (no `hsf` in this theorem). Probe replacement lemmas with
    `lean_multi_attempt` at these positions freely.
- **Timing:** ~0.75 hour
- **Depends on:** 1 (independent theorem; needs only the committed base). May run before/after the
  recognizer phases; recommended sequential after Phase 4.
- **Verification:**
  - Bounded error count: `:822,:823,:828` cluster cleared (or strictly fewer with the zip block
    resolved).
  - `git diff` confirms no theorem signature changed.
  - Commit: `task 364 phase 5: repair zip block (List.mem_zip -> List.getElem_zip)`.

---

### Phase 6: Tail — app-type-mismatch / `made no progress` / unsolved goals (~`:855-917`) [NOT STARTED]

- **Goal:** Repair the `hnewlen`/`ih`/`ih_inner` plumbing in `modalExpandBranches_closed_unsat`
  (some cascade from the zip/length fix). `hsf`-free — normal tooling SAFE.
- **Tasks:**
  - [ ] Application type mismatch at `:855/:858, :869/:872, :917/:920`: re-thread the correct
    argument to `modalClosed_unsat` / `modalExpandBranches_closed_unsat` applications (drop spurious
    `hsat` arg or supply the correct satisfiability hyp).
  - [ ] `made no progress` at `:878,:882,:886` and `unsolved goals` at `:875`: adjust the
    `simp`/rewrite chain after the zip/length plumbing is correct.
  - [ ] `Bool.or_eq_true` is now `Eq` not `Iff` (`:892/:894`): use `rw [Bool.or_eq_true] at hedge;
    rcases hedge with h' | h'` (or `simp only [Bool.or_eq_true] at hedge`) — the `.mp` is invalid.
  - [ ] `unusedSimpArgs` (`:873`): drop the now-unused simp argument (build-fatal in CSLib).
  - [ ] `lean_goal` PERMITTED here.
- **Timing:** ~0.75 hour
- **Depends on:** 5
- **Verification:**
  - Bounded error count: the `:855-:894` cluster cleared.
  - `git diff` confirms no theorem signature changed.
  - Commit: `task 364 phase 6: repair modalExpandBranches plumbing (app mismatch, Bool.or_eq_true)`.

---

### Phase 7: Tail — universe inference + full-build regression + zero-debt gate + handoff [NOT STARTED]

- **Goal:** Fix the final universe-inference error in `modalTableau_sound`, then run the blocking
  zero-debt and full-regression gate and finalize the wrap-up.
- **Tasks:**
  - [ ] `Failed to infer universe levels of binder hsat` at `:956/:959` in `modalTableau_sound`
    (`:953-962`): `kValid` uses monomorphic `∀ (World : Type)` (`:924`); annotate/align the universe
    of the `hsat` binder. Mechanical; `lean_goal` PERMITTED.
  - [ ] If `:100` "automatically included section variable unused" still appears, address it (drop or
    use the variable as the build dictates).
  - [ ] ZERO-DEBT GATE (BLOCKING): scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` clean
    (`grep -c "error:"` == 0); full `lake build` clean; `lake exe lint-style` clean; `lake exe
    checkInitImports` clean; `lake test` (CslibTests) green.
  - [ ] `grep -n "sorry\|admit" Cslib/Logics/Modal/Tableau/Soundness.lean` returns nothing;
    `lean_verify Cslib.Logics.Modal.Tableau.modalStepBranch_preserves_sat` and `…modalTableau_sound`
    show zero `sorry` / zero new axioms.
  - [ ] Final `git diff` confirms every public theorem statement is byte-for-byte unchanged.
  - [ ] Update `.orchestrator-handoff.json` with final status, sorry_inventory (empty), CI results.
- **Timing:** ~0.5 hour
- **Depends on:** 4, 6
- **Verification:**
  - Scoped + full `lake build` clean; `lake exe lint-style` + `checkInitImports` + `lake test` green.
  - Zero sorry / zero new axioms; statements preserved.
  - Commit: `task 364: complete implementation`.

## Testing & Validation

- [ ] Scoped: `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1 | grep -c "error:"` == 0.
- [ ] Full: `lake build` exits clean across the whole library.
- [ ] Lint: `lake exe lint-style` clean.
- [ ] Init imports: `lake exe checkInitImports` clean.
- [ ] Tests: `lake test` (CslibTests) green.
- [ ] Zero sorry: `grep -n "sorry\|admit" Cslib/Logics/Modal/Tableau/Soundness.lean` empty.
- [ ] Zero new axioms: `lean_verify` on `modalStepBranch_preserves_sat` and `modalTableau_sound`.
- [ ] Statement preservation: `git diff` shows no public theorem type changed.

## Artifacts & Outputs

- `plans/05_soundness-cases-a-repair.md` (this file).
- Repaired `Cslib/Logics/Modal/Tableau/Soundness.lean` (sorry-free, all statements preserved).
- `summaries/05_soundness-cases-a-repair-summary.md` (on implementation completion).
- Updated `.orchestrator-handoff.json`.
- One git commit per phase (Phase 1 already committed at 425c1c53).

## Rollback/Contingency

- Each phase is an independent commit; revert any single phase with `git revert <sha>` without losing
  earlier chunks.
- If a phase fails to reduce errors, mark it `[PARTIAL]`, commit progress only if the file still
  builds with strictly fewer errors and zero `sorry`; otherwise leave the working tree uncommitted
  for the next `/implement` to resume. Do NOT trust uncommitted edits from a prior overflowed agent.
- NEVER introduce an intermediate `sorry` or scaffolding; if a chunk cannot be completed sorry-free,
  stop and leave it uncommitted.
- If a recognizer phase overflows despite the discipline, narrow the phase to a SINGLE `cases a`
  sub-branch (e.g. just the `| imp a1 a2 => cases a2` subtree) and commit per sub-branch — do NOT
  fall back to Strategy A or the report-02 refactor (both rejected by report 04).
