# Handoff: Task 300 — Phase 2 (T system) Blocked

## Session

`sess_1784044325_11ad9e_300` (orchestrator-driven implementation dispatch, resuming after a
prior session's session-limit termination).

## What This Session Did

1. **Recovery**: The prior session's uncommitted Phase 2 work (`FrameRules.lean` new file,
   `FrameSoundness.lean` T-soundness additions) had been temporarily stashed by a concurrent
   task-396 session (`git stash` entry `task396-temp-stash-task300-wip`, needed to get a clean
   tree for its own CI run — there is no git worktree isolation between concurrent orchestrator
   sessions in this environment). Recovered via `git stash pop` and verified content integrity
   against what had been read earlier in the session.
2. **Fixed a build break**: two `subst hsf` tactic failures in `modalTBoxSelf_sound`/
   `modalTDiaNegSelf_sound` (`FrameSoundness.lean`) — the `simp only [...]` call left the
   `if`-condition as `false = true` instead of reducing to `False`; fixed by adding
   `Bool.false_eq_true` to the simp set.
3. **Committed the recovered + fixed T-rule and T-soundness work**
   (`git 8e2a005a`'s parent, commit `a9c3e79d`).
4. **Added `extractModelT`** (+ `extractModelT_r`, `extractModelT_refl`,
   `extractModelT_hasEdge_imp_r`) to `FrameCompleteness.lean`, using `Relation.ReflGen` as the
   Strategy-B closure operator; `Std.Refl` comes free via `inferInstance` (the suggested
   `Relation.reflexive_reflGen` lemma is deprecated).
5. **Registered `FrameRules.lean`** in `Cslib.lean` via `lake exe mk_all --module` (this also
   picked up a pending registration gap for `CS4.lean`/`CS5.lean` left by the concurrent
   task-501 session).
6. **Investigated** what remains for `Decidable (tValid φ)` and determined it requires a
   from-scratch T-specific tableau driver (`modalStepBranchT`/`modalExpandBranchesT`/
   `modalTableauT`) plus a K-scale termination re-derivation (`FmpMeasure.lean` is 2,959 lines
   for K alone) — see the plan file's Phase 2 `BLOCKER` section for full detail.
7. **Marked Phase 2 `[BLOCKED]`** in the plan file with task-level `[x]`/`[ ]` deviation
   annotations and a full blocker writeup.
8. **Ran the full CSLib CI pipeline** — all green (`lake build`, `lake exe checkInitImports`,
   `lake lint` — 2 pre-existing errors unrelated to task 300's files, `lake exe lint-style`,
   `lake shake` — no suggestions for task 300's files, `lake test` — exit 0).
9. Did **not** attempt Phases 3–7 (S5, B, S4, 5): each would hit the same root-cause blocker
   (needing its own K-scale driver + termination proof), likely at greater cost given their
   higher risk ratings in the plan.

## Current State (Committed, Green)

- `Cslib/Logics/Modal/Tableau/FrameRules.lean` (new, 113 lines): `modalTBoxSelf`,
  `modalTDiaNegSelf`, `modalApplyOneT`, `modalApplyOneT_eq_of_not_boxPos_diaNeg`. Sorry-free.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (233 lines): Phase 1 scaffolding
  (`FrameCondition`, `trivialFC`, `frameValid`, `branchSatisfiableIn`,
  `modalTableau_sound_frame`) plus Phase 2 T additions (`reflFC`, `tValid`,
  `branchSatisfiableIn_reflFC_boxPos_mem`/`_diaNeg_mem`, `modalTBoxSelf_sound`/
  `modalTDiaNegSelf_sound`). Sorry-free.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (135 lines): Phase 1's
  `extractModelWith`/`extractModelWith_id` plus Phase 2's `extractModelT`/`extractModelT_r`/
  `extractModelT_refl`/`extractModelT_hasEdge_imp_r`. Sorry-free.
- `Cslib.lean`: registers `FrameRules.lean` (and, incidentally, `CS4.lean`/`CS5.lean` from the
  concurrent task 501).

**Not yet started**: `S5Simplification.lean`, `LoopChecking.lean` (Phases 3–7).

## What Is Needed to Continue

**Recommended**: split "T-frame tableau completeness + decidability" (the remainder of
Phase 2) into its own dedicated task, separate from the five-system umbrella task. The same
driver-rebuild cost will recur — likely worse — for Phases 3 (S5), 4 (B), 5–6 (S4), 7 (5), so
each should probably become its own dedicated task too, rather than sub-phases of one
five-system task. See the plan file's Phase 2 `BLOCKER` section for the precise technical
detail on why a lightweight generalization of the existing K driver is not sound (transitive
diamond-rule world-minting triggered by T self-propagation).

If continuing Phase 2 directly: the next step is building `modalStepBranchT` (a copy of
`Saturation.lean`'s `modalStepBranch` with `modalApplyOne` replaced by `modalApplyOneT`), then
`modalExpandBranchesT`/`modalTableauT`, then re-deriving fuel-sufficiency/termination
(`FmpMeasure.lean`-style) for the new rule. Reuse
`modalApplyOneT_eq_of_not_boxPos_diaNeg` (already proved) to reduce most of the new truth
lemma's cases to the existing K bridge lemmas (`hintikka_box_pos`, `hintikka_diamond_pos`,
etc.) — only the box-positive case needs genuinely new reasoning (the reflexive self-edge).
