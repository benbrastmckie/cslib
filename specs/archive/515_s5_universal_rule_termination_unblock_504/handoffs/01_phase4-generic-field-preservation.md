# Handoff: Task 515 Phase 4 (Generic-Field Preservation) -- In Progress

**Date**: 2026-07-15
**Session**: sess_1784103256_616c12
**Status**: Phase 3 COMPLETED (commit `4f41f3a4`); Phase 4 IN PROGRESS, 1/6 fields landed (commit `12f32499`)

## What landed this dispatch

### Phase 3 (COMPLETED, commit `4f41f3a4`)

The crux fix. `Cslib/Logics/Modal/Tableau/S5Simplification.lean`:

- `blockingWorldS5Keyed φ₀ keys b s φ w : Option WorldIndex` -- the keys-aware guard, searching
  the threaded `keys` list for a stored `(w', k)` with `k = successorBirthContentS5 φ₀ b s φ w`,
  rather than comparing against live relevant sets (the v1 `blockingWorldS5` design, which task
  511's S4 development proved insufficient for `keysDistinct`).
- `blockingWorldS5Keyed_eq_birthContent` / `blockingWorldS5Keyed_none_fresh` -- the guard's two
  contract lemmas. `_none_fresh` is the birth-key invariant that makes `keysDistinct` a genuine
  per-step invariant (Phase 5's crux consumer).
- `S5LoopInv` extended from 4 to **11** fields (ten mirroring `S4LoopInv` exactly, plus
  `keysKnown` -- a necessary addition, see "Design notes" below).
- `modalStepBranchS5gKeyed` redesigned to compute the block/mint decision itself via the keyed
  guard, bypassing `modalApplyOneS5g`'s live-set dispatch on the two minting shapes entirely.
  `modalApplyOneS5g` and its Phase 2 agreement lemmas are untouched, valid reference artifacts.

Full CI green at this commit (lake build 3236/3236, checkInitImports, lint-style, lake lint,
lake test, shake). Zero sorry, zero new axioms.

### Phase 4 (IN PROGRESS, commit `12f32499`, 1 of 6 fields)

`modalStepBranchS5g_preserves_eNodup` landed sorry-free. Proved by **direct case analysis** on
`modalStepBranchS5gKeyed`'s own three-way `split`, NOT via the existing generic `_gen` wrappers
in `FmpMeasure.lean` (`modalStepBranch_preserves_accTargetsKnown_gen`,
`modalStepBranch_knownWorlds_gen`, etc.) -- **this is the key methodological finding of this
dispatch**, documented below.

Also landed (reusable infrastructure for the remaining five fields):
- `hasEdge_addEdge_cases_S5` -- local re-derivation of edge-membership-in-addEdge decomposition
  (mirrors `BDriver.lean`'s `hasEdge_addEdge_cases_B`).
- `modalStepBranchS5gKeyed_expanded_shape` (private) -- characterizes every child expanded set
  produced by a step as either `e ++ [sf]` or `e` unchanged. The proof template for this lemma
  is the reusable pattern for the remaining fields (see "Proof template" below).

## Why the existing generic `_gen` lemmas do NOT apply (the central finding)

`FmpMeasure.lean`'s generic wrappers (`modalStepBranch_preserves_accTargetsKnown_gen`,
`modalStepBranch_knownWorlds_gen`, `modalStepBranch_preserves_outDegEq_gen`, etc.) all take a raw
`hFreshLocal`-style hypothesis:

```
∀ sf b acc, (apply sf b acc).snd = acc
  ∨ ∃ wsf rest, (apply sf b acc).fst = .linear (wsf :: rest)
      ∧ (apply sf b acc).snd = acc.addEdge sf.label wsf.label
```

i.e. "acc unchanged, OR exactly one edge added to a *genuinely fresh* witness world headed by a
`.linear` result." This is true of K's `modalApplyOne` (`modalApplyOne_fresh_local`) and of every
prior loop-checking design in this codebase -- **except** the keys-aware guard's *blocked*
(loop-back) case, which adds an edge to an **existing, non-fresh** known world `wBlock` while
producing `.linear []` (not headed by a fresh witness at all). This fits **neither** disjunct of
`hFreshLocal`. Task 511's S4 development hit the identical wall (hence its Phase 5 block).

**Consequence**: all six Phase 4 lemmas (and the Phase 5 birth-key lemmas) must be proved by
*direct* case analysis on `modalStepBranchS5gKeyed`'s own dispatch, reusing K's *per-call*
lemmas (`modalApplyOne_knownWorlds_step`, `modalApplyOne_boxNeg_witness`,
`modalApplyOne_diamondPos_witness`, `modalApplyOne_fresh_local`) directly on the sub-cases where
the keyed stepper provably reduces to K (every case except the blocked/loop-back case), rather
than routing through the generic `_gen` machinery at all. This is real, own-terms proof
engineering -- there is no shortcut through the existing generic interface for this rule shape.

## The reusable proof template

`split at hsf` on `modalStepBranchS5gKeyed`'s unfolded body gives **exactly 3** top-level cases
(not 14 -- Lean's match compiler respects the 3 written arms: `.neg,.box`, `.pos,.diamond`,
wildcard), confirmed via `lean_goal`/`lean_multi_attempt`. Each of those further splits (via
`repeat' split at hsf`) into the guard result and/or the `RuleResult` shape, bottoming out at
**14 leaf goals** total (2 blocked + 2×4 mint-shape-dispatch + 4 non-minting-shape-dispatch).

The working, CI-verified tactic skeleton (see `modalStepBranchS5gKeyed_expanded_shape`'s proof,
`S5Simplification.lean` around line 733) is:

```lean
unfold modalStepBranchS5gKeyed at hstep
obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
clear hstep
by_cases hexp : e.any (· == sf) = true
· simp only [hexp, if_true] at hsf
  exact absurd hsf (by simp)
· rw [if_neg (by simpa using hexp)] at hsf
  refine ⟨sf, hsfmem, by simpa using hexp, ?_⟩
  clear hsfmem hexp
  split at hsf <;> repeat' split at hsf
  all_goals try injection hsf
  all_goals
    (rename_i hsf
     -- hsf is now the unwrapped tuple equality for each of the 14 leaf cases;
     -- 3 leaf shapes: some ([X],[e++[sf]],acc',keys')=some(...) [linear/blocked-like],
     -- some (branches.map(·++b), branches.map(fun _=>e++[sf]), acc', keys')=some(...) [branching],
     -- some ([X],[e],acc',keys')=some(...) [persistent-like].
     simp only [Prod.mk.injEq] at hsf
     ...)
```

Key gotchas discovered (document these to avoid re-deriving):
1. `first | (exact absurd hsf (by simp)) | ...` does **NOT** safely fail-and-backtrack on the
   valid (non-contradiction) goals -- a nested `by` term that doesn't fully close its own goal
   raises a hard elaboration error, not a catchable tactic failure. Use `try injection hsf`
   instead: `injection` cleanly auto-closes the 3 `none = some (...)` goals with zero new
   hypotheses, and cleanly succeeds (introducing one new hypothesis, anonymously named) on the
   11 valid goals -- proper tactic-level success/failure semantics throughout.
2. Do NOT pass `with hsf` to the `injection` inside a `try`/`all_goals` combo across
   heterogeneous goals (some closed, some not) -- the closed goals have nothing to name, causing
   "too many identifiers" if a fixed name is forced uniformly. Use bare `injection hsf`, then
   `rename_i hsf` on the (fewer) surviving goals to recover the name.
3. `clear hstep` / `clear hsfmem hexp` before the big case split keeps `lean_goal`/error output
   readable -- the raw `hstep` hypothesis pretty-prints the *entire* `modalStepBranchS5gKeyed`
   definition body (very large) at every one of the 14 leaf goals otherwise.
4. `List.nodup_append`'s disjointness component is `∀ a ∈ l1, ∀ y ∈ l2, a ≠ y` (two bound
   variables, not one) -- do not name the second bound variable `heq` expecting it to be an
   equality proof; it is a list *element*.

## Remaining Phase 4 fields (NOT YET STARTED this dispatch)

- `modalStepBranchS5g_preserves_accFresh` -- **assessed tractable**. Blocked case: new edge
  `sf.label → wBlock`; `wBlock` known via `blockingWorldS5Keyed_eq_birthContent` +
  `S5LoopInv.keysKnown` (the added 11th field), `sf.label` known trivially (`sf ∈ b`); both
  `< modalNextWorld b` via `modalNextWorld_gt` + `mem_modalKnownWorlds_S5`. Mint case: new edge
  target is `modalNextWorld b`, `< modalNextWorld (newForms ++ b)` since the branch grows by a
  formula *at* that exact label (needs a `modalNextWorld` branch-growth monotonicity fact --
  check whether `FmpMeasure.lean`/`BDriver.lean` already has one, else derive from
  `modalMaxWorld_append_single`-style reasoning at `LoopChecking.lean`). Non-minting case: `acc`
  provably unchanged (only K's `boxNeg`/`diamondPos` shapes mint, both excluded from this branch
  by construction) -- reuses `hasEdge_addEdge_cases_S5`.
- `modalStepBranchS5g_preserves_accKnown` -- same case shape as `accFresh`; reuses
  `S5LoopInv.keysKnown` for the blocked case, K's own `modalApplyOne_knownWorlds_step` for the
  mint case (once agreement with K is established on minting shapes via
  `modalApplyOneS5_eq_of_not_boxPos_diaNeg`), and `modalKnownWorlds_mono_append_S5` for the
  non-minting case.
- `modalStepBranchS5g_preserves_outDegEq` -- rule-agnostic bookkeeping; likely reuses
  `modalApplyOne_outDeg_step` (K's per-call lemma) on the agreement cases.
- `modalStepBranchS5g_preserves_bClosure` / `_preserves_eClosure` -- **flagged as the hard
  core**. The mint case's new formula sits at `modalNextWorld b`, a genuinely new label; showing
  `modalNextWorld b ≤ modalWorldBoundS5 φ₀` (needed for `modalUniverseS5` membership) requires
  the SAME cardinality/pigeonhole argument Phase 6 states as its headline result
  (`modalKnownWorlds_length_le_worldBoundS5`), fed by the PRE-state's `keysDistinct` +
  `keysInUniverse` + `keysTotal` (all available as `S5LoopInv` hypotheses on the pre-step
  branch). This is a genuine logical entanglement between Phase 4 and Phase 6, not an error --
  Lean does not enforce the plan's narrative phase ordering, so the pigeonhole cardinality
  lemma can (and likely must) be proved as a private helper consumed by Phase 4's `bClosure`,
  then re-exposed as Phase 6's public lemma. **Recommend**: prove the cardinality bound FIRST
  (as a standalone static fact about any `(b, keys)` satisfying `S5LoopInv`'s four birth-key
  fields, no step-preservation reasoning needed), then use it inside `bClosure`/`eClosure`'s
  mint-case proof obligations.

## Phase 5/6/7/8/9

Not started this dispatch. Phase 5 (birth-key preservation) is gated on Phase 4 completing;
`_preserves_keysDistinct` should now be the *easy* part (directly discharged by
`blockingWorldS5Keyed_none_fresh`, landed in Phase 3) -- the hard parts of Phase 5
(`keysTotal`/`keysInUniverse` preservation) share the same case-analysis + pigeonhole-adjacent
reasoning as Phase 4's `bClosure`. Phase 6 (pigeonhole) should fall out directly once the
cardinality helper above is proved. Phase 7 (soundness bridge, `FrameSoundness.lean`) is
independent of the termination chain and was not attempted this dispatch -- it forks off Phase 1
and does not require Phase 3-6 to be complete. Phase 8/9 (Hintikka lift, decidability,
5/KB5 completeness) are explicitly flagged in the plan as the highest-risk frontier and were not
attempted.

## Design notes: the `keysKnown` deviation (Phase 3)

`S5LoopInv` was extended with an 11th field beyond the plan's stated ten:

```lean
keysKnown : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b
```

This is the converse of `keysTotal` (`∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys`). It is
needed because `blockingWorldS5Keyed` filters over the threaded `keys` list directly, not over
`modalKnownWorlds b` -- so unlike the v1 live-set guard `blockingWorldS5` (which got "the
returned world is known" for free via `blockingWorldS5_mem_modalKnownWorlds`, a corollary of
filtering over `modalKnownWorlds b`), the keyed guard's blocked-case target `wBlock` needs this
as an explicit invariant to discharge `accKnown`/`accFresh` preservation at a loop-back step.
Documented inline in `S5LoopInv.keysKnown`'s docstring.

## Verification status at handoff

- `lake build` (full project): 3236/3236 green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint`: 0 new warnings (1 pre-existing unrelated `unusedArguments` error in
  `PrimeExclusion.lean`, predates this task).
- `lake test`: `CslibTests` suite green.
- `lake shake`: clean on touched files.
- `grep sorry` / `grep '^axiom '` on `S5Simplification.lean`: 0 / 0.

Commits: `4f41f3a4` (Phase 3), `12f32499` (Phase 4 partial).
