# Task 364 — Soundness Drift Repair: BLOCKED (genuine soundness-proof gap)

## Outcome

**Status: BLOCKED.** The 3 build errors in
`modalExpandBranches_closed_unsat` (succ-case `key` fuel-induction,
`Soundness.lean:1744/1749/1770`) cannot be closed by a local proof repair. They
stem from a genuine gap in the soundness proof rooted in the *definitions*
(`modalStepBranch` / `modalExpandBranches` / `modalApplyOne`), not from drift.

`Soundness.lean` was reverted to its committed baseline (3 errors) to avoid
regressing the error profile. No `sorry`, no axioms, no vacuous definitions were
introduced.

## What I did (genuine effort)

1. Traced all relevant definitions: `modalStepBranch` (Saturation.lean),
   `modalApplyOne` (Rules.lean), `modalNextWorld`/`modalMaxWorld`/`accFreshInv`,
   `Accessibility.addEdge`/`hasEdge`, `branchSatisfiable`, `Satisfies`.
2. Relaxed, then **dropped**, the vestigial `hstep` hypothesis of
   `modalExpandBranches_closed_unsat`. Its `b ∈ branches` premise was unprovable,
   and the hypothesis as a whole is *unthreadable*: it is fixed to one `acc`,
   whereas the recursion changes `acc` to `newAcc`. I replaced it by inlining
   `modalStepBranch_preserves_sat` (which is universally quantified over `acc`).
3. Reformulated `key` to carry per-branch freshness
   `(hpInv : ∀ bp ∈ pending, accFreshInv bp acc)`.
4. This reduced the whole succ-case to **three** helper obligations on the new
   worklist `done ++ newBs ++ bt` at the shared post-step accumulator `newAcc`
   (build-confirmed: the only remaining errors were the four references to these
   three helpers).
5. Constructed and **build-verified** a Lean counterexample refuting one of them.

## The three obligations

| # | Obligation | Status |
|---|-----------|--------|
| 1 | `accFreshInv b' newAcc` for result branches `b' ∈ newBs` | **TRUE / provable** |
| 2 | `accFreshInv bp acc → accFreshInv bp newAcc` for carried sibling `bp` | **FALSE** |
| 3 | `branchSatisfiable bp acc → branchSatisfiable bp newAcc` for carried `bp` | **FALSE (build-verified)** |

## Root cause

`modalExpandBranches` threads a **single shared `acc`** through *all* branches in
the worklist, while `modalApplyOne` (diamondPos / boxNeg) numbers fresh worlds
**per-branch** as `w' = modalNextWorld b`. So an edge `(w, w')` created by one
branch's existential rule is visible to, and constrains, sibling branches that do
not contain that fresh world.

- A sibling `bp` produced by an earlier propositional `.branching` shares `b`'s
  labels, so `modalNextWorld bp = modalNextWorld b = w'`. Then
  `accFreshInv bp newAcc` would require `w' < modalNextWorld bp = w'` — false.
- `modalStepBranch_preserves_sat` *requires* per-branch `accFreshInv` of the
  expanded branch for its fresh-world witness construction; that precondition is
  false for any branch processed after a sibling created a fresh world.
- The only invariant maintainable through the recursion,
  `accFreshInv (branches.flatMap id) acc`, is strictly **weaker** and cannot
  supply the per-branch fact (`modalNextWorld bp ≤ modalNextWorld (flatMap …)`,
  the wrong direction).

## Build-verified counterexample

`specs/364_modal_tableau_soundness_drift_repair/handoffs/verified-counterexample.lean`
compiles, proving:

```
∃ bp src tgt,
  branchSatisfiable bp Accessibility.empty ∧
  ¬ branchSatisfiable bp (Accessibility.empty.addEdge src tgt)
```

with `bp = [T(□p)@0, T(□(p→⊥))@0]`: satisfiable at a dead-end world 0, but
unsatisfiable once world 0 gains a successor 1 (forcing both `p` and `¬p` there).
This is exactly the satisfiability-lifting obligation `key` needs for carried
worklist branches.

## What is needed (out of current scope)

A definitional change — not a 3-error fix:

- **(A)** Give each branch its own `Accessibility` relation (fresh worlds/edges
  become branch-local), eliminating cross-branch pollution. Changes
  `modalStepBranch` / `modalExpandBranches` signatures and behavior.
- **(B)** Thread a globally-monotone fresh-world counter so fresh indices never
  collide across branches.
- **(C)** Prove a much stronger global invariant coupling box-positive
  consistency across all worklist branches (major proof redesign).

## Recommended next action

Escalate the design decision (A vs. B) to the maintainer, then re-plan the
soundness proof against the revised definitions. Do **not** re-dispatch this as a
local proof repair.

## Plan Deviations

- The plan/task framed this as closing 3 errors via a freshness-maintenance
  lemma. Genuine effort showed the maintenance lemma is only one of three
  obligations, and the other two are false for carried branches — a real
  soundness-proof gap, not transcription drift. Per the task's explicit
  instruction, I stopped and wrote a precise, build-evidenced blocker instead of
  inventing an unsound shortcut.
