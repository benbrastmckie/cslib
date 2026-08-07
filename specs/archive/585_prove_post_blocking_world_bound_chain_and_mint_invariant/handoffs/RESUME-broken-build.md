# RESUME NOTE — broken build, uncommitted

**Written by an orchestration run that was interrupted by repeated API failures.**
Read this before dispatching any further work on this task.

## Current state (verified directly, not self-reported)

| Fact | Value |
|------|-------|
| `lake build` | **RED — 25 errors** in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` |
| Working tree | `Scheme.lean` **+349/-10, UNCOMMITTED** |
| Plan phases | **6/11 COMPLETED** — Phase 7 was NOT closed |
| Sorry census | Tableau subtree **4**, repo-wide **6** — baseline intact, no new sorries |
| DP-2 sorry | Still present at `Scheme.lean:3495` |

Nothing was committed, so `git diff` is exactly the interrupted work.

## What happened

A dispatch began Phase 7's deferred wiring — threading `IAllWorldHist` / `IAllWorldHistCounter`
into `intExpandBranches_openBranch_sat`'s signature and key induction statement — and **died
mid-edit on an API error**. The signature was changed but not all recursive call sites and cases
were updated to match.

Its own `.return-meta.json` was left at `status: in_progress` / `stage: initializing`, so the
dispatch's account of its work is lost. Everything in the table above was re-established from
`git diff`, a plan-heading count, `lean-sorry-census.sh`, and a real `lake build` — not from any
agent's summary.

## Build errors: three real clusters plus downstream noise

1. **`IAllWorldHist` argument threading** — `Scheme.lean:6054`, `:6569` (both "Application type
   mismatch"). At `:6054` a recursive `ih (doneAug ++ [augH] ++ augT) []` call passes something
   where `IAllWorldHist φ0 (done ++ [...] ++ bt) (doneExp ++ [newExp] ++ eT) (doneNW ++ [nw'] ++ nwT) (doneEdges ++ [edgesH] ++ edgesT)`
   is expected. At `:6569` the top-level call passes `fun b' hb' ψ w hmem hcontra => ?m` where
   `IAllWorldHist φ ?m ?m ?m ?m` is expected — the new parameter was inserted into the signature
   but at least one call site still supplies the OLD argument list, shifting arguments by one.
2. **Unknown identifier `nwH`** — `:3393`, `:3394` (x3), `:3402`, `:3407`, `:3417`, plus
   `unsolved goals` at `:3402`. See the hypothesis below — this is probably NOT a naming problem.
3. **`IWorldHist_mono`** (new, `:3150`–`:3155`) — "does not use the following hypothesis in its
   type"; "automatically included section variable(s) unused". Also `rewrite` failed at `:3094`,
   unused simp argument at `:3339`.
4. **Downstream noise** — `simp made no progress` at `:3390`, `:3410`, `:3418`, `:6063`, `:6234`,
   `:6355`, `:6466`, `:6558`–`:6570`. Expected to largely clear once 1–3 are fixed. Do not chase
   these first.

## Leading hypothesis for cluster 2 (unverified — treat as a lead, not a finding)

`nwH` **is** correctly bound: `IWorldHist_mint`'s implicit binders at `Scheme.lean:3297`
(`{nwH l : Nat}`). It resolves fine at `:3339`/`:3341` and is only reported unknown from `:3393`
onward. A binder in scope at 3341 and unknown at 3393 is not a naming failure.

`IWorldHist` gained the `(H1-acc)` clause in Phase 6 — **one extra field**. The `refine ⟨…⟩` at
`:3360`–`:3363` supplies four witness functions, and the following `·` bullets discharge the
remaining goals. If that constructor arity and bullet structure were not updated for the extra
field, the goals misalign and cascade into bogus name-resolution errors plus much of the
`simp made no progress` tail.

**If this holds, clusters 2 and 4 are largely ONE structural fix at the `refine`, not eight
independent proof failures.** Verify before acting on it.

## Backups — reverting is safe and reversible

`.recovery/` (gitignored via a self-ignoring `.gitignore`, so a `task_dir/`-scoped commit cannot
sweep it into history):

- `.recovery/Scheme.lean.partial-wiring-backup` — full file as left by the dead dispatch
- `.recovery/585-partial-wiring.patch` — `git diff` of the partial wiring (~486 lines)

The 349 lines cannot be lost, so **reverting `Scheme.lean` to HEAD is a cheap, reversible
fallback**, not a destructive decision.

## Recommended next dispatch

Goal is a **GREEN BUILD, not Phase 7 completion**. Choose explicitly and on the evidence:

- **(A) Finish the wiring coherently** — update every recursive call site and all ten
  `intExpandBranches.go.induct` cases to match the new signature. Preferred if the signature
  change is sound and the remainder is mechanical.
- **(B) Back the signature change out cleanly** — restore `intExpandBranches_openBranch_sat`'s
  original signature, keep Phase 6's standalone additive declarations (which were green and
  sorry-free), and leave the wiring to a later dispatch with a proper plan.

Prefer (A) if achievable; **fall back to (B) rather than ending on a red build.** A clean (B)
beats a broken (A). Do not leave a third state where the signature is half-migrated.

Hard constraints: no new `sorry` and no silencing errors with `sorry` (verify with
`bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Propositional/Tableau/` — must still
report exactly 4, DP-2 at `:3495` untouched); do not weaken or vacuously restate any existing
lemma to dodge an error; do not delete a failing lemma to make the build pass; only mark a plan
phase `[COMPLETED]` if actually finished (6/11 is the honest count if only the build is repaired).

Serialize against `specs/430_prove_atom_persistence_upward_closure_for_intexpan/` — both edit
`Scheme.lean`.

**Write the terminal `.return-meta.json` and `.orchestrator-handoff.json` EARLY and update as you
go.** Three dispatches were lost to API errors holding unwritten accounts of their own work.

## Loop-guard accounting

`.orchestrator-loop-guard` carries `cycle_count: 1/5`, `infra_failures: 2/3`.

Only one dispatch did real work (charged as cycle 1). Two later dispatches died with zero
footprint — no `.return-meta.json` write, no file edits — and were charged to `infra_failures`
rather than the work budget, per
`.claude/context/patterns/infra-failure-discrimination.md`.

The API failures were **529 Overloaded / 500 capacity errors, unrelated to this task's
difficulty**. If resuming after a gap, resetting `infra_failures` to 0 is defensible — the
counter exists to bound a connectivity problem within one sitting, not to penalize the task.
The work budget (`cycle_count`) is barely touched and should be left as-is.
