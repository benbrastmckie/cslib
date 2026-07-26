# Teammate C (Critic) Findings — Task 317 Adversarial Audit

## Key Findings

1. **The "assembly only" premise is new, not a repeat of a prior false belief.** Plan v6
   (`plans/06_route-a-frame-plumbing.md`) reached Phase 9 `[BLOCKED]` and Phase 10 `[BLOCKED]`
   on exactly Gap 2 (determinacy) and Gap 1 (fuel sufficiency). Those blockers were real and were
   NOT closed by any "assembly" dispatch — they were closed by (a) a *different* task, 552
   ("shared calculus-conformance and rule-completeness repair", status `completed`), which added
   a genuine branching tableau rule (Gap 2), and (b) a task-317 Phase 10 dispatch that proved a
   real new termination lemma, `applyPersistenceFixpoint_genuine_of_count_le_fuel` (Gap 1). So
   the current "assembly only" claim is not the same claim that failed before — the two hard
   mathematical blockers plan v6 exposed are supported by newly-landed, non-trivial artifacts,
   not merely re-asserted. This is a materially different, better-supported situation than any
   prior plan version's optimism.

2. **The two contradictory docstrings are NOT a coin-flip — they are ordered in time, and the
   later one is authoritative.** `git blame` shows the "Gap 2 RESOLVED" docstring
   (`Scheme.lean:488`) was written in commit `db48c4c2` (2026-07-24 23:51:45, task 552), which is
   *chronologically after* the "Gap 2 investigation: determinacy remains BLOCKED" docstring
   (`Scheme.lean:3001`, commit `a0a16c4b`, 2026-07-24 08:26:34, task 317 phase 10). The later
   commit is precisely the one that landed the new `.pos, .imp` branching arm the earlier block
   says doesn't exist. The stale-docstring diagnosis in the task description is correct in
   direction: `Scheme.lean:3001-3022` is the outdated block and should be corrected/deleted, not
   `Scheme.lean:488-500`/`580-582`.

3. **A closer mathematical re-derivation suggests the block at `Scheme.lean:3001-3022` may be
   flatly wrong about what's needed, not merely stale.** That block claims the T-imp case needs
   the *converse* direction of the induction hypothesis (`IForces w' φ' → T(φ')@w' ∈ b`) to
   "invoke the genuine-fixpoint fact," and that this converse is unavailable. But the actual
   proof obligation (`T(φ'→ψ')@w ∈ b`, `w'` accessible, `IForces w' φ'` ⊢ `IForces w' ψ'`) closes
   with only the *forward* IH directions already available: assume the copy propagates to `w'`
   (Gap 1's fixpoint lemma), get the disjunction `F(φ')@w' ∈ b ∨ T(ψ')@w' ∈ b` (the new `sat_timp`,
   directly witnessed by the branching rule per `sfSatisfied`'s already-landed `.pos, .imp` case,
   `Scheme.lean:765-771`), then case-split: `F(φ')@w' ∈ b` contradicts the *given* `IForces w' φ'`
   via the **contrapositive** of `ih_φ'`'s F-direction (`F(φ)@w ∈ b → ¬IForces w φ`, already in
   the induction's stated type, `Scheme.lean:561-564`) — no converse needed; otherwise
   `T(ψ')@w' ∈ b` closes directly via `ih_ψ'`'s T-direction. I could not run `lake build` to
   confirm this in Lean (constraint: no build access), so this is a **plausible but unverified**
   resolution, not a certified one — flag it to the planner as the first thing to attempt, since
   if correct it removes essentially all of the mathematical risk task 317's description assigns
   to closing the T-imp case, and if it fails, the specific way it fails is exactly the
   information a plan needs.

4. **A live, concrete territory collision exists and the task description's own risk section
   never surfaces it.** `Scheme.lean` (line 10) `import`s
   `Cslib.Foundations.Logic.Tableau.Measure` and *uses* `sum_map_le_length_mul` from it
   (Phase 6 of plan v6). Task 557 ("Refactor and restructure the modal Tableau subsystem...
   identifying the correct abstractions and module divisions, archiving unnecessary code to a
   new Boneyard/") is currently `[IMPLEMENTING]` with a live `.lock` (`session_id
   sess_1785105096_50f3c7`, orchestrate, acquired 2026-07-26T22:31:36Z) and explicitly aims to
   restructure shared tableau abstractions. If 557 moves, splits, or archives
   `Cslib/Foundations/Logic/Tableau/Measure.lean` (or renames `sum_map_le_length_mul`), task
   317's Scheme.lean build breaks on the next full build even though 317 never writes to that
   file. Task 553 (S4 loop guard) also holds a live `.lock`. See Territory Risk section below.

## Claim Audit

| Claim (from task description) | Verdict | Evidence |
|---|---|---|
| Gap 2 (determinacy) is RESOLVED via `.pos, .imp` branching arm at `Rules.lean:274-275` | **CONFIRMED** (as landed code + newer docstring), proof-closure implication **UNVERIFIABLE** without a build | `Rules.lean:266-268` has the `\| .pos, .imp φ ψ => .branchingResult [[⟨.neg, φ, l⟩], [⟨.pos, ψ, l⟩]] nextWorld`; `Scheme.lean:488-500` (commit `db48c4c2`, task 552, `completed`) asserts resolution; `sfSatisfied`'s `.pos, .imp` clause (`Scheme.lean:765-771`) already states the exact same-label disjunction. Line numbers in the description (274-275) are off by ~8 from HEAD (266-268 today) — cosmetic drift, not a substantive error. |
| Gap 1 (fuel sufficiency) is RESOLVED, `applyPersistenceFixpoint_genuine_of_count_le_fuel` sorry-free at `Scheme.lean:2907` | **CONFIRMED** | Read the full lemma body (`Scheme.lean:2907-2999`); no `sorry`/`axiom`. Its two callees, `applyAllTImpRules_subset` (`:2204`) and `applyAllTImpRules_count_drop` (`:2831`), were also inspected — no sorries in this file at those lines (the file's only `sorry`s are at `:592` and `:1498`, both unrelated to this call chain). Transitive dependency chain to `intUniverse_length_le` also has no sorry in-file. |
| `Scheme.lean:581` (Gap 2 resolved) and the block at `~3000` ("determinacy remains BLOCKED") conflict, and the ~3000 block is stale | **CONFIRMED (direction), verdict is the ~3000 block is stale** | `git blame`: line 488 is commit `db48c4c2` @ 2026-07-24 23:51:45 (task 552); line 3001 is commit `a0a16c4b` @ 2026-07-24 08:26:34 (task 317 phase 10) — i.e. **15 hours earlier**. The later commit is the one that added the branching rule the earlier block says is missing. See Finding 3 above for why the ~3000 block's specific technical argument (needing "the converse") may also just be mistaken, independent of staleness. |
| Remaining scope is exactly 4 items (sat_timp add+discharge, T-imp `:592`, fuel=0 base case `:1498`, two IValid/MValid bridges) | **CONFIRMED — exact sorry-count match** | `grep -n sorry` over `Scheme.lean`/`Completeness.lean`/`Minimal/Completeness.lean` returns exactly 4 tactic-level sorries: `Scheme.lean:592`, `Scheme.lean:1498`, `Completeness.lean:133`, `Minimal/Completeness.lean:125`. No other file in the Intuitionistic/Minimal tree has a `sorry`. `sat_timp` field does not yet exist on `IBranchSaturation` (confirmed by reading the struct, `Scheme.lean:74-99`) — consistent with "add" being real, additive work, not already-done. |
| `sat_timp` has exactly ONE construction site (`IExpandedConsistent_sat`) | **CONFIRMED** | `IBranchSaturation` is only ever produced by `IExpandedConsistent_sat` (`Scheme.lean:899-975`); the other candidate producer, `intExpandBranches_openBranch_sat` (`:1492`), explicitly *delegates* to `IExpandedConsistent_sat`/`IExpandedAccessConsistent_sat` rather than constructing independently (confirmed by reading its `none`-branch docstring, `:1478-1480`). No other `IBranchSaturation`-returning declaration exists in the tree. |
| The 43-row `CslibTests/TableauConformance.lean` guard stays green and covers intuitionistic rows | **CONFIRMED, with a real gap** | File has 24 temporal-corpus rows + 19 propositional (`intuitionisticTableau`) rows = 43, matching the description exactly (own docstring at line 90-92 says "24 rows, all green"). However, the file contains **zero** `minimalTableau` rows — `grep -n "minimalTableau"` returns nothing. The regression guard does NOT cover the Minimal calculus at all, only Intuitionistic. Since task 317 also closes the Minimal side (`Minimal/Completeness.lean:125`), a regression there would go undetected by this guard. |
| Cslib/ bare-sorry count must go DOWN (measurable) | **PARTIALLY VERIFIABLE** | `grep -rn "sorry\b" Cslib --include=*.lean \| wc -l` = 159 across 37 files, but this raw count conflates actual `sorry` tactic uses with docstring/comment mentions of the word "sorry" (e.g. `Completeness.lean` has 4 comment-only hits and 1 real tactic use). A precise machine-checkable baseline needs a stricter pattern or `#print axioms`/`sorryAx` scan per declaration, not a bare grep. The planner should establish the exact baseline count (tactic-level only) before claiming a specific "must decrease by N." |

## Gaps and Blind Spots

- **Finding 3 (above) is the single highest-leverage unresolved question.** If the T-imp case
  closes with only forward-direction IH (no converse), Gap 2 is fully resolved and closing
  `Scheme.lean:592` is a matter of correctly stating and discharging `sat_timp` at
  `IExpandedConsistent_sat`. If it does NOT (i.e., if there is a real reason the forward-only
  argument fails that I am not seeing from static reading — e.g., an issue with *which* copy of
  `T(φ→ψ)` the branching rule fired on, or an ordering issue between when persistence ran and
  when a world was created), the plan needs a genuinely new argument and the "assembly only"
  framing is wrong. The plan should budget an explicit STOP-gate check here before committing to
  the rest of the sequencing.
- **`sat_timp`'s exact global statement is still a design choice, not settled by the code.** The
  per-step `sfSatisfied` clause is same-label/reflexive; the *global* `IBranchSaturation` field
  needs to quantify over all `w'` accessible from `w` (not just `w` itself), which requires
  composing the reflexive per-copy fact with Gap 1's genuine-fixpoint guarantee that every
  accessible world eventually gets its own copy. This composition is sketched in the docstrings
  but not yet written as Lean code anywhere — it is genuine (if modest) proof work, not pure
  "wiring."
- **The fuel=0 base case (`Scheme.lean:1498`) closure mechanism is asserted but not spelled out
  in the task description.** The description says "fuel is fully utilized" for closing this
  case but the actual argument (per the file's own docstring at `:1478`) is "fuel=0 ⟹
  measure=0 ⟹ branches=[] ⟹ `.openBranch` impossible" — this requires *reformulating*
  `intExpandBranches_openBranch_sat`'s signature to carry a `measure ≤ fuel` hypothesis (exactly
  what plan v6 Phase 10 scoped and left `[BLOCKED]`, pending Phase 9). This reformulation ripples
  into the two countermodel-lemma call sites. It is assembly-shaped, but not "trivial" — it is a
  signature change under a Postmortem-5-style constraint discipline, the same discipline plan v6
  spent real effort tracking.
- **No plan version yet reflects the post-552 world.** Plans 01-06 were all written against the
  pre-branching-rule design (or, for v6, against the belief that determinacy needed an entirely
  new calculus rule "out of scope for task 317"). A fresh plan should explicitly supersede v6's
  Phase 9/10 BLOCKED status rather than trying to resume it verbatim, since the blocking
  rationale in v6 (`Scheme.lean:3001-3022`'s own reasoning) is exactly what commit `db48c4c2`
  invalidated.

## Questions That Should Be Asked But Are Not

1. **Does the forward-only (no-converse) T-imp argument actually go through in Lean?** (Finding
   3.) This should be the FIRST thing attempted, ideally as a standalone spike before committing
   to a full phase sequence, because it determines whether the remaining work is genuinely
   assembly or whether a new mathematical gap will be discovered.
2. **Should the Minimal calculus get its own conformance-guard rows before/alongside this task?**
   The guard's blind spot for `minimalTableau` means task 317's Minimal-side changes
   (`Minimal/Completeness.lean:125`) have no executable regression protection. This isn't
   necessarily task 317's job to fix, but it should be named as a residual risk, not silently
   inherited.
3. **What exactly is the precise, tactic-level sorry count today (not the raw grep-159), and
   what is the exact expected count after this task (should be repo-wide N-4, or does closing
   `sat_timp` risk exposing a currently-hidden sorry inside a lemma this task's proof will now
   actually execute, e.g. inside `Foundations/Logic/Tableau/Measure.lean` or `FmpMeasure.lean`
   if reused)?** Nothing in the audited chain touches a sorried dependency, but this should be
   stated as a verified fact in the plan, not assumed.
4. **Is `Cslib/Foundations/Logic/Tableau/Measure.lean` safe from task 557's refactor for the
   duration of this task?** (Territory Risk below.) This needs either a coordination check with
   the 557 session or a plan-level read-only-dependency risk note; it is currently unmentioned in
   the task description's own scope/CI section.
5. **Does the new `sat_timp` field, once added to `IBranchSaturation`, force any change to
   `intRule_preserves_sat` (Soundness.lean, task 316/552 territory) or is it purely additive on
   the completeness side?** The task description frames `Soundness.lean` as out of scope
   entirely, and the `.pos, .imp` soundness case is reportedly already landed
   (`intRule_preserves_sat`, per commit `db48c4c2`), but this should be explicitly re-confirmed
   read-only before the plan locks in a "Soundness.lean untouched" constraint.

## Territory Risk

**Real, concrete collision surface**: `Cslib/Foundations/Logic/Tableau/Measure.lean`.

- Task 317's `Scheme.lean` imports it (`Scheme.lean:10`) and consumes
  `sum_map_le_length_mul` from it (landed in plan v6 Phase 6, "reuse for Phase 6-8"). Task 317
  does not need to (and per its description will not) *edit* this file.
- Task 557 ("modal Tableau subsystem... identifying the correct abstractions and module
  divisions, archiving unnecessary code to a new Boneyard/") is `[IMPLEMENTING]`, holds a live
  `.lock` (`specs/557_modal_tableau_refactor_abstractions_boneyard/.lock/holder.json`,
  session `sess_1785105096_50f3c7`, acquired 2026-07-26T22:31:36Z, still running as of this
  audit), and its own description centers on reorganizing exactly this class of shared tableau
  abstraction (branch/measure/closure primitives used by both Modal-K and the propositional
  tableaux). If 557 moves, renames, or archives `Measure.lean` or `sum_map_le_length_mul` as
  part of its "correct abstractions" pass, task 317's build breaks on next full `lake build`
  even though 317 never writes there.
- Task 553 ("S4 loop guard soundness reachability restriction") also holds a live `.lock`
  (`specs/553_s4_loop_guard_soundness_reachability_restriction/.lock/holder.json`) — its scope
  (S4 loop-guard soundness) is Modal-Tableau-specific and less likely to touch
  `Foundations/Logic/Tableau/`, but was not independently audited beyond confirming the lock
  exists.
- **Recommendation**: the plan should mark `Cslib/Foundations/Logic/Tableau/Measure.lean` as a
  read-only external dependency with an explicit pre-phase check (`git log -1 --
  Cslib/Foundations/Logic/Tableau/Measure.lean` compared against the SHA task 317 last verified
  against), and should not assume it is inert just because task 317 itself never edits it.

## Confidence Level

**Medium.** High confidence on the mechanically-checkable claims (sorry locations/count, commit
ordering via git blame, import graph, conformance-suite row counts, territory file identification)
— these are all directly grep/read-verified against HEAD. Medium-to-low confidence on Finding 3
(the forward-only T-imp closure argument) — this is a from-first-principles proof sketch I could
not verify in Lean under this dispatch's read-only constraint (no `lake build` access), so treat
it as a strong hypothesis for the planner to spike first, not a proven fact.
