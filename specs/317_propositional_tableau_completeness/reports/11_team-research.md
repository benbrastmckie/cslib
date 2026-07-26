# Research Report: Task #317 — Propositional/Intuitionistic Tableau Completeness

**Task**: Fill the remaining propositional/intuitionistic tableau completeness sorries
**Date**: 2026-07-26
**Mode**: Team Research (4 teammates: Primary, Alternatives, Critic, Horizons)
**Session**: sess_1785106431_e662fa
**Status**: RESEARCHED

## Summary

The task description's four enumerated obligations are the right four — the bare-`sorry`
inventory matches exactly, with no hidden extras. Its two "resolved blocker" claims both hold up
under independent verification. But its framing that **"REMAINING SCOPE IS ASSEMBLY ONLY" is
wrong**, and wrong in a specific, locatable way: item (1) (`sat_timp`) is genuinely mechanical,
while items (2) and (3) bottom out in a measure/fuel invariant that is **not currently threaded**
through `intExpandBranches_openBranch_sat`, and item (4) very likely needs a further
upward-closure (atom-persistence) argument that the four-item list does not name at all.

Two teammates reached the "item (4) is under-scoped" conclusion independently and by different
routes (Primary from reading `intExtractValuation`'s monotonicity obligation; Horizons from the
overlap with the separately-tracked atom-persistence task). That convergence is the single most
important output of this dispatch.

The good news is equally concrete: the parametric mandate the description issues is **already
satisfied in the codebase** and needs no refactor budget, and the mathematical objection recorded
in the stale docstring is not merely outdated but technically wrong, which removes the largest
perceived risk from the T-imp case.

## Key Findings

### Verified baseline (all four teammates agree, independently re-checked during synthesis)

Exactly **4 bare tactic-level `sorry`s** exist in `Cslib/Logics/Propositional/Tableau/`:

| Location | Obligation |
|---|---|
| `Intuitionistic/Scheme.lean:592` | `truthLemma` T-imp case |
| `Intuitionistic/Scheme.lean:1498` | fuel=0 base case of `intExpandBranches_openBranch_sat` |
| `Intuitionistic/Completeness.lean:133` | `IValid` bridge |
| `Minimal/Completeness.lean:125` | `MValid` bridge |

All other `sorry` hits in that tree are prose/docstring mentions. This is a clean, measurable
baseline for the "count must go DOWN" acceptance criterion — but see Gaps for why the repo-wide
figure needs a stricter measurement than `grep`.

### Primary Approach (Teammate A)

The four obligations do not decompose the way the description's numbered list suggests. Items (2)
and (3) share a single missing prerequisite, and item (4) needs something the list never mentions.

- `sat_timp` as an `IBranchSaturation` field is genuinely cheap: a same-label disjunction
  dischargeable at `IExpandedConsistent_sat` (`Scheme.lean:904-974`) by the exact six-line pattern
  already used for `sat_tand`/`sat_fand`/`sat_tor`/`sat_for_`. No new machinery.
- `applyPersistenceFixpoint_genuine_of_count_le_fuel` (`Scheme.lean:2907`) is sorry-free but is
  **dead code** — never called. It is necessary but not sufficient: invoking it requires a
  universe-membership hypothesis (`∀ x ∈ b, x ∈ intUniverse φ0`) and a measure bound that
  `intExpandBranches_openBranch_sat` does not carry.
- The T-imp case additionally needs a *copy-completeness* fact: every world `w'` edge-accessible
  from `w` carries its own copy `T(φ→ψ)@w' ∈ b`. This and the fuel=0 base case are blocked on the
  same missing invariant.
- A further, **distinct** monotonicity gap likely blocks the two validity bridges:
  `intExtractValuation`'s upward-closure along `intAccessPreorder edges` needs an induction on
  formula complexity, documented as unresolved at `Scheme.lean:442-483`. This is not what "consume
  the genuine-fixpoint lemma" delivers.

### Alternative Approaches (Teammate B)

- **The parametric mandate is already satisfied.** `IntMinScheme` exists at `Scheme.lean:118`
  with instances `intScheme` (:159) and `minScheme` (:208); `truthLemma`, `openBranch_countermodel`
  and `tableau_complete` are already stated once against `S : IntMinScheme Atom`, and both
  `Completeness.lean` files are thin ~130-line corollaries. There is no copy-paste duplication to
  refactor. Read "rather than duplicating" as "keep it this way," not as new infrastructure work.
- **No Mathlib leverage exists.** Heyting algebras exist but connect to nothing Kripke- or
  tableau-shaped; there is no Mathlib formalization of intuitionistic Kripke semantics, tableau
  calculi, or fuel/fixpoint-sufficiency measures. Do not budget search time for a shortcut that
  is not there. The right reusable pieces (`Relation.ReflTransGen`, `intAccessPreorder`) are
  already in-repo and in use.
- A short bridging lemma (~20-40 lines) converts the fixpoint equality into
  membership-at-every-accessible-world, using the proof idiom already established by
  `applyAllTImpRules_copy_notMem` (:2777) and `intTImpRule_output_notMem` (:2806).
- Prior art for the disjunction-elimination step is in-repo: the classical `T(a→c)` branching case
  (`Classical/Completeness.lean:202-222`) and the modal `box` case
  (`Modal/Tableau/Completeness.lean:566-573`). Neither needs an IH converse.

### Gaps and Shortcomings (Teammate C, Critic)

- **The "assembly only" premise is NOT a repeat of a prior false belief.** Plan v6 reached
  Phase 9/10 `[BLOCKED]` on exactly Gap 2 and Gap 1, and those blockers were closed by real
  artifacts — Gap 2 by the completed shared conformance/rule-completeness repair, Gap 1 by a
  genuine new termination lemma. The current optimism rests on landed code, not re-assertion.
  This is a materially better-supported situation than any prior plan version.
- **The docstring contradiction is settled by `git blame`, not by judgment.** The "Gap 2 RESOLVED"
  text (`Scheme.lean:488`) was written 2026-07-24 23:51 — *fifteen hours after* the "determinacy
  remains BLOCKED" block (`Scheme.lean:3001`, 2026-07-24 08:26), by the very commit that landed
  the branching arm the earlier block says is missing. The `~3000` block is the stale one, exactly
  as the description claims.
- **The stale block is also technically wrong, not merely outdated.** It claims the T-imp case
  needs the *converse* of the induction hypothesis. It does not: the `F(φ')@w'` arm closes by
  contrapositive of the IH's already-available F-direction, the `T(ψ')@w'` arm by the T-direction.
  B and C reached this independently.
- **The regression guard does not cover the Minimal calculus.** The 43-row
  `CslibTests/TableauConformance.lean` has zero `minimalTableau` rows (verified during synthesis:
  `grep -c` returns 0). Since this task also closes `Minimal/Completeness.lean:125`, a regression
  on the Minimal side would go undetected by the guard the acceptance criteria rely on.
- **`sat_timp`'s exact statement is an open design choice**, not settled by the code — see
  Conflicts below.

### Strategic Horizons (Teammate D)

- Task 317 heads a four-task fan-out (375, 413, 430, 456). 375 needs exactly what item (4)
  promises and no more. 456 is correctly sequenced after, not folded in.
- **430 is substantially subsumed** by item (4) — its own falsification spike already concedes
  the fix is 317 territory and that it "re-runs after 317 as verify/re-gate." Recommend an
  explicit disposition once 317 lands rather than dispatching it as independent work.
- **413's dependency edge looks like sequencing hygiene, not a content need** — its target files
  (`ListImplication.lean`, `bigconj_*`) are outside 317's file scope. Decoupling it could unblock
  wave 3 sooner. Flagged low-confidence; the orchestrator should verify 413 never touches
  `Tableau/`.
- Report `10_wave-a-atomic-derisk.md` says the de-risk work "closes 0/4 sorries but reshapes 3-4
  to edge-frame Phase-10 goals" — language matching the atom-persistence problem, corroborating
  that item (4) is not trivial wiring.

## Synthesis

### Conflicts Resolved

**1. Is the T-imp case hard or easy? (A vs B/C) — resolved: both, at different layers.**

B and C are right that the *semantic* step is elementary: disjunction elimination with no IH
converse, matching established in-repo prior art. The stale docstring's objection is void.

A is right that the *input* to that step is not currently available. Verified directly during
synthesis: `intExpandBranches_openBranch_sat`'s signature carries `IAllConsistent` /
`IAllAccessConsistent` with **no** measure hypothesis and **no** `φ0` universe parameter; and
`intExpMeasure_step_lt` (:2521), `intExpMeasure_step_lt_branch` (:2589) and
`intExpMeasure_init_le_fuel` have **zero call sites** — every other occurrence is a prose
reference. The plumbing is genuinely absent.

These compose rather than compete: B's bridging lemma converts fixpoint-equality into
membership-at-accessible-worlds, but its `hfuel`/`hb` hypotheses are exactly what A's invariant
threading supplies. B's estimate is optimistic because it assumes the fixpoint equality is already
available at the returned branch; it is not. **Both pieces of work are required, in A's order.**

**2. What shape should `sat_timp` take? (A vs B) — a real design fork the plan must decide.**

A proposes a same-label/reflexive field (cheap, mechanical discharge, deferring the
accessible-world lift into `truthLemma`). B proposes quantifying over accessible worlds inside the
field (moving the lift into the discharge site, requiring the bridging lemma there). The lift work
is identical in total; only its location differs. **Recommendation: A's reflexive field**, keeping
the discharge purely mechanical and isolating the copy-completeness lemma as a separately
verifiable unit. This should be stated explicitly in the plan rather than discovered mid-dispatch.

**3. Territory: is there a collision with the concurrent modal-tableau work? (A/D vs C) — C is
right, and more precise.**

A and D correctly establish that *write* scopes are disjoint: this task touches only
`Propositional/Tableau/{Intuitionistic,Minimal}/`. C identifies the real exposure, which is a
*read* dependency: `Scheme.lean:10` imports `Cslib.Foundations.Logic.Tableau.Measure` and consumes
`sum_map_le_length_mul` at lines 2058 and 2068 (both verified during synthesis). The concurrent
refactor aims at reorganizing exactly this class of shared tableau abstraction. If it moves,
renames, or archives that file or lemma, this task's build breaks without this task ever writing
there. The plan should record `Foundations/Logic/Tableau/Measure.lean` as a pinned read-only
dependency with a pre-phase `git log -1` check.

**4. Line-number drift.** C reports the branching arm at `Rules.lean:266-268` and calls the
description's `274-275` stale. Direct check during synthesis confirms `| .pos, .imp φ ψ =>` is at
**line 274**; the description and A are correct here, and C's drift note should be disregarded.
Similarly the fuel lemma is cited variously at `:2907` and `:2912` — the declaration begins at
2907.

### Gaps Identified

1. **Item (4) is under-scoped, with two independent lines of evidence.** The four-item list does
   not name the upward-closure/atom-persistence obligation that both A (from
   `Scheme.lean:442-483`) and D (from the subsumed atom-persistence task's own spike) identify as
   probably required. Neither verified it against live Lean goal state. **This is the highest-value
   thing to settle before planning locks phase boundaries.**
2. **Neither the "no converse IH needed" argument (B/C) nor the fuel=0 zero-case measure argument
   (A) was verified in Lean.** Both are static-reading proof sketches. No teammate ran `lake build`
   (correctly — another session is active in this repo), and none reported using `lean_goal` at
   the sorry sites. A explicitly recommends a `lean_goal`-driven confirmation pass before exact
   lemma statements are fixed.
3. **The Minimal calculus has no executable regression protection.** Not necessarily this task's
   job to fix, but it must be named as residual risk rather than silently inherited.
4. **The repo-wide sorry baseline is not yet measurable.** `grep -rn "sorry" Cslib --include=*.lean`
   returns ~159 hits across 37 files, conflating tactic uses with prose. The plan needs a stricter
   pattern or a `#print axioms`/`sorryAx` scan before asserting "decreases by N."
5. **Whether adding a field to `IBranchSaturation` disturbs `Soundness.lean`** was not confirmed
   read-only, though the structure has exactly one construction site (`IExpandedConsistent_sat`,
   verified by C).

### Recommendations

**Do first, before any phase boundaries are fixed:** a short `lean_goal`-driven spike at
`Scheme.lean:592` and at the two bridge sorries, answering (a) does the forward-only
disjunction-elimination argument actually close the T-imp case, and (b) do the bridges need an
atom-persistence field beyond `sat_timp`. Both questions are cheap to answer with live goal state
and expensive to get wrong. If (b) comes back "yes," the task is a five- or six-phase job, not the
four-item assembly its description describes, and that should be said explicitly rather than
discovered in dispatch three.

**Phase sequence** (adapted from A, incorporating B's bridging lemma and C's gates):

1. `sat_timp` field + mechanical discharge at `IExpandedConsistent_sat`. Independent, cheap.
2. Measure/fuel invariant threading through `intExpandBranches_openBranch_sat` — add the `φ0`
   parameter, universe-membership invariant and measure bound; establish at the sole call site
   `openBranch_countermodel` (:1871) via `intExpMeasure_init_le_fuel`; maintain across the `succ`
   case via `intExpMeasure_step_lt`/`_branch`. **Largest phase; likely needs splitting into
   "invariant definition + call-site threading" and "succ-case maintenance + zero-case discharge."**
3. Copy-completeness bridging lemma (B's, ~20-40 lines, idiom already established at :2777/:2806),
   then close `truthLemma`'s T-imp case at :592.
4. Repair the stale docstring at `Scheme.lean:3001-3022`. Land with phase 3, not before — the
   block only becomes fully obsolete once the proof it denies exists.
5. Upward-closure/monotonicity lemma for `intExtractValuation` (and `minBranchBotForces` for the
   Minimal side) — pending the spike above; may need its own short research pass to pin the exact
   statement.
6. Both validity bridges as one lemma parametric in `S : IntMinScheme Atom`, instantiated at
   `intScheme` (where the `modelBot` obligation is vacuous) and `minScheme` (where it is real).

**Do not budget for**: a parametric refactor (already built), a new calculus rule (the stale
block's recommendation is wrong), or a Mathlib search for Kripke/persistence machinery (none
exists).

**Record as plan-level risks**: the pinned read-only dependency on
`Foundations/Logic/Tableau/Measure.lean`; the Minimal-side conformance blind spot; and the
disposition of the subsumed atom-persistence task once item (4) lands.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|---|---|---|---|
| A | Primary route, phase decomposition | completed | medium-high on code-verified claims; medium on phase/monotonicity analysis |
| B | Prior art, alternatives, Mathlib leverage | completed | high on parametric/Mathlib findings; medium-high on the bridging-lemma estimate |
| C | Critic, claim audit, territory | completed | medium (high on mechanical checks, medium-low on the T-imp closure sketch) |
| D | Horizons, downstream consumers | completed | medium (high on dependency graph, medium-low on item-4 difficulty) |

## References

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — `IntMinScheme` (:118),
  `intScheme` (:159), `minScheme` (:208), `truthLemma` (:555), T-imp sorry (:592),
  `IExpandedConsistent_sat` (:904), fuel=0 sorry (:1498), `intExpMeasure_step_lt` (:2521),
  `_branch` (:2589), `applyPersistenceFixpoint_genuine_of_count_le_fuel` (:2907),
  stale docstring block (:3001-3022), unresolved monotonicity STOP-gate (:442-483)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean:274-275` — `.pos, .imp` branching arm
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:133`,
  `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:125` — the two validity bridges
- `Cslib/Logics/Propositional/Semantics/Kripke.lean:145-168` — `IValid`/`MValid`/`mvalid_implies_ivalid`
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:202-222` — prior-art branching case
- `Cslib/Foundations/Logic/Tableau/Measure.lean` — `sum_map_le_length_mul` (read-only dependency)
- `CslibTests/TableauConformance.lean` — 43-row guard, zero Minimal rows
- Teammate findings: `11_teammate-a-findings.md`, `11_teammate-b-findings.md`,
  `11_teammate-c-findings.md`, `11_teammate-d-findings.md`
- Prior artifacts: `plans/06_route-a-frame-plumbing.md`, `reports/10_wave-a-atomic-derisk.md`
