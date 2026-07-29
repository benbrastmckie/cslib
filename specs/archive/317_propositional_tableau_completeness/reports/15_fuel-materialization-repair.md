# Research Report: Fuel-Materialization Repair for Plan-13 Phase 4

- **Task**: 317 - propositional_tableau_completeness (blocker research)
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Session**: sess_1785275816_a84520_317
- **Focus**: Adjudicate the three repair candidates for the Phase 4 blocker
  ("intFuel resize target cannot be materialized by #eval corpus") and produce a
  phase-4-replacement spec.
- **Inputs**: plans/13_fuel-sufficiency-skeleton.md (Phase 4 BLOCKER section),
  summaries/13_phase4-fuel-resize-blocked-summary.md, .orchestrator-handoff.json blocker
  entry; code at HEAD: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`,
  `.../Scheme.lean`, `.../Rules.lean`, `.../Soundness.lean`, `.../Completeness.lean`,
  `.../DecisionProcedure.lean`, `CslibTests/TableauConformance.lean`.
- **Reference grounding**: Tier 3 (implementation-backed; the blocker is an engineering
  property of the landed code). Tier 1 anchors carried through from the plan, BibKeys
  verified against `references.bib`: `Fitting1983` (references.bib:211),
  `GargGenoveseNegri2012` (references.bib:239), `Dyckhoff1992` (:218), `Massacci2000`
  (:1041). No new literature claims are introduced by this report.

## Executive Summary

**Recommended candidate: (a) — per-branch fuel restructuring of `intExpandBranches`**,
realized in the shape-preserving form (thread `fuels : List Nat` as a fourth parallel list
through the existing worklist engine; well-founded recursion on the unconditional measure
`(Σ 3^fuelᵢ, pending.length)` lex). Candidates (b) and (c) are NO-GO for structural reasons
established below: (b) puts the unproven DP-2 invariant on the critical path of the engine
*definition* (a `decreasing_by` obligation that cannot be sorried under zero-debt), and (c)
creates an equivalence obligation that is per-formula-empirical, not provable, and not even
kernel-checkable, while gutting what the conformance corpus certifies — reintroducing the
exact sorry-free-but-wrong-verdict hazard class the corpus was built to close.

Two corrections to the blocked dispatch's record, both established empirically here:
1. The handoff's claim "≤ ~4,700-digit numerals for all corpus rows" under candidate (a) is
   **false for row 20** (the divergence witness): its `s = 19`, `intChainBound = 9,961,472`,
   so its per-branch fuel is a ≈13.0-million-digit numeral (~43 Mbit ≈ 5.4 MB).
2. The corrected numeral is nonetheless **materializable in 599 ms** (probe below), so
   candidate (a)'s feasibility conclusion survives with a corrected bound and one new
   in-phase verification obligation (a `lake test` timing gate for row 20).

## Findings

### 1. Why the blocker is real and structural (verified at HEAD)

- `intuitionisticTableau` strictly binds the fuel numeral before any expansion:
  `let fuel := intFuel φ` at `Expansion.lean:522-525` (same for `minimalTableau`,
  `Expansion.lean:535-538`). Early exit bounds *consumption*, never *materialization* —
  confirmed by reading the definition; there is no laziness in compiled Lean `let`.
- The engine (`intExpandBranches`, `Expansion.lean:333-426`) decrements ONE global
  `fuel : Nat` once per expansion step, across all branches. The sufficiency architecture
  (Phase 3's measure engine) therefore requires
  `fuel ≥ intExpMeasure (intUniverseExt φ) [[⟨.neg,φ,0⟩]] [[]] = 3^(intWork …)` with
  `intWork ≤ 2·|intUniverseExt φ|` (`Scheme.lean:2407-2415`, `2164`), i.e. a
  `3^Θ(WBound φ)`-bit numeral — physically unmaterializable for `s ≥ 4` (19 of 20 rows).
- **No smaller global fuel can exist under any global-scalar design**: global fuel must
  bound *total* steps; total steps are bounded below by branch count, and branch count is
  worst-case exponential in per-branch beta firings, which scale with
  `|intUniverseExt φ| = Θ(WBound φ)`. So `2^Θ(WBound)` is a floor for any provable global
  bound — the repair must change the fuel *architecture*, not the constant. This closes the
  door on any "tighter resize" non-candidate.

### 2. Candidate (a): per-branch fuel — GO

**Sufficiency shrinks from `3^(2|U|)` to `2|U| + 1` per branch.** A single branch takes at
most `intWork U b e ≤ 2·|U|` steps, because every arm of one step strictly decreases the
per-branch work: `intWork_drop` (`Scheme.lean:2524-2531`, proved, arm-agnostic — its own
docstring already notes it covers ALPHA, world-creation, reuse (`b' = b`, `hsub` refl), and
each BETA sub-branch), with persistence handled by weak monotonicity `intCount_notMem_mono`
(`Scheme.lean:2500-2513`, proved). So a per-branch budget
`intFuelExt φ := 4·(2·φ.complexity + 1)·(WBound φ + 1) + 1
  ≥ 2·|intUniverseExt φ| + 1` (via `intUniverseExt_length_le`, `Scheme.lean:2164-2165`)
suffices for every branch, and children of a beta split each inherit `fuel - 1`.

**The heavy sum-measure engine becomes non-load-bearing.** The new route consumes ONLY
`intWork_drop` + `intCount_notMem_mono` + a trivial init bound. The re-targeted
`intExpMeasure_step_lt` (`Scheme.lean:2575`) and `intExpMeasure_step_lt_branch` (`:2647`)
do not mention `intExpandBranches` in their statements (checked: they quantify over
worklists and `intStepBranch` only), so they stay green as retained-but-unconsumed assets —
no regression, no rework.

**Termination is unconditional — no invariants in the definition.** Recursion on the lex
measure `((fuels.map (3 ^ ·)).sum, pending.length)`:
- skip-closed arm (`go` moving a closed branch to done): sum unchanged, pending shrinks;
- linear / world-creating / reuse arms: one branch's `f + 1` becomes `f`,
  `3^f < 3^(f+1)`;
- beta arm: `f + 1` becomes two children at `f`; all three `branchingResult` sites emit
  literal 2-element lists (`Rules.lean:259` T-and, `:262` F-or, `:280` T-imp split), so
  `2·3^f < 3^(f+1)` — pure arithmetic, `pow3` family already in
  `Cslib/Foundations/Logic/Tableau/Measure.lean` (used at `Scheme.lean:2614, 2743`).
Unlike candidate (b), NO branch-containment or world-bound hypothesis is needed to define
the function. `#eval` compiles WF recursion fine (the compiler ignores termination proofs);
the corpus's own header (`TableauConformance.lean:28-37`) already documents that kernel
reduction (`decide`/`rfl`) is unavailable for the *current* engine too, so nothing regresses
on that axis.

**Corpus verdicts are preserved a priori.** The fuel value influences behavior only through
the exhaustion arm; per-branch budgets are astronomically larger than actual step counts
(row 20 saturates within hundreds of steps per the divergence-witness table,
`Expansion.lean:462-468`), and the persistence call keeps its shape (active branch's
remaining fuel, mirroring today's `fuel' + 1` at `Expansion.lean:363`). The step sequence is
therefore identical to today's on every corpus row; `intVerdict` distinguishes only
CLOSED/OPEN. Verified empirically in-phase as a done-criterion regardless.

**Empirical materialization probe** (this dispatch, `lake env lean`, method of the blocked
dispatch; `fuelExt s c := 4·(2c+1)·((s+1)^(2^s·s+1) + 1) + 1`):

| Row | s | c | fuel digits | materialize + `% p` | note |
|----|---|---|------------|--------------------|------|
| 2  | 4 | 2 | ~47 | trivial | matches blocked dispatch's table |
| 6  | 9 | 6 | ~4,613 | 0.117 ms | |
| 20 | **19** | 9 | **~12.96 million** | **599 ms** | corrects the "≤ ~4,700 digits for all rows" claim |
| 20 | | | | 500 decrements: 4 s (~8 ms/op) | per-step bignum cost during the run |

Row 20 consequences: (i) the fuel numeral is feasible (5.4 MB, 0.6 s); (ii) each `Nat`
match/decrement on it costs ~8 ms, so a few hundred to a few thousand steps add roughly
**2–20 s** to row 20's `#eval` — acceptable for a test row but MUST be timed in-phase
(done-criterion below). (iii) **Honest scope limit**: per-branch fuel digits scale as
`2^s·s·log₁₀(s+1)`; around `s ≈ 25` the numeral reaches ~0.5 GB and materialization dies
again. Candidate (a) makes the corpus (max `s = 19`) and small formulas evaluable; it does
NOT make `intuitionisticTableau` evaluable for arbitrarily large formulas. The sufficiency
THEOREM is unaffected (proof-side, all φ). Future corpus rows must keep `s ≲ 22`; record
this in the Phase 8 docs.

**Cost of (a)** — the honest bill: the fuel plumbing is the induction skeleton of four
engine-quantifying proofs, whose wrappers must be ported (contents transfer arm-by-arm):
1. `intExpandBranches_closed_unsat` (`Soundness.lean:1078`, ~690 lines, sorry-free, green —
   the soundness workhorse; unfolds `intExpandBranches.go` directly at `:1161, :1223`).
   Largest single porting risk.
2. `intExpandBranches_openBranch_closed` (`Scheme.lean:684`).
3. `intExpandBranches_openBranch_initial_mem` (`Scheme.lean:3301`).
4. `intExpandBranches_openBranch_sat` succ-case (`Scheme.lean:3014`, preserved asset; its
   pre-existing fuel-0 sorry at `:3055` stays put during the mechanical port, then Phase 6
   restates R1 exactly as planned).
Mitigation: parallel-build-then-flip (new engine + new lemmas land beside the old; the old
stays green until each replacement is proven; one flip commit swaps the entry points) —
tree green at every commit boundary, per the commit-per-green-substep mandate.

### 3. Candidate (b): well-founded recursion on the measure — NO-GO (as the Phase-4 repair)

The measure decrease is proven only UNDER invariants: `intExpMeasure_step_lt`
(`Scheme.lean:2575-2587`) requires `hb : ∀ x ∈ bh, x ∈ intUniverseExt φ0`, and maintaining
`hb` through the world-creating arm requires `hnw : nextWorld ≤ WBound φ0`
(`intApplyRuleFull_outputs_subset_ext`, `Scheme.lean:2323`, takes it as a threaded premise).
A WF-on-measure engine must re-establish both invariants **inside its own `decreasing_by` /
recursive-call obligations** — i.e. it needs precisely Phase 5's `hNW` fresh-mint
preservation, which is DP-2: research-grade and unproven (plan's own risk register). The
consequences are decisive:
- A `decreasing_by sorry` defines the function via `sorryAx`, tainting the entire
  procedure, `instDecidableIValid` (`DecisionProcedure.lean:107`), and every downstream
  theorem — forbidden by zero-debt and by the plan's own MUST-NOT list. There is no
  strategic-sorry placement that keeps the definition clean.
- This *inverts the skeleton plan's risk concentration*: DP-2 was deliberately a
  theorem-side division point (Phase 5 can sorry it and Phases 6-7 still land
  conditionally). Under (b), DP-2 failure means NO engine exists at all.
- Secondary costs: the engine signature becomes proof-carrying (subtype/hypothesis
  arguments), changing every consumer (`Soundness.lean`, both `Completeness.lean` files,
  the corpus's import surface); the runtime-check alternative (deciding membership in
  `intUniverseExt φ` at runtime instead of carrying proofs) is infeasible — that list has
  `Θ(WBound)` elements (~10^13,000,000 for row 20) and can never be built.
- What (b) gets right: no fuel numeral at all (best possible `#eval` profile), and `#eval`
  through WF compiles fine. It remains a legitimate *elective cleanup after DP-2 closes* —
  record as future-work, not as the Phase-4 repair.

### 4. Candidate (c): split proof-side from eval-side procedure — NO-GO

Let `intuitionisticTableauP` carry the huge fuel (theorems) and `intuitionisticTableau`
keep the current `intFuel` (corpus). The equivalence obligation is
`intuitionisticTableauP φ = intuitionisticTableau φ`, and it is not dischargeable:
- Verdict-stability under fuel increase is NOT free here, because the engine's behavior
  depends on remaining fuel beyond exhaustion: the persistence call
  `applyPersistenceFixpoint b edges (fuel' + 1)` (`Expansion.lean:363`) receives the
  remaining OUTER fuel, so two runs at different fuels compute different `bPers` unless the
  smaller run provably reaches genuine persistence fixpoints — which is exactly the
  sufficiency fact that is unavailable at the small fuel (that unavailability is the whole
  blocker). The general equivalence theorem therefore needs small-fuel sufficiency for all
  φ — false-or-unprovable.
- Per-row equivalence cannot be certified either: `decide`/`rfl` stall on the engine's
  `let rec`s in the kernel (documented at `TableauConformance.lean:28-37`), and `#eval`
  proves nothing.
- Without equivalence, the corpus certifies a procedure about which no theorem speaks, and
  the theorems (completeness, `instDecidableIValid`) attach to a procedure that is never
  executed anywhere — including the divergence-witness termination regression (row 20,
  `TableauConformance.lean:347-356`), which would silently stop guarding the proof-side
  procedure. This reintroduces the exact hazard class the corpus header names as its reason
  to exist ("sorry-free and lake build-green while still deciding the wrong verdict") and
  that the ancestor-blocking work closed. It also demotes Route 1's documented role as the
  constructive, executable decision route (`DecisionProcedure.lean:50-76`) to a de facto
  noncomputable one, duplicating the FMP route's niche.
- It is the cheapest edit — and buys a certification regime strictly worse than the status
  quo. NO-GO.

### 5. Recommended candidate and go/no-go argument

**GO: candidate (a).** It is the unique candidate that simultaneously:
(i) makes every corpus fuel numeral materializable (probe: 0.6 s worst row);
(ii) keeps the engine definition free of proof obligations (unconditional termination
     measure — pure `pow3` arithmetic over exactly-2-way branching);
(iii) preserves the plan's risk concentration (DP-1 stays proved; DP-2 stays a Phase-5
     theorem-side division point; hNW/hUniv remain R1 hypotheses discharged at the
     singleton call site by `WBound_pos`, `Scheme.lean:1768`);
(iv) *simplifies* Phases 6-7's arithmetic (fuel-0 discharge becomes `intWork < 0` absurd,
     replacing the measure-0 `3^k ≥ 1` argument; sufficiency consumes only `intWork_drop`);
(v) keeps the corpus certifying the same executed procedure with unchanged verdicts.
Its cost — porting four engine-induction wrappers, dominated by the ~690-line
`closed_unsat` — is real, bounded, mechanical in content, and mitigated by
parallel-build-then-flip. No blocking unknown remains: the two facts that could have killed
it (row 20's numeral size; exactly-2-way branching for the termination decrease) were both
verified empirically/by source this dispatch.

### 6. Phase-4 replacement spec (statement-level, for plan revision without re-research)

Replace plan-13 Phase 4 with three phases (4A/4B/4C), keeping Phases 5-8 numbering intact.
All new names are suggestions; the constraint set is binding, the naming is planner
latitude.

**Import-direction constraint (named planner decision)**: `intFuelExt` needs `WBound`
(currently `Scheme.lean:1762`), but the entry points currently live in `Expansion.lean`
(which `Scheme.lean` imports). Either (i) move the two entry-point defs
(`intuitionisticTableau`, `minimalTableau`) into `Scheme.lean` after `WBound` and repoint
the corpus import (`TableauConformance.lean:11,15` currently imports only `Expansion`), or
(ii) move `intSubfmls`/`intChainBound`/`WBound` (defs + the lemmas they need) below the
engine. Option (i) is smaller.

**Phase 4A — per-branch-fuel engine (parallel build; no consumer flipped)**
- Def `intFuelExt (φ) : Nat := 4 * (2 * φ.complexity + 1) * (WBound φ + 1) + 1`.
  MUST be this arithmetic form — never `2 * (intUniverseExt φ).length + 1`: the LIST has
  `Θ(WBound)` elements and is unmaterializable; only the numeral is feasible. Docstring
  records this and the `s ≲ 22` corpus-row feasibility envelope.
- New engine `intExpandBranchesB` (working name): same worklist shape, same parallel lists,
  with `fuel : Nat` replaced by `fuels : List Nat` (fourth parallel list). Arms: active
  branch's `f + 1` → `f` on linear/world-create/reuse; beta children each get `f`;
  active-branch `f = 0` → `.openBranch bPers` (exhaustion arm, mirroring today's global
  arm); persistence keeps receiving the active branch's remaining fuel. `go` lifted to a
  top-level (mutual or selector-refactored) def so WF elaboration and functional induction
  work; `termination_by` lex `((fuels.map (3 ^ ·)).sum, pending.length)`;
  `decreasing_by` via the `pow3` family — unconditional, no invariants.
- Lemma `intWork_init_lt_intFuelExt (φ) : intWork (intUniverseExt φ) [⟨.neg, φ, 0⟩] [] <
  intFuelExt φ` — the `intExpMeasureExt_init_le_fuel` REPLACEMENT (Phase 6's call-site
  discharge). Proof shape: the countP bookkeeping of `intExpMeasure_init_le_fuel`
  (`Scheme.lean:2787-2812`) + `intUniverseExt_length_le`, closing by `omega` (no pow
  manipulation — strictly easier than the lemma it replaces).
- **Done when**: new defs + init lemma build sorry-free (scoped build); an `#eval` parity
  probe (not committed, or committed as a temporary CslibTests section) shows
  `intVerdictB = intVerdict` on all 20 propositional rows; zero changes to existing
  declarations.

**Phase 4B — port the engine-quantifying lemmas to the B-engine (old ones untouched)**
- `intExpandBranchesB_closed_unsat` (port of `Soundness.lean:1078`): statement gains
  `fuels`; proof by functional induction on the B-engine (or manual WF induction on the lex
  measure); per-arm content transfers.
- `intExpandBranchesB_openBranch_closed`, `_initial_mem` (ports of `Scheme.lean:684`,
  `:3301`): fuel plays no role in their content; wrapper-only ports.
- Mechanical port of `intExpandBranches_openBranch_sat`'s succ case to the B-engine
  (statement gains `fuels`; NO R1 hypotheses yet; the pre-existing fuel-0 sorry carries
  over 1-for-1 — subtree bare-sorry count stays 4).
- **Done when**: all four B-lemmas build with exactly one sorry total (the carried fuel-0
  sorry); old lemmas untouched and green.

**Phase 4C — flip + retire + corpus gate**
- Redefine `intuitionisticTableau`/`minimalTableau` via the B-engine with
  `fuels := [intFuelExt φ]`; rename B-engine to `intExpandBranches` (retiring the old
  engine, old `intFuel`, `intExpMeasure_init_le_fuel` per Phase 8's deprecation-notes
  policy or immediately — planner choice); repoint `tableau_sound`,
  `openBranch_countermodel` (`Scheme.lean:3448`), `tableau_complete` (`:3504`), and the
  Minimal-side consumers at the ported lemmas. `propExpandBranches` alias updated.
- **Done when**: full `lake build` green; `lake test` green with ALL 44 corpus rows
  unchanged (esp. row 20); **timing gate**: record `lake test` wall time before Phase 4A
  and require the post-flip run within a declared budget (suggest ≤ 3 minutes total or
  ≤ 5× baseline, whichever is looser — row 20 is expected to add ~2-20 s of bignum
  arithmetic); dependents (`DecisionProcedure.lean`, both `Completeness.lean`) build green;
  subtree bare-sorry count still 4.

### 7. Impact on Phases 5-8 and preserved assets

| Item | Impact |
|------|--------|
| Phase 5 (hUniv/hNW threading, DP-2) | Substance unchanged: same four arms, same fresh-mint `hNW` risk, same `applyPersistenceFixpoint_subset_ext` consumption. Stated against the B-engine's arms (identical arm structure). |
| Phase 6 (R1 restatement) | `hFuel` hypothesis CHANGES FORM: from `intExpMeasure (intUniverseExt φ0) branches expandedSets ≤ fuel` to a per-branch parallel-list invariant (`IAllFuel`-style, mirroring `IAllConsistent`): `∀ i, intWork (intUniverseExt φ0) bᵢ eᵢ < fuelsᵢ`. Fuel-0 discharge simplifies: exhaustion arm + `hFuel` gives `intWork < 0`, absurd by `omega` (replaces 583 F5's measure-0 argument; no other change to the F5 shape). Re-establishment per arm: `intWork_drop` (+ `intCount_notMem_mono` for the persistence prefix), per child in the beta arm. Call-site repair discharges `hFuel` by `intWork_init_lt_intFuelExt`, `hUniv` by singleton membership, `hNW` by `WBound_pos` — as planned. |
| Phase 7 (truthLemma T-imp) | Unchanged. The genuine-fixpoint lemma (`Scheme.lean:2928`) needs persistence fuel ≥ `countP`-not-on-branch; at the R1 leaf the active branch's remaining fuel `f' + 1` satisfies `countP ≤ intWork ≤ f'` from the threaded `hFuel` — same consumption, per-branch. |
| Phase 8 (docs + CI) | Adds: `intFuel`→`intFuelExt` story; engine-restructure docstring; divergence-witness note updated for per-branch fuel semantics; sum-measure engine (`intExpMeasure_step_lt`(+`_branch`), `intExpMeasure`, splits) marked retained-but-unconsumed (they stay green; statements never mention the engine); the `s ≲ 22` corpus-row feasibility envelope recorded. |
| `intCreatedChain_le`, `WBound`, `intChainBound` (Phase 2, PROVED) | **Untouched** — no reference to the engine or fuel anywhere in their statements/proofs (`Scheme.lean:1753-1839`). |
| `intUniverseExt` family + `_outputs_subset_ext` containment family (Phase 3) | **Untouched** (`Scheme.lean:2155-2401`). |
| `applyAllTImpRules_count_drop`, `applyPersistenceFixpoint_genuine_of_count_le_fuel` | **Untouched** — they concern the persistence inner loop, not the outer engine (`Scheme.lean:2862, 2928`). |
| `intWork_drop`, `intCount_notMem_mono`/`_append_drop` | Untouched; PROMOTED to the load-bearing sufficiency core. |
| `intExpMeasure_step_lt`, `_step_lt_branch` (re-targeted in Phase 3) | Stay green (engine-independent statements); demoted to unconsumed. |
| `closed_unsat` / `tableau_sound` (sorry-free, green) | Ported in 4B (wrapper rework, content transfer). Biggest regression surface; old proof retained until the 4C flip. |
| Conformance corpus (44 rows incl. row 20) | Zero row edits; verdicts preserved (identical step sequences); row 20 gains ~0.6 s materialization + seconds of bignum stepping — timing gate in 4C. |
| `instDecidableIValid`, Completeness bridges (430), FMP route | Signatures untouched; the instance becomes genuinely evaluable-in-principle for small formulas (unlike under (c)). |

## Adversarial Self-Verification

Challenged this report's own load-bearing claims before finalizing; two claims from the
input record were REFUTED and corrected (rows marked ✗→corrected).

### Claim Verification Table

| Claim | Source/Counterexample | Verdict |
|-------|----------------------|---------|
| Global fuel binds strictly before expansion; early exit cannot avoid materialization | `Expansion.lean:522-525, 535-538` (strict `let`) | Verified |
| No global-scalar fuel of any materializable size can be provably sufficient | Branch count worst-case exponential in per-branch beta firings ≤ f(|intUniverseExt|); |intUniverseExt| = Θ(WBound) (`Scheme.lean:2164`) | Verified (argument, not probe) |
| Handoff: candidate (a) numerals "≤ ~4,700 digits for all corpus rows" | Probe: row 20 has s=19, chainBound=9,961,472 (`lake env lean` against landed `intSubfmls`/`intChainBound`); fuel ≈ 10^12,960,000 | ✗ REFUTED → corrected: ~13.0M digits for row 20 |
| Row 20's corrected numeral is still materializable | Probe: `4·19·(20^9961473+1)+1 % 1000003` computes in 599 ms; 500 decrements in 4 s | Verified (feasible, with a runtime caveat now recorded as a 4C timing gate) |
| Per-branch sufficiency needs only `intWork_drop` + monotonicity + init bound | `intWork_drop` docstring/statement covers all arms incl. reuse (`Scheme.lean:2516-2531`); persistence prefix via `intCount_notMem_mono` (`:2500`) | Verified |
| Termination decrease for (a) is unconditional | All three `branchingResult` sites emit literal 2-element lists (`Rules.lean:259, 262, 280`); `2·3^f < 3^(f+1)`; other arms `3^f < 3^(f+1)`; skip-closed shrinks pending | Verified by source |
| `#eval` works through WF recursion | Compiler ignores termination proofs; corpus header already excludes kernel routes for the CURRENT engine too (`TableauConformance.lean:28-37`), so no regression is possible on this axis | Verified (by mechanism + existing in-repo record; no new probe) |
| Candidate (b) requires DP-2 in the definition | `intExpMeasure_step_lt` needs `hb` (`Scheme.lean:2583`); `hb`-maintenance at world-creation needs `hnw ≤ WBound` (`:2323`); `hNW` fresh-mint preservation is DP-2 (plan Phase 5) | Verified |
| Candidate (b) runtime-check fallback is infeasible | Membership check against `intUniverseExt φ` requires the Θ(WBound)-element list (~10^13M elements, row 20) | Verified |
| Candidate (c) equivalence is blocked by fuel-dependent persistence | `applyPersistenceFixpoint b edges (fuel' + 1)` at `Expansion.lean:363` — remaining fuel leaks into `bPers` unless genuine fixpoint reached, which is the unavailable sufficiency fact | Verified |
| Candidate (c) per-row equivalence not kernel-checkable | `decide`/`rfl` stall on the engine's `let rec`s (`TableauConformance.lean:30-33`) | Verified (in-repo record) |
| Plan's Scope Hypothesis "corpus rows pin results, not fuel values" | Grep of `CslibTests/TableauConformance.lean`: no literal `intFuel` value pinned; rows assert verdict strings only | Verified |
| Corpus verdicts survive the restructure | Fuel affects behavior only via exhaustion; per-branch budgets ≫ observed step counts (divergence table, `Expansion.lean:465-468`); persistence fuel shape preserved | Verified (argument; empirical parity is a 4A/4C done-criterion, deliberately kept in-phase) |
| Phase 2/3 assets untouched by (a) | `intCreatedChain_le`(`:1805`), `WBound`(`:1762`), `intUniverseExt` family(`:2155-2401`) contain no engine/fuel references | Verified |
| "(a) restores evaluability for ALL formulas" | Self-challenged: FALSE — fuel digits ≈ 2^s·s·log₁₀(s+1); ~0.5 GB at s≈25 | ✗ Rejected → scoped honestly: corpus (s ≤ 19) and small formulas only; recorded as a Phase 8 doc item and corpus-row envelope |

### Uncertain claims (with confidence)

- Row 20's post-flip `#eval` wall time (estimated +2-20 s from ~8 ms/bignum-op × observed
  step counts; medium confidence — exact step count for row 20 not re-measured here). Gated
  by the 4C timing done-criterion, so a bad surprise blocks the phase, not the library.
- Functional induction (`.induct`) availability for a mutual WF pair with the lifted `go`
  (medium-high confidence; fallback named in-spec: manual WF induction on the lex measure;
  second fallback: selector-refactor of `go` into a total non-recursive-into-engine helper).
- 4B effort for the `closed_unsat` port (~690 lines): sized at 1-2 dispatches (medium
  confidence). Parallel-build staging means underestimation costs schedule, not greenness.

### Recommendations modified after verification

- The candidate-(a) numeral-size claim inherited from the handoff was corrected (row 20);
  the correction ADDED the 4C timing gate and the corpus-row feasibility envelope to the
  spec rather than changing the candidate choice.
- An initial draft treated (a)'s restructure as a single replacement phase; verifying the
  blast radius (four engine-induction proofs, `Soundness.lean:1161,1223` unfolding `go`
  directly) forced the 4A/4B/4C parallel-build-then-flip split to honor H8 sizing and the
  green-at-every-commit mandate.

### BibKey verification status

All four carried BibKeys verified present in `references.bib` this dispatch: `Fitting1983`
(:211), `Dyckhoff1992` (:218), `GargGenoveseNegri2012` (:239), `Massacci2000` (:1041). No
new literature citations introduced; this report's grounding is Tier 3 (implementation).

## Next Steps

Revise plan 13 (`/revise 317` or planner dispatch) replacing Phase 4 with the 4A/4B/4C
spec in §6 and applying the §7 deltas to Phases 6-8 (notably R1's `hFuel` form and the
`intWork_init_lt_intFuelExt` call-site discharge). No re-research needed. Candidate (b)
may be recorded as elective post-DP-2 future work; candidate (c) should be recorded as
rejected with the §4 rationale so it is not re-proposed.
