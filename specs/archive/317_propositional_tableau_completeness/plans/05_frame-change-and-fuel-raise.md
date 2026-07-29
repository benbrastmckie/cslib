# Implementation Plan: Task #317 (v5 — Frame change + fuel raise for sorry-FREE intuitionistic tableau completeness, HARD mode)

- **Task**: 317 - Close BOTH residual sorries (B1 `Scheme.lean:330` truthLemma T(→); B2 `Scheme.lean:986` `intExpandBranches_openBranch_sat` fuel=0) to reach a sorry-FREE intuitionistic tableau completeness
- **Status**: [BLOCKED] — Phase 2 (foundation) hit STOP-gate R1; Phases 3–11 gated. Requires an architectural decision (plan v6 revising Postmortem 5 signature constraint, or `IForces`/`Kripke.lean` change) before proceeding. See Phase 2 for the two documented blockers.
- **Effort**: 18 hours
- **Dependencies**: 316 (soundness, landed — TERRITORY HAZARD, `Soundness.lean` + `Expansion.lean` fuel site). Downstream: 430 (atom-persistence upward closure — RESHAPED by this plan's frame change, see Roadmap Alignment), then 375 (proof-system TFAE edges, needs 430 + completeness green).
- **Research Inputs**:
  - `specs/317_propositional_tableau_completeness/reports/07_option-b-fuel-bound.md` (VERDICT: Option B unsound; literal `sat_fimp` suffices; the REAL blocker for sorry 986 is that fuel counts expansion STEPS so it must cover the β-branching forest `2^Θ(c²)`, which dedup does NOT shrink — fix = RAISE the fuel + add a `measure ≤ fuel` hypothesis mirroring `classicalExpandBranches_hintikka` and Modal-K `FmpMeasure`; 6-phase B2 breakdown; RETIRE plan-v4 Phases 5/7)
  - `specs/317_propositional_tableau_completeness/reports/08_b1-truthlemma-timp.md` (VERDICT: sorry 330 is LITERALLY FALSE under the numeric `(ℕ,≤)` frame — phantom unlabeled worlds refute it; fix = re-base completeness accessibility from numeric `≤` to edge-reachability `isAccessible`/`MonotoneEdges` + add `sat_timp` field to `IBranchSaturation` + `intExtractValuation` monotonicity; keep the full two-direction truth lemma; 4-5 phase B1 breakdown)
- **Superseded context (reference only, do NOT revert their landed work)**:
  - `plans/04_sfor-dedup-fuel-sufficiency.md` — its Phases 1-4 (Sfor-dedup design + impl + countermodel-tightening + soundness fix) LANDED and are GREEN (Option A, commit `4202d1df`; soundness fix `8a5c0250`). Its Phases 5/7 (`intExpandBranches_fuel_sufficient` at the *current* fuel) are RETIRED — they rest on the false premise `forest ≤ 2^(2c+2)` (report 07 §Q2).
  - `plans/03_b2-fuel-sufficiency.md` — its Phase 1 (`IAllConsistent` invariant, B2 `none` case) is a Preserved Asset.
- **Artifacts**: `plans/05_frame-change-and-fuel-raise.md` (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md (CSLib zero-debt)
- **Type**: cslib
- **Lean Intent**: true

## Overview

Two adversarially-verified research spikes (reports 07 and 08) **overturned the v4 strategy**. The
build is GREEN with exactly two `sorry`s in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`: line ~330 (B1, truthLemma T(→)
forward case) and line ~986 (B2, the `fuel=0` base case of `intExpandBranches_openBranch_sat`).
v4 tried to close 986 by keeping the fuel fixed and adding an `Sfor`-containment dedup. Report 07
**refutes** that: fuel decrements once per expansion STEP, so it must cover the entire β-branching
expansion FOREST (`2^Θ(c²)`), which world-dedup provably does not shrink. Report 08 **independently
refutes** the v4 completeness frame: sorry 330 is *literally false* over the numeric `(ℕ,≤)` frame
because phantom unlabeled worlds `w' ≥ w` falsify the T(→) obligation.

The v5 unifying strategy has one FOUNDATION and two convergent tracks:

1. **FOUNDATION — Frame change (numeric `≤` → edge-reachability).** Re-base the completeness
   countermodel accessibility from the ambient `Preorder ℕ` `≤` onto edge-reachability
   (`isAccessible`/`MonotoneEdges`, already on the soundness side). This is *shared*: it makes B1's
   330 obligation TRUE, and it harmonizes the committed Option-A dedup (whose reuse can point to a
   *numerically-smaller* label, so `w' ≤ w` numeric ordering is not even valid accessibility) with
   the countermodel's accessibility relation. Sequence FIRST (Phases 1-3).
2. **B1 track (close 330)** — after the frame change: add `sat_timp` to `IBranchSaturation`
   (saturation dual of the soundness rule `intTImpRule`/`applyAllTImpRules`), prove `intExtractValuation`
   monotonicity from `propagatePersistence`, discharge the T(→) truth-lemma case over the new frame
   (Phases 4-5).
3. **B2 track (close 986)** — after the frame change: RAISE the fuel formula in `Expansion.lean`
   (task-316 TERRITORY HAZARD) to cover `2^Θ(c²)`; add `intUniverse`/`intWork`/`intExpMeasure` +
   the linear world bound; prove `intExpMeasure_step_lt` and `intExpMeasure_init_le_fuel`;
   REFORMULATE `intExpandBranches_openBranch_sat` with the `measure ≤ fuel` hypothesis (as the
   classical and Modal-K templates do); close 986 (Phases 6-10). Do NOT pursue Option B.
4. **Convergence.** Both tracks re-meet at exactly one lemma — `intExpandBranches_openBranch_sat`
   (and the `IBranchSaturation` structure it produces): B1's new `sat_timp` field and B2's
   `measure ≤ fuel` reformulation both land there (Phase 10). This is the sole serialization point.

**Definition of done**: `Scheme.lean` builds GREEN; BOTH sorry 330 and sorry 986 are closed
sorry-free; `grep -n sorry` over the four Intuitionistic tableau files returns nothing; no new
axioms / sorries / vacuous defs; `openBranch_countermodel`, `tableau_complete`, and any `Decidable`
consumer keep their public signatures stable; `Soundness.lean` (task 316) edited only where the
fuel-raise strictly forces it (separate scoped commit + coordination flag).

### Research Integration

- **Report 07 (B2, Tier 1 + Tier 3, H4-verified)** supplies the fuel-raise mechanism. Key
  overturns of v4: (a) fuel = total expansion-forest node count, NOT deduplicated-model size; (b)
  worlds are ALREADY linearly bounded (`W ≤ c+1`) with no dedup at all, so world-count is not the
  binding constraint; (c) the binding constraint is the `2^Θ(c²)` β-forest which no world-level
  dedup shrinks; (d) the *proven* Modal-K `FmpMeasure` "counting-against-fixed-universe" pattern
  (`|U\b| + |U\e|`, `Σ 3^work`) is the transferable measure, requiring fuel `~3^Θ(c²)`. Option B
  (append `F(ψ)@x` on reuse) is UNSOUND (breaks `intExpandBranches_closed_unsat`); literal
  `sat_fimp` needs no reformulation. Retire v4 Phases 5/7.
- **Report 08 (B1, Tier 1 + Tier 3, H4-verified)** supplies the frame change. Key overturns:
  (a) sorry 330 is false over `(ℕ,≤)` — a phantom world `k` larger than every branch label refutes
  the T(→) obligation (adversarial §, minimal `T(¬p→q)` breaks it); (b) fix = accessibility must be
  edge-reachability (`isAccessible edges`), NOT the ambient `≤`; (c) add `sat_timp` (saturation dual
  of `intTImpRule`/`applyAllTImpRules`, `Soundness.lean:353-406`) + prove `intExtractValuation`
  monotone along edges from `propagatePersistence`; (d) keep the full two-direction truth lemma (the
  F-imp case already calls `ih_φ'.1`, so the T-direction cannot be dropped; one-sided reformulation
  fails); (e) dedup SHARPENS the case against numeric `≤` (reuse can target a numerically-smaller
  label), independent confirmation the frame must be the edge relation.

#### Source-to-Implementation Mapping (Tier 1 — MANDATORY for this literature-backed task)

| Source claim | Citation / Report | Lean target (file:line) | Translation notes |
|---|---|---|---|
| Kripke forcing of `A→B` at `w` quantifies over the model's OWN constructed accessibility, not the ambient carrier order | Troelstra & Schwichtenberg §2.4; Negri & von Plato Ch. 8 (report 08 map) | `Kripke.lean:81,100` `IForces`/`IForces_imp`; completeness `Preorder` install (Phase 2) | Frame `≤` must be the RTC of `isAccessible edges`, not `Preorder ℕ`. The bug: the carrier's ambient `≤` was taken as accessibility. |
| Countermodel worlds = the finite set of branch labels; accessibility = the constructed edge relation | Negri & von Plato Ch. 8; Troelstra & Schwichtenberg §2.4 (report 08) | `Soundness.lean:344-348` `MonotoneEdges`/`isAccessible`; `Scheme.lean:72-99` `IBranchSaturation` | "World" ranges over finite branch labels ordered by branch edges — never over all of ℕ. Reuse the soundness-side machinery. |
| Persistent `T(A→B)` rule: copies to every accessible world, there splits `F(A) ∣ T(B)` | Fitting Ch. 4 (in-repo `Scheme.lean:45`); Negri & von Plato `L→` | `Soundness.lean:377-406` `intTImpRule`/`applyAllTImpRules`; `Expansion.lean:199,245` `propagatePersistence`/`applyPersistenceFixpoint` | The rule exists on the SOUNDNESS side; completeness needs its saturation dual as the new `sat_timp` field (Phase 4). |
| Truth lemma is a simultaneous both-signs induction, mutually dependent through `→` | Troelstra & Schwichtenberg §2.4; Fitting Ch. 4 (`Scheme.lean:45,244,1313`) | `Scheme.lean:303-335` `truthLemma` | F-imp needs the T-direction of a subformula (`ih_φ'.1`); keep the full two-direction lemma (Phase 5). |
| Counting-against-fixed-universe measure gives strict decrease despite persistence | task 442 `FmpMeasure.lean` (Modal K); report 06 §2.2; report 07 §Q4 | v5 `intUniverse`/`intWork`/`intExpMeasure` (Phases 7-9) | `modalWork U b e = |U\b|+|U\e|`, `modalExpMeasure = Σ 3^work` — a PROVEN repo pattern. Requires the RAISED fuel `intFuel φ ≈ 3^Θ(c²)`. |
| Fuel counts expansion STEPS = forest node count; current fuel `2^(2c+2)` is insufficient | report 07 §Q2 (grounded in `Expansion.lean:339-429` `go` recursion) | `Expansion.lean:464-467` fuel site (Phase 6) | Change `2^(2*φ.complexity+2)` → `intFuel φ`. Every downstream fuel-pinned caller must be re-audited (TERRITORY 316). |
| `measure ≤ fuel` hypothesis threaded into the saturation lemma closes the `fuel=0` case | `classicalExpandBranches_hintikka` (`Classical/Completeness.lean:906-939`); report 07 §Q3 | `Scheme.lean:969-986` `intExpandBranches_openBranch_sat` (Phase 10) | fuel=0 ⟹ measure=0 ⟹ `branches=[]` ⟹ `.openBranch` impossible. Copy the classical structure verbatim. Supply the bound internally to keep `openBranch_countermodel` stable. |
| Literal `sat_fimp` suffices; Option B append-`F(ψ)@x`-on-reuse is UNSOUND | report 07 §Q1, §Q3 (model-pinning counterexample) | `Scheme.lean:95-99` `sat_fimp`; `Soundness.lean:~1083` `intExpandBranches_closed_unsat` | Do NOT reformulate `sat_fimp`; do NOT pursue Option B. Option A (live, `4202d1df`) already satisfies `sat_fimp` soundly. |

BibKey status (report 07/08): `Fitting1983`, `ChagrovZakharyaschev1997`, `TroelstraSchwichtenberg2000`
are PRESENT in `references.bib`; `GargGenoveseNegri2012`, `DershowitzManna1979`, and the two B1
sources `Negri2001` (Negri & von Plato) / `Troelstra2000` are ABSENT — Phase 11 adds the load-bearing ones.

### Prior Plan Reference (plan v4)

Plan v4 (`04_sfor-dedup-fuel-sufficiency.md`) chose **dedup, keep fuel fixed** (its settled decision).
Reports 07/08 **overturn** that decision on two independent grounds (fuel counts the forest, not the
model; the numeric frame makes 330 false). v5 therefore:
- **RETIRES** v4 Phases 5 (`intExpandBranches_fuel_sufficient` at current fuel) and 7 (close 986 via
  dedup fuel-sufficiency) — both presuppose the false `forest ≤ 2^(2c+2)`.
- **PRESERVES** v4 Phases 1-4 (the committed Option-A dedup and its soundness fix) as sound assets;
  see Preserved Assets. Option A is a real, sound, committed deliverable — it is simply *insufficient*
  to bound the forest, so it is no longer the mechanism that closes 986.
- **REVERSES** v4's "do not change the fuel formula" constraint: v5 MUST raise the fuel (report 07),
  and MUST re-base the frame off numeric `≤` (report 08).

### Roadmap Alignment

No ROADMAP.md found. Downstream chain: this plan's completeness-green unblocks **task 430**
(atom-persistence upward closure), which unblocks **task 375** (proof-system TFAE edges).

**Coordination note for task 430 (do NOT plan here — flag only)**: task 430 reasons about
`intExtractValuation` upward-closure *under the accessibility relation*. This plan's
`≤` → edge-reachability frame change **directly reshapes 430's argument**: 430 must re-base its
upward-closure from numeric `≤` onto the same `isAccessible`-reachability frame installed in Phase 2,
and must account for the Option-A dedup's converging-witness structure (a reused ancestor `x` can
serve as the witness for many `F(→)` obligations, so the accessibility tree is shallower and more
cross-referenced than a fresh-world-per-obligation tree). **Task 430's plan/research MUST be revised
after this plan's Phase 2 (frame) and Phase 4 (`intExtractValuation` monotonicity) land.** Task 375
is gated on 430 + this plan's completeness-green.

## Preserved Assets (do NOT recreate or revert — build on these)

The following work is COMPLETE and must not regress:

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| Committed Option-A dedup `intFImpReuseWitness?` (requires an explicit `F(ψ)@x` entry on reuse — SOUND) | `Expansion.lean` | [COMPLETED] | commit `4202d1df` |
| Soundness fix `intExpandBranches_closed_unsat` for the dedup reuse case | `Intuitionistic/Soundness.lean` (task 316) | [COMPLETED] | commit `8a5c0250` |
| Phase-1-v3 `IAllConsistent` / `IExpandedConsistent` / `ILabelBound` invariant + monotonicity combinators | `Scheme.lean` | [COMPLETED] | plan 03 P1, commit `26508fe9` |
| `IExpandedConsistent_sat` bridge (`intStepBranch = none` + invariant → `IBranchSaturation`) | `Scheme.lean` (`:563-633`) | [COMPLETED] | sorry-free |
| B2 `none` case closed via `IAllConsistent` invariant | `Scheme.lean` | [COMPLETED] | commit `26508fe9` |
| Per-step preservation lemmas (`ILabelBound_extendMany`, `intStepBranch_some_exists`, `intStepBranch_linear_preserves`, `intStepBranch_branch_preserves`, `ILabelBound_applyPersistenceFixpoint`) | `Scheme.lean` | [COMPLETED] | sorry-free |
| Existing 5 `IBranchSaturation` fields incl. literal `sat_fimp` (report 07 §Q3: no reformulation needed) | `Scheme.lean:74-99` | [COMPLETED] | sorry-free |
| Soundness-side frame machinery `isAccessible`, `MonotoneEdges`, `intTImpRule`, `applyAllTImpRules`, `IEdges` | `Soundness.lean:344-406` | [COMPLETED] | reuse target for Phases 1-4 |
| `propagatePersistence`, `applyPersistenceFixpoint`, `posFormulasAt` | `Expansion.lean:122-139,199,245` | [COMPLETED] | reuse for monotonicity + `sat_timp` |
| Classical template `classicalExpMeasure`/`classicalExpMeasure_step_lt`/`classicalExpandBranches_hintikka` | `Classical/Completeness.lean:636,906-939` | [COMPLETED] | reference-only for Phases 7-10 |
| Modal-K `FmpMeasure` counting-against-universe template | `Modal/Tableau/FmpMeasure.lean:131,776-833,3018` | [COMPLETED] | reference-only for Phases 7-9 (task 442) |
| Calculus soundness | `Intuitionistic/Soundness.lean` (task 316) | [COMPLETED] | TERRITORY HAZARD — read-only unless Phase 6 forces it |

**Status of the Option-A dedup after the fuel-raise**: OPTIONAL but RETAINED. Report 07 establishes
that worlds are linearly bounded (`W ≤ c+1`) with NO dedup, so the dedup is no longer load-bearing
for either the world bound or fuel sufficiency; it is a sound, soundness-neutral refinement that
marginally reduces world count. **Do NOT revert it** (it is committed, sound, and keeps the
`GargGenoveseNegri2012` docstring meaningful). The Phase 7 world bound is proved *independently* of
the dedup so the two do not entangle.

## Goals & Non-Goals

**Goals**:
- Re-base the completeness countermodel accessibility from numeric `≤` to edge-reachability
  (`isAccessible`), re-threading `truthLemma`, `openBranch_countermodel`, `tableau_complete` and
  proving `intExtractValuation` monotone along edges.
- Add `sat_timp` to `IBranchSaturation`; discharge it in `IExpandedConsistent_sat`; close sorry 330.
- Raise the fuel formula to `intFuel φ ≈ 3^Θ(c²)`; add `intUniverse`/`intWork`/`intExpMeasure` and
  the linear world bound; prove `intExpMeasure_step_lt` and `intExpMeasure_init_le_fuel`; reformulate
  `intExpandBranches_openBranch_sat` with a `measure ≤ fuel` hypothesis; close sorry 986.
- Reach a sorry-FREE intuitionistic tableau completeness; keep all public signatures stable.

**Non-Goals**:
- **Option B** (append `F(ψ)@x` on the reuse path) — UNSOUND (report 07 §Q1); do NOT pursue.
- **Reformulating `sat_fimp`** or the Hintikka condition (report 07 §Q3: literal `sat_fimp` suffices).
- **A one-sided (F-only) truth lemma** — fails (report 08 §Q4); keep the two-direction lemma.
- **Reverting the Option-A dedup** — it is a sound committed asset.
- **Task 430 / 375** — flag the frame-change impact on 430 (Roadmap Alignment), do NOT implement.
- **Keeping the fuel formula fixed** (v4's decision) — reversed; the fuel MUST rise.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **R1 (STOP-gate a — highest): the frame change breaks a countermodel lemma that cannot be re-based without editing task-316 `Soundness.lean` or rippling into `Completeness.lean`/`Minimal/Completeness.lean`.** The frame is FOUNDATION — both tracks depend on it; if it stalls, the whole plan stalls. | H | M | Phase 2 carries an explicit **STOP-and-escalate gate**: install the `Preorder` as the RTC of `isAccessible edges` on the completeness carrier and re-thread the three completeness lemmas. If a countermodel lemma cannot be re-based using ONLY completeness-side edits + the read-only soundness machinery (`isAccessible`/`MonotoneEdges`), STOP, mark Phase 2 [BLOCKED], hand off exactly which lemma resists and what soundness edit it would need — do NOT edit `Soundness.lean` to force it. `IValid`-instantiation at the non-`≤` `Preorder` (`Scheme.lean:1348-1353`) is a real proof obligation (report 08 flags MEDIUM confidence) — verify it inside Phase 2, not assume it. |
| **R2 (STOP-gate b): the `measure ≤ fuel` reformulation changes `intExpandBranches_openBranch_sat`'s PUBLIC signature, breaking `openBranch_countermodel`/`tableau_complete`/`Decidable` consumers.** | H | M | Phase 10 supplies the measure bound INTERNALLY from `intExpMeasure_init_le_fuel`, threading the new hypothesis through a `private` `_aux`/`key` (as plan 03 Phase 1 did), so `openBranch_countermodel`'s own public signature is byte-stable. STOP-gate: if the hypothesis cannot be discharged internally at the top-level call site, STOP/[BLOCKED] and hand off — do NOT change a public signature. |
| **R3: adding `sat_timp` to `IBranchSaturation` ripples into `intExpandBranches_openBranch_sat`'s SUCC case (field-wise construction) before B2 is ready.** | M | M | Phase 4 discharges `sat_timp` in `IExpandedConsistent_sat`; the fuel=0 `sorry 986` (still open until Phase 10) SUBSUMES the new field, so the build stays green with exactly the two existing sorries. If the succ case builds `IBranchSaturation` field-wise, Phase 4 also threads `sat_timp` from `IExpandedConsistent_sat` (no measure needed — succ is not fuel=0). If that proves entangled with the fuel work, fold Phase 4's field addition INTO Phase 10 (convergence). |
| **R4 (TERRITORY 316): the fuel-raise edits `Expansion.lean:464-467` (task-316 territory) and its downstream fuel-pinned callers (`intExpandBranches_closed_unsat`, `DecisionProcedure.lean`, `Completeness.lean`).** | H | M | Phase 6 raises the fuel and AUDITS every downstream caller; the change is monotone-safe for the `openBranch → saturated` direction (report 07 Phase 1). Flag task-316 coordination PROMINENTLY; commit `Expansion.lean` (and any forced `Soundness.lean` edit) in a SEPARATE scoped commit. If a soundness lemma needs a non-trivial edit, STOP/[BLOCKED] and escalate rather than editing 316 territory unilaterally. |
| **R5 (anti-overflow): context overflow on the large recursive proofs (frame re-thread, `step_lt`).** Prior dispatches overflowed. | H | H | See Postmortem Constraints: scoped+grepped builds only, `offset`/`limit` windowed reads, `lean_multi_attempt` over `lean_goal` dumps, commit at every green, stop-and-handoff the instant context tightens. `step_lt` (Phase 8) and the frame re-thread (Phase 3) are pre-split candidates. |
| **R6 (concurrent-edit): multiple live orchestrator sessions edit `Scheme.lean`/`Expansion.lean`/`Soundness.lean`.** | M | M | `git log -1 -- <file>` + scoped rebuild GREEN before EACH phase; commit ONLY touched files, never `git add -A`. R6 forces single-writer-per-file: B1 and B2 Scheme.lean phases serialize even when logically parallel. |
| **R7: fuel/measure arithmetic off by a factor** (`intFuel φ = 3^(2·(2c+1)·(c+2))` vs `|U| = O(c²)`). | M | M | Phase 9 proves `intExpMeasure_init_le_fuel` with SLACK (`≤`, never `=`); reuse `FmpMeasure.lean`'s geometric caps (`:131,776-833`) and the linear world bound. If the bound is loose, widen `intFuel` — it is a fresh formula with no external consumer beyond the internal measure argument. |
| **R8: `sat_fimp`'s numeric `w ≤ w'` clause becomes incoherent under dedup** (reuse targets a smaller label; report 08 §Q5). | M | M | Phase 2/4 verify `sat_fimp`'s `w ≤ w'` survives, or restate it over the edge relation alongside `sat_timp`. This is a coherence check, not a new proof burden — the edge frame keeps `sat_fimp` meaningful (reachability, not numeric order). |

## Postmortem Constraints (HARD — every phase MUST obey)

Binding rules derived from v4's overflow incidents, the two v5 spikes, and the settled research
decisions. Items 1-6 carried forward verbatim from v4; items 7-11 encode the v5 reversals.

**Do NOT**:
1. **ANTI-OVERFLOW (R5).** Never run a raw full `lake build`. Build scoped + grepped ONLY:
   `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"`
   (swap the module for `Expansion`/`Soundness` when those are the edited file). Read with
   `offset`/`limit` around the target line ONLY — never whole-file reads of
   `Scheme.lean`/`Expansion.lean`/`Soundness.lean`. Prefer `lean_multi_attempt` over repeated
   `lean_goal` dumps. STOP and write a sharp handoff the instant context feels tight — a committed
   green partial IS success.
2. **Do NOT `git add -A`.** Commit only the files a phase actually touched. `git log -1 -- <file>`
   before each phase (R6 concurrent-edit).
3. **Do NOT introduce any `sorry`, `axiom`, or vacuous/placeholder def.** If a phase cannot close
   sorry-free, mark it [BLOCKED] and hand off (ZERO-DEBT). The only acceptable end states with
   sorries present are strictly BETWEEN phases (330 open until Phase 5; 986 open until Phase 10).
4. **Do NOT edit `Soundness.lean` (task 316)** unless Phase 6's fuel-raise strictly forces a
   fuel-pinned caller fix; if so, flag task-316 coordination PROMINENTLY and commit `Soundness.lean`
   in a SEPARATE scoped commit. Non-trivial soundness edits → STOP/[BLOCKED]/escalate.
5. **Do NOT change any PUBLIC signature** — `openBranch_countermodel`, `tableau_complete`, and any
   `Decidable`/decision-procedure consumer must stay byte-stable. Thread new hypotheses through
   `private` `_aux`/`key` helpers (STOP-gate b, Phase 10).
6. **Do NOT weaken any countermodel / saturation / soundness lemma** to force a case through.

**MUST preserve**:
- All Preserved Assets above (the committed Option-A dedup, the `IAllConsistent` invariant machinery,
  `IExpandedConsistent_sat`, the closed B2 `none` case, the soundness fix, calculus soundness).
- The full two-direction `truthLemma` (do NOT drop the T-direction).
- The green build at every commit boundary (exactly two sorries until they are closed in-phase).

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **RAISE the fuel** (report 07). Option B (append `F(ψ)@x` on reuse) is UNSOUND; keeping the fuel
  fixed cannot close 986 (dedup does not bound the `2^Θ(c²)` forest). This REVERSES v4.
- **Frame = edge-reachability** (`isAccessible`), NOT numeric `≤` (report 08). Sorry 330 is
  literally false over `(ℕ,≤)`. This REVERSES v4's implicit numeric frame.
- **Keep the literal `sat_fimp`** and the full two-direction truth lemma (reports 07 §Q3, 08 §Q4).
- **Add `sat_timp`** as the saturation dual of `intTImpRule`/`applyAllTImpRules`, stated over the
  edge relation.
- **Use the counting-against-fixed-universe measure** (`|U\b|+|U\e|`, `Σ 3^work`; Modal-K
  `FmpMeasure`), NOT the branch-complexity measure (non-monotone under persistence, report 04 F3).
- **Do NOT revert the Option-A dedup** — sound, committed, now an optional refinement.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 6, 7 | 3 |
| 5 | 5, 8, 9 | P5: 3, 4 · P8: 7 · P9: 6, 7 |
| 6 | 10 | 4, 8, 9 |
| 7 | 11 | 10 |

**Parallelism / serialization (R6 single-writer-per-file)**:
- **Foundation (Waves 1-3, Phases 1-3)** is strictly serial: all three are `Scheme.lean`
  completeness-side edits, causally chained (expose edges → install frame → re-thread lemmas).
- **After the frame change (Wave 4 onward), B1 and B2 proceed in parallel LOGICALLY.** The B1 track
  (Phases 4, 5) and the B2 track (Phases 6, 7, 8, 9) have no cross-dependency until the convergence.
  **Genuinely file-disjoint / truly concurrent**: Phase 6 (B2 fuel raise, `Expansion.lean`) runs
  concurrently with any B1 `Scheme.lean` phase. **Logically parallel but R6-serialized**: Phases 4
  and 7 (Wave 4) and Phases 5, 8, 9 (Wave 5) all edit disjoint REGIONS of `Scheme.lean`, so under
  single-writer-per-file they must be sequenced (in either order) rather than run by two live agents
  at once. The wave table shows the logical maximum; a dispatcher honoring R6 picks one Scheme.lean
  writer at a time and may run Phase 6 alongside.
- **The two tracks RE-CONVERGE at exactly one lemma**: Phase 10 reformulates
  `intExpandBranches_openBranch_sat` (and consumes the final `IBranchSaturation` shape with
  `sat_timp`), so it is the **sole serialization point** — it depends on both the completed B1
  structure work (Phase 4) and the completed B2 measure work (Phases 8, 9). B1's own terminal
  (Phase 5, close 330) does NOT depend on B2 and can finish while B2 is still grinding the measure.

---

### Phase 1: Expose branch edges from the expansion (plumbing) [COMPLETED]

- **Goal:** Make the per-branch `IEdges` of a returned open branch available to the completeness
  side, so accessibility can be defined from edges rather than numeric `≤`. No sorry closed here.
- **Tasks:**
  - [x] `git log -1 -- Scheme.lean Expansion.lean`; scoped+grepped rebuild GREEN baseline
        (`4202d1df`/`8a5c0250`).
  - [x] Read (windowed) the `.openBranch b` boundary (`Scheme.lean:1314-1318`), the internal `edges`
        argument threaded through `intExpandBranches` (`Scheme.lean:1316`, `[[]]`), and
        `IEdges`/`isAccessible` (`Soundness.lean:344-348`).
  - [x] Thread the branch's `IEdges` out through the `.openBranch` result OR provide a structural
        lemma `intExpandBranches_openBranch_edges` yielding the branch's `IEdges` without a
        return-type change. **PREFER** the structural lemma (avoids a return-type change that would
        ripple into `Decidable`/`DecisionProcedure` consumers — report 08 P1 flags MEDIUM confidence
        the edges are cleanly exposable without a signature change).
        **Implementation note (deviation from literal lemma name)**: rather than a brand-new
        standalone `intExpandBranches_openBranch_edges` lemma (which would require an awkward
        disjunctive conclusion to remain sound across nested fuel=0 recursion — effectively
        re-deriving Phase 10's fuel-sufficiency content prematurely), the EXISTING private lemma
        `intExpandBranches_openBranch_sat`'s conclusion was widened from `IBranchSaturation Atom b`
        to `∃ edges : IEdges, IBranchSaturation Atom b`, filling `edges := edgesH` at the existing
        "none leaf" case. This reuses the single pre-existing `sorry` (fuel=0 case, now at line 991)
        with zero new sorries and composes cleanly through the existing induction (recursive cases
        pass the IH's existential straight through, unchanged). `openBranch_countermodel`'s call site
        updated to `obtain ⟨edges, hsat⟩ := ...`; `edges` not yet consumed (Phase 2 will use it).
  - [x] **STOP-gate**: if edges cannot be exposed without changing the `.openBranch` return type (a
        public-signature change, forbidden by Postmortem 5), STOP, mark Phase 1 [BLOCKED], hand off
        the exact return-type obstacle. Do NOT change the public boundary silently.
        (Not triggered — `.openBranch`'s return type is untouched; only the `private` lemma's
        conclusion type changed.)
  - [x] Scoped+grepped build GREEN; two sorries unchanged (330, 986 — now at line 991 due to
        docstring additions); commit touched files only:
        `task 317 phase 1: expose branch edges for edge-accessibility frame`.
- **Estimated output:** ~150-300 lines. **Done when:** `intExpandBranches_openBranch_edges` (or an
  equivalent edge accessor) is sorry-free and the public `.openBranch` boundary is unchanged.
- **Timing:** 2.5 hours. **Depends on:** none.
- **Owned files:** `Scheme.lean` (+ `Expansion.lean` ONLY if a non-signature-changing accessor lemma
  must live there — flag). TERRITORY note: coordinate with Phase 6 (also `Expansion.lean`) via R6.

---

### Phase 2: Install edge-accessibility as the completeness frame + `intExtractValuation` monotonicity [BLOCKED]

- **Goal:** Replace the ambient `Preorder ℕ` `≤` with the reflexive-transitive closure of
  `isAccessible edges` on the completeness carrier, and prove `intExtractValuation` monotone along it
  (required for the extracted model to be a `KripkeModel`, `Kripke.lean:64-65` `v_upward_closed`).
  This is the highest-risk phase (R1 / STOP-gate a).
- **Tasks:**
  - [x] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [x] Define the countermodel `Preorder` (or reachable-label subtype) as the RTC of
        `isAccessible edges` (Phase 1's accessor). Read (windowed) `truthLemma` (`Scheme.lean:303`),
        `IForces`/`IForces_imp` (`Kripke.lean:81,100`), `intExtractValuation` (`Soundness.lean:1811`).
  - [ ] Prove `intExtractValuation` monotone along edges from `propagatePersistence`
        (`Expansion.lean:199,245` copies `T(atom p)` to created worlds along edges). **Prove against
        the DEDUP expansion** (report 08 §Q5: reuse must still propagate the parent's `T`-formulas;
        if reuse skips re-propagation, monotonicity along that edge could fail — verify the Option-A
        reuse path preserves the copy).
  - [x] Verify `IValid φ` still instantiates at this non-`≤` `Preorder` for `hvalid`
        (`Scheme.lean:1348-1353`) — a real obligation (report 08 MEDIUM confidence), not a given.
        **RESULT: it does NOT instantiate — see STOP-gate finding below.**
  - [ ] Verify `sat_fimp`'s `w ≤ w'` clause survives the dedup, or note it will be restated over the
        edge relation in Phase 4 (R8).
  - [x] **STOP-gate a**: if the frame cannot be installed / monotonicity cannot be proved using ONLY
        completeness-side edits + read-only soundness machinery, STOP, mark [BLOCKED], hand off which
        lemma resists and what `Soundness.lean` (task 316) edit it would require. Do NOT edit 316.
        **TRIGGERED — see finding below.**
  - [ ] Scoped+grepped build GREEN; two sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 2: install edge-accessibility completeness frame + intExtractValuation monotone`.
        **NOT REACHED — no Lean edits made this phase (analysis-only STOP, per the STOP-gate's own
        instruction not to force a workaround).**

#### STOP-gate a finding (2026-07-01, session `sess_1782919268_2df8d8_317`)

**Claim: the frame change cannot be installed using completeness-side edits alone, because
`openBranch_countermodel`/`tableau_complete`'s byte-stable (Postmortem 5) signatures pin
`IForces`'s `World` type-class argument to `Nat`'s canonical, GLOBAL, TOTAL `Preorder` instance,
and no completeness-side edit can override that instance for a *subset* of worlds without changing
those two theorems' stated types.**

**Mechanism (verified empirically, not just reasoned abstractly):**

1. `IForces` (`Kripke.lean:81`) is defined generically over `[Preorder World]`; its `.imp` case
   (`Kripke.lean:100-104`) unfolds to `∀ w', w ≤ w' → IForces v bot w' φ → IForces v bot w' ψ`,
   where `≤` is resolved via **typeclass instance search on `World`**, not passed as a runtime
   relation.
2. `openBranch_countermodel`'s and `tableau_complete`'s conclusions (`Scheme.lean:1320-1336,
   1360-1368`) both state `IForces (intExtractValuation b) (S.modelBot b) 0 φ` where
   `intExtractValuation b : Nat → Atom → Prop` (`Soundness.lean:1811`, unchanged type). Since `0`
   and `intExtractValuation b`'s domain are both bare `Nat`, `World` unifies to `Nat`, and Lean
   resolves `[Preorder Nat]` to the **unique, globally-registered** `Nat.instPreorder` — confirmed
   live via `#synth Preorder Nat` (returns `Nat.instPreorder`) and
   `example : (Preorder.toLE : LE Nat).le = (· ≤ ·) := rfl` (typechecks), i.e. this instance's `≤`
   is definitionally the standard, TOTAL, unbounded numeric order. This resolution happens at
   THEOREM-TYPE elaboration time (before any proof-body `letI`/`haveI` could run), so it cannot be
   locally overridden without changing `openBranch_countermodel`/`tableau_complete`'s stated types
   — forbidden by Postmortem 5.
3. Because `Nat.instPreorder` is TOTAL and unbounded, `∀ w' ≥ w` in the `.imp` case always ranges
   over infinitely many "phantom" naturals that are never branch labels — report 08's own
   adversarial counterexample (`T(¬p→q)@0`, phantom world `k` beyond every branch label) is a
   genuine, re-verified proof that the T(→) truth-lemma case is **false** under this frame: at
   phantom `k`, `IForces k (¬p) = True` (vacuous, since `intExtractValuation b j p = False` for
   every phantom `j`) but `IForces k q = False` (phantom), refuting
   `∀ w' ≥ w, IForces w' φ' → IForces w' ψ'`.
4. **New finding beyond report 08**: this is not merely "hard to prove" but **type-theoretically
   irreducible**. `Nat.instPreorder` is a *linear* (total) order. General intuitionistic
   Kripke-completeness requires *non-linear* (branching/tree-shaped) frames in general — e.g. two
   sibling worlds created by a β-split (`Scheme.lean` `branchingResult` case, `Expansion.lean`) are
   edge-incomparable, yet both get *some* numeric label under Nat's *total* order. No retraction or
   relabelling of edge-accessible worlds onto bare `Nat` can make Nat's canonical (total, chain-
   shaped) order coincide with a genuinely tree/DAG-shaped edge-accessibility relation — a total
   order cannot represent two incomparable elements. This rules out *any* "clever reindexing"
   workaround within the existing `World = Nat` commitment, not just the specific numeric-labelling
   scheme currently in place.

**What would unblock this** (both options are OUTSIDE "completeness-side edits + read-only
soundness machinery", i.e. both require STOP/escalate rather than unilateral action per Postmortem
4/5):
- **(a)** Change `openBranch_countermodel`'s/`tableau_complete`'s stated conclusion types to
  quantify over a *different* `World` type (not bare `Nat`) carrying a custom `Preorder` instance
  built from the branch's edge-accessibility. This is a deliberate, tracked **public signature
  change** — directly forbidden by Postmortem 5 as currently written. If the orchestrator/user
  decides this signature change is acceptable (it would need to thread through any
  `Decidable`/`DecisionProcedure` consumers too — audit required), Postmortem 5 needs to be revised
  for a re-planned Phase 2/3.
- **(b)** Change `IForces`'s definition (`Kripke.lean`) to take an *explicit* accessibility
  relation parameter instead of relying on `[Preorder World]` typeclass resolution. This is a
  foundational semantics change rippling into the ALREADY-GREEN, task-316-adjacent `tableau_sound`
  (`Scheme.lean:245-288`, same file) and potentially other `IForces` consumers across the
  propositional development — squarely the kind of "edit soundness-adjacent machinery to force it
  through" that Postmortem 4 forbids without STOP/escalation, and well outside `Scheme.lean`'s
  owned-files scope for this phase.

**Recommendation**: this requires a **human/orchestrator-level architectural decision** (likely a
plan v6 that explicitly revises Postmortem Constraint 5 to permit a *deliberate, audited* signature
change at `openBranch_countermodel`/`tableau_complete`, per option (a) above, with a companion
audit of all `Decidable`/`DecisionProcedure` consumers) before Phase 2 can proceed. Both sorries
(330, 991) remain open and untouched; no workaround, weakened lemma, or new sorry was introduced.

#### Supplementary finding (2026-07-01, session `sess_1782919268_2df8d8_317b`, concurrent dispatch)

A second, independent dispatch on this same phase (R6 concurrent-edit — both sessions landed
commits) reached the SAME [BLOCKED] verdict via a partially overlapping but distinct route, and
made two concrete additions worth preserving:

1. **`intAccessPreorder`/`intAccessPreorder_le_of_isAccessible` (`Scheme.lean`, committed
   `a1883c4e`) — a genuine, real, `lake build`-green `Preorder Nat` instance built from
   `Relation.ReflTransGen (isAccessible edges · · = true)`, sidestepping the need to separately
   prove `isAccessible` itself transitive.** This DOES fulfill the checklist's first task ("Define
   the countermodel `Preorder`... as the RTC of `isAccessible edges`") as *working Lean code*, not
   just analysis — correcting this section's earlier "no Lean files were edited" note (true for the
   FIRST dispatch, not the second). This artifact is a **Preserved Asset for the eventual re-plan**:
   if option (a) above is adopted (revise Postmortem 5, thread a custom `World`/`Preorder` through
   `openBranch_countermodel`/`tableau_complete`), `intAccessPreorder` is exactly the `Preorder`
   instance that re-plan would install.
2. **A second, independent blocker, deeper than the signature-pinning issue, found by attempting
   the monotonicity proof directly against `intAccessPreorder` (documented in-file, no `sorry`,
   at `Scheme.lean` immediately after `intAccessPreorder_le_of_isAccessible`)**: EVEN IF option (a)
   or (b) above is adopted and the signature-pinning issue is resolved, `intExtractValuation`
   monotonicity is SEPARATELY entangled with the B2 fuel-sufficiency argument (Phase 6-10, not yet
   implemented). Verified via source: `intApplyRuleFull` (`Rules.lean:245-268`) maps every
   `T(φ→ψ)` to `.notApplicable` — `T(→)` is handled exclusively by the fuel-bounded
   `applyPersistenceFixpoint`, whose convergence `intStepBranch b e nw = none` does NOT guarantee.
   Atom monotonicity for `T(→)`-triggered atoms co-inductively depends on the antecedent's OWN
   monotonicity, resolved only by repeated fixpoint passes (i.e. by fuel). This means Phase 2's
   monotonicity sub-task has a WAVE-ORDERING inversion (Wave 2 depending on Wave 6) independent of
   the signature question — so option (a)/(b) alone would NOT fully unblock Phase 2; the
   monotonicity discharge itself likely needs folding into Phase 10 (mirroring R3's existing
   anticipated fold for `sat_timp`'s succ-case), regardless of which signature-change route is
   chosen.

**Combined recommendation for the re-plan**: adopt option (a) (or (b)) to resolve the
signature-pinning issue, AND additionally restructure so `intExtractValuation` monotonicity is
NOT a standalone Phase 2 deliverable but a field/hypothesis threaded alongside `sat_timp` (Phase 4)
and discharged only once `measure ≤ fuel` (Phase 10) is available. `intAccessPreorder` remains
directly reusable once the signature question is resolved.

- **Estimated output:** ~300-500 lines (largest foundation phase). If it exceeds ~450 lines, split
  into **2.1** (frame + `Preorder` install + `IValid` instantiation) and **2.2**
  (`intExtractValuation` monotonicity against the dedup expansion), committing each at green.
- **Timing:** 4 hours. **Depends on:** 1.
- **Owned files:** `Scheme.lean` (+ possibly `Minimal/Completeness.lean` if the frame ripples there —
  flag as TERRITORY and commit separately). `Soundness.lean` is READ-ONLY.

---

### Phase 3: Re-thread `truthLemma` / `openBranch_countermodel` / `tableau_complete` over the new frame [NOT STARTED]

- **Goal:** Re-express the three completeness lemmas over the edge-accessibility `Preorder` from
  Phase 2, keeping their public signatures stable. This completes the FOUNDATION; both tracks open
  after it.
- **Tasks:**
  - [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Re-thread `truthLemma` (`Scheme.lean:303`), `openBranch_countermodel` (`Scheme.lean:1314,1336`),
        `tableau_complete` (`Scheme.lean:1360-1368`) so all `∀ w' ≥ w` quantifiers range over
        edge-reachable worlds. Keep the T(→) case (`:330`) as its existing `sorry` for now (Phase 5
        closes it once `sat_timp` exists) — the re-thread must leave exactly the two sorries.
  - [ ] Confirm the already-green F-imp case (`Scheme.lean:333-335`) still type-checks: its
        `sat_fimp` witness `w'` must now witness EDGE-accessibility, not numeric `≤` (report 08
        2nd adversarial challenge). Re-prove that step if needed.
  - [ ] Verify `openBranch_countermodel`/`tableau_complete` public signatures are byte-stable
        (Postmortem 5).
  - [ ] Scoped+grepped build GREEN; two sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 3: re-thread completeness lemmas over edge-accessibility frame`.
- **Estimated output:** ~250-400 lines. **Done when:** the three lemmas build over the new frame with
  stable public signatures and exactly two sorries remain (330 still open, 986 still open).
- **Timing:** 3 hours. **Depends on:** 2.
- **Owned files:** `Scheme.lean`.

---

### Phase 4: [B1] Add `sat_timp` to `IBranchSaturation` + prove it in `IExpandedConsistent_sat` [NOT STARTED]

- **Goal:** Extend `IBranchSaturation` with the T(→) saturation field over the edge relation and
  discharge it in the saturation bridge. The build stays green because the fuel=0 `sorry 986`
  subsumes the new field until Phase 10.
- **Tasks:**
  - [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Add the field (report 08 §Q2), stated over edge-accessibility:
        `sat_timp : ∀ φ ψ w w', T(φ→ψ)@w ∈ b → Accessible w w' → (F(φ)@w' ∈ b ∨ T(ψ)@w' ∈ b)`
        (with `Accessible` = the Phase 2 edge relation, NOT `w ≤ w'`).
  - [ ] Prove `sat_timp` inside `IExpandedConsistent_sat` (`Scheme.lean:563-633`) by mirroring the
        soundness `applyAllTImpRules`/`intTImpRule` argument (`Soundness.lean:353-406`):
        `propagatePersistence` copies `T(φ→ψ)` to `w'`, saturation applies the β split producing
        `F(φ)@w' ∣ T(ψ)@w'`.
  - [ ] **R3 check**: if `intExpandBranches_openBranch_sat`'s SUCC case constructs `IBranchSaturation`
        field-wise (not wholesale from `IExpandedConsistent_sat`), thread `sat_timp` through the succ
        case here too (no measure needed — succ is not fuel=0). Confirm the fuel=0 `sorry 986`
        continues to cover the whole `IBranchSaturation` including the new field, so the build stays
        green with exactly two sorries. If the succ case entangles with the fuel work, STOP and
        recommend folding this phase into Phase 10.
  - [ ] If R8 fired in Phase 2: restate `sat_fimp`'s `w ≤ w'` over the edge relation here.
  - [ ] Scoped+grepped build GREEN; two sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 4: add sat_timp field + discharge in IExpandedConsistent_sat`.
- **Estimated output:** ~200-400 lines. **Done when:** `IBranchSaturation` has `sat_timp`,
  `IExpandedConsistent_sat` discharges it sorry-free, and the build is green with two sorries.
- **Timing:** 3 hours. **Depends on:** 3.
- **Owned files:** `Scheme.lean`. Logically parallel with Phases 6/7; R6-serialized with Phase 7
  (both `Scheme.lean`); truly concurrent-capable only with Phase 6 (`Expansion.lean`).

---

### Phase 5: [B1] Close sorry 330 (T(→) truth-lemma forward case) [NOT STARTED]

- **Goal:** Discharge the T(→) case of `truthLemma` using `sat_timp` over the edge frame. This closes
  B1 and is INDEPENDENT of the entire B2 track.
- **Tasks:**
  - [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Replace the `sorry` at `Scheme.lean:330` with the `sat_timp` discharge (report 08 §Q2 snippet):
        `intro w' hacc hφ'; rcases hsat.sat_timp φ' ψ' w w' a✝ hacc with hF | hT` then
        `exact absurd hφ' ((ih_φ' w').2 hF)` / `exact (ih_ψ' w').1 hT`.
  - [ ] Re-verify the F-imp sibling case still type-checks against the new frame.
  - [ ] Scoped+grepped build GREEN; `grep -n sorry Scheme.lean` → only 986 (B2) remains.
  - [ ] `lean_verify truthLemma` → no `sorryAx`, no new axioms; commit `Scheme.lean` only:
        `task 317 phase 5: close B1 sorry 330 via sat_timp over edge frame`.
- **Estimated output:** ~50-150 lines (incl. F-imp fallout fixes). **Done when:** sorry 330 is gone,
  only 986 remains, `truthLemma` is `sorryAx`-free.
- **Timing:** 1.5 hours. **Depends on:** 3, 4. **Independent of the B2 track** — can complete while
  B2 (Phases 6-9) is still in progress.
- **Owned files:** `Scheme.lean`.

---

### Phase 6: [B2] Raise the fuel formula to `intFuel φ` + audit downstream callers [NOT STARTED]

- **Goal:** Change the fuel from `2^(2*φ.complexity+2)` to `intFuel φ ≈ 3^Θ(c²)` (report 07 §Q4) and
  re-verify every downstream fuel-pinned caller. TERRITORY HAZARD: task 316 (`Expansion.lean` +
  `Soundness.lean`).
- **Tasks:**
  - [ ] `git log -1 -- Expansion.lean Soundness.lean`; scoped+grepped rebuild GREEN.
  - [ ] Define `intFuel φ := 3 ^ (2·(2·φ.complexity+1)·(φ.complexity+2))` (or the exact bound Phase 9
        needs — size it so `intExpMeasure_init_le_fuel` closes with slack, R7). Change the fuel site
        at `Expansion.lean:466` (`intuitionisticTableau`) and the minimal analogue.
  - [ ] **AUDIT** every downstream fuel-pinned caller: `intExpandBranches_closed_unsat`
        (`Soundness.lean`, task 316), `DecisionProcedure.lean`, `Completeness.lean`. The change is
        monotone-safe for the `openBranch → saturated` direction; confirm each caller still builds.
  - [ ] **STOP-gate (R4/TERRITORY 316)**: if a `Soundness.lean` caller needs a non-trivial edit,
        STOP, mark [BLOCKED], escalate for task-316 coordination. If it needs only a mechanical
        re-pin, make the MINIMAL fix and commit `Soundness.lean` in a SEPARATE scoped commit with a
        prominent coordination flag.
  - [ ] Scoped+grepped builds (`Expansion`, then downstream) GREEN; two sorries unchanged; commit
        `Expansion.lean` only (+ separate `Soundness.lean` commit if forced):
        `task 317 phase 6: raise fuel to intFuel (coordinates task 316)`.
- **Estimated output:** ~100-200 lines + audit. **Done when:** the fuel is raised, all downstream
  callers build, task-316 coordination is flagged, two sorries unchanged.
- **Timing:** 2 hours. **Depends on:** 3 (foundation complete, so the audit is against the
  post-frame-change countermodel). **File-disjoint from the B1 `Scheme.lean` track → truly
  concurrent with Phases 4/5.**
- **Owned files:** `Expansion.lean` (+ `Soundness.lean` ONLY if forced, separate commit).

---

### Phase 7: [B2] `intUniverse` + `intWork` + the linear world bound [NOT STARTED]

- **Goal:** Define the fixed finite universe and the counting-against-universe work, and prove the
  linear world bound that bounds the world coordinate of `U`. (Modal-K `FmpMeasure` pattern.)
- **Tasks:**
  - [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Define `intUniverse φ : List (ISF Atom)` (the `(sign, subformula, world)` cells,
        `|U| ≤ 2·(2c+1)·(c+2)`) and `intWork U b e := (U.diff b).length + (U.diff e).length`
        (mirror `modalWork`, `FmpMeasure.lean:180-196`).
  - [ ] Prove `intExpandBranches_world_bound`:
        `(b.map (·.label)).eraseDups.length ≤ φ.complexity + 1` (report 04 F5 / report 07 §Q4 —
        holds with NO dedup; do NOT entangle with the Option-A dedup).
  - [ ] Scoped+grepped build GREEN; two sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 7: intUniverse + intWork + linear world bound`.
- **Estimated output:** ~200-350 lines. **Done when:** `intUniverse`, `intWork`, and
  `intExpandBranches_world_bound` are sorry-free.
- **Timing:** 3 hours. **Depends on:** 3 (foundation). Logically parallel with Phase 4; R6-serialized
  with it (both `Scheme.lean`).
- **Owned files:** `Scheme.lean`.

---

### Phase 8: [B2] `intExpMeasure_step_lt` (per-step strict decrease) [NOT STARTED]

- **Goal:** Prove each `go` step strictly decreases `intExpMeasure` — the hard B2 phase. Handles
  world-creation and persistence via the `|U\b|+|U\e|` decrease, NOT branch complexity.
- **Tasks:**
  - [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Define `intExpMeasure U branches expandedSets := Σ (b,e) ↦ 3 ^ intWork U b e`
        (mirror `modalExpMeasure`).
  - [ ] Prove `intExpMeasure_step_lt`: one `go` step gives
        `intExpMeasure U (done ++ newBs ++ rest) … + 1 ≤ intExpMeasure U (done ++ b :: rest) …`
        (mirror `modalExpMeasure_step_lt`, `FmpMeasure.lean:3018`). A fresh triple leaves `U\b`, so
        the work strictly drops even under persistence.
  - [ ] Scoped+grepped build GREEN; two sorries unchanged; if it exceeds ~450 lines, split into
        **8.1** (the `intExpMeasure` def + linear/non-branching step cases) and **8.2** (the
        world-creating / β-split cases). Commit `Scheme.lean` only:
        `task 317 phase 8: intExpMeasure_step_lt`.
- **Estimated output:** ~300-500 lines (pre-split candidate). **Done when:** `intExpMeasure_step_lt`
  is sorry-free.
- **Timing:** 4 hours. **Depends on:** 7 (uses `intUniverse`/`intWork`).
- **Owned files:** `Scheme.lean`.

---

### Phase 9: [B2] `intExpMeasure_init_le_fuel` (initial measure ≤ raised fuel) [NOT STARTED]

- **Goal:** Prove the initial measure is bounded by the raised fuel, using `|U| = O(c²)` and the
  linear world bound. This is where the fuel-raise pays off (impossible at the old fuel, report 07 §Q2).
- **Tasks:**
  - [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Prove `intExpMeasure_init_le_fuel φ : intExpMeasure (intUniverse φ) [[⟨.neg,φ,0⟩]] [[]] ≤ intFuel φ`
        with SLACK (`≤`, R7). Reuse pure arithmetic helpers `sum_map_le_length_mul` and geometric
        caps (`FmpMeasure.lean:131,776-833`; report 06 R1).
  - [ ] Scoped+grepped build GREEN; two sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 9: intExpMeasure_init_le_fuel`.
- **Estimated output:** ~150-300 lines. **Done when:** `intExpMeasure_init_le_fuel` is sorry-free.
- **Timing:** 2.5 hours. **Depends on:** 6 (uses `intFuel`), 7 (uses `intUniverse`/world bound).
  Logically parallel with Phase 8; R6-serialized (both `Scheme.lean`).
- **Owned files:** `Scheme.lean`.

---

### Phase 10: [B1 ∩ B2 CONVERGENCE] Reformulate `intExpandBranches_openBranch_sat` + close sorry 986 [NOT STARTED]

- **Goal:** The sole serialization point. Add the `intExpMeasure … ≤ fuel` hypothesis to
  `intExpandBranches_openBranch_sat`, discharge the `sat_timp` field it must produce (B1), and close
  sorry 986 — keeping `openBranch_countermodel` public-stable (STOP-gate b).
- **Tasks:**
  - [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Add the `intExpMeasure … ≤ fuel` hypothesis to `intExpandBranches_openBranch_sat`
        (`Scheme.lean:969`). fuel=0 ⟹ measure=0 ⟹ `branches=[]` ⟹ `.openBranch` impossible (copy
        `classicalExpandBranches_hintikka:922-939` verbatim in structure). Thread
        `intExpMeasure_step_lt` (Phase 8) through the succ case.
  - [ ] Discharge the `sat_timp` field (Phase 4) inside `intExpandBranches_openBranch_sat` at the
        fuel=0 close (the produced `IBranchSaturation` now includes `sat_timp` — supply it from the
        saturation reached at fuel=0, consistent with `IExpandedConsistent_sat`).
  - [ ] **STOP-gate b**: supply the measure bound INTERNALLY at the `openBranch_countermodel` call
        site from `intExpMeasure_init_le_fuel` (Phase 9), threading through a `private` `_aux`/`key`
        so `openBranch_countermodel`/`tableau_complete`/`Decidable` public signatures stay byte-stable.
        If the hypothesis cannot be discharged internally, STOP/[BLOCKED] — do NOT change a public
        signature.
  - [ ] Scoped+grepped build GREEN; `grep -n sorry` over the four Intuitionistic tableau files →
        NOTHING. `lean_verify intExpandBranches_openBranch_sat` + `openBranch_countermodel` +
        `tableau_complete` → no `sorryAx`, no new axioms.
  - [ ] Commit `Scheme.lean` only:
        `task 317 phase 10: close B2 sorry 986 via measure ≤ fuel + discharge sat_timp`.
- **Estimated output:** ~150-300 lines. **Done when:** sorry 986 is gone, the completeness is
  sorry-FREE, public signatures are byte-stable, `lean_verify` is clean.
- **Timing:** 3 hours. **Depends on:** 4 (final `IBranchSaturation`/`sat_timp` shape), 8
  (`step_lt`), 9 (`init_le_fuel`). Transitively 3, 6, 7.
- **Owned files:** `Scheme.lean`.

---

### Phase 11: Add load-bearing BibKeys [NOT STARTED]

- **Goal:** Add the citations the Phase 4/8/9 docstrings rely on to `references.bib`.
- **Tasks:**
  - [ ] `git log -1 -- references.bib`; confirm `GargGenoveseNegri2012`, `DershowitzManna1979`,
        `Negri2001` (Negri & von Plato), `Troelstra2000` are ABSENT and
        `Fitting1983`/`ChagrovZakharyaschev1997`/`TroelstraSchwichtenberg2000` are PRESENT.
  - [ ] Append the load-bearing entries (`GargGenoveseNegri2012` for the dedup docstring;
        `DershowitzManna1979` for the measure ordering; `Negri2001`/`Troelstra2000` for the frame /
        `sat_timp` citations).
  - [ ] Confirm the proof-comment BibKeys now resolve; commit `references.bib` only:
        `task 317 phase 11: add load-bearing BibKeys`.
- **Estimated output:** ~20-40 lines. **Done when:** the cited keys resolve.
- **Timing:** 0.5 hours. **Depends on:** 10.
- **Owned files:** `references.bib`.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"` → Build completed.
- [ ] Scoped builds of `Expansion` and (if touched) `Soundness` GREEN.
- [ ] `grep -rn sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/` → NOTHING (both 330 and 986 closed).
- [ ] `openBranch_countermodel`, `tableau_complete`, and `Decidable`/`DecisionProcedure` public signatures byte-identical to baseline.
- [ ] `lean_verify` on `truthLemma`, `intExpandBranches_openBranch_sat`, `openBranch_countermodel`,
      `tableau_complete`, `intExpMeasure_step_lt`, `intExpMeasure_init_le_fuel`,
      `intExpandBranches_world_bound` → no `sorryAx`, no new axioms.
- [ ] `Soundness.lean` (task 316) unchanged in the diff, or (if the fuel-raise forced a re-pin) in a
      SEPARATE scoped commit with a coordination note.
- [ ] Diff contains only `Scheme.lean`, `Expansion.lean`, `references.bib` (+ `Soundness.lean` /
      `Minimal/Completeness.lean` / `Completeness.lean` only where a phase explicitly flagged it) —
      never `git add -A`.
- [ ] Full CI smoke (only if context budget allows; else defer to /vet): `lake test`,
      `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`.

## Artifacts & Outputs

- `specs/317_propositional_tableau_completeness/plans/05_frame-change-and-fuel-raise.md` (this file)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (edge-accessibility
  frame; `intExtractValuation` monotonicity; `sat_timp` field; sorry 330 closed; `intUniverse`/
  `intWork`/`intExpMeasure`/world bound; `intExpMeasure_step_lt`/`intExpMeasure_init_le_fuel`;
  `intExpandBranches_openBranch_sat` reformulated; sorry 986 closed)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (fuel raised to
  `intFuel`; possibly a Phase-1 edge accessor)
- Modified: `references.bib` (`GargGenoveseNegri2012`, `DershowitzManna1979`, `Negri2001`, `Troelstra2000`)
- Possibly modified (flag + separate commit if so): `Intuitionistic/Soundness.lean` (task 316 —
  fuel re-pin only), `Minimal/Completeness.lean`, `Intuitionistic/Completeness.lean`
- Downstream effect: task 430 (atom-persistence upward closure) is RESHAPED by the frame change and
  must be re-planned (Roadmap Alignment); task 375 gated on 430 + this completeness-green.
- `specs/317_propositional_tableau_completeness/summaries/05_frame-change-and-fuel-raise-summary.md` (on completion)

## Rollback/Contingency

- Each phase commits at GREEN; `git revert` a phase commit if it regresses. The chain
  1→2→3→{4,6,7}→{5,8,9}→10→11 peels back cleanly to the `4202d1df`/`8a5c0250` Preserved-Asset green
  state (two sorries).
- **R1 escalation (Phase 2, STOP-gate a)**: if the frame cannot be installed without editing task-316
  `Soundness.lean`, mark Phase 2 [BLOCKED], leave both sorries intact, hand off the exact resisting
  lemma. The whole plan is gated on the frame — a clean [BLOCKED] here is the correct escalation.
- **R2 escalation (Phase 10, STOP-gate b)**: if the `measure ≤ fuel` hypothesis cannot be supplied
  internally without a public-signature change, mark Phase 10 [BLOCKED] and hand off — do NOT change
  `openBranch_countermodel`/`tableau_complete`/`Decidable` signatures.
- **R3 escalation (Phase 4)**: if adding `sat_timp` entangles the succ case with the fuel work, fold
  the field addition into Phase 10 rather than leaving a broken intermediate.
- **R4 escalation (Phase 6, TERRITORY 316)**: if the fuel-raise needs a non-trivial `Soundness.lean`
  edit, STOP/[BLOCKED]/escalate for task-316 coordination.
- **Overflow contingency (R5)**: a committed green partial (with the two-sorry state preserved) + a
  sharp handoff (which lemma is stated, its goal state, what remains) is the success criterion for an
  interrupted run. Phases 2, 3, 8 are pre-split candidates.
- Never pursue Option B (unsound) and never revert the Option-A dedup under any contingency.
