# Implementation Plan: Task #317 (v6 — Route (a) frame plumbing + report-07 fuel raise for sorry-FREE intuitionistic tableau completeness, HARD mode)

- **Task**: 317 - Close the residual intuitionistic completeness-chain sorries to reach a sorry-FREE intuitionistic (and minimal) tableau completeness, by un-pinning the completeness frame off the global `Nat` total preorder (Route (a)) and then raising the fuel (report 07).
- **Status**: [NOT STARTED]
- **Effort**: 24 hours
- **Dependencies**: 316 (soundness, landed — TERRITORY HAZARD, `Soundness.lean` + `Expansion.lean` fuel site, read-only unless Phase 5 forces a fuel re-pin). Downstream: 430 (atom-persistence upward closure — RESHAPED by this plan's frame change, re-plan after Wave A) then 375 (proof-system TFAE edges, gated on 430 + this completeness green). See Roadmap Alignment.
- **Research Inputs**:
  - `specs/317_propositional_tableau_completeness/reports/09_phase2-escape-routes.md` (PRIMARY — ground truth. VERDICT: Route (a) un-pin the frame via `intAccessPreorder edges`; Route (b) redefining `IForces` REJECTED. Decisive new fact: Route (a) public blast radius is ~zero — `instDecidableIValid` discharges via `intuitionisticTableau_complete`, NOT the countermodel lemma; the countermodel lemmas have no live code consumer. Route (a) is NECESSARY BUT NOT SUFFICIENT — must combine with report-07 fuel raise; ≈9-11 phases across ≥2 waves.)
  - `specs/317_propositional_tableau_completeness/reports/07_option-b-fuel-bound.md` (SUPPORTING — fuel raise: fuel counts expansion STEPS = the `2^Θ(c²)` β-forest, which dedup does NOT shrink; fix = RAISE fuel + `measure ≤ fuel` hypothesis mirroring `classicalExpandBranches_hintikka` / Modal-K `FmpMeasure`. Option B UNSOUND.)
  - `specs/317_propositional_tableau_completeness/reports/08_b1-truthlemma-timp.md` (SUPPORTING — frame-change necessity: the T(→) truth-lemma case is LITERALLY FALSE over `(ℕ,≤)`; add `sat_timp` field + `intExtractValuation` monotonicity over the edge relation.)
- **Superseded plan (reference only; do NOT revert its landed work)**: `plans/05_frame-change-and-fuel-raise.md` — [BLOCKED] at Phase 2 STOP-gate R1. v6 supersedes it by ADOPTING option (a) from v5's Phase-2 STOP-gate finding (a deliberate, audited signature change on the internal countermodel lemmas), per report 09's Route (a) verdict. v5's Phase 1 [COMPLETED] and its `intAccessPreorder` artifact are Preserved Assets (see below).
- **Artifacts**: `plans/06_route-a-frame-plumbing.md` (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md (CSLib zero-debt)
- **Type**: cslib
- **Lean Intent**: true

## Overview

Plan v5 reached a hard [BLOCKED] at Phase 2: the byte-stable-signature Postmortem Constraint 5 pinned
`IForces`'s `World` type-class argument to `Nat`'s **global, total** `Preorder` instance, over which
the T(→) truth-lemma obligation and the `intExtractValuation` monotonicity obligation are not merely
hard but **literally false** (a total order cannot represent the tree/DAG accessibility that general
intuitionistic completeness needs). Report 09 adversarially resolved the escape-route question:

**Route (a) — un-pin the completeness frame.** Restate the INTERNAL `openBranch_countermodel` and its
two `*OpenBranch_countermodel` corollaries over the already-built `intAccessPreorder edges` instance of
the **existing** `IForces` (do NOT redefine `IForces` — Route (b) is REJECTED). `intAccessPreorder`
(`Relation.ReflTransGen (isAccessible edges · ·)`) and `intAccessPreorder_le_of_isAccessible` already
exist and are green (commit `a1883c4e`, `Scheme.lean:309-323`), built precisely to replace
`Nat.instPreorder` with edge-reachability.

**Public blast radius is ~zero (report 09's decisive H4-verified fact).** `instDecidableIValid`
(`DecisionProcedure.lean:105-111`) discharges its `.openBranch` case via `intuitionisticTableau_complete`
(the `IValid φ → .closed` arrow), **not** the countermodel lemma. The countermodel lemmas have **no
live code consumer** (grep: docstrings only). So the signature Route (a) must change is consumed by
nothing; the STABLE PUBLIC CONTRACT (`tableau_complete`/`minimalTableau_complete`, `Decidable (IValid φ)`,
`Decidable (Derivable IntPropAxiom φ)`, and every DecisionProcedure consumer) does NOT move.

**Route (a) is NECESSARY BUT NOT SUFFICIENT.** It converts both blockers from *false-at-the-global-
preorder* to *true-in-principle-but-fuel-entangled*: the T(→) discharge (now over `sat_timp`) and the
`intExtractValuation` monotonicity discharge both need the returned branch to be a genuine persistence
fixpoint, which requires the **raised fuel** of report 07. So v6 = Route (a) frame plumbing (Wave A) ∪
report-07 fuel machinery (Wave B). **This is NOT one wave** (≈9-11 H8-phases, ~1700-3400 lines).
**Wave A lands independently**, threading `intExtractValuation` monotonicity and the new `sat_timp`
field as EXPLICITLY-DEFERRED obligations discharged by Wave B.

**Definition of done**: the four Intuitionistic-tableau files build GREEN and sorry-FREE
(`grep -n sorry` returns nothing); no new `axiom`/`sorry`/vacuous def; the STABLE PUBLIC CONTRACT stays
byte-stable (only the internal countermodel-lemma family restates over the edge preorder, per the
Postmortem-5 revision below); `Soundness.lean` (task 316) edited only where the fuel-raise strictly
forces it, in a separate scoped commit.

### Research Integration

- **Report 09 (PRIMARY, Tier 1 + Tier 3, H4-verified)** supplies the Route decision and the exact
  blast-radius accounting. Key facts adopted as ground truth: (a) Route (a) over `intAccessPreorder`,
  Route (b) rejected (category error, ~205 `IForces` refs across 13 green files at risk, zero
  second-blocker benefit); (b) the countermodel lemmas have no live consumer, so their signature change
  is safe and the public contract is stable; (c) Route (a) is necessary-but-not-sufficient — the second
  blocker (monotonicity + `sat_timp`) still needs the report-07 fuel fixpoint; (d) ≥2 waves.
- **Report 07 (SUPPORTING, Tier 1 + Tier 3, H4-verified)** supplies the fuel-raise mechanism: fuel =
  total expansion-forest node count (`2^Θ(c²)`), NOT deduplicated model size; the transferable measure
  is the Modal-K `FmpMeasure` counting-against-fixed-universe pattern (`|U\b|+|U\e|`, `Σ 3^work`)
  requiring fuel `~3^Θ(c²)`; Option B is UNSOUND; literal `sat_fimp` needs no reformulation.
- **Report 08 (SUPPORTING, Tier 1 + Tier 3, H4-verified)** supplies the frame-change necessity: sorry
  T(→) is false over `(ℕ,≤)`; fix = accessibility must be edge-reachability, add `sat_timp` (saturation
  dual of `intTImpRule`/`applyAllTImpRules`) + prove `intExtractValuation` monotone along edges; keep
  the full two-direction truth lemma.

#### Source-to-Implementation Mapping (Tier 1 — MANDATORY for this literature-backed task)

| Source claim | BibKey (references.bib status) | Lean target (file:line, HEAD) | Translation notes |
|---|---|---|---|
| Countermodel accessibility = reflexive-transitive closure of the relational atoms on the OPEN BRANCH over the finite set of branch labels — never the ambient carrier order | **NegriVonPlato2001** — **ABSENT** (load-bearing for Route (a)'s frame; add in Phase 11) | `intAccessPreorder = Relation.ReflTransGen (isAccessible edges · · = true)` (`Scheme.lean:309-313`, committed `a1883c4e`) | This IS Route (a). The preserved asset already encodes the Negri–von Plato frame. The bug was applying `IForces` at the global `Nat.instPreorder` (total). Phases 1-4 restate over `intAccessPreorder`. |
| Countermodel worlds = saturated (prime) sets ordered by inclusion; adequacy is a simultaneous both-signs induction; `→`-clause discharged by persistence across the order | **TroelstraSchwichtenberg2000** — **PRESENT** | `truthLemma` mutual T/F induction (`Scheme.lean:382-444`); T-imp sorry (`:409`) | The mutual induction means the externally-consumed F-direction transitively needs the T-direction; a one-sided F-only lemma cannot dodge the frame (report 08 Q4). Phase 1 re-threads; Phase 9 closes T-imp via `sat_timp`. |
| Intuitionistic tableau: persistent `T(A→B)` rule reapplied at every accessible world; model frame = branch world-creation tree | **Fitting1983** — **PRESENT** (`Scheme.lean:244,1398`) | `intTImpRule`/`applyAllTImpRules` (`Soundness.lean:353-406`); proposed `sat_timp` field | Rule exists on the SOUNDNESS side over `edges`; completeness needs its saturation dual as a new `IBranchSaturation.sat_timp` field, stated over `isAccessible` (Phase 9). |
| Persistence of forcing under the preorder (Prop 2.1) — the property `IForces` must preserve for a legal model | **ChagrovZakharyaschev1997** — **PRESENT** | `iforces_persistence` (`Kripke.lean:125-140`) | Its imp-case uses `le_trans` — this is exactly why Route (b) (redefining `IForces`) breaks it; Route (a) plugs a custom `Preorder` INSTANCE into the unchanged `IForces`, so `iforces_persistence` is reused, not re-proved. |
| Counting-against-fixed-universe measure gives strict decrease despite persistence; fuel must cover the `2^Θ(c²)` forest | **GargGenoveseNegri2012** (dedup docstring) / **DershowitzManna1979** (measure ordering) — **BOTH ABSENT** (add in Phase 11) | Modal-K `FmpMeasure.lean:131,776-833,3018`; v6 `intUniverse`/`intWork`/`intExpMeasure` (Phases 6-8) | `modalWork U b e = |U\b|+|U\e|`, `modalExpMeasure = Σ 3^work` — a PROVEN repo pattern. Requires the RAISED fuel `intFuel φ ≈ 3^Θ(c²)`. |
| `measure ≤ fuel` hypothesis threaded into the saturation lemma closes the `fuel=0` case | `classicalExpandBranches_hintikka` (`Classical/Completeness.lean:906-939`, in-repo) | `intExpandBranches_openBranch_sat` fuel-0 sorry (`Scheme.lean:1070`) | fuel=0 ⟹ measure=0 ⟹ `branches=[]` ⟹ `.openBranch` impossible. Supply the bound INTERNALLY (Phase 10) so the public contract stays stable. |

**BibKey status** (report 09, grep-verified against `references.bib`): `ChagrovZakharyaschev1997`,
`Fitting1983`, `TroelstraSchwichtenberg2000` **PRESENT**. `NegriVonPlato2001` (load-bearing for the
Route (a) frame citation), `GargGenoveseNegri2012`, `DershowitzManna1979` **ABSENT** — Phase 11 adds
the load-bearing ones (chiefly `NegriVonPlato2001`).

### Prior Plan Reference (plan v5) and the Postmortem-5 revision

Plan v5 chose "keep byte-stable signatures" and hit a hard [BLOCKED]: the Phase-2 STOP-gate finding
(`plans/05...md:329-394`) proved that the byte-stable countermodel signatures pin `IForces`'s `World`
to `Nat`'s global total preorder, over which the obligations are literally false. v5's own recommended
resolution (option (a): a deliberate, audited signature change on `openBranch_countermodel`/its
corollaries, revising Postmortem 5) is exactly what report 09 confirms as Route (a) with ~zero blast
radius. v6 adopts it.

**PLAN-LEVEL POSTMORTEM-CONSTRAINT CHANGE (recorded explicitly, with justification).**
Postmortem Constraint 5 of plan v5 ("do NOT change any PUBLIC signature — `openBranch_countermodel`,
`tableau_complete`, and any `Decidable` consumer byte-stable") is **REVISED** in v6 as follows:

- **What changes**: the internal countermodel-lemma family — `openBranch_countermodel` (the shared
  parametric lemma, `Scheme.lean:1399`) and its two corollaries `intuitionisticOpenBranch_countermodel`
  (`Completeness.lean:87`) and `minOpenBranch_countermodel` (`Minimal/Completeness.lean:93`) — MAY have
  their stated **conclusion** moved from `@IForces Nat _ Nat.instPreorder …` to
  `∃ edges, ¬ @IForces Nat _ (intAccessPreorder edges) …`. These are the two internal corollaries plus
  their shared parent; all three have **no live code consumer** (report 09 §a.1, grep-verified:
  docstrings only).
- **What stays LOCKED (the stable public contract, unchanged from v5)**:
  `tableau_complete`/`minimalTableau_complete` (`IValid/MValid φ → .closed`), `Decidable (IValid φ)`,
  `Decidable (Derivable IntPropAxiom φ)`, `instDecidableIValid`, and every DecisionProcedure consumer
  remain **byte-stable**.
- **Justification (zero-debt)**: the old global-preorder conclusion is *literally false* → closable
  only by `sorry`; the revision is the sorry-*removing* change, adds no `axiom`/`sorry`/vacuous def,
  leaves the public contract and all soundness/FMP/strong-completeness/algebra-bridge code untouched
  (Route (a) never touches `IForces`/`iforces_persistence`/`IValid`/`MValid`), and is the standard,
  cited Negri–von Plato construction. This is a principled, minimal, one-time revision — NOT churn (it
  removes sorries, it does not thrash a stable interface).

### Roadmap Alignment

No ROADMAP.md found. Downstream chain: this plan's completeness-green unblocks **task 430**
(atom-persistence upward closure), which unblocks **task 375** (proof-system TFAE edges).

**Coordination note (flag only — do NOT plan 430/375 here)**: task 430 reasons about
`intExtractValuation` upward-closure *under the accessibility relation*. This plan's `≤` →
`intAccessPreorder` frame change **directly RESHAPES 430's argument**: 430 must re-base its
upward-closure onto the same edge-reachability frame installed in Wave A, and must account for the
Option-A dedup's converging-witness structure. **Task 375 (TFAE edges) is GATED on 317 completeness
green.** BOTH 430 and 375 should be RE-PLANNED **after Wave A lands** (frame installed, Phases 1-4),
with 430 additionally consuming Wave B's `intExtractValuation` monotonicity (Phase 9).

## Preserved Assets (do NOT recreate or revert — build on these)

The following work is COMPLETE and must not regress:

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| **v5 Phase 1: branch `edges` exposed at the `.openBranch` boundary** (private lemma conclusion widened `IBranchSaturation Atom b` → `∃ edges : IEdges, IBranchSaturation Atom b`; `openBranch_countermodel` call site updated to `obtain ⟨edges, hsat⟩`) | `Scheme.lean` | [COMPLETED] | v5 P1, commit d6d78714-lineage |
| **`intAccessPreorder` + `intAccessPreorder_le_of_isAccessible`** — a real `lake build`-green `Preorder Nat` from `Relation.ReflTransGen (isAccessible edges · · = true)` (the exact frame Route (a) installs) | `Scheme.lean:309-323` | [COMPLETED] | commit `a1883c4e` |
| Committed Option-A dedup `intFImpReuseWitness?` (SOUND; requires explicit `F(ψ)@x` on reuse) | `Expansion.lean` | [COMPLETED] | commit `4202d1df` |
| Soundness fix `intExpandBranches_closed_unsat` for the dedup reuse case | `Intuitionistic/Soundness.lean` (task 316) | [COMPLETED] | commit `8a5c0250` |
| Phase-1-v3 `IAllConsistent`/`IExpandedConsistent`/`ILabelBound` invariant + monotonicity combinators; B2 `none` case closed | `Scheme.lean` | [COMPLETED] | plan 03 P1, commit `26508fe9` |
| `IExpandedConsistent_sat` bridge (`intStepBranch = none` + invariant → `IBranchSaturation`) | `Scheme.lean:563-633` | [COMPLETED] | sorry-free (`sat_timp` field added in Phase 9) |
| Existing 5 `IBranchSaturation` fields incl. literal `sat_fimp` (no reformulation needed) | `Scheme.lean:72-99` | [COMPLETED] | sorry-free |
| Soundness-side frame machinery `isAccessible`, `MonotoneEdges`, `IEdges`, `intTImpRule`, `applyAllTImpRules` | `Soundness.lean:344-406` | [COMPLETED] | reuse target (read-only) for Phases 1-4, 9 |
| `propagatePersistence`, `applyPersistenceFixpoint`, `posFormulasAt` | `Expansion.lean:122-139,199,245` | [COMPLETED] | reuse for `sat_timp` + monotonicity (Phase 9) |
| Classical template `classicalExpMeasure`/`classicalExpandBranches_hintikka` | `Classical/Completeness.lean:636,906-939` | [COMPLETED] | reference-only for Phases 7-10 |
| Modal-K `FmpMeasure` counting-against-universe template | `Modal/Tableau/FmpMeasure.lean:131,776-833,3018` | [COMPLETED] | reference-only for Phases 6-8 (task 442) |
| Calculus soundness | `Intuitionistic/Soundness.lean` (task 316) | [COMPLETED] | TERRITORY HAZARD — read-only unless Phase 5 forces a fuel re-pin |

**Current sorry inventory (report 09, verified at HEAD)** — v6 must reduce this to zero without
introducing any new sorry:
1. `Scheme.lean:409` — `truthLemma` T-imp (closed Phase 9 via `sat_timp` over the edge frame).
2. `Scheme.lean:1070` — `intExpandBranches_openBranch_sat` fuel-0 base case (closed Phase 10 via `measure ≤ fuel`).
3. `Completeness.lean:113` — validity→forcing bridge (closed Phase 10 via monotonicity discharge).
4. `Minimal/Completeness.lean:110` — validity→forcing bridge (closed Phase 10, mirror).

Plus the documented STOP-gate note (`Scheme.lean:326-367`, no sorry) — superseded by this plan.

## Goals & Non-Goals

**Goals**:
- **Wave A (frame plumbing, lands independently)**: re-thread `truthLemma` over `intAccessPreorder`;
  restate `openBranch_countermodel` and its two `*OpenBranch_countermodel` corollaries over the edge
  preorder (the Postmortem-5-revised internal signatures); instantiate `IValid`/`MValid` at the edge
  preorder in the public `*Tableau_complete` lemmas via a private bridge that carries the
  `intExtractValuation` monotonicity as a DEFERRED premise; keep the stable public contract byte-stable.
- **Wave B (fuel machinery + deferred discharge)**: raise the fuel to `intFuel φ ≈ 3^Θ(c²)`; add
  `intUniverse`/`intWork`/`intExpMeasure` + the linear world bound; prove `intExpMeasure_step_lt` and
  `intExpMeasure_init_le_fuel`; add `sat_timp` + discharge it and `intExtractValuation` monotonicity via
  the fuel fixpoint (closing sorry 1); reformulate `intExpandBranches_openBranch_sat` with `measure ≤
  fuel` (closing sorries 2-4); reach sorry-FREE.
- Add the load-bearing BibKeys (chiefly `NegriVonPlato2001`) to `references.bib`.

**Non-Goals**:
- **Route (b)** — redefining `IForces` in `Kripke.lean` — REJECTED (report 09): category error, ~205
  refs across 13 green files at risk, zero second-blocker benefit. Do NOT touch `IForces`,
  `iforces_persistence`, `IValid`, or `MValid` DEFINITIONS.
- **Option B** (append `F(ψ)@x` on reuse) — UNSOUND (report 07 §Q1).
- **Reformulating `sat_fimp`** or the Hintikka condition; **a one-sided F-only truth lemma**; **reverting
  the Option-A dedup**; **keeping the fuel fixed** — all rejected by reports 07/08/09.
- **Implementing task 430 / 375** — flag the frame-change reshaping (Roadmap Alignment); do NOT plan them here.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **R1 (frame instantiation at the edge preorder is subtler than report 09's sketch).** Installing `@IForces Nat _ (intAccessPreorder edges)` where the conclusion previously used `Nat.instPreorder` may surface elaboration/defeq friction (the two `Preorder Nat` instances are not defeq). | H | M | Phase 2 restates the conclusion with the `intAccessPreorder edges` instance made EXPLICIT (`@IForces`), never relying on instance search. `intAccessPreorder` is a committed green asset; `intAccessPreorder_le_of_isAccessible` bridges raw edge witnesses to `≤`-reachability. If a case still resists using ONLY completeness-side edits + read-only soundness machinery, STOP/[BLOCKED] and hand off the exact resisting subgoal — do NOT reach for Route (b). |
| **R2 (second-blocker entanglement — monotonicity/`sat_timp` are fuel-dependent).** Report 09 §a.2: even over the edge frame, monotonicity and `sat_timp` need a genuine persistence fixpoint = raised fuel. A naive attempt to discharge them in Wave A will fail. | H | H | Wave A THREADS both as explicitly-deferred obligations — `sat_timp` is NOT added as a field until Phase 9; monotonicity is carried as a `private`-bridge premise (Phase 4) discharged only in Phase 10. Wave A keeps the four existing sorries (re-stated over the edge frame where relevant); it introduces NO new sorry. |
| **R3 (adding `sat_timp` to `IBranchSaturation` breaks the green `IExpandedConsistent_sat`).** The field must be discharged wherever `IBranchSaturation` is constructed sorry-free. | M | M | Phase 9 adds the field AND discharges it in `IExpandedConsistent_sat` in the SAME phase, using the fuel fixpoint (Phase 7) — never leaving a broken intermediate. If the succ-case construction entangles, fold the field discharge into Phase 10 (convergence). |
| **R4 (STOP-gate b): the `measure ≤ fuel` reformulation changes `intExpandBranches_openBranch_sat`'s type, rippling into the countermodel lemmas' proofs.** | H | M | Phase 10 supplies the measure bound INTERNALLY from `intExpMeasure_init_le_fuel` through a `private` `_aux`/`key`, so the countermodel lemmas' (already Postmortem-5-revised) conclusions do not gain the hypothesis. STOP-gate: if it cannot be discharged internally, STOP/[BLOCKED]. |
| **R5 (TERRITORY 316): the fuel-raise (Phase 5) edits `Expansion.lean:466` and downstream fuel-pinned callers (`intExpandBranches_closed_unsat` in `Soundness.lean`, `DecisionProcedure.lean`, `Completeness.lean`).** | H | M | Phase 5 audits every downstream caller; the change is monotone-safe for the `openBranch → saturated` direction. Commit `Expansion.lean` (+ any forced `Soundness.lean`) in a SEPARATE scoped commit with a prominent 316 coordination flag. Non-trivial soundness edit → STOP/[BLOCKED]/escalate. |
| **R6 (anti-overflow): context overflow on the large recursive proofs (frame re-thread, `step_lt`, monotonicity).** Prior dispatches overflowed. | H | H | Scoped+grepped builds only; `offset`/`limit` windowed reads; `lean_multi_attempt` over `lean_goal` dumps; commit at every green; stop-and-handoff the instant context tightens. Phases 2, 7, 9 are pre-split candidates. |
| **R7 (concurrent-edit): multiple live orchestrator sessions edit `Scheme.lean`/`Expansion.lean` (v5 Phase 2 saw two concurrent dispatches land commits `a1883c4e` alongside another).** | M | H | Single-writer-per-file (Postmortem 7): `git log -1 -- <file>` + scoped rebuild GREEN before EACH phase; commit ONLY touched files (never `git add -A`); never run two `Scheme.lean` writers concurrently — the wave table's parallelism is realized ONLY where files are disjoint (Phase 5 `Expansion.lean` vs a Scheme.lean phase). |
| **R8: fuel/measure arithmetic off by a factor** (`intFuel φ ≈ 3^Θ(c²)` vs `|U| = O(c²)`). | M | M | Phase 8 proves `intExpMeasure_init_le_fuel` with SLACK (`≤`); reuse `FmpMeasure.lean`'s geometric caps. If loose, widen `intFuel` — a fresh formula with no external consumer. |

## Postmortem Constraints (HARD — every phase MUST obey)

Items 1-4, 6 carried forward VERBATIM from plan v5 (still valid). **Item 5 is the REVISED
signature constraint** (see the plan-level constraint change above). Item 7 is NEW (concurrent-edit).

**Do NOT**:
1. **ANTI-OVERFLOW (R6).** Never run a raw full `lake build`. Build scoped + grepped ONLY:
   `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"`
   (swap the module for `Expansion`/`Soundness`/`Completeness`/`Minimal.Completeness` when those are the
   edited file). Read with `offset`/`limit` around the target line ONLY — never whole-file reads of
   `Scheme.lean`/`Expansion.lean`/`Soundness.lean`. Prefer `lean_multi_attempt` over repeated
   `lean_goal` dumps. STOP and write a sharp handoff the instant context feels tight — a committed
   green partial IS success.
2. **Do NOT `git add -A`.** Commit only the files a phase actually touched. `git log -1 -- <file>`
   before each phase (R7 concurrent-edit).
3. **Do NOT introduce any `sorry`, `axiom`, or vacuous/placeholder def.** If a phase cannot close
   sorry-free, mark it [BLOCKED] and hand off (ZERO-DEBT). The only acceptable end states with sorries
   present are strictly BETWEEN phases (the four inventory sorries persist through Wave A; sorry 1 closes
   Phase 9; sorries 2-4 close Phase 10).
4. **Do NOT edit `Soundness.lean` (task 316)** unless Phase 5's fuel-raise strictly forces a fuel-pinned
   caller fix; if so, flag task-316 coordination PROMINENTLY and commit `Soundness.lean` in a SEPARATE
   scoped commit. Non-trivial soundness edits → STOP/[BLOCKED]/escalate.
5. **(REVISED — Route (a) signature un-pin, see plan-level change above.)** The internal countermodel
   family — `openBranch_countermodel`, `intuitionisticOpenBranch_countermodel`, `minOpenBranch_countermodel`
   — MAY move its conclusion to the `intAccessPreorder edges` instance (the intended Route (a) change).
   The STABLE PUBLIC CONTRACT — `tableau_complete`/`minimalTableau_complete` (`IValid/MValid φ → .closed`),
   `Decidable (IValid φ)`, `Decidable (Derivable IntPropAxiom φ)`, `instDecidableIValid`, and every
   DecisionProcedure consumer — MUST stay byte-stable. Thread any new internal hypotheses (measure bound,
   monotonicity) through `private` `_aux`/`key` helpers so the public contract never gains a premise.
   **Do NOT** extend the signature change beyond these three internal lemmas.
6. **Do NOT weaken any countermodel / saturation / soundness lemma** to force a case through. In
   particular, keep the full two-direction `truthLemma`.
7. **(NEW) SINGLE-WRITER-PER-FILE (R7).** Given concurrent live sessions, never run two writers on the
   same file at once. B1/B2 `Scheme.lean` phases serialize even when logically parallel; only genuinely
   file-disjoint phases (Phase 5 `Expansion.lean` vs a Scheme.lean phase) may run concurrently. Re-verify
   `git log -1 -- <file>` and a scoped GREEN build at the START of every phase.

**MUST preserve**:
- All Preserved Assets above (v5 Phase 1 edge exposure, `intAccessPreorder`, the Option-A dedup, the
  `IAllConsistent` invariant machinery, `IExpandedConsistent_sat`, the closed B2 `none` case, the
  soundness fix, calculus soundness).
- The green build at every commit boundary (the four inventory sorries until closed in-phase).

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **Route (a)** — un-pin the frame via `intAccessPreorder edges` on the EXISTING `IForces`. **Route (b)**
  (redefining `IForces`) is REJECTED (report 09): ~205 refs / 13 green files at risk, zero second-blocker
  benefit, semantic-primitive corruption.
- **RAISE the fuel** to cover the `2^Θ(c²)` forest (report 07). Option B is UNSOUND; the fixed fuel
  cannot bound the forest.
- **Frame = edge-reachability** (`intAccessPreorder`), NOT numeric `≤` (reports 08/09).
- **Keep the literal `sat_fimp`** and the full two-direction truth lemma.
- **Add `sat_timp`** as the saturation dual of `intTImpRule`/`applyAllTImpRules`, stated over `isAccessible`.
- **Use the counting-against-fixed-universe measure** (`|U\b|+|U\e|`, `Σ 3^work`; Modal-K `FmpMeasure`).
- **Do NOT revert the Option-A dedup** — sound, committed, now an optional refinement.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5, 6 | 4 |
| 6 | 7, 8 | P7: 6 · P8: 5, 6 |
| 7 | 9 | 4, 7 |
| 8 | 10 | 8, 9 |
| 9 | 11 | 10 |

**Wave grouping**: Wave A = Phases 1-4 (Route (a) frame plumbing, B2-INDEPENDENT, lands independently).
Wave B = Phases 5-11 (report-07 fuel machinery + discharge of the two deferred Wave-A obligations).

**Parallelism / serialization (R7 single-writer-per-file)**:
- **Wave A (Phases 1-4)** is strictly serial: 1-2, 4 are `Scheme.lean` edits causally chained
  (re-thread `truthLemma` → restate `openBranch_countermodel` → instantiate `IValid`/`MValid`); Phase 3
  edits the two Completeness modules and depends on the Phase-2 restated parent.
- **Wave 5**: Phase 5 (`Expansion.lean`, fuel raise) and Phase 6 (`Scheme.lean`, `intUniverse`) are
  FILE-DISJOINT → truly concurrent-capable.
- **Wave 6**: Phases 7 and 8 are both `Scheme.lean` — LOGICALLY parallel (7 uses `intUniverse`/`intWork`;
  8 uses `intFuel`+`intUniverse`) but R7-SERIALIZED (pick one Scheme.lean writer at a time).
- **Convergence**: Phase 10 (reformulate `intExpandBranches_openBranch_sat`, close sorries 2-4) is the
  SOLE serialization point — it depends on the completed measure work (Phase 8) and the discharged
  deferred obligations (Phase 9).

---

### Phase 1: [Wave A] Re-thread `truthLemma` over the `intAccessPreorder` edge frame [NOT STARTED]

- **Goal:** Re-express `truthLemma`'s `∀ w' ≥ w` quantifiers to range over `intAccessPreorder`-reachable
  worlds (via `intAccessPreorder_le_of_isAccessible`), re-proving the non-imp cases and the already-green
  F-imp case over the edge relation. The T-imp case (`Scheme.lean:409`) STAYS as its existing sorry —
  now stated over edge accessibility — deferred to Phase 9 (`sat_timp`). No sorry closed here.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN at HEAD. Reconfirm
        the Preserved Assets at HEAD: `intAccessPreorder`/`intAccessPreorder_le_of_isAccessible`
        (`Scheme.lean:309-323`) build green; the v5 Phase-1 `∃ edges, IBranchSaturation` exposure is
        present; `grep -rn sorry` over the four Intuitionistic tableau files shows exactly the four
        inventory sorries.
  - [ ] Re-thread `truthLemma` (`Scheme.lean:382-444`): every T/F clause that quantifies `∀ w' ≥ w`
        now quantifies over `intAccessPreorder edges`-reachability. Read (windowed) `truthLemma`,
        `IForces`/`IForces_imp` (`Kripke.lean:81,100`), `intAccessPreorder_le_of_isAccessible`.
  - [ ] Re-prove the F-imp case (report 08 2nd adversarial challenge): its `sat_fimp` witness `w'` must
        now witness edge-reachability, not numeric `≤`. Confirm it type-checks over the new frame.
  - [ ] Leave the T-imp `sorry` (`:409`) in place, stated over edge accessibility.
  - [ ] Scoped+grepped build GREEN; the four inventory sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 1: re-thread truthLemma over intAccessPreorder edge frame`.
- **Estimated output:** ~250-400 lines. **Done when:** `truthLemma` builds over `intAccessPreorder`
  with all non-T-imp cases proved, T-imp still the single deferred sorry over the edge frame.
- **Timing:** 3 hours. **Depends on:** none (builds on Preserved Assets).
- **Owned files:** `Scheme.lean`.

---

### Phase 2: [Wave A] Restate `openBranch_countermodel` conclusion over `intAccessPreorder edges` [NOT STARTED]

- **Goal:** Apply the Route (a) signature un-pin (Postmortem-5 revision) to the shared parametric
  countermodel lemma: its conclusion becomes `∃ edges, ¬ @IForces Nat Atom (intAccessPreorder edges)
  (intExtractValuation b) (S.modelBot b) 0 φ`, consuming the Phase-1 re-threaded `truthLemma` and the
  already-exposed `edges` (Preserved Asset). No sorry closed.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Change `openBranch_countermodel`'s (`Scheme.lean:1399`) stated conclusion to the explicit
        `@IForces Nat Atom (intAccessPreorder edges) …` instance (never rely on instance search — the
        two `Preorder Nat` instances are not defeq, R1). Bind `edges` from the exposed
        `∃ edges, IBranchSaturation` (Preserved Asset). The T-imp-dependent case of the proof still
        rests on the Phase-1 T-imp sorry (unchanged count).
  - [ ] Confirm NO live consumer of `openBranch_countermodel` breaks (report 09 §a.1: docstrings only).
        Re-grep `openBranch_countermodel` across `Cslib/` to re-verify at HEAD.
  - [ ] Scoped+grepped build GREEN; four inventory sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 2: restate openBranch_countermodel over intAccessPreorder (Route a)`.
- **Estimated output:** ~200-400 lines (pre-split candidate: 2.1 conclusion restatement / 2.2 proof
  re-thread). **Done when:** `openBranch_countermodel` builds with the edge-preorder conclusion and no
  new sorry; the stable public contract is untouched.
- **Timing:** 3 hours. **Depends on:** 1.
- **Owned files:** `Scheme.lean`.

---

### Phase 3: [Wave A] Restate the two `*OpenBranch_countermodel` corollaries over the edge preorder [NOT STARTED]

- **Goal:** Mirror the Phase-2 restatement into the two internal corollaries in the Completeness modules
  — `intuitionisticOpenBranch_countermodel` (`Completeness.lean:87-90`) and `minOpenBranch_countermodel`
  (`Minimal/Completeness.lean:93-96`) — completing the Postmortem-5-revised internal signature change.
  No sorry closed.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Completeness.lean Minimal/Completeness.lean`; scoped+grepped
        rebuild GREEN.
  - [ ] Restate both corollaries' conclusions over `intAccessPreorder edges` (consuming the Phase-2
        parent). Verify both have NO live code consumer beyond docstrings (report 09 §a.1).
  - [ ] Confirm the DecisionProcedure consumers (`instDecidableIValid` `DecisionProcedure.lean:105-111`;
        minimal analogue) still build — they route through `*Tableau_complete`, NOT the countermodel
        (blast-radius reconfirmation at HEAD).
  - [ ] Scoped+grepped builds GREEN; four inventory sorries unchanged; commit the two Completeness files
        only: `task 317 phase 3: restate *OpenBranch_countermodel corollaries over edge preorder`.
- **Estimated output:** ~150-300 lines. **Done when:** both corollaries build over the edge preorder;
  DecisionProcedure consumers unaffected; no new sorry.
- **Timing:** 2 hours. **Depends on:** 2.
- **Owned files:** `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`.

---

### Phase 4: [Wave A] Instantiate `IValid`/`MValid` at the edge preorder in `*Tableau_complete` via a deferred-monotonicity private bridge [NOT STARTED]

- **Goal:** Discharge the `hvalid`/`hmvalid` obligation in `intuitionisticTableau_complete`
  (`Completeness.lean:106-113`) and `minimalTableau_complete` (`Minimal/Completeness.lean:106`) by
  instantiating `IValid`/`MValid` at the `intAccessPreorder edges` frame. `IValid` already ∀-quantifies
  all preorders, so the PUBLIC `IValid φ → .closed` type is BYTE-STABLE. Thread `intExtractValuation`
  monotonicity as an EXPLICITLY-DEFERRED premise on a `private` bridge — its top-level discharge remains
  the existing Completeness-bridge sorry until Phase 10. Completes Wave A. No sorry closed.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Completeness.lean Minimal/Completeness.lean Scheme.lean`;
        scoped+grepped rebuild GREEN.
  - [ ] Add a `private` bridge `_intForcing_at_edge_frame` (and minimal mirror) taking an explicit
        `intExtractValuation`-monotonicity-along-`intAccessPreorder` premise, instantiating `IValid` at
        that frame to obtain `¬ IForces …` for the Phase-2/3 countermodel. The monotonicity premise is
        supplied by a `sorry` at exactly the existing bridge sites (`Completeness.lean:113`,
        `Minimal/Completeness.lean:110`) — i.e. NO NEW sorry; the count is preserved, the obligation is
        merely reshaped into a named, deferred premise Phase 10 will discharge.
  - [ ] Verify `intuitionisticTableau_complete`/`minimalTableau_complete` retain their exact public
        `IValid/MValid φ → .closed` types (Postmortem 5 stable contract). `lean_verify` the two public
        lemmas' TYPES against the pre-Wave-A baseline (byte-stable).
  - [ ] Scoped+grepped builds GREEN; four inventory sorries unchanged (sorries 3-4 now sit at the named
        deferred-monotonicity premise); commit the touched files only:
        `task 317 phase 4: instantiate IValid/MValid at edge frame via deferred-monotonicity bridge`.
- **Estimated output:** ~150-300 lines. **Done when:** the public `*Tableau_complete` types are
  byte-stable, the monotonicity premise is a named deferred obligation, Wave A is fully landed with
  exactly the four (now edge-framed) sorries. **Wave A is INDEPENDENTLY COMMITTABLE here** — a valid
  terminal state if Wave B is deferred/blocked (report 09: frame plumbing as committed green progress).
- **Timing:** 2.5 hours. **Depends on:** 3.
- **Owned files:** `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`, `Scheme.lean`.

---

### Phase 5: [Wave B / B2] Raise the fuel to `intFuel φ` + audit downstream callers [NOT STARTED]

- **Goal:** Change the fuel from `2^(2*φ.complexity+2)` to `intFuel φ ≈ 3^Θ(c²)` (report 07 §Q4) and
  re-verify every downstream fuel-pinned caller. TERRITORY HAZARD: task 316 (`Expansion.lean` +
  `Soundness.lean`). FILE-DISJOINT from the Scheme.lean track → truly concurrent with Phase 6.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Expansion.lean Soundness.lean`; scoped+grepped rebuild GREEN.
  - [ ] Define `intFuel φ := 3 ^ (2·(2·φ.complexity+1)·(φ.complexity+2))` (or the exact bound Phase 8
        needs — size for `intExpMeasure_init_le_fuel` with slack, R8). Change the fuel site at
        `Expansion.lean:466` and the minimal analogue.
  - [ ] AUDIT every downstream fuel-pinned caller: `intExpandBranches_closed_unsat` (`Soundness.lean`,
        316), `DecisionProcedure.lean`, `Completeness.lean`. The change is monotone-safe for the
        `openBranch → saturated` direction; confirm each still builds.
  - [ ] STOP-gate (R5/TERRITORY 316): a non-trivial `Soundness.lean` caller edit → STOP/[BLOCKED]/escalate.
        A mechanical re-pin → MINIMAL fix, `Soundness.lean` in a SEPARATE scoped commit with a coordination flag.
  - [ ] Scoped+grepped builds (`Expansion`, then downstream) GREEN; four inventory sorries unchanged;
        commit `Expansion.lean` only (+ separate `Soundness.lean` commit if forced):
        `task 317 phase 5: raise fuel to intFuel (coordinates task 316)`.
- **Estimated output:** ~100-200 lines + audit. **Done when:** the fuel is raised, all downstream callers
  build, task-316 coordination flagged, four sorries unchanged.
- **Timing:** 2 hours. **Depends on:** 4 (Wave A landed; sequenced after per the independent-landing narrative).
- **Owned files:** `Expansion.lean` (+ `Soundness.lean` ONLY if forced, separate commit).

---

### Phase 6: [Wave B / B2] `intUniverse` + `intWork` + the linear world bound [NOT STARTED]

- **Goal:** Define the fixed finite universe and the counting-against-universe work, and prove the linear
  world bound (Modal-K `FmpMeasure` pattern). FILE-DISJOINT from Phase 5.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Define `intUniverse φ : List (ISF Atom)` (the `(sign, subformula, world)` cells,
        `|U| ≤ 2·(2c+1)·(c+2)`) and `intWork U b e := (U.diff b).length + (U.diff e).length`
        (mirror `modalWork`, `FmpMeasure.lean:180-196`).
  - [ ] Prove `intExpandBranches_world_bound`: `(b.map (·.label)).eraseDups.length ≤ φ.complexity + 1`
        (report 07 §Q4 — holds with NO dedup; do NOT entangle with the Option-A dedup).
  - [ ] Scoped+grepped build GREEN; four sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 6: intUniverse + intWork + linear world bound`.
- **Estimated output:** ~200-350 lines. **Done when:** `intUniverse`, `intWork`, and
  `intExpandBranches_world_bound` are sorry-free.
- **Timing:** 3 hours. **Depends on:** 4. Logically parallel with Phase 5; R7-serialized only with
  other Scheme.lean phases (Phase 5 is `Expansion.lean` → truly concurrent).
- **Owned files:** `Scheme.lean`.

---

### Phase 7: [Wave B / B2] `intExpMeasure_step_lt` (per-step strict decrease) [NOT STARTED]

- **Goal:** Prove each `go` step strictly decreases `intExpMeasure` — the hard B2 phase. World-creation
  and persistence via the `|U\b|+|U\e|` decrease, NOT branch complexity.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Define `intExpMeasure U branches expandedSets := Σ (b,e) ↦ 3 ^ intWork U b e` (mirror `modalExpMeasure`).
  - [ ] Prove `intExpMeasure_step_lt`: one `go` step gives `intExpMeasure (done ++ newBs ++ rest) … + 1 ≤
        intExpMeasure (done ++ b :: rest) …` (mirror `modalExpMeasure_step_lt`, `FmpMeasure.lean:3018`).
  - [ ] Scoped+grepped build GREEN; four sorries unchanged; if it exceeds ~450 lines, split into 7.1
        (def + linear/non-branching step cases) and 7.2 (world-creating / β-split cases). Commit
        `Scheme.lean` only: `task 317 phase 7: intExpMeasure_step_lt`.
- **Estimated output:** ~300-500 lines (pre-split candidate). **Done when:** `intExpMeasure_step_lt` is sorry-free.
- **Timing:** 4 hours. **Depends on:** 6 (uses `intUniverse`/`intWork`).
- **Owned files:** `Scheme.lean`.

---

### Phase 8: [Wave B / B2] `intExpMeasure_init_le_fuel` (initial measure ≤ raised fuel) [NOT STARTED]

- **Goal:** Prove the initial measure is bounded by the raised fuel, using `|U| = O(c²)` and the linear
  world bound. This is where the fuel-raise pays off (impossible at the old fuel, report 07 §Q2).
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Prove `intExpMeasure_init_le_fuel φ : intExpMeasure (intUniverse φ) [[⟨.neg,φ,0⟩]] [[]] ≤ intFuel φ`
        with SLACK (`≤`, R8). Reuse arithmetic helpers `sum_map_le_length_mul` and geometric caps
        (`FmpMeasure.lean:131,776-833`).
  - [ ] Scoped+grepped build GREEN; four sorries unchanged; commit `Scheme.lean` only:
        `task 317 phase 8: intExpMeasure_init_le_fuel`.
- **Estimated output:** ~150-300 lines. **Done when:** `intExpMeasure_init_le_fuel` is sorry-free.
- **Timing:** 2.5 hours. **Depends on:** 5 (uses `intFuel`), 6 (uses `intUniverse`/world bound).
  Logically parallel with Phase 7; R7-serialized (both `Scheme.lean`).
- **Owned files:** `Scheme.lean`.

---

### Phase 9: [Wave B / discharge deferred Wave-A obligations] Add `sat_timp` + discharge, prove `intExtractValuation` monotonicity, close truthLemma T-imp (sorry 1) [NOT STARTED]

- **Goal:** Discharge the TWO deferred Wave-A obligations using the fuel fixpoint (Phase 7): (i) add
  `sat_timp` to `IBranchSaturation` and discharge it in `IExpandedConsistent_sat`; (ii) prove
  `intExtractValuation` monotone along `intAccessPreorder`. Then close the `truthLemma` T-imp sorry (1)
  via `sat_timp` over the edge frame.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [ ] Add the `sat_timp` field (report 09 §a.4), stated over `isAccessible`:
        `sat_timp : ∀ φ ψ w w', T(φ→ψ)@w ∈ b → isAccessible edges w w' → (F(φ)@w' ∈ b ∨ T(ψ)@w' ∈ b)`.
  - [ ] Discharge `sat_timp` inside `IExpandedConsistent_sat` (`Scheme.lean:563-633`) by mirroring the
        soundness `applyAllTImpRules`/`intTImpRule` argument (`Soundness.lean:353-406`) at the fuel
        fixpoint (Phase 7 `step_lt` certifies the fixpoint is genuine). R3: keep `IExpandedConsistent_sat`
        sorry-free; if the succ-case construction entangles, fold this into Phase 10.
  - [ ] Prove `intExtractValuation` monotone along `intAccessPreorder` from `propagatePersistence`
        (report 08 §Q5: verify the Option-A reuse path preserves the copy), at the fuel fixpoint.
  - [ ] Close the `truthLemma` T-imp sorry (`Scheme.lean:409`) via `sat_timp`
        (report 09 §a.4 snippet: `intro w' hacc hφ'; rcases hsat.sat_timp … with hF | hT`).
  - [ ] Scoped+grepped build GREEN; `grep -n sorry` → sorry 1 gone (three remain: 2, 3, 4);
        `lean_verify truthLemma` no `sorryAx`; if >450 lines split into 9.1 (`sat_timp` + T-imp close)
        and 9.2 (monotonicity). Commit `Scheme.lean` only:
        `task 317 phase 9: sat_timp + intExtractValuation monotonicity + close truthLemma T-imp`.
- **Estimated output:** ~250-450 lines (pre-split candidate). **Done when:** `sat_timp` is a discharged
  field, `intExtractValuation` monotonicity is proved, truthLemma is sorryAx-free.
- **Timing:** 4 hours. **Depends on:** 4 (frame + deferred obligations), 7 (fuel fixpoint / `step_lt`).
- **Owned files:** `Scheme.lean`.

---

### Phase 10: [Wave B / CONVERGENCE] Reformulate `intExpandBranches_openBranch_sat` + close sorries 2-4 → sorry-FREE [NOT STARTED]

- **Goal:** The sole serialization point. Add the `intExpMeasure … ≤ fuel` hypothesis to
  `intExpandBranches_openBranch_sat`, close the fuel-0 sorry (2), and supply the Phase-9 monotonicity to
  the Phase-4 `private` bridges to close the two Completeness-bridge sorries (3, 4) — keeping the stable
  public contract byte-stable (STOP-gate b). Reaches sorry-FREE.
- **Tasks:**
  - [ ] PREFLIGHT (R7): `git log -1 -- Scheme.lean Completeness.lean Minimal/Completeness.lean`;
        scoped+grepped rebuild GREEN.
  - [ ] Add the `intExpMeasure … ≤ fuel` hypothesis to `intExpandBranches_openBranch_sat`
        (`Scheme.lean:1070` site). fuel=0 ⟹ measure=0 ⟹ `branches=[]` ⟹ `.openBranch` impossible
        (copy `classicalExpandBranches_hintikka:922-939` in structure). Thread `intExpMeasure_step_lt`
        (Phase 7) through the succ case. Closes sorry 2.
  - [ ] Supply the measure bound INTERNALLY at the `openBranch_countermodel` call site from
        `intExpMeasure_init_le_fuel` (Phase 8), threading through a `private` `_aux`/`key` so the internal
        countermodel lemmas' (Route-(a)-revised) conclusions gain NO hypothesis and the stable public
        contract stays byte-stable (Postmortem 5). STOP-gate b: if it cannot be discharged internally,
        STOP/[BLOCKED].
  - [ ] Discharge the Phase-4 deferred-monotonicity premises with the Phase-9 `intExtractValuation`
        monotonicity, closing the two Completeness-bridge sorries (3, 4).
  - [ ] Scoped+grepped builds GREEN; `grep -rn sorry` over the four Intuitionistic tableau files →
        NOTHING. `lean_verify` on `intExpandBranches_openBranch_sat`, `openBranch_countermodel`,
        `intuitionisticTableau_complete`, `minimalTableau_complete`, `instDecidableIValid` → no `sorryAx`,
        no new axioms; the two public `*Tableau_complete` TYPES byte-identical to the pre-Wave-A baseline.
  - [ ] Commit the touched files only:
        `task 317 phase 10: close sorries 2-4 via measure ≤ fuel + monotonicity → sorry-FREE`.
- **Estimated output:** ~200-400 lines. **Done when:** the completeness is sorry-FREE, the stable public
  contract is byte-stable, `lean_verify` is clean.
- **Timing:** 3.5 hours. **Depends on:** 8 (`init_le_fuel`), 9 (`sat_timp`/monotonicity). Transitively 4, 7.
- **Owned files:** `Scheme.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`.

---

### Phase 11: Add load-bearing BibKeys (chiefly `NegriVonPlato2001`) [NOT STARTED]

- **Goal:** Add the citations the Phase 1-4/9 docstrings rely on to `references.bib` — chiefly
  `NegriVonPlato2001` (ABSENT; load-bearing for the Route (a) frame), plus `GargGenoveseNegri2012` and
  `DershowitzManna1979` where the dedup/measure docstrings cite them.
- **Tasks:**
  - [ ] `git log -1 -- references.bib`; confirm `NegriVonPlato2001`, `GargGenoveseNegri2012`,
        `DershowitzManna1979` ABSENT and `Fitting1983`/`ChagrovZakharyaschev1997`/
        `TroelstraSchwichtenberg2000` PRESENT.
  - [ ] Append the load-bearing entries (`NegriVonPlato2001` Ch. 8 for the frame / `sat_timp` citations;
        `GargGenoveseNegri2012` for the dedup docstring; `DershowitzManna1979` for the measure ordering).
  - [ ] Confirm the proof-comment BibKeys now resolve; commit `references.bib` only:
        `task 317 phase 11: add load-bearing BibKeys (NegriVonPlato2001 et al.)`.
- **Estimated output:** ~20-40 lines. **Done when:** the cited keys resolve.
- **Timing:** 0.5 hours. **Depends on:** 10.
- **Owned files:** `references.bib`.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"` → Build completed.
- [ ] Scoped builds of `Expansion`, `Intuitionistic/Completeness`, `Minimal/Completeness` (and, if touched, `Soundness`) GREEN.
- [ ] `grep -rn sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/ Cslib/Logics/Propositional/Tableau/Minimal/` → NOTHING (all four inventory sorries closed).
- [ ] Stable public contract byte-identical to baseline: `intuitionisticTableau_complete`, `minimalTableau_complete` (`IValid/MValid φ → .closed`), `Decidable (IValid φ)`, `Decidable (Derivable IntPropAxiom φ)`, `instDecidableIValid`, DecisionProcedure consumers. (The internal countermodel family MAY differ — Route (a) / Postmortem-5 revision.)
- [ ] `lean_verify` on `truthLemma`, `intExpandBranches_openBranch_sat`, `openBranch_countermodel`, `intuitionisticTableau_complete`, `minimalTableau_complete`, `intExpMeasure_step_lt`, `intExpMeasure_init_le_fuel`, `intExpandBranches_world_bound` → no `sorryAx`, no new axioms.
- [ ] `Soundness.lean` (task 316) unchanged in the diff, or (if the fuel-raise forced a re-pin) in a SEPARATE scoped commit with a coordination note.
- [ ] Diff contains only `Scheme.lean`, `Expansion.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`, `references.bib` (+ `Soundness.lean` only where Phase 5 flagged it) — never `git add -A`.
- [ ] Full CI smoke (only if context budget allows; else defer to /vet): `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`.

## Artifacts & Outputs

- `specs/317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md` (this file)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (truthLemma re-threaded over `intAccessPreorder`; `openBranch_countermodel` restated; `sat_timp` field + discharge; `intExtractValuation` monotonicity; truthLemma T-imp closed; `intUniverse`/`intWork`/`intExpMeasure`/world bound; `intExpMeasure_step_lt`/`intExpMeasure_init_le_fuel`; `intExpandBranches_openBranch_sat` reformulated; fuel-0 sorry closed)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` (`intuitionisticOpenBranch_countermodel` restated; deferred-monotonicity bridge; bridge sorry closed)
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (mirror)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (fuel raised to `intFuel`)
- Modified: `references.bib` (`NegriVonPlato2001`, `GargGenoveseNegri2012`, `DershowitzManna1979`)
- Possibly modified (flag + separate commit if so): `Intuitionistic/Soundness.lean` (task 316 — fuel re-pin only)
- Downstream effect: task 430 (atom-persistence) RESHAPED by the frame change → re-plan after Wave A; task 375 gated on 430 + this completeness-green.
- `specs/317_propositional_tableau_completeness/summaries/06_route-a-frame-plumbing-summary.md` (on completion)

## Rollback/Contingency

- Each phase commits at GREEN; `git revert` a phase commit if it regresses. The chain
  1→2→3→4→{5,6}→{7,8}→9→10→11 peels back cleanly to the `a1883c4e`/`d6d78714` Preserved-Asset green
  state (four sorries).
- **Wave A as a valid terminal state**: if Wave B is deferred or blocked (e.g. a decision not to raise the
  fuel), Phase 4's committed green frame plumbing (four edge-framed sorries) is correct, sorry-free-*enabling*
  progress — NOT a placeholder (report 09 zero-debt note). The correct terminal state then is [BLOCKED] on
  fuel sufficiency, with reports 07/09 as the escalation record.
- **R1 escalation (Phase 2)**: if a countermodel case resists the `intAccessPreorder` instantiation using
  ONLY completeness-side edits + read-only soundness machinery, mark the phase [BLOCKED] and hand off the
  exact resisting subgoal — do NOT reach for Route (b) (redefining `IForces`).
- **R4 escalation (Phase 10, STOP-gate b)**: if the `measure ≤ fuel` bound cannot be supplied internally
  without touching the stable public contract, mark Phase 10 [BLOCKED] and hand off — do NOT change
  `*Tableau_complete`/`Decidable` signatures.
- **R5 escalation (Phase 5, TERRITORY 316)**: if the fuel-raise needs a non-trivial `Soundness.lean` edit,
  STOP/[BLOCKED]/escalate for task-316 coordination.
- **Overflow contingency (R6)**: a committed green partial (four/three-sorry state preserved) + a sharp
  handoff is the success criterion for an interrupted run. Phases 2, 7, 9 are pre-split candidates.
- Never pursue Route (b) or Option B (both rejected), and never revert the Option-A dedup or the
  Preserved Assets under any contingency.
