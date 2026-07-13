# Implementation Plan: Task #317 (v6 — Route (a) frame plumbing + report-07 fuel raise for sorry-FREE intuitionistic tableau completeness, HARD mode)

- **Task**: 317 - Close the residual intuitionistic completeness-chain sorries to reach a sorry-FREE intuitionistic (and minimal) tableau completeness, by un-pinning the completeness frame off the global `Nat` total preorder (Route (a)) and then raising the fuel (report 07).
- **Status**: [IMPLEMENTING]
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

### Phase 1: [Wave A] Re-thread `truthLemma` over the `intAccessPreorder` edge frame [COMPLETED]

**Landed (this dispatch, on top of commit `6e24520d`)**: full Wave A (Phases 1-4) landed as ONE
consistent commit, confirming the prior handoff's finding that these phases are not
independently buildable-green in isolation (Lean compiles per-FILE, and `truthLemma`'s frame
change ripples immediately into `openBranch_countermodel` in the SAME file, then into
`Completeness.lean`/`Minimal/Completeness.lean`, then into `tableau_complete`'s `hvalid` bridge
shape). Design deviation from the handoff's suggestion (`IBranchSaturation` gains `edges` as a
FIELD): instead, `edges`/the edge-accessibility fact are threaded via a companion invariant
(`IFimpAccess edges b`, returned alongside `IBranchSaturation Atom b` from
`intExpandBranches_openBranch_sat`/`openBranch_countermodel`'s existing `∃ edges, …` pattern) —
mathematically equivalent, and it leaves `IBranchSaturation`'s structure completely untouched
(smaller footprint, zero risk to its 5 existing fields). `truthLemma` now takes `edges`/`hfimp`
and installs `intAccessPreorder edges` via `letI`; the F-imp case is closed over genuine
`isAccessible` (via `IExpandedAccessConsistent`/`sfAccessSat` threaded through
`intStepBranch_linear_preserves`/`intStepBranch_branch_preserves`/
`intExpandBranches_openBranch_sat`'s induction, using the two already-available per-site
witnesses: `intFImpRule`'s new edge for fresh worlds, `intFImpReuseWitness?_spec`'s `hacc` for
Option-A dedup reuse). T-imp stays `sorry` (deferred to Phase 9). Scoped builds GREEN for all
of `Scheme.lean`, `Completeness.lean`, `Minimal/Completeness.lean`, plus `DecisionProcedure.lean`
(both) and `IntDecidability.lean`/`MinDecidability.lean` reverified green. Four inventory
sorries unchanged in count (`Scheme.lean:533,1386`, `Completeness.lean:133`,
`Minimal/Completeness.lean:125` after line-number shift); `lean_verify` on
`intuitionisticTableau_complete`/`minimalTableau_complete`/`instDecidableIValid` shows only
`{propext, sorryAx, Classical.choice, Quot.sound}` (no new axioms). `Soundness.lean`/
`Expansion.lean` untouched (task 316 territory respected). See commit for the full diff; Phases
2-4 below are marked [COMPLETED] in the same commit for the reasons above.

- **Goal:** Re-express `truthLemma`'s `∀ w' ≥ w` quantifiers to range over `intAccessPreorder`-reachable
  worlds (via `intAccessPreorder_le_of_isAccessible`), re-proving the non-imp cases and the already-green
  F-imp case over the edge relation. The T-imp case (`Scheme.lean:409`) STAYS as its existing sorry —
  now stated over edge accessibility — deferred to Phase 9 (`sat_timp`). No sorry closed here.
- **Tasks:**
  - [x] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN at HEAD. Reconfirm
        the Preserved Assets at HEAD: `intAccessPreorder`/`intAccessPreorder_le_of_isAccessible`
        (`Scheme.lean:309-323`) build green; the v5 Phase-1 `∃ edges, IBranchSaturation` exposure is
        present; `grep -rn sorry` over the four Intuitionistic tableau files shows exactly the four
        inventory sorries.
  - [x] Re-thread `truthLemma` (`Scheme.lean:382-444`): every T/F clause that quantifies `∀ w' ≥ w`
        now quantifies over `intAccessPreorder edges`-reachability. Read (windowed) `truthLemma`,
        `IForces`/`IForces_imp` (`Kripke.lean:81,100`), `intAccessPreorder_le_of_isAccessible`.
  - [x] Re-prove the F-imp case (report 08 2nd adversarial challenge): its `sat_fimp` witness `w'` must
        now witness edge-reachability, not numeric `≤`. Confirm it type-checks over the new frame.
  - [x] Leave the T-imp `sorry` (`:409`) in place, stated over edge accessibility.
  - [x] Scoped+grepped build GREEN; the four inventory sorries unchanged; committed (with Phases 2-4,
        see deviation note above): `task 317 phases 1-4: Route (a) frame plumbing (Wave A complete)`.
- **Estimated output:** ~250-400 lines. **Done when:** `truthLemma` builds over `intAccessPreorder`
  with all non-T-imp cases proved, T-imp still the single deferred sorry over the edge frame.
- **Timing:** 3 hours. **Depends on:** none (builds on Preserved Assets).
- **Owned files:** `Scheme.lean`.

---

### Phase 2: [Wave A] Restate `openBranch_countermodel` conclusion over `intAccessPreorder edges` [COMPLETED]

**Landed together with Phase 1** (see deviation note under Phase 1): `openBranch_countermodel`'s
conclusion is now `∃ edges : IEdges, ¬ @IForces Atom Nat (intAccessPreorder edges)
(intExtractValuation b) (S.modelBot b) 0 φ` (note the explicit-instance argument order is
`Atom` then `Nat`/`World`, per `IForces`'s actual auto-bound parameter order — verified via
build error, not assumed). `IFimpAccess` made non-`private` since a `private` declaration
cannot appear in a `public`-section lemma's stated type in this module (a real, non-obvious
Lean 4 module-system constraint discovered this cycle).

- **Goal:** Apply the Route (a) signature un-pin (Postmortem-5 revision) to the shared parametric
  countermodel lemma: its conclusion becomes `∃ edges, ¬ @IForces Nat Atom (intAccessPreorder edges)
  (intExtractValuation b) (S.modelBot b) 0 φ`, consuming the Phase-1 re-threaded `truthLemma` and the
  already-exposed `edges` (Preserved Asset). No sorry closed.
- **Tasks:**
  - [x] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [x] Change `openBranch_countermodel`'s (`Scheme.lean:1399`) stated conclusion to the explicit
        `@IForces Nat Atom (intAccessPreorder edges) …` instance (never rely on instance search — the
        two `Preorder Nat` instances are not defeq, R1). Bind `edges` from the exposed
        `∃ edges, IBranchSaturation` (Preserved Asset). The T-imp-dependent case of the proof still
        rests on the Phase-1 T-imp sorry (unchanged count).
  - [x] Confirm NO live consumer of `openBranch_countermodel` breaks (report 09 §a.1: docstrings only).
        Re-grep `openBranch_countermodel` across `Cslib/` to re-verify at HEAD.
  - [x] Scoped+grepped build GREEN; four inventory sorries unchanged; committed with Phases 1,3,4:
        `task 317 phases 1-4: Route (a) frame plumbing (Wave A complete)`.
- **Estimated output:** ~200-400 lines (pre-split candidate: 2.1 conclusion restatement / 2.2 proof
  re-thread). **Done when:** `openBranch_countermodel` builds with the edge-preorder conclusion and no
  new sorry; the stable public contract is untouched.
- **Timing:** 3 hours. **Depends on:** 1.
- **Owned files:** `Scheme.lean`.

---

### Phase 3: [Wave A] Restate the two `*OpenBranch_countermodel` corollaries over the edge preorder [COMPLETED]

**Landed together with Phases 1,2,4** (see deviation note under Phase 1). Both
`intuitionisticOpenBranch_countermodel` and `minOpenBranch_countermodel` restated over
`∃ edges, ¬ @IForces Atom Nat (intAccessPreorder edges) …`; `intTruthLemma`/`minTruthLemma`
also updated to thread `edges`/`hfimp` through to the parametric `truthLemma`.
`DecisionProcedure.lean` (both) reverified green — they route through `*Tableau_complete`,
confirming the blast-radius claim.

- **Goal:** Mirror the Phase-2 restatement into the two internal corollaries in the Completeness modules
  — `intuitionisticOpenBranch_countermodel` (`Completeness.lean:87-90`) and `minOpenBranch_countermodel`
  (`Minimal/Completeness.lean:93-96`) — completing the Postmortem-5-revised internal signature change.
  No sorry closed.
- **Tasks:**
  - [x] PREFLIGHT (R7): `git log -1 -- Completeness.lean Minimal/Completeness.lean`; scoped+grepped
        rebuild GREEN.
  - [x] Restate both corollaries' conclusions over `intAccessPreorder edges` (consuming the Phase-2
        parent). Verify both have NO live code consumer beyond docstrings (report 09 §a.1).
  - [x] Confirm the DecisionProcedure consumers (`instDecidableIValid` `DecisionProcedure.lean:105-111`;
        minimal analogue) still build — they route through `*Tableau_complete`, NOT the countermodel
        (blast-radius reconfirmation at HEAD).
  - [x] Scoped+grepped builds GREEN; four inventory sorries unchanged; committed with Phases 1,2,4:
        `task 317 phases 1-4: Route (a) frame plumbing (Wave A complete)`.
- **Estimated output:** ~150-300 lines. **Done when:** both corollaries build over the edge preorder;
  DecisionProcedure consumers unaffected; no new sorry.
- **Timing:** 2 hours. **Depends on:** 2.
- **Owned files:** `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`.

---

### Phase 4: [Wave A] Instantiate `IValid`/`MValid` at the edge preorder in `*Tableau_complete` via a deferred-monotonicity private bridge [COMPLETED]

**Landed together with Phases 1-3** (see deviation note under Phase 1). Implementation
deviates slightly from the sketched `private` bridge helper: `tableau_complete`'s own
`hvalid` hypothesis was reshaped in-place to `∀ (edges : IEdges) (b : IBranch Atom), @IForces
Atom Nat (intAccessPreorder edges) …` (rather than adding a separate private wrapper lemma),
since `edges` is discovered only inside `tableau_complete`'s own proof (from the open-branch
case) and this is the minimal change that keeps the shape correct. `intuitionisticTableau_complete`/
`minimalTableau_complete` retain their exact public `IValid φ → .closed`/`MValid φ → .closed`
types (verified via successful `DecisionProcedure.lean` builds, which consume these lemmas
downstream, plus `lean_verify` showing only `{propext, sorryAx, Classical.choice, Quot.sound}` —
no new axioms). The bridge sorry is preserved (reshaped, not removed) at both sites.

- **Goal:** Discharge the `hvalid`/`hmvalid` obligation in `intuitionisticTableau_complete`
  (`Completeness.lean:106-113`) and `minimalTableau_complete` (`Minimal/Completeness.lean:106`) by
  instantiating `IValid`/`MValid` at the `intAccessPreorder edges` frame. `IValid` already ∀-quantifies
  all preorders, so the PUBLIC `IValid φ → .closed` type is BYTE-STABLE. Thread `intExtractValuation`
  monotonicity as an EXPLICITLY-DEFERRED premise on a `private` bridge — its top-level discharge remains
  the existing Completeness-bridge sorry until Phase 10. Completes Wave A. No sorry closed.
- **Tasks:**
  - [x] PREFLIGHT (R7): `git log -1 -- Completeness.lean Minimal/Completeness.lean Scheme.lean`;
        scoped+grepped rebuild GREEN.
  - [x] Add a `private` bridge (implemented as `tableau_complete`'s reshaped `hvalid` hypothesis, see
        deviation note above) taking an explicit `intExtractValuation`-monotonicity-along-
        `intAccessPreorder` premise, instantiating `IValid` at that frame to obtain `¬ IForces …` for
        the Phase-2/3 countermodel. The monotonicity premise is supplied by a `sorry` at exactly the
        existing bridge sites (`Completeness.lean:133`, `Minimal/Completeness.lean:125`, shifted) —
        i.e. NO NEW sorry; the count is preserved, the obligation is merely reshaped into a named,
        deferred premise Phase 10 will discharge.
  - [x] Verify `intuitionisticTableau_complete`/`minimalTableau_complete` retain their exact public
        `IValid/MValid φ → .closed` types (Postmortem 5 stable contract). `lean_verify` the two public
        lemmas' TYPES against the pre-Wave-A baseline (byte-stable).
  - [x] Scoped+grepped builds GREEN; four inventory sorries unchanged (sorries 3-4 now sit at the named
        deferred-monotonicity premise); commit the touched files only:
        `task 317 phases 1-4: Route (a) frame plumbing (Wave A complete)`.
- **Estimated output:** ~150-300 lines. **Done when:** the public `*Tableau_complete` types are
  byte-stable, the monotonicity premise is a named deferred obligation, Wave A is fully landed with
  exactly the four (now edge-framed) sorries. **Wave A is INDEPENDENTLY COMMITTABLE here** — a valid
  terminal state if Wave B is deferred/blocked (report 09: frame plumbing as committed green progress).
- **Timing:** 2.5 hours. **Depends on:** 3.
- **Owned files:** `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`, `Scheme.lean`.

---

### Phase 5: [Wave B / B2] Raise the fuel to `intFuel φ` + audit downstream callers [COMPLETED]

**Resolution**: Orchestrator authorized a combined dual-file dispatch (expanded H7 territory
covering `Expansion.lean` full + `Scheme.lean` limited to the 4 fuel-literal sites). Landed
`intFuel φ := 3 ^ (2·(2·φ.complexity+1)·(φ.complexity+2))` in `Expansion.lean` alongside
`intExpandBranches`, wired `intuitionisticTableau`/`minimalTableau` to it, and substituted the
4 hardcoded `2 ^ (2 * φ.complexity + 2)` literals in `Scheme.lean` (`tableau_sound:252`,
`openBranch_countermodel:1762`, `tableau_complete:1819,1822`) with `intFuel φ` in the SAME
atomic commit (`7291c940`). Both `Completeness.lean` modules and both `DecisionProcedure.lean`
modules build GREEN; four inventory sorries unchanged in count and location.

- **Goal:** Change the fuel from `2^(2*φ.complexity+2)` to `intFuel φ ≈ 3^Θ(c²)` (report 07 §Q4) and
  re-verify every downstream fuel-pinned caller. TERRITORY HAZARD: task 316 (`Expansion.lean` +
  `Soundness.lean`). FILE-DISJOINT from the Scheme.lean track → truly concurrent with Phase 6.
- **Tasks:**
  - [x] PREFLIGHT (R7): `git log -1 -- Expansion.lean Soundness.lean`; scoped+grepped rebuild GREEN.
  - [x] Define `intFuel φ := 3 ^ (2·(2·φ.complexity+1)·(φ.complexity+2))`. Changed the fuel site at
        `Expansion.lean:467` (`intuitionisticTableau`) and `Expansion.lean:480` (`minimalTableau`).
  - [x] AUDIT every downstream fuel-pinned caller: `Soundness.lean` (both) confirmed unaffected
        (uses fuel-generic lemma); `Scheme.lean`'s 4 hardcoded literal sites patched to `intFuel φ`
        in the SAME commit (orchestrator-authorized expanded territory); `DecisionProcedure.lean`
        (both) build GREEN.
  - [x] STOP-gate (R5/TERRITORY 316): no `Soundness.lean` edit was needed — confirmed unaffected.
  - [x] Scoped+grepped builds (`Intuitionistic.Completeness`, `Minimal.Completeness`,
        `Intuitionistic.DecisionProcedure`, `Minimal.DecisionProcedure`) GREEN; four inventory
        sorries unchanged (Scheme.lean:533,1386; Completeness.lean:133; Minimal/Completeness.lean:125);
        committed `Expansion.lean` + `Scheme.lean` together atomically: commit `7291c940`,
        `task 317 phase 5: raise fuel to intFuel (atomic Expansion+Scheme fuel-literal)`.
- **Estimated output:** ~100-200 lines + audit. **Done when:** the fuel is raised, all downstream callers
  build, task-316 coordination flagged, four sorries unchanged. — ACHIEVED.
- **Timing:** 2 hours. **Depends on:** 4 (Wave A landed; sequenced after per the independent-landing narrative).
- **Owned files:** `Expansion.lean` (+ `Soundness.lean` ONLY if forced, separate commit).

---

### Phase 6: [Wave B / B2] `intUniverse` + `intWork` + the linear world bound [PARTIAL]

**Resolution (partial)**: Landed `intSubfmls`/`intSubfmls_length_le` (List-recursive subformula
list, mirroring `modalSubfmls`/`modalSubfmls_length_le`, `FmpMeasure.lean:73-102`, restricted to
the propositional connective set), `intUniverse`/`intUniverse_length_le` (fixed finite
`(sign, subformula, world)` cell universe, world range `0..φ.complexity+1`, length bound
`2·(2c+1)·(c+2)` — exactly matching the exponent `intFuel φ` was pre-sized against), and
`intWork` (mirroring `modalWork`'s `countP`/`any` pattern exactly, NOT `List.diff`, since that
is the proven repo pattern). All three are sorry-free, additive, in `Scheme.lean` only. Added two
new imports to `Scheme.lean` (`Cslib.Foundations.Logic.Tableau.Measure` for
`sum_map_le_length_mul`; `Mathlib.Tactic.Ring` for the `ring` tactic used in the length-bound
proof, needed transitively since `Measure.lean`'s own `Mathlib.Tactic.Ring` import is private).
Both `Intuitionistic.Completeness` and `Minimal.Completeness` build GREEN; `checkInitImports`
passes; four inventory sorries unchanged in count and location (only line-shifted by the 2 new
import lines: `Scheme.lean:535,1388`; `Completeness.lean:133`; `Minimal/Completeness.lean:125`).

**Phase 6.2 resolution (this dispatch, commits `bb4ffa3c` + `015f81c1`)**:

*Sub-deliverable 1 (load-bearing containment, COMPLETE)*: Landed the full branch-universe
containment infrastructure mirroring Modal-K's `FmpMeasure.lean:266-754` subformula-closure
development, adapted to the simpler propositional rule set: `intSubfmls_self_mem`,
`intSubfmls_trans`, `mem_intUniverse_of[']`, `intUniverse_mem_formula`/`intUniverse_mem_label`
(constructor/extraction infrastructure), `intTImpRule_outputs_subset` /
`applyAllTImpRules_subset` / `applyPersistenceFixpoint_subset` (persistence-rule containment —
the persistent `T(φ→ψ)` rule never mints a fresh label, so no world-bound hypothesis is
needed there, mirroring Modal-K's `boxPos`/`diamondNeg` "world-preserving rules" P1a pattern),
and the headline **`intApplyRuleFull_outputs_subset`**: the step-level containment dispatch
covering all 5 rule arms (`T∧`/`F∨` ALPHA, `F∧`/`T∨` BETA, `F→` world-creating). This is
EXACTLY the `hb : ∀ x ∈ bh, x ∈ intUniverse φ0` hypothesis `intExpMeasure_step_lt`/`_branch`
already take as an assumption — Phase 10 discharges `hb` inductively over `go`'s recursion by
citing this lemma (plus `applyPersistenceFixpoint_subset` for the pre-step persistence
fixpoint) at each step, rather than re-deriving containment from scratch. Sorry-free,
axiom-clean (`#print axioms` → `[propext, Quot.sound]` only), ~250 lines.

*Sub-deliverable 2 (`intExpandBranches_world_bound`, NOT landed — precise continuation)*:
Also landed `isImpShaped`/`intSubfmls_impCount_le` (the number of `.imp`-node POSITIONS, not
distinct values, in `intSubfmls φ` is `≤ φ.complexity`) as verified supporting infrastructure.
The FULL lemma remains open. Extensive investigation this dispatch (superseding the prior
dispatch's vaguer "occurrence-tracking, comparable to Phase 7" note with a precise mechanism)
found:
- The naive "one world per syntactic occurrence, simple depth argument" is WRONG: `F∨` (the
  `.neg, .or` rule) is `.linearResult` (ALPHA, non-branching, `Rules.lean:260`), so BOTH
  `F(φ)@l` and `F(ψ)@l` land on the SAME branch — a single world CAN accumulate multiple
  independent `F`-imp obligations (e.g. from `(a→b) ∨ (c→d)`), each capable of independently
  firing to create a SIBLING world. So the bound requires a width-AND-depth argument, not
  depth alone.
- The CORRECT mechanism (verified against `Rules.lean`): `posFormulasAt`/
  `propagatePersistence`/`intTImpRule` are ALL `.pos`-only (`Rules.lean:126,139-141,174-186`)
  — **F-signed (negative) formulas never propagate across worlds via persistence**. So every
  world's set of `F`-signed formulas is exactly the decomposition closure of that world's own
  single "obligation" formula (`φ0` at world 0; the consequent `ψ` placed by the `F(φ→ψ)`
  rule that created any other world). Since decomposition only ever exposes PROPER
  subformulas (never duplicates a tree position into two lineage branches within one
  completed branch: `F∧`/`T∨` BETA picks one child per split; `F∨`/`T∧` ALPHA keeps both
  but at the SAME world, not a new one), the map `(world created) ↦ (the specific `.imp`
  tree-POSITION of φ0 whose firing created it)` is INJECTIVE into φ0's `.imp`-node positions.
  Combined with `intSubfmls_impCount_le` (`≤ φ.complexity` such positions), this gives
  `(worlds created) ≤ φ.complexity`, hence `eraseDups.length ≤ φ.complexity + 1` (the `+1`
  for world 0) — exactly the target bound.
- **Why this is NOT force-fittable into this dispatch**: formalizing the injection requires a
  NEW ghost/positional-tracking invariant threaded through an induction mirroring
  `Soundness.lean`'s `intExpandBranches_closed_unsat` (~700 lines, `Soundness.lean:1039-1714`)
  — i.e. a full top-level induction over `intExpandBranches`'s `go` recursion (outer induction
  on `fuel`, inner induction on `pending`), tracking an auxiliary "available `.imp` positions"
  ghost list/map alongside each branch, NOT a mirror of any existing Modal-K lemma (Modal-K's
  own `modalWorldBound` is exponential, `Sf^(depth+1)`, and never needed this argument — this
  is genuinely NEW mathematics for the intuitionistic calculus, not a port). Estimated
  ~500-800 lines given the `intExpandBranches_closed_unsat` scale comparison, exceeding the
  ~400-line H8 split threshold for a single dispatch.
- **Recommended next-dispatch strategy**: define a ghost position-tracking predicate (e.g. an
  injective labeling `originPos : Nat → List Nat` from world-label to a path-into-φ0's-tree,
  or reuse a Finset-of-positions bookkeeping list threaded as an extra invariant parameter
  alongside `hb`/`FreshAbove` in a `suffices`-based induction exactly matching
  `intExpandBranches_closed_unsat`'s shape), then prove: (a) positions are consumed exactly
  once (via the `expanded`-set + `.pos`-only-propagation facts above), (b) the ghost list's
  length is bounded by `intSubfmls_impCount_le`, (c) `nextWorld - 1 ≤` ghost list length at
  every reachable state. Re-verify against Phase 9/10's actual needs first (three independent
  dispatches — Phase 7, 7.2, 8 — already confirmed this exact lemma was NOT needed for the
  fuel-sufficiency argument; only the containment fact above was load-bearing).

- **Goal:** Define the fixed finite universe and the counting-against-universe work, and prove the linear
  world bound (Modal-K `FmpMeasure` pattern). FILE-DISJOINT from Phase 5.
- **Tasks:**
  - [x] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [x] Define `intUniverse φ : List (ISF Atom)` (the `(sign, subformula, world)` cells,
        `|U| ≤ 2·(2c+1)·(c+2)`) and `intWork U b e` (mirror `modalWork`, `FmpMeasure.lean:180-196`,
        using the proven `countP`/`any` pattern rather than `List.diff`).
  - [x] Prove the branch-universe containment fact (`intApplyRuleFull_outputs_subset` +
        persistence-containment infrastructure) discharging the `hb` hypothesis
        `intExpMeasure_step_lt`/`_branch` take as an assumption. **COMPLETE, sorry-free.**
  - [ ] Prove `intExpandBranches_world_bound`: `(b.map (·.label)).eraseDups.length ≤ φ.complexity + 1`
        (report 07 §Q4 — holds with NO dedup; do NOT entangle with the Option-A dedup).
        **DEFERRED — precise continuation recorded above (position-injection argument,
        supporting combinatorial lemma `intSubfmls_impCount_le` already landed).**
  - [x] Scoped+grepped build GREEN; four sorries unchanged; committed `Scheme.lean` only:
        `task 317 phase 6.2: branch-universe containment (discharges step_lt hb)` (`bb4ffa3c`),
        `task 317 phase 6.2: intSubfmls_impCount_le (world-bound combinatorial core)`
        (`015f81c1`).
- **Estimated output:** ~200-350 lines. **Done when:** `intUniverse`, `intWork`, and
  `intExpandBranches_world_bound` are sorry-free. — `intUniverse`/`intWork`/containment
  ACHIEVED (~290 lines this dispatch); `intExpandBranches_world_bound` DEFERRED (precise
  continuation, see resolution note; estimated ~500-800 lines, a genuinely new
  positional-tracking induction not present in the Modal-K template).
- **Timing:** 3 hours. **Depends on:** 4. Logically parallel with Phase 5; R7-serialized only with
  other Scheme.lean phases (Phase 5 is `Expansion.lean` → truly concurrent).
- **Owned files:** `Scheme.lean`.

---

### Phase 7: [Wave B / B2] `intExpMeasure_step_lt` (per-step strict decrease) [COMPLETED]

- **Goal:** Prove each `go` step strictly decreases `intExpMeasure` — the hard B2 phase. World-creation
  and persistence via the `|U\b|+|U\e|` decrease, NOT branch complexity.
- **Resolution**: Landed `intExpMeasure` (mirror `modalExpMeasure`, `FmpMeasure.lean:197`) plus the full
  strict-decrease engine, sorry-free, in ONE dispatch (no split needed — ~205 lines, under the ~450-line
  split threshold). Key simplification versus the Modal-K template: the intuitionistic calculus has NO
  separate "persistent" step kind inside `go`'s single-step transition (`applyPersistenceFixpoint` runs
  to full fixpoint BEFORE `intStepBranch`, not interleaved with it as a per-step case), so every arm of
  `go` (ALPHA, world-creation, `Sfor`-containment reuse, BETA) uniformly grows the expanded set by
  exactly `[sf]`. This let one core lemma `intWork_drop` (mirrors `modalWork_drop_linear`,
  `FmpMeasure.lean:2539`, generalized over an arbitrary successor branch `b'` with `∀ z ∈ b, z ∈ b'`)
  cover ALPHA/world-create (`b' = Branch.extendMany bh newForms`) AND the reuse arm (`b' = bh`, trivial
  reflexive `hsub`) without needing a `modalWork_drop_persistent` analogue at all. Landed: `intExpMeasure`
  (def), `intCount_notMem_append_drop`/`intCount_notMem_mono` (verbatim mirrors of
  `modalCount_notMem_append_drop`/`_mono`, `FmpMeasure.lean:2440,2517`, fully generic over
  `[BEq α][LawfulBEq α]`), `intWork_drop`, `intExpMeasure_split`/`_append` (mirror
  `modalExpMeasure_split`/`_append`, `FmpMeasure.lean:2826,2843`), and the main theorem
  `intExpMeasure_step_lt` covering the `.linearResult` arm of `intStepBranch` (ALPHA + world-creation +
  reuse, parameterized over the successor branch `b'`/`hsub` so all three instantiate the same lemma;
  the `.branchingResult` arm is dismissed by contradiction against the `.linearResult` pattern in the
  hypothesis, since this lemma's scope is the non-branching arm — the BETA/branching case was not
  separately proved this dispatch, see note below). Takes branch-containment `hb : ∀ x ∈ bh, x ∈
  intUniverse φ0` as a HYPOTHESIS (as the Modal-K template does for its own `hb`), confirming the
  orchestrator's prediction: `intExpandBranches_world_bound` (Phase 6's deferred distinct-label-count
  fact) was NOT needed for this lemma.
  **NOT landed this dispatch**: a separate `intExpMeasure_step_lt_branch` lemma for the BETA
  (`.branchingResult`) arm of `go` (F-and/T-or). The core `intWork_drop` engine already covers it
  trivially (apply it twice, once per branch, exactly as `modalExpMeasure_step_lt`'s branching case
  does with `pow3_two_add_one_le`) but the wiring lemma itself (a ~30-40 line analogue of the modal
  file's branching case, needing `intApplyRuleFull`'s two branching rules to expose a `.length = 2`
  fact, trivial since both literally construct 2-element list literals) was not additionally stated as
  its own top-level lemma. Recommend Phase 8/9's dispatcher decide whether to add it as a small
  follow-up lemma (using the SAME `intWork_drop`/`pow3_two_add_one_le` machinery already committed) or
  inline it directly into whichever downstream proof needs the BETA case.
- **Tasks:**
  - [x] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
  - [x] Define `intExpMeasure U branches expandedSets := Σ (b,e) ↦ 3 ^ intWork U b e` (mirror `modalExpMeasure`).
  - [x] Prove `intExpMeasure_step_lt`: one `go` step (ALPHA/world-create/reuse arm) gives
        `intExpMeasure (done ++ [b'] ++ rest) … + 1 ≤ intExpMeasure (done ++ bh :: rest) …` (mirror
        `modalExpMeasure_step_lt`, `FmpMeasure.lean:2873`). BETA/branching arm NOT separately wired
        (see resolution note).
  - [x] Scoped+grepped build GREEN; four sorries unchanged; committed `Scheme.lean` only:
        `task 317 phase 7: intExpMeasure_step_lt` (699c5fef).
- **Estimated output:** ~300-500 lines (pre-split candidate). **Actual:** ~205 lines, no split needed.
  **Done when:** `intExpMeasure_step_lt` is sorry-free. ACHIEVED for the linear/reuse arm; BETA-arm
  wiring lemma deferred as a small, low-risk follow-up (core engine already supports it).
  **Phase 7.2 resolution (landed)**: the deferred BETA-arm wiring lemma
  `intExpMeasure_step_lt_branch` is now landed, sorry-free, additive (~128 lines), mirroring
  `modalExpMeasure_step_lt`'s branching case (`FmpMeasure.lean:2921-2937`). Required one new
  helper not needed by Phase 7's linear-arm lemma: `intExpMeasure_const_exp` (mirrors
  `modalExpMeasure_const_exp`, `FmpMeasure.lean:2856`, using `List.map_prod_left_eq_zip` to
  collapse `intExpMeasure U newBs (newBs.map (fun _ => newExp))` to a plain sum). Case-splits on
  `intApplyRuleFull`'s two branching constructors (`.pos,.or` / F-or and `.neg,.and` / T-and, both
  literal 2-element lists of singletons per `Rules.lean:254,260`), applying `intWork_drop` twice
  (once per sub-branch) composed with `pow3_two_add_one_le`. Committed `Scheme.lean` only:
  `task 317 phase 7.2: intExpMeasure_step_lt_branch (BETA arm)` (`b5d2fc86`). Scoped+grepped
  build GREEN (`Intuitionistic.Completeness`, `Minimal.Completeness`); `checkInitImports` passes;
  `lean_verify` on the new lemma shows only `[propext, Classical.choice, Quot.sound]` (no new
  axioms); four inventory sorries unchanged (`Scheme.lean:535,1388`; `Completeness.lean:133`;
  `Minimal/Completeness.lean:125`).
- **Timing:** 4 hours. **Depends on:** 6 (uses `intUniverse`/`intWork`).
- **Owned files:** `Scheme.lean`.

---

### Phase 8: [Wave B / B2] `intExpMeasure_init_le_fuel` (initial measure ≤ raised fuel) [COMPLETED]

**RESOLVED (Phase 8.0 + Phase 8, commits `41d30054` + `e2c9bf3b`)**: `intFuel`'s exponent was
doubled from `2 * (2c+1) * (c+2)` to `4 * (2c+1) * (c+2)` in `Expansion.lean` (Phase 8.0),
mirroring `modalFuel`'s factor-of-2 exactly. All fuel-pinned callers (`Intuitionistic`/`Minimal`
`Completeness`, `DecisionProcedure`, `Soundness`) re-audited via full scoped build — GREEN, no
edits needed beyond the one-line exponent change (Postmortem/R5 territory concern: no
`Soundness.lean` edit was forced). `intExpMeasure_init_le_fuel` (Phase 8) then closed with
EQUALITY (no extra slack needed, simpler than the modal analogue's messier world-bound formula):
`intWork (intUniverse φ) [⟨.neg,φ,0⟩] [] ≤ 2·|intUniverse φ|` (via `List.countP_le_length` +
the `e=[]` exact-length case) `≤ 4·(2c+1)·(c+2)` (via `intUniverse_length_le` + `ring`) `=` the
doubled `intFuel` exponent exactly. Sorry-free, additive-only in `Scheme.lean`; axiom-clean
(`propext`, `Quot.sound` only, confirmed via `#print axioms`). Full `lake build`/`lake test`
green; four task-317 sorries unchanged. **World-bound necessity finding CONFIRMED**:
`intExpandBranches_world_bound` was NOT needed — the fix was a pure scalar exponent doubling,
orthogonal to distinct-world counting.

- **Goal:** Prove the initial measure is bounded by the raised fuel, using `|U| = O(c²)` and the linear
  world bound. This is where the fuel-raise pays off (impossible at the old fuel, report 07 §Q2).
- **BLOCKER (verified empirically, not a proof-difficulty issue — the goal is FALSE as stated)**:
  `intFuel φ := 3 ^ (2 * (2 * φ.complexity + 1) * (φ.complexity + 2))` (`Expansion.lean:462-463`)
  is under-provisioned by roughly a squaring factor relative to `intExpMeasure`'s actual initial
  value. `intWork U b []` with `b = [⟨.neg,φ,0⟩]` computes to `|U\b| + |U\∅| = (|U| - 1) + |U| =
  2·|U| - 1` (both terms genuinely scale with `|U|`, since the "not yet expanded" term starts at
  the FULL universe size when `e = []`) — NOT `≤ |U|` as the dispatch's proposed strategy assumed.
  Verified via `lean_run_code #eval` on two examples (before any file edit, per H2):
  - `φ = atom "p"` (complexity 0): `|intUniverse φ| = 4`, `intFuel φ = 3^4 = 81`,
    `intWork_init = 7 = 2·4 - 1`, `intExpMeasure_init = 3^7 = 2187 > 81 = intFuel φ`.
  - `φ = atom "p" → atom "q"` (complexity 1): `|intUniverse φ| = 18`, `intFuel φ = 3^18 =
    387,420,489`, `intWork_init = 35 = 2·18 - 1`, `intExpMeasure_init = 3^35 =
    50,031,545,098,999,707 ≫ intFuel φ`.
  Both examples exactly match the closed form `intWork_init = 2·|intUniverse φ| - 1`, confirming
  this is a systematic ~2x exponent gap, not a corner case. The Modal-K template does NOT have
  this gap: `modalFuel`'s exponent (`4 * (2·modalComplexity φ + 1) * (modalWorldBound φ + 1)`,
  `FmpMeasure.lean:232-233,249-251`) is already **2×** `modalUniverse_length_le`'s bound
  (`2 * (2·modalComplexity φ + 1) * (modalWorldBound φ + 1)`, `FmpMeasure.lean:155-157`) — see
  `modalExpMeasure_entry_le_fuel`'s own `hexp`/`heq` step (`FmpMeasure.lean:231-242`), which
  derives exactly `2 · |modalUniverse φ|` as the needed bound before invoking
  `Nat.pow_le_pow_right`. `intFuel`'s exponent (Phase 5, `Expansion.lean:462-463`,
  "`intFuel φ` was pre-sized against" `intUniverse_length_le`'s bound, per `Scheme.lean:1894-1897`'s
  doc comment) was set equal to the universe-length bound with NO doubling, apparently an
  oversight carried since Phase 5 — first surfaced now because Phase 6/7 fixed `intUniverse`'s
  concrete size and `intWork`'s concrete formula, making the gap computable.
  **Fix required (out of this dispatch's territory — `Expansion.lean` is read-only under R7)**:
  double `intFuel`'s exponent, e.g. `4 * (2 * φ.complexity + 1) * (φ.complexity + 2)` (mirroring
  the modal factor-of-2 pattern exactly), OR a tighter closed form covering the `2·|U| - 1`
  exact value. This requires a small `Expansion.lean` dispatch followed by RE-AUDITING all
  fuel-pinned callers per Phase 5's own audit note (`Soundness.lean`, `DecisionProcedure.lean`
  both variants, `Scheme.lean`'s hardcoded fuel-literal sites) — should be a safe increase (larger
  fuel only helps termination), but must be re-verified, not assumed.
  **World-bound necessity finding (as separately requested)**: this blocker is a pure scalar
  sizing gap in `intFuel`'s exponent, orthogonal to `intExpandBranches_world_bound` (the
  deferred distinct-label-count fact from Phase 6). The proposed Phase 8 strategy never
  references distinct-world counting — only `intUniverse_length_le` (a plain size bound). This
  is consistent with Phase 7's finding: `intExpandBranches_world_bound` remains UNNECESSARY for
  the fuel-sufficiency chain; Phase 10 should still not need it once `intFuel` is corrected.
  **No sorry, no vacuous statement, and no weakened restatement of `intExpMeasure_init_le_fuel`
  was introduced.** No `Scheme.lean` edit was made for this phase.
- **Tasks:**
  - [x] PREFLIGHT (R7): `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN (confirmed
        `b5d2fc86` before starting Phase 8 investigation).
  - [x] **Phase 8.0**: fixed `intFuel`'s exponent in `Expansion.lean` (doubled it, matching the
        Modal-K `modalFuel` factor-of-2 pattern) and re-audited all fuel-pinned callers
        (commit `41d30054`).
  - [x] Proved `intExpMeasure_init_le_fuel φ : intExpMeasure (intUniverse φ) [[⟨.neg,φ,0⟩]] [[]] ≤ intFuel φ`
        (closes with equality, no slack needed) after the fuel fix (commit `e2c9bf3b`).
  - [x] Scoped+grepped build GREEN; full `lake build`/`lake test` GREEN; four sorries unchanged;
        committed `Scheme.lean` only: `task 317 phase 8: intExpMeasure_init_le_fuel`.
- **Estimated output:** ~150-300 lines (Phase 8 proper) + a small `Expansion.lean` fix (Phase 8.0,
  separate dispatch, `Expansion.lean` territory). **Done when:** `intExpMeasure_init_le_fuel` is
  sorry-free — DONE.
- **Timing:** 2.5 hours (Phase 8 proper) + ~1 hour (Phase 8.0 fix + re-audit). **Depends on:** 5
  (uses `intFuel`), 6 (uses `intUniverse`/world bound), and now a NEW dependency: the `intFuel`
  exponent fix (Phase 8.0). Logically parallel with Phase 7; R7-serialized (both `Scheme.lean`,
  and Phase 8.0 touches `Expansion.lean`).
- **Owned files:** `Scheme.lean` (Phase 8 proper); `Expansion.lean` (Phase 8.0 fix, + `Soundness.lean`/
  `DecisionProcedure.lean` only if the re-audit forces it, separate commit, mirroring Phase 5's
  own territory-expansion precedent).

---

### Phase 9: [Wave B / discharge deferred Wave-A obligations] Add `sat_timp` + discharge, prove `intExtractValuation` monotonicity, close truthLemma T-imp (sorry 1) [BLOCKED]

**RESOLUTION (dispatch `sess_1783962327_d9c0b3`, commit `969782b5`)**: genuinely BLOCKED, not
deflected. Investigated all three deliverables against source (`Rules.lean`'s `intTImpRule`,
`Expansion.lean`'s `applyPersistenceFixpoint`, the exact `IExpandedConsistent_sat` call site inside
`intExpandBranches_openBranch_sat`) and found TWO independent gaps, neither closable without new
infrastructure: **(1) fuel entanglement** — identical in kind to the pre-existing
`intExtractValuation` monotonicity STOP-gate (`Scheme.lean:442-483`): `IExpandedConsistent_sat` is
only ever called on `bPers = applyPersistenceFixpoint bh edgesH (fuel'+1)`, and genuineness of
THAT fixpoint is not certified by any existing lemma — `intExpMeasure_step_lt` (Phase 7) bounds the
OUTER alpha/beta/world-creation loop only, not the INNER T-imp persistence recursion; a NEW
step-lt-style bound for `applyPersistenceFixpoint`'s own recursion is required, which is exactly
Phase 10's `intExpMeasure ≤ fuel` invariant-threading job, one level deeper. **(2) determinacy
(newly found, not in reports 08/09)**: even granting a genuine fixpoint, `intTImpRule` only
certifies `T(φ)@w' ∈ b → T(ψ)@w' ∈ b`, strictly weaker than the needed
`F(φ)@w' ∈ b ∨ T(ψ)@w' ∈ b` (report 09 §a.4's proposed signature); bridging the two needs a
`Sub(φ0)` determinacy/bivalence fact that exists nowhere in `IBranchSaturation` today. Full
evidence trail recorded in a new STOP-gate block in `Scheme.lean` (immediately after the existing
`intExtractValuation` monotonicity STOP-gate, before `## Parametric Truth Lemma`). Given the
zero-debt invariant (no sorry / no vacuous / no new axiom), the field could NOT be added without
forcing a new sorry at `IExpandedConsistent_sat`'s only construction site (currently sorry-free) —
so NO field/proof edit was made; only the STOP-gate documentation (comment-only, scoped build
GREEN, 807/807 jobs) was committed. Four inventory sorries UNCHANGED (line numbers shifted +50 in
`Scheme.lean` from the doc insertion; re-grep before any further edit). **Recommendation: fold
Phase 9's three deliverables into Phase 10**, which must additionally build (a) the
persistence-loop step-lt lemma and (b) the determinacy fact (or a restated, weaker `sat_timp` plus
a compensating completeness argument) before `sat_timp`/monotonicity/truthLemma-T-imp can close.
See `.orchestrator-handoff.json` `continuation_context.next_phase_should_build` for the itemized
list. This requires a `/plan`/`/revise` pass on this plan before the next `/implement --hard`
dispatch, not another blind implementation attempt.

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
