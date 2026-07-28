# Implementation Plan: Tableau Completeness — Blocking Bridge, Fuel-Sufficiency Development, R1 Restatement (Skeleton)

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Status**: [NOT STARTED]
- **Effort**: 24-40 hours (8 phase-sized dispatches; skeleton — full sorry-zero completion is
  explicitly NOT claimed by this plan alone, see Planned Strategic Sorries)
- **Dependencies**: 456 (completed — Blocking.lean), 552 (completed), 574 (completed — ancestor
  blocking repair). Subsumes: 583 (blocked — its R1 restatement is Phase 6 of this plan; close
  583 as superseded when Phase 6 lands). Defers to: 430 (planned — the two Completeness.lean
  bridge sorries stay in 430's territory; this plan does not touch them)
- **Research Inputs**:
  - reports/14_blocker-analysis.md — "## Adversarial Self-Verification" section (PRIMARY; the
    pre-repair body of reports 13/14 is STALE and must not be planned from)
  - specs/583_restate_intexpandbranches_openbranch_sat/reports/01_restate-openbranch-sat.md
    (F3 equivalence, F5 restatement R1, F6 prohibitions, prerequisite acceptance gate)
  - In-code notes at HEAD: Scheme.lean:100-111 (D8), Scheme.lean:504-557 (STOP-gate),
    Scheme.lean:1591-1605 (intUniverse warning), Scheme.lean:2526-2550 (fuel-0 refutation),
    Expansion.lean:450-494 (divergence witness), Expansion.lean:246-320 (ancestor loop-check)
  - plans/12_world-bound-prereq-threading.md (prior plan, reference only: Phases 0-2 landed;
    Phase 3 BLOCKED on the refuted pre-repair linear bound)
- **Artifacts**: plans/13_fuel-sufficiency-skeleton.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-compliance.md
  - .claude/rules/lean4.md
  - .claude/rules/cslib.md
- **Type**: cslib
- **Plan Version**: 13
- **Skeleton**: true (see `## Planned Strategic Sorries`; `plan_metadata.skeleton: true`)

## Overview

Four bare sorries remain (verified 2026-07-28): `Intuitionistic/Scheme.lean:617` (truthLemma
T-imp), `Intuitionistic/Scheme.lean:2551` (fuel-0 case of `intExpandBranches_openBranch_sat`,
REFUTED as stated), `Intuitionistic/Completeness.lean:133`, `Minimal/Completeness.lean:125`.
Per 583's F3 equivalence result, ALL FOUR bottom out in one missing development: the
post-blocking fuel-sufficiency theorem — a world bound `WBound φ` derived from the
ancestor-blocking combinatorics, an enlarged universe `intUniverseExt`/measure
`intExpMeasureExt`, an `intFuel` resize, and the `hUniv`/`hNW` threading invariants. No queued
task covers this gap; this plan incorporates it as its own phase-block (Phases 2-5), because
spawning it as a separate task would only add a dispatch boundary in the middle of one
tightly-coupled development inside two files this task already owns.

**Honest scope verdict**: full four-sorry completion in one plan is NOT credible. The
world-bound combinatorics is sketched, not proven (583's stated medium-confidence uncertainty),
and the S4 analogues of exactly this obligation are blocked tasks — independent evidence it is
substantial. This plan is therefore a SKELETON: Phases 1, 3, 4, 6, 7 land unconditional or
conditional-but-provable value; Phases 2 and 5 carry the research-grade risk and each ends in a
declared strategic-sorry division point (DP-1, DP-2) if the proof does not close within the
phase. The two Completeness bridges (DP-3, DP-4) are pre-existing sorries deferred to existing
task 430 and are NOT in this plan's discharge scope. Definition of done for this plan: sorries
at `Scheme.lean:2551` and `Scheme.lean:617` discharged (modulo at most DP-1/DP-2), no false
statement remains anywhere in the subtree, build green, full CI gate passed.

### Territory Resolutions (settled up front)

| Overlap | Resolution |
|---------|------------|
| Task 583 (blocked) owns the `Scheme.lean:2551` restatement | **SUBSUMED**: Phase 6 implements exactly 583's F5 form R1 (`hUniv`/`hNW`/`hFuel` hypothesis threading). When Phase 6 lands, 583 should be closed as superseded — orchestrator/user action, not this plan's |
| Task 430 (planned) owns the two Completeness bridges (IAtomPersist route) | **DEFERRED**: this plan does not modify `Intuitionistic/Completeness.lean` or `Minimal/Completeness.lean` beyond comment accuracy. 430's existing dependency on 317 is already the right direction |
| Task 456's Blocking.lean not yet consumed by the propositional tableau | **CONSUMED here**: Phase 1 is the bridge. `IBranch Atom` is definitionally `Branch (Proposition Atom) Nat` (`Rules.lean:73-76` vs `Branch.lean:47`), so the counting layer applies directly |

### Source-to-Implementation Mapping (H3; Tier 3 primary, Tier 1 anchors)

Literature note: per-repo sub-index present (34 entries) but contains no chunks for the anchors
below (search returned degraded/empty, matching 583's finding); Tier 1 anchoring rests on
`references.bib` entries (all BibKeys verified: `references.bib:211` Fitting1983, `:218`
Dyckhoff1992, `:239` GargGenoveseNegri2012, `:1041` Massacci2000) plus in-file provenance notes.

| Source | Claim | Lean Target | Status |
|--------|-------|-------------|--------|
| Fitting1983, Ch. 4 | Systematic intuitionistic tableau: open saturated branch yields Kripke countermodel; construction presumes the procedure terminates in saturation | `openBranch_countermodel` (Scheme.lean:2944), `intExpandBranches_openBranch_sat` restatement R1 (Phase 6) | pending |
| GargGenoveseNegri2012, §III | Count of distinct forced sets bounds blocking chains | `distinctTypes_le_pow`, `strictChain_le_card` (Blocking.lean:150,185 — landed sorry-free); consumed in Phase 2 | transcribed (456) / pending (consumption) |
| Massacci2000, Tech. 8.1/8.2 | Blocking side conditions are logic-specific | ψ-conditioned ancestor check `intFImpReuseWitnessAnc?` (Expansion.lean:260 — landed, 574); Phase 2 reasons FROM its spec, never edits it | transcribed (574) |
| Dyckhoff1992 | Termination via calculus-side contraction-free design (contrast route; not taken) | (none — provenance only) | n/a |
| 583 report F5 | Restatement R1 exact hypothesis set; fuel-0 discharge shape; call-site repair shape | Phase 6 | pending |

### Preserved Assets

The following work is complete, `lake build`-green at HEAD, and must not regress:

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| Ancestor-blocking repair: `intFImpReuseWitnessAnc?` + `_spec` | Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean:260,293 | [COMPLETED] (574) | 2026-07-28 |
| D8 `sat_fimp` (numeric conjunct dropped) + live `sat_timp` field | Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:100-118 | [COMPLETED] (574/552) | 2026-07-28 |
| `.pos, .imp` branching arm | Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean:245-268 | [COMPLETED] (552) | 2026-07-28 |
| Succ-fuel case of `intExpandBranches_openBranch_sat` incl. saturation leaf | Scheme.lean:2552-2915 | [COMPLETED] | 2026-07-28 (583 report) |
| Measure engine (sorry-free, currently unused): `intWork`, `intExpMeasure`, `intExpMeasure_step_lt`, `_step_lt_branch`, `_init_le_fuel`, `applyAllTImpRules_count_drop`, `applyPersistenceFixpoint_genuine_of_count_le_fuel` | Scheme.lean:1913-2487 | [COMPLETED] | 2026-07-28 (583 report F2) |
| Shared blocking module + counting layer | Cslib/Foundations/Logic/Tableau/Blocking.lean | [COMPLETED] (456), lean_verify clean | 2026-07-28 |
| Conformance corpus, 24 rows incl. divergence-witness regression row 20 | CslibTests/TableauConformance.lean | [COMPLETED] | 2026-07-28 |
| FMP decidability route | `Cslib.Logic.PL.decidableDerivableIntPropAxiomFMP` | [COMPLETED], sorry-free | 2026-07-28 (lean_verify) |
| In-code refutation/divergence records | Scheme.lean:1591-1605, 2526-2550; Expansion.lean:450-494 | [COMPLETED] | 2026-07-28 |

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the reports-13/14 adversarial
verification, 583's F6, the in-file directives, and twelve failed prior plan versions.

**Do NOT**:
- Plan against or state the refuted bound form `(b.labels.map b.typeAt).eraseDups.length ≤
  2^U.length` — REFUTED by sign doubling (456's research: 5 distinct type-lists over
  `U = [p,q]` vs bound 4). Only the landed signed form is valid: `distinctTypes_le_pow` with
  `2 ^ V.card` over `V : Finset (Sign × F)`, or `posTypeAt` over `U : Finset F` for `2 ^ U.card`.
- Re-add the D8-dropped `w ≤ w'` conjunct to `sat_fimp` (Scheme.lean:100-106) — false under
  ancestor blocking, and never consumed downstream.
- Attempt the containment invariant `∀ x ∈ b, x ∈ intUniverse φ` against the CURRENT
  `intUniverse` linear range — refuted (Scheme.lean:1591-1599); any new bound must come from
  the blocking combinatorics (Expansion.lean:485-489 directive), i.e. Phase 2's `WBound`.
- Edit `intFImpReuseWitnessAnc?` or its `_spec` (Expansion.lean:260-320) — 574's landed
  contract. In particular never Option B (appending fresh `F(ψ)@x` on reuse — proven UNSOUND,
  see Expansion.lean:250-253).
- Weaken/vacuize `intExpandBranches_openBranch_sat`, `tableau_complete`, or relocate a sorry
  into `tableau_complete`, the `Decidable` instance, or a standalone "no-exhaustion" axiom
  (583 F6 forbidden-deferral list; in-file prohibition Scheme.lean:502, 556-557).
- Add `.fuelExhausted` to `IntTableauResult` (583's R2 fallback) — rejected: relocates the
  identical obligation into `tableau_complete` and `instDecidableIValid` where nothing closes
  it. R1 hypothesis-threading is the settled form.
- Discharge `Scheme.lean:2551` or `Scheme.lean:617` alone via a weakened statement — the
  in-file STOP-gate (Scheme.lean:554-557) directs both be closed together in one pass over the
  same invariants (Phases 6-7, consecutive).
- Touch `Intuitionistic/Completeness.lean:133` or `Minimal/Completeness.lean:125` (430's
  territory) beyond comment-accuracy updates in Phase 8.
- Re-derive the divergence refutation or re-attempt `intExpandBranches_world_bound` /
  `hnw : nextWorld ≤ φ.complexity + 1` as previously stated — refuted, not hard.
- Place any sorry not corresponding to a `## Planned Strategic Sorries` row without flagging it
  as a plan-unanticipated deviation in the summary (plan-format deviation flag).

**MUST preserve**:
- Everything in the Preserved Assets table (in particular: do not regress the succ-fuel case of
  `intExpandBranches_openBranch_sat`, the measure engine, or any conformance corpus row).
- Repo-wide bare-sorry count must never increase net of the declared division points: each new
  sorry must be a DP row, and Phases 6-7 must each strictly decrease the count by one.
- `Blocking.lean` is read-only for this task (Foundations module owned by 456's landed design).

**Design decisions are SETTLED** (do not re-open without concrete counterexample):
- R1 hypothesis-threading restatement (not R2 trichotomy) — adversarially challenged and
  retained in 583's report.
- Ancestor-directed blocking with explicit `F(ψ)@x` conjunct; D8 conjunct drop.
- This plan subsumes 583 and defers the bridges to 430 (Territory Resolutions above).
- The signed, Finset-valued counting layer from Blocking.lean is the only counting substrate.
- Fuel-sufficiency is incorporated here (not spawned) — the development is inseparable from the
  restatement threading in the same two files.

## Goals & Non-Goals

- **Goals**:
  - Consume Blocking.lean's counting layer in the intuitionistic tableau (unconditional value).
  - Build the post-blocking fuel-sufficiency development (`WBound`, `intUniverseExt`,
    `intExpMeasureExt`, `intFuel` resize, threading invariants), with risk concentrated at two
    declared division points instead of diffused across false statements.
  - Restate `intExpandBranches_openBranch_sat` per R1 and discharge `Scheme.lean:2551`.
  - Discharge `truthLemma`'s T-imp case (`Scheme.lean:617`) in the same pass (STOP-gate).
  - Leave zero FALSE statements in the subtree; leave all remaining sorries tracked (DP rows).
- **Non-Goals**:
  - The two Completeness bridge sorries (430's scope — IAtomPersist route).
  - Any change to `Blocking.lean`, `intFImpReuseWitnessAnc?`, or the conformance corpus's
    landed rows (row additions for new regression checks are allowed in Phase 8).
  - A termination THEOREM for the decision procedure beyond what `WBound` requires (full
    decidability hygiene beyond the existing instances is out of scope).

## Risks & Mitigations

- **Risk**: The chain-bound combinatorics (Phase 2) does not close — the ψ-conditioned blocking
  check may not yield a clean pigeonhole (583: "sketched, not proven"; S4 analogues blocked).
  **Mitigation**: DP-1 strategic sorry, tracked, with follow-up task; Phases 3-7 are designed
  to proceed against the *statement* of the bound, so the skeleton still lands.
- **Risk**: `hNW` preservation (Phase 5) needs a creation-count invariant relating the
  `nextWorlds` counter to tree size — additional threading not in 583's sketch.
  **Mitigation**: DP-2 strategic sorry on the same follow-up task.
- **Risk**: The engine lemmas turn out NOT to be universe-parametric (some proof step uses the
  literal `intUniverse` range). **Mitigation**: Phase 3's Scope Hypothesis; if a proof does not
  re-run, generalize the single offending lemma over an abstract universe list with a
  membership-closure hypothesis — its statement shape is already parametric per 583 F5.
- **Risk**: `intFuel` resize breaks conformance rows or `#eval` feasibility. **Mitigation**:
  early exit on saturation/closure means fuel is a bound, not a step count; Phase 4 verifies
  every corpus row before commit (Scope Hypothesis on fuel-pinned rows).
- **Risk**: Same-file churn — every phase writes `Scheme.lean`. **Mitigation**: strictly
  sequential waves (H7: no parallel dispatch; single-owner territory), commit-per-green-substep.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 2, 3 |
| 6 | 6 | 3, 4, 5 |
| 7 | 7 | 5, 6 |
| 8 | 8 | 1-7 |

**Parallel opportunities: NONE — declared explicitly.** All phases write
`Cslib/Logics/Propositional/Tableau/Intuitionistic/{Scheme,Expansion}.lean`; H7 territory is
single-owner and waves are strictly sequential. (Phase 3 depends on Phase 2 only for the
`WBound` DEFINITION, not its proof — it proceeds unimpeded if DP-1 is sorried.)

### Phase 1: Blocking.lean consumption bridge [NOT STARTED]
- **Goal:** The propositional tableau imports and can invoke 456's counting layer.
- **Tasks:**
  - [ ] Import `Cslib.Foundations.Logic.Tableau.Blocking` into the intuitionistic development
    (at `Expansion.lean` or `Scheme.lean`, whichever the lemmas land in; respect shake).
  - [ ] Bridge lemma `posFormulasAt_mem_iff`: `φ ∈ posFormulasAt b w ↔ φ ∈ Branch.posTypeAt b w`
    (membership equivalence; `IBranch Atom` is definitionally `Branch (Proposition Atom) Nat`,
    so no coercion is needed — only the local-def-to-`posTypeAt` content equivalence, which
    differs by an `eraseDups`).
  - [ ] Instantiations at the propositional types: `distinctTypes_le_pow` with
    `V := (intSubfmls φ).toFinset ×ˢ {Sign.pos, Sign.neg}` (or equivalent signed universe) and
    `exists_typeAt_eq_of_card_lt`; confirm `strictChain_le_card` applies without wrapping.
- **Timing:** 1 dispatch. Estimated output: ~120-180 lines.
- **Depends on:** none
- **Verification Tier:** local
- **Done when:** bridge lemmas build sorry-free under a scoped
  `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`; zero new sorries;
  no change to any existing declaration.

### Phase 2: `WBound` definition + ancestor-chain bound lemma (division point DP-1) [NOT STARTED]
- **Goal:** A concrete `WBound : Proposition Atom → Nat` and the chain lemma that makes it a
  bound: along any edge chain of created worlds on a branch, chain length is bounded via the
  pigeonhole/strict-chain layer, because an over-long chain forces two chain worlds with equal
  positive type and equal creation obligation ψ, contradicting
  `intFImpReuseWitnessAnc?_spec`'s negation at the later creation site.
- **Tasks:**
  - [ ] Define `intChainBound φ` (per-chain depth bound, of order
    `(impCount + 1) * 2 ^ (2 * |Sub φ|)` — exact form implementer's choice, from the blocking
    combinatorics ONLY, never from `intUniverse`'s linear range) and
    `WBound φ` (total world bound: branching factor ≤ imp-subformula count per world, so a
    tree bound of order `(impCount + 1) ^ (intChainBound φ + 1)`; exponential-in-exponential
    is acceptable — it is a proof-side bound, not an evaluation step count).
  - [ ] State the chain lemma (working name `intCreatedChain_le`): for an edge chain
    `w_0 → … → w_k` of worlds created by unblocked `intFImpRule` firings on branch `b`,
    `k ≤ intChainBound φ`. Proof route: pigeonhole (`exists_typeAt_eq_of_card_lt` over
    `(posTypeAt, ψ)` pairs, Phase 1 instantiations) + the five-conjunct negation of
    `intFImpReuseWitnessAnc? = none` at the later site.
  - [ ] Attempt the proof within this dispatch. STOPPING CONDITION (bounded-unit): either the
    proof closes, or place the DP-1 strategic sorry on exactly `intCreatedChain_le` (one
    declaration) with the mandated comment
    (`-- sorry: assumes the ψ-conditioned pigeonhole closes; deferred: research-grade
    combinatorics; follow-up: task 585`), record it in `sorry_inventory` with
    `strategic: true`, and proceed. Do NOT iterate past one dispatch.
- **Timing:** 1 dispatch. Estimated output: ~200-350 lines.
- **Depends on:** 1
- **Verification Tier:** local
- **Scope Hypothesis:** the ψ-conditioned check admits a `(posTypeAt, ψ)`-pair pigeonhole with
  no further side condition; confirm at implementation against `intFImpReuseWitnessAnc?_spec`'s
  exact five conjuncts (in particular the `F(ψ)@x ∈ bPers` conjunct's availability at the
  earlier chain world). If a further condition is needed, enlarge the pigeonhole index type —
  never weaken the check.
- **Done when:** `WBound`/`intChainBound` defined; `intCreatedChain_le` stated with its final
  hypothesis set and either proved or carrying exactly the DP-1 sorry; scoped build green.

### Phase 3: `intUniverseExt` / `intExpMeasureExt` + engine re-target [NOT STARTED]
- **Goal:** The F2 measure engine runs over the enlarged universe
  `List.range (WBound φ + 1)` in place of `List.range (φ.complexity + 2)`.
- **Tasks:**
  - [ ] Define `intUniverseExt φ` (same cell structure as `intUniverse`, world range
    `WBound φ + 1`) and `intExpMeasureExt φ := intExpMeasure (intUniverseExt φ)` (or keep
    `intExpMeasure` parametric in `U` as it already is and only add the `Ext` universe + its
    length lemma `intUniverseExt_length_le`).
  - [ ] Re-target the engine: `intExpMeasure_step_lt`, `intExpMeasure_step_lt_branch`,
    `applyAllTImpRules_count_drop`, `applyPersistenceFixpoint_genuine_of_count_le_fuel` over
    `intUniverseExt`. Per 583 F5 these are parametric in the universe list ("statements are
    parametric; proofs re-run"); the load-bearing generalization is
    `intApplyRuleFull_outputs_subset`'s replacement: subformula-content closure into
    `intUniverseExt` under the hypothesis `nextWorld ≤ WBound φ` (the hypothesis is DISCHARGED
    in Phase 5; here it is threaded as a premise, which is provable without DP-1).
- **Timing:** 1 dispatch. Estimated output: ~250-400 lines.
- **Depends on:** 2 (definition only — proceeds if DP-1 is sorried)
- **Verification Tier:** local
- **Scope Hypothesis:** every engine proof re-runs over the enlarged universe with only
  membership/length facts about `U` (confirm by re-elaboration; the engine lemmas at
  Scheme.lean:2077/2145/2358/2424 take `hb : ∀ x ∈ b, x ∈ intUniverse φ0` as a premise and
  nowhere unfold the world range). If one proof step uses the literal range, generalize that
  single lemma over an abstract `U` with a closure hypothesis.
- **Done when:** enlarged-universe engine lemmas build sorry-free (given only Phase 2's
  statements); zero new sorries in this phase; the ORIGINAL `intUniverse` block is left intact
  (deprecation notes deferred to Phase 8).

### Phase 4: `intFuel` resize + `init_le_fuel` analogue + corpus re-verify [NOT STARTED]
- **Goal:** The pinned fuel at every call site is provably at least the initial enlarged
  measure.
- **Tasks:**
  - [ ] Resize `intFuel φ` (Expansion.lean:510) to dominate
    `intExpMeasure (intUniverseExt φ) [[⟨.neg, φ, 0⟩]] [[]]` — target shape
    `3 ^ (2 * |intUniverseExt φ| )`-class, mirroring the existing doubling note
    (Expansion.lean:498-509); update that docstring.
  - [ ] Prove `intExpMeasureExt_init_le_fuel` (the Scheme.lean:2279 analogue over the enlarged
    universe).
  - [ ] Re-verify EVERY conformance corpus row (`lake test`), especially divergence-witness
    row 20: early exit on saturation/closure means larger fuel must not change any result; any
    flipped row is a hard failure of this phase, not something to re-pin.
- **Timing:** 1 dispatch. Estimated output: ~120-250 lines.
- **Depends on:** 3
- **Verification Tier:** interface (changed def consumed by `DecisionProcedure.lean`, both
  `Completeness.lean` files, and `CslibTests/TableauConformance.lean` — build all four
  dependents in-phase)
- **Scope Hypothesis:** no conformance row pins a literal `intFuel` VALUE (they pin results);
  confirm by grep over `CslibTests/TableauConformance.lean` before editing. `#eval` cost is
  unaffected because runs exit at saturation/closure before consuming fuel.
- **Done when:** resize landed, `init_le_fuel` analogue sorry-free, `lake test` green,
  dependents build green.

### Phase 5: `hUniv`/`hNW` threading invariants (division point DP-2) [NOT STARTED]
- **Goal:** Preservation lemmas for the two new R1 hypotheses through all four recursion arms
  of `intExpandBranches` (linear, branching, world-creating with reuse, world-creating with
  fresh mint).
- **Tasks:**
  - [ ] `hUniv` preservation: rule outputs stay in `intUniverseExt φ0` — subformula-content
    side via the existing subformula closure lemmas; world-label side via `hNW`.
  - [ ] `hNW` preservation (`∀ nw ∈ nextWorlds, nw ≤ WBound φ0`): only the fresh-mint arm
    increments; needs the creation-count invariant "labels minted so far ≤ tree size ≤
    `WBound φ0`" tied to Phase 2's chain lemma. This is the second research-grade
    concentration. STOPPING CONDITION: prove within this dispatch, or place the DP-2 strategic
    sorry on exactly the one `hNW`-preservation lemma for the fresh-mint arm, with the mandated
    comment and `sorry_inventory` entry (`follow-up: task 585`), and proceed.
  - [ ] Package both as the `IAllConsistent`-style parallel-list invariants R1's induction will
    thread (mirror `IAllConsistent`/`IAllAccessConsistent`'s existing shape,
    Scheme.lean:2518-2520).
- **Timing:** 1 dispatch. Estimated output: ~250-400 lines.
- **Depends on:** 2, 3
- **Verification Tier:** local
- **Done when:** both invariants stated in final form and threaded-form lemmas build, with at
  most the DP-2 sorry; scoped build green.

### Phase 6: R1 restatement of `intExpandBranches_openBranch_sat` + fuel-0 discharge + call-site repair [NOT STARTED]
- **Goal:** `Scheme.lean:2551` discharged. Implements EXACTLY 583's F5 form R1 (subsumes task
  583).
- **Tasks:**
  - [ ] Add hypotheses `hUniv`, `hNW` (Phase 5's invariants), `hFuel :
    intExpMeasure (intUniverseExt φ0) branches expandedSets ≤ fuel` to
    `intExpandBranches_openBranch_sat` (Scheme.lean:2510-2523); the lemma gains a `φ0`
    parameter if not already threaded.
  - [ ] Fuel-0 discharge per 583 F5: `hFuel` at `fuel = 0` forces measure 0; each worklist
    cell contributes `3 ^ k ≥ 1`, so the zipped worklist is empty; `intExpandBranches [] … 0`
    reduces to `.closed`, contradicting `h`. No saturation reasoning at fuel 0.
  - [ ] Succ-case re-establishment of the three new hypotheses through the existing (PRESERVED)
    proof body: linear arm via `intExpMeasure_step_lt` (enlarged), beta arm via
    `_step_lt_branch`, persistence non-increase via `intCount_notMem_mono` + iterated
    `applyAllTImpRules_subset`, `hUniv`/`hNW` via Phase 5.
  - [ ] Call-site repair in `openBranch_countermodel` (Scheme.lean:2965-2968): discharge
    `hFuel` by `intExpMeasureExt_init_le_fuel` (Phase 4), `hUniv` by singleton membership,
    `hNW` by `1 ≤ WBound φ0`.
  - [ ] Replace the fuel-0 refutation comment block (Scheme.lean:2526-2550) with a short note
    recording that the refutation applied to the PRE-R1 statement and pointing at R1's
    hypotheses (keep the counter-instance citation — it is the durable record of why the
    hypotheses exist).
- **Timing:** 1 dispatch. Estimated output: ~300-450 lines (net; much is hypothesis threading
  through the existing succ-case body).
- **Depends on:** 3, 4, 5
- **Verification Tier:** local
- **Done when:** sorry at (what is now) `Scheme.lean:2551` GONE; repo bare-sorry count in the
  subtree strictly decreased by one (modulo DP-1/DP-2 which live in different declarations);
  `openBranch_countermodel` and `tableau_complete` build unchanged in statement; scoped build
  green.

### Phase 7: `truthLemma` T-imp discharge via persistence fixpoint sufficiency [NOT STARTED]
- **Goal:** `Scheme.lean:617` discharged, honoring the STOP-gate's one-pass directive with
  Phase 6 (same invariants, consecutive dispatches).
- **Tasks:**
  - [ ] Thread `applyPersistenceFixpoint_genuine_of_count_le_fuel` (enlarged-universe version,
    Phase 3) through the open-branch extraction so the returned branch is at a GENUINE
    persistence fixpoint: every world accessible from a `T(φ'→ψ')` source carries its own copy
    (the `applyAllTImpRules` copy channel at a fixpoint). Likely lands as an extra conjunct in
    the R1 conclusion or a companion lemma over the same induction — implementer's choice, but
    the STATEMENT of `truthLemma` itself must not weaken.
  - [ ] Close the T-imp case (Scheme.lean:601-617) with `sat_timp` per the in-file analysis:
    the `F(φ')@w'` arm contradicts via `ih_φ'.2`, the `T(ψ')@w'` arm closes via `ih_ψ'.1`.
  - [ ] Update the STOP-gate note (Scheme.lean:504-557) from "Gap 1 UNCHANGED" to resolved,
    citing the fixpoint-sufficiency route.
- **Timing:** 1 dispatch. Estimated output: ~200-350 lines.
- **Depends on:** 5, 6
- **Verification Tier:** local
- **Done when:** sorry at `Scheme.lean:617` GONE; count strictly decreased by one again;
  `truthLemma`'s statement unchanged; scoped build green.

### Phase 8: Documentation accuracy + full CI gate [NOT STARTED]
- **Goal:** No stale claim survives; the full repository gate passes.
- **Tasks:**
  - [ ] Update `intUniverse`'s warning docstring (Scheme.lean:1585-1599) to point at
    `intUniverseExt`/`WBound` as the live development; keep the refutation record.
  - [ ] Sync comments in both `Completeness.lean` files ONLY where they now misstate what is
    deferred (the bridge sorries themselves are untouched — 430's territory).
  - [ ] Optionally add a conformance regression row exercising the resized fuel path.
  - [ ] Sorry accounting: exactly the DP rows remain (DP-3/DP-4 always; DP-1/DP-2 only if
    placed) — enumerate in the summary's `sorry_inventory`.
  - [ ] Full CI gate in order: `lake build`, `lake exe checkInitImports`, `lake lint`,
    `lake exe lint-style`, `lake test`, `lake exe mk_all --module` (only if a new file was
    added), `lake shake --add-public --keep-implied --keep-prefix`.
- **Timing:** 1 dispatch. Estimated output: ~80-150 lines.
- **Depends on:** 1-7
- **Verification Tier:** full
- **Done when:** all gates green; summary written; `sorry_inventory` complete and matching the
  Planned Strategic Sorries table (or flagging deviations).

## Planned Strategic Sorries

| Division Point | File / Line / Statement | Assumption | Why Deferred | Follow-Up Task |
|-----------------|--------------------------|------------|---------------|----------------|
| DP-1: chain-bound lemma | Scheme.lean, TBD (Phase 2; `intCreatedChain_le`) | The ψ-conditioned ancestor-blocking pigeonhole bounds created-world chains by `intChainBound φ` | Research-grade combinatorics (583: sketched, not proven; S4 analogues blocked); one-dispatch attempt budget, sorry placed only on failure | 585 |
| DP-2: `hNW` preservation, fresh-mint arm | Scheme.lean, TBD (Phase 5) | Labels minted on a branch ≤ tree size ≤ `WBound φ` | Creation-count invariant beyond 583's sketch; same follow-up development as DP-1 | 585 |
| DP-3: intuitionistic validity bridge (pre-existing, NOT placed by this plan) | Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:133 (`intuitionisticTableau_complete`) | Upward-closure of `intExtractValuation b` along `intAccessPreorder edges` (IAtomPersist route) | Owned by existing planned task 430 (deps already point 430 → 317); presupposes saturated branches, i.e. this plan's output | 430 |
| DP-4: minimal validity bridge (pre-existing, NOT placed by this plan) | Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:125 (`minimalTableau_complete`) | Upward-closure of `intExtractValuation b` AND `minBranchBotForces b` along the frame | Same as DP-3 | 430 |

Notes: DP-1/DP-2 are contingent — if the Phase 2/5 proofs close within budget, no sorry is
placed and the follow-up task 585 should be closed as unnecessary by the
orchestrator/user. DP-3/DP-4 are pre-existing sorries recorded here for complete accounting;
they are not new placements and cite the existing task number directly (no placeholder).

## Testing & Validation

- [ ] Per-phase scoped `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`
  (and `.Expansion` when touched) — every phase.
- [ ] `lake test` at Phases 4 and 8 (conformance corpus, all 24 rows, esp. row 20).
- [ ] `lean_verify` on the restated `intExpandBranches_openBranch_sat` consumers
  (`openBranch_countermodel`, `tableau_complete`) at Phase 8: axiom set
  `{propext, Classical.choice, Quot.sound}` plus `sorryAx` ONLY via the declared DP
  declarations.
- [ ] Sorry census at Phase 8: bare sorries in the subtree = {DP-3, DP-4} ∪ (DP-1/DP-2 if
  placed); anything else is a defect.
- [ ] Full CI order per cslib.md (Phase 8 checklist).

## Artifacts & Outputs

- plans/13_fuel-sufficiency-skeleton.md (this file)
- specs/317_propositional_tableau_completeness/.skeleton-return.json (companion; `new_tasks`
  declaration for 585)
- summaries/13_fuel-sufficiency-skeleton-summary.md (implementation summary, on completion)
- Modified: Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean,
  Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean; possibly
  CslibTests/TableauConformance.lean (Phase 4/8 row additions only)

## Rollback/Contingency

- Every phase commits per green substep (`task 317 phase {P}.{O}: …`); rollback = revert the
  phase's commits. No phase leaves the tree red at a commit boundary.
- If Phase 3's Scope Hypothesis fails badly (engine not parametric and not cheaply
  generalizable), STOP the plan at Phase 2's landed value, mark plan [BLOCKED], and hand the
  finding to the orchestrator — do not force the engine.
- If BOTH DP-1 and DP-2 are sorried AND Phase 6's succ-case threading additionally fails, the
  skeleton premise is broken: mark [BLOCKED] with a handoff enumerating exactly which
  invariant re-establishment failed, rather than landing a hollow shell.
