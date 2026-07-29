# Implementation Plan: Tableau Completeness — Per-Branch Fuel Materialization Repair (Skeleton, v14)

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Status**: [COMPLETED] (Phases 1-6, 8 terminal-complete; Phase 7 terminal-`[BLOCKED]`,
  reassigned to task 430 — see Planned Strategic Sorries DP-5 and Phase 7's blocker-research
  update; no phase of this plan remains actionable)
- **Effort**: 26-44 hours (10 phase-sized dispatches, 3 completed; skeleton — full sorry-zero
  completion is explicitly NOT claimed by this plan alone, see Planned Strategic Sorries)
- **Dependencies**: 456 (completed — Blocking.lean), 552 (completed), 574 (completed — ancestor
  blocking repair). Subsumes: 583 (blocked — its R1 restatement is Phase 6 of this plan; close
  583 as superseded when Phase 6 lands). Defers to: 430 (planned — the two Completeness.lean
  bridge sorries stay in 430's territory; this plan does not touch them)
- **Research Inputs**:
  - reports/15_fuel-materialization-repair.md (PRIMARY for Phases 4A-4C and the Phase 5-8
    deltas; adjudicates the plan-13 Phase 4 blocker — candidate (a) GO, candidates (b)/(c)
    NO-GO with recorded rationale)
  - reports/14_blocker-analysis.md — "## Adversarial Self-Verification" section only (the
    pre-repair body of reports 13/14 is STALE and must not be planned from)
  - specs/583_restate_intexpandbranches_openbranch_sat/reports/01_restate-openbranch-sat.md
    (F3 equivalence, F5 restatement R1, F6 prohibitions, prerequisite acceptance gate)
  - In-code notes at HEAD: Scheme.lean:100-111 (D8), Scheme.lean:504-557 (STOP-gate),
    Scheme.lean:1591-1605 (intUniverse warning), fuel-0 refutation record (now adjacent to the
    fuel-0 sorry at Scheme.lean:3055), Expansion.lean:450-494 (divergence witness),
    Expansion.lean:246-320 (ancestor loop-check)
  - plans/13_fuel-sufficiency-skeleton.md (prior plan: Phases 1-3 landed and are carried
    forward verbatim below; its Phase 4 is superseded by Phases 4A-4C here — the blocker
    defect record lives in plan 13's Phase 4 body and in reports/15 §1)
- **Artifacts**: plans/14_fuel-materialization-repair.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-compliance.md
  - .claude/rules/lean4.md
  - .claude/rules/cslib.md
- **Type**: cslib
- **Plan Version**: 14
- **Skeleton**: true (see `## Planned Strategic Sorries`; `plan_metadata.skeleton: true`)

## Overview

Four bare sorries remain (count re-verified by reports/15 at HEAD): `Intuitionistic/Scheme.lean:617`
(truthLemma T-imp), `Intuitionistic/Scheme.lean:3055` (fuel-0 case of
`intExpandBranches_openBranch_sat`, REFUTED as stated pre-R1; line was :2551 at plan-13 time,
drifted by the Phase 1-3 insertions), `Intuitionistic/Completeness.lean:133`,
`Minimal/Completeness.lean:125`. Per 583's F3 equivalence result, all four bottom out in one
missing development: the post-blocking fuel-sufficiency theorem. Plan 13 landed its Phases 1-3
(Blocking.lean consumption bridge; `WBound`/`intChainBound` + `intCreatedChain_le` PROVED —
DP-1 closed inline; `intUniverseExt` + engine re-target) and then hit a structural blocker at
Phase 4: **any global-scalar fuel dominating the enlarged measure is a `3^Θ(WBound φ)`-bit
numeral, physically unmaterializable for 19 of 20 propositional corpus rows** (defect record:
plan 13 Phase 4; reports/15 §1 re-verifies it at HEAD and proves no tighter global resize can
exist).

**This revision (v14)** replaces the old Phase 4 with the repair adjudicated in reports/15:
**candidate (a), per-branch fuel restructuring of `intExpandBranches`**, realized
shape-preservingly (a `fuels : List Nat` fourth parallel list; well-founded recursion on the
unconditional lex measure `((fuels.map (3 ^ ·)).sum, pending.length)`). Per-branch sufficiency
shrinks the required budget from `3^(2|U|)` to `2|U| + 1`-class numerals — materializable for
every corpus row (worst row 20: ~13.0-million-digit numeral, 599 ms probe, ~5.4 MB; see the 4C
timing gate). The restructure is delivered as three H8-bounded phases (4A build-parallel,
4B port lemmas, 4C flip + retire + corpus gate) so the tree is green at every commit boundary.
Candidates (b) and (c) are NO-GO and constitutionally forbidden below (Postmortem Constraints).

**Honest scope verdict** (unchanged from v13): full four-sorry completion in one plan is NOT
credible. This plan is a SKELETON: Phases 4A-4C, 6, 7 land unconditional or
conditional-but-provable value; Phase 5 carries the remaining research-grade risk (DP-2; DP-1
was proved in Phase 2, no sorry placed). The two Completeness bridges (DP-3, DP-4) are
pre-existing sorries deferred to existing task 430 and NOT in this plan's discharge scope.
Definition of done for this plan: sorries at `Scheme.lean:3055` and `Scheme.lean:617`
discharged (modulo at most DP-2), no false statement remains anywhere in the subtree, build
green, full CI gate passed.

### Territory Resolutions (settled up front)

| Overlap | Resolution |
|---------|------------|
| Task 583 (blocked) owns the fuel-0/`openBranch_sat` restatement | **SUBSUMED**: Phase 6 implements exactly 583's F5 form R1 (`hUniv`/`hNW`/`hFuel` hypothesis threading, with `hFuel` in the per-branch form of reports/15 §7). When Phase 6 lands, 583 should be closed as superseded — orchestrator/user action, not this plan's |
| Task 430 (planned) owns the two Completeness bridges (IAtomPersist route) | **DEFERRED**: this plan does not modify `Intuitionistic/Completeness.lean` or `Minimal/Completeness.lean` beyond comment accuracy. 430's existing dependency on 317 is already the right direction |
| Task 456's Blocking.lean consumption | **CONSUMED** (Phase 1, landed) |

### Settled Planner Decision: entry points move to `Scheme.lean` (import direction)

`intFuelExt` needs `WBound` (Scheme.lean:1762), but the entry points
(`intuitionisticTableau`, `minimalTableau`) currently live in `Expansion.lean`, which
`Scheme.lean` imports. **DECIDED: option (i) of reports/15 §6 — move the two entry-point defs
into `Scheme.lean` (after `WBound`/`intFuelExt`/the B-engine) and repoint the corpus import
(`CslibTests/TableauConformance.lean:11,15`, which currently imports only `Expansion`).** This
is the smaller import-direction change; option (ii) (moving `intSubfmls`/`intChainBound`/
`WBound` and their lemma closure below the engine) is rejected. Consequences: the B-engine and
`intFuelExt` land in `Scheme.lean` at Phase 4A; the entry-point move + corpus-import repoint
execute at Phase 4C (the flip commit). Do not re-open this decision without a concrete
elaboration failure.

### Source-to-Implementation Mapping (H3; Tier 3 primary, Tier 1 anchors)

Literature note: per-repo sub-index present (34 entries) but contains no chunks for the anchors
below; Tier 1 anchoring rests on `references.bib` entries (all BibKeys re-verified by
reports/15: `references.bib:211` Fitting1983, `:218` Dyckhoff1992, `:239`
GargGenoveseNegri2012, `:1041` Massacci2000) plus in-file provenance notes. Reports/15
introduces no new literature claims; its grounding is Tier 3 (implementation-backed).

| Source | Claim | Lean Target | Status |
|--------|-------|-------------|--------|
| Fitting1983, Ch. 4 | Systematic intuitionistic tableau: open saturated branch yields Kripke countermodel; construction presumes the procedure terminates in saturation | `openBranch_countermodel` (Scheme.lean:3448), `intExpandBranches_openBranch_sat` restatement R1 (Phase 6) | pending |
| GargGenoveseNegri2012, §III | Count of distinct forced sets bounds blocking chains | `distinctTypes_le_pow`, `strictChain_le_card` (Blocking.lean:150,185); consumed via `intCreatedChain_le` (Phase 2, PROVED) | landed |
| Massacci2000, Tech. 8.1/8.2 | Blocking side conditions are logic-specific | ψ-conditioned ancestor check `intFImpReuseWitnessAnc?` (Expansion.lean:260 — landed, 574); never edited here | transcribed (574) |
| Dyckhoff1992 | Termination via calculus-side contraction-free design (contrast route; not taken) | (none — provenance only) | n/a |
| 583 report F5 | Restatement R1 exact hypothesis set; fuel-0 discharge shape; call-site repair shape | Phase 6 (with reports/15 §7's per-branch `hFuel` form and omega fuel-0 discharge) | pending |
| reports/15 §2, §6 | Per-branch fuel sufficiency needs only `intWork_drop` + `intCount_notMem_mono` + init bound; termination decrease is unconditional (exactly-2-way branching, `Rules.lean:259,262,280`) | `intFuelExt`, `intExpandBranchesB`, `intWork_init_lt_intFuelExt` (Phases 4A-4C) | pending |

### Preserved Assets

The following work is complete, `lake build`-green at HEAD, and must not regress. The
**Restructure impact** column is reports/15 §7's verified engine-independence audit — rows
marked "untouched" contain no reference to the engine or fuel in statements or proofs and MUST
stay green with zero edits through Phases 4A-4C.

| Component | File | Status | Restructure impact |
|-----------|------|--------|--------------------|
| Ancestor-blocking repair: `intFImpReuseWitnessAnc?` + `_spec` | Expansion.lean:260,293 | [COMPLETED] (574) | untouched |
| D8 `sat_fimp` + live `sat_timp` field | Scheme.lean:100-118 | [COMPLETED] (574/552) | untouched |
| `.pos, .imp` branching arm | Rules.lean:245-268 | [COMPLETED] (552) | untouched (read by 4A's termination argument: emits literal 2-element list) |
| `intCreatedChain_le` + `WBound` + `intChainBound` + `WBound_pos` (Phase 2, DP-1 PROVED) | Scheme.lean:1753-1839 | [COMPLETED] | **untouched** — no engine/fuel reference anywhere (reports/15 audit) |
| `intUniverseExt` family: def, `_length_le`, membership lemmas, `_outputs_subset_ext` containment family (Phase 3) | Scheme.lean:2155-2401 | [COMPLETED] | **untouched** |
| Persistence-fuel lemmas: `applyAllTImpRules_count_drop`, `applyPersistenceFixpoint_genuine_of_count_le_fuel` | Scheme.lean:2862, 2928 | [COMPLETED] | **untouched** — inner persistence loop, not the outer engine |
| `intWork_drop`, `intCount_notMem_mono` (+ `_append_drop`) | Scheme.lean:2516-2531, 2500-2513 | [COMPLETED] | untouched; **PROMOTED to the load-bearing sufficiency core** |
| Both step-lt lemmas: `intExpMeasure_step_lt`, `intExpMeasure_step_lt_branch` (re-targeted Phase 3) | Scheme.lean:2575, 2647 | [COMPLETED] | stay green **untouched** (statements never mention the engine); demoted to retained-but-unconsumed after 4C |
| Succ-fuel case of `intExpandBranches_openBranch_sat` incl. saturation leaf | Scheme.lean:3014- (fuel-0 sorry at :3055) | [COMPLETED] (succ case) | ported mechanically in 4B (content transfers arm-by-arm; fuel-0 sorry carries 1-for-1) |
| `intExpandBranches_closed_unsat` / `tableau_sound` (sorry-free) | Soundness.lean:1078 (~690 lines; unfolds `.go` at :1161,:1223) | [COMPLETED] | ported in 4B — biggest regression surface; old proof retained green until the 4C flip |
| Shared blocking module + counting layer | Cslib/Foundations/Logic/Tableau/Blocking.lean | [COMPLETED] (456), lean_verify clean | untouched (read-only for this task) |
| Conformance corpus, 44 rows incl. divergence-witness regression row 20 | CslibTests/TableauConformance.lean | [COMPLETED] | zero row edits; verdicts preserved a priori (identical step sequences); row 20 gains ~0.6 s materialization + seconds of bignum stepping — 4C timing gate |
| FMP decidability route | `Cslib.Logic.PL.decidableDerivableIntPropAxiomFMP` | [COMPLETED], sorry-free | untouched |
| In-code refutation/divergence records | Scheme.lean:1591-1605 + fuel-0 refutation block; Expansion.lean:450-494 | [COMPLETED] | comment updates only (Phases 6, 8) |

## Postmortem Constraints

Binding rules for all implementation dispatches. Rows 1-10 carry forward verbatim from plan 13
(derived from the reports-13/14 adversarial verification, 583's F6, the in-file directives, and
twelve failed prior plan versions); rows 11-13 are new, from reports/15.

**Do NOT**:
1. Plan against or state the refuted bound form `(b.labels.map b.typeAt).eraseDups.length ≤
   2^U.length` — REFUTED by sign doubling (456's research: 5 distinct type-lists over
   `U = [p,q]` vs bound 4). Only the landed signed form is valid: `distinctTypes_le_pow` with
   `2 ^ V.card` over `V : Finset (Sign × F)`, or `posTypeAt` over `U : Finset F` for `2 ^ U.card`.
2. Re-add the D8-dropped `w ≤ w'` conjunct to `sat_fimp` (Scheme.lean:100-106) — false under
   ancestor blocking, and never consumed downstream.
3. Attempt the containment invariant `∀ x ∈ b, x ∈ intUniverse φ` against the CURRENT
   `intUniverse` linear range — refuted (Scheme.lean:1591-1599); any new bound must come from
   the blocking combinatorics, i.e. `WBound` (landed, Phase 2).
4. Edit `intFImpReuseWitnessAnc?` or its `_spec` (Expansion.lean:260-320) — 574's landed
   contract. In particular never Option B (appending fresh `F(ψ)@x` on reuse — proven UNSOUND,
   see Expansion.lean:250-253).
5. Weaken/vacuize `intExpandBranches_openBranch_sat`, `tableau_complete`, or relocate a sorry
   into `tableau_complete`, the `Decidable` instance, or a standalone "no-exhaustion" axiom
   (583 F6 forbidden-deferral list; in-file prohibition Scheme.lean:502, 556-557).
6. Add `.fuelExhausted` to `IntTableauResult` (583's R2 fallback) — rejected: relocates the
   identical obligation into `tableau_complete` and `instDecidableIValid` where nothing closes
   it. R1 hypothesis-threading is the settled form.
7. Discharge the fuel-0 sorry (`Scheme.lean:3055`) or `Scheme.lean:617` alone via a weakened
   statement — the in-file STOP-gate (Scheme.lean:554-557) directs both be closed together in
   one pass over the same invariants (Phases 6-7, consecutive).
8. Touch `Intuitionistic/Completeness.lean:133` or `Minimal/Completeness.lean:125` (430's
   territory) beyond comment-accuracy updates in Phase 8.
9. Re-derive the divergence refutation or re-attempt `intExpandBranches_world_bound` /
   `hnw : nextWorld ≤ φ.complexity + 1` as previously stated — refuted, not hard.
10. Place any sorry not corresponding to a `## Planned Strategic Sorries` row without flagging
    it as a plan-unanticipated deviation in the summary (plan-format deviation flag).
11. **(NEW)** Define `intFuelExt` via `(intUniverseExt φ).length` — the LIST has `Θ(WBound φ)`
    elements (~10^13,000,000 for corpus row 20) and can never be built. `intFuelExt` MUST be
    the closed arithmetic form `4 * (2 * φ.complexity + 1) * (WBound φ + 1) + 1`; only the
    NUMERAL is materializable. The same prohibition applies to any runtime membership check
    against the `intUniverseExt` list.
12. **(NEW)** Candidate (b) — well-founded recursion on the measure as the engine definition —
    is FORBIDDEN until DP-2 is proved: its `decreasing_by` needs exactly Phase 5's `hNW`
    fresh-mint preservation, and a `decreasing_by sorry` defines the function via `sorryAx`,
    tainting `instDecidableIValid` and every downstream theorem (no strategic-sorry placement
    keeps the definition clean; it also inverts the skeleton's risk concentration). It remains
    a legitimate elective cleanup AFTER DP-2 closes — future work, never the Phase-4 repair.
13. **(NEW)** Candidate (c) — splitting a proof-side procedure from the `#eval` corpus
    procedure — is FORBIDDEN outright: the equivalence obligation is
    false-or-unprovable (persistence receives remaining outer fuel, `Expansion.lean:363`, so
    verdict-stability under fuel change is exactly the unavailable sufficiency fact), per-row
    equivalence is not kernel-checkable (`decide`/`rfl` stall on the engine's `let rec`s), and
    it reintroduces the exact sorry-free-but-wrong-verdict hazard class the conformance corpus
    was built to close and the ancestor-blocking repair closed. Do not re-propose.

**MUST preserve**:
- Everything in the Preserved Assets table. Rows marked "untouched" in the Restructure-impact
  column must survive Phases 4A-4C with ZERO edits; the two ported proof families
  (`closed_unsat`, `openBranch_sat` succ case) keep their OLD copies green until the 4C flip.
- Repo-wide bare-sorry count must never increase net of the declared division points: the count
  stays exactly 4 through Phases 4A-4C (the fuel-0 sorry carries 1-for-1 in the 4B port), each
  new sorry must be a DP row, and Phases 6-7 must each strictly decrease the count by one.
- `Blocking.lean` is read-only for this task (Foundations module owned by 456's landed design).

**Design decisions are SETTLED** (do not re-open without concrete counterexample):
- R1 hypothesis-threading restatement (not R2 trichotomy) — adversarially challenged and
  retained in 583's report; `hFuel` takes the per-branch form (reports/15 §7).
- Per-branch fuel restructuring, candidate (a), in the shape-preserving parallel-lists form
  with parallel-build-then-flip staging (reports/15 §5 go/no-go).
- Entry points move to `Scheme.lean` (option (i)) — see Settled Planner Decision above.
- Ancestor-directed blocking with explicit `F(ψ)@x` conjunct; D8 conjunct drop.
- This plan subsumes 583 and defers the bridges to 430 (Territory Resolutions above).
- The signed, Finset-valued counting layer from Blocking.lean is the only counting substrate.
- Fuel-sufficiency is incorporated here (not spawned) — inseparable from the restatement
  threading in the same files.

## Goals & Non-Goals

- **Goals**:
  - Restructure `intExpandBranches` to per-branch fuel (`fuels : List Nat`) with an
    unconditional termination measure, making every corpus fuel numeral materializable
    (Phases 4A-4C, parallel-build-then-flip).
  - Land `intFuelExt` (arithmetic form) and `intWork_init_lt_intFuelExt` as the call-site
    discharge replacing the unmaterializable `intExpMeasureExt_init_le_fuel` route.
  - Thread the `hUniv`/`hNW` invariants (Phase 5, DP-2 risk concentrated there).
  - Restate `intExpandBranches_openBranch_sat` per R1 with per-branch `hFuel` and discharge
    the fuel-0 sorry (`Scheme.lean:3055`).
  - Discharge `truthLemma`'s T-imp case (`Scheme.lean:617`) in the same pass (STOP-gate).
  - Leave zero FALSE statements in the subtree; leave all remaining sorries tracked (DP rows).
- **Non-Goals**:
  - The two Completeness bridge sorries (430's scope — IAtomPersist route).
  - Any change to `Blocking.lean`, `intFImpReuseWitnessAnc?`, or the conformance corpus's
    landed rows (row additions for new regression checks are allowed in Phase 8).
  - A termination THEOREM for the decision procedure beyond what the engine's WF measure and
    `WBound` require.
  - Evaluability of `intuitionisticTableau` for arbitrarily large formulas: per-branch fuel
    digits scale as `2^s·s·log₁₀(s+1)` and materialization dies again around `s ≈ 25`.
    Candidate (a) makes the corpus (max `s = 19`) and small formulas evaluable; the
    sufficiency THEOREM is unaffected (proof-side, all φ). Future corpus rows must keep
    `s ≲ 22` — recorded in Phase 8 docs.
  - Candidate (b) as future work (post-DP-2 elective) — recorded, not executed here.

## Risks & Mitigations

- **Risk**: The 4B port of `intExpandBranchesB_closed_unsat` (~690 lines, unfolds `.go`
  directly at Soundness.lean:1161,1223) exceeds one dispatch.
  **Mitigation**: parallel-build staging means underestimation costs schedule, not greenness
  (old proof stays green). If mid-dispatch it is clear 4B cannot land in one pass, split at a
  lemma boundary into 4B.1 (`closed_unsat` port alone) and 4B.2 (the three remaining ports) —
  a pre-authorized H8 split, not a deviation.
- **Risk**: Functional induction (`.induct`) may not be available for a mutual WF pair with
  the lifted `go` (reports/15: medium-high confidence it works).
  **Mitigation** (named in-spec fallbacks, in order): manual WF induction on the lex measure;
  then selector-refactor of `go` into a total non-recursive-into-engine helper.
- **Risk**: Row 20's post-flip `#eval` wall time (estimated +2-20 s from ~8 ms/bignum-op ×
  observed step counts; exact step count not re-measured).
  **Mitigation**: the 4C timing gate is a done-criterion — a bad surprise blocks the phase,
  not the library. Baseline `lake test` wall time recorded in Phase 4A before any change.
- **Risk**: `hNW` preservation (Phase 5) needs a creation-count invariant relating minted
  labels to tree size — additional threading beyond 583's sketch (unchanged from v13).
  **Mitigation**: DP-2 strategic sorry, tracked, follow-up task 585.
- **Risk**: Corpus verdict drift under the new engine despite the a-priori identity argument
  (fuel affects behavior only via the exhaustion arm; per-branch budgets ≫ observed step
  counts; persistence fuel shape preserved).
  **Mitigation**: empirical parity is an explicit 4A done-criterion (`intVerdictB = intVerdict`
  probe on all 20 propositional rows) and again at 4C (`lake test`, all 44 rows).
- **Risk**: Same-file churn — most phases write `Scheme.lean`. **Mitigation**: strictly
  sequential waves (H7: no parallel dispatch; single-owner territory), commit-per-green-substep.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 [COMPLETED] | -- |
| 2 | 2 [COMPLETED] | 1 |
| 3 | 3 [COMPLETED] | 2 |
| 4 | 4A | 3 |
| 5 | 4B | 4A |
| 6 | 4C | 4B |
| 7 | 5 | 2, 3, 4C |
| 8 | 6 | 4A, 4C, 5 |
| 9 | 7 | 5, 6 |
| 10 | 8 | 1-7 |

**Parallel opportunities: NONE — declared explicitly.** All remaining phases write
`Cslib/Logics/Propositional/Tableau/Intuitionistic/{Scheme,Expansion,Soundness}.lean`; H7
territory is single-owner and waves are strictly sequential.

### Phase 1: Blocking.lean consumption bridge [COMPLETED]
- **Goal:** The propositional tableau imports and can invoke 456's counting layer.
- **Tasks:**
  - [x] Import `Cslib.Foundations.Logic.Tableau.Blocking` into the intuitionistic development
    (at `Expansion.lean` or `Scheme.lean`, whichever the lemmas land in; respect shake).
    (Landed in `Scheme.lean` — the instantiations need `intSubfmls`, which lives there. Also
    added `Mathlib.Data.Finset.Prod` for the `×ˢ` signed-universe product.)
  - [x] Bridge lemma `posFormulasAt_mem_iff`: `φ ∈ posFormulasAt b w ↔ φ ∈ Branch.posTypeAt b w`
    (membership equivalence; `IBranch Atom` is definitionally `Branch (Proposition Atom) Nat`,
    so no coercion is needed — only the local-def-to-`posTypeAt` content equivalence, which
    differs by an `eraseDups`).
  - [x] Instantiations at the propositional types: `distinctTypes_le_pow` with
    `V := (intSubfmls φ).toFinset ×ˢ {Sign.pos, Sign.neg}` (or equivalent signed universe) and
    `exists_typeAt_eq_of_card_lt`; confirm `strictChain_le_card` applies without wrapping.
    (Landed as `intSignedUniverse φ := {.pos, .neg} ×ˢ (intSubfmls φ).toFinset :
    Finset (Sign × Proposition Atom)` — the `Sign × F` component order `distinctTypes_le_pow`
    expects — with `mem_intSignedUniverse` simp lemma, `intDistinctTypes_le_pow`,
    `intExists_typeAt_eq_of_card_lt`; `strictChain_le_card` confirmed to apply with no wrapper
    via a build-checked `example` at the propositional instantiation.)
- **Timing:** 1 dispatch. Estimated output: ~120-180 lines.
- **Depends on:** none
- **Verification Tier:** local
- **Done when:** bridge lemmas build sorry-free under a scoped
  `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`; zero new sorries;
  no change to any existing declaration.

### Phase 2: `WBound` definition + ancestor-chain bound lemma (division point DP-1) [COMPLETED]
- **Goal:** A concrete `WBound : Proposition Atom → Nat` and the chain lemma that makes it a
  bound: along any edge chain of created worlds on a branch, chain length is bounded via the
  pigeonhole/strict-chain layer, because an over-long chain forces two chain worlds with equal
  positive type and equal creation obligation ψ, contradicting
  `intFImpReuseWitnessAnc?_spec`'s negation at the later creation site.
- **Tasks:**
  - [x] Define `intChainBound φ` (per-chain depth bound, of order
    `(impCount + 1) * 2 ^ (2 * |Sub φ|)` — exact form implementer's choice, from the blocking
    combinatorics ONLY, never from `intUniverse`'s linear range) and
    `WBound φ` (total world bound: branching factor ≤ imp-subformula count per world, so a
    tree bound of order `(impCount + 1) ^ (intChainBound φ + 1)`; exponential-in-exponential
    is acceptable — it is a proof-side bound, not an evaluation step count).
    (Landed as `intChainBound φ := 2 ^ |Sub φ| * |Sub φ|` — the `(posTypeAt, ψ)`-pair count
    over `(intSubfmls φ).toFinset`, positive-projection `2 ^ U.card` form — and
    `WBound φ := (|Sub φ| + 1) ^ (intChainBound φ + 1)`, plus `WBound_pos : 1 ≤ WBound φ`
    for the Phase 6 singleton call-site. Scheme.lean "Post-Blocking World Bound" section.)
  - [x] State the chain lemma (working name `intCreatedChain_le`): for an edge chain
    `w_0 → … → w_k` of worlds created by unblocked `intFImpRule` firings on branch `b`,
    `k ≤ intChainBound φ`. Proof route: pigeonhole (`exists_typeAt_eq_of_card_lt` over
    `(posTypeAt, ψ)` pairs, Phase 1 instantiations) + the five-conjunct negation of
    `intFImpReuseWitnessAnc? = none` at the later site.
    (Landed. Final hypothesis set, all stated against the final branch `b`: `hsub`
    subformula containment; `hψ` obligations in `Sub φ0`; `hobl` explicit `F(ψs i)` entry at
    each created world; `hnotpos` openness; `hacc`/`hle` chain accessibility/label
    monotonicity; `hunb` the five-conjunct unblockedness negation transcribed against `b`.
    The `(posTypeAt, ψ)`-pair pigeonhole is `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
    over `Sub.powerset ×ˢ Sub` — the same core lemma `exists_typeAt_eq_of_card_lt` wraps;
    the Phase-1 label-indexed instantiation does not fit the chain-indexed quantification,
    a named-lemma substitution within the plan's declared route, not a route change.)
  - [x] Attempt the proof within this dispatch. STOPPING CONDITION (bounded-unit): either the
    proof closes, or place the DP-1 strategic sorry on exactly `intCreatedChain_le` (one
    declaration) with the mandated comment
    (`-- sorry: assumes the ψ-conditioned pigeonhole closes; deferred: research-grade
    combinatorics; follow-up: task 585`), record it in `sorry_inventory` with
    `strategic: true`, and proceed. Do NOT iterate past one dispatch.
    (**PROOF CLOSED — DP-1 PROVED INLINE, no strategic sorry placed.** `lean_verify`
    axioms: `{propext, Classical.choice, Quot.sound}`, no `sorryAx`. The Scope Hypothesis
    held: the `(posTypeAt, ψ)`-pair index sufficed with no enlargement — the `F(ψ)@x`
    conjunct is supplied at the earlier created world by its own creation obligation
    (`hobl`), exactly as anticipated. NOTE for Phase 5 / follow-up owner: `hunb` is the
    five-conjunct negation stated against the FINAL branch; the transfer from the runtime
    check (evaluated on the firing-time branch state) to the final branch is owned by the
    invariant-threading side (DP-2 territory), documented in the lemma docstring. DP-1's
    contingent follow-up in the Planned Strategic Sorries table is NOT needed for Phase 2;
    whether it stays open for DP-2 is decided at Phase 5.)
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

### Phase 3: `intUniverseExt` / `intExpMeasureExt` + engine re-target [COMPLETED]
- **Goal:** The F2 measure engine runs over the enlarged universe
  `List.range (WBound φ + 1)` in place of `List.range (φ.complexity + 2)`.
- **Tasks:**
  - [x] Define `intUniverseExt φ` (same cell structure as `intUniverse`, world range
    `WBound φ + 1`) and `intExpMeasureExt φ := intExpMeasure (intUniverseExt φ)` (or keep
    `intExpMeasure` parametric in `U` as it already is and only add the `Ext` universe + its
    length lemma `intUniverseExt_length_le`).
    (Landed: the parenthetical option — `intExpMeasure` stays parametric in `U`, no
    `intExpMeasureExt` def; the `hFuel` spec text writes
    `intExpMeasure (intUniverseExt φ0) …`. New "Enlarged Universe (post-blocking)" section
    in Scheme.lean: `intUniverseExt`, `intUniverseExt_length_le`
    (`≤ 2 * (2 * φ.complexity + 1) * (WBound φ + 1)`), membership lemmas
    `mem_intUniverseExt_of`/`_of'`, `intUniverseExt_mem_formula`, `intUniverseExt_mem_label`.)
  - [x] Re-target the engine: `intExpMeasure_step_lt`, `intExpMeasure_step_lt_branch`,
    `applyAllTImpRules_count_drop`, `applyPersistenceFixpoint_genuine_of_count_le_fuel` over
    `intUniverseExt`. Per 583 F5 these are parametric in the universe list ("statements are
    parametric; proofs re-run"); the load-bearing generalization is
    `intApplyRuleFull_outputs_subset`'s replacement: subformula-content closure into
    `intUniverseExt` under the hypothesis `nextWorld ≤ WBound φ` (the hypothesis is DISCHARGED
    in Phase 5; here it is threaded as a premise, which is provable without DP-1).
    (Landed. Scope Hypothesis CONFIRMED: all four proofs re-ran verbatim over the enlarged
    universe on the first elaboration — none unfolds the world range; only `set U := …` /
    membership-lemma names changed. The load-bearing replacement landed as
    `intApplyRuleFull_outputs_subset_ext` with `hnw : nextWorld ≤ WBound φ0` threaded as a
    premise, plus the Ext containment family `intTImpRule_outputs_subset_ext`,
    `applyAllTImpRules_subset_ext`, `applyPersistenceFixpoint_subset_ext` (the last needed by
    Phase 5's `hUniv` preservation). Original `intUniverse` block and its containment family
    left intact; deprecation notes deferred to Phase 8. `lean_verify` on
    `intApplyRuleFull_outputs_subset_ext`, `intExpMeasure_step_lt`,
    `applyPersistenceFixpoint_genuine_of_count_le_fuel`, `intUniverseExt_length_le`: axioms
    `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.)
- **Timing:** 1 dispatch. Estimated output: ~250-400 lines.
- **Depends on:** 2 (definition only — proceeds if DP-1 is sorried)
- **Verification Tier:** local
- **Scope Hypothesis:** every engine proof re-runs over the enlarged universe with only
  membership/length facts about `U` (confirm by re-elaboration; the engine lemmas take
  `hb : ∀ x ∈ b, x ∈ intUniverse φ0` as a premise and nowhere unfold the world range). If one
  proof step uses the literal range, generalize that single lemma over an abstract `U` with a
  closure hypothesis.
- **Done when:** enlarged-universe engine lemmas build sorry-free (given only Phase 2's
  statements); zero new sorries in this phase; the ORIGINAL `intUniverse` block is left intact
  (deprecation notes deferred to Phase 8).

### Phase 4A: `intFuelExt` + per-branch-fuel B-engine + init bound (parallel build; no consumer flipped) [COMPLETED]

Replaces plan-13 Phase 4, whose global-scalar resize was structurally unimplementable (defect
record: plan 13 Phase 4; reports/15 §1). Spec source: reports/15 §6, Phase 4A. All new names
below are suggestions; the constraint set is binding, the naming is implementer latitude.

- **Goal:** The per-branch fuel budget and the new engine exist beside the old engine, with an
  unconditional termination measure and a provable init bound; nothing downstream is flipped.
- **Tasks:**
  - [x] Record the pre-change `lake test` wall-time baseline (for the 4C timing gate) in the
    progress file before any edit.
  - [x] Def `intFuelExt (φ) : Nat := 4 * (2 * φ.complexity + 1) * (WBound φ + 1) + 1`, in
    `Scheme.lean` after `WBound`. MUST be this closed arithmetic form — NEVER
    `2 * (intUniverseExt φ).length + 1` (Postmortem constraint 11: the list has `Θ(WBound)`
    elements and is unmaterializable; only the numeral is feasible; it dominates
    `2 * |intUniverseExt φ| + 1` via `intUniverseExt_length_le`). Docstring records this
    prohibition and the `s ≲ 22` corpus-row feasibility envelope (fuel digits scale as
    `2^s·s·log₁₀(s+1)`; ~0.5 GB numeral at `s ≈ 25`).
  - [x] New engine `intExpandBranchesB` (working name), in `Scheme.lean`: same worklist shape
    and parallel lists as `intExpandBranches` (Expansion.lean:333-426), with the single global
    `fuel : Nat` replaced by `fuels : List Nat` as a fourth parallel list. Arms:
    - active branch's `f + 1` → `f` on linear / world-creating / reuse arms;
    - beta arm: children each inherit `f` (from the parent's `f + 1`);
    - active-branch `f = 0` → `.openBranch bPers` (exhaustion arm, mirroring today's global
      exhaustion arm);
    - persistence keeps receiving the active branch's remaining fuel (mirroring today's
      `fuel' + 1` shape at Expansion.lean:363);
    - skip-closed arm (`go` moving a closed branch to done) unchanged in content.
    `go` lifted to a top-level (mutual or selector-refactored) def so WF elaboration and
    functional induction work. `termination_by` the lex measure
    `((fuels.map (3 ^ ·)).sum, pending.length)`; `decreasing_by` via the `pow3` family
    (`Cslib/Foundations/Logic/Tableau/Measure.lean`): skip-closed leaves the sum unchanged and
    shrinks pending; single-successor arms use `3^f < 3^(f+1)`; the beta arm uses
    `2·3^f < 3^(f+1)` — sound because all three `branchingResult` sites emit literal 2-element
    lists (Rules.lean:259 T-and, :262 F-or, :280 T-imp split). UNCONDITIONAL — no
    branch-containment or world-bound hypothesis may appear in the definition (that would be
    candidate (b); Postmortem constraint 12).
  - [x] Lemma `intWork_init_lt_intFuelExt (φ) :
    intWork (intUniverseExt φ) [⟨.neg, φ, 0⟩] [] < intFuelExt φ` — the REPLACEMENT for
    plan-13's `intExpMeasureExt_init_le_fuel` (it is Phase 6's call-site `hFuel` discharge).
    Proof shape: the countP bookkeeping of `intExpMeasure_init_le_fuel` (Scheme.lean:2787-2812)
    + `intUniverseExt_length_le`, closing by `omega` — no pow manipulation, strictly easier
    than the lemma it replaces.
  - [x] `#eval` parity probe: `intVerdictB = intVerdict` on all 20 propositional corpus rows
    (not committed, or committed as a clearly-marked temporary CslibTests section removed at
    4C). Any mismatch is a hard failure of this phase.
- **Timing:** 1 dispatch. Estimated output: ~200-350 lines.
- **Depends on:** 3
- **Verification Tier:** local
- **Scope Hypothesis:** WF elaboration accepts the lifted `go` with the lex measure and the
  `pow3` decrease obligations as stated (reports/15 verified the arithmetic and the 2-way
  branching by source; fallbacks for `.induct` availability are named in Risks and consumed in
  4B, not here — 4A only needs the definition to elaborate and `#eval` to run).
- **Done when:** `intFuelExt`, `intExpandBranchesB`, and `intWork_init_lt_intFuelExt` build
  sorry-free (scoped build); parity probe passes on all 20 propositional rows; `lake test`
  baseline recorded; ZERO changes to existing declarations.

### Phase 4B: Port the four engine-quantifying lemmas to the B-engine (old ones untouched) [COMPLETED]
- **Goal:** Every theorem whose induction skeleton is the engine recursion exists in a
  B-engine form; the old lemmas and old engine remain green and untouched.
- **Tasks:**
  - [x] `intExpandBranchesB_closed_unsat` — port of `intExpandBranches_closed_unsat`
    (Soundness.lean:1078, ~690 lines, sorry-free; unfolds `intExpandBranches.go` directly at
    :1161, :1223 — the largest single porting risk). Statement gains `fuels`; proof by
    functional induction on the B-engine, falling back per the Risks ladder (manual WF
    induction on the lex measure; then the `go` selector-refactor). Per-arm content transfers.
    (Landed in Scheme.lean — the import direction Expansion → Soundness → Scheme forces the
    B-port to live where the B-engine is visible; enabled by de-privatizing 11 Soundness.lean
    helper lemmas, a visibility-only edit. `intExpandBranchesB.go.induct` worked on the
    primary route (10 cases, one flat worklist induction replaces the old outer-fuel/inner-go
    nesting); no fallback needed. Statement also gains `fuels.length = branches.length`.
    lean_verify: `{propext, Classical.choice, Quot.sound}`, no sorryAx.)
  - [x] `intExpandBranchesB_openBranch_closed` (port of Scheme.lean:684) and
    `intExpandBranchesB_openBranch_initial_mem` (port of Scheme.lean:3301): fuel plays no role
    in their content; wrapper-only ports. (Both landed sorry-free, same functional-induction
    skeleton; `openBranch_closed` was landed first as the route-validation probe.)
  - [x] Mechanical port of `intExpandBranches_openBranch_sat`'s succ case (Scheme.lean:3014)
    to the B-engine: statement gains `fuels`; NO R1 hypotheses yet (that is Phase 6); the
    pre-existing fuel-0 sorry (Scheme.lean:3055) carries over 1-for-1 — subtree bare-sorry
    count stays exactly 4.
    (Landed as `intExpandBranchesB_openBranch_sat`. The 1-for-1 carry is realized by
    CONSUMPTION, not token duplication: the B-engine's fuel-exhaustion arm (`f = 0`,
    open branch) is discharged by invoking the OLD sorried lemma at `fuel := 0` on the
    singleton worklist `[bPers]`, whose fuel-0 `findSome?` arm returns exactly
    `.openBranch bPers` — the sorry flows through `sorryAx` and the bare-sorry census
    stays at exactly 4. NOTE FOR 4C: retiring the old lemma requires materializing the
    sorry into the B-lemma's exhaustion arm at that point (census unchanged: old token
    removed, new token added), unless Phase 6's restatement lands the discharge first.)
  - [x] IN-PHASE SPLIT PROVISION (pre-authorized, not a deviation): if the `closed_unsat` port
    alone fills the dispatch, land it as 4B.1 (commit, green) and complete the remaining three
    ports as 4B.2 in the next dispatch at the same spec. (NOT NEEDED — all four ports landed
    in one dispatch.)
- **Timing:** 1-2 dispatches (reports/15 sizes the `closed_unsat` port at medium confidence).
  Estimated output: ~450-800 lines.
- **Depends on:** 4A
- **Verification Tier:** local
- **Scope Hypothesis:** the four listed lemmas are the COMPLETE set of engine-induction proofs
  (reports/15 §2: `intExpMeasure_step_lt`(+`_branch`) quantify over worklists and
  `intStepBranch` only, never the engine — checked by statement). Confirm by grepping
  `intExpandBranches` consumers before editing; any additional engine-quantifying lemma found
  is ported in this phase and flagged in the summary.
- **Done when:** all four B-lemmas build with exactly one sorry total (the carried fuel-0
  sorry); old engine, old lemmas, and all Preserved-Assets rows untouched and green; scoped
  build of `Scheme`, `Soundness` green.

### Phase 4C: Flip entry points + retire old engine + 44-row corpus gate with timing [COMPLETED]
- **Goal:** The B-engine IS the engine: entry points consume it with materializable fuel, the
  old global-fuel engine is retired, and the full corpus certifies the executed procedure with
  unchanged verdicts inside a declared time budget.
- **Tasks:**
  - [x] Execute the settled entry-point move (option (i)): relocate `intuitionisticTableau`
    and `minimalTableau` from `Expansion.lean` into `Scheme.lean` (after
    `WBound`/`intFuelExt`/the engine), redefined via the B-engine with
    `fuels := [intFuelExt φ]`; repoint the corpus import
    (CslibTests/TableauConformance.lean:11,15 — currently imports only `Expansion`).
  - [x] Rename the B-engine to `intExpandBranches`, retiring the old engine, old `intFuel`,
    and `intExpMeasure_init_le_fuel` (immediate removal; their docstring history is captured
    by the Phase 8 doc pass — the fuel-doubling note at Expansion.lean:498-509 is superseded
    by `intFuelExt`'s docstring).
  - [x] Repoint consumers at the ported lemmas: `tableau_sound` (Soundness.lean),
    `openBranch_countermodel` (Scheme.lean:3448), `tableau_complete` (Scheme.lean:3504), and
    the Minimal-side consumers. Update the `propExpandBranches` alias. (Note: the old
    `intExpandBranches_closed_unsat` + `intuitionisticTableau_sound` in Soundness.lean, and the
    old `minimalTableau_sound` in Minimal/Soundness.lean, were dead global-fuel-typed code left
    over from before the flip; retired in this dispatch as part of this task.)
  - [x] Remove the temporary 4A parity-probe section if it was committed. (None found; no-op.)
- **Timing:** 1 dispatch. Estimated output: ~150-300 lines (net; mostly repointing).
- **Depends on:** 4B
- **Verification Tier:** interface (changed defs consumed by `DecisionProcedure.lean`, both
  `Completeness.lean` files, `Soundness.lean`, and `CslibTests/TableauConformance.lean` —
  build all dependents in-phase)
- **Scope Hypothesis:** no conformance row pins a literal fuel VALUE (verified by reports/15's
  grep: rows assert verdict strings only); verdicts are preserved a priori because fuel
  influences behavior only through the exhaustion arm and per-branch budgets vastly exceed
  observed step counts (row 20 saturates within hundreds of steps, Expansion.lean:462-468).
- **Done when:** full `lake build` green; `lake test` green with ALL 44 corpus rows unchanged
  (especially divergence-witness row 20); **TIMING GATE**: post-flip `lake test` wall time
  within the declared budget — ≤ 3 minutes total or ≤ 5× the 4A-recorded baseline, whichever
  is looser (row 20 is expected to add ~0.6 s materialization plus ~2-20 s of bignum stepping;
  this is a timing gate, NOT a digit cap — the ~13.0-million-digit row-20 numeral is in-budget
  by measurement, reports/15 probe: 599 ms materialization); dependents build green; subtree
  bare-sorry count still exactly 4.

### Phase 5: `hUniv`/`hNW` threading invariants (division point DP-2) [COMPLETED]
- **Goal:** Preservation lemmas for the two new R1 hypotheses through all four recursion arms
  of the (post-flip, per-branch-fuel) `intExpandBranches` (linear, branching, world-creating
  with reuse, world-creating with fresh mint). Substance unchanged from v13 (reports/15 §7:
  same four arms, same fresh-mint `hNW` risk, same `applyPersistenceFixpoint_subset_ext`
  consumption); stated against the B-engine's arms (identical arm structure).
- **Tasks:**
  - [x] `hUniv` preservation: rule outputs stay in `intUniverseExt φ0` — subformula-content
    side via the existing subformula closure lemmas; world-label side via `hNW`. DONE:
    `intStepBranch_linear_preserves_univ`/`intStepBranch_branch_preserves_univ`
    (Scheme.lean), direct corollaries of `intApplyRuleFull_outputs_subset_ext` +
    `applyPersistenceFixpoint_subset_ext`; the ancestor-reuse arm needs no lemma (branch
    unchanged). Sorry-free.
  - [x] `hNW` preservation (`∀ nw ∈ nextWorlds, nw ≤ WBound φ0`): only the fresh-mint arm
    increments; needs the creation-count invariant "labels minted so far ≤ tree size ≤
    `WBound φ0`" tied to Phase 2's chain lemma (including the runtime-check-to-final-branch
    transfer noted in `intCreatedChain_le`'s docstring). This is the remaining research-grade
    concentration. STOPPING CONDITION: prove within this dispatch, or place the DP-2 strategic
    sorry on exactly the one `hNW`-preservation lemma for the fresh-mint arm, with the mandated
    comment and `sorry_inventory` entry (`follow-up: task 585`), and proceed. DONE (deferred
    per STOPPING CONDITION): the three trivial arms (alpha/beta/reuse) proved sorry-free
    (`intStepBranch_linear_preserves_nw_of_none`, `intStepBranch_branch_preserves_nw`); the
    fresh-mint arm carries the one authorized DP-2 strategic sorry
    (`intFreshMint_preserves_nw`), documented with the missing premise named explicitly
    (`nw < WBound φ0` strict, not derivable from the threaded `nw ≤ WBound φ0` alone).
  - [x] Package both as `IAllConsistent`-style parallel-list invariants R1's induction will
    thread (mirror `IAllConsistent`/`IAllAccessConsistent`'s existing shape). DONE: `IAllUniv`/
    `IAllNW` with `_append`/`_map` combinator lemmas (Scheme.lean).
- **Timing:** 1 dispatch. Estimated output: ~250-400 lines.
- **Depends on:** 2, 3, 4C
- **Verification Tier:** local
- **Done when:** both invariants stated in final form and threaded-form lemmas build, with at
  most the DP-2 sorry; scoped build green.

### Phase 6: R1 restatement of `intExpandBranches_openBranch_sat` + fuel-0 discharge + call-site repair [COMPLETED]
- **Goal:** The fuel-0 sorry (Scheme.lean:3055 pre-port) discharged. Implements EXACTLY 583's
  F5 form R1 (subsumes task 583), with `hFuel` in the per-branch form of reports/15 §7.
- **Tasks:**
  - [x] Add hypotheses `hUniv`, `hNW` (Phase 5's invariants), and the per-branch `hFuel` to
    the (ported) `intExpandBranches_openBranch_sat`; the lemma gains a `φ0` parameter if not
    already threaded. **`hFuel` form (CHANGED from v13/583-F5's global-measure form)**: a
    per-branch parallel-list invariant (`IAllFuel`-style, mirroring `IAllConsistent`):
    `∀ i, intWork (intUniverseExt φ0) bᵢ eᵢ < fuelsᵢ` — never
    `intExpMeasure … ≤ fuel` (the global form died with the old engine). DONE: `IAllFuel`
    added (simultaneous 3-list recursion, mirrors `IAllConsistent`) with `_append`/`_map`
    combinators, plus `intWork_persistence_le` (bridges the threaded `bh`-relative fact to
    the persisted `bPers` the engine actually consumes) and
    `intStepBranch_some_exists_fuel` (exposes the `e.any (·==sf) = false` witness
    `intWork_drop` needs). `φ0` added as the lemma's new first explicit parameter.
  - [x] Fuel-0 discharge, SIMPLIFIED from 583 F5's measure-0 argument: the exhaustion arm
    fires at active-branch `f = 0`; `hFuel` at that branch gives `intWork … < 0`, absurd by
    `omega`. No `3^k ≥ 1` measure reasoning, no saturation reasoning at fuel 0. (No other
    change to the F5 shape.) DONE: case3 of the induction (`Scheme.lean`, formerly the
    fuel-0 sorry) now extracts `hFuel`'s head component and closes by `omega`.
  - [x] Succ-case re-establishment of the three hypotheses through the ported proof body,
    per arm: linear/world-create/reuse arms via `intWork_drop` (arm-agnostic, covers reuse
    with `b' = b`); the persistence prefix via `intCount_notMem_mono`; each beta child via
    `intWork_drop` at its inherited `f`; `hUniv`/`hNW` via Phase 5's preservation lemmas.
    (The heavy sum-measure lemmas `intExpMeasure_step_lt`(+`_branch`) are NOT consumed —
    they remain retained-but-unconsumed assets.) DONE across all 10 induction cases
    (case1/case9 vacuous, case4 leaf/unused, case10 vacuous from `IAllConsistent`'s own
    shape mismatch — no threading needed; case2/case5/case6/case7/case8 thread and
    re-establish `hUniv`/`hNW`/`hFuel`). Case7's `hNW` forward preservation for the
    fresh-mint arm consumes the pre-existing DP-2 strategic sorry
    (`intFreshMint_preserves_nw`) as a black box, untouched.
  - [x] Call-site repair in `openBranch_countermodel` (Scheme.lean:3448): discharge `hFuel`
    at the singleton worklist by `intWork_init_lt_intFuelExt` (Phase 4A), `hUniv` by
    singleton membership, `hNW` by `WBound_pos` (Scheme.lean:1768). DONE.
  - [x] Replace the fuel-0 refutation comment block (adjacent to the sorry) with a short note
    recording that the refutation applied to the PRE-R1 statement and pointing at R1's
    hypotheses (keep the counter-instance citation — it is the durable record of why the
    hypotheses exist). DONE.
- **Timing:** 1 dispatch. Estimated output: ~300-450 lines (net; much is hypothesis threading
  through the existing succ-case body). ACTUAL: ~440 net new/changed lines (infrastructure +
  restated lemma + call-site repair).
- **Depends on:** 4A, 4C, 5
- **Verification Tier:** local
- **Done when:** the fuel-0 sorry GONE; repo bare-sorry count in the subtree strictly
  decreased by one (modulo DP-2 which lives in a different declaration);
  `openBranch_countermodel` and `tableau_complete` build unchanged in statement; scoped build
  green. VERIFIED: bare-sorry census in the subtree is 4 (was 5), scoped build green,
  full `lake build` green (3311/3311), `lake exe checkInitImports` exit 0,
  `openBranch_countermodel`/`tableau_complete` statements unchanged (only the private
  `intExpandBranches_openBranch_sat` gained `φ0`/`hUniv`/`hNW`/`hFuel`).

### Phase 7: `truthLemma` T-imp discharge via persistence fixpoint sufficiency [BLOCKED]
- **Goal:** `Scheme.lean:617` discharged, honoring the STOP-gate's one-pass directive with
  Phase 6 (same invariants, consecutive dispatches). Unchanged in substance from v13
  (reports/15 §7); the fuel fact it consumes is now per-branch.
- **Tasks:**
  - [ ] Thread `applyPersistenceFixpoint_genuine_of_count_le_fuel` (enlarged-universe version,
    Phase 3; Scheme.lean:2928) through the open-branch extraction so the returned branch is at
    a GENUINE persistence fixpoint: every world accessible from a `T(φ'→ψ')` source carries
    its own copy (the `applyAllTImpRules` copy channel at a fixpoint). At the R1 leaf the
    active branch's remaining fuel `f' + 1` satisfies `countP ≤ intWork ≤ f'` from the
    threaded per-branch `hFuel` — same consumption as v13, per-branch. Likely lands as an
    extra conjunct in the R1 conclusion or a companion lemma over the same induction —
    implementer's choice, but the STATEMENT of `truthLemma` itself must not weaken.
  - [ ] Close the T-imp case (Scheme.lean:601-617) with `sat_timp` per the in-file analysis:
    the `F(φ')@w'` arm contradicts via `ih_φ'.2`, the `T(ψ')@w'` arm closes via `ih_ψ'.1`.
  - [ ] Update the STOP-gate note (Scheme.lean:504-557) from "Gap 1 UNCHANGED" to resolved,
    citing the fixpoint-sufficiency route.
- **Timing:** 1 dispatch. Estimated output: ~200-350 lines.
- **Depends on:** 5, 6
- **Verification Tier:** local
- **Done when:** sorry at `Scheme.lean:617` GONE; count strictly decreased by one again;
  `truthLemma`'s statement unchanged; scoped build green.

#### Blocker (dispatch against this phase, `[IN PROGRESS] → [BLOCKED]`)

**The premise of this phase's first task no longer holds in this codebase; this is a confirmed
structural blocker, not an unattempted proof.** The task list's "every world accessible from a
`T(φ'→ψ')` source carries its own copy (the `applyAllTImpRules` copy channel at a fixpoint)"
describes the "Deliverable 6" self-copy mechanism. That mechanism was **deliberately removed**
by the completed ancestor-blocking calculus-repair dependency (commit `a70187dd`, "bound the
T-implication self-copy channel (STEP 1)"), verified by direct diff inspection: the `copies`/
`combined` block that used to copy `T(φ → ψ)` itself to every accessible world was deleted from
`applyAllTImpRules`. That commit's own docstring on `applyAllTImpRules` (`Expansion.lean`)
states explicitly that Gap 1 (`sat_timp` at accessible, not just reflexive, worlds) "remains out
of scope for this task" and that `truthLemma`'s T-imp sorry "is untouched by this change" — i.e.
the dependency task knew it was leaving this exact gap open, and this plan's Phase 7 was written
(after that dependency was already listed as completed, see `## Overview` `Preserved Assets`)
without re-checking that the specific mechanism it names still existed.

**What was tried.** The full STOP-gate note in `Scheme.lean` (immediately above `truthLemma`,
"GAP 1 UPDATE" paragraph, this dispatch) documents: (1) direct diff/commit verification that the
self-copy channel is gone; (2) that `applyAllTImpRules`'s surviving ψ-consequence propagation
(`intTImpRule`) still gives a genuine-fixpoint fact `T(φ)@w'∈b → T(ψ)@w'∈b` at any accessible
`w'` from a `T(φ→ψ)@w` source, WITHOUT needing a copy at `w'` — a real, provable fact, stronger
in one sense than the removed mechanism; (3) that this fact is nonetheless insufficient to close
the case, because the goal needs `IForces` (semantic forcing) at `w'`, not branch membership,
and `truthLemma`'s own induction hypotheses only give `T(_)@w'∈b → Force` / `F(_)@w'∈b →
¬Force`, never the converse `Force → T(_)@w'∈b` needed to invoke the surviving fact. No
bivalence/totality fact bridging that gap exists elsewhere in this file. No sorry was relocated,
weakened, or vacuously discharged.

**Why it cannot be completed as written in this dispatch.** Closing this case now requires
either (a) a new, *bounded* copy-propagation variant (gated so it cannot itself trigger fresh
world creation) validated by its own divergence probe — the exact methodology the ancestor-
blocking repair used before removing the old channel — or (b) the quotient/blocking-frame
reconstruction of `sat_fimp`/`sat_timp` that an earlier research report proposed as Option A
step 3. Both are calculus-level changes to `Expansion.lean`/`Rules.lean`, outside this phase's
`Scheme.lean`-only territory, and (a) specifically risks re-opening the ancestor-blocking
repair's settled, tested, already-landed design — not a call this dispatch is authorized to make
unilaterally.

**What is needed to unblock.** A follow-up scoped exactly like the ancestor-blocking repair
itself: a dedicated calculus investigation (divergence probing a bounded copy-channel variant,
or prototyping the quotient frame against `Minimal/Soundness.lean`'s
`intExpandBranches_closed_unsat` as the soundness regression gate) before any further
`Scheme.lean`-side attempt at this case. Until that lands, this phase's sorry stays exactly
where it is, tracked in the handoff `sorry_inventory` with `discharge_phase: null` (no phase of
*this* plan can discharge it).

**Update (dedicated blocker research, reports/17_timp-continuation-options.md — GO/NO-GO
assessment of the two options above, superseding two claims in "Why it cannot be completed"
above).** (i) Option (a)'s divergence probe is not a fresh unknown: the ancestor-blocking
repair's own variant-selection probe already compared self-copy retained vs. removed and found
both terminate at the identical saturated branch, so reinstating the channel is termination-safe
— only a re-confirmation against the current tree remains, not a probe "before being trusted"
from scratch. (ii) A more decisive finding not recorded above: even a full reinstatement of the
channel would NOT by itself close this case, because `truthLemma`'s frame ranges over an
AUGMENTED edge list (carrying the ancestor-blocking repair's loop-back edges) while any copy
channel only reaches the algorithm's RAW edges — a gap strictly larger than the copy-channel
question. Option (b) (quotient/blocking-frame reconstruction) is assessed NO-GO: this exact
design was built, then refuted and deleted, earlier in this codebase's history (a non-monotone
representative-map obstruction under branch growth), with independent literature confirmation.
**Recommendation, not re-executed by this plan**: widen task 430's scope from atom-persistence
to positive-formula-persistence along the augmented relation (this phase's Gap 1 is the
implication-shaped instance of the same fact DP-3/DP-4 need at the atom shape), gated behind a
Lean-prototype check of the loop-back transfer lemma before any calculus change. Phase 7 stays
`[BLOCKED]`; this plan takes no further action against it — see Phase 8's re-annotation of the
T-imp sorry as DP-5.

### Phase 8: Documentation accuracy + full CI gate [COMPLETED]
- **Goal:** No stale claim survives; the full repository gate passes.
- **Tasks:**
  - [x] Update `intUniverse`'s warning docstring (now Scheme.lean:1510-1531, shifted since the
    plan was written) to point at `intUniverseExt`/`WBound` as the live development; refutation
    record kept.
  - [x] Engine-restructure documentation (reports/15 §7 additions): the `intFuel` →
    `intFuelExt` story and per-branch fuel semantics were already documented at the
    `## Per-Branch-Fuel Expansion Engine` module note (pre-existing, accurate, verified this
    dispatch — no edit needed); expanded the `## Strict-Decrease Engine` module note to mark
    the sum-measure engine (`intExpMeasure`, `intWork`, `intExpMeasure_step_lt`(+`_branch`)) as
    retained-but-unconsumed, record candidate (b) as elective post-DP-2 future work and
    candidate (c) as rejected with its rationale, and record the `s ≲ 22` corpus-row
    feasibility envelope. **Divergence-witness note update deferred**: it lives in
    `Expansion.lean`, out of this dispatch's territory (task 574's file, explicitly excluded);
    verified read-only that it already reads "Historical record, measured on the RETIRED
    global-fuel expansion loop" — already accurate, not stale, no edit required there.
  - [x] Synced comments in both `Completeness.lean` files: both monotonicity-bridge `sorry`s
    no longer misstate the blocker as awaiting the fuel-sufficiency fixpoint (landed, modulo
    the unrelated DP-2 sorry) — corrected to name the actual blocker (positive-formula
    persistence along the augmented relation, same fact as DP-5 at the atom shape). The bridge
    sorries themselves are untouched (task 430's territory).
  - [ ] Optional conformance regression row: SKIPPED — genuinely optional per the plan's own
    wording ("Optionally add"), and `lake test`'s existing 44-row corpus (verified green this
    dispatch) already exercises the per-branch fuel path including the divergence-witness row.
  - [x] Sorry accounting: bare-sorry census in the subtree is exactly 4 — DP-2, DP-3, DP-4,
    DP-5 (re-annotated this dispatch; Phase 7's T-imp sorry, NOT discharged, was never DP-3/DP-4
    but is now a fifth accounted row) — enumerated in the summary's `sorry_inventory`.
  - [x] Full CI gate run in order: `lake build` (full, 3311/3311 green), `lake exe
    checkInitImports` (exit 0), `lake lint` (RED, but zero findings in this task's three
    territory files — see Phase 8 completion note below for the full accounting), `lake exe
    lint-style` (clean, zero output), `lake test` (green, `CslibTests.TableauConformance`
    built successfully, no observed timing regression), `lake exe mk_all --module` (skipped —
    no new file was added, per the plan's own conditional), `lake shake --add-public
    --keep-implied --keep-prefix` (zero import-drift findings for any of the three territory
    files; all findings are in unrelated pre-existing files elsewhere in the repo).
- **Timing:** 1 dispatch. Estimated output: ~100-180 lines.
- **Depends on:** 1-7
- **Verification Tier:** full
- **Done when:** all gates green; summary written; `sorry_inventory` complete and matching the
  Planned Strategic Sorries table (or flagging deviations).

**Phase 8 completion note — `lake lint` gate.** `lake lint` is RED at the repository level, but
every finding is a pre-existing unused-argument warning in unrelated modules (`Bimodal/**`,
`LTL/**`, `Modal/Tableau/FrameSoundness.lean`, `Temporal/**`) — grep-verified zero findings
against `Intuitionistic/Scheme.lean`, `Intuitionistic/Completeness.lean`, or
`Minimal/Completeness.lean`. This dispatch introduces no new lint debt; the repo-wide backlog
is out of this task's `file_scope` and is not a regression this dispatch caused or is
responsible for clearing. Flagging explicitly per the dispatch mandate rather than reporting an
unearned full-green CI gate.

## Planned Strategic Sorries

| Division Point | File / Line / Statement | Assumption | Why Deferred | Follow-Up Task |
|-----------------|--------------------------|------------|---------------|----------------|
| DP-1: chain-bound lemma — **RESOLVED, PROVED INLINE (Phase 2)** | Scheme.lean:1805 (`intCreatedChain_le`) | (was: the ψ-conditioned pigeonhole bounds created-world chains) | No sorry placed; `lean_verify` clean. Row retained for accounting continuity only | 585 (needed only if DP-2 is placed — decided at Phase 5) |
| DP-2: `hNW` preservation, fresh-mint arm | Scheme.lean, TBD (Phase 5) | Labels minted on a branch ≤ tree size ≤ `WBound φ` (incl. the runtime-check-to-final-branch transfer noted in `intCreatedChain_le`'s docstring) | Creation-count invariant beyond 583's sketch; the remaining research-grade concentration | 585 |
| DP-3: intuitionistic validity bridge (pre-existing, NOT placed by this plan) | Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:133 (`intuitionisticTableau_complete`) | Upward-closure of `intExtractValuation b` along `intAccessPreorder edges` (IAtomPersist route) | Owned by existing planned task 430 (deps already point 430 → 317); presupposes saturated branches, i.e. this plan's output | 430 |
| DP-4: minimal validity bridge (pre-existing, NOT placed by this plan) | Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:125 (`minimalTableau_complete`) | Upward-closure of `intExtractValuation b` AND `minBranchBotForces b` along the frame | Same as DP-3 | 430 |
| DP-5: `truthLemma` T-imp Gap 1 (pre-existing, RE-ANNOTATED by Phase 7's blocker research; NOT newly placed by this plan) | Scheme.lean, `truthLemma`, `imp` case, T-direction (line 602 at time of the Phase 7 blocker; re-locate by content if shifted) | `∀ w'` accessible from `w`, `T(φ'→ψ')@w ∈ b → w'` carries its own `T(φ'→ψ')` copy (positive-formula persistence along the augmented `intAccessPreorder edges` relation, at the implication shape) | Same fact as DP-3/DP-4's monotonicity bridge, one formula shape over (atom vs. implication). A bare self-copy-channel revert is termination-safe (measured by the ancestor-blocking repair's own variant-selection probe) but insufficient alone: `truthLemma`'s frame ranges over the augmented (loop-back-edge-carrying) edge list, while any copy channel only reaches the algorithm's raw edges. Widened into task 430's scope per reports/17 (`prove_atom_persistence_upward_closure_for_intexpan` → positive-formula persistence along the augmented relation) | 430 |

Notes: DP-2 is contingent — if the Phase 5 proof closes within budget, no sorry is placed and
the follow-up task 585 should be closed as unnecessary by the orchestrator/user (DP-1 already
closed without it). DP-3/DP-4/DP-5 are pre-existing sorries recorded for complete accounting;
they are not new placements and cite the existing task number directly. DP-5 is the T-imp
`sorry` Phase 7 was originally scoped to discharge; the dedicated blocker research (reports/17)
found the closure route it depended on structurally unavailable in this codebase (see Phase 7's
`[BLOCKED]` note below) and recommended re-annotating it into the same accounting treatment as
DP-3/DP-4 rather than re-planning Phase 7 — done in this dispatch. The fuel-0 sorry that
Phase 4B carries through the port is NOT a DP row — it is the pre-existing `Scheme.lean:3055`
sorry (one of the four), transported 1-for-1 and discharged in Phase 6.

## Testing & Validation

- [x] Per-phase scoped `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`
  (plus `.Soundness` at 4B, `.Expansion` when touched) — every phase, incl. Phase 8's own
  scoped build of Scheme/Completeness/Minimal.Completeness.
- [x] Phase 4A: `#eval` parity probe `intVerdictB = intVerdict` on all 20 propositional
  corpus rows; `lake test` wall-time baseline recorded.
- [x] `lake test` at Phases 4C and 8 (conformance corpus, all 44 rows, esp. divergence-witness
  row 20): green this dispatch, `CslibTests.TableauConformance` built successfully within the
  full `lake test` run; no observed timing regression (full suite completed well inside the
  command budget).
- [x] Sorry census: exactly 4 bare sorries in the subtree at Phase 8 exit (DP-2, DP-3, DP-4,
  DP-5) — grep-verified this dispatch (`\bsorry\b` excluding comment/docstring lines). Phase 6
  discharged the fuel-0 sorry as planned; Phase 7 did NOT discharge DP-5 (T-imp Gap 1) —
  `[BLOCKED]` per its dedicated blocker research, DP-5 re-annotated into the terminal
  accounting instead of a strict decrease.
- [x] `lean_verify` (Phase 8, this dispatch) on all four public completeness consumers:
  `openBranch_countermodel`, `tableau_complete` (`Scheme.lean`),
  `intuitionisticTableau_complete` (`Intuitionistic/Completeness.lean`),
  `minimalTableau_complete` (`Minimal/Completeness.lean`) — all four report axiom set
  `{propext, Classical.choice, Quot.sound, sorryAx}`, exactly as expected; `sorryAx` is
  present only via the four declared DP sorries, no unexpected axiom.
- [x] Sorry census at Phase 8: bare sorries in the subtree = {DP-2, DP-3, DP-4, DP-5} —
  matches exactly, confirmed by direct grep. DP-5 (T-imp Gap 1) was NOT discharged — Phase 7
  is `[BLOCKED]` per its dedicated blocker research (reports/17) and DP-5 carries the
  strategic-sorry annotation into this plan's terminal accounting instead.
- [x] Full CI order per cslib.md (Phase 8 checklist): all gates run this dispatch; `lake lint`
  is RED at the repo level but with zero findings against this task's three territory files
  (see Phase 8's completion note above) — every other gate (`lake build` full, `checkInitImports`,
  `lint-style`, `lake test`, `lake shake`) is green.

## Artifacts & Outputs

- plans/14_fuel-materialization-repair.md (this file)
- specs/317_propositional_tableau_completeness/.skeleton-return.json (companion; `new_tasks`
  declaration for 585 — needed only if DP-2 is placed)
- summaries/14_fuel-materialization-repair-summary.md (implementation summary, on completion)
- Modified: Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean,
  Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean,
  Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean (4B/4C ports and
  repointing), possibly Minimal-side consumer files (4C repointing only);
  CslibTests/TableauConformance.lean (import repoint at 4C; optional Phase 8 row addition;
  possible temporary 4A parity section)

## Rollback/Contingency

- Every phase commits per green substep (`task 317 phase {P}.{O}: …`); rollback = revert the
  phase's commits. No phase leaves the tree red at a commit boundary. The
  parallel-build-then-flip staging (4A/4B beside the old engine; single flip commit at 4C)
  guarantees the old engine and all its consumers stay green until the flip is fully proven.
- If 4A's WF elaboration fails through ALL named fallbacks (functional induction → manual WF
  induction → `go` selector-refactor), STOP at Phase 3's landed value, mark the plan
  [BLOCKED], and hand the finding to the orchestrator — do not force the engine and do not
  fall back to candidates (b)/(c) (Postmortem constraints 12-13).
- If the 4C timing gate fails (row 20 wall time out of budget), the phase is BLOCKED, not
  worked around: do not remove or weaken row 20 (the divergence-witness regression), do not
  cap digits — surface the measurement to the orchestrator.
- If DP-2 is sorried AND Phase 6's succ-case threading additionally fails, the skeleton
  premise is broken: mark [BLOCKED] with a handoff enumerating exactly which invariant
  re-establishment failed, rather than landing a hollow shell.

## Research Integration

- **Newly integrated**: reports/15_fuel-materialization-repair.md — supplies the entire
  Phase 4A/4B/4C replacement spec (§6), the Phase 5-8 impact deltas (§7: per-branch `hFuel`
  form, omega fuel-0 discharge, `intWork_init_lt_intFuelExt` call-site discharge, Phase 8 doc
  additions), the engine-independence audit backing the Preserved Assets table, the
  candidate (b)/(c) prohibitions (Postmortem constraints 12-13), the row-20 numeral
  correction (~13.0M digits, 599 ms — encoded as the 4C timing gate, not a digit cap), and
  the `s ≲ 22` feasibility envelope.
- **Carried forward** (already integrated in v13): reports/14 adversarial-verification
  section; 583's report (F3/F5/F6); reports/01-11 lineage as superseded background.
- `reports_integrated`: 01_tableau-completeness-research.md, 03_tableau-completeness-approach.md,
  04_fuel-sufficiency-measure.md, 05_fuel-sufficiency-literature.md,
  06_sfor-dedup-reuse-abstraction.md, 07_option-b-fuel-bound.md, 08_b1-truthlemma-timp.md,
  09_phase2-escape-routes.md, 10_wave-a-atomic-derisk.md, 11_team-research.md,
  13_blocker-root-cause-and-correct-approach.md (adversarial section only),
  14_blocker-analysis.md (adversarial section only), 15_fuel-materialization-repair.md
