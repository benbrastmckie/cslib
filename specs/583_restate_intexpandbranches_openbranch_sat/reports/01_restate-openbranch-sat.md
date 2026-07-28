# Research Report: Restating `intExpandBranches_openBranch_sat` (fuel-0 refutation)

- **Task**: 583 — restate `intExpandBranches_openBranch_sat` so it is provable, repair call
  sites, discharge the sorry
- **Session**: sess_1785275816_a84520_583
- **Agent**: cslib-research-hard-agent (H2/H3/H4 contracts active)
- **Reference grounding tier**: Tier 3 (implementation-backed) primary, with Tier 1 anchors
  (Fitting1983, GargGenoveseNegri2012, Dyckhoff1992 — all BibKeys verified in `references.bib`)
- **Literature**: `[lit] SUBINDEX_PRESENT` — per-repo sub-index (34 docs) used; it contains
  **no** chunks for Fitting1983 or GargGenoveseNegri2012 (verified by grep over the briefing),
  so Tier 1 anchoring below rests on `references.bib` entries + in-file provenance notes.

## Executive Verdict

1. **Not superseded by the divergence repair.** The ancestor-blocking repair task completed
   (commit `7106f60e` lineage; phase 7.2 commit message: "sorry count unchanged at 6") and did
   NOT restate this lemma. The sorry is now at `Scheme.lean:2551` (statement at
   `Scheme.lean:2510-2523`); the counter-instance note is at `Scheme.lean:2526-2550`.
2. **The refutation still holds — mechanically re-verified today** against the current
   (post-repair) code, not just re-read (see Verification Log below).
3. **Central structural finding**: any restatement whose call site remains
   `openBranch_countermodel` (`Scheme.lean:2966`) at fuel `intFuel φ` is **provably equivalent
   to the fuel-sufficiency theorem** ("the run at `intFuel φ` never exhausts fuel with an open
   branch"). No hypothesis weaker than that can be both (a) dischargeable at the call site and
   (b) re-establishable through the fuel induction. Details in Finding F3.
4. **The fuel-sufficiency theorem is not provable today**: its only known proof route (the
   already-landed measure engine) requires the universe-containment invariant
   `∀ x ∈ b, x ∈ intUniverse φ0`, which the file itself documents as refuted
   (`Scheme.lean:1591-1599`; divergence-witness note `Expansion.lean:450-494`). Post-repair,
   no replacement world-label bound has been proven (the repair added only an empirical
   termination-regression test, not a termination theorem).
5. **Recommendation**: mark task 583 **[BLOCKED]** and `/spawn` the named prerequisite
   (post-blocking termination bound + measure re-targeting, "B2"); the exact restatement to
   land afterwards is specified concretely in Finding F5 (hypothesis-threading form R1,
   fallback trichotomy form R2). This is a blocked-with-decomposition verdict, not an
   analysis-only verdict: the target statement, its discharge proof shape, the call-site
   repair, and the prerequisite's acceptance gate are all written out below.

## Source-to-Implementation Mapping

| Source Claim | BibKey | Lean Target | Translation Notes |
|--------------|--------|-------------|-------------------|
| Systematic intuitionistic tableau: an open saturated branch yields a Kripke countermodel (Ch. 4) | Fitting1983 | `openBranch_countermodel` (`Scheme.lean:2944`), `intExpandBranches_openBranch_sat` (`Scheme.lean:2510`) | Fitting's construction presumes the systematic procedure *terminates in saturation*; the Lean encoding replaces termination with a fuel bound, so "openBranch ⇒ saturated" holds only under fuel-sufficiency — exactly the gap at the fuel-0 case |
| Termination of intuitionistic proof search via loop-checking / contraction-free calculi | Fitting1983, Dyckhoff1992 | (missing) — the "B2" fuel-sufficiency theorem; prerequisites: post-blocking world bound + `intExpMeasure` re-target | Dyckhoff1992 achieves termination calculus-side; the CSLib calculus instead uses ancestor blocking (landed) whose termination *theorem* is unformalized |
| M ∪ C loop-back-edge countermodel construction | GargGenoveseNegri2012 | `augSets`/`IAllAccessConsistent` threading through this lemma's induction | Landed by the divergence-repair work; provenance only — does not bear on the fuel-0 case |

## Verification Log (H4 evidence, gathered before conclusions)

Mechanical re-check of the counter-instance on current sources, via `lean_run_code`:

```lean
#eval match intExpandBranches (Atom := Nat) [[⟨.neg, pq, 0⟩]] [[]] [1] [[]] 0
        isIntuitionisticallyClosed with ...
-- Output: "openBranch, unchanged singleton: true, has F(p)@0 or F(q)@0: false"
```

At `fuel = 0` with `branches = [[⟨.neg, p ∧ q, 0⟩]]`, `expandedSets = [[]]`,
`nextWorlds = [1]`, `edgeSets = [[]]`: the run returns `.openBranch` of the *unchanged*
singleton, which lacks both `F(p)@0` and `F(q)@0`, so `IBranchSaturation.sat_fand`
(`Scheme.lean:86`) fails. Hypothesis check against current definitions: `hAC` holds
(`IExpandedConsistent b []` vacuous, `ILabelBound b 1` holds since label `0 < 1`), `hLen0` is
`1 = 1`, `hACC` vacuous with `augSets = [[]]`. Every hypothesis holds, the conclusion is
false: **the lemma remains refuted as stated**.

## Findings

### F1. State of the code (post-divergence-repair)

- Sorry inventory in this subtree (bare sorries): `Scheme.lean:617` (truthLemma T-imp case),
  `Scheme.lean:2551` (this task), `Completeness.lean:133`, `Minimal/Completeness.lean:125`.
- The succ-fuel case of `intExpandBranches_openBranch_sat` is **fully discharged**, including
  the genuine-saturation leaf (`intStepBranch = none` at `Scheme.lean:2630-2638`, closed via
  `IExpandedConsistent_sat`/`IExpandedAccessConsistent_sat`). Only the fuel-0 base case is
  sorried.
- The fuel-0 arm of `intExpandBranches` (`Expansion.lean:341-346`) returns
  `.openBranch (first open branch)` — i.e. fuel exhaustion is *indistinguishable* from
  genuine saturation in the result type (`IntTableauResult`, `Expansion.lean:77-81`, two
  constructors only).
- Sole call site: `openBranch_countermodel` (`Scheme.lean:2966`), invoked at `intFuel φ`
  (`Expansion.lean:510-511`); consumed upward by `tableau_complete` (`Scheme.lean:3000-3011`)
  and ultimately the registered instance `instDecidableIValid`
  (`DecisionProcedure.lean:107-113`).

### F2. Existing machinery inventory (all sorry-free, all currently *unused* by any proof)

| Piece | Location | Status |
|-------|----------|--------|
| `intWork`, `intExpMeasure` (base-3 damped worklist measure) | `Scheme.lean:1913-1921` | landed |
| `intExpMeasure_step_lt` (alpha/linear arm strict decrease) | `Scheme.lean:2077` | landed; requires `hb : ∀ x ∈ bh, x ∈ intUniverse φ0` |
| `intExpMeasure_step_lt_branch` (beta arm) | `Scheme.lean:2145` | landed; same `hb` |
| `intExpMeasure_init_le_fuel` (initial measure ≤ `intFuel φ`) | `Scheme.lean:2279` | landed |
| `applyAllTImpRules_count_drop` (persistence round strict drop) | `Scheme.lean:2358` | landed; same `hb` |
| `applyPersistenceFixpoint_genuine_of_count_le_fuel` (persistence-fixpoint sufficiency; closes the sat_timp STOP-gate "Gap 1" *lemma-side*) | `Scheme.lean:2424` | landed; same `hb` |

The single missing link is the `hb` premise as a **loop invariant**: `Scheme.lean:1591-1599`
states outright "Do not read `∀ x ∈ b, x ∈ intUniverse φ` as an established invariant of
`intExpandBranches`", backed by the divergence-witness measurements
(`Expansion.lean:450-494`, consequences (a)-(c): world labels escape
`List.range (φ.complexity + 2)`). Those measurements predate the ancestor-blocking repair;
the repair plausibly bounds world growth (blocking cuts Sfor-set-contained repeats) but **no
post-repair bound has been proven** — the repair's acceptance artifact is an empirical
`#eval` termination-regression row in `CslibTests/TableauConformance.lean`, not a theorem.

### F3. Equivalence result: why no cheap precondition exists

Let `H(branches, expandedSets, nextWorlds, edgeSets, fuel)` be any added precondition making
the lemma provable. The fuel induction requires `H` to be re-establishable for the
successor-case recursive calls (each arm recurses into `intExpandBranches ... fuel'`, and
`fuel'` can reach 0 mid-run). Since the loop is deterministic, the *weakest* such `H` is "the
run from this state does not exhaust fuel while an open branch remains". Preservation of that
`H` is trivial (the tail of a non-exhausting run is non-exhausting); dischargeability at the
call site is precisely **fuel-sufficiency of `intFuel φ`** for the post-blocking calculus.
Every candidate checked reduces to this:

- *Saturation precondition on the initial worklist*: fails at the call site — the initial
  worklist `[[⟨.neg, φ, 0⟩]]` with `expandedSets = [[]]` is genuinely unsaturated for every
  compound `φ`; only fuel connects the initial state to saturation.
- *`0 < fuel`*: not preserved — the IH is invoked at `fuel'` which can be 0.
- *Measure bound `intExpMeasure (intUniverse φ0) branches expandedSets ≤ fuel`* (form R1):
  at fuel 0 forces measure 0, hence empty worklist, hence result `.closed` — contradiction
  with `h`, base case closes. Preservation through the succ case is exactly the
  strict-decrease engine of F2 — blocked solely on the refuted/unproven `hb` invariant (plus
  a `nextWorlds`-bound companion invariant for the world-creating arm).
- *Result-type trichotomy* (form R2, add `.fuelExhausted`): makes THIS lemma provable with no
  added hypotheses (both fuel-0 arms then return `.closed`/`.fuelExhausted ≠ .openBranch`),
  but relocates the identical obligation into `tableau_complete`'s new `.fuelExhausted` case
  and into `instDecidableIValid`'s third match arm, where only the fuel-sufficiency theorem
  (or a new sorry, or demoting the registered `Decidable` instance) can close it.

Conclusion: **discharging this sorry without new debt requires the fuel-sufficiency theorem
first**, under every restatement compatible with the existing call-site chain.

### F4. Corroboration from the file's own STOP-gates and the task queue

- `Scheme.lean:504-557` (sat_timp STOP-gate): "build the persistence fuel-sufficiency measure
  (Gap 1) as its own effort, then revisit `truthLemma`'s T-imp case together with
  `intExpandBranches_openBranch_sat`'s fuel-0 `sorry` in one pass ... Do NOT attempt to force
  either `sorry` via a weakened/vacuous statement." The lemma-side half of Gap 1 has since
  landed (F2); the invariant half (containment) has not.
- The S4-modal analogues of exactly this obligation are themselves blocked tasks in the queue
  (`s4_loop_checking_termination`, `s4_loopchecking_machinery_termination_bound_and_decidability`)
  — independent evidence that post-blocking termination bounds are a substantial development,
  not a phase-sized gap.
- No queued task currently covers the intuitionistic-side fuel-sufficiency prerequisite; the
  nearest neighbors (`prove_atom_persistence_upward_closure_for_intexpan`, the researched
  umbrella completeness task) target the monotonicity bridge, not B2.

### F5. Recommended restatement (to land once the prerequisite exists)

**Primary form (R1 — hypothesis threading; no result-type change, no `Decidable` ripple):**

```lean
private lemma intExpandBranches_openBranch_sat (φ0 : Proposition Atom) (fuel : Nat)
    (branches ...) (expandedSets ...) (nextWorlds ...) (edgeSets ...) (augSets ...)
    (closurePred ...) (b ...)
    (hAC : IAllConsistent branches expandedSets nextWorlds)
    (hLen0 : branches.length = edgeSets.length)
    (hACC : IAllAccessConsistent branches expandedSets augSets)
    (hUniv : ∀ b' ∈ branches, ∀ x ∈ b', x ∈ intUniverseExt φ0)   -- NEW (enlarged range)
    (hNW : ∀ nw ∈ nextWorlds, nw ≤ WBound φ0)                     -- NEW (post-blocking bound)
    (hFuel : intExpMeasureExt φ0 branches expandedSets ≤ fuel)    -- NEW (fuel-sufficiency)
    (h : intExpandBranches ... = .openBranch b) :
    ∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b
```

- Fuel-0 discharge: `hFuel` gives measure 0; each worklist cell contributes `3 ^ k ≥ 1`, so
  the zipped worklist is empty; `intExpandBranches [] ... 0` reduces to `.closed`,
  contradicting `h` — no saturation reasoning needed at fuel 0.
- Succ-case re-establishment: linear arm via `intExpMeasure_step_lt` (its generic `b'`/`hsub`
  form covers both the extend arm and the reuse-stall arm with `b' := bPers`); beta arm via
  `intExpMeasure_step_lt_branch`; persistence non-increase via `intCount_notMem_mono`;
  persistence containment via the iterated `applyAllTImpRules_subset`. All exist (F2) and
  only need `intUniverse` generalized to the enlarged domain.
- Call-site repair (`openBranch_countermodel`): discharge `hFuel` by the
  `intExpMeasure_init_le_fuel` analogue over the enlarged universe (resizing `intFuel`
  accordingly), `hUniv` by singleton-membership, `hNW` by `1 ≤ WBound φ0`.

**Fallback form (R2 — trichotomy)** if the prerequisite instead lands as a standalone
"no-exhaustion" theorem: add `.fuelExhausted` to `IntTableauResult`, return it from the
fuel-0 arm when an open branch remains; this lemma then discharges with **zero** new
hypotheses; `tableau_complete`'s and `instDecidableIValid`'s new cases close by `absurd` with
the no-exhaustion theorem. Wider API/conformance-corpus ripple (result rows and the two-arm
`Decidable` match), so R1 is preferred.

**Prerequisite task (to spawn; acceptance gate)**: prove a post-blocking world-label bound
`WBound φ` (from ancestor blocking: along any edge chain, each created world's Sfor-set is
not contained in any open ancestor's lacking its ψ — yielding an antichain-style bound
≤ exponential in subformula count), define `intUniverseExt`/`intExpMeasureExt` over
`List.range (WBound φ)`, re-target the F2 engine (statements are parametric in the universe
list; proofs re-run), resize `intFuel φ := 3 ^ |intUniverseExt φ|`, and prove the threading
invariants (`hUniv`/`hNW` preservation through all four recursion arms). Gate:
`intExpandBranches_openBranch_sat` restated per R1, sorry at `Scheme.lean:2551` discharged,
`lake build` green, repo bare-sorry count strictly decreased by one.

### F6. What must NOT be done (zero-debt + in-file directives)

- Do not weaken/vacuize the statement or the downstream `tableau_complete` (explicit in-file
  prohibition, `Scheme.lean:502,556-557`).
- Do not relocate the sorry (to `tableau_complete`, the `Decidable` instance, or a new
  "no-exhaustion" axiom) — forbidden deferral patterns.
- Do not attempt the containment invariant against the *current* `intUniverse` range — refuted
  (`Scheme.lean:1591-1599`), and the divergence-witness directive (`Expansion.lean:485-489`)
  requires any new bound to come from the blocking combinatorics, not from
  `intUniverse`'s linear range.

## Adversarial Self-Verification

| Claim | Source/Counterexample | Verdict |
|-------|----------------------|---------|
| The counter-instance still refutes the current statement | Live `lean_run_code` #eval on post-repair code: `.openBranch` of unchanged singleton, `sat_fand` premise true / disjuncts false; hypotheses re-checked against `IExpandedConsistent`/`ILabelBound`/`IAllAccessConsistent` defs | VERIFIED (mechanical) |
| The divergence-repair task did not restate the lemma (task not superseded) | Phase 7.2 commit message "sorry count unchanged at 6"; sorry present at `Scheme.lean:2551`; statement at `2510-2523` textually unchanged | VERIFIED |
| Succ case is fully discharged incl. the saturation leaf | Read of `Scheme.lean:2552-2915`: no sorry; leaf closed at `2637-2638` | VERIFIED |
| Measure engine + persistence-sufficiency lemmas exist sorry-free but unused | Grep: only doc-comment references, no proof-term uses; defs/proofs read at `1913-1921`, `2077`, `2145`, `2279`, `2358`, `2424-2487` | VERIFIED |
| Universe containment is refuted as a loop invariant | Explicit warning `Scheme.lean:1591-1599` + divergence note `Expansion.lean:450-494`; measurements predate blocking repair — post-repair status is OPEN (unproven), not re-refuted | VERIFIED with scope caveat (pre-repair refuted; post-repair unproven either way) |
| Any dischargeable restatement ⇔ fuel-sufficiency at the call site | Determinism argument (F3); each candidate hypothesis individually checked against the induction structure (`Scheme.lean:2524`, `2552-2573`, recursion arms `Expansion.lean:373-420`) | VERIFIED (structural argument; challenged below) |
| R2 (trichotomy) cannot land sorry-neutrally | `tableau_complete` case analysis (`Scheme.lean:3006-3011`) and `instDecidableIValid` two-arm match (`DecisionProcedure.lean:108-113`) both gain an uncloseable case; FMP-fallback alternative rejected (noncomputable, demotes the registered computable instance) | VERIFIED |
| BibKeys Fitting1983, GargGenoveseNegri2012, Dyckhoff1992 exist | `references.bib:211,228,217` | VERIFIED |

**Challenged and retained**: the F3 equivalence was challenged with a "fuel-stability"
candidate (hypothesize the same `.openBranch b` at `fuel` and `fuel + 1`): rejected because
the reuse-stall arm can return an identical branch at consecutive fuels without saturation,
and the call site could not discharge stability anyway without sufficiency.
**Challenged and revised**: an early draft recommended R2 as the primary restatement; the
adversarial pass surfaced the `Decidable`-instance terminus (no third arm closes without the
sufficiency theorem), demoting R2 to fallback and forcing the [BLOCKED]-with-prerequisite
verdict.
**Uncertainty (medium confidence)**: the prerequisite's world-bound combinatorics
(antichain-style bound from the ψ-conditioned blocking check) is sketched, not proven; its
difficulty estimate (comparable to the divergence-repair task itself) is corroborated by the
blocked S4 analogues but not measured.

## Reuse Check Protocol (all 5 steps)

1. `Cslib.Foundations.*`: `Cslib/Foundations/Logic/Tableau/Measure.lean` supplies
   `pow3_add_one_le`/`pow3_two_add_one_le` (already used by the engine) — reuse, nothing new.
2. Typeclass hierarchy: not applicable (no new notation/typeclass proposed).
3. Notation: none proposed.
4. Mathlib: measure plumbing uses `List.countP`/`Sublist` lemmas already in place; no missing
   Mathlib instantiation identified.
5. Logics/Languages: the Modal-K `FmpMeasure.lean` development is the template the engine
   already mirrors (`modalExpMeasure`, `modalWork`); the prerequisite should mirror its
   universe-parametric structure rather than invent new abstractions.

## Recommended Next Steps

1. Mark task 583 **[BLOCKED]** (blocker: missing post-blocking fuel-sufficiency prerequisite).
2. `/spawn 583` to create the prerequisite task per F5's acceptance gate (world bound +
   enlarged universe + engine re-target + `intFuel` resize + threading invariants).
3. On prerequisite completion, re-dispatch 583 to land restatement R1 and discharge the sorry;
   revisit `truthLemma`'s T-imp sorry (`Scheme.lean:617`) in the same pass, per the in-file
   STOP-gate's "one pass" directive — both consume the same invariants.
