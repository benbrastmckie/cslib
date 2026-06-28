# Implementation Plan: Task #376

- **Task**: 376 - Prove the fuel-sufficiency lemma for classical tableau completeness
- **Status**: [NOT STARTED]
- **Effort**: 5 hours (with high-variance tail; see Risks)
- **Dependencies**: None (spawned from task 363; unblocks 363's zero-debt green build)
- **Research Inputs**: specs/363_repair_classical_tableau_completeness/.orchestrator-handoff.json (blockers[0])
- **Artifacts**: plans/01_fuel-sufficiency-lemma.md (this file)
- **Standards**: plan-format.md, status-markers.md, cslib.md, lean4.md
- **Type**: cslib
- **Lean Intent**: false
- **Chosen Approach**: A (fuel-sufficiency), restated and corrected per the findings below

## Overview

The target is the `sorry` at `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:492`,
the body of `classicalExpandBranches_hintikka`. This plan commits to **Path A** (fuel
sufficiency) but corrects its premise based on two findings established during planning:

1. **The general lemma is FALSE as stated.** Concrete counterexample:
   `classicalExpandBranches [[⟨.pos, p ∧ q, ()⟩]] [[]] 0` evaluates the `fuel = 0` branch,
   finds the single non-closed branch via `findSome?`, and returns
   `.openBranch [T(p∧q)]`. That branch is open but **not** Hintikka (the linear rule for
   `T(p∧q)` requires `T(p)` and `T(q)` on the branch, which are absent). The current
   invariant (over `expandedSets`) is satisfied vacuously (`expandedSets = [[]]`). So the
   lemma claims a non-Hintikka branch is Hintikka. **No proof can close the lemma in its
   present universally-quantified-over-all-fuel form.** It must be restated with a
   fuel-sufficiency hypothesis (Path A's core idea), or bypassed.

2. **`fuel` counts GLOBAL expansion events.** In `classicalExpandBranches`, exactly one
   unit of fuel is consumed per single-formula expansion on a single branch (the
   `classicalStepBranch ... = some (...)` recursion decrements fuel by one; closed-branch
   skips inside `processNext` consume none). Because beta-rules duplicate the branch
   (`Branch.extendMany` copies the whole branch into each child), the total number of
   expansion events until the first open-saturated branch is found is, in the worst case,
   exponential in `φ.complexity`. The bound `4*(φ.complexity+1)+1` is **linear**. Therefore
   the linear bound is, in the general (adversarial-branching) case, **insufficient** to
   guarantee saturation. This is the genuine, previously-unrecognized root cause of the
   blocker.

The plan attacks the problem in the only structurally sound order: (i) restate the lemma with
a sufficiency hypothesis so it becomes TRUE and provable; (ii) prove it by fuel induction
using a soundly-decreasing measure; (iii) discharge the sufficiency hypothesis at the single
real call site (`classicalTableau`), which is where the linear-vs-exponential question is
decided. Phase 1 is a hard go/no-go that determines whether the existing linear bound can be
discharged or whether the bound in `Expansion.lean` must be raised to a provably-sufficient
value (a change that is safe for the already-proven, fuel-generic `classicalTableau_sound`).

### Research Integration

From `blockers[0]`: the `fuel = 0` base case is unprovable with the current invariant because
the invariant covers only already-expanded formulas (`sf ∈ expandedSets[i]`), not
`sf ∈ branches[i] \ expandedSets[i]`. The four prior approaches all modified the *invariant*;
none introduced a *separate fuel-sufficiency lemma*. Path A (the handoff's recommendation) is
therefore genuinely untried. This plan executes it, while correcting the false premise that the
*existing* linear bound is sufficient.

### Prior Plan Reference

No prior plan for task 376. Parent task 363's plan
(`specs/363_repair_classical_tableau_completeness/plans/01_repair-classical-tableau-completeness.md`)
established the surrounding proofs; its companion lemma
`classicalExpandBranches_openBranch_initial_mem` (Completeness.lean:540-638) is a fully-validated
fuel-induction + `processNext`-inner-induction skeleton that this plan reuses verbatim as the
proof scaffold. Treat it as a preserved asset, not a template to rewrite.

### Roadmap Alignment

No ROADMAP.md consulted for this spawned sub-task. The deliverable advances task 363's
completeness proof for the classical propositional tableau decision procedure.

## Goals & Non-Goals

**Goals**:
- Make `classicalExpandBranches_hintikka` a TRUE statement (add fuel-sufficiency hypothesis or
  bypass via a sufficiency-strengthened helper).
- Prove it sorry-free.
- Discharge the sufficiency obligation at the `classicalTableau` call site so that
  `classicalTableau_hintikka` (Completeness.lean:643) and downstream `classicalTableau_complete`
  build green with zero `sorry`.
- Keep `classicalTableau_sound` (Soundness.lean:621, proven, fuel-generic) green.
- `lake build` and `lake test` pass.

**Non-Goals**:
- Re-proving soundness or the truth lemma.
- Optimizing the decision procedure's runtime.
- Eliminating fuel in favor of well-founded recursion (this is the *fallback* spawn target,
  not in scope unless Phase 3/3' prove intractable).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Linear bound `4*(complexity+1)+1` is genuinely insufficient (no measure ≤ linear fuel exists), so the call-site hypothesis cannot be discharged | H | **H** | Phase 1 go/no-go decides this empirically. Contingency Phase 3' raises the bound in `Expansion.lean` to a provably-sufficient value; safe for fuel-generic soundness. |
| Even an exponential bound's sufficiency proof (tree-size induction) is intractable in budget | H | M | Fallback: mark phase [BLOCKED], document precisely, recommend a spawn task to refactor `classicalExpandBranches` to well-founded recursion (removing fuel). Preserve all validated assets. |
| No additive/multiset measure strictly decreases per expansion under beta-duplication | M | M | Define the measure tree-structurally (total remaining expansions = sum over branches of per-branch remaining-subformula-complexity, accepting it bounds by tree size, not linearly). The measure only needs `measure=0 ⟹ all saturated` and strict decrease; its *value* feeds the bound choice in Phase 3. |
| Restating the general lemma breaks its other call site | L | L | Only caller is `classicalTableau_hintikka` (grep-confirmed); update it in the same phase. |
| Raising fuel bound breaks `classicalTableau_sound` | L | L | Soundness is proven for *all* fuel (Soundness.lean:530-622 is fuel-parametric); a larger constant only changes the literal. Re-run `lake build` on Soundness after any change. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 (or 3' contingency) | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are strictly sequential (each builds the next proof layer); no parallelism.

---

### Phase 1: Ground-truth goal and decide measure feasibility [NOT STARTED]

**Goal**: Confirm the exact goal state at the sorry, characterize the saturation semantics of
`classicalStepBranch`, and make a hard go/no-go decision on whether a measure bounded by the
*existing* linear fuel can exist. No proof writing yet (analysis phase, but bounded and
decision-producing — not analysis-for-its-own-sake).

**Tasks**:
- [ ] `lean_goal` at Completeness.lean:492 to confirm the goal equals the stated lemma body.
- [ ] `lean_hover_info` on `classicalStepBranch` (Expansion.lean:87) and confirm:
      `classicalStepBranch b e = none ⟺ b has no unexpanded applicable formula` (saturation).
- [ ] Write down the candidate measure
      `remMeasure b e := (b.filter (fun sf => ¬ e.contains sf ∧ classicalApplyOne sf ≠ .notApplicable)).foldl (·+ sf.formula.complexity) 0`
      and the list-level `totalMeasure branches expandedSets := Σ remMeasure`.
- [ ] Use `lean_multi_attempt` / scratch reasoning to check the two properties:
      (P1) `totalMeasure = 0 ⟹ every non-closed branch is saturated`;
      (P2) one expansion step strictly decreases `totalMeasure`. Note that beta-duplication
      makes `totalMeasure` *increase* on branching — record whether a per-branch (max, not sum)
      or tree-structural measure is needed instead.
- [ ] **GO/NO-GO**: Determine whether `totalMeasure [[F(φ)]] [[]] ≤ 4*(φ.complexity+1)+1`
      can possibly hold for all φ. Expectation (from planning analysis): NO for branching φ,
      because total expansions are exponential. Record the decision:
      - **GO-linear**: proceed Phase 3 with existing bound.
      - **GO-raise**: proceed Phase 3' (raise bound). This is the expected branch.

**Timing**: 45 min

**Depends on**: none

**Files to modify**: none (produces a decision recorded in the orchestrator handoff / phase notes)

**Verification**:
- Goal state captured; saturation characterization confirmed; explicit GO decision recorded.

---

### Phase 2: Saturation-characterization helper lemma [NOT STARTED]

**Goal**: Prove that when `classicalExpandBranches` returns `.openBranch b` via the
`fuel ≥ 1` path (i.e. through `classicalStepBranch b e = none`), the branch `b` is saturated.
This isolates the "good" exit and is reusable regardless of which Phase-3 variant is taken.

**Tasks**:
- [ ] Add `private lemma classicalStepBranch_none_saturated (b e) :`
      `classicalStepBranch b e = none → ∀ sf ∈ b, (sf ∈ e) ∨ classicalApplyOne sf = .notApplicable`.
      Proof: `simp only [classicalStepBranch]`; use `List.findSome?_eq_none_iff`; for each
      `sf ∈ b`, the `findSome?` body returned `none`, so either `expanded.any (·==sf)` (⇒ `sf ∈ e`)
      or the `match classicalApplyOne sf` produced `.notApplicable`. Mirror the case analysis in
      `classicalStepBranch_mem_preserved` (Completeness.lean:508-536).
- [ ] Add `private lemma saturated_hintikka_cond (b e) :`
      from `(∀ sf ∈ e, <Hintikka rule output in b>)` and
      `(∀ sf ∈ b, sf ∈ e ∨ classicalApplyOne sf = .notApplicable)`, derive
      `∀ sf ∈ b, <classicalHintikkaSet rule clause for sf>`. This converts "expanded-set
      invariant + saturation" into the full per-formula Hintikka condition. Case split on
      whether `sf ∈ e` (use the invariant) or `notApplicable` (the `.notApplicable` arm is
      `True`).

**Timing**: 60 min

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - add two private lemmas
  immediately before `classicalExpandBranches_hintikka` (line ~478).

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` green with the two new
  lemmas sorry-free (the existing sorry at 492 still present, now shifted by added lines).

---

### Phase 3: Fuel-sufficiency lemma + restate the target lemma [NOT STARTED]

(Execute **either** 3 **or** 3' per Phase 1's GO decision. 3' is the expected branch.)

**Goal**: Define the measure, prove it strictly decreases per expansion and that
`measure = 0 ⟹ all non-closed branches saturated`, then restate
`classicalExpandBranches_hintikka` to carry the hypothesis `totalMeasure branches expandedSets ≤ fuel`
and prove it by fuel induction (reusing the companion-lemma skeleton).

**Tasks (Phase 3, GO-linear)**:
- [ ] Add `def classicalRemMeasure` and `classicalTotalMeasure` as in Phase 1.
- [ ] Prove `classicalTotalMeasure_zero_saturated`: `totalMeasure branches expandedSets = 0 →`
      `∀ b ∈ branches, isClassicallyClosed b = false → classicalStepBranch b (its e) = none`.
- [ ] Prove `classicalStep_decreases_measure`: one `processNext` expansion strictly decreases
      `totalMeasure` of the recursed argument list. **If beta-duplication defeats this (Phase 1
      P2 = fail), switch to 3'.**
- [ ] Restate `classicalExpandBranches_hintikka` adding `(hfuel : classicalTotalMeasure branches expandedSets ≤ fuel)`.
- [ ] Prove by `induction fuel`, mirroring `classicalExpandBranches_openBranch_initial_mem`
      (Completeness.lean:548-638): `zero` case — `hfuel` gives `totalMeasure = 0` ⇒ all
      saturated ⇒ the `findSome?` open branch is saturated ⇒ Hintikka via Phase-2 lemmas;
      `succ` case — `processNext` inner induction; saturated-exit ⇒ Hintikka via Phase 2;
      expansion-exit ⇒ measure strictly drops, so `hfuel` is preserved for `fuel'`, apply IH.

**Tasks (Phase 3', GO-raise — expected)**:
- [ ] In `Expansion.lean:158`, replace `let fuel := 4 * (φ.complexity + 1) + 1` with a
      provably-sufficient bound. Candidate: `let fuel := 2 * (φ.complexity + 1) * 2 ^ (2 * (φ.complexity + 1))`
      (depth ≤ `2*(complexity+1)` distinct signed subformulas; ≤ `2^depth` branches;
      ≤ depth expansions/branch). Keep it a named `def classicalTableauFuel (φ)` for reuse.
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness` to confirm the
      fuel-generic soundness proof still compiles with the new bound (only a literal changed).
- [ ] Define the measure and prove decrease + zero-saturation as in Phase 3 (the measure value
      is now ≤ the exponential bound, making the call-site discharge in Phase 5 feasible).
- [ ] Restate and prove `classicalExpandBranches_hintikka` with `hfuel` exactly as in Phase 3.

**Timing**: 90 min (3) / 120 min (3')

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - measure defs, sufficiency
  lemmas, restated target lemma proof.
- (3' only) `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean` - fuel bound.

**Verification**:
- `lake build` of Completeness + Soundness green; `classicalExpandBranches_hintikka` sorry-free
  (its body now proved under `hfuel`). The only remaining gap is discharging `hfuel` at the call
  site (Phase 5).

---

### Phase 4: Hintikka succ-case wiring and invariant bookkeeping [NOT STARTED]

**Goal**: Complete any remaining proof obligations inside the `succ` case of the restated lemma
that were deferred in Phase 3 — specifically the maintenance of the expanded-set Hintikka
invariant across an expansion step (new branches `done ++ newBs ++ restBs` with updated
`doneExp`), reusing `classicalStepBranch_mem_preserved` for membership and the Phase-2 lemmas.

**Tasks**:
- [ ] Prove the invariant is preserved when a linear/persistent rule fires (rule outputs are
      appended to the branch via `extendMany`, so `sf' ∈ newForms → sf' ∈ b'`; the newly
      expanded `sf` joins `e`, and its outputs are present by construction).
- [ ] Prove the invariant is preserved when a beta rule fires (the `∃ br ∈ brs` clause is
      witnessed by the chosen child branch; cross-reference `classicalStepBranch` branching arm).
- [ ] Confirm index bookkeeping `branches[i]? / expandedSets[i]?` lines up after
      `done ++ newBs ++ restBs` (lengths preserved; reuse the `by simp [hdlength, hlength_p]`
      pattern from the companion lemma at Completeness.lean:631-632).

**Timing**: 60 min

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - finish the `succ` case.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` green;
  `classicalExpandBranches_hintikka` fully sorry-free under `hfuel`.

---

### Phase 5: Discharge the call-site hypothesis and the line-492 sorry [NOT STARTED]

**Goal**: In `classicalTableau_hintikka` (Completeness.lean:643), discharge
`hfuel : classicalTotalMeasure [[⟨.neg, φ, ()⟩]] [[]] ≤ fuel` for the actual fuel
(`classicalTableauFuel φ`), thereby eliminating the original sorry and turning
`classicalTableau_hintikka` and downstream `classicalTableau_complete` green.

**Tasks**:
- [ ] Prove `classicalTotalMeasure_initial_le_fuel`:
      `classicalTotalMeasure [[⟨.neg, φ, ()⟩]] [[]] ≤ classicalTableauFuel φ`.
      For the single initial branch this is `remMeasure [F(φ)] [] = φ.complexity ≤ bound`,
      a direct numeric inequality (`omega`/`Nat.le` after unfolding) under the raised bound.
      **If GO-linear was taken in Phase 1/3 and this inequality is FALSE, this is the hard
      wall — invoke the Fallback (below).**
- [ ] Update `classicalTableau_hintikka` to supply the restated lemma with the discharged
      `hfuel`, keeping the existing initial-invariant lambda (Completeness.lean:649-660,
      which already proves the `expandedSets=[[]]` invariant vacuously).
- [ ] Remove the original sorry; confirm `classicalExpandBranches_hintikka` is invoked with all
      hypotheses satisfied.
- [ ] Full `lake build` (whole project), then `lake test`,
      `lake exe checkInitImports`, `lake exe lint-style`.

**Timing**: 45 min

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - call-site discharge,
  remove sorry.

**Verification**:
- Whole-project `lake build` green, **zero sorry** in Completeness.lean (verify with
  `lean_verify Cslib.Logic.PL.classicalExpandBranches_hintikka` and a `grep -n sorry`).
- `lake test` passes; `classicalTableau_complete` and `classicalTableau_decides` still build.

## Testing & Validation

- [ ] `grep -n "sorry" Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` returns nothing.
- [ ] `lake build` (full project) exits 0.
- [ ] `lake test` exits 0.
- [ ] `lean_verify` on `classicalExpandBranches_hintikka`, `classicalTableau_hintikka`,
      `classicalTableau_complete`, `classicalTableau_sound` reports no `sorryAx` / no extra axioms.
- [ ] `lake exe checkInitImports` and `lake exe lint-style` pass.

## Artifacts & Outputs

- Updated `Completeness.lean`: measure defs, saturation + sufficiency lemmas, restated and
  fully-proved `classicalExpandBranches_hintikka`, discharged call site, sorry removed.
- (Likely) Updated `Expansion.lean`: `classicalTableauFuel` raised to a provably-sufficient bound.
- Orchestrator handoff with final `sorry_inventory.count = 0` for this lemma.

## Rollback/Contingency

**Fallback (genuine intractability)**: If Phase 3/3' cannot produce a measure that both strictly
decreases per expansion AND is bounded by a fuel value the call site can satisfy — or if the
exponential-bound sufficiency proof exceeds budget — do NOT introduce a vacuous definition or a
`True`-stub (prohibited). Instead:
1. Mark the active phase **[BLOCKED]** in this plan.
2. Record in the handoff: the precise obstruction (global-fuel + beta-duplication ⇒ no additive
   linear measure; concrete counterexample to the unconditional lemma at fuel=0), the validated
   assets produced (Phase 2 saturation lemmas, restated lemma proof under `hfuel`), and the exact
   inequality that failed.
3. Recommend a spawn task: **refactor `classicalExpandBranches` to well-founded recursion** on a
   tree-structural measure (eliminating the `fuel` parameter and the degenerate `fuel = 0` exit
   entirely), which makes `.openBranch b ⟹ b saturated` hold unconditionally and renders this
   lemma trivial. This is the structurally correct long-term fix; the Phase-2 lemmas transfer
   directly.

**Git rollback**: each phase is a separate commit; `git revert` the phase commit to restore the
prior green-with-one-sorry state (the parent task 363 baseline). Never leave the file in a
non-building state across a phase boundary.
