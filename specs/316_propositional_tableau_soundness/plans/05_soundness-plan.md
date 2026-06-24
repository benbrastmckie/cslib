# Implementation Plan: Task #316

- **Task**: 316 - Propositional Tableau Soundness
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: None (all upstream infrastructure is proved)
- **Research Inputs**: specs/316_propositional_tableau_soundness/reports/04_b4-hard-research.md
- **Artifacts**: plans/05_soundness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Fill the 10 remaining `sorry` instances in `Intuitionistic/Soundness.lean` to make the
intuitionistic and minimal tableau soundness proofs complete. The sorries span four lemmas:
`applyAllTImpRules_sat` (persistence preservation), `isAccessible_go_reach_nw_implies_reach_parent`
(DFS fuel arithmetic), `monotoneEdges_update` (edge monotonicity under `Function.update`), and
`intExpandBranches_closed_unsat` (the main expansion loop invariant with 6 gap sorries). Once
`intExpandBranches_closed_unsat` is sorry-free, both `intuitionisticTableau_sound` and
`minimalTableau_sound` become sorry-free automatically. Definition of done: `lake build
Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` succeeds with zero sorries.

### Research Integration

The B4 hard-research report (04_b4-hard-research.md) confirmed:
- The `worldsAbove` design is sound; only the proof needs the `MonotoneEdges` invariant.
- Branch-local monotonicity (`MonotoneEdges worldOf edges`) survives `Function.update` because
  all old labels are `< nw` and the witness `w'` satisfies `worldOf parentLabel <= w'`.
- The loop invariant should be stated so that `worldOf` is universally quantified in the
  conclusion (contrapositive approach).
- `applyAllTImpRules` only adds formulas semantically entailed by existing formulas,
  requiring `MonotoneEdges` to justify the T(imp) modus ponens step.
- No existing formalized proof of intuitionistic tableau soundness exists in Lean 4.

### Prior Plan Reference

The prior plan (03_revised-soundness-plan.md) identified the contrapositive + strong induction
strategy from BimodalLogic. However, it did not account for the `MonotoneEdges` invariant that
the B4 research revealed is mandatory. It also planned for a refactoring of `intRule_preserves_sat`
into `intRule_preserves_sat_ext`, but the current file already has the correct existential
`worldOf'` signature. The effort calibration from the prior plan (multiple dispatch cycles
without completing the main loop) informs the phase sizing here.

### Roadmap Alignment

No specific ROADMAP.md items reference tableau soundness directly. This task advances the
propositional logic foundations that underpin the decidability instances.

## Goals & Non-Goals

**Goals**:
- Prove `applyAllTImpRules_sat`: persistence step preserves branch satisfiability
- Prove the two sub-goals in `isAccessible_go_reach_nw_implies_reach_parent`: DFS fuel chaining
- Prove `monotoneEdges_update`: `Function.update worldOf nw w'` preserves `MonotoneEdges`
- Fill all 6 sorry gaps in `intExpandBranches_closed_unsat`: MonotoneEdges threading, sf extraction, freshness
- Achieve zero sorry in `intuitionisticTableau_sound` and `minimalTableau_sound`

**Non-Goals**:
- Refactoring the algorithmic code (`intExpandBranches`, `intStepBranch`, `applyAllTImpRules`)
- Adding `Fitting1983` to `references.bib` (separate task)
- Proving completeness (separate module, not part of this task)
- Changing `intRule_preserves_sat` signature (already has the correct existential form)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `applyAllTImpRules` unfolding complexity | H | M | Use `simp only [applyAllTImpRules]` to expose filterMap structure; prove per-element using `intTImpRule` semantics |
| `intExpandBranches.go` unfolding fights with Lean | H | M | Follow classical `suffices hgo` pattern exactly; use `unfold intExpandBranches` then `set bPers` |
| MonotoneEdges threading requires signature change | H | L | The existing `intExpandBranches_closed_unsat` already universally quantifies `worldOf` in the conclusion; MonotoneEdges needs to be threaded as an additional hypothesis on each branch |
| HeartBeat timeout on complex induction | M | H | Use `set_option maxHeartbeats 3200000`; factor inner proofs into separate lemmas |
| DFS fuel arithmetic in isAccessible_go lemmas | M | M | The two sub-goals are classical fuel-chaining arguments; use `isAccessible_go_mono_fuel` (already proved) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Prove `applyAllTImpRules_sat` [NOT STARTED]

**Goal**: Fill the sorry at line 355 -- prove that applying all T(imp) persistence rules
preserves branch satisfiability when `worldOf` is monotone with respect to the edge set.

**Tasks**:
- [ ] Read the `applyAllTImpRules` definition (Expansion.lean:101-110) and `intTImpRule` (Rules.lean:173-185)
- [ ] Prove that each formula added by `intTImpRule` is semantically valid under `hsat` and `hmono`
- [ ] The key step: for each `T(psi) at w'` added, there exists `T(phi -> psi) at w` on `b` and `T(phi) at w'` on `b` with `isAccessible edges w w' = true`. From `hsat`: `IForces val botForces (worldOf w) (phi.imp psi)`, which means `forall u, worldOf w <= u -> IForces ... u phi -> IForces ... u psi`. From `hmono`: `worldOf w <= worldOf w'`. So `IForces val botForces (worldOf w') phi -> IForces val botForces (worldOf w') psi`, and we already have `IForces ... (worldOf w') phi` from `hsat`.
- [ ] Show the extended branch `b ++ newForms.flatten` preserves satisfaction: old formulas from `hsat`, new formulas from the T(imp) semantic argument above
- [ ] Verify with `lean_goal` at the sorry position and `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` -- replace sorry at line 355

**Verification**:
- `lean_goal` at the sorry site shows no remaining goals
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` compiles without sorry warning for `applyAllTImpRules_sat`
- `applyPersistenceFixpoint_sat` becomes fully proved (its induction step uses `applyAllTImpRules_sat`)

---

### Phase 2: Prove DFS helper lemmas and `monotoneEdges_update` [NOT STARTED]

**Goal**: Fill the 3 sorries in DFS fuel arithmetic (lines 502-503) and edge monotonicity
(line 528). These are prerequisites for threading `MonotoneEdges` through the main loop.

**Tasks**:
- [ ] **`isAccessible_go_reach_nw_implies_reach_parent` sub-goals (lines 502-503)**: Both sub-goals need to show `isAccessible.go edges parentLabel source edges.length = true` given that `ch` is a child of `source` in the original edges and either (a) `parentLabel` is reachable from `ch`, or (b) `ch = parentLabel`.
  - For case (a): We have `isAccessible.go edges parentLabel ch edges.length = true` (from `hreach`) and `(ch, source) in edges`. Need to chain: `source` has child `ch`, and from `ch` we can reach `parentLabel`. Use the `isAccessible.go` structure: unfold one step for `source`, find `ch` in the children, and apply `isAccessible_go_mono_fuel` to adjust fuel.
  - For case (b): `ch = parentLabel`, so `(parentLabel, source) in edges`. One step of `isAccessible.go` from `source` finds `parentLabel` as a child and returns `true` (since `parentLabel == parentLabel`).
- [ ] **`monotoneEdges_update` (line 528)**: Prove `MonotoneEdges (Function.update worldOf nw w') (edges ++ [(nw, parentLabel)])` given `MonotoneEdges worldOf edges`, `worldOf parentLabel <= w'`, and freshness of `nw`.
  - Unfold `MonotoneEdges`: for any `w1 w2`, if `isAccessible (edges ++ [(nw, parentLabel)]) w1 w2 = true`, then `Function.update worldOf nw w' w1 <= Function.update worldOf nw w' w2`.
  - Cases: (i) both `w1, w2 != nw`: reduces to `hmono` since `isAccessible` on extended edges implies reachability on old edges (by `isAccessible_go_reach_nw_implies_reach_parent`). (ii) `w2 = nw`: `isAccessible ... w1 nw = true` on extended edges means `w1` can reach `nw`, which means `w1` can reach `parentLabel` or `w1 = parentLabel`. Then `worldOf w1 <= worldOf parentLabel <= w'`. (iii) `w1 = nw`: `nw` has no children in old edges, and the only new edge is `(nw, parentLabel)`, so `nw` can only reach itself. If `w2 = nw`, reflexivity. If `w2 != nw`, unreachable from `nw`.
- [ ] Use `lean_multi_attempt` to test tactic approaches before editing
- [ ] Verify with `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` -- replace sorries at lines 502, 503, 528

**Verification**:
- `lean_verify` on `isAccessible_go_reach_nw_implies_reach_parent` and `monotoneEdges_update` shows no axioms/sorry
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` compiles

---

### Phase 3: Rewrite `intExpandBranches_closed_unsat` with MonotoneEdges threading [NOT STARTED]

**Goal**: Fill all 6 sorry gaps in `intExpandBranches_closed_unsat` (lines 630, 654, 675, 692,
704, 711). This requires threading `MonotoneEdges` as an invariant through the go-loop induction
and properly extracting `sf` from `intStepBranch` output for `intRule_preserves_sat` application.

**Tasks**:
- [ ] **Add MonotoneEdges to the lemma's conclusion**: The current signature universally quantifies `worldOf` but does not include `MonotoneEdges`. The `go` sub-lemma (`suffices hgo`) needs an additional hypothesis `MonotoneEdges worldOf edgesHead` for the branch being processed. Restructure the `suffices` to carry `MonotoneEdges`:
  ```
  suffices hgo : forall pending done ... pendingEdges ...,
      b in pending ->
      MonotoneEdges worldOf (pendingEdges corresponding to b) ->
      not intBranchSatisfied ...
  ```
  Alternatively, add `MonotoneEdges` as a hypothesis on the outer `intExpandBranches_closed_unsat` and pass it through. The initial call from `intuitionisticTableau_sound` can provide `MonotoneEdges (fun _ => w0) [] = True` trivially (empty edge list).
- [ ] **Fix the degenerate case sorry (line 630)**: This sorry handles `pendingExp = []` or `pendingNW = []` while `pending` is non-empty. The fix is to thread the length invariants into the go sub-lemma (adding `pendingExp.length = pending.length` etc. as hypotheses) so this case becomes `absurd` (impossible by the invariant).
- [ ] **Fix MonotoneEdges gaps (lines 654, 675, 704)**: Once `MonotoneEdges` is in the go-loop hypotheses, these become direct applications of the hypothesis.
- [ ] **Fix sf extraction and freshness gaps (lines 692, 711)**: When `intStepBranch bPers eHead nwHead = some (.linearResult newForms nw' newEdge, newExp)`, we need:
  - `sf in bPers` such that `intApplyRuleFull sf nwHead bPers = .linearResult newForms nw' newEdge`
  - `forall sf' in bPers, sf'.label != nwHead` (freshness)
  - Extract these from the `intStepBranch` definition: it uses `findSome?` on `bPers`, so the sf is in `bPers` and the freshness follows from the `nextWorld` invariant (all labels on the branch are `< nwHead`).
  - Apply `intRule_preserves_sat` with these witnesses to get `exists worldOf', ...` for linear case or `exists br in branches', ...` for branching case.
  - Use the `ih` (induction hypothesis at fuel `k`) to derive contradiction.
- [ ] **Thread MonotoneEdges through the recursive call**: When F(imp) fires, the new edge `(nw, parentLabel)` is added. Use `monotoneEdges_update` (Phase 2) to show `MonotoneEdges worldOf' (edges' ++ [(nw, parentLabel)])` from `MonotoneEdges worldOf edges` and `worldOf parentLabel <= w'`.
- [ ] **Add `nextWorld` freshness invariant**: Thread `forall sf in b, sf.label < nwHead` through the go-loop. The initial branch satisfies this (from `intuitionisticTableau`), and each expansion step maintains it (new labels are `< nw'` where `nw' > nwHead`).
- [ ] Consider using `set_option maxHeartbeats 3200000` if proof checking is slow
- [ ] Verify with `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`

**Timing**: 3 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` -- rewrite the `intExpandBranches_closed_unsat` proof body (lines 562-717)

**Verification**:
- `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` shows no sorry
- `lean_verify Cslib.Logic.PL.intuitionisticTableau_sound` shows no sorry
- `lean_verify Cslib.Logic.PL.minimalTableau_sound` shows no sorry (since Minimal/Soundness.lean uses `intExpandBranches_closed_unsat`)

---

### Phase 4: Build Verification and CI [NOT STARTED]

**Goal**: Verify the complete build compiles sorry-free and passes all CI checks.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` -- must succeed with no sorry warnings
- [ ] Run `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness` -- must succeed with no sorry warnings
- [ ] Run `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` -- must succeed with no sorry warnings
- [ ] Run `lean_verify` on `intuitionisticTableau_sound`, `minimalTableau_sound`, and `intExpandBranches_closed_unsat` -- confirm no axioms beyond `propext`, `Quot.sound`, `Classical.choice`
- [ ] Run `lake exe checkInitImports` -- verify all files import `Cslib.Init`
- [ ] Run `lake exe lint-style` -- verify style compliance
- [ ] Run `lake test` -- verify no test regressions

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- No new modifications expected; this is verification only
- Minor style fixes if lint-style reports issues

**Verification**:
- All CI commands pass
- `grep -rn "sorry" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` returns only comments
- `grep -rn "sorry" Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` returns only comments

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` compiles with zero sorry
- [ ] `lean_verify Cslib.Logic.PL.intuitionisticTableau_sound` shows no sorry and expected axioms only
- [ ] `lean_verify Cslib.Logic.PL.minimalTableau_sound` shows no sorry
- [ ] `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` shows no sorry
- [ ] `lake test` passes with no regressions
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes

## Artifacts & Outputs

- `specs/316_propositional_tableau_soundness/plans/05_soundness-plan.md` (this file)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (modified: all sorry removed)
- `specs/316_propositional_tableau_soundness/summaries/05_soundness-summary.md` (post-implementation)

## Rollback/Contingency

If a sorry cannot be removed:
1. Mark the specific phase as [BLOCKED] with the exact goal state that could not be closed
2. Preserve all completed sorry removals (each phase's work is independently useful)
3. The file compiles with fewer sorries than before, which is progress
4. Consider refactoring the relevant lemma statement (e.g., weakening hypotheses or adding additional helper lemmas)
5. `git stash` or `git checkout` to revert to the pre-implementation state if needed
