# Implementation Plan: Propositional Tableau Soundness (Revised v7)

- **Task**: 316 - propositional_tableau_soundness
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: 323 (completed)
- **Research Inputs**: reports/05_intuitionistic-soundness-induction.md; reports/06_research-verification.md; reports/07_freshabove-recovery.md
- **Artifacts**: plans/08_soundness-plan-revised.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: markdown

## Overview

A full `/orchestrate` run (5 cycles) advanced this task to a **green committed baseline**:
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` builds with 0 errors and 3 live
sorries (committed at `c98ea291`, restored at `74ae5f46`), and the recovered FreshAbove
freshness-invariant machinery is committed (approx lines 766-852: `freshAbove_applyPersistenceFixpoint`,
`freshAbove_extendMany`, `freshAbove_world_create`). This revision encodes the diagnosed
**structural blocker** that defeated three implementation dispatches and re-sequences the remaining work
into small, independently-committable phases. Definition of done: all soundness sorries across the
Intuitionistic, Classical, and Minimal tableau files are closed, each file builds green, and progress
is committed at every milestone.

**Diagnosed structural blocker**: The two `hfresh` sorries (`∀ sf' ∈ bPers, sf'.label ≠ nwH`, approx
lines 1184 and 1200) cannot be closed in place because the main induction's `key` suffices (approx lines
1078-1096) does not thread a freshness invariant into the inductive context. Although the FreshAbove
lemmas exist earlier in the file, no FreshAbove term is in scope at the sorry sites (confirmed via
`lean_goal`: the hypothesis list at line 1184 contains `bPers`, `nwH`, `hresult_sf`, `hstep`, `hgo`, but
no FreshAbove term). The invariant must be threaded through `key` first (Phase 1) before the sorries can
close (Phase 2).

### Research Integration

- **reports/05_intuitionistic-soundness-induction.md**: induction structure over expansion steps; rule
  preservation obligations for the intuitionistic Kripke semantics.
- **reports/06_research-verification.md**: verification of the soundness induction approach and the
  persistence-fixpoint reasoning.
- **reports/07_freshabove-recovery.md**: recovery recipe and insertion points for the FreshAbove
  machinery (now committed); the freshness invariant that Phase 1 must thread.

## Goals & Non-Goals

- **Goals**:
  - Close all 3 remaining Intuitionistic soundness sorries (2 `hfresh` + 1 `linearResult` F(→)).
  - Close the Classical soundness sorries (`classically_closed_unsatisfiable`, `classicalTableau_sound`,
    helper).
  - Close the Minimal soundness sorry (`minimalTableau_sound`).
  - Each file builds green; progress committed at every milestone.
- **Non-Goals**:
  - No refactor of the tableau expansion machinery beyond what is required to thread the freshness
    invariant.
  - No changes to completeness proofs or unrelated tableau files.
  - No `git add -A` commits (see Risks).

## Risks & Mitigations

- **Risk**: Context overflow on the ~1400-line `Intuitionistic/Soundness.lean` (two prior agents
  overflowed working the `linearResult` case). **Mitigation**: phases are bounded to one agent run
  (~100-300 lines of change); use `lean_goal`/`lean_multi_attempt` surgically at exact sorry positions;
  do NOT re-read the whole file; split Phase 3 into sub-steps.
- **Risk**: A stray `git add -A` from a concurrent orchestration session previously committed a broken
  in-progress file to main. **Mitigation**: every commit stages ONLY the specific touched file(s); never
  `git add -A`; build green before committing.
- **Risk**: Work lost before commit (documented history on this task). **Mitigation**: commit at every
  error-free / sorry-free milestone.
- **Risk**: The `intRule_preserves_sat` 4-tuple extension cascades type errors across call sites (the
  shelved WIP attempt had 9 errors). **Mitigation**: extend the signature and prove the 4th component
  first (commit), then update call sites and assemble the `linearResult` case (commit) as separate
  sub-steps.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 4 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 5 | 3 |

Phases within the same wave can execute in parallel. Phase 4 (Classical) is independent of the
Intuitionistic chain and may run in parallel from the start.

### Phase 1: Thread freshness invariant through the `key` suffices [NOT STARTED]
- **Goal:** Make a FreshAbove term available at the `bPers` sorry sites by strengthening the main
  induction's `key` suffices with a freshness invariant.
- **Tasks:**
  - [ ] Inspect the `key` suffices statement (approx lines 1078-1096) with `lean_goal`; identify the
    `pending`/`pendingEdges`/`pendingNW` binders.
  - [ ] Add a `freshInv` component, shape approximately
    `∀ bPend edgesPend nwPend, (bPend, edgesPend) ∈ pending.zip pendingEdges → nwPend ∈ pendingNW → FreshAbove bPend edgesPend nwPend`
    (adapt exact binder shape to the actual statement).
  - [ ] Prove the invariant is established at the induction's base/seed and preserved at each inductive
    step (use `freshAbove_extendMany`, `freshAbove_world_create` as needed).
  - [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` → 0 errors (3 sorries
    still acceptable here).
  - [ ] Commit ONLY `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`.
- **Timing:** 2-3 hours
- **Depends on:** none

### Phase 2: Close both `hfresh` freshness sorries [NOT STARTED]
- **Goal:** Discharge the two identical `hfresh` sorries (approx lines 1184, 1200) using the now-in-scope
  freshness invariant.
- **Tasks:**
  - [ ] At each `hfresh` site, `intro sf' hsf'` and close `sf'.label ≠ nwH` via
    `freshAbove_applyPersistenceFixpoint` + `Nat.ne_of_lt` (adapt to the in-scope `freshInv` hypothesis
    name from Phase 1).
  - [ ] Apply the identical proof to both sites.
  - [ ] `lake build ...Intuitionistic.Soundness` → 0 errors, 1 sorry remaining (`linearResult`).
  - [ ] Commit ONLY the Soundness.lean file.
- **Timing:** 1 hour
- **Depends on:** 1

### Phase 3: Close `linearResult bp=bh` F(→) case via 4-tuple extension [NOT STARTED]
- **Goal:** Close the final Intuitionistic sorry (approx line 1189) by extending `intRule_preserves_sat`
  to expose the accessible witness world.
- **Tasks:**
  - [ ] Sub-step 3a: Extend `intRule_preserves_sat` return value from the 3-tuple
    `⟨wo', hwo'_eq, hsat'⟩` to a 4-tuple `⟨wo', hwo'_eq, hsat', hle⟩` where
    `hle : worldOf parentLabel ≤ w'` (the accessible witness world from the Kripke F(→) truth
    condition). Prove the 4th component in each rule arm. Build green; commit.
  - [ ] Sub-step 3b: Update ALL call sites of `intRule_preserves_sat` to bind the new component; thread
    the updated `worldOf'` through the inductive hypothesis for the world-creating F(→) case; assemble
    the `linearResult bp=bh` case. Build green (0 sorries in this file); commit.
  - [ ] Reference (do NOT blindly re-apply): the shelved broken attempt at
    `specs/316_propositional_tableau_soundness/recovered/intrule-4tuple-attempt-broken.lean` (had 9 build
    errors: call-site type mismatches + an `nwH` scoping problem).
  - [ ] `lake build ...Intuitionistic.Soundness` → 0 errors, 0 sorries.
  - [ ] Commit ONLY the Soundness.lean file after each sub-step reaches green.
- **Timing:** 3 hours
- **Depends on:** 2

### Phase 4: Classical tableau soundness [NOT STARTED]
- **Goal:** Close the sorries in `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`.
- **Tasks:**
  - [ ] Prove `classically_closed_unsatisfiable` (a closed branch is unsatisfiable under any Boolean
    valuation).
  - [ ] Prove the helper lemma: by induction on rule applications, each propositional rule preserves
    satisfiability under any Boolean valuation.
  - [ ] Prove `classicalTableau_sound` (closed tableau implies `Tautology φ`).
  - [ ] `lake build Cslib.Logics.Propositional.Tableau.Classical.Soundness` → 0 errors, 0 sorries.
  - [ ] Commit ONLY `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`.
- **Timing:** 2 hours
- **Depends on:** none

### Phase 5: Minimal tableau soundness [NOT STARTED]
- **Goal:** Close `minimalTableau_sound` in `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`.
- **Tasks:**
  - [ ] Adapt the completed intuitionistic soundness proof (Phase 3) with `MinimalClosure`
    (complementary atoms only, no ex falso).
  - [ ] Prove `minimalTableau_sound` (closed tableau implies `MValid φ`).
  - [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` → 0 errors, 0 sorries.
  - [ ] Commit ONLY `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`.
- **Timing:** 2 hours
- **Depends on:** 3

## Testing & Validation
- [ ] After each phase: `lake build` of the touched module shows 0 errors.
- [ ] Phase 2 onward: live sorry count in the touched file strictly decreases.
- [ ] Final: `lake build` (full project) is green with 0 sorries across all three soundness files.
- [ ] CI gate before any PR: `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`.

## Artifacts & Outputs
- plans/08_soundness-plan-revised.md (this file)
- Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean (Phases 1-3)
- Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean (Phase 4)
- Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean (Phase 5)
- summaries/NN_soundness-summary.md (on completion)

## Rollback/Contingency
- Each phase ends at a green commit; if a phase breaks the build and cannot be fixed within budget,
  `git checkout <last-green-commit> -- <touched-file>` to restore the green baseline and stop. The last
  green Intuitionistic baseline is `74ae5f46`.
- NEVER `git add -A`; stage only the specific touched file(s). Concurrent sessions share this working
  tree.
