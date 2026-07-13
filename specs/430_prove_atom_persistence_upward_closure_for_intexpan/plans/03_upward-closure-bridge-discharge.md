# Implementation Plan: Task #430 — Atom-Persistence / Upward-Closure Bridge Discharge

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Status**: [NOT STARTED]
- **Effort**: 3 hours (net-new work; excludes prerequisite 317 Wave A)
- **Dependencies**: Task 317 Wave A (frame plumbing, Phases 1-4) MUST land first; Task 317 Phase 9 (`intExtractValuation` monotonicity along `intAccessPreorder`) is consumed by this plan.
- **Research Inputs**:
  - reports/01_atom-persistence-upward-closure.md (seed)
  - reports/02_team-research.md (team, 4 teammates)
  - reports/03_falsification-spike.md (empirical, decisive)
- **Artifacts**: plans/03_upward-closure-bridge-discharge.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md; lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 430's original goal is to discharge the two validity-bridge `sorry`s left by task 317
(`Intuitionistic/Completeness.lean:113` and `Minimal/Completeness.lean:110`) by supplying
upward-closure of `intExtractValuation b`. Research (three rounds, culminating in an empirical
falsification spike) and a direct read of current code establish that **this task has been
substantially reshaped by task 317's plan v6** and is **not an independent unblock of 317**.

Concretely, the code as it stands (verified this session):
- The two bridge sorries sit *after* `apply tableau_complete; intro _b`, so the goal's `Preorder`
  is the ambient default `≤`-on-ℕ (`tableau_complete`, `Scheme.lean:1448`; `truthLemma`,
  `Scheme.lean:387`). Under `≤`-on-ℕ the raw valuation is **provably not upward-closed** (sibling
  worlds; falsification spike EXPERIMENT 1a). So the bridges are **unclosable at the current frame**.
- The Route-A edge preorder `intAccessPreorder` (`Scheme.lean:309`) + its lift lemma
  `intAccessPreorder_le_of_isAccessible` (`Scheme.lean:321`) **already exist** (a task 317
  preserved asset), but they are **not yet wired** into `truthLemma` / `openBranch_countermodel` /
  `tableau_complete`. That wiring is task 317 v6 **Wave A** (Phases 1-4), which has **not landed**.
- Task 317 v6's `sorry_inventory` **already lists both bridge sorries** as "closes Phase 10", and
  its Phase 9 proves `intExtractValuation` monotonicity along `intAccessPreorder`.

Therefore the definition of done for 430 is: once 317 Wave A restates the completeness frame over
`intAccessPreorder edges` and 317 Phase 9 exposes `intExtractValuation` monotonicity, package a
single generic upward-closure corollary and use it to instantiate `IValid`/`MValid` at the edge
frame, closing both bridges. If 317 Phase 10 closes them first, 430 collapses to a verify-and-close
task. This plan front-loads a hard coordination gate (Phase 1) and treats everything after it as
conditional on that gate passing.

### Research Integration

- **Seed (01)**: identified the `≤`-on-ℕ vs edge-accessibility tension and the freedom to choose
  the Preorder in `IValid`/`MValid`.
- **Team (02)**: S1 siblings kill Approach B; S2 one generic `posAtWorld_upward_closed` lemma
  discharges BOTH bridges (atoms and ⊥ are the same `b.any (T(·)@w)` shape); S3 edges are dropped
  by the result type (needs 317 Wave A threading); S4 the soundness edge/order toolkit is reusable;
  placement should be standalone corollaries, NOT new `IntMinScheme` fields.
- **Spike (03, decisive)**: raw edge-UC FAILS (phi4); Route C containment REFUTED at imp-F (phi4);
  Route A closure valuation is UC-by-construction and typechecks but its truthLemma atom-F case is
  falsified on an arbitrary saturated branch (phi6). **Net decision**: adopt the edge
  (`Relation.ReflTransGen`) order, keep the **raw** valuation, and obtain edge-atom-persistence from
  a saturation invariant on the *returned* branch — which lives in 317's B2 / Phase 10 territory.
  "Do NOT plan 430 as an independent unblock of 317."

### Prior Plan Reference

No prior 430 plan exists (this is 430's first plan). The governing prior artifact is task
**317's plan v6** (`specs/317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md`)
and its handoff, which reshaped 430: `intAccessPreorder` landed as a preserved asset; Phase 9
proves the monotonicity 430 needs; Phase 10 lists 430's two bridge sorries. Effort calibration:
the frame change is heavy and owned by 317; 430's residual (generic corollary + two bridge
instantiations) is small once the frame is in place.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (roadmap_flag not set). Task 317's handoff records the
cross-task alignment: task 375 (TFAE edges) is gated on 430 + 317 completeness going green.

## Goals & Non-Goals

**Goals**:
- Close `Intuitionistic/Completeness.lean:113` (`intuitionisticTableau_complete` bridge) sorry-free.
- Close `Minimal/Completeness.lean:110` (`minimalTableau_complete` bridge) sorry-free.
- Expose the upward-closure fact **once** as a generic standalone corollary consumed by both
  bridges (no int/min duplication), per team S2.
- No new `axiom`s; CI green.

**Non-Goals**:
- Do NOT implement the Route-A frame change (restating `truthLemma`/`openBranch_countermodel`/
  `tableau_complete` over `intAccessPreorder edges`) — that is task 317 Wave A. 430 consumes it.
- Do NOT touch the `truthLemma` T-imp sorry (`Scheme.lean:409`) — task 317 Phase 9.
- Do NOT touch the `intExpandBranches_openBranch_sat` fuel-0 sorry (`Scheme.lean:1070`) — task 317
  Phase 10.
- Do NOT prove `intExtractValuation` monotonicity from scratch — consume 317 Phase 9's lemma. The
  spike proved this monotonicity is NOT a branch-local fact for arbitrary saturated branches; it is
  entangled with 317 B2.
- Do NOT touch `*/Soundness.lean` (task 316 territory).
- Do NOT pursue Route C (containment preorder) — empirically refuted at imp-F.
- Do NOT strengthen `propagatePersistence` (rejected Approach C; re-opens soundness).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| 317 Wave A has not landed when 430 runs (frame still `≤`-on-ℕ) | H | H | Phase 1 hard gate: verify frame is restated over `intAccessPreorder edges`. If not, mark [BLOCKED], do not proceed. |
| 317 Phase 10 closes both bridges before/independently of 430 (duplicate + territory conflict) | H | M | Phase 1 ownership decision with orchestrator/317; if already closed, collapse 430 to Phase 5 verify-only. |
| Concurrent writers on `Scheme.lean` / the two `Completeness.lean` files (single-writer rule) | H | M | Place the generic corollary in a NEW file; serialize any `Scheme.lean` edit behind 317; never edit a Completeness bridge while 317 Phase 10 is live. |
| `minBranchBotForces` UC does not reduce to the same generic lemma | M | L | Team S2 verified it is `b.any (T(.bot)@w)` — identical shape; the generic `posAtWorld_upward_closed` covers it by instantiating the formula slot at `.bot`. |
| Edges not reachable at the bridge site to build the frame instance | M | M | Depends on 317 Wave A `openBranch_countermodel` restatement threading `edges`; confirm in Phase 1. |
| `Preorder Nat` `lt`-field `rfl` gotcha | L | L | Already handled in the committed `intAccessPreorder` def (explicit `lt`); reuse it, do not redefine. |
| Monotonicity lemma from 317 Phase 9 has a different signature than expected | M | M | Phase 1 records its exact statement; Phase 2 corollary is written against the actual signature. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Coordination + frame gate (decision) [NOT STARTED]

**Goal**: Confirm the prerequisites from task 317 are in place and decide ownership of the bridge
discharge before writing any proof code. This phase is a gate; it may terminate the task as
[BLOCKED].

**Tasks**:
- [ ] Verify 317 Wave A frame plumbing has landed: `truthLemma` (`Scheme.lean` ~:387),
      `openBranch_countermodel` (~:1399), and `tableau_complete` (~:1448) conclude/hypothesize over
      `@IForces Nat (intAccessPreorder edges).toLE …` rather than the default `≤`-on-ℕ. Use
      `grep -n "intAccessPreorder" Scheme.lean` and read the three signatures.
- [ ] Verify task 317 Phase 9 has exposed an `intExtractValuation` monotonicity lemma along
      `intAccessPreorder edges` (search `Scheme.lean` for a lemma of shape
      `IAccessible/ReflTransGen … → intExtractValuation b w p → intExtractValuation b w' p`). Record
      its exact name and signature.
- [ ] Check whether `Completeness.lean:113` and `Minimal/Completeness.lean:110` are still `sorry`
      (i.e., 317 Phase 10 has not already closed them). Run
      `grep -n sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` and the
      Minimal analogue.
- [ ] **Decision**:
      - If frame NOT restated over the edge preorder OR monotonicity lemma absent -> **[BLOCKED]**;
        write handoff blocker "awaiting 317 Wave A + Phase 9"; stop.
      - If bridges already closed by 317 Phase 10 -> skip Phases 2-4; go to Phase 5 (verify-only);
        task 430 is satisfied-by-317.
      - Else (frame + monotonicity present, bridges still open) -> proceed to Phase 2 owning the
        bridge discharge; coordinate with 317 so Phase 10 does not also edit these two files.
- [ ] Confirm `Cslib/Scratch430.lean` is absent (verified absent this session; re-check and remove
      if a later spike re-introduced it).

**Timing**: 30 min

**Depends on**: none

**Files to modify**: none (read-only gate).

**Verification**:
- A recorded decision (proceed / blocked / verify-only) with the exact name + signature of the
  monotonicity lemma and the current frame type of the three shared declarations.

### Phase 2: Generic upward-closure corollary [NOT STARTED]

**Goal**: Package the upward-closure fact once, order-agnostically, so both bridges consume it.

**Tasks**:
- [ ] Add a generic lemma `posAtWorld_upward_closed` (parametric over the formula slot `φ`) stating:
      given the edge-preorder monotonicity fact from 317 Phase 9,
      `b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w)` is upward-closed along
      `intAccessPreorder edges`. (Team S2: atoms and ⊥ are instances of this same shape.)
- [ ] Derive two one-line corollaries: `intExtractValuation_upward_closed` (φ := `.atom p`) and
      `minBranchBotForces_upward_closed` (φ := `.bot`).
- [ ] Placement: NEW file (e.g. `Cslib/Logics/Propositional/Tableau/Intuitionistic/UpwardClosure.lean`,
      `import Cslib.Init` + the Scheme/Soundness modules) to avoid single-writer contention on
      `Scheme.lean`. Do NOT add fields to `IntMinScheme` (team S2 placement guidance). If the lemma
      genuinely must live in `Scheme.lean` for access to private defs, serialize the edit behind any
      live 317 `Scheme.lean` phase.
- [ ] `lean_verify` the new lemma is axiom-clean and sorry-free.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/UpwardClosure.lean` (new) - generic corollary
  + two specializations. (Fallback: `Scheme.lean` if privacy requires it.)
- `Cslib.lean` barrel - only if a new file is added (`lake exe mk_all --module`).

**Verification**:
- `lake build` of the new module green; `lean_verify` reports no new axioms, no sorry.

### Phase 3: Discharge the intuitionistic bridge [NOT STARTED]

**Goal**: Close `Intuitionistic/Completeness.lean:113` sorry-free.

**Tasks**:
- [ ] At the bridge, instantiate `IValid φ` at `World = ℕ`, `Preorder := intAccessPreorder edges`
      (the branch's edge set, threaded in via 317 Wave A `openBranch_countermodel`),
      `val := intExtractValuation b`, supplying `intExtractValuation_upward_closed` for the
      upward-closure obligation of `IValid`.
- [ ] Reconcile `modelBot`: `intScheme.modelBot b = fun _ => False`; discharge `IValid`'s bottom
      obligations accordingly.
- [ ] Replace the `sorry` with the assembled term; `lean_goal` at each step to confirm closure.

**Timing**: 45 min

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - replace sorry at ~:113.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` green;
  `grep -n sorry` on the file returns nothing; `lean_verify intuitionisticTableau_complete`
  axiom-clean.

### Phase 4: Discharge the minimal bridge [NOT STARTED]

**Goal**: Close `Minimal/Completeness.lean:110` sorry-free.

**Tasks**:
- [ ] Instantiate `MValid φ` at the edge frame with `val := intExtractValuation b` and
      `botForces := minBranchBotForces b`, supplying `intExtractValuation_upward_closed` AND
      `minBranchBotForces_upward_closed` for `MValid`'s two upward-closure obligations.
- [ ] Replace the `sorry`; `lean_goal` to confirm.

**Timing**: 45 min

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - replace sorry at ~:110.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness` green;
  `grep -n sorry` returns nothing; `lean_verify minimalTableau_complete` axiom-clean.

### Phase 5: CI + verification [NOT STARTED]

**Goal**: Confirm both bridges are sorry-free with no regressions and full CI green.

**Tasks**:
- [ ] `grep -n sorry` on both Completeness files returns nothing.
- [ ] `lean_verify` on both bridge theorems: no new axioms.
- [ ] Full CI pipeline: `lake build`; `lake exe checkInitImports`; `lake exe lint-style`;
      `lake shake --add-public --keep-implied --keep-prefix`; `lake test`.
- [ ] Confirm `Scheme.lean` and `*/Soundness.lean` remain green (no regressions in 317/316
      territory).
- [ ] Confirm no stray `Cslib/Scratch430.lean` in the tree.

**Timing**: 30 min

**Depends on**: 3, 4

**Files to modify**: none (verification only; lint/shake auto-fixes if flagged).

**Verification**:
- Entire CI pipeline exits zero; both bridge sorries gone; no new axioms.

## Testing & Validation

- [ ] `grep -n sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` -> empty.
- [ ] `grep -n sorry Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` -> empty.
- [ ] `lean_verify` on `intuitionisticTableau_complete` and `minimalTableau_complete`: no new axioms.
- [ ] `lake build` full project green.
- [ ] `lake exe checkInitImports`, `lake exe lint-style`, `lake shake …`, `lake test` all green.
- [ ] `Scheme.lean` truth-lemma T-imp sorry (317 Phase 9) and fuel-0 sorry (317 Phase 10) untouched
      by 430.

## Artifacts & Outputs

- plans/03_upward-closure-bridge-discharge.md (this file)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/UpwardClosure.lean` (new; generic corollary) —
  or the corollary folded into `Scheme.lean` if privacy requires
- Edited `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean` (bridges closed)
- summaries/03_upward-closure-bridge-discharge-summary.md (on implementation)

## Rollback/Contingency

- **Frame not landed / monotonicity absent (Phase 1)**: mark task [BLOCKED] "awaiting 317 Wave A +
  Phase 9"; no code changes made; re-dispatch 430 after 317 Wave A lands.
- **Bridges already closed by 317 Phase 10**: 430 is satisfied-by-317; run Phase 5 verify-only and
  mark 430 complete (absorbed), citing the 317 commit that closed the sorries.
- **Any proof phase fails**: revert that file to HEAD; the change is confined to the bridge site (or
  the new UpwardClosure file); no shared-frame edits are made by 430, so rollback is local and does
  not disturb 317's in-flight work.
- **Territory conflict detected mid-flight**: stop, yield the file to 317's single writer,
  re-synchronize at Phase 1's decision point.
