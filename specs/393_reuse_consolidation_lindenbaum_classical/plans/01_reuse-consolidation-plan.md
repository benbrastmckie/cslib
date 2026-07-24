# Implementation Plan: Reuse-Consolidation of Lindenbaum / MCS / Conservativity Constructions

- **Task**: 393 - reuse_consolidation_lindenbaum_classical
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/393_reuse_consolidation_lindenbaum_classical/reports/01_reuse-consolidation-survey.md
- **Artifacts**: plans/01_reuse-consolidation-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib

## Overview

Consolidate the duplicated Lindenbaum / MCS / conservativity constructions across the logic
families (Propositional, Modal, Temporal, Bimodal) onto the shared
`Cslib.Foundations.Logic.Metalogic` machinery, retiring per-family copies that add no value.
The research survey partitioned the duplication into four clusters; this plan executes the two
zero-debt, actionable clusters (B: retire; C: narrow generalization), documents the deliberately
retained cluster (A), and explicitly scopes out the large high-risk cluster (D) to a follow-on
task. Definition of done: every recommended change landed, no `sorry`, no new axioms, and the
full CI pipeline (`lake build` / `lint` / `lint-style` / `test`) green, with an incremental
green commit at each completed phase.

### Research Integration

The plan is built directly on `reports/01_reuse-consolidation-survey.md`. Its per-cluster verdicts
(A keep, B retire, C partial-generalize, D defer) and 4-step zero-debt ordering are honored.
Codebase verification during planning refined two points the plan reflects:

- **Cluster B (retire) verified low-risk**: the three `LiftViaMorphism.lean` files
  (Modal/InterSystem 221 lines, Propositional/Semantics/Algebra 203 lines,
  Bimodal/ConservativeExtension 183 lines) contain **no `instance` declarations** (the apparent
  matches in the Bimodal file are prose inside docstrings), and a repo-wide grep finds **no
  external references** to their headline symbols (`modalEquiv`, `plEquiv`, `bimodalHom`,
  `toDeriv_liftDerivation`, `Derivable_mono_via_morphism`, `toDeriv_lift`). Their `Cslib.lean`
  `public import` lines are confirmed at 250 (Bimodal), 385 (Modal), 560 (Propositional); the
  only prose mention is `ConjImpConservative.lean:57`.

- **Cluster C is narrower than the report implied**: the consistency and MCS members of the tail
  triple are **already consolidated**. `GenericMCS.setConsistent_iff_congr` (GenericMCS.lean:272)
  and `GenericMCS.setMaxConsistent_iff_congr` (GenericMCS.lean:281) already exist in Foundations
  — their docstrings read "was `*_setMaxConsistent_iff_algebraic` × 4" — and all four families'
  `*_setConsistent_iff_algebraic` / `*_setMaxConsistent_iff_algebraic` are already one-line
  delegations to them. The **only** remaining per-family duplication is the `*_deriv_iff_algebraic`
  glue: a ~6-line `unfold … ; constructor; · intro ⟨d⟩ => fwd d; · intro h => ⟨bwd h⟩` scaffold
  whose two transport maps (`derivTreeToList` forward, `listDerivToTree` backward) are
  irreducibly per-family. Phase B therefore targets only that glue and carries an explicit
  decision gate: hoist a Foundations scaffold helper **only if** it yields net reduction without
  new proof debt; otherwise document the tail triple as already maximally consolidated.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided; roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Retire the three demonstration-only `LiftViaMorphism.lean` overlays and their build wiring
  (Cluster B), the highest-value / lowest-risk consolidation.
- Narrow the remaining Cluster C duplication: either hoist the `*_deriv_iff_algebraic` glue
  scaffold into a Foundations helper the four bridges consume, or — if no clean, net-reducing
  parameterization exists over the per-family `unfold` targets — document the tail triple as
  already consolidated.
- Preserve Cluster A (the per-family `*_lindenbaum` naming adapters) unchanged, with a short
  durable comment recording why they are intentionally retained so the cluster is not re-flagged.
- Keep every change zero-debt: no `sorry`, no new axioms, CI green, incremental green commits.

**Non-Goals**:
- Cluster D (the four Lindenbaum *algebra* quotient constructions, ~2,400 lines): explicitly out
  of scope. It is high-value but high-risk (four large actively-used completeness files with
  divergent algebra targets) and is recommended as its own dedicated follow-on task.
- Generalizing `set_lindenbaum` over the superset-family predicate to absorb
  `restricted_lindenbaum` (the genuine Bimodal variant): out of scope, lower priority.
- Any change to the family combinators (`liftDerivation` / `liftDerivationTree` /
  `DerivationTree.lift`) — Cluster B retirement removes only the parallel overlays, not the
  originals.
- Retiring the Cluster A wrappers or the already-delegating consistency/MCS tail members (no
  proof-debt reduction; would churn many call sites for negative readability).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A deleted `LiftViaMorphism` module was transitively consumed (hidden instance/def) | H | L | Planning greps confirm no `instance` decls and no external symbol references; Phase 2 gate is a full `lake build` after removal — revert the deletion if red |
| Removing the wrong `Cslib.lean` import line (line numbers shift after first deletion) | M | M | Remove imports by exact module-path match, not line number; re-grep `LiftViaMorphism` in `Cslib.lean` after each edit |
| Phase B Foundations helper cannot cleanly abstract per-family `unfold` targets | M | M | Decision gate: only land the helper if it net-reduces lines with zero new debt; documented fallback is to mark the tail triple already-consolidated (still a valid, zero-debt outcome) |
| Phase B change to shared `GenericMCS.lean` breaks a downstream family build | H | L | Foundations edit is additive (new helper only); build all four families in Phase B before commit; revert helper if red |
| Lint/lint-style failure on new Foundations declaration (docBlame, defLemma, naming) | M | M | New decls get docstrings, `theorem` for Prop results, lowerCamelCase; run `lint` + `lint-style` inside Phase 3 and again in Phase 4 |
| CI slowness masks an incremental regression | L | M | Run `lake build` at each phase boundary, not only at the end; commit only on green |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel. Phases 2 and 3 touch disjoint file
territories (Phase 2: the three `LiftViaMorphism` files + `Cslib.lean` + `ConjImpConservative`;
Phase 3: `GenericMCSBridge.lean` × 4 + Foundations `GenericMCS.lean`) and are parallel-capable,
but a single autonomous agent should execute them sequentially with a green commit between so
each lands independently `lake build`-verified.

### Phase 1: Baseline verification and Cluster A documentation [PARTIAL]

- **Goal:** Establish a known-green starting point and record the Cluster A no-action rationale
  as a durable comment so the retained naming adapters are not re-flagged for consolidation.
- **Tasks:**
  - [x] Run `lake build` to confirm the repository is green before any change (records the
    baseline; if already red, stop and report — do not proceed onto a red tree). *(2026-07-24:
    full `lake build` completed successfully, 3253 jobs; pre-existing unrelated warnings/sorries
    in `Cslib/Logics/Propositional/Tableau/Intuitionistic/*` are outside this task's touched
    files and outside this task's scope.)*
  - [ ] Add a short durable comment near the per-family `*_lindenbaum` wrappers (e.g. in
    `Modal/Metalogic/MCS.lean` at the `modal_lindenbaum` delegation, and/or a one-line note in
    the sibling family MCS files) stating that these are intentional naming/signature adapters
    over `Metalogic.set_lindenbaum <family>DerivationSystem`, retained deliberately (retiring
    them would inline the generic at every call site for negative readability and zero
    proof-debt reduction). Reference the durable anchor (`Foundations/Logic/Metalogic/Consistency.lean`
    `set_lindenbaum`), never a task number, per no-task-references-in-deliverables.
    *(deviation: skipped -- the delegating orchestrator's concurrency coordination note for this
    run explicitly scopes this agent's territory to "the LiftViaMorphism.lean deletions,
    GenericMCSBridge files, and Cslib.lean import lines for the deleted files" only.
    `Temporal/Metalogic/MCS.lean` in particular falls inside a concurrently-running agent's
    claimed territory ("Temporal/ProofSystem + Metalogic"), so editing any of the four family
    MCS.lean files here was withheld to avoid a same-tree edit collision. A trial edit was made
    and reverted (git diff confirmed clean) before this run's Phase 2/3 work began. This
    documentation-only subtask carries no proof-debt implication either way and can be picked up
    in a follow-on pass once the concurrent Temporal task has landed.)*
  - [ ] Note in the comment that `restricted_lindenbaum`
    (`Bimodal/Metalogic/Core/RestrictedMCS.lean`) is a genuine Zorn variant over
    closure-restricted supersets, not reducible to `set_lindenbaum`, and is out of scope here.
    *(deviation: skipped -- see prior item; no comment was added this run.)*
  - [x] `lake build` to confirm the comment-only change stays green; commit. *(deviation: altered
    -- no comment-only commit was made since no comment was added this run; baseline build
    verified green above stands in its place. No commit needed for a no-op phase.)*
- **Timing:** ~0.5 hours (build-bound)
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/MCS.lean` (and sibling MCS files as needed) — add doc comment only
- **Verification:**
  - `lake build` green; the added text is a comment/docstring (no code semantics changed).

### Phase 2: Cluster B — retire the three LiftViaMorphism overlays [NOT STARTED]

- **Goal:** Delete the three demonstration-only overlays and all their build wiring (~607 lines
  removed), the fastest, lowest-risk win.
- **Tasks:**
  - [ ] Delete the three files:
    `Cslib/Logics/Modal/Metalogic/InterSystem/LiftViaMorphism.lean`,
    `Cslib/Logics/Propositional/Semantics/Algebra/LiftViaMorphism.lean`,
    `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean`.
  - [ ] Remove the three `public import` lines in `Cslib.lean` (Bimodal ~250, Modal ~385,
    Propositional ~560) — match by exact module path, not line number, since numbers shift after
    the first removal; re-grep `LiftViaMorphism` in `Cslib.lean` to confirm zero remain.
  - [ ] Edit the prose mention at `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean:57`
    to drop `LiftViaMorphism.lean` from the parenthesized file list (keep the sentence
    grammatical).
  - [ ] Optional (only if it adds narrative value at zero cost): append a single short
    example/doc block to `Foundations/Logic/Metalogic/ProofSystemMorphism.lean` capturing the
    "family lift is an instance of the generic `Metalogic.Deriv.map`" narrative that the three
    overlays existed to demonstrate. Skip if it risks any build weight; the retirement stands
    on its own without it.
  - [ ] Run a full `lake build` to confirm no transitive instance/def was consumed (planning
    greps indicate none: no `instance` decls in the deleted files, no external references to
    their headline symbols). If red, restore the specific deletion that caused it and report.
  - [ ] Commit on green.
- **Timing:** ~1 hour (build-bound)
- **Depends on:** 1
- **Files to modify:**
  - Delete: the three `LiftViaMorphism.lean` files listed above
  - `Cslib.lean` — remove three `public import` lines
  - `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` — drop prose mention
  - (optional) `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` — single doc/example block
- **Verification:**
  - Full `lake build` green with the three modules and imports gone; `grep LiftViaMorphism Cslib.lean`
    returns nothing; no `sorry`, no new axioms.

### Phase 3: Cluster C — narrow generalization of the deriv-glue tail [NOT STARTED]

- **Goal:** Remove the last per-family duplication in the MCS bridges — the `*_deriv_iff_algebraic`
  glue scaffold — by hoisting a Foundations helper the four bridges consume, or document the tail
  triple as already consolidated if no clean net-reducing parameterization exists.
- **Tasks:**
  - [ ] Confirm the current state in each of the four `GenericMCSBridge.lean` files
    (Propositional, Modal, Temporal, Bimodal/Core): the `*_setConsistent_iff_algebraic` and
    `*_setMaxConsistent_iff_algebraic` members already delegate one-line to
    `GenericMCS.setConsistent_iff_congr` / `setMaxConsistent_iff_congr` — leave these untouched.
  - [ ] Assess whether the `*_deriv_iff_algebraic` glue (`unfold <familyDerivationSystem> Deriv;
    constructor; · intro ⟨d⟩ => <fwd> d; · intro h => ⟨<bwd> h⟩`) can be captured by a single
    additive Foundations helper in `GenericMCS.lean` parameterized over the two transport maps
    (a forward `Deriv-tree → list-deriv` and a backward `list-deriv → Deriv-tree`), so each family
    supplies only its two maps. Account for the Temporal/Bimodal `_fc` frame-class layer
    (the `*_deriv_iff_algebraic_fc` variants) — the helper must not obstruct them.
  - [ ] Decision gate:
    - **If** a clean helper net-reduces lines with zero new proof debt: add the helper to
      `Foundations/Logic/Metalogic/GenericMCS.lean` (docstring, `theorem`, lowerCamelCase,
      namespaced), then refactor the four `*_deriv_iff_algebraic` (and, where applicable, the
      `_fc` wrappers) to consume it.
    - **Else** (per-family `unfold` targets prevent a clean abstraction, or the helper does not
      net-reduce): make no code change; add a short durable comment in each bridge stating the
      tail triple is already maximally consolidated (consistency/MCS delegate to `GenericMCS.*_congr`;
      the ~6-line deriv glue is irreducibly per-family via `derivTreeToList` / `listDerivToTree`).
  - [ ] Run `lake build` across all four families, then `lint` and `lint-style` on any new/edited
    Foundations declaration.
  - [ ] Commit on green.
- **Timing:** ~1.5 hours (build-bound; two possible outcomes)
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — additive helper (hoist outcome only)
  - `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`
  - `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`
  - `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
- **Verification:**
  - `lake build` green for all four families; `lint` + `lint-style` clean on new decls; no `sorry`,
    no new axioms; if hoist taken, net line count reduced; if fallback taken, only comments added.

### Phase 4: Full CI verification and Cluster D handoff note [NOT STARTED]

- **Goal:** Confirm the complete zero-debt gate and record the explicit out-of-scope handoff for
  Cluster D.
- **Tasks:**
  - [ ] Run the full CI pipeline: `lake build`, `lint`, `lint-style`, `test`. All must pass.
  - [ ] Grep the touched files to confirm zero `sorry` and no newly introduced `axiom`.
  - [ ] Record (in the implementation summary at completion) that Cluster D — the four Lindenbaum
    *algebra* quotient constructions (`LindenbaumAlg`, `HilbertLindenbaumAlgebra`,
    `ImpLindenbaumAlgebra`, `RelLindenbaumAlgebra`, ~2,400 lines) — is deliberately deferred and
    should be spawned as its own dedicated task (a Foundations `LindenbaumTarski` generic over a
    formula type + preorder-valued derivability relation + congruence witnesses), not bundled
    here.
  - [ ] Final commit on green.
- **Timing:** ~0.5 hours (CI-bound)
- **Depends on:** 2, 3
- **Files to modify:** none (verification + summary only)
- **Verification:**
  - `lake build` / `lint` / `lint-style` / `test` all green; no `sorry`; no new axioms.

## Testing & Validation

- [ ] `lake build` green at each phase boundary and at the end.
- [ ] `lint` clean (docBlame, defLemma, naming) on any new/edited Foundations declaration.
- [ ] `lint-style` clean.
- [ ] `test` suite green.
- [ ] `grep -r "sorry"` over touched files returns no proof `sorry`; no new `axiom` declarations.
- [ ] `grep LiftViaMorphism Cslib.lean` returns nothing (Cluster B fully unwired).
- [ ] Cluster A wrappers unchanged except for the added rationale comment.

## Artifacts & Outputs

- plans/01_reuse-consolidation-plan.md (this file)
- summaries/01_reuse-consolidation-summary.md (on implementation)
- Deleted: three `LiftViaMorphism.lean` files (~607 lines removed)
- Edited: `Cslib.lean` (3 imports removed), `ConjImpConservative.lean` (prose), four
  `GenericMCSBridge.lean` files and/or `GenericMCS.lean` (Phase 3 outcome-dependent), Modal/family
  `MCS.lean` (Cluster A rationale comment)

## Rollback/Contingency

- Each phase commits only on a green `lake build`, so a regression is isolated to the in-progress
  phase and revertible by `git revert` of that phase's commit without disturbing earlier phases.
- Cluster B (Phase 2) is pure deletion + unwiring: if the post-removal `lake build` is red,
  restore the specific deleted file / import that caused it (planning greps predict green) and
  report, rather than forcing the removal.
- Cluster C (Phase 3) Foundations helper is additive; if it breaks any downstream family build,
  drop the helper and take the documented already-consolidated fallback — both outcomes are
  zero-debt.
- No destructive git on a dirty tree; snapshot via `git-snapshot.sh` before any intentional
  rollback per git-workflow.md.
