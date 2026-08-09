# Blocker Analysis: Task #300

**Parent Task**: #300 - Extend modal K tableau with frame-specific rules for T, S4, S5, B, 5 (full modal cube)
**Generated**: 2026-07-14
**Blocker**: Phase 2 (T system) cannot deliver `Decidable (tValid φ)` because the existing K
tableau driver (`Saturation.lean`/`FmpMeasure.lean`/`CompletenessLoop.lean`, 8,066 lines,
91 call sites) hard-codes `modalApplyOne` and is not parametrized over the rule-application
function; a genuine terminating T-specific driver plus a from-scratch termination re-derivation
is required, and the same root cause recurs identically for every later system (S5, B, S4, 5).

## Root Cause

Task 300's plan (`specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md`)
completed Phase 1 (shared `frameValid`/`branchSatisfiableIn` scaffolding) and the rule-level
portion of Phase 2 (T system) cleanly and green: `FrameRules.lean` (`modalTBoxSelf`,
`modalTDiaNegSelf`, `modalApplyOneT`, and the agreement lemma
`modalApplyOneT_eq_of_not_boxPos_diaNeg`), plus rule-level T soundness in `FrameSoundness.lean`
and the free-`Std.Refl` extractor `extractModelT` in `FrameCompleteness.lean`. All committed,
zero-sorry.

Phase 2 then hit a hard architectural wall documented in the plan's Phase 2 BLOCKER section and
`handoffs/phase2-blocked-handoff.md`: `Decidable (tValid φ)` is not just a conditional truth
lemma — it requires an actual *terminating decision procedure* that *produces* a branch
satisfying the T-Hintikka property. Investigation of `Saturation.lean` (`modalStepBranch`),
`FmpMeasure.lean` (the 2,959-line FMP/termination measure `ModalPotentialInv` etc.), and
`CompletenessLoop.lean` (fuel-driven top-level loop) confirmed these three files call
`modalApplyOne` directly at 91 sites with no abstraction layer. A T-specific driver
(`modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT`) built on the already-proved
`modalApplyOneT` would need its own from-scratch termination/fuel-sufficiency argument, because
the T self-propagation rule can introduce `T(ψ)@w` not previously processed at `w`; if `ψ` is
diamond-shaped, the ordinary K diamond-positive rule (reached via `modalApplyOneT`'s fall-through)
can still mint a new witness world in response. A bounded post-processing T-closure over K's
finished output was considered and rejected as unsound for exactly this reason.

Critically, this is a **generic** problem, not one specific to T: the plan's own Phase 3 (S5),
Phase 4 (B), Phase 5–6 (S4), and Phase 7 (5) all sit on top of the same driver and would each
independently rediscover the identical blocker if attempted as sub-phases of one task. The
implementer's explicit recommendation (handoff, plan BLOCKER section) is to split the driver
work out as dedicated task(s) rather than inline "Phase N" work.

However, closer reading of `modalApplyOne` (`Rules.lean`) and the FMP measure's structure shows
the *kind* of new-world creation triggered by T/S5/B rules is not actually novel: worlds are
still minted **only** by the unmodified `diamondPos`/`boxNeg` arms of `modalApplyOne` itself
(reached identically whether the triggering box/diamond-negative formula arrived via a plain K
rule or via a T/S5/B self-/universal-/backward-propagation arm). T, S5, and B are all
"persistent-only" extensions per the plan's own difficulty gradient (§ Research Integration):
they add formulas only at *existing* worlds, drawn from the same finite `modalUniverse φ0`
catalog the K termination measure already bounds. This means the K termination argument's
*shape* — a finite catalog of `(SignedFormula, WorldIndex)` pairs with a monotone-decreasing
fuel measure — should generalize to any rule extension satisfying "no new-world creation outside
the K diamondPos/boxNeg dispatch, and all added formulas are already members of the finite
formula catalog." S4 is the one system that provably breaks this: the plan already documents
that K's depth-based `modalWorldBound` fails under transitive box propagation, requiring genuine
loop-checking / subset-blocking with a new `#worlds ≤ 2^|Sf|` bound — a structurally different
termination argument, not an instance of the K-style catalog bound.

This suggests the decomposition should isolate ONE foundational generalization of the driver +
termination argument (parametrized over an abstract rule-application function satisfying a small
set of structural hypotheses extracted from what T's instantiation needs), reused by T, S5, and
B, with S4 kept as its own dedicated high-risk task building genuinely new loop-checking
machinery (as the plan itself already flags).

## Proposed New Tasks

### New Task 1: Generalize the K tableau driver and complete T-system decidability
- **Effort**: 10-14 hours
- **Task Type**: cslib
- **Rationale**: This is the direct unblock for Phase 2 and the structural prerequisite for every
  later system. Parametrizing `Saturation.lean`'s `modalStepBranch`/`modalExpandBranches`/
  `modalTableau` and `FmpMeasure.lean`'s termination measure over an abstract rule-application
  function (matching `modalApplyOne`'s signature) — together with a small set of explicit
  structural hypotheses (no world creation outside the unmodified K `diamondPos`/`boxNeg` arms;
  all added formulas drawn from `modalUniverse φ0`) — lets K itself be re-derived as the trivial
  instantiation (must stay green, zero regression) and lets T be delivered as the first
  non-trivial instantiation via `modalApplyOneT` (already proved in `FrameRules.lean`). The
  hypotheses interface can only be correctly designed against a real client, so bundling the
  generalization with T's instantiation (rather than speculatively designing it in isolation) is
  the minimal-risk path. Completes Phase 2: rebuilds `modalStepBranchT`/`modalExpandBranchesT`/
  `modalTableauT`, discharges the T structural hypotheses, closes the T truth-lemma box-positive
  case (reflexive self-edge, reusing `modalApplyOneT_eq_of_not_boxPos_diaNeg` to reduce other
  cases to existing K bridge lemmas per the handoff's suggested path), and states
  `tValid`'s completeness + `Decidable (tValid φ)`.
- **Depends on**: None (builds on the already-committed, green Phase 1/2 rule-level work in
  `FrameRules.lean`/`FrameSoundness.lean`/`FrameCompleteness.lean`).

### New Task 2: S5 (and KB5/5-route Euclidean) decidability via the generic driver
- **Effort**: 5-7 hours
- **Task Type**: cslib
- **Rationale**: Delivers plan Phase 3 (S5 universal-cluster simplification, no loop-checking
  needed — moderate risk) plus Phase 7 (5/Euclidean coverage via the KB5/S5 equivalence route,
  since every equivalence relation is Euclidean and Phase 7 explicitly reuses Phase 3's
  machinery with no new architecture). Implements the "propagate box to ALL branch worlds"
  universal rule in `S5Simplification.lean`, extracts the countermodel via `Relation.EqvGen`
  (`Std.Refl`+`IsTrans`+`IsSymm`/`IsEquiv` free), discharges the Task-1 driver's structural
  hypotheses for the S5 rule (world creation still confined to the unmodified K diamondPos/boxNeg
  arms — each diamond mints at most once per formula, matching the difficulty gradient's
  "K-bounded" note), proves the truth lemma over the universal relation, states
  `s5Valid`/`Decidable (s5Valid φ)` against `Cube.S5`, and exposes the Euclidean frame condition
  (`Relation.RightEuclidean`) plus `5`/KB5 validity via `Satisfies.five` and
  `Cslib/Foundations/Relation/Euclidean.lean`'s API, documenting in-file that genuine pure-K5
  (Euclidean without full equivalence, no Mathlib closure operator) remains out of scope.
- **Depends on**: New Task 1, because the generic driver's structural-hypothesis interface
  (what a frame-rule extension must prove about itself to reuse the K-style termination measure)
  is only fixed once Task 1 designs and validates it against T; S5's instantiation must discharge
  that exact interface, not a hypothetical one.

### New Task 3: B (symmetric) decidability via the generic driver
- **Effort**: 5-7 hours
- **Task Type**: cslib
- **Rationale**: Delivers plan Phase 4 (B system, moderate risk). Adds the symmetric box rule
  to `FrameRules.lean` — box-positives propagate *backward* along recorded edges
  (`T(□φ)@w` + edge `v→w` ⊢ `T(φ)@v`), dually for `F(◇)` — with the backward-propagation
  saturation conjunct; extracts the countermodel via `Relation.SymmGen` (`Std.Symm` free);
  discharges the Task-1 driver's structural hypotheses for the B rule (backward propagation adds
  formulas only at existing worlds, so the K world bound and formula catalog survive unchanged);
  proves the B truth-lemma bridge over the symmetric closure; states `bValid`/
  `Decidable (bValid φ)` against `Cube.B`/`Satisfies.b`.
- **Depends on**: New Task 1, for the same reason as Task 2 — the structural-hypothesis interface
  is fixed by Task 1's T instantiation and Task 3 must discharge that exact interface.

### New Task 4: S4 rules, loop-checking machinery, termination bound, and decidability
- **Effort**: 8-12 hours (high risk; explicit [BLOCKED] fallback permitted)
- **Task Type**: cslib
- **Rationale**: Delivers plan Phases 5+6 combined (S4 is the acknowledged crux: K's depth-based
  `modalWorldBound` provably breaks under transitive box propagation, so genuine loop-checking /
  subset-blocking with a new `#worlds ≤ 2^|modalSubfmls φ0|` bound must be built from scratch,
  rivaling the 2,959-line K FMP measure in scope). This is deliberately **not** an instantiation
  of Task 1's generic driver — S4's termination argument is structurally different (a loop-check
  invariant, not the K-style finite-catalog counting measure) — so it is kept as its own
  standalone high-risk task rather than forced through the Task-1 interface. It does, however,
  reuse the Phase-2 T-rule (from Task 1) for its reflexive component and the same file/module
  layout Task 1 establishes. Builds the 4-rule (`FrameRules.lean`), the equality-of-formula-set
  blocking machinery (`LoopChecking.lean`: `formulasAtWorld`, the equality test over
  `modalSubfmls φ0`, the diamond-rule minting guard), `extractModelS4` via
  `Relation.ReflTransGen`, the box-positive truth-lemma bridge by induction on the
  `ReflTransGen` path, and (if the termination bound closes) `Decidable (s4Valid φ)` against
  `Cube.S4`/`Satisfies.four`. Per the existing plan's own risk table, this task should carry an
  explicit permission to land at [BLOCKED] (S4 rules/soundness/truth-lemma green, termination
  bound open) rather than force a `sorry`/`axiom`, with a documented recommendation for a further
  dedicated `s4-loop-checking-termination` task if the `2^|Sf|` invariant does not close in one
  run — this task itself should NOT be split further pre-emptively.
- **Depends on**: New Task 1, because it reuses the T self-propagation rule
  (`modalTBoxSelf`/`modalApplyOneT`, delivered by Task 1) for its reflexive component and the
  driver/module conventions Task 1 establishes (e.g., how a frame-specific
  `modalStepBranch*`/`modalTableau*` variant is structured, even though S4's own variant needs a
  different termination proof).

**Note on pure-K5 (genuine Euclidean-without-equivalence)**: the plan already treats this as an
explicit non-goal (no Mathlib closure operator exists for it). No task is proposed for it here;
if it is later required, a fifth task (`pure-k5-euclidean-closure`, building a custom `EuclGen`
inductive closure operator) should be spawned in a subsequent round once the shape of Task 4's
S4 loop-checking machinery is known (a custom Euclidean closure will likely need similar
loop-checking-style techniques, so sequencing it after Task 4 lands is preferable to guessing now).

## Dependency Reasoning

- **Task 2 (S5) depends on Task 1 (driver generalization + T)**: Task 1 fixes the exact set of
  structural hypotheses (about world-creation behavior and formula-catalog membership) that any
  frame-rule extension must discharge to reuse the generic K-style termination measure. Task 2's
  S5 universal rule must be proved to satisfy that precise interface — the interface's exact
  lemma statements and shape are an implementation detail only settled by Task 1's build, not
  something Task 2 can derive independently.
- **Task 3 (B) depends on Task 1 (driver generalization + T)**: identical reasoning to Task 2 —
  the B backward-propagation rule must discharge the same Task-1-fixed structural hypotheses
  interface to reuse the generic termination argument.
- **Task 4 (S4) depends on Task 1 (driver generalization + T)**: S4's 4-rule reuses the T-rule
  (`modalApplyOneT`) delivered by Task 1 for its reflexive component (S4 = reflexive +
  transitive), and its file/module structure follows the frame-specific driver-variant pattern
  Task 1 establishes (`modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT` as the template
  for an analogous S4-specific driver, even though S4's termination proof itself is new).
- **Task 2 (S5) and Task 3 (B) are independent**: they touch disjoint frame-rule shapes
  (universal-cluster propagation vs. backward symmetric propagation), disjoint closure operators
  (`Relation.EqvGen` vs. `Relation.SymmGen`), and disjoint new files
  (`S5Simplification.lean` vs. the B arm of `FrameRules.lean`). Neither's implementation choices
  affect how the other should be built; both independently instantiate the interface Task 1
  fixes. They can be implemented in either order or in parallel (with H7 territory contracts if
  concurrent, since both may touch `FrameSoundness.lean`/`FrameCompleteness.lean`).
- **Task 4 (S4) and Tasks 2/3 (S5, B) are independent of each other**: S4's loop-checking
  termination machinery is a structurally distinct argument from the Task-1 generic driver that
  Tasks 2/3 instantiate; nothing S5 or B decide affects how S4's blocking machinery must be
  built, and vice versa. Task 4 depends only on Task 1 (for the reflexive T-rule reuse and driver
  conventions), not on Tasks 2 or 3.

## After Completion

Once all spawned tasks are complete, resume the parent task #300 with `/implement 300` — or, more
likely given the scale, consider the parent task's remaining scope fully absorbed by Tasks 1-4
and close #300 as [EXPANDED] once they are all created, since the umbrella task's Phases 2-7 map
directly onto them.

The blocker will be resolved because: Task 1 supplies the one missing piece — a terminating,
sound decision procedure architecture — that every other frame system needs, and delivers it
concretely for T (closing Phase 2). Tasks 2 and 3 then reuse that architecture directly rather
than re-deriving K-scale termination machinery from scratch, and Task 4 isolates the one system
(S4) whose termination argument is genuinely different, with an explicit sanctioned [BLOCKED]
exit if the `2^|Sf|` bound proves too large for one task-scale run.
