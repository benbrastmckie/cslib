# Blocker Analysis: Task #299

**Parent Task**: #299 - Modal K Tableau Decision Procedure (modal_k_tableau)
**Generated**: 2026-06-30
**Blocker**: Phase 6 of task 299 (the completeness loop invariant) is blocked because the current
polynomial fuel bound `modalFuel = O(n^2)` is provably insufficient for modal K, which has an
exponential minimal-model lower bound. `modalExpandBranches_hintikka` is false as stated for the
current fuel.

## Root Cause

Category: **Missing prerequisite / technical unknown** (research-level formal-verification gap).

The plan (`specs/299_modal_k_tableau/plans/05_modal-k-tableau-plan.md`, Phase 6, "DECISIVE FINDING"
addendum, lines 440-483) already pins down the exact root cause with verified evidence from the
committed source:

1. `modalComplexity` (`Cslib/Logics/Modal/Tableau/Defs.lean:63`) counts connective nodes — this is
   **polynomial** in formula size `n`. Consequently `modalFuel φ = (4n+4)(n+2)+2 = O(n^2)`
   (`Cslib/Logics/Modal/Tableau/Saturation.lean:89`) is a polynomial bound.
2. `modalNextWorld b = modalMaxWorld b + 1` (`Cslib/Logics/Modal/Tableau/Branch.lean:98`) always
   mints a strictly fresh world. The rules `diamondPos` (`Rules.lean:91`) and `boxNeg` (`Rules.lean:117`)
   create a fresh world on **every** firing — there is no world-subset blocking implemented (the
   blocking sketched in the `Saturation.lean:47-53` design comment does not exist in code).
3. Each fuel unit expands exactly one formula (one `modalStepBranch = some` step,
   `Saturation.lean:170`), so saturating a branch costs at least (#worlds created) fuel steps.
4. Modal logic K has an exponential-model lower bound: K-SAT is PSPACE-complete, and nested-box
   formulas force smallest satisfying models (hence saturated open branches) with `2^Omega(n)`
   worlds for some satisfiable formulas of size `n`.
5. Therefore, for such formulas, `#worlds = 2^Omega(n) >> O(n^2) = modalFuel φ`, so
   `modalExpandBranches` (`Saturation.lean:141-146`) hits `fuel = 0` while the branch is still open
   but **not saturated** (not a Hintikka set). `modalExpandBranches_hintikka` is therefore false as
   stated for the current fuel, and `modalTableau_decides` fails too (dually, for exponential-closure
   valid formulas the procedure would incorrectly return an open branch).

This is not a proof-technique failure (e.g., a missing lemma or wrong tactic) — it is a
**definitional obstruction**: the theorem `modalExpandBranches_hintikka` cannot be proved against
the current `modalFuel` because it is mathematically false for that fuel value on some inputs. Fixing
it requires (a) revising the fuel bound to one that is actually sufficient, and (b) formalizing the
finite-model-property (FMP) measure/termination argument that proves the revised bound suffices.

Phase 5c (`modalTruthLemma`, the completeness truth lemma) is unaffected by this obstruction — it is
already GREEN and committed sorry-free. Soundness (Phases 1-4) is also unaffected and green; note
`modalExpandBranches_closed_unsat` (`Soundness.lean:226`) is fuel-agnostic (closed implies unsat holds
for arbitrary fuel), so raising the fuel value cannot break soundness.

The plan's own contingency clause explicitly names this exact escalation: "if world-creation
interleaving cannot close in one genuine attempt... `/spawn` a follow-up" (Phase 6 Contingency, plan
line 555-557), and the blocker note independently states: "Recommend `/spawn 299` to create a
dedicated task for the modal expansion-measure + fuel-sufficiency proof."

Two resolution routes exist; only one is in scope for this new task:

- **Option A (in scope)**: Revise `modalFuel` upward to an exponential (or double-exponential) bound
  (soundness-safe, since `modalExpandBranches_closed_unsat` does not depend on the fuel value), then
  formalize the FMP termination measure that discharges the `fuel = 0` case: an a-priori world-count
  bound, a finite signed-subformula universe `U(phi)`, a subformula-closure lemma over all four modal
  rules' outputs plus the propositional rule outputs, output-disjointness, and a `3^R` per-branch
  weight to absorb the <=2-way propositional branching.
- **Option B (explicitly out of scope)**: Implement world-subset blocking in `Rules.lean`/
  `modalNextWorld` (reuse an existing world when the candidate world's formula-set is subsumed by an
  existing one), which bounds `#worlds` combinatorially instead of raising fuel. This is a
  rules/datatype-level algorithm change and is already tracked as **task 441**
  (`specs/441_modal_proposition_native_refactor`). It must not be conflated with this new task.

## Proposed New Task

### New Task 1: Modal K Tableau FMP Fuel Measure

- **Effort**: 400-800 lines across multiple dispatches (research-level formal-verification task)
- **Task Type**: cslib
- **Rationale**: This is the sole remaining blocker for task 299 Phase 6
  (`modalExpandBranches_hintikka`) and, transitively, Phase 7 (`modalTableau_complete`,
  `modalTableau_decides`, and the `Decidable` instance). No other work is needed to unblock task 299;
  the truth lemma (5c) and countermodel wrapper (5d) are already green and consume only the public
  statement, which this new task's changes do not alter.
- **Depends on**: None (new task, standalone)

**Task description** (to be written verbatim into the new task's description field):

> Fix the Phase 6 blocker in task 299 (modal K tableau completeness) by revising the fuel bound and
> formalizing the finite-model-property (FMP) termination measure. Constraints: ZERO sorry, ZERO new
> axioms; NO datatype or rule change (world-subset blocking is "option B", already tracked as task
> 441, and is explicitly OUT OF SCOPE here — do not touch `modalNextWorld`'s world-reuse behavior or
> any rule's output shape). Three-part scope:
>
> 1. Revise `modalFuel` (`Cslib/Logics/Modal/Tableau/Saturation.lean:89`) upward from the current
>    polynomial `O(n^2)` to an exponential (or double-exponential, if the measure proof requires it)
>    bound in the formula size. This step alone is soundness-safe: `modalExpandBranches_closed_unsat`
>    (`Soundness.lean:226`) is fuel-agnostic (closed implies unsat holds for arbitrary fuel), so only
>    the numeric value of `modalFuel` changes — no soundness proof needs rework.
> 2. Formalize the FMP termination measure that discharges the `fuel = 0` case of
>    `modalExpandBranches`:
>    - An a-priori world-count / world-label bound (needed because `modalNextWorld`-minted labels
>      are currently unbounded a priori).
>    - A finite signed-subformula universe `U(phi)`.
>    - A subformula-closure lemma covering all four modal rules' outputs (witness + `boxProps` +
>      `diaNegProps`) plus the propositional rule outputs, showing every formula produced during
>      expansion lies in `U(phi)`.
>    - Output-disjointness: new formulas produced by a rule firing are fresh on the branch.
>    - A per-branch weight `~3^R` (where `R` measures unconsumed universe elements) to absorb the
>      <=2-way propositional branching, mirroring the classical `3^complexity` measure used in
>      `classicalExpandBranches_hintikka`.
> 3. Prove `modalStepBranch_none_saturated` and then `modalExpandBranches_hintikka` by fuel induction
>    plus inner `Forall₂`-accessibility induction, mirroring `classicalExpandBranches_hintikka`
>    (`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:924`) and reusing the
>    acc-threading pattern already established in `modalExpandBranches_closed_unsat`
>    (`Cslib/Logics/Modal/Tableau/Soundness.lean:165`). Then discharge `modalTableau_complete` via the
>    already-proven `modalOpenBranch_countermodel` (task 299 Phase 5d, green), and finally
>    `modalTableau_decides` plus its `Decidable` instance (task 299 Phase 7, currently gated on this
>    work).
>
> Reference templates: `classicalExpandBranches_hintikka`
> (`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:924`),
> `classicalStepBranch_none_saturated` / `classicalStepBranch_hintikka_inv` (same file, lines
> 694/722), and the hoisted `forall₂_*` worklist helpers already available in
> `Cslib/Logics/Modal/Tableau/LoopInduction.lean`. Full reference-signature detail and the precise
> per-rule dispatch obligations are recorded in task 299's plan
> (`specs/299_modal_k_tableau/plans/05_modal-k-tableau-plan.md`, Phase 6 "DECISIVE FINDING" addendum
> and "Precise residual obligation" list) and should be read as background before starting.
>
> Definition of done: `modalStepBranch_none_saturated`, `modalExpandBranches_hintikka`,
> `modalTableau_complete`, `modalTableau_decides`, and a `Decidable` instance all compile with ZERO
> `sorry` and ZERO new axioms; `#print axioms` on each shows only standard axioms; whole-library
> `lake build` stays green.

## Dependency Reasoning

Only one new task is proposed, so there is no internal dependency graph among new tasks. The
external dependency is one-directional: **task 299 (Phase 6/7) depends on the new task**, because
task 299's remaining phases (the loop invariant, `modalTableau_complete`, `modalTableau_decides`) are
literally unstatable/unprovable until the new task lands a sufficient fuel bound and the FMP measure
proof that justifies it. There is no reverse dependency — the new task's scope (`Saturation.lean`
fuel constant, a new measure module, and `Completeness.lean`'s loop-invariant lemmas) does not require
anything further from task 299 beyond what is already green (5a-5d), which the new task's Definition
of done explicitly reuses without modification.

No independent-task pairs exist in this proposal since only one new task is created, per the Task
Minimization Principle: the fuel revision (item 1) and the FMP measure formalization (item 2) are
inseparable — the fuel value is meaningless without a proof that it's sufficient, and the measure
proof's bound derivation directly determines what numeric fuel value to write in item 1. Splitting
these into separate tasks would create an artificial sequencing dependency where the first task's
output (a fuel constant) cannot be validated without doing the second task's work, so they are kept
as one task rather than manufactured into two.

## After Completion

Once the new task is complete, resume task 299 with `/implement 299` (Phase 6, `modalExpandBranches_hintikka`).

The blocker will be resolved because: task 299's Phase 6 will have a fuel bound (`modalFuel`) that is
provably sufficient to guarantee `fuel = 0` is never reached with an unsaturated open branch, backed
by a formalized FMP termination measure. This directly discharges the `fuel = 0` case that is
currently unprovable, allowing `modalExpandBranches_hintikka`, `modalTableau_complete`, and (via
Phase 7) `modalTableau_decides` to be proved without introducing `sorry` or new axioms.
