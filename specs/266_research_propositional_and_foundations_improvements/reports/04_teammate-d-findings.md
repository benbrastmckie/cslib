# Teammate D Findings: Strategic Horizons (Round 3)

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Role**: Teammate D — Horizons (Strategic Direction After the Hilbert-Primary Refactor)
- **Date**: 2026-06-23
- **Artifact**: 04 (teammate-d-findings, third research round)
- **Context**: Builds on 01 and 02 teammate-d findings and 01/02 team-research syntheses.
  This round specifically addresses what happens next after tasks 281-285 complete the
  Hilbert-primary refactor of Propositional/. Also examines how tasks 269, 278, 279, 280
  relate to 266's recommendations.

---

## Key Findings

### Finding 1: The Hilbert-Primary Refactor Is Complete — A Genuine Architectural Achievement

Tasks 281-285 have fully delivered the Hilbert-primary architecture for Propositional/:

| Task | Deliverable | Status |
|------|-------------|--------|
| 281 | Hilbert derived structural rules (andI, andE1, andE2, orI/E, impI/E, botE, dne) | COMPLETED |
| 282 | Lindenbaum algebra built over Hilbert derivations | COMPLETED |
| 283 | Algebraic completeness stated for `Derivable`/`SetDerivable` (Hilbert-primary) | COMPLETED |
| 284 | Conservative extension and Glivenko as Hilbert-primary theorems | COMPLETED |
| 285 | ND metalogical results refactored as corollaries via hilbert_iff_nd bridge | COMPLETED |

The resulting architecture in `Semantics/Algebra/HilbertCompleteness.lean` and
`HilbertConservativeGlivenko.lean` provides:
- `MPL.hilbert_alg_complete : Derivable MinPropAxiom φ ↔ GHAValid φ`
- `IPL.hilbert_alg_complete : Derivable IntPropAxiom φ ↔ HAValid φ`
- `CPL.hilbert_alg_complete : Derivable PropositionalAxiom φ ↔ BAValid φ`
- `hilbertIplConservativeOverMpl` and `hilbertGlivenko` as primary theorems
- `ipl_conservative_over_mpl` and `glivenko` as ND corollaries

This is a real architectural milestone: Hilbert is now unconditionally the spine of the proof
system, with ND as a convenient interface layer.

### Finding 2: The Primary Remaining Gap for 266 Is Phase 5 (GenericMCS Concretization)

The plan `03_propositional-foundations-plan.md` currently has Phase 1 marked [IN PROGRESS]
and Phases 2-7 as [NOT STARTED]. Given that 281-285 have resolved the Hilbert-algebraic
completeness gap independently (Phase 1 is therefore effectively done via the 281-285 tasks),
the remaining work for task 266 is:

- **Phase 2**: Fix stale documentation (ProofSystem.lean comment — the summary for task 285
  confirms this was done by task 285 already)
- **Phase 3**: Add HasDia primitive
- **Phase 4**: Decidable (Tautology phi) instance
- **Phase 5**: GenericMCS concretization for Modal logic (scope proof-of-concept)
- **Phase 6**: Extract propositional tableau rules to Foundations/
- **Phase 7**: Add propositional test coverage

Phases 1 and 2 of the plan are now completed by tasks 283-285. The remaining phases 3-7
remain actionable and unblocked.

### Finding 3: The Modal/Temporal/Bimodal Systems Should Follow the Hilbert-Primary Pattern

The Hilbert-primary architecture is now proven for Propositional/. The question is whether
Modal, Temporal, and Bimodal should adopt the same pattern. The answer is: yes, and the
infrastructure to do so already exists but is unhitched.

**Current gap**: Modal, Temporal, and Bimodal tag types (`Modal.HilbertK`,
`Temporal.HilbertBX`, `Bimodal.HilbertTM`, etc.) have no `InferenceSystem` or
`MinimalHilbert` instances registered. The `GenericMCS.lean` module provides free deduction
theorem and MCS properties for any `[MinimalHilbert S]`, but no modal/temporal/bimodal logic
can use it because no instances exist.

**What is needed for each downstream logic**:
1. `InferenceSystem (Modal.HilbertK) (Modal.Formula Atom)` — register the derivation system
2. `ModusPonens (Modal.HilbertK)` — provide the modus ponens rule
3. `HasAxiomImplyK/ImplyS/AxiomK/AxiomT/... (Modal.HilbertK)` — register all axioms
4. `ModalHilbert (Modal.HilbertK)` — the bundled instance

Following the 120-line propositional template in `Instances.lean`, each modal system is
approximately 100-150 lines. This is the lowest-effort highest-leverage move available.

**Once modal instances exist**:
- `algebraic_mcs_*` wrappers become usable, eliminating ~200-300 lines of custom MCS code
  per logic in `Modal/Metalogic/MCS.lean`, `Temporal/Metalogic/MCS.lean`, etc.
- The `GenericMCS.lean` `algebraicDerivationSystem` path becomes the canonical route for
  all modal completeness proofs
- `HasDeductionTheorem` automatically provides the deduction theorem for modal logics via
  the generic proof

**Strategic priority**: Before attempting abstract completeness infrastructure extraction
(ROADMAP remaining item 4), the modal tag instances must be provided. They are the unlock.

### Finding 4: The Path to Mathlib (Task 226) Is Now Cleaner — But Requires Careful Scoping

Task 226 (`propositional_semantics_upstream_pr`) targets upstreaming to Mathlib. The research
report `02_three-way-comparison.md` identifies the key structural divergence: CSLib uses a
primitive `.bot` constructor in `Proposition`, while both Thomas Waring's and Matthew Doty's
competing implementations use `atom ⊥` via `[Bot Atom]`.

**The Hilbert-primary refactor has no direct impact on the upstream PR difficulty** — that
divergence is at the `Proposition` type level, predating any proof system architecture. The
upstream PR question remains about which formula representation to use.

**However, the Hilbert-primary refactor creates new strategic value for upstream**:

1. **Argument for CSLib's approach**: The Hilbert-primary `Derivable` API avoids the
   `[DecidableEq Atom]` constraint that ND-based completeness required. This is a genuine
   API improvement that could be highlighted in the PR description.

2. **Scope clarification**: The upstream PR should scope to the `Semantics/` layer only
   (algebra, bool evaluation, semantic consequence) and NOT include the metalogic.
   The Hilbert-primary metalogic is CSLib-specific infrastructure that Mathlib would need
   time to integrate.

3. **Blocking issue**: The `02_three-way-comparison.md` notes that the primitive `.bot`
   constructor is the "most significant structural difference." To upstream, CSLib either
   needs to switch to the `[Bot Atom]` representation (breaking change) or make the case
   for primitive `.bot` as the right design. The Hilbert-primary refactor strengthens the
   case for primitive `.bot`: the `canonicalBotVal` mechanism in `HilbertCompleteness.lean`
   shows that explicit bot handling enables clean algebraic completeness proofs.

**Recommendation for task 226**: The plan should present the `AlgEvaluate` with explicit
`bot_val` parameter as a design feature (not a limitation) — it provides the GHA/HA/BA
hierarchy more cleanly than the `[Bot Atom]` approach. The Hilbert-primary completeness
corollaries are compelling evidence.

### Finding 5: Task 269 (Hilbert Search Tactic) Directly Benefits from the Hilbert-Primary Architecture

Task 269 builds a bounded DFS proof-search tactic for `InferenceSystem`. This tactic now
has a much cleaner target:
- Propositional axioms are registered as `HasAxiom*` instances (via tasks 281-285)
- The `DerivationTree` constructors (ax, assumption, modus_ponens) are the natural tactic
  targets for DFS
- The Hilbert-primary architecture means any completeness proof serves as a correctness
  oracle for the tactic

The dependency order is: 268 (normalization tags, done) -> 278 (proof simplification) -> 269
(search tactic). Task 278 depends on 266, meaning 266's recommendations directly gate the
search tactic. The specific connection: if Phase 5 of 266's plan (GenericMCS concretization)
succeeds, modal logics gain `InferenceSystem` instances, and the tactic from 269 immediately
becomes cross-logic polymorphic — it would work for modal, temporal, and bimodal systems
without modification.

**Strategic implication**: Completing 266 Phase 5 before implementing 269 is the right
sequencing. The tactic should be built after the instances exist so it can be validated across
all logic types.

### Finding 6: Task 278 (Normalization Tags) Is a Cleanup Pass That 266 Enables

Task 278 audits proofs using verbose `simp only [listImp_nil, listImp_cons, ...]` chains and
replaces them with `grind` or `simp` using the tags from task 268. This depends on 266
because:
- Phase 2 of 266 (documentation cleanup) ensures the proof patterns are accurate
- Phase 5 of 266 (GenericMCS bridge) may add new proofs that should use normalization tags
  from the start

Task 278 is a pure mechanical cleanup and does not need any specific 266 output — it can run
after 268 is done, with 266 as a soft dependency (waiting only for 266's implementation to
settle the final proof patterns before auditing).

**Relationship**: 278 depends on 266 for stability, not content. 266 should complete before
278 to avoid auditing files that will be modified again.

### Finding 7: Task 280 (Gap Analysis Metatask) and Task 279 (Sequent Calculus) Scope Has Shifted

Task 280 is a research metatask: audit proof systems, create tasks for gaps. Task 279 is the
sequent calculus implementation.

**Scope clarification after the Hilbert-primary refactor**:
- The prior round-2 team-research synthesis recommended sequent calculus as a "P4" item for
  266. It was subsequently split to task 279, with 280 as the gap analysis prerequisite.
- Given that 283-285 have now addressed the Hilbert-algebraic completeness gap, task 280's
  audit will find a much cleaner landscape: (a) Hilbert is primary and complete; (b) ND is
  a corollary layer; (c) the remaining gap is the absence of sequent calculus.

**What task 280 should focus on** given the new post-281-285 state:
1. **Hilbert**: fully served (algebraic completeness, MCS, conservative extension, Glivenko —
   all Hilbert-primary and sorry-free)
2. **Natural Deduction**: fully served (ND results are corollaries via bridge; Curry-Howard
   is the only remaining motivation for ND-specific additions — not yet in scope)
3. **Sequent Calculus**: entirely absent — this is the sole remaining proof system gap
4. **Decision Procedure**: `BoolEvaluate` provides decidability for CPL; IPL and MPL lack
   decision procedures (tableau or G4ip would provide this)

Task 280 should spawn exactly two tasks: (a) propositional LK/LJ (which is already task 279),
and (b) a G4ip decision procedure for IPL (if the community wants decidable IPL). Task 279
already covers (a), so task 280's output may be minimal.

### Finding 8: Research Opportunities Opened by the New Hilbert-Primary Infrastructure

The completed 281-285 tasks create concrete research opportunities not previously available:

**Opportunity A: Curry-Howard for Hilbert Systems**
The Hilbert calculus is computationally less natural than lambda calculus, but there are known
embeddings (Hilbert combinators S and K correspond to `λxy.x(yz)` and `λxy.x`). CSLib's
`Combinators.lean` in `Foundations/Logic/Theorems/` already has CombinatorK/S/I theorems.
A Curry-Howard correspondence for CSLib's Hilbert system would be a publishable result.

**Opportunity B: Completeness for Modal Logics via Generic Infrastructure**
Once modal tag instances exist (post-266 Phase 5), the completeness proof for any new modal
system becomes: (1) register instances, (2) provide frame conditions, (3) call generic MCS
and canonical model machinery. New modal systems (S4.3, GL provability logic, etc.) could be
added with ~500 lines instead of the current ~2000+ lines per system.

**Opportunity C: Decidable Tautology as a Verified Tactic Backend**
Phase 4 of 266 creates `instance [Fintype Atom] [DecidableEq Atom] : Decidable (Tautology φ)`.
This can serve as the correctness proof for a tautology-checking tactic. The combination of
`decide` (for concrete atoms) + `hilbert_search` tactic (for symbolic reasoning via task 269)
would give CSLib a two-tier automated reasoning system for propositional logic.

**Opportunity D: ProofSystem Triad as Community Infrastructure**
The combination of Hilbert (primary) + ND (corollary layer) + Sequent Calculus (task 279)
would create a three-proof-system verified framework unique in the Lean 4 ecosystem. The key
headline results:
- Hilbert ↔ ND ↔ LK equivalence bridges
- Cut elimination for LK (Hauptsatz)
- Algebraic, Boolean, and Kripke completeness for all three tiers

This is Mathlib-contribution-worthy infrastructure.

---

## Recommended Approach: Strategic Sequencing After Hilbert-Primary Completion

Given that the Hilbert-primary refactor is complete, the correct order for the remaining work
across tasks 266, 269, 278, 279, 280 is:

### Wave 1 (Parallel, all unblocked)
1. **266 Phases 3+4+6**: HasDia primitive, Decidable Tautology, tableau extraction
   — these are independent of each other and of everything else
2. **266 Phase 5**: GenericMCS concretization scoping for Modal logic
   — this is the strategic unlock for downstream logics
3. **266 Phase 7**: Propositional test coverage

### Wave 2 (After 266 is complete)
4. **278**: Proof simplification using normalization tags (depends on 266 for stable proof
   patterns)
5. **280**: Gap analysis metatask (will find a cleaner landscape after 266 adds instances and
   decidability)

### Wave 3 (After 280 has spawned tasks)
6. **269**: Hilbert search tactic (benefits from cross-logic instances from 266 Phase 5)
7. **279**: Propositional LK/LJ sequent calculus (the main remaining proof system gap)

### For Modal/Temporal/Bimodal (the longer-horizon strategic work)
8. Concretize `Modal.HilbertK` instances (spin-off task from 266 Phase 5 scoping)
9. Abstract completeness infrastructure in `Foundations/Logic/Metalogic/` (ROADMAP item 4)
10. Modal sequent systems (Fitting-style K, S4, S5) using LK as template

---

## Confidence Level

| Finding | Confidence |
|---------|------------|
| Tasks 281-285 fully completed the Hilbert-primary refactor | High — verified in summaries and source |
| Phase 1 and partial Phase 2 of 266 plan are done by 281-285 | High — HilbertCompleteness.lean and ProofSystem.lean docs confirmed updated |
| Modal/temporal/bimodal tags remain stubs | High — no Instances.lean found for any modal tag |
| GenericMCS is the strategic unlock for downstream logics | High — algebraicDerivationSystem confirmed in GenericMCS.lean |
| Task 226 upstream PR is not blocked by Hilbert-primary, but scoping matters | High — three-way comparison shows the issue is formula type, not proof system |
| The primitive `.bot` design is strengthened by the Hilbert-primary completeness | Medium — this is an interpretive argument for the upstream PR |
| Wave 1/2/3 sequencing is optimal | Medium — depends on resource availability |
| Curry-Howard for Hilbert systems is a viable research opportunity | Medium — known theoretically, not yet scoped in CSLib |
| Post-280 landscape will be minimal (LK is the main remaining gap) | Medium — depends on whether Curry-Howard / decidable IPL is in scope |
