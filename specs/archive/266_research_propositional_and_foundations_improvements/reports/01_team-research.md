# Research Report: Task #266

**Task**: Research Propositional and Foundations Improvements
**Date**: 2026-06-22
**Mode**: Team Research (4 teammates)

## Summary

The Propositional/ module (30 files) is CSLib's most complete logic module, providing three logic tiers (MPL/IPL/CPL) with two proof systems (Hilbert + ND), four semantic frameworks (Bool, Kripke, algebraic, bivalent), full strong completeness for all three logics, and an 8-theorem equivalence bridge between Hilbert and ND. Foundations/ (66 files) provides the shared typeclass infrastructure enabling polymorphic logic development across all CSLib logics.

The module has exactly one sorry (`ipl_conservative_over_mpl` requiring Dedekind-MacNeille completion) and one correctness defect (non-capture-avoiding `subs` in ND). Key gaps are: no sequent calculus, no decision procedure, incomplete `PropositionalConnectives` bundling (task 173 tombstoned), and an unresolved algebraic-to-Hilbert completeness bridge.

Strategic analysis shows improvements should prioritize (1) filling the sorry and bridging algebraic completeness to Hilbert level, (2) concretizing ProofSystem tag instances, and (3) adding a generic sequent calculus framework (using CLL as template) rather than propositional-specific proof systems. A propositional-specific tableau is not recommended — the bimodal tableau already exists and generalizing it would be more valuable.

## Key Findings

### Primary Approach (from Teammate A)

**Current Inventory**:
- **Language Layer**: `Proposition Atom` inductive (5 constructors), substitution monad, `IsIntuitionistic`/`IsClassical` typeclasses
- **Proof Systems**: Hilbert (3 axiom variants: Min/Int/Cl with `DerivationTree`) + ND (10-constructor `Theory.Derivation`)
- **Equivalence Bridge**: 8 theorems covering Min/Int/Cl x context-based/closed via `hilbert_iff_nd` family
- **Semantics**: Bivalent, Boolean (`BoolEvaluate` with decidability), Kripke (`IForces`/`IValid`/`MValid`), Algebraic (GHA/HA/BA via Lindenbaum tower)
- **Metalogic**: Full strong soundness/completeness for CPL (canonical model), algebraic completeness for all three levels, generic MCS/Lindenbaum framework

**Foundations/ Role**: Six subdirectories providing connective typeclasses, polymorphic axiom formulas, the Hilbert proof system class hierarchy (`MinimalHilbert` through `BimodalTMHilbert`), generic `DerivationSystem`/MCS/Lindenbaum framework, `InferenceSystem` notation, LTS/FLTS semantics, relation theory, syntax infrastructure, data structures, and control flow (free monads).

**Identified Gaps** (8 total):
1. `ipl_conservative_over_mpl` sorry (needs Dedekind-MacNeille completion)
2. No sequent calculus (LK/LJ)
3. No tableau system
4. No decision procedure / normal forms (CNF/DNF)
5. No Craig interpolation theorem
6. Non-capture-avoiding `subs` in ND
7. Algebraic completeness not bridged to Hilbert level
8. No Kripke completeness for IPL/MPL (only algebraic-route completeness exists)

### Alternative Approaches (from Teammate B)

**Mathlib Analysis**:
- Mathlib has NO standalone sequent calculus formalization — any CSLib sequent calculus is new work
- `Mathlib.Tactic.ITauto` implements G4ip internally but not as an exposed formal system
- `Mathlib.Order.Heyting.Basic` already used by CSLib's algebraic semantics
- Dedekind-MacNeille completion may be available via `Mathlib.Order.CompleteLattice.Completion`

**Prior Art Within CSLib**:
- CLL already has the multiset sequent pattern (`Sequent` as `Multiset`, `Proof` as `InferenceSystem`) — direct template for propositional LK
- CLL cut elimination is stubbed (TODO) — a parallel improvement target
- Bimodal Decidability has 8 propositional tableau rules (andPos/Neg, orPos/Neg, impPos/Neg, negPos/Neg) that could be extracted

**Cross-Module Patterns**:
- Propositional/ is ahead of all other logics in proof system coverage (Hilbert + ND + bridge)
- Modal, Temporal, Bimodal only have Hilbert systems — no ND
- Context representation varies: Finset (ND), List (Hilbert), Multiset (CLL) — a design decision needed for any new proof system

**Recommended Additions**: G4ip sequent calculus for IPL decidability; propositional tableau extracted from Bimodal; concrete ProofSystem instances

### Gaps and Shortcomings (from Critic)

**Critical Findings**:
1. **Zero test coverage**: No `CslibTests/` file imports any `Cslib.Logics.Propositional.*` module — the entire module is exercised only by compilation
2. **Two defects, not one**: The `subs` capture-avoidance TODO at `NaturalDeduction/Basic.lean:276` is a correctness defect, not just a missing feature
3. **`PropositionalConnectives` structurally incomplete**: `HasAnd`/`HasOr` not bundled; deferred to task 173 which has been TOMBSTONED
4. **Algebraic completeness has no Hilbert bridge**: No `Derivable MinPropAxiom φ ↔ GHAValid φ` theorem despite both halves existing separately
5. **`ProofSystem.lean` documentation is stale**: Comment says "future work" but `Instances.lean` and `IntMinInstances.lean` already register concrete instances for propositional tags
6. **BimodalLogic Report 16 is NOT about propositional logic**: It describes witness-count induction for EA-formulas on Prior temporal structures — using it as a PL tableau model would import unresolved complexity
7. **Kripke completeness for MPL is missing**: `KripkeBridge.lean` proves only one direction (algebraic → Kripke soundness)
8. **Task 265 overlap**: `track_conservative_lean_sorry` is already researching the `ipl_conservative_over_mpl` sorry

**Unvalidated Assumptions**:
- Whether the generic Foundations/ MCS machinery is actually used by downstream proofs (vs. each logic re-implementing its own)
- Whether the `subs` function is admissible in full generality despite not being capture-avoiding
- Whether adding a sequent calculus is straightforward (context representation conflicts, structural rules, cut elimination complexity)

### Strategic Horizons (from Horizons)

**Roadmap Alignment**:
- The roadmap's remaining items are discrete/continuous completeness for Bimodal and Temporal — these need abstract completeness infrastructure, not new proof systems
- Propositional improvements that align: fill sorry, concretize ProofSystem instances, extract abstract completeness
- A sequent calculus does NOT appear in the roadmap and would not unblock remaining items

**Strategic Scoping Options** (ranked):
- **Option A "Foundations First"** (RECOMMENDED): Concretize ProofSystem instances + extract abstract completeness + fill sorry — directly enables downstream tasks
- **Option B "Proof Systems Survey"**: Add LK + cut elimination — enriches Propositional/ but doesn't unblock roadmap
- **Option C "Generic Framework"**: Parameterized proof system framework — very high long-term impact but high design risk
- **Option D "Decision Procedure"**: Verified DPLL/SAT — practical value, moderate effort

**Long-term Vision**: CSLib as a "proof system functor" — given a logic (connective classes + axioms), automatically derive Hilbert, ND, sequent calculus, and tableau systems with verified bridges. Propositional/ is the natural template for this architecture.

**Key Strategic Insight**: Do NOT add a propositional-specific tableau — the bimodal tableau already exists. If tableau work is desired, generalize the bimodal tableau to `Foundations/Logic/`.

## Synthesis

### Conflicts Resolved

1. **ProofSystem instances: stubs vs. already registered** — Teammates B and D noted tag types as "unconnected stubs"; Teammate C found that `Instances.lean` and `IntMinInstances.lean` already register concrete instances for HilbertCl/Int/Min. **Resolution**: The stale comment in `ProofSystem.lean` is misleading — propositional tags DO have instances. However, modal/temporal/bimodal tags may still lack complete instances. The documentation needs updating.

2. **IPL/MPL completeness status** — Teammate A reported no Kripke completeness for IPL/MPL. Teammate D implied IntStrongCompleteness/MinStrongCompleteness exist. **Resolution**: Completeness via the algebraic route (MCS + Lindenbaum) does exist for all three logics. What's missing is direct Kripke completeness (via prime filter construction). The KripkeBridge is unidirectional (algebraic → Kripke soundness only).

3. **Priority ordering** — Teammates diverged on priorities. **Resolution**: Adopted D's strategic framing (Foundations-first) with C's insistence on test coverage and A's gap analysis specificity. Priority order: (1) foundational gaps (sorry, bridge, tests), (2) infrastructure (ProofSystem instances, abstract completeness), (3) new proof systems (sequent calculus, generic framework).

4. **Tableau recommendation** — A and B listed propositional tableau as priority 5. D strongly recommended against it. C noted the BimodalLogic reference is irrelevant to PL. **Resolution**: Adopted D's recommendation — do NOT add propositional-specific tableau. If tableau work is desired, generalize the existing bimodal tableau.

5. **Sequent calculus scope** — A proposed propositional-specific LK/LJ. B proposed G4ip for IPL. D recommended generic framework in Foundations/. **Resolution**: A generic sequent calculus framework (using CLL as template) is more strategically valuable than a propositional-specific one, but the initial implementation should target propositional as the first instantiation.

### Gaps Identified

1. **Test coverage**: Zero tests for the entire Propositional/ module — should be addressed before adding new features
2. **Task 265 coordination**: The `ipl_conservative_over_mpl` sorry is already being tracked by task 265 — any implementation here must coordinate
3. **`PropositionalConnectives` bundling**: Task 173 (tombstoned) blocks `HasAnd`/`HasOr` inclusion — this dependency is unresolved
4. **GenericMCS usage audit**: No verification of whether downstream logics actually use the generic MCS infrastructure vs. their own implementations
5. **Curry-Howard correspondence**: The ND `Derivation` is `Type`-valued (enabling term extraction) but no lambda calculus connection is formalized
6. **Compactness applications**: Proved but no downstream applications (Konig's lemma, ultraproducts)
7. **Strict inclusion proofs**: MPL ⊆ IPL ⊆ CPL stated but no separating formula witnesses with countermodels

### Recommendations

**Priority 1 — Fill Existing Gaps (High impact, mostly low effort)**:
1. **Bridge algebraic completeness to Hilbert**: Compose `alg_complete` with `hilbert_iff_nd` — estimated 30-60 lines
2. **Fill `ipl_conservative_over_mpl` sorry**: Via Dedekind-MacNeille completion — estimated 300-600 lines (coordinate with task 265)
3. **Add Propositional/ test coverage**: Create `CslibTests/Propositional.lean` exercising derivability, soundness, completeness with concrete instances
4. **Fix `subs` capture avoidance**: Use `HasFresh` infrastructure — estimated 50-150 lines
5. **Update stale documentation**: Fix `ProofSystem.lean` comment about "future work" since instances already exist

**Priority 2 — Infrastructure Improvements (High strategic value)**:
1. **Extract abstract completeness infrastructure**: Move shared MCS → canonical model → truth lemma → countermodel pattern to `Foundations/Logic/Metalogic/AbstractCompleteness.lean` — directly unblocks roadmap items for discrete/continuous completeness
2. **Audit and concretize ProofSystem tag instances**: Verify which tags beyond propositional have instances; complete missing ones for at least Modal.HilbertK and Bimodal.HilbertTM

**Priority 3 — New Proof Systems (High effort, strategic enrichment)**:
1. **Generic sequent calculus framework**: Define in `Foundations/Logic/SequentCalculus.lean` using CLL as template; instantiate for propositional LK first — estimated 400-800 lines
2. **G4ip for IPL decidability**: Contraction-free sequent calculus providing decidability as corollary — estimated 300-500 lines
3. **Propositional decision procedure**: Lift `BoolEvaluate` to a verified tautology checker — estimated 100-200 lines

**Do NOT Prioritize**:
- Propositional-specific tableau (use bimodal generalization instead)
- CNF/DNF normal forms (tangential to roadmap)
- Craig interpolation (valuable but independent concern)
- Curry-Howard correspondence (nice-to-have, not blocking)

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (inventory + gaps) | completed | high |
| B | Alternatives (prior art + patterns) | completed | high |
| C | Critic (gaps + blind spots) | completed | high |
| D | Horizons (strategic direction) | completed | high |

## References

- Dyckhoff, R. (1992). Contraction-free sequent calculi for intuitionistic logic (G4ip)
- Rasiowa, H. (1974). An Algebraic Approach to Non-Classical Logics (Dedekind-MacNeille completion)
- Gentzen, G. (1935). Investigations into logical deduction (LK/LJ sequent calculus)
- Troelstra, A.S. & van Dalen, D. (1988). Constructivism in Mathematics (IPL Kripke semantics)
- Sorensen, M.H. & Urzyczyn, P. (2006). Lectures on the Curry-Howard Isomorphism
- Fitting, M. (1983). Proof Methods for Modal and Intuitionistic Logics (modal sequent systems)
- BimodalLogic Report 16: Witness-count restructure for EA-formulas (context only — not a PL reference)
