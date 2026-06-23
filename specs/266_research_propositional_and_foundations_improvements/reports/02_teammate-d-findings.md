# Teammate D Findings: Strategic Horizons for Task 266 (Round 2)

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Role**: HORIZONS researcher (long-term alignment and strategic direction)
- **Date**: 2026-06-22
- **Agent**: formal-research-agent (Sonnet)
- **Artifact**: 02 (teammate-d-findings, second research round)
- **Context**: Builds on 01_teammate-d-findings.md; adds comparative analysis
  against BimodalLogic report 16 and fresh strategic angle

---

## Key Findings

### Finding 1: The Propositional Module Is Structurally Sorry-Free

The prior round (01_teammate-d-findings.md) identified `ipl_conservative_over_mpl` as the
last sorry in Propositional/. A re-scan of `Cslib/Logics/Propositional/` and
`Cslib/Foundations/Logic/` confirms: **zero sorry declarations currently exist in either
directory**. Either the prior findings were based on an earlier state or the sorry was
removed as part of recent work. This is good news — Propositional/ is clean.

The sorry-bearing code in the repository is exclusively in `Cslib/Logics/Bimodal/` (tasks 36
and 37 blockers: discrete completeness and continuous extension), and one sorry in
`TemporalConservativity.lean` (task 275). Propositional/ and Foundations/Logic/ are
completely sorry-free.

**Strategic implication**: The "fill the sorry" priority from round 1 is moot for
Propositional/. Strategic priorities must shift to new proof systems, infrastructure gaps, and
cross-module integration.

### Finding 2: The ProofSystem Tag Instances Gap Is Partially Closed — But Unevenly

Round 1 identified all 19 `HilbertX` tags as stubs. Inspection of
`Propositional/ProofSystem/Instances.lean` (120 lines) confirms that `Propositional.HilbertCl`
is fully instantiated with `InferenceSystem`, `ModusPonens`, and all `HasAxiom*` instances,
completing `ClassicalHilbert`. The file `IntMinInstances.lean` similarly handles
`HilbertInt` and `HilbertMin`.

However, **the 16 modal/temporal/bimodal tags remain stubs**:
- `Modal.HilbertK` through `Modal.HilbertDB` (14 tags)
- `Temporal.HilbertBX`
- `Bimodal.HilbertTM`

This asymmetry matters: Propositional/ is the lone logic where the Foundations/ typeclass
hierarchy is concretely inhabited. The benefit of having `ClassicalHilbert` as an abstract
interface is realized only when multiple formula types instantiate it, enabling polymorphic
theorems. Currently, the architecture is aspirational at the modal/temporal/bimodal level.

**Finding**: Propositional tags are done. The highest-leverage next step is providing
`InferenceSystem` + `ModalHilbert` instances for `Modal.HilbertK` using
`Modal.DerivationTree`.

### Finding 3: BimodalLogic Report 16 Is Strategically Irrelevant to Propositional/Foundations

BimodalLogic report 16 (`16_witness-count-restructure.md`) analyzes the K=0 sorry in
`PriorComposition.lean` — a temporal expressive completeness result about NF-depth vs.
witness-count induction on Prior structures. This is:

1. A **BimodalLogic-specific** problem (not yet ported to CSLib)
2. About **first-order temporal model theory**, not propositional proof systems
3. Using a **NormalForm framework** with no analog in CSLib's propositional infrastructure
4. Irrelevant to the tableau decision procedure referenced in the task description

The report's tableau description refers to the bimodal signed-formula tableau in
`Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean`, which is already ported and
sorry-free. **The tableau for propositional logic does not exist yet** and would need to be
built from scratch.

**What can be extracted from the bimodal tableau for propositional use**:
- The propositional rules (andPos/Neg, orPos/Neg, impPos/Neg, negPos/Neg) are already
  defined in `Tableau.lean` — these are exactly the 8 propositional tableau rules
- The `SignedFormula` type (`{T | F} × Formula`) pattern is directly reusable
- The `Branch`/`Saturation`/`Closure` infrastructure could be lifted to Foundations/

### Finding 4: The Sequent Calculus Gap Is The Highest-Value Missing Proof System

After reviewing the full module landscape:

| Proof System | Propositional | Modal | Temporal | Bimodal | LinearLogic |
|--------------|--------------|-------|----------|---------|-------------|
| Hilbert | Full (3 tiers) | Full | Full | Full | -- |
| Natural Deduction | Full + bridge | -- | -- | -- | -- |
| Sequent Calculus | -- | -- | -- | -- | CLL (no cut elim) |
| Tableau/Decision Proc. | -- | -- | -- | Full | -- |

The pattern is clear: **Natural Deduction and Sequent Calculus are missing from all logics
except Propositional (ND) and LinearLogic (SC)**. The CLL sequent calculus in
`Logics/LinearLogic/CLL/Basic.lean` has pending cut elimination (`CutElimination.lean` with
TODOs). A propositional LK or LJ would:

1. Complete the proof system triad (Hilbert + ND + SC) for propositional logic
2. Provide cut elimination — the foundational result proving consistency of the system
3. Serve as the template for modal sequent systems (Fitting-style systems for K, S4, S5)
4. Enable the Curry-Howard correspondence for propositional logic within CSLib

**The right design**: Use `Finset` contexts (like ND) rather than `Multiset` (CLL) for
LJ (intuitionistic), since this aligns with the existing ND context representation and
avoids context management overhead. LK uses sets on both sides (antecedent + succedent).

### Finding 5: The Kripke Completeness Gap for IPL/MPL Is Real But Addressable

`Propositional/Semantics/Kripke.lean` defines `IForces`, `KripkeModel`, and `IValid`/`MValid`
without proving completeness. The existing completeness proofs go via the algebraic route
(Lindenbaum-Tarski) and are bridged to Kripke semantics only one-directionally (algebraic
soundness → Kripke soundness via `KripkeBridge.lean`).

**Missing**: Direct Kripke completeness for IPL using the prime filter (DCCS world)
construction, and for MPL using prime MinTheory worlds. Both are well-known constructions
(Chagrov-Zakharyaschev Chapter 2) and would complete the Propositional/ semantic picture.

**Priority**: Medium. The algebraic route already handles completeness; this is about having
multiple independent completeness proofs, which is valuable for verification purposes but not
blocking anything.

### Finding 6: The Natural Deduction Capture-Avoidance Defect Has Downstream Implications

`NaturalDeduction/Basic.lean:276` has a comment:
```
/-- Substitution of a family of derivations... TODO: this implementation is not
capture avoiding. -/
def Theory.Derivation.subs ...
```

This is a correctness defect: the `subs` function is not capture-avoiding, meaning it can
accidentally substitute into the scope of bound variables. In a system where variables are
atoms (no binding in `Proposition Atom`), this may not currently cause problems. However:

1. It is a documented defect that blocks claiming full correctness of the ND system
2. If CSLib later adds quantifiers (first-order propositional logic or predicates), this
   defect would propagate
3. Any proof that uses `substAtom` + `subs` together could be affected

**The fix**: Alpha-renaming or de Bruijn indices for the atom substitution. Given that
`Proposition Atom` already uses a monad structure for substitution (`Proposition.subst`),
a capture-avoiding version likely just needs the substitution to track bound contexts.

---

## Roadmap Alignment

The `specs/ROADMAP.md` focuses on porting BimodalLogic content. The explicit remaining items are:

1. Discrete bimodal completeness (blocked by task 36)
2. Continuous bimodal completeness (blocked by task 37)
3. Dense/Discrete/Continuous temporal completeness
4. Abstract shared completeness infrastructure

Of these, items 1-3 depend on upstream BimodalLogic work that is itself blocked (the sorries
in discrete/continuous completeness are not Propositional/ sorries but BimodalLogic domain
sorries about irreflexive vs. reflexive semantics and continuous extension).

**Item 4 (abstract shared completeness)** is the most directly actionable:
- Extract the Lindenbaum/MCS/truth-lemma pattern into an abstract `AbstractCompleteness` module
- The `GenericMCS.lean` already provides the algebraic derivation system generically
- What remains: parameterize the canonical model construction over the choice of frame class

This is a **Foundations/ improvement** that would directly enable tasks 39, 40, 41 (temporal
completeness variants) and reduce code duplication between Modal, Temporal, and Bimodal
completeness modules.

---

## Downstream Impact Analysis

### Which modal logic modules would benefit from better propositional infrastructure?

1. **From concrete ProofSystem instances** (Modal.HilbertK inhabited):
   - `Modal/Metalogic/` could use generic `algebraic_mcs_*` wrappers from `GenericMCS.lean`
     instead of custom MCS code (currently Modal has its own `MCS.lean`)
   - Generic `HasDeductionTheorem` would propagate to all modal systems automatically

2. **From an abstract completeness framework**:
   - `Modal/Metalogic/Completeness.lean` (currently K completeness specific)
   - `Modal/Metalogic/Systems/S5/Completeness.lean`, etc. — all currently custom
   - A parameterized completeness proof taking `[ModalHilbert S]` + frame class would
     subsume these individual proofs

3. **From a propositional sequent calculus**:
   - Modal cut-free sequent systems (Fitting) would follow the same pattern
   - `LinearLogic/CLL/CutElimination.lean` could be completed using insights from LK cut elim
   - The `NaturalDeduction/Basic.lean` already proves cut as a derived rule — LK cut
     elimination would be a different (syntactic) proof

4. **From propositional tableau (if added)**:
   - The bimodal tableau already imports propositional rules internally
   - A standalone `Foundations/Logic/Tableau.lean` with signed formula infrastructure would
     let the bimodal tableau reuse it rather than re-implementing it
   - Modal tableau (K, S4, S5) would become instances of the generic framework

---

## Community Value Assessment

### What CSLib Could Contribute to the Lean 4 Ecosystem

The Lean 4 ecosystem currently lacks:

1. **A standalone verified propositional sequent calculus**: Mathlib has no LK/LJ
   formalization. CSLib adding it (especially with cut elimination) would be a first.

2. **A generic proof system framework**: The `InferenceSystem` + `HasDeductionTheorem`
   pattern in `Foundations/Logic/` is already a step toward this. A published/documented
   framework would attract modal logic contributors.

3. **Verified decision procedures for modal logics**: The bimodal tableau is impressive
   but domain-specific. A propositional tableau + modal K/S4/S5 tableaux (using generic
   infrastructure) would be highly valuable for software verification applications.

4. **Algebra-logic bridges**: The `AlgEvaluate` over `GeneralizedHeytingAlgebra` is
   sophisticated. Advertising this as "algebraic soundness/completeness for all three logic
   tiers" would be community-visible.

**The highest-community-value addition not in the roadmap**: A propositional LJ sequent
calculus with decidability (using G4ip — the display calculus for intuitionistic logic that is
known to be complete and terminating). This would:
- Enable automated proof search for intuitionistic propositional logic
- Serve as a foundation for a Lean 4 proof assistant / tactics library
- Attract constructive logic researchers who want verified intuitionistic proof theory

---

## Creative/Unconventional Approaches

### Unconventional Approach 1: Generic Proof System Functor

Rather than adding propositional-specific proof systems one by one, CSLib could define a
**typeclass for proof systems with structural rules**:

```lean
class SequentCalculus (S : Type*) (F : Type*) where
  antecedent : Type*  -- List, Finset, or Multiset
  succedent  : Type*
  derivation : antecedent → succedent → Sort v
  weak_ant   : ...
  weak_suc   : ...
  cut        : ...
```

Then propositional LK/LJ, modal K sequent, and CLL would all instantiate this typeclass.
Cut elimination would be a single `HasCutElimination` typeclass, proved once generically
where possible.

**Feasibility**: Medium. The difficulty is that different logics use different context types
(List, Finset, Multiset) and have different structural rules. Universe polymorphism issues
may arise. However, CLL already provides a working example of this pattern.

**Risk**: High design complexity; could over-engineer. Lean 4's typeclass system may not
support this gracefully without significant universe machinery.

### Unconventional Approach 2: Sequent Calculus as the Primary Proof System

Currently, Hilbert is the primary formalization backbone (derivation via `DerivationTree` is
the underlying implementation). What if this were inverted: use a sequent calculus as the
ground truth, with Hilbert as a derived system?

**Advantage**: Sequent systems have structural properties (weakening, contraction, cut) that
are cleaner to work with in automated proof search. The deduction theorem becomes a
structural property of the sequent system rather than something proved separately.

**Disadvantage**: All existing completeness proofs assume Hilbert as the primary system. The
MCS/Lindenbaum construction is Hilbert-native. Switching would require rebuilding the
metalogic around sequent derivability.

**Assessment**: This would be a significant architectural shift, not appropriate for an
incremental improvement task. However, for a **future modal logic contribution** (e.g.,
formalization of S4 or S5 tableaux), starting with sequent calculus as the primary system
and providing the Hilbert equivalence as a bridge would be more elegant.

### Unconventional Approach 3: Extract Propositional Tableau from Bimodal

Rather than building a propositional tableau from scratch, **extract the propositional rules
from the bimodal tableau into Foundations/** and let the bimodal tableau import them:

```lean
-- Foundations/Logic/Tableau.lean
inductive PropositionalRule (F : Type*) [HasImp F] [HasAnd F] [HasOr F] where
  | andPos | andNeg | orPos | orNeg | impPos | impNeg | negPos | negNeg

-- Logics/Bimodal/Metalogic/Decidability/Tableau.lean (now imports above)
inductive BimodalTableauRule extends PropositionalRule ... where
  | boxPos | boxNeg | allFuturePos | allFutureNeg | allPastPos | allPastNeg
```

**Advantage**: No redundant code; the bimodal tableau retains the propositional rules by
extension. Propositional completeness via the tableau (Anderson-Belnap completeness) becomes
a stepping stone.

**Disadvantage**: Requires refactoring the existing bimodal tableau, which is a PR risk.

**Assessment**: This is the right long-term architecture. As a near-term practical step,
adding `Foundations/Logic/PropositionalTableau.lean` as a standalone module and then
updating the bimodal import would be incremental and low-risk.

---

## Prioritization Strategy

Given limited development resources, the recommended sequence is:

### Priority 1 (High Impact, Low Risk): Concretize Modal.HilbertK + Generic MCS Usage
**Rationale**: The gap between Foundations/'s aspirational typeclass hierarchy and its actual
usage is primarily the missing modal tag instances. Providing `InferenceSystem` instances for
`Modal.HilbertK` (and ideally `Temporal.HilbertBX` and `Bimodal.HilbertTM`) would unlock
polymorphic proof development.

**Estimated effort**: 2-3 days. The pattern is established by `Propositional/ProofSystem/Instances.lean` (120 lines). Modal instances would follow the same structure.

**Benefit**: All 14 modal tags become usable. `ClassicalHilbert Modal.HilbertK` becomes
inhabitable. Generic `algebraic_mcs_*` wrappers become usable for modal completeness.

### Priority 2 (High Impact, Medium Risk): Abstract Completeness Infrastructure
**Rationale**: Explicitly listed in the ROADMAP as remaining work. Extracting the shared
pattern from Modal/Temporal/Bimodal completeness proofs into a generic module would:
- Reduce ~500 lines of duplicated code across three completion modules
- Enable discrete/continuous completeness as variations on the abstract pattern
- Unblock tasks 39, 40, 41 (temporal completeness variants)

**Estimated effort**: 1-2 weeks. Requires careful abstraction design.

**Benefit**: Directly unblocks roadmap items. High multiplier on future completeness work.

### Priority 3 (Medium Impact, Medium Risk): Propositional Sequent Calculus (LK/LJ)
**Rationale**: Completes the proof system triad (Hilbert + ND + SC) for propositional logic.
Cut elimination would be the headline result. Use `Finset`-based LJ for intuitionistic logic.

**Estimated effort**: 2-4 weeks. Cut elimination is a moderately involved syntactic proof.

**Benefit**: First LK/LJ in Lean 4 ecosystem. Template for modal sequent systems. Closes the
gap between CSLib and Mathlib's `Tactic.ITauto` (which uses G4ip internally but doesn't
expose it formally).

### Priority 4 (Medium Impact, Low Risk): Propositional Tableau Extraction
**Rationale**: The 8 propositional tableau rules already exist in the bimodal tableau.
Extracting them to `Foundations/Logic/PropositionalTableau.lean` and proving completeness via
the signed-formula expansion is a concrete, bounded task.

**Estimated effort**: 1 week. The decision procedure infrastructure (saturation, closure,
countermodel extraction) exists in the bimodal module and can be adapted.

**Benefit**: Propositional decidability via tableau (complementing the existing `BoolEvaluate`
decidability). Template for modal tableau.

### Do Not Prioritize
- **A full witness-count restructure** (BimodalLogic report 16): This is a BimodalLogic-
  specific problem about temporal NF composition that has no analog in CSLib's current scope.
- **The capture-avoidance fix for `subs`**: Low impact unless quantifiers are added. Document
  the limitation clearly.
- **Kripke completeness for IPL/MPL via prime filter**: Already covered algebraically. Only
  worth adding for completeness of the semantic picture, not for unblocking anything.

---

## Recommended Approach

The highest-leverage sequence for improving Propositional/ and Foundations/ while maximizing
downstream impact is:

1. **Concretize modal tag instances** (Priority 1): Unlock the Foundations/ architecture for
   Modal, Temporal, and Bimodal logics by providing concrete `InferenceSystem` and axiom
   instances for the major system tags.

2. **Extract abstract completeness** (Priority 2): Build `Foundations/Logic/Metalogic/
   AbstractCompleteness.lean` parameterized over frame class, directly unblocking the
   remaining roadmap items.

3. **Add propositional LJ sequent calculus with cut elimination** (Priority 3): Complete the
   proof system triad and provide the community-visible headline result.

4. **Extract propositional tableau to Foundations/** (Priority 4): Clean the bimodal code,
   enable propositional decidability via tableau, and template modal tableau.

This sequence avoids over-engineering, directly serves the roadmap, and creates reusable
infrastructure at each step.

---

## Evidence

### Evidence: Propositional/ is sorry-free (as of 2026-06-22)

```bash
$ grep -rn "sorry" Cslib/Logics/Propositional/ Cslib/Foundations/Logic/
# (no output — zero sorries)
```

All sorries in CSLib are in `Cslib/Logics/Bimodal/` (tasks 36, 37) and
`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` (task 275).

### Evidence: Modal tags are stubs but propositional tags are fully instantiated

`Propositional/ProofSystem/Instances.lean` (120 lines) registers:
- `InferenceSystem Propositional.HilbertCl`
- `ModusPonens Propositional.HilbertCl`
- `HasAxiomImplyK/ImplyS/EFQ/Peirce/AndI/AndE1/AndE2/OrI1/OrI2/OrE Propositional.HilbertCl`
- `ClassicalHilbert Propositional.HilbertCl` (bundled)

No equivalent file exists for `Modal.HilbertK` or any other modal/temporal/bimodal tag.

### Evidence: Bimodal tableau has propositional rules already defined

`Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` header lists:
```
### Propositional Rules
- andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg
```

These 8 rules are the exact content of a standalone propositional tableau. They are currently
coupled to `BimodalConnectives` and could be parameterized over any formula type implementing
`HasAnd`, `HasOr`, `HasImp`.

### Evidence: GenericMCS is a strategic asset with untapped potential

`GenericMCS.lean` provides for any `[MinimalHilbert S (F := F)]`:
- `algebraicDerivationSystem` — free derivation system
- `algebraic_has_deduction_theorem` — free deduction theorem
- `algebraic_mcs_closed_under_derivation` — free MCS closure
- `algebraic_mcs_implication_property` — free implication property
- `algebraic_mcs_negation_complete` — free negation completeness

Yet Modal, Temporal, and Bimodal completeness modules all re-prove these from scratch using
their own custom MCS implementations, because the modal/temporal/bimodal tags lack `MinimalHilbert` instances. Providing instances would immediately make ~200-300 lines of custom MCS code per logic redundant.

---

## Confidence Level

**High confidence** (directly verified in code):
- Propositional/ and Foundations/Logic/ are sorry-free
- `Propositional.HilbertCl/Int/Min` tags are fully instantiated; modal/temporal/bimodal tags are not
- BimodalLogic report 16 is about temporal NF composition, not propositional proof systems
- The bimodal tableau contains the 8 propositional rules already
- CLL provides the sequent calculus pattern (Basic.lean with InferenceSystem-based Proof type)
- GenericMCS provides free MCS infrastructure for any MinimalHilbert system

**Medium confidence** (architectural inference from code structure):
- Providing modal tag instances would enable polymorphic reuse of GenericMCS
- Abstract completeness extraction would unblock tasks 39, 40, 41
- Propositional LJ with cut elimination is feasible in 2-4 weeks given existing ND infrastructure

**Lower confidence** (speculative):
- Whether the generic `SequentCalculus` typeclass approach (Unconventional Approach 1) is
  feasible without excessive universe overhead
- Whether the bimodal tableau refactor (extracting to Foundations/) would be accepted by
  maintainers given the PR risk
- Whether the Lean 4 / Zulip community would prioritize a propositional sequent calculus
  contribution vs. the more applied Boole/algorithm contributions listed in CONTRIBUTING.md
