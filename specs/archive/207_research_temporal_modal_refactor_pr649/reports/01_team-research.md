# Research Report: Task #207

**Task**: Research refactoring Temporal/ and Modal/ implementations based on PR #649 review feedback
**Date**: 2026-06-15
**Mode**: Team Research (4 teammates)
**Session**: sess_1781542145_c0bb30

## Summary

Four parallel research angles converge on a clear diagnosis and recommendation: CSLib's metalogic infrastructure (DeductionTheorem, MCS, DerivationTree) is duplicated across Modal (~8K LOC), Temporal (~15K LOC), and Bimodal (~51K LOC) with near-identical structure. The Isabelle `Propositional_Logic_Class` (Doty 2022) demonstrates the target pattern -- proving all propositional metatheory once generically and inheriting it per-logic -- but requires adaptation for Lean 4's typeclass system and CSLib's proof-system polymorphism. The recommended approach is **Mixin Property Classes**: a generic `DerivationTree` parameterized by axiom predicates and inference rules, with the DeductionTheorem and MCS construction proved once at the Foundations level. This follows the Mathlib-aligned pattern, preserves concrete formula types and notation, and enables incremental migration.

**Critical gap**: The actual Zulip reviewer feedback (https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Tense.20Logic/near/603415032) could not be fetched by any teammate (requires JavaScript rendering/authentication). PR #649 has no GitHub review comments. The analysis below is reconstructed from the Isabelle link, PR context, and codebase structure. The user should read the Zulip thread directly to confirm alignment.

## Key Findings

### 1. The Core Problem: Metalogic Code Duplication (~890 LOC)

All four teammates independently quantified the duplication:

| Duplicated Component | Modal | Temporal | Bimodal | Savings if Unified |
|---|---|---|---|---|
| neg/top/and/or/iff abbrevs | 5 defs | 5 defs | 5 defs | 10 defs |
| BEq reflexivity + lawfulness | ~60 LOC | ~60 LOC | ~60 LOC | ~120 LOC |
| DerivationTree inductive | ~30 LOC | ~30 LOC | ~40 LOC | ~60 LOC |
| height function + lemmas | ~30 LOC | ~30 LOC | ~30 LOC | ~60 LOC |
| Deriv/Derivable wrappers | ~20 LOC | ~20 LOC | ~20 LOC | ~40 LOC |
| DeductionTheorem | ~200 LOC | ~200 LOC | ~200 LOC | ~400 LOC |
| MCS infrastructure | ~100 LOC | ~100 LOC | ~100 LOC | ~200 LOC |
| **Total** | | | | **~890 LOC** |

The DeductionTheorem is the highest-impact target: all three proofs follow identical structure (case split on tree constructors, K axiom for axiom/assumption cases, S combinator for MP, impossibility for necessitation, recursion for weakening), differing only in which constructors exist and which formula type is used.

### 2. CSLib Already Has the Right Foundation -- But It's Not Connected

CSLib has a dual-layer architecture:
- **Layer A (Concrete)**: Per-logic `Formula` inductives, `DerivationTree` inductives, bespoke metalogic proofs
- **Layer B (Abstract)**: `Foundations/Logic/` with `InferenceSystem`, `ProofSystem`, `HasAxiom*` typeclasses (84 of them), polymorphic `Axioms.*` abbreviations, and generic `Theorems/`

The layers are connected only via `wrap`/`unwrap` bridge patterns (e.g., `PropositionalHelpers.lean`). The abstract layer's theorems are used inside concrete metalogic only through manual bridging, creating boilerplate without eliminating duplication. The `HasHilbertTree` typeclass in `DeductionHelpers.lean` already demonstrates that abstracting the derivation tree pattern works -- it just hasn't been extended to the full metalogic pipeline.

### 3. The Isabelle Pattern: Right Idea, Needs Adaptation

The Isabelle AFP `Propositional_Logic_Class` (Doty 2022) defines:
- `implication_logic`: typeclass with `deduction` predicate, `implication` operation, axioms K/S/MP
- `classical_logic`: extends with `falsum` + double negation
- All metatheory (list deduction, set deduction, deduction theorem, MCS, Zorn extension) proved once generically

**Key insight from Isabelle**: Using `listImp` (list implication), the deduction theorem becomes *definitionally trivial*:
```
contextDeriv (A :: Gamma) B = deriv (listImp (A :: Gamma) B)
                            = deriv (imp A (listImp Gamma B))
                            = contextDeriv Gamma (imp A B)
```

**What does NOT translate directly**:
- Isabelle locales support `interpretation` (renaming + instantiation); Lean 4 typeclasses lack this
- The pure Isabelle pattern puts `deriv` as a field on the formula type, which **breaks proof-system polymorphism** -- CSLib supports multiple proof systems (K, T, S4, S5) on the same formula type via tag types
- Isabelle's formalization only covers propositional logic; it doesn't address modal/temporal operators or their inference rules (necessitation, temporal duality)

The adapted approach: keep CSLib's tag-type + `InferenceSystem` pattern for proof-system polymorphism, but lift the metalogic machinery to work generically over any formula type satisfying the right typeclasses.

### 4. Three Alternative Approaches Evaluated

**Approach 1: FormulaFunctor (Initial Algebra)** -- REJECTED
- Factor formula types as fixed points of composable functors
- Eliminates ALL duplication but is impractical: Lean 4's positivity checker rejects `Fix (F : Type -> Type)`, pattern matching degrades severely, no prior art in Lean 4
- Verdict: High risk, not recommended

**Approach 2: Mixin Property Classes** -- RECOMMENDED
- Keep concrete formula types, extract shared metatheory into generic infrastructure
- `GenericDerivationTree` parameterized by axiom predicate + inference rules
- `generic_deduction_theorem` proved once, requiring only K and S axioms
- Incremental adoption, preserves notation and pattern matching, Mathlib-aligned
- Verdict: Medium risk, high reward, most practical path

**Approach 3: Isabelle-Style Dependent Classes** -- PARTIALLY APPLICABLE
- Direct translation with `deriv` as a class field
- Loses proof-system polymorphism; adapted version (with tag types) converges back to CSLib's existing `InferenceSystem` pattern
- Confirms CSLib's existing architecture is sound at the type level; the gap is at the metalogic level
- Verdict: Medium-high risk, limited additional value over Approach 2

### 5. The Bimodal Module is the Constraining Factor

At 51,439 lines, the Bimodal logic includes decidability, separation, algebraic completeness, chronicle construction, conservative extension, and dense completeness. Any refactoring that changes formula types, axiom systems, or derivation tree structure cascades through ALL of this. The Bimodal logic should be touched LAST (or not at all in the initial phases).

## Synthesis

### Conflicts Resolved

**Conflict 1: Scope of refactoring**
- Teammate A proposed 5 phases ending with bridge elimination
- Teammate C advocated minimal-first approach
- **Resolution**: Start with Teammate C's minimal viable approach (axiom embedding, ~500 LOC), validate the pattern, then proceed to Teammate A's generic derivation framework. The phased approach means we get value early and can stop at any tier.

**Conflict 2: Whether the Isabelle approach is "the right model"**
- Teammate A: Yes, adapt it
- Teammate B: The pure version doesn't work; the adapted version converges to what CSLib already has
- Teammate C: It's insufficient (only propositional)
- **Resolution**: The Isabelle approach is the right *inspiration* at the propositional metatheory level. CSLib needs original design work beyond what Isabelle provides for modal/temporal rules. The key takeaway is the *principle* (prove shared metatheory once) not the *mechanism* (Isabelle locales).

**Conflict 3: Generic derivation tree design**
- Teammate A: `GenericDerivation` parameterized by `AxiomPredicate` only
- Teammate B: `GenericDerivationTree` parameterized by both `Axioms` and `Rules`
- **Resolution**: Teammate B's design is more general -- the `Rules` parameter handles logic-specific inference rules (necessitation, temporal duality) that A's design pushes into separate extension types. The two-parameter design (`Axioms : F -> Prop`, `Rules : List F -> F -> Prop`) is recommended.

### Gaps Identified

1. **Unknown reviewer feedback**: The specific Zulip discussion that motivated this task was inaccessible. The refactoring analysis stands on its own merits but may not address the reviewer's exact concerns.

2. **Definitional equality of polymorphic axioms**: It is unverified whether `Foundations/Logic/Axioms.lean` polymorphic axioms are definitionally equal to the concrete axiom patterns in Temporal/Modal. If they are not, the polymorphic layer cannot serve as the bridge. This must be checked before implementation.

3. **Typeclass resolution performance**: Adding generic metalogic typeclasses on top of the existing 84 `HasAxiom*` classes may impact elaboration performance. Benchmarking is needed.

4. **Interaction with PR #607**: fmontesi's PR #607 introduces per-operator typeclass files. If it merges, it changes the foundation this refactoring builds on.

5. **`listImp`-based deduction theorem feasibility**: The Isabelle pattern makes the deduction theorem definitionally trivial via `listImp`. It's unclear whether CSLib can adopt this representation while maintaining the `Type`-valued `DerivationTree` that enables structural recursion in existing proofs.

### Recommendations

#### Recommended Approach: Mixin Property Classes (Phased)

**Phase 0: Verify Foundations** (prerequisite, low risk)
- Confirm `Foundations/Logic/Axioms.lean` polymorphic axioms are definitionally equal to concrete axiom patterns
- Assess `HasHilbertTree` extension points for the full metalogic pipeline
- Estimated effort: 1-2 days

**Phase 1: Generic DeductionTheorem** (highest ROI, ~400 LOC savings)
- Define `GenericDerivationTree` in `Foundations/Logic/Derivation/` parameterized by `Axioms : F -> Prop` and `Rules : List F -> F -> Prop`
- Prove `generic_deduction_theorem` once, requiring K and S axioms
- Instantiate for Modal (simplest) as proof of concept
- Estimated effort: 1-2 weeks
- PR size: ~300-500 LOC

**Phase 2: Generic MCS Construction** (~200 LOC savings)
- Define `GenericMCS` and prove Lindenbaum extension once
- Leverage existing `Foundations/Logic/Metalogic/Consistency.lean` `DerivationSystem` pattern
- Estimated effort: 1 week
- PR size: ~300 LOC

**Phase 3: Connect Temporal and Modal** (migration)
- Replace concrete DeductionTheorem/MCS in Modal/ and Temporal/ with generic instantiations
- Eliminate `wrap`/`unwrap` bridge where possible
- Estimated effort: 2-3 weeks
- PR size: multiple ~300-500 LOC PRs

**Phase 4: Axiom Predicate Algebra** (future-proofing, novel)
- Define composable axiom predicates (`PropAxioms || ModalKAxiom || ModalTAxiom`)
- Enable defining new logics by composing axiom sets
- Estimated effort: 2-4 weeks
- PR size: ~500 LOC

**Phase 5: Bimodal Integration** (deferred, high risk)
- Only after pattern validated on Modal and Temporal
- May be deferred indefinitely if cost/benefit is unfavorable
- The 51K LOC module should not be touched until the pattern is battle-tested

#### Design Principles

1. **Preserve concrete formula types** -- no unified formula type, keep `Modal.Proposition`, `Temporal.Formula`, `Bimodal.Formula`
2. **Preserve proof-system polymorphism** -- keep tag types + `InferenceSystem` pattern
3. **Preserve `Type`-valued derivation trees** -- do not collapse to `Prop`-valued predicates
4. **Preserve scoped notation** -- each logic keeps its own notation
5. **Additive first, then migrative** -- new generic code alongside existing code, then gradual migration
6. **Small PRs** -- each phase as a self-contained ~300-500 LOC PR for upstream acceptance

#### Strategic Considerations (from Horizons analysis)

- The ROADMAP.md item "Abstract shared completeness infrastructure" directly calls for this work
- PR #649 and the Modal PR establish the connective typeclass foundation; this is the natural next step
- Future logics (epistemic, deontic, CTL, dynamic) are accommodated by the current connective typeclass design; the refactoring would make adding them cheaper
- Novel ideas worth prototyping: axiom predicate algebra, duality as a first-class typeclass, embedding hierarchy as Lean 4 coercions

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|-----------------|
| A | Primary | completed | high | Concrete 5-phase refactoring plan with code sketches |
| B | Alternatives | completed | medium-high | 3-approach comparison, Mixin Properties recommended |
| C | Critic | completed | medium | Risk analysis, Bimodal constraint, unanswered questions |
| D | Horizons | completed | medium-high | Strategic alignment, future-proofing, novel approaches |

## References

- Doty, M. (2022). Propositional Logic Class. Archive of Formal Proofs. https://isa-afp.org/thys/Propositional_Logic_Class/
- CSLib PR #649: Temporal formula type + connectives (under review)
- CSLib `Foundations/Logic/`: Connectives.lean, ProofSystem.lean, Axioms.lean, InferenceSystem.lean
- CSLib `Foundations/Logic/Metalogic/Consistency.lean`: Existing generic `DerivationSystem` pattern
- CSLib `Logics/Temporal/Metalogic/DeductionHelpers.lean`: `HasHilbertTree` typeclass (existing abstraction)
- Mathlib hierarchy design: `Mathlib.Order.Defs.PartialOrder` pattern (unbundled + extension)
