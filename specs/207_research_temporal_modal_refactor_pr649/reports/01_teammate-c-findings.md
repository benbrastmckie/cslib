# Teammate C (Critic) Findings: Modal/Temporal Refactoring

## Key Findings

1. **The core duplication problem is quantifiably severe.** There are 15 separate axiom inductive types across Modal alone (one per system: K, T, D, B, K4, K5, K45, S4, S5, TB, KB5, D4, D5, D45, DB), plus separate axiom types in Temporal and Bimodal. Each duplicates the 4 propositional axiom constructors verbatim. The Temporal `Axiom` inductive also redeclares all propositional axioms as concrete pattern-matched constructors rather than referencing the polymorphic `Axioms.*` from `Foundations/Logic/Axioms.lean`.

2. **The Isabelle Propositional_Logic_Class uses a minimal abstraction.** The `implication_logic` class has just two fields: a `deduction : 'a -> bool` predicate and an `implication : 'a -> 'a -> 'a` binary operation, plus axiom K, axiom S, and modus ponens. `classical_logic` extends this by adding `falsum :: 'a` and the double negation axiom. This is far simpler than CSLib's current approach but also far less expressive -- it only handles the implicational fragment plus classical negation.

3. **CSLib already has the polymorphic axiom layer but does not use it.** `Foundations/Logic/Axioms.lean` defines polymorphic `abbrev`s (`Axioms.ImplyK`, `Axioms.AxiomK`, `Axioms.SerialFuture`, etc.) and `Foundations/Logic/ProofSystem.lean` defines 84 `HasAxiom*` typeclasses. But the concrete proof systems in `Modal/`, `Temporal/`, and `Bimodal/` do NOT reference these -- they define their own axiom inductives with hard-coded formula patterns. The typeclass bridge (`ProofSystem/Instances/*.lean`) connects the two layers but does not reduce the duplication.

4. **The Zulip discussion and PR #649 review comments were not accessible.** The Zulip web interface requires JavaScript rendering and the API requires authentication. PR #649 has no GitHub review comments or inline reviews. The PR body references a Zulip discussion at `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Tense.20Logic/with/602336211` but the content could not be retrieved. **This is a critical gap in the research -- the actual reviewer feedback that motivated this task is unknown to us.**

5. **The three proof systems (Modal, Temporal, Bimodal) are completely independent.** There is zero code sharing between them. The Bimodal `ProofSystem/Derivation.lean` does not import Modal or Temporal. Each reimplements modus ponens, weakening, necessitation, deduction theorem, MCS construction, soundness, and completeness from scratch.

## Current Design Strengths (What to Preserve)

1. **The concrete axiom inductives enable decidable pattern matching.** The Temporal `Axiom` inductive with its `minFrameClass` function cleanly gates axiom use by frame class (Base/Dense/Discrete). This is elegant and cannot be easily replicated with a purely typeclass-based approach.

2. **The `DerivationTree` as `Type` (not `Prop`) design.** All three systems use `Type`-valued derivation trees with computable `height` functions. This enables well-founded recursion in deduction theorem proofs. The Isabelle approach, being purely propositional, does not address this concern.

3. **The `Foundations/Logic/Metalogic/Consistency.lean` generic framework.** The `DerivationSystem` structure and Lindenbaum's lemma are already abstracted. Both Modal and Temporal instantiate this. This is the RIGHT kind of abstraction and should be the model for further refactoring.

4. **The `InferenceSystem` typeclass with `DerivableIn` wrapper.** This separation of `Type`-valued derivation trees from `Prop`-valued derivability is sound and matches standard practice.

5. **The scoped notation design.** Each logic uses `scoped` notation to avoid conflicts. This is necessary and well-executed.

6. **The Bimodal logic's complete metalogic.** At 51,439 lines, the Bimodal logic has the most complete formalization (decidability, separation, algebraic completeness, chronicle construction). Any refactoring must not break this.

## Translation Risks (Isabelle to Lean 4)

1. **Isabelle locales vs Lean 4 typeclasses are fundamentally different.** Isabelle locales are contexts that can be opened and interpreted; Lean 4 typeclasses are resolved by instance synthesis. Isabelle's `interpretation` mechanism (re-proving locale axioms in a new context) has no direct Lean 4 analog. The closest Lean 4 pattern is explicit structure instantiation, which is more verbose.

2. **Isabelle's `'a` type variable is unconstrained; Lean 4 requires explicit typeclass constraints.** The Isabelle `implication_logic` works on any type `'a` with implication. In Lean 4, every function needs explicit `[HasImp F]` constraints. This is already handled by CSLib's `HasImp`/`HasBot` classes, but scaling it to modal/temporal connectives creates long constraint lists (see `TemporalBXHilbert` with 6 typeclass constraints on `F` alone).

3. **The Isabelle formalization only covers classical propositional logic.** It does not handle modalities, temporal operators, or multiple interacting proof rules (necessitation, temporal duality). Translating the "dependent type approach" to Lean 4 would require significant original design work beyond what Isabelle provides.

4. **Isabelle's deduction predicate `deduction :: 'a => bool` is a function from formulas to `bool`.** This is a decision procedure approach, not a proof-relevant derivation tree. CSLib's `DerivationTree` is `Type`-valued, which is strictly more informative. Collapsing to the Isabelle-style `Prop`-valued approach would lose the ability to do structural recursion on proofs.

5. **Isabelle's class mechanism allows default method overriding; Lean 4's does not.** In Isabelle, a class extending another can override or specialize parent methods. In Lean 4, typeclass fields are strictly inherited. This means Lean 4 hierarchies must be designed more carefully upfront.

## Typeclass Resolution Concerns

1. **Diamond inheritance is already present and explicitly documented.** `BimodalConnectives` avoids the diamond between `ModalConnectives` and `TemporalConnectives` by extending `ModalConnectives` directly and adding `HasUntil`/`HasSince` (line 130 of `Connectives.lean`). Any refactoring that introduces new typeclass hierarchies must preserve this discipline.

2. **Instance coherence across 15 modal systems.** Currently, each modal system (K, T, D, ..., S5) has its own opaque tag type (`Modal.HilbertK`, `Modal.HilbertT`, etc.) and separate instance declarations. If the refactoring parameterizes the proof system over an axiom predicate (as the current `DerivationTree Axioms` already does), the typeclass instances for `HasAxiomT`, `HasAxiom4`, etc. would need to be generated per-system. This is no easier than the current approach unless Lean 4 gets a mechanism for conditional instance synthesis.

3. **The `F` parameter in proof system typeclasses creates universe polymorphism pressure.** `TemporalBXHilbert` requires `[HasBot F] [HasImp F] [HasUntil F] [HasSince F] [InferenceSystem S F]` -- 5 constraints. Adding more connectives (HasAnd, HasOr, HasDia) increases this further. Each additional constraint slows typeclass search.

4. **Orphan instance risk with polymorphic axiom approach.** If axioms are defined polymorphically over `[HasImp F] [HasBot F]` etc., then registering instances for concrete formula types (which live in different modules) creates orphan instance scenarios that Lean 4 handles but with potential coherence warnings.

5. **The 84 `HasAxiom*` typeclasses in ProofSystem.lean already exhibit scaling problems.** Adding new axiom schemas (e.g., for intuitionistic modal logics, epistemic logics) would require adding to this flat list. A more structured approach (axiom families, or dependent types indexing axiom schemas) would be more maintainable but harder to implement.

## Scope and Migration Risks

### Code volume at risk

| Component | Lines | Impact |
|-----------|-------|--------|
| Foundations/Logic/ | 4,048 | Medium -- needs new abstractions |
| Modal/ | 8,117 | High -- 15 systems to rewire |
| Temporal/ | 14,871 | High -- axiom system + metalogic |
| Bimodal/ | 51,439 | Critical -- most complex, most fragile |
| **Total** | **78,475** | |

### The Bimodal logic is the constraining factor

The Bimodal logic at 51K lines includes:
- Decidability via tableau with correctness proofs
- Separation theorem (hierarchy induction)
- Algebraic completeness (Lindenbaum quotient, ultrafilter MCS)
- BX Canonical model (chronicle construction)
- Conservative extension proofs
- Dense completeness

Any refactoring that changes the formula type, axiom system, or derivation tree structure will cascade through ALL of this. The Bimodal logic was developed with the current concrete axiom pattern. Converting it to use polymorphic axioms would be a months-long effort.

### Incremental approaches

1. **Minimal viable refactoring (LOW RISK):** Keep concrete axiom inductives but generate them from a shared combinator. Add `Axiom.ofPropositional` / `Axiom.ofModal` / `Axiom.ofTemporal` constructors that embed sub-system axioms. No typeclass changes needed. Estimated impact: ~500 lines of new code, ~300 lines of deletions.

2. **Moderate refactoring (MEDIUM RISK):** Parameterize `DerivationTree` over a generic axiom type and provide axiom embedding functions. The Modal `DerivationTree` already does this (`DerivationTree Axioms`). Generalize this pattern to Temporal and Bimodal. Estimated: ~2000 lines changed.

3. **Full Isabelle-style refactoring (HIGH RISK):** Replace all concrete formula types with a single parameterized type; all axiom predicates with a single typeclass hierarchy; all derivation trees with a single parameterized tree. This would touch 78K+ lines. Not recommended for a single PR or even a single task.

### Migration path

The only safe approach is bottom-up:
1. First, ensure the `Foundations/Logic/` polymorphic axioms are definitionally equal to the concrete axioms used in Modal/Temporal/Bimodal (they currently are NOT -- the Temporal axioms use different derived operator definitions than the Foundations ones)
2. Second, refactor the smallest system (Propositional, if it uses Hilbert-style proofs) to validate the pattern
3. Third, apply to Modal (starting with K, the simplest)
4. Fourth, Temporal
5. LAST, Bimodal (if at all -- the cost/benefit is questionable)

## Unanswered Questions

1. **What exactly did the PR #649 reviewer say?** The Zulip discussion that motivated this task was inaccessible. Without knowing the specific concerns, we risk solving a problem the reviewer did not raise.

2. **Is the Isabelle Propositional_Logic_Class actually the right model?** The Isabelle formalization covers only classical propositional logic with implication and falsum. CSLib handles modal, temporal, and bimodal logics with multiple interacting proof rules. The Isabelle approach may be too simple to generalize.

3. **What does "dependent type approach" mean concretely for CSLib?** The task description mentions "a dependent type system approach in Lean 4" but does not specify what this means. Possible interpretations:
   - Axiom families indexed by logic system (dependent inductive)
   - Formula types parameterized by their connective set (sigma types)
   - Derivation trees indexed by both axiom predicate AND formula type
   - Something else entirely

4. **Are there performance constraints?** The current typeclass hierarchy already has 84 `HasAxiom*` classes. Does Lean 4's typeclass synthesis scale to the refactored design? Has anyone benchmarked typeclass search time for the current hierarchy?

5. **What is the actual goal: reducing upstream PR size, reducing duplication, or enabling new logic families?** These goals suggest different refactoring strategies. Reducing PR size suggests factoring out shared code. Reducing duplication suggests parameterization. Enabling new families suggests a fundamentally different architecture.

6. **Does the `Axioms.lean` polymorphic layer ACTUALLY unify with the concrete axiom formulas?** The Temporal axioms use `Formula.top.imp (Formula.someFuture Formula.top)` for serial future, while `Axioms.SerialFuture` uses `HasImp.imp top' (HasUntil.untl top' top')`. These should be definitionally equal given the `TemporalConnectives` instance, but this has not been verified. If they are NOT definitionally equal, the polymorphic axioms are useless for the concrete proof systems.

7. **What about the Bimodal ProofSystem?** The Bimodal logic has its own axiom predicate and derivation tree. The relationship between Bimodal's axiom system and the combined Modal+Temporal axiom systems is complex (conservative extension proofs exist but they work at the formula embedding level, not the axiom level).

8. **How does fmontesi's PR #607 interact with this?** PR #607 introduces per-operator typeclass files. If it merges, it changes the foundation the refactoring builds on. If it doesn't, this work proceeds on the current foundation.

## Confidence Level: MEDIUM

**Justification:**

- HIGH confidence in the duplication analysis and scope assessment (based on direct code reading)
- HIGH confidence in the Lean 4 typeclass resolution concerns (based on known Lean 4 limitations)
- MEDIUM confidence in the Isabelle translation analysis (based on partial access to the formalization -- only the Implication_Logic and Classical_Logic locales were retrievable)
- LOW confidence in the specific reviewer feedback assessment (the Zulip discussion was inaccessible, and PR #649 has no GitHub review comments)
- LOW confidence in recommending a specific refactoring strategy without knowing the reviewer's exact concerns

The biggest risk to this research is that we are solving a problem we have not precisely identified. The task description says "based on PR #649 review feedback" but no review feedback was found on the PR, and the Zulip discussion could not be accessed. The refactoring analysis above is sound on its own merits, but it may not address the actual concern that motivated the task.
