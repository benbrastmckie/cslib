# Teammate C (Critic) Findings — Task 261
## Propositional Logic Zulip Thread: Critical Analysis

**Date**: 2026-06-22
**Thread URL**: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/with/604219492
**Role**: Critic — identify gaps, blind spots, and underexamined risks in the debate

---

## Summary of the Debate

The thread involves three principals:

- **Benjamin Brast-McKie (BBM)**: Contributing implementer; built Hilbert systems for MPL/IPL/CPL with soundness/completeness, working through PR #648. Favors `⊥` as a primitive constructor and `Prop`-valued `Evaluate`.
- **Matthew Doty (MD)**: User needing DPLL and SAT machinery. Prefers `Atom → Bool` evaluation and is skeptical of two-semantics complexity. Wants `Evaluate` in a `HeytingAlgebra`.
- **Thomas Waring (TW)**: Core contributor with NaturalDeduction/ already in CSLib. Designed original ND system around `MPL` without primitive `⊥`. Proposes `GeneralizedHeytingAlgebra` as the right algebraic abstraction; has working code in a branch.

Four design issues are active:

1. **`⊥` as primitive constructor vs. atom**: BBM and MD favor primitive; TW designed MPL without it.
2. **`Prop` vs. `Bool` valuations**: MD wants `Bool`; BBM proposes dual semantics; TW/ctchou suggest GHA unifies them.
3. **`Evaluate` in `HeytingAlgebra` vs. `GeneralizedHeytingAlgebra`**: MD wants HA; TW insists GHA is needed for MPL.
4. **Which logic is primary**: TW treats MPL as the base layer; BBM works top-down from CPL/bimodal.

---

## Key Findings

### 1. The Codebase Has Already Moved Beyond the Thread Debate

The most critical finding is that the codebase (as of 2026-06-22) has largely resolved these debates unilaterally, without the thread reaching consensus:

- `⊥` **is already a primitive constructor** (`Defs.lean` line 86: `| bot`)
- `Evaluate` **is already `Prop`-valued** (`Bool.lean` provides `BoolEvaluate` alongside it)
- `AlgEvaluate` **is already parameterized over `GeneralizedHeytingAlgebra`** with explicit `bot_val` (`Semantics/Algebra.lean`)
- **Both semantics coexist**: `Evaluate`, `BoolEvaluate`, `IForces` (Kripke), and `AlgEvaluate` are all present

The Zulip thread (last message: Thomas Waring's MSG 605341190, asking "why did you delete...") appears to be asking about a deletion that happened during this implementation. The thread question remains **open and unacknowledged**; TW's message was cut off and appears to be asking about the deletion of something.

**Implication for the response**: Any reply to the Zulip thread must acknowledge that implementation has proceeded and explain the design choices that were made — the thread participants are waiting for a response.

---

## Assumptions Not Validated

### A1. The `bot_val` solution for MPL completeness is validated — but its ergonomics are not
BBM argues that making `⊥` a primitive constructor requires `bot_val` parameters throughout. The codebase confirms this: `AlgEvaluate` takes an explicit `bot_val : H` because `GeneralizedHeytingAlgebra` lacks `⊥`. This is correct formally, but:

- **Not validated**: Whether downstream users find this ergonomic. Every call to `AlgEvaluate` needs `bot_val`. For `HAValid` and `BAValid`, `bot_val = ⊥` is hardcoded — but for `GHAValid`, the quantification over `bot_val` in the definition means the signature is heavier.
- **Counterargument not addressed**: TW's point that "making `⊥` an atom avoids the extra field" is only dismissed at the universal-algebra level. No one addresses what happens when a proof user writes `AlgEvaluate v bot_val (¬A)` and gets `bot_val ⇨ AlgEvaluate v bot_val A` — this is not `⊥ ⇨ A`, and may confuse consumers.

### A2. The "substitution invariance" argument for primitive `⊥` assumes that substitutions should be unconstrained
BBM's argument (MSG 604219492) that primitive `⊥` preserves substitution closure without side conditions is correct at the syntactic level. But:

- **Assumption**: That unconstrained substitution is the desirable semantics. TW's point is that in MPL, substitutions that *do not* preserve `⊥` are needed to prove IPL conservative over MPL. If `⊥` is primitive, these substitutions are simply not available in the algebra of formulas — you'd need to use the `WithBot` trick (which the codebase already uses in `intuitionisticCompletion`).
- **Not validated**: Whether the `WithBot` approach in `Defs.lean` (line 200: `Theory.intuitionisticCompletion`) is ergonomic or causes universe issues. Adding `WithBot` changes the atom type, which threads through every downstream type signature.

### A3. The `Bool` vs. `Prop` separation is justified by canonical models — but this justification is partial
BBM's explanation that `canonicalValuation` must be `Prop`-valued (MCS membership is not computable) is valid. However:

- **Not validated**: MD's counter-proposal (MSG 603538889) — use `noncomputable def canonicalValuation ... := fun p => decide (Proposition.atom p ∈ S)` — was dismissed as "more clumsy." The actual complexity cost was not measured. In Lean 4, `decide` on a `Prop` that uses `Classical.propDecidable` is already `noncomputable`, so the "decide" approach does not actually reduce classical axiom usage.
- **Not validated**: Whether having **four** semantics (`Evaluate`, `BoolEvaluate`, `IForces`, `AlgEvaluate`) creates an unacceptable maintenance burden. Every semantic lemma potentially needs four versions or a sufficiently general abstraction.

### A4. Thomas Waring's final message was cut off and his concern about the deletion is unknown
TW's MSG 605341190 ends with "btw Benjamin, why did you delete" — the message is truncated (probably over API limit). This is the most recent message and it appears TW is asking about a deletion of something from the branch. This question was not answered in the thread.

**Critical gap**: We do not know what was deleted, whether TW considers it a mistake, or whether it changes his position.

---

## Potential Pitfalls

### P1. Four-semantics proliferation
The codebase now has:
1. `Evaluate : (Atom → Prop) → Proposition Atom → Prop` — bivalent Prop semantics
2. `BoolEvaluate : (Atom → Bool) → Proposition Atom → Bool` — computable Bool
3. `IForces : KripkeModel → World → Proposition Atom → Prop` — Kripke/intuitionistic
4. `AlgEvaluate : (Atom → H) → H → Proposition Atom → H` — GHA/algebraic

Every time a new connective is added or modified, all four definitions need updating. This is a maintenance multiplier that the thread has not explicitly acknowledged as a cost. The GHA approach (TW's suggestion) was supposed to unify at least 1 and 2, but the current code implements them separately with a bridge lemma instead of deriving one from the other via GHA instance. This means the "unification" is de facto not achieved — two separate definitions coexist with a proof of their equivalence.

**Risk**: When DPLL work begins (MD's goal), a fifth definition may be added without connecting back to the others, further fragmenting the semantic ecosystem.

### P2. The `⊥`-as-primitive-constructor decision is architecturally irreversible at this stage
The codebase already has hundreds of lines of proofs depending on pattern matching on `.bot`. The existing ND system (`NaturalDeduction/Basic.lean`) also has `⊥` as a primitive case in `Derivation`. If TW's position (that `⊥` should not be a primitive for MPL) were accepted later, the refactor would require:
- Changing `Proposition` inductive
- Rewriting all pattern matches
- Redesigning `MPL`, `IPL`, `CPL` theory definitions
- Rewriting `Kripke.lean`, `Bool.lean`, `Algebra.lean`
- Updating all downstream modal/temporal logics that use the PL embedding

This decision should not be made without explicit sign-off from all active CSLib maintainers, particularly TW.

### P3. The modal embedding uses Lukasiewicz encodings for `and`/`or` — this is a semantic gap
`FromPropositional.lean` encodes `PL.and` as `¬(A → ¬B)` in modal logic, which is classically correct but intuitionistically wrong (MSG 604219492 mentions this; `Connectives.lean` line 29 also acknowledges it). But the codebase contains theorems like `tautology_iff_toModal_valid` that assert full coherence. This coherence holds only under classical modal semantics. If CSLib ever adds intuitionistic modal logic, this embedding becomes a soundness landmine.

**Risk**: No warning is placed at the module level in `FromPropositional.lean` that the embedding is classically scoped. The docstring says "targets classical modal logic" but this is easily overlooked by future contributors building on the embedding.

### P4. The `intuitionisticCompletion` trick may cause universe issues
`Defs.lean` line 200 adds `WithBot` to the atom type when constructing `intuitionisticCompletion`. This changes the type from `Theory Atom` to `Theory (WithBot Atom)`. Any proof that starts with `MPL` over atoms of type `X` and needs to reason about `IPL` over the same atoms now has a type mismatch. The existing code provides `instIsIntuitionisticIntuitionisticCompletion` but no lemma connecting derivability in the original MPL to derivability in the completion over `WithBot Atom`. This is a potential usability gap.

### P5. The `DerivationSystem` abstraction is duplicated, not shared
The `propDerivationSystem` in `ProofSystem/Derivation.lean` instantiates a `Metalogic.DerivationSystem` for PL. The NaturalDeduction system in `NaturalDeduction/Basic.lean` provides a separate `InferenceSystem T Sequent`. These are two independent abstraction hierarchies. The bridge (`NaturalDeduction/Equivalence.lean`) proves equivalence between them. But the original vision (TW's `DerivationSystem` class vs. BBM's Hilbert approach) has generated two parallel hierarchies rather than a unified one. This is technical debt that will complicate future contributors trying to understand "what is the canonical proof system for PL in CSLib?"

---

## Hidden Trade-offs

### T1. `bot_val` parameter makes `AlgEvaluate` non-canonical
The explicit `bot_val` parameter in `AlgEvaluate` means there is no unique "standard evaluation" in a GHA. Two evaluations that agree on atoms but differ on `bot_val` produce different values for `⊥`-containing formulas. This is correct for MPL but means there is no `simp` lemma `AlgEvaluate_neg` because `¬A = A → ⊥` evaluates to `v A ⇨ bot_val`, which depends on `bot_val`. The `Evaluate`-to-`AlgEvaluate` bridge would need: `Evaluate v φ ↔ AlgEvaluate (fun a => v a) False φ = True` — but this is not stated anywhere in the current code (checked `Semantics/Algebra.lean` and `Semantics/Bool.lean`).

**Hidden gap**: The bridge between `Evaluate` (bivalent) and `AlgEvaluate` (GHA) is missing, even though `Prop` with `False` as bottom is a `BooleanAlgebra` instance.

### T2. The `Prop`/`Bool` decision has downstream consequences for decidability
By keeping `Evaluate` as `Prop`-valued, the predicate `Tautology` is not computably decidable for infinite atom types. This is fine for metatheory but means `decide` cannot be used to prove concrete tautologies unless the atom type is finite and decidable. MD's use-case (DPLL) requires computable evaluation. The current setup correctly provides `BoolEvaluate` for this, but:
- There is no `decide`-based tactic for `Tautology` (would need a finite-atom decidability instance)
- The bridge `BoolEvaluate_eq_iff` is proven but there is no automation that makes `Tautology` instances computable in proofs

### T3. The thread conflates "which logic is primary" with "which formalization is canonical"
MD's remark (MSG 603877853) that calling it `Cslib.Logic.Structural` might be more appropriate acknowledges that the namespace `PL` commits to propositional logic as a named entity, rather than as an instance of a general structural logic. TW's ND system is already in CSLib without the `PL` namespace issue. BBM's refactoring introduces `PL` as the namespace, which is fine short-term but may conflict if CSLib later wants to provide, e.g., `IL` (implicational logic) or `BPL` (basic propositional logic) as named subsystems. The namespace choice is subtle but nearly irreversible once PRs are merged.

### T4. Two-layer deduction (ND + Hilbert) doubles the proof maintenance surface
TW's ND system was already in CSLib (his original contribution). BBM has added a Hilbert system and proved equivalence. This is theoretically elegant but means:
- Any future change to axioms or rules must be made in two systems
- Any future connective addition (e.g., adding `next` to get LTL) requires updating both
- The equivalence proof itself is a large body of code that must be maintained

The thread does not ask whether the dual-system architecture was a deliberate design choice or whether one system should be canonical with the other derived.

---

## Missing Perspectives

### M1. Ching-Tsun Chou's position is incomplete
MSG 603163993 mentions that **ctchou** commented on PR #648 suggesting that `Bool.lean` alone would suffice. But ctchou's actual argument is only summarized by BBM, not quoted. ctchou is presumably a core maintainer whose full position should be represented. The thread does not include ctchou's voice directly.

### M2. No discussion of `DecidableEq Atom` constraint
`Defs.lean` line 75 requires `[DecidableEq Atom]` throughout. The ND system in `Basic.lean` also requires it (for `Finset` operations on contexts). This constraint rules out certain atom types (e.g., `ℝ → Prop`). No one in the thread discusses whether this is the right generality boundary or whether some results hold without `DecidableEq`.

### M3. No discussion of universe polymorphism vs. large-type compatibility
`Defs.lean` uses `universe u` with `Atom : Type u`. The GHA semantics in `Algebra.lean` quantifies over `H : Type*`, which means it ranges over all universes. The completeness theorem in TW's branch involves `∀ H : Type u [GHA H] ...` — but if `H` is constrained to the same universe `u` as `Atom`, there may be universe limitations when `H` is the Lindenbaum algebra (which lives at a higher universe). This is a well-known issue in algebraic completeness proofs and was not discussed in the thread.

### M4. No discussion of interoperability with Mathlib's existing propositional logic
Mathlib contains `Mathlib.Logic.Propositional` and related files. The CSLib `Cslib.Logic.PL` namespace is parallel to Mathlib's existing infrastructure. If Mathlib's propositional logic library grows, there could be name conflicts or duplication. No one discusses the relationship to Mathlib's existing `PropCat`, `BoolAlgebra`-based completeness, or `Decidable`-based evaluators.

### M5. No discussion of proof term size / kernel efficiency
The Hilbert derivation tree (`DerivationTree`) is a `Type` (not `Prop`) to support computable height. This means proof terms for `Nonempty (DerivationTree ...)` carry the full tree structure. For large derivations (e.g., completeness witnesses), these trees can be very large. No one discusses whether this causes elaboration performance issues or whether the `Nonempty`/`Prop` wrapper adequately insulates the kernel from the tree size.

---

## Confidence Level

| Finding | Confidence |
|---------|-----------|
| Thread cut-off (TW's final message truncated) | **High** — confirmed by API data |
| Four-semantics proliferation risk | **High** — confirmed by codebase structure |
| Bridge between `Evaluate` and `AlgEvaluate` missing | **High** — searched `Algebra.lean` and `Bool.lean` |
| `⊥`-as-primitive decision is architecturally irreversible | **High** — hundreds of pattern matches already committed |
| Lukasiewicz modal embedding is classically scoped | **High** — documented in `FromPropositional.lean` |
| `intuitionisticCompletion` `WithBot` ergonomics gap | **Medium** — identified structurally, not stress-tested |
| Universe polymorphism risks in GHA completeness | **Medium** — known issue in algebraic logic, not confirmed present |
| Namespace `PL` vs. structural logic concerns | **Low** — speculative about future conflicts |
| Mathlib interoperability | **Low** — Mathlib PL library is thin; risk is future-facing |

---

## Summary of Critical Questions for the Thread Response

The response to the Zulip thread should explicitly address:

1. **What did Thomas Waring's message refer to** ("why did you delete...")?  The truncated MSG 605341190 contains an unresolved question that must be answered.

2. **Is the dual-system architecture (ND + Hilbert) an explicit design choice?** Or did it happen incrementally? What is the canonical PL proof system in CSLib going forward?

3. **Is the `AlgEvaluate`-to-`Evaluate` bridge documented somewhere?** The relationship `Evaluate v φ ↔ AlgEvaluate (fun a => v a) False φ = True` appears to be missing from the codebase.

4. **What is the intended scope of the modal embedding?** Should `FromPropositional.lean` carry a more prominent warning that it is classically scoped and breaks under intuitionistic semantics?

5. **Was ctchou's position on the PR fully represented?** The thread mentions his comment but does not quote it; his recommendation may carry significant weight.
