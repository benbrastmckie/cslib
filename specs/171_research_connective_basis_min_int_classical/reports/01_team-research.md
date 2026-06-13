# Research Report: Task #171

**Task**: Research connective-basis design for minimal, intuitionistic, and classical propositional logic
**Date**: 2026-06-12
**Mode**: Team Research (4 teammates, standard mode)
**Completed**: 2026-06-12

---

## Summary

- **The {imp, bot} basis is classically complete but intuitionistically deficient.** The non-interdefinability of intuitionistic connectives is a proved theorem (Wajsberg 1938, McKinsey 1939, stated by Heyting 1930). The PR #635 claim that this basis is "standard in the literature" for intuitionistic logic is mathematically wrong: Heyting, Gentzen, Prawitz, and Troelstra & van Dalen all used full connective sets {∧, ∨, →, ⊥} as primitives.
- **The code is internally consistent but its scope claims are overclaimed.** The CSLib implementation itself is the strongest evidence: `andE1`, `andE2`, and `orE` in `DerivedRules.lean` all require `[IsClassical T]`. This means CSLib's "intuitionistic logic with ∧ and ∨" is actually classical logic — the derived connectives are classical abbreviations only.
- **The committed architecture ({atom, bot, imp} across all four formula types) should be preserved.** Changing constructors would invalidate bimodal embeddings and all downstream completed work. The correct fix is scoped documentation revision and two targeted structural repairs.
- **Two genuine structural bugs exist.** The `botE` rule in `NaturalDeduction/Basic.lean` is a primitive unconditionally available to all logics, making "minimal logic" derivations actually intuitionistic. The Johansson 1937 reference is absent from `references.bib` despite `MinimalHilbert` being named for his system.
- **PR #635 needs corrected citations and a restated scope claim.** Remove Heyting/Gentzen/Prawitz/Troelstra-van Dalen as supporting references for the {imp, bot} basis; retain Church 1956 and Chagrov & Zakharyaschev 1997 for the classical adequacy claim; restrict the "functionally complete" claim to classical logic explicitly.

---

## Key Findings

### Literature Verification (from Teammate A)

**High confidence across all sub-findings.**

The classical adequacy of {→, ⊥} is genuine and well-established: ¬A := A → ⊥, A ∨ B := (A → ⊥) → B, A ∧ B := (A → (B → ⊥)) → ⊥, and ⊤ := ⊥ → ⊥ are all classically valid definitions. Church 1956 and Chagrov & Zakharyaschev 1997 are appropriate citations for this claim.

The intuitionistic inadequacy is not a matter of convention but a proved theorem. The Stanford Encyclopedia of Philosophy states directly that the four connectives of IPC are "logically independent over IPC" and "none of the basic connectives can be dispensed with." The standard IPC formulation uses {→, ∧, ∨, ⊥} as primitives with ¬A abbreviating A → ⊥. The non-interdefinability was stated by Heyting 1930 himself and proved formally by Wajsberg 1938 and McKinsey 1939.

The literature audit of PR #635's cited sources is definitive:

| Author | What They Actually Used | Appropriate Citation For? |
|--------|------------------------|---------------------------|
| Heyting 1930 | Full {∧, ∨, →, ¬} as primitives; 11 axioms covering all connectives separately | NOT {imp, bot} basis; Heyting explicitly proved non-interdefinability |
| Gentzen 1935 (NJ) | All connectives with independent intro/elim rules: ∧I, ∧E₁, ∧E₂, ∨I₁, ∨I₂, ∨E, →I, →E, ⊥E | NOT {imp, bot} basis; ctchou attached the actual paper as PR evidence |
| Prawitz 1965 | "Twelve rules, one Introduction and one Elimination rule for each of the six logical connectives" | NOT {imp, bot} basis |
| Troelstra & van Dalen 1988 | Full {→, ∧, ∨, ⊥} with ¬A := A → ⊥ | NOT {imp, bot} basis |
| Church 1956 | {→, ⊥} basis for classical Hilbert-style axiomatization | YES — classical adequacy claim |
| Chagrov & Zakharyaschev 1997 | Modal logic; classical propositional background | YES — classical and modal context |

The CSLib code confirms the inadequacy directly: `DerivedRules.lean` lines 143, 174, and 232 gate `andE1`, `andE2`, and `orE` on `[IsClassical T]`. The module header (lines 28-36) explicitly states that elimination rules "require [IsClassical T]" because "the Lukasiewicz encoding of these connectives is only classically equivalent to their standard definitions." This is an internal admission that the {imp, bot} encoding is only classically adequate.

The "5 rules instead of 10" framing of PR #635 holds only for the classical system. For the intuitionistic system, the introduction rules are derivable (andI, orI1, orI2) but the elimination rules require classical axioms — so the claim is at best true classically and misleading in the intuitionistic context.

Minimal logic (Johansson 1937) uses the same full connective syntax as IPC: {→, ∧, ∨, ⊥} with ¬A := A → ⊥. The distinction from IPL is the absence of ex falso quodlibet, not a restriction to a smaller connective set.

---

### Architecture Alternatives (from Teammate B)

**High confidence on architecture comparison; medium confidence on botE semantics.**

Teammate B surveyed four options and concluded that Option A (current PR #635 approach: {atom, bot, imp} with `abbrev` derived connectives) is the correct choice for CSLib's purposes, with targeted repairs.

**Option A (current)**: Lean 4's `abbrev` mechanism gives derived connectives definitional equality to their {imp, bot} encodings. This means `simp` and `grind` see through them without any bridging lemmas — a significant practical advantage. Inductive proofs over `Proposition` have 3 cases instead of 5 or more. The pattern is already uniform across all four formula types (PL/Modal/Temporal/Bimodal).

**Option B (full {atom, bot, imp, and, or} constructors)**: Would require refactoring all four formula types, all semantic functions, and all existing proofs. Every recursion and induction gains 2 cases. The bimodal formula type would reach 6 constructors. This approach contradicts the established CSLib pattern and would require proving `and_simp : A.and B = imp (imp A (imp B bot)) bot` to connect constructors with existing Lukasiewicz definitions.

**Option C (typeclasses)**: Already implemented in `Connectives.lean`. The `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, and `BimodalConnectives` typeclasses provide polymorphic axiom definitions used throughout `Foundations/Logic/Axioms.lean`. PR #607's Operators/ directory proposal is an *extension* of this approach (per-operator simp lemma files), not a replacement.

**Option D (Mathlib algebraic classes)**: Inappropriate for formula types. Mathlib's `HeytingAlgebra` requires a bounded distributive lattice structure; CSLib formula types are free algebras over atoms. Mathlib's `HImp` is the Heyting arrow defined as `a ⇨ b = sSup {c | c ⊓ a ≤ b}` — semantically different from syntactic implication. Eric-wieser's suggestion to co-opt `Bot`, `HImp`, `Sup`, `Inf` would create confusion between syntactic and algebraic structure.

The `botE` inconsistency (confirmed high confidence): `NaturalDeduction/Basic.lean` includes `botE` as an unconditional primitive constructor in `Theory.Derivation`, available to all three logics. This means `MPL := ∅` theorems proved with `botE` are actually intuitionistic theorems, not genuinely minimal. The Hilbert system in `Derivation.lean` handles this correctly via the axiom predicate hierarchy; the natural deduction system does not.

---

### Gaps and Shortcomings (from Critic, Teammate C)

**High confidence across all findings.**

The Critic's assessment confirms and sharpens the literature verdict with direct Kripke counterexamples.

**Counterexample for ∧**: Consider two worlds w₀ ≤ w₁ where both p and q are forced at w₁ but not at w₀. Standard p ∧ q fails at w₀. But CSLib's ¬(p → ¬q) is forced at w₀ because p → ¬q fails at w₀ (witness: w₁ where p holds but ¬q fails). This demonstrates a world where CSLib's `A ∧ B` is forced but standard `A ∧ B` is not — the two formulas have genuinely different semantics in IPC.

**Counterexample for ∨**: In a world w₀ ≤ w₁ with p forced at w₁ and q unforced everywhere, standard p ∨ q fails at w₀ (neither is forced there) but CSLib's ¬p → q is vacuously true at w₀ (since ¬p fails at w₀ because p is forced at a successor). The CSLib ∨ definition has more "true" instances than standard ∨ in IPC.

**Gap 1 (Connective mismatch)**: The `int_soundness_completeness` theorem in `IntCompleteness.lean` is correct — but it is really about the {→, ⊥} fragment of IPC, not about a full intuitionistic propositional logic with standard ∧ and ∨. The formula type only has three constructors, so ∧ and ∨ in any completeness theorem are the classical abbreviations.

**Gap 2 (Disjunction property)**: The disjunction property (if ⊢ A ∨ B then ⊢ A or ⊢ B) is the hallmark of IPC. Under CSLib's encoding where A ∨ B := ¬A → B, this property becomes: if ⊢ (¬A → B) then ⊢ A or ⊢ B, which fails classically (take A = ¬p, B = p: ¬¬p → p is classically valid but neither ¬¬p nor p is a theorem). The disjunction property is absent from CSLib's stated theorems.

**Gap 3 (Negation ambiguity)**: ¬φ := φ → ⊥ has different behavior across the three logics (in MPL ⊥ does not explode, in IPL it does via EFQ, in CPL double-negation elimination holds) but this is underdocumented.

**Gap 4 (IsClassical constraint for ∧/∨ elimination)**: In standard IPC, `p ∧ q ⊢ p` is an axiom. In CSLib, deriving `p ∧ q ⊢ p` requires `[IsClassical T]` because `andE1` has that constraint. This means CSLib's "intuitionistic logic with ∧" is operationally indistinguishable from classical logic for ∧/∨ reasoning.

The Critic's overall verdict: the codebase is internally consistent and compiles correctly. The problem is a claim-reality mismatch. The code proves correct theorems about the formulas it actually has ({→, ⊥} with classical ∧/∨ abbreviations); the documentation and PR description claim more than what is formalized.

---

### Strategic Horizons (from Teammate D)

**High confidence on architecture status and roadmap alignment; medium on PR #607 collaboration timeline.**

The {atom, bot, imp} basis is not a pending decision — it is the committed architecture for all four formula types. Changing it would require rewriting the bimodal embedding work (PropositionalEmbedding, ModalEmbedding, TemporalEmbedding) documented in ROADMAP.md as complete. The cost is prohibitive.

The Johansson hierarchy is already encoded: `MinimalHilbert → IntuitionisticHilbert → ClassicalHilbert` in `ProofSystem.lean` is exactly the three-level hierarchy, with formula types shared and logics distinguished by axioms. The `Connectives.lean` typeclass infrastructure scales cleanly: new logics add formula type instances and axiom predicates without touching the connective hierarchy.

The roadmap principle "every component lives at the most general level it can compile at" supports the {bot, imp} basis: it is the most general (minimal) basis from which classical logic is derived by adding axioms. Adding and/or as primitives would bake classical information into the syntax.

The botE inconsistency confirmed: `NaturalDeduction/Basic.lean` comment describes `botE` as a primitive (ex falso quodlibet), and the roadmap shows this module is active. Genuine minimal logic natural deduction requires either a parameterized derivation type or a separate `Minimal.Derivation`.

On PR #607 and eric-wieser's Mathlib suggestion: Teammate D recommends prioritizing reconciliation with Montesi's approach. The `HasBot`/`HasImp` classes overlap with Mathlib's `Bot`/`HImp` but serve different purposes — the Mathlib alignment is not recommended for syntax-level formula types (same conclusion as Teammate B).

---

## Synthesis

### Conflicts Resolved

**Conflict 1: "Architecture is adequate for intuitionistic logic" (B, D) vs. "Architecture is inadequate for genuine IPC" (A, C)**

Resolution: Both claims are true simultaneously but about different things. Teammates B and D are correct that the architecture — specifically the formula type with {atom, bot, imp} constructors and the proof-system-level logic stratification — is correct and should be preserved. Teammates A and C are correct that the derived ∧/∨ connectives do not give genuine intuitionistic ∧/∨; the elimination rules require [IsClassical T]. The reconciliation is: CSLib's "intuitionistic logic" is the {→, ⊥} fragment of IPC with classical ∧/∨ abbreviations for notational convenience. This is mathematically consistent but must be documented accurately.

The formula type and architecture decisions (B, D) stand. The PR description and citation claims (A, C) need correction. There is no contradiction between these positions once the scope of each claim is properly stated.

**Conflict 2: "5 rules is an economy" (PR #635) vs. "10 rules is standard and necessary" (ctchou)**

Resolution: Both are correct in different scopes. 5 rules (ax, ass, impI, impE, botE) is genuine economy for the classical system. For the intuitionistic system with standard ∧/∨, 9-10 rules is the standard and is necessary because the connectives are genuinely independent. CSLib has traded genuine intuitionistic ∧/∨ for a compact formula type. This is a legitimate design choice, not an error, provided it is clearly documented.

**Conflict 3: "botE is fine as a primitive" vs. "botE makes minimal ND actually intuitionistic"**

Resolution: Teammate B raised this at medium confidence; Teammate D confirmed it at high confidence with direct code evidence. The `Derivation` comment in `Basic.lean` explicitly lists `botE` as a primitive rule. `MPL := ∅` derivations using `botE` are intuitionistic, not minimal. This is a genuine inconsistency between the Hilbert system (which correctly parameterizes via `MinPropAxiom/IntPropAxiom`) and the natural deduction system (which includes `botE` unconditionally). Resolution: this needs a structural fix (see Recommendations).

No conflicts between Teammates A and C — they reached the same conclusions from different angles (literature review vs. direct code analysis and Kripke counterexamples).

### Coverage Gaps

**Gap 1 (Completeness theorems scope)**: The completeness theorems (`int_soundness_completeness`, `min_soundness_completeness`) are correct as stated but represent completeness for the {→, ⊥} fragment of the respective logics. Whether CSLib intends to formalize full IPC (with genuine ∧/∨) or only this fragment is not explicitly stated in the roadmap or architecture documentation. This should be clarified.

**Gap 2 (Disjunction property)**: None of the four teammates investigated whether a disjunction property theorem exists or is provable for the CSLib encoding. For the {→, ⊥} fragment this is moot; if full IPC with standard ∧/∨ is ever added, this would become a key verification target.

**Gap 3 (Johansson 1937 citation)**: Confirmed missing by A and D. No teammate investigated whether additional citations are absent; the Johansson gap is the only confirmed missing entry.

**Gap 4 (PR #607 current state)**: Teammate B confirmed that the Operators/ directory does not exist on the current `pr3/temporal-syntax` branch. The interaction with PR #607 (Montesi's typeclass approach) depends on PR merge timing, which is not knowable from code inspection.

### Recommendations

The following recommendations are ordered by urgency and scope.

#### (a) PR #635 Description and Citations — Immediate

1. **Remove** Heyting 1930, Gentzen 1935, Prawitz 1965, and Troelstra & van Dalen 1988 from the list of citations supporting the {imp, bot} basis. These authors used full connective sets and did not use this basis for intuitionistic or minimal logic. Including them as support inverts their actual position.

2. **Restrict** the "functionally complete" claim explicitly to classical propositional logic. Change "since {imp, bot} is functionally complete for classical logic" wherever it appears without the classical qualifier.

3. **Retain** Church 1956 and Chagrov & Zakharyaschev 1997 as appropriate citations for the classical adequacy of {→, ⊥}.

4. **Add** a sentence clarifying the scope: "This gives a compact formula type adequate for classical propositional logic; for the {→, ⊥} fragment of intuitionistic and minimal logic, the system is also correct, but ∧ and ∨ elimination require classical axioms ([IsClassical T]) because the Lukasiewicz encodings are classical abbreviations."

5. **Change** the "5 rules instead of 10" framing to: "5 primitive rules adequate for classical propositional logic; the introduction rules for ∧ and ∨ are derivable in all three logics, but the elimination rules require classical axioms."

#### (b) Formula-Type Architecture Decision — Keep Option A, Document Scope

The formula type `{atom, bot, imp}` with `abbrev` derived connectives is the correct long-term architecture. Do NOT add and/or as constructors. The reasoning:

- The architecture is already deployed uniformly across all four formula types (PL/Modal/Temporal/Bimodal) with validated completeness results.
- `abbrev` provides definitional equality, meaning `grind`/`simp` handle derived connectives without bridging lemmas.
- Adding and/or constructors would require refactoring all four formula types, their semantic functions, all existing proofs, and the bimodal embedding — prohibitive cost for work already completed.
- The three-logic stratification is correctly handled at the proof-system layer (MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert), not the formula layer.

**Required documentation addition**: The `Connectives.lean` module docstring and any architecture overview should clearly state: "CSLib formalizes the {→, ⊥} fragment of minimal and intuitionistic logic, plus full classical propositional logic. The connectives ∧ and ∨ are defined as classical abbreviations using the Lukasiewicz convention; their elimination rules require classical axioms. Full intuitionistic or minimal logic with standard ∧ and ∨ (in the Gentzen/Prawitz/Heyting sense) is not the intended scope."

#### (c) botE / Minimal Logic Fix — Structural Repair Needed

The `NaturalDeduction/Basic.lean` derivation type includes `botE` (ex falso quodlibet) as an unconditional primitive inference rule, making all three natural deduction logics share the same derivation type with EFQ built in. This means `MPL := ∅` derivations that use `botE` are intuitionistic, not minimal.

**Recommended fix**: Use Option C from Teammate D — keep the current derivation type for intuitionistic/classical use and add a separate `Minimal.Derivation` that omits `botE`, parallel to the existing Hilbert-system distinction between `MinPropAxiom` and `IntPropAxiom`. The three logics then have separate derivation types sharing the formula type, consistent with `ProofSystem.lean`'s typeclass pattern.

If a separate derivation type is impractical in the short term: add a documentation note to `NaturalDeduction/Basic.lean` that the current derivation type is intuitionistic (not minimal), and that `Theory.Derivation MPL` with `botE` available is actually IPL-strength reasoning.

#### (d) references.bib Addition — Required

Add the Johansson 1937 entry to `references.bib`:

```bibtex
@article{Johansson1937,
  author       = {Johansson, Ingebrigt},
  title        = {Der Minimalkalk{\"u}l, ein reduzierter intuitionistischer Formalismus},
  journal      = {Compositio Mathematica},
  volume       = {4},
  pages        = {119--136},
  year         = {1937},
}
```

Add `\cite{Johansson1937}` to the docstrings of `Connectives.lean` and `ProofSystem.lean` wherever `MinimalHilbert` or `MPL` (minimal propositional logic) is introduced. `MinimalHilbert` is named directly after Johansson's calculus.

#### (e) PR #607 (Montesi) Reconciliation — Collaborative Approach

Teammate B confirmed that the Operators/ directory from PR #607 does not exist on the current branch. The current `Connectives.lean` typeclass architecture is already "Option C" in spirit — the PR #607 proposal would extend it with per-operator simp/grind lemma files.

The key alignment points:

1. The current `abbrev` approach and the PR #607 `def`-with-simp-lemmas approach are compatible: if PR #607 arrives, simp lemmas should be oriented in the direction **into** notation (not away from it), per the `chenson2018` review comment. Example: `@[simp] theorem neg_def [PropositionalConnectives F] (A : F) : neg' A = HasImp.imp A HasBot.bot` (unfolding raw typeclass form into notation).

2. Eric-wieser's suggestion to co-opt Mathlib's `Bot`, `HImp`, `Sup`, `Inf` classes should be declined for formula types. Mathlib's `HImp` carries lattice-algebraic semantics incompatible with syntactic proof-theoretic usage. CSLib's `HasBot`/`HasImp` classes are more appropriate. Document this decision explicitly in `Connectives.lean` to preempt future requests.

3. Coordinate with Montesi before further architecture changes: if PR #607 has a merge ETA, sync the connective typeclass design with Montesi's proposed Operators/ layout before committing additional per-operator infrastructure.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary: Literature verification and connective-basis truth | completed | high |
| B | Alternatives: Architecture options and code survey | completed | high (architecture); medium (botE semantics, PR #607) |
| C | Critic: Gaps, Kripke counterexamples, claim-reality mismatch | completed | high |
| D | Horizons: Strategic direction, roadmap alignment, long-term implications | completed | high (architecture, roadmap); medium (PR #607 timeline) |

---

## References

**Primary literature (verified in this research)**:
- Church, Alonzo. *Introduction to Mathematical Logic*. Princeton University Press, 1956. (Church1956 — appropriate for classical {→, ⊥} basis)
- Heyting, Arend. "Die formalen Regeln der intuitionistischen Logik." *Sitzungsberichte der Preußischen Akademie der Wissenschaften*, 1930. (Heyting1930 — used full {∧, ∨, →, ¬} primitives; proved non-interdefinability)
- Gentzen, Gerhard. "Untersuchungen über das logische Schließen." *Mathematische Zeitschrift*, 1935. (Gentzen1935 — NJ uses all connectives as primitives with independent rules)
- Prawitz, Dag. *Natural Deduction: A Proof-Theoretical Study*. Almqvist & Wiksell, 1965. (Prawitz1965 — twelve rules, all connectives primitive)
- Troelstra, A.S. and van Dalen, D. *Constructivism in Mathematics*, Vol. 1. North-Holland, 1988. (not appropriate for {imp, bot} claim)
- Chagrov, A. and Zakharyaschev, M. *Modal Logic*. Oxford University Press, 1997. (Chagrov-Zakharyaschev1997 — modal logic background, classical propositional logic as base)
- **Johansson, Ingebrigt. "Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus." *Compositio Mathematica* 4, 1937, pp. 119-136. (MISSING from references.bib — must add as Johansson1937)**

**Non-interdefinability proofs**:
- Wajsberg, M. (1938) — formal proof that intuitionistic connectives are not inter-definable
- McKinsey, J.C.C. (1939) — independent formal proof of same result

**CSLib codebase files directly relevant**:
- `Cslib/Foundations/Logic/Connectives.lean` — typeclass architecture
- `Cslib/Logics/Propositional/Defs.lean` — MPL/IPL/CPL definitions, Lukasiewicz abbrevs
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` — MinPropAxiom / IntPropAxiom / PropositionalAxiom
- `Cslib/Logics/Propositional/ProofSystem/DerivedRules.lean` — andE1/andE2/orE with [IsClassical T] constraints
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — botE as unconditional primitive
- `Cslib/Foundations/Logic/ProofSystem.lean` — MinimalHilbert / IntuitionisticHilbert / ClassicalHilbert hierarchy

**External references**:
- Stanford Encyclopedia of Philosophy, "Intuitionistic Logic" (consulted June 2026) — confirms connective independence
- Wikipedia, "Functional Completeness" — confirms {→, ⊥} is functionally complete for classical logic only
