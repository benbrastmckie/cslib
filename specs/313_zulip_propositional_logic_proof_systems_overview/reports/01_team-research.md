# Research Report: Task #313

**Task**: Zulip propositional logic proof systems overview
**Date**: 2026-06-23
**Mode**: Team Research (4 teammates)

## Summary

CSLib's propositional logic formalizes **two mature proof systems** (Hilbert and Natural Deduction) with a **third** (Tableau Calculus) as generic infrastructure in `Foundations/`. There is no Gentzen-style sequent calculus (LK/LJ) for propositional logic — the task description's mention of "Sequent Calculus" is inaccurate. All three systems cover a shared three-tier logic hierarchy (MPL/IPL/CPL), and both mature systems are entirely sorry-free. The Zulip comment should accurately present what exists, highlight the architectural decisions (theory-parameterized logic strength, efq as theory axiom), and frame the systems as complementary tools rather than competing formalisms.

## Key Findings

### Conflict Resolution: Two or Three Systems?

**Conflict**: Teammates A, B, C found exactly two proof systems (Hilbert + ND) and no sequent calculus. Teammate D found a third system — a generic **Tableau Calculus** in `Foundations/Logic/Tableau/` with 8 classical propositional expansion rules following Smullyan's uniform notation.

**Resolution**: Both are correct. CSLib has:
1. **Hilbert system** (`ProofSystem/`) — fully mature, complete metalogic
2. **Natural Deduction** (`NaturalDeduction/`) — strong combinatorial system with algebraic bridges
3. **Tableau Calculus** (`Foundations/Logic/Tableau/` + `PropositionalTableau.lean`) — generic infrastructure, logic-neutral, shared across logics

The task description's "Sequent Calculus" should be corrected to "Tableau Calculus" in the Zulip post. A Gentzen LK/LJ sequent calculus is planned (task 279) but not yet started.

### System 1: Hilbert System (Fully Mature)

**Location**: `Cslib/Logics/Propositional/ProofSystem/`

Three axiom tiers: `MinPropAxiom` (8), `IntPropAxiom` (9), `PropositionalAxiom` (10). Parameterized `DerivationTree Axioms Γ φ` with `List`-based contexts.

**Completed results**:
- Deduction theorem (well-founded recursion on tree height)
- Soundness (Boolean valuations)
- Strong completeness for all three tiers (CPL via Boolean/MCS, IPL/MPL via Kripke canonical models)
- Compactness (all three tiers)
- Algebraic completeness: MPL ↔ GHA-validity, IPL ↔ HA-validity, CPL ↔ BA-validity
- Glivenko's theorem: CPL ⊢ φ → IPL ⊢ ¬¬φ
- Conservative extension: IPL over MPL for bot-free formulas
- Decidability: `Decidable (Derivable PropositionalAxiom phi)` for finite atom types

**Best suited for**: Metalogical theorems (MCS construction, algebraic correspondence), completeness proofs where the deduction theorem is the key workhorse.

### System 2: Natural Deduction (Core Complete, Proof Theory Gaps)

**Location**: `Cslib/Logics/Propositional/NaturalDeduction/`

Standalone `Theory.Derivation` with 10 primitive constructors, `Finset`-based contexts (no explicit contraction/exchange). Theory parameter controls logic strength.

**Design decision**: EFQ (`⊥ → A`) is a theory axiom via `[IsIntuitionistic T]`, not a primitive constructor. This enables API uniformity across MPL/IPL/CPL while preserving ND symmetry. Documented in `Basic.lean` with reference to the existing Zulip discussion.

**Completed results**:
- Weakening, cut, substitution, atom substitution
- Equivalence relation on propositions
- ND algebraic completeness (GHA/HA/BA via Lindenbaum-Tarski algebra)
- Glivenko and conservative extension corollaries (via algebraic bridges)
- Full bidirectional equivalence with Hilbert system (`hilbert_iff_nd_ctx`)

**Notable gaps** (Critic finding):
- No normalization theorem (Prawitz-style) — task 290, not started
- No subformula property — blocked on normalization
- No Curry-Howard correspondence — task 293, blocked on normalization
- Semantic completeness goes through Hilbert bridge, not proved independently

**Best suited for**: Proof-theoretic analysis, derivation search, equational reasoning via `Theory.equiv`, structured derivation trees, connection to `InferenceSystem` typeclass.

### System 3: Tableau Calculus (Generic Infrastructure)

**Location**: `Cslib/Foundations/Logic/Tableau/` + `Cslib/Foundations/Logic/PropositionalTableau.lean`

Generic signed tableau infrastructure: `Sign`, `SignedFormula`, `RuleResult`, `Branch`, `ClosureCondition`. 8 standard classical propositional expansion rules following Smullyan's uniform notation. Logic-neutral design — instantiable for classical, intuitionistic, minimal, modal, and temporal logics.

**Best suited for**: Decision procedures, refutation calculi, mechanically computable proof search, automated reasoning. The logic-neutral design means this infrastructure is reused across the modal/temporal tower.

### Bridges and Semantic Layer

**Hilbert ↔ ND equivalence** (`Equivalence.lean`):
- `hilbert_iff_nd_ctx`: Primary generic form with `MinimalAxioms` typeclass
- `hilbertToND`: Computable structural translation (Hilbert → ND)
- `ndToHilbert`: Noncomputable (uses classical deduction theorem, ND → Hilbert)
- Six named corollaries for all three tiers (closed and context forms)

**Algebraic semantic hub** (`Semantics/Algebra/`):
- Serves as common semantic layer connecting both proof systems to each other and to Kripke semantics
- Three algebraic bridges: `derivableInMplIffDerivableMin`, `derivableInIplIffDerivableInt`, `derivableInCplIffDerivableProp`
- Bool evaluator and Prop evaluator unified as instances of `AlgEvaluate`

**Kripke–algebraic bridge** (`KripkeBridge.lean`):
- `kripkeAlgBridge`: Kripke forcing ↔ algebraic evaluation via upset algebra

### Zero-Sorry Status

An exhaustive grep confirms zero `sorry` markers in the entire propositional logic development. Both mature proof systems are completely verified. This is a genuinely strong claim worth highlighting in the Zulip post.

### What the Post Must NOT Claim

1. Three *completed* proof systems (Tableau is infrastructure, not a full proof system with soundness/completeness)
2. That ND has normalization or the subformula property
3. That IPL or MPL have decidability instances (only CPL does)
4. That ND has independent semantic completeness proofs (these route through Hilbert)
5. "Sequent Calculus" when it's actually Tableau Calculus

## Synthesis

### Recommended Zulip Comment Structure (400-600 words)

**Opening**: Lead with the architectural decision — theory-parameterized logic strength unifying MPL/IPL/CPL under one framework — rather than listing systems.

**Section 1: The propositional foundation** (3-5 sentences)
- Formula type with primitives, neg/top/biconditional derived
- Three theories parameterize logic strength
- EFQ design decision (reference existing Zulip discussion)

**Section 2: The proof systems** (one paragraph each)
- Hilbert: axiom schemata, metalogical results, completeness suite
- ND: 10-constructor inductive, structural rules, algebraic completeness
- Tableau: generic infrastructure in Foundations/, Smullyan's uniform notation, logic-neutral

**Section 3: The bridges** (2-4 sentences)
- `hilbert_iff_nd` formal equivalence
- Algebraic completeness as semantic hub (GHA/HA/BA)
- Glivenko's theorem and conservative extension

**Section 4: What this enables** (3-5 sentences)
- Base of the Modal/Temporal/Bimodal tower
- Tableau infrastructure reused for modal logic
- `InferenceSystem` typeclass for extensibility
- CSLib fills a genuine gap: Mathlib has propositional *tactics* but not formalized *object-level* proof systems

**Section 5: Future directions** (2-3 sentences)
- Sequent calculus (LK/LJ) planned
- First-order logic as natural next step
- Invitation for contributions

### Tone Guidance

- Write as a practitioner sharing interesting work, not a catalog
- Celebrate genuinely impressive results (zero-sorry, full completeness suite) without overclaiming
- Acknowledge the efq design decision (already on record in Zulip)
- Be honest about what's complete vs. planned

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary: system catalog | completed | high |
| B | Bridges and connections | completed | high |
| C | Critic: gaps and risks | completed | high |
| D | Horizons: strategic framing | completed | high |

## References

- `Cslib/Logics/Propositional/Defs.lean` — Architecture overview
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — ND system with efq design discussion
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` — Hilbert ↔ ND bridge
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` — Axiom hierarchy
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` — CPL completeness + decidability
- `Cslib/Logics/Propositional/Semantics/Algebra/` — Algebraic semantic hub
- `Cslib/Foundations/Logic/Tableau/` — Generic tableau infrastructure
- `Cslib/Foundations/Logic/PropositionalTableau.lean` — Propositional tableau rules
