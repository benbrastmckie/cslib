# Teammate D Findings: Horizons / Strategic Vision

**Role**: Articulate the WHY behind four proof systems and the long-term trajectory.
**Artifact**: `02_teammate-d-findings.md`

---

## The Core Thesis

The question "why four proof systems?" has a crisp answer: each formalism exposes a distinct structural dimension of propositional logic that the others conceal. The equivalence theorems between them are not redundant — they are the machinery that lets results discovered in one system's natural habitat migrate freely to all others.

CSLib's propositional logic layer is being built around this principle. The current state (June 2026) represents the first completed pass of this vision: two proof systems are fully verified, two are newly complete, and the unifying equivalence layer is in active construction.

---

## What Actually Exists Now (Updated Picture)

The first-round research synthesis (file `01_team-research.md`) was accurate as of its writing, but the task list has advanced. The current state is:

**Four distinct proof systems**:

1. **Hilbert System** (`ProofSystem/`) — fully mature with complete metalogic suite
2. **Natural Deduction** (`NaturalDeduction/`) — complete with algebraic bridges and Hilbert equivalence
3. **Sequent Calculus LJ** (`SequentCalculus/LJ/`) — task 315 COMPLETED; full cut elimination + soundness + completeness + IPL/MPL equivalence bridges
4. **Sequent Calculus LK** (`SequentCalculus/LK/`) — task 314 IMPLEMENTING; cut elimination done, soundness/completeness in progress
5. **Tableau Calculus** (`Tableau/`) — three variants (Classical, Intuitionistic, Minimal) with decision procedures; soundness/completeness in progress (tasks 316/317)

**Cross-system equivalences**:
- Task 291 (IMPLEMENTING): Three-way TFAE for CPL (Hilbert ↔ ND ↔ LK) and IPL (Hilbert ↔ ND ↔ LJ); all pairwise bridges already exist in the codebase

**Zulip post note**: The synthesis document's claim that "Sequent Calculus" should be corrected to "Tableau Calculus" is now itself outdated. CSLib has both. The post should reflect the full four-system architecture.

---

## Strategic Roles: Why Each System?

### Hilbert System: The Algebraic Hub

The Hilbert system's defining feature is its connection to algebra. With only modus ponens as an inference rule and 8–10 axiom schemata, soundness for a new semantics requires checking only finitely many axiom patterns. This makes the Hilbert system the natural home for algebraic completeness results.

**What CSLib demonstrates**:
- MPL complete w.r.t. `GeneralizedHeytingAlgebra` (GHA-validity)
- IPL complete w.r.t. `HeytingAlgebra` (HA-validity)
- CPL complete w.r.t. `BooleanAlgebra` (BA-validity)

These completeness results are **not just observations** — they are the mechanism for the conservative extension chain. Algebraic completeness is what makes `hilbertIplConservativeOverMpl` work: to show IPL conservative over MPL for bot-free formulas, the proof routes through the `WithBot` construction on generalized Heyting algebras. No other proof system makes this algebraic maneuver as transparent.

The Lindenbaum algebra construction (`Semantics/Algebra/Lindenbaum.lean`) is perhaps the most elegant illustration: the quotient of `Proposition Atom` by T-equivalence is literally a `GeneralizedHeytingAlgebra` for any theory T, a `HeytingAlgebra` when T is intuitionistic, and a `BooleanAlgebra` when T is classical. This algebraic identity — provability and order structure coincide — is formalized and checkable.

**Best for**: Algebraic completeness, conservative extension proofs, Glivenko's theorem, Hilbert algebra typeclass hierarchy, inter-logic structural theorems.

### Natural Deduction: The Computational Substrate

Natural deduction's structural advantage is that derivations are *programs*. The Curry-Howard correspondence (task 293, planned) makes this precise: ND proofs for IPL correspond to simply-typed lambda calculus terms, ND proofs for MPL correspond to terms in a system without bottom elimination.

Before that correspondence is formalized, ND already provides computational content through:
- 10-constructor inductive type with explicit derivation trees (not just a derivability predicate)
- `Finset`-based contexts (no explicit contraction/exchange — they are free)
- `Theory.equiv` as a computable equivalence relation on propositions

The EFQ design decision is strategically important here. By making ex falso quodlibet a theory axiom via `[IsIntuitionistic T]` rather than a primitive constructor, the `Derivation` type is genuinely minimal — it captures exactly the constructive core without presupposing any logical strength. IPL and CPL *extend* rather than *replace* the same derivation type. When Curry-Howard is eventually formalized, MPL derivations will correspond to the purest computational type theory.

**Planned**: Normalization (task 290), subformula property (blocked on normalization), Curry-Howard (task 293, blocked on normalization).

**Best for**: Computational content, program extraction, proof search over inductive structures, Curry-Howard correspondence, equational reasoning via `Theory.equiv`.

### Sequent Calculus: The Structural Mirror

The Sequent Calculus reveals proof structure that the Hilbert system and ND hide. The cut rule (`Γ ⊢ A    A, Γ ⊢ C ⊢ Γ ⊢ C`) is provable: it can be eliminated from any proof. This is Gentzen's Hauptsatz.

Why does cut elimination matter? The subformula property follows immediately: every formula appearing in a cut-free proof is a subformula of some formula in the conclusion. This has cascading consequences:

- **Decidability via proof-search**: In a cut-free system, proof search is bounded (only subformulas appear), so completeness + cut elimination implies decidability. For IPL this gives `Decidable (IValid φ)` via a terminating search through LJ (task 292, PLANNING).
- **Interpolation**: The subformula property is the key ingredient in Craig interpolation theorems. An interpolant for A → B must be buildable from subformulas common to A and B — this constraint has a natural proof in the cut-free setting.
- **Logical harmony**: The symmetry between left and right rules in Gentzen systems makes "what a connective means" visible as a structural duality.

CSLib has both variants:
- **LK** (classical): the additive Finset-based presentation following Negri-von Plato. Cut elimination proven (`LKProof.cutElim`).
- **LJ** (intuitionistic): single-conclusion sequents. Cut elimination proven (`LJProof.cutElim`).

The difference in succedent structure (multi-set in LK, single formula in LJ) is exactly the structural signature of classical versus intuitionistic logic. This is not an accident — it is a theorem (multiple-conclusion-ness corresponds to LEM).

**Best for**: Cut elimination, subformula property, Craig interpolation (future), decidability proofs, structural proof theory, comparison of logic strengths via sequent structure.

### Tableau Calculus: The Decision Engine

The tableau calculus is the algorithmic face of proof theory. Where the Hilbert and ND systems build proofs top-down, the tableau works by refutation: to show `φ` is valid, assume `F(φ)` (φ is false) and try to construct a countermodel. If every branch closes (reaches contradiction), no countermodel exists, so `φ` is valid.

The algorithmic character delivers something the other systems provide only indirectly: **decision procedures as executable programs**. CSLib already has:

```lean
instDecidableTautologyTableau : Decidable (Tautology φ)  -- via classical tableau
instDecidableMValid : Decidable (MValid φ)               -- via minimal tableau  
instDecidableIValid : Decidable (IValid φ)               -- via intuitionistic tableau
```

These `Decidable` instances are not just existence proofs — they are runnable programs. Open branches yield countermodels directly: the branch state encodes a partial valuation that can be completed to falsify the formula. This is model construction as a computational artifact.

The three-variant architecture (Classical, Intuitionistic, Minimal) is architecturally significant. The classical and intuitionistic/minimal tableaux differ in how they handle implication:
- **Classical**: F(φ → ψ) branches into T(φ) and F(ψ) on the *same* world
- **Intuitionistic/Minimal**: F(φ → ψ) at world w creates a *fresh* world w' with T(φ) and F(ψ), inheriting T(α) formulas from w (persistence)

The minimal tableau further differs by having T(⊥) not close a branch. These behavioral differences directly encode the semantics of each logic, making the tableau a kind of *runnable semantic theory*.

**Infrastructure reuse**: The tableau infrastructure in `Foundations/Logic/Tableau/` (generic `Sign`, `SignedFormula`, `Branch`, `ClosureCondition`) is designed to be instantiated not just for propositional logic but for modal and temporal logics. Tasks 299 (Modal K tableau), 300 (Modal extensions), and 301 (Temporal tableau) build on this exact foundation.

**Best for**: Decision procedures, countermodel generation, mechanizable proof search, extension to modal/temporal logics, the computational face of completeness theorems.

---

## The Conservative Extension Chain: MPL → IPL → CPL

The three logics form a chain: every MPL theorem is an IPL theorem, and every IPL theorem is a CPL theorem. But the reverse does not hold. This chain is not a trivial observation — it has formal teeth.

**The chain as actually formalized in CSLib**:

```
MPL ⊆ IPL ⊆ CPL        (fragment inclusion)
   IPL conservative over MPL for bot-free formulas
   CPL with ¬¬φ ↔ IPL with φ   (Glivenko's theorem)
```

- `hilbertIplConservativeOverMpl` (`HilbertConservativeGlivenko.lean`): If φ is IPL-derivable and bot-free, then φ is already MPL-derivable. The proof routes through algebraic completeness and the `WithBot` Heyting algebra construction.

- `hilbertGlivenko` (`HilbertConservativeGlivenko.lean`): If φ is CPL-derivable, then ¬¬φ is IPL-derivable. Proof uses the regular elements of a Heyting algebra (Mathlib's `Heyting.Regular.instBooleanAlgebra`).

- `ipl_conservative_over_conj_imp_bot` (task 318, COMPLETED): IPL is conservative over the {∧, →, ⊥} fragment for formulas in that fragment.

- Task 311 (IPL conservative over implication fragment) and task 312 (unified conservative extension chain) are planned to complete this picture.

The significance for CSLib's architecture: the three-level hierarchy (MPL/IPL/CPL) is not three parallel developments — it is a single tower where each level is a conservative extension of the level below. Proofs about CPL that route through the algebraic layer can often be "pushed down" to IPL or MPL using these conservative extension theorems.

**Glivenko's theorem** is particularly interesting because it explains the *limits* of classical reasoning from an intuitionistic perspective: everything CPL proves, IPL can prove with double negation. The algebraic proof via regular elements is a beautiful illustration of how the algebraic semantics layer mediates between proof systems — the algebra knows something that neither the Hilbert rules nor the ND rules make syntactically obvious.

---

## The Equivalence Thesis

The four proof systems are equivalent at each logic level:

| Level | Hilbert | ND | LK/LJ | Tableau |
|-------|---------|-----|-------|---------|
| CPL | PropositionalAxiom | IPL ∪ CPL theory | LK | Classical |
| IPL | IntPropAxiom | IPL theory | LJ | Intuitionistic |
| MPL | MinPropAxiom | ∅ theory | — | Minimal |

**What equivalence means in practice**:
- Prove something in the easiest system; transport it to any other via the TFAE theorems
- Algebraic completeness of Hilbert immediately gives algebraic completeness of ND (via the bridge)
- Cut elimination of LK immediately gives decidability search (no other system needed)
- Open tableau branches give countermodels that falsify Kripke validity

The three-way equivalence (task 291, IMPLEMENTING) packages this as `List.TFAE` theorems:
- CPL: `Derivable PropositionalAxiom φ ↔ DerivableIn (IPL ∪ CPL) (∅ ⊢ φ) ↔ Nonempty (LKProof (∅ ⊢ₛ {φ}))`
- IPL: `Derivable IntPropAxiom φ ↔ DerivableIn IPL (∅ ⊢ φ) ↔ Nonempty (LJProof (∅ ⊢ φ))`

Adding tableau to this TFAE is the natural next step once soundness/completeness for the tableau systems are complete (tasks 316/317).

---

## The Broader CSLib Trajectory

The propositional layer is the foundation for a tower that already extends to modal and temporal logics:

```
             Bimodal Logic (42-axiom Hilbert, completeness suite)
              /              \
       Modal K,T,S4,S5    Temporal (BX system, chronicle completeness)
              \              /
           Propositional (MPL / IPL / CPL)
                    |
            Foundations/Logic/ (shared infrastructure)
```

The design principle "put content at the most general level it can compile at" means:
- Propositional proof theory infrastructure lives in `Foundations/Logic/` and is reused by modal/temporal
- The tableau infrastructure (`Foundations/Logic/Tableau/`) already powers propositional tableau and will power modal/temporal tableau (tasks 299/300/301)
- The MCS theory in `Foundations/Logic/Metalogic/` is reused by all completeness proofs

The equivalence theorems at the propositional level provide a template for what higher logics should aspire to. Modal logic currently has only a Hilbert system; adding sequent calculi and natural deduction for modal logic would enable the same "choose your tool" flexibility.

---

## What Makes This Compelling for the Lean Community

**The honest claim**: CSLib is building something Mathlib does not have — formalized *object-level* proof systems for propositional logic, not just proof automation tactics. The distinction matters for:

1. **Teaching logic**: Students can inspect actual derivation trees, not just "this is provable"
2. **Metatheory**: Conservative extension, Glivenko, cut elimination are theorems *about* proof systems, not proofs *in* them
3. **Reusability**: The generic infrastructure is designed for extension — add a new logic, instantiate the existing frameworks

**The compelling architectural facts**:
- Zero sorry in all mature components (Hilbert system, Natural Deduction, Sequent Calculi)
- The four-system equivalence chain means results are not trapped in one formalism
- The Lindenbaum algebra construction concretizes the algebraic semantics as a computable quotient type
- `Decidable` instances for tautologyhood are *executable* decision procedures, not just existence proofs
- The tableau countermodel extraction makes completeness constructive

**The honest acknowledged gaps**:
- Tableau soundness/completeness proofs have sorry stubs (tasks 316/317 in progress)
- LK soundness/completeness in progress (task 314)
- ND normalization, subformula property, and Curry-Howard are planned but not started
- No first-order logic yet (natural next extension after propositional tower is complete)

---

## Framing Advice for the Zulip Post

The most compelling angle for the Lean community is not "we have four proof systems" but rather:

> "We have proven that four independently implemented proof systems are equivalent, and that this equivalence is not just a curiosity — it is the mechanism by which algebraic results, structural proof theory, and computational decision procedures talk to each other."

The equivalence is the story. Each system contributes something the others cannot provide natively:
- Algebra speaks naturally to Hilbert
- Computation speaks naturally to ND (and eventually Curry-Howard)
- Structural properties (cut elimination, subformula property) speak naturally to Sequent Calculus
- Algorithms (decision procedures, countermodel generation) speak naturally to Tableau

The three-tier logic hierarchy (MPL/IPL/CPL) with its conservative extension chain is a separate but complementary story: not just classical logic, but a family of logics with formal relationships between them. The Glivenko theorem is the headline result here — classical proofs translate to intuitionistic double-negation proofs algebraically.

The trajectory toward modal and temporal logic is the "why this matters beyond propositional logic" angle: every structural investment at the propositional level pays dividends as the tower is built upward.
