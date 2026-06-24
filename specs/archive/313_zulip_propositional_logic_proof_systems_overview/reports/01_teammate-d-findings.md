# Teammate D Findings: Horizons / Strategic Framing

## Key Findings

### 1. What CSLib Actually Has (The Real Picture)

The "three proof systems" framing needs careful characterization. CSLib's propositional logic
(`Cslib/Logics/Propositional/`) currently contains:

**System 1 — Natural Deduction** (`NaturalDeduction/Basic.lean`)
- Sequent-style natural deduction with 10 primitive constructors
- Context = `Finset` (no structural rules needed; weakening/contraction are free)
- Theory-parameterized: the same `Derivation` type covers MPL, IPL, and CPL
- MPL (Johansson minimal logic): no axioms beyond 10 primitive rules
- IPL (intuitionistic): adds ex falso quodlibet as a theory axiom
- CPL (classical): additionally adds double-negation elimination
- Derived rules: weakening, cut, substitution

**System 2 — Hilbert System** (`ProofSystem/`)
- Axiom predicate hierarchy: `MinPropAxiom` / `IntPropAxiom` / `PropositionalAxiom`
- 10 axiom schemata for CPL (K, S, EFQ, Peirce, and 6 conjunction/disjunction schemata)
- Sequent derivability and Hilbert-style proof trees
- Context = `List` (explicit structural rules)

**Bridge** (`NaturalDeduction/Equivalence.lean`)
- Formal equivalence proven between the two systems: `hilbert_iff_nd`, `hilbert_iff_nd_ctx`
- Specialized for all three logic strengths (min, int, cl)
- `MinimalAxioms` typeclass bundles 8 witness requirements for the ND->Hilbert direction

**System 3 — Tableau Calculus** (`Foundations/Logic/Tableau/` and `Foundations/Logic/PropositionalTableau.lean`)
- Generic signed tableau infrastructure (Sign, SignedFormula, RuleResult, Branch, ClosureCondition)
- 8 standard classical propositional expansion rules following Smullyan's uniform notation
- Logic-neutral: can be instantiated for classical, intuitionistic, minimal, modal, and temporal logics
- Lives in `Foundations/`, not `Logics/Propositional/`, because it is shared infrastructure

**Additional metalogic** (important for the framing):
- MCS completeness via canonical model (`Metalogic/StrongCompleteness.lean`)
- Algebraic completeness: MPL complete w.r.t. `GeneralizedHeytingAlgebra`, IPL w.r.t. `HeytingAlgebra`, CPL w.r.t. `BooleanAlgebra`
- Glivenko's theorem: CPL derivability of φ implies IPL derivability of ¬¬φ
- Conservative extension: IPL is conservative over MPL for bot-free formulas

**Note on "Sequent Calculus"**: The task description says "Sequent Calculus" as the third
system. In CSLib, the tableau system is closest to this. The natural deduction system also uses
"sequent style" notation (Γ ⊢ A) but is not a Gentzen LK/LJ-style sequent calculus. The Zulip
post should clarify this accurately or use "Tableau Calculus" if that is what is meant.

Linear Logic (`Logics/LinearLogic/CLL/`) separately has a sequent calculus, but it is not
part of classical propositional logic and has its own module.

### 2. CSLib's Vision and Positioning

From README.md and ORGANISATION.md:

- CSLib is "the Lean library for Computer Science" — positioned as CS-first, not math-first
- Mission: "formalising Computer Science theories and tools"
- Two stated aims: APIs for formalisation/verification/certified software, AND establishing a
  "common ground for connecting different developments in Computer Science"
- The reuse-first philosophy means every abstraction is maximally general: foundations lift
  to `Foundations/`, logics instantiate them

The propositional logic module exemplifies this architecture beautifully: it sits at the base
of a dependency pyramid (Propositional -> Modal/Temporal -> Bimodal), so its proof systems must
be robust, verified, and extensible.

### 3. What Makes This Interesting to the Lean/Mathlib Community

The Lean/Mathlib community will respond to three things:

**a) Structural novelty**: The theory-parameterized approach to logic strength (MPL/IPL/CPL
unified under one `Derivation` type) is cleaner than separate inductive types per logic.
This is a design decision with mathematical elegance that Mathlib contributors will appreciate.

**b) Verified bridges**: The formal equivalence proofs between Hilbert and ND (both in
context-based and closed forms) are exactly the kind of "boring but essential" infrastructure
Mathlib values. The bridge is parameterized by `MinimalAxioms` typeclass — usable for any
axiom system satisfying the 8 conditions.

**c) The three-logic-strength-at-once design**: The fact that EFQ enters as a *theory axiom*
rather than a *derivation constructor* is a deliberate architectural choice (documented in
`NaturalDeduction/Basic.lean`) with implications for the entire modal/temporal/bimodal tower
above it. This trade-off (API uniformity vs. constructor-rule correspondence) is exactly the
kind of debate Zulip discussions thrive on.

**d) Algebraic semantics**: Completeness w.r.t. Boolean algebras (CPL), Heyting algebras (IPL),
and generalized Heyting algebras (MPL) connects directly to Mathlib's `Order.Heyting` and
`Order.BooleanAlgebra` — a natural entry point for Mathlib contributors.

**e) Glivenko's theorem**: A non-trivial classical-constructive bridge that is machine-checked.
This is the kind of theorem that resonates with people interested in constructive mathematics.

### 4. What Mathlib Already Has

Mathlib has propositional logic infrastructure, but primarily:
- `Mathlib.Logic.Basic`, `Mathlib.Logic.Classical`, `Mathlib.Tactic.Tauto`
- These are propositional *reasoning* tools built into the meta-level, not *formal object-level*
  proof systems for propositional logic
- Mathlib does not have a standalone formalization of MPL/IPL/CPL as object-level proof systems
  with verified soundness and completeness and bridge theorems between them

CSLib fills a genuine gap: object-level logic formalizations with verified soundness, completeness,
and proof-system bridges — not just tactic support for classical reasoning.

### 5. Future Directions to Hint At

**Near-term (logical next steps visible in codebase)**:
- The proof systems are already serving as a base for Modal, Temporal, and Bimodal logics
  (the `FromPropositional.lean` embedding files exist in those modules)
- The tableau infrastructure (`Foundations/Logic/Tableau/`) is logic-neutral and is being
  extended for modal logic
- `Automation/HilbertSearch.lean` provides a bounded DFS proof-search tactic for `InferenceSystem`

**Medium-term (suggested by ROADMAP and gaps)**:
- First-order logic is not yet in CSLib; propositional is the stepping stone
- The conservative extension and Glivenko results position CSLib to formalize relationships
  between classical and constructive mathematics
- The algebraic completeness results open a path toward duality theorems (Stone duality)

**Long-term (architectural implications)**:
- The proof system architecture is language-neutral: `InferenceSystem` and `ProofSystem` are
  typeclasses that any logic can instantiate
- This makes CSLib a candidate for a shared foundation for verified compilers, type checkers,
  and proof assistants formalized within Lean

### 6. How to Frame the Three Systems as Complementary

**The key framing**: The three proof systems are tools for different tasks, not competing
formalisms:

- **Hilbert system**: Compact axiomatization, well-suited for metalogical proofs (MCS
  construction, soundness/completeness), and for clean definitions that extend easily to
  modal/temporal logics
- **Natural deduction**: Proof-theoretic intuition, closer to how mathematicians actually
  reason, good for demonstrating Curry-Howard correspondence, structured derivation trees
- **Tableau calculus**: Decision procedure / refutation calculus, mechanically computable,
  foundation for proof search and automated reasoning

The formal bridge between Hilbert and ND (`hilbert_iff_nd`) shows that these are not just
philosophically equivalent but provably so in Lean 4 — and the bridge theorem is generic,
working for any axiom predicate satisfying `MinimalAxioms`.

A compelling framing for Zulip: "Having all three in CSLib means you can *choose your tool
to match the task*: use Hilbert for completeness proofs, ND for Curry-Howard type theory
connections, tableau for automated proof search — and trust that the bridges between them
are machine-verified."

---

## Recommended Approach

### Overall Tone

Write as a practitioner sharing something genuinely interesting, not as a catalog entry.
The Lean/Mathlib community has seen many propositional logic formalizations; what makes CSLib
different is the architecture and what it enables above.

### Recommended Structure for the Zulip Comment

**Opening hook** (1-2 sentences): Don't start with "We have three proof systems." Start with
the architectural decision — e.g., the three-logic-strength-at-once design, or the formal
bridge — and let the proof systems emerge from that.

**Section 1: The propositional foundation** (3-5 sentences)
- Formula type with primitives (atom, bot, imp, and, or); neg/top/biconditional are derived
- The theory-parameterized logic strength: one `Proposition` type, three theories (MPL/IPL/CPL)
- EFQ design decision: why it is a theory axiom rather than a derivation constructor

**Section 2: The proof systems** (one paragraph each, with bullet points)
- Hilbert: what axiom schemata, what the derivability relation looks like, use for metalogic
- Natural Deduction: 10-constructor inductive, sequent-style, weakening as derived rule
- Tableau: generic signed tableau infrastructure, 8 classical propositional rules (Smullyan)

**Section 3: The bridges** (2-4 sentences)
- `hilbert_iff_nd` and its context-parameterized form
- What the `MinimalAxioms` typeclass does (enables generic bridge)
- The algebraic completeness results (Boolean/Heyting/Generalized Heyting)
- Glivenko's theorem as a bonus result

**Section 4: Why this matters for the rest of CSLib** (3-5 sentences)
- The propositional module is the base of the tower: Modal, Temporal, Bimodal all build on it
- `FromPropositional.lean` embeddings in each module
- The tableau infrastructure is reused for modal logic
- The `InferenceSystem` typeclass means any future logic can plug in

**Section 5: Future directions / invitation** (2-3 sentences)
- First-order logic is the natural next step
- Contributions welcome (the foundation is in place)
- Link to the Propositional Logic Zulip topic already referenced in `NaturalDeduction/Basic.lean`

### Length

Zulip comment: 400-600 words. Long enough to give substance, short enough to be read.
Use code snippets sparingly — one or two well-chosen Lean signatures to make it concrete,
not a tutorial.

### What NOT to Do

- Do not lead with a list of file names
- Do not claim "Sequent Calculus" if what exists is a Tableau Calculus
- Do not imply these are alternatives — frame them as a toolkit
- Do not oversell completeness of the library (ROADMAP shows remaining gaps)

---

## Evidence/Examples

### Key architectural claim (from `NaturalDeduction/Basic.lean` docstring):

The file explicitly cites the Zulip thread:
> "This design choice and its trade-offs are discussed further in the
> [CSLib Zulip thread on Propositional Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic)."

This confirms the Zulip thread already exists. The comment should acknowledge this ongoing
discussion, not duplicate it.

### Key theorem names to mention (accuracy check):

- `hilbert_iff_nd`, `hilbert_iff_nd_ctx` — Hilbert-ND equivalence
- `prop_strong_completeness` — strong completeness for CPL
- `prop_completeness_iff_tautology` — Hilbert completeness w.r.t. Boolean valuations
- `hilbertGlivenko` — Glivenko's theorem (Hilbert primary)
- `hilbertIplConservativeOverMpl` — IPL conservative over MPL

### Module path for community navigation:

```
Cslib.Logic.PL                      -- in Cslib/Logics/Propositional/Defs.lean
Cslib.Logic.PL.Theory.Derivation    -- in NaturalDeduction/Basic.lean
Cslib.Logic.PL.PropositionalAxiom   -- in ProofSystem/Axioms.lean
Cslib.Logic.Tableau                 -- in Foundations/Logic/Tableau/
```

### The Lean/Mathlib gap CSLib fills:

Mathlib has propositional reasoning tactics (omega, tauto, decide) but not formalized
*object-level* proof systems with soundness/completeness theorems. CSLib's propositional
module fills this gap — it is the "formal logic" layer that Mathlib's "reasoning" layer
uses implicitly but does not expose.

---

## Confidence Level

**High** for:
- Accurate characterization of the three systems (read the actual source)
- The Mathlib gap claim (verified by codebase search — no Mathlib.Logic.Hilbert etc.)
- The dependency tower structure (confirmed by ORGANISATION.md and ROADMAP.md)
- The EFQ design decision (explicitly documented in the ND file)

**Medium** for:
- Whether "Sequent Calculus" vs "Tableau Calculus" is intentional in the task description
  (the task says "Sequent Calculus" but the actual third system is tableau-based; this needs
  clarification with the synthesis agent)
- Exact state of tableau-for-modal extension (files exist in Foundations but modal tableau
  completeness not yet in the codebase)

**Low** for:
- Actual Zulip community reaction (cannot predict without seeing thread history)
- Whether there is a true sequent calculus (LK/LJ style) somewhere not yet found in the
  codebase (search covered main directories)
