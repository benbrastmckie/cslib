# Reference Sources for CSLib Propositional and Foundations Modules

Standard references for the propositional logic formalization in CSLib, organized by topic.
These sources inform the mathematical content, proof architecture, and citation standards.

## Propositional Logic (General)

- **Church 1956** [Church1956]: *Introduction to Mathematical Logic*, Vol. 1. Princeton University Press.
  Classical reference for propositional and predicate logic foundations. Hilbert-style axiomatization.

- **van Dalen 2013**: *Logic and Structure*, 5th ed. Springer.
  Standard graduate textbook covering propositional logic, predicate logic, completeness, compactness.
  Covers both classical and intuitionistic systems. **Not yet in references.bib.**

## Intuitionistic and Minimal Logic

- **Heyting 1930** [Heyting1930]: *Die formalen Regeln der intuitionistischen Logik*.
  Original formalization of intuitionistic propositional logic. Conjunction and disjunction are
  primitive (not definable from implication and falsum).

- **Johansson 1937** [Johansson1937]: *Der Minimalkalkul, ein reduzierter intuitionistischer Formalismus*.
  Defines minimal logic (removes ex falso quodlibet from intuitionistic logic). Key reference
  for MinPropAxiom.

- **McKinsey 1939** [McKinsey1939]: *Proof of the Independence of the Primitive Symbols of Heyting's Calculus of Propositions*.
  Proves that conjunction and disjunction cannot be defined from implication and negation in
  intuitionistic logic. Critical for justifying the five-primitive formula type.

- **Wajsberg 1938** [Wajsberg1938]: *Untersuchungen uber den Aussagenkalkul von A. Heyting*.
  Further independence results for Heyting's calculus. Supports the non-reducibility of
  connectives in intuitionistic logic.

- **Troelstra & van Dalen 1988** [TroelstraVanDalen1988]: *Constructivism in Mathematics: An Introduction*, Vol. 1. North-Holland.
  Comprehensive reference for constructive mathematics. Covers intuitionistic propositional
  logic, Kripke semantics, completeness, natural deduction. Section 2.5 for Kripke completeness,
  Section 10.4 for natural deduction.

- **Fitting 1969**: *Intuitionistic Logic, Model Theory and Forcing*. North-Holland.
  Kripke semantics for intuitionistic logic, completeness proofs, forcing techniques.
  **Not yet in references.bib.**

## Modal Logic (Foundations shared with Propositional)

- **Chagrov & Zakharyaschev 1997** [ChagrovZakharyaschev1997]: *Modal Logic*. Oxford Logic Guides 35.
  Primary reference for CSLib (cited as "CZ" throughout). Key sections:
  - Chapter 1: Classical propositional logic, truth tables, tautologies, completeness (Thm 1.16)
  - Section 2.2: Kripke semantics, persistence (Prop 2.1)
  - Section 2.4: Intuitionistic completeness (Thm 2.43)
  - Section 5.1: Maximal consistent sets, Lindenbaum's lemma, canonical models

- **Blackburn, de Rijke & Venema 2001** [Blackburn2001]: *Modal Logic*. Cambridge Tracts.
  Alternative modal logic reference. Covers Kripke semantics, bisimulation, correspondence theory.

## Natural Deduction and Proof Theory

- **Gentzen 1935** [Gentzen1935]: *Untersuchungen uber das logische Schliessen*.
  Introduces natural deduction and sequent calculus. Foundation for the ND proof system.
  Note: Gentzen uses all connectives as primitive in his intuitionistic system.

- **Prawitz 1965** [Prawitz1965]: *Natural Deduction: A Proof-Theoretical Study*. Almqvist & Wiksell.
  Definitive treatment of natural deduction. Normalization theorem. Key reference for the
  Hilbert/ND equivalence (task 186).

## Completeness and Compactness

- **Lindenbaum's lemma**: Every consistent set extends to a maximal consistent set (via Zorn's lemma).
  Attributed to Adolf Lindenbaum by Alfred Tarski (1930, *On Fundamental Concepts of Metamathematics*).
  Not published by Lindenbaum himself.

- **Strong completeness**: Standard result in CZ Chapter 1 (classical) and Chapter 2 (intuitionistic).
  The proof architecture (contrapositive: non-derivability -> MCS extension -> canonical model ->
  countermodel) is uniform across all three logics.

- **Compactness**: Follows as a corollary of strong completeness + strong soundness for
  propositional logics. For first-order logic, independent proofs exist via ultraproducts.

## Lean 4 Formalizations (Prior Art)

- **Bentzen 2023**: Lean 4 formalization of intuitionistic propositional logic completeness.
  Uses direct canonical model approach (same as CSLib).

- **Borges et al. 2024**: Lean 4 formalization of propositional logic.

- **From & Jacobsen 2025**: Lean 4 completeness results.

## Cautionary Notes

### PR #635 Lesson
The claim that {bot, imp} is a sufficient primitive basis for ALL propositional logics
(including intuitionistic and minimal) is FALSE. McKinsey (1939) proved that conjunction
and disjunction are independent in Heyting's calculus. The Lukasiewicz encodings
`and phi psi := neg (imp phi (neg psi))` and `or phi psi := imp (neg phi) psi` are only
classically valid. CSLib correctly uses five primitives {atom, bot, imp, and, or} for the
formula type, with neg and top as derived abbreviations valid in all three logics.

### CZ Citation Format
The codebase uses bare "CZ" abbreviation in many docstrings. For doc-gen cross-linking,
these should use the proper BibKey format `[ChagrovZakharyaschev1997]`.
