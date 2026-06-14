# Reference Sources for CSLib Propositional and Foundations Modules

Standard references for the propositional logic formalization in CSLib, organized by topic.
These sources inform the mathematical content, proof architecture, and citation standards.

File availability key: `[PDF]` = PDF in this directory, `[DJVU]` = DjVu in this directory,
`[MD]` = markdown conversion available, `[NO FILE]` = not freely available (book or paywalled journal).

All files follow the naming convention `{author}_{year}.{ext}` (first author surname, lowercase).

## Propositional Logic (General)

- **Hilbert & Bernays 1934** `[NO FILE]`: *Grundlagen der Mathematik*, Vol. 1. Springer.
  CSLib's Hilbert-style proof system (`Deriv`, `DerivationTree`) is named after this axiomatization.
  Truth-value semantics, completeness, and decidability for propositional logic first presented
  systematically here.

- **Church 1956** [Church1956] `[PDF] [MD]`: *Introduction to Mathematical Logic*, Vol. 1. Princeton University Press.
  Files: `church_1956.pdf`, `church_1956.md`.
  Classical reference for propositional and predicate logic foundations. Hilbert-style axiomatization.

- **Mendelson 2016** `[PDF] [MD]`: *Introduction to Mathematical Logic*, 6th ed. CRC Press.
  Files: `mendelson_2016.pdf`, `mendelson_2016.md`.
  Standard textbook covering propositional logic, first-order logic, formal number theory,
  and axiomatic set theory. Detailed Hilbert-style completeness proofs.

- **Post 1921** `[PDF] [MD]`: *Introduction to a General Theory of Elementary Propositions*. American Journal
  of Mathematics, 43(3):163-185. Source: Internet Archive.
  Files: `post_1921.pdf`, `post_1921.md`.
  Proved functional completeness of propositional connectives, introduced truth tables systematically.
  Relevant to CSLib's `Evaluate`/`Tautology` definitions.

- **Lukasiewicz & Tarski 1930** `[NO FILE]`: *Untersuchungen uber den Aussagenkalkul*. Comptes Rendus des
  Seances de la Societe des Sciences et des Lettres de Varsovie, Classe III, 23:30-50.
  The Lukasiewicz encoding `and phi psi := neg (phi -> neg psi)` and `or phi psi := neg phi -> psi`
  used in CSLib's upper layers (Modal, Temporal, Bimodal) is named after this work.

- **van Dalen 2013** `[NO FILE]`: *Logic and Structure*, 5th ed. Springer.
  Standard graduate textbook covering propositional logic, predicate logic, completeness, compactness.
  Covers both classical and intuitionistic systems. **Not yet in references.bib.**

## Intuitionistic and Minimal Logic

- **Heyting 1930** [Heyting1930] `[NO FILE]`: *Die formalen Regeln der intuitionistischen Logik*.
  Original formalization of intuitionistic propositional logic. Conjunction and disjunction are
  primitive (not definable from implication and falsum).

- **Johansson 1937** [Johansson1937] `[PDF] [MD]`: *Der Minimalkalkul, ein reduzierter intuitionistischer Formalismus*.
  Compositio Mathematica, 4:119-136.
  Files: `johansson_1937.pdf`, `johansson_1937.md`.
  Defines minimal logic by removing ex falso quodlibet (`⊥ → A`) from Heyting's intuitionistic
  system. Key reference for `MinPropAxiom`. Critically, Johansson's formula language **retains
  `⊥` (falsum) as a primitive** — minimal logic is not the positive fragment without falsum, but
  rather the full language `{⊥, →, ∧, ∨}` without the explosion principle. Negation is defined
  as `¬A := A → ⊥`, which requires `⊥` in the language. This justifies CSLib's design choice of
  `bot` as a primitive constructor in `Proposition`: all three logics (minimal, intuitionistic,
  classical) share the same formula type and differ only in inference rules/theory axioms.

- **McKinsey 1939** [McKinsey1939] `[NO FILE]`: *Proof of the Independence of the Primitive Symbols of Heyting's Calculus of Propositions*.
  Proves that conjunction and disjunction cannot be defined from implication and negation in
  intuitionistic logic. Critical for justifying the five-primitive formula type.

- **Wajsberg 1938** [Wajsberg1938] `[NO FILE]`: *Untersuchungen uber den Aussagenkalkul von A. Heyting*.
  Further independence results for Heyting's calculus. Supports the non-reducibility of
  connectives in intuitionistic logic.

- **Troelstra & van Dalen 1988** [TroelstraVanDalen1988] `[NO FILE]`: *Constructivism in Mathematics: An Introduction*, Vol. 1. North-Holland.
  Comprehensive reference for constructive mathematics. Covers intuitionistic propositional
  logic, Kripke semantics, completeness, natural deduction. Section 2.5 for Kripke completeness,
  Section 10.4 for natural deduction.

- **Kripke 1965** `[NO FILE]`: *Semantical Analysis of Intuitionistic Logic I*. In Crossley & Dummett (eds.),
  Formal Systems and Recursive Functions, pp. 92-130. North-Holland.
  CSLib's entire intuitionistic and minimal completeness proof architecture is built on Kripke
  frames (`IForces`, `KripkeFrame`, `KripkeModel` in `Kripke.lean`). This is the foundational paper.

- **Glivenko 1929** `[NO FILE]`: *Sur quelques points de la logique de M. Brouwer*. Academie Royale de
  Belgique, Bulletin de la Classe des Sciences, 15:183-188.
  Glivenko's theorem: phi is classically provable iff not-not-phi is intuitionistically provable.
  Foundational result connecting classical and intuitionistic logic.

- **Fitting 1969** `[NO FILE]`: *Intuitionistic Logic, Model Theory and Forcing*. North-Holland.
  Kripke semantics for intuitionistic logic, completeness proofs, forcing techniques.
  **Not yet in references.bib.**

## Modal Logic (Foundations shared with Propositional)

- **Chagrov & Zakharyaschev 1997** [ChagrovZakharyaschev1997] `[DJVU] [MD]`: *Modal Logic*. Oxford Logic Guides 35.
  Files: `chagrov_1997.djvu`, `chagrov_1997.md`.
  Primary reference for CSLib (cited as "CZ" throughout). Key sections:
  - Chapter 1: Classical propositional logic, truth tables, tautologies, completeness (Thm 1.16)
  - Section 2.2: Kripke semantics, persistence (Prop 2.1)
  - Section 2.4: Intuitionistic completeness (Thm 2.43)
  - Section 5.1: Maximal consistent sets, Lindenbaum's lemma, canonical models

- **Blackburn, de Rijke & Venema 2001** [Blackburn2001] `[PDF] [MD]`: *Modal Logic*. Cambridge Tracts.
  Files: `blackburn_2001.pdf`, `blackburn_2001.md`, `blackburn_2001_ch4_summary.md` (curated completeness chapter summary).
  Alternative modal logic reference. Covers Kripke semantics, bisimulation, correspondence theory.

- **Hughes & Cresswell 1996** `[MD]`: *A New Introduction to Modal Logic*. Routledge.
  File: `hughes_1996.md`.
  Accessible introduction to modal logic with detailed completeness proofs.
  PDF not available (copyrighted book, Routledge paywall).

- **Zakharyaschev, Wolter & Chagrov 2001** `[MD]`: *Advanced Modal Logic*. In Gabbay & Guenthner (eds.),
  Handbook of Philosophical Logic, Vol. 3, 2nd ed. Springer.
  Files: `zakharyaschev_2001.md`, `zakharyaschev_2001_pt2.md`.
  Supplementary modal logic material covering advanced topics.
  PDFs not available (Springer paywall).

## Natural Deduction and Proof Theory

- **Gentzen 1935** [Gentzen1935] `[PDF] [MD]`: *Untersuchungen uber das logische Schliessen*.
  Files: `gentzen_1935.pdf`, `gentzen_1935.md`.
  English translation by M.E. Szabo from *The Collected Papers of Gerhard Gentzen* (1969).
  Introduces natural deduction and sequent calculus. Foundation for the ND proof system.
  Note: Gentzen uses all connectives as primitive in his intuitionistic system.

- **Prawitz 1965** [Prawitz1965] `[NO FILE]`: *Natural Deduction: A Proof-Theoretical Study*. Almqvist & Wiksell.
  Definitive treatment of natural deduction. Normalization theorem. Key reference for the
  Hilbert/ND equivalence (task 186).

## Completeness and Compactness

- **Henkin 1949** `[PDF] [MD]`: *The Completeness of the First-Order Functional Calculus*. Journal of Symbolic
  Logic, 14(3):159-166.
  Files: `henkin_1949.pdf`, `henkin_1949.md`.
  The MCS-extension method used in CSLib's completeness proofs (`set_lindenbaum`, `prop_lindenbaum`,
  canonical model construction) is the Henkin method. While Henkin's paper is for first-order logic,
  the propositional specialization is what CSLib implements.

- **Tarski 1930** `[NO FILE]`: *Fundamentale Begriffe der Methodologie der deduktiven Wissenschaften I*.
  Monatshefte fur Mathematik und Physik, 37:361-404. English translation in *Logic, Semantics,
  Metamathematics*, 2nd ed., Hackett, 1983.
  Formalized the consequence operation and attributed Lindenbaum's lemma. CSLib's `SetDerivable`
  is essentially Tarski's consequence operator restricted to finite derivations.
  PDF not available (Springer paywall).

- **Godel 1930** `[NO FILE]`: *Die Vollstandigkeit der Axiome des logischen Funktionenkalkuls*. Monatshefte
  fur Mathematik und Physik, 37:349-360.
  First completeness proof (for first-order logic). Historical context for the completeness
  tradition CSLib participates in.
  PDF not available (Springer paywall).

- **Lindenbaum's lemma**: Every consistent set extends to a maximal consistent set (via Zorn's lemma).
  Attributed to Adolf Lindenbaum by Alfred Tarski (1930). Not published by Lindenbaum himself.

- **Strong completeness**: Standard result in CZ Chapter 1 (classical) and Chapter 2 (intuitionistic).
  The proof architecture (contrapositive: non-derivability -> MCS extension -> canonical model ->
  countermodel) is the Henkin method adapted to propositional logic.

- **Compactness**: Follows as a corollary of strong completeness + strong soundness for
  propositional logics. For first-order logic, independent proofs exist via ultraproducts.

## Algebraic Logic (Future Direction)

- **Rasiowa & Sikorski 1963** `[NO FILE]`: *The Mathematics of Metamathematics*. PWN, Warsaw.
  The algebraic approach to logic (Lindenbaum-Tarski algebras, representation theorems).
  Relevant background for any future algebraic completeness work in CSLib.

## Lean 4 Formalizations (Prior Art)

- **Bentzen 2023** `[PDF] [MD]`: *Verified completeness in Henkin-style for intuitionistic propositional logic*.
  arXiv:2310.01916.
  Files: `bentzen_2023.pdf`, `bentzen_2023.md`.
  First verified Henkin-style proof of completeness for IPL following
  Troelstra & van Dalen's method in Lean.

- **Trufas 2024** `[PDF] [MD]`: *Intuitionistic Propositional Logic in Lean*. arXiv:2410.23765.
  Files: `trufas_2024.pdf`, `trufas_2024.md`.
  Formalizes strong completeness for IPL with both Kripke and algebraic semantics in Lean.
  Directly comparable to CSLib's approach.

- **FormalizedFormalLogic**: *Logic Formalization in Lean 4*.
  GitHub: https://github.com/FormalizedFormalLogic/Foundation
  Book: https://formalizedformallogic.github.io/Book/
  Most comprehensive Lean 4 logic formalization project. Covers propositional completeness,
  modal logic completeness, and more. Important prior art for positioning CSLib.

- **From & Jacobsen 2022** `[PDF] [MD]`: *SeCaV: A Sequent Calculus Verifier in Isabelle/HOL*.
  arXiv:2204.03884.
  Files: `from_2022.pdf`, `from_2022.md`.
  Formalized soundness and completeness for sequent calculus.

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
