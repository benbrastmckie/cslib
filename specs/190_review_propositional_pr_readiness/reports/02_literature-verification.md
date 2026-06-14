# Literature Verification Report: PR Description for Task #188

**Task**: 190 - Review Propositional PR Readiness
**Date**: 2026-06-14
**Scope**: Fact-checking all literature references and attributions in the PR description at
`specs/188_first_propositional_upstream_pr/pr-description.md`

## Verdict Summary

| # | Claim | Verdict | Action Required |
|---|-------|---------|-----------------|
| 1 | [Church1956] §24 discusses propositional signature | **ACCURATE (qualified)** | Minor clarification recommended |
| 2 | [TroelstraVanDalen1988] Chapter 2 | **ACCURATE (qualified)** | None required, but see notes |
| 3 | [Johansson1937] negation as A -> bottom | **ACCURATE** | None required |
| 4 | [Gentzen1935], [Prawitz1965], [Church1956] re: "imp" naming | **MISLEADING** | Reword recommended |
| 5 | Gentzen date [Gentzen1935] | **ACCURATE** | None required |

---

## Detailed Analysis

### Claim 1: [Church1956] §24

**PR text (line 49)**: "This is the standard propositional signature in [Church1956] §24"

**What §24 actually covers**: Church's *Introduction to Mathematical Logic* (1956) uses a
numbered section system (§00-§59). §24 is titled **"Primitive connectives for the propositional
calculus"** and falls within Chapter II ("The Propositional Calculus (Continued)"). The section
discusses alternative choices of primitive connectives for propositional logic -- which sets of
connectives suffice as a basis, and the relationships between different choices.

**Verification**: The section reference is correct: §24 does exist and does discuss primitive
connectives for propositional logic. However, Church's primary system (P1, in Chapter I) uses
negation (~) and the material conditional (horseshoe) as primitives, with conjunction,
disjunction, and biconditional as defined connectives. §24 then discusses *alternative*
formulations with different primitive bases.

**Important nuance**: Church's treatment is classical. He does not use the specific five-primitive
signature {atom, bot, imp, and, or} that CSLib uses. Church's primitive basis is {~, horseshoe}
(negation, material conditional), and §24 discusses which *other* sets of connectives could serve
as alternatives. The claim that this is "the standard propositional signature in [Church1956] §24"
is somewhat misleading -- Church discusses the *topic* of primitive connective choices in §24,
but does not specifically endorse or present the five-primitive set {atom, bot, imp, and, or}.
The five-primitive set is motivated by *intuitionistic* considerations (McKinsey 1939
independence results), not by Church's classical analysis.

**Verdict**: **ACCURATE (qualified)** -- §24 is the right section for discussing primitive
connective choices, but Church does not present the specific five-primitive signature. The
citation is appropriate as a reference to the *topic* of primitive connective selection, but
could be read as implying Church used or endorsed this exact signature.

**Recommendation**: Consider rewording to: "The choice of primitive connectives is discussed
in [Church1956] §24; the five-primitive signature is standard for intuitionistic logic
following [TroelstraVanDalen1988] Chapter 2."

**Full-text access needed?** Yes -- to verify the exact scope of §24's discussion of
alternative primitive bases. The section title and placement are confirmed, but the detailed
content cannot be fully verified without the book.

---

### Claim 2: [TroelstraVanDalen1988] Chapter 2

**PR text (line 49)**: "...and [TroelstraVanDalen1988] Chapter 2"
**PR text (lines 78-79)**: "The planned roadmap mirrors the structure of Troelstra & van Dalen
[TroelstraVanDalen1988] Chapter 2, with PR 5-6 following the completeness proof strategy there."

**What Chapter 2 covers**: Chapter 2 of Troelstra & van Dalen's *Constructivism in Mathematics*,
Vol. 1 (1988) is titled **"Logic"**. It has at least 6 sections (2.1-2.6). Based on the project's
own `sources.md` and corroborating web sources:

- Section 2.5 covers Kripke semantics and completeness for intuitionistic propositional logic
- Section 2.6 appears to cover related completeness results
- The chapter covers intuitionistic propositional logic with its standard connectives

The Stanford Encyclopedia of Philosophy's article on intuitionistic logic cites Troelstra & van
Dalen [1988] as a comprehensive reference for Kripke semantics and completeness of intuitionistic
logic. Multiple academic sources reference "section 2.5" or "section 2.6" of this work for Kripke
completeness proofs.

**Verification of the five-primitive claim**: Intuitionistic propositional logic standardly uses
the connectives {bottom, implication, conjunction, disjunction} as primitives (with negation
defined as A -> bottom). This is because McKinsey (1939) proved that conjunction and disjunction
are independent in Heyting's calculus -- they cannot be defined from implication and negation
alone. Troelstra & van Dalen present intuitionistic logic with these connectives. The claim that
Chapter 2 uses this signature is consistent with the standard presentation of intuitionistic logic.

**Verification of the roadmap claim**: The PR roadmap (PRs 1-6) covers: formula type, proof
systems, equivalence, semantics/soundness, CPL completeness, IPL completeness. The claim that
this "mirrors the structure of Troelstra & van Dalen Chapter 2" is plausible -- a logic textbook
chapter would proceed through syntax, proof systems, semantics, soundness, and completeness in
roughly this order. The specific claim about "PR 5-6 following the completeness proof strategy
there" is consistent with the known content (Section 2.5 for Kripke completeness).

**Verdict**: **ACCURATE (qualified)** -- Chapter 2 is titled "Logic" and covers intuitionistic
propositional logic including Kripke completeness. The five-primitive signature is standard for
intuitionistic logic. The roadmap claim is plausible.

**Full-text access needed?** Yes -- to verify the *exact* section structure and confirm the
precise completeness strategy. The high-level claim is well-supported by secondary sources, but
the detailed structural correspondence cannot be fully verified without the book.

---

### Claim 3: [Johansson1937] negation as A -> bottom

**PR text (lines 50-51)**: "required for Johansson's minimal logic [Johansson1937] where
`not-A := A -> bottom` must be available without assumptions on the atom type"

**What Johansson actually wrote**: The full OCR of Johansson's paper is available locally
(`specs/literature/Johansson1937.md`). The critical passage is in §1 (Introduction), page 119-120,
and §4 (pages 129-131):

**§1 (Introduction, p. 119-120)**: "Die Moglichkeit [negation-a] durch a:)A (wo A 'Widerspruch'
oder 'etwas Falsches' bedeutet) zu ersetzen, ist wahrscheinlich recht allgemein bekannt" --
i.e., the possibility of replacing negation-of-a by a -> A (where A means "contradiction" or
"something false") is probably well known. Then: "Die Auffassung von A als undefiniertes
Grundzeichen und die Definition von [negation] durch [negation-a := a -> A] liegt dann sehr nahe"
-- i.e., the conception of A (absurdity) as an **undefined primitive symbol** and the definition
of negation as a -> A follows naturally.

**§4 (p. 129-130)**: Johansson explicitly gives the definition (22): negation-a is defined as
a -> A (where A is the absurdity constant). He then proves that axiom 4.11 follows from this
definition *without any assumptions about A* -- A is treated "nur wie eine Aussagenvariable"
(only like a propositional variable). This is the key result: **no special axiom about A (such
as A -> b, i.e., ex falso quodlibet) is needed**. The entire minimal calculus works with A as
an uninterpreted proposition.

**Verification**: The PR claim is **accurate**:
1. Johansson does define negation as A -> bottom (using A for the absurdity constant)
2. The absurdity constant A is primitive (an "undefiniertes Grundzeichen" = undefined primitive symbol)
3. The whole point of minimal logic is that negation via A -> bottom works "ohne Voraussetzung uber A" (without assumptions about A)
4. The PR's claim that "not-A := A -> bottom must be available without assumptions on the atom type" correctly captures Johansson's key insight

**One subtlety**: Johansson used "A" (the German Fraktur/Gothic letter) for absurdity, not the
modern "bottom" symbol. His notation was "la" for negation-of-a and "a :> A" for a-implies-A.
But the mathematical content is exactly as the PR claims.

**Another subtlety**: The PR says "`not-A := A -> bottom` must be available without assumptions
on the atom type" -- Johansson's point was about not needing assumptions on A (the absurdity
constant), not about "the atom type." In CSLib, this maps to not needing a `[Bot Atom]` constraint
because bottom is primitive. The PR correctly translates Johansson's mathematical insight into the
Lean formalization context.

**Verdict**: **ACCURATE** -- Fully supported by the primary source.

---

### Claim 4: [Gentzen1935], [Prawitz1965], [Church1956] re: naming "imp"

**PR text (lines 55-56)**: "The name `imp` is standard in both the proof theory literature
([Gentzen1935], [Prawitz1965], [Church1956]) and Lean formalization practice."

**What these authors actually used**:

- **Gentzen (1935)**: Used the symbol "horseshoe" (the superset symbol) for implication in his
  Hilbert-style system, and inference rule labels like "FE" (Folgerung-Einführung = implication
  introduction) and "FA" (Folgerung-Ausschaltung = implication elimination) in the sequent
  calculus. He did **not** use the abbreviation "imp". His system used German-language labels.

- **Prawitz (1965)**: Used the arrow symbol (→) for implication and rule labels like "→I"
  (implication introduction) and "→E" (implication elimination). He did **not** use the
  abbreviation "imp". His system used symbolic notation.

- **Church (1956)**: Used the horseshoe symbol (⊃) for the material conditional. He did **not**
  use the abbreviation "imp". His notation was entirely symbolic.

**The "imp" convention in formalization**: The abbreviation "imp" (or "Imp") is a convention
from *computer science formalizations*, not from the proof theory literature itself. In Lean,
Coq, Isabelle, and similar systems, constructors and function names cannot be symbols, so
abbreviated English names are used. "Imp" appears in Coq formalizations; some Lean projects use
"impl" or "implication". The FormalizedFormalLogic project and Trufas (2024) use various
conventions. There is no single "standard" across Lean formalizations.

**The problem with the citation**: The PR sentence "The name `imp` is standard in both the proof
theory literature ([Gentzen1935], [Prawitz1965], [Church1956]) and Lean formalization practice"
can be read two ways:

1. **Generous reading**: Implication is a standard connective in proof theory (as discussed by
   these authors), and "imp" is the standard *abbreviation* for it in formalization practice.
   Under this reading, the citations support the *concept* (implication as a primitive), and the
   *name* "imp" comes from formalization convention.

2. **Literal reading**: These authors used the name "imp", which is false. None of them used
   this abbreviation.

The sentence structure ("The name `imp` is standard in ... the proof theory literature
([Gentzen1935], [Prawitz1965], [Church1956])") most naturally reads as claiming these authors
used this name. This is **misleading**.

**Verdict**: **MISLEADING** -- The cited authors used symbols (horseshoe, arrow), not the
abbreviation "imp". The PR conflates the concept (implication as a primitive connective) with
the name (the specific abbreviation "imp"). The citations support the concept but not the name.

**Recommendation**: Reword to separate the two claims: "Implication is a standard primitive
connective in the proof theory literature ([Gentzen1935], [Prawitz1965], [Church1956]). The
abbreviated name `imp` follows standard Lean formalization practice (cf. FormalizedFormalLogic)."
Or more simply: "The name `imp` follows standard proof-assistant naming conventions. The
previous `impl` was non-standard."

---

### Claim 5: Gentzen date [Gentzen1935]

**PR text**: Uses [Gentzen1935] throughout.

**Publication history**:
- Gentzen submitted his inaugural dissertation (Habilitationsschrift) to Gottingen in **summer 1933**
- The paper was published in *Mathematische Zeitschrift*, volume 39, in **1935**:
  - Part I: pp. 176-210 (1935)
  - Part II: pp. 405-431 (1935)
- The BibTeX entry in `references.bib` correctly records `year = {1935}`

**Why some sources say "1934-35"**: The volume 39 of *Mathematische Zeitschrift* was issued
across 1934-1935 (journals in this era often had volumes spanning calendar years). Some
bibliographic databases thus cite it as "1934-35" or "1934/35". However, the standard citation
year for both parts is **1935**, as confirmed by:
- Springer (the publisher)
- PhilPapers
- Semantic Scholar
- The encyclopedia.com biography
- The CSLib references.bib entry

The Johansson (1937) paper itself cites Gentzen as "Math. Zeitschrift 39, 176-210, 405-431"
without a year, but this is consistent with the 1935 dating.

**Verdict**: **ACCURATE** -- 1935 is the correct and standard citation year.

---

## Summary of Required Corrections

### Must Fix
- **Claim 4 (naming "imp")**: The sentence on lines 55-56 is misleading. Gentzen, Prawitz,
  and Church used symbols, not the abbreviation "imp". Reword to separate the concept
  (implication as primitive) from the name (formalization convention).

### Recommended Clarification (Optional)
- **Claim 1 (Church §24)**: Consider noting that §24 discusses *alternative* primitive bases
  rather than endorsing the specific five-primitive set. The five-primitive set is motivated by
  intuitionistic considerations, not Church's classical analysis.

### No Changes Needed
- **Claim 2 (Troelstra & van Dalen Ch. 2)**: Accurate as stated.
- **Claim 3 (Johansson 1937)**: Accurate and well-supported by primary source.
- **Claim 5 (Gentzen 1935)**: Correct citation year.

## Sources Requiring Full-Text Access

| Source | Status | What Remains Unverified |
|--------|--------|------------------------|
| Church 1956 | `[NO FILE]` | Exact content of §24; whether it discusses bottom as primitive |
| Troelstra & van Dalen 1988 | `[NO FILE]` | Exact section structure of Ch. 2; detailed completeness strategy |
| Prawitz 1965 | `[NO FILE]` | Notation used; whether "imp" appears anywhere |
| Gentzen 1935 | `[PDF, no OCR]` | Local file is metadata only, not paper content |
| Johansson 1937 | `[PDF + MD]` | **Fully verified** from primary source |

## Research Methods

- Read local literature files: `Johansson1937.md` (full OCR), `Gentzen1935.md` (metadata only),
  `sources.md` (reference catalog)
- Read `references.bib` for BibTeX entries of all cited works
- Web searches for Church §24 table of contents, Troelstra & van Dalen Ch. 2 structure,
  Gentzen publication dating, Johansson negation definition, "imp" naming conventions
- Fetched: Wikipedia (minimal logic, Gentzen), Encyclopedia.com (Gentzen biography),
  HandWiki (minimal logic), Stanford Encyclopedia (intuitionistic logic), Google Books
  (Troelstra & van Dalen TOC), EPDF (Church TOC), Princeton University Press (Church),
  MacTutor (Gentzen biography)
- Cross-referenced Johansson paper OCR (§1 and §4) against PR claims

## Web Sources Consulted

- [Church TOC via EPDF](https://epdf.pub/introduction-to-mathematical-logic-volume-1.html)
- [Princeton University Press - Church](https://press.princeton.edu/books/paperback/9780691029061/introduction-to-mathematical-logic)
- [Troelstra & van Dalen on Google Books](https://books.google.com/books/about/Constructivism_in_Mathematics_Vol_1.html?id=-tc2qp0-2bsC)
- [Gentzen on Encyclopedia.com](https://www.encyclopedia.com/science/dictionaries-thesauruses-pictures-and-press-releases/gentzen-gerhard)
- [Gentzen on MacTutor](https://mathshistory.st-andrews.ac.uk/Biographies/Gentzen/)
- [Gentzen Part I on Springer](https://link.springer.com/article/10.1007/BF01201353)
- [Minimal logic on Wikipedia](https://en.wikipedia.org/wiki/Minimal_logic)
- [Minimal logic on HandWiki](https://handwiki.org/wiki/Minimal_logic)
- [Intuitionistic Logic on SEP](https://plato.stanford.edu/entries/logic-intuitionistic/)
- [Johansson paper on NUMDAM](http://www.numdam.org/item/CM_1937__4__119_0/)
- [Gentzen Part I on PhilPapers](https://philpapers.org/rec/GENUBD-3)
