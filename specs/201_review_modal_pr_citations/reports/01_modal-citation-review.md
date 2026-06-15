# Research Report: Modal PR Citation Review

- **Task**: 201 - Review modal PR citations
- **Started**: 2026-06-14T00:00:00Z
- **Completed**: 2026-06-14T01:00:00Z
- **Session**: sess_1781505781_7a3c35
- **Standards**: report-format.md, artifact-formats.md

## Executive Summary

- **Two factual errors found** in section-number citations: CSLib docstrings cite `[ChagrovZakharyaschev1997] Section 1.1` for the box-as-primitive convention, but Section 1.1 covers classical propositional logic; the modal language with box as primitive is defined in **Section 3.1** of that book.
- **One substantive accuracy issue**: CSLib docstrings claim "Box (necessity) is the canonical primitive modal operator ... following [Blackburn2001] Chapter 1." In fact, Blackburn et al. (2001) Definition 1.9 defines **diamond** as the primitive modal operator, with box derived as `box phi := neg diamond neg phi`. The specific Blackburn citation does not support the claim -- it supports the opposite convention.
- **Proof-theoretic justification for box-as-primitive**: The choice of box over diamond as primitive is not merely conventional -- it is the proof-theoretically natural choice. Necessitation (`if ⊢ φ then ⊢ □φ`) and the K axiom (`□(φ → ψ) → (□φ → □ψ)`) are pure proof rules stated in terms of a single primitive. With diamond as primitive, necessitation becomes the interaction law `if ⊢ φ then ⊢ ¬◇¬φ`, mixing two connectives (negation and diamond). Pure proof rules on a single primitive make for a cleaner foundation. This argument should be cited alongside Chagrov & Zakharyaschev as justification for CSLib's design choice.
- **All 5 BibKeys present and correct** in `references.bib` with accurate bibliographic metadata.
- **All literature files exist** and can be cross-checked against claims.
- **Bentzen2023 and Trufas2024 citations are appropriate** for the five-primitive signature precedent, though neither paper uses a box operator (both formalize intuitionistic propositional logic, not modal logic).
- **Johansson1937 citation is accurate**: the paper does introduce minimal logic with `bot` as a primitive and negation defined as `neg phi := phi -> bot`.

## Citation Inventory

| BibKey | Cited In | Claim | refs.bib | Literature | Accuracy |
|--------|----------|-------|----------|------------|----------|
| Blackburn2001 | Basic.lean:29,47,94; Connectives.lean:72,112 | Box is canonical primitive in Ch. 1 | Present, correct | `blackburn_2001/` (chunked) | **INACCURATE** -- Ch. 1 Def. 1.9 uses diamond as primitive |
| ChagrovZakharyaschev1997 | Basic.lean:29,95; Connectives.lean:53,73,113 | Box as primitive in Section 1.1 | Present, correct | `chagrov_1997/` (chunked) | **WRONG SECTION** -- Section 1.1 is classical logic; modal box is in Section 3.1 |
| Bentzen2023 | Not directly in code; cited in task 197 PR description | Five-primitive IPL signature precedent | Present, correct | `bentzen_2023.md` | Accurate for IPL `{atom, bot, impl, and, or}` |
| Trufas2024 | Not directly in code; cited in task 197 PR description | Five-primitive IPL signature precedent | Present, correct | `trufas_2024.md` | Accurate for IPL `{var, bottom, and, or, implication}` |
| Johansson1937 | Connectives.lean:43 | Bot-as-primitive, neg defined as `phi -> bot` | Present, correct | `johansson_1937.md` | Accurate |

## Detailed Per-Citation Findings

### 1. Blackburn2001

**BibKey verification**: Present at `references.bib` line 57 as `@book{Blackburn2001, ...}`.
- Author: "Blackburn, Patrick and Rijke, Maarten de and Venema, Yde" -- correct
- Title: "Modal Logic" -- correct
- Publisher: Cambridge University Press -- correct
- Year: 2001 -- correct
- Series: Cambridge Tracts in Theoretical Computer Science -- correct

**Literature availability**: `specs/literature/blackburn_2001/` contains 27 chunked markdown files covering Chapters 1-7.

**Cross-check against primary source**:

CSLib claims (Basic.lean lines 28-31):
> Box (necessity) is the canonical primitive modal operator in classical systems, following [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001] Chapter 1

What Blackburn2001 Chapter 1 actually says:
- **Definition 1.9** (Section 1.2, "Modal Languages"): "The basic modal language is defined using a set of proposition letters... and a unary modal operator **diamond** ('diamond'). The well-formed formulas of the basic modal language are given by the rule: phi ::= p | bot | neg phi | phi or phi | **diamond** phi"
- Box is then **derived**: "we have a dual operator box ('box') for our diamond which is defined by box phi := neg diamond neg phi"
- **Definition 1.20** (Section 1.3, "Models and Frames"): The satisfaction definition lists diamond as the primitive clause: "M,w |= diamond phi iff for some v in W with Rwv we have M,v |= phi. It follows from this definition that M,w |= box phi if and only if for all v in W such that Rwv, we have M,v |= phi."

**Verdict**: The citation is **factually inaccurate**. Blackburn2001 Chapter 1 uses diamond as the primitive, not box. However, the choice of box as primitive is not merely a matter of convention -- it is the proof-theoretically natural choice. With box as primitive, the necessitation rule (`if ⊢ φ then ⊢ □φ`) and the K axiom (`□(φ → ψ) → (□φ → □ψ)`) are pure proof rules stated in terms of a single primitive connective. With diamond as primitive, necessitation becomes the interaction law `if ⊢ φ then ⊢ ¬◇¬φ`, which mixes negation and diamond rather than operating on a single primitive. Pure proof rules make for a cleaner axiomatic foundation -- the proof system speaks directly in terms of its primitive rather than requiring detours through derived notation.

**Recommendation**: Reword the docstring to give the proof-theoretic justification and correct the citations:
- State that box is primitive because necessitation and the K axiom are pure proof rules on box -- with diamond as primitive, necessitation becomes the interaction law `¬◇¬`, mixing two connectives.
- Cite [ChagrovZakharyaschev1997] Section 3.1 for the box-first presentation.
- Cite [Blackburn2001] Chapter 1 for the diamond-first alternative and the interdefinability of box and diamond in classical modal logic.
- This is stronger than merely citing convention: it gives a principled reason for the design choice.

### 2. ChagrovZakharyaschev1997

**BibKey verification**: Present at `references.bib` line 67 as `@book{ChagrovZakharyaschev1997, ...}`.
- Author: "Chagrov, Alexander and Zakharyaschev, Michael" -- correct
- Title: "Modal Logic" -- correct
- Series: Oxford Logic Guides, volume 35 -- correct
- Publisher: Oxford University Press -- correct
- Year: 1997 -- correct
- ISBN: 978-0-19-853779-3 -- correct

**Literature availability**: `specs/literature/chagrov_1997/` contains 5 chunked markdown files covering the introduction (Ch 1-4) and Kripke semantics (Ch 5-6).

**Cross-check against primary source**:

CSLib cites "Section 1.1" in multiple locations:
- Basic.lean line 29: `[ChagrovZakharyaschev1997] Section 1.1`
- Basic.lean line 95: `[ChagrovZakharyaschev1997] Section 1.1`
- Connectives.lean line 73: `[ChagrovZakharyaschev1997] Section 1.1`
- Connectives.lean line 113: `[ChagrovZakharyaschev1997] Section 1.1`

What Section 1.1 actually covers:
- Chapter 1 is titled "CLASSICAL LOGIC"
- Section 1.1 is titled "Syntax and semantics" and defines the classical propositional language with primitives {variables, bot, and, or, imp} -- **no modal operators at all**

Where the modal language is actually defined:
- Chapter 3 is titled "MODAL LOGICS"
- **Section 3.1** "Possible world semantics" (starting at line 2506 in the literature file): "The propositional modal language MC is obtained by enriching the language L with the new unary connective **box**" (line 2518-2519)
- Diamond is then derived: "We define the connective O [diamond] as dual to box, i.e., by taking O phi = neg box neg phi" (line 2531-2532)

**Verdict**: The section reference is **incorrect**. Section 1.1 is about classical propositional logic; the modal language with box as primitive is defined in Section 3.1. Notably, Chagrov & Zakharyaschev *do* use box as the primitive modal operator (unlike Blackburn), so the substantive claim about box-as-primitive is supported -- just with the wrong section number.

**Recommendation**: Change all occurrences of `Section 1.1` to `Section 3.1` when referencing ChagrovZakharyaschev1997 in the context of modal logic primitives.

### 3. Bentzen2023

**BibKey verification**: Present at `references.bib` line 33 as `@inproceedings{Bentzen2023, ...}`.
- Author: "Guo, Huayu and Chen, Dongheng and Bentzen, Bruno" -- correct
- Title: "Verified Completeness in {Henkin}-Style for Intuitionistic Propositional Logic" -- correct
- Booktitle: "Logics for New-Generation Artificial Intelligence and Logic, AI and Law" -- correct
- Year: 2023 -- correct
- Pages: 36-48 -- correct
- DOI: 10.48550/arXiv.2310.01916 -- correct

**Literature availability**: `specs/literature/bentzen_2023.md` -- full paper text (823 lines).

**Cross-check against primary source**:

The paper defines IPL formulas with 5 constructors:
```lean
inductive form : Type
| atom : N -> form
| bot  : form
| impl : form -> form -> form
| and  : form -> form -> form
| or   : form -> form -> form
```

This is cited as precedent for the five-primitive signature `{atom, bot, imp, and, or}` used in CSLib's propositional logic. The citation is accurate -- Bentzen2023 does indeed use these five constructors.

**Note**: Bentzen2023 formalizes *intuitionistic propositional logic*, not modal logic. The paper includes no box or diamond operator. The citation is used specifically to support the propositional primitives (which modal logic inherits minus `and`/`or`), not the modal operator choice. This is appropriate usage.

**Verdict**: Accurate and appropriate.

### 4. Trufas2024

**BibKey verification**: Present at `references.bib` line 462 as `@inproceedings{Trufas2024, ...}`.
- Author: "Trufas, Dafina" -- correct
- Title: "Intuitionistic Propositional Logic in {Lean}" -- correct
- Booktitle: "Proceedings of the 8th Symposium on Working Formal Methods (FROM 2024)" -- correct
- Series: "Electronic Proceedings in Theoretical Computer Science" -- correct
- Volume: 410 -- correct
- Pages: 133-149 -- correct
- Year: 2024 -- correct
- DOI: 10.4204/EPTCS.410.9 -- correct

**Literature availability**: `specs/literature/trufas_2024.md` -- full paper text (782 lines).

**Cross-check against primary source**:

The paper defines IPL formulas with 5 constructors:
```lean
inductive Formula where
| var : Var -> Formula
| bottom : Formula
| and : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| implication : Formula -> Formula -> Formula
```

Like Bentzen2023, this supports the five-primitive signature precedent. The paper explicitly derives negation as `neg phi := phi => bot` and top as `top := neg bot`.

**Note**: Same caveat as Bentzen2023 -- this is an IPL paper, not modal logic. The citation is used for propositional-level primitive choices, not modal operator choices. Appropriate usage.

**Verdict**: Accurate and appropriate.

### 5. Johansson1937

**BibKey verification**: Present at `references.bib` line 277 as `@article{Johansson1937, ...}`.
- Author: "Johansson, Ingebrigt" -- correct
- Title: "Der Minimalkalkul, ein reduzierter intuitionistischer Formalismus" -- correct
- Journal: "Compositio Mathematica" -- correct
- Volume: 4 -- correct
- Pages: 119-136 -- correct
- Year: 1937 -- correct
- URL: http://www.numdam.org/item/CM_1937__4__119_0/ -- correct

**Literature availability**: `specs/literature/johansson_1937.md` -- full paper text (552 lines, OCR from German).

**Cross-check against primary source**:

Connectives.lean line 43 cites Johansson1937 in the context of "Der Minimalkalkul". The paper:
- Defines the "Minimalkalkul" (minimal calculus) by removing axiom 4.1 (`neg a -> (a -> b)`) from Heyting's intuitionistic logic
- Section 4 introduces `A` ("Widerspruch"/contradiction) as an undefined primitive symbol, with negation defined as `neg phi := phi -> A` (line 68-73 in the literature file: "Die Moglichkeit la durch a -> A (wo A 'Widerspruch' oder 'etwas Falsches' bedeutet) zu ersetzen")
- This is exactly the convention CSLib follows: `bot` as primitive, `neg phi := phi -> bot`

**Verdict**: Accurate and well-grounded.

## Additional Citations in Connectives.lean

Connectives.lean includes several additional citations not in the original task scope but relevant for completeness:

| BibKey | Line | Claim | Status |
|--------|------|-------|--------|
| Wajsberg1938 | 44 | Classical encodings of and/or are only propositionally equivalent | Present in refs.bib (line 299); not verified against primary source (German) |
| McKinsey1939 | 45-46 | Independence of and/or from imp in Heyting's calculus | Present in refs.bib (line 287); not verified against primary source |
| Prawitz1965 | 47 | Natural deduction reference | Present in refs.bib (line 400); standard reference |
| TroelstraVanDalen1988 | 48-49 | Constructivism reference | Present in refs.bib (line 450); standard reference |
| Church1956 | 50 | Mathematical logic reference | Present in refs.bib (line 141); standard reference |
| Heyting1930 | 51 | Formal rules of intuitionistic logic | Present in refs.bib (line 261); standard reference |
| Gentzen1935 | 52 | Natural deduction and sequent calculus | Present in refs.bib (line 195); standard reference |

All additional BibKeys are present and correctly formatted in `references.bib`. These are standard textbook references and do not require primary-source cross-checking.

## Gap Analysis

### Uncited Claims

1. **Basic.lean line 31-33**: "Box is chosen because it corresponds to universal quantification over accessible worlds, preserves conjunction (box(phi and psi) <-> box phi and box psi), distributes over implication (axiom K), and is the subject of necessitation." These are standard facts that do not strictly need individual citations, but the conjunction-preservation claim could benefit from a reference.

2. **Basic.lean line 36-38**: "This derivation relies on excluded middle (neg neg p <-> p) and fails in intuitionistic or minimal modal logic, where box and diamond are independent operators." The claim about independence of box and diamond in non-classical modal logics could cite a specific source (e.g., Simpson 1994 or Wijesekera 1990 for intuitionistic modal logic).

3. **The frame condition theorems** (T, B, 4, 5, D in Basic.lean) are not individually cited. These are completely standard results found in every modal logic textbook, so citations are not strictly necessary, but adding "[Blackburn2001] Proposition 3.3" or similar would follow best practice.

4. **Denotation.lean** contains no citations at all. The denotational semantics approach is described as "inspired by the development of Cslib.Logic.HML" (in Basic.lean line 49), which is an internal reference. No external literature citation is needed for this file specifically.

### Missing References

No references are missing from `references.bib` for the citations actually used. All BibKeys resolve correctly.

### CONTRIBUTING.md Compliance

CONTRIBUTING.md (line 87) states: "When formalising a concept that is explained in a published resource, please reference the resource in your documentation."

The current documentation meets this requirement -- all major design choices (primitive set, operator convention, derived connectives) are documented with literature references. The section-number errors should be corrected for accuracy.

## Recommendations

### Critical (factual errors)

1. **Fix ChagrovZakharyaschev1997 section references**: Change all occurrences of `Section 1.1` to `Section 3.1` in:
   - `Basic.lean` lines 29, 95
   - `Connectives.lean` lines 73, 113

2. **Reword Blackburn2001 box-as-primitive claim with proof-theoretic justification**: Blackburn2001 Ch. 1 uses diamond as primitive. The docstrings should give the principled reason for CSLib's box-as-primitive choice: necessitation (`if ⊢ φ then ⊢ □φ`) and the K axiom are pure proof rules on a single primitive. With diamond as primitive, necessitation becomes the interaction law `if ⊢ φ then ⊢ ¬◇¬φ`, mixing negation and diamond. Suggested wording: "CSLib takes box as primitive because the necessitation rule and K axiom are pure proof rules on box; with diamond primitive, necessitation becomes the interaction law ¬◇¬ ([Blackburn2001] Ch. 1 takes the diamond-first alternative). See [ChagrovZakharyaschev1997] Section 3.1 for the box-first presentation."

### Advisory (improvements)

3. **Add note about IPL vs. modal context for Bentzen/Trufas**: If these are cited in a PR description for the Modal PR, clarify that they establish precedent for the propositional primitives `{atom, bot, imp}`, not for the modal operator choice.

4. **Consider citing Burgess1984**: Task 197 Report 02 already recommends adding Burgess1984 to the PR description to strengthen the tense logic roadmap argument. The `@incollection{Burgess1984, ...}` entry is already in `references.bib`.

5. **Connectives.lean line 53**: "Chapter 1" of ChagrovZakharyaschev1997 should be "Chapter 3" -- same section-numbering issue.

## Files Examined

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean` (424 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Denotation.lean` (85 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/LogicalEquivalence.lean` (84 lines)
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Connectives.lean` (127 lines)
- `/home/benjamin/Projects/cslib/references.bib` (709 lines)
- `/home/benjamin/Projects/cslib/CONTRIBUTING.md`
- `/home/benjamin/Projects/cslib/specs/literature/blackburn_2001/ch01_relational-structures.md` (Section 1.2 Modal Languages)
- `/home/benjamin/Projects/cslib/specs/literature/blackburn_2001/ch01_models-and-frames.md` (Section 1.3 Satisfaction)
- `/home/benjamin/Projects/cslib/specs/literature/chagrov_1997/p01_introduction.md` (Sections 1.1 and 3.1)
- `/home/benjamin/Projects/cslib/specs/literature/bentzen_2023.md`
- `/home/benjamin/Projects/cslib/specs/literature/trufas_2024.md`
- `/home/benjamin/Projects/cslib/specs/literature/johansson_1937.md`
- `/home/benjamin/Projects/cslib/specs/197_modal_upstream_initial_pr/reports/02_literature-grounded-analysis.md`
