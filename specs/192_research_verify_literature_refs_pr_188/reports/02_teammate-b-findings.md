# Teammate B Findings (Round 2): BibTeX Audit for PR #188 Scope

**Task**: Audit `references.bib` for completeness against PR-scope files, draft missing BibTeX entries, verify existing entries.

---

## 1. BibKeys Cited in PR-Scope Files

### Connectives.lean
- `Wajsberg1938` — PRESENT
- `McKinsey1939` — PRESENT
- `Johansson1937` — PRESENT
- `Prawitz1965` — PRESENT
- `TroelstraVanDalen1988` — PRESENT
- `Church1956` — PRESENT
- `Heyting1930` — PRESENT
- `Gentzen1935` — PRESENT
- `ChagrovZakharyaschev1997` — PRESENT

### Defs.lean
- `Johansson1937` — PRESENT
- `Gentzen1935` — PRESENT
- `Prawitz1965` — PRESENT
- `TroelstraVanDalen1988` — PRESENT
- `Church1956` — PRESENT
- `ChagrovZakharyaschev1997` — PRESENT

### NaturalDeduction/Basic.lean
- `Johansson1937` — PRESENT
- `Prawitz1965` — PRESENT
- `TroelstraVanDalen1988` — PRESENT
- `Gentzen1935` — PRESENT

### NaturalDeduction/Equivalence.lean
- `Prawitz1965` — PRESENT
- `TroelstraVanDalen1988` — PRESENT

### PR Description (archive/188)
- `Church1956` — PRESENT
- `TroelstraVanDalen1988` — PRESENT
- `Johansson1937` — PRESENT

---

## 2. Known-Missing BibKeys: Status Confirmed

The task listed these as known missing: `Bentzen2023`, `Trufas2024`, `Post1921`, `Henkin1949`, `Tarski1930`, `Godel1930`, `FromJacobsen2022`.

**Search results**: None of these seven BibKeys appear in `references.bib`. However, none of them appear in the PR-scope files either:
- `Connectives.lean`, `Defs.lean`, `Basic.lean`, `Equivalence.lean` do not cite `Bentzen2023`, `Trufas2024`, `Post1921`, `Henkin1949`, `Tarski1930`, `Godel1930`, or `FromJacobsen2022`.
- The PR description (archive/188) also does not cite them.

**Conclusion**: These seven BibKeys are missing from `references.bib` but are also not currently cited in the PR-scope Lean files. They represent background literature referenced in the `specs/literature/README.md` and prior research reports, but are not currently linked from docstrings.

These entries should still be added to `references.bib` as a preventive measure for future use and completeness of the bibliography, since the literature files describe them as relevant context.

---

## 3. CONTRIBUTING.md Citation Conventions

CONTRIBUTING.md (line 87) states:
> "When formalising a concept that is explained in a published resource, please reference the resource in your documentation."

No explicit BibTeX format requirements are specified. The file defers to mathlib style for general coding/documentation standards. Looking at the existing `references.bib` entries, the implicit conventions are:
- Standard BibTeX fields: `author`, `title`, `journal`/`booktitle`, `year`, `volume`, `number`, `pages`, `doi`
- Unicode characters used for accented letters (e.g., `{\"u}`, `{\ss}`, `{\'{o}}`)
- BibKey format: `LastnameYYYY` (e.g., `Gentzen1935`, `Church1956`)
- Multi-author: `LastnameLastnameYYYY` (e.g., `TroelstraVanDalen1988`, `ChagrovZakharyaschev1997`)
- DOI included when available
- No consistent use of `url` or `isbn` across all entries — they appear selectively
- Indentation: 2 spaces for field lines within entries
- Most entries lack `abstract` field (only some newer entries have it)

---

## 4. Drafted Missing BibTeX Entries

### 4.1 Bentzen2023 (Guo, Chen, and Bentzen 2023)

**Source**: `specs/literature/bentzen_2023.md` — arXiv:2310.01916, published in *Logics for AI and Law* (LNGAI/LAL 2023, College Publications).

```bibtex
@inproceedings{Bentzen2023,
  author       = {Guo, Huayu and Chen, Dongheng and Bentzen, Bruno},
  title        = {Verified Completeness in {Henkin}-Style for Intuitionistic
                  Propositional Logic},
  booktitle    = {Logics for New-Generation Artificial Intelligence and
                  Logic, {AI} and Law},
  editor       = {Bentzen, Bruno and Liao, Beishui and Liga, Davide and
                  Markovich, Réka and Wei, Bei and Xiong, Minghui and Xu, Tao},
  pages        = {36--48},
  publisher    = {College Publications},
  year         = {2023},
  url          = {https://arxiv.org/abs/2310.01916},
  doi          = {10.48550/arXiv.2310.01916}
}
```

**Notes**: This is the Lean 3 formalization by Guo, Chen, and Bentzen — not solely by Bentzen. The BibKey `Bentzen2023` is conventional shorthand. The paper appeared in the joint proceedings of the Third International Workshop on Logics for New-Generation Artificial Intelligence and the International Workshop on Logic, AI and Law, 2023.

### 4.2 Trufas2024

**Source**: `specs/literature/trufas_2024.md` — EPTCS 410, 2024, pp. 133–149, doi:10.4204/EPTCS.410.9. Published in the 8th Symposium on Working Formal Methods (FROM 2024).

```bibtex
@inproceedings{Trufas2024,
  author       = {Trufas, Dafina},
  title        = {Intuitionistic Propositional Logic in {Lean}},
  booktitle    = {Proceedings of the 8th Symposium on Working Formal Methods
                  ({FROM} 2024)},
  editor       = {Marin, Madalina and Leu{\c{s}}tean, Laurent},
  series       = {Electronic Proceedings in Theoretical Computer Science},
  volume       = {410},
  pages        = {133--149},
  year         = {2024},
  doi          = {10.4204/EPTCS.410.9}
}
```

### 4.3 Post1921

**Source**: `specs/literature/post_1921.md` — *American Journal of Mathematics*, Vol. 43, No. 3 (1921), pp. 163–185.

```bibtex
@article{Post1921,
  author       = {Post, Emil L.},
  title        = {Introduction to a General Theory of Elementary Propositions},
  journal      = {American Journal of Mathematics},
  volume       = {43},
  number       = {3},
  pages        = {163--185},
  year         = {1921},
  doi          = {10.2307/2370324}
}
```

**Notes**: Post 1921 established the completeness and consistency of the propositional calculus using truth tables and is the historical source for the truth-table method. The DOI `10.2307/2370324` is the JSTOR stable URL for this article.

### 4.4 Henkin1949

**Source**: `specs/literature/henkin_1949.md` — *The Journal of Symbolic Logic*, Vol. 14, No. 3 (Sep., 1949), pp. 159–166.

```bibtex
@article{Henkin1949,
  author       = {Henkin, Leon},
  title        = {The Completeness of the First-Order Functional Calculus},
  journal      = {Journal of Symbolic Logic},
  volume       = {14},
  number       = {3},
  pages        = {159--166},
  year         = {1949},
  doi          = {10.2307/2267044}
}
```

**Notes**: The DOI `10.2307/2267044` is the JSTOR stable identifier for this article.

### 4.5 Tarski1930

**Source**: `specs/literature/README.md` (lines 117–121) — *Fundamentale Begriffe der Methodologie der deduktiven Wissenschaften I*. Monatshefte fur Mathematik und Physik, 37:361–404.

```bibtex
@article{Tarski1930,
  author       = {Tarski, Alfred},
  title        = {Fundamentale {B}egriffe der {M}ethodologie der deduktiven
                  {W}issenschaften. {I}},
  journal      = {Monatshefte f{\"u}r Mathematik und Physik},
  volume       = {37},
  number       = {1},
  pages        = {361--404},
  year         = {1930},
  doi          = {10.1007/BF01696782}
}
```

**Notes**: English translation appears in *Logic, Semantics, Metamathematics*, 2nd ed., Hackett, 1983. The DOI `10.1007/BF01696782` is the Springer link for the Monatshefte volume.

### 4.6 Godel1930

**Source**: `specs/literature/README.md` (lines 123–126) — *Die Vollstandigkeit der Axiome des logischen Funktionenkalkuls*. Monatshefte fur Mathematik und Physik, 37:349–360. Also cited in `specs/literature/henkin_1949.md` (reference [2] in Henkin's bibliography).

```bibtex
@article{Godel1930,
  author       = {G{\"o}del, Kurt},
  title        = {Die {V}ollst{\"a}ndigkeit der {A}xiome des logischen
                  {F}unktionenkalk{\"u}ls},
  journal      = {Monatshefte f{\"u}r Mathematik und Physik},
  volume       = {37},
  number       = {1},
  pages        = {349--360},
  year         = {1930},
  doi          = {10.1007/BF01696781}
}
```

**Notes**: This is the foundational completeness theorem for first-order logic. The `trufas_2024.md` file cites reference [9] as Gödel 1958 (Dialectica), not Gödel 1930 — these are different papers. `Godel1930` refers to the 1930 completeness paper.

### 4.7 FromJacobsen2022

**Source**: `specs/literature/from_2022.md` — EPTCS 357, 2022, pp. 38–55, doi:10.4204/EPTCS.357.4. Published in 16th Logical and Semantic Frameworks with Applications (LSFA 2021).

```bibtex
@inproceedings{FromJacobsen2022,
  author       = {From, Asta Halkj{\ae}r and Jacobsen, Frederik Krogsdal
                  and Villadsen, J{\o}rgen},
  title        = {{SeCaV}: {A} Sequent Calculus Verifier in {Isabelle/HOL}},
  booktitle    = {Proceedings of the 16th Logical and Semantic Frameworks
                  with Applications ({LSFA} 2021)},
  editor       = {Ayala-Rinc{\'o}n, Mauricio and Bonelli, Eduardo},
  series       = {Electronic Proceedings in Theoretical Computer Science},
  volume       = {357},
  pages        = {38--55},
  year         = {2022},
  doi          = {10.4204/EPTCS.357.4}
}
```

**Notes**: The BibKey `FromJacobsen2022` is the name used in the research context of this task. The paper has three authors: From, Jacobsen, and Villadsen. The venue LSFA 2021 was held in 2021 but proceedings published in EPTCS 2022.

---

## 5. Existing Entry Accuracy Audit

### Church1956
**In references.bib**: Author = Church, Alonzo. Title = "Introduction to Mathematical Logic". Volume = 1. Publisher = Princeton University Press. Year = 1956. ISBN = 978-0-691-02906-1.

**Cross-check against**: `specs/literature/church_1956.md` exists. The entry looks correct. Volume 1 (of 2) is the standard reference. ISBN confirmed as correct for the paperback reprint.

**Verdict**: CORRECT — no changes needed.

### Johansson1937
**In references.bib**: Author = Johansson, Ingebrigt. Title = "Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus". Journal = Compositio Mathematica. Volume = 4. Pages = 119–136. Year = 1937. URL = http://www.numdam.org/item/CM_1937__4__119_0/.

**Cross-check against**: `specs/literature/johansson_1937.md` exists. The Numdam URL is a publicly accessible version. All fields match standard bibliographic data.

**Verdict**: CORRECT — no changes needed.

### Gentzen1935
**In references.bib**: Author = Gentzen, Gerhard. Title = "Untersuchungen über das logische Schließen. I". Journal = Mathematische Zeitschrift. Volume = 39. Number = 1. Pages = 176–210. Year = 1935. DOI = 10.1007/BF01201353.

**Cross-check against**: `specs/literature/gentzen_1935.md` exists. The entry matches known bibliographic data. Part I covers the sequent calculus; there was also a Part II in the same volume/year. The BibKey `Gentzen1935` conventionally refers to Part I.

**Minor note**: The DOI `10.1007/BF01201353` links to the Springer page. The pages 176–210 are for Part I. This is correct.

**Verdict**: CORRECT — no changes needed.

### McKinsey1939
**In references.bib**: Author = McKinsey, J. C. C. Title = "Proof of the Independence of the Primitive Symbols of Heyting's Calculus of Propositions". Journal = Journal of Symbolic Logic. Volume = 4. Number = 4. Pages = 155–158. Year = 1939. DOI = 10.2307/2268715.

**Verdict**: CORRECT — standard reference, matches all bibliographic data.

### Wajsberg1938
**In references.bib**: Author = Wajsberg, Mordchaj. Title = "Untersuchungen über den Aussagenkalkül von A. Heyting". Journal = Wiadomości Matematyczne. Volume = 46. Pages = 45–101. Year = 1938.

**Note**: This entry lacks a DOI and URL, which is appropriate since this is a relatively obscure Polish mathematics journal from 1938 that is not widely digitized. No correction needed.

**Verdict**: CORRECT — no changes needed.

### Heyting1930
**In references.bib**: Author = Heyting, Arend. Title = "Die formalen Regeln der intuitionistischen Logik". Journal = Sitzungsberichte der Preußischen Akademie der Wissenschaften, physikalisch-mathematische Klasse. Year = 1930. Pages = 42–56.

**Note**: This entry lacks volume/number fields, but these are not meaningful for the Sitzungsberichte format (it was a proceedings/session record). The pages 42–56 match the standard bibliographic reference. The entry in `bentzen_2023.md` (reference [10]) confirms: "Sitzungsbericht Preußische Akademie der Wissenschaften Berlin, physikalisch-mathematische Klasse II pp. 42–56 (1930)."

**Verdict**: CORRECT — the format is appropriate for this publication type.

### Prawitz1965
**In references.bib**: Author = Prawitz, Dag. Title = "Natural Deduction: A Proof-Theoretical Study". Publisher = Almqvist & Wiksell. Address = Stockholm. Year = 1965. Note = "Reprinted by Dover Publications, 2006".

**Verdict**: CORRECT — standard reference. The Dover reprint note is a helpful addition for readers seeking modern access.

### TroelstraVanDalen1988
**In references.bib**: Author = Troelstra, A. S. and van Dalen, D. Title = "Constructivism in Mathematics: An Introduction". Volume = 1. Series = Studies in Logic and the Foundations of Mathematics. Number = 121. Publisher = North-Holland. Address = Amsterdam. Year = 1988. ISBN = 978-0-444-70506-8.

**Verdict**: CORRECT — Volume 1 (of 2) is the standard reference for propositional logic topics. The series number 121 is correct.

---

## 6. Summary

### Missing Entries (7 total — none currently cited in PR-scope files)

| BibKey | Status | Issue |
|---|---|---|
| `Bentzen2023` | MISSING | Not in `references.bib`; cited in research reports only |
| `Trufas2024` | MISSING | Not in `references.bib`; cited in research reports only |
| `Post1921` | MISSING | Not in `references.bib`; background literature |
| `Henkin1949` | MISSING | Not in `references.bib`; background literature |
| `Tarski1930` | MISSING | Not in `references.bib`; background literature |
| `Godel1930` | MISSING | Not in `references.bib`; background literature |
| `FromJacobsen2022` | MISSING | Not in `references.bib`; background literature |

### Existing Entries Audit Result

All 8 checked entries (`Church1956`, `Johansson1937`, `Gentzen1935`, `McKinsey1939`, `Wajsberg1938`, `Heyting1930`, `Prawitz1965`, `TroelstraVanDalen1988`) are **CORRECT** — no corrections needed.

### CONTRIBUTING.md Citation Format

- No explicit BibTeX format requirements in CONTRIBUTING.md
- Existing pattern in `references.bib`: `LastnameYYYY` keys, standard BibTeX fields, Unicode escape sequences for special characters (e.g., `{\"u}`, `{\ss}`)
- Draft entries above follow this pattern
