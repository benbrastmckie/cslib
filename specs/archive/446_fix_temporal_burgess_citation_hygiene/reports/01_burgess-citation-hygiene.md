# Research Report — Task 446: Temporal Burgess Citation Hygiene

**Task type:** cslib (markdown/docstring hygiene; no proof changes)
**Scope:** Convert plain-prose citations in the `Cslib/Logics/Temporal/` tree to the uniform
bracket `[Description][BibKey]` house style, disambiguating `Burgess1982I` vs `Burgess1982II`.
**Zero-debt note:** This is a pure documentation/comment task. No `sorry`, no axioms, no proof
obligations. Every change is inside a `/-! ... -/` or `/-- ... -/` doc block.

---

## 1. Path Corrections vs Task Description

The task description lists some stale paths. Actual locations (verified by grep):

| Task said | Actual file |
|-----------|-------------|
| `Metalogic/TruthLemma.lean` (:34, :274) | `Metalogic/Chronicle/TruthLemma.lean` (:34, :274) |
| `Semantics/RRelation.lean` (:21) | `Metalogic/Chronicle/RRelation.lean` (:21) |
| `Metalogic/Soundness.lean` (:28) | correct |
| `Metalogic/DenseSoundness.lean` (:28) | correct |

There is **no** `Semantics/RRelation.lean` and **no** `Metalogic/TruthLemma.lean` (only the
`Chronicle/` variants). The implementer must use the corrected paths below.

---

## 2. House Style (established, correct examples)

Reference-block bullet style (from `Syntax/Formula.lean:82-83` and `Tableau/Defs.lean:54-56`):

```
* [First. Last, *Title in Title Case*][BibKey]
```

- Bullet marker is `*` (asterisk), one space, then the bracket pair.
- First bracket: author initials + surname, comma, then `*Title*` (Markdown italic), Title Case.
- Second bracket: the exact BibKey — no space between the two brackets.
- Optional trailing gloss after the citation: ` — <note>` (em dash), e.g. a section pointer.

Confirmed correct existing examples:
- `* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]`
- `* [D. Gabbay, A. Pnueli, S. Shelah, J. Stavi, *On the temporal analysis of fairness*][GPSS1980]`
- `* [J. Burgess, *Basic Tense Logic*][Burgess1984]`
- `* [R. Smullyan, *First-Order Logic*][Smullyan1968]`

**Inline** citation style (from `Theorems.lean:24`): bare bracketed key, e.g. `([Boudou2017])`.

---

## 3. references.bib Validation

Repo-root `./references.bib`. All keys cited in the Temporal tree **resolve**. No missing keys,
**no new BibTeX entries required**.

| BibKey | bib line | Title in bib | Used for |
|--------|----------|--------------|----------|
| `Burgess1982I` | 660 | Axioms for Tense Logic. I. "Since" and "Until" | **BX axiom system** (Since/Until axioms) |
| `Burgess1982II` | 671 | Axioms for Tense Logic. II. Time Periods | **Chronicle construction / Claim 2.11 / Lemmas 2.2–2.11** |
| `Burgess1984` | 682 | Basic Tense Logic | Tableau/Defs.lean (already bracketed, OK) |
| `Kamp1968` | 693 | Tense Logic and the Theory of Linear Order | Formula.lean (already bracketed, OK) |
| `GPSS1980` | 700 | On the Temporal Analysis of Fairness | Formula.lean, Tableau/Defs.lean (OK) |
| `Xu1988` | 712 | On Some U,S-Tense Logics | Completeness.lean (prose → convert) |
| `Reynolds1994` | 741 | Axiomatising First-Order Temporal Logic… | Tableau tree (already bracketed) |
| `Smullyan1968` | 210 | First-Order Logic | Tableau tree (already bracketed, OK) |
| `Boudou2017` | 762 | A Decidable Intuitionistic Temporal Logic | Theorems.lean (already bracketed, OK) |

**Keys present / used:** all of the above. **Keys missing:** none. **Candidate new entries:** none.
**Citations pointing to non-existent keys:** none.

### Disambiguation rationale (Burgess1982I vs Burgess1982II)

- **Burgess1982II ("Time Periods")** — the chronicle/period completeness construction. The code
  already names this paper explicitly at every chronicle site (`"Axioms for tense logic II: Time
  periods"`), and Claim 2.11 + Lemmas 2.2–2.11 belong to that construction. Preserve this intent.
- **Burgess1982I ("Since"/"Until")** — the **BX axiom system** proper (the Until/Since axiom
  schemata on linear orders). The subtitle "Since and Until" matches the axiom-system references
  in `Soundness.lean`, `DenseSoundness.lean`, and the axiom part of `Completeness.lean`.

`Completeness.lean:40` currently conflates both ("BX axiom system **and** completeness") in one
bullet → split into two bullets (I for the axioms, II for the completeness/Claim 2.11).

---

## 4. Site-by-Site Conversion Table (REQUIRED — Metalogic scope)

All paths under `Cslib/Logics/Temporal/`. Bullet marker unified to `*`.

| # | file:line | current text | target text |
|---|-----------|--------------|-------------|
| 1 | `Metalogic/Chronicle/TruthLemma.lean:34` | `- Burgess 1982: Section 2, Claim 2.11` | `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — Section 2, Claim 2.11` |
| 2 | `Metalogic/Chronicle/TruthLemma.lean:274` (inline) | `This is Claim 2.11 of Burgess 1982, adapted to the temporal logic setting. -/` | `This is Claim 2.11 of Burgess (see [Burgess1982II]), adapted to the temporal logic setting. -/` |
| 3 | `Metalogic/Soundness.lean:28` | `* Burgess (1982) — BX axiom system` | `* [J. Burgess, *Axioms for Tense Logic I: Since and Until*][Burgess1982I] — BX axiom system` |
| 4 | `Metalogic/DenseSoundness.lean:28` | `- Burgess (1982): BX axiom system for temporal logic` | `* [J. Burgess, *Axioms for Tense Logic I: Since and Until*][Burgess1982I] — BX axiom system for temporal logic` |
| 5 | `Metalogic/Chronicle/RRelation.lean:21` | `* Burgess 1982: "Axioms for tense logic II: Time periods"` | `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]` |
| 6 | `Metalogic/Chronicle/ChronicleToCountermodel.lean:33` | `- Burgess 1982: Section 2, Claim 2.11` | `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — Section 2, Claim 2.11` |
| 7 | `Metalogic/Chronicle/PointInsertion.lean:41` | `* Burgess 1982: "Axioms for tense logic II: Time periods"` | `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]` |
| 8 | `Metalogic/Chronicle/ChronicleConstruction.lean:52` | `- Burgess 1982: "Axioms for tense logic II: Time periods", Section 2` | `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — Section 2` |
| 9 | `Metalogic/Chronicle/ChronicleTypes.lean:21` | `* Burgess 1982: "Axioms for tense logic II: Time periods"` | `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]` |
| 10 | `Metalogic/Chronicle/CounterexampleElimination.lean:40` | `- Burgess 1982: "Axioms for tense logic II: Time periods", Section 2` | `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — Section 2` |
| 11 | `Metalogic/Completeness.lean:40` | `* Burgess (1982) — BX axiom system and completeness` | **split into two bullets:** `* [J. Burgess, *Axioms for Tense Logic I: Since and Until*][Burgess1982I] — BX axiom system` and `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — chronicle completeness (Claim 2.11)` |
| 12 | `Metalogic/Completeness.lean:41` | `* Xu (1988) — Temporal completeness proofs` | `* [M. Xu, *On Some U,S-Tense Logics*][Xu1988] — temporal completeness proofs` |

Notes:
- Sites 1, 4, 6, 8, 10 also change the bullet marker `-` → `*` for uniformity with house style.
- Site 2 is **inline prose**, not a reference list; keep the sentence and just link the key.
- Site 11: after the split the block gains one bullet (renumbering not needed — bullets are
  unordered).

---

## 5. Docstring Tidy-Ups (advisory, low-risk)

These are prose that name Burgess for orientation, not formal citations. They are **out of the
required conversion scope** but listed so the implementer can decide on uniformity. Recommended:
leave as-is unless doing a full sweep, since they read as informal narration, not bibliography.

- `RRelation.lean:14` `# r-Relation Lemmas (Burgess 1982, Lemmas 2.2-2.5)` — title header.
- `PointInsertion.lean:15` `# Point Insertion Lemmas (Burgess 2.4-2.8)`.
- `ChronicleConstruction.lean:19` `…construction from Burgess 1982 Section 2.`
- `CounterexampleElimination.lean:15` `# Counterexample Elimination (Burgess 2.9-2.10)`.
- `Completeness.lean:98` `The truth lemma (Burgess Claim 2.11) connects satisfaction …`.

If uniformity is desired for the module-title headers, at most append `[Burgess1982II]` once per
header (e.g. `# r-Relation Lemmas ([Burgess1982II], Lemmas 2.2–2.5)`). Optional.

---

## 6. Explicit EXCLUSIONS — do NOT touch (not citations)

These "Burgess" occurrences are **Lean identifiers, module names, or informal proof-comment
shorthand** and must remain unchanged:

- Identifiers/definitions: `BurgessR3Maximal`, `burgessR`, `burgessRSince`, `burgessRSet`,
  `burgessR3`, `BurgessR3Maximal_extension_fails`, `BurgessR3Maximal_g_content_sub`,
  `BurgessR3Maximal_sdc`, `BurgessR3Maximal_bot_not_mem`.
- Module / import: `Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Burgess`,
  the `**Burgess** (`PointInsertion.Burgess`)` module description bullet.
- Section headers naming lemmas informally: `/-! ## Burgess Lemma 2.3 …`,
  `## Burgess Absorption (Lemma 2.5)`, `Burgess C4a`, `Burgess C5a`, `Burgess 2.10 induction`,
  and the many inline proof comments referencing "Burgess 2.x".
- `Burgess-Xu (BX)` phrasing in `ProofSystem/Axioms.lean:13,67,71` — this is the name of the
  system, not a citation.

These are semantic code names; converting them would break compilation or muddy proof narration.

---

## 7. Out-of-scope observations (report only, do NOT fix in task 446)

- **Reynolds1994 citation mismatch (Tableau tree):** `Tableau/{Saturation,Closure,Rules,
  Soundness,Completeness}.lean` render `[R. Reynolds, *An axiomatization of prior's tense
  logic*][Reynolds1994]`, but `Reynolds1994` in the bib is titled *Axiomatising First-Order
  Temporal Logic: Until and Since over Linear Time* (and its `year` field is 1996 despite the
  `1994` key). Description/title do not match the entry. Tableau is a sibling of `Metalogic/`,
  outside the required scope; flag for a separate bib-hygiene task.
- These Tableau reference blocks are already in correct bracket form; only the Reynolds
  description text is questionable.

---

## 8. Verification plan for the implementer

Pure comment edits — no Lean semantics change. After edits:

1. `lake build Cslib.Logics.Temporal.Metalogic.Completeness` (and the other edited modules) to
   confirm docstrings still parse (unterminated `/-! -/` is the only real risk).
2. `lake exe lint-style` — text linter (line length; the longer bracket bullets are still well
   under limits).
3. Grep guard: `grep -rn "Burgess (19\|Burgess 1982:" Cslib/Logics/Temporal/Metalogic/` should
   return **zero** prose-citation hits after conversion (identifier/header hits excluded).
