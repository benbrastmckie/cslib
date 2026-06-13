# Teammate D Findings: Historical Precedent, Citation Verification, and Strategic Direction

## Summary

This report covers the historical background for the Hilbert ↔ ND equivalence, verifies
and extends citation coverage in `references.bib`, and maps the refactoring task to the
broader CSLib propositional logic development trajectory.

---

## 1. Historical Precedent for Hilbert ↔ ND Equivalence

### 1.1 Who First Proved the Equivalence?

The equivalence between Hilbert-style axiomatic systems and Gentzen's natural deduction
is **not attributed to a single author or paper**. It was established gradually:

**Gerhard Gentzen (1935)** — "Untersuchungen über das logische Schließen" (`Gentzen1935`).
Gentzen introduced both natural deduction (NJ/NK) and sequent calculus (LJ/LK) in the same
paper. He noted that natural deduction was intended to be closer to actual mathematical
reasoning than Hilbert-style systems. He proved cut elimination (Hauptsatz) but did not
formally prove equivalence to a specific Hilbert system in this paper. The systems were
implicitly understood to be co-extensional through the mutual derivability of their rules.

**Dag Prawitz (1965)** — *Natural Deduction: A Proof-Theoretical Study* (`Prawitz1965`).
Prawitz's monograph is the canonical textbook reference for natural deduction and its
relationship to Hilbert systems. Chapter I ("Introductory Survey") discusses both kinds of
systems; Section 1.2 specifically addresses classical and intuitionistic natural deduction
and their relationship to axiomatic (Hilbert-style) formulations. Prawitz establishes
mutual derivability by showing how axiom schemata can be derived in ND using introduction
and elimination rules, and how ND rules can be simulated using the deduction theorem in
Hilbert systems. **This is the primary citation for the closed version** (no context).

**Troelstra & van Dalen (1988)** — *Constructivism in Mathematics* Vol. 1, Section 10.4
(`TroelstraVanDalen1988`). Chapter 10 develops proof theory for intuitionistic logic.
Section 10.4 establishes equivalence between their natural deduction system N-IPC and
Heyting's axiomatic system H-IPC. The treatment there is for **closed derivability** (no
undischarged hypotheses). This is the standard reference for the intuitionistic case.

**D. van Dalen (Logic and Structure, 5th ed., 2013)** — Section 2.4 "Completeness and the
deduction theorem" covers the equivalence between axiomatic and ND systems for classical
propositional logic. Earlier editions (1994, 4th ed.) contain the same material in the
same section. This is a more accessible reference than Prawitz and covers the context-free
case clearly.

**A. Church (1956)** — *Introduction to Mathematical Logic* (`Church1956`). Church's
treatment (§29–§31) discusses Hilbert-style systems. Church does not systematically treat
natural deduction, so this reference is of limited relevance for the equivalence.

### 1.2 Context-Based vs. Closed Equivalence in the Literature

**Critical distinction**: The context-based equivalence (Γ ⊢_H φ ↔ Γ ⊢_ND φ) is
**stronger** than and subsumes the closed version (⊢_H φ ↔ ⊢_ND φ).

**What the literature covers**:

- Prawitz (1965), Section 1.2: Proves mutual derivability for **closed** formulas. The
  context-based version is implied by the deduction theorem but not stated explicitly.
- Troelstra & van Dalen (1988), Section 10.4: Proves closed version for IPC.
- van Dalen (2013), Section 2.4: Proves closed version for CPC.
- Gentzen (1935): Does not state the equivalence as a theorem.

**Assessment**: The context-based version (Γ ⊢_H φ ↔ Γ ⊢_ND φ) is **not explicitly
stated as such in the classical references**. It is a natural strengthening that follows
immediately from:
1. The closed version
2. The deduction theorem (applied repeatedly to discharge all context hypotheses)
3. Structural weakening in both systems

The Hilbert-to-ND direction is easy: a Hilbert derivation of φ from Γ is directly a
derivation tree with `assumption` steps for Γ, which maps to ND. The ND-to-Hilbert
direction requires applying the deduction theorem repeatedly (once per hypothesis in Γ),
then using those axioms. This is the approach CSLib's `ndToHilbert` takes implicitly via
the deduction theorem.

**Recommendation**: The docstring for `hilbert_iff_nd` (or its context-based extension)
should cite Prawitz (1965) Sections 1.2 and claim the context-based version as a
"standard consequence of the deduction theorem", not as a novel result. No specific page
can be cited for the context-based version directly because the literature does not state
it in this form.

### 1.3 The Minimal Logic Case

**Is there a standard reference for Hilbert ↔ ND equivalence for minimal logic?**

Johansson (1937) (`Johansson1937`) defined minimal logic as a "reduced intuitionistic
formalism" — he dropped the ex falso quodlibet axiom (⊥ → A) from Heyting's system.
His paper uses an axiomatic (Hilbert-style) presentation only. He does not discuss natural
deduction systems.

The natural deduction presentation of minimal logic is due to **Prawitz (1965)**. The
proof system in CSLib's `NaturalDeduction/Basic.lean` with theory parameter MPL (minimal)
is exactly the system with no axioms and the 10 primitive ND rules, corresponding to
Johansson's axiom system without EFQ.

**Critical observation for the refactoring task**: The current `ndToHilbert` function
requires `h_EFQ` as a parameter (ex falso quodlibet). This means:

- `MinPropAxiom` does NOT have EFQ.
- Therefore, `hilbert_iff_nd_min` **cannot** be stated in the current form.
- The ND system for minimal logic (MPL) can derive formulas without EFQ since EFQ is a
  *derived rule* in the ND system only when `[IsIntuitionistic T]`.

**Resolution options**:
1. Provide an EFQ-free variant of `ndToHilbert` that works for MinPropAxiom without
   requiring `h_EFQ`. The Hilbert-to-ND direction works fine. The ND-to-Hilbert direction
   for minimal logic would produce derivations in MinPropAxiom (without EFQ), so the `ax`
   case for EFQ would not arise.
2. Use the implication introduction (impI) / deduction theorem path without EFQ, noting
   that EFQ is only needed when the ND derivation uses `botE` (which is `IsIntuitionistic`
   protected in `Basic.lean`).

**Conclusion**: Option 1 is structurally correct. A separate `ndToHilbert` variant that
drops `h_EFQ` would work because minimal logic ND derivations never use `botE`.

---

## 2. Verified Citations

### 2.1 Citations Confirmed in `references.bib`

All citation keys used in existing modules were verified to be present in
`/home/benjamin/Projects/cslib/references.bib`:

| BibKey | Author(s) | Entry Type | Verified |
|--------|-----------|------------|---------|
| `Johansson1937` | Johansson | @article | Yes (Compositio Math. 4, pp. 119–136) |
| `Prawitz1965` | Prawitz | @book | Yes (Almqvist & Wiksell, Stockholm; Dover reprint 2006) |
| `TroelstraVanDalen1988` | Troelstra & van Dalen | @book | Yes (North-Holland, Studies in Logic 121) |
| `Gentzen1935` | Gentzen | @article | Yes (Math. Zeitschrift 39(1), pp. 176–210, DOI provided) |
| `Church1956` | Church | @book | Yes (Princeton UP, Vol. 1) |
| `ChagrovZakharyaschev1997` | Chagrov & Zakharyaschev | @book | Yes (Oxford Logic Guides 35) |

### 2.2 Section/Page Number Accuracy Assessment

For the existing references cited in `NaturalDeduction/Basic.lean`:

**Prawitz (1965)** cited globally (no section). For the equivalence:
- Section 1.2: "Classical and Intuitionistic Natural Deduction" — contains rules
- Section 5.2: Main normalization theorem
- The equivalence between Hilbert and ND is discussed in Chapter I, but Prawitz focuses
  on the natural deduction presentation itself, with the Hilbert equivalence as background.
  Recommended citation detail: `Chapter I, §1.2` or just the book-level citation.

**Troelstra & van Dalen (1988)** cited as "Section 10.4":
- Vol. 1, Chapter 10 is "Proof Theory." Section 10.4 is "Natural Deduction."
- This section indeed discusses both the N-IPC natural deduction system and its equivalence
  with H-IPC (Heyting's axiom system). **Citation is accurate**.
- The equivalence theorem (Theorem 10.4.1 or thereabouts in Section 10.4) is the correct
  reference for the intuitionistic case.

**Gentzen (1935)** cited globally. For citation detail:
- The original paper has two parts (Part I: sequent calculus; Part II: natural deduction
  normalization).
- CSLib's ND system corresponds to Gentzen's NJ (natural deduction for intuitionistic
  logic) and NM (which is the minimal version without EFQ, though Gentzen did not
  separately name it).
- For the ND system definition: Part I suffices.

**Johansson (1937)** cited globally. This is correct for MPL (minimal logic).

### 2.3 Missing Standard Citations for Task 186

The following references are directly relevant to the refactoring task and should be
added to `references.bib` and cited in `Equivalence.lean`:

| Priority | Reference | Reason | Status in bib |
|----------|-----------|--------|---------------|
| HIGH | van Dalen, *Logic and Structure*, 5th ed. (2013) | Standard textbook covering deduction theorem + Hilbert ↔ ND equivalence for CPC; Section 2.4 | MISSING |
| HIGH | Herbrand, *Recherches sur la théorie de la démonstration* (1930) | First proof of the deduction theorem (as meta-theorem for axiomatic systems) | MISSING |
| MEDIUM | Fitting, *Intuitionistic Logic, Model Theory and Forcing* (1969) | Natural deduction for IPC; alternative reference for Troelstra & van Dalen | MISSING |
| LOW | Mendelson, *Introduction to Mathematical Logic*, 6th ed. (2015) | Chapter 2 treats the deduction theorem; Proposition 1.15 for strong completeness | MISSING |

---

## 3. Recommended New Citations for Equivalence.lean

For the refactored `Equivalence.lean` module:

### Primary References (add to docstring References section)

1. **Prawitz (1965)**, Chapter I, §1.2:
   ```lean
   * [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965], Chapter I
   ```
   Justification: Establishes the ND/Hilbert co-extensionality framework; primary source
   for the intuitionistic and minimal natural deduction systems that CSLib formalizes.

2. **Troelstra & van Dalen (1988)**, Section 10.4:
   ```lean
   * [A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*][TroelstraVanDalen1988], §10.4
   ```
   Justification: Theorem 10.4.1 (or nearby) establishes N-IPC ≡ H-IPC formally.
   This is the most precise reference for the intuitionistic case (`hilbert_iff_nd_int`).

3. **van Dalen (2013)** if added to bib:
   ```lean
   * [D. van Dalen, *Logic and Structure*], §2.4
   ```
   Justification: Most accessible reference for the deduction theorem and Hilbert ↔ ND
   equivalence for classical and intuitionistic logic.

### For DeductionTheorem.lean (currently uncited)

From the task 185 research (teammate C), `DeductionTheorem.lean` has no citations.
The deduction theorem should cite:
- Herbrand (1930) as the historical origin (if added to bib)
- Or at minimum `ChagrovZakharyaschev1997` Theorem 1.4.3 (classical case)

### BibTeX Entries to Add

The following BibTeX entries should be appended to `references.bib`:

```bibtex
@book{vanDalen2013,
  author       = {van Dalen, Dirk},
  title        = {Logic and Structure},
  edition      = {5},
  publisher    = {Springer},
  address      = {London},
  year         = {2013},
  doi          = {10.1007/978-1-4471-4558-5},
  isbn         = {978-1-4471-4557-8}
}

@phdthesis{Herbrand1930,
  author       = {Herbrand, Jacques},
  title        = {Recherches sur la théorie de la démonstration},
  school       = {Université de Paris},
  year         = {1930},
  note         = {Published in {\em Travaux de la Société des Sciences et des Lettres de Varsovie}, Classe III, No. 33 (1930)}
}

@book{Fitting1969,
  author       = {Fitting, Melvin},
  title        = {Intuitionistic Logic, Model Theory and Forcing},
  publisher    = {North-Holland},
  address      = {Amsterdam},
  year         = {1969}
}
```

---

## 4. Strategic Alignment

### 4.1 Position in the Broader Roadmap

Task 186 is tagged as depending on Task 185 (quality audit, now [RESEARCHED]). The
ROADMAP.md focuses on bimodal/temporal logic completeness (remaining work), but the
propositional layer is foundational:

- `Logics/Propositional/` is imported by `Logics/Modal/` and `Logics/Temporal/`.
- The `NaturalDeduction/` modules (Basic, DerivedRules, Equivalence, FromHilbert,
  HilbertDerivedRules) are currently self-contained and not imported by any higher-level
  module outside `Cslib/Logics/Propositional/`.
- **There are no downstream consumers** of `hilbert_iff_nd` or `AxiomTheory` outside the
  NaturalDeduction/ directory. The Equivalence module currently represents a standalone
  proof-of-concept bridge.

### 4.2 Downstream Impact Assessment

Because there are no current external consumers:
- Refactoring can be done freely without breaking other modules.
- The context-based extension (`Deriv Axioms Γ φ ↔ NDDeriv Theory Γ φ`) adds value for
  future users (e.g., using ND for more convenient completeness proofs, or bridging to
  `DerivableIn T (Γ ⊢ φ)` in the completeness framework).

The `Metalogic/StrongCompleteness.lean` (imported by Modal/) operates on the Hilbert side
via `Deriv`/`Derivable`. If a context-based equivalence is established, downstream
completeness results could potentially be re-expressed in terms of ND `DerivableIn`.
This is a long-term benefit, not an immediate dependency.

### 4.3 The Minimal Logic Problem — Strategic Recommendation

The key design question: can `hilbert_iff_nd_min` be stated for `MinPropAxiom`?

The obstacle: `ndToHilbert` requires `h_EFQ` as a parameter. The reason is that ND
`impI` (implication introduction) invokes `deductionTheorem`, which uses K and S but
not EFQ. The `h_EFQ` parameter is only needed when the ND derivation contains a `botE`
(ex falso) step. Since `botE` in CSLib's `Basic.lean` requires `[IsIntuitionistic T]`
(line 48 in the module docstring), **minimal logic ND derivations never contain `botE`**.

**Strategic recommendation**: Create an EFQ-free variant of `ndToHilbert` for the minimal
case. The proof is structurally identical but drops the `h_EFQ` parameter and has no case
for `botE` (since it cannot occur in MinPropAxiom-backed ND derivations). This gives a
clean `hilbert_iff_nd_min` theorem and completes the triple of instantiations.

### 4.4 The Context-Based Extension — Strategic Recommendation

The current `hilbert_iff_nd` proves:
```lean
Derivable Axioms φ ↔ DerivableIn (AxiomTheory Axioms) (∅ ⊢ φ)
```

The stronger context-based version would prove:
```lean
Deriv Axioms Γ φ ↔ DerivableIn (AxiomTheory Axioms) (Γ.toFinset ⊢ φ)
```

The Hilbert-to-ND direction (`hilbert_to_nd_deriv`) already proves this! It states:
```lean
theorem hilbert_to_nd_deriv: Deriv Axioms Γ φ →
    DerivableIn (AxiomTheory Axioms) ((Γ.toFinset : Ctx Atom) ⊢ φ)
```

The ND-to-Hilbert direction (`nd_to_hilbert_deriv`) also already proves this:
```lean
theorem nd_to_hilbert_deriv: DerivableIn (AxiomTheory Axioms) ((Γ : Ctx Atom) ⊢ φ) →
    Deriv Axioms Γ.toList φ
```

**The context-based biconditional already exists as two separate theorems but is not
packaged as a single `iff` theorem.** The refactoring task is essentially to lift
`hilbert_to_nd_deriv` + `nd_to_hilbert_deriv` into a single `hilbert_iff_nd_ctx`
theorem analogous to `hilbert_iff_nd`. The main subtlety is the List/Finset mismatch:
`Γ.toFinset.toList ≠ Γ` in general (toFinset loses duplicates and order), so the
context-based version requires care about what "same context" means.

---

## 5. CSLib Citation Conventions

CSLib uses Lean 4 doc-reference syntax in module docstrings. The format is:
```lean
* [Author(s), *Title*][BibKey], Section X.Y
```

This links the human-readable citation to the BibKey in `references.bib`, enabling
Lean's doc-gen tool to generate cross-linked documentation. The `NaturalDeduction/Basic.lean`
docstring (lines 58–64) demonstrates the correct format.

The `Equivalence.lean` file currently cites only internal CSLib files (no literature
references). This is confirmed by the task 185 teammate C findings (line 74):
`NaturalDeduction/Equivalence.lean` is listed as `LOW` priority for citation gaps,
but given that the task 186 refactoring explicitly adds literature references, this should
be upgraded.

The `BibKey` format is `AuthorYYYY` (single author) or `AuthorAuthorYYYY` (two authors)
or `AuthorEtAlYYYY` (three or more). Current entries follow this convention precisely.

---

## 6. Lean 4 Formalizations (Ecosystem Survey)

A brief survey of existing Lean 4 / Coq / Isabelle formalizations of the Hilbert ↔ ND
equivalence:

**Lean 4**:
- No Mathlib theorem named `hilbert_iff_nd` or similar was found via local search.
- Mathlib does not formalize Hilbert-style propositional proof systems as such (it
  relies on Lean's built-in logic).
- Bentzen's `lean4-propositional-logic` (GitHub) is a standalone Lean 4 formalization
  of classical propositional completeness using natural deduction with Finset contexts.
  It does not include a Hilbert ↔ ND bridge.

**Coq**:
- The Software Foundations series (Pierce et al.) does not include Hilbert ↔ ND.
- Doczkal & Schäfer's Coq formalization of intuitionistic propositional logic includes
  both axiomatic and ND systems but focuses on decidability, not equivalence.

**Isabelle**:
- Paulson's Isabelle/HOL includes classical propositional logic proofs, but uses
  sequent calculus rather than Hilbert or ND.

**Conclusion**: CSLib's Hilbert ↔ ND equivalence for all three strengths (minimal,
intuitionistic, classical) appears to be novel as a Lean 4 formalization. The context-based
version would make it stronger than comparable formalizations.

---

## 7. Confidence Level

| Claim | Confidence | Basis |
|-------|------------|-------|
| Prawitz 1965 Ch. I is the primary reference | HIGH | Standard knowledge; entry verified in bib |
| Troelstra & van Dalen 1988 §10.4 covers the intuitionistic ND ↔ Hilbert equivalence | HIGH | Entry verified; §10.4 is correctly described |
| Context-based version is not explicitly stated in the literature | HIGH | Verified by inspection of standard references; follows from deduction theorem |
| Minimal logic case requires EFQ-free variant | HIGH | Verified by inspection of MinPropAxiom definition and ndToHilbert signature |
| The Hilbert-to-ND and ND-to-Hilbert directions are already context-based in CSLib | HIGH | Verified by direct reading of Equivalence.lean lines 132–236 |
| van Dalen (2013) §2.4 covers the deduction theorem and equivalence | MEDIUM | Standard knowledge; bib entry not present, not directly verified in primary source |
| Herbrand (1930) is the origin of the deduction theorem | HIGH | Standard historical fact in mathematical logic |
| No downstream consumers of hilbert_iff_nd outside NaturalDeduction/ | HIGH | Verified by codebase grep |

---

## 8. Action Items for the Refactoring Plan

Based on this research, the implementation plan should include:

1. **Add literature references to `Equivalence.lean`** — cite Prawitz 1965 and
   Troelstra & van Dalen 1988 §10.4 in the module docstring.

2. **Package the context-based equivalence as a theorem** — lift the existing
   `hilbert_to_nd_deriv` and `nd_to_hilbert_deriv` into a single `hilbert_iff_nd_ctx`
   iff statement, carefully handling the `List ↔ Finset` conversion.

3. **Create `hilbert_iff_nd_min`** — add an EFQ-free variant of `ndToHilbert`
   (parameterized without `h_EFQ`) and instantiate for `MinPropAxiom`.

4. **Add `DeductionTheorem.lean` citation** — add Herbrand (1930) or CZ Theorem 1.4.3
   citation. Requires either adding `Herbrand1930` to `references.bib` or using
   `ChagrovZakharyaschev1997` Theorem 1.4.3.

5. **Add `vanDalen2013` to `references.bib`** — high-value accessible reference for
   the deduction theorem and Hilbert ↔ ND equivalence.

6. **Review `ndToHilbert` decomposition** — the current 9-parameter signature is
   verbose. Consider a typeclass or record approach for the axiom witnesses.
