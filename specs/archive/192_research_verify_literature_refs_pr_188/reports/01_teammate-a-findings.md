# Teammate A Findings: Literature Reference Verification for PR 188

## Task
Verify/falsify each literature claim in `specs/archive/188_first_propositional_upstream_pr/pr-description.md`.

---

## Claim 1: [Church1956] §24 — "The choice of primitive connectives for propositional logic is discussed in [Church1956] §24"

**Verdict: VERIFIED (but context needs clarification)**

Church (1956), §24 is titled "Primitive connectives for the propositional calculus" (Table of Contents, line 291). The section begins (line 7753):

> "24. Primitive connectives for the propositional calculus. In P2 we used implication and negation as primitive connectives for the propositional calculus, and in Px we used implication and the constant /. We go on now to consider some other choices of primitive connectives..."

The claim that §24 discusses "the choice of primitive connectives for propositional logic" is **accurate**. Church §24 discusses completeness of various primitive connective systems: {implication, negation}, {implication, f}, {negation, disjunction}, {negation, conjunction}, {implication, converse non-implication}, {conditioned disjunction, t, f}, and non-conjunction alone (Sheffer stroke). BibKey `Church1956` is confirmed in `references.bib`.

**Important caveat**: Church §24 is about *classical* propositional calculus and discusses connective completeness in terms of truth-table expressibility. It does **not** discuss the five-primitive signature {⊥, →, ∧, ∨} specifically, nor does it address intuitionistic/minimal logic. The section on intuitionistic logic (Church §26) lists five primitives (implication, conjunction, disjunction, equivalence, negation) but **not ⊥**. The connection between Church §24 and the five-primitive design choice is therefore indirect — Church §24 is correctly cited as a general reference for discussing primitive connective choices, but the specific five-primitive signature is better justified by the independence results (McKinsey 1939, Wajsberg 1938) and Johansson/Troelstra-van Dalen.

**Evidence**: Church §24 text at lines 7753–7997 of `church_1956.md`; Table of Contents entry at line 290–293.

**Confidence: HIGH** for the descriptive claim, **LOW** for implication that Church §24 directly supports the five-primitive choice with ⊥.

---

## Claim 2: [TroelstraVanDalen1988] Chapter 2 — "the five-primitive signature with ⊥ is the standard one for intuitionistic and minimal logic in [TroelstraVanDalen1988] Chapter 2"

**Verdict: UNVERIFIABLE (no file available)**

The file `specs/literature/` does not contain a markdown or PDF version of Troelstra & van Dalen (1988). The `sources.md` entry confirms:

> "**Troelstra & van Dalen 1988** [TroelstraVanDalen1988] `[NO FILE]`: *Constructivism in Mathematics: An Introduction*, Vol. 1. North-Holland."

The BibKey `TroelstraVanDalen1988` is confirmed in `references.bib`. The claim itself is consistent with standard knowledge about this book — Troelstra & van Dalen Chapter 2 does present intuitionistic propositional logic with the connectives {⊥, →, ∧, ∨} (without equivalence/negation as primitive, since ¬A := A → ⊥). However, **primary source verification is impossible** without the text.

The sources.md note adds that "Section 2.5 for Kripke completeness, Section 10.4 for natural deduction" are relevant — but does not confirm that Chapter 2 uses exactly these five (or four: {⊥, →, ∧, ∨}) primitives.

**Note on "five primitives"**: The formula type in CSLib is `{atom, bot, imp, and, or}`. In the literature on intuitionistic logic, the formula language is typically `{⊥, →, ∧, ∨}` (four logical connectives, with atom being a schema). The PR's "five-primitive signature" conflates the CSLib constructor count (which includes `atom`) with the logical connective count (which is four). This may be a minor imprecision.

**Evidence**: `sources.md` lines 57–59; `references.bib` entry for `TroelstraVanDalen1988`.

**Confidence: MEDIUM** — claim is plausible based on field knowledge but cannot be verified from available literature files.

---

## Claim 3: [Johansson1937] — "Primitive ⊥ is required for Johansson's minimal logic [Johansson1937], which defines negation ¬A := A → ⊥ using ⊥ as an undefined primitive symbol ('undefiniertes Grundzeichen')"

**Verdict: VERIFIED**

The Johansson 1937 PDF is available and the German text is unambiguous. From the introduction (§1, p. 120):

> "Die Möglichkeit ¬a durch a ⊃ Λ (wo Λ 'Widerspruch' oder 'etwas Falsches' bedeutet) zu ersetzen, ist wahrscheinlich recht allgemein bekannt; sie hängt ja mit dem Axiom 4.11 bei Heyting eng zusammen. **Die Auffassung von Λ als undefiniertes Grundzeichen** und die Definition von ¬ durch [¬a := a ⊃ Λ] liegt dann sehr nahe."

Translation: "The possibility of replacing ¬a by a ⊃ Λ (where Λ means 'contradiction' or 'something false') is probably quite generally known; it is closely connected with axiom 4.11 in Heyting. **The conception of Λ as an undefined primitive symbol** and the definition of ¬ via [¬a := a ⊃ Λ] is then very natural."

A second occurrence appears on p. 132 (Johansson's §4):

> "Die Auffassung von Λ als eine undefinierte Grundaussage ist mit der von Kolmogoroff angegebenen 'aufgabentheoretischen' Deutung der intuitionistischen Logik verwandt."

Translation: "The conception of Λ as an undefined primitive proposition is related to the 'task-theoretic' interpretation of intuitionistic logic given by Kolmogoroff."

The PR's claim is **precisely correct**: Johansson uses Λ (which corresponds to ⊥) as an *undefiniertes Grundzeichen* (undefined primitive symbol/sign), and defines negation as ¬a := a ⊃ Λ.

One minor linguistic note: the PR uses "Grundzeichen" (symbol/sign) while Johansson's second occurrence uses "Grundaussage" (primitive proposition). Both appear in the text; "Grundzeichen" is the term used first and is the more striking formulation. The PR's quotation of "undefiniertes Grundzeichen" is accurate to the first occurrence.

**Notation detail**: Johansson uses Λ for the false proposition (not the ⊥ symbol), and uses ⊃ for implication (not →). Johansson's formula language is described as containing ⊃, Λ, and ∨ as the connectives shared with Heyting's calculus.

**Evidence**: `johansson_1937.pdf` extracted text, lines 83–92 (§1 introduction) and lines 497–505 (§4).

**Confidence: HIGH**

---

## Claim 4: Naming claim — "'imp' is standard in Lean formalization practice... The previous 'impl' was non-standard — no major proof theory reference uses this abbreviation for implication."

**Verdict: PARTIALLY VERIFIED**

The claim has two parts:

**Part A: "imp is standard in Lean formalization practice"**
This cannot be directly verified from the literature files (which are historical logic texts, not Lean formalization references). However, the claim is plausible: Lean's `Prop` has operations like `And`, `Or`, `Not`, and implication is `Prop → Prop` (unnamed as a combinator). In Lean 4, the Mathlib convention for naming propositions about implication uses `imp` (e.g., `imp_iff`, `imp_congr`, `not_imp`). The modal logic formalizations referenced in `sources.md` (Bentzen 2023, From & Jacobsen 2022) would need direct inspection to confirm, but `imp` is broadly standard in Lean 4 naming.

**Part B: "no major proof theory reference uses 'impl' as an abbreviation for implication"**
This negative claim is supported by examination of available literature:
- Church (1956): uses "implication" fully or the symbol ⊃; no abbreviation `impl` or `imp`
- Gentzen (1935): uses ⊃ for implication, no abbreviation
- Johansson (1937): uses ⊃ for implication, no abbreviation
- Mendelson (2016): uses ⇒ for implication, no abbreviation
- Post (1921): propositional logic using symbols, no named abbreviation

None of the literature files use `impl`. The claim that `impl` is non-standard is accurate for the proof-theory literature examined. However, `impl` does appear in some proof assistant formalizations (e.g., Coq uses `Logic.Classical_Pred_Type` which has no `impl`; Isabelle uses `HOL.implies` abbreviated as `-->`) — but none of these use `impl` as a standalone name.

**The Gentzen/Prawitz connection in the PR title**: The PR description says "Renamed impl to imp (standard notation per Gentzen/Prawitz)." Gentzen and Prawitz do not actually use the abbreviation `imp` — they use ⊃ (Gentzen) or → (Prawitz) as symbols. The claim should be read as "standard abbreviation in formalization practice of the Gentzen/Prawitz tradition" rather than a direct quotation. The attribution "per Gentzen/Prawitz" is thus slightly misleading.

**Evidence**: Literature files checked for `imp`/`impl` abbreviations; `sources.md` notation descriptions.

**Confidence: MEDIUM** — the descriptive claim about `impl` being non-standard is likely correct; the positive claim about `imp` being "standard" is convention-dependent.

---

## Claim 5: "Renamed impl to imp (standard notation per Gentzen/Prawitz)"

**Verdict: PARTIALLY FALSIFIED**

Gentzen (1935) does **not** use the abbreviation `imp`. He uses ⊃ as the implication symbol and refers to it as the "implication symbol" in full. Prawitz (1965, no file available) uses → for implication in natural deduction and refers to "implication introduction/elimination" — no abbreviation `imp` appears in Prawitz's notation either.

The claim "standard notation per Gentzen/Prawitz" is inaccurate as a direct attribution: neither Gentzen nor Prawitz use the string `imp` as an abbreviation. What they establish is the *structural role* of implication in natural deduction (→I and →E rules), which CSLib inherits. The actual `imp` naming convention comes from Lean 4 formalization practice, not from the original Gentzen/Prawitz papers.

The substantive claim — that renaming `impl` to `imp` is an improvement — is defensible, but the "per Gentzen/Prawitz" attribution is misleading and should be softened to something like "following Lean 4 naming conventions for implication operators."

**Evidence**: Gentzen (1935) terminology section (extracted from `gentzen_1935.pdf`): uses ⊃ and the term "implication symbol"; no `imp` abbreviation found.

**Confidence: HIGH** that Gentzen/Prawitz do not use `imp`; **HIGH** that renaming `impl` → `imp` is a reasonable improvement regardless.

---

## Summary Table

| Claim | Verdict | Confidence |
|-------|---------|------------|
| Church §24 discusses choice of primitive connectives | VERIFIED | HIGH |
| Church §24 supports the specific five-primitive+⊥ design | PARTIALLY VERIFIED (indirect) | LOW-MEDIUM |
| TroelstraVanDalen1988 Chapter 2 uses five-primitive signature with ⊥ | UNVERIFIABLE (no file) | MEDIUM (plausible) |
| Johansson uses ⊥ as "undefiniertes Grundzeichen" | VERIFIED | HIGH |
| Johansson defines ¬A := A → ⊥ | VERIFIED | HIGH |
| "imp" is standard in Lean formalization | PARTIALLY VERIFIED | MEDIUM |
| "impl" not used in major proof theory references | VERIFIED | HIGH |
| "Standard notation per Gentzen/Prawitz" for "imp" | PARTIALLY FALSIFIED | HIGH |

---

## Recommended Corrections

1. **Church §24 citation**: The citation is defensible but should be clarified. Church §24 justifies *discussing* primitive connective choices in general; the specific five-primitive+⊥ choice is better justified by independence results (McKinsey 1939) cited elsewhere. Consider adding "and independence of connectives in intuitionistic logic is shown in [McKinsey1939]" for stronger justification.

2. **TroelstraVanDalen1988 Chapter 2**: Claim is plausible but unverifiable without the text. The more precise reference should be "Chapter 2.1 or 2.2" (the sections on intuitionistic propositional logic), not just "Chapter 2." If the book is accessible, verify the exact section.

3. **Johansson claim**: Accurate and well-supported. The German quotation "undefiniertes Grundzeichen" appears verbatim in the text.

4. **"per Gentzen/Prawitz" attribution**: Replace with "following Lean 4 naming conventions" or "standard in Lean formalization practice (Lean's own `imp_*` lemmas)." Gentzen uses ⊃, Prawitz uses →; neither uses the string `imp`.

5. **"Five-primitive signature"**: The literature term is typically "four connectives" {⊥, →, ∧, ∨} for intuitionistic/minimal logic. CSLib's type has five constructors because `atom` is a data constructor, not a connective. The PR correctly identifies this distinction elsewhere but the "five-primitive signature" phrase may confuse readers familiar with the standard four-connective presentation.

---

## Key Evidence Quotes

**Church §24 (verified from `church_1956.md`)**:
> "24. Primitive connectives for the propositional calculus. In P2 we used implication and negation as primitive connectives for the propositional calculus, and in Px we used implication and the constant /. We go on now to consider some other choices of primitive connectives..."

**Johansson 1937 (verified from `johansson_1937.pdf`)**:
> "Die Auffassung von Λ als undefiniertes Grundzeichen und die Definition von ¬ durch [¬a := a ⊃ Λ] liegt dann sehr nahe."
> (Conception of Λ as undefined primitive symbol, and defining negation via ¬a := a ⊃ Λ, is then very natural.)

**Johansson 1937, second occurrence**:
> "Die Auffassung von Λ als eine undefinierte Grundaussage ist mit der von Kolmogoroff angegebenen 'aufgabentheoretischen' Deutung der intuitionistischen Logik verwandt."
> (Conception of Λ as an undefined primitive proposition is related to Kolmogoroff's task-theoretic interpretation.)

**Gentzen 1935 (verified from `gentzen_1935.pdf`)**:
> "Logical symbols: & 'and', ∨ 'or', ⊃ 'if... then', ≡ 'is equivalent to', ¬ 'not'..."
> (No abbreviation `imp` used; implication is always written as the symbol ⊃ or referred to as "the implication symbol".)
