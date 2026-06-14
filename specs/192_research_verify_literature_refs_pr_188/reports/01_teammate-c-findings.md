# Teammate C Findings: Critical Evaluation of Literature Claims in PR #188 Description

**Role**: Critic — identify gaps, inaccuracies, attribution problems, and overclaiming
**Task**: 192 — Research to verify literature references in PR 188 description
**Date**: 2026-06-14
**Input**: `specs/archive/188_first_propositional_upstream_pr/pr-description.md`,
  `specs/literature/sources.md`, `specs/literature/church_1956.md`, `specs/literature/Gentzen1935.md`

---

## Executive Summary

The PR description makes five distinct literature claims. **Three are problematic in ways
that a diligent reviewer (like ctchou) could catch**. The most serious is the
Church [Church1956] §24 citation: Church §24 is about functional completeness and
independent connective systems for *classical* propositional logic, not about the
five-primitive signature for intuitionistic/minimal logic. The Gentzen/Prawitz attribution
for the name "imp" is anachronistic and misleading. The TroelstraVanDalen1988 Chapter 2
citation likely oversimplifies. The Johansson citation is the strongest claim and appears
accurate. One cited source (McKinsey 1939) is entirely absent from the PR description
despite being the key justification for why {bot, imp} alone is insufficient.

**Confidence**: HIGH for claims checkable against `church_1956.md` (PDF available).
MEDIUM for Troelstra & van Dalen (no PDF available). HIGH for Johansson (independently
corroborated by sources.md). HIGH for the Gentzen/Prawitz naming issue (Gentzen1935.md
is metadata-only; but the historical facts are unambiguous).

---

## Claim-by-Claim Analysis

### Claim 1: [Church1956] §24 Discusses "Choice of Primitive Connectives"

**PR text** (lines 48-50):
> "The choice of primitive connectives for propositional logic is discussed in
> [Church1956] §24"

**What Church §24 actually covers** (verified against `specs/literature/church_1956.md`):

Church §24 is titled "Primitive connectives for the propositional calculus" (page 129).
Its content is:
- Functional completeness of *classical* propositional calculus truth-functions
- {conditioned disjunction, t, f} as a complete independent system
- Proof that {implication, f} is complete; proof that {implication, negation} is complete
- Proof that {negation, disjunction} and {negation, conjunction} are complete
- Sheffer's stroke (NAND) and its completeness
- Complete systems of *independent* primitive connectives (Post 1941)

**The fatal mismatch**: Church §24 is entirely about classical, truth-functional
completeness — which classical two-element truth-tables are expressible from a given set
of connectives. It does not discuss:
- The five-primitive signature {bot, imp, and, or} for *intuitionistic* logic
- The non-definability of and/or from imp/bot in intuitionistic logic
- The specific connective selection rationale for constructive or minimal logic

Church's own system P₁ uses {implication, f} and P₂ uses {implication, negation} — neither
uses {bot, imp, and, or} as primitives. Church §24 actually shows that {implication, f} is
classically complete, which *undermines* the motivation for a five-primitive system in the
classical case.

**Severity**: HIGH. A reviewer who checks §24 (as ctchou checked Gentzen in PR #635) will
find the citation does not support the claim. The citation technically is not false —
Church §24 does discuss choosing primitive connectives — but the PR implies this supports
the five-primitive choice, when Church §24 actually concerns classical two-connective
complete bases. The connection to intuitionistic logic is not made in the Church text.

**Recommended correction**: Either (a) remove the Church citation and rely solely on
[TroelstraVanDalen1988] and [Johansson1937] for this claim, or (b) qualify it accurately:
"Church [Church1956] §24 treats functional completeness for *classical* connective systems;
for the intuitionistic case where {bot, imp} is insufficient, see [McKinsey1939]."

---

### Claim 2: [TroelstraVanDalen1988] Chapter 2 "Establishes the Five-Primitive Signature as Standard"

**PR text** (lines 50-52):
> "the five-primitive signature with ⊥ is the standard one for intuitionistic and minimal
> logic in [TroelstraVanDalen1988] Chapter 2"

**Problem — precision**: The sources.md entry for [TroelstraVanDalen1988] notes:
- "Section 2.5 for Kripke completeness"
- "Section 10.4 for natural deduction"

The PR cites "Chapter 2" as the source for the five-primitive signature, but sources.md
(which has clearly been checked against the book) points to Section 10.4 for natural
deduction, not Chapter 2. If the five-primitive ND formulation is in Section 10.4, the
citation should be "Section 10.4" not "Chapter 2." Chapter 2 may be about completeness,
not about the formula language.

**Problem — "the standard one"**: Troelstra & van Dalen (1988) is a constructivism
textbook, not a logic textbook. It covers one formulation, not all possible formulations.
Calling it "the standard one" based on a single source is overclaiming. Other standard
references (e.g., Prawitz 1965, Heyting 1930) could also be cited, and some formulations
of intuitionistic logic use different connective sets (e.g., pure implicational fragments).

**Problem — roadmap claim**: The PR also says (lines 85-87):
> "The planned roadmap mirrors the structure of Troelstra & van Dalen [TroelstraVanDalen1988]
> Chapter 2, with PR 5-6 following the completeness proof strategy there."

"Mirrors" is an overstatement unless the PR author has verified the chapter ordering in
Troelstra & van Dalen against the PR sequence. From sources.md, "Section 2.5 for Kripke
completeness" — so Chapter 2 does cover Kripke completeness, making "Chapter 2" partially
correct for the completeness claim. But the roadmap has 6 stages; Chapter 2 of a
constructivism book likely does not have this structure.

**Severity**: MEDIUM. The citation to Troelstra & van Dalen is appropriate and the book
does treat the five-primitive signature for IPL. The issue is precision (Chapter 2 vs.
Section 10.4 for ND) and overclaiming with "the standard one" and "mirrors."

**Recommended correction**: Cite Section 10.4 for the ND formula language, Section 2.5
for Kripke completeness. Remove "the standard one" — say instead "is used in" or
"follows." The roadmap claim should say "draws from" or "is inspired by" rather than
"mirrors."

---

### Claim 3: [Johansson1937] "Requires Primitive ⊥ and Uses 'Undefiniertes Grundzeichen'"

**PR text** (lines 51-54):
> "Primitive ⊥ is required for Johansson's minimal logic [Johansson1937], which defines
> negation ¬A := A → ⊥ using ⊥ as an undefined primitive symbol ('undefiniertes
> Grundzeichen')."

**Verdict**: This claim is accurate and well-supported. The sources.md entry for
[Johansson1937] confirms: "Critically, Johansson's formula language retains ⊥ (falsum)
as a primitive" and "Negation is defined as ¬A := A → ⊥, which requires ⊥ in the
language." The supplementary report `02_bot-primitive-justification.md` also verifies
this against the paper.

The German phrase "undefiniertes Grundzeichen" is plausible for Johansson's 1937
German-language paper (the paper is in German: "Der Minimalkalkül, ein reduzierter
intuitionistischer Formalismus"). However, **the exact phrase cannot be verified here
since only the PDF is available** (`johansson_1937.pdf`) and there is no markdown
conversion. If ctchou or another reviewer checks the paper, the phrase should be present.

**Residual risk (LOW)**: The exact phrase "undefiniertes Grundzeichen" should be quoted
accurately. If the paper uses a slightly different phrase (e.g., "primitive sign" or
"primitive Zeichen"), the citation would be misleading. This should be verified against
the PDF before PR submission.

**Severity**: LOW — the claim is accurate in substance; verification of exact phrasing
is a minor residual risk.

---

### Claim 4: "imp" is Standard "per Gentzen/Prawitz"

**PR text** (line 20):
> "Renamed impl to imp (standard notation per Gentzen/Prawitz)"

**PR text** (lines 57-59):
> "The name imp is standard in Lean formalization practice (e.g., Lean's own Prop
> operations and modal logic formalizations). The previous impl was non-standard — no
> major proof theory reference uses this abbreviation for implication."

**Fatal problem — attribution**: Gentzen (1935) wrote in German. His paper "Untersuchungen
über das logische Schließen" uses:
- Mathematical symbols: → for implication (or ⊃)
- German words: "Implikation" when named in prose
- No English abbreviations whatsoever

Prawitz (1965) *Natural Deduction: A Proof-Theoretical Study* writes in English but uses
mathematical notation (→) and the word "implication," not the abbreviation "imp."

Neither Gentzen nor Prawitz used "imp" as an ASCII abbreviation. They could not have,
since ASCII did not exist when Gentzen wrote (1935) and was not common in mathematical
publishing when Prawitz wrote (1965). Attributing the name "imp" to Gentzen/Prawitz is
**anachronistic and historically inaccurate**.

**What "per Gentzen/Prawitz" is actually trying to say**: The claim likely means that
Gentzen's and Prawitz's natural deduction systems used {⊥, →, ∧, ∨} as primitives
(which is true), and that the PR follows this tradition by choosing "imp" as the
constructor name. But the tradition these authors established was about *which connectives
are primitive*, not about what to call a Lean constructor 60–90 years later.

**The Lean claim is the stronger argument**: The PR also says "standard in Lean
formalization practice (e.g., Lean's own Prop operations and modal logic formalizations)."
This is the defensible part of the claim — "imp" appears in Lean core (e.g., `Prop.imp`)
and in various Lean logic formalizations. This should be the primary justification, not
the Gentzen/Prawitz attribution.

**Severity**: HIGH. The "per Gentzen/Prawitz" attribution is misleading. If a reviewer
reads this as "Gentzen and Prawitz used the name 'imp'", that is false. A reviewer who
checks Gentzen (as ctchou did in PR #635) will not find "imp" there.

**Recommended correction**: Change "standard notation per Gentzen/Prawitz" to "following
the tradition of Gentzen's NJ and Prawitz's ND system, where implication is a primitive"
(which is true) and separately justify "imp" as the specific name via Lean community
conventions, not historical attribution.

---

### Claim 5: "'impl' is non-standard — no major proof theory reference uses this abbreviation"

**PR text** (lines 58-59):
> "The previous impl was non-standard — no major proof theory reference uses this
> abbreviation for implication."

**Problem — verifiability**: This is a negative universal claim ("no major reference uses
impl"). Universal negatives are always risky. The claim appears plausible but cannot be
conclusively verified. Some proof assistants and formalizations (e.g., Agda libraries,
older Isabelle developments) may use "impl" as an abbreviation.

**Problem — internal consistency**: The upstream CSLib itself uses `impl` as the
implication constructor name in `Defs.lean`. When the PR says "no major proof theory
reference uses this abbreviation," the reviewer may point out that the *current upstream
CSLib* uses it. The PR might be seen as implicitly criticizing existing CSLib naming
conventions, which is unusual for a PR that is trying to get upstream acceptance.

**Severity**: MEDIUM. This is an overstatement that may invite a reviewer to defend
upstream's existing `impl` naming. The PR should instead say something like "we prefer
`imp` for conciseness and alignment with Lean's `Prop.imp`" without making the
historical universality claim.

---

## Missing Citations from sources.md

The following sources in `sources.md` are directly relevant to the PR's technical claims
but are **not cited anywhere in the PR description**:

| Source | BibKey | Relevance | Omission Severity |
|--------|--------|-----------|-------------------|
| McKinsey 1939 | [McKinsey1939] | Proves and/or cannot be defined from imp/negation in Heyting's calculus — the primary justification for why five primitives are needed for IPL | **CRITICAL** |
| Wajsberg 1938 | [Wajsberg1938] | Further independence results; cited in sources.md as supporting non-reducibility | HIGH |
| Heyting 1930 | [Heyting1930] | Original IPL formalization; conjunction and disjunction are primitive (not definable) — directly relevant to why five primitives are needed | MEDIUM |

**The McKinsey omission is the most serious**: The entire rationale for five primitives
rather than two rests on the non-definability of ∧ and ∨ from → and ⊥ in intuitionistic
logic. McKinsey (1939) proved this. The PR mentions this motivating fact implicitly (the
"substitution breaks ⊥" argument) but cites Church §24 (which does NOT prove this for
IPL) rather than McKinsey (who does). If a reviewer asks "where is the proof that you
need five primitives?", the PR cannot answer correctly without [McKinsey1939].

The PR description cites [McKinsey1939] nowhere. It is listed in `sources.md` with the
note: "Critical for justifying the five-primitive formula type." Its absence is not an
accident — it is a gap that should be filled.

---

## Summary of Issues by Severity

| Claim | Severity | Issue Type |
|-------|----------|-----------|
| Church §24 citation | HIGH | Wrong content — §24 is about classical functional completeness, not IPL five-primitive rationale |
| "imp" per Gentzen/Prawitz | HIGH | Anachronistic — neither author used English abbreviations; attribution is misleading |
| McKinsey1939 missing | CRITICAL | Missing citation — the primary proof for why five primitives are needed |
| "impl is non-standard" | MEDIUM | Overclaiming universal negative; antagonizes upstream naming |
| TroelstraVanDalen1988 Chapter 2 | MEDIUM | Section imprecision (may be 10.4, not Chapter 2); "the standard one" overclaims |
| Johansson "undefiniertes Grundzeichen" | LOW | Accurate in substance; exact phrase unverified from PDF |
| "mirrors T&vD Chapter 2" roadmap | LOW | Overstatement ("mirrors" too strong) |

---

## Recommended Corrections

### For the PR description "Why bot Should Be Primitive" section:

**Replace**:
> "The choice of primitive connectives for propositional logic is discussed in [Church1956]
> §24; the five-primitive signature with ⊥ is the standard one for intuitionistic and
> minimal logic in [TroelstraVanDalen1988] Chapter 2."

**With**:
> "For intuitionistic and minimal logic, conjunction and disjunction cannot be defined from
> implication and negation ([McKinsey1939], [Wajsberg1938]), which necessitates five
> primitives {⊥, →, ∧, ∨}. This signature is used in [TroelstraVanDalen1988] (Section 10.4)
> and [Prawitz1965] (Chapter I)."

### For the "imp vs impl" section:

**Replace**:
> "Renamed impl to imp (standard notation per Gentzen/Prawitz)"

**With**:
> "Renamed impl to imp (following Lean naming conventions; Gentzen's NJ and Prawitz's ND
> systems use implication as a primitive connective)"

**Replace** the claim "no major proof theory reference uses this abbreviation" with a
positive claim about why "imp" is preferred.

### Add McKinsey citation:

Somewhere in the "Why bot Should Be Primitive" section or an additional section:

> "Conjunction (∧) and disjunction (∨) are independent from implication (→) and
> negation (¬) in Heyting's intuitionistic calculus [McKinsey1939], unlike in classical
> logic where both can be defined from {→, ¬}. This justifies the five-primitive
> formula type for formalizations intended to cover all three logic strengths
> (classical, intuitionistic, minimal)."

---

## Confidence Assessment

| Finding | Confidence | Evidence |
|---------|------------|----------|
| Church §24 is about classical functional completeness, not IPL five-primitive rationale | HIGH | Direct read of church_1956.md, §24 content verified |
| Gentzen/Prawitz did not use "imp" as an ASCII abbreviation | HIGH | Historical fact; Gentzen1935.md confirms paper is in German |
| McKinsey1939 is missing from PR but in sources.md as "critical" | HIGH | Direct read of sources.md and pr-description.md |
| Johansson claim is accurate in substance | HIGH | Corroborated by sources.md and 02_bot-primitive-justification.md |
| TroelstraVanDalen Chapter 2 vs Section 10.4 | MEDIUM | sources.md points to Section 10.4 for ND; book not available for direct check |
| "impl is non-standard" overclaims | MEDIUM | Upstream CSLib uses impl; universal negatives are risky |
