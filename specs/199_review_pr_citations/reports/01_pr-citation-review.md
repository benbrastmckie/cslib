# Research Report: PR Citation Review for Propositional Logic PR

**Task**: 199 -- Review citations in PR changes for accuracy and completeness
**Date**: 2026-06-14
**Session**: sess_1781472454_5c6dc9

---

## 1. Citation-by-Citation Verification

### 1.1 [Bentzen2023] -- Guo, Chen, Bentzen (arXiv:2310.01916)

**PR claim (PR 198, line 55-56)**: "[Bentzen2023] uses exactly `{atom, bot, impl, and, or}` in his Lean formalization of IPL completeness."

**Verification**: ACCURATE. Bentzen 2023 defines (lines 110-127 of `bentzen_2023.md`):
```lean
inductive form : Type
| atom : N -> form
| bot  : form
| impl : form -> form -> form
| and  : form -> form -> form
| or   : form -> form -> form
```

The five constructors are exactly `atom`, `bot`, `impl`, `and`, `or`. The PR correctly notes the constructor name is `impl` (not `imp`), which supports the five-primitive design but does not support the naming change.

**Minor note**: The PR says "his" but the paper has three authors (Guo, Chen, Bentzen). The arXiv link is correct.

### 1.2 [Trufas2024] -- Trufas (EPTCS 410.9)

**PR claim (PR 198, lines 57-58)**: "[Trufas2024] uses `{var, bottom, and, or, implication}` with negation and top derived as `phi => bot` and `~bot`."

**Verification**: ACCURATE. Trufas 2024 defines (lines 92-103 of `trufas_2024.md`):
```lean
inductive Formula where
| var : Var -> Formula
| bottom : Formula
| and : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| implication : Formula -> Formula -> Formula
```

And derives (lines 112-116):
```lean
def negation (phi : Formula) : Formula := phi => bot
def top : Formula := ~bot
```

All claims match the source exactly. The DOI link (10.4204/EPTCS.410.9) is correct.

### 1.3 [Johansson1937] -- Johansson, "Der Minimalkalkul"

**PR claim (PR 198, lines 59-60)**: "Johansson [Johansson1937] treats bot as an undefined primitive symbol ('undefiniertes Grundzeichen') and defines negation `neg a := a => bot`."

**Verification**: SUBSTANTIALLY ACCURATE with conventional notation modernization.

- **"undefiniertes Grundzeichen"**: Confirmed at lines 71-72 of `johansson_1937.md`, section 1: "Die Auffassung von A als undefiniertes Grundzeichen und die Definition von [negation] durch liegt dann sehr nahe."
- **"undefinierte Grundaussage"**: Also appears at line 362, section 4: "Die Auffassung von A als eine undefinierte Grundaussage..."
- **Negation definition**: Johansson defines neg(a) := a => A (formula 22, referenced at line 320).

**Notation caveat**: Johansson uses **A** (not bot) for falsum and **=>** (horseshoe, not arrow) for implication. The PR's use of bot and arrow notation is standard modern practice, not fabrication. The German phrase "undefiniertes Grundzeichen" is accurately quoted.

**PR 188 claim (lines 51-53)**: Same content. Also accurate.

### 1.4 [TroelstraVanDalen1988] -- Troelstra & van Dalen, "Constructivism in Mathematics"

**PR claim (PR 188, lines 50-51)**: "The five-primitive signature `{atom, bot, imp, and, or}` is the standard one for intuitionistic and minimal logic in [TroelstraVanDalen1988] Chapter 2."

**Verification**: PLAUSIBLE BUT UNVERIFIABLE. The book is not in `specs/literature/`. However:
- Bentzen 2023 explicitly formalizes "the classical proof of completeness in Henkin-style developed by Troelstra and van Dalen" and uses {atom, bot, impl, and, or}.
- Trufas 2024 cites Troelstra as an inspiration and also uses five primitives with bot.
- The claim is consistent with standard constructive mathematics practice where bot is primitive for minimal/intuitionistic logic.

**Lean source claim (Basic.lean line 61)**: "Section 10.4" is cited. Also unverifiable without the book. Plausible -- Section 10.4 in a constructive mathematics textbook would likely cover natural deduction.

**Lean source claim (Defs.lean line 21)**: The phrase "standard Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition" is an **invented label** with no literature precedent. Task 192 flagged this as medium severity. See Section 3 for details.

**PR 198 claim (lines 108-111)**: "The planned roadmap draws from the development in Troelstra & van Dalen [TroelstraVanDalen1988] Chapter 2." This is a well-hedged claim about the development approach, not a factual claim about specific content.

### 1.5 Citations in Source Files Not Referenced in PR Descriptions

The following are cited in Lean source file docstrings but not in PR descriptions:

| BibKey | Where Cited | Accuracy |
|--------|-------------|----------|
| [Wajsberg1938] | Connectives.lean lines 31, 44 | ACCURATE -- Wajsberg studied independence of Heyting's primitives |
| [McKinsey1939] | Connectives.lean lines 31, 46 | ACCURATE -- McKinsey proved independence of Heyting's primitive symbols |
| [Prawitz1965] | Connectives.lean line 47, Defs.lean line 63, Basic.lean line 59 | ACCURATE -- Prawitz's natural deduction monograph is the standard reference |
| [Heyting1930] | Connectives.lean line 51 | ACCURATE -- Heyting's original axiomatization of intuitionistic logic |
| [Gentzen1935] | Connectives.lean line 52, Defs.lean line 62, Basic.lean lines 62-63 | ACCURATE -- Gentzen's natural deduction/sequent calculus paper |
| [Church1956] | Connectives.lean line 50, Defs.lean line 67 | SEE BELOW |
| [ChagrovZakharyaschev1997] | Connectives.lean line 53, Defs.lean line 67, Connectives.lean lines 72-73, 112-113 | ACCURATE -- modal logic reference, correctly cited for box modality |
| [Blackburn2001] | Connectives.lean lines 72, 112 | ACCURATE -- modal logic reference for box as canonical primitive |

**Church1956 in source files**: Church is cited in the reference blocks of Connectives.lean (line 50) and Defs.lean (line 67) without inline context. Task 192 found that Church's discussion of intuitionistic logic (in section 26, not section 24) uses {imp, conj, disj, equiv, neg} as primitives -- with negation primitive, not bot. Church's treatment is classical in focus and does not support the five-primitive-with-bot signature. The citation is **tangential** -- it is a general reference for propositional logic but does not directly support the specific design decision of making bot primitive. This is low severity since it appears in a general reference list rather than as an inline citation supporting a specific claim.

---

## 2. references.bib Audit

### 2.1 BibKeys Present (All Lean-Source Citations)

All 10 BibKeys cited in the three Lean source files exist in `references.bib` with complete entries:

| BibKey | Type | Status |
|--------|------|--------|
| Blackburn2001 | book | Complete |
| ChagrovZakharyaschev1997 | book | Complete |
| Church1956 | book | Complete |
| Gentzen1935 | article | Complete |
| Heyting1930 | article | Complete |
| Johansson1937 | article | Complete |
| McKinsey1939 | article | Complete |
| Prawitz1965 | book | Complete |
| TroelstraVanDalen1988 | book | Complete |
| Wajsberg1938 | article | Complete |

### 2.2 BibKeys Missing (PR Description Citations)

The PR descriptions (primarily PR 198) cite two references that lack entries in `references.bib`:

| BibKey | Source | Status | Action Needed |
|--------|--------|--------|---------------|
| Bentzen2023 | Guo, Chen, Bentzen (arXiv:2310.01916, LNGAI/LAL 2023) | **MISSING** | Add entry |
| Trufas2024 | Trufas (EPTCS 410.9, FROM 2024) | **MISSING** | Add entry |

Task 192 round 2 drafted BibTeX entries for both. These should be added.

### 2.3 Additional Missing Entries (From Task 192)

Task 192 identified 5 additional entries needed for future roadmap citations:

| BibKey | Status | Priority |
|--------|--------|----------|
| Post1921 | Missing | Low (tangential to IPL) |
| Henkin1949 | Missing | Medium (relevant to completeness roadmap) |
| Tarski1930 | Missing | Low |
| Godel1930 | Missing | Low |
| FromJacobsen2022 | Missing | Low |

These are not cited in the current PR scope and can be deferred.

---

## 3. Lean Source File Citation Audit

### 3.1 MEDIUM: "full-connective tradition" in Defs.lean

**File**: `Cslib/Logics/Propositional/Defs.lean`, line 21
**Current text**: "following the standard Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition"
**Issue**: "Full-connective tradition" is an invented label with no literature precedent. It slightly mischaracterizes Gentzen (who keeps negation as a primitive, only noting it is eliminable via bot). The phrase omits Johansson, who is the most direct predecessor for making bot primitive.

**Recommended replacement** (per task 192 findings):
```
Primitives are `atom`, `bot` (falsum), `imp` (implication), `and` (conjunction), and
`or` (disjunction). Negation (`neg`), verum (`top`), and biconditional (`iff`) are
derived connectives (`abbrev`s). This follows natural deduction style
([Gentzen1935], [Prawitz1965], Ch. I sec. 1.2) and the constructive mathematics
tradition ([Johansson1937], [TroelstraVanDalen1988]) in which `neg A` abbreviates
`A -> bot` rather than being taken as primitive.
```

### 3.2 LOW: Church1956 in reference blocks

**Files**: Connectives.lean line 50, Defs.lean line 67
**Issue**: Church is listed in the reference blocks but not cited inline. Church's treatment is primarily classical. His IPL formulation (section 26) uses negation as a primitive, not bot. Including Church as a general reference is not wrong but could be misleading to readers who look up section 24 (primitive connectives) expecting to find support for the five-primitive-with-bot design.
**Recommendation**: Keep as a general reference but consider adding a brief qualifier, or demote from the reference block. Low priority.

### 3.3 LOW: Prawitz1965 in Connectives.lean

**File**: Connectives.lean line 47
**Issue**: Listed in the reference block but not cited inline in the module docstring. Prawitz is cited inline in Defs.lean (via the recommended fix in 3.1) and Basic.lean.
**Recommendation**: No action needed -- reference blocks can include general references.

### 3.4 OK: All Other Inline Citations

The inline citations in Connectives.lean (Wajsberg1938, McKinsey1939 at lines 31-32), Basic.lean (Johansson1937 at line 51), and the box modality citations (Blackburn2001, ChagrovZakharyaschev1997 at lines 72-73, 112-113) are all accurate and well-placed.

---

## 4. Completeness Assessment (Missing Citations)

### 4.1 Citations That Could Be Added

| Reference | Relevance | Priority |
|-----------|-----------|----------|
| Heyting1930 in Defs.lean | Heyting's axiom system is the starting point for IPL | Low -- already cited in Connectives.lean |
| Kolmogoroff1925 | Johansson cites Kolmogoroff for related treatment of bot | Low -- tangential |
| vanDalen2013 | More accessible modern treatment than TroelstraVanDalen1988 | Low -- already have TvD1988 |

### 4.2 Citations Confirmed Not Needed

| Reference | Reason Not Needed |
|-----------|-------------------|
| Post1921 | Classical truth-table work; not relevant to IPL five-primitive design |
| Henkin1949 | Relevant to completeness proofs (future PRs), not to this PR |
| Church1956 sections 24/26 | Already cited in source files; section-specific claims removed from PR descriptions |

### 4.3 Overall Completeness

The citation coverage is **good**. The core design decision (five primitives with bot, neg and top derived) is well-supported by:
- Johansson1937 (original source for bot as primitive, neg derived)
- Bentzen2023 (modern Lean formalization using the same pattern)
- Trufas2024 (independent Lean formalization confirming the pattern)
- TroelstraVanDalen1988 (standard textbook reference)

The classical Lukasiewicz encoding issue (and/or as derived) is well-supported by Wajsberg1938 and McKinsey1939.

---

## 5. Specific Recommendations

### Priority 1 (HIGH): Add Missing BibTeX Entries

Add entries for Bentzen2023 and Trufas2024 to `references.bib`. These are actively cited in PR 198's description. Drafted entries are available in task 192 round 2 teammate B findings (`specs/192_research_verify_literature_refs_pr_188/reports/02_teammate-b-findings.md`).

### Priority 2 (MEDIUM): Fix "full-connective tradition" in Defs.lean

Replace the invented label "standard Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition" (line 21) with language grounded in actual literature. See Section 3.1 for recommended replacement text.

### Priority 3 (LOW): Consider Church1956 placement

Church1956 in the reference blocks of Connectives.lean and Defs.lean is tangential to the IPL five-primitive design. Consider either:
- Adding a brief note "(classical treatment)" next to the reference, or
- Moving it to a separate "See also" subsection, or
- Keeping as-is (acceptable since reference blocks can include general references)

### Priority 4 (LOW): Minor authorship note in PR 198

PR 198 line 55 says "his Lean formalization" referring to Bentzen, but the paper has three authors (Guo, Chen, Bentzen). Consider changing to "their Lean formalization."

---

## 6. Cross-Check with Task 192

Task 192 (round 2) produced a comprehensive team research report. The findings are consistent:

| Task 192 Finding | This Review | Status |
|------------------|-------------|--------|
| Church sec 24 is classical only | Confirmed; sec 24 claim removed from PR descriptions | RESOLVED |
| Bentzen uses `impl` not `imp` | Confirmed; PR 198 correctly notes `impl` | RESOLVED |
| "full-connective tradition" invented | Confirmed; still in Defs.lean line 21 | STILL OPEN |
| 7 BibTeX entries missing | 2 are PR-scope (Bentzen, Trufas), 5 are deferred | PARTIALLY ADDRESSED |
| Johansson quotes confirmed | Confirmed with notation modernization caveat | NO ACTION NEEDED |
| Gentzen does not use "imp" | PR descriptions no longer claim Gentzen uses "imp" | RESOLVED |

Key improvements since task 192: The PR descriptions (both 188 and 198) have been cleaned up. The Church sec 24 claim, the "impl is non-standard" claim, and the Gentzen/Prawitz naming claim have all been removed. The remaining issues are: (1) Defs.lean docstring, (2) missing BibTeX entries.

---

## Summary

- **Bentzen2023 citation**: ACCURATE
- **Trufas2024 citation**: ACCURATE
- **Johansson1937 citation**: ACCURATE (with conventional notation modernization)
- **TroelstraVanDalen1988 citation**: PLAUSIBLE, unverifiable without source text
- **references.bib**: 10/10 Lean-source BibKeys present; 2 PR-description BibKeys (Bentzen2023, Trufas2024) MISSING
- **Defs.lean docstring**: "full-connective tradition" is an invented label -- recommend rewording
- **Church1956 in source files**: Tangential but not harmful in reference block position
- **Overall assessment**: PR citation quality is good. Two action items: add 2 BibTeX entries, fix 1 docstring phrase.
