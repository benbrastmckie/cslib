# Research Report: Task #192 (Round 2)

**Task**: Research new literature sources and draft concrete revisions for PR description, references.bib, and codebase citations
**Date**: 2026-06-14
**Mode**: Team Research (4 teammates)
**Session**: sess_1781458639_96acef

## Summary

Round 2 used new full-content markdown conversions of primary sources (Church, Gentzen, Johansson, Bentzen, Trufas) to verify claims at the source level and produce concrete revision text. All Round 1 findings are confirmed and strengthened. The key deliverables are: (1) exact replacement text for 7 PR description sections, (2) 7 drafted BibTeX entries for references.bib, (3) a recommended Defs.lean docstring fix, and (4) sources.md file-availability updates.

## Verified Findings (Primary Source Level)

### Church §24: Confirmed Misleading (HIGH)

Teammate A verified against `church_1956.md` lines 7724-8079:
- §24 is titled "Primitive connectives for the propositional calculus" — topic is correct
- Content is **entirely classical** — discusses truth-table completeness of {⊃, ¬}, {⊃, f}, Sheffer stroke, etc.
- **No mention of intuitionistic logic** in §24
- §26 (not §24) covers IPL, listing primitives as {→, ∧, ∨, ↔, ¬} — with negation primitive, **not ⊥**
- Church's formulation of minimal logic (P") also keeps negation primitive

**Conclusion**: Church §24 should be demoted to a general reference. The PR should lead with McKinsey 1939.

### Gentzen 1935: Confirmed No "imp" (HIGH)

Teammate A verified against `gentzen_1935.md`:
- Gentzen uses **⊃** (horseshoe) for implication throughout
- Inference figures named `⊃-I` / `⊃-E` — using the symbol, not an English abbreviation
- NJ uses {&, v, ⊃, ¬, ∀, ∃} as logical symbols
- §5.2 notes ¬A can be treated as A ⊃ A (falsum), but keeps ¬ as an explicit primitive
- **The string "imp" never appears in the text**

### Johansson 1937: Confirmed Accurate (HIGH)

Teammate A verified against `johansson_1937.md`:
- "undefiniertes Grundzeichen" confirmed at lines 71-72 (§1)
- "undefinierte Grundaussage" confirmed at line 362 (§4)
- Johansson uses **A** (not ⊥ or Λ) for falsum, and **⊃** (not →) for implication
- Definition: ¬a := a ⊃ A (formula 22, line 320)
- The PR's modernization (⊥ for A, → for ⊃) is conventional, not fabrication

### Bentzen 2023: Uses `impl`, Not `imp` (HIGH)

Teammate A confirmed against `bentzen_2023.md` lines 110-127:
```lean
inductive form : Type
| atom : N → form
| bot  : form
| impl : form → form → form
| and  : form → form → form
| or   : form → form → form
```
This directly contradicts the PR claim that "`impl` was non-standard."

## references.bib Audit

### Status: All PR-Scope BibKeys Present

Teammate B confirmed all 9 BibKeys cited in PR-scope Lean files exist in references.bib. All 8 checked entries are accurate — no corrections needed.

### 7 Missing Entries Drafted

The following BibKeys are cited in sources.md/research reports but missing from references.bib. Teammate B drafted BibTeX entries for each:

1. **Bentzen2023** — Guo, Chen, Bentzen. *Verified Completeness in Henkin-Style for IPL*. LNGAI/LAL 2023.
2. **Trufas2024** — Trufas. *Intuitionistic Propositional Logic in Lean*. EPTCS 410, FROM 2024.
3. **Post1921** — Post. *Introduction to a General Theory of Elementary Propositions*. AJM 43(3).
4. **Henkin1949** — Henkin. *Completeness of First-Order Functional Calculus*. JSL 14(3).
5. **Tarski1930** — Tarski. *Fundamentale Begriffe der Methodologie*. Monatshefte 37.
6. **Godel1930** — Gödel. *Die Vollständigkeit der Axiome*. Monatshefte 37.
7. **FromJacobsen2022** — From, Jacobsen, Villadsen. *SeCaV*. EPTCS 357, LSFA 2021.

Full BibTeX in `02_teammate-b-findings.md`.

## Codebase Citation Audit

### Medium Severity: "full-connective tradition" in Defs.lean

Teammate C found the phrase "standard Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition" (Defs.lean line 21) is:
- An invented label with no literature precedent
- Slightly mischaracterizes Gentzen (who keeps ¬ as primitive, only noting it's eliminable)
- Omits Johansson, the most direct predecessor for the CSLib design

**Recommended replacement** (lines 20-22):
```
Primitives are `atom`, `bot` (falsum), `imp` (implication), `and` (conjunction), and
`or` (disjunction). Negation (`neg`), verum (`top`), and biconditional (`iff`) are
derived connectives (`abbrev`s). This follows natural deduction style
([Gentzen1935], [Prawitz1965], Ch. I §1.2) and the constructive mathematics
tradition ([Johansson1937], [TroelstraVanDalen1988]) in which `¬A` abbreviates
`A → ⊥` rather than being taken as primitive.
```

### Low Severity Issues
- [Church1956] in Connectives.lean/Defs.lean reference blocks is tangential (classical, not intuitionistic)
- [Prawitz1965] in Connectives.lean reference block is not cited inline
- [TroelstraVanDalen1988] §10.4 — plausible but unverifiable without the book

### All Other Citations Accurate
Johansson, Wajsberg, McKinsey, and Gentzen citations in Connectives.lean, Basic.lean, Equivalence.lean, and Axioms.lean are all accurate per primary sources.

## Concrete PR Description Revisions

Teammate D produced exact replacement text for 7 sections. Summary:

### Priority 1 (CRITICAL): "Why bot Should Be Primitive" Citations
Lead with McKinsey 1939 (independence proof), demote Church §24 to general reference, add Prawitz alongside TvD.

### Priority 2 (HIGH): Summary Bullet — "Renamed impl to imp"
Replace "standard notation per Gentzen/Prawitz" with CSLib internal consistency argument.

### Priority 3 (HIGH): "Naming: imp vs impl" Section
Replace "no major reference uses impl" (false — Bentzen 2023 does) with positive CSLib-uniformity argument.

### Priority 4 (MEDIUM): "Relationship to PR #607"
Replace "superset" with "builds on / complements" framing.

### Priority 5 (MEDIUM): New "Relationship to PR #536"
Add acknowledgment of overlapping file modifications with merge coordination offer.

### Priority 6 (MEDIUM): AI Disclosure
Add human verification statement per Mathlib AI policy.

### Priority 7 (LOW): Roadmap
Soften "mirrors" to "draws from."

Full replacement text in `02_teammate-d-findings.md`.

## sources.md File Availability Updates

4 entries need marker updates:

| Entry | Current | Should Be |
|-------|---------|-----------|
| Gentzen 1935 | `[PDF]` | `[PDF] [MD]` |
| Church 1956 | `[NO FILE]` | `[MD]` |
| Trufas 2024 | `[PDF]` | `[PDF] [MD]` |
| Mendelson 2016 | `[NO FILE]` | `[MD]` |

## Implementation Scope

The implementation phase should:
1. Edit `pr-description.md` with the 7 revised sections from Teammate D
2. Edit `Defs.lean` line 21 docstring (replace "full-connective tradition")
3. Add 7 BibTeX entries to `references.bib` from Teammate B drafts
4. Update `sources.md` file availability markers (4 entries)
5. Run `lake build` to verify Lean files still compile after docstring changes

## Teammate Contributions

| Teammate | Angle | Status | Key Finding |
|----------|-------|--------|-------------|
| A | Primary source verification | completed | Church §24 confirmed classical-only; §26 uses {→,∧,∨,↔,¬} not {⊥,→,∧,∨} |
| B | references.bib audit | completed | All PR-scope BibKeys present; 7 missing entries drafted |
| C | Codebase citation audit | completed | "full-connective tradition" is invented label; most other claims accurate |
| D | PR description revision | completed | Exact replacement text for 7 sections |
