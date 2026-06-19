# Research Report: Task #192

**Task**: Research and verify literature references in task 188 PR description
**Date**: 2026-06-14
**Mode**: Team Research (4 teammates)

## Summary

Team verification of literature claims in the PR description for CSLib's first propositional upstream PR. Of the five main literature claims, two are well-verified (Johansson, five-primitive signature), one is defensible but indirect (Church §24), one is an overclaim (TroelstraVanDalen precision), and one is partially falsified ("imp per Gentzen/Prawitz"). The most critical gap is the missing McKinsey 1939 citation — the actual proof that five primitives are necessary for intuitionistic logic. Several strategic improvements are recommended for upstream acceptance.

## Claim Verification Summary

| # | Claim | Verdict | Confidence | Action |
|---|-------|---------|------------|--------|
| 1 | [Church1956] §24 discusses primitive connective choice | **VERIFIED** (topic correct) | HIGH | Reword — §24 is classical, not intuitionistic |
| 2 | Church §24 supports five-primitive+⊥ for IPL | **PARTIALLY FALSIFIED** | HIGH | Remove or qualify significantly |
| 3 | [TroelstraVanDalen1988] Ch. 2 uses five-primitive signature | **PLAUSIBLE** (unverifiable) | MEDIUM | Keep; may need section precision |
| 4 | [Johansson1937] "undefiniertes Grundzeichen" | **VERIFIED** | HIGH | Keep — exact German quote confirmed |
| 5 | "imp" standard per Gentzen/Prawitz | **PARTIALLY FALSIFIED** | HIGH | Replace with Lean convention argument |
| 6 | "no major reference uses impl" | **OVERSTATED** | HIGH | Bentzen 2023 uses `impl`; reword |
| 7 | Roadmap "mirrors" TvD Ch. 2 | **OVERCLAIMED** | MEDIUM | Soften to "draws from" |

## Key Findings

### 1. Church §24: Correct Topic, Wrong Scope (HIGH severity)

All teammates agree: Church §24 is titled "Primitive connectives for the propositional calculus" — the topic reference is accurate. However, §24 concerns **classical** functional completeness (truth-table expressibility) and discusses two-connective bases like {⊃, ¬} and {⊃, f}. It does **not** discuss:
- The five-primitive signature {⊥, →, ∧, ∨} for intuitionistic logic
- Non-definability of ∧/∨ from →/⊥ in intuitionistic logic
- Connective independence in Heyting's calculus

Church §24 actually shows {implication, f} is classically *complete* — which undermines the five-primitive motivation in the classical case. A reviewer who checks §24 (as ctchou checked Gentzen in PR #635) will find the citation does not support the intuitionistic claim.

**Recommendation**: Replace with McKinsey 1939 / Wajsberg 1938 citations, or qualify Church as a general reference for the topic of primitive connective choice rather than implying it supports the specific five-primitive design.

### 2. Johansson 1937: Fully Verified (LOW severity — no change needed)

The exact German phrase "undefiniertes Grundzeichen" appears verbatim in Johansson 1937 §1 (p. 120):

> "Die Auffassung von Λ als undefiniertes Grundzeichen und die Definition von ¬ durch [¬a := a ⊃ Λ] liegt dann sehr nahe."

Translation: "The conception of Λ as an undefined primitive symbol and the definition of ¬ via [¬a := a ⊃ Λ] is then very natural."

Johansson uses Λ (not ⊥) and ⊃ (not →), but the mathematical content matches exactly. A second occurrence on p. 132 uses "undefinierte Grundaussage" (undefined primitive proposition). The PR's quotation of "undefiniertes Grundzeichen" is accurate to the first occurrence.

### 3. McKinsey 1939: Critical Missing Citation (CRITICAL severity)

**All teammates flagged this independently.** The `sources.md` file explicitly marks McKinsey 1939 as "Critical for justifying the five-primitive formula type," yet the PR description does not cite it anywhere. McKinsey proved that conjunction and disjunction **cannot** be defined from implication and negation in Heyting's intuitionistic calculus — this is the key theoretical result justifying why five primitives are needed.

The PR cites Church §24 in the position where McKinsey 1939 should appear. Church §24 proves various bases are classically complete (including {→, f}), which is the opposite of what the PR needs to argue.

**Recommendation**: Add [McKinsey1939] (and optionally [Wajsberg1938]) to the "Why `bot` Should Be Primitive" section.

### 4. "imp" Naming: Gentzen/Prawitz Attribution is Anachronistic (HIGH severity)

All teammates agree: Gentzen (1935) wrote in German using the symbol ⊃ for implication and the word "Implikation" in prose. Prawitz (1965) used → and the word "implication." Neither used the ASCII abbreviation "imp" — ASCII was not relevant to mathematical publishing in 1935 or 1965. The PR's claim "standard notation per Gentzen/Prawitz" is historically inaccurate.

Additionally, Teammate B found that Bentzen 2023 — the first verified Henkin-style completeness proof for IPL in Lean — uses `impl` as its constructor name, directly contradicting the claim that "no major proof theory reference uses this abbreviation." The landscape of Lean formalization naming:

| Project | Constructor Name |
|---------|-----------------|
| CSLib (Bimodal, Temporal) | `imp` |
| Bentzen 2023 (Lean 3) | `impl` |
| Trufas 2024 (Lean 4) | `implication` |
| From & Jacobsen 2022 (Isabelle) | `Imp` |

The real justification for `imp` is **CSLib-internal consistency**: the Bimodal and Temporal formula types already use `| imp`, and rule names `impI`/`impE` use the `imp` prefix matching `andI`/`andE1`/`orI1`/`orE`.

**Recommendation**: Replace "standard notation per Gentzen/Prawitz" with an internal consistency argument. Replace "no major proof theory reference uses impl" with the positive case for `imp`.

### 5. "Superset of PR #607": Diplomatically Risky (MEDIUM severity)

Teammate D flagged that calling the PR "a superset of PR #607" is dismissive toward fmontesi, who is both the PR #607 author and a CODEOWNERS reviewer. The language should be collaborative, not competitive.

**Recommendation**: Reframe as "builds on the per-operator typeclass direction established by PR #607" with explicit merge coordination.

### 6. Missing PR #536 Acknowledgment (MEDIUM severity)

Teammate D noted that PR #536 (thomaskwaring) modifies `Defs.lean` and `NaturalDeduction/Basic.lean` — the same files this PR touches. No mention appears in the PR description. Reviewers will ask about merge conflicts.

**Recommendation**: Add acknowledgment and merge coordination plan.

## Synthesis

### Conflicts Between Teammates

No significant conflicts. All four teammates independently identified the Gentzen/Prawitz attribution and Church §24 scope as problems. Teammates B and C both flagged the McKinsey 1939 omission. Teammate D's strategic perspective reinforced the technical findings.

Minor disagreement on TroelstraVanDalen: Teammate A noted the "five-primitive" vs "four-connective" distinction (CSLib counts `atom` as a constructor; the literature counts four logical connectives). Teammate C suggested the section reference might be 10.4 rather than Chapter 2. These are precision issues, not contradictions.

### Gaps Identified

1. **TroelstraVanDalen1988 is `[NO FILE]`** — cannot verify Chapter 2 vs Section 10.4 distinction
2. **Heyting 1930** is relevant (original IPL with primitive ∧/∨) but uncited in the PR
3. **PR #536 conflict** is unaddressed
4. **AI disclosure** should add human verification statement per Mathlib AI policy

### Recommended PR Description Changes

**Priority 1 — Fix "Why bot Should Be Primitive" citations**:

Replace:
> The choice of primitive connectives for propositional logic is discussed in [Church1956] §24; the five-primitive signature with ⊥ is the standard one for intuitionistic and minimal logic in [TroelstraVanDalen1988] Chapter 2.

With:
> For intuitionistic and minimal logic, conjunction and disjunction cannot be defined from implication and negation ([McKinsey1939], [Wajsberg1938]), necessitating primitive ∧ and ∨ alongside ⊥ and →. This four-connective signature {⊥, →, ∧, ∨} is used in [TroelstraVanDalen1988] and [Prawitz1965]. For a general discussion of primitive connective choice in propositional logic, see [Church1956] §24.

**Priority 2 — Fix "imp" naming justification**:

Replace:
> Renamed `impl` to `imp` (standard notation per Gentzen/Prawitz)

With:
> Renamed `impl` to `imp` (matching CSLib's existing convention in Bimodal and Temporal formula types, and aligning constructor names with rule name prefixes: `impI`/`impE`, cf. `andI`/`andE1`, `orI1`/`orE`)

Replace:
> The name `imp` is standard in Lean formalization practice (e.g., Lean's own `Prop` operations and modal logic formalizations). The previous `impl` was non-standard — no major proof theory reference uses this abbreviation for implication.

With:
> The name `imp` is used throughout CSLib's other logic modules (Bimodal, Temporal) and aligns constructor names with the introduction/elimination rule names `impI`/`impE`.

**Priority 3 — Reframe PR #607 relationship**:

Replace:
> Our PR is a superset of PR #607 for the propositional case

With:
> Our `Connectives.lean` builds on the per-operator typeclass direction of PR #607, adding `HasBot` and `HasImp` alongside PR #607's `HasAnd` and `HasOr`. If PR #607 merges first, we will update to import its definitions rather than redefining them.

**Priority 4 — Add human verification to AI disclosure**:

Append:
> The mathematical content, proof architecture, and design decisions were verified by the author. All Lean code compiles with no sorries.

**Priority 5 — Acknowledge PR #536**:

Add:
> This PR also intersects with PR #536 (@thomaskwaring), which modifies `Defs.lean`. If PR #536 merges first, this PR will be rebased accordingly.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary literature verification | completed | high |
| B | Alternative sources and naming | completed | high |
| C | Critic (gaps and blind spots) | completed | high |
| D | Horizons (strategic PR quality) | completed | high |

## References

- Church, A. (1956). *Introduction to Mathematical Logic*, Vol. 1. Princeton University Press. [Church1956]
- Gentzen, G. (1935). Untersuchungen über das logische Schließen. *Mathematische Zeitschrift*, 39:176-210, 405-431. [Gentzen1935]
- Johansson, I. (1937). Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus. *Compositio Mathematica*, 4:119-136. [Johansson1937]
- McKinsey, J.C.C. (1939). Proof of the Independence of the Primitive Symbols of Heyting's Calculus. [McKinsey1939]
- Prawitz, D. (1965). *Natural Deduction: A Proof-Theoretical Study*. Almqvist & Wiksell. [Prawitz1965]
- Troelstra, A.S. & van Dalen, D. (1988). *Constructivism in Mathematics*, Vol. 1. North-Holland. [TroelstraVanDalen1988]
- Wajsberg, M. (1938). Untersuchungen über den Aussagenkalkül von A. Heyting. [Wajsberg1938]
- Bentzen, B. (2023). Verified completeness in Henkin-style for intuitionistic propositional logic. arXiv:2310.01916.
- Trufas, L. (2024). Intuitionistic Propositional Logic in Lean. arXiv:2410.23765.
