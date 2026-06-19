# Teammate D Findings (Round 2): Revised PR Description Sections

**Role**: Horizons — concrete revised text for each problematic section
**Task**: 192
**Date**: 2026-06-14

## Overview

This report provides exact replacement text for each problematic section in the PR description at `specs/archive/188_first_propositional_upstream_pr/pr-description.md`, based on Round 1 synthesis findings. For each section: current text, revised text, and brief rationale.

---

## Section 1: "Why `bot` Should Be Primitive" — Citation Paragraph (lines 48–53)

### Current Text

```
With primitive `bot`, all derived connectives (`neg`, `top`, `iff`) and logic definitions
(`IPL`, `IsIntuitionistic`, `IsClassical`) are constraint-free. The choice of primitive
connectives for propositional logic is discussed in [Church1956] §24; the five-primitive
signature with `⊥` is the standard one for intuitionistic and minimal logic in
[TroelstraVanDalen1988] Chapter 2. Primitive `⊥` is required for Johansson's minimal logic
[Johansson1937], which defines negation `¬A := A → ⊥` using `⊥` as an undefined primitive
symbol ("undefiniertes Grundzeichen").
```

### Revised Text

```
With primitive `bot`, all derived connectives (`neg`, `top`, `iff`) and logic definitions
(`IPL`, `IsIntuitionistic`, `IsClassical`) are constraint-free. For intuitionistic and
minimal logic, conjunction and disjunction cannot be defined from implication and negation
alone ([McKinsey1939]), so all four connectives {⊥, →, ∧, ∨} must appear as primitives in
the formula type. This four-connective signature is used in [TroelstraVanDalen1988] and
[Prawitz1965]. For a general discussion of primitive connective choice in propositional
logic, see [Church1956] §24. Primitive `⊥` is required for Johansson's minimal logic
[Johansson1937], which defines negation `¬A := A → ⊥` using `⊥` as an undefined primitive
symbol ("undefiniertes Grundzeichen").
```

### Rationale

Church §24 covers classical functional completeness (showing {→, f} suffices classically), not intuitionistic connective independence. A reviewer who reads §24 expecting IPL motivation will find the opposite: a classical reduction argument. The McKinsey 1939 result is the actual theoretical justification for why five primitives are needed — it proves ∧ and ∨ are independent in Heyting's calculus. Moving Church to a "general reference" position and leading with McKinsey corrects the logical order of the argument. Wajsberg 1938 is omitted here to keep the text concise; it can be added if reviewers want supporting citations. The phrase "Chapter 2" in TroelstraVanDalen is retained but not asserted as the specific location, since the exact section (2.x vs 10.4) cannot be verified without file access.

---

## Section 2: Summary bullet — "Renamed `impl` to `imp`" (line 20)

### Current Text

```
   - Renamed `impl` to `imp` (standard notation per Gentzen/Prawitz)
```

### Revised Text

```
   - Renamed `impl` to `imp` (matching CSLib's existing convention in Bimodal and Temporal
     formula types, and aligning constructor names with rule prefixes: `impI`/`impE`,
     cf. `andI`/`andE1`, `orI1`/`orE`)
```

### Rationale

Gentzen (1935) wrote in German using ⊃ and the word "Implikation." Prawitz (1965) used → and "implication." Neither used the ASCII abbreviation "imp" — it is irrelevant to mathematical publishing conventions of 1935 or 1965. The attribution is historically anachronistic. The real justification is CSLib-internal: Bimodal and Temporal formula types already use `| imp`, and introduction/elimination rules already use `impI`/`impE`. Citing internal consistency is both accurate and defensible to a reviewer who checks.

---

## Section 3: "Naming: `imp` vs `impl`" (lines 55–59)

### Current Text

```
## Naming: `imp` vs `impl`

The name `imp` is standard in Lean formalization practice (e.g., Lean's own `Prop` operations
and modal logic formalizations). The previous `impl` was non-standard — no major proof theory
reference uses this abbreviation for implication.
```

### Revised Text

```
## Naming: `imp` vs `impl`

The name `imp` is used throughout CSLib's other logic modules (Bimodal, Temporal) and aligns
constructor names with introduction/elimination rule names (`impI`/`impE`), consistent with
the `andI`/`andE1`/`orI1`/`orE` naming pattern. This makes the propositional module
consistent with the rest of CSLib rather than introducing an isolated abbreviation (`impl`).
```

### Rationale

The original claim "no major proof theory reference uses impl" is directly falsified: Bentzen 2023 (the first verified Henkin completeness proof for IPL in Lean) uses `impl`. The positive case for `imp` — CSLib-internal uniformity — is both true and more compelling to Mathlib reviewers who care about library coherence. "Lean's own `Prop` operations" is vague and harder to verify; removing it tightens the argument.

---

## Section 4: "Relationship to PR #607" (lines 65–71)

### Current Text

```
## Relationship to PR #607

PR #607 by @fmontesi introduces `HasAnd`/`HasOr` typeclasses. Our `Connectives.lean` follows
the same operator-typeclass approach and is compatible: we define `HasBot`, `HasImp`, `HasAnd`,
`HasOr` as atomic classes and `PropositionalConnectives` as a bundled class. Our PR is a
superset of PR #607 for the propositional case, while PR #607 focuses on conjunctive/disjunctive
operators. If PR #607 merges first, our `Connectives.lean` can absorb its definitions.
```

### Revised Text

```
## Relationship to PR #607

PR #607 by @fmontesi introduces `HasAnd`/`HasOr` typeclasses. Our `Connectives.lean` builds
on the per-operator typeclass direction established by PR #607, adding `HasBot` and `HasImp`
alongside `HasAnd` and `HasOr`, and bundling them in `PropositionalConnectives`. The designs
are compatible and complementary. If PR #607 merges first, we will update `Connectives.lean`
to import its `HasAnd`/`HasOr` definitions rather than redefining them.
```

### Rationale

"Our PR is a superset of PR #607" reads as dismissive toward fmontesi, who is both the PR #607 author and a CODEOWNERS reviewer for the propositional modules. Calling it a "superset" implies the other PR is subsumed and therefore less important. The revised text frames the relationship as complementary — our PR adds Bot/Imp; their PR adds And/Or — and explicitly commits to importing their work if it merges first. This is both more accurate (the two PRs address different connective pairs) and more diplomatically effective.

---

## Section 5: New Subsection — "Relationship to PR #536"

### Current Text

*(Not present in the PR description)*

### Revised Text

Add as a new subsection after "Relationship to PR #607":

```
## Relationship to PR #536

PR #536 by @thomaskwaring modifies `Defs.lean` and `NaturalDeduction/Basic.lean` — the same
files changed by this PR. We are aware of the overlap. If PR #536 merges first, this PR will
be rebased to incorporate those changes. We are happy to coordinate directly with @thomaskwaring
to minimize merge conflicts.
```

### Rationale

PR #536 touches the exact same files as this PR. Reviewers will immediately ask about merge conflicts if no acknowledgment appears. Proactively naming the overlap and offering to coordinate signals good contributor hygiene. Omitting it looks like an oversight.

---

## Section 6: "AI Tools Used" (lines 107–112)

### Current Text

```
## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and extracting files from a development branch to create a clean PR branch
- Running CI verification commands
```

### Revised Text

```
## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and extracting files from a development branch to create a clean PR branch
- Running CI verification commands

The mathematical content, proof architecture, and design decisions were reviewed and verified
by the author. All Lean code compiles with no `sorry`s.
```

### Rationale

Mathlib's AI policy requires disclosure (present) plus a statement that the mathematical content has been human-verified. Without the verification statement, reviewers cannot assess whether the AI-generated content was checked. The addition is brief and standard: it attests that the author took responsibility for the mathematical substance, not just the mechanical formatting. "No sorries" is a standard CI requirement and worth stating explicitly since CI output is not visible in the PR description.

---

## Section 7: "Roadmap mirrors TvD" (line 85)

### Current Text

```
The planned roadmap mirrors the structure of Troelstra & van Dalen [TroelstraVanDalen1988]
Chapter 2, with PR 5-6 following the completeness proof strategy there.
```

### Revised Text

```
The planned roadmap draws from the structure of Troelstra & van Dalen [TroelstraVanDalen1988],
with PR 5-6 following a Kripke-based completeness proof strategy in the spirit of that work.
```

### Rationale

"Mirrors" implies a closer structural correspondence than can be verified without file access to TvD. Additionally, the exact chapter (Ch. 2 vs §10.4) is uncertain per Round 1 findings. "Draws from" is softer and accurate: CSLib's roadmap is inspired by TvD's presentation, not a direct chapter-by-chapter mapping. "In the spirit of" covers the proof strategy without overclaiming structural identity.

---

## Sources.md: File Availability Updates

Examining `specs/literature/README.md` (the canonical sources file), the following entries currently marked `[NO FILE]` now have markdown conversions available in `specs/literature/`:

| Entry | Current Marker | Files Found | Recommended Update |
|-------|---------------|-------------|-------------------|
| Johansson 1937 | `[PDF] [MD]` | `johansson_1937.md` exists | Already correct |
| Bentzen 2023 | `[PDF] [MD]` | `bentzen_2023.md` exists | Already correct |
| Gentzen 1935 | `[PDF]` | `gentzen_1935.md` exists | **Add `[MD]`** |
| Church 1956 | `[NO FILE]` | `church_1956.md` exists | **Change to `[MD]`** |
| Trufas 2024 | `[PDF]` | `trufas_2024.md` exists | **Add `[MD]`** |
| From & Jacobsen 2022 | `[PDF] [MD]` | `from_2022.md` exists | Already correct |
| Chagrov & Zakharyaschev 1997 | `[MD]` | `chagrov_1997.md` exists | Already correct |
| Blackburn et al. 2001 | `[PDF] [MD]` | `blackburn_2001.md` exists | Already correct |
| Mendelson 2016 | `[NO FILE]` | `mendelson_2016.md` exists | **Change to `[MD]`** |

**Entries confirmed still `[NO FILE]`** (no matching `.md` file found):
- McKinsey 1939 — `[NO FILE]` (correct)
- Wajsberg 1938 — `[NO FILE]` (correct)
- TroelstraVanDalen 1988 — `[NO FILE]` (correct)
- Prawitz 1965 — `[NO FILE]` (correct)
- Heyting 1930 — `[NO FILE]` (correct)

**Four entries need updates in README.md**:
1. Gentzen 1935: `[PDF]` → `[PDF] [MD]`
2. Church 1956: `[NO FILE]` → `[MD]` (no PDF, but markdown conversion present)
3. Trufas 2024: `[PDF]` → `[PDF] [MD]`
4. Mendelson 2016: `[NO FILE]` → `[MD]`

---

## Summary of All Changes

| Section | Change Type | Severity |
|---------|-------------|----------|
| "Why bot should be primitive" citation paragraph | Replace Church-first framing with McKinsey-first | CRITICAL |
| Summary bullet "Renamed impl to imp" | Remove Gentzen/Prawitz attribution; cite CSLib consistency | HIGH |
| "Naming: imp vs impl" section | Rewrite: drop "no reference uses impl"; use internal consistency argument | HIGH |
| "Relationship to PR #607" | Reframe "superset" as "builds on / complements" | MEDIUM |
| New: "Relationship to PR #536" | Add acknowledgment and rebase commitment | MEDIUM |
| "AI Tools Used" | Add human verification statement | MEDIUM |
| "Roadmap mirrors TvD" | Soften "mirrors" to "draws from" | LOW |
| sources.md (README.md) | Update 4 file availability markers | LOW |
