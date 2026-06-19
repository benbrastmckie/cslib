# Teammate B Findings: Alternative Sources and Naming Convention Claims

## Investigation Scope

Examination of (1) the "imp" vs "impl" naming claim in the PR, (2) the Gentzen/Prawitz
attribution, (3) the five-primitive signature claim, (4) the McKinsey 1939 citation, and
(5) the Troelstra & van Dalen roadmap claim. Primary method: reading the literature files
and searching the codebase for naming patterns.

---

## Key Finding 1: "imp" vs "impl" — The PR Claim is Mostly Accurate, With Caveats

### Claim Examined
> "The name 'imp' is standard in Lean formalization practice... no major proof theory
> reference uses this abbreviation ['impl'] for implication."

### What the Evidence Shows

**CSLib itself uses "imp" consistently across all logic levels.** The Bimodal `Formula`
type (`Cslib/Logics/Bimodal/Syntax/Formula.lean` line 38), the Temporal `Formula` type
(`Cslib/Logics/Temporal/Syntax/Formula.lean` line 52), and the Propositional `Proposition`
type (the file being refactored) all use `| imp` as the constructor name. The renamed
rules `impI`/`impE` appear throughout the natural deduction system.

**However, the claim about external formalization is mixed.** Looking at the literature files:

- **Bentzen 2023** (`specs/literature/Bentzen2023.md`): Uses `impl` as the constructor name:
  ```
  | impl : form → form → form
  ```
  This directly contradicts the PR claim that "impl" is non-standard in Lean formalization.
  Bentzen 2023 is a Lean 3 formalization (the first verified Henkin-style completeness proof
  for IPL) and it uses `impl`, not `imp`.

- **Trufas 2024** (`specs/literature/Trufas2024.md`): Uses `implication` as the constructor:
  ```
  | implication : Formula → Formula → Formula
  ```
  A third variant, neither `imp` nor `impl`.

- **From & Jacobsen 2022** (`specs/literature/FromJacobsen2022.md`): Uses `Imp` (capital I)
  in Isabelle/HOL:
  ```
  datatype fm = Pre nat ⟨tm list⟩ | Imp fm fm | Dis fm fm | Con fm fm | Exi fm | Uni fm | Neg fm
  ```

- **CSLib's Foundations module** uses `HasImp` as the typeclass name and `imp` as the
  operation, which is internally consistent.

**Assessment**: The claim that "impl" is non-standard is weakened by Bentzen 2023 using
exactly "impl" in the Lean formalization this PR is most directly related to. The PR is
accurate that "imp" is the CSLib-wide convention (used in Bimodal and Temporal logics before
this PR touched propositional), and the `impl` name in the old Proposition type was
inconsistent with the rest of CSLib. The stronger claim ("no major proof theory reference
uses this abbreviation") is an overstatement given Bentzen 2023.

**Confidence: MEDIUM** — "imp" is the right choice for CSLib internal consistency; the
"no reference uses impl" claim is an overstatement.

---

## Key Finding 2: The Gentzen/Prawitz Attribution is Problematic

### Claim Examined
> "Renamed `impl` to `imp` (standard notation per Gentzen/Prawitz)"

### What the Evidence Shows

The `Gentzen1935.md` file is not the actual paper content — it is metadata from the GDZ
Göttingen digitization library, describing archival terms and conditions. The actual Gentzen
1935 article content is not in the markdown file (it is a scanned PDF with no OCR layer,
per `sources.md` line 103). The metadata shown belongs to a different article ("Über die
Lösbarkeit der Gleichung t²-Du²=-4"), not Gentzen's logic paper.

More importantly: **Gentzen wrote in German and used full German words**, not English
abbreviations. He did not abbreviate "Implikation" as "imp" or "impl" — he used logical
symbols directly (→, ⊃). `sources.md` line 103 notes: "Gentzen uses all connectives as
primitive in his intuitionistic system." The attribution of "imp" to Gentzen/Prawitz is
a retroactive standardization claim, not a direct citation to their notation.

The `Defs.lean` file now claims the convention follows "standard Gentzen/Prawitz/Troelstra-
van Dalen full-connective tradition" (line 22–23 of Defs.lean), which is a broader and more
defensible characterization than the PR description's bare "standard notation per Gentzen/Prawitz."

**Confidence: HIGH** — The Gentzen/Prawitz attribution in the PR description is vague and
potentially misleading. The Defs.lean module docstring gives a better-worded attribution.

---

## Key Finding 3: Five-Primitive Signature — The Claim is Accurate and Well-Supported

### Claim Examined
> "five primitives {atom, bot, imp, and, or} is standard"

### What the Evidence Shows

**All three Lean formalization sources in the literature use five primitives (or equivalent):**

1. **Bentzen 2023**: `{atom, bot, impl, and, or}` — identical structure, different name for `→`
2. **Trufas 2024**: `{var, bottom, and, or, implication}` — identical five-primitive structure
3. **From & Jacobsen 2022**: Uses `{Pre, Imp, Dis, Con, Neg}` for FOL (no `bot` as primitive,
   but a separate `Neg`)

**Heyting 1930** (per `sources.md`): "Conjunction and disjunction are primitive (not definable
from implication and falsum)." This directly supports the five-primitive choice.

**McKinsey 1939** (per `sources.md`): "Proves that conjunction and disjunction cannot be defined
from implication and negation in intuitionistic logic." This is the formal proof of why
{atom, bot, imp} alone is insufficient for intuitionistic/minimal logic.

**The Lukasiewicz tradition** (per `sources.md`): The encodings `and φ ψ := ¬(φ → ¬ψ)` and
`or φ ψ := ¬φ → ψ` are used in CSLib's Modal, Temporal, and Bimodal logics (where classical
equivalence holds). But these fail intuitionistically, which is precisely why propositional
logic needs five primitives.

**Alternative standard choices**: Church 1956 is cited in the PR and `sources.md` for the
discussion of primitive connectives (§24). Church discusses various choices; the five-primitive
signature is indeed "the standard one for intuitionistic and minimal logic" as the PR claims.

**Confidence: HIGH** — The five-primitive claim is well-founded and matches all comparable
Lean formalizations.

---

## Key Finding 4: McKinsey 1939 Citation — Accurately Used

### Claim Examined
Whether the PR properly leverages the McKinsey 1939 independence result.

### What the Evidence Shows

The PR does not directly cite McKinsey 1939 in its text, but the `sources.md` (lines 49–52)
and the `Connectives.lean` module docstring both properly invoke McKinsey 1939 as the key
justification for why {bot, imp} is insufficient as a primitive basis for intuitionistic
logic.

The `Connectives.lean` file states:
> "The classical encodings `and φ ψ := ¬(φ → ¬ψ)` and `or φ ψ := ¬φ → ψ` are only
> propositionally equivalent to `∧` and `∨` in classical logic ([Wajsberg1938], [McKinsey1939]);
> they fail in intuitionistic and minimal logic."

This is an accurate use of the McKinsey result. Wajsberg 1938 is also cited, providing
additional independence results. The McKinsey citation is appropriate and appears in the
codebase documentation (Connectives.lean), though not in the PR description itself.

**Confidence: HIGH** — McKinsey 1939 is cited correctly in the codebase. The PR description
omits this citation but the Connectives.lean module docstring includes it.

---

## Key Finding 5: Troelstra & van Dalen Roadmap Claim

### Claim Examined
> "The planned roadmap mirrors the structure of Troelstra & van Dalen [TroelstraVanDalen1988]
> Chapter 2, with PR 5-6 following the completeness proof strategy there."

### What the Evidence Shows

The `sources.md` describes TroelstraVanDalen1988 as:
> "Covers intuitionistic propositional logic, Kripke semantics, completeness, natural
> deduction. Section 2.5 for Kripke completeness, Section 10.4 for natural deduction."

The Bentzen 2023 paper explicitly confirms that Chapter 2 of Troelstra & van Dalen contains
the Henkin-style completeness proof for IPL: "[Troelstra and van Dalen] propose a completeness
proof in Henkin-style for full intuitionistic predicate logic with respect to Kripke models...
as its propositional fragment is concerned, the main ingredient of Troelstra and van Dalen's
Henkin-proof is a model construction based on a consistent extension of sets of formulas."

The roadmap in the PR (PRs 1-6: formula type → Hilbert system → ND-Hilbert equivalence →
semantics → CPL completeness → IPL completeness) is a reasonable decomposition of the
mathematical content in TroelstraVanDalen1988 Chapter 2 plus related material. The
Henkin-style canonical model construction for IPL completeness is indeed the strategy in
Section 2.5 (per sources.md) and is Troelstra & van Dalen's method.

**Caveat**: TroelstraVanDalen1988 is marked `[NO FILE]` — the claim cannot be verified
against the actual book. The roadmap attribution is plausible given secondary sources
(Bentzen 2023 explicitly describes following this method).

**Confidence: MEDIUM-HIGH** — The roadmap claim is plausible and consistent with secondary
sources. Cannot be verified against the primary source.

---

## Alternative Approaches Found in the Literature

| Source | Formula Language | Implication Name | Primitives |
|--------|-----------------|------------------|------------|
| Bentzen 2023 (Lean 3) | IPL | `impl` | {atom, bot, impl, and, or} |
| Trufas 2024 (Lean 4) | IPL | `implication` | {var, bottom, and, or, implication} |
| From & Jacobsen 2022 (Isabelle) | FOL | `Imp` | {Pre, Imp, Dis, Con, Neg} |
| SeCaV unshortener | FOL | `Imp` | N/A (sequent calculus) |
| CSLib Bimodal/Temporal | Modal/Temporal | `imp` | includes box/until |
| CSLib Propositional (new) | PL | `imp` | {atom, bot, imp, and, or} |

The choice of `imp` is CSLib-internally consistent and matches the project's other logics.
The external Lean formalization landscape shows `impl`, `implication`, and `Imp` are all
used by different projects. No single "standard" exists across all Lean formalizations.

---

## Summary Assessment

| Claim | Accuracy | Evidence Quality |
|-------|----------|-----------------|
| "imp is standard in Lean formalization" | Partially true (CSLib-wide convention; not universally standard) | MEDIUM |
| "no reference uses 'impl'" | FALSE — Bentzen 2023 uses `impl` | HIGH |
| "standard notation per Gentzen/Prawitz" | Vague/misleading — they used symbols, not English abbrevs | HIGH |
| "five-primitive signature is standard" | TRUE — matches all comparable Lean formalizations | HIGH |
| McKinsey 1939 justifies five primitives | TRUE — correctly applied in Connectives.lean | HIGH |
| Roadmap mirrors TroelstraVanDalen Ch. 2 | PLAUSIBLE — confirmed by Bentzen 2023 secondary source | MEDIUM-HIGH |

---

## Critical Gap

The strongest concern with the PR description's naming claim is the overstatement about
"no major proof theory reference uses impl." The immediately relevant prior art (Bentzen 2023,
the first verified Henkin completeness proof for IPL in Lean) uses `impl`. The PR should
have said something like "The choice of `imp` matches the convention used throughout CSLib's
other logics (Bimodal, Temporal) and the `HasImp` typeclass in Foundations."

The actual justification for `imp` over `impl` is CSLib-internal consistency, not external
standardization. The naming claim in the PR description overstates the external consensus.
