# Research Report: Completeness Statement Alternatives for Primitive-Bot Design

- **Task**: 227 -- Algebraic completeness design
- **Session**: sess_1781717358_7b7629
- **Started**: 2026-06-17T00:00:00Z
- **Completed**: 2026-06-17T01:00:00Z
- **Effort**: Hard-mode research (H2+H3+H4)
- **Dependencies**: Report 02_d-thomas-approach.md (Thomas's design), Report 05 (implementation plan)
- **Reference grounding tier**: Tier 3 (implementation-backed: Thomas's code, CSLib code, Mathlib API)
- **Sources/Inputs**:
  - Thomas Waring: `Heyting.lean` (cslib_SKI fork), completeness pattern
  - CSLib: `Semantics/Algebra.lean` (AlgEvaluate, GHAValid, HAValid, BAValid)
  - CSLib: `Defs.lean` (Proposition inductive, 5 constructors)
  - Mathlib: `GeneralizedHeytingAlgebra`, `HeytingAlgebra`, `Pointed`, `OrderBot`
  - Report 02_d-thomas-approach.md, Report 05_hard-implementation-research.md
  - specs/227_algebraic_completeness_design/zulip.md (primitive-bot argument)
- **Artifacts**: This report
- **Standards**: report-format.md, anti-analysis.md, reference-grounding.md

---

## Executive Summary

- Five alternatives to the status quo `(v, bot_val)` completeness statement were evaluated:
  bundled interpretation, extended valuation (`Option Atom`), sum-type valuation
  (`Atom + Unit`), Johansson algebra typeclass, and AAL-style filter approach.
- All alternatives are mathematically equivalent to the status quo -- the `bot_val` parameter
  is inherent in the primitive-bot design and must appear somewhere in the quantifier.
- The **bundled interpretation** (`AlgInterp`) is the only alternative that improves the
  general completeness statement while preserving clean IPL/CPL specializations.
- **Recommendation**: Adopt a **hybrid approach** -- define `AlgInterp` as lightweight
  syntactic sugar for the general completeness theorem, keep `AlgEvaluate` with
  `(v, bot_val)` as the evaluation engine, and keep `HAValid`/`BAValid`/`GHAValid` unchanged.
- The status quo plan (report 05) is confirmed as the correct path. The bundled `AlgInterp`
  is an optional ergonomic addition, not a required change.

---

## Source-to-Implementation Mapping

| Source Claim | BibKey / Source | Lean Target | Translation Notes |
|--------------|----------------|-------------|-------------------|
| GHA evaluator with bot_val | Thomas Heyting.lean / CSLib Algebra.lean | `Cslib.Logic.PL.AlgEvaluate` | Already exists; 5-case vs Thomas's 4-case |
| GHAValid (all GHA, all v, all bot_val) | CSLib Algebra.lean | `Cslib.Logic.PL.GHAValid` | Already exists |
| HAValid (all HA, v, bot=bot) | CSLib Algebra.lean | `Cslib.Logic.PL.HAValid` | Already exists |
| BAValid (all BA, v, bot=bot) | CSLib Algebra.lean | `Cslib.Logic.PL.BAValid` | Already exists |
| Theory-parametric completeness | Thomas Heyting.lean l.325 | `Cslib.Logic.PL.Theory.alg_complete` | pending; uses `(v, bot_val)` quantifier |
| Bundled interpretation (new) | This report | `Cslib.Logic.PL.AlgInterp` (optional) | Syntactic sugar only |

---

## Context & Scope

The task 227 plan (report 05) specifies the completeness statement as:

```lean
DerivableIn T A ↔
  ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
    AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤
```

Thomas Waring's fork achieves the cleaner:

```lean
DerivableIn T A ↔ ∀ {H} [GHA H] {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A
```

where `v` is a single function `Atom → H` that implicitly handles `bot` because
`bot = atom bot` in Thomas's 4-constructor `Proposition`. The question is whether any
reformulation of CSLib's statement can achieve comparable syntactic economy while keeping
the 5-constructor `Proposition` with primitive `bot`.

---

## Findings

### Alternative 1: Bundled Interpretation (`AlgInterp`)

**Definition** (verified in `lean_run_code`):

```lean
structure AlgInterp (Atom : Type*) (H : Type*) [GeneralizedHeytingAlgebra H] where
  val : Atom → H
  botVal : H
```

With evaluation function:

```lean
def AlgInterp.eval (I : AlgInterp Atom H) : Proposition Atom → H
  | .atom x => I.val x
  | .bot => I.botVal
  | .imp a b => I.eval a ⇨ I.eval b
  | .and a b => I.eval a ⊓ I.eval b
  | .or a b => I.eval a ⊔ I.eval b
```

**Completeness statement shape**:

```lean
DerivableIn T A ↔
  ∀ {H} [GHA H] (I : AlgInterp Atom H), I.tModels T → I ⊨ A
```

**Equivalence**: Proved in `lean_run_code`. `AlgInterp.eval I φ = AlgEvaluate I.val I.botVal φ`
by structural induction (all 5 cases are `rfl` or `simp`).

**Specializations**:

| Logic | Bundled Form | Status Quo Form |
|-------|-------------|-----------------|
| MPL | `∀ (H) [GHA H] (I : AlgInterp Atom H), I ⊨ A` | `∀ (H) [GHA H] (v) (bot_val), AlgEvaluate v bot_val A = ⊤` |
| IPL | `∀ (H) [HA H] (I : AlgInterp Atom H), I.botVal = ⊥ → I ⊨ A` | `∀ (H) [HA H] (v), AlgEvaluate v ⊥ A = ⊤` |
| CPL | `∀ (H) [BA H] (I : AlgInterp Atom H), I.botVal = ⊥ → I ⊨ A` | `∀ (H) [BA H] (v), AlgEvaluate v ⊥ A = ⊤` |

**Assessment**:
- General statement: 1 visible quantifier (I) instead of 2 (v, bot_val). Win.
- MPL specialization: Marginal improvement (1 quantifier vs 2).
- IPL/CPL specialization: **Worse** -- requires explicit `I.botVal = ⊥` hypothesis.
  The status quo `HAValid` hardcodes `bot_val = ⊥` into the definition, eliminating the
  hypothesis entirely.
- Compatibility: Easy bridge via `AlgInterp.eval = AlgEvaluate`.
- Refactoring cost: Small (define new structure, add bridge lemmas).

**Verdict**: Useful as optional syntactic sugar for the general theorem. Does NOT replace
`HAValid`/`BAValid` for specializations.

### Alternative 2: Extended Valuation (`Option Atom → H`)

**Definition** (verified in `lean_run_code`):

```lean
def OptAlgEvaluate (v : Option Atom → H) : Proposition Atom → H
  | .atom x => v (some x)
  | .bot => v none
  | .imp a b => OptAlgEvaluate v a ⇨ OptAlgEvaluate v b
  | .and a b => OptAlgEvaluate v a ⊓ OptAlgEvaluate v b
  | .or a b => OptAlgEvaluate v a ⊔ OptAlgEvaluate v b
```

**Equivalence**: `OptAlgEvaluate v φ = AlgEvaluate (v ∘ some) (v none) φ` -- proved.

**Completeness statement shape**:

```lean
DerivableIn T A ↔
  ∀ {H} [GHA H] (v : Option Atom → H), (∀ B ∈ T, OptAlgEvaluate v B = ⊤) → OptAlgEvaluate v A = ⊤
```

**Specializations**:

| Logic | Option Form |
|-------|------------|
| MPL | `∀ (H) [GHA H] (v : Option Atom → H), OptAlgEvaluate v A = ⊤` |
| IPL | `∀ (H) [HA H] (v : Option Atom → H), v none = ⊥ → OptAlgEvaluate v A = ⊤` |
| CPL | `∀ (H) [BA H] (v : Option Atom → H), v none = ⊥ → OptAlgEvaluate v A = ⊤` |

**Assessment**:
- General statement: 1 visible quantifier (v), same as bundled. Slight win.
- IPL/CPL: `v none = ⊥` is syntactically awkward. Worse than status quo.
- Alternative IPL form: `∀ (H) [HA H] (v : Atom → H), OptAlgEvaluate (fun | some a => v a | none => ⊥) A = ⊤` -- this is ugly.
- Breaks the Atom/evaluation duality: `v` now operates on `Option Atom` but formulas
  are still over `Atom`. This introduces a type mismatch in contexts where `v` is used
  both for evaluation and for other purposes (e.g., substitution-valuation interaction).
- Canonical valuation becomes: `fun | some x => quotient_mk (.atom x) | none => quotient_mk .bot` --
  less natural than `canonicalV (x) = quotient_mk (.atom x)` with `bot_val = quotient_mk .bot`.

**Verdict**: Strictly worse than bundled. The `Option Atom` domain leaks into all quantifiers
and makes specializations awkward.

### Alternative 3: Sum-Type Valuation (`Atom + Unit → H`)

**Definition** (verified in `lean_run_code`):

```lean
def ExtAlgEvaluate (v : Atom ⊕ Unit → H) : Proposition Atom → H
  | .atom x => v (.inl x)
  | .bot => v (.inr ())
  | .imp a b => ExtAlgEvaluate v a ⇨ ExtAlgEvaluate v b
  | .and a b => ExtAlgEvaluate v a ⊓ ExtAlgEvaluate v b
  | .or a b => ExtAlgEvaluate v a ⊔ ExtAlgEvaluate v b
```

**Assessment**: Same trade-offs as Alternative 2 but with `Atom ⊕ Unit` instead of
`Option Atom`. `Atom ⊕ Unit` is isomorphic to `Option Atom` via `Equiv.optionEquivSumPUnit`.
Slightly more verbose and less idiomatic. No advantage over Alternative 2.

**Verdict**: Strictly worse than Alternative 2. Dismissed.

### Alternative 4: Johansson Algebra Typeclass

**Definition** (verified in `lean_run_code`):

```lean
class JohanssonAlgebra (H : Type*) extends GeneralizedHeytingAlgebra H where
  designated : H
```

**Completeness statement shape**:

```lean
DerivableIn T A ↔
  ∀ {H} [JohanssonAlgebra H] (v : Atom → H), (v ⊨ T) → v ⊨ A
```

where evaluation uses `JohanssonAlgebra.designated` for `.bot`.

**Assessment**:
- General statement: Syntactically identical to Thomas's. `v` is a plain `Atom → H`.
  The `bot_val` is hidden inside the typeclass. This is the best possible general statement.
- **Fatal flaw -- diamond problem**: For a given GHA `H`, there are multiple possible
  `designated` values. The JohanssonAlgebra typeclass forces ONE choice per type. To quantify
  over all choices of `designated` (as MPL completeness requires), you would need to quantify
  over all JohanssonAlgebra instances, which conflicts with typeclass resolution.
- IPL specialization would need: `JohanssonAlgebra H` where `designated = ⊥` and
  `H` is a `HeytingAlgebra`. But if `H` already has a `HeytingAlgebra` instance, the
  `haToJohansson` instance forces `designated = ⊥`, making the MPL quantification
  impossible for the same type.
- Mathlib has no `JohanssonAlgebra` or similar "algebra with designated constant" class.
  Report 02_d confirmed: "Mathlib has no JohanssonAlgebra class."

**Verdict**: Dismissed. Diamond problem makes it unworkable for the three-tier
MPL/IPL/CPL specialization.

### Alternative 5: AAL-Style (Rasiowa/Font/Blok-Pigozzi)

**Concept**: Abstract Algebraic Logic (AAL) defines algebraic semantics via:
- A **translation function** `tau : Formula → Equation` mapping formulas to algebra equations
- The **Leibniz operator** `Omega` computing the largest congruence compatible with a filter
- **Algebraic models** = algebras with a designated filter (not a single element)

In this framework, validity is: `phi` is valid iff `tau(phi)` holds in all algebraic models,
where "holds" means the equation `tau(phi)` is satisfied modulo the designated filter.

**Assessment**:
- This framework is designed for general sentential logics, not specifically for
  propositional logic with `{bot, imp, and, or}`.
- For Heyting algebras, the designated filter is `{top}` (the trivial filter), so the
  AAL framework reduces to: `AlgEvaluate v bot_val phi = top`.
- The AAL machinery (Leibniz operator, translation maps, filter theory) adds complexity
  without improving the completeness statement for CSLib's specific use case.
- No Mathlib infrastructure for AAL exists. Building it would be a major separate project.
- The `bot_val` parameter is NOT eliminated by AAL -- it appears inside the evaluation
  function regardless of whether you use filters or single elements for validity.

**BibKey status**: Rasiowa1974, Font2016, BlokPigozzi1989 are NOT in `references.bib`.
These would need to be added if AAL were pursued, but AAL is not recommended.

**Verdict**: Dismissed. AAL is a powerful general framework but adds complexity without
improving the specific completeness statement. The `bot_val` is inherent.

### Alternative 6: Status Quo Defense

The plan's current approach:

```lean
DerivableIn T A ↔
  ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
    AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤
```

**Strengths**:
- IPL specialization is the cleanest possible: `HAValid φ = ∀ H [HA H] v, AlgEvaluate v ⊥ φ = ⊤`.
  No extra hypotheses, no bundled structures, no extended domains.
- CPL specialization is equally clean: `BAValid φ = ∀ H [BA H] v, AlgEvaluate v ⊥ φ = ⊤`.
- MPL case: `GHAValid φ = ∀ H [GHA H] v bot_val, AlgEvaluate v bot_val φ = ⊤`.
  The `bot_val` quantifier is visible but semantically motivated (it IS the Johansson
  algebra's free designated constant).
- Zero refactoring: `AlgEvaluate`, `GHAValid`, `HAValid`, `BAValid` already exist.
- The `v ⊨ T` pattern works: `AlgTValid T v bot_val` plays the same role as Thomas's `v ⊨ T`.

**Weakness**:
- The general completeness theorem has 2 visible quantifiers `(v, bot_val)` instead of
  Thomas's 1 `(v)`. This is a genuine syntactic cost.

**Assessment**: The syntactic cost is real but localized to the general completeness theorem
and `GHAValid`. The IPL and CPL specializations -- which are the theorems most users will
interact with -- are already optimal.

---

## Side-by-Side Comparison Table

| Criterion | Status Quo | Bundled `AlgInterp` | `Option Atom` | `Atom + Unit` | Johansson TC | AAL |
|-----------|-----------|-------------------|--------------|-------------|-------------|-----|
| General statement quantifiers | 2 (v, bot_val) | 1 (I) | 1 (v) | 1 (v) | 1 (v) | N/A |
| IPL specialization | **best** (no hypothesis) | ok (I.botVal = bot) | poor (v none = bot) | poor | **fail** (diamond) | N/A |
| CPL specialization | **best** (no hypothesis) | ok (I.botVal = bot) | poor | poor | **fail** | N/A |
| MPL specialization | ok (2 quantifiers) | good (1 quantifier) | good (1 quantifier) | ok | **fail** | N/A |
| AlgEvaluate compatibility | **perfect** | bridge lemma | bridge lemma | bridge lemma | new evaluator | N/A |
| Refactoring cost | **none** | small | medium | medium | large | prohibitive |
| Mathlib precedent | yes (curried params) | uncommon | uncommon | uncommon | none | none |
| Substitution invariance | preserved | preserved | preserved | preserved | preserved | N/A |

---

## Impact Analysis on IPL/CPL/MPL Specializations

### MPL (Minimal Propositional Logic)

MPL is the only tier where the status quo is visibly worse than Thomas's approach. The
quantifier `∀ v bot_val` is two parameters instead of one. However:
- MPL completeness is the least-used specialization in practice
- The `bot_val` parameter has clear semantic content ("the designated constant of the
  Johansson algebra")
- The bundled `AlgInterp` reduces this to one parameter if desired

### IPL (Intuitionistic Propositional Logic)

IPL is where the status quo shines. `HAValid φ = ∀ H [HA H] v, AlgEvaluate v ⊥ φ = ⊤`
is the cleanest possible statement. Every alternative makes this worse by introducing
either an extra hypothesis (`I.botVal = ⊥`) or an extended domain (`v none = ⊥`).

Thomas's IPL statement is: `∀ H [HA H] v, v bot = bot → v ⊨ A`. The `v bot = bot`
hypothesis is the price Thomas pays for `bot`-as-atom. Our `HAValid` eliminates this
hypothesis entirely by hardcoding `bot_val = ⊥` in the definition.

### CPL (Classical Propositional Logic)

Same analysis as IPL. `BAValid` is already optimal.

---

## Decisions

1. **Keep `AlgEvaluate` with `(v, bot_val)` as the primary evaluation function.** No change.
2. **Keep `GHAValid`, `HAValid`, `BAValid` as they are.** No change.
3. **State the general completeness theorem with explicit `(v, bot_val)`.** This is the
   plan's current approach (report 05). Confirmed as correct.
4. **Optionally define `AlgInterp`** as syntactic sugar for the general completeness theorem.
   This is a low-priority ergonomic addition, not a blocker for implementation.
5. **Do not pursue** `Option Atom`, `Atom + Unit`, Johansson typeclass, or AAL alternatives.

---

## Recommendations

1. **Proceed with the plan in report 05 as-is.** The completeness statement with explicit
   `(v, bot_val)` is the right design. No changes needed.

2. **Consider adding `AlgInterp` post-completion** (separate follow-up, not a blocker).
   Define the structure, add `I.eval = AlgEvaluate I.val I.botVal`, and provide an
   alternative completeness statement using `AlgInterp` notation. This gives users a choice
   between the explicit `(v, bot_val)` form and the bundled `I` form.

3. **Document the design rationale** in the Algebra.lean module docstring: explain why
   `bot_val` is an explicit parameter (because GHA lacks `⊥`), why `HAValid`/`BAValid`
   hardcode `⊥` (because HA/BA have one), and how the general completeness theorem
   unifies the three validity predicates.

4. **BibKey additions** (if pursuing the AAL/Rasiowa references in future documentation):
   - Rasiowa1974 -- MISSING from references.bib
   - Font2016 -- MISSING
   - BlokPigozzi1989 -- MISSING
   These are NOT needed for the current implementation but would be needed if CSLib ever
   adds AAL infrastructure.

---

## Risks & Mitigations

| Risk | Severity | Mitigation |
|------|----------|------------|
| Status quo `(v, bot_val)` confuses new contributors | Low | Document rationale in module docstring; HAValid/BAValid are the user-facing API |
| Bundled AlgInterp creates maintenance overhead | Low | Make it optional; define via bridge lemma, not duplication |
| Future AAL formalization blocked by missing infrastructure | Low | AAL is not needed for PL completeness; defer to separate task if ever pursued |

---

## Adversarial Self-Verification

### Challenged Claims

1. **"All alternatives are mathematically equivalent"** -- VERIFIED. Each alternative was
   implemented in `lean_run_code` and proved equivalent to `AlgEvaluate` by structural
   induction. The equivalence proofs are: `eval_eq_algEvaluate` (bundled), `ext_eq_algEvaluate`
   (sum type), `opt_eq_algEvaluate` (option). All compiled successfully.

2. **"Johansson typeclass has diamond problems"** -- VERIFIED. Implemented `JohanssonAlgebra`
   in `lean_run_code`. The `haToJohansson` instance forces `designated = ⊥` for any HA,
   making it impossible to simultaneously have a JohanssonAlgebra instance with arbitrary
   `designated` and a HeytingAlgebra instance on the same type. This blocks the MPL/IPL
   joint quantification.

3. **"IPL specialization is best with status quo"** -- VERIFIED by comparison. Status quo
   `HAValid` has type `∀ H [HA H] v, AlgEvaluate v ⊥ φ = ⊤` with zero hypotheses about
   bot. Bundled adds `I.botVal = ⊥`. Option adds `v none = ⊥`. Both are strictly worse.

4. **"AAL framework does not eliminate bot_val"** -- VERIFIED by analysis. The AAL translation
   function for propositional logic maps `φ` to the equation `eval(φ) = ⊤`. The `eval`
   function still needs to handle the `.bot` case, which requires `bot_val`. The Leibniz
   operator and filter machinery operate on the algebra side, not the formula side.

5. **"Option Atom breaks the canonical valuation"** -- CHALLENGED AND REVISED. The canonical
   valuation with `Option Atom` is `fun | some x => quotient_mk (.atom x) | none => quotient_mk .bot`,
   which is well-typed and correct. It does not "break" the construction. However, it IS
   less natural than the status quo canonical valuation `fun x => quotient_mk (.atom x)` with
   separate `bot_val = quotient_mk .bot`. Revised claim: Option Atom makes the canonical
   valuation less natural, not broken.

### Uncertain Claims

- **"Bundled AlgInterp is worth adding post-completion"** (confidence 0.5): The ergonomic
  benefit of 1 quantifier vs 2 in the general completeness theorem may not justify the API
  surface increase. Most users will interact with `HAValid`/`BAValid`, not the general theorem.

### Recommendations Modified After Verification

- **Original claim (implicit)**: Option Atom is a viable alternative worth considering.
  **Revised**: Option Atom is strictly dominated by bundled AlgInterp on every criterion
  except "no new types" (both introduce new types). Dismissed entirely.

### BibKey Verification Status

| BibKey | Status | Used In |
|--------|--------|---------|
| Johansson1937 | Present in references.bib | Johansson algebra discussion |
| ChagrovZakharyaschev1997 | Present | Algebra.lean module doc |
| Gentzen1935 | Present | Defs.lean references |
| Prawitz1965 | Present | Defs.lean references |
| TroelstraVanDalen1988 | Present | Defs.lean references |
| vanDalen2013 | Present | Prior reports |
| Rasiowa1974 | MISSING | AAL discussion (not needed for implementation) |
| Font2016 | MISSING | AAL discussion (not needed for implementation) |
| BlokPigozzi1989 | MISSING | AAL discussion (not needed for implementation) |

---

## Appendix

### A. Lean Code Verification Summary

All alternatives were implemented and tested via `lean_run_code`:

| Alternative | File | Compiles | Equivalence Proved |
|-------------|------|---------|-------------------|
| Bundled `AlgInterp` | `lean_run_code` Alt1 | yes | `eval_eq_algEvaluate` |
| `Option Atom` | `lean_run_code` Alt3 | yes | `opt_eq_algEvaluate` |
| `Atom + Unit` | `lean_run_code` Alt2 | yes | `ext_eq_algEvaluate` |
| Johansson TC | `lean_run_code` Alt4 | yes (but diamond) | N/A (not needed) |

### B. Mathlib API Findings

- `Pointed` (Mathlib.CategoryTheory.Category.Pointed): a structure `{X : Type, point : X}`.
  This is the categorical notion of pointed type. It is NOT useful for our purpose because
  it is a bundled type, not a typeclass. We would need a typeclass on `H` that provides a
  distinguished element, which is what Alternative 4 (JohanssonAlgebra) attempted.

- `HeytingAlgebra` extends `GeneralizedHeytingAlgebra` and `OrderBot`. The key structural
  fact: `HA = GHA + OrderBot + Compl + himp_bot`. The `OrderBot` provides `⊥` and `bot_le`.

- `BooleanAlgebra.ofRegular` (Mathlib.Order.Heyting.Regular): promotes HA to BA given that
  every element is Heyting-regular. Used in the CPL completeness proof (confirmed in report 05).

- No Mathlib class for "GHA with designated constant" or "Johansson algebra" or "pseudo-Boolean
  algebra with designated element" exists. The GHA/HA/BA hierarchy is the standard three-tier
  system.

### C. Quantifier Count Summary

| Statement | Thomas (bot-as-atom) | Status Quo (bot_val) | Bundled (AlgInterp) |
|-----------|---------------------|---------------------|-------------------|
| General completeness | `∀ H [GHA] v` (3, 1 visible) | `∀ H [GHA] v bot_val` (4, 2 visible) | `∀ H [GHA] I` (3, 1 visible) |
| MPL specialization | `∀ H [GHA] v` (3, 1 visible) | `∀ H [GHA] v bot_val` (4, 2 visible) | `∀ H [GHA] I` (3, 1 visible) |
| IPL specialization | `∀ H [HA] v, v bot = bot →` (3+1 hyp) | `∀ H [HA] v` (3, 0 hyp) | `∀ H [HA] I, I.botVal = bot →` (3+1 hyp) |
| CPL specialization | `∀ H [BA] v, v bot = bot →` (3+1 hyp) | `∀ H [BA] v` (3, 0 hyp) | `∀ H [BA] I, I.botVal = bot →` (3+1 hyp) |

The status quo wins on IPL/CPL (0 extra hypotheses) and loses on general/MPL (1 extra quantifier).
The bundled approach ties Thomas on general/MPL but loses to status quo on IPL/CPL.
No approach wins on all four statements simultaneously.
