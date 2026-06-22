# Research Report: Typeclass Split and Dual-Type Analysis

- **Task**: 261 - Review Zulip thread on propositional logic setup in CSLib
- **Started**: 2026-06-22T01:00:00Z
- **Completed**: 2026-06-22T01:30:00Z
- **Effort**: 30 minutes
- **Dependencies**: 01_team-research.md, 02_nd-vs-hilbert-analysis.md
- **Sources/Inputs**:
  - Zulip MSG 605712144 (Matthew Doty on class-based approach)
  - Zulip MSG 605341190 (Thomas Waring's compromise proposal)
  - Thomas Waring's `intuitionistic` branch (`thomaskwaring/cslib_SKI`)
  - CSLib codebase: `Defs.lean`, `NaturalDeduction/Basic.lean`, `Connectives.lean`, `FromPropositional.lean`
- **Artifacts**: This report
- **Standards**: report-format.md, status-markers.md

## Executive Summary

- CSLib's ND system is a "hybrid": `⊥` is in the syntax (`Proposition` has a `bot` constructor) but `efq` is not a primitive derivation rule (it enters via the theory parameter and `IsIntuitionistic`). Thomas Waring argues this breaks ND symmetry.
- Three typeclass-split approaches were analyzed to avoid the hybrid. **None can eliminate it without duplicating the formula type.** Lean 4's inductive type system does not support conditionally-available constructors.
- Thomas's dual-type approach (`IProposition`/`IDerivation` with translations) achieves pure ND but at the cost of duplicating the entire formula API — monad, substitution, `DecidableEq`, all evaluation functions, all bridge lemmas, and all downstream embeddings (`FromPropositional.lean` for Modal/Temporal/Bimodal).
- Matthew Doty (MSG 605712144) endorses a class-based approach but flags two concerns: ad-hoc design and difficulty proving conservative extensions.
- **Conclusion**: CSLib's current design is the better approach for a library building upward through multiple logic layers, because it avoids compounding duplication while the "hybrid" reflects a genuine logical asymmetry (`⊥` has no introduction rule in any system).

## Context & Scope

This report addresses the question: can a typeclass split avoid CSLib's hybrid ND approach? It was prompted by Zulip MSG 605712144 and builds on rounds 1-2.

## Findings

### 1. The Hybrid ND Explained

CSLib's `Derivation` has 10 constructors matching 5 connectives (intro + elim each): `andI`/`andE1`/`andE2`, `orI1`/`orI2`/`orE`, `impI`/`impE`, plus `ax` (theory axiom) and `ass` (context assumption). `⊥` is in the `Proposition` syntax but has no corresponding constructor in `Derivation`. Instead, `efq` is derived:

```lean
theorem Derivation.efq [IsIntuitionistic T] (d : Derivation T Γ ⊥) (A) :
    Derivation T Γ A :=
  impE (ax (IsIntuitionistic.efq A)) d
```

Thomas's objection: if `⊥` is a connective in the syntax, its elimination rule should be a primitive constructor for ND symmetry.

### 2. Three Typeclass-Split Options

**Option A — Split at formula level (Thomas's approach)**: Define `IProposition Atom` with primitive `bot` and `IDerivation` with 11 constructors (adds `efq`). Connect via `propEquiv : Proposition (WithBot Atom) ≃ IProposition Atom` and bidirectional derivation translations.

- Pro: Pure Gentzen-style ND — every connective has intro/elim
- Con: Duplicates the entire formula API. Every downstream module (Modal, Temporal, Bimodal `FromPropositional.lean`) depends on `Proposition` having `bot` with the mapping `| .bot => .bot`. All evaluation functions (`Evaluate`, `BoolEvaluate`, `AlgEvaluate`), the monad instance, substitution lemmas, and `DecidableEq` would need parallel versions.
- Con: `toIDerivation` is `noncomputable` (uses `Classical.choose`)
- **Not implemented in CSLib** — exists only on Thomas's fork

**Option B — Split at Derivation level**: Keep one `Proposition` type, parameterize `Derivation` so `efq` is only available when a typeclass is satisfied. But Lean 4 inductive constructors cannot be conditionally available via typeclass constraints. The alternatives collapse back to either Option A (separate `IDerivation` type) or the current design (efq gated by `IsIntuitionistic` through the theory parameter).

**Option C — Typeclass on connectives**: Define `MinimalConnectives` (without `Bot`) and `IntuitionisticConnectives` (with `Bot`). This only controls which notation/API surface is available — it does not remove the `bot` constructor from the `Proposition` inductive type, and `Derivation` still pattern-matches on it. Does not solve the hybrid at all.

### 3. Matthew Doty's Concerns (MSG 605712144)

Matthew endorses a class-based approach but flags:
1. **Ad-hoc design**: typeclass-controlled connective availability "might not be very conducive to automation"
2. **Conservative extension proofs**: if formula types differ, "IPL is conservative over MPL" requires a translation function, making conservativity a theorem about that translation rather than a subset relation on derivations

### 4. Why the Hybrid Reflects Logical Reality

The "broken symmetry" in the current ND is not a design flaw — it reflects a genuine logical asymmetry. `⊥` is unique among connectives: it has **no introduction rule** in any proof system (ND, Hilbert, or sequent calculus). Every other connective has both intro and elim rules. So the constructor-rule correspondence is 2:1 for `∧`, `∨`, `→` (intro + elim each), and 0:1 for `⊥` (no intro, elim is efq). Whether efq is primitive or derived, the asymmetry exists.

Making efq a theory axiom rather than a derivation constructor is a deliberate choice: it lets MPL (`Theory.MPL = ∅`) have no axioms beyond the 10 rules, with IPL and CPL as extensions. This is how Troelstra & Van Dalen present minimal logic.

### 5. The Duplication Cost Compounds

Thomas's dual-type approach doesn't just double `Proposition` — it doubles everything downstream:

| Component | Current (single type) | With IProposition |
|---|---|---|
| Formula type | 1 (`Proposition`) | 2 (`Proposition` + `IProposition`) |
| Monad instance | 1 | 2 |
| Substitution lemmas | 1 set | 2 sets |
| `DecidableEq` | 1 | 2 |
| Evaluation functions | 3 (`Evaluate`, `BoolEvaluate`, `AlgEvaluate`) | 6 |
| Bridge lemmas | 2 (`propEvaluateEq`, `boolEvaluateEq`) | 4 |
| `FromPropositional` embeddings | 2 (Modal, Temporal) | 4 |
| Derivation type | 1 (`Derivation`) | 2 (`Derivation` + `IDerivation`) |
| Equivalence bridge (ND↔Hilbert) | 1 | 2 |

This is a permanent maintenance multiplier, not a one-time cost.

## Decisions

- CSLib's current single-type design with theory-parameterized efq is the correct choice for a library building upward through Modal, Temporal, and Bimodal logics.
- Thomas's dual-type approach is mathematically clean but impractical for CSLib's architecture due to compounding duplication.
- No typeclass trick can avoid the hybrid without duplicating the formula type — this is a structural constraint of Lean 4's inductive type system.
- The Zulip response should explain this trade-off clearly: the hybrid reflects logical asymmetry, the duplication cost is prohibitive, but Thomas's ND symmetry point is acknowledged as a genuine design consideration.

## Recommendations

1. The Zulip response narrative arc (Phase 3 of the plan) should include a clear explanation of why the dual-type approach was evaluated and rejected — framing it as a cost/purity trade-off rather than dismissing it.
2. The neutral docstring in `NaturalDeduction/Basic.lean` should name the specific trade-off: "substitution closure and API uniformity vs. constructor-rule correspondence."
3. The response should credit Thomas's `IProposition`/`IDerivation` as a valid proof-of-concept that demonstrates the translation is possible, while explaining why CSLib opts for the single-type architecture.
4. Matthew's conservative extension concern should be acknowledged — it applies to both the dual-type and typeclass approaches.

## Appendix

### Thomas's Key Code (from `intuitionistic` branch)

```lean
-- IProposition: formula type with primitive bot
inductive IProposition (Atom : Type u) where
  | atom : Atom → IProposition Atom
  | bot : IProposition Atom
  | impl : IProposition Atom → IProposition Atom → IProposition Atom
  | and : IProposition Atom → IProposition Atom → IProposition Atom
  | or : IProposition Atom → IProposition Atom → IProposition Atom

-- Translation: Proposition (WithBot Atom) ≃ IProposition Atom
def propEquiv : Proposition (WithBot Atom) ≃ IProposition Atom

-- IDerivation: 11 constructors (10 + efq)
-- toDerivation / toIDerivation: bidirectional translation
```

### CSLib's Current Architecture

```lean
-- Single Proposition type with bot
inductive Proposition (Atom : Type u) where
  | atom | bot | imp | and | or

-- Single Derivation type, 10 constructors, no efq
-- efq derived via: impE (ax (IsIntuitionistic.efq A)) d

-- Theory parameter controls logic strength
def Theory.MPL : Theory Atom := ∅
def Theory.IPL : Theory Atom := Set.range (fun A => ⊥ → A)
```
