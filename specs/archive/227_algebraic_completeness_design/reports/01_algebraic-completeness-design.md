# Research Report: Algebraic Completeness Design for Propositional Logic with Primitive ⊥

**Task**: 227 — Algebraic completeness design
**Session**: sess_1750123500_research226 (continuation)
**Date**: 2026-06-17

## 1. Problem Statement

CSLib has algebraic **soundness** for three tiers of propositional logic (MPL/IPL/CPL) via
`AlgEvaluate` with a `bot_val` parameter, but no algebraic **completeness**. The question is:
what is the most general and elegant way to achieve algebraic completeness while keeping
primitive `⊥` in the `Proposition` type?

## 2. The bot_val Parameter Is a Johansson Algebra

### 2.1 Standard Algebraic Hierarchy

The literature establishes a clean three-tier correspondence between logics and algebras:

| Logic | Algebra | ⊥ treatment | Key reference |
|-------|---------|-------------|---------------|
| **MPL** (minimal) | **Johansson algebra** (j-algebra) | Arbitrary constant — no axioms | Johansson 1937, Rasiowa 1974 |
| **IPL** (intuitionistic) | **Heyting algebra** | Bottom element: `⊥ ≤ a` ∀a | Rasiowa-Sikorski 1963 |
| **CPL** (classical) | **Boolean algebra** | Bottom + complementation | Stone 1936 |

A **Johansson algebra** is a Brouwerian algebra (= GHA in Mathlib terms) equipped with a
designated constant `⊥` that has **no axioms constraining it**. Adding the single axiom
`⊥ ≤ a` for all `a` upgrades a Johansson algebra to a Heyting algebra.

### 2.2 Current Design Maps Exactly to This

Our `AlgEvaluate [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H)` is precisely
evaluation in a Johansson algebra where `bot_val` is the designated constant:

- `GHAValid` (∀ H, ∀ v, ∀ bot_val) = validity in all Johansson algebras = MPL
- `HAValid` (∀ H : HA, ∀ v, bot_val = ⊥) = validity in all Heyting algebras = IPL
- `BAValid` (∀ H : BA, ∀ v, bot_val = ⊥) = validity in all Boolean algebras = CPL

The `bot_val` parameter is not a hack — it IS the Johansson algebra approach, unbundled.

### 2.3 Why Naive ⊥ → ⊥ Breaks MPL Completeness

In any Heyting algebra, `⊥ ⇨ a = ⊤` for all `a` (because `⊥ ≤ a` means `x ⊓ ⊥ = ⊥ ≤ a`
for all `x`, so the Heyting implication is `⊤`). If the evaluator maps proposition `⊥` to the
algebra's `⊥`, then `evaluate v (⊥ → A) = ⊤` always — making `efq` semantically valid. But
MPL does not derive `efq`. Completeness fails.

The fix: decouple proposition `⊥` from the algebra's bottom. Either:
- **Our approach**: Explicit `bot_val` parameter in a GHA (= Johansson algebra)
- **xcthulhu's approach**: No primitive `⊥`; treat it as atom via `[Bot Atom]`

Both are isomorphic. Ours is better for CSLib because primitive `⊥` is load-bearing across
20+ pattern-match sites in Modal/Temporal/Bimodal.

## 3. The JohanssonAlgebra Typeclass Question

### 3.1 Option A: Keep bot_val as Loose Parameter (Current Design)

```lean
def AlgEvaluate [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H) :
    Proposition Atom → H
```

**Pros**: Minimal, no new typeclasses, works today.
**Cons**: `bot_val` is unstructured — no algebraic identity ties it to the evaluator. Completeness
proofs need to thread `bot_val` manually.

### 3.2 Option B: Introduce JohanssonAlgebra Typeclass

```lean
class JohanssonAlgebra (H : Type*) extends GeneralizedHeytingAlgebra H where
  designated_bot : H

instance : JohanssonAlgebra H → HeytingAlgebra H where
  -- requires: designated_bot = ⊥ (i.e., designated_bot ≤ a for all a)
```

Then `AlgEvaluate` becomes:

```lean
def AlgEvaluate [JohanssonAlgebra H] (v : Atom → H) : Proposition Atom → H
  | .bot => JohanssonAlgebra.designated_bot
  | ...
```

**Pros**:
- Makes the algebraic lineage explicit (literature-standard name)
- Eliminates the loose parameter — `bot` is part of the algebra structure
- Three-tier hierarchy is typeclass-driven: `JohanssonAlgebra → HeytingAlgebra → BooleanAlgebra`
- Validity definitions become cleaner: `JValid φ := ∀ (H) [JohanssonAlgebra H] (v), AlgEvaluate v φ = ⊤`
- Completeness proofs are more natural: the Lindenbaum algebra IS a JohanssonAlgebra

**Cons**:
- New typeclass not in Mathlib — potential maintenance burden
- May be over-engineering if algebraic completeness is far off
- `HeytingAlgebra` doesn't extend `JohanssonAlgebra` in Mathlib, so the subclass relationship
  needs a manual instance (straightforward: `designated_bot := ⊥`)

### 3.3 Option C: Bundled Algebra (Rasiowa Style)

```lean
structure JAlgebra where
  carrier : Type*
  [gha : GeneralizedHeytingAlgebra carrier]
  bot_val : carrier
```

**Pros**: No typeclass pollution. Self-contained.
**Cons**: Less ergonomic than typeclass approach. Harder to compose with Mathlib's hierarchy.

### 3.4 Recommendation

**Short term (upstream PR)**: Keep Option A (loose `bot_val`). Add docstring references to
Johansson algebras. This is sufficient for soundness and keeps the PR small.

**Medium term (algebraic completeness)**: Introduce Option B (`JohanssonAlgebra` typeclass)
when building the completeness proofs. The Lindenbaum algebra naturally instantiates it, and
the typeclass hierarchy makes the three-tier completeness statements clean.

**The typeclass is small** (~5 lines) and the instance for `HeytingAlgebra` is trivial:

```lean
instance [HeytingAlgebra H] : JohanssonAlgebra H where
  designated_bot := ⊥
```

## 4. Adapting xcthulhu's Completeness to Primitive ⊥

### 4.1 xcthulhu's Architecture

xcthulhu's `Heyting.lean` (~400 lines) provides:

| Component | Lines | Purpose |
|-----------|-------|---------|
| `Valuation.interp` | ~15 | Evaluation (4 cases, no bot) |
| Soundness (`Derivation.sound'`) | ~15 | By induction on derivation |
| `propGeneralizedHeyting` | ~80 | GHA instance on Lindenbaum quotient |
| `propHeyting` / `propBoolean` | ~40 | HA/BA instances (with efq/dne) |
| `canonicalV` / `canonicalVDM` | ~40 | Canonical valuations + specs |
| `Theory.complete` | ~20 | Main completeness theorem |
| `MPL.complete` / `IPL.complete` | ~30 | Tier-specific corollaries |

Dependencies:
- `DedekindMacneille.lean` (~418 lines) — order-theoretic completion
- `ForMathlib/Order/Heyting/Hom.lean` — Heyting algebra homomorphism lemmas

### 4.2 What Changes with Primitive ⊥

**Almost nothing.** The adaptation is ~15 lines:

1. **`Valuation.interp` → `AlgEvaluate`**: Add `| .bot => bot_val` case. (~1 line)

2. **`canonicalV_spec`**: Add `| .bot => simp [AlgEvaluate]` case. (~2 lines)

3. **`canonicalVDM_spec`**: Add `| .bot => ...` case lifting through D-M embedding. (~3 lines)

4. **`propBot`**: Simplifies — `bot := ⟦.bot⟧` instead of `⟦.atom ⊥⟧`. No `[Bot Atom]` needed.

5. **Soundness proof**: Unchanged — works by induction on derivation trees, not propositions.

6. **GHA/HA/BA instances**: Unchanged — defined via `Quotient.lift₂` on connective operations.

7. **Completeness theorem**: Unchanged in structure. The canonical `bot_val = ⟦.bot⟧` gives:
   - For MPL: `⟦.bot⟧` is NOT `⊥` of the GHA (no efq → no `⟦.bot⟧ ≤ ⟦A⟧`)
   - For IPL: `⟦.bot⟧ = ⊥` of the HA (efq gives `⟦.bot⟧ ≤ ⟦A⟧` for all A)

### 4.3 Dedekind-MacNeille Completion

Still needed. The Lindenbaum algebra for MPL is only a GHA. The completeness theorem for MPL
is stated as "valid in all HeytingAlgebras (with unrestricted bot_val)" — D-M completion
promotes GHA → complete lattice → HA. The completion is purely order-theoretic and unchanged
by adding a `.bot` constructor.

Note: xcthulhu's `DedekindMacneille.lean` (418 lines) would need to be ported. It imports
from `Cslib.ForMathlib.Order.Heyting.Hom` which would also need porting. Check whether
Mathlib has gained any of this since xcthulhu wrote it.

## 5. Completeness Results to Prove

### 5.1 Target Theorems

```lean
-- MPL: derivable iff valid in all HAs with unrestricted bot_val
theorem MPL.algebraic_complete :
    DerivableIn MPL A ↔
    ∀ (H : Type*) [HeytingAlgebra H] (v : Atom → H) (bot_val : H),
      AlgEvaluate v bot_val A = ⊤

-- IPL: derivable iff valid in all HAs with bot_val = ⊥
theorem IPL.algebraic_complete :
    DerivableIn IPL A ↔
    ∀ (H : Type*) [HeytingAlgebra H] (v : Atom → H),
      AlgEvaluate v ⊥ A = ⊤

-- CPL: derivable iff valid in all BAs with bot_val = ⊥
theorem CPL.algebraic_complete :
    DerivableIn CPL A ↔
    ∀ (H : Type*) [BooleanAlgebra H] (v : Atom → H),
      AlgEvaluate v ⊥ A = ⊤

-- General: for any theory T
theorem Theory.algebraic_complete :
    DerivableIn T A ↔
    ∀ (H : Type*) [HeytingAlgebra H] (v : Atom → H) (bot_val : H),
      (∀ B ∈ T, AlgEvaluate v bot_val B = ⊤) → AlgEvaluate v bot_val A = ⊤
```

### 5.2 Proof Architecture

```
Proposition Atom
    |
    | quotient by ProvEquiv (derivability equivalence)
    v
Lindenbaum Algebra (Quotient T.propositionSetoid)
    |
    | instantiate GeneralizedHeytingAlgebra (propGeneralizedHeyting)
    | instantiate HeytingAlgebra when T ⊇ IPL (propHeyting)
    | instantiate BooleanAlgebra when T ⊇ CPL (propBoolean)
    |
    | canonical valuation: canonicalV(x) = ⟦.atom x⟧, bot_val = ⟦.bot⟧
    |
    | truth lemma: AlgEvaluate canonicalV ⟦.bot⟧ φ = ⟦φ⟧
    v
Completeness: ⟦A⟧ = ⊤ iff DerivableIn T A
    |
    | (for MPL: need HA, so apply Dedekind-MacNeille completion)
    v
Theory.algebraic_complete
```

### 5.3 Dependencies to Port

| File | Source | Lines | Status |
|------|--------|-------|--------|
| `DedekindMacneille.lean` | xcthulhu | ~418 | Needs porting; check Mathlib for overlap |
| `ForMathlib/Order/Heyting/Hom.lean` | xcthulhu | ~? | Check if Mathlib now has this |
| `Heyting.lean` (completeness) | xcthulhu | ~400 | Adapt with ~15 lines changed |

## 6. Existing Algebraic Machinery in BimodalLogic

The `~/Projects/BimodalLogic/Metalogic/Algebraic/` directory (4,034 lines, 3 sorries — none
in core propositional/Boolean machinery) contains:

| File | Lines | Relevance |
|------|-------|-----------|
| `LindenbaumQuotient.lean` | 440 | Quotient type + lifted operations — **directly reusable pattern** |
| `BooleanStructure.lean` | 447 | `BooleanAlgebra` on Lindenbaum — **CPL completeness ready** |
| `UltrafilterMCS.lean` | 1053 | Ultrafilter-MCS bijection — classical completeness |
| `AlgebraicCompleteness.lean` | 191 | Truth lemma + completeness theorem |

This provides the **CPL path**. For IPL/MPL, xcthulhu's approach (GHA + D-M completion) is
needed since BimodalLogic only has BooleanAlgebra.

## 7. Relationship to Kripke Completeness

### 7.1 Current Kripke Results

All three tiers have Kripke strong completeness:
- `Metalogic/MinStrongCompleteness.lean` — MPL via arbitrary `botForces`
- `Metalogic/IntStrongCompleteness.lean` — IPL via `botForces = fun _ => False`
- `Metalogic/StrongCompleteness.lean` — CPL via Prop-valued `Tautology`

### 7.2 botForces ↔ bot_val Correspondence

The `botForces` parameter in Kripke semantics is the relational-semantics version of `bot_val`
in algebraic semantics:

| Semantics | MPL (minimal) | IPL (intuitionistic) |
|-----------|---------------|---------------------|
| Kripke | `botForces` arbitrary upward-closed | `botForces = fun _ => False` |
| Algebraic | `bot_val` arbitrary | `bot_val = ⊥` |

Both decouple proposition `⊥` from "true falsity" to avoid forcing efq.

### 7.3 Conservative Extension

xcthulhu notes that algebraic completeness w.r.t. HeytingAlgebra (with `bot_val = ⊥`) normally
establishes that IPL is a conservative extension of MPL — anything valid in all HAs with
`bot_val = ⊥` that doesn't mention `⊥` is also valid with arbitrary `bot_val`. This is a
natural corollary of the completeness results and would be a valuable theorem to include.

## 8. Implementation Plan

### Phase 1: Docstring Update (Small, Immediate)
- Update `Algebra.lean` docstrings to reference Johansson algebras
- Add citations: Johansson 1937, Rasiowa 1974, Citkin 2021
- Include in task 226 upstream PR

### Phase 2: Dependencies (Medium)
- Port `DedekindMacneille.lean` from xcthulhu — check Mathlib overlap first
- Port `ForMathlib/Order/Heyting/Hom.lean` — check if Mathlib has gained this
- These can be a separate PR or ForMathlib contribution

### Phase 3: Lindenbaum Algebra (Large)
- Adapt xcthulhu's `propGeneralizedHeyting` / `propHeyting` / `propBoolean`
- Add `.bot` case to canonical valuation specs (~15 lines)
- Prove truth lemma: `AlgEvaluate canonicalV ⟦.bot⟧ φ = ⟦φ⟧`

### Phase 4: Completeness Theorems
- `Theory.algebraic_complete` (general)
- `MPL.algebraic_complete`, `IPL.algebraic_complete`, `CPL.algebraic_complete`

### Phase 5: JohanssonAlgebra Typeclass (Optional, Clean)
- Introduce `JohanssonAlgebra` if completeness proofs benefit from it
- Refactor `AlgEvaluate` to use the typeclass
- Establish `HeytingAlgebra → JohanssonAlgebra` instance

### Phase 6: Conservative Extension
- Prove IPL is conservative over MPL for ⊥-free formulas
- Corollary of algebraic completeness

## 9. Key References

- Johansson, I. (1937). "Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus."
  *Compositio Mathematica*, 4, 119–136.
- Rasiowa, H. (1974). *An Algebraic Approach to Non-Classical Logics.* North-Holland.
- Rasiowa, H. & Sikorski, R. (1963). *The Mathematics of Metamathematics.* PWN.
- Citkin, A. (2021). "On Finitely-Generated Johansson Algebras." BLAST 2021.
- Chagrov, A. & Zakharyaschev, M. (1997). *Modal Logic.* Oxford University Press.
- xcthulhu (Thomas Waring). CSLib branch: `488309e3...` — Heyting.lean, DedekindMacneille.lean.
- Trufaş, L. (2024). "Formalizing Intuitionistic Propositional Logic in Lean." arXiv:2410.23765.

## 10. Summary

The `bot_val` parameter in `AlgEvaluate` is the standard Johansson algebra approach to handling
primitive `⊥` in minimal logic. Adapting xcthulhu's completeness proofs requires ~15 lines of
changes. The main porting effort is `DedekindMacneille.lean` (~418 lines) and checking Mathlib
for overlap. A `JohanssonAlgebra` typeclass is a clean long-term option but not needed
immediately. The recommended path: keep current design for soundness PR, introduce the
typeclass when building completeness proofs.
