# Team Synthesis: Algebraic Completeness Design for Propositional Logic

**Task**: 227 — Algebraic completeness design
**Session**: sess_1750130000_research227
**Date**: 2026-06-17
**Sources**: Agent A (completeness architecture), Agent B (Mathlib API), Agent C (conservative extensions), Agent D (Thomas's approach)

---

## 1. Design Resolution: Thomas's `v ⊨ T` Style with Primitive ⊥

### The Question

Three design choices were evaluated:
1. Our current `bot_val` parameter with separate `GHAValid`/`HAValid`/`BAValid` predicates
2. Thomas's `v ⊨ T` approach with `⊥`-as-atom (`[Bot Atom]`)
3. A `JohanssonAlgebra` typeclass bundling `bot_val` into the algebra

### Resolution

**Adopt Thomas's `v ⊨ T` completeness style while keeping our 5-constructor Proposition with primitive `⊥`.**

The parametric completeness theorem becomes:

```lean
theorem Theory.alg_complete [Inhabited Atom] {A : PL.Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      (∀ B ∈ T, AlgEvaluate v bot_val B = ⊤) → AlgEvaluate v bot_val A = ⊤
```

This is formally equivalent to Thomas's statement (Agent D confirmed the formal
correspondence `bot_val ↔ v ⊥`), but keeps our Proposition type unchanged. The
`v ⊨ T` hypothesis does all the work of specialization:

- **MPL** (`T = MPL`): The hypothesis is trivially true for any `(v, bot_val)` since all
  MPL axioms are GHA-valid. It drops out, yielding: `∀ [GHA H] v bot_val, AlgEvaluate v bot_val A = ⊤`.
- **IPL** (`T = IPL`): In an HA, the hypothesis forces `bot_val ⇨ x = ⊤` for all `x`
  (from efq axioms), which is equivalent to `bot_val = ⊥`. Reduces to our `HAValid`.
- **CPL** (`T = CPL`): In a BA, same reduction plus regularity. Reduces to our `BAValid`.

### JohanssonAlgebra: Not Needed

Agent D's finding resolves the tension with Agent A: Mathlib's existing `GeneralizedHeytingAlgebra` /
`HeytingAlgebra` / `BooleanAlgebra` hierarchy exactly matches the three logic tiers. The `bot_val`
parameter serves the role that `JohanssonAlgebra.designated_bot` would, without introducing a
new typeclass. With the `v ⊨ T` framing, the parameter's role is clear — it is the interpretation
of `⊥` in the algebra, unconstrained for MPL, forced to `⊥` for IPL/CPL.

A `JohanssonAlgebra` typeclass could still be introduced later for clarity, but it is not required
for any of the planned theorems.

---

## 2. Consolidated Implementation Roadmap

### Phase 1: Dedekind-MacNeille Completion (~420 lines)

**New file**: `Cslib/ForMathlib/Order/DedekindMacNeille.lean`

Port from xcthulhu (Yijun Yuan). Pure order theory — no logic content.

| Component | Lines | Mathlib status |
|-----------|-------|---------------|
| `CompleteLattice` on `ClosureOperator.Closeds` | ~110 | Not in Mathlib |
| D-M Galois connection + closure operator | ~15 | Not in Mathlib |
| `DedekindMacNeilleCompletion` type + `CompleteLattice` | ~5 | Not in Mathlib |
| `HeytingAlgebra` on D-M completion of GHA | ~100 | Not in Mathlib |
| Order embedding `coe'` + simp lemmas (`coe_inf`, `coe_sup`, `coe_himp`) | ~100 | Not in Mathlib |
| `LinearOrder` / `CompleteLinearOrder` for linear α | ~60 | Not in Mathlib |
| Universal property | ~30 | Not in Mathlib |

**Why needed**: The Lindenbaum algebra for MPL is a GHA, not an HA. D-M completion promotes
GHA → complete HA, closing the completeness argument for the general `Theory.alg_complete`.

**Can be submitted as an independent PR** (or ForMathlib contribution).

### Phase 2: Lindenbaum Algebra (~300 lines)

**New file**: `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean`

Build the Lindenbaum quotient algebra on our Proposition type. Adapted from Thomas/xcthulhu
with an extra `.bot` case in each induction.

| Component | Lines | Notes |
|-----------|-------|-------|
| `PartialOrder` on `Quotient T.propositionSetoid` | ~40 | `⟦A⟧ ≤ ⟦B⟧ ↔ DerivableIn T ({A} ⊢ B)` |
| `Lattice` (sup via `∨`, inf via `∧`) | ~60 | Congruence from `Theory.Equiv.or_or`, `and_and` |
| `GeneralizedHeytingAlgebra` (himp via `→`) | ~50 | Key: `le_himp_iff` = deduction theorem |
| `HeytingAlgebra` (when `[IsIntuitionistic T]`) | ~40 | `bot_le` from efq; no `[Bot Atom]` needed |
| `BooleanAlgebra` (when `[IsClassical T]`) | ~40 | Via `BooleanAlgebra.ofRegular` + DNE |
| Simp lemmas (`mk_le_mk`, `mk_sup_mk`, etc.) | ~50 | Standard quotient lifting lemmas |
| Compl instance + `Nontrivial` from consistency | ~20 | For HA/BA tiers |

**CSLib advantage over xcthulhu**: Primitive `.bot` eliminates all `[Bot Atom]` requirements.
`propBot` is just `⟦.bot⟧`, always available.

**Key verification**: `⟦.bot⟧` is NOT `⊥` of the GHA for MPL (no efq ⟹ no `⟦.bot⟧ ≤ ⟦A⟧`).
For IPL, efq gives `⟦.bot⟧ = ⊥` of the HA. Confirmed by both Agents A and D.

### Phase 3: Completeness Theorems (~200 lines)

**New file**: `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean`

| Component | Lines | Notes |
|-----------|-------|-------|
| `canonicalV` + `canonicalVDM` | ~15 | Canonical valuations (Lindenbaum + D-M lifted) |
| `canonicalV_spec` | ~15 | Truth lemma: `AlgEvaluate canonicalV ⟦.bot⟧ φ = ⟦φ⟧` |
| `canonicalVDM_spec` | ~20 | D-M lifted truth lemma (uses `coe_inf`, `coe_sup`, `coe_himp`) |
| `lindenbaum_complete` | ~8 | `⟦A⟧ = ⊤ ↔ DerivableIn T A` |
| `tValid_canonicalV`, `tValid_canonicalVDM` | ~15 | Canonical valuations model T |
| `Theory.alg_complete` | ~25 | General completeness |
| `MPL.alg_complete` | ~15 | MPL specialization |
| `IPL.alg_complete` | ~15 | IPL specialization |
| `CPL.alg_complete` | ~15 | CPL specialization |
| Hilbert-level corollaries | ~20 | Via `hilbert_iff_nd_min/int/cl` |
| `AlgTValid` predicate | ~10 | `∀ B ∈ T, AlgEvaluate v bot_val B = ⊤` |

**New `.bot` case in `canonicalV_spec`**: One line — `| .bot => simp [AlgEvaluate]`.
**New `.bot` case in `canonicalVDM_spec`**: ~3 lines using `coe'`.

### Phase 4: Conservative Extension (~80 lines)

**New file**: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`

| Component | Lines | Notes |
|-----------|-------|-------|
| `Proposition.IsBotFree` predicate | ~10 | Recursive Bool or Prop predicate |
| `AlgEvaluate_botFree_independent` | ~15 | Core lemma: evaluation ignores `bot_val` for bot-free formulas |
| `HAValid_botFree_implies_arbitrary_bot` | ~10 | Semantic conservative extension |
| `ipl_conservative_over_mpl` | ~10 | Syntactic corollary (via completeness) |
| Hilbert-level corollary | ~5 | Via ND-Hilbert bridge |
| `GHAValid_implies_HAValid`, `HAValid_implies_BAValid` | ~10 | Validity subsumption (trivial) |

### Phase 5 (Optional): Kripke-Algebraic Bridge (~80 lines)

**New file**: `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean`

| Component | Lines | Notes |
|-----------|-------|-------|
| `IForces_eq_AlgEvaluate_UpperSet` | ~50 | `UpperSet W` is HA via Mathlib; structural induction |
| `MValid_implies_UpperSet_valid` | ~15 | One-direction Kripke → algebraic |
| Full equivalence (representation theorem) | deferred | Requires prime filter spectrum |

Agent C confirmed `UpperSet W` has `HeytingAlgebra` via Mathlib's
`CompletelyDistribLattice` chain.

### Phase 6 (Future): Glivenko's Theorem

Best approached after algebraic completeness is in place. Mathlib has `Heyting.Regular` and
`BooleanAlgebra.ofRegular` — the key infrastructure. Would be a novel Lean 4 formalization
(Agent C found no existing one). Algebraic proof: the double-negation map surjects onto
`Heyting.Regular H` (a BA), giving `BAValid φ ↔ HAValid (¬¬φ)`.

---

## 3. Exact Theorem Signatures (Recommended Approach)

### General Completeness

```lean
/-- Algebraic completeness: A is derivable from T iff every GHA valuation
that models T also models A. Uses Dedekind-MacNeille completion to promote
the Lindenbaum GHA to an HA. -/
theorem Theory.alg_complete [Inhabited Atom] {A : PL.Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      (∀ B ∈ T, AlgEvaluate v bot_val B = ⊤) → AlgEvaluate v bot_val A = ⊤
```

### Tier Specializations

```lean
theorem MPL.alg_complete [Inhabited Atom] {A : PL.Proposition Atom} :
    DerivableIn MPL A ↔
    ∀ {H : Type u} [HeytingAlgebra H] (v : Atom → H) (bot_val : H),
      AlgEvaluate v bot_val A = ⊤

theorem IPL.alg_complete {A : PL.Proposition Atom} :
    DerivableIn IPL A ↔
    ∀ {H : Type u} [HeytingAlgebra H] (v : Atom → H),
      AlgEvaluate v (⊥ : H) A = ⊤

theorem CPL.alg_complete {A : PL.Proposition Atom} :
    DerivableIn CPL A ↔
    ∀ {H : Type u} [BooleanAlgebra H] (v : Atom → H),
      AlgEvaluate v (⊥ : H) A = ⊤
```

### Hilbert-Level Corollaries

```lean
theorem Hilbert.MPL.alg_complete {A} :
    Derivable MinPropAxiom A ↔
    ∀ {H} [HeytingAlgebra H] (v : Atom → H) (bot_val : H),
      AlgEvaluate v bot_val A = ⊤ :=
  hilbert_iff_nd_min.trans MPL.alg_complete
```

### Conservative Extension

```lean
theorem AlgEvaluate_botFree_independent
    [GeneralizedHeytingAlgebra H] (v : Atom → H) (b1 b2 : H)
    {φ : PL.Proposition Atom} (hbf : φ.IsBotFree) :
    AlgEvaluate v b1 φ = AlgEvaluate v b2 φ

theorem ipl_conservative_over_mpl {A : PL.Proposition Atom}
    (hbf : A.IsBotFree) :
    DerivableIn IPL A → DerivableIn MPL A
```

---

## 4. Infrastructure Porting Summary

| Source | Component | Lines | Required for | Can defer? |
|--------|-----------|-------|-------------|------------|
| xcthulhu | `DedekindMacneille.lean` | ~420 | Phase 1 (MPL completeness) | No |
| xcthulhu | `ForMathlib/Order/Heyting/Hom.lean` (GeneralizedHeytingHom) | ~200 | Theory extensions / functoriality | **Yes** — not used by core completeness |
| xcthulhu | `ForMathlib/Order/PrimeSeparator.lean` | ~200 | Prime ideal separation | **Yes** — only for Kripke-algebraic bridge |
| xcthulhu | `Heyting.lean` (completeness) | ~400 | Phase 2-3 (adapt, not port wholesale) | No |

**Minimal porting**: Only `DedekindMacneille.lean` (~420 lines) must be ported verbatim.
The Lindenbaum and completeness code is adapted (not copied), since our Proposition type
differs. `GeneralizedHeytingHom` and `PrimeSeparator` are deferrable.

---

## 5. Dependency Graph

```
Mathlib.Order.Heyting.Basic
Mathlib.Order.Closure
         |
ForMathlib/Order/DedekindMacNeille.lean (NEW ~420, Phase 1)
         |
         |    NaturalDeduction/Basic.lean (EXISTS)
         |              |
         |    Semantics/Algebra.lean (EXISTS)
         |              |
         |    Semantics/Algebra/Soundness.lean (EXISTS)
         |             /
         |            /
Semantics/Algebra/Lindenbaum.lean (NEW ~300, Phase 2)
         |
Semantics/Algebra/Completeness.lean (NEW ~200, Phase 3)
         |
Semantics/Algebra/Conservative.lean (NEW ~80, Phase 4)
```

**Total new code**: ~1000 lines across 4 files.
**Existing modifications**: ~5 lines (docstring updates to Algebra.lean).

---

## 6. Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| D-M completion port has universe issues | Low | xcthulhu's code is universe-polymorphic |
| `[Inhabited Atom]` requirement threading | Medium | CSLib's `derivableIn_top` is unconditional (better than xcthulhu) |
| HA instance needs `efqOfIPLHyp` adaptation | Medium | CSLib has `IsIntuitionistic.efq` — direct path |
| BA instance needs `dneOfCPL` adaptation | Medium | Use `BooleanAlgebra.ofRegular` (proven strategy) |
| D-M completion not in Mathlib, maintenance burden | Low | Self-contained; candidate for Mathlib PR |
| Existing soundness proofs need refactoring | None | Soundness is independent of completeness files |

---

## 7. Summary Recommendation

1. **Keep primitive `⊥`** — 257 downstream pattern-match sites make removal infeasible
2. **Adopt Thomas's `v ⊨ T` parametric completeness style** — one theorem, not three predicates
3. **Do not introduce JohanssonAlgebra** — GHA/HA/BA hierarchy is sufficient
4. **Port D-M completion from xcthulhu** as Phase 1 (independent, reviewable)
5. **Build Lindenbaum + completeness** in Phases 2-3, adapting Thomas's proof strategy
6. **Conservative extension** is a clean corollary in Phase 4
7. **Glivenko and Kripke-algebraic bridge** are future work, not blockers
