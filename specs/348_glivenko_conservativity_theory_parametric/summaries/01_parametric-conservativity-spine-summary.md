# Implementation Summary: Theory-Parametric Glivenko & Conservativity Spine

- **Task**: 348 — glivenko_conservativity_theory_parametric
- **Status**: Implemented
- **Phases completed**: 5/5
- **Sorry count**: 0
- **New axioms**: 0

## Deliverables

### Phase 1: L2 parametric core

**`derivable_mono`** added to `ConjImpConservative.lean` (right after `liftDerivationTree`):
```lean
theorem derivable_mono {Atom : Type u}
    {A₁ A₂ : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, A₁ ψ → A₂ ψ)
    {φ : PL.Proposition Atom} (h : Derivable A₁ φ) : Derivable A₂ φ
```
Single-line: `let ⟨d⟩ := h; ⟨liftDerivationTree h_sub d⟩`.

**`derivableIn_axiomTheory_iff_derivable`** added to `HilbertConservativeGlivenko.lean`:
```lean
theorem derivableIn_axiomTheory_iff_derivable
    {Atom : Type u} [DecidableEq Atom]
    (Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms] {φ}:
    DerivableIn (AxiomTheory Axioms) (∅ ⊢ φ) ↔ Derivable Axioms φ
```
Single-line: `hilbert_iff_nd.symm`.

### Phase 2: Theory-parametric Glivenko

**`hilbertGlivenko_theory`** added to `HilbertConservativeGlivenko.lean`:
```lean
theorem hilbertGlivenko_theory {Atom : Type u} {φ : PL.Proposition Atom}
    (A_cl A_int : PL.Proposition Atom → Prop)
    [MinimalAxioms A_cl] [MinimalAxioms A_int]
    (h_cl : ∀ ψ, Derivable A_cl ψ → BAValid.{u, u} ψ)
    (h_int : ∀ ψ, HAValid.{u, u} ψ → Derivable A_int ψ)
    (h : Derivable A_cl φ) : Derivable A_int (¬¬φ)
```
One-liner: `h_int _ (glivenko_algebraic (h_cl _ h))`.

`hilbertGlivenko` re-derived as a `hilbertGlivenko_theory` instantiation at
`(PropositionalAxiom, IntPropAxiom)` with `CPL.hilbert_alg_complete.mp` / `IPL.hilbert_alg_complete.mpr`.

**`hilbertGlivenko_strength`** added to `ConservativeChain.lean`:
```lean
theorem hilbertGlivenko_strength {Atom : Type u} {φ : PL.Proposition Atom}
    (A_cl A_int : PL.Proposition Atom → Prop)
    [MinimalAxioms A_cl] [MinimalAxioms A_int]
    (hcl : ∀ ψ, A_cl ψ → @PropositionalAxiom Atom ψ)
    (hint : ∀ ψ, @IntPropAxiom Atom ψ → A_int ψ)
    (h : Derivable A_cl φ) : Derivable A_int (¬¬φ)
```
Discharges BA-soundness and HA-completeness hypotheses via `CPL.hilbert_alg_complete.mp`
and `IPL.hilbert_alg_complete.mpr` composed with `derivable_mono`.

**Design deviation from plan**: The plan proposed `CPL ⊆ AxiomTheory A_cl` as the strength
hypothesis. The correct condition for BA-soundness is the predicate-level inclusion
`∀ ψ, A_cl ψ → PropositionalAxiom ψ`. This was documented in the impl.

### Phase 3: `conservative_via_embedding` combinator

Added to `HilbertConservativeGlivenko.lean`:
```lean
theorem conservative_via_embedding {Atom : Type*}
    {A_big A_small : PL.Proposition Atom → Prop}
    (BigValid SmallValid : PL.Proposition Atom → Prop)
    (P : PL.Proposition Atom → Bool)
    (big_complete : ∀ φ, Derivable A_big φ → BigValid φ)
    (small_complete : ∀ φ, P φ = true → SmallValid φ → Derivable A_small φ)
    (commute : ∀ φ, P φ = true → BigValid φ → SmallValid φ)
    {φ : PL.Proposition Atom} (hP : P φ = true) (h : Derivable A_big φ) :
    Derivable A_small φ
```
One-liner: `small_complete φ hP (commute φ hP (big_complete φ h))`.
`BigValid`/`SmallValid` kept opaque so instance resolution stays at the call site (per R5).

### Phase 4: Corollary recovery (regression guard)

All existing public theorem names and signatures preserved. Re-derived as instantiations:

| Theorem | File | Recovery |
|---------|------|----------|
| `derivableConjImpOfDerivableInt` | `ConjImpConservative.lean` | `derivable_mono` one-liner |
| `derivableMinOfDerivableInt` | `ConservativeChain.lean` | `derivable_mono` one-liner |
| `derivableIntOfDerivableProp` | `ConservativeChain.lean` | `derivable_mono` one-liner |
| `hilbertGlivenko` | `HilbertConservativeGlivenko.lean` | `hilbertGlivenko_theory` instantiation |
| `derivableInMplIffDerivableMin` | `HilbertConservativeGlivenko.lean` | `derivableIn_axiomTheory_iff_derivable` composition |
| `derivableInIplIffDerivableInt` | `HilbertConservativeGlivenko.lean` | `derivableIn_axiomTheory_iff_derivable` composition |
| `derivableInCplIffDerivableProp` | `HilbertConservativeGlivenko.lean` | `derivableIn_axiomTheory_iff_derivable` composition |

Deferred (original proofs kept in place per contingency rule):
- `derivableImpOfDerivableInt`, `derivableConjImpBotOfDerivableInt` — original proofs remain,
  `conservative_via_embedding` instantiations not attempted (complex commutation lemmas require
  additional scaffolding beyond this task's scope)

### Phase 5: CI gate + optional hom

`AlgEvaluate_heytingHom` was skipped: it does not pay off for the Brouwerian/free-meet completions
(those embeddings are not full Heyting-algebra homomorphisms) and the `WithBot`/Glivenko cases
are already handled by `coe_AlgEvaluate` and `eval_regular_val`. Decision recorded per plan.

**CI results for modified propositional algebra modules**:
- `lake build` on algebra subtree: **PASS**
- `lake lint` on modified files: **PASS** (no lint issues)
- `lake exe lint-style` on modified files: **PASS** (no style issues)
- `lake shake --add-public --keep-implied --keep-prefix` on modified files: **PASS**
- Zero sorries in all modified files: **CONFIRMED**
- Zero new axioms: **CONFIRMED**

**Pre-existing failures** (unrelated to task 348, confirmed by git blame):
- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` — `simp` made no progress (task 263)
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` — unsolved goals (pre-existing)
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — unknown identifier (pre-existing)
These failures prevent `lake test` and `lake exe checkInitImports` from completing on the full project,
but are confirmed to predate this task by checking `git log`.

## Files Modified

| File | Phase | Changes |
|------|-------|---------|
| `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` | 1, 4 | Added `derivable_mono`; re-derived `derivableConjImpOfDerivableInt` |
| `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` | 1, 2, 3, 4 | Added `derivableIn_axiomTheory_iff_derivable`, `hilbertGlivenko_theory`, `conservative_via_embedding`; re-derived `hilbertGlivenko` and all three ND bridges |
| `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` | 2, 4 | Added `hilbertGlivenko_strength`; re-derived `derivableMinOfDerivableInt`, `derivableIntOfDerivableProp` |

## Plan Deviations

1. **`hilbertGlivenko_strength` uses predicate-level inclusion** (not `CPL ⊆ AxiomTheory A_cl`):
   The plan proposed ND-theory subset conditions, but the correct condition for BA-soundness
   is the axiom-predicate-level condition `∀ ψ, A_cl ψ → PropositionalAxiom ψ`.

2. **Phase 4 recoveries deferred for `derivableImpOfDerivableInt` and `derivableConjImpBotOfDerivableInt`**:
   These require `conservative_via_embedding` instantiations at complex commutation lemmas.
   Per the plan contingency rule, original proofs are kept in place.

3. **Phase 5 `AlgEvaluate_heytingHom` skipped**:
   Does not pay off; Brouwerian/free-meet completions are not full Heyting-algebra homs.
   Decision documented per plan gate condition.

## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and implementing Lean 4 proof code for the parametric spine
- Running CI verification commands
- Writing this implementation summary

All Lean code was verified to compile cleanly with zero sorries and zero new axioms.
