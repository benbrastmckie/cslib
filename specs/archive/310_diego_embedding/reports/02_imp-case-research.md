# Research Report: principal_le_algEvaluate imp Case Fix

- **Task**: 310 - Diego embedding theorem (stuck proof)
- **Started**: 2026-06-23T12:00:00Z
- **Completed**: 2026-06-23T13:00:00Z
- **Effort**: Hard mode (H2+H3+H4)
- **Session**: sess_1750723200_a3b1c2_310
- **Sources/Inputs**:
  - `Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean` (stuck proof at line 464)
  - `Cslib/Foundations/Order/HilbertAlgebra.lean` (HilbertAlgebra axioms)
  - `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` (coe_AlgEvaluate_impTopOnly)
  - `Cslib/Logics/Propositional/Semantics/Algebra/Hilbert.lean` (HilbertEvaluate)
  - [Rasiowa1974] Ch. V -- Hilbert algebras and deductive filters
- **Artifacts**: This report
- **Standards**: status-markers.md, artifact-management.md, report-format.md

## Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| [Rasiowa1974] | Def. V.1.1 | `HilbertAlgebra` | `class HilbertAlgebra (H : Type*)` | transcribed (task 304) |
| [Rasiowa1974] | Def. V.3.1, p.83 | `HilbertFilter` | `structure HilbertFilter (H : Type*) [HilbertAlgebra H]` | transcribed |
| [Rasiowa1974] | Thm. V.3.3, p.85 | `instGeneralizedHeytingAlgebra` | `GeneralizedHeytingAlgebra (HilbertFilter H)` | transcribed |
| [Rasiowa1974] | Def. V.3.5, p.86 | `HilbertFilter.principal` | `H -> HilbertFilter H` | transcribed |
| [Rasiowa1974] | Thm. V.3.6, p.87 | `principal_le_himp` | `principal (a ⇨ b) ≤ himpFilter (principal a) (principal b)` | transcribed |
| [Rasiowa1974] | Thm. V.3.6 (embedding) | `principal_le_algEvaluate` | `principal (HilbertEvaluate v φ) ≤ AlgEvaluate (principal ∘ v) ⊥ φ` | **stuck (imp case)** |
| [Rasiowa1974] | Thm. V.3.6 (top) | `principal_top` | `principal ⊤ = ⊥` | transcribed |
| [Rasiowa1974] | Thm. V.3.6 (inj) | `principal_injective` | `Function.Injective principal` | transcribed |
| (corollary) | -- | `hilbertEmbeddingLemma` | `HilbertEvaluate v φ = ⊤ ↔ principal (HilbertEvaluate v φ) = ⊥` | transcribed |

## Executive Summary

The stuck proof of `principal_le_algEvaluate` has a simple three-step fix. The imp case was attempting to use the induction hypothesis for the antecedent (`iha`) and the existing lemma `principal_le_himp`, but this approach is blocked by the antitonicity of `himpFilter` in its first argument. The correct proof does not need `iha` at all: it chains `principal_le_iff.mpr le_himp` (the K axiom gives `vb ≤ va ⇨ vb`), the IH for the consequent (`ihb`), and the GHA's `le_himp` property.

## Findings

### 1. Root Cause Analysis: Why the imp Case Was Stuck

The stuck proof at lines 407-465 attempted the following strategy:

1. Apply `principal_le_himp` to get `x ∈ himpFilter (principal va) (principal vb)`
2. Use the induction hypotheses `iha` and `ihb` to convert from `himpFilter (principal va) (principal vb)` to `himpFilter (Ae a) (Ae b)`

This fails because `himpFilter` is **antitone in its first argument**: if `F1 ≤ F2` then `himpFilter F2 G ≤ himpFilter F1 G`. The IH `iha` gives `principal(va) ≤ Ae(a)`, but antitonicity gives `himpFilter(Ae a)(-) ≤ himpFilter(principal va)(-)` -- the wrong direction for the chain.

While `himpFilter` is monotone in its second argument (which lets us use `ihb`), the two monotonicity directions conflict, making the transitivity chain impossible.

### 2. The Correct Proof: Three-Step calc Chain

The key insight is that we do not need `iha` or `principal_le_himp` at all. Instead, we use the K axiom of Hilbert algebras, which gives `b ≤ a ⇨ b` (this is `le_himp` in the algebra), combined with `principal_le_iff` (which reverses the order for principal filters).

The proof for the imp case is:

```lean
calc principal (HilbertEvaluate v a ⇨ HilbertEvaluate v b)
    ≤ principal (HilbertEvaluate v b) := principal_le_iff.mpr le_himp
  _ ≤ AlgEvaluate (principal ∘ v) ⊥ b := ihb hφ.2
  _ ≤ AlgEvaluate (principal ∘ v) ⊥ a ⇨ AlgEvaluate (principal ∘ v) ⊥ b := le_himp
```

Step-by-step:
1. **`principal(va ⇨ vb) ≤ principal(vb)`**: By `principal_le_iff.mpr le_himp`. The K axiom gives `vb ≤ va ⇨ vb`, and `principal_le_iff` says `principal x ≤ principal y ↔ y ≤ x`, so `vb ≤ va ⇨ vb` gives `principal(va ⇨ vb) ≤ principal(vb)`.
2. **`principal(vb) ≤ Ae(b)`**: By the induction hypothesis `ihb` applied to `hφ.2`.
3. **`Ae(b) ≤ Ae(a) ⇨ Ae(b)`**: By `le_himp` from the `GeneralizedHeytingAlgebra` instance on `HilbertFilter H`. In any GHA, `b ≤ a ⇨ b`.

This proof has been verified to compile in Lean 4 via `lean_run_code`.

### 3. Why Equality (`principal(a ⇨ b) = himpFilter(principal a)(principal b)`) Fails

The existing `principal_le_himp` only gives the ≤ direction. The reverse direction `himpFilter(principal a)(principal b) ≤ principal(a ⇨ b)` is **false in general**.

**Counterexample**: In the 2-element Hilbert algebra `{0, 1}` with `0 < 1 = ⊤`:
- `principal(0) = topFilter = {0, 1}` (everything above 0)
- `principal(1) = ⊥ = {1}` (everything above 1)
- `himpFilter(principal 0)(principal 0) = himpFilter(topFilter)(topFilter) = topFilter` (since the condition `∀ y ≥ x, True → True` is trivially satisfied for all x)
- `principal(0 ⇨ 0) = principal(1) = ⊥ = {1}`
- But `topFilter = {0, 1} ≠ {1} = ⊥`

So `himpFilter(principal 0)(principal 0) = topFilter ≰ ⊥ = principal(0 ⇨ 0)`.

This means `principal` does NOT preserve `⇨` as equality, and the approach via `coe_AlgEvaluate_impTopOnly` (which requires `f(a ⇨ b) = f(a) ⇨ f(b)` as equality) is inapplicable.

### 4. Consequences for the Diego Embedding Theorem

The fixed `principal_le_algEvaluate` gives only one direction of the full Diego result:

**Provable (with the fix):**
- `AlgEvaluate (principal ∘ v) ⊥ φ = ⊥ → HilbertEvaluate v φ = ⊤`

**Proof sketch**: If `AlgEvaluate = ⊥`, then `principal(HilbertEvaluate v φ) ≤ ⊥` by `principal_le_algEvaluate`. Since `⊥` is the bottom, `principal(eval) = ⊥`, so `eval = ⊤` by `principal_injective` and `principal_top`.

**Not provable from `principal_le_algEvaluate` alone:**
- `HilbertEvaluate v φ = ⊤ → AlgEvaluate (principal ∘ v) ⊥ φ = ⊥`

This would require the reverse inequality `AlgEvaluate ≤ principal(eval)`, which cannot be proved by the same induction (symmetric antitonicity problem).

**However**, the existing `hilbertEmbeddingLemma` already proves `HilbertEvaluate v φ = ⊤ ↔ principal(eval) = ⊥` without going through `AlgEvaluate`, so the embedding theorem as formulated in the file is already complete. The `principal_le_algEvaluate` lemma strengthens it by adding the connection to `AlgEvaluate`.

### 5. Cleanup: Remove Dead Code in the imp Case

Lines 413-465 of `DiegoEmbedding.lean` contain extensive comments documenting the failed approach. These should be replaced with the clean calc proof. The existing `sorry` at line 464 and the `Or.inl` workaround at line 464 should be removed entirely.

### 6. No Additional Helper Lemmas Needed

The fix requires only existing lemmas:
- `principal_le_iff` (already in the file, line 132)
- `le_himp` (from Mathlib's `GeneralizedHeytingAlgebra`, via `Mathlib.Order.Heyting.Basic`)
- The induction hypothesis `ihb`

No new helper lemmas are needed.

## Recommendations

### Implementation (Priority 1)

Replace lines 407-466 of `DiegoEmbedding.lean` with the clean proof:

```lean
  | imp a b iha ihb =>
    simp only [Proposition.IsImpTopOnly, Bool.and_eq_true] at hφ
    simp only [HilbertEvaluate_imp, AlgEvaluate_imp]
    calc principal (HilbertEvaluate v a ⇨ HilbertEvaluate v b)
        ≤ principal (HilbertEvaluate v b) := principal_le_iff.mpr le_himp
      _ ≤ AlgEvaluate (principal ∘ v) ⊥ b := ihb hφ.2
      _ ≤ AlgEvaluate (principal ∘ v) ⊥ a ⇨ AlgEvaluate (principal ∘ v) ⊥ b := le_himp
```

This replaces approximately 55 lines of commented-out failed attempts with 6 lines of clean proof.

### Implementation (Priority 2)

Add a corollary `diegoEmbedding_soundness` after `hilbertEmbeddingLemma`:

```lean
/-- Filter-lattice validity implies Hilbert-algebra validity. -/
theorem diegoEmbedding_soundness {Atom : Type*} {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) (φ : Proposition Atom) (hφ : φ.IsImpTopOnly = true) :
    AlgEvaluate (principal ∘ v) (⊥ : HilbertFilter H) φ = ⊥ →
    HilbertEvaluate v φ = ⊤ := by
  intro h
  have hle := principal_le_algEvaluate v φ hφ
  rw [h] at hle
  exact (hilbertEmbeddingLemma v φ hφ).mpr (le_antisymm hle bot_le)
```

### Documentation Update (Priority 3)

Update the module docstring comment at line 39-41 to reflect that `principal_le_himp` gives only a half-morphism, and that the embedding lemma uses a different strategy (the K axiom chain) rather than converting between `himpFilter` and `principal`.

## Adversarial Self-Verification

### Challenged Claims

1. **Claim: The reverse inequality `himpFilter(principal a)(principal b) ≤ principal(a ⇨ b)` is false.**
   - **Verification**: Verified with concrete counterexample in the 2-element Hilbert algebra. `himpFilter(principal 0)(principal 0) = topFilter` but `principal(0 ⇨ 0) = principal(1) = ⊥`. Since `topFilter ≠ ⊥` (and `0 ∈ topFilter` but `0 ∉ ⊥`), the inequality `topFilter ≤ ⊥` fails.
   - **Status**: Confirmed.

2. **Claim: The induction hypothesis `iha` is not needed in the proof.**
   - **Verification**: The compiled proof in `lean_run_code` uses only `ihb hφ.2` and never references `iha`. The `iha` term is still bound by the `induction` tactic but is an unused variable. Lean 4's unused variable linting may flag this with `_iha`; the implementation should use `_` or `_iha` if needed.
   - **Status**: Confirmed. (Note: may need `_` pattern to suppress lint warning.)

3. **Claim: `le_himp` from the GHA gives `Ae(b) ≤ Ae(a) ⇨ Ae(b)`.**
   - **Verification**: `le_himp` from `Mathlib.Order.Heyting.Basic` has type `a ≤ b ⇨ a`. In our application, this gives `Ae(b) ≤ Ae(a) ⇨ Ae(b)` (with `a := Ae(a)` and the implicit `a` in `le_himp`'s statement playing the role of `Ae(b)`). The naming might be confusing because Mathlib's `le_himp` says `a ≤ b ⇨ a` (K-axiom shape), not `b ≤ a ⇨ b`. Both are the same statement with different variable naming.
   - **Status**: Confirmed. Verified via `lean_run_code`.

4. **Claim: `principal_le_iff.mpr le_himp` proves `principal(va ⇨ vb) ≤ principal(vb)`.**
   - **Verification**: `principal_le_iff` says `principal x ≤ principal y ↔ y ≤ x`. Applying `.mpr` with `le_himp : vb ≤ (va ⇨ vb)` gives `principal(va ⇨ vb) ≤ principal(vb)`. Types check because `le_himp` in the Hilbert algebra gives `b ≤ a ⇨ b` (K axiom).
   - **Status**: Confirmed. Verified via `lean_run_code`.

### Reuse Check Protocol

1. **CSLib Foundations**: `principal_le_iff`, `le_himp` (Hilbert algebra K axiom), `principal_le_himp` -- all already exist and are used.
2. **Existing typeclass hierarchy**: `GeneralizedHeytingAlgebra` on `HilbertFilter H` already provides `le_himp` from the GHA.
3. **Notation typeclasses**: No new notation needed.
4. **Mathlib**: `le_himp` from `Mathlib.Order.Heyting.Basic` is the version used in the filter GHA. No additional Mathlib lemmas needed.
5. **Logics/Languages namespaces**: `AlgEvaluate_imp`, `HilbertEvaluate_imp` already exist as simp lemmas.

All 5 steps exhausted. No new abstractions needed.

### BibKey Verification

- **Rasiowa1974**: Found in `references.bib` at line 757. BibKey verified.
- **Diego1966**: NOT found in `references.bib`. Should be added for proper citation. Full citation: A. Diego, *Sobre Algebras de Hilbert*, Notas de Matematica 12, Instituto de Matematica, Universidad Nacional del Sur, Bahia Blanca, 1966.
- **Kohler1981**: NOT referenced in the current file and not needed for this fix. No BibKey verification needed.
