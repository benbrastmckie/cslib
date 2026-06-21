# Research Report: Refactor Duplicated Proof Patterns in GNBA.lean

**Task**: 258
**File**: `Cslib/Logics/LTL/Semantics/GNBA.lean`
**Session**: sess_1781994910_0cdf2d_258

## Summary

Two groups of near-identical inductive proofs in GNBA.lean can be unified by introducing a single `Formula.subformulas_trans` lemma (subformula transitivity). This lemma already exists for Bimodal and Temporal logics in CSLib, making it a natural addition. The refactoring replaces 5 inductive proofs with 1, and simplifies 4 closure membership lemmas from near-identical case analyses to one-liners.

## Current State

### Group 1: Subformula Downward-Closure Lemmas (lines 236-333)

Four private lemmas proving that binary constructors' children are subformulas:

| Lemma | Line | Proves |
|-------|------|--------|
| `subformulas_untl_left` | 236 | `untl ψ₁ ψ₂ ∈ subformulas φ → ψ₁ ∈ subformulas φ` |
| `subformulas_untl_right` | 261 | `untl ψ₁ ψ₂ ∈ subformulas φ → ψ₂ ∈ subformulas φ` |
| `subformulas_imp_left` | 286 | `imp ψ₁ ψ₂ ∈ subformulas φ → ψ₁ ∈ subformulas φ` |
| `subformulas_imp_right` | 311 | `imp ψ₁ ψ₂ ∈ subformulas φ → ψ₂ ∈ subformulas φ` |

Each is a 20-25 line induction on `φ` with 5 cases. The proofs are nearly identical -- they differ only in:

1. **Which constructor is the "matching" case** (`imp` branch for `imp_*` lemmas, `untl` branch for `untl_*` lemmas). The matching case uses `injEq` to extract `⟨rfl, rfl⟩`; the non-matching case dispatches with `simp at h`.
2. **Which child is the conclusion** (left vs right). This affects exactly one proof term in the `⟨rfl, rfl⟩` branch:
   - Left: `Set.mem_union_left _ (Set.mem_union_right _ (Formula.self_mem_subformulas _))`
   - Right: `Set.mem_union_right _ (Formula.self_mem_subformulas _)`

Additionally, `subformulas_next_sub` (line 712) is a fifth instance for the unary `next` constructor, following the same induction pattern.

**All five lemmas are private and only used within GNBA.lean.**

### Group 2: Closure Membership Lemmas (lines 358-396)

Four lemmas proving that closure is downward-closed for binary constructors:

| Lemma | Line | Proves | Extra hypothesis |
|-------|------|--------|-----------------|
| `untl_left_mem_closure` | 359 | `untl ψ₁ ψ₂ ∈ closure φ → ψ₁ ∈ closure φ` | none |
| `untl_right_mem_closure` | 367 | `untl ψ₁ ψ₂ ∈ closure φ → ψ₂ ∈ closure φ` | none |
| `imp_left_mem_closure` | 375 | `imp ψ₁ ψ₂ ∈ closure φ → ψ₂ ≠ bot → ψ₁ ∈ closure φ` | `hne : ψ₂ ≠ bot` |
| `imp_right_mem_closure` | 385 | `imp ψ₁ ψ₂ ∈ closure φ → ψ₂ ≠ bot → ψ₂ ∈ closure φ` | `hne : ψ₂ ≠ bot` |

All four use the same skeleton: `rcases Formula.mem_closure_cases h`, then dispatch the `subformula` case using a Group 1 lemma, and close the other two cases with `simp at heq` or `absurd`.

The `untl` pair is identical except for calling `subformulas_untl_left` vs `subformulas_untl_right`. The `imp` pair is identical except for calling `subformulas_imp_left` vs `subformulas_imp_right`.

### Additional Observation: Redundant Lemmas

`imp_left_mem_closure` (line 375) and `imp_right_mem_closure` (line 385) are **defined but never used** downstream. All callers use the stronger variants `imp_sub_left_mem_closure` (line 423) and `imp_sub_right_mem_closure` (line 433) instead, which handle the `ψ₂ = bot` case more gracefully. The Group 2 `imp_*` lemmas are dead code.

## Downstream Usage Analysis

All usages are internal to GNBA.lean. No other file references these lemmas.

### Group 1 Downstream Callers

| Lemma | Called At | By |
|-------|----------|----|
| `subformulas_untl_left` | L362 | `untl_left_mem_closure` |
| `subformulas_untl_right` | L370 | `untl_right_mem_closure` |
| `subformulas_imp_left` | L379, L426 | `imp_left_mem_closure`, `imp_sub_left_mem_closure` |
| `subformulas_imp_right` | L389, L437 | `imp_right_mem_closure`, `imp_sub_right_mem_closure` |
| `subformulas_next_sub` | L745 | `next_sub_mem_closure` |

### Group 2 Downstream Callers

| Lemma | Called At | By |
|-------|----------|----|
| `untl_left_mem_closure` | L539, L808, L1124 | `canonicalAtom_isAtom`, `canonicalAtom_gnbaTr`, `gnba_language_eq` |
| `untl_right_mem_closure` | L527, L800, L1125, L1262 | `canonicalAtom_isAtom`, `canonicalAtom_gnbaTr`, `gnba_language_eq` (x2) |
| `imp_left_mem_closure` | (never called) | dead code |
| `imp_right_mem_closure` | (never called) | dead code |

## Recommended Refactoring Strategy

### Strategy: Introduce `Formula.subformulas_trans` (Transitivity)

This is the highest-leverage refactoring. A single lemma captures the shared induction pattern:

```lean
/-- Subformula membership is transitive: if `χ` is a subformula of `ψ` and `ψ` is a
subformula of `φ`, then `χ` is a subformula of `φ`. -/
lemma Formula.subformulas_trans {χ ψ φ : Formula Atom}
    (h1 : χ ∈ Formula.subformulas ψ) (h2 : ψ ∈ Formula.subformulas φ) :
    χ ∈ Formula.subformulas φ
```

**Argument order convention**: `(h1 : χ ∈ subformulas ψ) (h2 : ψ ∈ subformulas φ)` matches the existing `Cslib.Logic.Bimodal.Formula.subformulas_trans` and `Cslib.Logic.Temporal.Formula.subformulas_trans`.

**Proof** (verified compiles):
```lean
  induction φ with
  | atom p => simp [Formula.subformulas] at h2; subst h2; exact h1
  | bot => simp [Formula.subformulas] at h2; subst h2; exact h1
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h2 ⊢
    rcases h2 with (rfl | h₁) | h₂
    · exact h1
    · exact Or.inl (Or.inr (ih₁ h₁))
    · exact Or.inr (ih₂ h₂)
  | next φ₁ ih =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h2 ⊢
    rcases h2 with rfl | h₁
    · exact h1
    · exact Or.inr (ih h₁)
  | untl φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.subformulas, Set.mem_union, Set.mem_singleton_iff] at h2 ⊢
    rcases h2 with (rfl | h₁) | h₂
    · exact h1
    · exact Or.inl (Or.inr (ih₁ h₁))
    · exact Or.inr (ih₂ h₂)
```

### Phase 1: Replace Group 1 (lines 236-333)

Replace the four private lemmas with `subformulas_trans` plus one-liner wrappers:

```lean
private lemma Formula.subformulas_untl_left {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₁ ∈ Formula.subformulas φ :=
  Formula.subformulas_trans (by simp [Formula.subformulas]) h

private lemma Formula.subformulas_untl_right {φ ψ₁ ψ₂ : Formula Atom}
    (h : Formula.untl ψ₁ ψ₂ ∈ Formula.subformulas φ) : ψ₂ ∈ Formula.subformulas φ :=
  Formula.subformulas_trans (by simp [Formula.subformulas]) h
```

(Same pattern for `subformulas_imp_left`, `subformulas_imp_right`.)

**Alternative**: Inline `subformulas_trans` at call sites and remove the wrappers entirely, since all callers just compose with `subformula_mem_closure`. This would use `Formula.subformula_mem_closure (Formula.subformulas_trans (by simp [Formula.subformulas]) hsub)` directly. But keeping the wrappers is safer for API stability.

### Phase 2: Replace `subformulas_next_sub` (line 712)

Replace with a one-liner:

```lean
private lemma Formula.subformulas_next_sub {φ ψ : Formula Atom}
    (h : Formula.next ψ ∈ Formula.subformulas φ) : ψ ∈ Formula.subformulas φ :=
  Formula.subformulas_trans (by simp [Formula.subformulas]) h
```

### Phase 3: Simplify Group 2 Closure Lemmas (lines 358-396)

The `untl_left_mem_closure` and `untl_right_mem_closure` lemmas remain structurally necessary (they bridge from closure to subformulas via `mem_closure_cases`). However, their bodies become cleaner since the Group 1 lemmas they call are now one-liners. No further simplification is needed here -- the duplication in Group 2 is minimal (3 lines each, differing only in calling `_left` vs `_right`).

### Phase 4: Remove Dead Code

`imp_left_mem_closure` (line 375) and `imp_right_mem_closure` (line 385) are never called downstream. They can be removed. The existing `imp_sub_left_mem_closure` (line 423) and `imp_sub_right_mem_closure` (line 433) serve the same purpose with better generality.

## Net Impact

| Metric | Before | After |
|--------|--------|-------|
| Inductive proofs in Group 1 | 4 (80 lines) | 1 (20 lines) + 4 one-liner wrappers (12 lines) |
| `subformulas_next_sub` | 1 (22 lines) | 1 one-liner wrapper (3 lines) |
| Dead code (Group 2 imp lemmas) | 2 (16 lines) | 0 |
| Total lines saved | ~80 lines | |
| New API surface | `Formula.subformulas_trans` (consistent with Bimodal/Temporal) | |

## Risks and Mitigations

1. **API breakage**: All affected lemmas are either `private` (Group 1, `subformulas_next_sub`) or used only within GNBA.lean (Group 2). No external callers exist. Risk: none.

2. **Proof performance**: The `by simp [Formula.subformulas]` in the one-liner wrappers should be fast since `subformulas` unfolds to a small union expression. If performance is a concern, `by exact Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_insert_iff.mpr (Or.inl rfl)))` or similar explicit terms could be used instead, but `simp` is cleaner and verified to compile.

3. **Naming convention**: Using `subformulas_trans` matches the existing `Bimodal.Formula.subformulas_trans` and `Temporal.Formula.subformulas_trans` in CSLib. The argument order `(h1 : χ ∈ subformulas ψ) (h2 : ψ ∈ subformulas φ)` matches both existing instances.

## Tactic Survey Results

The `subformulas_trans` proof was tested with the following approaches:

- **Direct induction**: Works cleanly. Each case is 2-3 lines. The `rfl` substitution in base cases is key.
- **`simp` for membership goals**: `by simp [Formula.subformulas]` successfully resolves all child-membership goals in the one-liner wrappers.
- **Conjunction approach** (proving `ψ₁ ∈ ... ∧ ψ₂ ∈ ...`): Also works but is less elegant than transitivity and doesn't generalize as cleanly.

The transitivity approach is strictly superior: it unifies all 5 lemmas (4 binary + 1 unary) into a single proof, while the conjunction approach only unifies pairs (4 -> 2 but still needs `next` separately).
