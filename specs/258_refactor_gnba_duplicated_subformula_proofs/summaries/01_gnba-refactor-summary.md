# Implementation Summary: Refactor Duplicated Proof Patterns in GNBA.lean

- **Task**: 258
- **Status**: [COMPLETED]
- **File Modified**: `Cslib/Logics/LTL/Semantics/GNBA.lean`
- **Net Line Reduction**: 87 lines (126 deletions, 39 insertions)

## What Was Done

### Phase 1: Introduce `Formula.subformulas_trans` and replace Group 1 lemmas

Added a single `Formula.subformulas_trans` lemma that proves subformula membership is
transitive: if `χ ∈ subformulas ψ` and `ψ ∈ subformulas φ`, then `χ ∈ subformulas φ`.

The proof is a clean 20-line induction on `φ` using `simp only` to unfold `subformulas`
and `rcases` to handle each constructor. Base cases (`atom`, `bot`) use `subst` after
simplifying `h2 : ψ ∈ {φ}` to `ψ = φ`.

This replaced four 20-25 line inductive proofs:
- `subformulas_untl_left` -- now a 2-line wrapper using `Set.mem_union_left _ (Set.mem_union_right _ (Formula.self_mem_subformulas _))`
- `subformulas_untl_right` -- now a 2-line wrapper using `Set.mem_union_right _ (Formula.self_mem_subformulas _)`
- `subformulas_imp_left` -- same structure as `untl_left`
- `subformulas_imp_right` -- same structure as `untl_right`

Note: The research report suggested `by simp [Formula.subformulas]` for the wrappers, but
the full `lake build` rejected this (the LSP accepted it, but the compiler did not close the
goal). Explicit set-membership terms were used instead.

Also fixed a `flexible` linter warning in `subformulas_trans` itself: the base cases used
`simp [Formula.subformulas] at h2` (which is flexible because it modifies `h2`). Changed
to `simp only [Formula.subformulas, Set.mem_singleton_iff] at h2`.

### Phase 2: Replace `subformulas_next_sub` and remove dead code

Converted `subformulas_next_sub` (22-line induction) to a one-liner:
```lean
Formula.subformulas_trans (Set.mem_union_right _ (Formula.self_mem_subformulas _)) h
```

Removed two dead-code lemmas that were never called downstream:
- `imp_left_mem_closure` (9 lines)
- `imp_right_mem_closure` (8 lines)

Confirmed zero callers via `grep` before deletion.

### Phase 3: CI Verification

All CI checks passed:
- `lake build Cslib.Logics.LTL.Semantics.GNBA` -- success
- `lake exe checkInitImports` -- success (no output)
- `lake exe lint-style` -- success (no output)
- Zero sorries in modified file
- No new axioms introduced

## Plan Deviations

- **Task 1.6 / wrapper tactic**: Plan said `by simp [Formula.subformulas]` would work for
  the one-liner wrappers (research report confirmed it). In practice, `lake build` rejected
  it with "unsolved goals" even though the LSP showed "no goals". Used explicit set-membership
  terms (`Set.mem_union_left`, `Set.mem_union_right`, `Formula.self_mem_subformulas`) instead.
  These are term-mode proofs, not tactic proofs, and are equally readable.
- **Flexible linter warning**: The research proof for `subformulas_trans` used
  `simp [Formula.subformulas] at h2` in base cases, which triggered the flexible linter.
  Changed to `simp only` with an explicit lemma set.

## Verification Results

| Check | Result |
|-------|--------|
| `lake build` (scoped) | passed |
| `lake exe checkInitImports` | passed |
| `lake exe lint-style` | passed |
| Sorry count | 0 |
| New axioms | 0 |
| Line reduction | 87 lines (target: ~80) |
