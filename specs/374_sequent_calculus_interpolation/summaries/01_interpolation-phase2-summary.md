# Task 374 Phase 2 Summary: LK Interpolation Mechanical Cases

## Status

Green build with 5 intentional `sorry` stubs for Phase 3.

## What Was Done

Repaired `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` from RED
(multiple build errors) to GREEN (0 errors, 5 deferred `sorry`).

## Errors Fixed

### Binder arity errors (weakL, weakR)
`| weakL A _ d' ih =>` (4 names, 3 expected) replaced with `| @weakL Γ Δ A d' ih =>`.
Same for `weakR`. Using `@` pattern syntax binds the implicit `{Γ Δ}` constructor arguments
so they can be referenced in the proof body.

### Invalid `.seq` field projection
`d'.seq.ant` and `d'.seq.suc` are invalid: `LKProof` is an indexed inductive type, not a
structure, so recursive sub-proofs have no `.seq` projection. After using `@weakL Γ Δ A d' ih`,
the implicit `Γ` and `Δ` are directly available and were substituted throughout.

### Rewrite pattern-not-found (botL, andL, orR)
After induction, `hant` has type `(Γ ⊢ₛ Δ).ant = Γ₁ ∪ Γ₂` (the projection form), not
syntactically `Γ = Γ₁ ∪ Γ₂`. `rw [hant]` fails because Lean's `rw` is syntactic.
Fix: `have hant' : Γ = Γ₁ ∪ Γ₂ := hant` exploits definitional equality to restate the
hypothesis in a form that `rw` can use.

### Cover direction mismatch (weakL, weakR IH calls)
The IH expects `seq.ant = Γ₁' ∪ Γ₂'` but `hcover` was defined as `Γ₁' ∪ Γ₂' = seq.ant`.
Fix: pass `hcover.symm` to the IH.

### Cover proofs for andL, orR sub-cases
Replaced `d'.seq.ant` / `d'.seq.suc` references with `Γ` / `Δ` (now in scope via `@` pattern).
Cover equality proved via `rw [hant'/hsuc']; ext x; simp only [Finset.mem_insert,
Finset.mem_union]; tauto` to avoid timeout from using `hant'` inside `simp only`.

### `hAB_vars.trans Finset.subset_union_left` direction error (andL, orR)
`hAB_vars : A.vars ∪ B.vars ⊆ Γ₁.vars` and `Finset.subset_union_left : A.vars ⊆ A.vars ∪ B.vars`.
The composition must be `Finset.subset_union_left.trans hAB_vars`, not `hAB_vars.trans ...`.

### andL/Γ₂ right half-derivation (andL rule application)
`d_right : LKProof (insert I (insert A (insert B Γ₂)) ⊢ₛ Δ₂)` but `andL` needs the antecedent
as `insert A (insert B (insert I Γ₂))`. Added `hperm` and `d_right.mono hperm (Finset.Subset.refl _)`.

### orR/Δ₂ right half-derivation (orR rule application)  
`d_right : LKProof (insert I Γ₂ ⊢ₛ insert A (insert B Δ₂))`. `LKProof.orR A B hAB₂ d_right`
applies directly (no `mono` needed). Removed incorrect `hperm`-based mono call.

### Explicit calc wildcards (timeout fix)
`calc I.vars ⊆ _ ∩ (Γ₂ ∪ (_ ∪ Δ₂)).vars` with two wildcards caused expensive `whnf`
unification timeout. Replaced with fully explicit `(Γ₁ ∪ Δ₁).vars ∩ (insert A (insert B Γ₂) ∪ Δ₂).vars`.

## Remaining Sorries (5)

| Line | Case | Notes |
|------|------|-------|
| 268  | `ax` | Four sub-cases by (A ∈ Γ₁?, A ∈ Δ₁?) — interpolant selection |
| 272  | `andR` | Two-premise; combine interpolants via ∨ |
| 276  | `orL` | Two-premise dual to andR |
| 280  | `impL` | Two-premise; most intricate |
| 284  | `impR` | One-premise; reuse interpolant, reapply rule |
