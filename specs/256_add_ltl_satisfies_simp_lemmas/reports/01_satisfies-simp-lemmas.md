# Research Report: Add @[simp] Unfold Lemmas for LTL.Satisfies

**Task**: 256
**Session**: sess_1781994910_0cdf2d_256

## Summary

The LTL `Satisfies` definition at `Cslib/Logics/LTL/Semantics/Satisfies.lean:52` is a bare
`def` with zero `@[simp]` lemmas. The analogous Temporal `Satisfies` at
`Cslib/Logics/Temporal/Semantics/Satisfies.lean:57` has four `@[simp]` constructor lemmas
(`atom_iff`, `imp_iff`, `untl_iff`, `snce_iff`) plus non-simp derived lemmas (`bot_false`,
`neg_iff`, `top_true`, `someFuture_iff`, `allFuture_iff`, etc.). Downstream LTL files
(GNBA.lean, OmegaRegular.lean) currently use `simp only [Satisfies]` or `simp [Satisfies]`
to unfold the definition directly, which is fragile and verbose.

## Current State

### LTL Satisfies Definition (Satisfies.lean:52-57)

```lean
def Satisfies (v : Atom → State → Prop) (w : ωSequence State) : Formula Atom → Prop
  | .atom p => v p w.head
  | .bot => False
  | .imp φ ψ => Satisfies v w φ → Satisfies v w ψ
  | .next φ => Satisfies v w.tail φ
  | .untl φ ψ => ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ
```

### LTL Formula Constructors (Formula.lean:68-79)

Five primitive constructors: `atom`, `bot`, `imp`, `next`, `untl`.

### LTL Derived Operators (Formula.lean:81-111)

All defined as `abbrev`:
- `neg φ := imp φ bot`
- `top := imp bot bot`
- `or φ₁ φ₂ := imp (imp φ₁ bot) φ₂`
- `and φ₁ φ₂ := imp (imp φ₁ (imp φ₂ bot)) bot`
- `iff φ₁ φ₂ := and (imp φ₁ φ₂) (imp φ₂ φ₁)`
- `someFuture φ := untl top φ`
- `allFuture φ := neg (someFuture (neg φ))`
- `leadsto p q := allFuture (imp p (someFuture q))`

### Temporal Satisfies Pattern (reference)

The Temporal module has this structure inside `namespace Satisfies`:

| Declaration | `@[simp]`? | Proof | Notes |
|-------------|-----------|-------|-------|
| `bot_false` | No | `id` | `¬ Satisfies M t .bot` |
| `atom_iff` | **Yes** | `Iff.rfl` | `↔ M.valuation t p` |
| `imp_iff` | **Yes** | `Iff.rfl` | `↔ (Satisfies M t φ → Satisfies M t ψ)` |
| `untl_iff` | **Yes** | `Iff.rfl` | `↔ ∃ s, t < s ∧ ...` |
| `snce_iff` | **Yes** | `Iff.rfl` | `↔ ∃ s, s < t ∧ ...` (no LTL analogue) |
| `neg_iff` | No | `simp only [Satisfies]` | Derived |
| `top_true` | No | `intro h; exact h` | Derived |
| `someFuture_iff` | No | `simp only [Satisfies]; ...` | Derived |
| `allFuture_iff` | No | `simp only [Satisfies]; ...` | Derived |

### Downstream Usage of `Satisfies` in LTL

Across GNBA.lean and OmegaRegular.lean, there are **14 occurrences** of
`simp only [Satisfies, ...]` or `simp [Satisfies]`. These all unfold the definition
directly. With proper `@[simp]` lemmas, many of these would become just `simp` or
`simp only [Satisfies.atom_iff, Satisfies.untl_iff]` etc.

Key patterns found:
- `simp only [Satisfies, ωSequence.head_drop]` (atom case in GNBA.lean:769, 1065)
- `simp only [Satisfies]` (bot case in GNBA.lean:1070)
- `simp only [Satisfies]` (imp case in GNBA.lean:1074)
- `simp only [Satisfies, ωSequence.tail_drop']` (next case in GNBA.lean:783, 787, 1111)
- `simp only [Satisfies, ωSequence.drop_drop]` (untl case in GNBA.lean:792, 1120, 1256)
- `simp only [Satisfies, ωSequence.drop_zero]` (untl right case in GNBA.lean:511)
- `simp [Satisfies]` (OmegaRegular.lean:122 for bot)
- `simp only [..., Satisfies]` (OmegaRegular.lean:80, 264, 294 for language membership)

## Recommended Lemmas

### Phase 1: Core @[simp] Constructor Lemmas

These mirror the Temporal pattern exactly. All provable by `Iff.rfl` since `Satisfies` is
a non-recursive `def` that pattern-matches on the formula constructor.

#### 1. `atom_iff` (simp)

```lean
@[simp]
theorem atom_iff (v : Atom → State → Prop) (w : ωSequence State) (p : Atom) :
    Satisfies v w (.atom p) ↔ v p w.head :=
  Iff.rfl
```

#### 2. `bot_iff` (simp)

```lean
@[simp]
theorem bot_iff (v : Atom → State → Prop) (w : ωSequence State) :
    Satisfies v w .bot ↔ False :=
  Iff.rfl
```

Note: Temporal uses `bot_false : ¬ Satisfies M t .bot` (non-simp). For LTL, prefer
`bot_iff` as the `@[simp]` form since `↔ False` is more canonical for `simp` (it can
rewrite `Satisfies v w .bot` to `False` in goals and hypotheses). The non-simp `bot_false`
can also be added as an alias.

#### 3. `imp_iff` (simp)

```lean
@[simp]
theorem imp_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ ψ : Formula Atom) :
    Satisfies v w (.imp φ ψ) ↔
      (Satisfies v w φ → Satisfies v w ψ) :=
  Iff.rfl
```

#### 4. `next_iff` (simp)

```lean
@[simp]
theorem next_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ : Formula Atom) :
    Satisfies v w (.next φ) ↔ Satisfies v w.tail φ :=
  Iff.rfl
```

Note: No Temporal analogue (Temporal has no `next` constructor). This is LTL-specific.

#### 5. `untl_iff` (simp)

```lean
@[simp]
theorem untl_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ ψ : Formula Atom) :
    Satisfies v w (.untl φ ψ) ↔
      ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ :=
  Iff.rfl
```

### Phase 2: Derived Lemmas (non-simp)

These follow the Temporal pattern of providing semantic characterizations for derived
operators. Since `neg`, `top`, `someFuture`, `allFuture`, and `leadsto` are all `abbrev`s
(transparent to the elaborator), their `Satisfies` characterizations reduce to compositions
of the primitive constructor lemmas.

#### 6. `bot_false` (non-simp alias)

```lean
theorem bot_false (v : Atom → State → Prop) (w : ωSequence State) :
    ¬ Satisfies v w .bot :=
  id
```

#### 7. `neg_iff` (non-simp)

```lean
theorem neg_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ : Formula Atom) :
    Satisfies v w (¬φ) ↔ ¬ Satisfies v w φ := by
  simp only [Satisfies]
```

Scoped notation `¬φ` is `Formula.neg φ = imp φ bot`, so `Satisfies v w (¬φ)` unfolds to
`Satisfies v w φ → False`, which is `¬ Satisfies v w φ`. The `simp only [Satisfies]`
should close this since `imp_iff` and `bot_iff` apply. Alternatively `Iff.rfl` may work
since `neg` is an `abbrev`.

#### 8. `top_true` (non-simp)

```lean
theorem top_true (v : Atom → State → Prop) (w : ωSequence State) :
    Satisfies v w Formula.top := by
  intro h; exact h
```

`Formula.top = imp bot bot`, so `Satisfies v w top = (False → False) = True` (up to
definitional reduction).

#### 9. `someFuture_iff` (non-simp)

```lean
theorem someFuture_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ : Formula Atom) :
    Satisfies v w (◇φ) ↔
      ∃ j, Satisfies v (w.drop j) φ := by
  simp only [Satisfies]
  constructor
  · rintro ⟨j, hj, _⟩; exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, hj, fun _ _ => top_true v _⟩
```

`someFuture φ = untl top φ`, so the guard becomes `Satisfies v (w.drop k) top` which is
always true. The characterization simplifies to just `∃ j, Satisfies v (w.drop j) φ`.

Note: The guard in LTL's untl is `∀ k < j, Satisfies v (w.drop k) φ₁` where `φ₁` is
the **first** argument. In `someFuture φ = untl top φ`, the guard is `top` (always true),
so it simplifies away.

#### 10. `allFuture_iff` (non-simp)

```lean
theorem allFuture_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ : Formula Atom) :
    Satisfies v w (□φ) ↔
      ∀ j, Satisfies v (w.drop j) φ := by
  simp only [Satisfies]
  constructor
  · intro h j
    by_contra hns
    exact h ⟨j, hns, fun _ _ => top_true v _⟩
  · intro h ⟨j, hevent, _⟩
    exact hevent (h j)
```

`allFuture φ = neg (someFuture (neg φ))`. Semantically: `¬∃ j, ¬Satisfies v (w.drop j) φ`,
which is `∀ j, Satisfies v (w.drop j) φ`.

#### 11. `leadsto_iff` (non-simp)

```lean
theorem leadsto_iff (v : Atom → State → Prop) (w : ωSequence State)
    (p q : Formula Atom) :
    Satisfies v w (p ⇝ q) ↔
      ∀ j, Satisfies v (w.drop j) p →
        ∃ k, j ≤ k ∧ Satisfies v (w.drop k) q := by
  ...
```

`leadsto p q = allFuture (imp p (someFuture q))`. This unfolds to:
`∀ j, (Satisfies v (w.drop j) p → ∃ k, Satisfies v (w.drop j |>.drop k) q)`.
Using `ωSequence.drop_drop`, this becomes `∃ k, Satisfies v (w.drop (j+k)) q`, which can
be re-indexed to `∃ k ≥ j, Satisfies v (w.drop k) q`.

This is more complex and may require careful proof. Consider deferring to a follow-up or
simplifying the statement.

## Proof Strategy

### Core Lemmas (1-5)

All five core lemmas are `Iff.rfl` proofs. The `Satisfies` function pattern-matches on the
formula constructor, so `Satisfies v w (.atom p)` definitionally reduces to `v p w.head`.
The `↔` is therefore reflexive.

**Risk assessment**: Zero risk. These are definitional equalities.

### Derived Lemmas (6-11)

These require short tactic proofs combining the core simp lemmas. The main subtleties:

1. **`neg_iff`**: Since `neg` is `abbrev`, this might be `Iff.rfl` directly. If not,
   `simp only [Satisfies]` will close it since it unfolds to `(Satisfies v w φ → False) ↔
   ¬ Satisfies v w φ`.

2. **`someFuture_iff`**: Requires eliminating the trivially-true guard. The guard
   `∀ k < j, Satisfies v (w.drop k) (imp (imp bot bot) bot)` reduces to
   `∀ k < j, (False → False) → False`, which is `∀ k < j, True → False`, wait -- this
   is `¬ top`, not `top`. Let me re-examine.

   Actually, `someFuture φ = untl top φ` where `untl` is `untl guard event`. Looking at
   the definition: `| .untl φ ψ => ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ`
   
   So `Satisfies v w (untl top φ)` = `∃ j, Satisfies v (w.drop j) φ ∧ ∀ k < j, Satisfies v (w.drop k) top`.
   
   Since `top = imp bot bot` and `Satisfies v w (imp bot bot) = (False → False) = True` (which
   is `fun h => h`), the guard is trivially satisfied. So:
   `∃ j, Satisfies v (w.drop j) φ ∧ True` simplifies to `∃ j, Satisfies v (w.drop j) φ`.

3. **`allFuture_iff`**: Dual of `someFuture_iff`. `allFuture φ = neg (someFuture (neg φ))`.
   After unfolding: `¬ ∃ j, Satisfies v (w.drop j) (neg φ)`, then using `neg_iff`:
   `¬ ∃ j, ¬ Satisfies v (w.drop j) φ`, which is `∀ j, Satisfies v (w.drop j) φ`.

4. **`leadsto_iff`**: Most complex. May need `ωSequence.drop_drop` and re-indexing.

## Impact on Downstream Files

### GNBA.lean

The 14 `simp only [Satisfies, ...]` calls can potentially be simplified:
- `simp only [Satisfies, ωSequence.head_drop]` -> `simp` (atom_iff handles it, head_drop may still be needed as a separate simplification lemma)
- `simp only [Satisfies]` in bot/imp cases -> `simp`
- `simp only [Satisfies, ωSequence.tail_drop']` -> `simp` (next_iff handles the outer unfold)
- `simp only [Satisfies, ωSequence.drop_drop]` -> `simp` (untl_iff handles outer, drop_drop still needed)

However, changing these downstream usages is **not required** for this task. Adding the
simp lemmas is backwards-compatible: `simp only [Satisfies]` still works (it just uses the
equation lemma), and `simp` will now additionally use the `@[simp]` lemmas. Future cleanup
can migrate call sites.

### OmegaRegular.lean

Similar pattern. The `simp [Satisfies]` calls will get the benefit of `@[simp]` lemmas
automatically.

### OmegaExecutionSatisfies.lean

Already has its own `satisfiesExec_atom`, `satisfiesExec_bot`, etc. These are for the
`SatisfiesExec` wrapper and are not affected.

## simpNF Compliance

All proposed `@[simp]` lemmas are `Iff.rfl` proofs, meaning the LHS does not simplify
further. This satisfies the `simpNF` linter requirement that the LHS cannot be simplified
by other simp lemmas.

Potential concern: Since `neg`, `top`, `someFuture`, `allFuture`, `leadsto` are all
`abbrev` (transparent), `simp` with `atom_iff`/`bot_iff`/`imp_iff`/`next_iff`/`untl_iff`
might automatically simplify `Satisfies v w (¬φ)` by seeing it as `Satisfies v w (.imp φ .bot)`
and applying `imp_iff` + `bot_iff`. This is actually desirable behavior and means the
derived lemmas are truly non-simp (they provide readable characterizations but are not
needed for automation).

## File Placement

All new lemmas should go in `Cslib/Logics/LTL/Semantics/Satisfies.lean` inside a new
`namespace Satisfies` block after the `Satisfiable` definition, mirroring the Temporal
file structure.

## Recommended Implementation Plan

### Phase 1: Core @[simp] Lemmas (atom_iff, bot_iff, imp_iff, next_iff, untl_iff)

Add a `namespace Satisfies` block with five `@[simp] theorem` declarations, all proved
by `Iff.rfl`. This is the minimum viable change that enables `simp` to unfold `Satisfies`
constructor-by-constructor.

### Phase 2: Derived Lemmas (bot_false, neg_iff, top_true, someFuture_iff, allFuture_iff)

Add non-simp theorems providing readable characterizations of derived operators. These
require short tactic proofs.

### Phase 3 (Optional): leadsto_iff

Add characterization of `leadsto`. This is more complex and could be deferred.

### Verification

Run `lake build Cslib.Logics.LTL.Semantics.Satisfies` after Phase 1 to ensure the simp
lemmas compile. Then run `lake build` to confirm no downstream breakage.

## Lint Prevention Checklist

- All new declarations need docstrings (docBlame)
- Prop-valued declarations must use `theorem` not `def` (defLemma)
- Names use lowerCamelCase, no underscores (defsWithUnderscore -- note `bot_iff` etc. use
  snake_case following Mathlib/CSLib convention for theorem names, which is acceptable)
- `@[simp]` lemmas need simpNF compliance (satisfied: all are Iff.rfl)
- Declarations go inside the existing `Cslib.Logic.LTL` namespace
