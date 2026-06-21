# Research Report: Fix Stale LTL Docstrings Post Task-254

## Summary

All four stale docstring/comment locations identified in the task description have been verified.
Each is a genuine documentation debt left over from the task-254 LTL convention revision. The
fixes are purely textual (docstrings and comments); no Lean code changes are required.

## Findings

### Issue 1: Embedding.lean module docstring (line 14)

**File**: `Cslib/Logics/LTL/Embedding.lean`, lines 12-32

**Current text** (line 14-15):
```
This module defines the canonical embedding of `LTL.Formula` into `Temporal.Formula`,
mapping LTL's five primitives to their Burgess-temporal counterparts.
```

**Problem**: The phrase "mapping LTL's five primitives to their Burgess-temporal counterparts"
implies LTL uses Burgess conventions. After task-254, LTL uses the **standard** convention
(guard=first, event=second) while Temporal uses the Burgess convention (event=first,
guard=second). The module docstring should explain both conventions and that the embedding
bridges between them.

**Recommended replacement** (lines 14-15):
```
This module defines the canonical embedding of `LTL.Formula` into `Temporal.Formula`.
LTL uses the standard convention (`untl guard event`) while Temporal uses the Burgess
convention (`untl event guard`); the embedding bridges the two.
```

The rest of the module docstring (lines 23-26 on semantic correspondence) is actually correct
and should be preserved as-is. The reflexive/strict until distinction is accurate.

### Issue 2: Formula.lean next constructor docstring (line 75)

**File**: `Cslib/Logics/LTL/Syntax/Formula.lean`, line 75

**Current text**:
```
/-- Next-step operator: Xφ holds at t iff φ holds at t+1. -/
```

**Problem**: The notation `Xφ` is the ASCII/text convention. After task-254, LTL uses the
Unicode notation `◯` (white circle, U+25EF) for next. The docstring should use the
project's notation.

**Recommended replacement**:
```
/-- Next-step operator: ◯φ holds at t iff φ holds at t+1. -/
```

### Issue 3: Embedding.lean untl match arm parameter names (line 49)

**File**: `Cslib/Logics/LTL/Embedding.lean`, line 49

**Current code**:
```lean
| .untl ψ φ => (toTemporal φ).reflexiveUntl (toTemporal ψ)
```

**Analysis**: LTL's `untl` constructor has parameters `(φ₁ φ₂ : Formula Atom)` where
`φ₁` = guard and `φ₂` = event (standard convention, post-task-254). The match arm binds
`ψ` to the first position (guard) and `φ` to the second position (event).

The **semantic mapping is correct**: the embedding passes `φ` (event) as `reflexiveUntl`'s
first argument and `ψ` (guard) as its second, which matches `reflexiveUntl`'s signature
`(φ ψ : Formula Atom)` = (event, guard). The Temporal `reflexiveUntl` docstring says:
"φ holds at some point >= t with ψ at all intermediate points", confirming φ = event,
ψ = guard.

However, the **variable naming is confusing**: the match arm uses `ψ` for the first
constructor argument (guard=φ₁) and `φ` for the second (event=φ₂). This swaps the
conventional Greek letter ordering. Two options:

**Option A** (rename for clarity):
```lean
| .untl φ₁ φ₂ => (toTemporal φ₂).reflexiveUntl (toTemporal φ₁)
```

**Option B** (add inline comment explaining the swap):
```lean
  -- ψ=guard (LTL's φ₁), φ=event (LTL's φ₂); swapped to match Temporal's Burgess order
| .untl ψ φ => (toTemporal φ).reflexiveUntl (toTemporal ψ)
```

**Recommendation**: Option A is cleaner. Using `φ₁` and `φ₂` matches the LTL constructor's
own parameter names and makes the embedding logic self-documenting.

### Issue 4: OmegaRegular.lean stale proof_wanted reference (line 310)

**File**: `Cslib/Logics/LTL/Semantics/OmegaRegular.lean`, lines 305-310

**Current docstring**:
```
/-- The ω-language of `φ U ψ` (guard `φ`, event `ψ`) is ω-regular,
given IH for both subformulas.

Proved via the global GNBA construction (Baier-Katoen / Vardi-Wolper 1986). The hypotheses
`hφ` and `hψ` are not needed by this approach — the GNBA for `untl φ ψ` handles all
subformulas simultaneously — but the signature matches the original `proof_wanted`. -/
```

**Problem**: The phrase "the signature matches the original `proof_wanted`" references a
`proof_wanted` placeholder that no longer exists -- the proof is now complete (completed in
task-254 phase 6). The reference is stale and confusing.

**Recommended replacement**:
```
/-- The ω-language of `φ U ψ` (guard `φ`, event `ψ`) is ω-regular,
given IH for both subformulas.

Proved via the global GNBA construction (Baier-Katoen / Vardi-Wolper 1986). The hypotheses
`hφ` and `hψ` are not needed by this approach — the GNBA for `untl φ ψ` handles all
subformulas simultaneously — but the signature retains them for uniformity with the
inductive cases in `Formula.isRegular`. -/
```

This explains **why** the unused hypotheses are still present (for structural consistency
with the `induction` tactic's generated goals) without referencing the defunct `proof_wanted`.

## File Inventory

| # | File | Line(s) | Change Type |
|---|------|---------|-------------|
| 1 | `Cslib/Logics/LTL/Embedding.lean` | 14-15 | Rewrite module docstring |
| 2 | `Cslib/Logics/LTL/Syntax/Formula.lean` | 75 | Replace `Xφ` with `◯φ` |
| 3 | `Cslib/Logics/LTL/Embedding.lean` | 49 | Rename pattern variables or add comment |
| 4 | `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` | 310 | Remove `proof_wanted` reference |

## Build Impact

All changes are docstring/comment-only (issues 1, 2, 4) or variable renaming in a pattern
match (issue 3). Issue 3 (renaming `ψ φ` to `φ₁ φ₂`) changes no semantics -- pattern
variable names in a match arm are local bindings with no external effect. No proof changes
are needed.

A `lake build` should pass without changes to any proof.

## Complexity Assessment

This is a straightforward documentation-only task. No proof obligations, no sorry risks,
no new definitions needed. Estimated implementation effort: 15-20 minutes of editing with
a single build verification pass.
