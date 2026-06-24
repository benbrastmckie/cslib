# Research Report: Derived Connective Defaults (Task 340)

**Session**: sess_1750832400_multi_340
**Date**: 2026-06-24

## Problem Statement

Five derived connectives (`neg`, `top`, `and`, `or`, `iff`) are copy-pasted with identical
Lukasiewicz encodings across four formula files:
- `Cslib/Logics/Modal/Basic.lean` (`Proposition.neg`, `.top`, `.and`, `.or`, `.iff`)
- `Cslib/Logics/Temporal/Syntax/Formula.lean` (`Formula.neg`, `.top`, `.and`, `.or`, `.iff`)
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` (`Formula.neg`, `.top`, `.and`, `.or`; no `iff`)
- `Cslib/Logics/LTL/Syntax/Formula.lean` (`Formula.neg`, `.top`, `.and`, `.or`, `.iff`)

Total duplicated lines: ~75 (28 Modal + 17 Temporal + 13 Bimodal + 17 LTL).

## Encodings (All Identical)

| Connective | Encoding |
|---|---|
| `neg φ` | `imp φ bot` |
| `top` | `imp bot bot` |
| `and φ ψ` | `imp (imp φ (imp ψ bot)) bot` |
| `or φ ψ` | `imp (imp φ bot) ψ` |
| `iff φ ψ` | `and (imp φ ψ) (imp ψ φ)` |

## Recommended Approach: Default Fields on `PropositionalConnectives`

Add `neg`, `top`, `and`, `or`, `iff` as **defaulted fields** to `PropositionalConnectives`
in `Connectives.lean`. Each formula file then replaces its standalone `abbrev` bodies with
thin delegates to the typeclass fields.

### Connectives.lean Change

```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F where
  /-- Negation derived via Lukasiewicz encoding: neg phi := phi imp bot. -/
  neg : F -> F := fun φ => HasImp.imp φ HasBot.bot
  /-- Verum derived via Lukasiewicz encoding: top := bot imp bot. -/
  top : F := HasImp.imp (HasBot.bot : F) HasBot.bot
  /-- Conjunction derived via Lukasiewicz encoding: and phi psi := neg(phi imp neg psi). -/
  and : F -> F -> F := fun φ ψ =>
    HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot
  /-- Disjunction derived via Lukasiewicz encoding: or phi psi := neg phi imp psi. -/
  or : F -> F -> F := fun φ ψ =>
    HasImp.imp (HasImp.imp φ HasBot.bot) ψ
  /-- Biconditional: iff phi psi := and (phi imp psi) (psi imp phi). -/
  iff : F -> F -> F := fun φ ψ =>
    and (HasImp.imp φ ψ) (HasImp.imp ψ φ)
```

### Per-Formula-File Change Pattern

Replace standalone `abbrev` definitions to delegate to typeclass:

```lean
-- Before (~15 lines per file):
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := .imp φ .bot
abbrev Formula.top : Formula Atom := .imp .bot .bot
abbrev Formula.and (φ ψ : Formula Atom) : Formula Atom :=
  .imp (.imp φ (.imp ψ .bot)) .bot
abbrev Formula.or (φ ψ : Formula Atom) : Formula Atom :=
  .imp (.imp φ .bot) ψ
abbrev Formula.iff (φ ψ : Formula Atom) : Formula Atom :=
  (φ.imp ψ).and (ψ.imp φ)

-- After (~5 lines per file):
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := PropositionalConnectives.neg φ
abbrev Formula.top : Formula Atom := PropositionalConnectives.top
abbrev Formula.and (φ ψ : Formula Atom) : Formula Atom := PropositionalConnectives.and φ ψ
abbrev Formula.or (φ ψ : Formula Atom) : Formula Atom := PropositionalConnectives.or φ ψ
abbrev Formula.iff (φ ψ : Formula Atom) : Formula Atom := PropositionalConnectives.iff φ ψ
```

## Feasibility Verification

All critical properties were tested via `lean_run_code` (standalone snippets simulating
the CSLib typeclass hierarchy):

### 1. Definitional Equality Preserved

```lean
-- With instance providing imp := .imp, bot := .bot:
example (φ : MF) : PropConn.neg φ = MF.imp φ .bot := rfl  -- PASSES
example : (PropConn.top : MF) = MF.imp .bot .bot := rfl    -- PASSES
```

The typeclass defaults unfold to the same constructor terms as the current inline definitions.

### 2. `simp only` Unfolding Works

```lean
example (φ : MF) : sat (~φ) = (sat φ → False) := by
  simp only [MF.neg, PropConn.neg, sat]  -- PASSES
```

`simp` can unfold through the `abbrev -> typeclass field -> default value -> constructor` chain.

### 3. `change` Tactic Works

```lean
example (φ ψ : MF) : sat (MF.and φ ψ) ↔ sat (MF.and φ ψ) := by
  change ((sat φ → sat ψ → False) → False) ↔ _  -- PASSES
  exact Iff.rfl
```

The proof term structure expected by `change` is identical.

### 4. Defaults Propagate Through `extends`

```lean
class ModalConn (F : Type) extends PropConn F, HasBox' F
instance : ModalConn MF where bot := .bot; imp := .imp; box := .box
-- neg, top, and, or, iff all get Lukasiewicz defaults automatically
example (φ : MF) : PropConn.neg φ = MF.imp φ .bot := rfl  -- PASSES
```

### 5. Bridge Instance Preserves Defaults

```lean
instance bimodalToModal (F : Type) [BimodalConn F] : ModalConn F where
  bot := HasBot'.bot; imp := HasImp'.imp; box := HasBox'.box
-- Defaults from PropConn are correctly reconstructed
example (φ : BF) : @PropConn.neg BF (bimodalToModal BF).toPropConn φ = BF.imp φ .bot := rfl
```

### 6. PL.Proposition Override Works

`PL.Proposition` has native `and`/`or` constructors. It can override the Lukasiewicz defaults:

```lean
instance : PropConn PL where
  bot := .bot; imp := .imp
  and := .and   -- override: use native constructor
  or := .or     -- override: use native constructor
-- neg still gets Lukasiewicz default, and/or use native constructors
```

## Downstream Impact Analysis

### Heavy Consumers of Derived Connectives

| File | Uses |
|------|------|
| `Bimodal/Metalogic/Soundness/FrameClassVariants.lean` | `Formula.neg`, `.and`, `.or` in ~40 `simp only` calls |
| `Bimodal/Metalogic/BXCanonical/` (multiple files) | `Formula.neg`, `.and` in derivation trees |
| `Modal/Basic.lean` | `Proposition.neg`, `.and`, `.or` in Satisfies proofs |
| `Temporal/Metalogic/CompletenessHelpers.lean` | `Formula.neg`, `.top`, `.and` in 30+ locations |
| `LTL/ModelChecking.lean` | `Formula.neg` in model checking |

### Expected Impact

**No proof breakage.** All downstream code uses the namespace-qualified abbreviations
(`Formula.neg`, `Proposition.neg`, etc.) or scoped notation (`¬`, `∧`, `∨`, `→`, `↔`).
Since the `abbrev` declarations are retained as thin delegates, the names and notation
bindings are unchanged. The definitional unfolding chain is equivalent.

### Simp Lemma Consideration

If `simp only [Formula.neg]` alone doesn't unfold through the delegation, the fix is to
add `PropositionalConnectives.neg` to the simp call or mark the delegate `abbrev` with
`@[reducible]` (which `abbrev` already implies). Testing during implementation will confirm.

## Relationship to Existing Code

### Axioms.lean (`neg'`, `top'`, `conj'`, `disj'`)

`Axioms.lean` defines standalone abbreviations `neg'`, `top'`, `conj'`, `disj'` with the
same Lukasiewicz encodings. These become redundant once `PropositionalConnectives` has the
default fields. However, unifying Axioms with the new defaults is a separate cleanup:
`conj'`/`disj'` are used in ~30 lines of Axioms.lean and renaming would touch many
expressions. Recommend deferring to a follow-up task.

### Task 173 (Adding `HasAnd`/`HasOr` to `PropositionalConnectives`)

Task 173 (archived) planned to add `HasAnd`/`HasOr` as required superclasses of
`PropositionalConnectives`. Task 340 is complementary: it adds `and`/`or` as *defaulted*
fields (not required), giving Lukasiewicz encodings by default. When task 173 is eventually
done, types with native constructors can override the defaults, while types without native
constructors keep the Lukasiewicz encoding.

### Bimodal `iff` Gap

Bimodal's `Formula.lean` is the only one of the four files that does not define `iff`.
The implementation should add the delegate `abbrev` for `iff` to Bimodal, improving
consistency across all four logics.

## Implementation Plan Recommendation

### Phase 1: Add Defaults to Connectives.lean (~12 lines added)

Add 5 defaulted fields (`neg`, `top`, `and`, `or`, `iff`) to `PropositionalConnectives`.
Update the module docstring to reflect the new design.

### Phase 2: Update Formula Files (~40 lines modified across 4 files)

For each of Modal, Temporal, Bimodal, LTL:
1. Replace the inline Lukasiewicz body of each `abbrev` with a delegate to
   `PropositionalConnectives.*`
2. Remove the per-connective docstrings that just restate the encoding (the canonical
   doc is now on the `PropositionalConnectives` field)
3. Add `iff` delegate to Bimodal (currently missing)

### Phase 3: Build Verification

Run `lake build` to confirm all downstream proofs compile. If any `simp` calls fail,
add `PropositionalConnectives.neg` etc. to the relevant `simp only` lists.

### Estimated Metrics

- **Lines removed**: ~55 (inline definitions + their docstrings)
- **Lines added**: ~12 (Connectives.lean defaults) + ~20 (thin delegates)
- **Net reduction**: ~25-30 lines
- **Consistency guarantee**: All four logics provably share encodings via single source

### Risk Assessment

- **Low risk**: Verified via `lean_run_code` that all critical properties hold
- **No sorry needed**: Pure refactoring, no proof obligations
- **Backwards compatible**: Default fields are additive; existing instances unchanged
- **Rollback**: If any downstream proof breaks, the delegate `abbrev` can be replaced
  with the original inline definition without touching `Connectives.lean`

## Files to Modify

1. `Cslib/Foundations/Logic/Connectives.lean` — add default fields to `PropositionalConnectives`
2. `Cslib/Logics/Modal/Basic.lean` — delegate `Proposition.{neg,top,and,or,iff}`
3. `Cslib/Logics/Temporal/Syntax/Formula.lean` — delegate `Formula.{neg,top,and,or,iff}`
4. `Cslib/Logics/Bimodal/Syntax/Formula.lean` — delegate `Formula.{neg,top,and,or}` + add `iff`
5. `Cslib/Logics/LTL/Syntax/Formula.lean` — delegate `Formula.{neg,top,and,or,iff}`

## Reuse Check

- **CSLib Foundations**: No existing derived-connective default infrastructure found.
  `Axioms.lean` has `neg'`/`top'`/`conj'`/`disj'` but as standalone abbreviations, not
  typeclass fields.
- **Mathlib**: No directly applicable pattern. Mathlib's algebraic typeclasses use
  default fields extensively (e.g., `SubtractionMonoid.toInvolutiveNeg`), but for
  algebraic operations, not logical connectives.
- **CSLib typeclasses**: `HasAnd`/`HasOr` exist as atomic classes but are not yet integrated
  into `PropositionalConnectives` (deferred by task 173). The proposed defaults are independent
  of `HasAnd`/`HasOr`.
