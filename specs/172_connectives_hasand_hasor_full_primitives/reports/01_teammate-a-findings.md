# Teammate A Findings: Connectives.lean Implementation Approach

**Task**: 172 — Extend Connectives.lean for five-primitive signature {atom, bot, imp, and, or}
**Angle**: Implementation approach for Connectives.lean specifically
**Date**: 2026-06-12

---

## Key Findings

### 1. HasAnd/HasOr Typeclass Design

The existing pattern is clean and consistent: each operator is its own one-field typeclass over a `Type*`. The same pattern should apply verbatim for `HasAnd` and `HasOr`:

```lean
/-- A type has a conjunction connective. -/
class HasAnd (F : Type*) where
  /-- The conjunction connective. -/
  and : F → F → F

/-- A type has a disjunction connective. -/
class HasOr (F : Type*) where
  /-- The disjunction connective. -/
  or : F → F → F
```

**Field name choices**: The single-field names `and` and `or` mirror `bot`, `imp`, `box`, `untl`, `snce`. All are lowercase, short, matching the operator they represent. Using `conj`/`disj` would diverge from the established pattern without benefit.

**Potential name conflict**: `HasAnd.and` and `HasOr.or` are fully qualified names in the `Cslib.Logic` namespace. Lean 4 allows `and` and `or` as field names (they are keywords only in certain syntactic positions, not as structure fields). The existing fields `bot`, `imp`, `box`, `untl`, `snce` include two-argument functions (`imp`, `untl`, `snce`) as fields without conflict, confirming this works. However, `HasImp.imp` uses `imp` which is also a Lean keyword — this already works in the codebase, so `HasAnd.and`/`HasOr.or` will too.

**No conflict with Mathlib's `And`/`Or`**: Mathlib's propositional `And` and `Or` are `Prop`-level. `HasAnd.and : F → F → F` where `F : Type*` targets formula types, not `Prop`. There is no conflict.

### 2. Bundled Class Updates

**Current situation**: The bundled classes `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` are the compositional layer. None of them are currently used as typeclass constraints in code outside `Connectives.lean` itself — the concrete instance registrations are the only uses. The constraint pattern throughout the codebase uses the atomic `[HasBot F]`, `[HasImp F]`, etc. directly.

**Should PropositionalConnectives include HasAnd/HasOr?** Yes, but with important nuance. The task 172 description explicitly requires adding `HasAnd` and `HasOr` to the bundled classes. The five-primitive signature is the intended primitive basis going forward. Adding them makes `PropositionalConnectives` self-documenting as "the full primitive basis" for the fork's design.

**Updated bundled classes**:

```lean
/-- Propositional connectives: falsum, implication, conjunction, disjunction. -/
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F, HasAnd F, HasOr F

/-- Modal connectives: propositional connectives plus necessity. -/
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F

/-- Temporal connectives: propositional connectives plus until and since. -/
class TemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F, HasSince F

/-- Bimodal connectives: modal connectives plus until and since.
    Note: we extend `ModalConnectives` and add `HasUntil`/`HasSince` directly
    rather than extending `TemporalConnectives`, to avoid a typeclass diamond. -/
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

**Diamond note**: The bimodal comment about avoiding a typeclass diamond is already in the code. The diamond avoidance pattern is unaffected by adding `HasAnd`/`HasOr` to `PropositionalConnectives` — both `ModalConnectives` and `TemporalConnectives` would inherit `HasAnd`/`HasOr` from `PropositionalConnectives`, and `BimodalConnectives` extends `ModalConnectives` (which already has `HasAnd`/`HasOr`) without extending `TemporalConnectives`. The diamond concern is only about `HasUntil`/`HasSince`, not the propositional connectives.

**Backward compatibility**: Since none of the bundled classes are used as typeclass constraints in downstream code (only the atomic `Has*` classes are), adding new `extends` to the bundled classes does NOT break any existing code. The only downstream effect is on the concrete instances:
- `instance : PropositionalConnectives (Proposition Atom) where bot := .bot; imp := .imp` will need to add `and := .and` and `or := .or` fields — but task 173 adds those constructors.
- For task 172 only, the bundled class bodies are updated but no existing instance breaks (instances for existing formula types still satisfy the existing fields; they become incomplete until task 173 adds constructors, but task 172 doesn't change those files).

**Implementation detail for task 172**: Since task 173 will add the `and`/`or` constructors to the concrete formula types, task 172 can safely add `HasAnd`/`HasOr` to the bundled class definitions. The existing formula type instances (`Proposition`, `Modal.Proposition`, `Temporal.Formula`, `Bimodal.Formula`) will NOT need to provide `and`/`or` fields yet — they will fail to compile until task 173 completes them. However, this is expected: task 172 changes `Connectives.lean` only, and the downstream breakage is deferred to task 173.

**ALTERNATIVE approach (zero-breakage in task 172)**: If the goal is that task 172 produces a zero-breakage change to `Connectives.lean` alone, the bundled class updates should be deferred to task 173. Task 172 would add only the atomic `HasAnd`/`HasOr` typeclasses, and the bundled class extensions would be part of task 173 alongside the formula type additions.

Given the task description says "update the bundled classes... to include them," the bundled class changes are explicitly in scope for task 172. This means task 172 itself will cause compilation failures in the instance declarations until task 173 is complete. This is an acceptable interim state if tasks 172 and 173 are planned as sequential, which the dependency graph confirms.

### 3. ImpBotDerived Fate

**Current state**: `ImpBotDerived` is defined in `Connectives.lean` and used nowhere else in the codebase. It is explicitly documented as "intentionally uninstantiated" and a "specification artifact." Its four fields are: `neg`, `top`, `or`, `and`.

**The task description is precise**: The fix is to retain `neg` and `top` (valid in all three logics), and remove `or` and `and` (classical-only under Lukasiewicz convention).

**Remaining after surgery**:

```lean
/-- Derived connectives definable from `bot` and `imp` alone.

Provides `neg` and `top` as definitional abbreviations valid across minimal, intuitionistic,
and classical logics: negation is implication to falsum (`neg φ := imp φ bot`), verum is
`imp bot bot`.

The connectives `and` and `or` are no longer provided here. Under the Lukasiewicz convention,
`and φ ψ := ¬(φ → ¬ψ)` and `or φ ψ := ¬φ → ψ` are classically equivalent to conjunction
and disjunction, but are NOT intuitionistically or minimally equivalent (Wajsberg 1938,
McKinsey 1939). With and/or promoted to primitives (HasAnd, HasOr), these definitions are
no longer needed and their presence in ImpBotDerived would misrepresent them as
logic-neutral.

**Status**: This class is intentionally uninstantiated. See existing formula type `abbrev`
definitions for concrete derived connective implementations. The class is retained as a
specification artifact and for potential future use in polymorphic proof-system abstractions.
-/
class ImpBotDerived (F : Type*) [HasBot F] [HasImp F] where
  /-- Negation: `neg φ := imp φ bot` -/
  neg : F → F := fun φ => HasImp.imp φ HasBot.bot
  /-- Top/verum: `top := imp bot bot` -/
  top : F := HasImp.imp HasBot.bot HasBot.bot
```

**Why keep ImpBotDerived at all?** Two reasons:
1. `neg` and `top` are genuinely derivable from {imp, bot} and valid in all three logics.
2. The class serves as documentation that these derivations are primitive-free — a specification artifact as noted.

**Alternative**: Delete `ImpBotDerived` entirely since it is never instantiated and the individual formula types already define their own `abbrev` neg/top. This would be the simplest approach. However, retaining the class (trimmed to neg/top) preserves its architectural documentation value at negligible cost.

**Recommendation**: Trim to neg/top only, update docstring to explain why and/or were removed.

### 4. Backward Compatibility Analysis

**Files that import Connectives.lean** (directly or transitively):
- `Cslib/Foundations/Logic/Axioms.lean` — uses `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` directly; uses `neg'`, `top'`, `conj'`, `disj'` local abbreviations (NOT `ImpBotDerived`). No breakage.
- `Cslib/Foundations/Logic/ProofSystem.lean` — uses `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` directly. No breakage.
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — uses `[HasBot F] [HasImp F]`. No breakage.
- `Cslib/Foundations/Logic/Theorems/*/` — use `HasBot`, `HasImp`, etc. directly. No breakage.
- `Cslib/Logics/Propositional/Defs.lean` — provides `instance : PropositionalConnectives (Proposition Atom)`. BREAKS if `PropositionalConnectives` now extends `HasAnd F, HasOr F` and `Proposition` does not have and/or constructors.
- `Cslib/Logics/Modal/Basic.lean` — provides `instance : ModalConnectives (Proposition Atom)`. BREAKS for same reason.
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — provides `instance : TemporalConnectives (Formula Atom)`. BREAKS.
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` — provides `instance : BimodalConnectives (Formula Atom)`. BREAKS.

**Summary**: Adding `HasAnd`/`HasOr` to the bundled classes in `Connectives.lean` causes exactly 4 downstream compile failures (the four instance declarations in the four concrete formula type files). These are the expected breakages that task 173+ will fix.

**Mitigating the breakage**: The task 172 implementation could use `default` field values to avoid breaking downstream instances temporarily:

```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F, HasAnd F, HasOr F
```

Unfortunately, `HasAnd` and `HasOr` have no natural defaults — `and : F → F → F` needs to produce an `F` value, and there is no canonical "partial" conjunction that works before the constructors exist. Default implementations would require `HasImp`/`HasBot` and be the Lukasiewicz definitions — which is exactly what we want to avoid (classical-only).

**Conclusion**: The 4 downstream breakages are expected and acceptable as part of the planned refactor sequence. Task 172 intentionally sets up the interface; task 173 fills in the implementations.

### 5. PR #607 Alignment

PR #607 (Montesi's approach) favors one-class-per-operator with notation-level design. The proposed `HasAnd`/`HasOr` typeclasses align perfectly with this direction:
- Each is a single-field typeclass over `F : Type*`
- Each provides exactly one operator
- The design does not bundle operators (no `PropositionalConnectives` analog in PR #607's Operators/ approach)

The CSLib bundled classes (`PropositionalConnectives`, `ModalConnectives`, etc.) are compositional conveniences — they are not at odds with PR #607. PR #607 would add per-operator simp lemma files; the bundled classes group them for instance registration convenience. These are complementary layers.

The task 171 research noted that simp lemmas in PR #607 should be oriented "into notation" (e.g., `@[simp] theorem and_def [HasAnd F] (a b : F) : HasAnd.and a b = ...`). Task 172 does not add any simp lemmas, so this is a note for task 173+.

---

## Recommended Approach

### Step 1: Add atomic typeclasses

Add immediately after `HasSince`:

```lean
/-- A type has a conjunction connective. -/
class HasAnd (F : Type*) where
  /-- The conjunction connective. -/
  and : F → F → F

/-- A type has a disjunction connective. -/
class HasOr (F : Type*) where
  /-- The disjunction connective. -/
  or : F → F → F
```

### Step 2: Update bundled classes

Update `PropositionalConnectives` to include `HasAnd F, HasOr F`. The extension chain propagates automatically:

```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F, HasAnd F, HasOr F
```

`ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` are unchanged structurally — they extend `PropositionalConnectives` and will inherit `HasAnd`/`HasOr` automatically.

### Step 3: Trim ImpBotDerived

Remove `or` and `and` fields from `ImpBotDerived`. Update docstring to explain the rationale (Lukasiewicz definitions are classical-only; and/or are now primitives). Retain `neg` and `top`.

### Step 4: Update module docstring

The current docstring says:
> "Falsum and implication are taken as the only propositional primitives because `{imp, bot}` is functionally complete for classical logic..."

This must be updated to reflect the five-primitive design. New framing:
> "The five propositional primitives are `{bot, imp, and, or}` plus atoms. This matches the standard signature of natural deduction systems (Gentzen 1935, Prawitz 1965, Heyting 1930, Troelstra & van Dalen 1988). Negation (`neg := φ → ⊥`) and verum (`top := ⊥ → ⊥`) remain derived connectives valid across minimal, intuitionistic, and classical logic."

The module's `## Design` section should also update the bullet point listing atomic classes to include `HasAnd` and `HasOr`.

---

## Evidence/Examples

### Pattern Consistency

The pattern for `HasAnd`/`HasOr` is exactly parallel to the existing atomic classes:

| Class | Field | Arity | Type |
|-------|-------|-------|------|
| `HasBot` | `bot` | 0 | `F` |
| `HasImp` | `imp` | 2 | `F → F → F` |
| `HasBox` | `box` | 1 | `F → F` |
| `HasUntil` | `untl` | 2 | `F → F → F` |
| `HasSince` | `snce` | 2 | `F → F → F` |
| **`HasAnd`** | **`and`** | **2** | **`F → F → F`** |
| **`HasOr`** | **`or`** | **2** | **`F → F → F`** |

### ImpBotDerived: Before and After

**Before** (current `ImpBotDerived`): 4 fields — `neg`, `top`, `or`, `and`

**After** (task 172): 2 fields — `neg`, `top` only

**Justification**: The Lukasiewicz definitions `or φ ψ := (φ → ⊥) → ψ` and `and φ ψ := ¬(φ → ¬ψ)` are classically equivalent to ∨ and ∧ but NOT intuitionistically or minimally equivalent (Wajsberg 1938, McKinsey 1939 — confirmed in task 171 research with Kripke counterexamples). Retaining them in `ImpBotDerived` would misrepresent them as primitive-basis-neutral.

### Downstream Breakage Map

| File | Instance | Status after task 172 |
|------|----------|-----------------------|
| `Defs.lean` | `PropositionalConnectives (Proposition Atom)` | Breaks (missing and/or) → fixed by task 173 |
| `Modal/Basic.lean` | `ModalConnectives (Proposition Atom)` | Breaks → fixed by task 175 |
| `Temporal/Syntax/Formula.lean` | `TemporalConnectives (Formula Atom)` | Breaks → fixed by task 176 |
| `Bimodal/Syntax/Formula.lean` | `BimodalConnectives (Formula Atom)` | Breaks → fixed by task 177 |

The Axioms.lean file and all Foundations/Logic/Theorems/* files are unaffected because they use the atomic `HasBot`, `HasImp`, etc. classes directly, not the bundled `PropositionalConnectives`.

---

## Confidence Level

**High confidence** on:
- HasAnd/HasOr typeclass design (exact parallel to existing pattern)
- ImpBotDerived trimming (only neg/top are logic-neutral; and/or are Lukasiewicz classical-only)
- Downstream breakage map (only the 4 instance declaration files; confirmed by grep)
- No usages of bundled classes as typeclass constraints anywhere in the codebase

**Medium confidence** on:
- Whether the bundled class updates should be in task 172 or deferred to task 173 (task description says 172, but a zero-breakage task 172 would defer them)
- Whether `ImpBotDerived` should be retained (trimmed) or deleted entirely (it is never instantiated)

**Low concern areas**:
- Lean 4 field name conflicts (`and`, `or` as field names): confirmed safe by analogy with `imp` (also a keyword) working as a field name in `HasImp`
- PR #607 alignment: the one-class-per-operator approach is exactly what is proposed

---

## Notes for Downstream Tasks

- **Task 173** (Propositional refactor): Will need to add `and := .and` and `or := .or` to the `PropositionalConnectives` instance in `Defs.lean`, after adding constructors to `Proposition`. The `subst`, `complexity`, `atoms` functions will gain two cases.

- **Axioms.lean compatibility**: The existing `conj'` and `disj'` abbreviations in `Axioms.lean` use Lukasiewicz encoding via `HasBot`/`HasImp`. These remain valid and are not replaced by `HasAnd.and`/`HasOr.or`. The Hilbert axiom formulas for and/or (which task 173 will add to `Axioms.lean`) will need to reference `HasAnd.and` and `HasOr.or` directly — not the Lukasiewicz `conj'`/`disj'`.

- **ProofSystem.lean extension**: Task 173 will need new `HasAxiomAndIntro`, `HasAxiomAndElim1`, `HasAxiomAndElim2`, `HasAxiomOrIntro1`, `HasAxiomOrIntro2`, `HasAxiomOrElim` typeclass types in `ProofSystem.lean`, each parameterized with `[HasAnd F]` or `[HasOr F]` constraints alongside the existing `[HasBot F]`/`[HasImp F]`.
