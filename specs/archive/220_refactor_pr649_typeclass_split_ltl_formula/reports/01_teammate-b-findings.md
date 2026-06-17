# Teammate B Research Findings: Alternative Approaches and Prior Art
## Task 220: Refactor PR #649 Typeclass Split and LTL Formula

**Confidence Level**: High (based on direct codebase analysis; medium for Lean/Mathlib LTL prior art, as none was found)

---

## Key Findings

### 1. No Prior Art for LTL in Lean 4 / Mathlib

LeanSearch, LeanFinder, and local search all return zero results for:
- `HasNext`, `FutureTemporalConnectives`, `LTLConnectives`
- LTL formula types in Mathlib
- Temporal logic next-operator typeclasses

The Mathlib `ComplexShape.next` results are unrelated (homological algebra). CSLib is pioneering LTL typeclass hierarchies in Lean 4.

**Implication**: There is no prior art to reuse or instantiate from Mathlib for the typeclass design. The design decision is therefore primarily a CSLib-internal one.

### 2. The MCS/Deduction Theorem is Already Solved — No New Work Needed

Matthew's request to "abstract MCS/Deduction Theorem proofs into classes" is **already implemented** in CSLib via `GenericMCS.lean`. The `algebraicDerivationSystem` (`Cslib/Foundations/Logic/Metalogic/GenericMCS.lean:47`) gives the deduction theorem for free to any `MinimalHilbert` proof system.

The temporal logic already:
- Has `temporal_has_deduction_theorem` (`Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean:167`)
- Has `temporal_lindenbaum`, `temporal_closed_under_derivation`, `temporal_negation_complete` (`Cslib/Logics/Temporal/Metalogic/MCS.lean`)
- Has a fully instantiated `TemporalBXHilbert` instance for `Temporal.HilbertBX` (`ProofSystem/Instances.lean`)

**Conclusion**: Matthew's concern about abstracting deduction theorem/MCS into classes is already satisfied by the existing infrastructure. The follow-up PR does NOT need to revisit these proofs — they automatically apply to any formula type that instantiates `MinimalHilbert`.

### 3. HasNext: Primitive vs. Derived — the Diamond Problem is Real

The `Temporal.Formula` type already defines `next φ := φ U ⊥` as a derived `def` (Formula.lean:413), not a constructor. For LTL, the task description proposes a new formula type `{atom, bot, imp, next, untl}` where `next` IS a constructor.

This creates a fundamental design tension:

**Option A: `HasNext` as derived from `HasUntil`**
```lean
-- next φ := φ U ⊥
-- No new typeclass needed
-- Advantage: TemporalConnectives already has HasUntil
-- Disadvantage: LTL.Formula's constructor 'next' differs from its derived encoding
```

**Option B: `HasNext` as independent atomic typeclass**
```lean
class HasNext (F : Type*) where
  next : F → F
-- Advantage: LTL.Formula.next is a direct constructor, clean
-- Disadvantage: diamond risk if also HasUntil and next = φ U ⊥
```

**Diamond analysis**: In Lean 4, diamonds in the *typeclass* hierarchy (when `LTLConnectives extends FutureTemporalConnectives, HasNext`) do NOT automatically cause incoherence if both paths define the same field. The issue arises only if `HasNext.next` and `HasUntil.untl _ bot` are definitionally distinct on the same formula type. Since `LTL.Formula.next` would be a primitive constructor while `φ U ⊥` expands to `untl φ bot`, they ARE definitionally distinct — Lean won't auto-unify them.

**Recommended resolution**: Define `HasNext` as an independent atomic typeclass (Option B), make `LTL.Formula` an instance, and add a compatibility `theorem ltl_next_eq_untl_bot : HasNext.next φ = HasUntil.untl φ HasBot.bot`. This mirrors how `HasBox` and `HasDia` are handled in modal logic (they are independent, not derived from each other), per the existing pattern in `Connectives.lean:81-91`.

### 4. The Typeclass Split: FutureTemporalConnectives → TemporalConnectives

Currently `TemporalConnectives` in `Connectives.lean:125` extends `PropositionalConnectives, HasUntil, HasSince`. The proposed split is:

```
PropositionalConnectives (HasBot + HasImp)
    ↑
FutureTemporalConnectives (+ HasUntil)
    ↑
TemporalConnectives (+ HasSince)        LTLConnectives (+ HasNext)
```

This is architecturally sound. Evidence from existing patterns:
- `ModalConnectives extends PropositionalConnectives, HasBox` (Connectives.lean:122) shows single-step extension
- `BimodalConnectives` (Connectives.lean:130) already uses the anti-diamond pattern: `extends ModalConnectives F, HasUntil F, HasSince F` rather than `extends TemporalConnectives F` — specifically to avoid the diamond from multiple inheritance

**Key constraint**: `BimodalConnectives` will need to be updated from `extends ModalConnectives F, HasUntil F, HasSince F` to `extends ModalConnectives F, TemporalConnectives F` or explicitly not extend `FutureTemporalConnectives` if that creates a new diamond. The existing anti-diamond comment at line 129 must be preserved.

### 5. ctchou's LTS/Omega-Execution Concern: Scope Should be Deferred

ctchou wants LTL semantics over omega-executions of LTS. The existing infrastructure:
- `LTS.OmegaExecution` exists at `Cslib/Foundations/Semantics/LTS/OmegaExecution.lean:26`
- It defines `OmegaExecution lts ss μs` as an ω-sequence of transitions
- The current `Temporal.Satisfies` uses `LinearOrder D` (a generic linear order), NOT LTS sequences

Connecting LTL to LTS omega-executions would require a new satisfaction relation parameterized over `ωSequence State` rather than `LinearOrder D`. This is **significant new work** beyond the scope of PR #649's typeclass refactor.

**Recommended scope for follow-up commit**: LTL omega-word semantics (satisfaction over `ωSequence State` with a labeling function `State → Atom → Prop`) can be added in `Cslib/Logics/LTL/Semantics/OmegaSatisfies.lean` without touching the existing temporal semantics. The LTS integration (where the state sequence comes from an `OmegaExecution`) should be a further separate file.

### 6. What the Minimal Viable PR #649 Follow-Up Should Contain

Based on ctchou's feedback and the zero-debt policy:

**Include**:
1. Split `TemporalConnectives` → `FutureTemporalConnectives` + `TemporalConnectives` in `Connectives.lean`
2. Add `HasNext` as atomic typeclass in `Connectives.lean`
3. Add `LTLConnectives` bundle: `extends FutureTemporalConnectives, HasNext`
4. Create `Cslib/Logics/LTL/Syntax/Formula.lean` with `{atom, bot, imp, next, untl}` primitives
5. Register `LTL.Formula` as `LTLConnectives` instance
6. Add `LTL.Formula.toTemporal : LTL.Formula Atom → Temporal.Formula Atom` embedding
7. Add basic LTL semantics over `ℕ`-indexed state sequences (`ωSequence State`)

**Exclude from this PR** (save for completeness PR):
- All `Encodable`/`Countable`/`Infinite`/`Denumerable` instances on any formula type
- `BEq`/`LawfulBEq` instances
- LTL proof system (axioms, derivation trees)
- MCS/Lindenbaum for LTL
- Past-time LTL operators (`since`, `historically`)
- LTS integration (connecting `OmegaExecution` to LTL semantics)
- `HasSince` and `snce` do NOT need a `FutureSinceConnectives` analog; `since` is purely past

### 7. Isabelle Reference: Locales vs. Lean Typeclasses

Matthew cited Isabelle's `Propositional_Logic_Class.thy` (which uses locales to abstract propositional axioms). The `GenericMCS.lean` file already explicitly references this:

```
-- References: Isabelle `Propositional_Logic_Class.thy` -- `list_deduction_logic` interpretation
```

The `algebraicDerivationSystem` in `GenericMCS.lean` is the direct Lean 4 analog of the Isabelle locale interpretation. For LTL.Formula, instantiating `MinimalHilbert` (when a proof system is added) will automatically provide deduction theorem and MCS for free through this existing infrastructure. **No new abstraction is needed.**

---

## Recommended Approach

### Typeclass Hierarchy (Recommended Design)

```lean
-- Connectives.lean additions:

class HasNext (F : Type*) where
  next : F → F

class FutureTemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F

class TemporalConnectives (F : Type*) extends FutureTemporalConnectives F, HasSince F

class LTLConnectives (F : Type*) extends FutureTemporalConnectives F, HasNext F
```

Rationale for `LTLConnectives extends FutureTemporalConnectives, HasNext` (not `TemporalConnectives`):
- LTL is purely future-time; `since` (past) is not an LTL primitive
- This matches the standard LTL definition (Vardi & Wolper 1986, Kamp 1968 future-only fragment)
- Avoids bundling past operators into LTL's typeclass

### LTL Formula Type

```lean
-- Cslib/Logics/LTL/Syntax/Formula.lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Formula Atom)
  | next (φ : Formula Atom)       -- primitive constructor
  | untl (φ₁ φ₂ : Formula Atom)  -- primitive constructor

instance : LTLConnectives (Formula Atom) where
  bot  := .bot
  imp  := .imp
  untl := .untl
  next := .next
```

Derived operators follow the Burgess convention (matching `Temporal.Formula`):
- `someFuture φ := φ U ⊤`  (eventually F)
- `allFuture φ := ¬(F ¬φ)` (globally G)
- Weak-until W(φ,ψ) := (φ U ψ) ∨ G(φ)

### LTL Omega-Word Semantics

```lean
-- Cslib/Logics/LTL/Semantics/OmegaSatisfies.lean
-- Satisfaction over ω-sequences (future-only, standard LTL)
def OmegaSatisfies (v : ℕ → Atom → Prop) (i : ℕ) : Formula Atom → Prop
  | .atom p  => v i p
  | .bot     => False
  | .imp φ ψ => OmegaSatisfies v i φ → OmegaSatisfies v i ψ
  | .next φ  => OmegaSatisfies v (i + 1) φ
  | .untl φ ψ => ∃ j > i, OmegaSatisfies v j φ ∧ ∀ k, i < k → k < j → OmegaSatisfies v k ψ
```

Note: Using `ℕ` (discrete successor) as time domain lets `next φ` have the natural semantics `OmegaSatisfies v (i+1) φ` — this is semantically clean and does NOT require `Discrete` frame axioms in the proof system.

### toTemporal Embedding

```lean
-- LTL.Formula.toTemporal : LTL.Formula Atom → Temporal.Formula Atom
| .atom p   => .atom p
| .bot      => .bot
| .imp φ ψ  => .imp (toTemporal φ) (toTemporal ψ)
| .next φ   => .untl (toTemporal φ) .bot  -- X(φ) = φ U ⊥ in Temporal
| .untl φ ψ => .untl (toTemporal φ) (toTemporal ψ)
```

This embedding proves the relationship between `LTL.Formula.next` and `Temporal.Formula.next` (the derived `def`). It provides the conceptual bridge without creating typeclass diamonds.

---

## Evidence / Examples from Codebase

- **Typeclass anti-diamond pattern**: `BimodalConnectives` (Connectives.lean:129-131) explicitly avoids extending `TemporalConnectives` to prevent diamond. Same care needed when updating `BimodalConnectives` after the split.
- **GenericMCS already covers Matthew's concern**: `algebraicDerivationSystem` (GenericMCS.lean:47-49) wraps `MinimalHilbert` for any formula type. LTL.Formula will inherit this for free once its proof system is added.
- **Isabelle cross-reference already present**: `GenericMCS.lean:27` cites `Propositional_Logic_Class.thy` — Matthew's Isabelle reference IS the model that CSLib already follows.
- **OmegaExecution exists**: `Cslib/Foundations/Semantics/LTS/OmegaExecution.lean` provides `OmegaExecution lts ss μs : Prop`. LTS-based LTL semantics would use this, but it's out of scope for this PR.
- **Discrete FrameClass exists**: `Temporal.FrameClass.Discrete` (ProofSystem/Axioms.lean:43) already names the discrete frame class. The `next` operator's axioms (`Xφ ↔ ¬Y¬φ`) would go under `Discrete` FrameClass if a proof system is added to LTL.

---

## Confidence Assessment

| Finding | Confidence |
|---------|-----------|
| No Mathlib LTL prior art | High (exhaustive search) |
| GenericMCS covers Matthew's concern | High (direct code reading) |
| HasNext should be atomic typeclass | High (modal HasBox/HasDia precedent) |
| Diamond risk is real but manageable | High (Lean 4 typeclass behavior) |
| ctchou's LTS concern is out of scope | Medium (depends on reviewer intent) |
| Minimal viable PR scope | Medium (judgment call on reviewer expectations) |
| toTemporal embedding approach | High (direct definitional match) |
