# Task 179: Upstream Study -- Primitive Diamond Refactor

## Executive Summary

The upstream CSLib (`leanprover/cslib`, `upstream/main`) uses a **fundamentally different** primitive set from our fork. Upstream has `{atom, not, and, diamond}` as primitive constructors with `box`, `imp`, and `or` as derived connectives. Our fork has `{atom, bot, imp, box}` with `neg`, `and`, `or`, and `diamond` as derived. This is not a minor divergence -- the two designs embody opposite philosophical choices about which operators are primitive.

Adding `.dia` as a primitive to our fork should **not** attempt to align with upstream's approach. Instead, the clean-break refactor should extend our existing `{atom, bot, imp, box}` signature to `{atom, bot, imp, box, dia}`, preserving our design philosophy while gaining the operational independence of box and diamond needed for non-classical modal logics.

---

## 1. Upstream Proposition Type

### 1.1 Upstream Primitives

**File**: `upstream/main:Cslib/Logics/Modal/Basic.lean`

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | not (φ : Proposition Atom)
  | and (φ₁ φ₂ : Proposition Atom)
  | diamond (φ : Proposition Atom)
```

Upstream constructors: `{atom, not, and, diamond}` (4 constructors).

### 1.2 Upstream Derived Connectives

| Connective | Definition | Derived From |
|-----------|-----------|-------------|
| `or φ ψ` | `¬(¬φ ∧ ¬ψ)` | not, and |
| `impl φ ψ` | `¬φ ∨ ψ` (i.e., `¬(¬(¬φ) ∧ ¬ψ)`) | not, and, or |
| `iff φ ψ` | `(φ → ψ) ∧ (ψ → φ)` | impl, and |
| `box φ` | `¬◇¬φ` | not, diamond |

**Key observations**:
- Negation (`not`) is a **primitive constructor**, not derived from `imp` and `bot`.
- There is **no** `bot` constructor; falsum is not primitive upstream.
- `diamond` is primitive; `box` is derived as `¬◇¬φ`.
- `imp` (called `impl`) is derived, not primitive.

### 1.3 Upstream Satisfaction

```lean
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => m.v w p
  | .not φ => ¬Satisfies m w φ
  | .and φ₁ φ₂ => Satisfies m w φ₁ ∧ Satisfies m w φ₂
  | .diamond φ => ∃ w', m.r w w' ∧ Satisfies m w' φ
```

- `box_iff_forall` is a **derived theorem** proved via `grind`, not definitional.
- `impl_iff_impl` is also a derived theorem.

### 1.4 Upstream File Scope

Upstream modal logic consists of only **4 files**:
- `Basic.lean` -- Proposition type, Satisfies, axiom validity theorems
- `Cube.lean` -- Modal cube definitions (K, T, B, S4, S5, etc.)
- `Denotation.lean` -- Denotational semantics
- `LogicalEquivalence.lean` -- Logical equivalence with contexts

Notably absent from upstream:
- No `Metalogic/` directory (no proof systems, derivation trees, MCS, completeness)
- No `ProofSystem/` directory
- No `FromPropositional.lean` (no embedding from PL)
- No `Foundations/Logic/Connectives.lean` (no typeclass hierarchy for connectives)
- No `Foundations/Logic/Axioms.lean` (no abstract axiom definitions)

### 1.5 Upstream Has No Connective Typeclasses

The upstream repository has **no** `HasBot`, `HasImp`, `HasBox`, `HasDia`, or any connective typeclass. The `Foundations/Logic/` directory contains only:
- `InferenceSystem.lean`
- `LogicalEquivalence.lean`

The connective typeclass hierarchy (`PropositionalConnectives`, `ModalConnectives`, etc.) is entirely our fork's creation.

---

## 2. Comparison: Our Fork vs. Upstream

### 2.1 Constructor Comparison

| Feature | Our Fork | Upstream |
|---------|----------|----------|
| **Primitives** | `{atom, bot, imp, box}` | `{atom, not, and, diamond}` |
| **Constructor count** | 4 | 4 |
| **Negation** | Derived: `neg φ := imp φ bot` | Primitive: `.not φ` |
| **Falsum** | Primitive: `.bot` | None (no bot constructor) |
| **Implication** | Primitive: `.imp φ ψ` | Derived: `impl φ ψ := ¬φ ∨ ψ` |
| **Conjunction** | Derived: `and φ ψ := ¬(φ → ¬ψ)` | Primitive: `.and φ ψ` |
| **Disjunction** | Derived: `or φ ψ := ¬φ → ψ` | Derived: `or φ ψ := ¬(¬φ ∧ ¬ψ)` |
| **Box** | Primitive: `.box φ` | Derived: `box φ := ¬◇¬φ` |
| **Diamond** | Derived: `diamond φ := ¬□¬φ` | Primitive: `.diamond φ` |
| **Satisfaction cases** | 4 (`atom`, `bot`, `imp`, `box`) | 4 (`atom`, `not`, `and`, `diamond`) |

### 2.2 Design Philosophy Differences

**Our fork** follows the Hilbert-style tradition: `{bot, imp}` as the propositional core, `box` as the modal primitive. This is the standard choice for proof-system work (derivation trees, deduction theorems, completeness proofs). The `imp`+`bot` basis aligns with:
- Mendelson's *Introduction to Mathematical Logic*
- Blackburn, de Rijke, Venema's *Modal Logic* (proof system chapters)
- Church's *Introduction to Mathematical Logic*

**Upstream** follows a semantic/algebraic tradition: `{not, and}` as the propositional core, `diamond` as the modal primitive. This is closer to:
- Boolean algebra presentation (complement + meet)
- HML tradition (diamond as the primitive existential modality)
- Category-theoretic approaches (diamond as the left adjoint)

### 2.3 Implications for Alignment

The two designs are **dual to each other** in a precise sense:
- Our fork: `box` primitive, `diamond` derived via classical duality
- Upstream: `diamond` primitive, `box` derived via classical duality

**This means**: Simply adding `.dia` to our fork does NOT move us toward the upstream design. The upstream would need to add `.box`, and we would need to add `.dia` -- but even then the propositional bases differ completely (`bot`+`imp` vs `not`+`and`).

**Recommendation**: Do NOT attempt upstream alignment. The designs are too different. Instead, extend our fork's signature cleanly to `{atom, bot, imp, box, dia}`, which is a superset of both approaches.

---

## 3. Clean-Break Refactor Strategy

### 3.1 Target Signature

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Proposition Atom)
  | box (φ : Proposition Atom)
  | dia (φ : Proposition Atom)
  deriving DecidableEq, BEq
```

### 3.2 Constructor Name: `dia` not `diamond`

The prior team research recommended `.dia` and the upstream uses `.diamond`. We should use `.dia` for our constructor because:
1. It matches the `HasDia` typeclass convention (parallel to `HasBox`)
2. It keeps the name short (parallel to `box`)
3. The `diamond` abbreviation can be kept for backward compatibility
4. It matches the abbreviation convention used in the literature (`dia` is standard shorthand)

### 3.3 Satisfaction Extension

```lean
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => m.v w p
  | .bot => False
  | .imp φ₁ φ₂ => Satisfies m w φ₁ → Satisfies m w φ₂
  | .box φ => ∀ w', m.r w w' → Satisfies m w' φ
  | .dia φ => ∃ w', m.r w w' ∧ Satisfies m w' φ
```

### 3.4 Backward Compatibility Layer

```lean
/-- Backward-compatible abbreviation: ◇φ via primitive constructor. -/
abbrev Proposition.diamond (φ : Proposition Atom) : Proposition Atom := .dia φ
```

The existing `◇` notation already points to `Proposition.diamond`, so changing the body from `.neg (.box (.neg φ))` to `.dia φ` will update notation transparently.

### 3.5 HasDia Typeclass (Connectives.lean)

```lean
/-- A type has a possibility (diamond) modality. -/
class HasDia (F : Type*) where
  /-- The possibility/diamond modality. -/
  dia : F → F
```

Update `ModalConnectives`:
```lean
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F, HasDia F
```

Register `Modal.Proposition` instance:
```lean
instance : ModalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
  box := .box
  dia := .dia
```

### 3.6 Duality Theorem (New)

The classical duality `◇φ ↔ ¬□¬φ` becomes a **provable theorem** rather than a definitional identity:

```lean
/-- Classical duality: diamond equals negated box of negation. -/
theorem Satisfies.dia_eq_neg_box_neg :
    Satisfies m w (◇φ) ↔ Satisfies m w (.neg (.box (.neg φ))) := by
  simp only [Satisfies]
  constructor
  · intro ⟨w', hr, hs⟩ hbox
    exact hbox w' hr hs
  · intro h
    by_contra hc
    push_neg at hc
    exact h fun w' hr hs => absurd hs (hc w' hr)
```

This preserves all existing proofs that rely on `diamond_iff` -- they just now reference the theorem instead of unfolding `abbrev`.

### 3.7 Axioms.lean Updates

The abstract axioms in `Cslib/Foundations/Logic/Axioms.lean` currently encode diamond as `¬□¬φ` using `HasBot`, `HasImp`, and `HasBox`. With `HasDia`, the axioms B, 5, D should be updated:

**Before** (current):
```lean
protected abbrev AxiomB (φ : F) : F :=
  HasImp.imp φ (HasBox.box
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))
```

**After** (with HasDia):
```lean
protected abbrev AxiomB (φ : F) : F :=
  HasImp.imp φ (HasBox.box (HasDia.dia φ))
```

Similarly for Axiom5 and AxiomD. This dramatically simplifies the axiom expressions and is the core payoff of having `HasDia`.

---

## 4. File-by-File Impact Assessment

### 4.1 Must Change (pattern-match on Proposition)

These files directly pattern-match on the `Proposition` constructors and will need a new `| .dia φ => ...` case.

| File | Pattern-Match Site | Required Change |
|------|-------------------|----------------|
| `Basic.lean` | `Satisfies` definition (line 104-108) | Add `| .dia φ => ∃ w', m.r w w' ∧ Satisfies m w' φ` |
| `Denotation.lean` | `Proposition.denotation` (lines 25-30) | Add `| .dia φ => {w \| ∃ w', m.r w w' ∧ w' ∈ φ.denotation m}` |
| `LogicalEquivalence.lean` | `Proposition.Context` inductive (line 40) | Add `| dia (c : Context Atom)` constructor |
| `LogicalEquivalence.lean` | `Context.fill` (line 51) | Add `| .dia c, φ => .dia (c.fill φ)` case |
| `LogicalEquivalence.lean` | `congruence` proof (line 64) | Add `| dia c ih =>` case |
| `FromPropositional.lean` | `PL.Proposition.toModal` (line 50) | No change needed (PL has no dia constructor) |
| `Metalogic/Soundness.lean` | `soundness` (line 57) | Not a direct pattern-match on Proposition |
| `Metalogic/DerivationTree.lean` | `ModalAxiom.modalB` (line 87) | Update `Proposition.diamond φ` to `Proposition.dia φ` or keep abbrev |

### 4.2 Must Change (Connectives / Axioms infrastructure)

| File | Required Change |
|------|----------------|
| `Foundations/Logic/Connectives.lean` | Add `HasDia` class; extend `ModalConnectives` to include `HasDia` |
| `Foundations/Logic/Axioms.lean` | Simplify `AxiomB`, `Axiom5`, `AxiomD` using `HasDia.dia` |
| `Foundations/Logic/Theorems/Modal/Basic.lean` | Update abstract diamond lemmas to use `HasDia` |
| `Basic.lean` | Change `Proposition.diamond` from `abbrev := .neg (.box (.neg φ))` to `abbrev := .dia φ`; update `ModalConnectives` instance; add `Satisfies.dia_iff` and `Satisfies.dia_eq_neg_box_neg` |

### 4.3 Should Change (use `Proposition.diamond` abbrev)

These files reference `Proposition.diamond` or `◇` but don't pattern-match. They should work unchanged if `diamond` stays as an `abbrev` pointing to `.dia`, but proofs that unfold `diamond` into `neg(box(neg ...))` will need updating.

| File | Usage | Update Needed |
|------|-------|--------------|
| `Basic.lean` | `Satisfies.diamond_iff` (line 115) | Becomes trivial `Iff.rfl` since satisfaction of `.dia` is definitionally `∃ w', ...` |
| `Basic.lean` | `Satisfies.dual` (line 245) | Proof must change: duality is now a theorem, not definitional |
| `Basic.lean` | `Satisfies.t` (line 252) | Uses `diamond_iff`; may need minor adjustments |
| `Basic.lean` | `Satisfies.b` (line 288) | Uses `diamond_iff`; may need minor adjustments |
| `Basic.lean` | `Satisfies.four` (line 313) | Uses `diamond_iff`; may need minor adjustments |
| `Basic.lean` | `Satisfies.five` (line 341) | Uses `diamond_iff`; may need minor adjustments |
| `Basic.lean` | `Satisfies.d` (line 370) | Uses `diamond_iff`; may need minor adjustments |
| `Metalogic/DerivationTree.lean` | `ModalAxiom.modalB` (line 87) | Uses `Proposition.diamond`; works via abbrev |
| `Metalogic/MCS.lean` | `mcs_box_diamond` (line 164) | Uses `Proposition.diamond`; works via abbrev |
| `Metalogic/Completeness.lean` | `canonical_symm`, `canonical_eucl` | Use `Proposition.diamond` in axiom B; works via abbrev |
| All `ProofSystem/Instances/*.lean` | B axiom instances | Use `Proposition.diamond`; works via abbrev |
| All `Metalogic/Systems/*/Soundness.lean` | Soundness proofs | Unfold `diamond` to prove satisfaction; need `dia_eq_neg_box_neg` or direct reasoning |
| All `Metalogic/Systems/*/Completeness.lean` | Completeness proofs | Use `diamond` in MCS membership; mostly works via abbrev |

### 4.4 Impact on Completeness Proofs

The completeness proofs are the most sensitive area. The `truth_lemma` functions pattern-match on `Proposition` constructors:

```lean
| .atom p => ...
| .bot => ...
| .imp φ ψ => ...
| .box φ => ...
```

Each truth lemma will need a new `| .dia φ =>` case. The dia case of the truth lemma is:

```
Satisfies (CanonicalModel Axioms) S (.dia φ) ↔ (.dia φ) ∈ S.val
```

This is the `mcs_dia_witness` lemma identified in prior research. The forward direction (satisfaction implies membership) needs:
- If `∃ T, R S T ∧ φ ∈ T`, then `.dia φ ∈ S`.
- This follows from: if `.dia φ ∉ S`, then `¬.dia φ ∈ S` (MCS maximality), so `□¬φ ∈ S` (by duality as a derived theorem in the proof system), so `∀ T, R S T → ¬φ ∈ T`, contradicting `φ ∈ T`.

The backward direction:
- If `.dia φ ∈ S`, then `∃ T, R S T ∧ φ ∈ T`.
- This is the Existence Lemma for diamond, analogous to `mcs_box_witness`.
- It constructs `W = {ψ | □ψ ∈ S} ∪ {φ}`, proves `W` is consistent, extends to MCS `T`.

**Critically**: This proof requires establishing that `.dia φ ∈ S` implies the consistency of `{ψ | □ψ ∈ S} ∪ {φ}`. The argument uses: if this set is inconsistent, then `{ψ | □ψ ∈ S}` derives `¬φ`, so `□¬φ ∈ S` (by box-lifting). But `.dia φ ∈ S` and `□¬φ ∈ S` together give (via the axiom `◇φ → ¬□¬φ` or its derivable equivalent) that `⊥ ∈ S`, contradicting MCS consistency.

For this argument to go through in the proof system, we need:
- A derivable theorem `◇φ → ¬□¬φ` (this is half of duality).
- This is derivable in any system that has `◇φ` as primitive with the obvious semantics.
- Alternatively, we need a proof-system axiom connecting `dia` and `box`.

**New Proof System Requirement**: The derivation system needs a way to connect `dia` and `box`. Two options:
1. **Add a duality axiom**: `AxiomDual : ModalAxiom (dia φ).imp (.neg (.box (.neg φ)))` and its converse. This is the cleanest approach.
2. **Define the interaction through existing axioms**: This is not possible if `dia` is truly primitive with no axiomatic connection to `box`.

The duality axiom approach is standard in the literature when both operators are primitive.

### 4.5 No Change Expected

| File | Reason |
|------|--------|
| `Cube.lean` | Only uses notation `◇` and named theorems |
| `FromPropositional.lean` | PL has no diamond; the `toModal` function doesn't produce `◇` |

### 4.6 Bimodal Impact

The `Cslib/Logics/Bimodal/` directory has its own `Formula` type with its own `diamond` abbreviation. It is not directly affected by changes to `Modal.Proposition`, but for consistency should eventually be updated similarly. This is out of scope for task 179.

---

## 5. Connectives.lean Alignment

### 5.1 HasDia Design

Upstream has no connective typeclasses at all, so there is no upstream `HasDia` to align with. Our design is:

```lean
/-- A type has a possibility (diamond) modality. -/
class HasDia (F : Type*) where
  /-- The possibility/diamond modality. -/
  dia : F → F
```

This parallels `HasBox` exactly:
- `HasBox.box : F → F` (unary)
- `HasDia.dia : F → F` (unary)

### 5.2 ModalConnectives Update

Current:
```lean
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F
```

Proposed:
```lean
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F, HasDia F
```

This change propagates to:
- `BimodalConnectives` (extends `ModalConnectives`)
- Any formula type that registers as `ModalConnectives` instance
- The `Modal.Proposition` instance itself

### 5.3 Axioms.lean with HasDia

With `HasDia` available, the modal axioms in `Foundations/Logic/Axioms.lean` become dramatically cleaner:

| Axiom | Before (verbose, uses only HasBox) | After (with HasDia) |
|-------|-----|------|
| B: `φ → □◇φ` | `HasImp.imp φ (HasBox.box (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))` | `HasImp.imp φ (HasBox.box (HasDia.dia φ))` |
| 5: `◇φ → □◇φ` | `HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot) (HasBox.box (...))` | `HasImp.imp (HasDia.dia φ) (HasBox.box (HasDia.dia φ))` |
| D: `□φ → ◇φ` | `HasImp.imp (HasBox.box φ) (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)` | `HasImp.imp (HasBox.box φ) (HasDia.dia φ)` |

The Axioms with `HasDia` are far more readable and maintainable.

---

## 6. Refactor Phases (Recommended Implementation Order)

### Phase 1: Foundation Layer
1. Add `HasDia` to `Connectives.lean`
2. Extend `ModalConnectives` to include `HasDia`
3. Update `Axioms.lean` to use `HasDia.dia` in B, 5, D axiom definitions
4. Update `Theorems/Modal/Basic.lean` if needed

### Phase 2: Core Modal Type
5. Add `.dia` constructor to `Proposition` in `Basic.lean`
6. Add `| .dia φ => ∃ w', m.r w w' ∧ Satisfies m w' φ` to `Satisfies`
7. Change `Proposition.diamond` body from `.neg (.box (.neg φ))` to `.dia φ`
8. Add `Satisfies.dia_iff : Satisfies m w (.dia φ) ↔ ∃ w', m.r w w' ∧ Satisfies m w' φ := Iff.rfl`
9. Add classical duality theorem `Satisfies.dia_eq_neg_box_neg`
10. Update `ModalConnectives` instance to include `dia := .dia`
11. Fix `diamond_iff`, `dual`, and all axiom validity proofs (t, b, four, five, d)

### Phase 3: Context and Denotation
12. Add `.dia` case to `Proposition.Context` and `Context.fill` in `LogicalEquivalence.lean`
13. Add `.dia` case to `Proposition.denotation` in `Denotation.lean`
14. Fix `satisfies_mem_denotation` induction (add dia case)

### Phase 4: Proof System
15. Add duality axiom(s) to `ModalAxiom` and `KAxiom` (and all system axiom types)
16. Add `.dia` case to all `truth_lemma` functions
17. Prove `mcs_dia_witness` for each system's completeness proof
18. Update all soundness proofs that unfold diamond

### Phase 5: System-Specific Files (K, T, B, D, S4, S5, etc.)
19. Update each `Systems/*/Completeness.lean` truth lemma
20. Update each `Systems/*/Soundness.lean` axiom soundness proof
21. Update each `ProofSystem/Instances/*.lean` axiom instance

---

## 7. Risk Assessment

### 7.1 Low Risk
- Adding `HasDia` to Connectives.lean (additive change)
- Adding `.dia` constructor (Lean will flag missing cases)
- Updating notation (transparent via abbrev)

### 7.2 Medium Risk
- Completeness proofs: The `mcs_dia_witness` lemma is non-trivial but well-understood
- Soundness proofs: Straightforward but numerous (15 system-specific files)
- Axioms.lean: Changing axiom definitions requires updating all consumers

### 7.3 High Risk
- Duality axiom in proof system: Must decide whether to add explicit `dia ↔ ¬□¬` axiom. Without it, the proof system cannot derive facts about `dia` from `box` or vice versa, breaking completeness.
- `DecidableEq` derivation: Need to verify that adding `.dia` preserves the `deriving DecidableEq, BEq` on `Proposition`. This should work since `.dia` takes a single `Proposition Atom` argument, same as `.box`.

### 7.4 Scope Estimate

| Category | Files | Effort |
|----------|-------|--------|
| Foundation (Connectives, Axioms) | 3-4 | Low |
| Core (Basic, Denotation, LogicalEquivalence) | 3 | Medium |
| Proof System infrastructure | 2-3 | Medium |
| System-specific (15 systems x 2 files) | ~30 | Medium-High (repetitive) |
| FromPropositional | 1 | Low (no dia in PL) |
| **Total** | **~40 files** | **Medium-High** |

---

## 8. Conclusion

The upstream CSLib has a completely different primitive set (`{atom, not, and, diamond}`) from our fork (`{atom, bot, imp, box}`). Attempting upstream alignment is not feasible -- the propositional bases are fundamentally different. The correct strategy is:

1. **Extend our fork** to `{atom, bot, imp, box, dia}` (5 primitives)
2. **Add `HasDia` typeclass** parallel to `HasBox`
3. **Keep `diamond` as abbrev** for backward compatibility
4. **Add duality axiom** to the proof system for completeness
5. **Update all pattern-match sites** (Lean compiler flags these automatically)

This gives us a signature that is a superset of both upstream (`{atom, not, and, diamond}`) and our current fork (`{atom, bot, imp, box}`), positioning us for future work on both classical and non-classical modal logics.
