# Research Report: Task 173 -- Propositional Five-Primitive Refactor

**Task**: Refactor Cslib/Logics/Propositional to the hybrid five-primitive formula type
**Date**: 2026-06-12
**Mode**: CSLib Research (single agent)
**Status**: Researched

---

## Summary

- The current `Proposition` inductive has 3 constructors: `atom`, `bot`, `imp`. Adding `and` and `or` as constructors is a deep structural change affecting 22 files.
- The ND system (`NaturalDeduction/Basic.lean`) has `botE` as an unconditional primitive; the task requires removing it and replacing it with theory-axiom-based explosion, matching upstream Waring.
- The Hilbert axiom hierarchy (`MinPropAxiom`/`IntPropAxiom`/`PropositionalAxiom`) must be extended with 6 new constructors for and/or axioms each.
- All recursive functions on `Proposition` (subst, Evaluate, IForces, toModal, toTemporal, substAtom, etc.) gain 2 new cases.
- The DerivedRules.lean `[IsClassical T]` constraints on andE1/andE2/orE/iffE1/iffE2 become moot because these become primitive ND rules.
- The ND-Hilbert bridge (Equivalence.lean) must be extended with cases for the new ND constructors (andI, andE1, andE2, orI1, orI2, orE).
- Two external embedding files (Modal/FromPropositional.lean, Temporal/FromPropositional.lean) need 2 new cases each.

---

## File-by-File Inventory

### 1. Defs.lean (Cslib/Logics/Propositional/Defs.lean)

**Current state**: 174 lines. `Proposition` inductive with 3 constructors (`atom`, `bot`, `imp`). Derived connectives as `abbrev`s: `neg`, `top`, `or`, `and`, `iff`. Notation instances. `PropositionalConnectives` instance (bot, imp only). `subst` function (3 cases). `Monad` instance. Theory definitions (MPL, IPL, CPL). `IsIntuitionistic`/`IsClassical` theory predicates.

**Changes needed**:
1. Add `and` and `or` constructors to `Proposition` inductive.
2. Change `Proposition.and` and `Proposition.or` from `abbrev` (Lukasiewicz encoding) to the constructors directly. Keep `neg`, `top`, `iff` as `abbrev`s (neg := A -> bot, top := bot -> bot, iff := (A -> B) and (B -> A)).
3. Add `HasAnd` and `HasOr` instances for `Proposition`.
4. Update `PropositionalConnectives` instance (or update once `PropositionalConnectives` extends `HasAnd`/`HasOr`).
5. Extend `subst` with `| and A B => .and (A.subst f) (B.subst f)` and `| or A B => .or (A.subst f) (B.subst f)`.
6. The `Monad` instance relies on `subst` -- automatically updated.

**Risk**: LOW for the formula type change itself. The main risk is cascading changes. The notation declarations for `∧`, `∨` switch from pointing at `abbrev`s to constructors -- the notation strings stay the same.

### 2. NaturalDeduction/Basic.lean

**Current state**: 345 lines. `Theory.Derivation` inductive with 5 constructors: `ax`, `ass`, `impI`, `impE`, `botE`. Operations: `weak`, `cut`, `subs`, `substAtom`. Equivalence definitions.

**Changes needed**:
1. Remove `botE` as a primitive constructor.
2. Add 6 new constructors: `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`. Following upstream Waring's 10-rule system: ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE.
3. Update `weak` to handle all 8 new/changed cases (remove botE case, add andI/andE1/andE2/orI1/orI2/orE cases).
4. Update `subs` for the new cases.
5. Update `substAtom` for the new cases.
6. Update `cut` if it pattern-matches on constructors (currently it uses `impE`/`impI` directly, so may not need deep changes).
7. The `derivationTop` proof needs reworking since it currently uses `impI` + `ass` (which works because `top := bot -> bot`).

**Risk**: HIGH. This is the most complex file. The `weak`, `subs`, and `substAtom` functions all pattern-match on every constructor and must be extended. The removal of `botE` changes the fundamental character of the ND system -- `botE` usages in other files must be replaced with theory-axiom-based reasoning.

**Detailed constructor signatures (upstream-aligned)**:
```lean
| andI {A B} (Γ) : Derivation Γ A -> Derivation Γ B -> Derivation Γ (A ∧ B)
| andE1 {A B} (Γ) : Derivation Γ (A ∧ B) -> Derivation Γ A
| andE2 {A B} (Γ) : Derivation Γ (A ∧ B) -> Derivation Γ B
| orI1 {A B} (Γ) : Derivation Γ A -> Derivation Γ (A ∨ B)
| orI2 {A B} (Γ) : Derivation Γ B -> Derivation Γ (A ∨ B)
| orE {A B C} (Γ) : Derivation Γ (A ∨ B) -> Derivation (insert A Γ) C -> Derivation (insert B Γ) C -> Derivation Γ C
```

Note: NO `botE` primitive rule. Explosion (bot -> A) is obtained by appealing to theory axioms via `ax` when `IsIntuitionistic T` holds.

### 3. NaturalDeduction/DerivedRules.lean

**Current state**: 387 lines. Derived rules for Lukasiewicz-encoded connectives. `andE1`, `andE2`, `orE`, `iffE1`, `iffE2` all require `[IsClassical T]`. `andI`, `orI1`, `orI2`, `negI`, `negE`, `topI`, `dne`, `iffI` do not require classicality.

**Changes needed**:
1. `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE` become trivial one-line wrappers around the new primitive ND constructors. The `[IsClassical T]` constraints on andE1/andE2/orE are removed entirely.
2. `negI` and `negE` remain as-is (they wrap impI/impE since neg := imp A bot).
3. `topI` remains as-is (top := bot -> bot, so impI + ass).
4. `dne` (double negation elimination) now requires `[IsClassical T]` via the theory axiom, not via pattern matching. The implementation changes: instead of `impE (ax (IsClassical.dne A)) d`, it becomes more complex because `botE` is no longer available. But: `dne` can be derived from IsClassical's DNE axiom (which is `(¬¬A → A) ∈ T`). We have `ax (IsClassical.dne A) : T.Derivation Γ (¬¬A → A)`, then `impE` gives us `A` from `¬¬A`. This still works directly -- the DNE axiom IS the implication `¬¬A → A`, so `impE (ax ...) d` works.
5. `iffI` becomes `andI` on `(A → B)` and `(B → A)`.
6. `iffE1` becomes `andE1` on `(A ↔ B)`, and `iffE2` becomes `andE2`. Both lose `[IsClassical T]`.
7. `botE` as a derived rule: With `[IsIntuitionistic T]`, we get `(⊥ → A) ∈ T` via `IsIntuitionistic.efq`. Then `ax (IsIntuitionistic.efq A)` gives a derivation of `⊥ → A`, and `impE` with the bot derivation gives `A`. This should be added as `Theory.Derivation.botE [IsIntuitionistic T]`.

**Risk**: MEDIUM. The logic is straightforward but there are many rules to update and their DerivableIn-level wrappers.

### 4. ProofSystem/Axioms.lean

**Current state**: 106 lines. Three axiom inductives: `PropositionalAxiom` (4 constructors: implyK, implyS, efq, peirce), `IntPropAxiom` (3: implyK, implyS, efq), `MinPropAxiom` (2: implyK, implyS). Subsumption theorems.

**Changes needed**:
1. Add 6 new constructors to each axiom inductive for the and/or axiom schemata:
   - `andI (φ ψ)`: `φ → (ψ → φ ∧ ψ)` (conjunction introduction)
   - `andE1 (φ ψ)`: `φ ∧ ψ → φ` (left elimination)
   - `andE2 (φ ψ)`: `φ ∧ ψ → ψ` (right elimination)
   - `orI1 (φ ψ)`: `φ → φ ∨ ψ` (left introduction)
   - `orI2 (φ ψ)`: `ψ → φ ∨ ψ` (right introduction)
   - `orE (φ ψ χ)`: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))` (elimination)
2. All three axiom sets (Min, Int, Cl) get ALL 6 new constructors, since and/or are structural axioms valid in minimal logic.
3. Update subsumption theorems: `MinPropAxiom.toIntProp` and `IntPropAxiom.toProp` need 6 new cases each.

**Risk**: LOW. Mechanical extension -- add constructors, add cases to subsumption proofs.

### 5. ProofSystem/Derivation.lean

**Current state**: 163 lines. `DerivationTree` inductive (4 constructors: ax, assumption, modus_ponens, weakening). `height`, `Deriv`, `Derivable`, `propDerivationSystem`.

**Changes needed**: NONE. The `DerivationTree` is parameterized over `Axioms` and does not directly reference formula constructors. The new and/or axioms flow through the `Axioms` predicate. `height` handles all trees via 4 structural cases that are formula-agnostic.

**Risk**: NONE.

### 6. ProofSystem/Instances.lean

**Current state**: 91 lines. `InferenceSystem`, `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, and `ClassicalHilbert` instances for `HilbertCl`.

**Changes needed**:
1. Add `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE` instances for `HilbertCl`.
2. These require corresponding `HasAxiom*` typeclasses to exist in `ProofSystem.lean` (Foundations).

**Risk**: LOW, but depends on adding the `HasAxiom*` typeclasses to `Foundations/Logic/ProofSystem.lean` first.

### 7. ProofSystem/IntMinInstances.lean

**Current state**: 109 lines. Instances for `HilbertInt` and `HilbertMin`.

**Changes needed**: Same as Instances.lean -- add and/or axiom instances for both `HilbertInt` and `HilbertMin`.

**Risk**: LOW.

### 8. NaturalDeduction/FromHilbert.lean

**Current state**: 302 lines. ND-flavored wrappers around Hilbert trees. `impI`, `impE`, `botE`, `assume`, `axiomRule`. Cut, weakening, substitution.

**Changes needed**:
1. The `hilbertSubstitution` function matches on `DerivationTree` constructors (ax, assumption, modus_ponens, weakening) -- these do NOT change, so no update needed.
2. `subst_preserves_axiom`, `subst_preserves_intAxiom`, `subst_preserves_minAxiom` need 6 new cases each for the and/or axioms.
3. May want to add and/or wrappers (hilbertAndI, hilbertAndE1, etc.) but these already exist in `HilbertDerivedRules.lean` -- they would become simpler since they'd use the axioms directly.

**Risk**: LOW.

### 9. NaturalDeduction/HilbertDerivedRules.lean

**Current state**: 559 lines. Derived rules for Hilbert system mirroring the ND derived rules. Classical layer requires K, S, EFQ, Peirce.

**Changes needed**:
1. The and/or rules become SIMPLER because they now use axioms directly rather than going through the Lukasiewicz encoding.
2. `hilbertAndI`: use `andI` axiom (`φ → (ψ → φ ∧ ψ)`) with modus ponens. Requires only K+S (for deduction theorem if needed), not EFQ or Peirce.
3. `hilbertAndE1`, `hilbertAndE2`: use `andE1`/`andE2` axioms with modus ponens. No classicality needed.
4. `hilbertOrI1`, `hilbertOrI2`: use `orI1`/`orI2` axioms with modus ponens.
5. `hilbertOrE`: use `orE` axiom. No classicality needed.
6. `hilbertDne` stays as-is (requires Peirce).
7. Iff rules become simpler: `hilbertIffE1`/`hilbertIffE2` use `andE1`/`andE2` directly without Peirce.

**Risk**: MEDIUM. Many functions to rewrite, but they all become dramatically simpler.

### 10. NaturalDeduction/Equivalence.lean

**Current state**: 231 lines. Bridges between Hilbert `DerivationTree` and ND `Theory.Derivation`.

**Changes needed**:
1. `hilbertToND`: Add cases for the new and/or axiom constructors in the Hilbert system. When translating an axiom that proves e.g. `φ → (ψ → φ ∧ ψ)`, need to construct the corresponding ND derivation.
2. `ndToHilbert`: Add cases for the 6 new ND constructors (andI, andE1, andE2, orI1, orI2, orE). Each must be translated to Hilbert derivation trees using the corresponding axiom schemata plus deduction theorem/modus ponens.
3. Remove the `botE` case from `ndToHilbert` since botE is no longer a primitive.
4. The bridge lemma needs updating since the ND theory (`AxiomTheory`) must now include the and/or axioms.

**Risk**: HIGH. The `ndToHilbert` direction is the most complex -- translating `orE` (which has 3 sub-derivations with context manipulation) to Hilbert-style is non-trivial. However, the existing `hilbertOrE` in HilbertDerivedRules.lean already does this, so it can be reused.

### 11. Semantics/Basic.lean

**Current state**: 47 lines. `Evaluate` function (3 cases).

**Changes needed**:
1. Add `| .and a b => Evaluate v a ∧ Evaluate v b` case.
2. Add `| .or a b => Evaluate v a ∨ Evaluate v b` case.

**Risk**: LOW.

### 12. Semantics/Kripke.lean

**Current state**: 134 lines. `IForces` function (3 cases), `iforces_persistence` theorem.

**Changes needed**:
1. Add and/or cases to `IForces`:
   - `| .and φ ψ => IForces v bf w φ ∧ IForces v bf w ψ`
   - `| .or φ ψ => IForces v bf w φ ∨ IForces v bf w ψ`
2. Add and/or cases to `iforces_persistence`:
   - `and`: persistence of both conjuncts (by IH).
   - `or`: persistence of either disjunct (by IH on whichever holds).

**Risk**: LOW.

### 13. Metalogic/Soundness.lean

**Current state**: 88 lines. `prop_axiom_sound` (4 cases), `prop_soundness` (4 cases on DerivationTree).

**Changes needed**:
1. Add 6 cases to `prop_axiom_sound` for the new axiom constructors. Each is straightforward:
   - `andI`: `Evaluate v (φ → (ψ → φ ∧ ψ))` -- intro twice, give pair.
   - `andE1`: `Evaluate v (φ ∧ ψ → φ)` -- project left.
   - etc.
2. `prop_soundness` does NOT need changes -- it matches on `DerivationTree` constructors (ax, assumption, modus_ponens, weakening) which are unchanged.

**Risk**: LOW.

### 14. Metalogic/IntSoundness.lean

**Current state**: 103 lines. `int_axiom_sound` (3 cases), `int_soundness` (4 cases).

**Changes needed**:
1. Add 6 cases to `int_axiom_sound` for and/or axioms. Need to prove each axiom schema is IValid using Kripke semantics with `IForces`.
   - andI validity: straightforward.
   - andE1/andE2 validity: straightforward projection.
   - orI1/orI2 validity: inject into disjunction.
   - orE validity: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))` -- case split on the disjunction. This requires care with persistence in the Kripke setting (the disjunction at a successor world gives either φ or ψ at that world, but the implication hypotheses quantify over all successors).

**Risk**: MEDIUM. The orE case needs careful Kripke reasoning with persistence.

### 15. Metalogic/MinSoundness.lean

**Current state**: 97 lines. `min_axiom_sound` (2 cases), `min_soundness` (4 cases).

**Changes needed**: Add 6 cases to `min_axiom_sound`. Same structure as IntSoundness but for MValid (arbitrary bot_forces).

**Risk**: MEDIUM. Same as IntSoundness.

### 16. Metalogic/Completeness.lean

**Current state**: Pattern-matches on `Proposition` with 3 cases (atom, bot, imp).

**Changes needed**: Add and/or cases to the truth lemma or whatever function matches on formulas.

**Risk**: MEDIUM-HIGH. Completeness proofs are typically the most delicate.

### 17. Metalogic/IntCompleteness.lean

**Changes needed**: Same as Completeness.lean -- add and/or cases.

**Risk**: MEDIUM-HIGH.

### 18. Metalogic/MinCompleteness.lean

**Changes needed**: Same.

**Risk**: MEDIUM-HIGH.

### 19. Metalogic/DeductionTheorem.lean

**Current state**: Pattern-matches on `DerivationTree` constructors (ax, assumption, modus_ponens, weakening).

**Changes needed**: NONE. The deduction theorem works on `DerivationTree` which is formula-agnostic.

**Risk**: NONE.

### 20. Metalogic/MCS.lean, IntLindenbaum.lean, MinLindenbaum.lean

**Changes needed**: These use generic MCS framework. Likely no changes needed unless they reference specific formula structure.

**Risk**: LOW.

### 21. Modal/FromPropositional.lean (EXTERNAL)

**Current state**: `toModal` function with 3 cases (atom, bot, imp).

**Changes needed**: Add `| .and φ₁ φ₂ => .and (φ₁.toModal) (φ₂.toModal)` and `| .or φ₁ φ₂ => .or (φ₁.toModal) (φ₂.toModal)`. BUT: This requires that `Modal.Proposition` ALSO has `and`/`or` constructors (which is task 174/175 scope).

**Risk**: LOW for this task, but creates a dependency. OPTION: temporarily map `and`/`or` via Lukasiewicz encoding until Modal is updated: `| .and φ₁ φ₂ => .imp (.imp φ₁.toModal (.imp φ₂.toModal .bot)) .bot`. Or: defer this file to task 174.

### 22. Temporal/FromPropositional.lean (EXTERNAL)

**Same situation as Modal/FromPropositional.lean.** Needs Temporal.Formula to also have and/or constructors (task 176 scope).

---

## Upstream Comparison

### Waring's ND System (from task 171 research)

Waring's upstream approach uses:
- **Theory-parameterized derivation**: No `botE` primitive. Explosion is obtained by having `(⊥ → A) ∈ T` when the theory is intuitionistic.
- **10 ND rules**: ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE.
- **Theory predicates**: Same `IsIntuitionistic`/`IsClassical` approach as the fork.

The fork's main difference from upstream:
1. **botE as primitive** -- needs removal (task directive).
2. **Lukasiewicz and/or** -- needs replacement with constructors (task directive).
3. **Hilbert system hierarchy** -- the fork has a richer Min/Int/Cl typeclass structure that upstream lacks. Task 173 retains this.

### Key Design Decision: bot as Constructor

The task description specifies keeping `bot` as a constructor (not encoding it as a special atom as upstream does). This is the "one deliberate departure" from upstream. The justification is structural semantics: `bot` has fundamentally different semantic behavior from atoms (it's always false / never forced), so it deserves constructor status.

---

## Impact Analysis: Pattern Match Counts

Functions that pattern-match on `Proposition` constructors and need 2 new cases:

| File | Function | Current Cases | New Cases Needed |
|------|----------|---------------|------------------|
| Defs.lean | `subst` | 3 | +2 (and, or) |
| Semantics/Basic.lean | `Evaluate` | 3 | +2 |
| Semantics/Kripke.lean | `IForces` | 3 | +2 |
| Semantics/Kripke.lean | `iforces_persistence` | 3 | +2 |
| Modal/FromPropositional.lean | `toModal` | 3 | +2 (deferred to task 174) |
| Temporal/FromPropositional.lean | `toTemporal` | 3 | +2 (deferred to task 176) |
| Completeness.lean | truth lemma | 3 | +2 |
| IntCompleteness.lean | truth lemma | 3 | +2 |
| MinCompleteness.lean | truth lemma | 3 | +2 |

Functions that pattern-match on `Theory.Derivation` constructors and need changes:

| File | Function | Current Cases | Changes |
|------|----------|---------------|---------|
| Basic.lean | `weak` | 5 (ax,ass,impI,impE,botE) | -1 (botE) +6 (and/or rules) = 10 |
| Basic.lean | `subs` | 5 | Same |
| Basic.lean | `substAtom` | 5 | Same |
| Equivalence.lean | `hilbertToND` | 4 (ax,ass,impE,weakening) | No direct changes (maps DerivationTree) |
| Equivalence.lean | `ndToHilbert` | 5 (ax,ass,impE,botE,impI) | -1 (botE) +6 (and/or rules) = 10 |

---

## Hilbert Axiom Extension Details

### New Axiom Typeclasses Needed (in Foundations/Logic/ProofSystem.lean)

```lean
class HasAxiomAndI (S : Type*) [HasBot F] [HasImp F] [HasAnd F] [InferenceSystem S F] where
  andI {φ ψ : F} : DerivableIn S (HasImp.imp φ (HasImp.imp ψ (HasAnd.and φ ψ)))

class HasAxiomAndE1 (S : Type*) [HasBot F] [HasImp F] [HasAnd F] [InferenceSystem S F] where
  andE1 {φ ψ : F} : DerivableIn S (HasImp.imp (HasAnd.and φ ψ) φ)

class HasAxiomAndE2 (S : Type*) [HasBot F] [HasImp F] [HasAnd F] [InferenceSystem S F] where
  andE2 {φ ψ : F} : DerivableIn S (HasImp.imp (HasAnd.and φ ψ) ψ)

class HasAxiomOrI1 (S : Type*) [HasBot F] [HasImp F] [HasOr F] [InferenceSystem S F] where
  orI1 {φ ψ : F} : DerivableIn S (HasImp.imp φ (HasOr.or φ ψ))

class HasAxiomOrI2 (S : Type*) [HasBot F] [HasImp F] [HasOr F] [InferenceSystem S F] where
  orI2 {φ ψ : F} : DerivableIn S (HasImp.imp ψ (HasOr.or φ ψ))

class HasAxiomOrE (S : Type*) [HasBot F] [HasImp F] [HasOr F] [InferenceSystem S F] where
  orE {φ ψ χ : F} : DerivableIn S
    (HasImp.imp (HasImp.imp φ χ) (HasImp.imp (HasImp.imp ψ χ) (HasImp.imp (HasOr.or φ ψ) χ)))
```

### New Polymorphic Axiom Abbrevs Needed (in Foundations/Logic/Axioms.lean)

```lean
section AndOrAxioms
variable [HasBot F] [HasImp F] [HasAnd F] [HasOr F]

protected abbrev AndI (φ ψ : F) : F :=
  HasImp.imp φ (HasImp.imp ψ (HasAnd.and φ ψ))

protected abbrev AndE1 (φ ψ : F) : F :=
  HasImp.imp (HasAnd.and φ ψ) φ

protected abbrev AndE2 (φ ψ : F) : F :=
  HasImp.imp (HasAnd.and φ ψ) ψ

protected abbrev OrI1 (φ ψ : F) : F :=
  HasImp.imp φ (HasOr.or φ ψ)

protected abbrev OrI2 (φ ψ : F) : F :=
  HasImp.imp ψ (HasOr.or φ ψ)

protected abbrev OrE (φ ψ χ : F) : F :=
  HasImp.imp (HasImp.imp φ χ) (HasImp.imp (HasImp.imp ψ χ) (HasImp.imp (HasOr.or φ ψ) χ))

end AndOrAxioms
```

### Bundled Class Updates (in Foundations/Logic/ProofSystem.lean)

`MinimalHilbert`, `IntuitionisticHilbert`, and `ClassicalHilbert` all need to extend the new `HasAxiom*` classes. Since and/or axioms are valid even in minimal logic, they go at the `MinimalHilbert` level:

```lean
class MinimalHilbert (S : Type*) [HasBot F] [HasImp F] [HasAnd F] [HasOr F]
    [InferenceSystem S F]
    extends ModusPonens S (F := F),
            HasAxiomImplyK S (F := F),
            HasAxiomImplyS S (F := F),
            HasAxiomAndI S (F := F),
            HasAxiomAndE1 S (F := F),
            HasAxiomAndE2 S (F := F),
            HasAxiomOrI1 S (F := F),
            HasAxiomOrI2 S (F := F),
            HasAxiomOrE S (F := F)
```

**CRITICAL**: This adds `[HasAnd F]` and `[HasOr F]` as requirements to `MinimalHilbert` and all its subclasses. This is a BREAKING CHANGE that propagates to Modal/Temporal/Bimodal Hilbert classes. All downstream formula types that instantiate `ClassicalHilbert` (or any Hilbert subclass) will need `HasAnd`/`HasOr` instances.

**Alternative**: Keep `HasAnd`/`HasOr` OFF the bundled class signature and instead have separate `HasAxiomAndI` etc. instances registered independently. This avoids breaking the modal/temporal/bimodal Hilbert classes until those formula types are updated (tasks 174-176). This is the RECOMMENDED approach for this task.

---

## ND-Hilbert Bridge Feasibility

### Current Bridge Architecture

- `hilbertToND`: DerivationTree -> Theory.Derivation. Straightforward structural translation.
- `ndToHilbert`: Theory.Derivation -> DerivationTree. Uses deduction theorem for impI case, botE maps to EFQ axiom + modus ponens.

### Changes for Level-by-Level Correspondence

The task requires:
- Minimal ND (empty theory) <-> MinimalHilbert
- ND + explosion theory axioms <-> IntuitionisticHilbert
- ND + DNE <-> ClassicalHilbert

**hilbertToND direction** (easier):
- New axiom constructors (andI, andE1, etc.) in the Hilbert system map to corresponding ND rules (which are now primitives).
- The `AxiomTheory` definition already handles this generically.

**ndToHilbert direction** (harder):
- New ND constructors (andI, andE1, andE2, orI1, orI2, orE) map to Hilbert axiom + modus ponens compositions.
- andI: `d1 : Γ ⊢ A`, `d2 : Γ ⊢ B`. Need `Γ ⊢ A ∧ B`. Have axiom `A → (B → A ∧ B)`. Apply d1, then d2. Two modus ponens.
- andE1: `d : Γ ⊢ A ∧ B`. Have axiom `A ∧ B → A`. One modus ponens.
- orE: `d : Γ ⊢ A ∨ B`, `dA : insert A Γ ⊢ C`, `dB : insert B Γ ⊢ C`. Need `Γ ⊢ C`. Use deduction theorem on dA to get `Γ ⊢ A → C` and on dB to get `Γ ⊢ B → C`. Then axiom `(A → C) → ((B → C) → (A ∨ B → C))`. Three modus ponens.

All directions are feasible with the existing deduction theorem + modus ponens infrastructure.

### Level Correspondence

The key insight: the `AxiomTheory` bridges this. For minimal logic:
- `AxiomTheory MinPropAxiom` includes K, S, and the 6 new and/or axioms.
- `Theory.Derivation (AxiomTheory MinPropAxiom)` has access to ax (for theory membership) + 10 rules.
- The Hilbert side has `DerivationTree MinPropAxiom` with the same axiom set.

For intuitionistic logic:
- `AxiomTheory IntPropAxiom` adds EFQ to the above.
- On the ND side, EFQ in the theory gives `botE`-equivalent power via `ax + impE`.

For classical logic:
- `AxiomTheory PropositionalAxiom` adds Peirce.

This architecture already works -- the existing `hilbert_iff_nd` theorem structure accommodates it. The extensions are mechanical.

---

## DerivedRules [IsClassical T] Cleanup

The specific constraints to remove:

| Rule | Line | Current Constraint | New Status |
|------|------|--------------------|------------|
| `andE1` | 143 | `[IsClassical T]` | Primitive ND rule (no constraint) |
| `andE2` | 174 | `[IsClassical T]` | Primitive ND rule (no constraint) |
| `orE` | 232 | `[IsClassical T]` | Primitive ND rule (no constraint) |
| `iffE1` | 289 | `[IsClassical T]` | Uses `andE1` (no constraint) |
| `iffE2` | 299 | `[IsClassical T]` | Uses `andE2` (no constraint) |
| `dne` | 129 | `[IsClassical T]` | KEEP -- requires classical theory axiom |
| DerivableIn wrappers | 331-385 | Various `[IsClassical T]` | Remove where base rule loses constraint |

---

## Connectives.lean Status (from Task 172)

Task 172 added `HasAnd` and `HasOr` as standalone typeclasses in `Connectives.lean` and removed `ImpBotDerived`. The `PropositionalConnectives` class currently extends ONLY `HasBot` and `HasImp`. The docstring explicitly says extending to include `HasAnd`/`HasOr` is "deferred to task 173."

**Decision for task 173**: Either:
(a) Extend `PropositionalConnectives` to include `HasAnd` and `HasOr` (adds them to Modal/Temporal/Bimodal connective classes too -- acceptable since those tasks 174-176 will add constructors).
(b) Keep `PropositionalConnectives` as-is and register `HasAnd`/`HasOr` instances independently on `Proposition`.

Option (a) is cleaner long-term but creates a compilation dependency: Modal/Temporal/Bimodal formula types must register `HasAnd`/`HasOr` instances even before their constructors are added (pointing to the Lukasiewicz abbrevs temporarily). Option (b) is safer for this task but leaves `PropositionalConnectives` incomplete.

**Recommendation**: Option (b) for this task. Register `HasAnd`/`HasOr` on `Proposition` directly. Extending `PropositionalConnectives` is task 174-176 scope.

---

## Risk Assessment and Ordering

### Dependency Graph

```
Phase 1 (Foundations, no downstream breakage):
  1a. Axioms.lean (Foundations) -- add polymorphic and/or axiom abbrevs
  1b. ProofSystem.lean (Foundations) -- add HasAxiom* typeclasses (standalone, NOT in bundled classes yet)

Phase 2 (Formula type change -- causes cascading breaks):
  2a. Defs.lean -- add and/or constructors, update subst, register HasAnd/HasOr instances
  2b. Semantics/Basic.lean -- add Evaluate cases
  2c. Semantics/Kripke.lean -- add IForces cases + persistence

Phase 3 (Axiom system extension):
  3a. Axioms.lean (Propositional) -- add and/or axiom constructors to all 3 inductives
  3b. Instances.lean -- add HasAxiom* instances for HilbertCl
  3c. IntMinInstances.lean -- add HasAxiom* instances for HilbertInt and HilbertMin

Phase 4 (ND system overhaul):
  4a. Basic.lean (ND) -- remove botE, add 6 new constructors, update weak/subs/substAtom
  4b. DerivedRules.lean -- rewrite rules as wrappers around new primitives

Phase 5 (Bridge and metalogic):
  5a. FromHilbert.lean -- update subst_preserves_* theorems
  5b. HilbertDerivedRules.lean -- simplify and/or rules
  5c. Equivalence.lean -- add new cases to hilbertToND and ndToHilbert
  5d. DeductionTheorem.lean -- no changes needed (formula-agnostic)

Phase 6 (Soundness/Completeness):
  6a. Soundness.lean -- add axiom soundness cases
  6b. IntSoundness.lean -- add axiom soundness cases
  6c. MinSoundness.lean -- add axiom soundness cases
  6d. Completeness.lean -- add truth lemma cases
  6e. IntCompleteness.lean -- add truth lemma cases
  6f. MinCompleteness.lean -- add truth lemma cases

Phase 7 (External embeddings -- may defer):
  7a. Modal/FromPropositional.lean -- add and/or cases (or defer to task 174)
  7b. Temporal/FromPropositional.lean -- add and/or cases (or defer to task 176)
```

### Estimated Complexity

| Phase | Files | Est. Lines Changed | Difficulty |
|-------|-------|-------------------|------------|
| 1 | 2 | ~60 | Low |
| 2 | 3 | ~30 | Low |
| 3 | 3 | ~100 | Low |
| 4 | 2 | ~300 | High |
| 5 | 3 | ~200 | High |
| 6 | 6 | ~150 | Medium-High |
| 7 | 2 | ~20 | Low (if deferred, 0) |

**Total estimated**: ~860 lines changed/added across ~21 files.

### Risk Matrix

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Completeness proofs break | High | Medium | Phase 6 allocated separately; existing proofs provide structure |
| Bundled class cascade | High | Low | Recommendation: keep HasAxiom* standalone, not in bundled classes |
| Embedding breakage | Medium | High | Defer Modal/Temporal embeddings to tasks 174/176 |
| ND botE removal breaks Basic.lean | High | Medium | Careful refactor; botE becomes derived rule under IsIntuitionistic |
| orE Kripke soundness | Medium | Medium | Well-known proof structure; persistence handles it |

---

## Upstream Compatibility Notes

1. The 10-rule ND system (ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE) matches upstream Waring exactly for the minimal case.
2. The theory-predicate approach for explosion/DNE matches upstream exactly.
3. The Hilbert system hierarchy (Min/Int/Cl) is a fork addition not present upstream. This is explicitly retained per task directive.
4. Keeping `bot` as constructor (vs upstream's atom trick) is the documented deliberate departure.
5. The `iff` encoding as `(A → B) ∧ (B → A)` using the NEW and constructor is correct for all three logics.

---

## Open Questions for Planning

1. **External embeddings**: Should Modal/FromPropositional.lean and Temporal/FromPropositional.lean be updated in this task (mapping and/or via Lukasiewicz to the 3-constructor target types) or deferred to tasks 174/176?

2. **PropositionalConnectives extension**: Should this task also extend the bundled class to include `HasAnd`/`HasOr`, or leave that for the formula type propagation tasks?

3. **Phase sizing**: The 7-phase plan above totals ~860 lines of changes. Should this be split into sub-tasks or handled as a single large implementation with multiple phases?

---

## References

- Task 171 research report: `specs/171_research_connective_basis_min_int_classical/reports/01_team-research.md`
- Connectives.lean: `Cslib/Foundations/Logic/Connectives.lean`
- ProofSystem.lean: `Cslib/Foundations/Logic/ProofSystem.lean`
- Axioms.lean (Foundations): `Cslib/Foundations/Logic/Axioms.lean`
- All 22 files under `Cslib/Logics/Propositional/`
