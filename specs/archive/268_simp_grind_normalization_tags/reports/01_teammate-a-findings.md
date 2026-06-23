# Teammate A (Primary Angle) Research Findings
## Task 268: Add @[simp, scoped grind =] Normalization Tags to Hilbert System Definitional Lemmas

---

## 1. Key Findings

### 1.1 Existing Co-Tagging Convention

CSLib uses `@[simp, scoped grind =]` for **characterization/definitional lemmas** where the LHS is a complex expression that should rewrite to a simpler normal form. The clearest established pattern is in:

**`Cslib/Logics/HML/Basic.lean`** (lines 61, 72, 77, 100, 128):
```lean
@[simp, scoped grind =]
def Proposition.neg (a : Proposition Label) : Proposition Label := ...

@[simp, scoped grind =]
def Proposition.finiteAnd ...

@[simp, scoped grind =]
theorem neg_satisfies ...
```

**`Cslib/Logics/Modal/Basic.lean`** (line 189, 199, 204-232):
```lean
@[simp, scoped grind =]
def Satisfies.Bundled ...

@[scoped grind =]
theorem derivation_def ...  -- Iff characterization

@[scoped grind =]
theorem neg_satisfies, Satisfies.or_iff_or, Satisfies.impl_iff_impl,
        Satisfies.box_iff_forall, Satisfies.diamond_iff_exists, Satisfies.and_iff_and
```

**`Cslib/Logics/Modal/Denotation.lean`** (lines 25, 34, 57):
```lean
@[simp, scoped grind =]
def Proposition.denotation ...

@[scoped grind =]
theorem satisfies_mem_denotation ...

@[scoped grind =]
theorem neg_denotation ...
```

**`Cslib/Logics/Modal/Cube.lean`** (lines 28-84):
```lean
@[scoped grind =]
def K World Atom := logic ...
-- (all 15 modal logic definitions: T, B, Four, Five, K45, D, ...)
```

**Summary of the co-tagging convention**:
- `@[simp, scoped grind =]` on **def** that is an unfolding (works as simp rewrite)
- `@[scoped grind =]` on **theorem** that is an iff/eq (biconditional characterization)
- The distinction: `simp` is added when the definition itself should be unfolded by simp; `scoped grind =` is always paired on definitional/characterization theorems that are iff-shaped

### 1.2 Files with NO simp/grind Tags (Current Gaps)

After surveying all target directories:

#### Propositional (`Cslib/Logics/Propositional/`)
- **`ProofSystem/Derivation.lean`**: `DerivationTree`, `Deriv`, `Derivable`, `mp_deriv`, `weakening_deriv`, `assumption_deriv`, `propDerivationSystem` -- no tags
- **`ProofSystem/Instances.lean`**: Instance registrations -- no tags, and none needed (instances are not lemmas)
- **`ProofSystem/Axioms.lean`**: Not a separate file in PL (axioms are in `Defs.lean` inline)
- **`Defs.lean`**: `isIntuitionisticIff`, `isClassicalIff` -- have `@[scoped grind =]` already (lines 170, 179)

#### Foundations (`Cslib/Foundations/Logic/`)
- **`Metalogic/ListImplication.lean`**: `listImp_nil`, `listImp_cons` -- have `@[simp]` only (lines 51, 54); MISSING `scoped grind =`
- **`Theorems/BigConj.lean`**: `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`, `negBigconj_def` -- have `@[simp]` only; MISSING `scoped grind =`
- **`Theorems/Combinators.lean`**: None of the combinators (`imp_trans`, `identity`, `b_combinator`, etc.) are tagged
- **`Theorems/Propositional/Core.lean`**: None tagged
- **`Theorems/Propositional/Connectives.lean`**: None tagged
- **`Theorems/Temporal/TemporalDerived.lean`**: None tagged
- **`Theorems/Modal/Basic.lean`**: None tagged

#### Temporal (`Cslib/Logics/Temporal/`)
- **`ProofSystem/Derivation.lean`**: Constructors -- should NOT be tagged (see Section 1.4)
- **`ProofSystem/Derivable.lean`**: `ax`, `assume`, `mp`, `temp_nec`, `temp_dual`, `weaken` -- should NOT be tagged
- **`FromPropositional.lean`**: Embedding lemmas have `@[simp]` already (lines 69-92); MISSING `scoped grind =` on some

#### Modal (`Cslib/Logics/Modal/`)
- **`Basic.lean`**: `Satisfies.neg_iff`, `Satisfies.diamond_iff`, `Satisfies.and_iff`, `Satisfies.or_iff` -- NOT tagged (used internally but not exposed)
- **`Basic.lean`** (lines 199-232): Characterization theorems DO have `@[scoped grind =]`
- **`Cube.lean`**: Modal logic definitions (K, T, B, etc.) have `@[scoped grind =]` already (lines 28-84)
- **`Denotation.lean`**: Has `@[simp, scoped grind =]` and `@[scoped grind =]` already

#### Bimodal (`Cslib/Logics/Bimodal/`)
- **`ProofSystem/Substitution.lean`**: Substitution lemmas have `@[simp]` (lines 55-83) but no `scoped grind =`
- No existing `scoped grind` tags in Bimodal at all

### 1.3 Concrete Lemmas TO Tag (Prioritized by Impact)

#### HIGH PRIORITY - listImp equalities (`Foundations/Logic/Metalogic/ListImplication.lean`)

These are structural/definitional equalities that match the HML/Modal co-tag pattern exactly:

```lean
-- Line 51: CURRENTLY @[simp] only -- ADD scoped grind =
@[simp] theorem listImp_nil (φ : F) : listImp ([] : List F) φ = φ

-- Line 54: CURRENTLY @[simp] only -- ADD scoped grind =
@[simp] theorem listImp_cons (ψ : F) (Ψ : List F) (φ : F) :
    listImp (ψ :: Ψ) φ = HasImp.imp ψ (listImp Ψ φ)
```

**Why**: These are definitional unfolding equalities (rfl proofs). They should be co-tagged for grind automation.

#### HIGH PRIORITY - BigConj equalities (`Foundations/Logic/Theorems/BigConj.lean`)

```lean
-- Line 72: CURRENTLY @[simp] only -- ADD scoped grind =
@[simp] theorem bigconj_nil : bigconj ([] : List F) = HasBot.bot

-- Line 76: CURRENTLY @[simp] only -- ADD scoped grind =
@[simp] theorem bigconj_singleton (φ : F) : bigconj [φ] = ...

-- Line 79: CURRENTLY @[simp] only -- ADD scoped grind =
@[simp] theorem bigconj_cons_cons (φ ψ : F) ...

-- Line 87: CURRENTLY @[simp] only -- ADD scoped grind =
@[simp] theorem negBigconj_def (L : List F) : ...
```

#### MEDIUM PRIORITY - Temporal embedding lemmas (`Temporal/FromPropositional.lean`)

These `@[simp]` lemmas lack `scoped grind =`:

```lean
-- Lines 69, 74, 79, 84, 90 -- all have @[simp] but not scoped grind =
@[simp] theorem PL.Proposition.toTemporal_atom
@[simp] theorem PL.Proposition.toTemporal_bot
@[simp] theorem PL.Proposition.toTemporal_imp
@[simp] theorem PL.Proposition.toTemporal_and
@[simp] theorem PL.Proposition.toTemporal_or
```

#### MEDIUM PRIORITY - Modal Satisfies characterizations that should be tagged

In `Cslib/Logics/Modal/Basic.lean`, the internal `Satisfies.*_iff` theorems are used as proof steps but lack grind tags:
```lean
theorem Satisfies.neg_iff : Satisfies m w (¬φ) ↔ ¬Satisfies m w φ
theorem Satisfies.diamond_iff : Satisfies m w (◇φ) ↔ ∃ w', m.r w w' ∧ Satisfies m w' φ
theorem Satisfies.and_iff : Satisfies m w (φ₁ ∧ φ₂) ↔ Satisfies m w φ₁ ∧ Satisfies m w φ₂
theorem Satisfies.or_iff : Satisfies m w (φ₁ ∨ φ₂) ↔ Satisfies m w φ₁ ∨ Satisfies m w φ₂
```
(Note: the `⇓Modal[...]`-wrapped versions in lines 199-232 already have `@[scoped grind =]`)

#### LOW PRIORITY - Propositional Defs.lean isIntuitionisticIff/isClassicalIff

Already have `@[scoped grind =]` (lines 170, 179). No action needed.

### 1.4 Lemmas Explicitly NOT to Tag (Derivability Constructors)

The task explicitly excludes:

**`Temporal/ProofSystem/Derivable.lean`**: `Temporal.Derivable.ax`, `Temporal.Derivable.assume`, `Temporal.Derivable.mp`, `Temporal.Derivable.temp_nec`, `Temporal.Derivable.temp_dual`, `Temporal.Derivable.weaken`, `Temporal.Derivable.lift`

**`Bimodal/ProofSystem/Derivable.lean`**: `Bimodal.Derivable.ax`, `Bimodal.Derivable.assume`, `Bimodal.Derivable.mp`, `Bimodal.Derivable.nec`, `Bimodal.Derivable.temp_nec`, `Bimodal.Derivable.temp_dual`, `Bimodal.Derivable.weaken`, `Bimodal.Derivable.lift`

**`Propositional/ProofSystem/Derivation.lean`**: `mp_deriv`, `weakening_deriv`, `assumption_deriv`, `DerivationTree.height_modus_ponens_left`, etc.

**Why excluded**: These are proof-construction lemmas. Tagging them as simp lemmas would cause simp to unfold derivability goals into their constructors, which breaks proof automation rather than helping it. They are intended as building blocks for the proof-search tactic, not as normalization lemmas.

---

## 2. Recommended Approach

### Phase 1: Co-tag listImp equalities (Highest impact)

In `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/ListImplication.lean`:
- Change `@[simp]` to `@[simp, scoped grind =]` on lines 51 and 54

### Phase 2: Co-tag BigConj equalities

In `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Theorems/BigConj.lean`:
- Change `@[simp]` to `@[simp, scoped grind =]` on lines 72, 76, 79, 87

### Phase 3: Co-tag Temporal embedding lemmas

In `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/FromPropositional.lean`:
- Change `@[simp]` to `@[simp, scoped grind =]` on lines 69, 74, 79, 84, 90

### Phase 4: Add grind tags to Modal Satisfies characterizations

In `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean`:
- Add `@[scoped grind =]` to `Satisfies.neg_iff`, `Satisfies.diamond_iff`, `Satisfies.and_iff`, `Satisfies.or_iff`

### Order Note

The `@[scoped grind =]` attribute will only take effect in files that open the relevant scope (via `open` or `namespace`). The Temporal and Modal logics use scoped notations, so the `scoped grind` attribute is appropriate.

---

## 3. Evidence/Examples of Existing Co-Tagging Patterns

### Pattern A: `@[simp, scoped grind =]` on definitional def

From `HML/Basic.lean`:
```lean
@[simp, scoped grind =]
def Proposition.neg (a : Proposition Label) : Proposition Label :=
  match a with
  | .true => .false
  | .false => .true
  | and a b => or a.neg b.neg
  ...
```
Use case: When you have `neg φ` in a goal, simp/grind can unfold it.

### Pattern B: `@[scoped grind =]` on iff characterization theorem

From `Modal/Basic.lean`:
```lean
@[scoped grind =]
theorem Satisfies.or_iff_or {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∨ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∨ ⇓Modal[m,w ⊨ φ₂] := Satisfies.or_iff
```
Use case: When you have a satisfaction goal with `∨`, grind knows how to split it.

### Pattern C: `@[scoped grind =]` on def (not simp) for unfolding definitions

From `Modal/Cube.lean`:
```lean
@[scoped grind =]
def K World Atom := logic (Set.univ (α := Model World Atom))
```
Note: No `simp` here because unfolding `K` by simp could cause simp loops or explosion.

### Pattern D: Pure `@[simp]` without grind on structural list lemmas

From `Temporal/Syntax/Formula.lean`:
```lean
@[simp]
theorem swapTemporal_someFuture (φ : Formula Atom) :
    (Formula.someFuture φ).swapTemporal = Formula.somePast φ.swapTemporal
```
These are structural equalities that don't need grind because they're only used in `simp only` calls in specific proofs.

### Pattern E: Already co-tagged listImp pattern (the target pattern)

Currently in `ListImplication.lean`, `listImp_nil` and `listImp_cons` have only `@[simp]`. The task wants these upgraded to `@[simp, scoped grind =]` to match the HML/Modal pattern.

---

## 4. What the Task Means by Each Category

### "Derived connective unfoldings"
These are lemmas like `Satisfies.diamond_iff`, `Satisfies.or_iff`, `Satisfies.and_iff` in `Modal/Basic.lean` that characterize derived connectives (`◇`, `∨`, `∧`) in terms of the primitive constructors. The task wants `@[scoped grind =]` added.

### "Context manipulation lemmas"
These likely refer to lemmas about `listImp` (which encodes contexts as list-implications):
- `listImp_nil`: `listImp [] φ = φ`
- `listImp_cons`: `listImp (ψ :: Ψ) φ = ψ → listImp Ψ φ`

These enable grind to reason about proof contexts as formulas.

### "`listImp` equalities"
Confirmed to be `listImp_nil` and `listImp_cons` in `Foundations/Logic/Metalogic/ListImplication.lean`.

### "Structural/characterization lemmas"
These include:
- BigConj lemmas in `Foundations/Logic/Theorems/BigConj.lean`
- The embedding lemmas in `Temporal/FromPropositional.lean`
- Any other `X_def`/`X_iff` type lemmas that characterize compound operators

---

## 5. Files NOT Found (Important Negative Results)

The following files were searched for and confirmed to have **no existing simp/grind tags** that need updating (they have no relevant lemmas for this task):

- `Propositional/ProofSystem/Derivation.lean` -- Only constructors and height measures (excluded)
- `Propositional/ProofSystem/Instances.lean` -- Only typeclass instances (no theorems)
- `Temporal/ProofSystem/Derivation.lean` -- Only constructors (excluded)
- `Temporal/ProofSystem/Derivable.lean` -- Only constructor-mirroring lemmas (excluded)
- `Temporal/ProofSystem/Axioms.lean` -- Only axiom inductive (no lemmas to tag)
- `Temporal/ProofSystem/Instances.lean` -- Only typeclass instances
- `Bimodal/ProofSystem/Derivable.lean` -- Only constructor-mirroring lemmas (excluded)
- `Foundations/Logic/Theorems/Combinators.lean` -- Proof-theoretic combinators (not definitional)
- `Foundations/Logic/Theorems/Propositional/Core.lean` -- Proof-theoretic theorems (not definitional)
- `Foundations/Logic/Theorems/Propositional/Connectives.lean` -- Proof-theoretic theorems
- `Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` -- Generic-typeclass derived theorems
- `Foundations/Logic/Theorems/Modal/Basic.lean` -- Generic-typeclass modal theorems

The combinator/theorem files (Combinators.lean, Core.lean, etc.) should NOT receive simp/grind tags because:
1. They are parameterized by proof system `S`, not definitional equations about formulas
2. They express derivability (type `InferenceSystem.DerivableIn S φ`) not formula equalities
3. Tagging them as simp lemmas would try to rewrite derivability goals, not formula structure

---

## 6. Complete File-by-File Action List

| File | Action | Lemmas |
|------|--------|--------|
| `Foundations/Logic/Metalogic/ListImplication.lean` | Upgrade `@[simp]` to `@[simp, scoped grind =]` | `listImp_nil`, `listImp_cons` |
| `Foundations/Logic/Theorems/BigConj.lean` | Upgrade `@[simp]` to `@[simp, scoped grind =]` | `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`, `negBigconj_def` |
| `Logics/Temporal/FromPropositional.lean` | Upgrade `@[simp]` to `@[simp, scoped grind =]` | `toTemporal_atom`, `toTemporal_bot`, `toTemporal_imp`, `toTemporal_and`, `toTemporal_or` |
| `Logics/Modal/Basic.lean` | Add `@[scoped grind =]` | `Satisfies.neg_iff`, `Satisfies.diamond_iff`, `Satisfies.and_iff`, `Satisfies.or_iff` |

All other files either already have the correct tags, have no relevant lemmas, or have lemmas that should be excluded (derivability constructors).

---

## 7. Confidence Level

**HIGH** for the following conclusions:
- The existing co-tagging convention: `@[simp, scoped grind =]` on definitional unfoldings, `@[scoped grind =]` on iff characterizations
- The listImp and BigConj lemmas are the primary targets (structural equalities missing grind)
- The exclusion of derivability constructors (Derivable.ax, mp, etc.) is architecturally correct

**MEDIUM** for:
- Whether `Satisfies.neg_iff` etc. in `Modal/Basic.lean` should get `@[scoped grind =]` — there are already `@[scoped grind =]` wrappers for the `⇓Modal[...]` notation versions; adding grind to the unwrapped versions may be redundant or beneficial
- Whether the Temporal FromPropositional embedding lemmas need `scoped grind =` (they may only be used in simp-specific proofs)

**LOW** for:
- Whether any Bimodal-specific files have missed definitional lemmas (the Bimodal ProofSystem has no `scoped grind` tags at all, but the `@[simp]` lemmas in `Substitution.lean` are structural and may qualify)
