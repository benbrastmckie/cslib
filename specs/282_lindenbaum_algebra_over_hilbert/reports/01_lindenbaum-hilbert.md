# Research Report: Lindenbaum Algebra Over Hilbert Derivations

**Task**: 282 — Rebuild the Lindenbaum algebra construction over Hilbert derivations instead of ND  
**Session**: sess_1782187168_2b1b69_282  
**Chain Position**: 281 (done) -> **282** -> 283 -> 284 -> 285

## 1. Current Lindenbaum Architecture

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean`  
**Import**: `Cslib.Logics.Propositional.NaturalDeduction.DerivedRules` + `Mathlib.Order.Heyting.Regular`  
**Namespace**: `Cslib.Logic.PL`

### 1.1 Quotient Type

```lean
abbrev LindenbaumAlgebra (T : Theory Atom) : Type u :=
  Quotient (T.propositionSetoid)
```

The setoid `Theory.propositionSetoid` is defined in `NaturalDeduction/Basic.lean` (line 416) as:

```lean
protected def propositionSetoid (T : Theory Atom) : Setoid (Proposition Atom) :=
  ⟨T.Equiv, T.equiv_equivalence⟩
```

Where `T.Equiv A B := Nonempty (T.equiv A B)` and `T.equiv A B := T↓({A} ⊢ B) × T↓({B} ⊢ A)`.

**Key observation**: The equivalence relation `T.Equiv` is defined using ND `DerivableIn T ({A} ⊢ B)` (Finset-based contexts). The quotient ordering `lindenbaumLe` also uses `DerivableIn T ({A} ⊢ B)`.

### 1.2 Lattice Operations

| Operation | Definition | Type |
|-----------|-----------|------|
| `lindenbaumMk T A` | `Quotient.mk T.propositionSetoid A` | Quotient map |
| `lindenbaumLe T x y` | `Quotient.liftOn₂ ... (fun A B => DerivableIn T ({A} ⊢ B))` | Order |
| `lindenbaumSup T x y` | `Quotient.lift₂ (fun A B => lindenbaumMk T (.or A B)) ...` | Join |
| `lindenbaumInf T x y` | `Quotient.lift₂ (fun A B => lindenbaumMk T (.and A B)) ...` | Meet |
| `lindenbaumHimp T x y` | `Quotient.lift₂ (fun A B => lindenbaumMk T (.imp A B)) ...` | Heyting implication |
| Top | `lindenbaumMk T (.imp .bot .bot)` | Top element |
| Bot (intuitionistic) | `lindenbaumMk T .bot` | Bottom element |

### 1.3 Typeclass Instances

| Instance | Requirement | Key proofs |
|----------|-------------|------------|
| `GeneralizedHeytingAlgebra` | Any `T` | All `lindenbaumLe_*`, `lindenbaumSup_le`, `lindenbaumLe_inf`, `lindenbaumLe_himp_iff`, `lindenbaumLe_top` |
| `HeytingAlgebra` | `[IsIntuitionistic T]` | `lindenbaumBot_le` + `himp_bot` |
| `BooleanAlgebra` | `[IsIntuitionistic T] [IsClassical T]` | `lindenbaumEM`, `lindenbaumRegular`, via `BooleanAlgebra.ofRegular` |

### 1.4 ND Rules Used in Each Proof

| Lindenbaum Proof | ND Rules Used |
|-----------------|---------------|
| `lindenbaumLe` well-defined | `DerivableIn.cut`, `DerivableIn.weakCtx` |
| `lindenbaumLe_refl` | `Derivation.ass` |
| `lindenbaumLe_trans` | `DerivableIn.cut_away`, `DerivableIn.weakCtx` |
| `lindenbaumLe_antisymm` | `Quotient.sound`, `Theory.equiv_iff` |
| `lindenbaumLe_sup_left` | `Derivation.orI1`, `Derivation.ass` |
| `lindenbaumLe_sup_right` | `Derivation.orI2`, `Derivation.ass` |
| `lindenbaumSup_le` | `Derivation.orE`, `DerivableIn.weakCtx` |
| `lindenbaumInf_le_left` | `Derivation.andE1`, `Derivation.ass` |
| `lindenbaumInf_le_right` | `Derivation.andE2`, `Derivation.ass` |
| `lindenbaumLe_inf` | `Derivation.andI`, `Classical.choice` |
| `lindenbaumLe_himp_iff` | `Derivation.andE1`, `Derivation.andE2`, `Derivation.impI`, `Derivation.impE`, `Derivation.andI`, `DerivableIn.cut_away` |
| `lindenbaumLe_top` | `Derivation.impI`, `Derivation.ass` |
| `lindenbaumBot_le` | `Derivation.botE` (requires `[IsIntuitionistic T]`) |
| `lindenbaumEM` | `Derivation.impI`, `Derivation.impE`, `Derivation.orI1`, `Derivation.orI2`, `Derivation.dne` |
| Well-definedness of sup/inf/himp | `Equiv.or_congr`, `Equiv.and_congr`, `Equiv.imp_congr` |
| `nontrivialOfConsistent` | `Theory.derivationTop`, `DerivableIn.cut`, `DerivableIn.weakCtx` |

## 2. Hilbert Derivation Infrastructure

### 2.1 Core Types (in `ProofSystem/Derivation.lean`)

```lean
inductive DerivationTree (Axioms : PL.Proposition Atom → Prop) :
    List (PL.Proposition Atom) → PL.Proposition Atom → Type _ where
  | ax | assumption | modus_ponens | weakening

def Deriv (Axioms) (Γ : List (PL.Proposition Atom)) (φ) : Prop :=
  Nonempty (DerivationTree Axioms Γ φ)

def Derivable (Axioms) (φ) : Prop := Deriv Axioms [] φ
```

Key difference from ND: contexts are `List (PL.Proposition Atom)` not `Finset`.

### 2.2 Axiom Predicates

| Predicate | Axioms | Use |
|-----------|--------|-----|
| `MinPropAxiom` | K, S, andI/E1/E2, orI1/I2/E | Minimal logic |
| `IntPropAxiom` | MinPropAxiom + EFQ | Intuitionistic logic |
| `PropositionalAxiom` | IntPropAxiom + Peirce | Classical logic |

### 2.3 Structural Rules (in `FromHilbert.lean`)

| Rule | Type | Axiom Requirements |
|------|------|-------------------|
| `impI` (deduction theorem) | `DerivationTree Axioms (A :: Γ) B → DerivationTree Axioms Γ (A → B)` | K, S |
| `impE` (modus ponens) | Direct wrapper around `modus_ponens` constructor | None |
| `botE` | `DerivationTree Axioms Γ ⊥ → DerivationTree Axioms Γ A` | EFQ |
| `hilbertCut` | `Γ ⊢ A → (A :: Δ) ⊢ B → (Γ ++ Δ) ⊢ B` | K, S |
| `hilbertWeakening` | Direct wrapper around `weakening` constructor | None |

### 2.4 Derived Rules (in `HilbertDerivedRules.lean`)

All `hilbert*` rules from task 281 are available at both `DerivationTree` and `Deriv` levels:

| Rule | DerivationTree level | Deriv level | Requirements |
|------|---------------------|-------------|--------------|
| `hilbertAndI` | Yes | `hilbertAndIDeriv` | andI axiom |
| `hilbertAndE1` | Yes | `hilbertAndE1Deriv` | andE1 axiom |
| `hilbertAndE2` | Yes | `hilbertAndE2Deriv` | andE2 axiom |
| `hilbertOrI1` | Yes | `hilbertOrI1Deriv` | orI1 axiom |
| `hilbertOrI2` | Yes | `hilbertOrI2Deriv` | orI2 axiom |
| `hilbertOrE` | Yes | `hilbertOrEDeriv` | K, S, orE |
| `hilbertImpI` | Yes | `hilbertImpIDeriv` | K, S |
| `hilbertImpE` | Yes | `hilbertImpEDeriv` | None |
| `hilbertBotE` | Yes | `hilbertBotEDeriv` | EFQ |
| `hilbertDne` | Yes | `hilbertDneDeriv` | K, S, EFQ, Peirce |
| `hilbertNegI` | Yes | `hilbertNegIDeriv` | K, S |
| `hilbertNegE` | Yes | `hilbertNegEDeriv` | None |
| `hilbertTopI` | Yes | `hilbertTopIDeriv` | EFQ |
| `hilbertIffI` | Yes | `hilbertIffIDeriv` | andI |
| `hilbertIffE1` | Yes | `hilbertIffE1Deriv` | andE1 |
| `hilbertIffE2` | Yes | `hilbertIffE2Deriv` | andE2 |

### 2.5 SetDerivable (in `Semantics/SemanticConsequence.lean`)

```lean
def SetDerivable (Axioms : PL.Proposition Atom → Prop)
    (Γ : Set (PL.Proposition Atom)) (φ : PL.Proposition Atom) : Prop :=
  ∃ L : List (PL.Proposition Atom),
    (∀ x ∈ L, x ∈ Γ) ∧ (propDerivationSystem Axioms).Deriv L φ
```

This is the set-based (infinite context) version of Hilbert derivability.

## 3. Bridge Theorems

### 3.1 Core Equivalence (`NaturalDeduction/Equivalence.lean`)

The `MinimalAxioms` typeclass bundles 8 axiom witnesses (K, S, andI, andE1, andE2, orI1, orI2, orE). Instances exist for `MinPropAxiom`, `IntPropAxiom`, and `PropositionalAxiom`.

**Primary bridge** (context-based):
```lean
theorem hilbert_iff_nd_ctx [MinimalAxioms Axioms] {Γ : Ctx Atom} {φ} :
    Deriv Axioms Γ.toList φ ↔ DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ)
```

**Closed-context specializations**:
```lean
theorem hilbert_iff_nd_min : Derivable MinPropAxiom φ ↔ DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)
theorem hilbert_iff_nd_int : Derivable IntPropAxiom φ ↔ DerivableIn (AxiomTheory IntPropAxiom) (∅ ⊢ φ)
theorem hilbert_iff_nd_cl  : Derivable PropositionalAxiom φ ↔ DerivableIn (AxiomTheory PropositionalAxiom) (∅ ⊢ φ)
```

**Important limitation**: The bridge is between `Deriv Axioms Γ.toList φ` and `DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ)`, NOT between `Deriv Axioms [A] φ` and `DerivableIn T ({A} ⊢ φ)` for arbitrary theory `T`. The ND side always uses `AxiomTheory Axioms` as its theory, not the arbitrary `T` that parameterizes the Lindenbaum algebra.

### 3.2 Gap Analysis

The current Lindenbaum algebra is parameterized over an arbitrary theory `T : Theory Atom`. The ND equivalence relation `T.Equiv` uses `DerivableIn T ({A} ⊢ B)` where `T` can be any set of propositions.

The bridge theorems connect `Deriv Axioms Γ.toList φ` to `DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ)`. This means:

1. **For `T = AxiomTheory Axioms`**: The bridge works directly. We can define a Hilbert equivalence `Deriv Axioms [A] B ∧ Deriv Axioms [B] A` and show it equals the ND equivalence under `AxiomTheory Axioms`.

2. **For arbitrary `T`**: No direct bridge exists. The existing Lindenbaum is parameterized over `T`, but Hilbert `Deriv` is parameterized over `Axioms`. There is no mechanism to go from `DerivableIn T ({A} ⊢ B)` to `Deriv Axioms [A] B` for a general theory `T` that may not equal `AxiomTheory Axioms`.

## 4. Approach Analysis

### Option A: Pure Hilbert Lindenbaum (From Scratch)

**Idea**: Define a new quotient using a Hilbert-native equivalence relation, define all operations in terms of `Deriv`, prove all GHA/HA/BA instances from scratch using `hilbert*` derived rules.

**New type**:
```lean
def HilbertEquiv (Axioms : PL.Proposition Atom → Prop) (A B : Proposition Atom) : Prop :=
  Deriv Axioms [A] B ∧ Deriv Axioms [B] A

def hilbertPropositionSetoid (Axioms) : Setoid (Proposition Atom) := ...

abbrev HilbertLindenbaumAlgebra (Axioms) : Type u :=
  Quotient (hilbertPropositionSetoid Axioms)
```

**Advantages**:
- Clean, self-contained Hilbert presentation
- No dependency on ND bridge theorems
- Directly uses the `Deriv` / `DerivationTree` types that the task chain (282-285) wants to standardize on

**Disadvantages**:
- Must re-prove ALL 15+ lemmas from scratch using Hilbert structural rules
- The proofs will be verbose because Hilbert derivation trees require explicit axiom parameters at every step
- The equivalence relation is parameterized over `Axioms` not `T`, which changes the API surface
- Context representation difference: Hilbert uses `List`, ND uses `Finset`
- `hilbertOrE` and `hilbertImpI` are `noncomputable` (due to deduction theorem), which may cause issues

**Proof effort per lemma** (using `Deriv`-level `hilbert*Deriv` rules):
- `lindenbaumLe_refl`: `assumption_deriv` (trivial)
- `lindenbaumLe_trans`: needs `hilbertCutDeriv` + `hilbertWeakeningDeriv`
- `lindenbaumLe_sup_left`: `hilbertOrI1Deriv` + `assumption_deriv`
- `lindenbaumSup_le`: `hilbertOrEDeriv` + `hilbertWeakeningDeriv`
- `lindenbaumLe_himp_iff`: `hilbertImpIDeriv` + `hilbertImpEDeriv` + `hilbertAndI/E1/E2Deriv` + `hilbertCutDeriv`
- `lindenbaumEM`: `hilbertDneDeriv` + multiple `hilbertImpI/EDeriv` + `hilbertOrI1/I2Deriv`

**Verdict**: Feasible but high effort. Every proof must be rewritten. Estimated 300-400 lines.

### Option B: Redefine Quotient, Use Bridge for Proofs

**Idea**: Define the Hilbert equivalence and quotient, then use `hilbert_iff_nd_ctx` to translate each proof obligation to the ND system, reuse existing ND Lindenbaum proofs.

**Problem**: The bridge requires `Axioms` and connects to `AxiomTheory Axioms`, but the current Lindenbaum uses arbitrary `T`. The bridge only works when `T = AxiomTheory Axioms`. This means we must either:
- Restrict the Hilbert Lindenbaum to `AxiomTheory Axioms` theories (losing generality)
- Or prove a more general bridge theorem (significant additional work)

**Verdict**: Works but only for `T = AxiomTheory Axioms`. Loses the generality of the current construction.

### Option C: Keep ND Lindenbaum Internal, Add Hilbert Wrappers

**Idea**: The existing ND Lindenbaum stays as-is (parameterized over `T`). New Hilbert-facing API is added as a thin wrapper layer that provides Hilbert-typed access to the same quotient and instances.

The wrapper translates between `Deriv Axioms [A] B` and `DerivableIn (AxiomTheory Axioms) ({A} ⊢ B)` using the bridge theorems. The quotient type, lattice operations, and typeclass instances remain the same -- only new `simp` lemmas and API entrypoints are added.

**New lemmas**:
```lean
theorem lindenbaumMk_le_mk_hilbert [MinimalAxioms Axioms] (A B : Proposition Atom) :
    lindenbaumMk (AxiomTheory Axioms) A ≤ lindenbaumMk (AxiomTheory Axioms) B ↔
    Deriv Axioms [A] B := ...
```

**Advantages**:
- Minimal code change
- Preserves all existing downstream users
- Keeps generality over arbitrary `T`

**Disadvantages**:
- Not truly "over Hilbert" -- the core construction still uses ND
- The Hilbert API is restricted to `AxiomTheory Axioms` theories
- Does not fulfill the task requirement to "redefine using Hilbert SetDerivable/Deriv"

**Verdict**: Insufficient for the task description. The task explicitly says "redefine using Hilbert".

### Recommended Approach: Option A (Pure Hilbert) with Strategic Design

The task description is clear: "Redefine using Hilbert SetDerivable/Deriv". Option A is the correct approach.

**Key design decisions**:

1. **Parameterize over `Axioms` with `[MinimalAxioms Axioms]`**: This bundles all 8 axiom witnesses, avoiding 8 explicit parameters in every definition. The three tiers (min/int/cl) get instances for free.

2. **Use `Deriv`-level rules** (not `DerivationTree`-level): The `Deriv` wrappers are `Prop`-level, matching the `Prop`-level `Nonempty` pattern used in the Lindenbaum construction. This avoids `Classical.choice` extraction of `DerivationTree` values.

3. **Context representation**: Use `List` contexts directly (the Hilbert native). The equivalence relation becomes `Deriv Axioms [A] B ∧ Deriv Axioms [B] A`, using singleton lists `[A]` instead of singleton finsets `{A}`.

4. **Bridge for verification**: After constructing the Hilbert Lindenbaum, prove `HilbertLindenbaumAlgebra Axioms ≃ LindenbaumAlgebra (AxiomTheory Axioms)` as a verification step. This confirms the two constructions agree.

5. **Noncomputability**: The `hilbertImpI`/`hilbertOrE` rules are `noncomputable`, so the Hilbert Lindenbaum proofs using them will also be `noncomputable`. This is acceptable -- the existing ND Lindenbaum already uses `Classical.choice`.

## 5. Dependency Map

### 5.1 Direct Importers of Lindenbaum.lean

| File | Usage |
|------|-------|
| `Semantics/Algebra/Completeness.lean` | `canonicalV`, `canonicalBotVal`, `lindenbaumMk`, typeclass instances for GHA/HA/BA |

### 5.2 Transitive Importers

| File | Chain |
|------|-------|
| `Semantics/Algebra/HilbertCompleteness.lean` | imports Completeness, Soundness, Bridge, Equivalence |
| `Semantics/Algebra/Conservative.lean` | imports Completeness |
| `Semantics/Algebra/Glivenko.lean` | imports Completeness |
| `Semantics/Algebra/KripkeBridge.lean` | imports Completeness |

### 5.3 Files That Do NOT Import Lindenbaum.lean

The `Metalogic/IntLindenbaum.lean` and `Metalogic/MinLindenbaum.lean` files are about Lindenbaum's *lemma* (extending consistent sets to MCS), NOT the Lindenbaum *algebra*. They do not import the algebra file.

### 5.4 Bimodal Lindenbaum (Separate)

The bimodal logic has its own `LindenbaumQuotient` in `Cslib/Logics/Bimodal/Metalogic/Algebraic/`. This is a separate construction over bimodal formulas and does not import the propositional Lindenbaum.

## 6. Implementation Roadmap

### Phase 1: Hilbert Equivalence Relation and Quotient Type

**New file**: `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean`

1. Define `HilbertEquiv Axioms A B := Deriv Axioms [A] B ∧ Deriv Axioms [B] A`
2. Prove it is an equivalence relation (using `assumption_deriv`, `hilbertCutDeriv`, `hilbertWeakeningDeriv`)
3. Define `hilbertPropositionSetoid Axioms`
4. Define `HilbertLindenbaumAlgebra Axioms`
5. Define `hilbertLindenbaumMk`

### Phase 2: Lattice Operations

1. Define `hilbertLindenbaumLe` using `Deriv Axioms [A] B`
2. Prove well-definedness (needs `hilbertCutDeriv`, `hilbertWeakeningDeriv`)
3. Define `hilbertLindenbaumSup`, `hilbertLindenbaumInf`, `hilbertLindenbaumHimp`
4. Prove well-definedness via congruence lemmas (needs Hilbert-level congruence for or/and/imp)
5. Prove simp lemmas

### Phase 3: GHA Instance

Prove all 12 axioms of `GeneralizedHeytingAlgebra`:
- `le_refl`, `le_trans`, `le_antisymm`
- `le_sup_left`, `le_sup_right`, `sup_le`
- `inf_le_left`, `inf_le_right`, `le_inf`
- `le_himp_iff`
- `le_top`

### Phase 4: HA Instance (Intuitionistic)

1. Define `Bot` instance requiring EFQ axiom
2. Prove `bot_le` using `hilbertBotEDeriv`
3. Prove `himp_bot`

### Phase 5: BA Instance (Classical)

1. Prove `hilbertLindenbaumEM` using `hilbertDneDeriv`
2. Prove `hilbertLindenbaumRegular`
3. Apply `BooleanAlgebra.ofRegular`

### Phase 6: Bridge Verification

1. Prove `HilbertLindenbaumAlgebra Axioms ≃ LindenbaumAlgebra (AxiomTheory Axioms)` (order isomorphism)
2. Prove the Hilbert-native simp lemma: `hilbertLindenbaumMk A ≤ hilbertLindenbaumMk B ↔ Deriv Axioms [A] B`

## 7. Key Technical Challenges

### 7.1 Congruence Lemmas for Hilbert

The existing congruence lemmas (`Equiv.or_congr`, `Equiv.and_congr`, `Equiv.imp_congr`) are in the ND system. We need Hilbert versions:

```lean
theorem HilbertEquiv.or_congr [MinimalAxioms Axioms]
    (hA : HilbertEquiv Axioms A A') (hB : HilbertEquiv Axioms B B') :
    HilbertEquiv Axioms (A ∨ B) (A' ∨ B') := ...
```

These need: `hilbertOrEDeriv`, `hilbertOrI1Deriv`, `hilbertOrI2Deriv`, `hilbertWeakeningDeriv`, `hilbertCutDeriv`.

### 7.2 Context Manipulation

The Hilbert system uses `List` contexts, so `[A]` means `[A]` (a singleton list). Cut and weakening work with `List.mem` and `List.append`. The context manipulation is different from the Finset-based ND system but structurally parallel.

### 7.3 Axiom Parameter Threading

With `[MinimalAxioms Axioms]`, the 8 axiom witnesses are available via typeclass resolution (e.g., `MinimalAxioms.h_K`). However, the `hilbert*Deriv` rules take explicit parameters. We need either:
- Extract axiom witnesses from the typeclass in each proof: `MinimalAxioms.h_K`, `MinimalAxioms.h_S`, etc.
- Or define wrapper rules that take `[MinimalAxioms Axioms]` and call the explicit versions.

The second approach is cleaner. Example:
```lean
theorem hilbertOrI1Deriv' [MinimalAxioms Axioms] (h : Deriv Axioms Γ A) :
    Deriv Axioms Γ (A ∨ B) :=
  hilbertOrI1Deriv MinimalAxioms.h_orI1 h
```

### 7.4 EFQ and Classical Requirements

The HA instance needs EFQ. Currently the ND system controls this via `[IsIntuitionistic T]`. In the Hilbert setting, we need a way to express "the axiom predicate includes EFQ". This could be:
- A new typeclass `HasEFQ Axioms` with `h_EFQ : ∀ φ, Axioms (⊥ → φ)`
- Or use the fact that `IntPropAxiom` and `PropositionalAxiom` have EFQ

Similarly for classical: `HasPeirce Axioms` or use `PropositionalAxiom`.

**Design choice**: Define `IntuitionisticAxioms` extending `MinimalAxioms` with EFQ, and `ClassicalAxioms` extending `IntuitionisticAxioms` with Peirce. This parallels the ND `IsIntuitionistic`/`IsClassical` hierarchy.

## 8. Tactic Survey Results

For the Hilbert Lindenbaum proofs, the primary proof strategy is:
- **Direct term construction** using `hilbert*Deriv` rules (most proofs)
- **`simp` with custom lemmas** for quotient manipulation
- **`obtain ⟨d⟩ := h; exact ⟨...⟩`** pattern for Nonempty/Deriv unwrapping

The `grind` tactic may help with Finset/List membership goals. The `omega` tactic is not relevant (no arithmetic). `aesop` may help with simple structural goals but is unlikely to close Hilbert derivation goals.

## 9. Estimated Complexity

| Component | Lines (est.) | Difficulty |
|-----------|-------------|-----------|
| Equivalence relation + setoid | 30 | Low |
| Quotient type + map | 10 | Low |
| Lattice operations + well-definedness | 80 | Medium (congruence proofs) |
| GHA instance proofs | 150 | Medium-High (himp_iff is complex) |
| HA instance | 20 | Low |
| BA instance (EM + regular) | 60 | Medium |
| Simp lemmas + API | 30 | Low |
| Bridge verification | 40 | Medium |
| **Total** | **~420** | Medium-High |

## 10. Recommendations

1. **Proceed with Option A** (Pure Hilbert Lindenbaum from scratch).
2. **Create new file** `HilbertLindenbaum.lean` alongside existing `Lindenbaum.lean`.
3. **Do NOT delete** the existing ND `Lindenbaum.lean` -- downstream files (`Completeness.lean`, etc.) depend on it. The task description says "The existing ND Lindenbaum can be kept temporarily as internal machinery."
4. **Use `[MinimalAxioms Axioms]`** typeclass throughout, extending with EFQ/Peirce witness typeclasses for HA/BA.
5. **Define MinimalAxioms-aware wrappers** for `hilbert*Deriv` rules to avoid explicit axiom parameter threading.
6. **Start with the `le_himp_iff` proof** as the hardest lemma -- if this can be proved cleanly, the rest will follow.
7. **Prioritize the GHA instance** (Phase 3) as the critical deliverable. HA and BA are incremental additions.
