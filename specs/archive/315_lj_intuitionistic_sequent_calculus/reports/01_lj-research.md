# Research Report: LJ Intuitionistic Sequent Calculus (Task 315)

## 1. Executive Summary

Task 315 requires implementing the intuitionistic sequent calculus LJ for propositional logic within CSLib. The key design decisions center on sequent type selection, rule presentation style (G3ip vs G1i), and the structure of bridge proofs. This report recommends:

1. **Reuse the existing ND `Sequent` type** (`Ctx Atom x Proposition Atom`) for LJ sequents, since LJ uses single-conclusion sequents matching the ND shape exactly.
2. **Follow the G3ip-style all-additive presentation** from Negri and von Plato (2001), consistent with the existing LK implementation.
3. **Include weakening and cut as explicit constructors** (matching LK's design) rather than adopting the structural-rule-free G3ip calculus, to maintain consistency across the SequentCalculus module.
4. **Structure the ND-LJ bridge** as a near-definitional translation since both systems use identical sequent shapes (`Finset` antecedent, single `Proposition` conclusion).

## 2. Existing Infrastructure Analysis

### 2.1 Sequent Types in CSLib

Two distinct sequent types exist:

| Type | Definition | Location | Shape |
|------|-----------|----------|-------|
| `Sequent` (ND) | `abbrev Sequent := Ctx Atom x Proposition Atom` | `NaturalDeduction/Basic.lean:108` | `Finset` antecedent, single conclusion |
| `LKSequent` | `structure LKSequent` with `ant : Finset` and `suc : Finset` | `SequentCalculus/Defs.lean:50-54` | `Finset` antecedent, `Finset` succedent |

LJ uses single-conclusion sequents (`Gamma => C` where `C` is a single formula). This matches the ND `Sequent` type exactly. The `LKSequent` type is unsuitable because its `suc` field is a `Finset`, whereas LJ succedents are always single formulas.

**Recommendation**: Reuse the ND `Sequent` type. This yields a near-definitional ND-LJ bridge because both systems index proofs over `Ctx Atom x Proposition Atom`. Define `LJSequent` as an alias:

```lean
/-- An LJ sequent reuses the ND single-conclusion sequent shape. -/
abbrev LJSequent := @Sequent Atom
```

This introduces a semantic alias without creating a new type, and allows using the existing `Gamma |- A` notation within the LJ module (after opening the ND notation scope, or defining a parallel notation `Gamma |-_LJ A`).

**Notation decision**: Since `Gamma |- A` is already scoped notation for `(Gamma, A) : Sequent` in the ND namespace, and since the LJ namespace will be separate, we can either:
- (a) Use the same `|-` notation by opening the ND scope, or
- (b) Define a new notation `Gamma |-_i A` for LJ sequents to distinguish them visually.

Option (a) is cleaner given that `LJSequent = Sequent` definitionally. The planner should decide.

### 2.2 LK Implementation (Task 314 Reference)

The LK implementation provides the template for LJ. Key patterns:

- **`LKProof`**: Inductive type with 11 constructors: `ax`, `botL`, `andL`, `andR`, `orL`, `orR`, `impL`, `impR`, `weakL`, `weakR`, `cut`.
- **`LKProof.height`**: Proof height function used in cut elimination.
- **`LKProof.mono`**: Monotonicity/weakening as a derived lemma over structural induction.
- **`CutFree`**: Predicate asserting no `cut` steps appear.
- **`CutFreeLKProof`**: Subtype `{ d : LKProof seq // CutFree d }`.
- **`cutAdmissibility`**: Cut elimination by structural induction on the cut formula (not proof height).
- **`LKProof.cutElim`**: Every LK proof has a cut-free counterpart (`Nonempty`).
- **`LKProof.sound`**: Soundness by structural induction on the proof tree.
- **`ndToLK`/`nd_iff_lk`**: ND-to-LK translation for classical logic.
- **`hilbert_iff_lk`**: Composition of Hilbert-ND and ND-LK bridges.

### 2.3 ND System

The ND system (`Theory.Derivation`) has 10 constructors:
- `ax` (theory axiom), `ass` (context assumption)
- `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `impI`, `impE`

ND derivations are parameterized by a `Theory Atom` (set of propositions). Logic strength is controlled by:
- `MPL` (minimal): empty theory
- `IPL` (intuitionistic): adds `bot -> A` for all `A`
- `CPL` (classical): adds `neg neg A -> A` for all `A`

### 2.4 Hilbert System

The Hilbert system uses `IntPropAxiom` for intuitionistic logic (9 axiom constructors: K, S, efq, andI, andE1, andE2, orI1, orI2, orE). Bridge `hilbert_iff_nd_int` already exists.

### 2.5 Intuitionistic Semantics

Kripke semantics for intuitionistic logic exists:
- `IForces`: Forcing relation with upward-closure
- `IValid`: Validity in all intuitionistic Kripke models
- `int_strong_completeness`: `ISemanticEntails Gamma phi -> SetDerivable IntPropAxiom Gamma phi`
- `int_soundness_derivable`: `Derivable IntPropAxiom phi -> IValid phi`

## 3. Literature Proof Structure

### 3.1 G3ip Rules (Negri & von Plato, Ch. 2)

The G3ip calculus for intuitionistic propositional logic has these rules:

**Axiom**: `P, Gamma => P` (atoms only)

**Left rules**:
- `L-bot`: `bot, Gamma => C` (no premise)
- `L-and`: From `A, B, Gamma => C` derive `A & B, Gamma => C`
- `L-or`: From `A, Gamma => C` and `B, Gamma => C` derive `A v B, Gamma => C`
- `L-imp`: From `A -> B, Gamma => A` and `B, Gamma => C` derive `A -> B, Gamma => C`
  - Note: The principal formula `A -> B` is **repeated** in the left premise (Kleene's device for contraction-freeness)

**Right rules**:
- `R-and`: From `Gamma => A` and `Gamma => B` derive `Gamma => A & B`
- `R-or1`: From `Gamma => A` derive `Gamma => A v B`
- `R-or2`: From `Gamma => B` derive `Gamma => A v B`
- `R-imp`: From `A, Gamma => B` derive `Gamma => A -> B`

**Key differences from LK**:
1. Single-conclusion sequents (no Finset succedent)
2. No `weakR` (only one formula on the right)
3. The `L-imp` rule repeats the principal formula in the left premise
4. Axiom restricted to atoms

### 3.2 Design Choice: G3ip vs G1i vs LK-style

Three options for the LJ inductive:

| Feature | G3ip (Negri) | G1i (Troelstra) | LK-style (CSLib pattern) |
|---------|-------------|-----------------|------------------------|
| Structural rules | Admissible (not constructors) | Explicit (weakening, contraction) | Explicit (weakening, cut) |
| Axiom restriction | Atoms only | Any formula | Any formula |
| L-imp repetition | Yes (Kleene device) | No | No |
| Contraction | Admissible | Explicit | Built into Finset |
| Consistency with LK module | Low | Medium | High |

**Recommendation**: Use the **LK-style** presentation for consistency with the existing codebase. This means:
- `ax` with `A in Gamma` (any formula, not just atoms) -- matching LK's `ax`
- `botL` with `bot in Gamma`
- Explicit `weakL` constructor
- Explicit `cut` constructor
- No `weakR` (single conclusion)
- Standard `impL` without repetition of the principal formula

With `Finset` contexts, contraction and exchange are built in. The G3ip device of repeating the principal formula in `L-imp` is unnecessary because `Finset.insert` is idempotent.

### 3.3 Cut Elimination Strategy (Troelstra & Schwichtenberg, Ch. 4; Negri & von Plato, Ch. 2)

The cut elimination proof for LJ follows the same strategy as for LK:
- Structural induction on the cut formula `A`
- For each formula case, inner induction on the d1 proof (and sometimes d2)
- Principal cases: when the cut formula is introduced on the right by d1 and decomposed on the left by d2
- Non-principal cases: structural pushing of the cut

**Key difference from LK cut elimination**: In LK, the `impR` rule can introduce `A -> B` into a multi-formula succedent, requiring the inner induction on d2. In LJ, `impR` introduces `A -> B` as the **sole** conclusion, which simplifies the principal `imp` case somewhat.

**Critical observation**: The existing LK `cutAdmissibility` proof is 770+ lines. The LJ version will be comparable in length but structurally simpler because:
1. No `weakR` constructor to handle
2. No `orR` or `andR` rules that split the succedent
3. The `impR` principal case is slightly simpler (single conclusion, no need to track `A -> B` membership in a Finset succedent)

However, the LJ `impL` rule creates complexity because both premises share the same context but differ in conclusion:
- Left premise: `Gamma => A` (derive the antecedent)
- Right premise: `B, Gamma => C` (use the consequent)

### 3.4 ND-LJ Bridge (Gentzen 1935, Sec. V)

The ND-LJ translation is the most natural of all bridge proofs because both systems:
1. Use `Finset` antecedents
2. Use single-formula conclusions
3. Have corresponding rules for each connective

**ndToLJ direction** (ND -> LJ): Structural induction on `Theory.Derivation`.
- `ax h_mem`: The ND axiom `A in T` needs special handling. For IPL (`IsIntuitionistic T`), the axiom `bot -> A` translates to LJ's `impR` + `botL`. More generally, each theory axiom produces an LJ proof of `empty => axiom_formula`, weakened to `Gamma => axiom_formula`.
- `ass h_mem`: Maps directly to `LJProof.ax A Gamma h_mem`
- `andI d1 d2`: Maps to `LJProof.andR` (both premises have same context, same conclusion shape)
- `andE1 d`: Requires cut with `andL`
- `andE2 d`: Requires cut with `andL`
- `orI1 d`: Maps to `LJProof.orR1`
- `orI2 d`: Maps to `LJProof.orR2`
- `orE d dA dB`: Requires cut with `orL`
- `impI d`: Maps directly to `LJProof.impR`
- `impE d1 d2`: Requires cut with `impL`

The elimination rules (andE1, andE2, orE, impE) require `cut` because ND uses elimination-style rules while SC uses left-introduction rules.

**ljToND direction** (LJ -> ND): Also structural induction.
- `ax`: Maps to `ass`
- `botL`: Maps to `ax (efq A)` (using theory axiom for `bot -> A`)
- `andL`: Maps to `andE1`/`andE2` + `cut`
- `andR`: Maps to `andI`
- `orL`: Maps to `orE`
- `orR1/orR2`: Maps to `orI1`/`orI2`
- `impL`: Maps to `impE` + `cut`
- `impR`: Maps to `impI`
- `weakL`: Maps to `weak`
- `cut`: Maps to `cut`

**Near-definitional claim**: The bridge is "near-definitional" because the sequent shapes match exactly. However, it is NOT literally definitional -- the elimination vs left-introduction asymmetry means every elimination rule translation requires a cut step.

### 3.5 Hilbert-LJ Bridge

The `hilbert_iff_lj` bridge composes:
1. `hilbert_iff_nd_ctx_int` (existing): Hilbert `IntPropAxiom` <-> ND under `AxiomTheory IntPropAxiom`
2. `nd_iff_lj` (to be built): ND under `AxiomTheory IntPropAxiom` <-> LJ provability

For the backward direction (LJ -> Hilbert), we can either:
- (a) Compose through ND: LJ -> ND -> Hilbert
- (b) Use semantics: LJ sound -> Kripke valid -> Hilbert completeness

Option (a) is more constructive and reuses existing bridges. Option (b) is more direct but requires `int_strong_completeness`.

**Recommendation**: Use option (a) for the constructive direction and document that option (b) is available via semantics.

## 4. Proposed LJProof Inductive

```lean
/-- LJ proof trees for intuitionistic propositional logic. Single-conclusion sequents
with Finset antecedents. The presentation follows the LK-style all-additive pattern
with explicit weakening and cut constructors. -/
inductive LJProof : @Sequent Atom → Type u where
  /-- Identity axiom: formula A appears in the antecedent. -/
  | ax (A : Proposition Atom) (Γ : Ctx Atom) (_ : A ∈ Γ) :
      LJProof (Γ ⊢ A)
  /-- Left falsum: ⊥ in the antecedent proves anything. -/
  | botL (Γ : Ctx Atom) (C : Proposition Atom) (_ : (⊥ : Proposition Atom) ∈ Γ) :
      LJProof (Γ ⊢ C)
  /-- Left conjunction: from A, B, Γ ⊢ C derive A ∧ B, Γ ⊢ C. -/
  | andL (A B : Proposition Atom) {Γ : Ctx Atom} {C : Proposition Atom}
      (_ : (A ∧ B) ∈ Γ)
      (_ : LJProof (insert A (insert B Γ) ⊢ C)) :
      LJProof (Γ ⊢ C)
  /-- Right conjunction: from Γ ⊢ A and Γ ⊢ B derive Γ ⊢ A ∧ B. -/
  | andR (A B : Proposition Atom) {Γ : Ctx Atom}
      (_ : LJProof (Γ ⊢ A))
      (_ : LJProof (Γ ⊢ B)) :
      LJProof (Γ ⊢ A ∧ B)
  /-- Left disjunction: from A, Γ ⊢ C and B, Γ ⊢ C derive A ∨ B, Γ ⊢ C. -/
  | orL (A B : Proposition Atom) {Γ : Ctx Atom} {C : Proposition Atom}
      (_ : (A ∨ B) ∈ Γ)
      (_ : LJProof (insert A Γ ⊢ C))
      (_ : LJProof (insert B Γ ⊢ C)) :
      LJProof (Γ ⊢ C)
  /-- Right disjunction (left): from Γ ⊢ A derive Γ ⊢ A ∨ B. -/
  | orR1 (A B : Proposition Atom) {Γ : Ctx Atom}
      (_ : LJProof (Γ ⊢ A)) :
      LJProof (Γ ⊢ A ∨ B)
  /-- Right disjunction (right): from Γ ⊢ B derive Γ ⊢ A ∨ B. -/
  | orR2 (A B : Proposition Atom) {Γ : Ctx Atom}
      (_ : LJProof (Γ ⊢ B)) :
      LJProof (Γ ⊢ A ∨ B)
  /-- Left implication: from Γ ⊢ A and B, Γ ⊢ C derive A → B, Γ ⊢ C. -/
  | impL (A B : Proposition Atom) {Γ : Ctx Atom} {C : Proposition Atom}
      (_ : (A → B) ∈ Γ)
      (_ : LJProof (Γ ⊢ A))
      (_ : LJProof (insert B Γ ⊢ C)) :
      LJProof (Γ ⊢ C)
  /-- Right implication: from A, Γ ⊢ B derive Γ ⊢ A → B. -/
  | impR (A B : Proposition Atom) {Γ : Ctx Atom}
      (_ : LJProof (insert A Γ ⊢ B)) :
      LJProof (Γ ⊢ A → B)
  /-- Left weakening: add a formula to the antecedent. -/
  | weakL (A : Proposition Atom) {Γ : Ctx Atom} {C : Proposition Atom}
      (_ : LJProof (Γ ⊢ C)) :
      LJProof (insert A Γ ⊢ C)
  /-- Cut rule: cut on formula A. -/
  | cut (A : Proposition Atom) {Γ : Ctx Atom} {C : Proposition Atom}
      (_ : LJProof (Γ ⊢ A))
      (_ : LJProof (insert A Γ ⊢ C)) :
      LJProof (Γ ⊢ C)
```

**Differences from LK**:
1. No `weakR` (single conclusion)
2. No succedent membership proofs (single conclusion is always the conclusion formula)
3. `orR` split into `orR1`/`orR2` (no succedent to track membership in)
4. `andR` has no membership proof (conclusion is always `A and B`)
5. `impR` has no membership proof
6. `impL` left premise is `Gamma => A` not `Gamma =>_s insert A Delta`

**Constructor count**: 11 (same as LK: ax, botL, andL, andR, orL, orR1, orR2, impL, impR, weakL, cut)

## 5. Soundness Strategy

LJ soundness uses Kripke semantics (intuitionistic validity), not Boolean valuation:

```lean
/-- Semantic validity of an LJ sequent: for every intuitionistic Kripke model and world,
if all antecedent formulas are forced then the conclusion is forced. -/
def LJSequent.ivalid (seq : @Sequent Atom) : Prop :=
  ∀ (World : Type*) [Preorder World] (M : KripkeModel World Atom) (w : World),
    (∀ A ∈ seq.1, IForces M.v M.botForces w A) →
    IForces M.v M.botForces w seq.2
```

Wait -- this is not quite right. Since LJ is for intuitionistic logic specifically, `botForces` should be `fun _ => False` (the intuitionistic interpretation). But we can define validity more generally and specialize.

Actually, the simpler approach mirrors the LK soundness strategy: define validity as a semantic condition on the sequent and prove each rule preserves it. The key insight is that LJ soundness should be relative to the **intuitionistic Kripke semantics** (`IForces` with `botForces = fun _ => False`), using `iforces_persistence` for the persistence property.

**Alternative**: Since `IValid` already exists and `int_soundness_derivable` proves Hilbert soundness, we could define LJ validity in terms of the Kripke forcing relation and prove soundness by structural induction on `LJProof`.

## 6. Cut Elimination Strategy

The LJ cut elimination follows the LK pattern exactly:
1. Define `CutFree : LJProof seq -> Prop` (predicate, `False` on `cut` constructor)
2. Define `CutFreeLJProof seq := { d : LJProof seq // CutFree d }`
3. Prove `CutFree.mono` (cut-freeness preserved under weakening)
4. Prove `cutAdmissibility` by structural induction on the cut formula
5. Prove `LJProof.cutElim` by structural induction on the proof

The LJ cut elimination is simpler than LK because there is no succedent Finset to manage. The principal cases:

**imp case** (principal): d1 = `impR` (proves `Gamma => A -> B` from `A, Gamma => B`), d2 = `impL` (uses `A -> B` on the left: `Gamma => A` and `B, Gamma => C` to get `A -> B, Gamma => C`).
- Cut A -> B out of d2 using inner induction (height decrease)
- Cut A using ih_A (complexity decrease)
- Cut B using ih_B (complexity decrease)

**and case** (principal): d1 = `andR`, d2 = `andL`. Similar to LK.

**or case** (principal): d1 = `orR1` or `orR2`, d2 = `orL`. Similar to LK.

## 7. File Layout

```
Cslib/Logics/Propositional/SequentCalculus/
  Defs.lean                    -- existing (LKSequent, notation)
  LJ/
    Basic.lean                 -- LJProof inductive, height, mono, CutFree
    Soundness.lean             -- LJProof.sound (Kripke semantics)
    CutElimination.lean        -- cutAdmissibility, LJProof.cutElim
  LJ.lean                     -- barrel import for LJ/
  SequentCalculus.lean         -- update barrel to include LJ
```

Bridge proofs go in:
```
Cslib/Logics/Propositional/NaturalDeduction/
  Equivalence.lean             -- add nd_iff_lj, hilbert_iff_lj (intuitionistic)
```

Or alternatively, create a dedicated bridge file:
```
Cslib/Logics/Propositional/SequentCalculus/LJ/
  Completeness.lean            -- ndToLJ, ljToND, nd_iff_lj, hilbert_iff_lj
```

**Recommendation**: Follow the LK pattern and place the bridge in `LJ/Completeness.lean`, matching the existing `LK/Completeness.lean` structure.

## 8. Dependency Analysis

### Direct Dependencies (Task 314 outputs)
- `Cslib/Logics/Propositional/SequentCalculus/Defs.lean` -- shared infrastructure
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- `Sequent`, `Ctx`, `Theory.Derivation`
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` -- `IForces`, `IValid`, `iforces_persistence`

### Bridge Dependencies
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- `hilbert_iff_nd_int`
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` -- `int_strong_completeness`
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` -- `int_soundness_derivable`
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- `IntPropAxiom`

### Mathlib Dependencies
- `Mathlib.Data.Finset.Basic` -- `Finset` operations
- `Mathlib.Data.Finset.Insert` -- `insert_comm`, `insert_subset_insert`
- `Mathlib.Order.Defs.PartialOrder` -- `Preorder` for Kripke models

## 9. Reuse Check Results

| Concept | Checked Location | Found? | Action |
|---------|-----------------|--------|--------|
| LJ sequent type | `lean_local_search LJSequent` | No | Reuse ND `Sequent` |
| LJ proof type | `lean_local_search LJProof` | No | Create new |
| Intuitionistic forcing | `lean_local_search IForces` | Yes | Reuse |
| Intuitionistic validity | `lean_local_search IValid` | Yes | Reuse |
| Intuitionistic soundness | `lean_local_search int_soundness` | Yes | Reuse for bridge |
| Intuitionistic completeness | `lean_local_search int_completeness` | Yes | Reuse for bridge |
| Hilbert-ND int bridge | `lean_local_search hilbert_iff_nd_int` | Yes | Reuse for bridge |
| ND weakening | `Derivation.weak` | Yes | Reuse |
| ND cut | `Derivation.cut` | Yes | Reuse |
| Finset insert_comm | Mathlib | Yes | Reuse |

## 10. Risk Assessment and Blockers

### No Blockers Identified

All dependencies are available. The task is well-specified and follows the established LK pattern closely.

### Risks

1. **Cut elimination proof length**: The LK cut elimination is 770+ lines. The LJ version will be substantial but shorter due to the simpler succedent structure. Estimate: 400-600 lines.

2. **Bridge noncomputability**: The `ndToLJ` direction may require `noncomputable` if it needs to dispatch on `IntPropAxiom` (which is `Prop`-valued), following the pattern of `ndToLK`. The `ljToND` direction should be computable.

3. **Theory parameterization**: The ND system is parameterized by `Theory Atom`. For the LJ bridge, we need to fix the theory to `AxiomTheory IntPropAxiom` (matching the intuitionistic Hilbert system) or to `IPL` (matching the ND `IsIntuitionistic` class). The planner should decide which parameterization to use. Using `AxiomTheory IntPropAxiom` aligns with the LK bridge pattern; using `IPL` aligns with the ND derived rules pattern.

4. **Soundness target**: LJ soundness should target Kripke semantics (`IForces`) rather than Boolean valuation (`Evaluate`), since the latter is classical. The soundness proof will use `iforces_persistence` heavily.

## 11. Tactic Survey

For the LJ proofs, the following tactics will be central:
- `simp [Finset.mem_insert]` -- for membership decomposition in left rules
- `grind` -- for Finset subset obligations
- `exact?` / `apply?` -- for finding Finset lemmas
- Structural recursion -- for all inductive proofs (not `omega`/`ring` which are irrelevant here)

The LK implementation uses manual case analysis throughout without heavy automation. The LJ implementation should follow the same pattern.

## 12. Estimated Complexity

| File | Lines (est.) | Difficulty |
|------|-------------|------------|
| LJ/Basic.lean | 200-250 | Medium (LJProof inductive + height + mono + CutFree) |
| LJ/Soundness.lean | 120-160 | Medium (structural induction, Kripke semantics) |
| LJ/CutElimination.lean | 400-600 | Hard (mirrors LK pattern but simpler) |
| LJ/Completeness.lean | 200-300 | Medium-Hard (ndToLJ + ljToND + bridge composition) |
| Total | 920-1310 | |
