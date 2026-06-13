# Teammate A Findings: Strong Completeness via Lindenbaum's Lemma / Maximal Consistent Sets

## Executive Summary

The CSLib codebase already has **weak completeness** for all three propositional logics (minimal, intuitionistic, classical), but these results only establish `Valid phi -> Derivable Axioms phi` (validity implies derivability from the empty context). **Strong completeness** --- the statement that `Gamma |= phi -> Gamma |- phi` (semantic consequence from an arbitrary set of assumptions implies syntactic derivability from those assumptions) --- is not yet formalized. This report analyzes the Lindenbaum/MCS approach to establishing strong completeness, identifies what infrastructure exists, what must be built, and how the three systems can share proof components.

---

## 1. Current State of CSLib Infrastructure

### 1.1 What Already Exists

CSLib has a rich two-layer architecture for propositional logic:

**Proof Systems** (three axiom predicates sharing the same `DerivationTree` type):
- `MinPropAxiom`: K + S + conjunction/disjunction axioms (8 axiom constructors)
- `IntPropAxiom`: MinPropAxiom + EFQ (9 constructors)
- `PropositionalAxiom`: IntPropAxiom + Peirce's law (10 constructors)

All three use the same parameterized `DerivationTree Axioms Gamma phi` type and the same `propDerivationSystem Axioms` instance of the generic `Metalogic.DerivationSystem`.

**Semantics**:
- Classical: `Evaluate v phi` (bivalent truth-value semantics, `Semantics/Basic.lean`)
- Intuitionistic: `IForces v (fun _ => False) w phi` (Kripke forcing with `bot_forces = fun _ => False`)
- Minimal: `IForces v bot_forces w phi` (Kripke forcing with arbitrary upward-closed `bot_forces`)

**Weak Completeness** (already proven):
- `prop_completeness`: `Tautology phi -> Derivable PropositionalAxiom phi` (in `Completeness.lean`)
- `int_completeness`: `IValid phi -> Derivable IntPropAxiom phi` (in `IntCompleteness.lean`)
- `min_completeness`: `MValid phi -> Derivable MinPropAxiom phi` (in `MinCompleteness.lean`)

**MCS / Lindenbaum Infrastructure** (in `Foundations/Logic/Metalogic/Consistency.lean`):
- `DerivationSystem F`: Generic structure with `Deriv`, `weakening`, `assumption`, `mp`
- `SetConsistent D S`: Every finite subset is consistent
- `SetMaximalConsistent D S`: Consistent + adding any non-member makes it inconsistent
- `set_lindenbaum`: Lindenbaum's lemma (consistent set extends to MCS via Zorn)
- `HasDeductionTheorem`: Deduction theorem hypothesis
- `closed_under_derivation`: MCS is closed under derivation (given DT)
- `implication_property`: Modus ponens closure for MCS
- `negation_complete`: For any phi, either phi in S or (phi -> bot) in S

**Intuitionistic/Minimal Completeness Infrastructure**:
- `IntDCCS`: Deductively closed consistent sets (consistency + deductive closure)
- `IntPrimeDCCS`: Prime DCCS (disjunction property: phi v psi in S => phi in S or psi in S)
- `int_prime_exclusion`: Zorn-based extension of DCCS to prime DCCS excluding a formula
- `MinTheory`: Deductively closed sets (no consistency requirement)
- `MinPrimeTheory`: Prime MinTheory
- `min_prime_exclusion`: Analogous Zorn extension for MinTheory

### 1.2 What Is Missing for Strong Completeness

1. **Semantic consequence definitions**: No `SetSemanticConsequence` / `SetEntails` for any of the three logics
2. **Set-based syntactic derivability** (from theory): No `SetDerivable Axioms Gamma phi` for the Hilbert system
3. **Strong completeness theorems**: None exist
4. **The "bridge" connecting set-based derivability to the existing list-based `Deriv`**

---

## 2. Strong Completeness Theorem Statements

### 2.1 Classical Propositional Logic

**Definition needed** -- Semantic consequence:
```lean
/-- phi is a semantic consequence of Gamma iff every valuation satisfying all of Gamma also satisfies phi. -/
def SetSemanticConsequence (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  forall (v : Valuation Atom), (forall psi in Gamma, Evaluate v psi) -> Evaluate v phi
```

**Definition needed** -- Set-based derivability:
```lean
/-- phi is derivable from Gamma iff there exists a finite subset L of Gamma such that L |- phi. -/
def SetDerivable (Axioms : PL.Proposition Atom -> Prop)
    (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  exists (L : List (PL.Proposition Atom)), (forall x in L, x in Gamma) /\
    (propDerivationSystem Axioms).Deriv L phi
```

**Strong completeness**:
```lean
theorem prop_strong_completeness {Gamma : Set (PL.Proposition Atom)} {phi : PL.Proposition Atom}
    (h : SetSemanticConsequence Gamma phi) : SetDerivable PropositionalAxiom Gamma phi
```

### 2.2 Intuitionistic Propositional Logic

**Definition needed** -- Kripke semantic consequence:
```lean
/-- phi is an intuitionistic semantic consequence of Gamma iff in every Kripke model,
at every world where all of Gamma is forced, phi is also forced. -/
def ISetSemanticConsequence (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  forall (World : Type*) [Preorder World] (val : World -> Atom -> Prop),
    (forall {w w' : World} (p : Atom), w <= w' -> val w p -> val w' p) ->
    forall w, (forall psi in Gamma, IForces val (fun _ => False) w psi) ->
      IForces val (fun _ => False) w phi
```

**Strong completeness**:
```lean
theorem int_strong_completeness {Gamma : Set (PL.Proposition Atom)} {phi : PL.Proposition Atom}
    (h : ISetSemanticConsequence Gamma phi) : SetDerivable IntPropAxiom Gamma phi
```

### 2.3 Minimal Propositional Logic

**Definition needed** -- Minimal Kripke semantic consequence:
```lean
/-- phi is a minimal semantic consequence of Gamma iff in every minimal Kripke model,
at every world where all of Gamma is forced, phi is also forced. -/
def MSetSemanticConsequence (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  forall (World : Type*) [Preorder World] (val : World -> Atom -> Prop)
    (bot_forces : World -> Prop),
    (forall {w w' : World} (p : Atom), w <= w' -> val w p -> val w' p) ->
    (forall {w w' : World}, w <= w' -> bot_forces w -> bot_forces w') ->
    forall w, (forall psi in Gamma, IForces val bot_forces w psi) ->
      IForces val bot_forces w phi
```

**Strong completeness**:
```lean
theorem min_strong_completeness {Gamma : Set (PL.Proposition Atom)} {phi : PL.Proposition Atom}
    (h : MSetSemanticConsequence Gamma phi) : SetDerivable MinPropAxiom Gamma phi
```

---

## 3. Proof Architecture: The Lindenbaum/MCS Approach

### 3.1 High-Level Proof Structure (All Three Logics)

The proof of strong completeness via Lindenbaum's lemma follows a uniform pattern across all three logics:

1. **Assume** `Gamma |= phi` (semantic consequence)
2. **Contrapositive**: Assume `Gamma |-/- phi` (phi is not derivable from Gamma)
3. **Show** `Gamma union {neg phi}` is consistent (using non-derivability of phi)
4. **Lindenbaum extension**: Extend `Gamma union {neg phi}` to a maximal / prime / MCS set `M`
5. **Canonical model construction**: Build a model from `M` (or from the collection of such sets)
6. **Truth lemma**: Show `psi in M <-> M |= psi`
7. **Derive contradiction**: All of Gamma is in M (hence satisfied), but neg phi is also in M (hence phi is not satisfied), contradicting the semantic consequence assumption

### 3.2 Classical Logic: The Simplest Case

For classical logic, the proof is particularly clean because the canonical model is a **single valuation** derived from one MCS:

**Step 3**: Show `Gamma union {neg phi}` is `PropSetConsistent`. If not, there exists a finite `L subset Gamma union {neg phi}` with `L |- bot`. By the deduction theorem, we can remove neg phi from L to get `L' subset Gamma` with `L' |- neg phi -> bot`. Using classical reasoning (Peirce's law / DNE), `L' |- phi`, contradicting non-derivability from Gamma.

**Step 4**: Apply `prop_lindenbaum` (already exists) to get MCS M containing `Gamma union {neg phi}`.

**Step 5**: The canonical valuation `canonicalValuation M` is already defined.

**Step 6**: `prop_truth_lemma` (already exists) gives `Evaluate (canonicalValuation M) psi <-> psi in M`.

**Step 7**: Since Gamma subset M, all of Gamma is satisfied by the canonical valuation. By semantic consequence, phi is satisfied. By the truth lemma, phi in M. But neg phi in M too, so bot in M -- contradicting `prop_mcs_bot_not_mem`.

**Key observation**: The classical strong completeness proof reuses almost all existing infrastructure. The main new work is:
- Defining `SetSemanticConsequence` and `SetDerivable`
- Proving `Gamma union {neg phi}` is consistent when phi is not derivable from Gamma
- Assembling the pieces

### 3.3 Intuitionistic Logic: Prime DCCS as Worlds

For intuitionistic logic, the canonical model uses **all prime DCCSs** as worlds (already implemented as `IntCanonicalWorld`), not a single MCS:

**Step 3**: Show the deductive closure of `Gamma union {neg phi}` is consistent as an IntDCCS. The existing `intDeductiveClosure_is_dccs` handles this given consistency of the union. We need to show `Gamma union {neg phi}` is `PropSetConsistent IntPropAxiom` -- this requires showing that if `Gamma union {neg phi}` were inconsistent, we could derive phi from a finite subset of Gamma. The argument uses EFQ: from `L, neg phi |- bot` we get `L |- neg phi -> bot`, i.e. `L |- neg neg phi`. In intuitionistic logic, we do NOT have `neg neg phi -> phi`, so we need a different argument. The correct approach: from `L, neg phi |- bot` we get `L |- neg phi -> bot` by DT. But `neg phi = phi -> bot`, so `L |- (phi -> bot) -> bot`. This is `L |- neg neg phi`. In intuitionistic logic this does NOT give `L |- phi`. Instead, we need to observe: by DT from `L, neg phi |- bot`, we get `L |- neg(neg phi)`. But for an IntDCCS, `neg phi` would need to be in any DCCS containing L by closure. The actual approach is the **contrapositive via the canonical model**: start from `SetDerivable IntPropAxiom Gamma phi` being false, build a canonical world containing Gamma but not phi.

The correct approach for intuitionistic strong completeness:

1. Assume phi is not set-derivable from Gamma
2. Define `S = intDeductiveClosure(Gamma)` -- this is an IntDCCS (if Gamma is Int-consistent)
3. If `phi in S`, then phi is set-derivable from Gamma (contradiction), so `phi not in S`
4. Apply `int_prime_exclusion` to S to get prime DCCS T with `Gamma subset T` and `phi not in T`
5. Let T be a world in the canonical model
6. By the truth lemma, all of Gamma is forced at T, but phi is not forced at T
7. This contradicts `Gamma |= phi`

**Critical subtlety**: We need to show `Gamma` is Int-consistent (no finite subset derives bot). This is the side condition. If Gamma is inconsistent, then from Gamma we can derive anything (by EFQ), so strong completeness holds trivially. We can handle this with a case split.

### 3.4 Minimal Logic: MinTheory as Worlds

For minimal logic, the structure is analogous but uses `MinTheory` (no consistency requirement) and `MinPrimeTheory`:

1. Assume phi is not set-derivable from Gamma
2. Define `S = minDeductiveClosure(Gamma)` -- this is a MinTheory (always, no consistency needed)
3. If `phi in S`, then phi is set-derivable from Gamma (contradiction), so `phi not in S`
4. Apply `min_prime_exclusion` to S to get prime MinTheory T with `Gamma subset T` and `phi not in T`
5. Let T be a world in the canonical model
6. By the truth lemma, all of Gamma is forced at T, but phi is not forced at T
7. This contradicts `Gamma |= phi`

**Key advantage over intuitionistic**: No consistency side condition needed. `minDeductiveClosure` is always a MinTheory regardless of consistency (since `MinTheory` has no consistency requirement). This is the fundamental simplification of minimal logic.

---

## 4. Infrastructure Sharing Across the Three Systems

### 4.1 Fully Shared Components (Already Exist)

| Component | Location | Used By |
|-----------|----------|---------|
| `DerivationSystem` | `Consistency.lean` | All three |
| `propDerivationSystem` | `Derivation.lean` | All three (parameterized over Axioms) |
| `DerivationTree` | `Derivation.lean` | All three |
| `deductionTheorem` | `DeductionTheorem.lean` | All three (parameterized over h_implyK, h_implyS) |
| `set_lindenbaum` | `Consistency.lean` | Classical (directly), Int/Min (through prime exclusion) |
| `Proposition` type | `Defs.lean` | All three |

### 4.2 New Shared Components to Build

| Component | Description | Shareable? |
|-----------|-------------|------------|
| `SetDerivable Axioms Gamma phi` | Set-based derivability | Yes -- parameterized over Axioms |
| `SetDerivable_of_Derivable` | `Derivable phi -> SetDerivable Gamma phi` | Yes |
| `SetDerivable_of_mem` | `phi in Gamma -> SetDerivable Gamma phi` | Yes |
| `SetDerivable_weakening` | `Gamma subset Delta -> SetDerivable Gamma phi -> SetDerivable Delta phi` | Yes |
| `not_SetDerivable_consistent_union` | If phi not derivable from Gamma, then `Gamma union {neg phi}` is consistent | Logic-specific (classical uses Peirce) |

### 4.3 Logic-Specific Components

**Classical** (simplest):
- `SetSemanticConsequence` via bivalent semantics
- Single-MCS canonical model (already have `canonicalValuation` and `prop_truth_lemma`)
- Consistency of `Gamma union {neg phi}` using Peirce's law

**Intuitionistic**:
- `ISetSemanticConsequence` via Kripke semantics
- Multi-world canonical model using `IntCanonicalWorld` (already built)
- Consistency argument using EFQ / case split on Gamma consistency
- Need `intDeductiveClosure_contains_Gamma` and `intDeductiveClosure_phi_iff_SetDerivable`

**Minimal**:
- `MSetSemanticConsequence` via Kripke semantics
- Multi-world canonical model using `MinCanonicalWorld` (already built)
- No consistency side condition needed (simplest Lindenbaum extension)
- Need `minDeductiveClosure_contains_Gamma` and `minDeductiveClosure_phi_iff_SetDerivable`

---

## 5. Weak Completeness as a Corollary

### 5.1 The Relationship

Weak completeness is the special case of strong completeness where `Gamma = empty_set`:

```
Strong:  forall Gamma phi, (Gamma |= phi) -> (Gamma |- phi)
Weak:    forall phi, (empty |= phi) -> (empty |- phi)
```

Since `SetSemanticConsequence empty phi` is equivalent to `Tautology phi` (or `IValid phi` / `MValid phi`), and `SetDerivable Axioms empty phi` is equivalent to `Derivable Axioms phi`, weak completeness follows immediately from strong completeness with `Gamma := empty_set`.

### 5.2 Corollary Statements

```lean
-- Classical
theorem prop_completeness' (h : Tautology phi) : Derivable PropositionalAxiom phi :=
  let h' : SetSemanticConsequence {} phi := ...  -- easy conversion
  let h'' := prop_strong_completeness h'
  ... -- extract Derivable from SetDerivable with empty Gamma

-- Intuitionistic
theorem int_completeness' (h : IValid phi) : Derivable IntPropAxiom phi :=
  let h' : ISetSemanticConsequence {} phi := ...
  let h'' := int_strong_completeness h'
  ...

-- Minimal (analogous)
```

### 5.3 Practical Consideration

CSLib already has the weak completeness theorems proven directly. Rather than replacing them, the strong completeness theorems should be added alongside them. A `_iff_` biconditional combining strong soundness with strong completeness would be the ultimate deliverable:

```lean
theorem prop_strong_completeness_iff :
    SetSemanticConsequence Gamma phi <-> SetDerivable PropositionalAxiom Gamma phi
```

---

## 6. Lindenbaum's Lemma: Variations Across the Three Logics

### 6.1 Classical: Standard Lindenbaum (MCS)

- **Input**: A consistent set S (PropSetConsistent PropositionalAxiom S)
- **Output**: An MCS M containing S (PropSetMaximalConsistent PropositionalAxiom M, S subset M)
- **Tool**: `set_lindenbaum` from `Consistency.lean` (already exists, uses Zorn's lemma)
- **Key property of MCS**: For every phi, either phi in M or neg phi in M (`negation_complete`)
- **Where used**: In the strong completeness proof, we extend `Gamma union {neg phi}` to MCS M

### 6.2 Intuitionistic: Prime Extension (Prime DCCS)

- **Input**: A DCCS S (IntDCCS S) with phi not in S
- **Output**: A prime DCCS T containing S with phi not in T (IntPrimeDCCS T, S subset T, phi not in T)
- **Tool**: `int_prime_exclusion` (already exists in `IntLindenbaum.lean`, uses Zorn's lemma)
- **Key property**: Disjunction property (phi v psi in T => phi in T or psi in T)
- **Where used**: The canonical model uses ALL prime DCCSs as worlds. We extend `intDeductiveClosure(Gamma)` to a prime DCCS excluding phi.
- **Why not MCS?** In intuitionistic logic, MCSs are "too classical" -- they satisfy `phi in M or neg phi in M`, which gives `phi v neg phi in M` by deductive closure, but this is the law of excluded middle, which intuitionistic logic rejects. Instead, we need prime DCCS which only has the weaker disjunction property.

### 6.3 Minimal: Prime Extension (Prime MinTheory)

- **Input**: A MinTheory S with phi not in S
- **Output**: A prime MinTheory T containing S with phi not in T (MinPrimeTheory T, S subset T, phi not in T)
- **Tool**: `min_prime_exclusion` (already exists in `MinLindenbaum.lean`, uses Zorn's lemma)
- **Key advantage**: No consistency requirement on S. The `minDeductiveClosure` of any set is always a MinTheory, so we never need to prove consistency of `Gamma union {neg phi}`. This is because in minimal logic, `bot` at a world just means "bot is forced at that world" (a genuine predicate), not absurdity.

### 6.4 Comparison Table

| Aspect | Classical | Intuitionistic | Minimal |
|--------|-----------|----------------|---------|
| World structure | Single MCS | Prime DCCS | Prime MinTheory |
| Lindenbaum tool | `set_lindenbaum` | `int_prime_exclusion` | `min_prime_exclusion` |
| Consistency required? | Yes | Yes (for DCCS) | No |
| Key property | Negation complete | Disjunction property | Disjunction property |
| bot semantics | False (absurd) | False (absurd) | Predicate (may be true) |
| EFQ needed? | Yes (in axioms) | Yes (in axioms) | No |
| Peirce needed? | Yes (consistency proof) | No | No |
| Truth lemma | `prop_truth_lemma` | `int_truth_lemma` | `min_truth_lemma` |
| Existing? | Yes | Yes | Yes |

---

## 7. Prior Art in Formalizations

### 7.1 Lean Formalizations

**FormalizedFormalLogic/Foundation** ([GitHub](https://github.com/FormalizedFormalLogic/Foundation)):
- Lean 4 project formalizing mathematical logic
- Has propositional logic with Tait-style calculus and completeness
- Has Kripke completeness for intuitionistic logic and superintuitionistic logics
- May have strong completeness results (needs deeper investigation of their codebase)

**Bentzen's IPL formalization** ([arXiv:2310.01916](https://arxiv.org/abs/2310.01916)):
- Verified Henkin-style completeness for IPL in Lean (earlier version)
- Uses prime extension lemma and canonical model construction
- Hilbert-style axiomatization with implication, conjunction, disjunction, falsity
- Very close to CSLib's approach

**Trufas's IPL formalization** ([arXiv:2410.23765](https://arxiv.org/abs/2410.23765)):
- Formalization of IPL in Lean proof assistant
- Verifies soundness and strong completeness for both Kripke and algebraic semantics
- Directly relevant to our task

### 7.2 Other Proof Assistants

**Coq/Rocq**:
- Various formalizations of propositional completeness exist
- The `coq-community/comp-dec-modal` project has modal logic completeness

**Isabelle/HOL**:
- Berghofer's formalization of first-order completeness (includes propositional as special case)
- Uses Lindenbaum + Henkin construction

### 7.3 Mathlib

Mathlib has first-order completeness (`Mathlib.ModelTheory.Satisfiability`) with:
- `FirstOrder.Language.Theory.IsMaximal`: Maximal theories
- `FirstOrder.Language.Theory.IsComplete`: Complete theories
- `completeTheory.isMaximal`: Complete theory of a nonempty model is maximal

However, Mathlib does NOT have propositional-level strong completeness as a separate result. The first-order machinery is too heavyweight for our purposes. CSLib's existing infrastructure is better suited.

---

## 8. Recommended Implementation Strategy

### 8.1 File Organization

```
Cslib/Logics/Propositional/Metalogic/
  StrongCompleteness/
    Defs.lean           -- SetDerivable, SetSemanticConsequence (all three)
    Classical.lean       -- prop_strong_completeness
    Intuitionistic.lean  -- int_strong_completeness
    Minimal.lean         -- min_strong_completeness
```

Or, alternatively, add the strong completeness results directly to the existing files:
- Add `SetDerivable` and `SetSemanticConsequence` to existing files
- Add `prop_strong_completeness` to `Completeness.lean`
- Add `int_strong_completeness` to `IntCompleteness.lean`
- Add `min_strong_completeness` to `MinCompleteness.lean`

### 8.2 Implementation Order

**Phase 1: Shared Definitions** (in a new `Defs.lean` or in existing files)
1. Define `SetDerivable Axioms Gamma phi`
2. Define `SetSemanticConsequence`, `ISetSemanticConsequence`, `MSetSemanticConsequence`
3. Basic lemmas: `SetDerivable_of_mem`, `SetDerivable_weakening`, `SetDerivable_of_Derivable`

**Phase 2: Minimal Logic Strong Completeness** (simplest, no consistency side condition)
1. Prove `minDeductiveClosure(Gamma) contains Gamma`
2. Prove `phi in minDeductiveClosure(Gamma) <-> SetDerivable MinPropAxiom Gamma phi`
3. Prove `min_strong_completeness` using `min_prime_exclusion` + `min_truth_lemma`

**Phase 3: Intuitionistic Logic Strong Completeness**
1. Handle the consistency case split
2. Prove `intDeductiveClosure(Gamma) is DCCS` when Gamma is Int-consistent
3. Prove `int_strong_completeness` using `int_prime_exclusion` + `int_truth_lemma`

**Phase 4: Classical Logic Strong Completeness** 
1. Prove consistency of `Gamma union {neg phi}` using Peirce's law
2. Prove `prop_strong_completeness` using `prop_lindenbaum` + `prop_truth_lemma`

**Phase 5: Corollaries**
1. Derive weak completeness from strong completeness
2. Biconditional wrappers

### 8.3 Estimated Complexity

- **Phase 1**: ~80-120 lines (definitions + basic lemmas)
- **Phase 2**: ~100-150 lines (most infrastructure already exists)
- **Phase 3**: ~120-180 lines (consistency argument adds complexity)
- **Phase 4**: ~100-150 lines (Peirce-based consistency argument)
- **Phase 5**: ~40-60 lines (straightforward corollaries)

**Total**: ~440-660 lines of new Lean code

---

## 9. Key Technical Risks and Mitigations

### 9.1 Risk: Consistency of `Gamma union {neg phi}` (Classical)

The argument requires showing that if `Gamma |-/- phi`, then adding `neg phi` to Gamma does not cause inconsistency. In the classical case, this uses Peirce's law to derive phi from `neg phi -> bot`. The existing code in `prop_completeness` already does this for `{neg phi}` alone -- extending to `Gamma union {neg phi}` requires a similar but slightly more involved argument.

**Mitigation**: The existing `prop_completeness` proof (lines 318-398 of `Completeness.lean`) contains exactly this argument structure. We can adapt it.

### 9.2 Risk: Consistency Side Condition (Intuitionistic)

For intuitionistic logic, we cannot derive phi from `neg neg phi`. The consistency argument is different: if `Gamma union {neg phi}` is inconsistent, then from some finite `L subset Gamma` we get `L, neg phi |- bot`, hence `L |- neg neg phi`. But this does NOT give `L |- phi` in IPC. 

**Mitigation**: Handle the case split explicitly:
- If Gamma is Int-inconsistent (some finite subset derives bot), then everything is set-derivable from Gamma by EFQ, including phi. Strong completeness holds trivially.
- If Gamma is Int-consistent, then `intDeductiveClosure(Gamma)` is an IntDCCS, and we proceed with the canonical model argument.

### 9.3 Risk: Universe Polymorphism

The existing `IValid` and `MValid` use universe parameters `{u, v}`. The strong completeness statements must be careful about universe levels in `ISetSemanticConsequence` / `MSetSemanticConsequence`. The canonical model construction already works at specific universe levels (e.g., `MinCanonicalWorld Atom` lives in the same universe as `Atom`).

**Mitigation**: Follow the existing patterns in `IntCompleteness.lean` and `MinCompleteness.lean`, which already handle universe polymorphism correctly.

---

## 10. Proof Sketches

### 10.1 Classical Strong Completeness (Detailed Sketch)

```
theorem prop_strong_completeness 
    (h_sc : SetSemanticConsequence Gamma phi) : 
    SetDerivable PropositionalAxiom Gamma phi := by
  by_contra h_not_deriv
  -- Step 1: Show Gamma union {neg phi} is PropSetConsistent
  have h_cons : PropSetConsistent PropositionalAxiom (Gamma union {neg phi}) := by
    intro L hL
    intro hd
    -- From L |- bot where L subset Gamma union {neg phi},
    -- extract L' subset Gamma with L' |- neg phi -> bot (by DT)
    -- Then L' |- phi by Peirce/DNE
    -- This contradicts h_not_deriv since L' subset Gamma
    ...
  -- Step 2: Extend to MCS
  obtain <M, hM_sup, hM_mcs> := prop_lindenbaum h_cons
  -- Step 3: Gamma subset M and neg phi in M
  have h_gamma_sub : Gamma subset M := subset.trans subset_union_left hM_sup
  have h_neg : (neg phi) in M := hM_sup (mem_union_right _ (mem_singleton _))
  -- Step 4: By truth lemma backward, neg phi is true under canonical valuation
  have h_eval_neg := (prop_truth_lemma hM_mcs (neg phi)).mpr h_neg
  -- Step 5: By semantic consequence, phi is true (since all of Gamma is true)
  have h_eval_gamma : forall psi in Gamma, Evaluate (canonicalValuation M) psi :=
    fun psi h_mem => (prop_truth_lemma hM_mcs psi).mpr (h_gamma_sub h_mem)
  have h_eval_phi := h_sc (canonicalValuation M) h_eval_gamma
  -- Step 6: Contradiction
  exact h_eval_neg h_eval_phi
```

### 10.2 Minimal Strong Completeness (Detailed Sketch)

```
theorem min_strong_completeness
    (h_sc : MSetSemanticConsequence Gamma phi) :
    SetDerivable MinPropAxiom Gamma phi := by
  by_contra h_not_deriv
  -- Step 1: minDeductiveClosure(Gamma) is a MinTheory with phi not in it
  have h_theory : MinTheory (minDeductiveClosure Gamma) := minDeductiveClosure_is_theory Gamma
  have h_not_mem : phi not in minDeductiveClosure Gamma := by
    intro h_mem; obtain <L, hL, hd> := h_mem; exact h_not_deriv <L, hL, hd>
  -- Step 2: Extend to prime MinTheory excluding phi
  obtain <T, hT_sup, hT_prime, hT_excl> := min_prime_exclusion h_theory h_not_mem
  -- Step 3: Build canonical world
  let W0 : MinCanonicalWorld Atom := <T, hT_prime>
  -- Step 4: All of Gamma is forced at W0
  have h_gamma_forced : forall psi in Gamma, IForces minCanonicalVal minBotForces W0 psi := by
    intro psi h_mem
    exact (min_truth_lemma W0 psi).mpr 
      (hT_sup (min_subset_deductive_closure Gamma (subset_union_left h_mem)))
  -- Step 5: But phi is not forced at W0
  have h_not_forced : not (IForces minCanonicalVal minBotForces W0 phi) := by
    intro h; exact hT_excl ((min_truth_lemma W0 phi).mp h)
  -- Step 6: Contradiction with semantic consequence
  have h_forced := h_sc (MinCanonicalWorld Atom) minCanonicalVal minBotForces
    (fun p hw hv => minCanonicalVal_upward_closed p hw hv)
    (fun hw hbf => minBotForces_upward_closed hw hbf)
    W0 h_gamma_forced
  exact h_not_forced h_forced
```

---

## 11. Sources

### Papers
- [Intuitionistic Propositional Logic in Lean (Trufas, 2024)](https://arxiv.org/abs/2410.23765) -- Strong completeness for IPL formalized in Lean
- [Verified completeness in Henkin-style for intuitionistic propositional logic (Guo, Chen, Bentzen, 2023)](https://arxiv.org/abs/2310.01916) -- Henkin-style completeness for IPL in Lean
- [A Succinct Formalization of the Completeness of First-Order Logic](https://drops.dagstuhl.de/storage/00lipics/lipics-vol239-types2021/LIPIcs.TYPES.2021.8/LIPIcs.TYPES.2021.8.pdf) -- First-order completeness formalization approaches

### Codebases
- [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) -- Lean 4 logic formalization project
- [Lean4 Logic Formalization Book](https://formalizedformallogic.github.io/Book/) -- Documentation for the Foundation project
- [Bentzen's IPL formalization](https://github.com/bbentzen/ipl) -- Lean formalization of IPL completeness

### Reference
- [Lindenbaum's Lemma (Wikipedia)](https://en.wikipedia.org/wiki/Lindenbaum%27s_lemma)
- [Completeness (logic) (Wikipedia)](https://en.wikipedia.org/wiki/Completeness_(logic))
- [Weak and Strong Completeness (Corcoran)](https://www.academia.edu/33304337/Weak_and_Strong_Completeness)
