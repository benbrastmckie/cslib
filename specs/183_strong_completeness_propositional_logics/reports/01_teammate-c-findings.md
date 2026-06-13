# Teammate C Findings: CSLib Codebase Audit and Proof Architecture Dependencies

## 1. Complete Inventory of Existing Infrastructure

### 1.1 Propositional Formula Type and Theories

**File**: `Cslib/Logics/Propositional/Defs.lean`

- `PL.Proposition Atom` -- inductive with constructors: `atom`, `bot`, `imp`, `and`, `or`
- Derived connectives: `neg` (A -> bot), `top` (bot -> bot), `iff` ((A -> B) /\ (B -> A))
- `Theory Atom := Set (Proposition Atom)` -- theories are arbitrary sets
- Theory instances:
  - `Theory.MPL := empty` -- minimal propositional logic
  - `Theory.IPL := Set.range (fun A => bot -> A)` -- intuitionistic (adds EFQ)
  - `Theory.CPL := Set.range (fun A => neg(neg A) -> A)` -- classical (adds DNE)
- Typeclasses: `IsIntuitionistic T` (efq A : (bot -> A) in T), `IsClassical T` (dne A : (neg neg A -> A) in T)
- `PropositionalConnectives` instance for `Proposition Atom` (bot := .bot, imp := .imp)

### 1.2 Axiom Predicates (Hilbert-style)

**File**: `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`

Three separate inductive types define axiom schemata:

| Axiom Predicate | Constructors | Logic |
|-----------------|-------------|-------|
| `MinPropAxiom` | implyK, implyS, andI, andE1, andE2, orI1, orI2, orE (8 axioms) | Minimal |
| `IntPropAxiom` | same + efq (9 axioms) | Intuitionistic |
| `PropositionalAxiom` | same + efq + peirce (10 axioms) | Classical |

Subsumption theorems:
- `MinPropAxiom.toIntProp` -- every minimal axiom is intuitionistic
- `IntPropAxiom.toProp` -- every intuitionistic axiom is classical

### 1.3 Derivation System (Hilbert-style)

**File**: `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`

- `DerivationTree Axioms Gamma phi : Type` -- inductive with 4 constructors:
  - `ax` (axiom instance), `assumption` (phi in Gamma), `modus_ponens`, `weakening`
- `Deriv Axioms Gamma phi : Prop` := `Nonempty (DerivationTree Axioms Gamma phi)`
- `Derivable Axioms phi : Prop` := `Deriv Axioms [] phi` (empty context)
- `propDerivationSystem Axioms : Metalogic.DerivationSystem (PL.Proposition Atom)` -- connects to generic MCS framework

**Key observation**: The Hilbert system already supports context-based derivability via `Deriv Axioms Gamma phi` where `Gamma : List (PL.Proposition Atom)`. This is the syntactic side needed for strong completeness.

### 1.4 Natural Deduction System

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

- `Theory.Derivation : Ctx Atom -> Proposition Atom -> Type u` -- 10-constructor ND system
- Uses `Finset` contexts (not `List`)
- Theory parameter controls logic strength: `MPL`, `IPL`, `CPL`
- `InferenceSystem` instances for both `Sequent` and `Proposition` types

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`

- `hilbert_iff_nd` -- extensional equivalence between Hilbert and ND systems
- Parameterized over axiom predicate with instantiations for Int and Cl

### 1.5 Proof System Typeclass Hierarchy

**File**: `Cslib/Foundations/Logic/ProofSystem.lean`

Three-level propositional hierarchy:
- `MinimalHilbert` extends `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`
- `IntuitionisticHilbert` extends `MinimalHilbert`, `HasAxiomEFQ`
- `ClassicalHilbert` extends `IntuitionisticHilbert`, `HasAxiomPeirce`

Full conjunction/disjunction axiom typeclasses: `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE`

Tag types: `Propositional.HilbertMin`, `Propositional.HilbertInt`, `Propositional.HilbertCl`

**Files**: `ProofSystem/Instances.lean`, `ProofSystem/IntMinInstances.lean`
- All instances registered for all three tag types

### 1.6 Semantics

#### Boolean Valuations (Classical)

**File**: `Cslib/Logics/Propositional/Semantics/Basic.lean`

- `Valuation Atom := Atom -> Prop` -- bivalent valuations
- `Evaluate v : Proposition Atom -> Prop` -- recursive evaluation (atom, bot, imp, and, or)
- `Tautology phi := forall v, Evaluate v phi` -- valid under ALL valuations

**Note**: No semantic consequence from a set of assumptions is defined. `Tautology` is a single-formula validity notion.

#### Kripke Semantics (Intuitionistic/Minimal)

**File**: `Cslib/Logics/Propositional/Semantics/Kripke.lean`

- `KripkeModel World Atom` -- bundles preorder, valuation, botForces, upward-closure proofs
- `IForces v bot_forces w phi : Prop` -- forcing relation (5 cases: atom, bot, imp, and, or)
  - imp case: `forall w' >= w, IForces w' phi -> IForces w' psi`
- `iforces_persistence` -- forcing is monotone under the preorder
- `IValid phi` -- forced at every world in every intuitionistic Kripke model (botForces = fun _ => False)
- `MValid phi` -- forced at every world in every minimal Kripke model (arbitrary upward-closed botForces)
- `mvalid_implies_ivalid` -- minimal validity implies intuitionistic validity

**Note**: Like `Tautology`, `IValid` and `MValid` are single-formula validity notions. No semantic consequence from a set of formulas is defined for Kripke semantics.

### 1.7 MCS/Lindenbaum Infrastructure (Foundations)

**File**: `Cslib/Foundations/Logic/Metalogic/Consistency.lean`

Generic framework parameterized over `DerivationSystem F`:
- `DerivationSystem F` -- structure with `Deriv`, `weakening`, `assumption`, `mp`
- `Consistent D Gamma` := not D.Deriv Gamma bot
- `SetConsistent D S` -- every finite subset is consistent
- `SetMaximalConsistent D S` -- set-consistent + maximally so
- `consistent_chain_union` -- chain unions preserve consistency (Zorn input)
- `set_lindenbaum` -- Lindenbaum's lemma via `zorn_subset_nonempty`
- `HasDeductionTheorem D` -- separate hypothesis (not bundled)
- `closed_under_derivation` -- MCS closed under derivation (needs DT)
- `implication_property` -- phi -> psi in S and phi in S implies psi in S
- `negation_complete` -- phi in S or neg phi in S

### 1.8 Existing Completeness Results

#### Classical Weak Completeness

**File**: `Cslib/Logics/Propositional/Metalogic/Completeness.lean`

- `canonicalValuation S : Valuation Atom` -- atom p is true iff atom p in S
- `prop_truth_lemma` -- `Evaluate (canonicalValuation S) phi <-> phi in S` for MCS S
- **`prop_completeness`**: `Tautology phi -> Derivable PropositionalAxiom phi`
- `completeness_iff_tautology`: `Tautology phi <-> Derivable PropositionalAxiom phi`

**This is WEAK completeness only**: "every tautology is derivable (from the empty context)."

#### Intuitionistic Weak Completeness

**File**: `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean`

- `IntCanonicalWorld Atom` -- prime DCCS for IntPropAxiom (subtype of `Set (Proposition Atom)`)
- Preorder by set inclusion
- `intCanonicalVal` -- atom p true at world S iff atom p in S
- `int_truth_lemma` -- `IForces intCanonicalVal (fun _ => False) S phi <-> phi in S.val`
- **`int_completeness`**: `IValid phi -> Derivable IntPropAxiom phi`
- `int_soundness_completeness`: `IValid phi <-> Derivable IntPropAxiom phi`

**WEAK completeness only.**

#### Minimal Weak Completeness

**File**: `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`

- `MinCanonicalWorld Atom` -- prime MinTheory for MinPropAxiom
- `minBotForces w := bot in w.val` -- key difference from intuitionistic
- `min_truth_lemma` -- `IForces minCanonicalVal minBotForces S phi <-> phi in S.val`
  - bot case is `Iff.rfl` (trivial) vs multi-step in intuitionistic
- **`min_completeness`**: `MValid phi -> Derivable MinPropAxiom phi`
- `min_soundness_completeness`: `MValid phi <-> Derivable MinPropAxiom phi`

**WEAK completeness only.**

### 1.9 Supporting Infrastructure per Logic

#### Classical MCS

**File**: `Cslib/Logics/Propositional/Metalogic/MCS.lean`

- `PropSetConsistent`, `PropSetMaximalConsistent` -- abbreviations for propDerivationSystem
- `prop_lindenbaum` -- delegates to generic `set_lindenbaum`
- `prop_closed_under_derivation`, `prop_implication_property`, `prop_negation_complete` -- parameterized over Axioms
- `prop_mcs_bot_not_mem`, `prop_mcs_neg_of_not_mem`, `prop_mcs_not_mem_of_neg`, `prop_mcs_mem_iff_neg_not_mem`

#### Intuitionistic Lindenbaum/DCCS

**File**: `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`

- `IntDCCS S` -- consistent + deductively closed set for IntPropAxiom
- `IntPrimeDCCS S` -- IntDCCS + disjunction property
- `intDeductiveClosure S` -- deductive closure
- `int_imp_witness` -- implication witness lemma (key for Kripke completeness)
- `int_prime_exclusion` -- prime exclusion via Zorn's lemma
- `int_theorems_dccs` -- set of theorems is a DCCS
- `int_consistent` -- IntPropAxiom is consistent (proved by lifting to classical)

#### Minimal Lindenbaum/Theory

**File**: `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`

- `MinTheory S` -- deductively closed (NO consistency requirement)
- `MinPrimeTheory S` -- MinTheory + disjunction property
- `minDeductiveClosure S`
- `min_imp_witness` -- simpler than intuitionistic (no EFQ needed)
- `min_prime_exclusion` -- via Zorn's lemma
- `min_theorems_theory` -- set of theorems is a MinTheory
- `min_consistent` -- MinPropAxiom consistent (via lift to classical)

#### Soundness

- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` -- classical: `prop_axiom_sound`, `prop_soundness`, `soundness_tautology`
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` -- `int_axiom_sound`, `int_soundness`, `int_soundness_derivable`
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` -- `min_axiom_sound`, `min_soundness`, `min_soundness_derivable`

#### Deduction Theorem

**File**: `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`

- `deductionTheorem` -- if `A :: Gamma |- B` then `Gamma |- A -> B` (parameterized over Axioms with implyK/implyS proofs)
- `deductionWithMem` -- helper for weakening case
- `prop_has_deduction_theorem` -- generic `HasDeductionTheorem` instance

---

## 2. Gap Analysis: What Strong Completeness Requires

### 2.1 What is Strong Completeness?

**Weak completeness** (currently proved): `Valid phi -> Derivable Axioms phi`
- "Every valid formula is a theorem."

**Strong completeness** (task goal): `Gamma |= phi -> Gamma |- phi`
- "Every semantic consequence of Gamma is derivable from Gamma."
- Equivalently: "If Gamma union {neg phi} is unsatisfiable, then Gamma |- phi."

### 2.2 Missing Definitions

#### For Classical Logic:

1. **`SemanticEntails Gamma phi`** (or `SetEntails`): for all valuations v, if (forall psi in Gamma, Evaluate v psi) then Evaluate v phi
   - Currently no such definition exists
   
2. **`SetDerivable Axioms Gamma phi`**: exists finite L subset Gamma such that Deriv Axioms L phi
   - The `Deriv Axioms Gamma phi` uses `List` contexts but `Gamma` would be a `Set`
   - Need a bridge from `Set` to finite `List` subsets

#### For Intuitionistic Logic:

1. **`ISemanticEntails Gamma phi`**: for all Kripke models, for all worlds w, if (forall psi in Gamma, IForces w psi) then IForces w phi
   - Currently `IValid` only handles the empty set of assumptions

2. **`SetDerivable IntPropAxiom Gamma phi`**: same as classical

#### For Minimal Logic:

1. **`MSemanticEntails Gamma phi`**: for all minimal Kripke models, for all worlds w, if (forall psi in Gamma, IForces v bf w psi) then IForces v bf w phi

2. **`SetDerivable MinPropAxiom Gamma phi`**: same

### 2.3 Proof Strategy for Strong Completeness

The standard approach for all three logics is the **Henkin/canonical model construction with a context parameter**:

1. Assume `Gamma |= phi` but `Gamma |- phi` fails
2. Then `Gamma union {neg phi}` is consistent (syntactically)
3. Extend to an MCS/DCCS/MinTheory M containing Gamma union {neg phi}
4. Build canonical model from M
5. Truth lemma: phi in M iff phi holds in canonical model
6. All of Gamma holds in the model (since Gamma subset M)
7. neg phi holds in the model (since neg phi in M)
8. But Gamma |= phi means phi holds in the model -- contradiction

### 2.4 What Already Exists for Each Step

| Step | Classical | Intuitionistic | Minimal |
|------|-----------|----------------|---------|
| Lindenbaum (extend consistent set to MCS) | `prop_lindenbaum` | `int_prime_exclusion` | `min_prime_exclusion` |
| Canonical model/valuation | `canonicalValuation` | `IntCanonicalWorld` + preorder | `MinCanonicalWorld` + preorder |
| Truth lemma | `prop_truth_lemma` | `int_truth_lemma` | `min_truth_lemma` |
| Soundness (validates weak side) | `prop_soundness` | `int_soundness` | `min_soundness` |
| Consistency of neg phi context | needs `prop_mcs_neg_of_not_mem` variant | needs new | needs new |

### 2.5 What Must Be Built

#### Definitions (shared across all three):

1. **`SetDerivable Axioms (Gamma : Set (Proposition Atom)) phi`**:
   ```
   exists L : List (Proposition Atom), (forall x in L, x in Gamma) /\ Deriv Axioms L phi
   ```

#### Per-logic definitions:

2. **Classical `SemanticEntails`**:
   ```
   def SemanticEntails (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) :=
     forall v : Valuation Atom, (forall psi in Gamma, Evaluate v psi) -> Evaluate v phi
   ```

3. **Intuitionistic `ISemanticEntails`**:
   ```
   def ISemanticEntails (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) :=
     forall World [Preorder World] val v_uc w,
       (forall psi in Gamma, IForces val (fun _ => False) w psi) ->
       IForces val (fun _ => False) w phi
   ```

4. **Minimal `MSemanticEntails`**:
   ```
   def MSemanticEntails (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) :=
     forall World [Preorder World] val bf v_uc bf_uc w,
       (forall psi in Gamma, IForces val bf w psi) ->
       IForces val bf w phi
   ```

#### Per-logic theorems:

5. **Strong soundness** (for each): `SetDerivable Axioms Gamma phi -> SemanticEntails Gamma phi`
   - Follows easily from existing per-formula soundness + weakening

6. **Strong completeness** (for each): `SemanticEntails Gamma phi -> SetDerivable Axioms Gamma phi`
   - This is the main theorem

7. **Biconditional wrappers**: `SemanticEntails Gamma phi <-> SetDerivable Axioms Gamma phi`

---

## 3. Dependency Graph

### 3.1 Existing Dependencies (already built)

```
Foundations/Logic/Metalogic/Consistency.lean
  |-- DerivationSystem, SetConsistent, SetMaximalConsistent, set_lindenbaum, HasDeductionTheorem
  |
  v
Propositional/ProofSystem/Derivation.lean
  |-- DerivationTree, Deriv, Derivable, propDerivationSystem
  |
  v
Propositional/ProofSystem/Axioms.lean
  |-- MinPropAxiom, IntPropAxiom, PropositionalAxiom, subsumption
  |
  v
Propositional/Metalogic/DeductionTheorem.lean
  |-- deductionTheorem, prop_has_deduction_theorem
  |
  v
Propositional/Metalogic/MCS.lean             (classical)
Propositional/Metalogic/IntLindenbaum.lean    (intuitionistic)
Propositional/Metalogic/MinLindenbaum.lean    (minimal)
  |
  v
Propositional/Metalogic/Completeness.lean     (classical weak)
Propositional/Metalogic/IntCompleteness.lean  (intuitionistic weak)
Propositional/Metalogic/MinCompleteness.lean  (minimal weak)
```

### 3.2 New Dependencies (to be built)

```
NEW: Propositional/Semantics/SemanticConsequence.lean
  |-- SemanticEntails, ISemanticEntails, MSemanticEntails
  |-- SetDerivable (shared definition)
  |
  v
NEW: Propositional/Metalogic/StrongSoundness.lean
  |-- strong_soundness (classical)
  |-- int_strong_soundness (intuitionistic)
  |-- min_strong_soundness (minimal)
  |   (each follows from per-formula soundness + weakening)
  |
  v
NEW: Propositional/Metalogic/StrongCompleteness.lean
  |-- strong_completeness (classical)
  |   Deps: prop_lindenbaum, prop_truth_lemma, SemanticEntails, SetDerivable
  |
NEW: Propositional/Metalogic/IntStrongCompleteness.lean
  |-- int_strong_completeness (intuitionistic)
  |   Deps: int_prime_exclusion, int_truth_lemma, ISemanticEntails, SetDerivable
  |
NEW: Propositional/Metalogic/MinStrongCompleteness.lean
  |-- min_strong_completeness (minimal)
  |   Deps: min_prime_exclusion, min_truth_lemma, MSemanticEntails, SetDerivable
```

### 3.3 Shared vs Per-Logic Work

**Shared (define once)**:
- `SetDerivable Axioms Gamma phi` -- works for all three axiom predicates
- Basic `SetDerivable` lemmas: weakening, assumption, modus ponens
- Relationship between `SetDerivable` and `Derivable`: `SetDerivable Axioms empty phi <-> Derivable Axioms phi`

**Per-logic (three copies, but structurally similar)**:
- Semantic entailment definition (3 variants)
- Strong soundness (3 variants -- easy)
- Strong completeness (3 variants -- main work)

---

## 4. Kripke Semantics Status

### 4.1 What Exists

- Full Kripke semantics defined in `Cslib/Logics/Propositional/Semantics/Kripke.lean`
- `IForces` covers all 5 proposition constructors (atom, bot, imp, and, or)
- `iforces_persistence` proved
- `KripkeModel` structure defined (not used in completeness proofs -- they use unbundled components)
- `IValid` and `MValid` defined
- `mvalid_implies_ivalid` proved

### 4.2 What's Missing for Strong Completeness

The Kripke semantics infrastructure is complete for strong completeness. The only missing piece is the **semantic entailment definitions** that quantify over a set of assumptions (as noted in Section 2.2 above).

### 4.3 Comparison with Modal Kripke Semantics

The Modal logic (`Cslib/Logics/Modal/`) has its own Kripke frames/models/semantics:
- `Modal.Satisfies` -- satisfaction relation
- `Modal.Valid` -- validity
- Separate `Completeness.lean` for K, T, S4, S5, etc. (15 systems)

The propositional Kripke semantics intentionally does NOT reuse the modal infrastructure because:
- Intuitionistic implication requires quantification over ALL accessible successors (not just local evaluation)
- This is semantically different from modal `Satisfies`
- Noted explicitly in the Kripke.lean docstring

No infrastructure sharing between propositional Kripke and modal Kripke is possible or desirable.

---

## 5. Proof Complexity Assessment

### 5.1 Classical Strong Completeness

**Estimated difficulty: LOW**

The existing `prop_completeness` proof is almost exactly the proof of strong completeness, just specialized to `Gamma = empty`. The key change:
- Instead of starting from `{neg phi}` being consistent, start from `Gamma union {neg phi}` being consistent
- This requires showing that `Gamma union {neg phi}` is consistent iff `Gamma` does not derive `phi`
- Existing `prop_lindenbaum` and `prop_truth_lemma` work unchanged
- The canonical valuation satisfies all of `Gamma` because `Gamma subset M`

**Key helper needed**: If `Gamma` does not derive `phi` (SetDerivable), then `Gamma union {neg phi}` is set-consistent. This follows from the deduction theorem (already proved).

### 5.2 Intuitionistic Strong Completeness

**Estimated difficulty: MEDIUM**

Similar structure to classical but:
- Must extend `Gamma union {neg phi}` to a prime DCCS (not just MCS)
- The existing `int_prime_exclusion` starts from an IntDCCS, not a raw set
- Need: first close `Gamma` under IntPropAxiom derivation to get an IntDCCS, then apply prime exclusion
- Existing `intDeductiveClosure` + `intDeductiveClosure_is_dccs` handle this
- But must show `phi not in intDeductiveClosure(Gamma)` iff `Gamma` does not derive `phi`

Wait -- actually there's a subtlety. For intuitionistic strong completeness with Kripke semantics, the canonical model has multiple worlds (prime DCCSs), not just one. The semantic entailment must hold at ALL worlds, not just the initial world. But persistence of forcing (iforces_persistence) + the fact that all Gamma formulas are in every world that extends the initial DCCS handles this.

### 5.3 Minimal Strong Completeness

**Estimated difficulty: MEDIUM**

Same structure as intuitionistic but:
- Uses MinTheory (no consistency requirement) instead of IntDCCS
- `minDeductiveClosure` is always a MinTheory (even if inconsistent)
- The `min_prime_exclusion` works from any MinTheory
- Key simplification: bot case in truth lemma is `Iff.rfl`

---

## 6. Relevant Mathlib Infrastructure

### 6.1 Zorn's Lemma (already used)

- `zorn_subset_nonempty` from `Mathlib.Order.Zorn` -- used in all three Lindenbaum lemmas

### 6.2 Filter/Ultrafilter (NOT needed)

- Mathlib has `Filter`, `Ultrafilter`, `Ultrafilter.exists_le` etc.
- These are NOT needed for propositional strong completeness
- The MCS construction (Lindenbaum) is the right tool, already fully implemented

### 6.3 FirstOrder.Language.Theory.IsMaximal (informational)

- Mathlib has `FirstOrder.Language.Theory.IsMaximal` in `Mathlib.ModelTheory.Satisfiability`
- This is for first-order model theory, not propositional logic
- Not directly reusable but conceptually analogous

---

## 7. File Organization Recommendation

### Option A: Minimal new files (recommended)

1. `Semantics/SemanticConsequence.lean` -- all 3 semantic entailment defs + SetDerivable + basic lemmas
2. `Metalogic/StrongCompleteness.lean` -- classical strong completeness + strong soundness
3. `Metalogic/IntStrongCompleteness.lean` -- intuitionistic strong completeness + strong soundness
4. `Metalogic/MinStrongCompleteness.lean` -- minimal strong completeness + strong soundness

### Option B: Grouped by operation

1. `Semantics/SemanticConsequence.lean` -- all 3 semantic entailment defs + SetDerivable
2. `Metalogic/StrongSoundness.lean` -- all 3 strong soundness theorems
3. `Metalogic/StrongCompleteness.lean` -- classical strong completeness
4. `Metalogic/IntStrongCompleteness.lean` -- intuitionistic strong completeness
5. `Metalogic/MinStrongCompleteness.lean` -- minimal strong completeness

---

## 8. Risk Assessment

### Low risk:
- Classical strong completeness -- trivial lift from existing weak completeness
- Semantic entailment definitions -- straightforward generalizations
- Strong soundness for all three -- direct from existing per-formula soundness

### Medium risk:
- Intuitionistic/minimal strong completeness -- the multi-world canonical model construction requires care:
  - Must ensure the initial world (built from Gamma's closure) excludes phi
  - Must ensure all of Gamma is forced at the initial world
  - The persistence argument must carry through

### No risk items:
- Kripke semantics -- fully built, no changes needed
- MCS/Lindenbaum infrastructure -- fully built, no changes needed
- Deduction theorem -- fully built for all three axiom predicates
- Axiom subsumption -- fully built

---

## 9. Summary

**Existing infrastructure coverage**: approximately 85-90% of what's needed is already built.

**What must be added**:
1. Three semantic entailment definitions (trivial generalizations of existing validity defs)
2. One shared `SetDerivable` definition with basic lemmas
3. Three strong soundness theorems (easy, follow from existing per-formula soundness)
4. Three strong completeness theorems (main work, but closely follow existing weak completeness proofs)

**Total estimated new code**: ~400-600 lines across 3-4 new files.

**Key architectural insight**: The existing weak completeness proofs already contain 95% of the logic needed for strong completeness. The canonical model construction, truth lemma, and Lindenbaum extension all work for arbitrary consistent sets (not just {neg phi}). The main new work is:
- Defining the semantic consequence notions
- Showing that `Gamma` not deriving `phi` implies `Gamma union {neg phi}` is consistent
- Connecting the dots in the final contradiction argument
