# Task 175: Modal And/Or Propagation -- Research Report

Session: sess_1781317385_e83d59_175

## 1. Executive Summary

This task propagates the hybrid five-primitive design from Propositional to Modal logic.
Currently, Modal.Proposition has 4 constructors `{atom, bot, imp, box}` with `and`/`or`
as Lukasiewicz-derived `abbrev`s. The target is 6 constructors `{atom, bot, imp, and, or, box}`
with `diamond`/`neg`/`top`/`iff` remaining derived. This mirrors what task 173 already completed
for PL.Proposition `{atom, bot, imp, and, or}`.

The change touches 5 layers of the Modal codebase spanning 55 files. The critical insight
is that the existing `Satisfies` relation, `DerivationTree`, truth lemmas, and soundness
proofs are all parameterized over axiom predicates -- the parameterized infrastructure
itself does NOT need modification for the and/or cases. Only the concrete axiom predicates
for each system and their soundness/completeness instantiations need extension.

## 2. Current Architecture

### 2.1 Modal.Proposition (Basic.lean, lines 46-55)

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (phi1 phi2 : Proposition Atom)
  | box (phi : Proposition Atom)
  deriving DecidableEq, BEq
```

Derived connectives (lines 57-77):
- `neg phi := .imp phi .bot`  (abbrev)
- `top := .imp .bot .bot`  (abbrev)
- `or phi1 phi2 := .imp (.imp phi1 .bot) phi2`  (abbrev -- Lukasiewicz)
- `and phi1 phi2 := .imp (.imp phi1 (.imp phi2 .bot)) .bot`  (abbrev -- Lukasiewicz)
- `diamond phi := .neg (.box (.neg phi))`  (abbrev)
- `iff phi1 phi2 := .and (.imp phi1 phi2) (.imp phi2 phi1)`  (abbrev)

### 2.2 Satisfies (Basic.lean, lines 97-102)

```lean
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom -> Prop
  | .atom p => m.v w p
  | .bot => False
  | .imp phi1 phi2 => Satisfies m w phi1 -> Satisfies m w phi2
  | .box phi => forall w', m.r w w' -> Satisfies m w' phi
```

The and/or satisfaction is proved via separate theorems (`Satisfies.and_iff`, `Satisfies.or_iff`)
that unfold the Lukasiewicz encodings and use classical reasoning. With native constructors,
these become direct structural clauses.

### 2.3 ProofSystem Instances (15 systems)

Each system has an axiom predicate inductive with 4 propositional constructors
(`implyK`, `implyS`, `efq`, `peirce`) plus system-specific modal axioms. The 15 systems are:

| System | Axiom Predicate | Propositional Axioms | Modal Axioms | Instance File |
|--------|----------------|---------------------|--------------|---------------|
| K | KAxiom | 4 (K,S,EFQ,P) | 1 (K) | K.lean |
| T | TAxiom | 4 | 2 (K,T) | T.lean |
| D | DAxiom | 4 | 2 (K,D) | D.lean |
| B | BAxiom | 4 | 2 (K,B) | B.lean |
| K4 | K4Axiom | 4 | 2 (K,4) | K4.lean |
| K5 | K5Axiom | 4 | 2 (K,5) | K5.lean |
| K45 | K45Axiom | 4 | 3 (K,4,5) | K45.lean |
| KB5 | KB5Axiom | 4 | 3 (K,B,5) | KB5.lean |
| D4 | D4Axiom | 4 | 3 (K,D,4) | D4.lean |
| D5 | D5Axiom | 4 | 3 (K,D,5) | D5.lean |
| D45 | D45Axiom | 4 | 4 (K,D,4,5) | D45.lean |
| DB | DBAxiom | 4 | 3 (K,D,B) | DB.lean |
| TB | TBAxiom | 4 | 3 (K,T,B) | TB.lean |
| S4 | S4Axiom | 4 | 3 (K,T,4) | S4.lean |
| S5 | ModalAxiom | 4 | 4 (K,T,4,B) | S5.lean |

Note: `ModalAxiom` in `DerivationTree.lean` is the S5 axiom set (8 constructors).

### 2.4 Metalogic Truth Lemma Families

There are **three** truth lemma families, differing in the box-witness:

1. **`truth_lemma`** (Completeness.lean): For logics containing axiom T. Uses
   `mcs_box_witness`. Used by: S5, T, S4, TB.

2. **`k_truth_lemma`** (K/Completeness.lean): For logics NOT containing T or D.
   Uses `k_mcs_box_witness`. Used by: K, B, K4, K5, K45, KB5.

3. **`truth_lemma_d`** (D/Completeness.lean): For logics containing D but NOT T.
   Uses `mcs_box_witness_d`. Used by: D, D4, D5, D45, DB.

All three match on `Proposition Atom` with exactly 4 cases: `.atom`, `.bot`, `.imp`, `.box`.
Adding `.and` and `.or` constructors requires extending all three.

### 2.5 Existing sorry in FromPropositional.lean

`modal_satisfies_toModal_iff_evaluate` has two `sorry` entries (lines 97, 101) for the
`and` and `or` cases. The comment says these are deferred because the Lukasiewicz encoding
is only classically equivalent. Adding native and/or constructors to Modal will let these
be completed.

## 3. Change Analysis by File

### Layer 1: Core Definitions (Basic.lean)

**File**: `Cslib/Logics/Modal/Basic.lean`
**Lines affected**: ~400 -> ~430
**Changes**:
1. **Proposition inductive** (line 46): Add `| and (phi1 phi2)` and `| or (phi1 phi2)` constructors
2. **Derived `and`/`or`**: Change from `abbrev` to derived-satisfaction lemmas (keep the
   abbrev names but repurpose them, or remove and let the constructors serve directly)
   - Actually: DELETE the `abbrev Proposition.and` and `abbrev Proposition.or` definitions
   - The `.and` and `.or` constructors replace them
   - `Proposition.neg`, `Proposition.top`, `Proposition.diamond`, `Proposition.iff` remain `abbrev`s
3. **Satisfies** (line 98): Add two clauses:
   ```lean
   | .and phi1 phi2 => Satisfies m w phi1 /\ Satisfies m w phi2
   | .or phi1 phi2 => Satisfies m w phi1 \/ Satisfies m w phi2
   ```
4. **Satisfaction lemmas**: `Satisfies.and_iff` and `Satisfies.or_iff` become trivial
   (`Iff.rfl`) instead of classical proofs
5. **ModalConnectives instance** (line 90): Currently registers `bot`, `imp`, `box`.
   Does NOT change (ModalConnectives doesn't include HasAnd/HasOr).
6. **NEW: HasAnd/HasOr instances**: Add:
   ```lean
   instance : HasAnd (Proposition Atom) where and := .and
   instance : HasOr (Proposition Atom) where or := .or
   ```
7. **Notation**: `scoped infix:36 " /\ "` and `scoped infix:35 " \/ "` already point to
   `Proposition.and` / `Proposition.or`. Since these will now be constructors instead of
   abbrevs, the notation continues to work.

### Layer 2: Denotation, LogicalEquivalence, Cube (3 files)

**File**: `Cslib/Logics/Modal/Denotation.lean`
**Changes**:
- `Proposition.denotation`: Add 2 cases:
  ```lean
  | .and phi1 phi2 => phi1.denotation m ∩ phi2.denotation m
  | .or phi1 phi2 => phi1.denotation m ∪ phi2.denotation m
  ```
- `satisfies_mem_denotation`: Add 2 induction cases for `and`/`or`
- `neg_denotation`: May need adjustment if it unfolds through and/or

**File**: `Cslib/Logics/Modal/LogicalEquivalence.lean`
**Changes**:
- `Proposition.Context`: Add 4 new constructors:
  ```lean
  | andL (c : Context Atom) (phi : Proposition Atom)
  | andR (phi : Proposition Atom) (c : Context Atom)
  | orL (c : Context Atom) (phi : Proposition Atom)
  | orR (phi : Proposition Atom) (c : Context Atom)
  ```
- `Context.fill`: Add 4 cases
- `LogicallyEquivalent.congruence`: Add 4 induction cases

**File**: `Cslib/Logics/Modal/Cube.lean`
- No changes needed. The `Cube.lean` definitions use `Proposition.valid` and `logic`,
  which operate at the level of sets of propositions. The inductive change is transparent
  to them. The validity proofs (`K.k_valid`, `T.t_valid`) use `grind` and do not
  pattern-match on Proposition constructors.

### Layer 3: FromPropositional.lean

**File**: `Cslib/Logics/Modal/FromPropositional.lean`
**Changes**:
- `PL.Proposition.toModal`: The `and`/`or` cases currently map to `abbrev`s:
  ```lean
  | .and phi1 phi2 => phi1.toModal.and phi2.toModal  -- was Lukasiewicz
  | .or phi1 phi2 => phi1.toModal.or phi2.toModal    -- was Lukasiewicz
  ```
  With native constructors, these become **homomorphic**:
  ```lean
  | .and phi1 phi2 => .and (phi1.toModal) (phi2.toModal)
  | .or phi1 phi2 => .or (phi1.toModal) (phi2.toModal)
  ```
- `modal_satisfies_toModal_iff_evaluate`: The two `sorry` entries can be completed:
  ```lean
  | and phi psi ih1 ih2 =>
    constructor
    . intro <h1, h2>; exact <ih1.mp h1, ih2.mp h2>
    . intro <h1, h2>; exact <ih1.mpr h1, ih2.mpr h2>
  | or phi psi ih1 ih2 =>
    constructor
    . intro h; cases h with
      | inl h => exact Or.inl (ih1.mp h)
      | inr h => exact Or.inr (ih2.mp h)
    . intro h; cases h with
      | inl h => exact Or.inl (ih1.mpr h)
      | inr h => exact Or.inr (ih2.mpr h)
  ```

### Layer 4: ProofSystem/Instances (15 + 1 files)

**File**: `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`
**Changes**:
- `ModalAxiom` (S5 axiom set): Add 6 constructors:
  ```lean
  | andI (phi psi) : ModalAxiom (phi.imp (psi.imp (phi.and psi)))
  | andE1 (phi psi) : ModalAxiom ((phi.and psi).imp phi)
  | andE2 (phi psi) : ModalAxiom ((phi.and psi).imp psi)
  | orI1 (phi psi) : ModalAxiom (phi.imp (phi.or psi))
  | orI2 (phi psi) : ModalAxiom (psi.imp (phi.or psi))
  | orE (phi psi chi) : ModalAxiom ((phi.imp chi).imp ((psi.imp chi).imp ((phi.or psi).imp chi)))
  ```
  (from 8 to 14 constructors)

**15 Instance Files** (K.lean through DB.lean): Each axiom predicate (`KAxiom`, `TAxiom`,
etc.) needs the same 6 and/or axiom constructors added. Each instance file also needs
6 new `HasAxiom*` instance registrations:
```lean
instance : HasAxiomAndI Modal.HilbertX (F := Modal.Proposition Atom) where
  andI := <Modal.DerivationTree.ax [] _ (Modal.XAxiom.andI _ _)>
-- ... similarly for AndE1, AndE2, OrI1, OrI2, OrE
```

**File**: `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- barrel import, no changes needed.

### Layer 5: Metalogic (5 core + 30 system files)

#### 5a. Parameterized Infrastructure (5 files)

**Soundness.lean**: The parameterized `soundness` theorem matches on `DerivationTree`
constructors (`.ax`, `.assumption`, `.modus_ponens`, `.necessitation`, `.weakening`), NOT
on `Proposition`. **No change needed.**

**DeductionTheorem.lean**: Matches on `DerivationTree` constructors. **No change needed.**

**MCS.lean**: Uses `DerivationTree` constructors and `modalDerivationSystem`. **No change needed.**

**Completeness.lean**: Contains `truth_lemma` which matches on `Proposition` with 4 cases.
**Add 2 cases** for `.and` and `.or`:
```lean
| .and phi psi => by
  constructor
  . intro <h1, h2>
    -- phi in S and psi in S, so phi.and psi in S by AndI axiom
    ...
  . intro h_mem
    -- phi.and psi in S, so phi in S by AndE1 and psi in S by AndE2
    constructor
    . exact (truth_lemma ... S phi).mpr (mcs_mp_axiom ... h_mem (h_andE1 phi psi))
    . exact (truth_lemma ... S psi).mpr (mcs_mp_axiom ... h_mem (h_andE2 phi psi))
| .or phi psi => by
  constructor
  . intro h
    cases h with
    | inl h1 =>
      have := (truth_lemma ... S phi).mp h1
      exact mcs_mp_axiom ... this (h_orI1 phi psi)
    | inr h2 =>
      have := (truth_lemma ... S psi).mp h2
      exact mcs_mp_axiom ... this (h_orI2 phi psi)
  . intro h_mem
    rcases modal_negation_complete ... S phi with hp | hnp
    . exact Or.inl ((truth_lemma ... S phi).mpr hp)
    . -- neg phi in S, phi.or psi in S
      -- Need: OrE + neg phi gives psi in S, then Or.inr
      ...
```

The truth_lemma will need **additional axiom hypotheses**:
```lean
(h_andI : forall (phi psi), Axioms (phi.imp (psi.imp (phi.and psi))))
(h_andE1 : forall (phi psi), Axioms ((phi.and psi).imp phi))
(h_andE2 : forall (phi psi), Axioms ((phi.and psi).imp psi))
(h_orI1 : forall (phi psi), Axioms (phi.imp (phi.or psi)))
(h_orI2 : forall (phi psi), Axioms (psi.imp (phi.or psi)))
(h_orE : forall (phi psi chi), Axioms ((phi.imp chi).imp ((psi.imp chi).imp ((phi.or psi).imp chi))))
```

Similarly for `k_truth_lemma` and `truth_lemma_d`.

**neg_consistent_of_not_derivable** (Completeness.lean): Does not match on Proposition.
**No change needed.**

#### 5b. System-Specific Files (30 files)

Each system has a Soundness.lean and Completeness.lean file.

**Soundness files (15)**: Each `*_axiom_sound` theorem matches on the system's axiom
predicate. Adding 6 new constructors means adding 6 new cases. All 6 are propositional
and identical across systems:

```lean
| andI phi psi =>
  intro h1 h2; exact <h1, h2>
| andE1 phi psi =>
  intro <h1, _>; exact h1
| andE2 phi psi =>
  intro <_, h2>; exact h2
| orI1 phi psi =>
  intro h; exact Or.inl h
| orI2 phi psi =>
  intro h; exact Or.inr h
| orE phi psi chi =>
  intro h1 h2 h3
  cases h3 with
  | inl hp => exact h1 hp
  | inr hp => exact h2 hp
```

These cases are frame-independent (no modal content), so they are the same for all 15 systems.

**Completeness files (15)**: Each completeness theorem calls one of the three truth lemma
families. The 6 new axiom hypotheses must be passed through. The pattern is mechanical:
```lean
-- For T system, currently:
(truth_lemma ... (fun phi => .efq phi) (fun phi psi => .peirce phi psi) ...)
-- Add:
(fun phi psi => .andI phi psi)
(fun phi psi => .andE1 phi psi)
(fun phi psi => .andE2 phi psi)
(fun phi psi => .orI1 phi psi)
(fun phi psi => .orI2 phi psi)
(fun phi psi chi => .orE phi psi chi)
```

## 4. Dependency Analysis

The changes must be applied in a strict dependency order:

```
Phase 1: Basic.lean (Proposition inductive + Satisfies + HasAnd/HasOr instances)
    |
Phase 2: Denotation.lean, LogicalEquivalence.lean, FromPropositional.lean (parallel)
    |
Phase 3: DerivationTree.lean (ModalAxiom + all 15 system axiom predicates)
    |      Note: ModalAxiom is in DerivationTree.lean; system axioms are in
    |      ProofSystem/Instances/*.lean files
    |
Phase 4: ProofSystem/Instances/*.lean (16 files: add 6 and/or axiom constructors
    |      to each axiom predicate + register HasAxiom* instances)
    |
Phase 5: Metalogic core (truth_lemma, k_truth_lemma, truth_lemma_d -- add and/or cases)
    |
Phase 6: Metalogic/Systems/*/{Soundness,Completeness}.lean (30 files: add axiom sound
         cases + pass through and/or axiom hypotheses)
```

**Critical ordering constraints**:
- Phase 1 must complete before any other phase (all files import Basic.lean)
- Phase 3 must complete before Phase 4 (Instances import DerivationTree)
- Phase 4 must complete before Phase 5 (truth lemmas use axiom predicates)
- Phase 5 must complete before Phase 6 (system files call truth lemmas)
- Phases within a layer (e.g., the 15 soundness files) are independent of each other

## 5. Estimated Change Scope

| File / Group | Files | Est. Lines Changed | Difficulty |
|---|---|---|---|
| Basic.lean | 1 | ~40 | Medium (core type change) |
| Denotation.lean | 1 | ~20 | Easy (structural) |
| LogicalEquivalence.lean | 1 | ~30 | Easy (add context cases) |
| Cube.lean | 1 | 0 | None |
| FromPropositional.lean | 1 | ~20 | Easy (remove 2 sorry) |
| DerivationTree.lean (ModalAxiom) | 1 | ~15 | Easy (add constructors) |
| ProofSystem/Instances/*.lean | 15 | ~40 each, ~600 total | Medium (repetitive) |
| Metalogic core (3 truth lemmas) | 3 | ~60 each, ~180 total | Hard (proof engineering) |
| System Soundness files | 15 | ~15 each, ~225 total | Easy (identical cases) |
| System Completeness files | 15 | ~20 each, ~300 total | Medium (pass axiom hyps) |
| **Total** | **55** | **~1430** | |

## 6. Risk Assessment

### 6.1 DecidableEq / BEq

Adding constructors to the inductive preserves `deriving DecidableEq, BEq` -- Lean 4
auto-derives for all constructors of an inductive with decidable fields.

### 6.2 Notation Conflict

The `scoped infix:36 " /\ " => Proposition.and` notation currently resolves to the `abbrev`.
When `Proposition.and` becomes a constructor, this notation continues to work because
Lean resolves `Proposition.and` by name, not by its definition kind.

### 6.3 Upstream grind/simp Annotations

The `@[scoped grind]` annotation on `Satisfies` will automatically pick up the new cases.
The `@[scoped grind =]` theorems for and/or characterization (`Satisfies.and_iff_and`,
`Satisfies.or_iff_or`) will become trivial `Iff.rfl` proofs.

### 6.4 Truth Lemma Signature Growth

The truth lemma will grow from ~6 axiom hypotheses to ~12. This is unavoidable but follows
the existing parameterization pattern. The `truth_lemma`, `k_truth_lemma`, and
`truth_lemma_d` all need the same 6 new hypotheses.

### 6.5 iff Derived Connective

`Proposition.iff` is currently defined as `.and (.imp phi1 phi2) (.imp phi2 phi1)`.
With native `.and`, this remains well-typed -- it uses the constructor directly.

### 6.6 Completeness truth_lemma Or Case

The `.or` case of the truth lemma is the most technically challenging. The forward direction
(Satisfies -> membership) requires showing that `phi.or psi in S` given `phi in S` (via OrI1)
or `psi in S` (via OrI2). The backward direction (membership -> Satisfies) requires showing
that `phi.or psi in S` implies `Satisfies m w phi \/ Satisfies m w psi`. This uses the OrE
axiom together with negation completeness: either `phi in S` (done) or `neg phi in S`, and
from `neg phi in S` and `phi.or psi in S` we derive `psi in S` using OrE + MP.

This proof pattern is standard in Hilbert-style completeness theory and matches how the
Propositional layer handles it in its MCS completeness proof.

## 7. Recommendations

### 7.1 Phase Plan

The implementation should proceed in 6 phases matching the dependency analysis above.
Phases 2 and the individual system files within Phases 5-6 have internal parallelism.

### 7.2 Template Approach for System Files

The 15 axiom predicate extensions and 30 system soundness/completeness files follow
identical patterns. A template-driven approach (modify one exemplar, replicate to others)
is recommended.

### 7.3 Existing sorry Resolution

The 2 `sorry` entries in FromPropositional.lean are directly resolved by this task.
They should be completed in Phase 2.

### 7.4 ModalConnectives Extension

The task description mentions registering `HasAnd`/`HasOr` instances "from task 172".
Looking at the `ModalConnectives` class definition (Connectives.lean line 97):
```lean
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F
```
This does NOT extend `HasAnd`/`HasOr`. The `HasAnd`/`HasOr` instances should be registered
as standalone instances on `Modal.Proposition Atom`, matching the pattern used in PL:
```lean
instance : HasAnd (Proposition Atom) where and := .and
instance : HasOr (Proposition Atom) where or := .or
```

### 7.5 DeductionTheorem Stability

The deduction theorem matches on `DerivationTree` constructors, not `Proposition` constructors.
Since the `DerivationTree` inductive is unchanged (still 5 constructors: ax, assumption,
modus_ponens, necessitation, weakening), the deduction theorem requires NO modification.

### 7.6 MCS Stability

All MCS lemmas (`mcs_mp_axiom`, `mcs_box_closure`, `mcs_box_box`, `mcs_box_diamond`, etc.)
operate at the level of set membership and derivability, not pattern matching on Proposition.
They require NO modification.
