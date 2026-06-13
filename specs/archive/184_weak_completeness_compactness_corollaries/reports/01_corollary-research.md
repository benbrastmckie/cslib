# Research Report: Weak Completeness and Compactness as Corollaries of Strong Completeness

## Task 184

## 1. What Already Exists from Task 183

Task 183 delivered four files:

### SemanticConsequence.lean
Defines the foundational infrastructure:
- `SetDerivable Axioms Gamma phi`: finite-list derivability from a set
- `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails`: semantic consequence for classical, intuitionistic, minimal
- `SetDerivable_empty_iff`: `SetDerivable Axioms empty phi <-> Derivable Axioms phi` (KEY BRIDGE)
- `SetDerivable_of_mem`, `SetDerivable_weakening`, `SetDerivable_of_Derivable`, `SetDerivable_mp`
- `SemanticEntails_of_Tautology`, `ISemanticEntails_of_IValid`, `MSemanticEntails_of_MValid`

### StrongCompleteness.lean
- `prop_strong_soundness`: `SetDerivable PropositionalAxiom Gamma phi -> SemanticEntails Gamma phi`
- `prop_strong_completeness`: `SemanticEntails Gamma phi -> SetDerivable PropositionalAxiom Gamma phi`
- `prop_strong_completeness_iff`: biconditional wrapper
- `prop_compactness`: compactness corollary (ALREADY EXISTS)

### IntStrongCompleteness.lean
- `int_strong_soundness`, `int_strong_completeness`, `int_strong_completeness_iff`
- `int_compactness` (ALREADY EXISTS)
- Helper: `intDeductiveClosure_iff_SetDerivable`, `SetDerivable_efq_int`

### MinStrongCompleteness.lean
- `min_strong_soundness`, `min_strong_completeness`, `min_strong_completeness_iff`
- `min_compactness` (ALREADY EXISTS)
- Helper: `minDeductiveClosure_iff_SetDerivable`

## 2. Existing Weak Completeness Theorems

### Completeness.lean (409 lines)
Contains both INFRASTRUCTURE and the weak completeness theorem:
- **Infrastructure** (lines 1-309): `canonicalValuation`, `prop_truth_lemma` (truth lemma for classical MCS worlds) -- these are REUSED by StrongCompleteness.lean
- **Weak theorem** (lines 316-398): `prop_completeness (phi) (h_taut : Tautology phi) : Derivable PropositionalAxiom phi` -- standalone 82-line proof via Lindenbaum + canonical model
- **Biconditional** (lines 404-407): `completeness_iff_tautology : Tautology phi <-> Derivable PropositionalAxiom phi`

### IntCompleteness.lean (210 lines)
Contains both INFRASTRUCTURE and the weak completeness theorem:
- **Infrastructure** (lines 1-178): `IntCanonicalWorld`, `intCanonicalVal`, `int_truth_lemma` -- REUSED by IntStrongCompleteness.lean
- **Weak theorem** (lines 185-199): `int_completeness (h_valid : IValid phi) : Derivable IntPropAxiom phi` -- 15-line proof
- **Biconditional** (lines 205-208): `int_soundness_completeness`

### MinCompleteness.lean (226 lines)
Contains both INFRASTRUCTURE and the weak completeness theorem:
- **Infrastructure** (lines 1-191): `MinCanonicalWorld`, `minCanonicalVal`, `minBotForces`, `min_truth_lemma` -- REUSED by MinStrongCompleteness.lean
- **Weak theorem** (lines 199-215): `min_completeness (h_valid : MValid phi) : Derivable MinPropAxiom phi` -- 17-line proof
- **Biconditional** (lines 221-224): `min_soundness_completeness`

## 3. Compactness Status

All three compactness corollaries ALREADY EXIST in the strong completeness files:
- `prop_compactness` in StrongCompleteness.lean (lines 220-226)
- `int_compactness` in IntStrongCompleteness.lean (lines 159-165)
- `min_compactness` in MinStrongCompleteness.lean (lines 136-146)

No new compactness proofs are needed.

## 4. Refactoring Design: Weak Completeness as Corollary of Strong

### The Mathematical Bridge

For each logic, weak completeness follows from strong completeness via:

1. **Validity implies empty-set entailment**: e.g., `Tautology phi -> SemanticEntails empty phi` (trivially: empty premise set means no premises to satisfy)
2. **Strong completeness**: `SemanticEntails empty phi -> SetDerivable Axioms empty phi`
3. **Empty-set bridge**: `SetDerivable Axioms empty phi <-> Derivable Axioms phi` (via `SetDerivable_empty_iff`)

The refactored `prop_completeness` would be approximately:
```lean
theorem prop_completeness (phi : PL.Proposition Atom)
    (h_taut : Tautology phi) : Derivable PropositionalAxiom phi :=
  SetDerivable_empty_iff.mp
    (prop_strong_completeness (fun v _ => h_taut v))
```

Similarly for intuitionistic (using `IValid -> ISemanticEntails empty -> SetDerivable empty -> Derivable`) and minimal.

### Import Constraint

CRITICAL: The strong completeness files IMPORT the weak completeness files:
- `StrongCompleteness.lean` imports `Completeness.lean`
- `IntStrongCompleteness.lean` imports `IntCompleteness.lean`
- `MinStrongCompleteness.lean` imports `MinCompleteness.lean`

This means we CANNOT have the weak completeness files import the strong completeness files (circular import). The refactored weak completeness theorems must live in the strong completeness files, not the weak ones.

### Bridging Lemmas Needed

No existing lemmas connect `Tautology`/`IValid`/`MValid` to `SemanticEntails empty`/`ISemanticEntails empty`/`MSemanticEntails empty`. However, the bridge is trivial (the empty-set premise condition is vacuously true) and can be done inline in the corollary proof. No separate bridging lemma is strictly necessary, but adding them improves clarity:

- `Tautology_iff_SemanticEntails_empty`: `Tautology phi <-> SemanticEntails empty phi`
- `IValid_iff_ISemanticEntails_empty`: `IValid phi <-> ISemanticEntails empty phi`
- `MValid_iff_MSemanticEntails_empty`: `MValid phi <-> MSemanticEntails empty phi`

These could go in `SemanticConsequence.lean` (which defines both sides) or directly in the strong completeness files.

## 5. Redundancy Analysis

### What Can Be Removed

From `Completeness.lean`:
- `prop_completeness` (lines 316-398): 82 lines of standalone proof -- REPLACEABLE as ~3-line corollary
- `completeness_iff_tautology` (lines 404-407): 4 lines -- REPLACEABLE as ~3-line corollary

From `IntCompleteness.lean`:
- `int_completeness` (lines 185-199): 15 lines -- REPLACEABLE as ~3-line corollary
- `int_soundness_completeness` (lines 205-208): 4 lines -- REPLACEABLE as ~3-line corollary

From `MinCompleteness.lean`:
- `min_completeness` (lines 199-215): 17 lines -- REPLACEABLE as ~3-line corollary
- `min_soundness_completeness` (lines 221-224): 4 lines -- REPLACEABLE as ~3-line corollary

**Total removable**: ~126 lines of standalone proofs
**Total replacement**: ~18 lines of corollaries

### What MUST Stay (Infrastructure)

- `Completeness.lean`: `canonicalValuation`, `prop_truth_lemma`, and all helper defs (~309 lines). These are used by `StrongCompleteness.lean`.
- `IntCompleteness.lean`: `IntCanonicalWorld`, `intCanonicalVal`, `intCanonicalVal_upward_closed`, `int_truth_lemma` (~178 lines). Used by `IntStrongCompleteness.lean`.
- `MinCompleteness.lean`: `MinCanonicalWorld`, `minCanonicalVal`, `minCanonicalVal_upward_closed`, `minBotForces`, `minBotForces_upward_closed`, `min_truth_lemma` (~191 lines). Used by `MinStrongCompleteness.lean`.

## 6. Downstream Dependencies

### `prop_completeness` is used in 3 downstream locations:

1. **`Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean`** (line 50):
   ```lean
   prop_completeness phi (toModal_valid_implies_tautology ...)
   ```
   Currently imports `Completeness.lean`. After refactoring, must import `StrongCompleteness.lean`.

2. **`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`** (line 118):
   ```lean
   apply prop_completeness
   ```
   Currently imports `Completeness.lean`. After refactoring, must import `StrongCompleteness.lean`.

3. **`Cslib/Logics/Temporal/ConservativeExtension.lean`** (line 89):
   ```lean
   apply prop_completeness
   ```
   Currently imports `Completeness.lean`. After refactoring, must import `StrongCompleteness.lean`.

All 3 downstream files use the theorem with the SAME signature (`(phi : PL.Proposition Atom) (h_taut : Tautology phi) : Derivable PropositionalAxiom phi`). The refactored corollary must preserve this signature exactly.

### `int_completeness` and `min_completeness` have NO downstream uses.

### `completeness_iff_tautology`, `int_soundness_completeness`, `min_soundness_completeness` have NO downstream uses.

## 7. Recommended Implementation Plan

### Phase 1: Add corollary theorems to strong completeness files

In each strong completeness file, add weak completeness and its biconditional as corollaries:

**StrongCompleteness.lean** -- add after `prop_compactness`:
```lean
/-- Weak completeness as corollary of strong completeness. -/
theorem prop_completeness (phi : PL.Proposition Atom)
    (h_taut : Tautology phi) : Derivable PropositionalAxiom phi :=
  SetDerivable_empty_iff.mp
    (prop_strong_completeness (fun v _ => h_taut v))

theorem completeness_iff_tautology {phi : PL.Proposition Atom} :
    Tautology phi <-> Derivable PropositionalAxiom phi :=
  Iff.intro (prop_completeness phi) soundness_tautology
```

**IntStrongCompleteness.lean** -- add after `int_compactness`:
```lean
theorem int_completeness {phi : PL.Proposition Atom}
    (h_valid : IValid.{u, u} phi) : Derivable IntPropAxiom phi :=
  SetDerivable_empty_iff.mp
    (int_strong_completeness (fun World _ val v_uc w _ => h_valid World val v_uc w))

theorem int_soundness_completeness {phi : PL.Proposition Atom} :
    IValid.{u, u} phi <-> Derivable IntPropAxiom phi :=
  Iff.intro int_completeness int_soundness_derivable
```

**MinStrongCompleteness.lean** -- add after `min_compactness`:
```lean
theorem min_completeness {phi : PL.Proposition Atom}
    (h_valid : MValid.{u, u} phi) : Derivable MinPropAxiom phi :=
  SetDerivable_empty_iff.mp
    (min_strong_completeness
      (fun World _ val bot_forces v_uc bf_uc w _ =>
        h_valid World val bot_forces v_uc bf_uc w))

theorem min_soundness_completeness {phi : PL.Proposition Atom} :
    MValid.{u, u} phi <-> Derivable MinPropAxiom phi :=
  Iff.intro min_completeness min_soundness_derivable
```

### Phase 2: Remove old proofs from weak completeness files

- Remove `prop_completeness` and `completeness_iff_tautology` from `Completeness.lean`
- Remove `int_completeness` and `int_soundness_completeness` from `IntCompleteness.lean`
- Remove `min_completeness` and `min_soundness_completeness` from `MinCompleteness.lean`

### Phase 3: Update downstream imports

Change 3 files from importing `Completeness` to `StrongCompleteness`:
1. `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean`
2. `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`
3. `Cslib/Logics/Temporal/ConservativeExtension.lean`

### Phase 4: Optional bridging lemmas

Add to `SemanticConsequence.lean` (optional, for documentation value):
```lean
theorem Tautology_iff_SemanticEntails_empty {phi : PL.Proposition Atom} :
    Tautology phi <-> SemanticEntails empty phi :=
  Iff.intro (fun h v _ => h v) (fun h v => h v (fun _ hx => absurd hx (Set.not_mem_empty _)))

theorem IValid_iff_ISemanticEntails_empty {phi : PL.Proposition Atom} :
    IValid.{u, u} phi <-> ISemanticEntails empty phi :=
  Iff.intro
    (fun h W _ val v_uc w _ => h W val v_uc w)
    (fun h W _ val v_uc w => h W val v_uc w (fun _ hx => absurd hx (Set.not_mem_empty _)))

theorem MValid_iff_MSemanticEntails_empty {phi : PL.Proposition Atom} :
    MValid.{u, u} phi <-> MSemanticEntails empty phi :=
  Iff.intro
    (fun h W _ val bf v_uc bf_uc w _ => h W val bf v_uc bf_uc w)
    (fun h W _ val bf v_uc bf_uc w =>
      h W val bf v_uc bf_uc w (fun _ hx => absurd hx (Set.not_mem_empty _)))
```

### Phase 5: Verification

Run the CI pipeline:
1. `lake build`
2. `lake exe checkInitImports`
3. `lake test`
4. `lake exe lint-style`
5. `lake shake --add-public --keep-implied --keep-prefix`

## 8. Risk Assessment

- **Low risk**: All compactness corollaries already exist; no new proofs needed for those.
- **Low risk**: Downstream API is preserved (same theorem names and signatures).
- **Low risk**: The import changes are mechanical (3 files, 1 line each).
- **Medium risk**: The corollary proof for `int_completeness` involves matching the universe-polymorphic `IValid.{u,u}` signature; care needed with universe parameters.
- **No blockers identified**.

## 9. Summary of Findings

1. All three compactness corollaries (prop, int, min) ALREADY EXIST in the strong completeness files. No new compactness work needed.
2. Weak completeness can be derived as 3-line corollaries of strong completeness via `SetDerivable_empty_iff`.
3. The refactored theorems must live in the strong completeness files (not the weak ones) due to the import direction.
4. Three downstream files need import updates to resolve `prop_completeness` from the new location.
5. `int_completeness` and `min_completeness` have no downstream uses, making their refactoring risk-free.
6. Optional bridging lemmas (`Tautology_iff_SemanticEntails_empty`, etc.) provide cleaner documentation but are not strictly needed.
7. Total net reduction: ~126 lines of standalone proofs replaced by ~18 lines of corollaries.
