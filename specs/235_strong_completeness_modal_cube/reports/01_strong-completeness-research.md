# Research Report: Strong Completeness for the Modal Cube

## Task 235 -- Upgrade Weak Completeness to Strong Completeness

**Session**: sess_1781834791_c4c530
**Date**: 2026-06-18

---

## 1. Executive Summary

The existing modal cube infrastructure proves **weak completeness** for all 15 systems: if a formula is valid over the appropriate frame class, then it is derivable from the empty context (`Derivable Axioms phi`). The task is to upgrade this to **strong completeness**: if `phi` is a semantic consequence of a set of premises `Gamma` (over the appropriate frame class), then `phi` is set-derivable from `Gamma`.

The propositional logic already has strong completeness (`prop_strong_completeness` in `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean`), and the modal infrastructure has all the building blocks needed. The upgrade requires:

1. Defining modal `ModalSetDerivable` and `ModalSemanticEntails` (analogues of the propositional `SetDerivable` and `SemanticEntails`).
2. Proving a key lemma: if `phi` is not set-derivable from `Gamma`, then `Gamma ∪ {neg phi}` is consistent.
3. Proving strong soundness and strong completeness for all 15 systems.

All the required proof infrastructure (Lindenbaum's lemma, deduction theorem with member removal, truth lemmas, canonical model construction) already exists.

---

## 2. Existing Architecture

### 2.1 Weak Completeness Structure

Each of the 15 systems has:
- **Axiom predicate**: An inductive type (e.g., `KAxiom`, `TAxiom`, `S4Axiom`, `ModalAxiom` for S5) in `Cslib/Logics/Modal/ProofSystem/Instances/{System}.lean`
- **Soundness file**: `Cslib/Logics/Modal/Metalogic/Systems/{System}/Soundness.lean` with:
  - `{sys}_axiom_sound`: Each axiom is valid over the appropriate frame class
  - `{sys}_soundness`: If `Gamma |- phi`, then `phi` is satisfied where `Gamma` is (contextual/strong soundness with `List` context)
  - `{sys}_soundness_derivable`: If `phi` is derivable, then `phi` is valid
- **Completeness file**: `Cslib/Logics/Modal/Metalogic/Systems/{System}/Completeness.lean` with:
  - `{sys}_completeness`: If `phi` is valid over the frame class, then `Derivable Axioms phi`

### 2.2 Truth Lemma Families

There are three truth lemma families, each parameterized over axioms:

| Family | Location | Uses | Used By |
|--------|----------|------|---------|
| `truth_lemma` | Completeness.lean | axiom T via `mcs_box_witness` | S5, T, S4, TB |
| `k_truth_lemma` | Systems/K/Completeness.lean | K-specific box witness (no axiom T) | K, B, K4, K5, K45, KB5 |
| `truth_lemma_d` | Systems/D/Completeness.lean | D-specific box witness (axiom D, no T) | D, D4, D5, D45, DB |

### 2.3 Frame Conditions per System

| System | Frame Conditions | Axioms Beyond K |
|--------|-----------------|-----------------|
| K | none | -- |
| T | reflexive | T |
| B (KB) | symmetric | B |
| D | serial | D |
| K4 | transitive | 4 |
| K5 | Euclidean | 5 |
| S4 (KT4) | reflexive, transitive | T, 4 |
| S5 (KT4B) | reflexive, transitive, Euclidean | T, 4, B |
| TB | reflexive, symmetric | T, B |
| K45 | transitive, Euclidean | 4, 5 |
| KB5 | symmetric, Euclidean | B, 5 |
| D4 | serial, transitive | D, 4 |
| D5 | serial, Euclidean | D, 5 |
| D45 | serial, transitive, Euclidean | D, 4, 5 |
| DB | serial, symmetric | D, B |

### 2.4 Propositional Strong Completeness Pattern

The propositional strong completeness in `StrongCompleteness.lean` follows this structure:

1. **`SetDerivable Axioms Gamma phi`**: Exists finite `L ⊆ Gamma` such that `Deriv Axioms L phi`
2. **`SemanticEntails Gamma phi`**: For all valuations satisfying `Gamma`, `phi` holds
3. **`prop_strong_soundness`**: `SetDerivable -> SemanticEntails` (unfold, apply list soundness)
4. **`prop_not_SetDerivable_union_neg_consistent`**: If `phi` not set-derivable from `Gamma`, then `Gamma ∪ {neg phi}` is consistent (uses `deductionWithMem` + DNE)
5. **`prop_strong_completeness`**: `SemanticEntails -> SetDerivable` (contrapositive: extend `Gamma ∪ {neg phi}` to MCS via Lindenbaum, truth lemma gives countermodel)

### 2.5 Existing Soundness Structure

The parameterized `soundness` theorem (in `Metalogic/Soundness.lean`) already handles contexts:

```lean
theorem soundness {Axioms} {World} {Gamma : List (Proposition Atom)} {phi}
    (d : DerivationTree Axioms Gamma phi)
    (m : Model World Atom)
    (h_ax_sound : ∀ psi, Axioms psi → ∀ w, Satisfies m w psi)
    (w : World)
    (h_ctx : ∀ psi ∈ Gamma, Satisfies m w psi) : Satisfies m w phi
```

This is already "strong soundness" in the sense that it handles arbitrary contexts. The per-system wrappers like `t_soundness` similarly take a list context `Gamma` with `h_ctx`. The `_derivable` variants just specialize to the empty context.

### 2.6 Key Building Blocks Already Present

- `modal_lindenbaum`: Lindenbaum's lemma for any consistent set
- `neg_consistent_of_not_derivable`: If `phi` is not derivable, then `{neg phi}` is consistent
- `deductionWithMem`: From `Gamma' |- phi` with `A ∈ Gamma'`, get `removeAll Gamma' A |- A -> phi`
- `deductionTheorem`: From `A :: Gamma |- B`, get `Gamma |- A -> B`
- All three truth lemma families
- All canonical frame property proofs

---

## 3. What Needs to Be Built

### 3.1 New Definitions (Parameterized, in a shared file)

**Modal `SetDerivable`**: Analogous to the propositional version but using `modalDerivationSystem`:

```lean
def ModalSetDerivable (Axioms : Proposition Atom → Prop)
    (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) : Prop :=
  ∃ L : List (Proposition Atom),
    (∀ x ∈ L, x ∈ Gamma) ∧ (modalDerivationSystem Axioms).Deriv L phi
```

**Modal `ModalSemanticEntails`**: Must quantify over models with frame conditions. There are two design options:

**Option A -- Per-system semantic entailment with frame conditions baked in**: Each system gets its own `ModalSemanticEntails` with the appropriate frame condition. This matches the per-system `{sys}_completeness` signature.

**Option B -- Parameterized semantic entailment with frame class parameter**: A single definition parameterized by a predicate on models:

```lean
def ModalSemanticEntails
    (FrameClass : ∀ {World : Type u}, Model World Atom → Prop)
    (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) : Prop :=
  ∀ (World : Type u) (m : Model World Atom), FrameClass m →
    ∀ w, (∀ psi ∈ Gamma, Satisfies m w psi) → Satisfies m w phi
```

**Recommendation**: Option B is cleaner and avoids duplicating 15 definitions. The frame class parameter matches the structure already used in `Cube.lean` (e.g., `{m | Std.Refl m.r}`). However, for K (no frame condition), the predicate is `fun _ => True`.

For K specifically, the existing weak completeness has:
```lean
h_valid : ∀ (World : Type u) (m : Model World Atom), ∀ w, Satisfies m w phi
```
which is `ModalSemanticEntails (fun _ => True) ∅ phi`.

### 3.2 Key Lemma: Consistency of `Gamma ∪ {neg phi}`

The critical new proof is the modal analogue of `prop_not_SetDerivable_union_neg_consistent`:

```lean
theorem modal_not_SetDerivable_union_neg_consistent
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ...) (h_implyS : ...) (h_efq : ...) (h_peirce : ...)
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h_not : ¬ ModalSetDerivable Axioms Gamma phi) :
    SetConsistent Axioms (Gamma ∪ {neg phi})
```

This proof follows the same pattern as the propositional version:
1. If some finite `L ⊆ Gamma ∪ {neg phi}` derives `bot`:
   - Case `neg phi ∈ L`: Use `deductionWithMem` to get `removeAll L (neg phi) |- neg phi -> bot`, then DNE gives `removeAll L (neg phi) |- phi`, contradicting non-set-derivability.
   - Case `neg phi ∉ L`: All of L is in Gamma; weaken to get `(neg phi) :: L |- bot`, deduction theorem gives `L |- neg phi -> bot`, DNE gives `L |- phi`, contradiction.

The `dne_from_neg_neg` helper (EFQ + implyS + Peirce -> DNE) already exists in the propositional version and can be replicated for modal derivation trees. Actually, examining the code more carefully, the same construction works because modal `DerivationTree` has the same constructors.

### 3.3 Strong Soundness (Per System)

For each system, strong soundness is:
```lean
theorem {sys}_strong_soundness
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable {SysAxiom} Gamma phi) :
    ModalSemanticEntails {frame_class} Gamma phi
```

Proof: Unfold `ModalSetDerivable` to get `L ⊆ Gamma` and `Deriv L phi`. Apply existing `{sys}_soundness` which handles list contexts. This is very short (2-5 lines).

### 3.4 Strong Completeness (Per System)

For each system, strong completeness is:
```lean
theorem {sys}_strong_completeness
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSemanticEntails {frame_class} Gamma phi) :
    ModalSetDerivable {SysAxiom} Gamma phi
```

Proof by contrapositive:
1. Assume `phi` is not set-derivable from `Gamma`.
2. By `modal_not_SetDerivable_union_neg_consistent`, `Gamma ∪ {neg phi}` is consistent.
3. By `modal_lindenbaum`, extend to MCS `M ⊇ Gamma ∪ {neg phi}`.
4. `neg phi ∈ M` and `Gamma ⊆ M`.
5. Construct canonical model. Show frame properties (reuse existing canonical_refl, canonical_trans, etc.).
6. By truth lemma, all of `Gamma` is satisfied at `M` (since `Gamma ⊆ M`).
7. By `ModalSemanticEntails` hypothesis, `phi` is satisfied at `M`.
8. By truth lemma, `phi ∈ M`.
9. But `neg phi ∈ M` -- contradiction via `mcs_bot_not_mem`.

### 3.5 Weak Completeness as Corollary

After strong completeness, weak completeness becomes a corollary:
```lean
theorem {sys}_completeness' : ... :=
  ModalSetDerivable_empty_iff.mp
    ({sys}_strong_completeness (ModalSemanticEntails_of_Valid h_valid ∅))
```

### 3.6 Compactness Corollary

Like propositional logic, compactness follows from strong soundness + strong completeness.

---

## 4. File Organization

### 4.1 New Shared Infrastructure File

**`Cslib/Logics/Modal/Metalogic/StrongCompleteness.lean`** (new):
- `ModalSetDerivable` definition
- `ModalSemanticEntails` definition (parameterized over frame class)
- `ModalSetDerivable_of_mem`, `ModalSetDerivable_weakening`, `ModalSetDerivable_of_Derivable`, `ModalSetDerivable_empty_iff` (basic lemmas mirroring propositional)
- `ModalSemanticEntails_of_Valid` (validity implies semantic entailment from any set)
- `modal_dne_from_neg_neg` (DNE helper for modal derivation trees)
- `modal_not_SetDerivable_union_neg_consistent` (key consistency lemma)

### 4.2 Per-System Strong Completeness Files

Two options for organization:

**Option A -- Extend existing Completeness.lean files**: Add `{sys}_strong_soundness`, `{sys}_strong_completeness`, `{sys}_strong_completeness_iff`, and `{sys}_compactness` to each system's existing `Completeness.lean` file.

**Option B -- New StrongCompleteness.lean files per system**: Create `Cslib/Logics/Modal/Metalogic/Systems/{Sys}/StrongCompleteness.lean` for each system.

**Recommendation**: Option B (separate files) is cleaner because:
- Each existing `Completeness.lean` is already a cohesive unit proving weak completeness
- Adding ~50 lines of strong completeness would double each file
- The new files import the existing completeness files and `StrongCompleteness.lean`
- Module structure stays clean

### 4.3 Naming Convention

Following the existing pattern where:
- Weak: `{sys}_completeness`
- Strong: `{sys}_strong_completeness`
- Strong soundness: `{sys}_strong_soundness`
- Biconditional: `{sys}_strong_completeness_iff`
- Compactness: `{sys}_compactness`

### 4.4 Import Structure

```
StrongCompleteness.lean (shared definitions + key lemma)
  ├── Systems/K/StrongCompleteness.lean (imports K/Completeness + K/Soundness + StrongCompleteness)
  ├── Systems/T/StrongCompleteness.lean (imports T/Completeness + T/Soundness + StrongCompleteness)
  ├── ... (13 more per-system files)
  └── (Metalogic.lean updated with new imports)
```

---

## 5. Proof Complexity Assessment

### 5.1 Shared Infrastructure (~150 lines)

The `StrongCompleteness.lean` shared file contains:
- Definitions: ~30 lines (ModalSetDerivable, ModalSemanticEntails, basic lemmas)
- `modal_dne_from_neg_neg`: ~30 lines (adapting propositional DNE to modal)
- `modal_not_SetDerivable_union_neg_consistent`: ~50 lines (adapting propositional consistency lemma)
- Module docstring + imports: ~40 lines

### 5.2 Per-System Files (~50-70 lines each)

Each per-system `StrongCompleteness.lean` contains:
- `{sys}_strong_soundness`: ~10 lines (unfold + apply existing soundness)
- `{sys}_strong_completeness`: ~30 lines (contrapositive + existing infrastructure)
- `{sys}_strong_completeness_iff`: ~3 lines (biconditional wrapper)
- `{sys}_compactness`: ~8 lines (corollary)
- Module docstring + imports: ~15 lines

Total per system: ~60-70 lines

### 5.3 Total New Code

- 1 shared file: ~150 lines
- 15 per-system files: ~60-70 lines each = ~900-1050 lines
- Module file updates: ~30 lines
- **Total: ~1100-1230 lines**

### 5.4 Risk Assessment

**Low risk**. The proof pattern is well-established (already done for propositional logic), all building blocks exist, and the per-system files are highly repetitive. The main challenge is correctly adapting the consistency lemma and DNE helper from propositional to modal derivation trees.

Key considerations:
- The modal `DerivationTree` has a `necessitation` constructor that the propositional version lacks, but this doesn't affect the `deductionWithMem` or DNE arguments since they only involve propositional reasoning.
- Universe polymorphism: Modal `ModalSemanticEntails` must use `universe u` consistently with the existing completeness theorems which use `∀ (World : Type u)`.
- The `deductionWithMem` for modal trees already exists and works identically to the propositional version.

---

## 6. Reuse Check

### 6.1 CSLib Foundations Check

- `Metalogic.SetConsistent`, `Metalogic.SetMaximalConsistent`: Already used via abbreviations in `MCS.lean`
- `modal_lindenbaum`: Already exists
- `deductionWithMem` (modal): Already exists in `DeductionTheorem.lean`
- No existing `ModalSetDerivable` or `ModalSemanticEntails` -- these need to be created

### 6.2 Mathlib Check

No direct Mathlib infrastructure for modal logic strong completeness exists. The proof is self-contained within CSLib.

### 6.3 Propositional Logic as Template

The propositional `StrongCompleteness.lean` (562 lines) serves as the complete template. The modal version will be simpler in some ways (no `and`/`or` connective cases in truth lemma -- those are already handled) and identical in others (the consistency lemma and DNE).

---

## 7. Design Decisions

### 7.1 Frame Class Parameterization

The `ModalSemanticEntails` definition should use a frame class predicate:

```lean
def ModalSemanticEntails.{u}
    (FC : ∀ {World : Type u}, Model World Atom → Prop)
    (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) : Prop :=
  ∀ (World : Type u) (m : Model World Atom), @FC World m →
    ∀ w, (∀ psi ∈ Gamma, Satisfies m w psi) → Satisfies m w phi
```

For K (no frame condition), use `FC := fun _ => True`.

### 7.2 Per-System Frame Class Abbreviations

For readability, define per-system abbreviations:

```lean
abbrev KFrameClass : ∀ {World : Type u}, Model World Atom → Prop := fun _ => True
abbrev TFrameClass : ∀ {World : Type u}, Model World Atom → Prop := fun m => ∀ w, m.r w w
-- etc.
```

Or inline them (matching the existing completeness theorem signatures).

### 7.3 Docstring Standards

Every new definition and theorem must have a docstring (docBlame linter). The pattern from the existing codebase should be followed: reference BRV Chapter 4, note the relationship between strong and weak versions.

---

## 8. Implementation Plan Sketch

### Phase 1: Shared Infrastructure
Create `Cslib/Logics/Modal/Metalogic/StrongCompleteness.lean` with:
- `ModalSetDerivable` + basic lemmas
- `ModalSemanticEntails` (parameterized)
- `modal_dne_from_neg_neg`
- `modal_not_SetDerivable_union_neg_consistent`

### Phase 2: Per-System Strong Completeness (K-group)
Create files for K, B, K4, K5, K45, KB5 (all use `k_truth_lemma`).

### Phase 3: Per-System Strong Completeness (T-group)
Create files for T, S4, S5, TB (all use `truth_lemma`).

### Phase 4: Per-System Strong Completeness (D-group)
Create files for D, D4, D5, D45, DB (all use `truth_lemma_d`).

### Phase 5: Module Updates + Verification
Update `Metalogic.lean` with new imports. Run `lake build`, `lake exe checkInitImports`, `lake exe mk_all --module`.

---

## 9. Key Files Reference

| File | Role |
|------|------|
| `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` | Template for the entire effort |
| `Cslib/Logics/Modal/Metalogic/Completeness.lean` | Canonical model + truth_lemma + neg_consistent |
| `Cslib/Logics/Modal/Metalogic/Soundness.lean` | Parameterized soundness (already handles contexts) |
| `Cslib/Logics/Modal/Metalogic/MCS.lean` | SetConsistent, SetMaximalConsistent, modal_lindenbaum |
| `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` | deductionWithMem, deductionTheorem |
| `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` | k_truth_lemma + k_completeness |
| `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` | truth_lemma_d + d_completeness |
| `Cslib/Logics/Modal/Metalogic/Systems/{Sys}/Soundness.lean` | {sys}_soundness (list context) |
| `Cslib/Logics/Modal/Metalogic/Systems/{Sys}/Completeness.lean` | {sys}_completeness (weak) |
| `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` | SetDerivable, SemanticEntails definitions |

---

## 10. Lint Compliance Checklist

- [ ] All new declarations have docstrings (docBlame)
- [ ] Prop-valued declarations use `theorem`/`lemma` not `def` (defLemma)
- [ ] Names use lowerCamelCase (defsWithUnderscore) -- note: existing convention uses snake_case for theorems (e.g., `k_completeness`), so follow the existing pattern
- [ ] All files import `Cslib.Init`
- [ ] Section variables are minimal
- [ ] Instance declarations wrapped in namespaces
