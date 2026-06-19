# Research Report: Weak Completeness as Corollaries of Strong Completeness

## Task Summary

Derive weak completeness as corollaries of strong completeness for all 15 modal cube systems.
Move each `{sys}_completeness` theorem from `Completeness.lean` into `StrongCompleteness.lean`,
replacing the direct proof with a short corollary via `ModalSetDerivable_empty_iff` and
`{sys}_strong_completeness`. Remove the original theorem from each `Completeness.lean` (keeping
all supporting infrastructure). Update docstrings in both files.

## Key Infrastructure

### Bridge Lemma

`ModalSetDerivable_empty_iff` at line 94 of
`Cslib/Logics/Modal/Metalogic/StrongCompleteness.lean`:

```lean
theorem ModalSetDerivable_empty_iff {Axioms : Proposition Atom → Prop}
    {phi : Proposition Atom} :
    ModalSetDerivable Axioms ∅ phi ↔ Derivable Axioms phi
```

This converts between set-derivability from the empty set and ordinary derivability.

### Corollary Strategy

For each system: instantiate strong completeness at `Gamma = ∅`, discard the vacuous
`∀ γ ∈ ∅, Satisfies m w γ` hypothesis, and apply `ModalSetDerivable_empty_iff.mp`.

## Two Proof Patterns

### Pattern 1: K (uses `ModalSemanticEntails`)

K's strong completeness uses `ModalSemanticEntails (fun _ => True)` while the weak
completeness takes a plain validity hypothesis. The bridge uses
`ModalSemanticEntails_of_Valid`:

```lean
/-- **Completeness Theorem for Modal Logic K** (corollary of strong completeness):
If `phi` is valid over all frames, then `phi` is K-derivable. -/
theorem k_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      ∀ w, Satisfies m w φ) :
    Derivable (@KAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k_strong_completeness (ModalSemanticEntails_of_Valid (fun W m _ => h_valid W m) ∅))
```

### Pattern 2: All Other Systems (direct quantification)

For the 14 systems that use direct quantification in strong completeness, the corollary
sets `Gamma = ∅` and discards the vacuous premise-satisfaction hypothesis. The frame
condition arguments are threaded through directly.

General template (N frame conditions):
```lean
theorem {sys}_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      <frame_cond_1> → ... → <frame_cond_N> →
      ∀ w, Satisfies m w φ) :
    Derivable (@{Sys}Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    ({sys}_strong_completeness (fun W m w fc₁ ... fcN _ => h_valid W m fc₁ ... fcN w))
```

The `_` discards the `∀ γ ∈ ∅, Satisfies m w γ` hypothesis (vacuously true).

## Per-System Catalog

### Frame Conditions and Axiom Names

| System | Axiom Type | Frame Conditions | # FC args |
|--------|-----------|------------------|-----------|
| K | `KAxiom` | none | 0 |
| T | `TAxiom` | refl | 1 |
| B | `BAxiom` | symm | 1 |
| D | `DAxiom` | serial | 1 |
| S4 | `S4Axiom` | refl, trans | 2 |
| S5 | `ModalAxiom` | refl, trans, eucl | 3 |
| K4 | `K4Axiom` | trans | 1 |
| K5 | `K5Axiom` | eucl | 1 |
| K45 | `K45Axiom` | trans, eucl | 2 |
| KB5 | `KB5Axiom` | symm, eucl | 2 |
| D4 | `D4Axiom` | serial, trans | 2 |
| D5 | `D5Axiom` | serial, eucl | 2 |
| D45 | `D45Axiom` | serial, trans, eucl | 3 |
| DB | `DBAxiom` | serial, symm | 2 |
| TB | `TBAxiom` | refl, symm | 2 |

### Infrastructure Remaining in Completeness.lean After Move

| System | Declarations Staying | File Status After Move |
|--------|---------------------|----------------------|
| K | k_derive_box_from_inconsistency, k_mcs_box_witness, k_truth_lemma | 3 declarations remain |
| T | t_canonical_refl, t_truth_lemma | 2 declarations remain |
| B | (none) | Empty module body (imports only) |
| D | derive_box_from_inconsistency_d, mcs_box_witness_d, canonical_serial, truth_lemma_d | 4 declarations remain |
| S4 | (none) | Empty module body (imports only) |
| S5 | (none) | Empty module body (imports only) |
| K4 | (none) | Empty module body (imports only) |
| K5 | (none) | Empty module body (imports only) |
| K45 | (none) | Empty module body (imports only) |
| KB5 | (none) | Empty module body (imports only) |
| D4 | (none) | Empty module body (imports only) |
| D5 | (none) | Empty module body (imports only) |
| D45 | (none) | Empty module body (imports only) |
| DB | (none) | Empty module body (imports only) |
| TB | tb_canonical_refl, tb_canonical_symm, tb_truth_lemma | 3 declarations remain |

### Special Cases

- **S5**: Has `alias completeness := s5_completeness` that must move with the theorem.
- **10 systems with empty bodies**: B, S4, K4, K5, K45, KB5, D4, D5, D45, DB will have
  empty module bodies after the move. These files must be retained because:
  1. They are in the barrel import (`Cslib.lean`).
  2. StrongCompleteness.lean imports them for transitive access to infrastructure.
  3. They serve as stable import targets for external consumers.
  Their module docstrings should be updated to say "supporting infrastructure for {Sys}
  completeness" and note the infrastructure is imported transitively.

## Corollary Proof Terms (All 15 Systems)

### K (Pattern 1 -- uses ModalSemanticEntails)

```lean
theorem k_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      ∀ w, Satisfies m w φ) :
    Derivable (@KAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k_strong_completeness (ModalSemanticEntails_of_Valid (fun W m _ => h_valid W m) ∅))
```

### T

```lean
theorem t_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) → ∀ w, Satisfies m w φ) :
    Derivable (@TAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (t_strong_completeness (fun W m w hRefl _ => h_valid W m hRefl w))
```

### B

```lean
theorem b_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) → ∀ w, Satisfies m w φ) :
    Derivable (@BAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (b_strong_completeness (fun W m w hSymm _ => h_valid W m hSymm w))
```

### D

```lean
theorem d_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r → ∀ w, Satisfies m w φ) :
    Derivable (@DAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d_strong_completeness (fun W m w hSer _ => h_valid W m hSer w))
```

### S4

```lean
theorem s4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@S4Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (s4_strong_completeness (fun W m w hRefl hTrans _ => h_valid W m hRefl hTrans w))
```

### S5

```lean
theorem s5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@ModalAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (s5_strong_completeness (fun W m w hRefl hTrans hEucl _ =>
      h_valid W m hRefl hTrans hEucl w))

alias completeness := s5_completeness
```

### K4

```lean
theorem k4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K4Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k4_strong_completeness (fun W m w hTrans _ => h_valid W m hTrans w))
```

### K5

```lean
theorem k5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K5Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k5_strong_completeness (fun W m w hEucl _ => h_valid W m hEucl w))
```

### K45

```lean
theorem k45_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K45Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k45_strong_completeness (fun W m w hTrans hEucl _ => h_valid W m hTrans hEucl w))
```

### KB5

```lean
theorem kb5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@KB5Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (kb5_strong_completeness (fun W m w hSymm hEucl _ => h_valid W m hSymm hEucl w))
```

### D4

```lean
theorem d4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@D4Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d4_strong_completeness (fun W m w hSer hTrans _ => h_valid W m hSer hTrans w))
```

### D5

```lean
theorem d5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@D5Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d5_strong_completeness (fun W m w hSer hEucl _ => h_valid W m hSer hEucl w))
```

### D45

```lean
theorem d45_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@D45Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d45_strong_completeness (fun W m w hSer hTrans hEucl _ =>
      h_valid W m hSer hTrans hEucl w))
```

### DB

```lean
theorem db_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      ∀ w, Satisfies m w φ) :
    Derivable (@DBAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (db_strong_completeness (fun W m w hSer hSymm _ => h_valid W m hSer hSymm w))
```

### TB

```lean
theorem tb_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      ∀ w, Satisfies m w φ) :
    Derivable (@TBAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (tb_strong_completeness (fun W m w hRefl hSymm _ => h_valid W m hRefl hSymm w))
```

## Implementation Approach

### Phase 1: Systems with substantial infrastructure (K, T, D, TB)

These systems have multiple declarations in Completeness.lean that STAY. The edit is
targeted: remove the completeness theorem (and its section header/docstring), add it to
StrongCompleteness.lean with the corollary proof, and update both module docstrings.

Files to edit:
- `K/Completeness.lean`: Remove lines 267-300 (k_completeness + section header)
- `K/StrongCompleteness.lean`: Add k_completeness corollary after compactness
- `T/Completeness.lean`: Remove lines 75-105 (t_completeness + section header)
- `T/StrongCompleteness.lean`: Add t_completeness corollary after compactness
- `D/Completeness.lean`: Remove lines 371-428 (d_completeness + section header)
- `D/StrongCompleteness.lean`: Add d_completeness corollary after compactness
- `TB/Completeness.lean`: Remove lines ~95-129 (tb_completeness + section header)
- `TB/StrongCompleteness.lean`: Add tb_completeness corollary after compactness

### Phase 2: Systems with single-declaration Completeness (10 systems)

These systems (B, S4, S5, K4, K5, K45, KB5, D4, D5, D45, DB) have only the completeness
theorem in Completeness.lean. After removal, the file has an empty module body with just
imports and docstrings.

For each:
1. Remove the theorem (and alias for S5) from Completeness.lean
2. Update Completeness.lean docstring to note it provides import infrastructure
3. Add the corollary to StrongCompleteness.lean with updated docstring

### Phase 3: Verification

Run `lake build` to verify all 30 files (15 Completeness + 15 StrongCompleteness) compile.

## Docstring Updates

### Completeness.lean (files with remaining infrastructure)

Update the module docstring `## Main Results` section to remove the completeness theorem
entry. Add a note that weak completeness is now in StrongCompleteness.lean.

### Completeness.lean (files becoming empty)

Replace the module docstring with a brief note:
```
/-! # {Sys} Completeness Infrastructure

This module provides import infrastructure for modal logic {Sys}.
The canonical model construction, truth lemma, and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `{sys}_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.{Sys}.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

### StrongCompleteness.lean

Add a new section before `end Cslib.Logic.Modal`:
```
/-! ## {Sys} Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic {Sys}** (corollary of strong completeness):
If `phi` is valid over all {frame_class} frames, then `phi` is {Sys}-derivable.

This is a corollary of `{sys}_strong_completeness` instantiated at `Gamma = ∅`. -/
```

Update the module docstring `## Main Results` section to add the weak completeness entry.

## Import Dependency Analysis

No import changes are needed. Each StrongCompleteness.lean already imports its
Completeness.lean (or the parent system's Completeness.lean for D-family). The corollary
only uses `{sys}_strong_completeness` (defined in the same file) and
`ModalSetDerivable_empty_iff` (from `Cslib.Logics.Modal.Metalogic.StrongCompleteness`,
already imported). For K, `ModalSemanticEntails_of_Valid` is also already available
through the same import.

## Risk Assessment

- **Low risk**: This is a pure refactoring -- the theorem statements do not change, only
  the proof terms. The theorem names and types are preserved exactly.
- **No behavioral change**: External consumers importing these modules get the same API.
- **Build verification**: Running `lake build` after the refactoring will confirm
  correctness. Each corollary proof is a single term-mode expression, so type errors
  will surface immediately.
- **Potential subtlety**: The corollary proof must match universe levels correctly. All
  systems use `universe u` with `{Atom : Type u}`, and `ModalSetDerivable_empty_iff`
  is universe-polymorphic, so this should be straightforward.
