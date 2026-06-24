# Research Report: Task 335 — Parametric Modal Soundness Refactor

## Problem Statement

All 15 system-specific `Soundness.lean` files under `Cslib/Logics/Modal/Metalogic/Systems/*/` contain identical 5-case proof blocks for propositional + K axiom soundness (implyK, implyS, efq, peirce, modalK). The shared `Cslib/Logics/Modal/Metalogic/Soundness.lean` currently has only the parameterized `soundness` and `soundness_derivable` theorems — no shared axiom-level lemmas.

## Codebase Analysis

### Current Structure

**16 files, 1,375 total lines:**

| File | Lines | Base Cases | System-Specific Cases |
|------|-------|------------|----------------------|
| `Soundness.lean` (shared) | 84 | — | — |
| `Systems/K/Soundness.lean` | 82 | 5 (all) | none |
| `Systems/T/Soundness.lean` | 77 | 5 | modalT |
| `Systems/B/Soundness.lean` | 75 | 5 | modalB |
| `Systems/D/Soundness.lean` | 76 | 5 | modalD |
| `Systems/S4/Soundness.lean` | 92 | 5 | modalT, modalFour |
| `Systems/S5/Soundness.lean` | 87 | 5 | modalT, modalFour, modalB |
| `Systems/K4/Soundness.lean` | 84 | 5 | modalFour |
| `Systems/K5/Soundness.lean` | 77 | 5 | modalFive |
| `Systems/K45/Soundness.lean` | 95 | 5 | modalFour, modalFive |
| `Systems/KB5/Soundness.lean` | 95 | 5 | modalB, modalFive |
| `Systems/D4/Soundness.lean` | 87 | 5 | modalD, modalFour |
| `Systems/D5/Soundness.lean` | 88 | 5 | modalD, modalFive |
| `Systems/D45/Soundness.lean` | 96 | 5 | modalD, modalFour, modalFive |
| `Systems/DB/Soundness.lean` | 87 | 5 | modalD, modalB |
| `Systems/TB/Soundness.lean` | 93 | 5 | modalT, modalB |

### Duplicated Block (identical in all 15 system files)

Each `_axiom_sound` theorem contains this identical block inside `cases h_ax with`:

```lean
  | implyK φ ψ =>
    intro hφ _
    exact hφ
  | implyS φ ψ χ =>
    intro h₁ h₂ h₃
    exact h₁ h₃ (h₂ h₃)
  | efq φ =>
    intro h
    exact absurd h id
  | peirce φ ψ =>
    intro h
    by_contra h_not
    exact h_not (h (fun hφ => absurd hφ h_not))
  | modalK φ ψ =>
    intro h_box_imp h_box_phi w' hr
    exact h_box_imp w' hr (h_box_phi w' hr)
```

This is 16 lines per file (5 case labels + 11 proof body lines), totaling 240 duplicated lines across 15 files.

### Axiom Type Architecture

Each system defines its own independent inductive axiom type (e.g., `KAxiom`, `TAxiom`, `S4Axiom`, `D45Axiom`). There is no shared base type or inheritance relationship. All 15 types repeat the same 5 propositional+K constructors with identical formula types, adding system-specific constructors (modalT, modalB, modalD, modalFour, modalFive) as needed.

The `ModalAxiom` type (defined in `DerivationTree.lean`) is the S5 axiom with all 8 constructors. `KAxiom` is defined in `ProofSystem/Instances/K.lean`.

### Import Chain

```
Soundness.lean → DerivationTree.lean → Basic.lean (Satisfies, Model, Proposition)
Systems/*/Soundness.lean → Soundness.lean, ProofSystem/Instances
```

The shared `Soundness.lean` has access to `Satisfies`, `Model`, `Proposition` — everything needed for standalone formula-level soundness lemmas. It does NOT import any system-specific axiom type.

### Existing Semantic Lemmas (in Basic.lean)

The following already exist as `Satisfies.*` theorems in `Basic.lean`:
- `Satisfies.t` — T axiom valid for reflexive models
- `Satisfies.b` — B axiom valid for symmetric models
- `Satisfies.four` — 4 axiom valid for transitive models
- `Satisfies.five` — 5 axiom valid for Euclidean models
- `Satisfies.d` — D axiom valid for serial models

**No equivalent lemmas exist for the 5 propositional+K cases.** These are the gap this task fills.

## Recommended Approach

### Design: 5 Standalone `Satisfies` Lemmas

Add 5 individual soundness lemmas to `Cslib/Logics/Modal/Metalogic/Soundness.lean`. Each proves that a specific axiom formula is satisfied at any world of any model (no frame conditions needed):

```lean
/-- Propositional axiom K (weakening) is valid on all frames. -/
lemma Satisfies.implyK_axiom (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp φ (Proposition.imp ψ φ)) := by
  intro hφ _; exact hφ

/-- Propositional axiom S (distribution) is valid on all frames. -/
lemma Satisfies.implyS_axiom (m : Model World Atom) (w : World)
    (φ ψ χ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
      (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ))) := by
  intro h₁ h₂ h₃; exact h₁ h₃ (h₂ h₃)

/-- Ex falso quodlibet is valid on all frames. -/
lemma Satisfies.efq_axiom (m : Model World Atom) (w : World)
    (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp Proposition.bot φ) := by
  intro h; exact absurd h id

/-- Peirce's law / double negation elimination is valid on all frames. -/
lemma Satisfies.peirce_axiom (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ) := by
  intro h; by_contra h_not; exact h_not (h (fun hφ => absurd hφ h_not))

/-- Modal axiom K (distribution) is valid on all frames. -/
lemma Satisfies.modalK_axiom (m : Model World Atom) (w : World)
    (φ ψ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
      (Proposition.imp (Proposition.box φ) (Proposition.box ψ))) := by
  intro h_box_imp h_box_phi w' hr; exact h_box_imp w' hr (h_box_phi w' hr)
```

**Note on `lemma` vs `theorem`**: These are `Prop`-valued declarations, so CSLib lint rules (defLemma) require `lemma` not `def`. Using `lemma` also matches the existing `Satisfies.t`, etc. pattern.

### Refactored System Files

Each system file replaces its 5 duplicated case proofs with one-liner delegations:

```lean
-- Example: S4 axiom sound (before: 16 base lines, after: 5 base lines)
theorem s4_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : S4Axiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | modalT φ =>
    intro h_box
    exact h_box w (h_refl w)
  | modalFour φ =>
    intro h_box w₁ hr₁ w₂ hr₂
    exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)
```

For K specifically: `k_axiom_sound` can be proved entirely by delegating all 5 cases, or the theorem can be removed and `k_soundness` can inline the delegation.

### Why This Approach

| Criterion | Assessment |
|-----------|-----------|
| No import changes needed | The shared file already imports `Basic.lean` via `DerivationTree` |
| No axiom type changes | Each `XAxiom` inductive stays as-is |
| No typeclass machinery | Simple lemma calls, no instance resolution |
| Naming consistency | Follows existing `Satisfies.t`, `Satisfies.b`, `Satisfies.four`, `Satisfies.five`, `Satisfies.d` pattern |
| Case split preserved | Each system file keeps its readable `cases h_ax with` structure |
| Zero sorry risk | Each lemma is trivially provable from the definition of `Satisfies` |

### Rejected Alternatives

1. **KAxiom embedding** (`KAxiom.ofTAxiom`): Would require importing `ProofSystem/Instances/K` into the shared file, creating a circular dependency risk. Also requires defining embedding functions for all 15 axiom types.

2. **Typeclass `HasKAxiomSoundness`**: Over-engineered — typeclass resolution overhead for 5 simple cases that are statically known at each call site. No extensibility benefit since the set of propositional axioms is fixed.

3. **Sum-type decomposition** (`KAxiom ⊕ SpecificAxiom`): Requires restructuring all 15 axiom inductives, touching the proof system layer. Massive blast radius for modest gain.

4. **Macro/metaprogramming**: Would obscure the proof structure and add a metaprogramming dependency. CSLib favors explicit proofs.

## Line Count Analysis

| Item | Lines |
|------|-------|
| Current total (16 files) | 1,375 |
| Duplicated base case lines (15 files × 16 lines) | 240 |
| After refactor: base cases become one-liners (15 × 5) | 75 |
| New shared lemmas added to Soundness.lean | ~25 |
| **Net reduction** | **~140 lines** |
| **Post-refactor total** | **~1,235 lines** |

The task description's target of ~600 lines reduced is not achievable from this refactoring alone. The actual identical propositional+K case block is 16 lines per file (not ~40). To approach 600 lines reduced, one would need additional orthogonal refactorings:
- Abstract the `_soundness` and `_soundness_derivable` wrapper theorems (which follow an identical pattern but differ in type signatures)
- Restructure the axiom inductives to share a common base type
- These are out of scope for this task and would constitute separate tasks.

## Implementation Plan Sketch

### Phase 1: Add shared lemmas to Soundness.lean (~25 new lines)

**File**: `Cslib/Logics/Modal/Metalogic/Soundness.lean`

Add 5 `Satisfies.*_axiom` lemmas between the module docstring section and the `soundness` theorem. No new imports needed.

### Phase 2: Refactor all 15 system Soundness.lean files

**Files**: All 15 `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean`

For each file, replace the 5 propositional+K case proof bodies with one-liner `exact Satisfies.*_axiom ...` calls. The case labels remain; only the proof bodies change.

### Phase 3: Verify

Run `lake build Cslib.Logics.Modal.Metalogic` to verify all 16 files compile.

## Risk Assessment

- **Risk**: Zero — all changes are mechanical replacements of proof bodies with equivalent lemma calls
- **Sorry risk**: Zero — the 5 shared lemmas are trivially provable
- **Import risk**: Zero — no import changes needed
- **Downstream breakage**: Zero — no public API changes; theorem signatures are unchanged

## References

- `Cslib/Logics/Modal/Basic.lean:130-134` — `Satisfies` definition
- `Cslib/Logics/Modal/Basic.lean:280-407` — existing `Satisfies.t/b/four/five/d` lemmas
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean:58-83` — `ModalAxiom` definition
- `Cslib/Logics/Modal/Metalogic/Soundness.lean:50-82` — parameterized `soundness` theorem
- Blackburn, de Rijke, Venema — "Modal Logic" (2002), Ch. 4, Definition 4.9
