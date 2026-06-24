# Implementation Plan: Task #314 -- LK Classical Sequent Calculus

- **Task**: 314 - LK classical sequent calculus for propositional logic
- **Status**: [IMPLEMENTING]
- **Effort**: 10 hours
- **Dependencies**: None (all infrastructure exists)
- **Research Inputs**: specs/314_lk_classical_sequent_calculus/reports/01_lk-research.md
- **Artifacts**: plans/01_lk-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Implement the classical sequent calculus LK for propositional logic in CSLib, following the
G3cp presentation from Negri & von Plato (2001) with cut elimination via lexicographic
induction from Troelstra & Schwichtenberg (2000, Ch. 4). The implementation creates 5 new
Lean files under `Cslib/Logics/Propositional/SequentCalculus/`, reusing the existing
`Proposition` type, `Proposition.complexity`, `InferenceSystem` typeclass, ND `Theory.Derivation`,
and `hilbert_iff_nd_ctx` bridge. Completeness is obtained as a corollary through bridge
composition with existing Hilbert completeness (`prop_completeness_iff_tautology` from
`Metalogic/StrongCompleteness.lean`).

### Research Integration

Key findings from the research report (01_lk-research.md):
- All-additive Finset-based design confirmed optimal for CSLib (shared contexts match ND)
- 11 constructors in `LKProof` (ax, botL, andL, andR, orL, orR, impL, impR, weakL, weakR, cut)
- Cut elimination uses `(Proposition.complexity A, d1.height + d2.height)` lexicographic measure
- Bridge via `hilbert_iff_lk = hilbert_iff_nd_ctx.trans nd_iff_lk`
- Estimated 840-1450 lines across 5 files

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `LKSequent` type with `⊢ₛ` notation
- Define `LKProof` inductive with all-additive Finset-based rules
- Prove structural admissibility (monotone context weakening)
- Prove soundness of LK with respect to Boolean semantics
- Prove cut elimination (Hauptsatz) via lexicographic induction
- Establish ND-LK equivalence bridge (`nd_iff_lk`)
- Derive Hilbert-LK bridge and LK completeness as corollaries

**Non-Goals**:
- Intuitionistic sequent calculus (LJ) -- separate task
- Decidability procedures via LK search
- Display calculus or deep inference variants
- Multi-succedent ND system

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cut elimination termination checker struggles | H | M | Use helper functions for each case; fall back to `WellFounded.recursion` with explicit `prod_lex` |
| Finset.insert commutativity bookkeeping | M | M | Use `simp [Finset.insert_comm]` systematically; prove rewrite lemmas up front |
| Theory handling in ND-to-LK bridge | M | L | Prove each `PropositionalAxiom` constructor is LK-derivable as individual lemmas |
| LK-to-ND direction for multi-succedent | M | L | Only prove single-conclusion case (`LKProof (Gamma ⊢ₛ {A})`) which suffices for Iff |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2 |
| 4 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Definitions and LK Proof Inductive [COMPLETED]


**Goal**: Create the foundational types, notation, and the LKProof inductive with structural
lemmas (height, mono, cutFree predicate).

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/Defs.lean` with:
  - `LKSequent` structure (ant/suc as `Finset (Proposition Atom)`)
  - Scoped notation `⊢ₛ` for `LKSequent.mk`
  - `LKSequent.valid` semantic validity definition
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LK/Basic.lean` with:
  - `LKProof` inductive (11 constructors: ax, botL, andL, andR, orL, orR, impL, impR, weakL, weakR, cut)
  - `LKProof.height` function
  - `LKProof.mono` (monotone context weakening by structural induction)
  - `CutFree` predicate on `LKProof`
  - `InferenceSystem` instance for LK
- [ ] Add barrel imports: create `Cslib/Logics/Propositional/SequentCalculus.lean` and `Cslib/Logics/Propositional/SequentCalculus/LK.lean`
- [ ] Run `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Basic` to verify

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/Defs.lean` - new file
- `Cslib/Logics/Propositional/SequentCalculus/LK/Basic.lean` - new file
- `Cslib/Logics/Propositional/SequentCalculus.lean` - new barrel import
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` - new barrel import

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Basic` succeeds
- `LKProof` has 11 constructors
- `LKProof.mono` type-checks with correct signature

---

### Phase 2: Soundness [COMPLETED]

**Goal**: Prove that every LK-derivable sequent is semantically valid.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LK/Soundness.lean`
- [ ] Prove `LKProof.sound : LKProof seq → seq.valid` by structural induction on LKProof
  - Each case (ax, botL, andL, andR, orL, orR, impL, impR, weakL, weakR, cut) follows by 2-5 lines of case analysis using `Evaluate` simp lemmas
- [ ] Derive `Nonempty (LKProof seq) → seq.valid` as corollary
- [ ] Run `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Soundness`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Soundness.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Soundness` succeeds
- `LKProof.sound` has correct type signature
- No `sorry` in the file

---

### Phase 3: Cut Elimination [IN PROGRESS]

**Goal**: Prove the Hauptsatz -- every LK proof can be transformed into a cut-free proof.

**Research inputs**: `specs/314_lk_classical_sequent_calculus/reports/02_cutelim-rewrite-research.md`

**Architecture (revised per research findings)**:

The first implementation attempt (873 lines) failed with ~100 build errors due to three
interconnected issues with Lean 4's dependent elimination on Finset (quotient type):
1. `cases` on `LKProof` indexed by `insert`-structured Finset triggers "Failed to solve equation"
2. `Or.casesOn` cannot eliminate into Type (only Prop), blocking Finset.mem_insert branching
3. `CutFree` is a recursive def, not an inductive — anonymous constructor `⟨...⟩` fails

The fix uses the **generic-sequent helper pattern**: define case-analysis helpers with a
FREE `{seq : LKSequent Atom}` parameter. Lean unifies constructor patterns with the free
variable without solving Finset quotient equations. Callers pass subset proofs connecting
the generic sequent to the specific structured sequent.

**Proof strategy** (per [TroelstraSchwichtenberg2000] Theorem 4.1.5 and [NegriVonPlato2001]
Theorem 3.2.3): Main recursion on formula complexity (`match A with`), with each case
using generic-sequent helpers for structural case analysis on the proof trees. Termination
by `sizeOf A` (compound principal cases recurse on strict subformulas).

**Tasks**:
- [ ] Rewrite `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` from scratch
- [ ] Keep height lemmas (lines 111-145 of current file — these build correctly)
- [ ] Fix `CutFree.mono_aux` (argument order errors in current version)
- [ ] Implement `cutAdm_atom` + generic-sequent helper `cutAdm_atom_left`:
  - Match on `d₁` with free `{seq}` parameter
  - Use `if heq : phi = .atom x then ... else ...` (DecidableEq) for membership branching
  - `cut` case: `absurd hcf (by simp [CutFree])`
- [ ] Implement `cutAdm_bot` + generic-sequent helper:
  - Similar to atom; `⊥` in antecedent gives `botL` directly
- [ ] Implement `cutAdm_imp` + generic-sequent helpers (most complex):
  - Non-principal subcases: recurse with same formula, structurally smaller proof
  - Principal case (impR left, impL right): 4 sub-cuts per [NegriVonPlato2001] p. 57:
    1. Cut `A→B` from d₁ and d₂a (same formula, smaller proof) → `Γ ⊢ₛ insert A Δ`
    2. Cut `A` from step1 and d₁' using IH for A → `Γ ⊢ₛ insert B Δ`
    3. Cut `A→B` from d₁ and d₂b (same formula, smaller proof) → `insert B Γ ⊢ₛ Δ`
    4. Cut `B` from step2 and step3 using IH for B → `Γ ⊢ₛ Δ`
  - Takes continuation `ih` for recursive calls on subformulas
- [ ] Implement `cutAdm_and` + generic-sequent helpers:
  - Principal case (andR left, andL right): symmetric to imp pattern
- [ ] Implement `cutAdm_or` + generic-sequent helpers:
  - Principal case (orR left, orL right): symmetric to imp pattern
- [ ] Wire up top-level `cutAdmissibility`:
  ```
  noncomputable def cutAdmissibility
      (A : Proposition Atom) (Γ Δ : Finset (Proposition Atom))
      (d₁ : CutFreeLKProof (Γ ⊢ₛ insert A Δ))
      (d₂ : CutFreeLKProof (insert A Γ ⊢ₛ Δ)) :
      CutFreeLKProof (Γ ⊢ₛ Δ)
  termination_by sizeOf A
  ```
- [ ] Wire up `LKProof.cutElim`:
  ```
  theorem LKProof.cutElim (d : LKProof seq) : Nonempty (CutFreeLKProof seq)
  ```
  By structural induction; `cut` case uses `cutAdmissibility` on IH results.
- [ ] Run `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination`

**Key constraints**:
- Mark all definitions `noncomputable` (DecidableEq branching into Type requires it)
- Use `CutFreeLKProof.mono` (exists in Basic.lean) for context weakening
- Use `CutFree.mono` (exists in Basic.lean) for threading CutFree evidence through `LKProof.mono`
- No changes to `Basic.lean` — all definitions there build correctly
- Generic-sequent helpers use `⊆` (subset) for `hant`/`hsuc` instead of `=` (equality)

**Timing**: 4 hours (increased from 3 due to architectural complexity)

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - full rewrite

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` succeeds
- `cutAdmissibility` proves cut is removable
- No `sorry` in the file
- `lean_verify` confirms no axiom usage beyond standard

---

### Phase 4: ND-LK Bridge Proofs [IN PROGRESS]

**Goal**: Establish equivalence between ND derivability and LK derivability for single-conclusion
sequents, and compose with Hilbert bridge.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LK/Completeness.lean`
- [ ] Prove `ndToLK : T.Derivation Gamma A → LKProof (Gamma ⊢ₛ {A})` by structural induction on ND derivation
  - `ax h_mem`: Prove each CPL axiom is LK-derivable (10 concrete proofs for `PropositionalAxiom` constructors), then weaken
  - `ass h_mem`: `LKProof.ax A` with `mono` to fill context
  - `andI`: compose via `andR` with `mono`
  - `andE1`/`andE2`: `andL` then `ax`
  - `orI1`/`orI2`: `orR` with weakening
  - `orE`: `orL` on branches, compose with `cut`
  - `impI`: `impR`
  - `impE`: `impL` with `cut`
- [ ] Prove `lkToND : LKProof (Gamma ⊢ₛ {A}) → T.Derivation Gamma A` for single-conclusion case
  - Each LK constructor maps back to ND operations
  - Multi-conclusion LK cases cannot arise with singleton succedent (cases on the succedent structure)
- [ ] State and prove `nd_iff_lk`:
  ```
  nd_iff_lk : DerivableIn (AxiomTheory PropositionalAxiom) (Gamma ⊢ A) ↔
              Nonempty (LKProof (Gamma ⊢ₛ {A}))
  ```
- [ ] Compose `hilbert_iff_lk`:
  ```
  hilbert_iff_lk : Deriv PropositionalAxiom Gamma.toList phi ↔
                   Nonempty (LKProof (Gamma ⊢ₛ {phi}))
  ```
  via `hilbert_iff_nd_ctx.trans nd_iff_lk`
- [ ] Run `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Completeness`

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Completeness.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Completeness` succeeds
- `nd_iff_lk` and `hilbert_iff_lk` type-check
- No `sorry` in the file

---

### Phase 5: Completeness Corollary and CI Verification [IN PROGRESS]

**Goal**: Derive LK completeness from Hilbert completeness, register barrel imports, and pass
the full CI pipeline.

**Tasks**:
- [ ] Add LK completeness corollary to `Completeness.lean`:
  ```
  lk_completeness : Tautology phi → Nonempty (LKProof (∅ ⊢ₛ {phi}))
  ```
  via `prop_completeness_iff_tautology.mp` composed with `hilbert_iff_lk.mp`
- [ ] Add LK soundness-completeness iff:
  ```
  lk_iff_tautology : Tautology phi ↔ Nonempty (LKProof (∅ ⊢ₛ {phi}))
  ```
- [ ] Update `Cslib/Logics/Propositional/SequentCalculus/LK.lean` barrel to import all 4 LK files
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean`
- [ ] Run full CI pipeline:
  - `lake build`
  - `lake exe checkInitImports`
  - `lake exe lint-style`
  - `lake test`
  - `lake shake --add-public --keep-implied --keep-prefix`
- [ ] Fix any lint or style issues

**Timing**: 1 hour

**Depends on**: 2, 3, 4

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Completeness.lean` - add corollaries
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` - update barrel imports
- `Cslib.lean` - auto-updated by `mk_all`

**Verification**:
- Full `lake build` succeeds
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- No `sorry` anywhere in the 5 new files

---

## Testing & Validation

- [ ] All 5 new files compile without errors (`lake build`)
- [ ] No `sorry` in any file (`lean_verify` on key theorems)
- [ ] `LKProof.sound` correctly relates derivability to `LKSequent.valid`
- [ ] `cutAdmissibility` produces genuine cut-free proofs
- [ ] `nd_iff_lk` establishes bidirectional equivalence
- [ ] `hilbert_iff_lk` composes through ND bridge
- [ ] `lk_completeness` follows from Hilbert completeness
- [ ] CI pipeline passes: `checkInitImports`, `lint-style`, `lake test`

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/Defs.lean` - LKSequent type and notation
- `Cslib/Logics/Propositional/SequentCalculus/LK/Basic.lean` - LKProof inductive, structural lemmas
- `Cslib/Logics/Propositional/SequentCalculus/LK/Soundness.lean` - Semantic soundness
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - Hauptsatz
- `Cslib/Logics/Propositional/SequentCalculus/LK/Completeness.lean` - Bridge proofs, completeness
- `Cslib/Logics/Propositional/SequentCalculus.lean` - Barrel import
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` - LK barrel import
- `specs/314_lk_classical_sequent_calculus/plans/01_lk-plan.md` - This plan

## Rollback/Contingency

All changes are additive (new files only). Rollback by deleting the
`Cslib/Logics/Propositional/SequentCalculus/` directory and its barrel imports. No existing
files are modified. If cut elimination proves intractable with the termination checker,
a fallback is to use `noncomputable` with `WellFounded.recursion` and explicit
`WellFounded.prod_lex` witness, or to leave `cutElim` with a `sorry` on the termination
proof only and mark Phase 3 as [PARTIAL].
