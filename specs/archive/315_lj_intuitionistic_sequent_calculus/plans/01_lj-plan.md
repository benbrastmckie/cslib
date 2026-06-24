# Implementation Plan: LJ Intuitionistic Sequent Calculus

- **Task**: 315 - LJ intuitionistic sequent calculus for propositional logic
- **Status**: [COMPLETED]
- **Effort**: 16 hours
- **Dependencies**: Task 314 (LK) must be complete (verified: LK files exist)
- **Research Inputs**: specs/315_lj_intuitionistic_sequent_calculus/reports/01_lj-research.md
- **Artifacts**: plans/01_lj-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Implement the intuitionistic sequent calculus LJ for propositional logic within CSLib, following
the established LK implementation pattern. LJ uses single-conclusion sequents (reusing the
existing ND `Sequent` type = `Ctx Atom x Proposition Atom`) with 11 constructors matching the
LK-style all-additive presentation. The implementation covers the LJProof inductive type with
structural lemmas, soundness via Kripke semantics, cut elimination (Hauptsatz), and equivalence
bridges to ND and Hilbert systems for intuitionistic logic. The file layout mirrors LK:
`LJ/Basic.lean`, `LJ/Soundness.lean`, `LJ/CutElimination.lean`, `LJ/Completeness.lean`,
plus barrel files `LJ.lean` and updates to `SequentCalculus.lean`.

### Research Integration

The research report (01_lj-research.md) provides:
- Confirmed that LJ reuses ND `Sequent` type (not `LKSequent`)
- Proposed LJProof inductive with 11 constructors (ax, botL, andL, andR, orL, orR1, orR2,
  impL, impR, weakL, cut) -- no `weakR` since single-conclusion
- Soundness targets Kripke semantics (`IForces`/`IValid`), not Boolean valuation
- Cut elimination follows LK pattern, estimated 400-600 lines (simpler due to single-conclusion)
- ND-LJ bridge is structural but requires cut for elimination rules
- Hilbert-LJ bridge composes `hilbert_iff_nd_ctx_int` with `nd_iff_lj`
- No blockers identified; all dependencies available

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `LJProof` inductive type with 11 constructors for intuitionistic propositional logic
- Prove structural admissibility: `LJProof.mono` (left weakening), `LJProof.height`
- Define `CutFree` predicate and `CutFreeLJProof` subtype
- Prove soundness relative to Kripke semantics (`IForces` with `bot_forces = fun _ => False`)
- Prove cut elimination: `cutAdmissibility` and `LJProof.cutElim`
- Build ND-LJ equivalence bridge (`nd_iff_lj`) via structural translation
- Build Hilbert-LJ bridge (`hilbert_iff_lj`) by composing existing bridges
- Create barrel imports (`LJ.lean`, update `SequentCalculus.lean`)
- Pass full CI pipeline (lake build, checkInitImports, lint-style, lake test)

**Non-Goals**:
- No `LJSequent` as a new structure (reuse ND `Sequent` type via abbreviation)
- No right weakening (`weakR`) -- single-conclusion sequents have no succedent set
- No negation (`neg`) as a primitive -- it is encoded as `A -> bot`
- No separate notation for LJ sequents (reuse `Gamma |- A` from ND module)
- No quantifier or first-order extensions
- No decision procedure for LJ provability

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cut elimination proof exceeds 600 lines | M | M | Follow LK pattern closely; LJ is structurally simpler (no weakR, no succedent Finset management) |
| `ndToLJ` requires `noncomputable` due to Prop-valued `IntPropAxiom` | L | H | Use same `Classical.choice` + `Nonempty` pattern as `ndToLK`; mark `noncomputable` |
| Kripke soundness requires `iforces_persistence` in every imp case | M | L | `iforces_persistence` already exists and is proven; use it directly |
| LJProof indexing over ND `Sequent` creates unification issues with LK code | M | L | LJ and LK modules are independent; no shared proof terms needed |
| `IntPropAxiom` axiom dispatch for LJ differs from `PropositionalAxiom` (no Peirce) | L | H | Fewer cases (9 vs 10); no `peirce` case simplifies the axiom proofs |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: LJ/Basic.lean -- Inductive, Height, Mono, CutFree [COMPLETED]

**Goal**: Define the LJProof inductive type, proof height function, monotonicity lemma
(left weakening), and cut-freeness predicate. This is the foundation all other files import.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean`
- [ ] Add copyright header, `module`, `import Cslib.Init`, `public import` of
      `Cslib.Logics.Propositional.NaturalDeduction.Basic` (for `Sequent`, `Ctx` types)
      and `Cslib.Foundations.Logic.InferenceSystem`
- [ ] Define `LJProof : @Sequent Atom -> Type u` inductive with 11 constructors:
      `ax`, `botL`, `andL`, `andR`, `orL`, `orR1`, `orR2`, `impL`, `impR`, `weakL`, `cut`
      following the signatures from research report Section 4
- [ ] Define `LJProof.height : LJProof seq -> Nat` by structural recursion (same pattern as
      `LKProof.height` but with `orR1`/`orR2` instead of single `orR`, no `weakR`)
- [ ] Prove `LJProof.mono : (hL : Gamma <= Gamma') -> LJProof (Gamma |- C) -> LJProof (Gamma' |- C)`
      by structural induction (left-side only monotonicity, simpler than LK's two-sided mono)
- [ ] Define `CutFree : LJProof seq -> Prop` predicate (True on all constructors except `cut`)
- [ ] Define `CutFreeLJProof seq := { d : LJProof seq // CutFree d }`
- [ ] Add `InferenceSystem` instance for `@Sequent Atom` using `LJProof`
- [ ] Add module docstring with references to Negri & von Plato (2001) and
      Troelstra & Schwichtenberg (2000)
- [ ] Verify: `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Basic`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` - create new file

**Verification**:
- File compiles without errors or warnings
- `LJProof` has exactly 11 constructors
- `LJProof.mono` type-checks with single-sided weakening
- `CutFree` returns `False` only on the `cut` constructor

---

### Phase 2: LJ/Soundness.lean -- Kripke Semantics Soundness [IN PROGRESS]

**Goal**: Prove that every LJ-derivable sequent is valid in intuitionistic Kripke semantics.
Unlike LK soundness which uses Boolean valuation, LJ soundness targets `IForces` with
`bot_forces = fun _ => False`.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LJ/Soundness.lean`
- [ ] Add imports: `LJ.Basic`, `Cslib.Logics.Propositional.Semantics.Kripke`
- [ ] Define `LJSequent.ivalid (seq : @Sequent Atom) : Prop` as:
      for every `World`, `Preorder World`, Kripke model `M`, and world `w`,
      if all antecedent formulas are forced then the conclusion is forced
      (using `IForces M.v (fun _ => False) w`)
- [ ] Prove `LJProof.sound : LJProof seq -> LJSequent.ivalid seq` by structural induction:
  - `ax`: direct from antecedent hypothesis
  - `botL`: from `IForces_bot` with `bot_forces = fun _ => False` giving `False`
  - `andL`: decompose via `IForces_and`, reconstruct antecedent membership
  - `andR`: combine both IH results via `IForces_and`
  - `orL`: case split via `IForces_or`, apply appropriate IH
  - `orR1/orR2`: wrap via `IForces_or`
  - `impL`: the key case -- use `iforces_persistence` for the imp hypothesis,
    apply IH for left premise to get the antecedent, IH for right premise with consequent
  - `impR`: introduce universal quantification over future worlds, apply IH
  - `weakL`: restrict antecedent hypothesis
  - `cut`: compose IH for both premises
- [ ] Prove convenience lemma `lj_sound` wrapper
- [ ] Add module docstring
- [ ] Verify: `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Soundness`

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Soundness.lean` - create new file

**Verification**:
- File compiles without errors
- `LJProof.sound` type-checks with Kripke validity target
- `impL` and `impR` cases correctly use `iforces_persistence`
- No sorry/sorry-equivalent remains

---

### Phase 3: LJ/CutElimination.lean -- Hauptsatz [NOT STARTED]

**Goal**: Prove cut admissibility for LJ: every LJ proof can be transformed into a cut-free
proof. This follows the LK cut elimination pattern (structural induction on the cut formula)
but is simpler due to single-conclusion sequents.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean`
- [ ] Add imports: `LJ.Basic`
- [ ] Prove `CutFree.mono`: cut-freeness preserved under `LJProof.mono`
      (by structural recursion, same pattern as LK `CutFree.mono` but single-sided)
- [ ] Prove `CutFreeLJProof.mono`: cut-free proof monotonicity wrapper
- [ ] Prove height lemmas for structural induction:
  - `LJProof.height_lt_andL`, `height_lt_andR_left`, `height_lt_andR_right`
  - `height_lt_orL_left`, `height_lt_orL_right`, `height_lt_orR1`, `height_lt_orR2`
  - `height_lt_impL_left`, `height_lt_impL_right`, `height_lt_impR`
  - `height_lt_weakL`, `height_lt_cut_left`, `height_lt_cut_right`
- [ ] Prove `cutAdmissibility`:
      From cut-free proofs of `Gamma |- A` and `insert A Gamma |- C`,
      produce a cut-free proof of `Gamma |- C`.
      By structural induction on `A` (the cut formula):
  - **Atom/bot base cases**: inner induction on d1 proof
  - **And case (principal)**: d1 = `andR`, d2 = `andL` -- use IH for subformulas
  - **Or case (principal)**: d1 = `orR1`/`orR2`, d2 = `orL` -- use IH for subformulas
  - **Imp case (principal)**: d1 = `impR`, d2 = `impL` -- use IH for A and B subformulas
  - **Non-principal cases**: structural pushing of the cut through rules
- [ ] Prove `LJProof.cutElim : LJProof seq -> Nonempty (CutFreeLJProof seq)`
      by structural induction on the proof, applying `cutAdmissibility` at `cut` nodes
- [ ] Add module docstring with Troelstra & Schwichtenberg (2000) Ch. 4 reference
- [ ] Verify: `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination`

**Timing**: 5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - create new file

**Verification**:
- File compiles without errors
- `cutAdmissibility` takes `CutFree` inputs and produces `CutFree` output
- `LJProof.cutElim` produces `Nonempty (CutFreeLJProof seq)`
- All height lemmas verified (used in well-founded recursion)
- No sorry/sorry-equivalent remains

---

### Phase 4: LJ/Completeness.lean -- ND-LJ and Hilbert-LJ Bridges [NOT STARTED]

**Goal**: Build equivalence bridges connecting LJ to ND (under `AxiomTheory IntPropAxiom`)
and Hilbert (`IntPropAxiom`). The ND-LJ bridge is structural; the Hilbert-LJ bridge composes
existing bridges.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LJ/Completeness.lean`
- [ ] Add imports: `LJ.Soundness`,
      `Cslib.Logics.Propositional.NaturalDeduction.Equivalence`,
      `Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness`
- [ ] Build LJ proofs for each `IntPropAxiom` constructor (9 cases, no Peirce):
  - `ljAxiomImplyK`, `ljAxiomImplyS`, `ljAxiomEfq`
  - `ljAxiomAndI`, `ljAxiomAndE1`, `ljAxiomAndE2`
  - `ljAxiomOrI1`, `ljAxiomOrI2`, `ljAxiomOrE`
  - Each proves `LJProof (empty |- axiom_formula)` using LJ rules
  - Pattern: `impR` wrappers, then left rules + `ax` leaves
  - Simpler than LK versions: no succedent membership proofs needed
- [ ] Prove `ljOfIntAxiom`: dispatch on `IntPropAxiom` to produce
      `Nonempty (LJProof (Gamma |- phi))` (using `LJProof.mono` to weaken from empty)
- [ ] Define `noncomputable def ndToLJ`:
      `(AxiomTheory IntPropAxiom).Derivation Gamma A -> LJProof (Gamma |- A)`
      by structural induction on ND derivation:
  - `ax h_mem`: `Classical.choice (ljOfIntAxiom h_mem)`
  - `ass h_mem`: `LJProof.ax A Gamma h_mem`
  - `andI d1 d2`: `LJProof.andR A B (ndToLJ d1) (ndToLJ d2)`
  - `andE1 d`: cut with `andL` (as in LK pattern)
  - `andE2 d`: cut with `andL`
  - `orI1 d`: `LJProof.orR1` (direct, no succedent membership)
  - `orI2 d`: `LJProof.orR2`
  - `orE d dA dB`: cut with `orL`
  - `impI d`: `LJProof.impR` (direct)
  - `impE d1 d2`: cut with `impL`
- [ ] Prove `nd_iff_lj`:
      `DerivableIn (AxiomTheory IntPropAxiom) (Gamma |- A) <->
       Nonempty (LJProof (Gamma |- A))`
  - Forward: by `ndToLJ`
  - Backward: LJ soundness -> Kripke validity -> `ISemanticEntails` ->
    `int_strong_completeness` -> `SetDerivable IntPropAxiom` ->
    `hilbert_iff_nd_ctx_int` -> ND derivability
- [ ] Prove `hilbert_iff_lj`:
      `Deriv IntPropAxiom Gamma.toList phi <-> Nonempty (LJProof (Gamma |- phi))`
      by composing `hilbert_iff_nd_ctx_int.symm` with `nd_iff_lj`
- [ ] Prove corollaries:
  - `lj_completeness`: `IValid phi -> Nonempty (LJProof (empty |- phi))`
  - `lj_iff_ivalid`: `IValid phi <-> Nonempty (LJProof (empty |- phi))`
- [ ] Add module docstring
- [ ] Verify: `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Completeness`

**Timing**: 4 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Completeness.lean` - create new file

**Verification**:
- File compiles without errors
- `ndToLJ` is marked `noncomputable`
- `nd_iff_lj` gives iff between ND derivability and LJ provability
- `hilbert_iff_lj` gives iff between Hilbert derivability and LJ provability
- `lj_iff_ivalid` gives iff between intuitionistic validity and LJ provability
- No sorry/sorry-equivalent remains

---

### Phase 5: Barrel Files, CI, and Final Verification [NOT STARTED]

**Goal**: Create barrel import files, update the SequentCalculus module barrel, run full CI
pipeline, and ensure all files pass lint and style checks.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LJ.lean` barrel file:
      import all four LJ submodules (Basic, Soundness, CutElimination, Completeness)
- [ ] Update `Cslib/Logics/Propositional/SequentCalculus.lean` to add
      `public import Cslib.Logics.Propositional.SequentCalculus.LJ`
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [ ] Run full CI verification:
  - `lake build` (full project build)
  - `lake exe checkInitImports` (all files import Cslib.Init)
  - `lake exe lint-style` (text linters)
  - `lake test` (CslibTests suite)
- [ ] Fix any lint or style issues discovered
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` for import minimization
- [ ] Verify `lean_verify` on key theorems:
  `Cslib.Logic.PL.LJProof.sound`, `Cslib.Logic.PL.LJProof.cutElim`,
  `Cslib.Logic.PL.nd_iff_lj`, `Cslib.Logic.PL.hilbert_iff_lj`

**Timing**: 1.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ.lean` - create barrel file
- `Cslib/Logics/Propositional/SequentCalculus.lean` - add LJ import
- `Cslib.lean` - auto-updated by `mk_all`

**Verification**:
- Full `lake build` passes with zero errors
- `checkInitImports` passes
- `lint-style` passes
- `lake test` passes
- `lake shake` produces no required changes
- All key theorems verified axiom-clean via `lean_verify`

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Basic` -- Basic module compiles
- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Soundness` -- Soundness compiles
- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination` -- Cut elimination compiles
- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Completeness` -- Completeness compiles
- [ ] `lake build` -- Full project builds cleanly
- [ ] `lake exe checkInitImports` -- All files import Cslib.Init
- [ ] `lake exe lint-style` -- No style violations
- [ ] `lake test` -- Test suite passes
- [ ] `lean_verify` on `LJProof.sound` -- No sorry, no non-standard axioms
- [ ] `lean_verify` on `LJProof.cutElim` -- No sorry, no non-standard axioms
- [ ] `lean_verify` on `nd_iff_lj` -- No sorry (may use `Classical.choice` via noncomputable)
- [ ] `lean_verify` on `hilbert_iff_lj` -- No sorry

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` -- LJProof inductive, height, mono, CutFree
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Soundness.lean` -- Kripke soundness
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` -- Hauptsatz
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Completeness.lean` -- ND/Hilbert bridges
- `Cslib/Logics/Propositional/SequentCalculus/LJ.lean` -- barrel import
- `Cslib/Logics/Propositional/SequentCalculus.lean` -- updated barrel
- `specs/315_lj_intuitionistic_sequent_calculus/plans/01_lj-plan.md` -- this plan

## Rollback/Contingency

All changes are additive (new files in a new `LJ/` subdirectory plus barrel updates). To
rollback:
1. Delete `Cslib/Logics/Propositional/SequentCalculus/LJ/` directory
2. Remove `LJ.lean` barrel
3. Revert the `SequentCalculus.lean` barrel change (remove the `LJ` import line)
4. Run `lake exe mk_all --module` to regenerate `Cslib.lean`

No existing files are modified in substance; the only edits to existing files are import
additions in barrel files.

If cut elimination proves intractable within the time budget:
- Complete phases 1, 2, and 4 (Basic, Soundness, Completeness) with cut as an admitted rule
- Mark Phase 3 as [BLOCKED] with a detailed description of the stuck point
- The bridges in Phase 4 use cut (via `ndToLJ`) so they work regardless of cut elimination status
- Cut elimination can be completed in a follow-up task
