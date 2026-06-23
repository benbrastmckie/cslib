# Implementation Plan: Task #283 - Restate Algebraic Completeness as Hilbert-Primary

- **Task**: 283 - Restate algebraic completeness as Hilbert-primary
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: Task 282 (Hilbert Lindenbaum algebra -- done)
- **Research Inputs**: specs/283_hilbert_primary_algebraic_completeness/reports/01_hilbert-completeness.md
- **Artifacts**: plans/01_hilbert-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This task makes the Hilbert system the primary formulation for algebraic completeness across all three propositional logic tiers (MPL, IPL, CPL). Currently, HilbertCompleteness.lean routes the completeness direction through ND completeness (`MPL.alg_complete`, `IPL.alg_complete`) plus the `hilbert_iff_nd` bridge. After this task, the completeness direction will use the Hilbert Lindenbaum algebra directly: a canonical valuation into `HilbertLindenbaumAlgebra Axioms`, a truth lemma, and the `hilbertLindenbaumMk_eq_top_iff` characterization. ND completeness theorems in Completeness.lean are kept unchanged; downstream files (Conservative.lean, Glivenko.lean) continue to use them.

### Research Integration

Key findings from the research report:

1. **ND completeness theorems** (`Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical`) are all stated for `DerivableIn T` in Completeness.lean and are directly referenced by Conservative.lean (line 166-168) and Glivenko.lean (lines 128-129). These must be preserved as-is.
2. **Hilbert completeness theorems** (`MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete`) exist in HilbertCompleteness.lean but route through ND -- these will be rewritten.
3. **Soundness theorems** (`min_alg_soundness_derivable`, `int_alg_soundness_derivable`, `prop_alg_soundness_derivable`) are already Hilbert-primary -- no changes needed.
4. **Missing piece**: `hilbertLindenbaumMk_eq_top_iff` lemma in HilbertLindenbaum.lean, plus canonical valuation and truth lemma.
5. The HilbertLindenbaum.lean module already provides all required algebra instances and simp lemmas for the truth lemma proof.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is part of the Hilbert-primary proof system chain: 281 (done) -> 282 (done) -> **283** -> 284 -> 285.

## Goals & Non-Goals

**Goals**:
- Add `hilbertLindenbaumMk_eq_top_iff` to HilbertLindenbaum.lean (truth-at-top characterization)
- Add Hilbert canonical valuation (`Hilbert.canonicalV`, `Hilbert.canonicalBotVal`) and truth lemma (`Hilbert.canonicalV_spec`) to HilbertLindenbaum.lean
- Rewrite `MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete` in HilbertCompleteness.lean to use the Hilbert Lindenbaum algebra directly (removing ND dependency for the completeness direction)
- Remove the ND-routing imports from HilbertCompleteness.lean (it should no longer need `Completeness.lean`)
- Ensure full project builds cleanly

**Non-Goals**:
- Do NOT modify Completeness.lean (ND completeness theorems stay as-is for Conservative/Glivenko)
- Do NOT modify Soundness.lean (already Hilbert-primary)
- Do NOT restate Conservative.lean or Glivenko.lean (that is tasks 284-285)
- Do NOT add new theorem names -- keep existing `MPL.hilbert_alg_complete` etc. names

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `hilbertLindenbaumMk_eq_top_iff` proof difficulty (quotient + cut reasoning) | H | L | Research sketched the proof; `Quotient.exact`/`Quotient.sound` + `hilbertImpIDeriv` are available |
| Universe level mismatch when instantiating HilbertLindenbaumAlgebra in completeness proof | M | L | Existing HilbertCompleteness.lean already handles this pattern; follow same `{Atom : Type u}` approach |
| Removing Completeness.lean import from HilbertCompleteness.lean breaks transitive imports | M | M | Check what HilbertCompleteness.lean actually needs; may still need Soundness.lean import |
| `hilbert_iff_nd_min` bridge no longer needed in HilbertCompleteness.lean after refactor | L | H | Remove the bridge import; it is only used in the completeness direction being replaced |
| IPL canonical bot_val definitional equality with Heyting algebra bot | L | L | Both are `hilbertLindenbaumMk bot` -- definitionally equal |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

### Phase 1: Foundation Lemmas in HilbertLindenbaum.lean [COMPLETED]

**Goal**: Add the `hilbertLindenbaumMk_eq_top_iff` lemma, canonical valuation, and truth lemma to HilbertLindenbaum.lean. These are the building blocks for the direct Hilbert completeness proof.

**Tasks**:
- [ ] Add `hilbertLindenbaumMk_eq_top_iff` theorem after the existing API simp lemmas section:
  ```lean
  theorem hilbertLindenbaumMk_eq_top_iff
      {Axioms : Proposition Atom -> Prop} [inst : MinimalAxioms Axioms]
      {A : Proposition Atom} :
      hilbertLindenbaumMk (Axioms := Axioms) A = top <-> Derivable Axioms A
  ```
  Proof strategy: rewrite `top` via `hilbertLindenbaumTop` to `[bot.imp bot]`, then use `Quotient.exact`/`Quotient.sound` with `HilbertEquiv`. Forward direction extracts `Deriv [bot.imp bot] A` from quotient equality, cuts with `Deriv [] (bot.imp bot)` (from `hilbertImpIDeriv`). Backward direction weakens `Deriv [] A` and constructs `HilbertEquiv`.
- [ ] Add `Hilbert.canonicalV` definition:
  ```lean
  def Hilbert.canonicalV (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms] :
      Atom -> HilbertLindenbaumAlgebra Axioms :=
    fun x => hilbertLindenbaumMk (.atom x)
  ```
- [ ] Add `Hilbert.canonicalBotVal` definition:
  ```lean
  def Hilbert.canonicalBotVal (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms] :
      HilbertLindenbaumAlgebra Axioms :=
    hilbertLindenbaumMk .bot
  ```
- [ ] Add `Hilbert.canonicalV_spec` truth lemma:
  ```lean
  theorem Hilbert.canonicalV_spec
      (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms]
      (A : Proposition Atom) :
      AlgEvaluate (Hilbert.canonicalV Axioms) (Hilbert.canonicalBotVal Axioms) A =
      hilbertLindenbaumMk A
  ```
  Proof by structural induction on `A`, using `rfl` for `atom`/`bot` cases and existing simp lemmas (`hilbertLindenbaumMk_himp`, `hilbertLindenbaumMk_inf`, `hilbertLindenbaumMk_sup`) for connective cases.
- [ ] Add `Hilbert.tValid_canonicalV` lemma for axiom validity:
  ```lean
  theorem Hilbert.tValid_canonicalV
      (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms]
      (phi : Proposition Atom) (h : Axioms phi) :
      AlgEvaluate (Hilbert.canonicalV Axioms) (Hilbert.canonicalBotVal Axioms) phi = top
  ```
  Proof: rewrite via `canonicalV_spec` to `hilbertLindenbaumMk phi = top`, then apply `hilbertLindenbaumMk_eq_top_iff` with the axiom derivation.
- [ ] Verify phase: `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- add ~60 lines before `end Cslib.Logic.PL`

**Verification**:
- Module builds without errors
- `lean_verify` on `hilbertLindenbaumMk_eq_top_iff` shows no sorry/axiom issues
- `lean_verify` on `Hilbert.canonicalV_spec` shows no sorry/axiom issues

---

### Phase 2: Rewrite HilbertCompleteness.lean [COMPLETED]

**Goal**: Refactor the completeness direction of all three Hilbert completeness theorems to use the Hilbert Lindenbaum algebra directly, removing the ND detour.

**Tasks**:
- [ ] Update imports in HilbertCompleteness.lean:
  - Add: `public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum`
  - Keep: `public import Cslib.Logics.Propositional.Semantics.Algebra.Soundness` (for soundness direction)
  - Remove (if safe): `public import Cslib.Logics.Propositional.Semantics.Algebra.Completeness` (no longer needed for completeness direction)
  - Remove (if safe): `public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence` (bridge no longer needed)
  - Remove (if safe): `public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness` (was only needed for CPL route through tautology)
  - Remove: `public import Cslib.Logics.Propositional.Semantics.Algebra.Bridge` (no longer needed)
- [ ] Remove `ipl_subset_axiomTheory_int` lemma (only used in old IPL completeness route)
- [ ] Rewrite `MPL.hilbert_alg_complete` completeness direction:
  ```lean
  -- New completeness direction:
  intro h
  have hLind := h (H := HilbertLindenbaumAlgebra MinPropAxiom)
    (Hilbert.canonicalV MinPropAxiom) (Hilbert.canonicalBotVal MinPropAxiom)
  rw [Hilbert.canonicalV_spec] at hLind
  exact hilbertLindenbaumMk_eq_top_iff.mp hLind
  ```
- [ ] Rewrite `IPL.hilbert_alg_complete` completeness direction:
  The Heyting algebra instance is `hilbertLindenbaumIntHA`. The canonical `bot_val` is `hilbertLindenbaumMk .bot` which equals `bot` in the Heyting algebra. Instantiate `HAValid` at `HilbertLindenbaumAlgebra IntPropAxiom` with `Hilbert.canonicalV IntPropAxiom`.
- [ ] Rewrite `CPL.hilbert_alg_complete` completeness direction:
  The Boolean algebra instance is `hilbertLindenbaumClBA`. Instantiate `BAValid` at `HilbertLindenbaumAlgebra PropositionalAxiom` with `Hilbert.canonicalV PropositionalAxiom`. Remove the `baValid_implies_tautology` helper (only used in old CPL route).
- [ ] Update module docstring to reflect the new proof strategy (no longer routes through ND)
- [ ] Verify phase: `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` -- rewrite completeness directions (~80 lines changed)

**Verification**:
- Module builds without errors
- `lean_verify` on `MPL.hilbert_alg_complete` -- no sorry, no axiom issues
- `lean_verify` on `IPL.hilbert_alg_complete` -- no sorry, no axiom issues
- `lean_verify` on `CPL.hilbert_alg_complete` -- no sorry, no axiom issues
- The theorems retain their existing type signatures (only proofs change)

---

### Phase 3: Downstream Verification [COMPLETED]

**Goal**: Ensure all downstream files still compile after the HilbertCompleteness.lean changes (especially import changes).

**Tasks**:
- [ ] Build Conservative.lean: `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative`
  - This imports Completeness.lean (unchanged) so should be unaffected
- [ ] Build Glivenko.lean: `lake build Cslib.Logics.Propositional.Semantics.Algebra.Glivenko`
  - This imports Completeness.lean (unchanged) so should be unaffected
- [ ] If any downstream file imported HilbertCompleteness.lean transitively for ND-related lemmas (like `ipl_subset_axiomTheory_int`), fix the import chain
- [ ] Run `lake exe checkInitImports` to verify import integrity
- [ ] Run `lake exe lint-style` for style compliance

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- Potentially fix imports in downstream files if they transitively depended on removed imports from HilbertCompleteness.lean

**Verification**:
- All modules in `Cslib/Logics/Propositional/Semantics/Algebra/` build
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

---

### Phase 4: Full CI Verification [COMPLETED]

**Goal**: Run the complete CI pipeline to confirm no regressions anywhere in the project.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` to verify import minimality
- [ ] Confirm no new sorry or axiom usage via `lean_verify` on key theorems

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- None expected (fix any issues discovered)

**Verification**:
- All CI checks pass
- No new sorry or axiom usage
- Import graph is clean

## Testing & Validation

- [ ] `hilbertLindenbaumMk_eq_top_iff` correctly characterizes top as derivability
- [ ] `Hilbert.canonicalV_spec` truth lemma covers all five proposition constructors
- [ ] `MPL.hilbert_alg_complete` type signature unchanged, proof uses Hilbert Lindenbaum directly
- [ ] `IPL.hilbert_alg_complete` type signature unchanged, proof uses Hilbert Lindenbaum directly
- [ ] `CPL.hilbert_alg_complete` type signature unchanged, proof uses Hilbert Lindenbaum directly
- [ ] Conservative.lean and Glivenko.lean build unchanged
- [ ] Full `lake build` succeeds
- [ ] `lake test` passes
- [ ] No sorry or vacuous definitions introduced

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- extended with foundation lemmas
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` -- rewritten completeness proofs
- `specs/283_hilbert_primary_algebraic_completeness/plans/01_hilbert-completeness-plan.md` -- this plan

## Rollback/Contingency

If the Hilbert Lindenbaum-based completeness proofs encounter unforeseen difficulties:
1. The old HilbertCompleteness.lean (routing through ND) is preserved in git history
2. `git checkout HEAD -- Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` restores the ND-routed version
3. New additions to HilbertLindenbaum.lean (Phase 1) are purely additive and can be kept regardless
4. Completeness.lean is never modified, so no rollback needed there
