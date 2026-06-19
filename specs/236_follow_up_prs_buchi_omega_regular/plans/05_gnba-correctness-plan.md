# Implementation Plan: Task #236 -- GNBA Correctness (gnba_language_eq)

- **Task**: 236 - Complete follow-up PRs from PR #649 for Buchi automata and closure of omega-regular languages under boolean operations
- **Status**: [IN PROGRESS]
- **Effort**: 18 hours
- **Dependencies**: None (Phases 1-3 and 5 from plan v03 are complete; GNBA.lean has closure, atoms, canonical atoms, GNBA construction, and integration scaffolding in place; only `gnba_language_eq` at line 795 remains as sorry)
- **Research Inputs**: specs/236_follow_up_prs_buchi_omega_regular/reports/03_gnba-tableau-research.md, specs/236_follow_up_prs_buchi_omega_regular/reports/04_gnba-correctness-research.md
- **Artifacts**: plans/05_gnba-correctness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan addresses the remaining sorry in `Formula.gnba_language_eq` (GNBA.lean:795), which is the sole blocker for a sorry-free `Formula.isRegular`. The prior plan (v03) completed Phases 1-3 (closure, canonical atoms, GNBA construction) and Phase 5 (integration scaffolding), leaving Phase 4 (correctness proof) as [PARTIAL] with sorry.

Research report 04 identified a critical bug in the `gnbaNBA` definition: the cycling counter advances unconditionally (`i+1 = j ∨ (j=0 ∧ i=gnbaK)`) instead of conditionally on acceptance set membership, per Baier-Katoen Lemma 4.56. With unconditional advance, every infinite run visits counter=0 infinitely often, making all runs Buchi-accepting regardless of GNBA acceptance sets. This must be fixed before the correctness proof can proceed.

The correctness proof decomposes into two directions: completeness (satisfaction implies NBA acceptance via canonical run + counter cycling) and soundness (NBA acceptance implies satisfaction via structural induction + degeneralization forward).

### Research Integration

- Report `04_gnba-correctness-research.md`: Identified gnbaNBA counter bug, provided corrected definition with conditional advance, decomposed proof into completeness (C1-C5) and soundness (S0-S3) steps, estimated 340-530 lines of new proof code.

## Goals & Non-Goals

**Goals**:
- Fix `Formula.gnbaNBA` definition: replace unconditional counter advance with conditional advance based on acceptance set membership (Baier-Katoen Lemma 4.56)
- Prove completeness: `gnbaOmegaLanguage phi <= language (gnbaNBA phi)` -- construct accepting NBA run from satisfying valuation using canonical atoms
- Prove soundness: `language (gnbaNBA phi) <= gnbaOmegaLanguage phi` -- extract satisfaction from accepting NBA run via structural induction
- Remove the sorry from `Formula.gnba_language_eq` (GNBA.lean:795)
- Verify that `Formula.isRegular` in OmegaRegular.lean becomes sorry-free transitively

**Non-Goals**:
- Modifying any completed infrastructure (closure, atoms, canonical atoms, GNBA transition relation, acceptance sets)
- Optimizing the GNBA state space or counter representation
- Adding new constructors or cases to `Formula.isRegular`
- McNaughton's theorem or deterministic Buchi automata

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fixing gnbaNBA counter definition breaks downstream code (isRegular', isRegular_untl) | M | L | The only downstream use is gnba_language_eq which already has sorry; the fix makes it provable. isRegular' and isRegular_untl reference gnbaNBA only through gnba_language_eq. |
| Counter cycling proof (completeness C4-C5) is technically involved with Nat.find and iterated induction | M | M | Split into small lemmas: counter progress lemma (single step) + iteration. Use frequently_atTop characterization. |
| Soundness imp case requires careful handling of closure vs subformula distinction | H | M | Research report provides exact case analysis via mem_closure_cases into three sub-cases (subformula, imp chi bot, next untl). Each handled by existing atom properties. |
| Soundness Until case needs Nat.find for minimum witness | M | L | Well-established Mathlib pattern; research report outlines exact proof steps. |
| Total proof size (~400+ lines) may exceed single-phase scope | H | M | Decomposed into 3 phases of ~120-200 lines each; each phase independently verifiable. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Fix gnbaNBA Counter + Completeness Direction [NOT STARTED]

**Goal**: Fix the gnbaNBA cycling counter to use conditional advancement per Baier-Katoen Lemma 4.56, then prove the completeness direction of gnba_language_eq: satisfaction implies NBA acceptance.

**Tasks**:
- [ ] Fix `Formula.gnbaNBA` definition (GNBA.lean:656-663): replace unconditional counter advance `(i.val + 1 = j.val ∨ (j = 0 ∧ i.val = gnbaK))` with conditional advance: if current state is in the acceptance set indexed by counter mod gnbaK, advance counter by 1 mod gnbaK; otherwise counter stays. When gnbaK = 0, counter stays at 0.
- [ ] Prove `canonicalAtom_mem_start`: `canonicalAtom v 0 phi` is a start state when `Satisfies v 0 phi` (~5 lines)
- [ ] Prove `canonicalAtom_gnba_acceptance`: for each Until subformula `chi` in closure, the canonical run visits `gnbaAcceptSet phi chi` infinitely often. Proof by contradiction: if not frequently, then eventually always `chi in B_i` and `psi2 not-in B_i`, but Until semantics gives a witness `j` with `psi2 in B_j`, contradiction. (~40-60 lines)
- [ ] Define `gnbaCanonicalCounter`: the counter sequence for the canonical run, defined recursively with conditional advance based on acceptance set membership (~15-25 lines)
- [ ] Prove counter progress: if counter = j at time n, then there exists m > n with counter = (j+1) mod K, using the fact that acceptance set F_j is visited infinitely often (~30-50 lines)
- [ ] Prove counter returns to 0 infinitely often by iterating the progress lemma through all K acceptance sets (~20-40 lines)
- [ ] Prove `gnba_completeness : gnbaOmegaLanguage phi <= language (gnbaNBA phi)` by combining canonical run, transitions (existing `canonicalAtom_gnbaTr`), start state, and counter cycling acceptance (~30-50 lines)
- [ ] Verify: `lake build Cslib.Logics.LTL.Semantics.GNBA`

**Timing**: 8 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` -- fix gnbaNBA definition, add completeness lemmas and proof

**Verification**:
- `lean_verify` on `gnba_completeness` shows no sorry
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors

---

### Phase 2: Soundness Direction [NOT STARTED]

**Goal**: Prove the soundness direction of gnba_language_eq: NBA acceptance implies satisfaction. This is the harder direction, requiring structural induction on formula constructors with careful handling of the Until and imp cases.

**Tasks**:
- [ ] Prove `degeneralization_forward`: NBA Buchi acceptance (counter = 0 infinitely often) implies every GNBA acceptance set is visited infinitely often. Between consecutive counter-0 visits, the counter passes through all values 0..K-1, advancing only when the current acceptance set is satisfied. (~40-60 lines)
- [ ] Prove `gnba_soundness_key`: for all `psi in closure phi` and all `i`, `psi in B_i.val -> Satisfies v i psi`, by structural induction on `psi`:
  - atom case: letter consistency from gnbaTr (~5 lines)
  - bot case: vacuous by botConsistent (~3 lines)
  - imp case: use impClosure + propConsistent with mem_closure_cases for the reverse direction when psi1 not-in B_i (~30-40 lines, the second-hardest case)
  - next case: next-step consistency from gnbaTr + IH at i+1 (~5 lines)
  - untl case: use GNBA acceptance (from degeneralization_forward) to find minimum j >= i with psi2 in B_j, show psi1 in B_k for i <= k < j by untlLeft + minimality, apply IH (~40-60 lines, the hardest case)
  Total: ~100-150 lines
- [ ] Prove `gnba_soundness : language (gnbaNBA phi) <= gnbaOmegaLanguage phi` by extracting the GNBA run from the NBA run, applying degeneralization_forward for GNBA acceptance, then gnba_soundness_key at psi = phi, i = 0, using start condition phi in B_0 (~20-30 lines)
- [ ] Verify: `lake build Cslib.Logics.LTL.Semantics.GNBA`

**Timing**: 8 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` -- add soundness lemmas and proof

**Verification**:
- `lean_verify` on `gnba_soundness` shows no sorry
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors

---

### Phase 3: Language Equality and Final Verification [NOT STARTED]

**Goal**: Combine completeness and soundness to prove `gnba_language_eq`, remove the sorry, and verify that `Formula.isRegular` is transitively sorry-free.

**Tasks**:
- [ ] Replace the sorry in `gnba_language_eq` (GNBA.lean:795) with the proof combining completeness and soundness: `ext v; exact ⟨gnba_soundness phi v, gnba_completeness phi v⟩` (or equivalent Set.ext formulation) (~5-10 lines)
- [ ] Run `lean_verify` on `Cslib.Logic.LTL.Formula.gnba_language_eq` to confirm no sorry/sorryAx
- [ ] Run `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular` to confirm transitively sorry-free
- [ ] Run `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular_untl` to confirm sorry-free
- [ ] Run full CI pipeline:
  - `lake build` (full project)
  - `lake test`
  - `lake exe checkInitImports`
  - `lake exe lint-style`
- [ ] Verify no `proof_wanted` or `sorry` remains in GNBA.lean or OmegaRegular.lean

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` -- replace sorry with proof in gnba_language_eq

**Verification**:
- `lean_verify` on `Cslib.Logic.LTL.Formula.gnba_language_eq` passes (no sorry, no sorryAx)
- `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular` passes (all five cases sorry-free)
- Full CI pipeline passes: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`

## Testing & Validation

- [ ] `lake build Cslib.Logics.LTL.Semantics.GNBA` succeeds after each phase
- [ ] `lake build` (full project) succeeds after Phase 3
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lean_verify` confirms no sorry in `Formula.isRegular`, `Formula.isRegular_untl`, `Formula.gnba_language_eq`, `gnba_completeness`, and `gnba_soundness`
- [ ] All existing per-constructor lemmas (`isRegular_atom`, `isRegular_bot`, `isRegular_imp`, `isRegular_next`) remain intact
- [ ] Existing canonical atom and GNBA transition infrastructure unchanged (canonicalAtom_isAtom, canonicalAtom_gnbaTr, etc.)

## Artifacts & Outputs

- `Cslib/Logics/LTL/Semantics/GNBA.lean` (modified) -- fixed gnbaNBA definition, completeness + soundness proofs, sorry removed from gnba_language_eq
- `specs/236_follow_up_prs_buchi_omega_regular/plans/05_gnba-correctness-plan.md` (this file)

## Rollback/Contingency

- **Phase 1 (gnbaNBA fix)**: If the corrected conditional counter definition causes unexpected type issues, an alternative is to define a wrapper function `gnbaCounterAdvance` separately and reference it in the Tr field, keeping the logic modular.
- **Phase 1 (completeness)**: The completeness direction is the easier of the two. If counter cycling is too complex, the canonical run construction (start + transitions) can be proved first, leaving counter acceptance as sorry, providing incremental progress.
- **Phase 2 (soundness)**: This is the highest-risk phase. If the full structural induction is too large:
  - Complete the atom/bot/next cases first (straightforward, ~15 lines each)
  - Tackle the imp case next (moderate, needs mem_closure_cases analysis)
  - Leave the untl case with sorry as a documented gap if needed -- it is the single hardest case
  - The untl case can be decomposed further: find minimum witness (Nat.find), show psi1 holds along path (untlLeft), apply IH
- **Phase 3**: If Phases 1-2 succeed, this phase is mechanical. If they don't fully complete, keep the sorry in gnba_language_eq with partial progress documented.
- **Overall fallback**: All existing infrastructure (closure, atoms, canonical atoms, GNBA construction, isRegular' scaffolding, per-constructor proofs) is preserved regardless. The gnbaNBA fix is independently valuable even if the full correctness proof is not completed.
