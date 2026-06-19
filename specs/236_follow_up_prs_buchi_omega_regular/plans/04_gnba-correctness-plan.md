# Implementation Plan: Task #236 -- GNBA Correctness Proof (v04)

- **Task**: 236 - Complete follow-up PRs from PR #649 for Büchi automata and closure of omega-regular languages under boolean operations
- **Status**: [IMPLEMENTING]
- **Effort**: 20 hours
- **Dependencies**: None (Phases 1-3 from plan v03 complete; GNBA.lean exists with closure, atoms, transitions, and NBA conversion)
- **Research Inputs**: specs/236_follow_up_prs_buchi_omega_regular/reports/04_gnba-correctness-research.md
- **Artifacts**: plans/04_gnba-correctness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan completes the GNBA correctness proof (`gnba_language_eq`) by fixing a critical bug in the `gnbaNBA` cycling counter definition and proving both directions of the language equality theorem (Baier-Katoen Theorem 5.39). The research report (`04_gnba-correctness-research.md`) identified that the current `gnbaNBA` unconditionally advances the cycling counter, making every run Büchi-accepting. The standard degeneralization (Baier-Katoen Lemma 4.56) conditionally advances the counter only when the current acceptance set is satisfied.

After fixing the definition, the proof decomposes into:
- **Completeness**: satisfaction → NBA accepting run (via canonical atoms and counter cycling)
- **Soundness**: NBA accepting run → satisfaction (via structural induction on formulas)

Filling the sorry in `gnba_language_eq` transitively removes the `sorryAx` from `Formula.isRegular_untl` and `Formula.isRegular` in `OmegaRegular.lean` (Phase 5 wiring is already in place).

### Research Integration

Report `04_gnba-correctness-research.md` provides:
- Identification of the gnbaNBA cycling counter bug (unconditional vs conditional advance)
- Complete proof decomposition: 9 lemmas across completeness and soundness directions
- CSLib-specific implementation details: `Run`/`OmegaExecution` structure, `∃ᶠ` API, `ωLanguage.mem_ext` pattern
- The imp case in soundness requires the reverse direction (`ψ ∉ B_i → ¬Satisfies v i ψ`) which is obtained from propositional consistency + forward direction on `imp ψ bot`
- The Until case in soundness uses `Nat.find` to obtain the minimum acceptance-visiting position and eliminates the `untl ∉ B_j` sub-case by contradiction via the expansion transition rule

### Current State

From plan v03:
- **Phases 1-3**: COMPLETED — GNBA.lean (799 lines) contains closure, atoms, canonical atoms, GNBA construction, NBA conversion
- **Phase 4**: PARTIAL — `gnba_language_eq` has sorry at line 795; gnbaNBA definition has a bug
- **Phase 5**: COMPLETED structurally — `isRegular_untl` and `isRegular` in OmegaRegular.lean are wired through `gnba_language_eq` and `isRegular'`, but `sorryAx` propagates from the sorry

## Goals & Non-Goals

**Goals**:
- Fix the `gnbaNBA` cycling counter to use conditional advancement (Baier-Katoen Lemma 4.56)
- Prove `gnba_language_eq : language (gnbaNBA φ) = gnbaOmegaLanguage φ` with zero sorry
- Transitively eliminate `sorryAx` from `Formula.isRegular_untl` and `Formula.isRegular`

**Non-Goals**:
- Modifying Phases 1-3 definitions (closure, atoms, transitions — these are correct)
- Modifying Phase 5 wiring (OmegaRegular.lean — already correct modulo gnba_language_eq)
- Factoring degeneralization into a reusable general GNBA→NBA lemma (inline proof is acceptable)
- Proving the biconditional `ψ ∈ B_i ↔ Satisfies v i ψ` (forward direction S1 suffices for soundness)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fixing gnbaNBA definition breaks downstream `isRegular'`/`isRegular_untl` | M | L | Only downstream use is `gnba_language_eq` (currently sorry); `isRegular'` references `gnbaNBA` and `gnba_language_eq` — definition change is transparent through the language equality |
| Counter cycling proof (Phase 2 C4) is technically involved | M | M | Split into counter_progress lemma (single advancement) + iteration; use `Nat.find` for well-definedness |
| Soundness imp case requires reverse direction across closure cases | H | M | Use `mem_closure_cases` to split `ψ₁` into 3 forms (subformula, `imp χ bot`, `next (untl χ₁ χ₂)`); each handled by propConsistent/IH |
| Soundness Until case needs minimum witness via well-ordering | M | L | Standard Mathlib pattern with `Nat.find`; existence from `frequently_atTop.mp` |
| Total proof size (~400 lines) exceeds single-phase scope | H | M | Decomposed into 3 focused phases of 100-200 lines each |
| `Fin` arithmetic for counter cycling introduces edge cases | M | M | Handle k=0 case separately (trivial — all states accepting); k>0 uses `Nat.mod_lt` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Fix gnbaNBA and Prove Completeness [NOT STARTED]

**Goal**: Fix the cycling counter in `gnbaNBA` to use conditional advancement, then prove the completeness direction: `gnbaOmegaLanguage φ ⊆ language (gnbaNBA φ)`.

**Tasks**:

- [ ] **Fix `Formula.gnbaNBA`** (GNBA.lean:656-663): Replace unconditional counter advance with conditional advance based on acceptance set membership. The corrected transition:
  ```
  gnbaTr φ B a B' ∧
  if gnbaK φ = 0 then j.val = 0
  else
    let idx : Fin (gnbaK φ) := ⟨i.val % gnbaK φ, ...⟩
    let χ := (untlFinset φ)[idx]
    if B ∈ gnbaAcceptSet φ χ then j.val = (i.val + 1) % gnbaK φ
    else j = i
  ```
  State type remains `GNBANBAState φ = GNBAState φ × Fin (gnbaK φ).succ`.
  Start states remain `{ s | s.1 ∈ gnbaStart φ ∧ s.2 = ⟨0, ...⟩ }`.
  Acceptance remains `{ s | s.2 = ⟨0, ...⟩ }`.

- [ ] **Prove `canonicalAtom_mem_start`**: Given `Satisfies v 0 φ`, the canonical atom at position 0 is a start state.
  ```lean
  lemma canonicalAtom_mem_start (v : ℕ → (Atom → Prop)) (φ : Formula Atom)
      (hsat : Satisfies v 0 φ) :
      ⟨canonicalAtom v 0 φ, canonicalAtom_isAtom v 0 φ⟩ ∈ gnbaStart φ
  ```
  Proof: `canonicalAtom_mem_iff.mpr ⟨self_mem_closure φ, hsat⟩`. Trivial.

- [ ] **Prove `canonicalAtom_gnba_acceptance`**: The canonical GNBA run visits each acceptance set infinitely often.
  ```lean
  lemma canonicalAtom_gnba_acceptance (v : ℕ → (Atom → Prop)) (φ : Formula Atom)
      (χ : Formula Atom) (hχ : χ ∈ untlSubformulas φ) :
      ∀ N, ∃ k ≥ N, ⟨canonicalAtom v k φ, canonicalAtom_isAtom v k φ⟩ ∈ gnbaAcceptSet φ χ
  ```
  Proof by contradiction: Assume from some N onwards, `χ ∈ (canonicalAtom v k φ)` and `ψ₂ ∉ (canonicalAtom v k φ)`. From `χ ∈ canonicalAtom` unpack `Satisfies v N (untl ψ₁ ψ₂)` to get `∃ j ≥ N, Satisfies v j ψ₂`, giving `ψ₂ ∈ canonicalAtom v j φ` — contradiction.

- [ ] **Define the canonical counter sequence** `canonicalCtr`: Recursively define the cycling counter for the canonical GNBA run.
  ```lean
  noncomputable def canonicalCtr (v : ℕ → (Atom → Prop)) (φ : Formula Atom) : ℕ → Fin (gnbaK φ).succ
  ```
  `canonicalCtr v φ 0 := ⟨0, ...⟩`
  `canonicalCtr v φ (n+1) := if gnbaK φ = 0 then ⟨0, ...⟩ else <conditional advance>`

- [ ] **Prove `canonicalCtr_transitions`**: The NBA transitions hold for the canonical run paired with the counter sequence.

- [ ] **Prove `canonicalCtr_frequently_zero`**: The counter returns to 0 infinitely often.
  ```lean
  lemma canonicalCtr_frequently_zero (v : ℕ → (Atom → Prop)) (φ : Formula Atom)
      (hsat : Satisfies v 0 φ) :
      ∀ N, ∃ k ≥ N, (canonicalCtr v φ k).val = 0
  ```
  When `gnbaK φ = 0`: trivial, counter always 0.
  When `gnbaK φ > 0`: prove counter progress lemma (counter at j eventually reaches (j+1) mod K because acceptance set F_j is visited infinitely often). Iterate from counter=0 through 0,1,...,K-1,0 to show counter returns to 0.

- [ ] **Prove `gnba_completeness`**: Combine start state, transitions, and acceptance.
  ```lean
  lemma gnba_completeness (φ : Formula Atom) (v : ωSequence (Set Atom))
      (hsat : Satisfies (fun n p => p ∈ v n) 0 φ) :
      v ∈ ωAcceptor.language (gnbaNBA φ)
  ```
  Construct `ss : ℕ → GNBANBAState φ` as `fun i => (canonicalGNBA i, canonicalCtr i)`. Prove `NA.Run` (start + OmegaExecution) and `∃ᶠ k in atTop, ss k ∈ accept` (from `canonicalCtr_frequently_zero`).

- [ ] Verify: `lake build Cslib.Logics.LTL.Semantics.GNBA`

**Timing**: 8 hours

**Depends on**: none (within this plan)

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` — fix gnbaNBA definition, add completeness lemmas

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors
- `gnba_completeness` has no sorry
- `gnbaNBA` definition uses conditional counter advance

---

### Phase 2: Prove Soundness [NOT STARTED]

**Goal**: Prove the soundness direction: `language (gnbaNBA φ) ⊆ gnbaOmegaLanguage φ`. Given an accepting NBA run, show the input satisfies the formula.

**Tasks**:

- [ ] **Prove `degeneralization_forward`**: NBA Büchi acceptance (counter=0 infinitely often) implies all GNBA acceptance sets are visited infinitely often.
  ```lean
  lemma degeneralization_forward (φ : Formula Atom) (B : ℕ → GNBAState φ)
      (ctr : ℕ → Fin (gnbaK φ).succ) (v : ωSequence (Set Atom))
      (htrans : ∀ i, gnbaTr φ (B i) (v i) (B (i+1)))
      (hctr : <counter follows conditional advance rule>)
      (hacc : ∀ N, ∃ k ≥ N, (ctr k).val = 0)
      (χ : Formula Atom) (hχ : χ ∈ untlSubformulas φ) :
      ∀ N, ∃ k ≥ N, (B k) ∈ gnbaAcceptSet φ χ
  ```
  Proof: Between consecutive counter-0 times, the counter passes through each value 0..K-1. Each time the counter advances from j to j+1, the GNBA state satisfies F_j (by the conditional advance rule). Since counter=0 occurs infinitely often, every F_j is visited infinitely often.

- [ ] **Prove `gnba_soundness_key`**: The core structural induction lemma.
  ```lean
  lemma gnba_soundness_key (φ : Formula Atom) (B : ℕ → GNBAState φ)
      (v : ωSequence (Set Atom))
      (htrans : ∀ i, gnbaTr φ (B i) (v i) (B (i+1)))
      (hgnba_acc : ∀ χ ∈ untlSubformulas φ, ∀ N, ∃ k ≥ N, (B k) ∈ gnbaAcceptSet φ χ)
      (ψ : Formula Atom) (hψ : ψ ∈ closure φ) (i : ℕ) :
      ψ ∈ (B i).val → Satisfies (fun n p => p ∈ v n) i ψ
  ```
  Proof by structural induction on ψ (IH available for all i):

  **Case `atom p`**: Letter consistency (from `htrans` at step i): `atom p ∈ (B i).val ↔ p ∈ v i`. So `p ∈ v i` = `Satisfies v i (atom p)`.

  **Case `bot`**: By `(B i).property.botConsistent`, `bot ∉ (B i).val`. Contradiction — vacuously true.

  **Case `imp ψ₁ ψ₂`**: By `(B i).property.impClosure`: `imp ψ₁ ψ₂ ∈ (B i).val ↔ (ψ₁ ∉ (B i).val ∨ ψ₂ ∈ (B i).val)`.
  - If `ψ₂ ∈ (B i).val`: IH gives `Satisfies v i ψ₂`, implication holds.
  - If `ψ₁ ∉ (B i).val`: Need `¬Satisfies v i ψ₁` (reverse direction). Assume `Satisfies v i ψ₁` for contradiction. Use `mem_closure_cases` on ψ₁:
    - ψ₁ ∈ subformulas: by `propConsistent`, `imp ψ₁ bot ∈ (B i).val`. By IH on `imp ψ₁ bot`: `¬Satisfies v i ψ₁`. Contradiction.
    - ψ₁ = imp χ bot: `Satisfies v i (imp χ bot)` = `¬Satisfies v i χ`. By `propConsistent` on χ: `χ ∈ (B i).val`. By IH on χ: `Satisfies v i χ`. Contradiction.
    - ψ₁ = next (untl χ₁ χ₂): By next-step consistency: `next (untl χ₁ χ₂) ∉ (B i).val → untl χ₁ χ₂ ∉ (B (i+1)).val`. By `propConsistent` on `untl χ₁ χ₂`: `imp (untl χ₁ χ₂) bot ∈ (B (i+1)).val`. By IH: `¬Satisfies v (i+1) (untl χ₁ χ₂)`. But `Satisfies v i (next (untl χ₁ χ₂))` = `Satisfies v (i+1) (untl χ₁ χ₂)`. Contradiction.

  **Case `next ψ`**: By next-step consistency: `next ψ ∈ (B i).val ↔ ψ ∈ (B (i+1)).val`. IH at i+1 gives `Satisfies v (i+1) ψ` = `Satisfies v i (next ψ)`.

  **Case `untl ψ₁ ψ₂`** (hardest case):
  1. From `hgnba_acc` on `untl ψ₁ ψ₂`: `∀ N, ∃ k ≥ N, (B k) ∈ gnbaAcceptSet φ (untl ψ₁ ψ₂)`.
  2. In particular: `∃ j ≥ i, untl ψ₁ ψ₂ ∉ (B j).val ∨ ψ₂ ∈ (B j).val`.
  3. Take the **minimum** such j using `Nat.find`.
  4. Eliminate sub-case `untl ψ₁ ψ₂ ∉ (B j).val`:
     - If j = i: contradicts hypothesis.
     - If j > i: at k = j-1, minimality gives `untl ψ₁ ψ₂ ∈ (B (j-1)).val ∧ ψ₂ ∉ (B (j-1)).val`. By Until expansion (transition at j-1): `untl ψ₁ ψ₂ ∈ (B j).val`. Contradiction.
  5. So `ψ₂ ∈ (B j).val`. IH: `Satisfies v j ψ₂`.
  6. For k with i ≤ k < j: by minimality, `untl ψ₁ ψ₂ ∈ (B k).val ∧ ψ₂ ∉ (B k).val`. By `untlLeft`: `ψ₁ ∈ (B k).val`. IH: `Satisfies v k ψ₁`.
  7. Combine: `⟨j, hij, Satisfies v j ψ₂, guard⟩`.

- [ ] **Prove `gnba_soundness`**: Combine degeneralization forward, soundness key, and start condition.
  ```lean
  lemma gnba_soundness (φ : Formula Atom) (v : ωSequence (Set Atom))
      (hacc : v ∈ ωAcceptor.language (gnbaNBA φ)) :
      Satisfies (fun n p => p ∈ v n) 0 φ
  ```
  Extract NBA run `ss`. Project GNBA states `B i := (ss i).1` and counter `ctr i := (ss i).2`. From OmegaExecution, extract GNBA transitions and counter rule. From Büchi acceptance (counter=0 frequently), derive GNBA acceptance via `degeneralization_forward`. Apply `gnba_soundness_key` at ψ=φ, i=0 with `φ ∈ (B 0).val` (from start condition).

- [ ] Verify: `lake build Cslib.Logics.LTL.Semantics.GNBA`

**Timing**: 10 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` — add soundness lemmas

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors
- `gnba_soundness` has no sorry
- `gnba_soundness_key` structural induction covers all 5 formula cases

---

### Phase 3: Combine and Verify [NOT STARTED]

**Goal**: Prove `gnba_language_eq` by combining completeness and soundness. Verify that `sorryAx` is eliminated from `Formula.isRegular`.

**Tasks**:

- [ ] **Prove `gnba_language_eq`**:
  ```lean
  theorem Formula.gnba_language_eq (φ : Formula Atom) :
      ωAcceptor.language (gnbaNBA φ) = gnbaOmegaLanguage φ := by
    ext v
    constructor
    · exact fun hacc => gnba_soundness φ v hacc
    · exact fun hsat => gnba_completeness φ v hsat
  ```

- [ ] **Verify `gnba_language_eq`**: `lean_verify` shows axioms = `[propext, Classical.choice, Quot.sound]` with NO `sorryAx`.

- [ ] **Verify `isRegular_untl`**: `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular_untl` shows NO `sorryAx`.

- [ ] **Verify `isRegular`**: `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular` shows NO `sorryAx`.

- [ ] **Run full CI pipeline**:
  - `lake build` (full project)
  - `lake test`
  - `lake exe checkInitImports`
  - `lake exe lint-style`

- [ ] **Verify no sorry remains**: `grep -n sorry Cslib/Logics/LTL/Semantics/GNBA.lean` returns zero hits.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` — replace sorry in gnba_language_eq with proof

**Verification**:
- `lean_verify` on `gnba_language_eq`: no `sorryAx`
- `lean_verify` on `isRegular_untl`: no `sorryAx`
- `lean_verify` on `isRegular`: no `sorryAx`
- Full CI pipeline passes
- Zero `sorry` in GNBA.lean and OmegaRegular.lean

## Testing & Validation

- [ ] `lake build Cslib.Logics.LTL.Semantics.GNBA` succeeds after each phase
- [ ] `lake build` (full project) succeeds after Phase 3
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lean_verify` confirms no `sorryAx` in `Formula.isRegular`, `Formula.isRegular_untl`, `Formula.gnba_language_eq`
- [ ] All existing per-constructor lemmas (`isRegular_atom`, `isRegular_bot`, `isRegular_imp`, `isRegular_next`) remain intact
- [ ] `omegaLanguage_untl` semantic equation preserved

## Artifacts & Outputs

- `Cslib/Logics/LTL/Semantics/GNBA.lean` (modified) — fixed gnbaNBA definition + correctness proof
- `specs/236_follow_up_prs_buchi_omega_regular/plans/04_gnba-correctness-plan.md` (this file)

## Rollback/Contingency

- **Phase 1 (fix + completeness)**: If the corrected gnbaNBA definition causes unforeseen type issues with `Fin` arithmetic, simplify by using a `Nat`-valued counter with manual bounds proofs instead of `Fin`. If the counter cycling proof is too involved, prove it for the special case `gnbaK φ ≤ 1` first (covers formulas with at most one Until subformula).
- **Phase 2 (soundness)**: The imp case is the trickiest due to the reverse direction. If `mem_closure_cases` splitting creates too many sub-goals, factor the reverse direction into a separate lemma `gnba_soundness_reverse : ψ ∈ subformulas φ → ψ ∉ (B i).val → ¬Satisfies v i ψ` proved via propConsistent + forward direction on `imp ψ bot`. If the Until case's `Nat.find` approach is problematic, use strong induction on the distance to the next acceptance visit instead.
- **Phase 3 (combine)**: This is mechanical once Phases 1-2 succeed. No contingency needed.
- **Overall fallback**: The existing `isRegular` proof with sorry is preserved in git history. The GNBA infrastructure (closure, atoms, canonical atoms, transitions) is independently valuable regardless.
