# Research Report: Refactor CutElimination.lean Heartbeats

## Task 328 | Session: sess_1782300531_c471d6_328

## 1. File Structure Analysis

**File**: `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` (911 lines)

### Declaration Map

| Declaration | Lines | Size | Location |
|-------------|-------|------|----------|
| `CutFree.mono` | 48-82 | 34 | Pre-mutual |
| `CutFreeLKProof.mono` | 85-89 | 4 | Pre-mutual |
| `CutIH` (abbrev) | 96-102 | 6 | Pre-mutual |
| `mem_of_ne_head` | 106-109 | 3 | Pre-mutual |
| `cutAdm_right_andR` | 118-266 | 148 | Mutual block |
| `cutAdm_right_orR` | 269-410 | 141 | Mutual block |
| `cutAdm_right_impR` | 413-553 | 140 | Mutual block |
| `cutAdm_right` | 556-692 | 136 | Mutual block |
| `cutAdm_left` | 697-852 | 155 | Mutual block |
| `cutAdmissibility` | 860-869 | 9 | Post-mutual |
| `LKProof.cutElim` | 874-910 | 36 | Post-mutual |

Total mutual block: 739 lines (lines 114-853), under `set_option maxHeartbeats 800000`.

### Public API (Must Remain Unchanged)

- `cutAdmissibility` -- cut admissibility by well-founded recursion on `sizeOf C`
- `LKProof.cutElim` -- Gentzen's Hauptsatz, structural induction
- `CutFreeLKProof.mono` -- weakening for cut-free proofs

No external file imports `CutElimination.lean` (the import in `LK.lean` is commented out).
No external reference exists to any internal helper (`cutAdm_right_*`, `cutAdm_left`,
`cutAdm_right`, `mem_of_ne_head`, `CutIH`).

## 2. Mutual Recursion Dependency Analysis

### Call Graph

```
cutAdm_right_andR  --> cutAdm_right_andR  (self only)
cutAdm_right_orR   --> cutAdm_right_orR   (self only)
cutAdm_right_impR  --> cutAdm_right_impR  (self only)
cutAdm_right       --> cutAdm_left        (mutual)
cutAdm_left        --> cutAdm_left        (self)
                   --> cutAdm_right_andR  (one-way)
                   --> cutAdm_right_orR   (one-way)
                   --> cutAdm_right_impR  (one-way)
```

**Key finding**: The three `cutAdm_right_*` helpers are purely self-recursive. They are
called by `cutAdm_left` but never call `cutAdm_left` or `cutAdm_right`. The only true
mutual recursion is between `cutAdm_right` and `cutAdm_left`.

### Implication for File Splitting

The three `cutAdm_right_*` helpers (435 lines total) can be extracted from the mutual block
and defined as standalone recursive definitions. Lean 4 allows mutual block members to call
functions defined before the block. This alone should provide a significant heartbeat
reduction because the elaborator's mutual recursion checker processes fewer simultaneous
definitions.

The remaining mutual block would contain only `cutAdm_right` and `cutAdm_left` (296 lines),
which is 60% smaller than the current 739-line block.

## 3. Elaboration Cost Drivers

### 3.1 Repeated Finset Subset Proof Patterns

The file contains massive repetition of Finset subset proof terms. Quantitative analysis:

| Pattern | Occurrences | Description |
|---------|-------------|-------------|
| `Finset.insert_subset_insert` | 113 | Insert-preserves-subset |
| `Finset.subset_insert` | 107 | Weakening to insert |
| `Finset.insert_subset` (constructor) | 156 | Building insert-subset proofs |
| `Finset.mem_insert` variants | 59 | Membership in insert |
| `Finset.Subset.refl _` | 83 | Identity subset |
| `mem_of_ne_head` | 25 | Custom helper for membership |
| `fun x hx => hsuc hx` (eta-reducible) | 44 | Lambda wrapping subset hypotheses |

Each case in each `cutAdm_right_*` helper constructs 3-8 line subset proof terms inline.
These terms are structurally identical across functions, differing only in the cut formula.

### 3.2 The "Push Through Cut Formula" Pattern

The most common multi-line pattern (35 occurrences) is:

```lean
let hant' : insert A' Γ ⊆ insert C (insert A' Γ₀) :=
  Finset.insert_subset
    (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
    (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
```

This proves `insert a s ⊆ insert c (insert a t)` given `s ⊆ insert c t`. A single helper
lemma would replace all 35 occurrences.

### 3.3 The "Double-Insert Weakening" Pattern

14 occurrences of:

```lean
let wk2 : Γ₀ ⊆ insert A' (insert B' Γ₀) :=
  (Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)
```

A single `Finset.subset_insert₂` lemma replaces these.

### 3.4 Eta-Reducible Lambda Wrappers

44 occurrences of `(fun x hx => hsuc hx)` which is eta-equivalent to `hsuc` itself (since
`hsuc : Δ ⊆ Δ₀` and the lambda just applies it pointwise). Similarly for `hant`. These
create unnecessary term bloat.

### 3.5 `.mono` with `Finset.Subset.refl`

83 occurrences of `Finset.Subset.refl _`, most paired with `.mono` calls where one side
doesn't change. A custom `CutFreeLKProof.monoL` / `CutFreeLKProof.monoR` helper could
eliminate these.

## 4. Proposed Refactoring Strategy

### Phase 1: Extract Finset Subset Helpers (Pre-mutual, ~20 new lines)

Define reusable helpers before the mutual block:

```lean
/-- `s ⊆ insert a (insert b s)` -/
private theorem subset_insert₂ (a b : α) (s : Finset α) :
    s ⊆ insert a (insert b s) :=
  (Finset.subset_insert b s).trans (Finset.subset_insert a _)

/-- Transport subset through an outer insert:
    `insert a s ⊆ insert c (insert a t)` from `s ⊆ insert c t`. -/
private theorem insert_subset_swap {c a : α} {s t : Finset α}
    (h : s ⊆ insert c t) : insert a s ⊆ insert c (insert a t) :=
  Finset.insert_subset
    (Finset.mem_insert_of_mem (Finset.mem_insert_self a _))
    (fun _ hx => (Finset.insert_subset_insert c (Finset.subset_insert a _)) (h hx))
```

The `insert_subset_swap` helper composes: `insert_subset_swap (insert_subset_swap h)` handles
the double-insert-through-cut-formula pattern.

These helpers have been verified to type-check via `lean_run_code`.

**Additional one-sided mono helpers**:

```lean
private def CutFreeLKProof.monoL (h : Γ ⊆ Γ') (d : CutFreeLKProof (Γ ⊢ₛ Δ)) :
    CutFreeLKProof (Γ' ⊢ₛ Δ) := d.mono h (Finset.Subset.refl _)

private def CutFreeLKProof.monoR (h : Δ ⊆ Δ') (d : CutFreeLKProof (Γ ⊢ₛ Δ)) :
    CutFreeLKProof (Γ ⊢ₛ Δ') := d.mono (Finset.Subset.refl _) h
```

### Phase 2: Extract Three Right Helpers from Mutual Block (~435 lines moved)

Move `cutAdm_right_andR`, `cutAdm_right_orR`, and `cutAdm_right_impR` out of the `mutual`
block into standalone recursive definitions, placed before the mutual block but after the
Finset helpers.

This is valid because:
1. Each helper is purely self-recursive (verified by call graph analysis)
2. Lean 4 allows mutual block members to call pre-defined functions (verified by test)
3. The structural recursion on `d₂ : LKProof` is straightforward and Lean can verify
   termination independently

The mutual block shrinks from 5 definitions (739 lines) to 2 definitions (~296 lines).

### Phase 3: Apply Helpers to Simplify Proofs (~200+ lines removed)

Replace inline subset proof constructions with helper calls:
- 35 "push through cut formula" patterns -> `insert_subset_swap h`
- 14 "double-insert weakening" patterns -> `subset_insert₂ a b s`
- 44 eta-reducible lambdas -> direct hypothesis reference
- 83 `Finset.Subset.refl` pairings -> `monoL` / `monoR`

### Phase 4: Reduce Heartbeats, Verify, and Test

After Phase 1-3, attempt:
1. Remove `set_option maxHeartbeats 800000` entirely
2. If default (200000) fails, try `400000`
3. Run full CI pipeline

### Optional: File Splitting (Phase 5)

Move the extracted `cutAdm_right_*` helpers into
`Cslib/Logics/Propositional/SequentCalculus/LK/CutAdmRight.lean`:
- This module would contain the three helpers + the Finset subset helpers
- `CutElimination.lean` imports `CutAdmRight.lean` and contains only the mutual block +
  `cutAdmissibility` + `cutElim`
- Further reduces elaboration scope per file

**Assessment**: File splitting is optional and lower priority than phases 1-4. The heartbeat
reduction from extracting the helpers from the mutual block and using shared Finset helpers
should be sufficient to reach the target.

## 5. Feasibility Assessment

### Heartbeat Reduction Estimate

| Optimization | Estimated Impact | Confidence |
|-------------|-----------------|------------|
| Extract 3 helpers from mutual block | 40-50% reduction | High |
| Shared Finset subset helpers | 15-25% reduction | Medium-High |
| Eta-reduce lambda wrappers | 5-10% reduction | Medium |
| monoL/monoR helpers | 5-10% reduction | Medium |
| **Combined** | **60-80% reduction** | **Medium** |

Current: 800000 heartbeats. Target: 200000-400000.
With 60-80% reduction: 160000-320000 heartbeats.

**Reaching 400000 is highly feasible**. Reaching 200000 (default) is likely achievable but
may require the optional file split.

### Risk Factors

1. **Mutual block extraction**: Low risk. The three helpers are demonstrably self-recursive.
   Lean's termination checker should handle them independently.

2. **Finset helper approach**: Very low risk. All helpers have been verified via `lean_run_code`.
   The transformations are mechanical.

3. **API preservation**: No risk. No external code references any internal helper. The public
   API (`cutAdmissibility`, `LKProof.cutElim`, `CutFreeLKProof.mono`) is unchanged.

4. **File splitting risk**: Low-medium risk. Creating a new module requires adding it to
   `Cslib.lean` and running `lake exe mk_all`. Import hygiene must be verified.

### Blockers

None identified. Task 327 (dependency) is completed. No other task modifies this file.

## 6. Recommendations

1. **Start with Phase 2** (extract from mutual block) -- this gives the largest heartbeat
   reduction for the least code change effort.
2. **Then Phase 1 + 3** (helpers + simplification) -- reduces code size and further cuts
   heartbeats.
3. **Measure heartbeats** after Phase 2+3 before deciding on file splitting.
4. **Remove the `Tableau.Defs` import** -- it is unused in this file and no downstream file
   imports CutElimination.lean.
5. **Replace `(fun x hx => hsuc hx)` with `hsuc`** throughout -- these are eta-expandable
   but the eta-reduced form is cleaner and generates less elaboration work.

## 7. Tactic Survey Results

| Tactic | Applicability | Notes |
|--------|---------------|-------|
| `gcongr` | Not applicable | Does not work on `Finset.insert_subset` goals |
| `simp` + `Finset.insert_subset_iff` | Partially works | Requires manual `rcases` after |
| `tauto` | Does not close goals | Needs `Finset.mem_insert` unfolded first |
| Term-mode helpers | Best approach | Predictable heartbeat cost, composable |

**Recommendation**: Use term-mode helpers (Phase 1) rather than tactic-based approaches.
Tactics introduce unpredictable elaboration overhead in large mutual blocks.
