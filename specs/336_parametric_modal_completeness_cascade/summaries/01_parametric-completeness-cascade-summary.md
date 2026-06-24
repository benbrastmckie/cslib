# Implementation Summary: Task #336 - Parametric Modal Completeness Cascade

- **Task**: 336 - Parametric modal completeness cascade
- **Status**: [COMPLETED]
- **Type**: cslib
- **Completed**: 2026-06-24

## What Was Done

Added a parametric completeness cascade to `Metalogic/Completeness.lean` and refactored all 15
`Systems/*/Completeness.lean` files to thin instantiations, delegating to the shared
parametric core.

### Parametric Core (`Metalogic/Completeness.lean`)

Added 5 parametric theorems:
- `strong_soundness`: Generic over `Axioms`, `FC`, and a soundness callback `h_sound`.
- `strong_completeness`: Generic over `Axioms`, `FC`, axiom callbacks, `truthLemma`,
  and `canonical_FC`.
- `strong_completeness_iff`: Biconditional combining both.
- `compactness`: Generic compactness via strong completeness + strong soundness.
- Helper wrappers inheriting from the above.

Also added `dFC` (serial), `d5FC` (serial ∧ eucl), `d45FC` (serial ∧ trans ∧ eucl),
`dbFC` (serial ∧ symm), `d4FC` (serial ∧ trans) frame condition definitions.

### Per-System Refactoring (15 Systems)

Each system's cascade tail replaced with thin delegations:

| Family | Systems | Truth Lemma |
|--------|---------|-------------|
| K-family (no extra modal axioms) | K | `k_truth_lemma` |
| K-family (extra axioms) | K4, K5, K45, KB5, B | `k_truth_lemma` |
| T-family | T, S4, S5, TB | `truth_lemma` |
| D-family | D, D4, D5, D45, DB | `d_truth_lemma` |

Each system defines:
1. `<sys>FC` — frame condition predicate
2. `<sys>_canonical_FC` — proof the canonical model satisfies the FC
3. `<sys>_truth_lemma_applied` (or pre-applied truth lemma) — satisfaction iff membership
4. `<sys>_sound_cb` — soundness adapter threading `<sys>_soundness` via FC destructuring
5. Thin cascade delegations for all 5 theorems

### D-Family Specific Notes

The D-family uses `d_truth_lemma` (which requires the axiom D hypothesis) instead of
`k_truth_lemma` (which uses `T`). The D-family canonical FC proofs handle `Relation.Serial`
(a typeclass, not `∀`) using nested `constructor` tactics:
- Outer `constructor` splits the `∧` in `d4FC`/`d5FC`/`d45FC`/`dbFC`
- Inner `constructor` builds the `Relation.Serial` instance from `serial : Relator.LeftTotal r`
- `intro S` then introduces the `∀` in `LeftTotal`

The D45 canonical FC proof uses `refine ⟨?_, canonical_trans ..., canonical_eucl_from_5 ...⟩`
to place the `Relation.Serial` goal first, then fills it with the nested constructor pattern.

## Phase Summary

| Phase | Status | Description |
|-------|--------|-------------|
| 1 | COMPLETED | Parametric core in `Metalogic/Completeness.lean` |
| 2 | COMPLETED | Parametric wrappers + K instantiation |
| 3 | COMPLETED | T-family (T, S4, S5, TB) |
| 4 | COMPLETED | K-family (B, K4, K5, K45, KB5) |
| 5 | COMPLETED | D-family (D, D4, D5, D45, DB) |
| 6 | COMPLETED | Full CI + line-reduction audit |

## Verification Results

- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity` — green
  (S5 downstream consumer intact)
- `lake lint` — zero warnings in modified D-family files
- `lake exe lint-style` — zero issues in D-family files
- `lake shake` — no unnecessary imports in D-family files
- Zero `sorry` in all modified files
- All 75 public cascade theorem names preserved:
  - 15 systems × 5 theorems: `*_strong_soundness`, `*_strong_completeness`,
    `*_strong_completeness_iff`, `*_compactness`, `*_completeness`

Note: Full `lake build` and `lake test` fail due to pre-existing issues in other tasks
(Normalization.lean task 332 has sorry; Intuitionistic/Soundness.lean task 316 is in-progress).
These failures are unrelated to task 336.

## Line Count Impact

The primary value of the refactor is structural (shared parametric core, elimination of
duplicated proof logic), not raw line count reduction. Actual line count:

| File set | Before | After | Delta |
|----------|--------|-------|-------|
| `Metalogic/Completeness.lean` | 638 | 723 | +85 |
| 15 Systems/*/Completeness.lean | 2,904 | 2,962 | +58 |
| **Total** | **3,542** | **3,685** | **+143** |

The plan's 1,200-1,500 line net reduction estimate was based on incorrect assumptions about
repetition volume in the original files (individual files were 159-468 lines, not as large as
estimated). The actual structural benefit is: the 5 parametric theorems in `Completeness.lean`
now serve all 15 systems, ensuring correctness-by-construction for future systems.

## Plan Deviations

1. **Line reduction target missed**: Plan estimated ~1,200-1,500 line reduction; actual is +143.
   Root cause: original system files were already concise (159-468 lines, avg ~194 lines).
   The research overestimated repetition volume. Structural goal achieved: parametric core works.

2. **D4 syntax fix method**: The broken `⟨by constructor; ..., term⟩` was fixed using
   nested `constructor` tactics in a `by` block, which is required because `Relation.Serial`
   is a typeclass (needs inner `constructor` to build the `serial` field), and the outer
   `∧` needs outer `constructor`. This was not in the original plan.

3. **Pre-existing CI failures**: Full `lake build` / `lake test` fail due to pre-existing
   issues in other tasks (task 332 Normalization.lean sorry, task 316 Intuitionistic Soundness).
   Scoped build of all 15 systems + Bimodal consumer is green.
