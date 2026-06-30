# Execution Summary: Task 388

- **Task**: 388 - Remove dead normalization track and heartbeat/simp debt in Termination.lean
- **Status**: [IMPLEMENTING] → implemented
- **Date**: 2026-06-29
- **Agent**: cslib-implementation-agent

## What Was Done

### Phase 1: Delete Group A (normalizeAux_fixpoint cascade) [COMPLETED]

Deleted the entire `normalizeAux_fixpoint` support chain from
`Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean`:
- `/-! ## Normalization Termination Lemmas -/` section header (line 202)
- `normalizeAux_ax` (`@[simp] private`, line 204)
- `normalizeAux_ass` (`@[simp] private`, line 210)
- `normalizeAux_fixpoint_aux` (`private`, lines 216-303)
- `normalizeAux_fixpoint` (public `theorem`, lines 304-308)

Total: ~107 lines removed.

Updated the module docstring to remove the `normalizeAux_fixpoint` bullet from the
`## Main Results` section.

Scoped `lake build` confirmed no simp regressions: the `@[simp]` lemmas `normalizeAux_ax`
and `normalizeAux_ass` were only referenced inside `normalizeAux_fixpoint_aux` (itself
deleted), so no other proofs depend on them.

### Phase 2: Delete Group B (subs/subsOne redex pair) [COMPLETED]

Deleted the jointly-dead pair:
- `subs_maximalFormulas_mem` (private theorem, lines 376-657 post-Phase-1)
- `subsOne_new_redex_complexity_lt` (private theorem, lines 659-682 post-Phase-1)

Both declarations had 0 external callers. The next live declaration `commutingSum`
(private def, previously line 796) was confirmed intact.

Total: ~308 lines removed.

### Phase 3: Lint sweep + CI verify [COMPLETED]

Fixed residual lint debt surfaced after the deletions:

1. **Unused simp args** (lines 446, 450 in `commutingSum_weak`): Removed `nodeCount_weak`
   from two `cases D <;> simp [Theory.Derivation.weak, nodeCount_weak]` calls.

2. **Unused simp args** (lines 618, 641 in `snAndE1Form`/`snAndE2Form`): Removed
   `isOrERoot` and `isIntroRoot` from two `simp_all [isStronglyNormal, isOrERoot, isIntroRoot]`
   calls.

3. **Flexible simp** (lines 805-806 in `snImpEForm`): Changed
   `by simp [isStronglyNormal]; exact ha` to
   `by simp only [isStronglyNormal]; exact ha` for two cases (`.ax h`, `.ass h`).

4. **Unused argument** (`conclusionGrounded`, line 39): Added `@[nolint unusedArguments]`
   to suppress the pre-existing `unusedArguments` linter warning. The `_d` argument is
   intentionally unused in the body (it serves only to bind the implicit `G` and `A` via
   its type); this is a legitimate pattern. Updated docstring to clarify.

### Phase 4 (OPTIONAL): Skipped

The `snImpEForm`/`snOrEForm`/`snSubst` mutual well-founded recursion at line ~782
(with the `maxHeartbeats 2000000` override at line 778) was NOT decomposed. The override
is already comment-justified (lines 779-781), so no mandatory action was required.
Decomposing the mutual block is high-risk with no trivial path.

## CI Verification

All CI steps passed:

| Step | Result |
|------|--------|
| `lake build Module` (scoped) | ✔ pass (clean, no warnings) |
| `lake build` (full) | ✔ pass |
| `lake exe checkInitImports` | ✔ pass |
| `lake lint` (Termination.lean) | ✔ clean (no new warnings) |
| `lake exe lint-style` | ✔ clean |
| `lake shake` | ✔ clean |
| `lake exe mk_all --module` | ✔ no update necessary |
| `lake test` | ✔ all tests pass |

Additional checks:
- Sorry count in modified file: 0 (two grep matches are in comments: "sorry-free")
- Vacuous definitions: 0
- New axioms introduced: 0
- `normalize`/`normalizeAux` in `Reduction.lean`: untouched (confirmed live)

## Plan Deviations

- **Phase 4** (OPTIONAL): Skipped per plan guidance -- high-risk, not trivially cheap;
  `maxHeartbeats` override is already comment-justified. No functional change.
- **`conclusionGrounded` `unusedArguments` fix**: Not in the plan but addressed as
  pre-existing lint debt surfaced during Phase 3. Applied `@[nolint unusedArguments]`
  rather than redesigning the signature (which would break type inference).

## File Changes

- **Modified**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean`
  - Net: 9 insertions, 424 deletions (1518 → 1103 lines)
  - Groups A + B deleted, lint fixed, `conclusionGrounded` lint suppressed

## Summary

Task 388 is complete. Removed ~415 lines of confirmed dead code from Termination.lean,
fixed all residual lint warnings surfaced by the deletions, and passed the full CI
pipeline. No new axioms, no sorries, no vacuous definitions.
