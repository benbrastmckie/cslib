# Implementation Summary: Simplify Normalization Proof Sites (Narrowed Scope)

- **Task**: 412 - simplify_proofs_normalization_foundations
- **Plan**: plans/01_narrow-normalization-collapses.md
- **Status**: [COMPLETED]

## What Was Done

Applied the two research-confirmed `grind` collapses identified in
`reports/01_simplify-normalization-proof-sites.md`, deleting the dead follow-on tactic lines each
collapse produced:

1. **`Cslib/Foundations/Logic/Theorems/BigConj.lean`** — in the `nil` sub-branch of
   `bigconj_mem_derivable` (singleton-list case), replaced
   `simp only [bigconj_singleton] at hconj` / `simp only [List.mem_singleton] at hmem` /
   `rw [hmem]; exact hconj` with a single `grind`. Verified with `lean_multi_attempt` before
   editing (bare `grind` closes the goal; the two follow-on lines become "No goals to be
   solved" dead code) and with `lean_goal` after editing ("no goals").

2. **`Cslib/Foundations/Logic/Metalogic/ListDeduction.lean`** — in the `φ = ψ` branch of
   `list_deriv_reflection`, replaced `simp only [listImp_cons]` / `exact listImp_axiom_k φ Ψ`
   with `grind [listImp_axiom_k]`, keeping the preceding `unfold ListDeriv`. Confirmed via
   `lean_multi_attempt` that bare `grind [listImp_axiom_k]` (without `unfold ListDeriv`) fails,
   so the `unfold ListDeriv` line was retained as required by the plan's fallback guidance.

## Plan Deviations

None. Both edits were applied exactly as specified; the one open verification question in the
plan (whether `unfold ListDeriv` is still required before `grind [listImp_axiom_k]`) was
resolved empirically in favor of keeping it, per the plan's own instruction to "verify ... and
keep the minimal form that closes the goal."

## Verification (CSLib CI Pipeline)

All steps run from a warm Mathlib cache (`lake exe cache get`: "Already decompressed 8542
file(s)"):

| Step | Result |
|------|--------|
| `lake build` (full project) | Passed — 3255/3255 jobs |
| `lake exe checkInitImports` | Passed — no output |
| `lake lint` | Passed — "Linting passed for Cslib." |
| `lake exe lint-style` | Passed — no output |
| `lake shake --add-public --keep-implied --keep-prefix` | No findings for either modified file. The command's own build/replay pass surfaces pre-existing warnings and `sorry`s in unrelated `Cslib/Logics/Propositional/Tableau/**` files and ends with a stale-olean message; this is a known, out-of-scope shake artifact (precedent: `specs/550_remove_bimodal_temporal_linter_suppressions/summaries/01_drop-linter-suppressions-summary.md`), not a regression from this change. |
| `lake exe mk_all --module` | "No update necessary" |
| `lake test` | Passed — 9247/9247 jobs |

Additional checks:
- `grep -n "\bsorry\b"` on both modified files — zero matches.
- `lean_verify` on `bigconj_mem_derivable` and `list_deriv_reflection` — axiom sets are exactly
  `{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no new axioms).
- `git show` on the implementation commit confirms only the two intended files were touched
  under `Cslib/`, both with net line reductions and no new declarations.

## Files Modified

- `Cslib/Foundations/Logic/Theorems/BigConj.lean` (net -2 lines)
- `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` (net -1 line)

## Non-Goals Respected

Per the plan, the following were left untouched: `Metalogic/MCSProperties.lean`,
`Metalogic/GenericMCS.lean` (deferred pending task 41), all `Logics/*/Metalogic/**/
GenericMCSBridge.lean` sites, `ListDeduction.lean:82-83`, and the `BigConj.lean:115,128,133,136`
normalization-then-manual-ModusPonens sites.
