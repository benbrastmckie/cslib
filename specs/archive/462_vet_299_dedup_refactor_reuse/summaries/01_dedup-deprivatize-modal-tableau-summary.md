# Implementation Summary: Task #462 — Dedup Case-Arms + De-privatize Reused Lemmas (Modal Tableau)

- **Task**: 462 - vet_299_dedup_refactor_reuse
- **Plan**: plans/01_dedup-deprivatize-modal-tableau.md
- **Status**: Implemented (all 4 phases complete; scoped/manual CI green)
- **Session**: sess_1783922075_911857_462

## What Was Done

### Phase 1 — SoundnessStep.lean helper-lemma extraction
Extracted two private helper lemmas, `negImp_alpha_preserved` (positive antecedent) and
`negImp_alpha_preserved_neg` (negation antecedent `A = A1 → ⊥`), placed right after
`accFreshInv_empty` and before `modalStepBranch_preserves_sat`. Collapsed all 22 duplicated
leaf case-arms of the negative-implication α-rule family (18 positive-antecedent + 4
negation-antecedent) down to one-line `exact ⟨_, List.mem_cons_self, negImp_alpha_preserved(_neg)
hacc hb hneg⟩` calls, keeping each arm's per-constructor `simp [...] at hsf; obtain ...;
subst ...` prefix intact. `SoundnessStep.lean`: 1705 → 1482 lines.

### Phase 2 — De-privatize base lemmas
Removed `private` from `modalStepBranch_none_saturated` (Completeness.lean) and from
`modalStepBranch_eClosure`, `modalSf_pos`, `modalSf_one_imp_depth_zero` (FmpMeasure.lean).
Added a docstring to `modalSf_pos` (previously undocumented, would have tripped the cron-only
`docBlame` linter). Did not add `protected` (confirmed a no-op for cross-module reuse in
Lean's module system — the fix is removing `private` in a `@[expose] public section`).

### Phase 3 — Delete CompletenessLoop.lean local copies
Deleted the four now-redundant exact-copy local lemmas: `modalLoop_stepBranch_none_saturated`,
`modalLoopSf_pos`, `modalLoopSf_one_imp_depth_zero`, `modalLoop_eClosure` (with their
doc-comments), and repointed all ~12 call sites and doc-comment cross-references to the
de-privatized originals. Left `modalMaxWorld_lt_worldBound_of_phiBound` and `modalLoop_bClosure`
untouched (confirmed legitimate generalizations, not private-blocked copies).
`CompletenessLoop.lean`: 1197 → 1096 lines.

### Phase 4 — CI verification
All 11 `Cslib.Logics.Modal.Tableau.*` modules build clean (scoped `lake build`, zero errors).
`lean_verify` on `modalStepBranch_preserves_sat` reports only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero new axioms, zero sorry. `lake exe
lint-style` exits 0 with zero findings. `checkInitImports` manually verified (all 4 touched
files import `Cslib.Init`). `lake shake` processed the touched files with zero new
unused-import findings before erroring on an unrelated out-of-date target. Grep confirms zero
residual references anywhere in `Cslib/` to the four deleted lemma names.

**CI caveat**: `lake exe checkInitImports` (binary), `lake test`, `lake exe mk_all --module`,
and a full `lake shake` pass all require a full-project `lake build`, which is currently
blocked by unrelated, uncommitted, in-progress changes to
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (task 317's territory, actively
edited by a concurrent agent, containing an active `sorry` and a type-mismatch error). This is
disjoint from this task's territory (`Cslib/Logics/Modal/Tableau/`) and not caused by these
changes. Scoped/manual equivalents (above) substitute for these four steps; they should be
re-run once task 317's tree is green again.

## Plan Deviations

- Phase 4: substituted scoped/manual verification for the four full-repo-only CI steps
  (`checkInitImports` binary, `lake test`, `lake shake` full pass, `mk_all` binary) because the
  repo-wide `lake build` was blocked by a concurrent, uncommitted, out-of-territory build
  failure (task 317's `Scheme.lean`), not by any change in this task. See the Phase 4 note in
  the plan file for the full list of equivalents run and their results.
- No other deviations. All theorem statements are unchanged (pure proof-term / accessibility
  refactor); no `sorry`, no new axioms, no vacuous definitions introduced.

## Net Line-Count Impact

| File | Before | After | Δ |
|------|--------|-------|---|
| SoundnessStep.lean | 1705 | 1482 | −223 |
| Completeness.lean | 831 | 832 | +1 |
| FmpMeasure.lean | 3009 | 3011 | +2 |
| CompletenessLoop.lean | 1197 | 1096 | −101 |
| **Total** | **6742** | **6421** | **−321** |

## Commits

- `f11e3a48` — task 462 phase 1: extract negImp_alpha_preserved(_neg) helper lemmas
- `38089c61` — task 462 phase 2: de-privatize reused Tableau lemmas
- `b834fce6` — task 462 phase 3: delete CompletenessLoop private-copy re-derivations
- (this summary + final metadata commit follows)

## Files Modified

- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean`
- `Cslib/Logics/Modal/Tableau/Completeness.lean`
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
