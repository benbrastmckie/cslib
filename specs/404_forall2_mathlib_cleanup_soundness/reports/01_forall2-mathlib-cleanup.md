# Research Report: Task 404 — Replace local List.Forall₂ re-proofs with Mathlib lemmas

**Task type:** cslib | **Session:** sess_1782791125_e726d9 | **Date:** 2026-06-30

## Summary

The four local private helpers in `Cslib/Logics/Modal/Tableau/Soundness.lean`
(`forall₂_of_zip_mem`, `forall₂_append_aux`, `forall₂_drop_aux`, `forall₂_take_aux`)
each have an exact canonical counterpart in `Mathlib.Data.List.Forall2`. The recommended
fix is: add `import Mathlib.Data.List.Forall2`, delete the four local helpers, and switch
the call sites to the library lemmas (with the `List.` namespace prefix).

**This was verified end-to-end**: a trial edit applying the full change builds green via
`lake build Cslib.Logics.Modal.Tableau.Soundness` (492/492 jobs, 0 errors, 0 sorry). The
trial was then reverted, leaving a clean working tree for the implementation phase.

## Reuse Check (CSLib reuse-first)

- The concept is generic `List.Forall₂` plumbing — there is no CSLib `Foundations` abstraction
  to prefer; the right home is Mathlib's `List.Forall₂` API. Reuse is the correct call.
- `List.Forall₂` (the inductive) is already in scope today (used in theorem signatures at lines
  231/233), pulled in transitively. Only the *lemmas* about it live in
  `Mathlib.Data.List.Forall2`, which is **not** transitively imported by `Cslib.Init`
  (`Cslib.Init` only brings `Mathlib.Init` + `Mathlib.Tactic.Common`). This is exactly why
  task 402 added the local re-proofs. Adding the one import resolves it.

## Lemma Mapping (verified)

All Mathlib lemmas are in `namespace List` (file `Mathlib/Data/List/Forall2.lean`). Soundness.lean
has no `open List`, so call sites need the `List.` prefix.

| Local helper (delete) | Mathlib replacement | Mathlib signature |
|---|---|---|
| `forall₂_of_zip_mem hlen h` | `List.forall₂_iff_zip.mpr ⟨hlen, h⟩` | `forall₂_iff_zip : Forall₂ R l₁ l₂ ↔ length l₁ = length l₂ ∧ ∀ {a b}, (a,b) ∈ zip l₁ l₂ → R a b` (line 163) |
| `forall₂_append_aux h1 h2` | `List.rel_append h1 h2` | `rel_append : (Forall₂ R ⇒ Forall₂ R ⇒ Forall₂ R) (· ++ ·) (· ++ ·)` (line 212) |
| `forall₂_drop_aux n h` | `List.forall₂_drop n h` | `forall₂_drop : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (drop n l₁) (drop n l₂)` (line 185) |
| `forall₂_take_aux n h` | `List.forall₂_take n h` | `forall₂_take : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (take n l₁) (take n l₂)` (line 180) |

`forall₂_drop`/`forall₂_take` are drop-in (identical signatures). `rel_append` is the Relator
`⇒` form, which is definitionally a function `Forall₂ R l1 m1 → Forall₂ R l2 m2 → Forall₂ R (l1++l2) (m1++m2)`,
so direct application works. `forall₂_iff_zip` differs only in being an `Iff` over a conjunction,
so the call site changes from `apply` to `refine ... .mpr ⟨_, ?_⟩`.

### Out of scope — keep

`forall₂_replicate_right` (Soundness.lean line 177, used at lines 332/380) is **not** in the
task's list of four and has no trivial Mathlib drop-in. Leave it in place.

## Exact Edits (verified to build)

1. Add after `import Cslib.Init` (line 9):
   ```lean
   import Mathlib.Data.List.Forall2
   ```
   (Plain `import`, not `public import`: the lemmas are used only inside proof terms, never in
   Soundness's public signatures, so a non-public import is correct and shake-friendly.)

2. Delete the four private lemmas: `forall₂_of_zip_mem` (lines 156–175), `forall₂_append_aux`
   (197–203), `forall₂_drop_aux` (205–210), `forall₂_take_aux` (212–217). Keep
   `forall₂_replicate_right` (177–195).

3. Call-site replacements:
   - Line 241: `apply forall₂_of_zip_mem hlength_accs.symm`
     → `refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩` (following `intro b a hmem` unchanged)
   - Line 299: `(forall₂_append_aux hFresh_done` → `(List.rel_append hFresh_done`
   - Line 338: `forall₂_append_aux (forall₂_append_aux hFresh_done hFreshNew) hFresh_rest`
     → `List.rel_append (List.rel_append hFresh_done hFreshNew) hFresh_rest`
   - Line 353: `forall₂_drop_aux done.length hunsat_all` → `List.forall₂_drop done.length hunsat_all`
   - Line 362: `forall₂_drop_aux newBs.length hunsat_newBs_bt` → `List.forall₂_drop newBs.length hunsat_newBs_bt`
   - Line 370: `forall₂_take_aux newBs.length hunsat_newBs_bt` → `List.forall₂_take newBs.length hunsat_newBs_bt`

(Line numbers are pre-edit; deleting the helpers shifts the call sites up ~60 lines. The
implementer should match on the surrounding text shown above, not raw line numbers.)

## Verification Performed

- `lake build Cslib.Logics.Modal.Tableau.Soundness` after applying all edits above:
  **`Build completed successfully (492 jobs)`**, 0 errors, 0 sorry.
- Pre-existing warnings unrelated to this change: `linter.style.longLine` warnings in
  `SoundnessStep.lean`, and one `unusedSectionVars` warning on `modalApplyOne_fresh`
  (line 86, untouched). None are introduced by this task.
- Trial reverted with `git checkout`; working tree clean.

## Recommendation

Proceed with the add-import-and-replace approach (do **not** keep the local helpers — the
Mathlib lemmas fully subsume the four in-scope ones). Single-phase implementation, low risk,
no sorry, no new axioms.

### CI / lint considerations for the implementer
- Run the full CI order: `lake build`, `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`.
- Run `lake shake --add-public --keep-implied --keep-prefix` — confirm shake is satisfied with
  the plain (non-public) `import Mathlib.Data.List.Forall2` and does not request promotion/removal.
- Deleting the helpers removes their docstrings/`private` decls — no docBlame impact.
- No new declarations are added, so no naming-convention (defsWithUnderscore/lowerCamelCase) work.
```

