# Implementation Summary: Phase 5 — Discharge `nested_sound_impL`

- **Task**: 570 - nested_sound_impL_lambda_chain_induction
- **Plan**: `specs/570_nested_sound_impL_lambda_chain_induction/plans/01_lambda-chain-induction-plan.md`
  (Phase 5 of 8)
- **Research**: `specs/570_nested_sound_impL_lambda_chain_induction/reports/01_lambda-chain-induction.md`
- **Status**: [COMPLETED]
- **Session**: sess_1785113705_bcf38a
- **Commit**: `702c4c6b`

## Overview

Replaced the strategic `sorry` in `nested_sound_impL` with the research-compiled `impL_repaired`
assembly (report §L5), transcribed and adapted to the in-file names of the declarations Phases
1–4 landed. This is the task's headline deliverable: the Cslib bare-sorry census moves 41 → 40,
with the `Nested/Soundness.lean` entry gone from the inventory.

## What Changed

**File**: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`

- **`nested_sound_impL`'s body**, replaced end-to-end:
  1. `ΨX`/`ΨY`/`ΨZ` set to the box/RHS shapes the source's `L_X`/`L_Y`/`L_Z` correspond to.
  2. `h4 : ⊢ (ΨX.fm ∧ ΨY.fm) ⊃ ΨZ.fm`, via `lemma4_7_iii (lambdaChain_step2 (P := ctx.π.fm)
     (lambdaChain_XZ_imp_Y A B ctx.Λ))`, aligned to `ΨX.fm`'s shape by `rw [psiX_fm ctx A]`.
  3. `h5 := lemma4_9_fillRhs h4 ctx.Γ'` — the lift through `Γ'` (already-landed Lemma 4.9 branch).
  4. `hAX : ⊢ (ctx.Γ'.fillRhs ΨX).fm` — transports premise `hA` via
     `match hΓ : ctx.Γ' with | [] => … | G :: r' => …`:
     - `G :: r'`: `rw [hΓ, OutputCtx.fillRhs_append] at hA; exact hA` — definitional transport
       through the already-landed `OutputCtx.fillRhs_append`.
     - `[]`: `hA` reduces to a closed derivation (a theorem, not merely derivable-under-a-box), so
       `obtain ⟨d⟩ := hA; exact cs5DerivImpOfDerivable Proposition.top ⟨.necessitation _ d⟩`
       necessitates it and weakens behind `⊤ ⊃`. This mirrors the existing `lemma4_2_id`/
       `lemma4_2_bot` necessitation idiom already in this file (Lemma 4.2 section).
  5. `exact andMP h5 hAX hB`.
- **Section docstring** (`/-! ## ⊃• (impL): … -/`), retitled from "Deferred, Strategic Sorry" to
  describe the landed construction. Records the source's `L_X, L_Y, L_Z` page-10 text, the
  flagged Lean-encoding divergence (`lemma4_9_fillRhs`/`fillRhs` instead of the source's stated
  `lemma4_8`/`fillFull` route — rejected because `fillFull`'s singleton-case `comma Φ Γ` merge
  produces a `⊤`-conjunct mismatch that `fillRhs`'s uniform base case avoids), and why the
  two-case split on `ctx.Γ'` is needed and sound (a closed derivation can be necessitated; a
  hypothesis merely derivable inside a box cannot).
- **`nested_sound_impL`'s own docstring**, rewritten to state what it proves (Theorem 4.1's `⊃•`
  case, pp. 9–10) instead of pointing at a deferral.
- **`nested_sound` section docstring**, corrected: removed "Every constructor except `impL` is
  fully discharged" (doubly inaccurate — `cut` was never present as a constructor arm at all),
  replaced with an accurate statement that `impL` is now sorry-free and a forward-pointing note
  that `.cut` still needs its arm (Phase 7).
- **Deferral comment block** (`-- sorry: …`) removed entirely.

## Decisions

- **Verbatim transcription of the compiled assembly**, per the dispatch's settled design — the
  report's `impL_repaired` was already compiled sorry-free end-to-end (with `lambdaChain_XZ_imp_Y`
  and `lambdaChain_step2` supplied as hypotheses, both independently landed by Phases 3–4). No
  proof-strategy re-derivation.
- **The report's `hAX` case bodies were elided** (`…` placeholders in both branches of the
  `match`). This dispatch filled them in from the surrounding toolkit: the `G :: r'` branch from
  `OutputCtx.fillRhs_append`'s literal statement (`Context.lean:221`), and the `[]` branch from
  the already-landed `cs5DerivImpOfDerivable` + `.necessitation` idiom used identically at
  `lemma4_2_id`/`lemma4_2_bot` (`Soundness.lean:259–293`) for the exact same "closed theorem,
  weaken behind a fresh antecedent" shape. Verified via `lean_goal` (goal state before/after the
  final `exact andMP h5 hAX hB` line showed `goals_after: []`, i.e. proof complete) and then via
  scoped `lake build`, which returned exactly one diagnostic (see Verification below).

## Plan Deviations

None. All five Phase 5 task-list items were executed as specified; the `hAX` case bodies (left as
`…` in the report) were filled in using only already-landed lemmas cited in the plan's dependency
list (`OutputCtx.fillRhs_append`, `necessitation`), not new machinery.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness` — fails with **exactly
  one** diagnostic: `Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)` (the
  pre-existing, Phase-7-owned non-exhaustiveness error). The `declaration uses 'sorry'` warning is
  **gone**. No other diagnostic was introduced.
- `bash .claude/scripts/lean-sorry-census.sh Cslib` — `sorry_count: 40` (was 41); the inventory
  has **no** `Nested/Soundness.lean` entry at any line.
- `#print axioms nested_sound_impL` — **not run**. Per the plan's own note (Phase 5 "Note"
  paragraph), the module does not yet produce a `.olean` (still red on the unrelated `.cut` case),
  so `import`-based axiom checking is impossible until Phase 7 closes the build. Correctly
  deferred to Phase 8; not claimed here.
- All 18 existing `nested_sound_*` case lemmas and the Preserved-Assets declarations are untouched
  (only `nested_sound_impL`'s body and three docstrings were edited).

## Impacts

- Cslib bare-sorry census: 41 → 40.
- `Soundness.lean` is now down to exactly one diagnostic (the `cut` non-exhaustiveness error),
  matching the plan's stated build expectation for this phase precisely.
- No new `axiom`, no vacuous definition, no `sorry` introduced anywhere.

## Follow-ups

- Phase 6 (`OutputCtx.fillLhs_empty_imp_fillEmpty` in `Translation.lean`, the `cut` bridging
  induction) is independently available — it depends only on Phase 2, already `[COMPLETED]`.
- Phase 7 (land `nested_sound_cut` and the `.cut` arm, RED → green) requires **both** this phase
  and Phase 6 to be `[COMPLETED]` before it starts.

## References

- Research report: `specs/570_nested_sound_impL_lambda_chain_induction/reports/01_lambda-chain-induction.md`,
  §"L5. The assembled `nested_sound_impL`".
- Source: R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal Logics*,
  LMCS 11(3:7), 2015, pp. 9–10 (Theorem 4.1, `⊃•` case; Lemma 4.9). BibKey
  `ArisakaDasStrassburger2015`.
- Plan: `specs/570_nested_sound_impL_lambda_chain_induction/plans/01_lambda-chain-induction-plan.md`,
  Phase 5.
