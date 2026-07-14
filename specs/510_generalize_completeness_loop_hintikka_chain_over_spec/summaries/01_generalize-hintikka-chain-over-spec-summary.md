# Implementation Summary: Task #510 — Generalize the Completeness/Hintikka Chain over RuleApplicationSpec

- **Task**: 510 - `generalize_completeness_loop_hintikka_chain_over_spec`
- **Status**: [COMPLETED] — all 9 phases green, all 3 acceptance criteria confirmed by direct
  inspection of committed source.
- **Plan**: `plans/01_generalize-hintikka-chain-over-spec.md`
- **Research**: `reports/01_generalize-hintikka-chain-over-spec.md`

## What Was Delivered

The Hintikka-set / saturation-characterisation chain (`Completeness.lean` +
`CompletenessLoop.lean`, ~850 lines) is now generalized over an abstract
`apply : RuleApply Atom` mediated by an 11-field `RuleApplicationSpec` (grown from task 507's
7 fields by F8 `localShapeInvariance`, F9 `boxPosNotExpanding`, F10 `diaNegNotExpanding`, F11
`boxNegWitness`, F12 `diaPosWitness`). T (task 503) now instantiates the entire chain as a
one-liner instead of re-deriving an ~850-line system-specific analog.

### The Three Acceptance Criteria (all confirmed)

- **AC1**: F9/F10 are stated `∃ out, (apply sf b acc).1 = .persistent out` in
  `GenericDriver.lean` — not against K's concrete `boxPropagation` payload. Both
  `modalApplyOne_spec` (K) and `modalApplyOneT_spec` (T) discharge them in Phase 2 (the
  structural proof this form is right, since a concrete form would make T's discharge
  impossible).
- **AC2**: `modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean`, Phase 7, the crux)
  concludes in `modalHintikkaSetGen apply bR aR`, not the concrete `modalHintikkaSet bR aR`.
- **AC3**: `modalExpandBranchesT_hintikka` (`TDriver.lean`, Phase 9) typechecks as a genuine
  one-liner: `modalExpandBranchesGen_hintikka modalApplyOneT modalApplyOneT_spec φ0 fuel`. This
  is the structural proof that AC1 and AC2 were both met — it could not compile otherwise.

## Phases Completed (9/9)

| Phase | Description | Commit |
|---|---|---|
| 1 | Relocate K shape/witness lemmas to `Rules.lean`, payload-weakened | `6ac19353` |
| 2 | Extend `RuleApplicationSpec` to 11 fields; `modalHintikkaSetGen` | `e4a7dd0e` |
| 3 | `Completeness.lean` layer — clause lift, saturation, hintikka_inv | `c3f32a61` |
| 4 | Close the 507 `accFreshInv` gap in `Soundness.lean` | `639779f5` |
| 5 | `CompletenessLoop.lean` — import `GenericDriver`, `ModalLoopInvGen` | `0c2c8fd2` |
| 6 | The four witness-invariant preservation helpers (F9-F12) | `e11096f7` |
| 7 | **CRUX** — `modalStepGen_preserves_invariant` + `modalExpandBranchesGen_hintikka` | `9ac0ef09` |
| 8 | K re-instantiation and zero-regression verification (byte-identity by diff) | `bddc26fb` |
| 9 | T instantiation — `modalExpandBranchesT_hintikka` delivered | (this commit) |

## Files Modified

- `Cslib/Logics/Modal/Tableau/Rules.lean` — relocated `tryAllPropRules_pos`/`_neg` (generic,
  deviation from plan — needed upstream) plus the four K shape/witness lemmas, two
  payload-weakened to `∃ out`.
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — `modalHintikkaSetGen` (spec-free) +
  `modalHintikkaSet_eq`.
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — `RuleApplicationSpec` 7 → 11 fields (F8-F12);
  `modalApplyOne_spec` extended; module docstring updated.
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — one-line import-visibility fix (`import` →
  `public import` for `Completeness.lean`; deviation, see below).
- `Cslib/Logics/Modal/Tableau/Completeness.lean` — `modalHintikkaClauseGen` + `_eq`; `_lift`
  (raw F8); `modalStepBranchGen_none_saturated` (no field); `modalStepBranchGen_hintikka_inv`
  (raw F8, public); `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`; de-privatized
  `modalApplyOne_fst_eq_of_not_box` (F8's K discharge).
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — `modalStepBranch_preserves_accFreshInv_gen`
  (raw `freshLocal`) + K corollary.
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — imports `GenericDriver`; `ModalLoopInvGen`
  + `ModalLoopInv_iff_gen`; `modalLoopGen_bClosure`, `modalStepBranchGen_newExps_const`,
  `modalApplyGen_hasEdge_mono` (deletes `modalLoop_snd_eq_or_addEdge`); the four F9-F12 witness
  helpers; `modalStepGen_preserves_invariant`; `modalExpandBranchesGen_hintikka` (the crux);
  `modalLoopInvGen_initial`, `modalStepBranchGen_mem_preserved`,
  `modalExpandBranchesGen_openBranch_initial_mem`. All K originals retained as byte-identical
  corollaries.
- `Cslib/Logics/Modal/Tableau/TDriver.lean` — `modalApplyOneT_spec` extended to 11 fields (five
  new discharges); imports `CompletenessLoop.lean`; `modalExpandBranchesT_hintikka` (one-liner,
  AC3) plus `modalStepBranchT_eq`/`modalExpandBranchesT_eq`/`modalTableauT_eq` `rfl` bridges.

## Plan Deviations

1. **Phase 1**: `tryAllPropRules_pos`/`_neg` (previously in `Completeness.lean`) had to be
   relocated to `Rules.lean` alongside the four shape/witness lemmas — they are entirely generic
   (no `Atom`-specific content) but were needed by the relocated lemmas, which must live upstream
   of `Completeness.lean`. Pure relocation, zero proof-content change.
2. **Phase 2**: Discovered `FmpMeasure.lean:17`'s `import Cslib.Logics.Modal.Tableau.Completeness`
   was non-`public`, so `GenericDriver.lean` could not transitively reach the de-privatized
   `modalApplyOne_fst_eq_of_not_box` despite `Completeness.lean` being file-order upstream. Fixed
   by flipping that one import to `public import` — a pure visibility change.
3. **Phase 3**: Skipped separate "bundled `spec`-taking wrapper" theorems in `GenericDriver.lean`
   for the three new `Completeness.lean` `_gen` lemmas, since they already use the plan's own
   "Gen inserted mid-name" naming convention, which would collide with `GenericDriver.lean`'s
   established bundled-wrapper naming pattern for the same name. `modalStepBranchGen_hintikka_inv`
   (the only one Phase 7 needs directly) was de-privatized instead, so `CompletenessLoop.lean`
   calls it directly with `spec.localShapeInvariance` inline — functionally equivalent, no name
   collision.

None of these deviations touch the interface design (F8-F12's statements, `modalHintikkaSetGen`'s
definition, or the crux's conclusion type) — all are import-topology or naming adjustments
discovered only when building, consistent with "pure relocation, zero proof-content change."

## Zero-Regression Verification

Confirmed by `diff` (not assertion) against baseline commit `64be55dc` (parent of Phase 1's
`6ac19353`):
- `kValid`, `modalTableau_decides`, `instDecidableKValid`: **byte-for-byte identical including
  proof bodies** (`diff` exit 0).
- `ModalLoopInv`, `modalHintikkaSet`, `modalHintikkaClause`, `modalExpandBranches_hintikka`,
  `modalStep_preserves_invariant`, `modalStepBranch_hintikka_inv`,
  `modalStepBranch_none_saturated`, `modalStepBranch_preserves_accFreshInv`,
  `modalTableau_complete`: **byte-identical statements** (normalized-whitespace signature diff,
  zero drift).

## Downstream Impact

- **Task 503 (T)**: `modalExpandBranchesT_hintikka` — the exact lemma Phase 5 was blocked on —
  is delivered. 503's remaining work is its own `hintikka_box_pos`/`hintikka_diamond_neg`
  analogues (payload-reading, irreducibly T-specific, explicitly out of scope here) plus its
  truth lemma.
- **Task 505 (B)**: gets the full generic chain + spec discharge path, plus the two free
  projection bridges (`hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`). Must still write its
  own payload-reading bridges and truth lemma.
- **Task 506 (S4)**: gets the **statement shape only** via the spec-free `modalHintikkaSetGen`
  (`Saturation.lean`) — S4 cannot discharge `RuleApplicationSpec` (explicitly excluded,
  `GenericDriver.lean`'s module docstring) but can produce its own `modalHintikkaSetGen
  (modalApplyOneS4 φ0) b acc` witness and interoperate at the statement level.

## Verification

Zero `sorry`, zero new `axiom`, zero vacuous placeholders across all eight touched files. Full
CSLib CI (build, `checkInitImports`, `lint`, `lint-style`, `shake`, `test`) green at every phase
boundary. No new lint/style warnings introduced beyond the pre-existing baseline (one unrelated
`PrimeExclusion.lean` `unusedArguments` finding, documented by task 507's precedent).

Concurrent sessions (tasks 506, 509) were actively editing `LoopChecking.lean`,
`FrameCompleteness.lean`, and `Cslib/Logics/Modal/Metalogic/Constructive/*.lean` throughout this
implementation, occasionally causing transient full-project `lake build`/`lake test` failures
unrelated to this task's eight files. Every such incident was verified via a scoped build over
exactly this task's touched modules before proceeding; none were caused by or related to this
task's changes. Every `git add` was scoped narrowly to this task's own files.
