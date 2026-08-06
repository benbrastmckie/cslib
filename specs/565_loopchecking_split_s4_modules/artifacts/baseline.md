# Phase 1 Baseline — Live-Tree Re-Verification

**Tree state**: `HEAD` at the start of implementation, identical blob content to `11607e0f`
(the research tree state) for `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — confirmed via
`git hash-object` matching `git rev-parse 11607e0f:...LoopChecking.lean`
(`d0b722d6a35fa116ab4d5b0728e0f35228f9dfde`) and via `git log --oneline 11607e0f..HEAD -- ...`
returning no commits touching the file. **No drift occurred between research and
implementation start.**

## Re-measurement

- `wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean` → **11,393 lines** (matches research).
- Corrected declaration-count scan (attribute/`public`-aware, not the stale in-file grep):
  **241 top-level declarations**, **58 `private`** — matches research exactly.

## Regeneration procedure (§3.1)

A fresh Python extraction pass over the live file: stripped block comments (`/- ... -/`,
nested-aware) and line comments (`-- ...`) character-by-character (string-literal-aware so `--`
inside strings is not treated as a comment starter), identified declaration headers
(`(private|protected|public|scoped|noncomputable)* (def|theorem|lemma|instance|structure|
inductive|abbrev|class) NAME`, attribute blocks attached to the following declaration),
computed each declaration's `[start, end)` span, and tokenised each span (identifiers, including
dotted-component splitting) intersected against the local declaration-name set to build `refs`.

**Result**: 241 declarations found, 58 private — **identical name set, line numbers, and
visibility** to the existing `decl-graph.json`/`module-assignment.md` (zero names only-in-old,
zero names only-in-new, zero line mismatches, zero visibility mismatches). `decl-graph.json` was
overwritten with the freshly regenerated version (same `fam`/`sub` assignments carried over
verbatim from `module-assignment.md` since the declaration set is unchanged; `refs` recomputed
against the live tree). `module-assignment.md`'s existing content is confirmed still accurate
against the live tree and requires no edit.

## Forward-edge check — HARD GATE

Layering order used: `Universe(0) < BirthKey(1) < Guard(2) < Driver(3) < {Hintikka, InvKeys,
InvAcc}(4) < {Redirect, Invariant}(5) < InvHintikka(6) < LoopChecking(7, residue)`.

Checked every declaration's freshly-regenerated `refs` against this order.

**Result: 0 forward-edge violations.** The layering holds against the live tree. Phase 2 may
proceed.

## Gate results (all against live tree, pre-split)

| Gate | Command | Result |
|---|---|---|
| Build | `lake build Cslib` | **Green — exact job count 3313** |
| Sorry census (`Modal/Tableau`) | manual grep, excluding comment/doc lines | **Exactly 1** — `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1251` (`branchSatisfiableIn_s4FC_ancestor_redirect`) |
| Axiom census | `bash scripts/check-axiom-census.sh` | exit 0 — 43 sorryAx-tainted declarations (baseline 43, matches) |
| Shake residue | `bash scripts/check-shake-residue.sh` | 9 findings (baseline 9, matches); **none in `Modal/Tableau/`** (confirmed via `--list`) |
| Lint suppressions | `bash scripts/check-lint-suppressions.sh` | exit 0 — 19 blanket suppressions (ceiling 19, matches) |
| `checkInitImports` | `lake exe checkInitImports` | exit 0 |
| `mk_all --check` | `lake exe mk_all --check` | exit 0 — "No update necessary" |
| `lint-style` | `lake exe lint-style` | exit 0 |
| `lake test` | `lake test` | exit 0, green (3281/3591 jobs reported at tail, no failures) |
| Boneyard quarantine | `bash scripts/check-boneyard-quarantine.sh` | exit 0 — all 5 sub-checks (a)-(e) OK |

**Baseline job count for Phase 15 reconciliation: 3313.**

## Seam-crossing `private` declarations (26 total)

Confirmed by name against the regenerated graph, and confirmed via docstring-adjacency scan
(each declaration's line immediately preceded by a `-/`-terminated block, after skipping blank
lines) that **all 26 already carry a docstring** — zero missing.

- **Universe (11)**: `mem_modalUniverseS4_of`, `mem_modalUniverseS4_of'`,
  `modalUniverseS4_mem_label`, `mem_of_any_beq_S4`, `any_beq_of_mem_S4`,
  `mem_signedSubfmls_of_formula_S4`, `modalNextWorld_fresh_beq_S4`, `modalTBoxSelf_fresh`,
  `modalTDiaNegSelf_fresh`, `modalFourBoxProp_fresh`, `modalFourDiaNegProp_fresh`.
- **BirthKey (4)**: `boxPlusExtraS4_outputs_subset_S4`, `boxPlus_pos_disjunct_elim`,
  `boxPlus_neg_disjunct_elim`, `successorBirthContent_subset_signedSubfmls`.
- **Driver (11)**: `modalStepBranchS4Keyed_result_keys_eq`,
  `modalStepBranchS4Keyed_result_acc_eq`, `modalApplyOneS4Keyed_nonMint_known_S4`,
  `modalApplyOneS4Keyed_nonMint_universe_S4`, `modalApplyOneS4Keyed_nonMint_snd_eq_acc`,
  `modalStepBranchS4Keyed_keys_subset`, `modalStepBranchS4KeyedOrdered_keys_subset`,
  `modalHintikkaClauseGen_S4Keyed_keys_indep`,
  `modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding`,
  `modalApplyOneS4Keyed_boxNeg_ne_notApplicable`, `modalApplyOneS4Keyed_diaPos_ne_notApplicable`.

## Directory creation

`Cslib/Logics/Modal/Tableau/S4/` created (empty, ready for Phase 2).

## Verdict

All Phase 1 gates pass; the hard gate (zero forward-edge violations) is satisfied. **Phase 2 may
proceed** using the observed figures above (not the research report's figures, though they are
identical in this case) as the baseline for the rest of the task.
