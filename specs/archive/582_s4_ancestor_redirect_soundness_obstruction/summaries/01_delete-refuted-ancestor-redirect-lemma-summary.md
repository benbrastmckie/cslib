# Implementation Summary: Delete the Refuted Ancestor-Redirect Lemma

- **Task**: 582 - s4_ancestor_redirect_soundness_obstruction
- **Status**: [COMPLETED]
- **Started**: 2026-08-07T07:04:49Z
- **Completed**: 2026-08-07T07:28:23Z
- **Artifacts**: `CslibTests/AncestorRedirectRefutation.lean` (new regression witness);
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (lemma, docstring, and section comment
  deleted; obstruction record relocated into the `accPinnedBy` module comment);
  `Cslib/Logics/Modal/Tableau/README.md` and `specs/ROADMAP.md` (sorry-count prose
  reconciled by live re-measurement); `scripts/axiom-census-baseline.txt` (regenerated via
  `check-axiom-census.sh --update`)
- **Standards**: CSLib `CONTRIBUTING.md`, `NOTATION.md`, `ORGANISATION.md`; verified against
  `lake build --wfail --iofail`, `lake test`, and the five honesty-gate scripts
  (`check-axiom-census.sh`, `check-sorry-suppressions.sh`, `check-shake-residue.sh`,
  `check-lint-suppressions.sh`, `check-boneyard-quarantine.sh`)
- **Plan**: `specs/582_s4_ancestor_redirect_soundness_obstruction/plans/01_delete-refuted-ancestor-redirect-lemma.md`
- **Research**: `specs/582_s4_ancestor_redirect_soundness_obstruction/reports/01_ancestor-redirect-refutation-and-route-choice.md`

## Outcome

All 8 phases completed. Route (c) — DELETE — executed exactly as planned: the refuted
`branchSatisfiableIn_s4FC_ancestor_redirect` lemma (`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`,
formerly `:1227`, `sorry` at `:1251`) — the repository's only `sorry` with no owning task — has
been deleted. Its refutation (a machine-checked, sorry-free, zero-`sorryAx` three-world
countermodel) is preserved as an executable regression witness in
`CslibTests/AncestorRedirectRefutation.lean`, and the upgraded obstruction record (refuted, not
merely blocked) is relocated into `FrameSoundness.lean`'s `accPinnedBy` module comment.
`Cslib/Logics/Modal/Tableau/` is now at **0** code-position sorries (down from 1); the repository
is at **27** (down from 28). Every falsified prose record was reconciled by live re-measurement,
never hand-decremented. Task 566's carve-out 1 (`branchSatisfiableIn_s4FC_ancestor_redirect` is
IMMOVABLE) is recorded as lapsed; carve-out 2 (`keysOriginS4`) is confirmed untouched.

## Phase-by-Phase Results

**Phase 1 — Re-verify refutation, capture baselines**: Re-ran the scratch probe (exit 0, axioms
`[propext, Quot.sound]`, no `sorryAx`). Captured every "before" figure the definition of done
compares against: touched-module `--wfail --iofail` sorry-warning count (1,
`FrameSoundness.lean:1227`), `lake test` (exit 0), two-grep code-position sorry census (28
repo-wide, 1 in Modal/Tableau), axiom-census-baseline.txt (58 lines / 43 tainted rows), and a
3-hit-0-use-site consumer audit. All figures matched the plan's Scope Hypothesis exactly.

**Phase 2 — Promote countermodel into `CslibTests/`**: Created
`CslibTests/AncestorRedirectRefutation.lean` (namespace `RefuteAncestorRedirect`, per plan),
adapted to the `module` + paired `import`/`public meta import` idiom from
`S4LoopGuardRegression.lean`, with a full module docstring. Registered it in `CslibTests.lean`
alphabetically before `CslibTests.Bisimulation`. Build and test green; `lean_verify` confirmed
`[propext, Quot.sound]`, no warnings, no `sorryAx`.

**Phase 3 — Relocate the obstruction record**: Rewrote the "three prior soundness routes died"
sentence in the `accPinnedBy` module comment to no longer name the (about-to-be-deleted)
declaration or say "above". Added a new subsection carrying the three surviving facts from the
research report (statement is false + countermodel; why it's false — ancestor
transitive-closure payload; the Massacci citation's dead-end/category-error status), citing the
Phase 2 regression witness, and recording the route decision inline. Comment-only diff,
delimiters balanced, build green.

**Phase 4 — Delete the section comment, docstring, and lemma**: Re-derived all three deletion
boundaries by content (unchanged from Phase 1's hypothesis) and deleted the contiguous
94-line block. `FrameSoundness.lean` now has zero code-position sorries.

*Deviation found and resolved*: Phase 4's verification requires a literal 0-hit grep for the
deleted identifier across `Cslib/ CslibTests/`, but Phase 2's and Phase 3's own prose (already
committed) named the identifier for documentation clarity, producing 2 hits. Resolved by
rewording both mentions to describe the lemma descriptively without reproducing the exact
identifier substring, preserving full semantic content. Re-verified 0 hits; both files rebuild
clean.

**Phase 5 — Regenerate the axiom census baseline**: `check-axiom-census.sh --update` removed
exactly the target row (58→57 lines, 43→42 tainted), matching the plan's hypothesis exactly. One
incidental, explicitly-non-compared metadata (`reason` column) drift on an unrelated row was
noted for the record per the baseline file's own documented comparison contract.

**Phase 6 — Reconcile falsified prose records**: A repo-wide sweep (excluding `specs/**`, which
is frozen historical record, consistent with the plan's own treatment of `TODO.md`) found
exactly the plan's predicted two live-tree files. `README.md`'s sorry census: `1`→`0`, dropped
the retained/immovable clause and the lemma's name entirely (per an explicit task instruction);
re-measured (not hand-decremented) the repo-wide figure `28`→`27`, and also corrected an
adjacent, same-site stale figure (`158`→`187`) per the task 567 house standard. `ROADMAP.md`:
per-subsystem breakdown re-measured (Modal→0), and the Remaining-table row revised to
"DISCHARGED BY REFUTATION". `specs/TODO.md` correctly left untouched.

**Phase 7 — Update the Boneyard carve-out record**: Appended a dated addendum to task 566's
summary recording carve-out 1's lapse (declaration deleted, not moved; both its mechanical
confirmations were consequences of the retained `sorry` and vanished with it), confirming the
Boneyard convention itself is unaffected (a refuted statement was never provenance-bearing), and
confirming carve-out 2 untouched via a fresh live re-measurement.

**Phase 8 — Full gate and route record**: Full `lake build --wfail --iofail`: exactly 4 sorry
warnings remain (all pre-existing Propositional, unrelated to this task), zero in Modal/Tableau,
zero new anywhere. `lake test` exit 0. All five honesty-gate scripts (`check-axiom-census.sh`,
`check-sorry-suppressions.sh`, `check-shake-residue.sh`, `check-lint-suppressions.sh`,
`check-boneyard-quarantine.sh`) exit 0 at or better than baseline. Additional CI-pipeline steps
(`checkInitImports`, `lake lint`, `lake exe lint-style`, `lake shake`, `lake exe mk_all
--module`) all clean on touched files. Cumulative diff confirmed against the plan's predicted
touch set exactly — no other proof, definition, or theorem statement altered.

## Plan Deviations

One deviation, documented inline at Phase 4 and above: the plan's Phase 4 verification gate
(literal 0-hit grep for the deleted identifier) was in tension with Phase 2's and Phase 3's own
prose requirements (which named the identifier for documentation clarity). Resolved by
rewording the two prose mentions to describe the lemma without reproducing its exact identifier
substring — no semantic content was lost, and both the grep gate and the documentation intent
are satisfied. No plan steps were skipped, altered in substance, or deferred.

## Files Changed

- `CslibTests/AncestorRedirectRefutation.lean` (new — executable regression witness)
- `CslibTests.lean` (one import registration)
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (obstruction record relocated into
  `accPinnedBy`; section comment, docstring, and lemma deleted)
- `Cslib/Logics/Modal/Tableau/README.md` (sorry census corrected)
- `scripts/axiom-census-baseline.txt` (regenerated, one row removed)
- `specs/ROADMAP.md` (sorry counts and the S4 guard row reconciled)
- `specs/566_boneyard_creation_eligible_moves/summaries/01_boneyard-creation-eligible-moves-summary.md`
  (carve-out 1 lapse recorded)

## Commits

- `49895836` — task 582 phase 1: re-verify refutation and capture pre-change baselines
- `95136f4c` — task 582 phase 2: promote ancestor-redirect countermodel into CslibTests/
- `9a31b9eb` — task 582 phase 3: relocate upgraded obstruction record into accPinnedBy comment
- `81ae408c` — task 582 phase 4: delete refuted branchSatisfiableIn_s4FC_ancestor_redirect lemma
- `e7bce09c` — task 582 phase 5: regenerate axiom census baseline
- `26644732` — task 582 phase 6: reconcile falsified sorry-count prose in README and ROADMAP
- `7ac1f412` — task 582 phase 7: record task 566 carve-out 1 lapse
- `41475b7a` — task 582 phase 8: full gate green, route (c) DELETE recorded

## AI Tools Used

This work was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Re-verifying the refutation probe and capturing measured baselines
- Adapting the countermodel into an executable `CslibTests/` regression witness
- Relocating and rewriting the obstruction record, and deleting the refuted lemma
- Regenerating the axiom census baseline and reconciling falsified prose records
- Running the full CSLib CI verification pipeline and honesty-gate scripts
- Drafting this summary

All Lean code was verified to compile cleanly against the full CI gate set described above.
