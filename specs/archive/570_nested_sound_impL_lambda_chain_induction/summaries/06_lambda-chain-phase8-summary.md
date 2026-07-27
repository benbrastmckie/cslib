# Phase 8 Summary: Full CI Gate, Axiom Check, and Census Re-Verification

## What Was Done

This was the final, verification-only phase: no new proof obligations, just running every stated
exit invariant with a command that actually ran and fixing forward any fallout it exposed. No
fallout was found inside this task's declared file scope, so no `.lean` edits were made in this
phase — only the plan file's Phase 8 checklist, plan-level status, and Testing & Validation
section were updated to record the verified outcomes.

## Gate Results (verbatim)

| Gate | Result |
|---|---|
| `lake build` (whole library) | **PASS** — 3259/3259 jobs, "Build completed successfully" |
| `lake build Cslib...Nested.Soundness` | **PASS** — 734/734 jobs, zero errors |
| `bash .claude/scripts/lean-sorry-census.sh Cslib` | **PASS** — `sorry_count: 40` (down from 41), no `Nested/Soundness.lean` entry at any line |
| `#print axioms nested_sound_impL` | **PASS** — `[propext, Classical.choice, Quot.sound]` only |
| `#print axioms nested_sound_cut` | **PASS** — `[propext, Classical.choice, Quot.sound]` only |
| `#print axioms nested_sound` | **PASS** — `[propext, Classical.choice, Quot.sound]` only |
| New-axiom diff (task's 4 owned files) | **PASS** — no `axiom` declarations added; all `axiom` hits are prose |
| `lake exe checkInitImports` | **PASS** — exit 0, silent |
| `lake exe mk_all --check` | **PASS** — "No update necessary" |
| `lake test` | **PASS** — exit 0, all 9253 targets including `CslibTests` |
| `lake lint` | **FAIL (out of scope)** — 2 pre-existing errors, `LoopChecking.lean:106-107`, task 559, never touched by task 570 |
| `lake exe lint-style` | **FAIL (out of scope)** — same 2 errors, same file/lines; deviation from the plan's expectation that this target would not exist — it does exist |
| `bash scripts/pre-pr-check.sh` | steps 1-3 pass (report only pre-existing, out-of-scope items); step 4 fails on a stale hardcoded `lake build Cslib.Logics.Bimodal.Metalogic` path — that barrel file has never existed in this repository's git history; not caused by this task |

## Out-of-Scope Fallout (recorded, not fixed)

Two independent pre-existing issues were surfaced by the full-repository gates, both fully outside
this task's declared file scope (`Soundness.lean`, `Rules.lean`, `Context.lean`,
`Translation.lean`):

1. **`Cslib/Logics/Modal/Tableau/LoopChecking.lean:106-107`**: two style errors (space before
   semicolon) inside a markdown-fenced shell snippet embedded in a docstring. `git log`/`git
   blame` confirm this file was last touched by task 559 and never by any of task 570's eight
   phase commits. Flagged by both `lake lint` and `lake exe lint-style`.
2. **`scripts/pre-pr-check.sh` step 4**: hardcodes `lake build Cslib.Logics.Bimodal.Metalogic`,
   but `Bimodal/Metalogic` is a directory, not a `.lean` barrel file, and has never been one in
   this repository's history. The script itself was last touched by an unrelated historical task;
   task 570 never touched `Bimodal/`.

Per the Postmortem Constraints ("Do NOT edit any file outside the declared file scope") and the
plan's Rollback/Contingency guidance for out-of-scope fallout, both are reported here rather than
silently fixed.

## Optional Hardening: Attempted, Dropped

The plan's Phase 8 task list named an optional (non-critical-path) regression test formalising
D2's counterexample as a `CKValidFC cs5FC''` instance against `cs5_soundness_derivable''`
(`CS5.lean:446`). Unlike every other Preserved Asset in this plan, the research report explicitly
did not attempt or compile this — it rated feasibility only "Medium" and left it unattempted.
Instantiating `CKValidFC cs5FC''` requires building a full fallible-world model from scratch
(`World` type, `Preorder` instance, relation `r`, valuation `val`, `botForces`, and all of
`CKValidFC`'s upward-closure/monotonicity side-conditions) with no compiled starting point beyond
the two syntactic-derivability witnesses `hA_derivable`/`hB_derivable`. This is substantial novel
semantic engineering, not the "small, bounded fix-forward" character of the rest of Phase 8. Per
the task item's own explicit escape hatch ("if it does not close within a bounded attempt, drop
it and say so; it is not on the critical path and must not be allowed to turn a green task red"),
it was dropped. All mandatory exit criteria are green without it.

## Task-Level Outcome

All eight phases are `[COMPLETED]`. The task's headline invariants all hold:

- `lake build` RED (baseline `88b198bf`) to GREEN (flipped at Phase 7, reconfirmed here on the
  full whole-library build).
- Cslib bare-sorry census 41 to **40**, with `Soundness.lean:1315` gone from the inventory.
- `nested_sound_impL`, `nested_sound_cut`, and `nested_sound` are all `sorryAx`-free with no new
  axioms.
- The task's mandatory scope expansion (D1 `lemma4_7_ii`, D2 `outputPruning` repair, D3 the
  missing `.cut` arm) is fully landed alongside the discharge the task was originally titled for.

## Plan Deviations

- `lake exe lint-style` **is** a defined target in this repository's `lakefile.toml`, contrary to
  the plan's stated expectation (Risks & Mitigations, and the Phase 8 task list) that it was not.
  It ran and reported 2 pre-existing, out-of-scope errors (see above) — recorded as the actual
  outcome rather than the anticipated "target not defined" outcome.
- The optional D2-regression hardening task was attempted-then-dropped per its own sanctioned
  escape hatch (see above) — not a deviation from the plan's contingency, but the contingency's
  intended outcome given no compiled starting point existed.

## Commit

This phase's edits are confined to the plan file (Phase 8 checklist, plan-level status, Testing &
Validation section) — no `.lean` files were touched, since no in-scope gate failure required a
fix-forward edit.
