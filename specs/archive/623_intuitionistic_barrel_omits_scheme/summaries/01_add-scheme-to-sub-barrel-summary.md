# Implementation Summary: Add Scheme to the Intuitionistic Sub-Barrel

- **Task**: 623 - Reconcile Intuitionistic.lean sub-barrel omitting Scheme while Cslib.lean imports it directly
- **Plan**: plans/01_add-scheme-to-sub-barrel.md
- **Research**: reports/01_barrel-scheme-omission.md
- **Status**: [COMPLETED]

## What Changed

One line added to `Cslib/Logics/Propositional/Tableau/Intuitionistic.lean`:

```lean
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
```

Inserted between the existing `Soundness` and `Completeness` import lines, matching the file's
bottom-up dependency ordering and the true chain `Rules -> Expansion -> Soundness -> Scheme ->
Completeness -> DecisionProcedure`. No other line in the file was touched.

`git diff --stat -- Cslib/Logics/Propositional/Tableau/Intuitionistic.lean` confirms exactly
`1 file changed, 1 insertion(+)`, matching the plan's Scope Hypothesis.

Note: the working tree also carries several unrelated, pre-existing modifications from other
in-flight tasks (`.claude/scripts/literature-fidelity-audit.sh`,
`.claude/scripts/literature-search.sh`, other tasks' plan/metadata files, `specs/TODO.md`,
`specs/state.json`, `specs/events.jsonl`) that predate this session -- these are out of scope
and untouched by this task.

## Verification Performed

Per the plan's sanctioned verification set (not the generic 7-step CSLib CI pipeline, which was
deliberately excluded for this task due to the full-build hazard below):

1. **Targeted build**: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic` -- succeeded
   (963 jobs). Also built the immediate parent barrel `Cslib.Logics.Propositional.Tableau`
   (978 jobs, ~2s) to keep its olean fresh relative to the edit. Both builds are clean except for
   one pre-existing, unrelated linter warning in `Intuitionistic/DecisionProcedure.lean`
   (`unusedDecidableInType`), present before this change.
2. **`lake exe mk_all --module`**: reported "No update necessary"; `git diff --stat -- Cslib.lean`
   is empty -- `Cslib.lean` is byte-identical, confirming the barrel-membership edit was exactly
   the missing piece (Cslib.lean already imported `Scheme` directly; nothing to regenerate).
3. **`lake exe checkInitImports`**: exit 0, no output -- passes.
4. **`lake exe lint-style`**: exit 0, no output -- passes.
5. **`bash scripts/check-shake-residue.sh --list`**: see deviation below.
6. **Scope Hypothesis**: confirmed via `git diff --stat` scoped to the target file.

## Plan Deviations

**Shake residue verification (Phase 1, task 6 / Testing & Validation item 5)**: the plan
specified running `bash scripts/check-shake-residue.sh --list` and confirming the changed file is
not newly flagged. This could not be run as literally specified, for a discovered reason not
anticipated in the plan's Risks table:

- `lake shake` internally runs a `lake build --no-build` freshness sanity check against its
  target (the whole `Cslib` library facade, i.e., effectively the entire ~700-module tree,
  including `Cslib.lean` itself), *before* it performs any actual import analysis.
- Live evidence: a direct `lake shake --add-public --keep-implied --keep-prefix Cslib` invocation
  progressed through 3324/3325 build jobs (mostly fast cache replays) and then failed with
  `error: target is out-of-date and needs to be rebuilt` / `error: there are out of date oleans;
  run 'lake build' or fetch them from a cache first` on the final `Cslib` facade target -- i.e.,
  achieving a state where shake can even begin its analysis requires the exact full-tree build
  the plan's BUILD HAZARD section explicitly and absolutely prohibits ("NEVER run a bare full
  `lake build`. It does not complete on this tree; it stalls on
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`.").
- Critically, `scripts/check-shake-residue.sh --list`'s wrapper does **not** surface this failure:
  it treats any `lake shake` exit code of 0 or 1 as valid and parses flagged-file lines with the
  regex `^/.*\.lean:$`. The "target is out-of-date" error text does not match that pattern, so it
  is silently discarded, and the script reports zero flagged files with exit 0 -- indistinguishable
  from a genuine "nothing flagged" result. Running the wrapper as specified would have produced a
  **false clean**, not a real confirmation. (Verified directly: grepping the raw `lake shake`
  output for the flagged-file pattern returns zero matches even on the failed run, and the shake
  analysis phase itself never started -- the error happens before analysis.) This is a real latent
  bug in `check-shake-residue.sh`; fixing it is out of scope for this task (non-goal: no change to
  files outside the one target file).
- **Substituted verification**: `lake shake --add-public --keep-implied --keep-prefix --force
  Cslib.Logics.Propositional.Tableau.Intuitionistic`. The `--force` flag is shake's own documented
  option (`lake shake --help`) to skip its internal build-freshness gate; scoping the `MODULE`
  argument to the changed target (already confirmed freshly and correctly built in step 1) avoids
  needing the prohibited full-tree build. This ran to completion in ~6s with **exit 0 and zero
  output**. Per shake's own documented exit-code semantics (0 = no suggestions, 1 = has
  suggestions), this is a real, trustworthy confirmation that the changed file's transitive
  closure has zero import-minimization issues, including the newly added `Scheme` import -- not a
  masked failure like the wrapper's result.
- This substitution stays strictly within the plan's BUILD HAZARD constraints: no bare `lake
  build` was run, no `lake env lean <file>` without `--setup` was run, and the additional targeted
  build (`Cslib.Logics.Propositional.Tableau`, the file's immediate parent barrel) was a small,
  fast, scoped build consistent with the plan's own "targeted module build" verification pattern,
  not an approach toward the full-tree build.
- The generic CSLib CI pipeline's `lake exe cache get`, `lake lint`, and `lake test` steps were
  intentionally **not** run, per the delegation context's explicit instruction that "the plan's
  sanctioned verification is: [the five listed steps]" -- these broader steps risk the same
  full-build hazard and were out of scope for this narrowly-scoped task.

No other deviations. All Non-Goals from the plan were respected: `Cslib.lean` was not edited, the
other 12 partial barrels were not touched, no "deliberately excluded" comment was substituted for
the import, and no content module (`Scheme.lean`, `Completeness.lean`, etc.) was modified.

## Final State

- `Cslib/Logics/Propositional/Tableau/Intuitionistic.lean` now declares all six children:
  Rules, Expansion, Soundness, Scheme, Completeness, DecisionProcedure -- matching the sibling
  convention set by `Classical.lean`.
- Zero sorries, zero vacuous definitions, zero new axioms (pure import-line addition; no proof
  content touched).
- Phase 1 marked `[COMPLETED]` in the plan file with inline deviation annotations documenting the
  shake-verification substitution.
