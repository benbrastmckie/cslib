# Implementation Summary: Promote openBranch_countermodel Witness Probes to CslibTests

- **Task**: 602 - Promote the openBranch_countermodel witness probes into CslibTests for CI protection
- **Status**: Implemented
- **Plan**: plans/01_promote-witness-probes.md
- **Research**: reports/01_promote-witness-probes.md

## What Was Done

Three new CI-protected files were created under `CslibTests/`, mirroring the
`CslibTests/BetaSplitRefutation.lean` promotion idiom (copyright header, `module` + paired
`import`/`public meta import`, `/-! # ... -/` module docstring with a scratch-provenance
pointer, `set_option autoImplicit false`, and every printed assertion converted from a bare
`#eval!` to `/-- info: <value> -/` + `#guard_msgs in` + plain `#eval`):

- `CslibTests/WitnessProbe.lean` -- the intuitionistic `[(1,0)]` witness for `phiRef1`
  (7 assertions), plus the folded `WitnessSearch2.lean` search-space content: an `inclPairs`
  computation (no powerset) exposing `(worldCount, admissiblePairCount) = (4, 7)` for `phiRef1`,
  and a membership check that the known witness `[(1,0)]` lies in that admissible-pair space.
- `CslibTests/WitnessSearch3.lean` -- the maximal-inclusion-frame sweep over 8 formulas
  (intuitionistic) + 4 formulas (minimal), 12 assertions, confirming the `phiRef1`/`phiRef3`
  family is where the maximal frame fails.
- `CslibTests/MinProbe.lean` -- the minimal-scheme (`isMinimallyClosed`) witness evidence for
  `phiRef1`, 6 assertions, with the scratch file's genuine parse error fixed by construction
  (the two `/-- ... -/` docstrings that sat directly above bare `#eval!` commands are now either
  `/-! ... -/` section comments or the `/-- info: ... -/` argument of `#guard_msgs`).
- `CslibTests.lean` -- regenerated via `lake exe mk_all --module` (not hand-edited); three new
  `public import CslibTests.*` lines landed alphabetically (`MinProbe`, then later
  `WitnessProbe`, `WitnessSearch3`).

Total of 25 `#guard_msgs` assertions across the three files (7 + 12 + 6), matching the
scratch files' `#eval!` counts exactly (WitnessSearch2.lean's content is folded into
WitnessProbe.lean's docstring plus two new bounded assertions, not a 1:1 port).

## Reconciliation Findings (all transcription fixes, no semantic drift)

Per the plan's reconciliation protocol, every assertion's semantic claim was pre-declared from
the research report before building, then checked against the actual `#guard_msgs` diff:

- **`WitnessSearch3.lean`'s tuple printing** flattens rather than nests:
  `("OPEN", (true, false), true, false)`, not `("OPEN", (true, false), (true, false))` as a naive
  reading of the return type `String × (Bool × Bool) × (Bool × Bool)` might suggest. This exactly
  matched the research report's captured (and flagged-as-needing-re-verification) form. All 12
  assertions in this file needed this one correction; semantic content (which rows pass/fail) was
  unchanged.
- **`WitnessProbe.lean`'s `searchSpaceSize`**: the admissible-pair count for `phiRef1` is 7, not
  the hand-estimated 6 initially written. Pure transcription -- the actual `#guard_msgs` diff was
  read and the assertion corrected to the true value; the witness-membership fact
  (`witnessInSearchSpace = some true`) was unaffected.
- All other assertions (`WitnessProbe.lean`'s 7, `MinProbe.lean`'s 6) matched the research
  report's captured values on the first build with no corrections needed.

No semantic drift was found anywhere: every witness/non-witness pattern predicted by the research
report held exactly as predicted.

## Plan Deviations

- Phase 1's initial draft accidentally placed two consecutive `/-- ... -/` doc comments above
  several `#guard_msgs in #eval` calls (explanatory prose immediately followed by the
  `/-- info: ... -/` argument). This does not parse -- the first docstring has nothing to attach
  to. Fixed before the first build by converting the explanatory prose to `/-! ... -/`
  free-floating section comments, leaving a single `/-- info: ... -/` immediately above each
  `#guard_msgs in`. This pattern recurred in `MinProbe.lean` and was caught and fixed the same
  way before that file's first build too. No plan deviation in scope or content -- purely a
  self-corrected syntax slip caught before any build attempt.
- Phase 4's plan draft (written while composing `WitnessProbe.lean` in Phase 1, ahead of Phase 4's
  formal start) initially recorded a decision NOT to port the bounded `inclPairs` search-space
  check, reasoning it was redundant with `WitnessSearch3.lean`'s machinery. On reaching Phase 4
  proper, this was recognized as re-deciding the plan's own "Bounded optional addition" task
  rather than executing it (the plan-compliance rule's "assessing what's truly minimal" is an
  explicitly forbidden rationalization) -- so the addition was implemented and timed as the plan
  directs (Phase 4 task 3), confirmed to build in ~1.6s (well under the ~10s budget), and kept.

## Verification

Full CSLib CI order run in sequence, all green:

| Step | Result |
|------|--------|
| `lake build` (full project) | Green, 2.3s (warm cache); pre-existing `sorry` warnings in `Scheme.lean`/`Completeness.lean` files unrelated to this task |
| `lake exe checkInitImports` | Exit 0 (the three new `CslibTests/` files, like `BetaSplitRefutation.lean`, do not import `Cslib.Init` and this passes, matching the risk-mitigation note in the plan) |
| `lake lint` | Green, 2m54s; zero warnings attributed to the three new files (grepped explicitly) |
| `lake exe lint-style` | Green, no output |
| `lake test` | Green, 50.7s; visibly built `CslibTests.MinProbe` (3.3s), `CslibTests.WitnessProbe` (3.4s), `CslibTests.WitnessSearch3` (3.9s) -- total added `lake test` wall-time ~10.6s, close to the plan's ~12s estimate |
| `lake exe mk_all --module` (idempotent re-run) | "No update necessary" -- confirms `lake exe mk_all --check` (CI's actual gate) would pass |
| `lake shake --add-public --keep-implied --keep-prefix` | All findings are pre-existing, in `Cslib/` files outside this task's `CslibTests/`-only scope; zero findings for the three new files |
| Zero-debt grep (`sorry`, `axiom`, bare `#eval!`, vacuous `:= True`/`:= trivial`) | Clean -- the only `#eval!` string matches are inside prose describing the historical scratch files, not live commands |
| **Negative control** | Perturbed `WitnessProbe.lean`'s `check [(1,0)]` expected string from `some (true, false)` to `some (true, PERTURBED)`; `lake build CslibTests.WitnessProbe` failed exactly as expected (`❌️ Docstring on #guard_msgs does not match generated message`); reverted and rebuilt green. Confirms the assertions are load-bearing. |

`git status` after the full pipeline shows changes confined to `CslibTests/WitnessProbe.lean`,
`CslibTests/WitnessSearch3.lean`, `CslibTests/MinProbe.lean`, `CslibTests.lean`, and this task's
`specs/` artifacts -- no `Cslib/` source file was edited by this task. (An unrelated, concurrently
running session was independently editing `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
during this task's execution; that file's changes are not part of this task's diff and were left
untouched.)

Zero new sorries, zero new axioms, zero `#eval!`, zero vacuous definitions.

## Findings

- **`Minimal.Soundness` import was dead**: `WitnessSearch3.lean`'s scratch original imported
  `Cslib.Logics.Propositional.Tableau.Minimal.Soundness` alongside the three shared imports.
  Building `CslibTests/WitnessSearch3.lean` without it succeeded, confirming the import was
  unnecessary (as the research report's correction predicted, by analogy with `MinProbe.lean`,
  which never imported it).
- No semantic drift in any of the 25 promoted assertions (see Reconciliation Findings above).

## Follow-ups Flagged (NOT edited -- outside this task's `CslibTests/`-only `file_scope`)

1. `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` currently carries two stale
   "not CI-protected" / "not promoted into `CslibTests/`" provenance citations. **Line numbers
   have already drifted** from the plan's anchors (7868/7882) to their current locations (as of
   this task's final verification pass) at **lines 7954 and 7968** -- located by the quoted
   phrases `"not CI-protected: see the scratch probes"` and `` `WitnessSearch3.lean`, computed,
   not CI-protected `` respectively, per the plan's own caveat that anchors may have moved. Both
   should retarget to `CslibTests/WitnessProbe.lean` (which now also carries the
   `WitnessSearch2.lean` search-space content) and `CslibTests/WitnessSearch3.lean` respectively,
   dropping the "not CI-protected" qualifier.
2. `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (around lines 141-146, in the
   `minimalTableau_complete` docstring) cites the minimal-scheme witness fact inline
   ("`[(1, 0)]` discharges both upward-closure obligations under `isMinimallyClosed`") with no
   filename. It can now cite `CslibTests/MinProbe.lean` by path.
3. The `Minimal.Soundness` import in the scratch `WitnessSearch3.lean` proved dead (see Findings
   above) -- no action needed on the scratch file itself, but noted for completeness since the
   plan asked this to be recorded.

All three are docstring-only edits with no proof/statement changes, and are left for a
follow-up task per the plan's `Non-Goals` and the `file_scope` restriction.

## Files Modified

- `CslibTests/WitnessProbe.lean` (new)
- `CslibTests/WitnessSearch3.lean` (new)
- `CslibTests/MinProbe.lean` (new)
- `CslibTests.lean` (regenerated barrel, three new import lines)
- `specs/602_promote_openbranch_witness_probes_to_cslibtests/plans/01_promote-witness-probes.md` (phase status markers)
