# Handoff: Cycle 16 (Phase 4 regression fix + Phase 5 dispatch)

- **Task**: 575
- **Session**: sess_1785175989_6e99ab
- **Scope of this dispatch**: two items, in order — (1) resolve the `lake shake`
  import-minimization drift flagged (not fixed) at cycle 15's close, since it falsified Phase 4's
  closed "clean" criterion; (2) continue Phase 5 (suppression audit) with remaining budget. Phase
  7's two carried-forward blockers were NOT re-investigated (see below, carried forward verbatim).

## Item 1: Phase 4 `lake shake` regression — RESOLVED

A live `lake shake --add-public --keep-implied --keep-prefix Cslib` found **23 files** flagged
(not the ~15 cycle 15 estimated). Gated each individually through
`git cat-file -e upstream/main:<path>`:

- **12 upstream-shared, confirmed out of scope, unchanged**: `Algorithms/Lean/TimeM.lean`,
  `Computability/Machines/Turing/{MultiTape/Deterministic,SingleTape/NonDeterministic}.lean`,
  `Foundations/{Data/StackTape,Relation/Defs,Relation/Confluence,Control/Monad/Free,
  Data/HasFresh}.lean`, `Languages/{CCS/Basic,CombinatoryLogic/Defs,
  LambdaCalculus/LocallyNameless/Untyped/LcAt}.lean`, `Logics/Modal/Basic.lean`. Routed to a
  future upstream PR.
- **11 local-only, fixed** (11 individual commits, each rebuilt file + downstream importers):
  `Foundations/Logic/Metalogic/{Chronicle/SinceSeedConsistency,ListDeduction,
  ProofSystemMorphism}.lean`, `Foundations/Logic/Tableau/SignedFormula.lean`,
  `Foundations/Logic/Theorems/BigConj.lean`, `Foundations/Order/HilbertAlgebra/
  DiegoEmbedding.lean`, `Logics/Modal/Metalogic/Constructive/Forcing.lean`,
  `Logics/Propositional/Semantics/Algebra/{PointedBrouwerian,BrouwerianBot,
  NonemptyLowerSet}.lean`, `Logics/Temporal/Tableau/TimeOrdering.lean`.

One non-mechanical case: `ProofSystemMorphism.lean`'s shake suggestion was to *remove*
`public import Mathlib.Tactic.SetNotationForOrder`. Rejected — the file's own inline comment
documents that import as required for the public `Deriv.weak` constructor's `⊆` elaboration.
Annotated `-- shake: keep` instead of deleting it, and added the tool's separate
`Mathlib.Tactic.Attr.Core` suggestion alongside it.

Full CI pipeline (`lake build --wfail --iofail`, `checkInitImports`, `lint-style`,
`mk_all --module`, `lake test`) re-run clean after the fix. `lake shake` repo-wide now reports
exactly the 12 upstream-shared files and nothing else. Phase 4's marker stays COMPLETED, now
empirically re-verified rather than merely re-asserted.

Commits: `1e290783`, `84fee7c8`, `19bea2d3`, `8bce62f4`, `818958da`, `e5e0f532`, `047ecc0c`,
`c5a30696`, `ea5915a8` (9 commits — one covered the tightly-coupled Propositional/Semantics/
Algebra 3-file batch, one covered SignedFormula standalone), plus plan-doc commit `bceed851`.

## Item 2: Phase 5 — advanced by 1 file

Processed `Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/XuGuard.lean` (5→0, 1146
lines, commit `c0a11b8d`) — the smallest of the 3 files left in the count-5 tier at cycle 15's
close. `style.emptyLine`/`style.setOption` vestigial; `unusedSimpArgs` (1 site) fixed
mechanically; `style.longLine` (~59 sites, across two structurally mirrored `lemma_2_7`/
`lemma_2_8` proof blocks) fixed by rewrapping; `flexible` (4 declarations — the same `l27`-family
names already seen in `Splitting.lean`, cycle 15) narrowed to declaration-scoped `set_option`
lines. Ratchet re-baselined in the same commit.

Only 1 file was completed this cycle (not the full remaining budget) because item 1 took
priority per the delegation's explicit ordering.

## Numbers

- Phase 5 suppression-audit progress: 213 → 214 sites audited cumulative (34 files fully
  processed cumulative)
- Ratchet (blanket suppressions, repo-wide): 228 → 223
- Local-only in-scope remaining: 209 (223 minus the 14 upstream-carved-out)
- Count-5 tier remaining: 2 files, both `ChronicleConstruction.lean` (`Temporal/Metalogic/
  Chronicle/`, 1435 lines; `Bimodal/Metalogic/BXCanonical/Chronicle/`, 1532 lines)
- Count-6 tier: unchanged, 6 files (see Phase 5's cycle-16 entry in the plan for the full list)

## Plan file updates

- RESUME HERE: new cycle-16 entries for both items, "pick up cold" instructions updated to
  include a `lake shake` sanity check, baseline table's `lake shake` and `set_option linter.*`
  rows updated.
- Phase 4: new addendum documenting the regression investigation and fix (commit `bceed851`).
- Phase 5: new cycle-16 sub-entry with XuGuard.lean's category breakdown, a new safety finding
  (mirrored-block `Edit` `replace_all` caution), and a refreshed resume point (commit `e21115b8`).

## Verification (full CI pipeline, run at cycle end)

- `lake build --wfail --iofail`: exit 1, exactly the 5 documented baseline sorry warnings
  (`FrameSoundness.lean:1252`, `Intuitionistic/Scheme.lean:570,2583`,
  `Intuitionistic/Completeness.lean:124`, `Minimal/Completeness.lean:118`), zero others
- `lake exe checkInitImports`: clean
- `lake exe lint-style`: clean, no output
- `lake shake --add-public --keep-implied --keep-prefix Cslib`: exactly the 12 upstream-shared
  files, zero local-only findings
- `lake exe mk_all --module`: "No update necessary"
- `lake test`: exit 0, same 5 baseline sorry warnings plus the one pre-existing unrelated
  `backward.privateInPublic` warning in `CslibTests/FreeMonad.lean`
- Vacuous-def grep: unchanged, 1 pre-existing false positive (`Computability/URM/Basic.lean:92`)
- Axiom count: unchanged, 26

## Carried forward verbatim — NOT re-investigated this dispatch (per explicit instruction)

Both are settled and await a human decision, not further investigation:

1. **Phase 7 item 1**: `NOTATION.md`'s drafted "Logic notation scoping" section cannot land
   locally because the file is confirmed byte-identical to `upstream/main` (out of scope under
   the upstream-exposure carve-out). Needs a human decision: (a) route as a small upstream PR
   (recommended), or (b) explicitly authorize editing this specific shared docs file locally as
   an exception to the carve-out.
2. **Phase 7 item 2**: the 5 "stale NOTE: block" deletions were found NOT stale in a prior
   cycle's investigation and deliberately left in place; still flagged for explicit user
   sign-off on that judgment call.

## Next steps for a cold resume

1. Confirm baseline per the plan's "To pick Phase 5 up cold" step 1 (3 commands: `--wfail`,
   `lake test`, `lake shake`).
2. Pick either `ChronicleConstruction.lean` (both ~1450-1550 lines, similar size) and apply the
   established Phase 5 method.
3. Once both are done, re-derive the worst-offender list fresh — the count-4 tier (~15+ files)
   becomes the new frontier; no cached tier framing survives past that point.
4. Surface the two Phase 7 blockers above to the user for a decision — they do not block further
   Phase 5 progress but do block Phase 7's own final close.
