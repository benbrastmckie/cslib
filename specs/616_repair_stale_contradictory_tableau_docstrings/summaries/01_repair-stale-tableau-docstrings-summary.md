# Implementation Summary: Repair Stale and Self-Contradictory Tableau Docstrings

- **Task**: 616
- **Status**: Implemented
- **Plan**: specs/616_repair_stale_contradictory_tableau_docstrings/plans/01_repair-stale-tableau-docstrings.md
- **Report**: specs/616_repair_stale_contradictory_tableau_docstrings/reports/01_repair-stale-tableau-docstrings.md

## Scope

DOCUMENTATION ONLY. No `.lean` proof term, statement, or definition was changed. Verified via
`git diff` (only comment/docstring hunks), a full `lake build` (3325 jobs, green), and
`CslibTests/` left untouched.

## Files Modified

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean`

## Phases Completed

1. **Part 1**: Retargeted the `IFimpAccess`-refutation witness citation in
   `openBranch_countermodel`'s docstring from `WitnessProbe.lean` (off-target by kind and by
   line) to `BetaSplitRefutation.lean`'s `fimpWitnesses`/`branchesAgree`/raw-edge-list
   assertions. Kept the frame-adequacy table and "REFUTED" verdict verbatim, per the report's
   machine-verified authoritative-verdict finding. Fixed both sites (`:9603-9611`, `:9732-9733`).
2. **Part 2(a)(b)**: Re-tensed the copy-channel-removal and `truthLemma`-sorry paragraphs as
   PRE-REPAIR historical, noting the later reinstatement/discharge. Left the verbatim historical
   quotation intact.
3. **Part 2(c)(d)(e)**: Fixed "not yet proved" (now proved) and "deferred to Phase 6" (landed as
   `IAugMembers_persist`) stale claims; narrowed the `Expansion.lean` world-boundedness directive
   so `IAllUniv` is no longer listed among refuted items (it is threaded and discharged).
4. **Part 2(f)(g)**: Dropped the self-contradictory `sorryAx` parenthetical in
   `Minimal/DecisionProcedure.lean`; replaced the dangling task-number citation ("317") in both
   decidability files with the durable anchor already present in their own later prose, per
   `no-task-references-in-deliverables.md`.
5. **Part 3(h)(i) + sibling S1**: Fixed the false attribution crediting dead raw-frame lemmas
   with the live upward-closure conjuncts (the live route is `hpersAug` over the augmented
   frame); corrected two parenthetical attributions implying `minimalTableau_complete` routes
   through `minOpenBranch_countermodel` (it does not); fixed the identical false dependency at
   sibling S1.
6. **Part 4 + siblings S2-S4**: Fixed ~30 stale self- and cross-reference line-number citations
   across `Scheme.lean` and `Rules.lean` cross-references (including a T-or/F-and prose label
   swap); fixed the "11th conjunct" -> "7th conjunct" numbering contradiction; fixed the
   duplicated off-target `Expansion.lean:462-463` citation (S4) for a historical `intFuel`
   formula no longer present under that name. For citations the report flagged as wrong but
   could not pin an exact correct target, applied the report's own "keep the name, drop the
   number" convention.
7. **Optional, deferred**: `FmpMeasure.lean` citations (report Section 5.5) — explicitly
   optional per the delegation's committed scope; not attempted.

## Plan Deviations

- Investigated two defects beyond what the report explicitly resolved: the `Expansion.lean:
  462-463` fuel-formula citation (S4) and the Option-B-unsound `Expansion.lean:515-516`
  citation both point to content that does not exist anywhere in `Expansion.lean` under any
  name (a historical "intFuel" exponential formula, since superseded by `intFuelExt`, and an
  unrecorded "Option B" finding respectively). Fixed both with factual, non-inventive notes
  rather than guessing replacement line numbers.
- The `:250`/`:3272`/`:7058`/`:485-533` Scheme.lean self-reference cluster, which the report
  flagged as wrong but left unresolved (empty "correct target" column), was fixed via the
  report's own Section 8 recommendation: name- or section-heading-based references replacing
  the broken numbers.

## Verification

- `git diff -U0 -- Cslib/` statement-invariance check: zero lines matching a declaration
  keyword (`lemma`/`theorem`/`def`/`instance`/`structure`/`inductive`) across all six files.
- `lake build` (full project): 3325 jobs, success. Only pre-existing, out-of-scope warnings
  (unrelated files/lines) remain.
- `lake exe checkInitImports`: pass.
- `lake lint`: pre-existing warnings elsewhere in the repo; zero in the six modified files.
- `lake exe lint-style`: pass.
- `lake test`: pass, exit 0. `CslibTests/` untouched (`git diff` empty for that tree).
- `lake exe mk_all --module`: no update necessary.
- `lake shake`: zero import-minimization suggestions for the six modified files.
- No `sorry` introduced (compiler-verified: zero "declaration uses sorry" warnings in a fresh
  scoped build of all six files); no new `axiom` declarations (diff-verified); no vacuous
  definitions.
- Task-number lint: the in-scope violation is fixed and verified absent. Pre-existing,
  out-of-scope violations remain under `.memory/**` (unrelated to this task's file_scope).

## AI Tools Used

This task was implemented with the assistance of Claude Code (Anthropic). The AI tool was used
for reading the research report, locating each flagged citation/claim in the live source via
grep and targeted reads, drafting the corrected docstring text, running the CSLib CI
verification pipeline, and drafting this summary. All `.lean` docstring text was reviewed for
accuracy against the live source and test files before being written.
