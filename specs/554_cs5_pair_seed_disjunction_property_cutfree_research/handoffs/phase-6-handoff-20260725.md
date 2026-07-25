# Task 554 Continuation Handoff — After Phase 6

**Date**: 2026-07-25
**Session**: sess_1785007897_038307_554
**Plan**: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`

## State

Stage A (Phases 1–5, statement repair + route closure) and Phase 6 (Stage B's first phase,
nested sequent syntax) are COMPLETE and committed. 6/32 phases done. All commits are on `main`,
whole-project `lake build` / `lake test` / `lake lint` / `lake exe checkInitImports` green at
every commit. Invariants held: `Cslib/` bare-`sorry` count still exactly 5, axiom count still
26 (unchanged), zero new `sorry`/`axiom` introduced by any of this session's commits.

## Commits This Session

- `b5f13c0e` — task 554: mark Phase 4 COMPLETED (stale marker from a prior session's recovery
  commit c7d2d87b), begin Phase 5
- `ad0f25eb` — task 554 phase 5: close the product-model route (machine-checked). New file
  `Cslib/Logics/Modal/Metalogic/InterSystem/CS5ToIS5.lean`.
- `8c3c944f` — task 554 phase 6: nested sequent structures and the `fm` translation. New file
  `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Syntax.lean`.

## Next Action

Resume at **Phase 7: Contexts, hole filling, and output pruning** (Stage B, second phase).
Depends on Phase 6 (done). Files to modify: extend `Nested/Syntax.lean` or create
`Nested/Context.lean` if the file would exceed ~350 lines (Phase 6's `Syntax.lean` is currently
~185 lines, so there is room, but Phase 7 adds a fair amount — use judgement at implementation
time and record the choice, per the plan's own file-placement note).

Phase 7 needs: `OutputCtx := List NestedLhs` (Observation 2.2, eq. (2.2)); `InputCtx` as the
triple `⟨Γ' : OutputCtx, Λ : OutputCtx, Π : Proposition⟩` (eq. (2.3)); hole-filling for both
context kinds at each admissible filler type; output pruning `Γ⇓{ }` (Definition 2.3); basic
equational lemmas (filling with `∅`, nesting/associativity of filling, `(Γ⇓){∆}` vs `Γ{∆}`).

## Literature Access — Use the Recovered PDF Directly, Not the Search Index

The `literature-search.sh --include-unverified` index chunks are `unverified_summary`
fidelity and can garble dense math (confirmed this session — the FTS5 index also chokes on
punctuation like periods in queries). **Better approach, used successfully this session**: read
the recovered source PDF directly with the `Read` tool's `pages` parameter, e.g.:

```
Read({file_path: "~/Projects/Literature/.sources-recovered/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics.pdf", pages: "5-8"})
```

**Cross-check with `pdftotext -layout` too** — it catches transcription slips the vision-render
alone might introduce, but it has its own gap: it silently drops the `□` (box) glyph everywhere
in this PDF's font encoding (confirmed: `♦`, `⊃`, `∧`, `∨`, `⊤` all extract fine, `□` extracts as
nothing). When cross-checking a formula against `pdftotext` output, mentally restore a `□`
wherever the source's direct-render shows one and the `pdftotext` text has a suspiciously
box-free parenthesized group. Command used:

```bash
pdftotext -f <page> -l <page> -layout ~/Projects/Literature/.sources-recovered/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics.pdf -
```

Page 5 (of the source PDF) has eq. (2.1), the `fm` clauses, Example 2.1, Observation 2.2 (eq.
2.2, 2.3), and Definition 2.3 — i.e. everything Phase 7 needs. Page 6 has Figure 2 (System
`NCK`), needed later for Phase 9. Already read and transcribed this session; re-reading these
same pages for Phase 7 should be quick confirmation, not fresh discovery.

## One Documented Discrepancy (Not a Blocker, Just Know About It)

Example 2.1's printed "corresponding formula" for `Γ₁{Δ₁}` informally simplifies an innermost
`⊤ ⊃ B` subformula to `B` (a valid propositional identity, but not one the `fm` clauses
themselves perform). The landed Lean `example` in `Nested/Syntax.lean` computes the literal,
unsimplified `fm` output and documents this in a comment. This is very likely just authorial
informality in the worked example, not a defect in the stated formal system — the `fm` clauses
themselves (eq. after (2.1)) are unambiguous and were followed literally. Do not "fix" this by
changing the `fm` definition; the definition is correct as transcribed.

## Do Not Touch

`Cslib/Logics/Modal/Tableau/` — another concurrent session owns those files (confirmed
uncommitted changes to `LoopChecking.lean` present throughout this session, never staged or
touched). Stage only `Cslib/Logics/Modal/Metalogic/Constructive/` (and this session's new
`InterSystem/CS5ToIS5.lean`) plus the task directory; never a repo-wide `git add`.

## Scale Reminder

32 phases total, 86-hour original estimate (Stage A 9.5h actual across ~5 sessions including
this one; Stage B 7.5h estimate, C 5.5h, D 8h, E 5h, F 28h, G 22h — F and G estimates carry wide
error bars per the plan). This is a multi-session undertaking. Each phase should still be
committed independently and cleanly per the Commit-Per-Green-Substep Mandate — do not batch
multiple phases into one commit, and do not leave a phase half-done uncommitted at session end.
