# PR #648 Rebase — Scaffolding

> **This file is verified factual scaffolding, not prose to paste.** Every claim below was
> checked against the live repository, the GitHub review record, or the rebased worktree at the
> time this file was written. It is raw material for a human to write the updated PR description
> and the re-review request from — not text to copy into GitHub or Zulip as-is. Per CSLib's
> adoption of the Mathlib AI policy (see "CONTRIBUTING.md disclosure" below), any GitHub-facing
> text describing this rebase must be human-authored.

## 1. Where the work lives

- Worktree: `/home/benjamin/Projects/cslib-pr648`
- Branch: `rebase/pr648-upstream`
- Base: `upstream/main` at `4bec19fc` (toolchain `v4.34.0-rc1`, Mathlib `de5ce8a9`)
- Rebased commits (7, in order): `c007ac73`, `efcf8d78`, `8d204744`, `2f790a10`, `c06d7623`,
  `829b24eb` (the PR's original 6), plus `49a17094` (this task's `Defs.lean` reconciliation and
  the `Theory.lean` grind fix, both required to make the rebased tree build).
- Diff against the new merge base: exactly 4 files —
  `Cslib/Logics/Propositional/Defs.lean`, `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`,
  `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean`, `references.bib`.
- Status: unpushed. `origin/feat/propositional-v2` (the live PR branch, head `4834be23`) is
  untouched. No push, no `gh pr` write, no Zulip post has been performed by any agent.
- Local CI: all five gates from `upstream/main:.github/workflows/lean_action_ci.yml` pass
  (`lake build --wfail --iofail`, `lake test --wfail --iofail`, `lake exe mk_all --check`,
  `lake exe checkInitImports`, `lake exe lint-style Cslib`). See the implementation summary for
  full command output.

## 2. ctchou's four review bullets — verified dispositions

Review record (verified read-only against the GitHub PR):

| Date | Reviewer | State |
|---|---|---|
| 2026-06-15 | ctchou | CHANGES_REQUESTED |
| 2026-07-06 | thomaskwaring | APPROVED |
| 2026-07-13 | benbrastmckie | COMMENTED ×5 (answering all five inline comments) |

ctchou's review is the only outstanding blocking review. Its four points, verbatim, with
disposition:

| # | ctchou's point (verbatim) | Disposition |
|---|---|---|
| 1 | "I like the idea of adding `\bot` as a primitive." | Supportive from the start, unchanged. Independently backed by Matthew Doty on DPLL grounds (third participant, same thread). |
| 2 | Why both `Semantics/Basic.lean` and `Semantics/Bool.lean`? | Moot — the rebased PR ships no `Semantics/` file at all. `git diff --stat` and a `git grep` for `Semantics/` on the rebased tree both confirm this. |
| 3 | Prefers Avigad's textbook over 1930s German sources for references. | `Avigad2022` added and cited as the **lead** reference in both `Defs.lean` and `NaturalDeduction/Basic.lean` (module docstring + `## References` section in each). The Gentzen entry itself was rewritten to the English Szabo translation (commit `1956d75b`, carried through the rebase as `c06d7623`) — BibTeX type changed from `@article` to `@incollection`, now cites *The Collected Papers of Gerhard Gentzen* (North-Holland, 1969, trans. M. E. Szabo). The 1935 German original is retained only as a `note` field on that entry, not as a separate top-level citation. |
| 4 | "You should definitely coordinate this PR with #607 and #587. #536 is ready to merge, so you should wait for it." | Actionable and now discharged: #536 merged 2026-06-16, and the original PR was already rebased onto it. #607 merged 2026-08-03 and **this task's rebase performs that coordination** — the reconciliation in `Defs.lean` is precisely absorbing #607's `Operators.lean` typeclass mechanism. #587 is a stale draft, untouched since 2026-06-17; its `Connectives.lean` typeclass module was superseded by #607's `Cslib/Foundations/Logic/Operators.lean`, which this rebase now imports directly. |

**Bottom line**: there is no standing technical opposition to primitive `bot` on the review
record. ctchou's own first bullet endorses it.

## 3. Reviewer-visible semantic changes (itemize, don't leave buried in the diff)

These two items are not obvious from a raw diff and should be called out explicitly in the PR
description and/or re-review request:

### 3a. `IPL` keeps its identifier but changes meaning

| | Upstream `main` (pre-rebase) | This PR (post-rebase) |
|---|---|---|
| `Theory.IPL` | `Set.range (Proposition.imp ⊥ ·)` — i.e. `{⊥ → A \| A}`, one axiom schema per proposition | `∅` — the empty theory |
| Where does "ex falso" live? | As a *theory axiom schema* (`efq_mem_ipl`) | As a *primitive inference rule* (`Derivation.efq`, a constructor of `Theory.Derivation`) |

Both encode intuitionistic propositional logic; the difference is architectural (axiom-schema vs.
primitive rule), not semantic. This PR's design was reached via a Zulip compromise (see §4) and
is the design ctchou's bullet #1 already endorsed.

### 3b. Five public API removals

The rebase deletes five identifiers present on this fork's `main` (which had drifted back to a
`[IsIntuitionistic T]`-gated design — explicitly out of scope for this PR, see the task's
non-goals):

- `Theory.MPL`
- `Theory.intuitionisticCompletion`
- `Theory.IsIntuitionistic`
- `Theory.efq_mem_ipl`
- `instInhabitedOfBot`

**Safety argument** (blast-radius evidence, Phase 6 of the implementation plan): on the rebased
tree, `git grep -l "Cslib.Logics.Propositional" -- '*.lean'` returns exactly three files —
`Cslib.lean` (the import manifest) and the two `NaturalDeduction/` files this PR already rewrites.
No other file in the library references the `Propositional` namespace, so none of the five removed
identifiers has an external caller outside files already being changed by this PR.

## 4. Standing-approval record

- thomaskwaring **APPROVED** 2026-07-06, after a Zulip compromise reached 2026-06-28 ("if we are
  going to have `bot` as a primitive, we should also have `efq`"), implemented 2026-06-29.
- All five of thomaskwaring's inline review comments were answered and marked resolved on
  2026-07-13.
- The PR body's original hedge ("open to reverting to `impl` if reviewers prefer it") can be
  dropped: #607 landed the `imp` naming (not `impl`), and upstream's `Modal/Basic.lean` now
  itself uses `Proposition.imp` + the `HasImp` typeclass — so `imp` is the naming convention
  the rest of the library has converged on independently.
- This approval **stands** and should be cited in the updated PR description, not re-litigated.

## 5. CONTRIBUTING.md disclosure (human decision required)

CONTRIBUTING.md § "The role of AI" requires:

> If you use artificial intelligence [...] please explain this in the PR description. Explain
> which tool(s) you used and how you used it.

This rebase (toolchain/Mathlib bump absorption, conflict resolution, `Defs.lean` reconciliation
against `Operators.lean`, CI verification) was performed with AI assistance (Claude Code). **A
human must decide the exact wording of this disclosure and add it to the PR description** — this
scaffolding file does not draft that text, per the hard constraint that GitHub-facing prose must
be human-authored.

## 6. Two decisions left to the user

1. **Constructor order**: keep the approved order `atom, bot, imp, and, or` (recommended).
   Reordering would churn match arms in `subst`, `weak`, `subs`, `substAtom` across
   `NaturalDeduction/Basic.lean`, which otherwise applies untouched by this rebase. (A separate
   task exists for switching connective notation from `infix` to `infixr` at upstream precedences
   — sequenced to run *after* this rebase lands, so as not to pollute the approved diff.)
2. **Wording of the re-review request to ctchou**: this file provides the four itemized
   dispositions (§2) as raw material; a human should write the actual Zulip/GitHub message.
