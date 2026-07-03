# Research Report: Fix and stack PR #662 on PR #648 (rebase, decouple, cherry-pick task-472)

- **Task**: 475 — fix_and_stack_pr_662_on_648
- **Type**: cslib (git/PR orchestration + formal-Lean)
- **Session**: sess_1783038723_6ac05b
- **Date**: 2026-07-02
- **Status**: researched
- **Agent**: cslib-research-agent
- **Dependencies**: tasks 468 (resync), 469 (Connectives decision), 472 (model-class Equiv restore — COMPLETED on `main`)
- **Method**: read-only `git`, read-only `gh`, reading of 468/469/472 artifacts. **No git state was mutated. No `lake build` was run** (see §9 CI baseline for why and what must be verified during implementation).

## Executive Summary

- **Ground truth confirmed**: PR #662 (`feat/modal-formula-primitives`) targets `base=main`
  (i.e. `leanprover/cslib:main` = `upstream/main`), is **10 commits behind** current
  `upstream/main`, and is **NOT a descendant of** PR #648 (`feat/propositional-v2`). The two
  branches diverge at `e0573fbc` (an old upstream commit). #662 ships **stale copies** of #648's
  three propositional files reflecting the pre-refactor MPL/`IsIntuitionistic`/`intuitionisticCompletion`
  design, whereas #648 head has moved to the **primitive `efq`** design.
- **The modal layer is cleanly separable**: `Cslib/Logics/Modal/Basic.lean` imports
  `Cslib.Foundations.Logic.Connectives`, `InferenceSystem`, `Relation.Defs`, `Cslib.Init` and
  Mathlib — but **does NOT import `Cslib.Logics.Propositional.*`**. So #662's genuine modal
  contribution has no functional dependency on the propositional files it currently re-ships. This
  is the structural fact that makes "stack on #648, drop the propositional changes" viable.
- **The task-472 fix is a near-clean cherry-pick.** It is commit **`9c5cbd08`** on local `main`
  (only file of interest: `Cslib/Logics/Modal/LogicalEquivalence.lean`). The pre-472 base of that
  file on `main` differs from #662's copy by **only 3 lines** — so re-applying the 472 rewrite onto
  the (rebased) #662 branch is expected to apply with minimal/no conflict.
- **`main` already carries #662's `{atom, bot, imp, box}` modal primitives and `Connectives.lean`**,
  so the 472 work was genuinely built over the #662 design (as its summary claims).
- **Connectives.lean decision (task 469)**: deletion is **not viable** (load-bearing; #607 is
  unmerged and lacks `HasBot`/bundles). Recommended: **#662 self-owns `Connectives.lean`** as part
  of its genuine modal contribution and defers the typeclass-layer merge to a joint #607/#662
  coordination — do NOT try to inherit it from #648 (#648 head has removed it) and do NOT delete it.
- **Force-push is the single hard gate**: rebasing both branches and squashing #662 rewrites
  published PR history. Nothing should be pushed without explicit user approval (§11).

## 1. Git / branch state (ground truth)

All hashes verified read-only on 2026-07-02.

| Ref | Tip | Ahead of `upstream/main` | Behind `upstream/main` | merge-base w/ `upstream/main` |
|---|---|---|---|---|
| `upstream/main` | `5c41dcf2` | — | — | — |
| `origin/main` (fork) | `359d8286` | — | **516 behind** (stale; NOT a rebase target) | — |
| `feat/propositional-v2` (local, #648) | `c98c4348` | 5 | 2 | `2772f421` |
| `origin/feat/propositional-v2` (#648 pushed head) | `c9364b65` | 3 | 2 | `2772f421` |
| `feat/modal-formula-primitives` (local, #662) | `3ff6d02d` | 3 | **10** | `e0573fbc` |
| `origin/feat/modal-formula-primitives` (#662 pushed head) | `f46056b9` | 1 | **10** | `e0573fbc` |

Key relationships (all verified with `git merge-base --is-ancestor`):

- `feat/propositional-v2` **is NOT an ancestor of** `feat/modal-formula-primitives` (locally or on
  origin) → **#662 does not contain #648's history**. This is the core defect.
- merge-base of the two feature branches = `e0573fbc` (the old upstream toolchain-bump commit
  `#664` that the modal branch is based on).
- **Local branches are ahead of their pushed PR heads** (unpushed refinement commits):
  - #648: `bbcbef85` (revert binder/naming churn, restore derived rules), `c98c4348`
    (English Gentzen 1935 citation).
  - #662: `93cf984e` (restore grind/simp coverage for derived connectives), `3ff6d02d`
    (attribution, doc language, iff precedence, import pruning).

**Rebase-scope implication**: `feat/propositional-v2` is only 2 commits behind upstream and 5
ahead → a small, low-risk rebase onto `upstream/main`. `feat/modal-formula-primitives` is 10
behind, and the 10 include **Mathlib bumps** (`#694 → mathlib d52d26f`, `#670 → 29af524`,
`#628 → 8589236`) and the `Relation` module split (`#632`) — these are the likely source of any
rebase/adaptation work (see §10 Risks).

## 2. PR metadata (from `gh pr view`, read-only)

| | PR #648 | PR #662 |
|---|---|---|
| Title | feat(Logics/Propositional): five-primitive formula type with primitive bot | feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box} |
| State | OPEN | OPEN |
| `baseRefName` | **`main`** | **`main`** |
| `headRefName` | `feat/propositional-v2` | `feat/modal-formula-primitives` |
| Head repo | `benbrastmckie` (cross-repo fork) | `benbrastmckie` (cross-repo fork) |
| `mergeable` | MERGEABLE | MERGEABLE |
| Pushed commits | 3 (`1a2e2e7e`, `cc44c14d`, `c9364b65`) | 1 (`f46056b9`) |
| URL | https://github.com/leanprover/cslib/pull/648 | https://github.com/leanprover/cslib/pull/662 |

Both PRs target `leanprover/cslib:main` from the `benbrastmckie/cslib` fork. **PR #662's base must
be retargeted to `feat/propositional-v2`** to realize the stack.

## 3. File overlap / divergence

**#662 changeset** (`e0573fbc..feat/modal-formula-primitives`), 10 files:

| File | Category | Lines |
|---|---|---|
| `Cslib/Logics/Modal/Basic.lean` | **genuine modal** | +275/−(part of 275) |
| `Cslib/Logics/Modal/Cube.lean` | **genuine modal** | 1 |
| `Cslib/Logics/Modal/Denotation.lean` | **genuine modal** | 25 |
| `Cslib/Logics/Modal/LogicalEquivalence.lean` | **genuine modal** (target of 472 fix) | 173 |
| `Cslib/Foundations/Logic/Connectives.lean` | **genuine modal** (self-owned typeclass file) | +91 (new file) |
| `Cslib.lean` | **genuine modal** (module registration) | 1 |
| `references.bib` | mixed (modal keys wanted; prop keys inherited from #648) | 8 |
| `Cslib/Logics/Propositional/Defs.lean` | **OVERLAP w/ #648 — DROP** | 107 |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | **OVERLAP w/ #648 — DROP** | 149 |
| `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` | **OVERLAP w/ #648 — DROP** | 91 |

**#648 changeset** (`2772f421..feat/propositional-v2`), 4 files: exactly the three propositional
files + `references.bib`.

**Divergence between the two PR heads on the shared propositional files** (`feat/propositional-v2`
vs `feat/modal-formula-primitives`): `Defs.lean` 53 lines, `NaturalDeduction/Basic.lean` 115 lines,
`NaturalDeduction/Theory.lean` 62 lines, `references.bib` 56 lines. The divergence is substantive
and by design (two different completeness-of-base designs):

- **#648 head** (authoritative): primitive `efq` `Derivation` constructor (11 constructors),
  `abbrev IPL : Theory Atom := ∅`, **no** `MPL`/`IsIntuitionistic`/`intuitionisticCompletion`,
  **no** `Connectives` import.
- **#662 head** (stale): `efq` derived (10 constructors, gated on `[IsIntuitionistic T]`),
  `MPL := ∅`, `IPL := Set.range (imp ⊥ ·)`, `IsIntuitionistic` class + `intuitionisticCompletion`
  present, `public import Connectives` + `PropositionalConnectives`/`HasAnd`/`HasOr` registrations.

**Conclusion**: When #662 is stacked on #648, all three propositional files (and their `references.bib`
propositional keys) must be **dropped from #662 and inherited from #648**. This is task 468's goal,
realized structurally (by rebasing onto #648) rather than by hand-editing #662's copies.

## 4. Modal ↔ Propositional coupling (why the split is safe)

`git show feat/modal-formula-primitives:Cslib/Logics/Modal/Basic.lean | grep import`:

```
public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives      -- self-owned by #662
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Logic.Nonempty
public import Cslib.Foundations.Relation.Defs
```

Modal `Basic.lean` registers `instance : ModalConnectives (Modal.Proposition Atom)` and defines its
own `inductive Proposition {atom, bot, imp, box}`. It **does not import
`Cslib.Logics.Propositional`** — `Modal.Proposition` and `Propositional.Proposition` are distinct
types. Therefore dropping #662's propositional-file edits does not break the modal files at the
import level. **Caveat**: this must still be confirmed by an actual build once stacked on #648 head,
because #648 head removed `Connectives.lean` and the `PropositionalConnectives` registration — if
any modal proof implicitly relied on a `Propositional`-side instance re-export, it would surface
only at build time (§10 R2).

## 5. Task-472 fix location and cherry-pick feasibility

- **Fix commit**: `9c5cbd08` on local `main` — "task 472: complete implementation". It restores
  the model-class-parametric `Proposition.Equiv (S : Set (Model World Atom))` + `LogicalEquivalence`
  framework integration and removes the standalone `LogicallyEquivalent`, entirely within
  `Cslib/Logics/Modal/LogicalEquivalence.lean` (153 lines changed in the Lean file). The commit
  **also touches specs artifacts** (`plans/…`, `summaries/…`, `TODO.md`, `state.json`) — those must
  **not** be carried onto the PR branch.
- **Recommended cherry-pick technique** (Lean file only): `git cherry-pick -n 9c5cbd08` then keep
  only the Lean file (`git restore --staged --worktree :/` for the specs paths), **or** apply
  surgically: `git show 9c5cbd08 -- Cslib/Logics/Modal/LogicalEquivalence.lean | git apply`.
  Since #662 is being squashed to one commit anyway, the practical route is to just checkout the
  finished file: `git checkout main -- Cslib/Logics/Modal/LogicalEquivalence.lean`.
- **Conflict risk = low**. The pre-472 version of `LogicalEquivalence.lean`
  (`9c5cbd08^:…/LogicalEquivalence.lean`) differs from #662's head copy by **only 3 lines**
  (`git diff --stat` = 3 insertions / 3 deletions). So `main`'s finished file is `main`'s pre-472
  state (≈ #662 head) plus the 472 rewrite; transplanting it onto the rebased #662 branch is
  expected to be near-clean. The 3-line delta is the only place a manual reconcile might be needed
  (likely a header/import/notation-open line that shifted between #662 and `main`).
- **Verified**: `main` carries the same `{atom, bot, imp, box}` `Modal.Proposition` primitives and
  the self-owned `Connectives.lean` as #662, so the 472 work was legitimately authored against the
  #662 design (its summary's claim holds).

## 6. Connectives.lean typeclass question (task 469)

From `specs/469_.../reports/01_drop-connectives-typeclass-layer.md`. Verified this run: **#648 head
has NO `Connectives.lean`; #662 and `main` HAVE it.**

Three options and tradeoffs:

| Option | What it means | Feasibility / tradeoff |
|---|---|---|
| **A. Self-own in #662** (recommended) | Keep `Foundations/Logic/Connectives.lean` inside #662 as part of its own contribution; state clearly it is introduced by #662 (not inherited from #648). Defer the #607-vs-#662 typeclass-hierarchy merge to a later joint coordination. | **Viable now.** Zero-debt. Keeps #662 self-contained and reviewable. The connective file is genuinely #662's (it provides `HasBox`/`ModalConnectives` the modal files need). |
| **B. Decouple** (inline notation, drop the file) | Replace `ModalConnectives`/`PropositionalConnectives` registrations with direct `def`/`abbrev` + per-type scoped notation in Modal/Basic (pre-typeclass style). | Possible but larger diff and re-proof surface; loses the polymorphic layer #662 intentionally introduced. Only worth it if reviewers reject a new Foundations typeclass file. |
| **C. Coordinate with #607** (`@chenson2018`/`@fmontesi`) | Rebase #662's connective needs onto #607's `Operators/` hierarchy once merged. | **Blocked**: #607 is OPEN/BLOCKED, unmerged, and lacks `HasBot`, bundle classes, and uses `HasImpl.impl` (vs `HasImp.imp`) with the opposite Modal primitive set (`{not, and, diamond}`). Cannot be done today. |

**Recommendation for task 475**: take **Option A** — #662 self-owns `Connectives.lean` as its
genuine modal contribution; do not delete it and do not attempt to inherit it from #648. Surface the
#607 coordination as an open review item in the PR body + Zulip reply (not a code change now). This
is a **decision point that should be confirmed with the user** (§11 D4).

## 7. Dependency task summaries (468 / 469 / 472)

- **Task 468 (resync)** — `reports/01_resync-pr-662-with-648-head.md`. Concluded #662 embeds the
  pre-refactor propositional design; authoritative reference is #648 head `c9364b6` (NOT `main`,
  which predates #648). Gave a precise 3-file + `references.bib` reconciliation recipe and flagged
  the `Connectives.lean` question as separable and gating. **For 475, this hand-edit recipe is
  superseded by the cleaner "rebase #662 onto #648 and drop the propositional files" approach** —
  same end state, less manual risk. 468's file-level facts remain the divergence ground truth.
- **Task 469 (Connectives)** — see §6. Concluded deletion is BLOCKED; recommended Interpretation A
  (self-own / decouple on the PR branch, coordinate #607 separately).
- **Task 472 (model-class Equiv restore)** — **COMPLETED on `main`** (commit `9c5cbd08`). Restored
  parametric `Proposition.Equiv S` + `LogicalEquivalence` instance in Modal/LogicalEquivalence.lean,
  removed standalone `LogicallyEquivalent`, CI green, zero-debt (only 3 foundational axioms). This
  is the artifact that must be transplanted onto the finalized #662 branch (§5).

## 8. #662 slimming target (per @fmontesi "one at a time")

The finalized #662 should contain **only** its genuine modal contribution:

- `Cslib/Logics/Modal/Basic.lean`
- `Cslib/Logics/Modal/Cube.lean`
- `Cslib/Logics/Modal/Denotation.lean`
- `Cslib/Logics/Modal/LogicalEquivalence.lean` (with the task-472 fix applied)
- `Cslib/Foundations/Logic/Connectives.lean` (self-owned, Option A)
- `Cslib.lean` (module registration for the four modal modules)
- `references.bib` (**modal keys only**; propositional keys inherited from #648 — de-dup on merge)

Everything propositional is dropped and inherited from #648. Preserve the stated design rationale in
the code/PR body: **box primitive** (necessitation as a pure rule), **diamond derived** as
`¬□¬`, `HasBox`/`ModalConnectives`, **K/T/B/4/5/D proofs via explicit `simp only [Satisfies]` +
`intro`** (not `grind`), and the **classical-modal restriction** with `HasDia` deferred for IK/CK.

## 9. CI / build baseline

CSLib CI that must pass (per extension manifest): `lake build`, `lake test`, `lake exe
checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`
(plus `lake lint` env-linters, run weekly not in PR CI but worth honoring).

- **Not run this research pass** (deliberately): a full `lake build` is ~3,000+ jobs and the target
  states (rebased branches) do not yet exist, so a pre-rebase build would not answer the real
  question. The task-472 summary records **CI fully green for `main`'s state** (`lake build` 3189
  jobs, `lake test`, `checkInitImports`, `lint-style` all pass; `shake` flags only pre-existing
  unrelated files; zero sorries/axioms).
- **What the plan MUST verify by build** after each rewrite step: (a) rebased
  `feat/propositional-v2` builds on current `upstream/main` (mathlib bump adaptation); (b) the
  slimmed, stacked #662 builds on top of #648 head — specifically that dropping #662's
  `Propositional/Defs.lean` (which registered `PropositionalConnectives`) does not break any modal
  proof; (c) `checkInitImports` / `lint-style` / `shake` clean on the final #662 tree.

## 10. Recommended ordered strategy (git-command level, DRY-RUN until §11 gates)

> All steps below are **local** and reversible until a `push --force-with-lease`. Create safety
> backups first. **No push happens without §11 approval.**

**Step 0 — safety net (no approval needed, local only)**
```
git fetch upstream
git branch backup/648-pre-rebase feat/propositional-v2
git branch backup/662-pre-rebase feat/modal-formula-primitives
git tag pre-475-472fix 9c5cbd08          # pin the task-472 fix commit
```

**Step 1 — rebase #648 onto current upstream/main** (5 commits, 2 behind → small)
```
git switch feat/propositional-v2
git rebase --onto upstream/main 2772f421 feat/propositional-v2
# resolve any mathlib-bump conflicts; then:
lake exe cache get && lake build && lake test && lake exe checkInitImports && lake exe lint-style
```

**Step 2 — build the finalized #662 branch stacked on #648** (recommended: rebuild the modal
contribution as a single clean commit on top of #648, rather than replaying #662's stale history)
```
git switch -c feat/modal-formula-primitives-v2 feat/propositional-v2   # start from rebased #648 head
# bring in ONLY the genuine modal contribution from the old modal branch:
git checkout feat/modal-formula-primitives -- \
  Cslib/Logics/Modal/Basic.lean \
  Cslib/Logics/Modal/Cube.lean \
  Cslib/Logics/Modal/Denotation.lean \
  Cslib/Logics/Modal/LogicalEquivalence.lean \
  Cslib/Foundations/Logic/Connectives.lean \
  Cslib.lean
# apply the task-472 fix (finished file from main; near-clean per §5):
git checkout main -- Cslib/Logics/Modal/LogicalEquivalence.lean
# merge modal-only references.bib keys into #648's references.bib (manual/de-dup)
# then verify:
lake build && lake test && lake exe checkInitImports && lake exe lint-style
git shake --add-public --keep-implied --keep-prefix   # confirm modal files not newly flagged
git add -A && git commit    # single clean commit (§11 will approve the message)
```
*(Alternative to Step 2: `git rebase --onto feat/propositional-v2 e0573fbc
feat/modal-formula-primitives` then `git rm` the three propositional files and reconcile — but this
replays stale history and the `Connectives`-drop conflict; the checkout-and-recommit route above is
cleaner and matches the "squash to a single commit" requirement.)*

**Step 3 — retarget + push (GATED, §11)**
```
# after user approval only:
git push --force-with-lease origin feat/propositional-v2
gh pr edit 662 --repo leanprover/cslib --base feat/propositional-v2
git push --force-with-lease origin feat/modal-formula-primitives-v2:feat/modal-formula-primitives
gh pr edit 662 ...   # update body (§8, correct the stack description)
```

**Step 4 — PR body correction + Zulip reply** (§11 D5, D6). Correct #662's body to describe the
stack-on-#648 relationship, the box-primitive/diamond-derived design, the self-owned
`Connectives.lean`, and the deferred `HasDia`/#607 coordination. Draft a Zulip reply to @fmontesi
(CSLib > Modal Logic) that takes his points one at a time (PR size → now slimmed to modal-only
stacked on #648) and offers to join a CSLib online meeting (he returns 23 July). Task 474 already
drafted CSLib-meeting Zulip replies — reuse that draft as a base.

## 11. Decision points requiring explicit user approval

| # | Decision | Why it needs approval |
|---|---|---|
| **D1** | **Force-push `feat/propositional-v2`** (rewrites PR #648 published history) | Destructive/irreversible on the remote; per git-workflow rules force-push is never done without explicit request. |
| **D2** | **Force-push the rebuilt #662 branch** (squash to one commit, rewrites PR #662 history) | Same; also drops #662's existing single pushed commit `f46056b9`. |
| **D3** | **Retarget PR #662 base `main → feat/propositional-v2`** via `gh pr edit` | Changes the PR contract; reviewers see a different diff. |
| **D4** | **Connectives.lean = Option A (self-own in #662)** vs decouple vs #607-coordination | Design/maintainer-facing choice (task 469); affects diff size and review. Recommended A. |
| **D5** | **Final squashed commit message + corrected PR #662 body text** | User authors the public narrative. |
| **D6** | **Sending the Zulip reply to @fmontesi** | Outbound public communication. |
| **D7** | Whether to also fold the unpushed local refinements (`bbcbef85`/`c98c4348` on #648; `93cf984e`/`3ff6d02d` on #662) into the pushed heads | They are local-only improvements not yet on the PRs; user should confirm inclusion. |

## 12. Risks & mitigations

- **R1 — Mathlib-bump rebase conflicts.** #662 is 10 behind upstream including 3 mathlib bumps and
  the `Relation` split (#632). Rebasing may require API adaptations (the recurring "fix breaking
  changes" pattern in upstream). *Mitigation*: rebase #648 first (only 2 behind, low risk); build
  after each step; the Step-2 checkout-onto-#648 route inherits #648's already-adapted base so the
  modal files meet current mathlib only once.
- **R2 — Dropping #662's `Propositional/Defs.lean` breaks a modal proof.** #648 head removed
  `Connectives.lean` and the `PropositionalConnectives` registration; if any modal file implicitly
  used a Propositional-side instance, it fails at build. *Mitigation*: §4 shows Modal/Basic.lean
  does not import Propositional and self-owns `Connectives.lean`; **confirm by `lake build`** on the
  stacked branch before pushing. Zero-debt: no `sorry`/axiom patch is acceptable — if a proof
  breaks, fix it structurally or mark BLOCKED.
- **R3 — Losing the task-472 work.** The 472 fix lives only on local `main` (commit `9c5cbd08`);
  a careless rebuild of #662 that checks out #662's old `LogicalEquivalence.lean` would silently
  revert it. *Mitigation*: `git tag pre-475-472fix 9c5cbd08` (Step 0); the Step-2 recipe explicitly
  `git checkout main -- …/LogicalEquivalence.lean` after pulling the modal files; verify the
  parametric `Proposition.Equiv S` and absence of `LogicallyEquivalent` post-build
  (`git grep LogicallyEquivalent Cslib/` must be empty).
- **R4 — `references.bib` duplication/omission.** Both PRs touch it. *Mitigation*: after stacking,
  diff `references.bib` and ensure modal keys are present, propositional keys are single-sourced
  from #648, no dangling BibKeys.
- **R5 — Force-push race / stale remote.** *Mitigation*: use `--force-with-lease`, and keep the
  `backup/*` branches until the PRs are confirmed green on GitHub CI.
- **R6 — origin/main confusion.** `origin/main` (fork) is 516 behind `upstream/main`; it is NOT a
  rebase target. Always rebase onto `upstream/main`.

## 13. Zulip context

- Thread: `CSLib > Modal Logic`,
  https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/607842603
- @fmontesi feedback (2026-07-02): overwhelmed by the PR size; wants to review "one at a time";
  returns **23 July**; open to a CSLib online meeting.
- Response plan (D6): acknowledge the size concern → explain #662 is now slimmed to the modal-only
  contribution stacked on #648; take his points individually; offer to join the CSLib online
  meeting after 23 July. Reuse the task-474 CSLib-meeting Zulip draft as a starting point.

## Appendix — verified hashes

- `upstream/main` = `5c41dcf2`; `origin/main` = `359d8286` (516 behind upstream).
- #648: local `feat/propositional-v2` `c98c4348` (mb `2772f421`, 5 ahead / 2 behind);
  origin/PR head `c9364b65`.
- #662: local `feat/modal-formula-primitives` `3ff6d02d` (mb `e0573fbc`, 3 ahead / 10 behind);
  origin/PR head `f46056b9`.
- Task-472 fix commit: `9c5cbd08` (parent `9c5cbd08^`; pre-472 `LogicalEquivalence.lean` differs
  from #662 head by 3 lines).
- Connectives.lean presence: `main` ✅, `feat/modal-formula-primitives` ✅,
  `feat/propositional-v2` ❌ (removed at #648 head).
- #662 does NOT contain #648 history (`merge-base --is-ancestor` = false, both local and origin).
