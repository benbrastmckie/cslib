**Target**: [PR #607](https://github.com/leanprover/cslib/pull/607) — `feat(Logic): logical operators` (fmontesi, CSLib maintainer)
**Status**: DRAFT — do NOT post. Requires EXPLICIT user approval before posting.
**Posting guidance** (once approved): post as a single plain PR comment (or review discussion).
Never a GitHub "suggested change" applied to his branch — the head branch is in-org
(`leanprover/cslib`, not a fork), so coordination stays comment-only, never a push/edit/rebase of
`fmontesi/connectives`.
**Re-verify before posting**: confirm #607 is still ~15 commits behind `main` and `ci-checks` is
still red for the same `HML/LogicalEquivalence.lean` reason (§4.3 of the research report). If the
branch has since been rebased, drop or reword item 1.

---

Hi Fabrizio — a few notes on this:

1. **Bundling** (re the "one file vs. split" / "should these be bundled?" thread): I have a `HasBot`
   class and bundled `PropositionalConnectives`/`ModalConnectives` — written for the modal PR
   downstream — that cover the two pieces this layer is currently missing. They're CI-green; happy to
   open them as a PR against your branch whenever you'd like, so downstream just imports this layer.

2. **Naming**: `HasImpl.impl` here vs. `HasImp.imp` downstream. I lean `imp` (matches the
   `impI`/`impE` prefixes), but it's your call — I'll conform the downstream PRs either way.

3. **Modal primitives**: there's a box- vs. diamond-primitive question for `Modal/Basic.lean` that
   decides whether the `HasDiamond`/`HasNot` instances here stay as-is — details in the Modal Logic
   Zulip thread. Nothing blocking on this PR.

4. **CI**: the red check looks like pre-existing `main` drift rather than anything in this PR — a
   rebase onto `main` should clear it.
