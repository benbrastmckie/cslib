**Target**: [PR #607](https://github.com/leanprover/cslib/pull/607) — `feat(Logic): logical operators` (fmontesi, CSLib maintainer)
**Status**: SUPERSEDED — do NOT post. The substantive #607 coordination was carried by the posted
comment https://github.com/leanprover/cslib/pull/607#issuecomment-4837502740 (benbrastmckie,
2026-06-29), which covers the #648 overlap, the `⊥`-representation decision, and Has*-prefix naming.
This modal-focused draft is retained for reference only; its box-vs-diamond point lives in the Zulip
note, and its bundle/`imp` nits are minor thread replies if they come up. Kept below as history.
**Posting guidance** (once approved): post as a single plain PR comment (or review discussion). Never a GitHub "suggested change" applied to his branch — the head branch is in-org (`leanprover/cslib`, not a fork), so coordination stays comment-only, never a push/edit/rebase of `fmontesi/connectives`.
**Re-verify before posting**: confirm #607 still lacks `HasBot`/bundled classes (no `Operators/Bot.lean`), still uses `HasImpl.impl`, and still carries the diamond-inclusive modal basis; and that #662 still provides `HasBot`/`PropositionalConnectives`/`ModalConnectives` with `imp` naming. (CI note dropped deliberately: the red `ci-checks` is this PR's own `LogicalEquivalence` parametrisation leaving `HML/LogicalEquivalence.lean` on the old signature — a regression to fix in-PR, not main drift, so it is not raised in the comment.)

---

Hi Fabrizio — a few notes on this:

1. **Bundling** (re the "one file vs. split" / "should these be bundled?" thread): I have a `HasBot` class and bundled `PropositionalConnectives`/`ModalConnectives` — written for the modal PR downstream — that cover the two pieces this layer is currently missing. They're CI-green; happy to open them as a PR against your branch whenever you'd like, so downstream just imports this layer.

2. **Naming**: `HasImpl.impl` here vs. `HasImp.imp` downstream. I lean `imp` (matches the `impI`/`impE` prefixes), but it's your call — I'll conform the downstream PRs either way.

3. **Modal primitives**: there's a box- vs. diamond-primitive question for `Modal/Basic.lean` that decides whether the `HasDiamond`/`HasNot` instances here stay as-is — details in the Modal Logic Zulip thread. Nothing blocking on this PR.
