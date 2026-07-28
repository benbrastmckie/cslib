# Draft: PR #648 re-review comment

## Comment to paste on PR #648

@ctchou — this hasn't had a re-review since your CHANGES_REQUESTED on June 15, even
though there have been two rounds of rework since then. Sorry for the gap; I wanted the
design to actually settle before asking you to look again.

The main change is that `⊥` is now a primitive constructor and `efq` is a primitive
natural-deduction rule, so IPL is the base logic. That's the compromise Thomas Waring
proposed on Zulip
(https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/606970606),
and since it postdates your original review I wanted to point straight at it rather than
leave it as a vague "see the Zulip thread" reference.

On your three points: Avigad's *Mathematical Logic and Computation* is now the lead
reference, the 1930s papers are cut back, and Gentzen is kept but with an English gloss
instead of the German title. Both `Semantics/` files are out of the PR — semantics is
deferred to a follow-up, which also answers why we seemed to need both. And on
coordination: #536 is merged and this branch is rebased on top of it; dropping semantics
and the connective typeclasses from this PR resolves the overlap with #587 and #607 (I'll
give those a review separately).

Would appreciate a re-review when you get a chance.

---

## Reviewer notes / decisions (NOT part of the comment — do not paste)

**Open decisions for Benjamin to settle before posting:**

1. **Ping Thomas Waring too?** He said in the settlement message he'd "review the PR
   properly once we've settled on the design." Given the design has now settled, it may be
   worth an explicit @-mention alongside ctchou, but the comment above is addressed to
   ctchou only — add Waring only if you want to.
2. **Include the acceptance permalink too?** The comment above links only the settlement
   message (606970606, Waring's compromise). It optionally could also link the acceptance
   message (607217129, Benjamin's own reply confirming implementation against the
   compromise) for anyone who wants to see the implementation confirmation directly. Left
   out above to keep the comment tight — add it if you'd rather be explicit.
3. **Push-before-post ordering — confirm.** The comment describes the PR's state as
   already settled (references reordered, semantics removed, coordination resolved), which
   matches GitHub head `c9364b65`. But two design-neutral polish commits, `bbcbef85` and
   `c98c4348`, are local-only and not yet on GitHub. Push `feat/propositional-v2` before
   posting this comment so GitHub's head matches what the comment implies. Do not post
   first and push later.

**Fact-check against `reports/01_pr-review-research.md`:**
- Settlement permalink: `.../near/606970606` (Thomas Waring, 2026-06-28) — used in the
  comment above. Confirmed correct.
- Optional acceptance permalink: `.../near/607217129` (benbrastmckie, 2026-06-29) — not
  used in the comment above; available if decision 2 above goes the other way.
- Forbidden link: `.../near/604219492` (benbrastmckie's own earlier position statement,
  2026-06-17, not the settlement) — confirmed **not** present anywhere in the comment
  above.
- GitHub head SHA: `c9364b65391b1cc2bfd211102a3deb86f3844d48`.
- Unpushed local-only SHAs: `bbcbef85`, `c98c4348` (design-neutral polish; kept out of the
  design narrative above per the plan).
- PR: #648. Coordinated PRs referenced: #536 (merged), #587, #607.
