<!-- ============================================================
HUMAN-AUTHOR-REQUIRED

This file is AI-assisted scaffolding for a Zulip reply to Thomas Waring's
message 606970606 in the CSLib "Propositional Logic" thread.

CRITICAL — Zulip AI policy: Zulip messages MUST be human-authored.
Chris Henson explicitly flagged AI-drafted Zulip messages as not allowed
(msg 605827029). This file will NOT be posted by any automated tool.
The author (benbrastmckie) must read, reword entirely in their own voice,
and post manually.

The content below is a structural scaffold only — facts and talking points,
not a polished final message. Reword everything before posting.
============================================================ -->

# Zulip Response Draft — Thread: Propositional Logic (stream CSLib)

**Thread**: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic
**Responding to**: Thomas Waring, message 606970606
**Context**: Waring's two flags + design acceptance of efq-as-primitive

---

## Draft Message Body

<!-- [FILL IN] Reword entirely in your own voice before posting. Do NOT copy-paste AI-drafted prose to Zulip. -->

Hi Thomas,

Thanks for the detailed feedback. A few updates:

**efq as gated primitive (your closing suggestion)**: This is now implemented.
`efq` is a primitive constructor of `Theory.Derivation` gated on
`[IsIntuitionistic T]`, exactly as you suggested. IPL is the base logic;
MPL is retained as a fragment (the `AxiomTheory MinPropAxiom` theory admits no
`IsIntuitionistic` instance, so `efq` is unconstructible there). This is fully
verified: `lake build`, `lake test`, `lake exe checkInitImports`,
`lake exe lint-style`, and `lake shake` all pass on the fork.

**Connective typeclasses removed (your flag (a))**: The `PropositionalConnectives`,
`HasAnd`, `HasOr` instances have been removed from the foundation PR. I will
coordinate with fmontesi's PR #607 separately. I have a local task (400) tracking
this coordination.

**References and Zulip-thread link added (your flag (b))**: Johansson 1937,
Gentzen 1935, Prawitz 1965, Troelstra & van Dalen 1988, Sørensen & Urzyczyn 2006,
Church 1956, and Chagrov & Zakharyaschev 1997 are all now in `references.bib` and
cited in the relevant files. The Zulip design thread is linked in
`## Implementation notes` of `Basic.lean`.

I will refresh PR #648 with this focused foundation commit shortly.
Looking forward to your formal review once the PR is updated.

[FILL IN: add any personal context, questions, or acknowledgments in your own words]

---

## Key Facts to Convey (Checklist for the Author)

- [ ] efq is now implemented as gated primitive per Waring's suggestion (task 398 complete, CI green)
- [ ] Connective typeclasses are NOT in this PR (Waring flag a); coordination with PR #607 is task 400
- [ ] References and Zulip link are now present (Waring flag b)
- [ ] Theory.lean is deleted in the cherry-pick (instances absorbed into Defs.lean; derived rules follow)
- [ ] Foundation is a single focused commit off upstream/main (verified locally)
- [ ] Welcoming Waring's formal review once the PR is refreshed

---

## Thread / Recipient Details

- **Stream**: CSLib (channel 513188)
- **Topic**: Propositional Logic
- **Key message to reply to**: msg 606970606 (Waring's closing message with the two flags)
- **Sender reference**: Thomas Waring (@thomaskwaring on Zulip)
