<!-- ============================================================
HUMAN-AUTHOR-REQUIRED

This file is AI-assisted scaffolding for a Zulip reply to Thomas Waring's
message 606970606 in the CSLib "Propositional Logic" thread.

CRITICAL — Zulip AI policy: Zulip messages MUST be human-authored.
Chris Henson explicitly flagged AI-drafted Zulip messages as not allowed
(msg 605827029). This file will NOT be posted by any automated tool.
The author (benbrastmckie) must read, reword ENTIRELY in their own voice,
and post manually.

The content below is a structural scaffold only — facts and talking points,
not a message to copy-paste. Reword everything before posting.
============================================================ -->

# Zulip Response Draft — Thread: Propositional Logic (stream CSLib)

**Thread**: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic
**Responding to**: Thomas Waring, message 606970606
**Context**: accept Waring's compromise (efq as a rule, set minimal logic aside for now) + his two flags

---

## Talking points (reword entirely in your own voice — do NOT paste AI prose to Zulip)

**1. Agree with the compromise.** Waring proposed: have efq as a rule (so `⊥` isn't a constructor
without semantics), postpone the fragment design, and "forget about minimal logic for the moment."
That's the design now in #648 — and it reads as a reasonable compromise.

- efq is now an **ungated primitive constructor** of `Theory.Derivation`, so **IPL is the base
  logic** and `⊥` has a genuine elimination rule.
- **Minimal logic is set aside in this PR** — `MPL`, the `IsIntuitionistic` typeclass, and the
  derived-rule scaffolding are removed; the fragment design / minimal-logic development is left for
  separate later work, as suggested.
- The classical layer stays (`CPL` = base + double-negation elimination; `byContra`/`lem`/`pierce`).
- Verified locally: build green, `lint-style` clean, `checkInitImports` clean, zero `sorry`.

**2. Connective typeclasses — flag (a).** Removed from the PR (`Connectives.lean` and its
registration instances are gone). Happy to take it to fmontesi's PR #607 instead. One design point
worth raising there: #607 currently makes negation primitive (`HasNot`) with no `HasBot`, but for
intuitionistic/minimal logic `¬φ := φ → ⊥`, so a `HasBot` class with `¬`/`⊤` derived would let the
`⊥`-primitive `Proposition` register cleanly. (Optional — judge whether to mention this here or as a
review on #607 itself.)

**3. References + Zulip link — flag (b).** Added: Johansson 1937, Gentzen 1935, Prawitz 1965,
Troelstra & van Dalen 1988 are in `references.bib` and cited in `Basic.lean`; the design thread is
linked in its `## Implementation notes`.

**4. PR status.** #648 is refreshed by adding one focused commit (fast-forward — the existing
commits stay). Looking forward to your review now that the base design is settled.

[FILL IN: your own framing, any questions for Thomas, acknowledgement of the encoding-vs-rule
trade-off he raised, etc.]

---

## Fact checklist for the author

- [ ] efq is an **ungated** primitive rule ⇒ IPL is the base (NOT "gated / MPL retained" — minimal is set aside)
- [ ] Minimal logic / fragment design **deferred to later work** (matches Waring's compromise)
- [ ] Connective typeclasses removed from PR; engage PR #607 (task 400); HasBot/derived-¬ point
- [ ] References (4: Johansson/Gentzen/Prawitz/Troelstra–van Dalen) + Zulip link added
- [ ] #648 updated by fast-forward (no force-push); existing commits + review preserved
- [ ] Welcome formal review

## Thread / recipient details
- **Stream**: CSLib (channel 513188) — **Topic**: Propositional Logic
- **Reply to**: msg 606970606 (Waring's closing message)
- **Recipient**: Thomas Waring
