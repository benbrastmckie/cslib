<!-- ============================================================
HUMAN-AUTHOR-REQUIRED

This file is AI-assisted scaffolding for the PR body of PR #648.
The HUMAN (benbrastmckie) must review, reword, and finalize before pasting
it into the GitHub PR body.

This draft is a MINIMAL REVISION of the CURRENT live #648 description: same
section skeleton (Summary / Modified files / Design rationale / Coordination /
Deferred / AI Tools), with only the parts changed by the IPL-base commit edited.
It does NOT restructure the existing description.

Zulip AI policy: AI-drafted Zulip messages are NOT allowed. This document will
not be posted by any automated tool.
============================================================ -->

# PR Description — PR #648 (minimal revision of the live body)

**PR**: https://github.com/leanprover/cslib/pull/648
**Branch**: `feat/propositional-v2` — rebased onto current `upstream/main` (toolchain
`v4.32.0-rc1`); 3 clean commits, head `65a3af7a`. **GitHub CI green; MERGEABLE.**
Net diff: 4 files — `Defs.lean`, `NaturalDeduction/Basic.lean`, `NaturalDeduction/Theory.lean`,
`references.bib`. (`Connectives.lean` and `Cslib.lean` are no longer touched by the PR.)

---

## Delta from the current live #648 description (so you can see what changed)

- **Summary → Key changes**: added the efq/IPL-base bullet; added "connective typeclasses removed";
  rewrote the references bullet (we now ship Gentzen/Prawitz/Troelstra–van Dalen, not "German refs
  replaced with Avigad").
- **Removed the "New files" section** — `Connectives.lean` is no longer added.
- **Modified files**: dropped `Cslib.lean` (no net change) and all `Connectives` mentions; updated
  the `Defs.lean`/`Basic.lean`/`Theory.lean` lines for IPL-base + `efq`; `references.bib` now lists
  the 3 added entries.
- **Design rationale**: one added sentence on primitive `efq` / IPL-base.
- **Coordination / Deferred**: updated for connectives→#607 and the minimal-logic deferral.

---

## Suggested PR Body (paste-ready after rewording)

## Summary

Revises PR #648 based on reviewer feedback (thomaskwaring, msg 606970606). Adds `bot` as a primitive constructor of `Proposition` (eliminating all `[Bot Atom]` constraints) and makes **IPL the base logic** by taking ex falso quodlibet as a primitive natural-deduction rule. Rebased on upstream/main post-#536.

**Key changes from #648:**
- `bot` is a primitive constructor (not an atom), so explosion and `IsClassical` no longer require `[Bot Atom]`
- **Ex falso quodlibet is now a primitive rule** (`efq` constructor of `Derivation`), so `⊥` has an inference rule and **IPL is the base logic**; minimal logic (MPL) is set aside for a separate PR/discussion, per the agreed compromise
- Reconciled with merged PR #536's InferenceSystem-parameterized typeclasses
- Constructor naming uses `imp`/`impI`/`impE` (renamed from `impl`/`implI`/`implE` for consistency with FormalizedFormalLogic convention; open to reverting if reviewers prefer `impl`)
- Semantics not included — deferred to a follow-up PR (per thomaskwaring's request)
- Connective typeclasses removed — a separate development coordinated via PR #607 (this PR no longer ships `Connectives.lean`)
- References include Avigad 2022, Gentzen 1935, Prawitz 1965, and Troelstra & van Dalen 1988, and a link to the CSLib Zulip design thread is added

## Modified files

- `Cslib/Logics/Propositional/Defs.lean` -- `Proposition` with primitive `bot`; derived `neg`, `top`, `iff`; `IPL` is the empty base theory and `CPL` adds double-negation elimination (the `MPL` / `IsIntuitionistic` / `intuitionisticCompletion` layer is set aside for the minimal-logic PR)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- derivation constructors `impI`/`impE`, `andE1`/`andE2`, `orI1`/`orI2` with explicit `Γ` arguments, plus the new primitive `efq` (⊥-elimination); implementation notes, references, and Zulip-thread link
- `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` -- `[Bot Atom]` removed; the classical layer (`IsClassical`, `byContra`/`lem`/`pierce`, and the `CPL`/`LEM`/`Pierce` instances) re-proved over the new base via the `efq` constructor
- `references.bib` -- added `Avigad2022`, `Gentzen1935`, `Prawitz1965`, `TroelstraVanDalen1988`

## Design rationale

Primitive `bot` eliminates `[Bot Atom]` constraints throughout the propositional logic API, gives `Proposition.subst` a natural recursive case for `bot`, and follows the standard treatment in Avigad (2022) where `bot` is a logical constant rather than an atomic proposition. The trade-off (noted by thomaskwaring) is an extra `bot` case in structural recursions. Relatedly, taking ex falso as a **primitive rule** rather than leaving `⊥` a constructor with no inference behaviour follows the standard natural-deduction treatment (Gentzen 1935, Prawitz 1965, Troelstra & van Dalen 1988) and is thomaskwaring's recommendation; minimal logic — the efq-free fragment — is deferred so the fragment design can be settled on its own.

These benefits extend to planned completeness work for modal and temporal logics: primitive `bot` ensures `Proposition.subst` preserves bottom structurally (`subst f .bot = .bot`), whereas atom-encoded bot requires additional constraints to prevent `subst f (.atom ⊥) = f ⊥` from mapping bottom to an arbitrary formula. As thomaskwaring notes, non-bottom-preserving maps are also useful (e.g., conservativity results via `WithBot.some`).

## Coordination

- **PR #607** (fmontesi): connective typeclasses are a separate development; this PR no longer ships its own `Connectives.lean`. One design point for #607: it makes negation primitive (`HasNot`) with no `⊥`/`⊤` class, but a `⊥`-primitive `Proposition` (where `¬φ := φ → ⊥` and `⊤ := ⊥ → ⊥`) registers faithfully by reusing Mathlib's `Bot`/`Top` together with a derived `HasNot` (`not := neg`) and a `(φ → ⊥) = ¬φ` grind bridge — no separate `HasBot` class needed. I'll leave a review on #607.

## Deferred

- **Minimal logic (MPL) + fragment design** -- a separate PR/discussion (the agreed deferral).
- **Semantics** (`Bool.lean`, evaluation) -- follow-up PR; the `Prop` vs `Bool` vs `GeneralizedHeytingAlgebra` question (raised by thomaskwaring and ctchou) will be addressed there.
- Hilbert systems, sequent calculi, and tableau -- stacked PRs.

## AI Tools Used

Claude Code was used to refactor for primitive `efq`/IPL-base, remove the connective typeclasses and the minimal-logic layer, rebase onto upstream/main and resolve the `references.bib` conflict, and verify CI. All mathematical decisions reviewed.
