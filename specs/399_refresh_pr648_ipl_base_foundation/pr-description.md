<!-- ============================================================
HUMAN-AUTHOR-REQUIRED

This file is AI-assisted scaffolding for the PR body of PR #648.
The HUMAN (benbrastmckie) must review, reword, and finalize every section
before pasting it into the GitHub PR body.

Zulip AI policy: AI-drafted Zulip messages are NOT allowed (Chris Henson warning,
msg 605827029). This document will not be posted by any automated tool. The author
must copy, read, reword, and submit in their own words.

Sections marked [FILL IN] require human input.
============================================================ -->

# PR Description Draft — PR #648: IPL-base propositional foundation

**PR**: https://github.com/leanprover/cslib/pull/648
**Branch**: `feat/propositional-v2` — rebased onto current `upstream/main` (toolchain
`v4.32.0-rc1`); 3 clean commits, no merge commit. Head commit `63cd13c8` adds the IPL-base
refactor. The two original commits (`1a2e2e7e`, `cc44c14d`) are preserved.
**CI**: GitHub Actions — all checks **green** on `63cd13c8`. Verified locally too:
`lake build`, `lake exe mk_all --check`, `lake exe checkInitImports`, `lake lint`,
`lake exe lint-style`, `lake test` — all pass; zero `sorry`.

---

## Suggested commit message (the new commit)

```
feat(Logics/Propositional): make IPL the base logic with primitive ex falso

Promote ex falso quodlibet (bottom-elimination) to an ungated primitive
constructor of the natural-deduction Derivation, so IPL is the base
propositional logic and the primitive bot constructor has an inference
rule. IPL becomes the empty base theory; CPL still adds double negation
elimination.

The minimal-logic (MPL) layer is deferred to a separate PR: this removes
MPL, the IsIntuitionistic typeclass, intuitionisticCompletion, and the
derived efq rules, keeping the classical layer (byContra/lem/pierce and
the IsClassical instances for CPL/LEM/Pierce) intact, re-proved via the
efq constructor.

Per reviewer feedback (Waring, CSLib Zulip 'Propositional Logic'):
- Drop the connective typeclasses (Foundations/Logic/Connectives.lean and
  its registration instances) -- a separate development handled via PR #607.
- Restore references (Johansson 1937, Gentzen 1935, Prawitz 1965,
  Troelstra-van Dalen 1988) and add the CSLib Zulip thread link.
```

---

## Suggested PR Body

<!-- [FILL IN] Reword in your own voice before posting. -->

This refreshes PR #648 to settle the propositional-logic *base* per Thomas Waring's
recommendation on the Zulip thread
[Propositional Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic)
(msg 606970606): with `⊥` a primitive constructor, ex falso should be a real rule, so
**IPL is the base logic** and the question of a separate minimal-logic development is
**deferred to later work**.

### What the PR delivers

- **Five-primitive `Proposition`**: `atom`, `bot`, `imp`, `and`, `or`. `⊥` is a primitive
  constructor (no `[Bot Atom]` constraint); `¬φ := φ → ⊥`, `⊤ := ⊥ → ⊥` are derived.
- **IPL is the base natural-deduction system.** Ex falso quodlibet (`efq`, ⊥-elimination)
  is an **ungated primitive constructor** of `Theory.Derivation` — so `⊥` has an inference
  rule rather than being a constructor with no behaviour. `CPL` extends the base with double
  negation elimination; classical derived rules (`byContra`, `lem`, `pierce`) and the
  `IsClassical` instances for `CPL`/`LEM`/`Pierce` are included.
- **References + Zulip link**: `Johansson1937`, `Gentzen1935`, `Prawitz1965`,
  `TroelstraVanDalen1988` are in `references.bib` and cited in `NaturalDeduction/Basic.lean`,
  whose `## Implementation notes` motivate primitive efq and link the design thread.

### Addressing the review comments (Waring, msg 606970606)

- **efq as a rule / forget minimal logic for now.** efq is now a primitive rule and `⊥` has
  semantics. Minimal logic (MPL) is **not** part of this PR — `MPL`, the `IsIntuitionistic`
  typeclass, `intuitionisticCompletion`, and the derived efq rules are removed. The
  minimal-as-fragment / fragment-design work is deferred to a separate PR for separate
  discussion (tracked on the fork as tasks 407–409).
- **Connective typeclasses are a separate development.** `Cslib/Foundations/Logic/Connectives.lean`
  and its registration instances are **removed** from this PR; the connective-typeclass work is
  coordinated with fmontesi's PR #607 (see task 400). One design point for #607: it currently makes
  negation primitive (`HasNot`) with no `HasBot`; for IPL/MPL `¬φ := φ → ⊥`, so a `HasBot` class
  with derived `¬`/`⊤` is needed for `Proposition` to register.
- **References + Zulip link.** Added (above).

### Deferred to follow-up PRs

| Content | Future home |
|---|---|
| Minimal logic (MPL) + fragment design | separate PR (the deferred discussion) |
| Connective typeclasses | via PR #607 |
| Hilbert systems, ND–Hilbert equivalence | stacked PR |
| Algebraic / Kripke semantics | stacked PR |
| Sequent calculi LJ/LK, tableau | stacked PRs |

### Namespace note (pending, task 387)

The PR exposes `namespace Cslib.Logic.PL`; the rename to `Cslib.Logics.Propositional`
(per ORGANISATION.md) needs maintainer consensus and is tracked in task 387. Not blocking.

### AI tool disclosure

<!-- [FILL IN] Per CSLib/Mathlib AI policy, disclose how AI tools were used, e.g.:
"AI tools (Claude) assisted with refactoring, proof adjustment, documentation drafting,
and bib lookup; all Lean code was reviewed and verified by the author." -->

---

## Status / next steps

The branch is **already pushed** and **GitHub CI is green** (head `63cd13c8`); the PR is
`MERGEABLE` (awaiting maintainer review). Remaining, human-only:

1. Reword this draft in your own words (AI policy — see banner) and paste it into the #648 PR body.
2. Post `zulip-response.md` to Zulip thread 606970606 **in your own words**.
