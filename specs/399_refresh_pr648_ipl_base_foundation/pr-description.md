<!-- ============================================================
HUMAN-AUTHOR-REQUIRED

This file is AI-assisted scaffolding for the PR body of a refreshed PR #648.
The HUMAN (benbrastmckie) must review, reword, and finalize every section
before pasting it into the GitHub PR body.

Zulip AI policy: AI-drafted Zulip messages are NOT allowed (Chris Henson warning,
msg 605827029). This document will not be posted by any automated tool. The author
must copy, read, reword, and submit in their own words.

Sections marked [FILL IN] require human input. All prose should be reworded
to reflect the author's own voice before posting.
============================================================ -->

# PR Description Draft — Refresh PR #648: IPL-Base Foundation

**PR URL**: https://github.com/leanprover/cslib/pull/648
**Branch**: `feat/propositional-foundation` (new branch off upstream/main)
**Build verified locally**: `lake build`, `lake exe checkInitImports`, `lake exe lint-style` — all green off upstream/main HEAD (`2772f421`, toolchain v4.32.0-rc1).

---

## Suggested PR Title

```
feat(Logics/Propositional): IPL-base foundation with primitive ⊥ and gated efq
```

---

## Suggested Commit Message

```
feat(Logics/Propositional): IPL-base foundation with primitive ⊥ and gated efq

Add bot as a primitive constructor of Proposition and efq as a gated
primitive natural deduction rule, making IPL the base logic with MPL
retained as a fragment.

Changes:
- Defs.lean: five-primitive Proposition {atom, bot, imp, and, or};
  IsIntuitionistic/IsClassical on Theory Atom (new API); subst monad
- NaturalDeduction/Basic.lean: 11 constructors including efq gated on
  [IsIntuitionistic T]; imp/impI/impE naming; IPL-as-base design note;
  restored references; Zulip-thread link
- references.bib: add Johansson1937, Gentzen1935, Prawitz1965,
  TroelstraVanDalen1988, SorensenUrzyczyn2006, Church1956,
  ChagrovZakharyaschev1997
- Delete NaturalDeduction/Theory.lean (instances absorbed into Defs.lean)
- Cslib.lean: remove Theory import

Connective typeclasses (PropositionalConnectives, HasBot, HasImp, HasAnd,
HasOr) are excluded per reviewer request; see PR #607 and task 400.
Derived rules (byContra, lem, pierce) follow in a separate PR.
Hilbert systems, semantics, sequent calculi, and tableau follow as
stacked PRs.
```

---

## Suggested PR Body

<!-- [FILL IN] Reword in your own voice before posting. -->

This is a focused refresh of PR #648, scoped down to the propositional
*foundation* layer per Thomas Waring's closing recommendation (Zulip thread
[Propositional Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic),
message 606970606).

### What this PR does

- **Five-primitive `Proposition` type**: `atom`, `bot`, `imp`, `and`, `or`.
  `⊥` is a primitive constructor (not simulated via `[Bot Atom]`), which
  eliminates all `[Bot Atom]` constraints from the API.

- **Gated `efq` (ex falso quodlibet)**: `efq` is a primitive *gated* constructor
  of `Theory.Derivation`, carrying an `[IsIntuitionistic T]` instance binder. This
  makes IPL the base logic — `efq` is available exactly when the theory validates
  explosion. Minimal logic (MPL) is retained as a fragment: `AxiomTheory MinPropAxiom`
  admits no `IsIntuitionistic` instance, so `efq` is unconstructible in MPL
  derivations and the entire MPL metatheory (Hilbert substrate, soundness,
  Lindenbaum, strong-completeness, conservativity chains) is preserved unchanged.

- **`impl`/`implI`/`implE` → `imp`/`impI`/`impE` rename**: This follows the
  `imp` naming in `Defs.lean`.

- **References restored and Zulip-thread link added**: All cited references
  (Johansson 1937, Gentzen 1935, Prawitz 1965, Troelstra & van Dalen 1988,
  Sørensen & Urzyczyn 2006, Church 1956, Chagrov & Zakharyaschev 1997) are
  present in `references.bib` and cited in the `## References` sections of the
  relevant files. The Zulip design thread is linked in `## Implementation notes`.

- **IPL-as-base design note**: `NaturalDeduction/Basic.lean` now contains an
  `## Implementation notes` section explaining the design choice (IPL-as-base,
  MPL-as-fragment), the trade-offs with the Johansson/Waring encoding approach,
  and a link to the CSLib Zulip thread.

### What is NOT in this PR (addressing Waring flag (a))

Per Thomas Waring's feedback, **connective typeclasses are a separate development**
and are NOT bundled here:

- `Cslib/Foundations/Logic/Connectives.lean` (new file with `HasBot`, `HasImp`,
  `HasAnd`, `HasOr`, `PropositionalConnectives`) is excluded.
- The `PropositionalConnectives`, `HasAnd`, `HasOr` instances that appeared in
  `Defs.lean` in the previous version of this PR are removed.
- See PR #607 (fmontesi) for the existing connective typeclass work; the
  CSLib-side coordination is tracked in task 400.

Other deferred work (not in this PR, to come in stacked PRs):

| Content | Reason | Future home |
|---------|--------|-------------|
| Derived rules (`byContra`, `lem`, `pierce`) | Keep this PR small | Follow-up `DerivedRules` PR |
| Hilbert proof systems / ND–Hilbert equivalence | Later stacked PR | Future work |
| Algebraic / Kripke semantics | Later stacked PR (see Waring's `GeneralizedHeytingAlgebra` suggestion) | Future work |
| Sequent calculi LJ/LK | Later stacked PR | Future work |
| Tableau systems | Later stacked PR | Future work |

### Theory.lean deletion — explicit reviewer decision

`NaturalDeduction/Theory.lean` (upstream/main) uses the old
`IsIntuitionistic Atom (S : InferenceSystem) [Bot Atom]` API, which is
fundamentally incompatible with the new `IsIntuitionistic (T : Theory Atom)` API
in the refreshed `Defs.lean`. The PR therefore **deletes `Theory.lean`** and
removes its import from `Cslib.lean`.

The core instances previously in `Theory.lean` (`instIsIntuitionisticIPL`,
`instIsClassicalCPL`, `instIsIntuitionisticIntuitionisticCompletion`) are now in
`Defs.lean`. The derived rules (`efqCtx`, `efqRule`, `contra`, `byContra`,
`lem`, `pierce`, `LEM`, `Pierce`, `instIsClassicalLEM`, `instIsClassicalPierce`)
are available in a follow-up `DerivedRules` PR (already implemented on the fork).

This is the only way to land the foundation without carrying forward the old API.
I am flagging this explicitly for reviewer confirmation.

### Namespace note (pending, task 387)

The PR exposes `namespace Cslib.Logic.PL`. The rename to
`namespace Cslib.Logics.Propositional` requires upstream maintainer consensus
and is tracked separately in task 387. It does not block this PR.

### AI tool disclosure

<!-- [FILL IN] Per CSLib and Mathlib AI usage policy, disclose how AI tools
were used in this PR. E.g.:
"AI tools (Claude) were used to assist with proof structure exploration,
documentation drafting, and bib entry lookup. All Lean code was reviewed
and verified by the author." -->

### Build verification

Verified locally on a fresh branch from upstream/main HEAD (`2772f421`,
toolchain `v4.32.0-rc1`):
- `lake build Cslib.Logics.Propositional.Defs` — green
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` — green
- `lake build Cslib` (full barrel) — green
- `lake exe checkInitImports` — green
- `lake exe lint-style` on touched files — green

---

## User Next Steps

1. Review and finalize this draft in your own words (AI policy — see banner above).
2. Run `bash specs/399_refresh_pr648_ipl_base_foundation/prepare-foundation-branch.sh`
   to create the local branch `feat/propositional-foundation` off upstream/main with
   all recipe changes staged (no commit yet).
3. Commit with the suggested commit message above (or your own wording).
4. Run `/pr 399` (user-only command) to push the branch and open the GitHub PR.
5. Finalize and post `zulip-response.md` to Zulip thread 606970606 **in your own words**.
