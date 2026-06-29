# PR #648 — Minimal IPL-Base Revision (FINAL APPROACH)

**Supersedes** the full-replacement cherry-pick approach in this directory
(`cherry-pick-recipe.md`, `prepare-foundation-branch.sh`, `update-pr648-branch.sh`).
Those built a fresh single commit off `upstream/main`, deleted `Theory.lean`, and required a
force-push. They are **no longer the plan** — kept only for history.

**Date**: 2026-06-29
**Decision**: minimal, additive revision of what is already in PR #648 (user direction:
"minimally revise PR 648 to promote the IPL-as-base refactor, saving the MPL-as-base dispute
for later"). efq design = **ungated primitive constructor** (IPL is the base; minimal/MPL
deferred). See AskUserQuestion record in session.

## Implementation — DONE & VERIFIED

- **Branch**: `feat/propositional-ipl-base` (cut from PR #648's `feat/propositional-v2`,
  toolchain v4.31.0).
- **Commit**: `5dbed274` — "feat(Logics/Propositional): make IPL the base logic with primitive
  ex falso".
- **Diff**: 3 files, +27 / −81 (net −54). Self-contained — verified no other consumer of the
  removed decls exists anywhere in the tree.
  - `Defs.lean`: `IPL := ∅` (base); removed `MPL`, `efq_mem_ipl`, `intuitionisticCompletion`,
    `class IsIntuitionistic`. Kept `CPL`, `IsClassical`.
  - `NaturalDeduction/Basic.lean`: added ungated `efq {Γ A} : Derivation Γ ⊥ → Derivation Γ A`
    constructor (11th) + efq arms in `weak`/`subs`/`substAtom`; `Equiv := IPL.Equiv`; docstrings
    updated (IPL-as-base, efq primitive); removed orphaned `[Avigad2022]` ref (still cited in
    `Defs.lean`, so the bib entry stays).
  - `NaturalDeduction/Theory.lean`: removed the `IsIntuitionistic` layer (instances + efqCtx/
    efqRule/contra); kept the classical layer (`IsClassical.byContra/lem/pierce`, CPL/LEM/Pierce
    instances), re-proved explosion steps via the `efq` constructor; `LEM`/`Pierce` instances
    simplified from `… ∪ IPL` to `…`.
- **Build**: `lake build Cslib.Logics.Propositional.NaturalDeduction.Theory` → 594 jobs green.
- **Lint**: `lake exe lint-style` on the 3 files → clean.
- **Debt**: zero `sorry`, zero new axioms, no warn suppressions.

## How #648 gets updated — FAST-FORWARD, no force-push

`feat/propositional-v2` is an **ancestor** of `5dbed274`, so updating #648 is a plain
fast-forward (preserves the existing 2 commits + all review threads; CI re-runs on the new
commit):

```bash
# from repo root
git push origin feat/propositional-ipl-base:feat/propositional-v2
# (or: git checkout feat/propositional-v2 && git merge --ff-only feat/propositional-ipl-base && git push origin feat/propositional-v2)
```

#648 then shows 3 commits; the new one promotes IPL to the base.

## Remaining steps (HUMAN — per CSLib AI policy)

1. Review `git show 5dbed274` (and `git diff feat/propositional-v2 feat/propositional-ipl-base`).
2. Fast-forward push (above) to update #648.
3. Update the #648 PR description: primitive `⊥` + primitive **ungated** `efq` ⇒ IPL is the
   base logic; double-negation gives CPL; **minimal logic (MPL) is intentionally deferred** to a
   separate PR for separate discussion (tracked here as tasks 407/408/409). Reword
   `pr-description.md` in your own voice (drop the now-inaccurate "delete Theory.lean / cherry-
   pick off upstream" framing).
4. Post the Zulip reply (thread 606970606) **by hand**, in your own words.

## Deferred — the MPL-as-base dispute

Tasks **407** (mpl_base_structure_first_redesign), **408** (minimal_sequent_calculus_lm),
**409** (bot_rule_free_nd_option_b) hold the structure-first / MPL-as-base alternative. They are
the "saved for later" dispute and should stay deferred until after the IPL-base PR discussion —
they pursue the opposite base choice and must not block #648.
