# PR #648 Refresh Research: IPL-Base Foundation

**Task**: #399
**Date**: 2026-06-29
**Focus**: Gather concrete inputs for the PR #648 cherry-pick/refresh strategy

---

## Sources Fetched

| Source | Type | Status |
|--------|------|--------|
| https://github.com/leanprover/cslib/pull/648 | GitHub PR | Fetched (1 review, 2 comments) |
| CSLib Zulip "Propositional Logic" (stream 513188-CSLib) | Zulip Thread | Fetched (27 messages) |
| Local repo: main branch, specs/398 summary | Local files | Read |

---

## PR #648 Current State

### Metadata

- **Title**: `feat(Logics/Propositional): five-primitive formula type with primitive bot`
- **State**: OPEN, not merged
- **Author**: benbrastmckie
- **Branch**: `feat/propositional-v2` → base `main`
- **URL**: https://github.com/leanprover/cslib/pull/648
- **Created**: 2026-06-14 (revised 2026-06-16 with ctchou feedback addressed)
- **Commits on PR branch**: 2 (on top of merge base `70c5bf5874a1` = PR #536 merge)
- **Changed files** (current PR): 6
- **Additions**: 282, **Deletions**: 145

### How Far Behind Upstream/main

As of 2026-06-29:

- **Merge base**: `70c5bf5874a1a511b32ad1ae605c07a13345d071` (PR #536 "classical and intuitionistic inference systems" — the last commit shared by feat/propositional-v2 and upstream/main)
- **Commits on feat/propositional-v2 AHEAD of merge base**: 2 (the two PR commits)
- **Commits on upstream/main AHEAD of merge base**: 11

The original task description said "~239 commits behind" — that number was accurate at task creation time; upsteam/main has since caught up closer to the merge base. The PR is currently **11 commits behind upstream/main** (not 239).

The 11 new upstream commits are:
```
2772f421  chore: fix header of Cslib/Computability/Automata/DA/Prod.lean (#682)
a441db60  feat(Automata): Transducers (#650)
f10c0493  feat(untyped): define CBN and Standard evaluation strategies (#671)
dbce0f9a  chore: bump mathlib to 29af524, fix breaking changes (#670)
f03afdc0  feat: Set.ReflOn, Set.SymmOn (#663)
5564021e  refactor(LocallyNameless/Untyped): rename close_open_to_subst (#668)
7e1ac9da  feat(LocallyNameless/Untyped): generalize eta_subst_fvar (#667)
dc23a39f  feat(LocallyNameless/Untyped): subst_intro weaker precondition (#666)
e0573fbc  chore: bump toolchain to v4.32.0-rc1 (#664)
1dbda533  feat(Automata, LTS, TM): Introduce LTS.SMTr, etc. (#625)
c2197aca  feat(FLP): show that asynchronous distributed consensus is possible (#619)
```

None of these 11 commits touch Propositional logic files — they are all in Automata, LambdaCalculus, and infrastructure. This means a fresh branch off current upstream/main will have clean propositional files to replace.

### PR Commits

```
194f0c3d  doc: fix docstrings for primitive bot perspective
7cc09612  feat(Logics/Propositional): five-primitive formula type with primitive bot
```

### Files in Current PR #648

| File | Change |
|------|--------|
| `Cslib.lean` | Add `Connectives` import |
| `Cslib/Foundations/Logic/Connectives.lean` | NEW: typeclass hierarchy (HasBot, HasImp, HasAnd, HasOr, PropositionalConnectives) |
| `Cslib/Logics/Propositional/Defs.lean` | 5-primitive Proposition; derived neg/top/iff; typeclass instances |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | imp/impI/impE renaming; explicit Γ arguments |
| `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` | [Bot Atom] removed; instIsIntuitionisticIntuitionisticCompletion added |
| `references.bib` | Avigad2022 entry added |

### Current PR Description Summary

The PR adds `bot` as a primitive constructor of `Proposition`, eliminating all `[Bot Atom]` constraints. It reconciles with merged PR #536. The semantics files (Basic.lean, Bool.lean) were removed per reviewer request. German-language references were replaced with Avigad (2022). `Connectives.lean` adds per-operator typeclasses. Deferred work noted: semantics (`Prop`/`Bool`/`GeneralizedHeytingAlgebra` question), coordination with PR #607 and #587.

---

## Review Feedback Summary

### ctchou — CHANGES_REQUESTED (2026-06-15)

1. Likes the idea of adding `⊥` as a primitive.
2. Does not understand why both `Semantics/Basic.lean` and `Semantics/Bool.lean` are needed — thinks `Bool.lean` alone suffices. (Semantics files have since been removed from the PR.)
3. Old/German-language references are not helpful — recommends Avigad 2022 textbook (Cambridge). (Avigad2022 entry has been added to the PR.)
4. Must coordinate with PR #607 and #587; wait for #536 to merge first. (#536 is now merged; coordination with #607 noted in PR description.)

### thomaskwaring — (2026-06-16, comment — no formal review state)

Raised several concerns in a comment (not a formal review submission):
- If `⊥` is in minimal logic it behaves like an atom; why not represent it as such?
- Minimal logic works perfectly well without `⊥` (per _Lectures on the Curry-Howard Correspondence_).
- Extra constructor makes proofs and definitions more verbose.
- Substitution argument acknowledged but noted `WithBot.some` maps for conservativity.
- `⊤ := a → a` is a feature not a bug.
- Agreed `imp`/`implI` renaming is fine.
- Requested semantics be split into a separate PR.
- Agreed on modern English references (Gentzen paper was his mistake).

The PR author (benbrastmckie) responded at length addressing each point, noting the semantics were removed and references updated.

---

## Zulip Discussion Synthesis

### Thread Overview

CSLib Zulip, stream "CSLib", topic "Propositional Logic". 27 messages from June 2026. Key participants: Benjamin Brast-McKie, Thomas Waring, Matthew Doty, Ching-Tsun Chou, Chris Henson.

### Early Thread: Design Debate

**Matthew Doty** (msg 603062659): Requested a smaller PR with just semantics and strong soundness.

**Thomas Waring** (msg 603084275): Suggested `GeneralizedHeytingAlgebra` for the right generality. Expressed interest in reviewing small pieces.

**Long design debate** (msgs 603884159 – 604219492): Waring and Doty explored the `⊥`-as-atom vs. `⊥`-as-constructor question in depth. Key points:
- Waring: with `⊥` as constructor, evaluation must preserve bottom, which means MPL completeness (which requires valuations where `⊥ ≠ ⊥_algebra`) needs extra treatment.
- Brast-McKie (msg 604219492): Argued for `⊥` as primitive via substitution-invariance and the free-algebra perspective; the `bot_val` parameter in `AlgEvaluate` handles MPL's freedom without the `[Bot Atom]` side conditions.

**Chris Henson warning** (msg 605827029): Asked if message 605813681 was written by an LLM; this is not allowed by Zulip AI policy. Brast-McKie confirmed he uses AI for drafting but reviews outputs — and committed to avoiding AI-drafted Zulip messages going forward.

### Waring's Closing Message (msg 606970606) — THE KEY INPUT

This is the most recent message and the primary driver for this task:

> "My sense is that, if we are going to have `⊥` as a primitive, we should also have efq — then minimal logic becomes `IPL⟨→,∧,∨,⊤⟩` as Matthew suggested above. It seems very unnatural to me to have a constructor with no semantics, even if that was the original treatment of Johanssen. It also makes the way Benjamin has stated the conservativity result, using the 'IsBotFree' predicate, more natural.
>
> I initially started with the 'encoding approach', axiomatising a minimal system then encoding the others with axioms, because it is very easy to lift structural results (weakening, etc) from smaller to larger systems. I'm now convinced we will want to consider various fragments, in which case it makes sense to have efq as a rule, but I think we should be careful with the design to ensure that manipulations on derivations can be carried out for those fragments — ideally this should also be ensured by the way a fragment is specified, rather than being reproved for each.
>
> Given that work to get the fragment design right, I think it should be postponed to later work, in which case we would forget about minimal logic for the moment.
>
> Does this sound like a reasonable compromise? I'd like also to get some input from other reviewers / maintainers if & when they have capacity. I'll review the PR properly once we've settled on the design, but a couple things I will flag now:
>
> - To me it seems like the addition of connective typeclasses is a separate development, perhaps you could just leave a review on the existing PR on the subject &/or help that get merged — the design seems very similar.
> - You mentioned adding back references and a link to the zulip thread, but I don't see that in the PR."

**Waring's two flags:**
- **(a)** Connective typeclasses are a separate development → do not bundle with foundation PR (see task 400).
- **(b)** References and Zulip-thread link are missing from the PR → must be in the cherry-pick.

**Waring's design acceptance:** efq should be a primitive rule; MPL becomes `IPL⟨→,∧,∨,⊤⟩` (a fragment without `⊥`/efq). Fragment design details are deferred to later work. The IPL-as-base / gated-efq design (task 398) is exactly the compromise Waring is asking for.

### Matthew Doty's Asks

- Small, reviewable pieces (msg 603062659, confirmed).
- `Bool`-valued semantics for DPLL (deferred to follow-up PR per ctchou/Waring).
- Heyting-algebra evaluate for generality (deferred to follow-up, flagged by Waring as right direction).

---

## Task 398 Completion — Foundation Is Ready

Task 398 (now COMPLETE) implemented efq as a primitive gated constructor in `NaturalDeduction/Basic.lean`:

- `efq {Γ A} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A`
- `[IsIntuitionistic T]` binder: efq is available at IPL/CPL, unconstructible at MPL.
- MPL metatheory (Hilbert, soundness, Lindenbaum, strong-completeness, conservativity chains) is preserved unchanged — efq is unconstructible at `AxiomTheory MinPropAxiom`.
- `## Implementation notes` in `Basic.lean` updated to state the IPL-as-base design with Zulip link at line 78.
- Full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake` all green.

The LOCAL fork `main` branch now contains this complete foundation, verified by CI.

---

## Precise Foundation File Scope

### IN Scope — Cherry-Pick

These files constitute the "propositional foundation" layer to cherry-pick into the new PR branch:

| File | What Changes | Notes |
|------|-------------|-------|
| `Cslib/Logics/Propositional/Defs.lean` | 5-primitive Proposition type; `imp` naming; `IsIntuitionistic (T : Theory Atom)` (new API); Theory instances; `subst` monad | **EXCLUDE** `public import Cslib.Foundations.Logic.Connectives` and the three typeclass instances (`PropositionalConnectives`, `HasAnd`, `HasOr`) — Waring flag (a) |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | 11 constructors (10 ungated + `efq` gated); `imp`/`impI`/`impE` naming; IPL-as-base `## Implementation notes`; restored references; Zulip link at line 78 | Full local fork main version — no exclusions needed |
| `references.bib` | Add: Johansson1937, Gentzen1935, Prawitz1965, TroelstraVanDalen1988, SorensenUrzyczyn2006, Avigad2022 (Church1956, ChagrovZakharyaschev1997 may also be needed depending on Defs.lean imports retained) | All entries already present in local fork `main`'s references.bib |

### OUT of Scope — Excluded from Cherry-Pick

| Content | Reason | Future Home |
|---------|--------|-------------|
| `Cslib/Foundations/Logic/Connectives.lean` | Waring flag (a): separate development; coordinate with fmontesi PR #607 | Task 400 |
| `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` derived rules (byContra, contra, lem, pierce, LEM/Pierce theories) | Not in IPL-base foundation; Waring asked for small pieces | Subsequent PR (DerivedRules) |
| Hilbert proof systems (`ProofSystem/`) | Later stacked PR | Task series after foundation |
| ND–Hilbert equivalence (`NaturalDeduction/Equivalence.lean`) | Later stacked PR | Task series after foundation |
| Algebraic semantics / MPL metatheory / conservativity chains (`Semantics/Algebra/`) | Later stacked PR; Waring suggested `GeneralizedHeytingAlgebra` direction | Later PRs |
| Kripke semantics (`Semantics/Kripke.lean`) | Later stacked PR | Later PRs |
| Sequent calculi LJ/LK (`SequentCalculus/`) | Later stacked PR | Later PRs |
| Tableau systems (`Tableau/`) | Later stacked PR | Later PRs |

### Critical Structural Issue: Theory.lean

**Upstream/main** has `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` (26 definitions/instances) that:
1. Uses the OLD `IsIntuitionistic Atom (S : InferenceSystem) [Bot Atom]` API
2. Is imported directly by the `Cslib.lean` barrel
3. Provides derived rules: `efqCtx`, `efqRule`, `contra`, `byContra`, `lem`, `pierce`, `LEM`, `Pierce`, `instIsClassicalLEM`, `instIsClassicalPierce`

**Local fork main** does NOT have `Theory.lean` — its content was absorbed into the new `Defs.lean` (the instances `instIsIntuitionisticIPL`, `instIsClassicalCPL`, `instIsIntuitionisticIntuitionisticCompletion` are now in Defs.lean). The derived rules (`byContra`, etc.) moved to `DerivedRules.lean`.

**Implication for the cherry-pick branch**: If the new `Defs.lean` is applied to a branch from upstream/main, `Theory.lean` will **fail to compile** because it uses the old `IsIntuitionistic` API. The cherry-pick commit must therefore:

**Option A (Recommended): Delete Theory.lean from the PR**
- Delete `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean`
- Remove its import from `Cslib.lean`
- The Defs.lean new version already includes the core instances; derived rules (byContra etc.) deferred to a follow-up DerivedRules PR

**Option B: Update Theory.lean in the same commit**
- Rewrite Theory.lean to use the new IsIntuitionistic API
- Keep the derived rules live in upstream
- Slightly expands the cherry-pick scope but keeps derived rules available

The research recommendation is **Option A** (delete Theory.lean + remove from barrel), matching the local fork main design. This keeps the cherry-pick tightly scoped to the foundation. The derived rules (`byContra`, `contra`, `lem`, `pierce`) are available on local fork main in `DerivedRules.lean` and can be submitted in a subsequent small PR.

---

## Cherry-Pick / Branching Strategy

### Branch Creation

```bash
# Start from current upstream/main
git fetch upstream
git checkout -b feat/propositional-foundation upstream/main
```

### Files to Modify in the Commit

**1. `Cslib/Logics/Propositional/Defs.lean`**

Take the local fork main version (currently at HEAD) **except**:
- Remove line 10: `public import Cslib.Foundations.Logic.Connectives`
- Remove lines 113–124: the three typeclass instance registrations (PropositionalConnectives, HasAnd, HasOr)

The resulting file contains: 5-primitive Proposition type, notation, subst monad, Theory, IsIntuitionistic/IsClassical definitions and instances, `intuitionisticCompletion`.

**2. `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`**

Take the local fork main version (currently at HEAD) as-is. This file:
- Does NOT import Connectives.lean (only imports Defs and InferenceSystem)
- Contains 11 constructors including gated `efq`
- Has the full `## Implementation notes` with IPL-as-base design, Zulip link, and restored references

**3. `Cslib.lean`** (barrel)

Remove the line:
```
public import Cslib.Logics.Propositional.NaturalDeduction.Theory
```

**4. `references.bib`**

Add the six entries present on local fork main but absent from upstream/main:
- `Johansson1937` — Der Minimalkalkül
- `Gentzen1935` — Untersuchungen über das logische Schließen
- `Prawitz1965` — Natural Deduction: A Proof-Theoretical Study
- `TroelstraVanDalen1988` — Constructivism in Mathematics
- `SorensenUrzyczyn2006` — Lectures on the Curry-Howard Isomorphism
- `Avigad2022` — Mathematical Logic and Computation

### Files to DELETE in the Commit

**1. `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean`**

This file's instances (instIsIntuitionisticIPL, instIsClassicalCPL) are now in the new `Defs.lean`. The derived rules it provides (byContra, contra, lem, pierce, LEM, Pierce, instIsClassicalLEM, instIsClassicalPierce) will be absent until a follow-up `DerivedRules` PR.

### Summary Diff

```
Files modified:  Defs.lean, Basic.lean, Cslib.lean (1 line removed), references.bib (6 entries)
Files deleted:   NaturalDeduction/Theory.lean
Files NOT touched: Connectives.lean (does not exist in upstream/main and is excluded)
```

### Single Focused Commit Message (draft — human to finalize)

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
  TroelstraVanDalen1988, SorensenUrzyczyn2006, Avigad2022
- Delete NaturalDeduction/Theory.lean (instances absorbed into Defs.lean)
- Cslib.lean: remove Theory import

Connective typeclasses (PropositionalConnectives, HasBot, HasImp, HasAnd,
HasOr) are excluded per reviewer request; see PR #607 and task 400.
Derived rules (byContra, lem, pierce) follow in a separate PR.
Hilbert systems, semantics, sequent calculi, and tableau follow as
stacked PRs.
```

---

## PR Description Scaffolding (Human-Authored Draft Points)

The following are **factual inputs only** — the user must write the actual human-authored PR description (AI policy). Key points to cover:

**What changed:**
- `⊥` is now a primitive constructor of `Proposition Atom` (not simulated via `[Bot Atom]`)
- `efq` (ex falso quodlibet) is a primitive gated constructor of `Theory.Derivation`, gated on `[IsIntuitionistic T]`
- IPL is the base logic: efq is available exactly when the theory validates explosion
- MPL is retained as a fragment: `AxiomTheory MinPropAxiom` admits no `IsIntuitionistic` instance, so efq is unconstructible there
- `impl`/`implI`/`implE` renamed to `imp`/`impI`/`impE`
- References restored: Johansson 1937, Gentzen 1935, Prawitz 1965, Troelstra & van Dalen 1988, Sørensen & Urzyczyn 2006, Avigad 2022
- Zulip thread link added to `## Implementation notes`

**What's excluded (and why):**
- Connective typeclasses: separate development, see PR #607 (fmontesi) — task 400
- Semantics: deferred per Waring's earlier request (separate PR)
- Hilbert/equivalence/conservativity: stacked PRs

**Design trade-off note:**
The `## Implementation notes` section of `Basic.lean` now states both sides of the MPL/IPL-base debate (per Waring's earlier request for neutral documentation) and links to this Zulip thread.

---

## Zulip Message Scaffolding (Human-Authored Draft Points)

AI policy: Zulip messages must be human-authored. These are factual inputs only.

To respond to Waring's closing message (606970606) after the PR is ready:

**Points to convey:**
- Task 398 implemented efq as gated primitive constructor per Waring's closing suggestion; this is now on fork main with full CI green
- The connective typeclasses have been removed from the foundation PR (Waring flag a); see task 400 for coordination with PR #607
- References and Zulip-thread link are now in the PR (Waring flag b)
- Foundation cherry-pick from upstream/main will be a single focused commit (Defs.lean + Basic.lean + references)
- Welcoming Waring's formal review once the PR is updated

---

## Coordination with PR-Readiness Vet Tasks 386/387/389

These tasks apply to LOCAL fork main (not the upstream foundation PR):

- **Task 386** (Fix lake lint errors, 21 violations): Fixes PL-specific lint violations (defsWithUnderscore, defLemma, docBlame, unusedArguments, simpNF) that MUST be resolved before the Propositional metatheory PRs. Does not block the foundation cherry-pick PR since that PR contains only Defs.lean + Basic.lean + references.bib, which have clean lint.
  
- **Task 387** (PL → Propositional namespace rename): UPSTREAM-GATED. The foundation PR exposes `namespace Cslib.Logic.PL` publicly. The renaming decision requires upstream maintainer consensus (human-authored Zulip thread). Flag as pending in the foundation PR description. Does not block submission.

- **Task 389** (docBlame, barrel headers, unusedSectionVars, broken citation): Fixes for Tableau barrels, HilbertAlgebra docstrings, unusedSectionVars. Separate from foundation PR.

**Key coordination point**: The foundation PR is clean for submission now (CI green on local fork main for foundation files). Tasks 386/387/389 address downstream files that are NOT part of the foundation cherry-pick. They do not block the foundation PR but will be needed for subsequent stacked PRs.

---

## Open Questions

1. **Theory.lean derived rules**: The cherry-pick deletes `Theory.lean`, which removes `byContra`, `contra`, `lem`, `pierce`, `LEM`, `Pierce`, `instIsClassicalLEM`, `instIsClassicalPierce` from upstream/main until a follow-up PR. Is this acceptable scope restriction, or should the foundation PR include a minimal Theory.lean update?

2. **Defs.lean API change scope**: The new `IsIntuitionistic (T : Theory Atom)` class has a different API than the old `IsIntuitionistic Atom (S : InferenceSystem)`. Any upstream code that uses the old API will need updating. Are there other upstream files (beyond Theory.lean) that use this class?
   - Quick check shows only Theory.lean in upstream/main imports or uses `IsIntuitionistic` directly. The barrel imports Defs and Basic and Theory only from the Propositional module; no other upstream files import from `Cslib.Logics.Propositional.NaturalDeduction.Theory`.

3. **`impl` → `imp` rename**: This rename affects any user code that calls `implI`/`implE`/`implE₁` etc. upstream/main currently has the old naming in Theory.lean only (which is being deleted). No other upstream files in the barrel import the old Basic.lean constructors directly. The rename is backward-breaking for downstream users but Theory.lean is the only upstream consumer. Confirm this before submitting.

4. **Namespace `PL` vs `Propositional`**: See task 387. Flag in PR description, no action required now.

5. **References coverage**: `Church1956` and `ChagrovZakharyaschev1997` appear in local Defs.lean comments. Confirm they are needed in the cherry-pick version (after Connectives.lean is removed) and add their bib entries if so. Both are present in local fork main's references.bib.

---

## Requested Changes Summary

Based on reviewer and Zulip feedback, the cherry-pick PR must address:

| Item | Status |
|------|--------|
| `⊥` as primitive constructor | Done (task 398, CI green) |
| efq as primitive gated ND rule | Done (task 398, CI green) |
| References restored (Johansson, Gentzen, Prawitz, etc.) | Done on local main (in references.bib and Basic.lean docstring) |
| Zulip-thread link in Basic.lean | Done on local main (Basic.lean line 78) |
| Remove semantics files | Done (not in local fork main propositional foundation) |
| Modern English references (Avigad 2022) | Done (references.bib has Avigad2022) |
| Connective typeclasses excluded | Must be excluded in the cherry-pick (remove from Defs.lean) |

---

## Next Steps for the User

1. Run `bash .claude/scripts/update-task-status.sh preflight 399 research sess_1782661425_115d26_399` to mark task 399 as [RESEARCHING].
2. Review this report, especially the "Critical Structural Issue: Theory.lean" section.
3. Decide on Option A vs B for Theory.lean handling.
4. Proceed to planning (`/plan 399`) to generate the detailed step-by-step for creating the cherry-pick branch and preparing the PR description.
5. After plan is created, the user executes: create branch from upstream/main, apply file changes, verify CI green, then write PR description and Zulip message in their own words (AI policy).

---

## Orchestrator Handoff

```json
{
  "status": "researched",
  "task_number": 399,
  "task_slug": "refresh_pr648_ipl_base_foundation",
  "artifacts": [
    {
      "type": "research_report",
      "path": "specs/399_refresh_pr648_ipl_base_foundation/reports/01_pr648-refresh-research.md"
    }
  ],
  "key_findings": {
    "pr_state": "open, 11 commits behind upstream/main (not 239), merge base at PR #536",
    "waring_flags": ["(a) connective typeclasses excluded", "(b) references + Zulip link missing from PR — now fixed on local main"],
    "foundation_scope": "Defs.lean (no Connectives.lean) + Basic.lean (with gated efq) + references.bib",
    "structural_blocker": "Theory.lean must be deleted (or updated) in the cherry-pick; it uses old IsIntuitionistic API",
    "task_398_complete": true,
    "ci_green": true,
    "ai_policy": "PR description and Zulip message must be human-authored"
  }
}
```
