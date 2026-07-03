# Research Report: Cleanly divide overlapping modal PRs and coordinate with #607

- **Task**: 476 — divide_modal_prs_coordinate_607
- **Type**: cslib (PR coordination + design analysis)
- **Session**: sess_1783062822_5d09a2
- **Date**: 2026-07-03
- **Status**: researched
- **Agent**: cslib-research-agent
- **Builds on**: task 475 (`specs/475_fix_and_stack_pr_662_on_648/`), tasks 468/469/472/474
- **Method**: read-only `gh` (PR view/diff/checks, `gh api` reviews/comments/CI logs), read-only
  `git show` of fetched branches, reading of task-475 artifacts. **No branch was modified. No push,
  rebase, or force-push. Nothing posted to GitHub or Zulip. No throwaway build was needed** — the
  #607 CI failure is already fully diagnosed from CI logs (§4.3).

## Executive Summary

- **Four PRs, one shared pressure point**: all four touch the connective/operator typeclass layer
  and/or the modal semantics. The genuinely mutually-exclusive conflict is **only** between #607 and
  #662 over `Modal/Basic.lean`'s primitive constructor set. #648 (propositional) and #649 (LTL) are
  **not** in hard conflict with #607 — they overlap only on `Propositional/Defs.lean` and
  `references.bib`, which are reconcilable.
- **The central decision is @fmontesi's** (maintainer + owner of the earlier PR #607): keep the
  current **diamond-inclusive** primitive set `{atom, not, and, diamond}` (#607's basis, with
  `box := ¬◇¬`), or move to **box-primitive** `{atom, bot, imp, box}` (#662, with `diamond := ¬□¬`).
  These are incompatible: merging #662 deletes the `Proposition.diamond`/`.not`/`.and` constructors
  that #607's `HasDiamond`/`HasNot`/`HasAnd` instances are built on. §5 frames the tradeoffs.
- **Recommended clean division** (§2): **#607 owns the operator-typeclass layer**
  (`Foundations/Logic/Operators/*`), **#662 owns the modal semantics**
  (`Modal/Basic/Denotation/LogicalEquivalence`), **#648 owns the propositional formula type**, **#649
  owns LTL**. #662 has already built `HasBot` + the `PropositionalConnectives`/`ModalConnectives`
  bundles that #607 lacks — these can be **offered to #607** as a contribution (§2.3), resolving the
  one-class-per-operator vs bundled-class question that reviewers raised.
- **#607 is landable with modest work, and the CI failure is NOT its fault**: #607's `ci-checks`
  failure is an *upstream-drift* breakage in `Cslib/Logics/HML/LogicalEquivalence.lean` (a file #607
  never touches), caused by being **15 commits behind** `main` across Mathlib bumps. A rebase onto
  `main` should clear it. The substantive review asks are small and concrete (§4).
- **#662-on-#607 migration is a conditional, gated plan** (§6): it MUST wait until the box-vs-diamond
  direction is agreed with @fmontesi (returns **23 July**). Prematurely coupling #662 to unmerged
  #607 is exactly the risk task 469 avoided by choosing self-own Option A.

## 1. PR characterization & current state (read-only, 2026-07-03)

| | #607 | #648 | #649 | #662 |
|---|---|---|---|---|
| Title | feat(Logic): logical operators | feat(Propositional): five-primitive formula, primitive bot | feat(LTL): LTL formula + ω-word semantics | feat(Modal): refactor primitives to {atom,bot,imp,box} |
| Author | **fmontesi** (maintainer) | benbrastmckie | benbrastmckie | benbrastmckie |
| Head branch | `fmontesi/connectives` | `feat/propositional-v2` | `feat/temporal-formula-propositional` | `feat/modal-formula-primitives` |
| Head repo | **leanprover** (in-org branch) | benbrastmckie (fork) | benbrastmckie (fork) | benbrastmckie (fork) |
| Base | main | main | main | main |
| State | OPEN | OPEN | OPEN | OPEN |
| Mergeable | MERGEABLE | MERGEABLE | **CONFLICTING (DIRTY)** | MERGEABLE |
| mergeState | BLOCKED | BLOCKED | DIRTY | BLOCKED |
| Review decision | **CHANGES_REQUESTED** | CHANGES_REQUESTED | CHANGES_REQUESTED | REVIEW_REQUIRED |
| CI `ci-checks` | **FAIL** (upstream drift, §4.3) | PASS | PASS | PASS |
| Commits behind main | **15** | 5 | 5 | 1 |
| # commits | 15 | 5 | 5 | 1 |

Notes:
- #607's head branch lives **inside the leanprover org** (not a fork). This is why the hard
  constraint matters doubly: we have write access in principle, so discipline (review/comments only,
  never push) is essential.
- #649 is the only branch with a **git conflict** against main (needs its own rebase; it is the least
  entangled with the #607/#662 core conflict — see §2.4).
- #662 is only 1 behind main and CI-green; #648 is 5 behind and CI-green. These two are the healthy
  branches. (Task 475 already analyzed #662↔#648 stacking; this report does not re-derive it.)

### 1.1 File-overlap matrix

Legend: ✎ = modifies, ＋ = adds new file, — = untouched.

| File | #607 | #648 | #649 | #662 |
|---|---|---|---|---|
| `Cslib/Foundations/Logic/Operators/{And,Or,Not,Impl,Box,Diamond,Iff,Tensor}.lean` | ＋ (8 files) | — | — | — |
| `Cslib/Foundations/Logic/Connectives.lean` | — | — | ＋ (106) | ＋ (91) |
| `Cslib/Foundations/Logic/LogicalEquivalence.lean` | ✎ (+18/−5) | — | — | — |
| `Cslib/Logics/Modal/Basic.lean` | ✎ (+58/−18) | — | — | ✎ (+183/−92) |
| `Cslib/Logics/Modal/Denotation.lean` | ✎ (+1/−1) | — | — | ✎ (+18/−7) |
| `Cslib/Logics/Modal/LogicalEquivalence.lean` | ✎ (+2/−2) | — | — | ✎ (+128/−90) |
| `Cslib/Logics/Modal/Cube.lean` | — | — | — | ✎ (+1) |
| `Cslib/Logics/Propositional/Defs.lean` | ✎ (+16/−6) | ✎ (+40/−50) | ✎ (+69/−38) | — |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | — | ✎ (+99/−65) | ✎ (+78/−71) | — |
| `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` | — | ✎ (+39/−48) | ✎ (+55/−36) | — |
| `Cslib/Logics/LTL/Syntax/Formula.lean` | — | — | ＋ (136) | — |
| `Cslib/Logics/LTL/Semantics/Satisfies.lean` | — | — | ＋ (70) | — |
| `Cslib/Logics/LinearLogic/CLL/Basic.lean` | ✎ (+1/−1) | — | — | — |
| `Cslib.lean` (module registry) | ✎ (+8) | — | ✎ (+3) | ✎ (+1) |
| `CslibTests/GrindLint.lean` | — | — | — | ✎ (+4) |
| `references.bib` | — | ✎ (+42) | ✎ (+107) | ✎ (+18) |

**Hard-conflict cells** (mutually exclusive designs, cannot both merge as-is):
- `Modal/Basic.lean` — **#607 vs #662** (the core conflict; §5).
- `Modal/Denotation.lean`, `Modal/LogicalEquivalence.lean` — #607 vs #662 (follow from Basic).

**Soft-conflict cells** (overlap, reconcilable by choosing one design + rebase):
- `Propositional/Defs.lean` — touched by #607, #648, #649. #648 is authoritative (primitive `⊥`,
  five-primitive type). #607's edits here are minor `HasAnd`/`HasOr` instance registrations that
  would move to #607's own Operators layer or be dropped once #648's type lands. #649 re-ships a
  stale copy (task-475 §3 pattern) and must rebase onto #648.
- `Foundations/Logic/Connectives.lean` — added by both #649 and #662 (near-identical, both
  self-owned interim files). Only one can land; the operator layer ultimately belongs in #607's
  `Operators/*` (§2).

### 1.2 references.bib conflict detail

`gh pr diff` of the `references.bib` hunks:

| BibKey | #607 | #648 | #649 | #662 | Conflict |
|---|---|---|---|---|---|
| `Avigad2022` | — | ＋ | ＋ | ＋ | **Triple-added** — will collide on any two-way merge; de-dup to one entry. |
| `Gentzen1935` | — | ＋ (`@incollection`, English) | ＋ (`@article`, German) | — | **Double-added with different entry types/titles** — reconcile to one canonical entry. |
| `Prawitz1965` | — | ＋ | ＋ | — | Double-added; de-dup. |
| `TroelstraVanDalen1988` | — | ＋ | ＋ | — | Double-added; de-dup. |
| `ChagrovZakharyaschev1997` | — | — | — | ＋ | **#662-unique** (modal); no conflict. Keep with #662. |
| `Church1956`, `Johansson1937`, `McKinsey1939`, `Wajsberg1938` | — | — | ＋ | — | #649-unique (propositional/minimal-logic); keep with #649. |
| `Kamp1968`, `Pnueli1977`, `VardiWolper1986` | — | — | ＋ | — | #649-unique (temporal); keep with #649. |

**Key finding**: **#607 does NOT touch `references.bib`** (not in its file list). The
"triple-added Avigad2022" is across **#648 / #649 / #662**, not #607. Whichever propositional PR lands
first should own the canonical `Avigad2022`, `Gentzen1935`, `Prawitz1965`, `TroelstraVanDalen1988`
entries; downstream PRs drop their duplicates on rebase.

## 2. Clean-division recommendation

**Principle** (reuse-first + one-concern-per-PR, matching @fmontesi's "one at a time" request): each
PR owns exactly one layer, imports rather than re-defines the layers below it.

```
Layer 3  LTL              → #649   (Logics/LTL/*)          imports Propositional + Connectives layer
Layer 3  Modal semantics  → #662   (Logics/Modal/*)        imports operator layer
Layer 2  Propositional    → #648   (Logics/Propositional/*) imports operator layer
Layer 1  Operator layer   → #607   (Foundations/Logic/Operators/*, bundles)  foundation, no deps
```

### 2.1 #607 owns the operator-typeclass layer

`Foundations/Logic/Operators/{And,Or,Not,Impl,Box,Diamond,Iff,Tensor}.lean` — one class per operator,
scoped notation, `Cslib.Logic` namespace. This is #607's genuine, foundational contribution and
nothing else should define these classes. Reviewers (eric-wieser, chenson2018, ctchou) want the
**file granularity revisited** (§4.2) — that is a #607-internal decision, but the *ownership* is clear.

### 2.2 #662 owns the modal semantics

`Modal/Basic.lean` (the `Proposition` inductive + `Satisfies` + K/T/B/4/5/D), `Modal/Denotation.lean`,
`Modal/LogicalEquivalence.lean`. Once #607's operator layer lands, #662 **imports** `Operators/{Box,
Impl,Bot,…}` instead of shipping its interim `Foundations/Logic/Connectives.lean` (§6).

### 2.3 What #662 built that it can OFFER to #607

#662's self-owned `Foundations/Logic/Connectives.lean` (verified via `git show`) contains exactly the
pieces #607 is missing:

| #662 provides | #607 has? | Offer to #607? |
|---|---|---|
| `HasBot` (atomic class) | **No** | **Yes** — #607 relies on Mathlib `Bot`; a dedicated `HasBot` in the Operators family is the natural home. |
| `HasImp` / `imp` | #607 has `HasImpl` / `impl` | **Naming decision** (§2.5) — pick one spelling. |
| `HasBox`, `HasAnd`, `HasOr` | Yes (`Operators/{Box,And,Or}`) | Already covered by #607. |
| `PropositionalConnectives` bundle (`extends HasBot, HasImp`) | **No** | **Yes** — #607 "LACKS bundled classes"; this fills the gap. |
| `ModalConnectives` bundle (`extends PropositionalConnectives, HasBox`) | **No** | **Yes** — same. |
| `HasDia` **deferred** (classical `◇ := ¬□¬`; note that non-classical IK/CK needs a primitive `HasDia`) | #607 has `HasDiamond` (primitive) | Design-linked to §5. |

**Recommendation**: benbrastmckie offers the `HasBot` + `PropositionalConnectives`/`ModalConnectives`
bundle definitions to #607 (as a code suggestion or a small follow-up PR fmontesi can cherry-pick),
so the operator layer lands **complete** in #607 and #662/#648/#649 all just import it. This directly
answers chenson2018/ctchou's "should these be bundled?" and eric-wieser's "one file" comments.

### 2.4 Where #648 (propositional) and #649 (LTL) fit

- **#648** owns the propositional `Proposition` type (primitive `⊥`, five constructors) and its
  natural deduction. It is CI-green, only 5 behind, and its overlap with #607 is limited to a few
  `HasAnd`/`HasOr` instance lines in `Propositional/Defs.lean` — trivially reconciled once #607's
  classes are the single source. **#648 is the least controversial and could land first / in parallel
  with #607.**
- **#649** owns LTL (`Logics/LTL/*`). It currently **re-ships stale copies** of #648's propositional
  files and its own `Connectives.lean`, and is **git-conflicting** with main. #649 should be **rebased
  onto #648** (inherit the propositional layer) and **onto #607** (inherit the operator layer),
  dropping its interim `Connectives.lean`. It is downstream of both and should land last. It is *not*
  part of the box-vs-diamond conflict.

### 2.5 The one naming decision inside the operator layer

`HasImpl.impl` (#607) vs `HasImp.imp` (#662/#648). benbrastmckie already flagged this
(issue-comment 2026-06-17) and prefers `imp` (consistency with `impI`/`impE` rule prefixes and
FormalizedFormalLogic). fmontesi has not ruled. This is a **#607-owned decision**; whichever spelling
#607 adopts, #648/#649/#662 conform. Recommend surfacing it as an explicit question in the #607
review (§4.4).

## 3. The two designs, precisely

### 3.1 #607 (current basis): diamond-inclusive primitives

`Modal/Basic.lean` keeps `inductive Proposition := atom | not | and | diamond` and *derives* the
rest:
- `or φ₁ φ₂ := ¬(¬φ₁ ∧ ¬φ₂)`, `impl φ₁ φ₂ := ¬φ₁ ∨ φ₂`, `iff := (→)∧(→)`, `box φ := ¬◇¬φ`.
- Registers `instance : HasNot / HasAnd / HasDiamond / HasOr / HasImpl / HasIff / HasBox`.
- Adds `@[scoped grind =] Proposition.{not,and,diamond,or,impl,iff,box}_def` bridge lemmas
  (`φ.and ψ = (φ ∧ ψ) := rfl` etc.) so `grind` sees through the notation.
- `Satisfies` characterisations become `rfl`/`grind` (e.g. `not_iff_not`, `and_iff_and`,
  `diamond_iff_exists`, `box_iff_forall`).

### 3.2 #662: box-primitive `{atom, bot, imp, box}`

`Modal/Basic.lean` uses `inductive Proposition := atom | bot | imp | box` and derives
`not φ := imp φ ⊥`, `and`, `or`, `diamond φ := ¬□¬φ`. Necessitation is a **pure rule** stated in
`box` alone (`⊢ φ → ⊢ □φ`), K stays a pure axiom; `HasDiamond`/`HasDia` is **deferred** (classical
`◇ := ¬□¬`). `Connectives.lean` supplies `ModalConnectives` (bundled).

### 3.3 Why they cannot coexist in `Modal/Basic.lean`

They define **different constructors** for the same type `Modal.Proposition`. #607's instances
`HasNot := {not := Proposition.not}` and `HasDiamond := {diamond := Proposition.diamond}` reference
constructors (`.not`, `.diamond`) that **do not exist** in #662's `{atom,bot,imp,box}` set (there
`not`/`diamond` are `def`s, not constructors). Merging #662 invalidates #607's instance bodies and
its `_def` `rfl` lemmas. Hence a single maintainer decision is required before either modal PR lands.

## 4. Substantive #607 review material (DRAFT — do NOT post; human approval required)

> All text in §4.4 and §7 is **draft** for later human-approved posting via GitHub review / Zulip.
> Nothing here has been or should be posted by the agent.

### 4.1 What is genuinely good about #607 (lead with this — it is @fmontesi's earlier work)

- Clean, minimal **one-class-per-operator** design with good docstrings and scoped notation; the
  `Cslib.Logic` namespace and `@[inherit_doc]` notation are idiomatic.
- The `_def` bridge-lemma pattern (`φ.and ψ = (φ ∧ ψ) := rfl`, tagged `@[scoped grind =]`) is a
  thoughtful fix to the exact grind-through-notation problem chenson2018/thomaskwaring raised — and
  fmontesi already marked it "Should be ok now."
- Reuses Mathlib `Bot`/`Top` (so `not_eq := rfl` already), consistent with CSLib's reuse-first ethos.
- Keeps the modal `Satisfies` characterisations as `rfl`/`grind` one-liners — very readable.

### 4.2 What the CHANGES_REQUESTED / review comments actually target

The blocking review is **chenson2018's CHANGES_REQUESTED (2026-05-29)**; eric-wieser's three reviews
are **COMMENTED** (not blocking) but carry weight. Consolidated open threads:

1. **File granularity** (chenson2018, eric-wieser, ctchou): should the 8 per-operator files be merged?
   - eric-wieser: "merge all these operators into a single `LogicOperators` file" (one docstring for
     the conventions).
   - ctchou: proposes 3 files — `Modal` (box+diamond), `Tensor`, `Propositional` (the rest); also
     asks "do we need parameterized box/diamond for HML?".
   - fmontesi (open): "I don't know yet… we'll know more once we get there."
   - **Status: unresolved design question, likely the main thing blocking merge.**
2. **grind/simp lemma direction** (chenson2018, thomaskwaring): are the `simp`/`grind =` lemmas
   "backwards"? They should simplify *into* the notation (like `List.append_eq`), and grind should be
   given `Satisfies`-notation lemmas (`⇓Modal[m,w ⊨ φ₁ ∧ φ₂] = …`) rather than unfolding `Satisfies`.
   - fmontesi replied "Should be ok now" — **verify this thread is resolved**; if the `_def` lemmas
     now point the right way it can be marked done.
3. **`grind?` at `Basic.lean:196`** (chenson2018): "This should not be undone, `grind?` still fails
   here." — a specific spot to re-check.
4. **`Has` prefix** (eric-wieser): "largely a Lean 3-ism." fmontesi defended the convention
   (`HasX` for canonical `X` when `X` is parametrised; matches `HasSubstitution`/`HasFresh`).
   **Status: maintainer has a stated policy; likely resolved as "keep `Has`".**
5. **Instance sugar** (eric-wieser): `instance : HasAnd (Proposition Atom) where and := .and` is
   cleaner than the record form. Easy accept.

### 4.3 The CI failure is upstream drift, not a #607 defect (important, verified)

`gh run view 27601699542 --log-failed`: the failure is
```
error: Cslib/Logics/HML/LogicalEquivalence.lean:105:11: failed to synthesize instance …
error: Cslib/Logics/HML/LogicalEquivalence.lean:106:58: Application type mismatch …
```
**`HML/LogicalEquivalence.lean` is a file #607 does not touch.** The break comes from #607 being **15
commits behind main** across Mathlib bumps / the `Relation` split (same drift pattern task-475 §12-R1
noted for #662). A **rebase onto current `main`** should clear CI. This is a friendly, concrete,
low-effort ask for fmontesi and should be framed as "your PR is fine; it just needs a rebase to pick
up the Mathlib bumps that already fixed HML on main."

### 4.4 DRAFT review comment for #607 (for later human approval)

> Thanks for this, Fabrizio — the one-class-per-operator layer reads cleanly and the
> `@[scoped grind =] _def` bridge lemmas are a nice fix for the grind-through-notation issue raised
> earlier. A few coordination notes, no rush given you're back on the 23rd:
>
> 1. **CI**: the current red `ci-checks` is not from this PR's code — it's `HML/LogicalEquivalence.lean`
>    failing to synthesize an instance because the branch is ~15 commits behind `main` (Mathlib bumps
>    + the `Relation` split already fixed HML on `main`). A rebase onto `main` should turn it green.
> 2. **File granularity** (picking up chenson2018/eric-wieser/ctchou): happy to go whichever way you
>    prefer — one `LogicOperators` file, or ctchou's `Modal`/`Tensor`/`Propositional` split. If it
>    helps, I can send the `HasBot` class plus bundled `PropositionalConnectives`/`ModalConnectives`
>    classes I've prototyped so the operator layer lands complete here and everything downstream just
>    imports it.
> 3. **Naming**: `HasImpl.impl` here vs `HasImp.imp` in the propositional/modal work — I lean `imp`
>    (matches the `impI`/`impE` rule prefixes and FormalizedFormalLogic), but your call as owner of
>    this layer; I'll conform whichever you pick.
> 4. **Modal primitives**: separately (Modal Zulip thread) there's the box-primitive vs
>    diamond-primitive question for `Modal/Basic.lean` — that's the one design choice that decides
>    whether the `HasDiamond`/`HasNot` instances here stay as-is. I've written up the tradeoffs; keen
>    to align with you before either modal PR moves.

*(Do not post until user approves. Prefer posting #1 as a plain comment and #2–#4 as review
discussion, not as code "suggestions" on his branch.)*

## 5. Box-vs-diamond primitive framing (for @fmontesi, the maintainer)

Framed as a decision, with concrete consequences. **This is fmontesi's call.**

| Dimension | Diamond-inclusive `{atom,not,and,diamond}` (#607 basis) | Box-primitive `{atom,bot,imp,box}` (#662) |
|---|---|---|
| Necessitation rule | Stated via derived `box := ¬◇¬`; the rule mixes `diamond`+`not` under the hood. | **Pure**: `⊢ φ ⇒ ⊢ □φ` in `box` alone. Cleaner for K/necessitation metatheory. |
| K axiom | `□(φ→ψ)→(□φ→□ψ)` expands through `¬◇¬` — provable but noisier. | Stated directly on primitive `box`. |
| `⊥` handling | `⊥` via `[Bot Atom]` side-condition / Mathlib `Bot`; `not_eq := rfl` already. | Primitive `bot` ⇒ substitution-invariant, free-algebra property; `not := imp · ⊥` unconditional. |
| `HasDiamond`/`HasNot` instances | **Present & primitive** (`.diamond`, `.not` constructors). | `diamond`/`not` are **derived defs**; primitive `HasDia` **deferred** (needed only for IK/CK non-classical modal). |
| Classical vs non-classical | Diamond primitive is fine classically; awkward if IK/CK later wants independent `□`,`◇`. | Box primitive + derived `◇=¬□¬` is the standard classical choice; IK/CK cleanly add a primitive `HasDia` later. |
| Downstream proof churn | #607's `Satisfies.{diamond_iff_exists,box_iff_forall}` are `rfl`. | #662 re-proves K/T/B/4/5/D via `simp only [Satisfies]; intro` (deliberately, not `grind`). |
| Free-algebra / substitution | `⊥ = atom ⊥` lies in image of `atom` ⇒ substitution can rewrite falsum (not free algebra). | Primitive `bot`/`imp` ⇒ genuine free algebra over the signature; substitution-invariant. |
| Alignment with #662/#648 | Requires #648 (primitive `⊥`) and #662 to bend back to diamond/atom-⊥. | Consistent with #648's primitive-`⊥` propositional type already merged direction. |

**Trade-off summary for Fabrizio**:
- **Choose box-primitive (#662)** if the priority is clean necessitation/K rules, substitution
  invariance / free-algebra formula type, and forward-compatibility with intuitionistic/minimal modal
  logics (IK/CK) via a later `HasDia`. Cost: #607's `HasDiamond`/`HasNot` primitive instances are
  dropped, and the modal characterisations are `simp;intro` rather than `rfl`.
- **Choose diamond-inclusive (#607 basis)** if the priority is keeping the already-reviewed #607
  modal edits intact with `rfl` characterisations and minimal near-term churn. Cost: `⊥`-as-`atom`
  breaks the free-algebra property, reintroduces `[Bot Atom]` side-conditions, and makes a future IK/CK
  extension harder.
- The two propositional/modal PRs (#648 primitive-`⊥`, #662 box-primitive) already point the
  **box-primitive** way and are CI-green; #607's operator *layer* is orthogonal and lands either way.
  So the recommendation to fmontesi is: **let the operator layer (#607) land independently, and adopt
  box-primitive for the modal semantics (#662)** — but this is explicitly his decision and should be
  offered, not asserted.

## 6. #662-on-#607 migration steps (CONDITIONAL — gated on design agreement)

**Precondition (hard gate)**: do NOT begin until (a) fmontesi agrees the box-primitive direction (or
the joint plan is settled) AND (b) #607's operator layer has landed on `main` (or is stable enough to
target). Prematurely coupling #662 to unmerged #607 is the exact anti-pattern task 469 avoided; until
then #662 keeps its self-owned `Connectives.lean` (task-475 Option A).

Once gated open, the restructure (all local + gated push per task-475 §11):

1. **Rebase #662 onto landed #607/main**
   `git rebase --onto <607-merged-main> e0573fbc feat/modal-formula-primitives` (or rebuild on the
   #648 stack per task-475 §10 Step 2). Resolve Mathlib-bump drift.
2. **Drop the interim typeclass file**
   `git rm Cslib/Foundations/Logic/Connectives.lean` — its role is now filled by #607's
   `Operators/*` + the bundles (which #662 offered to #607 in §2.3).
3. **Re-point imports** in `Modal/Basic.lean`: replace
   `public import Cslib.Foundations.Logic.Connectives` with
   `public import Cslib.Foundations.Logic.Operators.Box` /`…Impl`/`…Bot` (+ `And`/`Or`/`Not` as
   needed), matching #607's namespace (`Cslib.Logic`) and chosen `imp`/`impl` spelling.
4. **Register `ModalConnectives`** for `Modal.Proposition` against #607's classes (or against the
   bundle if #607 accepted the offered bundles). Adjust `not`/`diamond` derivations to #607's
   `HasImpl`/`HasBox` API.
5. **Reconcile `references.bib`**: keep `ChagrovZakharyaschev1997` (#662-unique); drop the duplicate
   `Avigad2022` (inherit the canonical entry from whichever propositional PR landed first).
6. **Re-run full CI** on the restructured branch (local, in a throwaway/backup branch first):
   `lake build && lake test && lake exe checkInitImports && lake exe lint-style &&
   lake shake --add-public --keep-implied --keep-prefix`. Zero-debt: no `sorry`/axiom patch — if a
   modal proof breaks under #607's derived `box`, fix structurally or mark BLOCKED.
7. **Push only after explicit user approval** (`--force-with-lease`); keep `backup/*` branches until
   GitHub CI is green (task-475 §11 gates D1–D7 apply).

## 7. DRAFT Zulip coordination note (do NOT post; human approval required)

Thread: `CSLib > Modal Logic`,
https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/607842603 .
fmontesi returns **23 July**; earlier he flagged PR-size overwhelm and asked to review "one at a
time," and is open to a CSLib online meeting.

> Draft (reuse the task-474 CSLib-meeting draft as the base): acknowledge the "one at a time" ask →
> note the modal work is now split cleanly (operator layer = your #607; modal semantics = #662;
> propositional = #648; LTL = #649, downstream) → surface the single design question (box-primitive
> vs diamond-inclusive) as *your* call with the §5 tradeoffs attached → offer the prototyped
> `HasBot` + bundled classes for #607 → offer to sync at the CSLib meeting after the 23rd. Keep it
> short and defer to him on ordering and naming.

## 8. Constraints honored / decision points for the user

- **READ-ONLY**: no branch pushed, rebased, or modified; #607 (fmontesi's) untouched. No GitHub/Zulip
  posts. No throwaway build was needed (CI failure already diagnosed from logs, §4.3).
- **Decisions requiring the user** before any action: (D1) which spelling `imp`/`impl`; (D2) whether to
  offer the `HasBot`/bundles to #607 now vs after 23 July; (D3) box-vs-diamond stance to advocate;
  (D4) exact wording + timing of the #607 review comment (§4.4) and Zulip note (§7); (D5) any push /
  retarget of #662 (still gated per task-475 §11).

## References

- PRs (read-only): [#607](https://github.com/leanprover/cslib/pull/607),
  [#648](https://github.com/leanprover/cslib/pull/648),
  [#649](https://github.com/leanprover/cslib/pull/649),
  [#662](https://github.com/leanprover/cslib/pull/662).
- #607 failing CI run: https://github.com/leanprover/cslib/actions/runs/27601699542 (HML drift).
- Prior task artifacts: `specs/475_fix_and_stack_pr_662_on_648/reports/01_...md` (git ground truth,
  Connectives Option A), tasks 468/469/472/474.
- Zulip: `CSLib > Modal Logic` (link above); Propositional-`⊥` rationale
  https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/604219492 .
- Source inspected: `#607 Operators/{Box,Impl}.lean`, `#607 Modal/Basic.lean` diff,
  `#662 Foundations/Logic/Connectives.lean` (`HasBot`/`HasImp`/`HasAnd`/`HasOr`/`HasBox` +
  `PropositionalConnectives`/`ModalConnectives`, `HasDia` deferred).
