# Falsum Representation: Adapt, Re-argue, or Diverge — Decision Report

**Task**: 400 — reconcile_connectives_pr607
**Date**: 2026-08-10
**Status**: researched
**Type**: cslib (research)
**Supersedes**: `reports/01_pr607-engagement.md`, `reports/02_engagement-strategy.md` (both written
against the pre-merge #607 premise)
**Primary sources**: live read-only `gh` against `leanprover/cslib` (PRs 607, 648, 649, 662),
`git log`/`git show` against `upstream/main`, the CSLib Zulip topic `CSLib > Propositional Logic`
(35 messages, read-only API GET), and direct measurement of this fork's Lean sources.
**No `.lean` file was created, moved, or edited. Nothing was posted to GitHub or Zulip.**

> **This report is the final deliverable of the task.** Orchestration stops at `[RESEARCHED]`; no
> plan or implementation artifact will follow. It is written to be acted on directly — §10 is a
> standalone action checklist that does not depend on a plan document existing.

---

## 0. Executive recommendation

**Recommend Option B (re-argue for primitive bot) — but the framing "re-argue" overstates what is
required. The argument was already won, on the record, before #607 merged. What #648 needs is a
rebase and a stale-review clearance, not a new debate.**

**On PR #648: rework and rebase — do not close, do not leave pending.**

Two load-bearing premises in the task description are factually wrong, and correcting them
inverts the decision:

1. **#607 did not settle the falsum question, in either direction.** The bot-as-atom design
   (`instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩`) predates #607 by four
   PRs — it dates to PR #89, the original `Logics/Propositional` definitions commit. #607's diff
   on `Propositional/Defs.lean` carries that line through unchanged, as context. #607 is a
   notation-and-naming PR: it renamed `impl` → `imp`, replaced per-type `scoped infix` notation
   with `HasAnd`/`HasOr`/`HasImp`/`HasNot` instances, and added a `not_eq` grind lemma. It never
   touched the constructor set.

2. **#648's blocking review is stale, not adverse — and thomaskwaring has already approved it.**
   `thomaskwaring` submitted `APPROVED` on 2026-07-06, after proposing a compromise on Zulip
   (2026-06-28) that Benjamin implemented. All five of his inline comments were answered on
   2026-07-13. The lone outstanding `CHANGES_REQUESTED` is `ctchou`'s from 2026-06-15, whose
   **first bullet reads "I like the idea of adding \bot as a primitive"** and whose four concrete
   points are all now addressed.

Measured cost of Option A: 512 of 1,614 declarations (31.7%) in this fork's `Logics/Propositional/`
would acquire a `[Bot Atom]` gate, three central semantic definitions would change meaning, and a
42,166-line, **zero-sorry** development would be put at risk — to satisfy a decision no maintainer
has actually asked for. Option C forfeits that same development and blocks PR #649.

---

## 1. Verified state of the record

### 1.0 Reference point (fresh refs)

All upstream claims below were measured against refs re-fetched with `git fetch upstream --prune`
on 2026-08-10. The fetch confirmed `upstream/main` was already current, so no measurement in this
report is stale.

| | |
|---|---|
| `upstream/main` | `3951377e5a3f5772737f11cd62bc5bb6a72f95d1`, 2026-08-10 11:17:56 +0000, *"chore: bump toolchain to v4.33.0 (#789)"* |
| local `HEAD` | `bd8df07ece3d6fd7635c11f88e538ec13541a950`, *"task 400, 497, 409: revise against merged upstream PR #607"* |
| `git rev-list --left-right --count upstream/main...HEAD` | `21  4605` (21 behind, 4605 ahead) |
| `Cslib/Foundations/Logic/Operators.lean` at `upstream/main` | exists (confirms the #607 merge landed it) |

Independent corroboration that #607 is merged and retired: the `--prune` deleted the remote branch
`upstream/fmontesi/connectives` along with seven other `fmontesi/*` branches, and
`git ls-remote --heads upstream | grep -c connectives` now returns `0`. The PR's source branch no
longer exists upstream.

### 1.1 What #607 actually changed (and did not)

```
$ git log --oneline -S 'instBotProposition' upstream/main -- Cslib/Logics/Propositional/Defs.lean
61785643 feat(Logics/Propositional): definitions (#89)
```

`instBotProposition` was introduced in PR #89. The full commit history of that file upstream:

```
$ git log --oneline upstream/main -- Cslib/Logics/Propositional/Defs.lean
b8ad3923 feat(Logic): logical operators (#607)
70c5bf58 refactor(Logics/Propositional): classical and intuitionistic inference systems (#536)
6d112db4 feat: add Logics/Propositional/NaturalDeduction/* (#91)
5e8967dd chore: conform to header linter (#517)
61785643 feat(Logics/Propositional): definitions (#89)
```

`gh pr diff 607` on that file shows `instBotProposition` and `instInhabitedOfBot` as unchanged
context lines. The `+`/`-` hunks are confined to: the `Operators` import, the notation paragraph of
the module docstring, `| impl` → `| imp` (constructor rename, propagated to `neg`, `top`, `subst`),
replacement of four `scoped infix` declarations with four class instances, and the new `not_eq`
lemma.

**Conclusion**: the claim that "the falsum question settled AGAINST the fork's design" on
2026-08-03 is unsupported. #607 is orthogonal to falsum representation.

### 1.2 PR #648 review timeline

```
$ gh api repos/leanprover/cslib/pulls/648/reviews -q '.[] | "\(.submitted_at)  \(.user.login)  \(.state)"'
2026-06-15T23:41:08Z  ctchou         CHANGES_REQUESTED
2026-07-06T13:26:27Z  thomaskwaring  APPROVED
2026-07-13T15:42:28Z  benbrastmckie  COMMENTED   (×5, inline replies)
```

thomaskwaring's approval body: *"this looks pretty good to me! i'd like opinions from other logic
contributors, but on the whole i'd be happy for this to be merged."*

ctchou's 2026-06-15 review, bullet by bullet, with current disposition:

| ctchou's point | Disposition |
|---|---|
| "I like the idea of adding \bot as a primitive." | Supportive — **not an objection** |
| "I don't understand why we need both Semantics/Basic.lean and Semantics/Bool.lean" | Both files removed from #648 (2026-06-30) |
| "not helpful to refer to old papers from the 1930s… use Avigad" | Avigad added as lead reference; German title dropped |
| "coordinate with #607 and #587. #536 is ready to merge, wait for it" | #536 merged and rebased; **#607 merged 2026-08-03** |

`reviewDecision: CHANGES_REQUESTED` is therefore an artifact of an unresolved review whose author
is on record *in favour* of the design in question, written against a version of the PR that no
longer exists.

thomaskwaring's five inline comments (2026-07-06) were all resolved on 2026-07-13. One is directly
relevant downstream: *"i don't have a strong opinion on `imp` vs `impl`, so long as after #607
lands it is consistent across the library."* **#607 landed `imp`.** The naming question is settled
in this fork's favour with no further argument required.

### 1.3 The Zulip record: a compromise was negotiated and met

The design objection the task description quotes (thomaskwaring, 2026-06-16, "why not represent it
as such?") was superseded on the same thread twelve days later. thomaskwaring, 2026-06-28
(`near/606970606`):

> "My sense is that, if we are going to have `⊥` as a primitive, we should also have efq — then
> minimal logic becomes `IPL⟨→,∧,∨,⊤⟩` as Matthew suggested above. It seems very unnatural to me to
> have a constructor with no semantics… Does this sound like a reasonable compromise?"

Benjamin implemented exactly that in #648 (2026-06-29, `near/607217129`): `⊥` primitive, `efq` a
primitive rule, IPL as base, minimal logic and the fragment machinery deferred. thomaskwaring
approved eight days later.

A third participant, Matthew Doty (2026-06-17, `near/604166734`), independently backed primitive
falsum on implementation grounds:

> "I'm still a proponent of an explicit falsum in the base syntax (and thus EFQ)… For the purposes
> of DPLL, having `⊥ : Atom` adds some extra complexity, since `pos ⊥` has to be removed from every
> clause and clauses with `neg ⊥` need to be removed. Also, additional care is needed to ensure
> `v ⊥ = ⊥` for any valuation `v` the algorithm outputs."

So of the four people who engaged the question, two maintainer-side reviewers (thomaskwaring after
compromise, ctchou from the outset) and one contributor (Doty) support primitive `⊥`. There is no
standing opposition on the record.

### 1.4 The predicted `HasBot` gap — correcting the correction

The task description states the original prediction "held": #607 needs `HasBot`/`HasTop` and none
landed. This is half right and misleads on the consequence.

- **True**: no `HasBot` or `HasTop` class exists anywhere in `upstream/main`.
- **False as a blocker**: this fork's own prior research already retracted the `HasBot`
  recommendation (`review-scaffolding/02_falsum-bridge-sketch.md` §0). Mathlib's `Bot`/`Top`
  (`Mathlib/Order/Notation.lean`) already supply `⊥`/`⊤`, and this fork already uses them —
  `instance : Bot (Proposition Atom) := ⟨.bot⟩` at `Cslib/Logics/Propositional/Defs.lean:104`. A
  five-primitive `Proposition` registers against merged #607 with **zero new typeclasses**. The
  reuse-first answer is Mathlib's `Bot`, not a new `HasBot`.

What *did* land is a small, clean, entirely non-adversarial **documentation bug** in merged
upstream code. `Cslib/Logics/Propositional/Defs.lean:36-37` (upstream/main) reads:

> "In the case that `Atom` has a bottom element (respectively, is inhabited) we give instances
> `HasBot (Proposition Atom)` and (respectively, `HasTop (Proposition Atom)`)."

```
$ git grep -n 'HasBot\|HasTop' upstream/main -- '*.lean'
upstream/main:Cslib/Logics/Propositional/Defs.lean:37:`HasBot (Proposition Atom)` and (respectively, `HasTop (Proposition Atom)`).
```

The only occurrence in the entire upstream tree is that docstring. The classes do not exist; the
code gives Mathlib `Bot`/`Top` instances. This is a factual defect report, not a design argument —
useful as a low-friction re-entry point to the conversation.

---

## 2. Measured cost of Option A (adapt to bot-as-atom)

### 2.1 `.bot` match-site count

Repo-wide, scoped by directory (each figure is `grep -rn '\.bot\b' --include='*.lean'`):

| Directory | `.bot` lines | files |
|---|---:|---:|
| `Cslib/Logics/Bimodal/` | 731 | 71 |
| `Cslib/Foundations/` | 547 | 23 |
| `Cslib/Logics/Modal/` | 464 | 52 |
| `Cslib/Logics/Temporal/` | 328 | 30 |
| **`Cslib/Logics/Propositional/`** | **165** | **39** |
| `Cslib/Logics/LTL/` | 30 | 8 |
| `Cslib/Logics/LinearLogic/` | 20 | 4 |
| `Cslib/Computability/` | 2 | 1 |
| **repo total** | **2,287** | **228** |

Only the Propositional figure is `PL.Proposition.bot`; the rest belong to the Modal, Temporal,
Bimodal, and LTL formula types, which have their own primitive `bot` constructors. Within
`Logics/Propositional/`:

```
match-arm lines (^\s*|.*\bbot\b) :   120
'.bot' token lines               :   165
'Proposition.bot' qualified      :    50
bare '⊥' glyph occurrences       :   790
```

The 790 `⊥` occurrences would *mostly* survive a migration, since `Bot (Proposition Atom)` still
exists upstream — but only inside a `[Bot Atom]` context.

### 2.2 `Bot`-free public statements that would acquire the gate

Declaration-level census over `Cslib/Logics/Propositional/` (116 files):

```
files=116   total_decls=1614   decls mentioning ⊥ / ¬ / bot / neg = 512   (31.7%)
```

Every one of those 512 declarations currently states without any `Bot Atom` hypothesis, because
this fork's `bot` is a constructor. Under Option A each acquires `[Bot Atom]`. Heaviest files:

| falsum-touching / total decls | file |
|---:|---|
| 76 / 247 | `Tableau/Intuitionistic/Scheme.lean` |
| 34 / 98 | `ProofSystem/FragmentAxioms.lean` |
| 21 / 24 | `Semantics/Algebra/FragmentPredicates.lean` |
| 16 / 52 | `Semantics/Algebra/HilbertLindenbaum.lean` |
| 13 / 15 | `Semantics/Algebra/BrouwerianBot.lean` |
| 12 / 32 | `NaturalDeduction/HilbertDerivedRules.lean` |
| 12 / 31 | `Semantics/Algebra/HilbertAlgCompleteness.lean` |
| 12 / 16 | `Semantics/Algebra/NonemptyLowerSet.lean` |
| 11 / 27 | `Defs.lean` |

The specific public statements named in the task description are confirmed `Bot`-free:

| Declaration | Current context | File:line |
|---|---|---|
| `instDecidableMValid`, `instDecidableDerivableMinPropAxiom` | `variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]` | `Tableau/Minimal/DecisionProcedure.lean:104` |
| `instDecidableTautologyTableau` | same | `Tableau/Classical/DecisionProcedure.lean:57` |
| `instDecidableIValid`, `instDecidableDerivableIntPropAxiom` | same | `Tableau/Intuitionistic/DecisionProcedure.lean:89` |
| `MValid`, `IValid` | `variable {Atom : Type u}` only | `Semantics/Kripke.lean:145,153` |

### 2.3 Cross-module blast radius

```
files outside Logics/Propositional/ that import it        : 21
files outside it that reference PL.Proposition            : 32
```

These include all 19 `Modal/Metalogic/Systems/*/ConservativeExtension.lean` files,
`Temporal/FromPropositional.lean`, `Temporal/ConservativeExtension.lean`,
`Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`,
`Bimodal/Embedding/PropositionalEmbedding.lean`, `Modal/Tableau/Defs.lean`,
`Foundations/Logic/Theorems/BigConj.lean`, and
`Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean`.

### 2.4 The cost that is not syntactic

The line counts understate Option A. Three definitions change *meaning*, not just signature:

**(a) `Tautology` stops being tautologyhood.** `Semantics/Bool.lean` defines
`Evaluate v .bot = False` definitionally (line 69, with `Evaluate_bot` as a `rfl` simp lemma at
line 77) and `Tautology φ := ∀ (v : Valuation Atom), Evaluate v φ` (line 90), where
`Valuation Atom := Atom → Prop`. Under bot-as-atom, `Evaluate v ⊥` reduces to `v ⊥`, which a
valuation may make true — so `⊥ → p` is no longer a tautology. `Tautology` must be restated to
quantify only over valuations with `v ⊥ = False`, and every classical soundness, completeness, and
decidability statement inherits that restriction.

**(b) `IValid` gains a model side-condition.** `Semantics/Kripke.lean:145` pins
`bot_forces = fun _ => False`. Under bot-as-atom that becomes an explicit hypothesis
`∀ w, ¬ val w ⊥` threaded through the intuitionistic Kripke development.

**(c) `MValid` genuinely simplifies — and this is the one real point in Option A's favour.**
`Semantics/Kripke.lean:153` quantifies over an arbitrary upward-closed `bot_forces : World → Prop`
alongside the atom valuation. Under bot-as-atom, `bot_forces w` *is* `val w ⊥`, and the extra
quantifier plus its upward-closure hypothesis disappear. This is precisely thomaskwaring's
"it behaves precisely like the atomic formulae" argument, and for minimal logic in isolation it is
correct. The trade is real but asymmetric: this fork develops MPL, IPL, and CPL together, so the
IPL and CPL layers pay a side-condition tax to buy the MPL layer's simplification.

**(d) Substitution stops being free.** With `⊥` primitive, `subst` has `| .bot => .bot` and axiom
schemes are automatically substitution-closed. With `⊥` an atom, `bind σ` sends `⊥ ↦ σ(⊥)`, and
`subst_preserves_axiom`, `subst_preserves_intAxiom`, `subst_preserves_minAxiom`,
`hilbertSubstitution`, and `Theory.Derivation.substAtom` each acquire a `σ(⊥) = ⊥` side condition.
(This argument is already on the Zulip record at `near/604219492`; it went unrebutted.)

### 2.5 What is being risked

```
$ git diff --stat upstream/main..HEAD -- Cslib/Logics/Propositional/
117 files changed, 42166 insertions(+), 238 deletions(-)

$ # term/tactic-position sorry in Logics/Propositional/
0

$ # term/tactic-position sorry repo-wide (Cslib/)
1     (Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean)
```

Upstream's `Logics/Propositional/` is **3 files**. This fork's is **116**. The fork's propositional
development is sorry-free, and the entire repository carries exactly one sorry, outside this
subtree. Option A proposes a semantics-altering refactor of 512 declarations across a sorry-free
42k-line development, in response to a decision that was never made.

**Verdict on A: reject.** Not because the migration is impossible, but because the premise
motivating it does not exist, the cost is large and partly semantic, and the one genuine technical
benefit (§2.4c) is confined to minimal logic and is outweighed within the same development.

### 2.6 Drift in the 21 unmerged commits — applies under every option

Three items in `HEAD..upstream/main` bear on cost. Only the third is significant.

**(a) Toolchain: small, and not a differentiator.**

```
$ cat lean-toolchain                          -> leanprover/lean4:v4.33.0-rc1
$ git show upstream/main:lean-toolchain       -> leanprover/lean4:v4.33.0
```

The fork pins Mathlib to commit `169c26b52a38b704fad2c009372d76844a059bdf`; upstream pins the tag
`v4.33.0`. Three commits close the gap: `3aa9d441` (rc2, #773), `3951377e` (v4.33.0, #789), and
`d350fc30` ("bump mathlib to 3069656, fix breaking changes", #757). This is one release candidate's
worth of drift — routine, and identical work under A, B, or C, so it does not distinguish the
options. It is a prerequisite for the #648 rebase (§5 step 1), not an argument for or against any
option.

**(b) `cef17d84 fix(Modal): combine frame conditions in modal cube (#746)`** touches upstream's
`Modal/Cube.lean`, which overlaps PR #662's territory. Relevant to #662's own rebase; irrelevant to
the falsum decision.

**(c) `3491c629 feat(Logic): improvements to the inference system and congruence frameworks (#753)`
— this surfaces a divergence the task description does not mention, and it affects all three
options.**

Upstream's `Propositional/Defs.lean` states `IsIntuitionistic`/`IsClassical` over an inference
system, `public import`ing `Foundations.Logic.InferenceSystem`:

```lean
class IsIntuitionistic (Atom : Type u) [Bot Atom] (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  efq (A : Proposition Atom) : S⇓(⊥ → A)
```

This fork's `Propositional/Defs.lean` does **not** import `InferenceSystem` at all, and states the
same two classes as plain theory-membership predicates (`Defs.lean:166`, `Defs.lean:175`):

```lean
class IsIntuitionistic (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T
```

PR #648 had already reconciled this (its 2026-06-16 comment: *"reconciled `IsIntuitionistic`/
`IsClassical` with the InferenceSystem-parameterized versions from #536"*), so **the fork's `main`
has since diverged back away from upstream on a point #648 had already settled.** Meanwhile #753
refactored the framework underneath it.

Scope of #753, for rebase budgeting:

```
Cslib/Foundations/Logic/InferenceSystem.lean     |  21 +-
Cslib/Foundations/Logic/LogicalEquivalence.lean  |  30 +-
Cslib/Foundations/Syntax/Congruence.lean         |  34 +-
Cslib/Logics/HML/Basic.lean                      | 335 +-
Cslib/Logics/HML/LogicalEquivalence.lean         | 194 +-
Cslib/Logics/Modal/LogicalEquivalence.lean       |  75 +-
(16 files, 554 insertions, 251 deletions)
```

The part that matters for Propositional is small — `InferenceSystem.lean` moved by 21 lines. The
bulk lands in HML, which this fork does not develop. So #753 is a modest rebase item, **but the
`IsIntuitionistic`/`IsClassical` shape mismatch is a genuine reconciliation obligation** that no
option avoids: 80 files in this fork reference `InferenceSystem`, just not from
`Propositional/Defs.lean`. Fold this into the #648 rebase (§5 step 1) rather than treating it as a
separate discovery later.

---

## 3. Option B winnability, honestly assessed

The task description asks: what NEW argument or evidence is being brought that was not made in
June? Four items, none of which is a repetition:

1. **The compromise thomaskwaring asked for was implemented, and he approved it.** This is not an
   argument at all — it is the state of the record, dated 2026-07-06, three weeks after the
   objection the task description quotes. Nothing needs re-arguing.

2. **This fork has since gone strictly beyond #648, in the direction thomaskwaring wanted.** In
   `NaturalDeduction/Basic.lean:182` `efq` is a primitive `Derivation` constructor **gated on
   `[IsIntuitionistic T]`**, so it is structurally unavailable at `T = MPL = ∅` while being a
   genuine primitive rule at IPL/CPL strength. #648 as pushed has `efq` ungated
   (`| efq {Γ} {A} : Derivation Γ ⊥ → Derivation Γ A`) and pays for it by dropping minimal logic —
   thomaskwaring's own summary was "in which case we would forget about minimal logic for the
   moment." The gated design satisfies his ND-symmetry requirement (`⊥` has an elimination rule in
   the derivation type) *without* sacrificing MPL. That is new, and it is responsive to his stated
   concern rather than a restatement of the June position.

3. **#607's merge removed a June friction rather than creating one.** thomaskwaring's only reserved
   inline comment on #648 was the `imp`/`impl` naming, conditioned on "so long as after #607 lands
   it is consistent across the library." #607 landed `HasImp.imp`. #648 already uses `imp`. The
   condition is met.

4. **A 42,166-line sorry-free development now exists** (§2.5). In June the primitive-`⊥` case was
   argued on universal-algebra grounds against a much smaller body of work. The load-bearing
   evidence today is that the design carried a full metalogical development — strong completeness
   for MPL/IPL/CPL, Hilbert↔ND equivalence, four-step fragment conservativity chains, and three
   tableau decision procedures — to zero sorries.

### Risks and what B actually costs

| Risk | Status | Mitigation |
|---|---|---|
| `mergeable: CONFLICTING` | Confirmed via `gh pr view 648` | Mechanical rebase. #607 renamed `impl`→`imp`, the same direction #648 took, so conflicts are textual not semantic |
| ctchou's stale `CHANGES_REQUESTED` | Confirmed, blocking `reviewDecision` | Re-request review, itemising the four dispositions in §1.2 |
| "other logic contributors" input still pending | thomaskwaring asked for it in his approval | Nothing to do but ask; Doty is already supportive on Zulip |
| Fork main has diverged from the #648 branch (gated vs ungated `efq`) | Confirmed | See §5 — land #648 as approved first; gated `efq` is the deferred fragment work, not a #648 change |
| **CSLib Zulip AI policy** | Chris Henson formally queried an LLM-drafted message on this exact thread (`near/605827029`); Benjamin committed to avoiding AI drafting | **No agent-drafted prose may be posted.** See §7 |

**Winnability: high.** One approval in hand, one stale objection from a reviewer who supports the
design, an implemented negotiated compromise, and no standing counter-argument. The realistic
failure mode is not losing the argument — it is the PR going stale a second time from inaction.

---

## 4. Option C and the downstream PRs

**#649 (LTL) does depend on the propositional base.** Its changed files:

```
Cslib.lean
Cslib/Foundations/Logic/Connectives.lean
Cslib/Logics/LTL/Semantics/Satisfies.lean
Cslib/Logics/LTL/Syntax/Formula.lean
Cslib/Logics/Propositional/Defs.lean
Cslib/Logics/Propositional/NaturalDeduction/Basic.lean
Cslib/Logics/Propositional/NaturalDeduction/Theory.lean
references.bib
```

Three of the four #648 files appear verbatim; #649 is stacked on #648. Option C blocks it.

**#662 (Modal) does not.** Its changed files are `Modal/{Basic,Cube,Denotation,LogicalEquivalence}.lean`
plus `references.bib`, and upstream `Modal/Basic.lean` imports only `Foundations.Logic.Operators`,
`Foundations.Logic.InferenceSystem`, `Foundations.Relation.Euclidean`, and Mathlib — no
`Logics.Propositional` import. #662 is independent of the falsum outcome and can proceed on its own
schedule. (It sits at `REVIEW_REQUIRED`, i.e. nobody has reviewed it, which is a separate problem.)

**A collision #649 must resolve regardless of which option is chosen.** #649 carries this fork's
`Cslib/Foundations/Logic/Connectives.lean`, which declares classes in `namespace Cslib.Logic` that
merged #607 now also declares in `Cslib/Foundations/Logic/Operators.lean`, same namespace:

| Class | fork `Connectives.lean` | upstream `Operators.lean` |
|---|---:|---:|
| `HasAnd` | 1 | 1 |
| `HasOr` | 1 | 1 |
| `HasImp` | 1 | 1 |
| `HasBox` | 1 | 1 |
| `HasIff` | 0 | 1 |
| `HasNot` | 0 | 1 |

Four hard duplicate-declaration collisions. Additionally the fork names the possibility modality
`HasDia` where upstream names it `HasDiamond`. Reconciling `Connectives.lean` against
`Operators.lean` is a prerequisite for #649 under **every** option, and is independent of falsum.

**Verdict on C: reject as a strategy, though it is the de-facto status quo.** It forfeits a
42k-line sorry-free development that two upstream reviewers have signalled they want, blocks #649,
and does not even avoid the `Connectives`/`Operators` reconciliation work.

---

## 5. Recommendation on PR #648: rework and rebase

**Do not close. Do not leave pending. Rebase and clear the stale review.**

Sequence, smallest-first:

1. **Rebase `feat/propositional-v2` onto post-#607 `upstream/main`** (`3951377e`). Expect textual
   conflicts only on the falsum axis: #607's `impl`→`imp` rename moves toward #648's naming, and
   #607's notation-to-instances change touches the same docstring region #648 edits. Three
   non-falsum items ride along and should be absorbed in the same pass (§2.6): the `v4.33.0-rc1` →
   `v4.33.0` toolchain and Mathlib pin bump, #753's `InferenceSystem` refactor, and — the one to
   watch — re-confirming that #648's `IsIntuitionistic`/`IsClassical` still match upstream's
   inference-system-parameterized shape, since this fork's `main` has drifted back to the
   theory-membership form that #648 had already reconciled away.
2. **Keep #648's scope exactly as approved** — four files, `⊥` primitive, `efq` primitive, IPL
   base, minimal logic deferred. Do **not** widen it to this fork's current `[IsIntuitionistic T]`-
   gated `efq`. thomaskwaring explicitly agreed to defer fragment work; gated `efq` *is* that
   deferred work and belongs in a follow-up PR. Widening the scope forfeits a standing approval to
   reopen a settled design discussion.
3. **Register `HasAnd`/`HasOr`/`HasImp`/`HasNot` instances for the five-primitive `Proposition`**
   against merged #607, using Mathlib `Bot`/`Top` for `⊥`/`⊤` — no new classes (§1.4). Include the
   `not_eq`-style `@[grind =]` bridge lemma so #607's grind automation sees through derived `neg`.
4. **Re-request review from ctchou**, itemising the four dispositions in §1.2, and note that
   thomaskwaring's approval stands.
5. **Only then** open the follow-up for gated `efq` + MPL restoration, and separately for the
   semantics layer that was pulled out of #648 at thomaskwaring's request.

---

## 6. Independent finding: notation associativity (act on this regardless)

This is orthogonal to falsum and is a strict, low-risk improvement.

| Connective | this fork (`Propositional/Defs.lean`) | upstream (`Operators.lean`) |
|---|---|---|
| `∧` | `scoped infix:36` | `scoped infixr:36` |
| `∨` | `scoped infix:35` | `scoped infixr:30` |
| `→` | `scoped infix:30` | `scoped infixr:25` |
| `↔` | `scoped infix:20` | `scoped infixr:20` |
| `¬` | `scoped prefix:40` | `scoped notation:max "¬" p:40` |

The task description flags the `→` precedence gap (30 vs 25) and the associativity gap. Both hold,
and `∨` differs in precedence too (35 vs 30) — though the *relative* ordering `∧ > ∨ > →` is
preserved in both, so no existing formula reparses to a different tree. **Associativity is the real
defect**, and it is worse than "the arrow": Lean's `infix:n` is non-associative, so *every* binary
connective here rejects chaining. Verified empirically against this fork's build:

```lean
import Cslib.Logics.Propositional.Defs
open Cslib.Logic.PL
variable {A : Type} [DecidableEq A] (a b c : Proposition A)
example : Proposition A := a → b         -- OK
example : Proposition A := a → (b → c)   -- OK
example : Proposition A := a → b → c     -- ERROR: "type expected, got (a : Proposition A)"
example : Proposition A := a ∧ b ∧ c     -- ERROR: falls through to Prop-level `And`, type mismatch
example : Proposition A := a ∨ b ∨ c     -- ERROR: falls through to Prop-level `Or`, type mismatch
```

The failure mode is nastier than a parse error: because the scoped non-associative notation cannot
match the chained form, Lean's built-in `And`/`Or`/`→` win the overload and the user gets a
*type mismatch against `Prop`* rather than a notation error. Switching this fork's five
declarations to `infixr` at upstream's precedences is a small, self-contained change that fixes
this and pre-pays part of any future reconciliation. It should be a separate task; no `.lean` file
was touched here.

---

## 7. Constraint on any outward communication

Any GitHub or Zulip text arising from this report **must be written by a human, from scratch**.
This is not a general caution: on this exact Zulip topic, Chris Henson formally challenged an
LLM-drafted message (`near/605827029`, 2026-06-22), and Benjamin replied committing to avoid AI
drafting going forward. This report therefore deliberately contains **no draft post prose** — only
verified facts, citations, and dispositions that a human can write up in their own words. The prior
`review-scaffolding/` artifacts carry the same warning banner and should be treated the same way.

Nothing was posted. No `gh` write command, no Zulip write API call, and no `git push` was executed
during this research; all `gh` and Zulip access was read-only (`gh pr view`, `gh pr diff`,
`gh api ... GET`, Zulip `GET /api/v1/messages`).

---

## 8. Downstream consequences

- **The `imp`/`impl` naming task is unblocked and its direction is determined.** Upstream settled
  on `HasImp.imp`; this fork already uses `imp` for `PL.Proposition`. The remaining work is
  renaming `Modal`'s `impl` (upstream's `Modal/Basic.lean` still uses `impl`-era naming in places)
  and reconciling `HasDia` → `HasDiamond`. That work does not depend on the falsum outcome and can
  start once this decision is recorded.
- **`Connectives.lean` ↔ `Operators.lean` reconciliation is required under every option** (§4) and
  is the highest-value next unit of upstreamable work: it unblocks #649, it is additive, and #607
  having merged makes the target stable.
- **Notation associativity** (§6) should be spawned as its own task.

## 9. Action checklist (self-contained — no plan artifact will follow)

Orchestration stops here. The following is the complete actionable residue of this report, ordered
so that each item is independently landable. Nothing below has been started; no `.lean` file was
touched and nothing was posted.

**Decision to record**

- [ ] Record **Option B** as task 400's outcome. The `imp`/`impl` naming task is thereby unblocked
      and its direction is determined: upstream landed `HasImp.imp` and this fork already uses
      `imp` for `PL.Proposition`.

**Item 1 — Revive PR #648** *(external; requires human-authored text — see §7)*

- [ ] Rebase `feat/propositional-v2` onto `upstream/main` @ `3951377e`, absorbing the toolchain/
      Mathlib pin bump and #753, and re-confirming the `IsIntuitionistic`/`IsClassical` shape
      (§2.6c, §5 step 1).
- [ ] Hold scope at the four approved files. Do **not** widen to gated `efq`.
- [ ] Add `HasAnd`/`HasOr`/`HasImp`/`HasNot` instances for the five-primitive `Proposition` against
      merged #607, using Mathlib `Bot`/`Top` for `⊥`/`⊤` — no new typeclasses (§1.4) — plus a
      `not_eq`-style `@[grind =]` bridge so #607's grind automation sees through derived `neg`.
- [ ] Re-request review from `ctchou`, itemising the four dispositions in §1.2; note that
      `thomaskwaring`'s approval stands.
- [ ] Optionally report the upstream docstring defect (§1.4): `Defs.lean:36-37` promises
      `HasBot`/`HasTop` instances for classes that exist nowhere in the tree. Low-friction, purely
      factual, and a natural re-entry point to the conversation.

**Item 2 — Reconcile `Connectives.lean` against `Operators.lean`** *(local `.lean` work; required
under every option; prerequisite for #649)*

- [ ] Resolve four duplicate declarations in `namespace Cslib.Logic` — `HasAnd`, `HasOr`, `HasImp`,
      `HasBox` — declared in both this fork's `Foundations/Logic/Connectives.lean` and merged
      upstream's `Foundations/Logic/Operators.lean` (§4).
- [ ] Rename this fork's `HasDia` → upstream's `HasDiamond`.
- [ ] Decide the fate of the fork-only bundles (`PropositionalConnectives`, `ModalConnectives`,
      `TemporalConnectives`, `BimodalConnectives`, `LTLConnectives`, `FutureTemporalConnectives`)
      against upstream's à-la-carte one-class-per-operator direction.

**Item 3 — Notation associativity** *(local `.lean` work; low-risk, self-contained, orthogonal to
falsum)*

- [ ] Switch the five `scoped infix`/`prefix` declarations in `Logics/Propositional/Defs.lean` to
      `infixr` at upstream's precedences (§6). This fixes chained `∧`, `∨`, and `→`, which
      currently fail as `Prop`-level type mismatches rather than notation errors.

**Explicitly out of scope / not recommended**

- Migrating `Proposition` to four constructors (Option A) — rejected, §2.
- Abandoning upstreaming of `Logics/Propositional/` (Option C) — rejected, §4.
- Any agent-drafted GitHub or Zulip prose — prohibited, §7.

## 10. Commands run (reproducibility)

All measurements in this report come from these commands, run at `bd8df07e` on branch `main` with
`upstream` = `https://github.com/leanprover/cslib.git`, against refs re-fetched 2026-08-10
(`upstream/main` = `3951377e`):

```bash
git fetch upstream --prune
git rev-list --left-right --count upstream/main...HEAD
git ls-remote --heads upstream | grep -c connectives
cat lean-toolchain; git show upstream/main:lean-toolchain
git log --oneline HEAD..upstream/main
git show --stat 3491c629
git log --oneline -S 'instBotProposition' upstream/main -- Cslib/Logics/Propositional/Defs.lean
git log --oneline upstream/main -- Cslib/Logics/Propositional/Defs.lean
gh pr diff 607 --repo leanprover/cslib          # inspected Propositional/Defs.lean hunk
gh api repos/leanprover/cslib/pulls/648/reviews -q '.[] | "\(.submitted_at)  \(.user.login)  \(.state)"'
gh api repos/leanprover/cslib/pulls/648/comments
gh pr view 648 --repo leanprover/cslib --json mergeable,reviewDecision,state,updatedAt
gh pr view 649 --repo leanprover/cslib --json files -q '.files[].path'
gh pr view 662 --repo leanprover/cslib --json files -q '.files[].path'
git grep -n 'HasBot\|HasTop' upstream/main -- '*.lean'
git show upstream/main:Cslib/Foundations/Logic/Operators.lean
grep -rn '\.bot\b' <dir> --include='*.lean' | wc -l          # per-directory table, §2.1
grep -rn '^\s*|.*\bbot\b' Cslib/Logics/Propositional --include='*.lean' | wc -l
grep -rln 'import Cslib\.Logics\.Propositional' Cslib --include='*.lean' | grep -v '^Cslib/Logics/Propositional/'
git diff --stat upstream/main..HEAD -- Cslib/Logics/Propositional/
grep -rE '^[[:space:]]*sorry[[:space:]]*$|:=[[:space:]]*sorry[[:space:]]*$' Cslib --include='*.lean'
```

The 512/1,614 declaration census (§2.2) used a Python pass that segments each `.lean` file at
declaration keywords (`theorem|lemma|def|abbrev|instance|inductive|structure|class|example`,
allowing attribute and modifier prefixes) and flags any block containing `⊥`, `¬`, `bot`, or `neg`.
Script retained at
`/tmp/claude-1000/-home-benjamin-Projects-cslib/42296e58-587b-44ee-bb90-d31eaf0cd452/scratchpad/count_decls.py`.

The notation check (§6) used the `lean_run_code` MCP tool against this fork's build; the two error
messages quoted are verbatim from its diagnostics.
