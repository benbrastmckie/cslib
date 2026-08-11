# Research Report: Rebase PR #648 onto upstream/main and clear the stale blocking review

**Date**: 2026-08-10
**Session**: sess_1786405794_f0204e_620
**Agent**: cslib-research-agent
**Source**: `specs/400_reconcile_connectives_pr607/reports/03_falsum-representation-decision.md` §5

All findings below were verified read-only against the live repository and the GitHub API on
2026-08-10. No `git push`, no `gh` write call, no Zulip post was made.

---

## 1. Executive summary

The rebase is **substantially smaller and safer than the task description implies**. Empirical
conflict probing (`git merge-tree`, no working tree touched) shows exactly **two conflicted files**:
`Cslib/Logics/Propositional/Defs.lean` (real semantic reconciliation) and `references.bib`
(trivial append-at-EOF collision). The two `NaturalDeduction/` files merge **cleanly** —
upstream has not touched them since the PR's merge base.

Three items in the task description need correction before planning (§3). The most consequential:
**the PR branch has already reconciled `IsClassical` to the inference-system shape** — that work is
done, not pending. The theory-membership drift described in the task lives on *this fork's `main`*,
which is a completely separate 117-file development line that must not be involved in the rebase.

Blast radius is provably nil outside the three Propositional files: nothing else in upstream
imports `Cslib.Logics.Propositional` (§4.4).

---

## 2. Verified ground truth

### 2.1 Branch topology

| Ref | Commit | Toolchain | Mathlib rev | Note |
|---|---|---|---|---|
| merge base | `056cf937` (#708) | `v4.32.0-rc1` | `d52d26fc` | where the PR branched |
| `origin/feat/propositional-v2` (PR head) | `4834be23` | `v4.32.0-rc1` | `d52d26fc` | 6 commits, 4 files |
| `upstream/main` (rebase target) | `3951377e` (#789) | `v4.33.0` | `db584cd6` | 40 commits ahead of base |
| this fork's `main` | `212318f2` | `v4.33.0-rc1` | `169c26b5` | **not involved in the rebase** |

The PR branch does **not** modify `lean-toolchain` or `lake-manifest.json`, so the rebase inherits
upstream's `v4.33.0` / `db584cd6` automatically with **no conflict and no manual bump**.

### 2.2 PR #648 diff (vs merge base) — exactly four files, as approved

```
 Cslib/Logics/Propositional/Defs.lean                    |  89 +++++-------
 Cslib/Logics/Propositional/NaturalDeduction/Basic.lean  | 161 +++++++++++++--------
 Cslib/Logics/Propositional/NaturalDeduction/Theory.lean |  87 +++++------
 references.bib                                          |  44 +++++-
 4 files changed, 218 insertions(+), 163 deletions(-)
```

GitHub state: `OPEN`, `mergeable: CONFLICTING`, `mergeStateStatus: DIRTY`, base `main`,
head `benbrastmckie:feat/propositional-v2`, last updated 2026-07-13.

### 2.3 Review record (re-verified verbatim)

```
2026-06-15T23:41:08Z  ctchou         CHANGES_REQUESTED
2026-07-06T13:26:27Z  thomaskwaring  APPROVED
2026-07-13T15:42:28Z  benbrastmckie  COMMENTED ×5 (inline replies, all five threads)
```

thomaskwaring's approval body, verbatim: *"this looks pretty good to me! i'd like opinions from
other logic contributors, but on the whole i'd be happy for this to be merged."*

ctchou's review opens, verbatim: *"I like the idea of adding \bot as a primitive."* The remaining
three bullets are procedural (file organization, references, coordination). **There is no technical
objection to primitive `bot` anywhere on the record.**

### 2.4 Empirical conflict probe

```
$ git merge-tree --write-tree --name-only \
    --merge-base=056cf937 upstream/main origin/feat/propositional-v2
Cslib/Logics/Propositional/Defs.lean
references.bib
CONFLICT (content): Merge conflict in Cslib/Logics/Propositional/Defs.lean
CONFLICT (content): Merge conflict in references.bib
```

Five conflict hunks in `Defs.lean`; one in `references.bib`.

---

## 3. Corrections to the task description

These are stated up front because two of them change the plan's shape.

### 3.1 CORRECTION — the `IsIntuitionistic`/`IsClassical` shape reconciliation is already done on the PR branch

The task description says the fork "does not import InferenceSystem and states these as
theory-membership predicates (`Defs.lean:166,175`)" and that "the fork's main has since drifted
BACK", implying rework is needed on the PR.

Verified: `origin/feat/propositional-v2:Cslib/Logics/Propositional/Defs.lean` **does**
`public import Cslib.Foundations.Logic.InferenceSystem` and states:

```lean
class IsClassical (Atom : Type u) (S : Type*) [InferenceSystem S (Proposition Atom)] where
  dne (A : Proposition Atom) : S⇓(¬¬A → A)
```

— the inference-system shape, matching upstream. It has **no `IsIntuitionistic` class at all**,
because `efq` became a primitive `Derivation` constructor (that is the approved design).

The theory-membership form (`(⊥ → A) ∈ T` at `Defs.lean:166,175`, importing
`Cslib.Foundations.Logic.Connectives` rather than `InferenceSystem`) is on **this fork's `main`**,
which carries 117 files under `Cslib/Logics/Propositional/` versus the PR branch's 3. That line of
work is exactly the `[IsIntuitionistic T]`-gated design the task correctly forbids widening into.

**Planning consequence**: the rebase must be performed on `origin/feat/propositional-v2` against
`upstream/main`. The fork's `main` must not be a merge source, a cherry-pick source, or a
conflict-resolution reference at any point. This is the single highest-risk failure mode of the
task — pulling from `main` would silently forfeit thomaskwaring's approval.

### 3.2 CORRECTION — toolchain drift is two releases, not one, and requires no manual action

The task says "fork pins `v4.33.0-rc1` ... upstream is at `v4.33.0` ... One release-candidate of
drift." That describes the fork's `main`. The **PR branch** pins `v4.32.0-rc1` / Mathlib
`d52d26fc` — a full minor release behind. But since the PR branch never touches either file, the
rebase takes upstream's pins verbatim with zero conflict. The only practical consequence is that
the first local `lake build` after the rebase needs a fresh toolchain and Mathlib cache
(`lake exe cache get`), which is slow but not a decision point.

### 3.3 REFINEMENT — PR #753 has no impact on the PR's files

The task lists "PR #753's InferenceSystem/Congruence framework refactor (commit `3491c629`)" as
something the rebase must absorb. Verified: `3491c629` exists and touched
`Cslib/Foundations/Logic/InferenceSystem.lean`, but the diff is **purely additive** — a module
docstring plus an `app_delab` delaborator that hides `InferenceSystem.Default` in `⇓a` notation.
The `S⇓(...)` notation and the `InferenceSystem` class signature are unchanged. Nothing in the
PR's four files needs to move for #753.

### 3.4 REFINEMENT — `file_scope` in state.json is inaccurate

Declared: `Defs.lean`, `NaturalDeduction/`, `lean-toolchain`, `lake-manifest.json`.
Actual files the rebase writes: `Defs.lean`, `NaturalDeduction/Basic.lean`,
`NaturalDeduction/Theory.lean`, `references.bib`. `lean-toolchain` and `lake-manifest.json` are
inherited, not edited; `references.bib` is missing from the declared scope but **is** a conflict.

---

## 4. The one real conflict: `Defs.lean`

### 4.1 What upstream #607 changed (merged 2026-08-03, commit `b8ad3923`)

Two changes that interact directly with #648, both in the PR's favour:

1. **`Proposition.impl` → `Proposition.imp`.** Upstream adopted the exact rename #648 made. The PR
   body still hedges ("open to reverting if reviewers prefer `impl`") and thomaskwaring's inline
   comment asked only for post-#607 consistency. That question is now settled *for* the PR.
   Upstream `Modal/Basic.lean` also uses `Proposition.imp` + `HasImp` now, so the library is
   uniformly `imp`.
2. **Scoped `infix` notation → typeclass instances.** Upstream deleted the local notation
   declarations and registered instances against a new `Cslib/Foundations/Logic/Operators.lean`:

```lean
instance : HasAnd (Proposition Atom) := ⟨.and⟩
instance : HasOr  (Proposition Atom) := ⟨.or⟩
instance : HasImp (Proposition Atom) := ⟨.imp⟩
instance [Bot Atom] : HasNot (Proposition Atom) := ⟨.neg⟩

omit [DecidableEq Atom] in
@[grind =]
lemma not_eq [Bot Atom] (A : Proposition Atom) : (A → ⊥) = ¬ A := rfl
```

Upstream keeps bot **atom-encoded**: `instance instBotProposition [Bot Atom] : Bot (Proposition
Atom) := ⟨.atom ⊥⟩`. That is precisely what #648 replaces.

### 4.2 Reuse check (CSLib reuse-first protocol) — no new abstractions needed

Verified contents of `Cslib/Foundations/Logic/Operators.lean` on `upstream/main`:
`HasAnd`, `HasOr`, `HasImp`, `HasIff`, `HasNot`, `HasBox`, `HasDiamond`, `HasDynamicBox`,
`HasDynamicDiamond`, `HasTensor`, all in namespace `Cslib.Logic`.

**There is no `HasBot` and no `HasTop` class** — upstream uses Mathlib's `Bot`/`Top` for those.
(Note for anyone working from the agent context file: its list of "existing CSLib typeclasses"
names `HasBot`/`HasTop`/`HasDia`, none of which exist under those names upstream.)

Conclusion: the rebase requires **zero new typeclasses**. Everything the five-primitive
`Proposition` needs is already in `Operators.lean` plus Mathlib `Bot`/`Top`. `HasIff` already
exists and should be used for #648's derived `iff` (the PR currently declares its own
`scoped infix:20 " ↔ "`).

### 4.3 Required shape of the reconciled `Defs.lean`

| Item | Upstream (`b8ad3923`) | PR #648 branch | Reconciled target |
|---|---|---|---|
| imports | `public import ...Operators` + `...InferenceSystem` | `import Cslib.Init` + `...InferenceSystem` | add `Operators`; drop redundant `Cslib.Init` (arrives transitively; `checkInitImports` satisfied) |
| `Proposition` ctors | `atom, and, or, imp` | `atom, bot, imp, and, or` | keep the PR's (approved) five-ctor form |
| `Bot (Proposition Atom)` | `[Bot Atom]`, `⟨.atom ⊥⟩` | unconditional `⟨.bot⟩` | unconditional; **keep the name `instBotProposition`** |
| `instInhabitedOfBot` | `[Bot Atom] : Inhabited Atom` | absent | delete — used nowhere else in upstream (§4.4); itemize as an API removal |
| `neg` | `[Bot Atom]` | unconditional | unconditional |
| `top` | `[Inhabited Atom]`, `imp (.atom default) (.atom default)` | unconditional `imp .bot .bot` | unconditional; keep `instTopProposition` name |
| upstream's `example : (⊤ : Proposition Atom) = Proposition.imp ⊥ ⊥ := rfl` | `[Bot Atom]`-gated | — | **keep it, ungated** — under primitive bot it becomes unconditionally true, which is a clean demonstration of the design |
| notation | typeclass instances | 5 local `scoped infix`/`prefix` | **delete all 5 local declarations**; register `HasAnd`/`HasOr`/`HasImp`/`HasIff`/`HasNot`, all ungated |
| `not_eq` grind bridge | `[Bot Atom]`-gated | absent | **add, ungated** — required so #607's `grind` automation sees through derived `neg` |
| `Theory.MPL := ∅` | present | deleted | deleted (PR renames the empty theory to `IPL`) |
| `Theory.IPL` | `{⊥ → A | A}` | `∅` | PR's meaning (empty = IPL, since `efq` is primitive) |
| `efq_mem_ipl` | present | deleted | deleted |
| `intuitionisticCompletion` | present | deleted | deleted |
| `IsIntuitionistic` | present | deleted | deleted |
| `IsClassical` | `[Bot Atom]` + `[InferenceSystem S ...]` | ungated + `[InferenceSystem S ...]` | PR's (already correct) |

Two of these carry reviewer-visible weight and should be itemized explicitly in the PR
description rather than left to be discovered in the diff:

- **`IPL` is silently repurposed.** Upstream `IPL Atom = {⊥ → A | A}`; #648 makes `IPL = ∅`. Both
  names denote intuitionistic propositional logic, but the *definitions* are incompatible. This is
  correct under the approved design (empty theory + primitive `efq` = IPL) but a reviewer reading
  only the diff will see a name keep its identifier and change its meaning.
- **`MPL`, `intuitionisticCompletion`, `IsIntuitionistic`, `efq_mem_ipl`, `instInhabitedOfBot` are
  deleted.** All five are justified under primitive `bot` + primitive `efq`, and all five are
  provably unused outside the three Propositional files (§4.4) — but they are public API removals.

### 4.4 Blast radius: provably confined

```
$ git grep -l "Cslib.Logics.Propositional" upstream/main -- '*.lean'
Cslib.lean
Cslib/Logics/Propositional/NaturalDeduction/Basic.lean
Cslib/Logics/Propositional/NaturalDeduction/Theory.lean
```

Nothing outside the Propositional directory imports it. Every use of `IsIntuitionistic`,
`intuitionisticCompletion`, `MPL`, `efq_mem_ipl`, `instInhabitedOfBot`, and `instBotProposition` is
inside the three files #648 already rewrites. This is a strong, checkable safety argument to state
in the re-review request.

### 4.5 Notation precedence: a real behavioural change riding along

The PR's local notation and upstream's `Operators.lean` differ in both precedence and
associativity:

| Connective | PR #648 local | upstream `Operators.lean` |
|---|---|---|
| `∧` | `infix:36` | `infixr:36` |
| `∨` | `infix:35` | `infixr:30` |
| `→` | `infix:30` | `infixr:25` |
| `↔` | `infix:20` | `infixr:20` |
| `¬` | `prefix:40` | `notation:max "¬" p:40` |

Relative ordering `∧ > ∨ > →` is preserved on both sides, so no existing formula reparses to a
different tree. Adopting upstream's declarations also **fixes** a defect independently confirmed in
the source report: `infix:n` is non-associative, so chained `a → b → c` / `a ∧ b ∧ c` currently
fail — and fail badly, falling through to Lean's `Prop`-level `And`/`Or`/`→` and producing a type
mismatch rather than a notation error. Deleting the local declarations in favour of upstream's
instances resolves this for free. **Do not re-declare local notation** — both sets are `scoped` in
different namespaces (`Cslib.Logic` vs `Cslib.Logic.PL`), so keeping both would create genuine
ambiguity wherever both scopes are open.

---

## 5. The trivial conflict: `references.bib`

Both sides append at EOF; the merge base ended without a trailing newline. Verified no duplicate
keys — `upstream/main` contains no Avigad, Gentzen, Prawitz, or Troelstra entry.

- PR adds: `Gentzen1935`, `Prawitz1965`, `TroelstraVanDalen1988`, `Avigad2022`
- Upstream added since base: `Acclavio2026`, `Copes2018`, `AroraBarak09`, `Papadimitriou94`

Resolution: keep both blocks, upstream's first, PR's appended. No judgment required.

---

## 6. Disposition of ctchou's four bullets (factual scaffolding only)

Stated as verified facts for a human to write up. **This is not draft prose** — see §8.

| ctchou's bullet (verbatim) | Verified disposition |
|---|---|
| "I like the idea of adding \bot as a primitive." | Supportive, not an objection. Unchanged in the current PR. A third participant (Matthew Doty) independently backed primitive bot on DPLL grounds. |
| "I don't understand why we need both Semantics/Basic.lean and Semantics/Bool.lean. I think the latter alone is enough." | Moot against the current head: the PR ships **no** Semantics file. Verified — the diff is 4 files, none under `Semantics/`. Semantics was pulled out entirely at thomaskwaring's request and is deferred to a follow-up. |
| "It is not helpful to the readers to refer to old papers from the 1930s, some of which are in German... A good modern reference is Jeremy Avigad's textbook" | `Avigad2022` added and cited as the lead reference in both `Defs.lean` and `NaturalDeduction/Basic.lean`. The Gentzen entry was rewritten to the **English** Szabo translation (commit `1956d75b`), with the German original retained only as a `note`. |
| "You should definitely coordinate this PR with #607 abd #587. #536 is ready to merge, so you should wait for it." | **#536** MERGED 2026-06-16 — the PR was rebased onto it and reconciled `IsClassical` to the inference-system shape. **#607** MERGED 2026-08-03 — this rebase performs the coordination: it adopts #607's `imp` naming and registers against #607's `Operators.lean` typeclasses. **#587** is a stale **draft**, untouched since 2026-06-17, whose `Connectives.lean` was superseded by #607's `Operators.lean`; there is nothing live to coordinate with. |

Additional standing facts worth citing:

- thomaskwaring's five inline comments (2026-07-06) were **all** answered and resolved 2026-07-13.
- The one with downstream consequence — *"i don't have a strong opinion on `imp` vs `impl`, so long
  as after #607 lands it is consistent across the library (noting eg `Modal` has `impl` also)"* —
  is now discharged: #607 landed `imp`, and upstream `Modal/Basic.lean` uses
  `Proposition.imp` + `HasImp`.
- The Zulip compromise (2026-06-28: *"if we are going to have `bot` as a primitive, we should also
  have `efq`"*) was implemented 2026-06-29 and is what thomaskwaring approved on 2026-07-06.
- Primitive `efq` also **simplifies** the classical layer: `instIsClassicalLEM` /
  `instIsClassicalPierce` are now instances for `LEM Atom` / `Pierce Atom` directly, where upstream
  needs `LEM Atom ∪ IPL Atom` / `Pierce Atom ∪ IPL Atom`.

---

## 7. Recommended execution sequence

Sized so each step is independently verifiable. Zero-debt: no step admits a `sorry`, and none is
expected to need one — the PR branch already builds green against its base, and the reconciliation
is definitional, not proof-level.

1. **Fetch and confirm topology.** `git fetch upstream`; re-confirm the four rows of §2.1. Abort if
   `upstream/main` has moved past `3951377e` in a way that touches
   `Cslib/Logics/Propositional/` or `Cslib/Foundations/Logic/` — re-run the §2.4 probe if so.
2. **Create the rebase workspace from the PR branch only.**
   `git checkout -b <work> origin/feat/propositional-v2`. Never touch this fork's `main` (§3.1).
3. **Toolchain first.** After rebasing, `lean-toolchain` reads `v4.33.0`; run `lake exe cache get`
   before any build. Expect a long first build.
4. **`git rebase upstream/main`.** Expect conflicts on `Defs.lean` and `references.bib` only.
   Resolve `references.bib` mechanically (§5).
5. **Resolve `Defs.lean` per the §4.3 table.** This is the only step requiring judgment. Anchor on
   the PR's semantics (five primitives, ungated) and upstream's mechanism (typeclass instances from
   `Operators.lean`, Mathlib `Bot`/`Top`, `not_eq` grind bridge). Delete the five local notation
   declarations (§4.5).
6. **Verify the two ND files applied clean** and adjust only if the `Defs.lean` resolution forces
   it (e.g. `Equiv := IPL.Equiv` in `Basic.lean:159` region). No other change should be needed.
7. **Green the PR CI gates locally**, in this order:
   `lake build --wfail --iofail` → `lake test --wfail --iofail` → `lake exe mk_all --check` →
   `lake exe checkInitImports` → mathlib `lint-style` check.
   These four plus lint-style are the *entire* PR CI (`.github/workflows/lean_action_ci.yml`);
   `lake shake` is commented out, and environment linters are weekly-cron only.
8. **Update the PR description** to record: the rebase onto post-#607 `upstream/main`; the `IPL`
   repurposing and the five API deletions (§4.3); that `imp` is now settled by #607 (removing the
   "open to reverting" hedge); the corrected #587 status; and the AI-tools disclosure required by
   `CONTRIBUTING.md` §"The role of AI".
9. **Stop.** Push, `gh pr` writes, and the re-review request are user actions (§8).

Decision left to the user, flagged not resolved: whether to keep the PR's constructor order
(`atom, bot, imp, and, or`) or reorder to minimize diff noise against upstream
(`atom, and, or, imp` + `bot`). Recommendation: **keep the PR's order.** It is what was approved,
and reordering churns the match arms in `subst`, `weak`, `subs`, and `substAtom` across two files
that would otherwise apply untouched.

---

## 8. Hard constraints observed

- **No agent-initiated push, `gh pr` write, or Zulip post.** Per `.claude/rules/pr-prohibition.md`,
  those are user-invoked only. Everything in this report came from `git` (local, read-only) and
  `gh pr view` / `gh api ... GET`. The implementation phase must stop at a local commit and mark
  the task `[PR READY]`.
- **The GitHub text must be human-authored.** CSLib follows Mathlib's AI policy
  (`CONTRIBUTING.md` §"The role of AI"), and Chris Henson formally challenged an LLM-drafted
  message on this exact Zulip topic (`near/605827029`, 2026-06-22). §6 is therefore a verified
  fact table with dispositions and citations — **not prose to paste**. The re-review request and
  any Zulip message must be written from scratch by a human.
- **Scope is frozen at four files as approved.** No widening to the fork's `[IsIntuitionistic T]`-
  gated `efq` design, no re-adding the Semantics layer, no minimal-logic restoration. Each belongs
  in a separate follow-up PR.

---

## 9. Open follow-ups surfaced (out of scope here)

1. Gated `efq` + MPL restoration — the deferred fragment work.
2. The Semantics layer (`Bool.lean`, evaluation) — deferred at thomaskwaring's request; this is
   where ctchou's `Semantics/Basic.lean` vs `Semantics/Bool.lean` question should actually be
   answered.
3. This fork's `main` carries 117 Propositional files against upstream's 3, on a
   `Foundations/Logic/Connectives.lean` that upstream superseded with `Operators.lean`. Nothing
   about that divergence is addressed by this rebase, and it will need its own reconciliation
   strategy before any of that work can be upstreamed.
