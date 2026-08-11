# Reconciling `Foundations/Logic/Connectives.lean` against merged `Operators.lean`

**Task**: 619 — reconcile_connectives_operators
**Date**: 2026-08-10
**Status**: researched
**Type**: cslib (research)
**Source**: `specs/400_reconcile_connectives_pr607/reports/03_falsum-representation-decision.md`, §4 and
§9 Item 2. This task is that checklist item.
**Method**: `git`/`git merge-tree` against `upstream/main` @ `3951377e`, direct measurement of this
fork's Lean sources, and five `lean_run_code` experiments against this fork's live build.
**No `.lean` file was created, moved, or edited. Nothing was posted to GitHub or Zulip.**

---

## 0. Executive summary

Three findings, in descending order of consequence.

1. **The four named duplicates are the easy part.** `HasAnd`, `HasOr`, `HasImp`, `HasBox` are
   *field-for-field identical* between the two files — same class name, same namespace, same field
   name, same type. Adopting upstream's and deleting the fork's is a pure deletion with zero
   call-site churn: all 1,746 `HasImp`/`HasBox` references continue to resolve. `HasDia` → `HasDiamond`
   is a 6-site rename (field `dia` → `diamond`).

2. **The load-bearing collision is not the classes — it is the notation, and this report is the
   first place it is measured.** Upstream's `Operators.lean` attaches `scoped` notation
   (`∧ ∨ → ↔ ¬ □ ◇`) to the typeclass projections in `namespace Cslib.Logic`. This fork attaches its
   own `scoped` notation for the same symbols to concrete constructors in the *child* namespaces
   `Cslib.Logic.{PL, Modal, Bimodal, Temporal, LTL}`. Scoped notation from an enclosing namespace is
   active inside its children, so both interpretations become live simultaneously and Lean raises a
   hard **`Ambiguous term`** error. Measured empirically: **exactly 12 collision sites across 5
   files** (§3). Everything else in the fork's notation is safe.

3. **The reconciliation cannot be verified against the current tree without first bringing
   `Operators.lean` into it.** `upstream/main`'s `b8ad3923` is *not* an ancestor of local `HEAD`
   (`git merge-base HEAD b8ad3923` = `f36649cf`, 21 commits behind / 4,635 ahead), and
   `Cslib/Foundations/Logic/Operators.lean` does not exist locally. The task's own acceptance
   criterion ("verify with `lake build` that the tree stays green") therefore forces the
   implementation shape: **vendor upstream's `Operators.lean` verbatim** as the first phase, then
   reduce `Connectives.lean` to a delta over it. Vendoring the byte-identical file also makes the
   eventual `upstream/main` merge a clean add-add on that path (`git merge-tree` confirms
   `Operators.lean` is currently a conflict-free new file; the 6 files that *do* conflict are listed
   in §5.3 and are out of this task's scope).

**Recommended disposition**: adopt upstream wholesale for the 4 duplicates, rename `HasDia` →
`HasDiamond`, keep the fork's 4 fork-only atomic classes and 6 bundles unchanged as the upstreamable
delta, and delete the 12 colliding local notation declarations with upstream-style `@[scoped grind =]`
`_def` bridge lemmas as compensation.

---

## 1. Verified state of the record

| | |
|---|---|
| local `HEAD` | `212318f2` on `main` |
| `upstream/main` | `3951377e` — *"chore: bump toolchain to v4.33.0 (#789)"* |
| `git merge-base HEAD b8ad3923` | `f36649cf` (*"refactor(LocallyNameless)… (#740)"*) |
| `git merge-base --is-ancestor b8ad3923 HEAD` | **NO** — #607 is not in this fork |
| `git rev-list --count f36649cf..HEAD` / `..upstream/main` | `4635` / `21` |
| `Cslib/Foundations/Logic/Operators.lean` locally | **absent** |
| `git diff b8ad3923 upstream/main -- …/Operators.lean` | *empty* — the file has not changed since #607 merged |
| local toolchain / upstream toolchain | `v4.33.0-rc1` / `v4.33.0` |
| `lake build Cslib.Foundations.Logic.Connectives Cslib.Logics.Modal.Basic` | **green** (484 jobs), baseline established |

`Operators.lean` being frozen since `b8ad3923` matters: the vendoring target is stable, so a verbatim
copy will not go stale mid-implementation.

### 1.1 Why the collision is currently invisible

Because the fork has never merged #607, nothing is broken today. Two independent mechanisms will
break simultaneously the moment `Operators.lean` enters the tree:

**(a) Duplicate declaration.** Verified:

```
import Cslib.Foundations.Logic.Connectives
namespace Cslib.Logic
class HasAnd (α : Type*) where
  and (a b : α) : α
--> error: `Cslib.Logic.HasAnd` has already been declared
```

This is unconditional once both modules are in the same import closure, and `Cslib.lean` (the
`mk_all` barrel) imports every module, so it is guaranteed.

**(b) Notation ambiguity.** See §3 — this is the finding that sizes the task.

---

## 2. Per-class disposition

`Connectives.lean` declares 9 atomic classes + 6 bundles + 1 bridge instance. `Operators.lean`
declares 9 classes and no bundles.

### 2.1 The four hard duplicates — **adopt upstream, delete the fork's**

| Class | fork declaration | upstream declaration | Field name | Projection type | Verdict |
|---|---|---|---|---|---|
| `HasAnd` | `and : F → F → F` | `and (a b : α) : α` | `and` = `and` | identical | **drop fork's** |
| `HasOr` | `or : F → F → F` | `or (a b : α) : α` | `or` = `or` | identical | **drop fork's** |
| `HasImp` | `imp : F → F → F` | `imp (a b : α) : α` | `imp` = `imp` | identical | **drop fork's** |
| `HasBox` | `box : F → F` | `box (a : α) : α` | `box` = `box` | identical | **drop fork's** |

The binder-style difference (`imp : F → F → F` vs `imp (a b : α) : α`) is presentational only; both
elaborate the projection to `Cslib.Logic.HasImp.imp : {α : Type u_1} → [self : HasImp α] → α → α → α`.

**Consequence for call sites: none.** Because name, namespace, and field name all agree, every
existing reference resolves unchanged after the swap. Measured occurrence counts across
`Cslib/` + `CslibTests/`:

| `HasImp` | `HasBox` | `HasOr` | `HasAnd` |
|---:|---:|---:|---:|
| 1,514 | 204 | 56 | 28 |

None of these 1,802 sites needs editing. This is the single most important cost fact in the report:
the *class* reconciliation is nearly free.

**Doc loss to mitigate.** The fork's `HasBox` carries a substantial docstring (why box is primitive,
`ChagrovZakharyaschev1997` §3.1, the necessitation/K-axiom argument, `Blackburn2001`'s diamond-first
alternative); upstream's is one line. Deleting the fork's class deletes that prose. It should be
relocated — the natural home is the module docstring of `Connectives.lean`, or `Axioms.lean` where
`AxiomDiaDuality` already lives. Do not silently drop it; it is cited material.

### 2.2 The naming divergence — **rename `HasDia` → `HasDiamond`**

Upstream: `class HasDiamond (α : Type*)` with field `diamond`. Fork: `class HasDia (F : Type*)` with
field `dia`. Not a duplicate — a divergence, and the fork loses: upstream is merged, `HasDiamond`
pairs with `HasDynamicDiamond` in the same file, and the fork's `Connectives.lean` is precisely what
PR #649 proposes to carry upstream.

**Total footprint: 17 lines in 5 files**, of which only **6 are code**:

| File | Line | Kind |
|---|---|---|
| `Cslib/Foundations/Logic/Connectives.lean` | 112 | class declaration + field `dia` |
| `Cslib/Foundations/Logic/Axioms.lean` | 197 | `variable [HasDia F]` |
| `Cslib/Foundations/Logic/Axioms.lean` | 206, 217 | `HasDia.dia φ` (in `AxiomDiaDuality`) |
| `Cslib/Foundations/Logic/ProofSystem.lean` | 210 | `variable [HasDia F]` |
| `Cslib/Logics/Modal/Basic.lean` | 109–110 | `instance : HasDia (Proposition Atom)` |

The remaining 11 are docstring/comment mentions (`Connectives.lean:98,111,168`;
`Modal/Basic.lean:39,48,108`; `Axioms.lean:158,170,183,201`; `Modal/Semantics/Birelational.lean:47`).

**Open sub-decision for the planner**: whether the *fork-local* identifier `AxiomDiaDuality` and the
`Dia`-flavoured naming around it also rename (`AxiomDiamondDuality`). Recommendation: **yes**, in the
same pass — leaving `Dia` in fork-authored names while the class says `Diamond` reintroduces exactly
the inconsistency this task exists to remove. It is a mechanical rename inside fork-only territory.

### 2.3 Fork-only classes — **keep unchanged; this is the upstreamable delta**

| Class | Upstream equivalent | Verdict |
|---|---|---|
| `HasBot` (field `bot : F`) | none — upstream uses Mathlib `Bot` | **keep** (falsum decision settled: primitive bot) |
| `HasUntil` (`untl`) | none | **keep** — required by LTL/Temporal/Bimodal |
| `HasSince` (`snce`) | none | **keep** |
| `HasNext` (`next`) | none | **keep** |

No name collides with anything in `Operators.lean` or Mathlib. `HasBot` is orthogonal to Mathlib's
`Bot` (different name), and the fork already carries `instance : Bot (…)` alongside `HasBot` in
`Modal/Basic.lean:134`, `Temporal/Syntax/Formula.lean:178`, `LTL/Syntax/Formula.lean:217` without
issue — so keeping both is already-proven, not speculative.

### 2.4 Fork-only bundles — **keep, but record the direction-of-travel tension**

`PropositionalConnectives`, `ModalConnectives`, `FutureTemporalConnectives`, `LTLConnectives`,
`TemporalConnectives`, `BimodalConnectives`, plus the priority-100
`BimodalConnectives → ModalConnectives` bridge instance.

Upstream's `Operators.lean` is deliberately à-la-carte: one class per operator, no bundles. The
fork's bundles are load-bearing here — 194 `PropositionalConnectives` references, and the
`neg`/`top` Łukasiewicz *defaulted fields* on `PropositionalConnectives` are the single canonical
source that `Modal/Basic.lean:112-121`, `Bimodal/Syntax/Formula.lean:63-68`,
`Temporal/Syntax/Formula.lean:132-137`, and `LTL/Syntax/Formula.lean:172-178` all delegate to.

**Verdict: keep all six, unchanged, in this task.** They collide with nothing. Whether upstream will
*accept* bundles alongside its à-la-carte direction is a live question for the #649 review — but it
is a review question, not a build question, and resolving it here would be scope creep into a
decision no maintainer has been asked. Flag it in the #649 description; do not pre-emptively
dismantle a hierarchy that 220+ references depend on.

### 2.5 Upstream-only classes the fork does not have

`HasIff`, `HasNot`, `HasDynamicBox`, `HasDynamicDiamond`, `HasTensor`. All arrive free with the
vendored file. **Do not register fork instances for `HasIff` or `HasNot` in this task** — see §3.3,
where doing so would *create* new notation ambiguities that do not currently exist.

---

## 3. The measured second-order collision: notation ambiguity

This is the part of the task that is not visible from the class inventory, and it is where the real
work is.

### 3.1 Mechanism

`Operators.lean` declares, in `namespace Cslib.Logic`:

```lean
@[inherit_doc] scoped infixr:36 " ∧ " => HasAnd.and
@[inherit_doc] scoped infixr:30 " ∨ " => HasOr.or
@[inherit_doc] scoped infixr:25 " → " => HasImp.imp
@[inherit_doc] scoped infixr:20 " ↔ " => HasIff.iff
@[inherit_doc] scoped notation:max "¬" p:40 => HasNot.not p
@[inherit_doc] scoped prefix:40 "□" => HasBox.box
@[inherit_doc] scoped prefix:40 "◇" => HasDiamond.diamond
```

The fork declares the same symbols, scoped to concrete constructors, in `Cslib.Logic.PL`
(`Propositional/Defs.lean:107-111`), `Cslib.Logic.Modal` (`Modal/Basic.lean:231-237`),
`Cslib.Logic.Bimodal` (`Bimodal/Syntax/Formula.lean:98-109`), `Cslib.Logic.Temporal`
(`Temporal/Syntax/Formula.lean:166-175`), `Cslib.Logic.LTL` (`LTL/Syntax/Formula.lean:206-215`), and
`Cslib.Logic.LinearLogic…` (`CLL/Basic.lean:60`).

Entering `namespace Cslib.Logic.PL` activates scoped declarations of every enclosing namespace,
including `Cslib.Logic`. Both interpretations then elaborate successfully and Lean errors:

```
error: Ambiguous term
  a ∧ b
Possible interpretations:
  a ∧ b : Proposition A
  a ∧ b : Proposition A
```

(Verbatim from `lean_run_code` against this fork's build.)

**Critically, ambiguity requires *both* alternatives to elaborate.** When the concrete type has no
instance of the relevant class, upstream's notation fails to elaborate, the local one is the sole
survivor, and Lean resolves it **silently with no error**. Verified separately: `□ a` and `a ∧ b` on
`LTL.Formula` (which has neither `HasBox` nor `HasAnd`) compile clean under the simulated upstream
notation. This is what makes the blast radius small and *exactly* enumerable.

### 3.2 The exact collision set — 12 sites, 5 files

Simulated the full upstream notation set at upstream precedences against all five formula types
(`◇` bound to `HasDia.dia` to model the post-rename state). Result:

| File | Line | Symbol | Bound to | Why it collides |
|---|---:|---|---|---|
| `Cslib/Logics/Propositional/Defs.lean` | 107 | `∧` | `Proposition.and` | `HasAnd` instance at `Defs.lean:119` |
| | 108 | `∨` | `Proposition.or` | `HasOr` instance at `Defs.lean:123` |
| | 109 | `→` | `Proposition.imp` | `HasImp` via `PropositionalConnectives` at `Defs.lean:114` |
| `Cslib/Logics/Modal/Basic.lean` | 232 | `∧` | `Proposition.and` | `HasAnd` instance at `Basic.lean:101` |
| | 233 | `∨` | `Proposition.or` | `HasOr` instance at `Basic.lean:105` |
| | 234 | `→` | `Proposition.imp` | `HasImp` via `ModalConnectives` at `Basic.lean:95` |
| | 235 | `□` | `Proposition.box` | `HasBox` via `ModalConnectives` |
| | 236 | `◇` | `Proposition.diamond` | `HasDia` instance at `Basic.lean:109` |
| `Cslib/Logics/Bimodal/Syntax/Formula.lean` | 101 | `→` | `Formula.imp` | `HasImp` via `BimodalConnectives` at `Formula.lean:53` |
| | 102 | `□` | `Formula.box` | `HasBox` via `BimodalConnectives` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 169 | `→` | `Formula.imp` | `HasImp` via `TemporalConnectives` at `Formula.lean:123` |
| `Cslib/Logics/LTL/Syntax/Formula.lean` | 209 | `→` | `Formula.imp` | `HasImp` via `LTLConnectives` at `Formula.lean:162` |

**Confirmed clean (no instance ⇒ sole interpretation wins silently), keep as-is:**

- `¬` in all five namespaces — no fork type has a `HasNot` instance.
- `↔` in PL, Modal, Temporal, LTL — no fork type has a `HasIff` instance.
- `∧`, `∨` in Bimodal, Temporal, LTL — those `Formula` types have no `HasAnd`/`HasOr` instance
  (documented deliberately at `Connectives.lean:143-146`).
- `◇` in Bimodal and LTL, `□` in LTL — no `HasDia`/`HasBox` instance on those types
  (LTL binds `□`/`◇` to `allFuture`/`someFuture`, a *different* meaning that must be preserved).
- `⊗` in CLL — no `HasTensor` instance.
- All ASCII/unicode temporal operators (`U`, `S`, `𝓤`, `◯`, `⇝`, `F`/`G`/`P`/`H`, `𝐅`/`𝐆`/`𝐏`) —
  no upstream counterpart.

### 3.3 A latent trap the plan must record

The "clean" rows above are clean *only because an instance is missing*. Registering `HasNot`,
`HasIff`, `HasAnd`, `HasOr`, `HasDiamond`, or `HasTensor` for any of those types in a later task
will silently re-open the collision for that symbol. In particular:

- Registering `HasNot` for any formula type ⇒ 5 new `¬` collisions.
- Registering `HasIff` ⇒ 4 new `↔` collisions.
- LTL is the dangerous one: giving `LTL.Formula` a `HasBox`/`HasDiamond` instance would both collide
  *and* conflate `□`-as-necessity with `□`-as-`allFuture`.

This belongs in the `Connectives.lean` module docstring as a standing invariant, not only in a
report.

### 3.4 Resolution and its cost

Upstream's own #607 migration is the template: delete the per-type `scoped` notation, register the
instances, and add `@[scoped grind =] lemma X_def : φ.x = ⟨notation⟩ := rfl` bridge lemmas
(`Proposition.and_def`, `imp_def`, `box_def`, `diamond_def`, … in upstream's `Modal/Basic.lean`).

Deleting a local notation changes what the symbol *elaborates to* — from `Formula.imp a b` to
`HasImp.imp a b`. Two facts bound the risk:

- **They are `rfl`-equal.** Verified for all five affected pairings:
  `HasImp.imp a b = Bimodal.Formula.imp a b := rfl`, `HasBox.box a = Bimodal.Formula.box a := rfl`,
  `HasImp.imp a b = Modal.Proposition.imp a b := rfl`,
  `HasAnd.and a b = Modal.Proposition.and a b := rfl`,
  `HasDia.dia a = Modal.Proposition.diamond a := rfl`. All compiled clean.
- **Constructor pattern-matching is untouched** — `| .imp φ ψ => …` does not go through notation.

So the exposure is confined to *syntactic* matching: `simp`/`grind`/`rw` lemmas stated against the
concrete constructor no longer match terms built through the projection. That is precisely what the
`_def` bridge lemmas fix, and it is why they must land in the same phase as each notation deletion,
not afterwards.

**Sizing.** The affected subtrees total 201,583 lines across 488 files
(Propositional 42,561 / Modal 83,504 / Bimodal 52,462 / Temporal 20,310 / LTL 2,746). The *edit* is
12 deleted lines plus ~12 bridge lemmas; the *verification* is a full `lake build` of all of it. Plan
the phases around build cost, not edit cost, and sequence them smallest-first — **LTL (1 collision,
2,746 lines) → Temporal (1, 20,310) → Bimodal (2, 52,462) → Propositional (3, 42,561) → Modal (5,
83,504)** — so a regression is caught on a cheap module first.

---

## 4. Recommended implementation shape

The task's acceptance criterion (`lake build` green) is unsatisfiable while `Operators.lean` is
absent, so phase 1 is forced.

1. **Vendor `Operators.lean` verbatim.** `git show b8ad3923:Cslib/Foundations/Logic/Operators.lean >
   Cslib/Foundations/Logic/Operators.lean`. Byte-identical, so the eventual `upstream/main` merge is
   a clean add-add on that path. Add to `Cslib.lean` via `lake exe mk_all --module`. Do **not**
   hand-edit the vendored file — divergence here defeats the entire task.
2. **Reduce `Connectives.lean` to a delta.** Delete `HasAnd`/`HasOr`/`HasImp`/`HasBox`; add
   `public import Cslib.Foundations.Logic.Operators`; rename `HasDia` → `HasDiamond` (field `dia` →
   `diamond`); relocate the `HasBox` design docstring into the module docstring; keep `HasBot`,
   `HasUntil`, `HasSince`, `HasNext` and all six bundles.
3. **Propagate the rename** — 5 code sites in `Axioms.lean`, `ProofSystem.lean`, `Modal/Basic.lean`,
   plus the 11 doc mentions, plus (recommended) `AxiomDiaDuality` → `AxiomDiamondDuality`.
4. **Notation de-duplication, one module per phase, smallest-first** (§3.4 ordering): delete the
   listed local declaration, add the `_def` bridge lemma(s), `lake build <Module>` green before
   moving on.
5. **Full-gate verification**: `lake build`, `lake exe checkInitImports`, `lake lint`,
   `lake exe lint-style`, `lake test`, `lake exe mk_all --module`,
   `lake shake --add-public --keep-implied --keep-prefix`.

### Lint prevention for this task specifically

- The vendored `Operators.lean` already carries per-field docstrings and passes upstream CI — do not
  add to it.
- `HasDiamond` and every retained fork class/bundle needs its docstring preserved through the edit
  (`docBlame`).
- The `_def` bridge lemmas must be `lemma`, not `def` (`defLemma`), and must be named
  lowerCamelCase without underscores in the *namespace-qualified head*
  (upstream's `Proposition.imp_def` is the sanctioned shape).
- `Operators.lean` uses `public import Cslib.Init`; `Connectives.lean` currently uses bare
  `import Cslib.Init`. Keep `Connectives.lean`'s import of `Operators` `public` so downstream
  modules still see the classes.

---

## 5. Risks, scope boundaries, and what this task must NOT absorb

### 5.1 Zero-debt compliance

No step above requires `sorry`, and none introduces an axiom. Every change is a deletion, a rename,
or an `rfl` bridge lemma. If a `_def` bridge lemma does not close by `rfl`, that is a *signal* that
the instance and the constructor have drifted — escalate as `[BLOCKED]`, do not paper over it.

### 5.2 Named risks

| Risk | Assessment | Mitigation |
|---|---|---|
| Deleting local `→` notation breaks `simp`/`grind` proofs at scale | Real, and the dominant risk | `_def` bridge lemma in the same edit; per-module build gate; smallest-first ordering |
| Vendored `Operators.lean` drifts from upstream | Low — file unchanged since `b8ad3923` | Verbatim copy, never hand-edited; re-verify with `git diff b8ad3923 upstream/main` before starting |
| `AxiomDiaDuality` rename ripples wider than expected | Low — 4 sites | Confirm with `grep -rn 'AxiomDia'` before the pass |
| Toolchain gap (`v4.33.0-rc1` vs `v4.33.0`) | Not a differentiator | Out of scope; belongs to the #648 rebase |
| Bundles rejected upstream in #649 review | Live but external | Flag in the PR description; do not pre-emptively dismantle |

### 5.3 Explicitly out of scope

- **Merging `upstream/main`.** `git merge-tree HEAD upstream/main` reports content conflicts in
  `Cslib.lean`, `Cslib/Foundations/Logic/InferenceSystem.lean`, `Cslib/Logics/Modal/Basic.lean`,
  `Cslib/Logics/Modal/LogicalEquivalence.lean`, `Cslib/Logics/Propositional/Defs.lean`,
  `CslibTests.lean`, and `references.bib`. Notably `Operators.lean` is **not** among them. Resolving
  those 7 is the #648 rebase, a separate task.
- **The falsum representation question** — settled (primitive `HasBot` retained), per the source
  report. Do not reopen.
- **Notation associativity/precedence for the *retained* fork notations** (source report §9 Item 3:
  `infix` → `infixr` in `Propositional/Defs.lean`). Partially overtaken by this task — the three PL
  declarations at lines 107-109 are *deleted* here, which fixes chaining for `∧`/`∨`/`→` in PL as a
  side effect. The `↔` and `¬` declarations at lines 110-111 survive and still need that fix. Keep
  Item 3 open, narrowed to those two lines plus the corresponding declarations in Modal, Bimodal,
  Temporal, LTL.
- **Registering `HasNot`/`HasIff` instances** — would create new collisions (§3.3). Separate task,
  paired with deleting the corresponding local notation.
- **Any GitHub or Zulip prose.** Per the CSLib AI policy and the formal challenge Chris Henson
  raised on the Propositional Logic topic (`near/605827029`), no agent-authored outward text. If
  #649's description needs updating, produce a factual scaffolding file for a human to rewrite.

---

## 6. Commands and experiments run (reproducibility)

```bash
git merge-base --is-ancestor b8ad3923 HEAD; echo $?
git merge-base HEAD b8ad3923
git show --stat --oneline b8ad3923
git show b8ad3923:Cslib/Foundations/Logic/Operators.lean
git diff b8ad3923 upstream/main -- Cslib/Foundations/Logic/Operators.lean     # empty
git show b8ad3923 -- Cslib/Logics/Modal/Basic.lean Cslib/Logics/Propositional/Defs.lean
git merge-tree --write-tree --name-only HEAD upstream/main
git rev-list --count f36649cf..HEAD ; git rev-list --count f36649cf..upstream/main
grep -rn 'HasDia' --include=*.lean Cslib/ CslibTests/
grep -rho '\bHasImp\b' --include=*.lean Cslib/ CslibTests/ | wc -l   # per-class census
lake build Cslib.Foundations.Logic.Connectives Cslib.Logics.Modal.Basic   # green, 484 jobs
```

Five `lean_run_code` experiments against this fork's live build:

1. Duplicate-declaration check → `` `Cslib.Logic.HasAnd` has already been declared ``.
2. Two-symbol ambiguity probe (`∧`, `→` in `Cslib.Logic.PL`) → 2 × `Ambiguous term`.
3. Sole-interpretation probe (`□`, `∧` on `LTL.Formula`, no instance) → **clean, no error**.
4. Full five-namespace × five-symbol matrix → the 12 collisions tabulated in §3.2.
5. Defeq probe → five `rfl` proofs of `HasX.x … = Concrete.x …`, all clean.
