# Research Report: Reconciling `→` Notation with Upstream (Precedence + Associativity)

**Task**: 497 — `reconcile_imp_naming` (retargeted to a notation-only task)
**Task type**: cslib
**Session**: `sess_1786397542_991316_497`
**Date**: 2026-08-10
**Scope**: parts (a) precedence and (b) associativity, in the four `file_scope` files.
Part (c) (typeclass fold onto `HasImp`) is out of scope — it belongs to the
`reconcile_connectives_operators` sibling task.

---

## Executive Summary

The arrow-only change (`infix:30` → `infixr:25` in the four in-scope files) was **applied and
built**: 372 modules, 2013 jobs, **exit 0, zero errors, warning count unchanged (32 → 32)**,
with 364 of 434 `.olean` files genuinely recompiled. **Transitive parse impact is empirically
zero.** No existing site relies on the current non-associative parse.

One correction to the task framing is load-bearing and changes the recommended edit set:

> The framing states the fork's ordering is `∧36 > ∨35 > →30 > ↔20`, and concludes that "moving
> `→` alone inverts no relationship." **That ordering holds only for `Propositional/Defs.lean`,
> which is explicitly out of scope.** In three of the four in-scope files — `Modal/Basic.lean`,
> `LTL/Syntax/Formula.lean`, `Temporal/Syntax/Formula.lean` — `↔` is declared at **`infix:30`**,
> the same level as `→`. Moving `→` alone to 25 therefore leaves `↔` binding *tighter* than `→`,
> which **does** invert the standard relationship and diverges from upstream.

This was confirmed by `rfl`, not inferred (see §4). The recommendation is to move `↔` to
`infixr:20` in those three files alongside `→`. That combined change was also applied and built
green under identical conditions.

`∧`/`∨` do **not** need to move: their order relative to `→` is preserved at either precedence,
and the build confirms no impact. Defer them to the notation-wide reconciliation.

---

## 1. Current Notation Declarations (all connectives, with line numbers)

### 1.1 `Cslib/Logics/Bimodal/Syntax/Formula.lean`

| Line | Declaration | Note |
|---|---|---|
| 98  | `@[inherit_doc] scoped prefix:40 "¬" => Formula.neg` | |
| 99  | `@[inherit_doc] scoped infix:36 " ∧ " => Formula.and` | |
| 100 | `@[inherit_doc] scoped infix:35 " ∨ " => Formula.or` | |
| **101** | `@[inherit_doc] scoped infix:30 " → " => Formula.imp` | **target** |
| 102 | `@[inherit_doc] scoped prefix:40 "□" => Formula.box` | |
| 103 | `@[inherit_doc] scoped prefix:40 "◇" => Formula.diamond` | |
| 104 | `@[inherit_doc] scoped infix:40 " U " => Formula.untl` | |
| 105 | `@[inherit_doc] scoped infix:40 " S " => Formula.snce` | |
| 106–109 | `prefix:40` for `F`/`G`/`P`/`H` | |

**Bimodal declares no `↔` at all** (`grep -n "iff\|↔"` on this file returns nothing). Nothing to
align there.

### 1.2 `Cslib/Logics/LTL/Syntax/Formula.lean`

| Line | Declaration | Note |
|---|---|---|
| 206 | `scoped prefix:40 "¬" => Formula.neg` | |
| 207 | `scoped infix:36 " ∧ " => Formula.and` | |
| 208 | `scoped infix:35 " ∨ " => Formula.or` | |
| **209** | `scoped infix:30 " → " => Formula.imp` | **target** |
| **210** | `scoped infix:30 " ↔ " => Formula.iff` | **entangled — see §4** |
| 211 | `scoped infix:40 " 𝓤 " => Formula.untl` | |
| 212–214 | `prefix:40` for `◯`, `◇`, `□` | |
| 215 | `scoped infix:20 " ⇝ " => Formula.leadsto` | see §5.3 |

Header docstring lines **33–45** carry a human-readable precedence table that must be updated in
lockstep (lines 37 and 38 state `(infix, 30)` for `→` and `↔`).

### 1.3 `Cslib/Logics/Modal/Basic.lean`

| Line | Declaration | Note |
|---|---|---|
| 231 | `scoped prefix:40 "¬" => Proposition.neg` | |
| 232 | `scoped infix:36 " ∧ " => Proposition.and` | |
| 233 | `scoped infix:35 " ∨ " => Proposition.or` | |
| **234** | `scoped infix:30 " → " => Proposition.imp` | **target** |
| 235 | `scoped prefix:40 "□" => Proposition.box` | |
| 236 | `scoped prefix:40 "◇" => Proposition.diamond` | |
| **237** | `scoped infix:30 " ↔ " => Proposition.iff` | **entangled — see §4** |
| 278 | `scoped notation "Modal[" m "," w " ⊨ " φ "]" => Judgement.mk m w φ` | closed delimiters; precedence-immune |

No prose precedence table in this file's header.

### 1.4 `Cslib/Logics/Temporal/Syntax/Formula.lean`

| Line | Declaration | Note |
|---|---|---|
| 166 | `scoped prefix:40 "¬" => Formula.neg` | |
| 167 | `scoped infix:36 " ∧ " => Formula.and` | |
| 168 | `scoped infix:35 " ∨ " => Formula.or` | |
| **169** | `scoped infix:30 " → " => Formula.imp` | **target** |
| **170** | `scoped infix:30 " ↔ " => Formula.iff` | **entangled — see §4** |
| 171 | `scoped infix:40 " U " => Formula.untl` | |
| 172 | `scoped infix:40 " S " => Formula.snce` | |
| 173–176 | `prefix:40` for `𝐅`/`𝐆`/`𝐏`/`𝐇` | |
| 348, 351 | `scoped prefix:80` for `△`, `▽` | |

Header docstring lines **33–48** carry a precedence table; lines 37–38 need updating.

### 1.5 Upstream reference (`Cslib/Foundations/Logic/Operators.lean` @ `upstream/main`)

| Line | Declaration |
|---|---|
| 31 | `@[inherit_doc] scoped infixr:36 " ∧ " => HasAnd.and` |
| 38 | `@[inherit_doc] scoped infixr:30 " ∨ " => HasOr.or` |
| **45** | `@[inherit_doc] scoped infixr:25 " → " => HasImp.imp` |
| **52** | `@[inherit_doc] scoped infixr:20 " ↔ " => HasIff.iff` |
| 59 | `@[inherit_doc] scoped notation:max "¬" p:40 => HasNot.not p` |
| 72, 79 | `scoped prefix:40` for `□`, `◇` |
| 116 | `@[inherit_doc] scoped infixr:35 " ⊗ " => HasTensor.tensor` |

Upstream is right-associative throughout. Note `¬` upstream is `notation:max` with arg `:40`,
where the fork uses `prefix:40`; that difference is out of scope and harmless (both admit
`¬p ∧ q` and `¬p → q`).

---

## 2. Transitive Parse Impact: Measured, Not Estimated

### 2.1 Method

Target set derived mechanically from `Cslib.lean`:

```
grep -oE "Cslib\.Logics\.(Bimodal|LTL|Modal|Temporal)[A-Za-z0-9_.]*" Cslib.lean | sort -u
```

→ **372 modules** (Bimodal 139, LTL 12, Modal 163, Temporal 58). Built via
`lake build $(cat targets.txt)`, which sidesteps the known full-build stall on
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (that module is not in this
dependency cone).

### 2.2 Results

| Run | Change | Exit | Jobs | Errors | Warnings |
|---|---|---|---|---|---|
| Baseline | none | 0 | 2013 | 0 | 32 |
| **A. Arrow-only** | `infix:30 " → "` → `infixr:25 " → "` in all 4 files | **0** | 2013 | **0** | 32 |
| **B. Arrow + iff** | A, plus `infix:30 " ↔ "` → `infixr:20 " ↔ "` in Modal/LTL/Temporal | **0** | 2013 | **0** | 32 |

Recompilation was genuine, not cached: 364 of 434 `.olean` files under the four subtrees carry
mtimes postdating the source edit.

**The working tree was reverted after the experiment** (`git checkout --` on the four files);
`git status -- Cslib/` is clean.

### 2.3 Answer to research question 2

**Zero sites require fixing.** The set of existing sites relying on the current non-associative
parse is empty. This is not a sampling result — it is a full build of every module in the
dependency cone of all four in-scope files.

### 2.4 Why the impact is zero (mechanism)

Lowering the arrow's precedence 30 → 25 makes the `→` *node* looser, so the only way to break
existing code is for a `→` term to sit unparenthesized as an argument of a notation demanding
precedence in `[26, 30]`. A repo-wide scan for such notations found exactly one class of
candidate:

- `Cslib/Foundations/Logic/LogicalEquivalence.lean:33` — `scoped infix:29 " ≡ "` (args require
  ≥ 30). Also `Cslib/Logics/LinearLogic/CLL/Basic.lean:255,263` and
  `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:279`, same level.

This hazard is **real in principle** and was confirmed in a minimal model: with `≡` at
`infix:29`, `a ≡ a → a` parses when `→` is at 30 and **fails** when `→` is at 25 (requiring
`a ≡ (a → a)`). It is **inert in practice** for the four in-scope subtrees:

- Every `≡`-adjacent-`→` line found in Bimodal/LTL/Modal/Temporal is a comment or docstring
  (`Modal/Metalogic/Constructive/CS5.lean:118`, `Temporal/Tableau/Rules.lean:345,353`).
- Modal's own equivalence notation is `Cslib/Logics/Modal/LogicalEquivalence.lean:98`
  — `scoped notation:50 φ₁ " ≡ " φ₂`, whose **unannotated** arguments accept a full `term`,
  so it is precedence-immune.
- The `≡[T]` form with an annotated `B:29` argument lives in `Propositional/NaturalDeduction`,
  outside scope, and its live uses are already parenthesized
  (`Basic.lean:516`: `(A → B) ≡[T] (A' → B')`).

Two further shapes were checked explicitly and are **not** regressions:

- **Derivation/turnstile notations** (`Γ ⊢ φ → ψ`, the single most common shape in the tree):
  `Bimodal/ProofSystem/Derivation.lean:108` and `Temporal/ProofSystem/Derivation.lean:86` use
  `notation:50` with **unannotated** arguments. Verified in a model that an `infixr:25` arrow
  fits such an argument. Safe.
- **Validity notations** with annotated `φ:50` (`Temporal/Semantics/Validity.lean:142,145`,
  `Bimodal/Semantics/Validity.lean:60,81`): these reject an arrow at 25 — but they already reject
  one at 30 (30 < 50), so those sites are *already* parenthesized today. No change.

---

## 3. Confirmation Against Upstream (research question 4)

`git fetch upstream` run 2026-08-10.

| Check | Command | Result |
|---|---|---|
| `b8ad3923` ancestor of `upstream/main`? | `git merge-base --is-ancestor b8ad3923 upstream/main` | **YES** |
| `b8ad3923` ancestor of fork `HEAD`? | `git merge-base --is-ancestor b8ad3923 HEAD` | **NO** (unchanged from prior verification) |
| The commit | `git log -1 b8ad3923` | `feat(Logic): logical operators (#607)`, Mon 2026-08-03 |
| `upstream/main` tip | | `3951377e5a3f5772737f11cd62bc5bb6a72f95d1` — `chore: bump toolchain to v4.33.0 (#789)`, 2026-08-10 |
| Fork/upstream merge-base | | `f36649cff2c9d9fa1f91a848caa5c5a6f9d6bab1`, 2026-07-25 |

`Cslib/Foundations/Logic/Operators.lean` does **not** exist in the fork
(`ls Cslib/Foundations/Logic/` confirms). The fork's counterpart is
`Cslib/Foundations/Logic/Connectives.lean`, which declares `HasImp` at line 85 with **no
notation bound to it** — consistent with the task framing, and reserved for the sibling task.

---

## 4. Should the Sibling Connectives Move? (research question 3)

### 4.1 `↔` — YES, in Modal / LTL / Temporal. This is a genuine correction to the framing.

The framing's premise (`↔` at 20) is true only of the excluded `Propositional/Defs.lean:110`.
In the three in-scope files that declare `↔`, it sits at `infix:30` — the **same** level as `→`.

Today both are non-associative at 30, so `a → b ↔ c` and `a ↔ b → c` **both fail to parse**;
no ordering between `→` and `↔` is expressed at all. Move `→` to 25 alone and an ordering
suddenly appears — the wrong one.

Verified by `rfl` against the real `Temporal.Formula` type:

```lean
-- with → at infixr:25 and ↔ LEFT at infix:30 (arrow-only variant):
example (a b c : Formula Nat) : (a ⟹ b ⟺ c) = (a → (b ↔ c)) := rfl   -- INVERTED
-- with → at infixr:25 and ↔ moved to infixr:20:
example (a b c : Formula Nat) : (a → b ↔ c) = ((a → b) ↔ c) := rfl    -- standard, matches upstream
```

So the arrow-only variant silently *starts accepting* `a → b ↔ c` and binds it as
`a → (b ↔ c)` — backwards from both standard logical convention and upstream's `↔` at 20.

Severity nuance worth recording: this **cannot** silently change the meaning of any existing
code, because the shape is currently unparseable, so no such site exists (and the build confirms
it). It is a forward-facing trap, not a live defect. But leaving a known-inverted precedence in
the tree between this task and the notation-wide reconciliation is a latent hazard for zero cost
avoided — variant B builds green.

**Bimodal needs no `↔` edit** (it declares none).

### 4.2 `∧` (36) and `∨` (35) — NO, leave them

- Relative order is preserved at either arrow precedence: `∧36 > ∨35 > →25` and
  `∧36 > ∨30 > →25` both hold. Moving `→` alone inverts nothing here — the framing's claim is
  correct for `∧`/`∨`.
- Neither can appear unparenthesized as an argument where the change matters: `∧`'s args need
  ≥ 37 and `∨`'s need ≥ 36, so an arrow term already required parentheses under both regimes.
- Build variant A confirms zero impact.
- `∨` at 35 vs upstream's 30 is a real remaining divergence, as is the fork's use of
  non-associative `infix` for `∧`/`∨` (so `a ∧ b ∧ c` fails in the fork exactly as `a → b → c`
  does). Both belong to the notation-wide reconciliation, not here.

### 4.3 Resulting precedence table

| Connective | Fork now (Modal/LTL/Temporal) | After recommended change | Upstream |
|---|---|---|---|
| `¬` | `prefix:40` | unchanged | `notation:max … p:40` |
| `∧` | `infix:36` | unchanged | `infixr:36` |
| `∨` | `infix:35` | unchanged | `infixr:30` |
| **`→`** | `infix:30` | **`infixr:25`** | `infixr:25` |
| **`↔`** | `infix:30` | **`infixr:20`** | `infixr:20` |

Order after the change: `∧36 > ∨35 > →25 > ↔20` — same order as upstream, coherent, with `→`
and `↔` at upstream's exact levels.

---

## 5. Implementation Notes for Planning

### 5.1 Edit set (7 declaration lines + 2 docstring tables)

| File | Line | From | To |
|---|---|---|---|
| `Cslib/Logics/Bimodal/Syntax/Formula.lean` | 101 | `scoped infix:30 " → "` | `scoped infixr:25 " → "` |
| `Cslib/Logics/LTL/Syntax/Formula.lean` | 209 | `scoped infix:30 " → "` | `scoped infixr:25 " → "` |
| `Cslib/Logics/LTL/Syntax/Formula.lean` | 210 | `scoped infix:30 " ↔ "` | `scoped infixr:20 " ↔ "` |
| `Cslib/Logics/Modal/Basic.lean` | 234 | `scoped infix:30 " → "` | `scoped infixr:25 " → "` |
| `Cslib/Logics/Modal/Basic.lean` | 237 | `scoped infix:30 " ↔ "` | `scoped infixr:20 " ↔ "` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 169 | `scoped infix:30 " → "` | `scoped infixr:25 " → "` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 170 | `scoped infix:30 " ↔ "` | `scoped infixr:20 " ↔ "` |

Plus prose updates:
- `Cslib/Logics/LTL/Syntax/Formula.lean:37–38` — `(infix, 30)` → `(infixr, 25)` / `(infixr, 20)`
- `Cslib/Logics/Temporal/Syntax/Formula.lean:37–38` — same

No other file needs editing. `NOTATION.md` contains no precedence table (its only relevant entry
is line 57, about `S` as *Since*, unaffected).

### 5.2 Verification recipe (avoids the known stall)

```bash
grep -oE "Cslib\.Logics\.(Bimodal|LTL|Modal|Temporal)[A-Za-z0-9_.]*" Cslib.lean | sort -u > /tmp/targets.txt
lake build $(cat /tmp/targets.txt)   # expect: exit 0, 2013 jobs, 0 errors, 32 warnings
```

Warning count must stay at 32 — a rise would indicate new `unusedSectionVars`/`simpNF` fallout.
Do **not** run a bare full `lake build` (stalls on `Propositional/Tableau/Intuitionistic/
Scheme.lean`), and do **not** use `lake env lean <file>` without `--setup`.

Capability regression test (all four namespaces, verified working post-change):

```lean
example (a b c : Formula Nat) : Formula Nat := a → b → c          -- Bimodal, LTL, Temporal
example (a b c : Proposition Nat) : Proposition Nat := a → b → c  -- Modal
example (a b c : Formula Nat) : (a → b → c) = (a → (b → c)) := rfl
example (a b c : Formula Nat) : (a → b ↔ c) = ((a → b) ↔ c) := rfl
```

### 5.3 Minor note: LTL's `⇝` at `infix:20`

Moving `↔` to 20 puts it at the same level as `Formula.leadsto` (`⇝`,
`LTL/Syntax/Formula.lean:215`). Today `a ⇝ b ↔ c` parses as `a ⇝ (b ↔ c)` (since `⇝`'s args need
≥ 21 and `↔` sits at 30); after the change both are at 20 and that shape needs parentheses. The
build proves no live site does this. If it matters aesthetically, `⇝` could move to a lower level,
but that is a judgement call outside this task's scope and upstream has no `⇝` to match against.

### 5.4 Zero-debt posture

No `sorry` is involved anywhere in this change — it is a pure notation-declaration edit with an
empirically green build. There is no proof obligation to defer and no axiom to introduce.

### 5.5 Lint posture

The edited lines keep their `@[inherit_doc]` attributes, so `docBlame` is unaffected. No new
declarations are introduced, so `defLemma`, `defsWithUnderscore`, `dupNamespace`, and
`topNamespace` are not engaged. `simpNF` and `unusedSectionVars` are unaffected — warning count
held at 32 across both experimental builds.

---

## 6. Open Items Explicitly NOT Addressed Here

1. **Part (c)** — binding `→` to `Cslib.Logic.HasImp` (`Foundations/Logic/Connectives.lean:85`,
   1039 usage sites, currently notation-free) and reconciling `Connectives.lean` against
   upstream's `Operators.lean`. Sibling task.
2. **`Cslib/Logics/Propositional/Defs.lean`** — owned by the sibling task carrying the
   standing-approval dependency chain. Untouched, as instructed.
3. **`∨` at 35 vs upstream 30**, and **`infix` → `infixr` for `∧`/`∨`** — real divergences,
   deferred to the notation-wide reconciliation.
4. **The `Scheme.lean` full-build stall** — pre-existing, tracked separately, gates only final
   whole-tree verification.
5. **4 residual `impl` tokens** — local tactic hypothesis names in `Connectives.lean`; cosmetic,
   out of scope per the task description.

---

## 7. Evidence Index

| Claim | Evidence |
|---|---|
| Arrow-only change is parse-impact-free | `lake build` over 372 modules: exit 0, 2013 jobs, 0 errors |
| Rebuild was genuine, not cached | 364/434 `.olean` mtimes postdate the edit |
| Arrow + `↔` change is also green | second `lake build`: exit 0, 2013 jobs, 0 errors, 32 warnings |
| `→` becomes right-associative | `example … : (a → b → c) = (a → (b → c)) := rfl` |
| `↔` at 20 gives the standard binding | `example … : (a → b ↔ c) = ((a → b) ↔ c) := rfl` |
| Leaving `↔` at 30 inverts the binding | `example … : (a ⟹ b ⟺ c) = (a → (b ↔ c)) := rfl` |
| `a → b → c` fails today | model build: `type expected, got (a : F)` (Lean's `Prop` arrow wins) |
| `≡` at `infix:29` is the only precedence hazard class | repo-wide scan for notations with arg precedence in `[26,30]` |
| That hazard has no live site in scope | all `≡`/`→` co-occurrences in the four subtrees are comments |
| Turnstile notations are precedence-immune | unannotated `notation:50` args accept an `infixr:25` term (model build) |
| `b8ad3923` in upstream, not in fork | `git merge-base --is-ancestor` both directions |
