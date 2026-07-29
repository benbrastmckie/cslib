# Research Report: Upstream Packaging of Propositional Semantics (Follow-up to PR #648)

**Task 226**: propositional_semantics_upstream_pr
**Session**: sess_1784907631_dfd0bb_226
**Date**: 2026-07-24
**Type**: Re-research (builds on `reports/02_three-way-comparison.md`)

## 0. Relationship to Prior Report

The prior report (`02_three-way-comparison.md`) compared our implementation against Thomas
Waring's and Matthew Doty's forks and recommended an `Algebra + Bool + Bridge` PR at ~378 LOC.
This report **supersedes the LOC and scope numbers** in that report (the files have grown) and
adds the decisive new finding the prior report lacked: **exactly what PR #648 contains**, which
determines the true dependency footprint of each candidate file. The design discussion in the
prior report (bot-as-primitive vs bot-as-atom, `bot_val` rationale) remains valid and is not
repeated here.

## 1. The Four Target Files: Exact Paths and Current LOC

All four files live under `Cslib/Logics/Propositional/Semantics/`:

| # | File | Path | LOC | Sorry |
|---|------|------|-----|-------|
| 1 | Algebra.lean | `Cslib/Logics/Propositional/Semantics/Algebra.lean` | 164 | none |
| 2 | Bool.lean | `Cslib/Logics/Propositional/Semantics/Bool.lean` | 190 | none |
| 3 | SemanticConsequence.lean | `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` | 295 | none |
| 4 | Kripke.lean | `Cslib/Logics/Propositional/Semantics/Kripke.lean` | 170 | none |
| | **Total (all four)** | | **819** | **0** |

The prior report listed 145 / 149 / 180 / 170; the first three have grown to 164 / 190 / 295.
**All four are sorry-free** (verified by grep for `sorry`/`admit`). The 819 LOC total is
**~64% over the <500 LOC budget** — the four files cannot all ship together.

The "bridge to AlgEvaluate" named in task scope item (2) does **not** live in `Bool.lean`
(which imports only `Defs`, not `Algebra`). It lives in a fifth file,
`Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` (**133 LOC**, imports `Algebra` +
`Bool`), which provides the `Evaluate`/`BoolEvaluate` ↔ `AlgEvaluate` correspondence. Delivering
the item-(2) "bridge" literally requires including `Bridge.lean`.

## 2. Dependency Footprint (the decisive finding)

**What PR #648 (`origin/feat/propositional-v2`) actually contains** — exactly three
Propositional files:

```
Cslib/Logics/Propositional/Defs.lean                    (formula type: PL.Proposition)
Cslib/Logics/Propositional/NaturalDeduction/Basic.lean  (natural deduction)
Cslib/Logics/Propositional/NaturalDeduction/Theory.lean (natural deduction)
```

There is **no** `Semantics/`, **no** `ProofSystem/`, **no** `Metalogic/`, and **no**
`NaturalDeduction/Equivalence.lean` in #648. This is the base the follow-up stacks on.

Per-file dependency analysis (imports beyond `Cslib.Init` and Mathlib):

| File | Non-Mathlib imports | All in #648? | Verdict |
|------|--------------------|-------------|---------|
| **Algebra.lean** | `Propositional.Defs` | ✅ yes | **CLEAN** — Defs + `Mathlib.Order.Heyting.Basic`, `Mathlib.Order.BooleanAlgebra.Basic` |
| **Bool.lean** | `Propositional.Defs` | ✅ yes | **CLEAN** — Defs + `Mathlib.Data.Fintype.Pi` |
| **Kripke.lean** | `Propositional.Defs` | ✅ yes | **CLEAN** — Defs + `Mathlib.Order.Defs.PartialOrder`, `Mathlib.Order.Defs.Unbundled` |
| **Bridge.lean** (5th) | `Semantics.Algebra`, `Semantics.Bool` | ✅ (if those ship) | **CLEAN** — no new upstream deps |
| **SemanticConsequence.lean** | `Semantics.Bool`, `Semantics.Kripke`, **`ProofSystem.Derivation`**, **`Metalogic.DeductionTheorem`**, **`NaturalDeduction.Equivalence`** | ❌ **NO** | **DIRTY** — pulls in the Hilbert proof system + metalogic, none of which is upstream |

**Conclusion:** three of the four target files (Algebra, Bool, Kripke) plus the bridge
(Bridge.lean) depend **only** on `Defs` (from #648) and Mathlib — perfectly packageable.
`SemanticConsequence.lean` is the outlier: its three bolded imports drag in the entire
Hilbert `ProofSystem/Derivation`, `Metalogic/DeductionTheorem`, and `NaturalDeduction/Equivalence`
layers, **none of which is in #648**. It cannot ship in this follow-up in its current form.

### 2.1 SemanticConsequence.lean splits cleanly into two halves

Its declarations partition by dependency:

- **Syntactic half (NOT upstream-ready)** — `SetDerivable` and lemmas
  `SetDerivable_of_mem/_weakening/_of_Derivable/_empty_iff/_mp`, `setDeriv_deduction`,
  `setDeriv_cut`. These are what pull in `ProofSystem.Derivation`, `Metalogic.DeductionTheorem`,
  and `NaturalDeduction.Equivalence`.
- **Semantic half (upstream-ready)** — `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails`
  (the actual "semantic consequence" definitions of task item 3) and
  `SemanticEntails_of_Tautology`, `ISemanticEntails_of_IValid`, `MSemanticEntails_of_MValid`.
  These need only `Bool` + `Kripke`.

A trimmed `SemanticConsequence.lean` keeping only the semantic half would be ~100–120 LOC and
depend only on `Bool` + `Kripke`. This is the only way item (3) can ship in the follow-up.
(Note: `Tautology` itself is defined in `Bool.lean`, so "tautology definitions" already arrive
with Bool.)

## 3. LOC Budgeting and Recommended Scope

Because the four files total 819 LOC, at most a subset fits under 500. Two coherent, clean,
under-budget packages exist. Both are sorry-free and depend only on #648 + Mathlib.

### Package A — Algebraic core + bridge (RECOMMENDED, satisfies items 1 & 2 literally)

| File | LOC |
|------|-----|
| Algebra.lean | 164 |
| Bool.lean | 190 |
| Algebra/Bridge.lean | 133 |
| **Total** | **487** ✅ under 500 |

Delivers the GHA/HA/BA algebraic evaluator (`AlgEvaluate` with `bot_val`), the bivalent
`Evaluate` and computable `BoolEvaluate`, and the actual `AlgEvaluate ↔ Evaluate/BoolEvaluate`
bridge that task item (2) asks for. Defers Kripke and SemanticConsequence. **This is the
cleanest option: comfortably under budget, all-clean deps, and it is the only package that
delivers the item-(2) bridge literally.**

### Package B — Evaluators + Kripke (satisfies items 1, 2-partial, 4)

| File | LOC |
|------|-----|
| Algebra.lean | 164 |
| Bool.lean | 190 |
| Kripke.lean | 170 |
| **Total** | **524** ⚠️ ~24 LOC over |

Delivers algebraic + bivalent/Boolean evaluators plus Kripke semantics (with `botForces` for
minimal logic, exactly as item 4 describes). At 524 LOC it is marginally over; landing under 500
requires trimming ~24+ LOC of docstring prose / blank lines (there is ample expository
docstring text to tighten without touching any proof). Does **not** include the AlgEvaluate
bridge (that would add Bridge.lean → 657 LOC) and defers SemanticConsequence.

### Why not include SemanticConsequence.lean

- In full form it imports non-upstream `ProofSystem/Derivation`, `Metalogic/DeductionTheorem`,
  and `NaturalDeduction/Equivalence` (Section 2) — it would force those whole layers into the PR.
- Even trimmed to its semantic half (~110 LOC), adding it to Package A (487) → ~597 or Package B
  (524) → ~634 blows the 500 budget.
- **Recommendation:** defer item (3) to a subsequent PR. If the maintainers specifically want
  semantic-consequence definitions now, the only viable route is to ship the **trimmed semantic
  half alone** in place of one of the larger files — e.g. `Algebra + Bool + trimmed-SemConseq`
  ≈ 164+190+110 = **464 LOC** — but this drops both the bridge and Kripke.

### Kripke fit verdict (item 4 asks explicitly)

Kripke.lean has **clean dependencies** and is self-contained (`KripkeModel` with `botForces`,
`IForces`, persistence, `IValid`/`MValid`, `mvalid_implies_ivalid`) — no proof-system
dependency, so its bare definitions ship fine. The only obstacle is the **budget**: it fits in
Package B (with light trimming) but not alongside the Bridge in Package A. **Recommendation:**
include Kripke only if the maintainers prefer Kripke over the AlgEvaluate bridge; otherwise
defer it to a third PR. It does not need to be stubbed — it is complete and independent.

## 4. State of the PR #648 Base

- PR #648 head = `origin/feat/propositional-v2`, contributing `Defs.lean` +
  `NaturalDeduction/{Basic,Theory}.lean` only (Section 2).
- The base uses the **Lean module system** (`module` / `public import`); all four candidate
  files also use `module` + `public import` + `@[expose] public section`, so they are
  module-system-consistent with the base. The follow-up branch must be cut from the #648 head so
  `Defs.lean` (primitive `bot`, `.imp`/`.and`/`.or`/`.atom`/`.bot` five-constructor type) matches.
- Local git history shows the stacking was reconciled (`task graph: reconcile #662/#648/#607
  stacking`, `force-push #648+#662`), and review comments on #648 were already addressed
  (`chore(Logics/Propositional): address review comments from PR #648`). Confirm #648 is still
  open/unmerged before cutting the branch; if it has merged to upstream `main`, stack on `main`
  instead.
- The `bot`-as-primitive design (vs Waring/Doty's `bot = atom ⊥`) is settled in #648's favor;
  the Zulip decision rationale (substitution-invariance / free-algebra argument) is recorded in
  `specs/400_reconcile_connectives_pr607/pr-response.md` and should inform the PR description.

## 5. CI Pipeline Verification

Ground truth is `.github/workflows/lean_action_ci.yml` (runs on every `pull_request`). The
**actual PR-blocking gates**, in order:

1. **`lake build`** via `leanprover/lean-action@v1` with **`build-args: "--wfail --iofail"`**.
   `--wfail` makes **all warnings fatal** — unused variables/section-variable warnings, deprecated
   lemmas, etc. will fail the build. This is stricter than a plain `lake build`.
2. **`lake test`** (`testDriver = "CslibTests"` in `lakefile.toml`), via lean-action `test-args`.
3. **`lake exe mk_all --check`** — **NOT named in the task, but PR-blocking.** New files must be
   registered in the aggregate `Cslib.lean` (currently a flat mk_all-generated import list;
   `Semantics/Algebra`, `Bridge`, etc. already appear at `Cslib.lean:532+`). Run
   `lake exe mk_all` on the branch so the aggregate matches exactly the files present, or this
   check fails. **This is the single most likely gate to trip and the task omits it.**
4. **`lake exe checkInitImports`** — verifies each file's `import Cslib.Init` init-import
   discipline. All four candidates already open with `import Cslib.Init`. ✅
5. **`leanprover-community/lint-style-action` (mode: check)** — the Mathlib **style** linter
   (copyright header, module docstring, ≤100-col lines, import ordering, trailing whitespace).
   Checked directly: **all four files have 0 lines over 100 cols**, and all have the copyright
   header + `/-! # … -/` module docstring. This is the task's "lake exe lint-style". ✅ expected pass.

**`lake shake` is currently COMMENTED OUT** in `lean_action_ci.yml` (lines 29–32) — it is
**not** a live PR gate right now, despite being named in the task. Still run it manually
(`lake shake --add-public --keep-implied --keep-prefix Cslib`) to catch transitively-unused
imports before submission, since maintainers may re-enable it. Given the clean, minimal import
lists of the candidate files, shake violations are unlikely.

**Environment linters (`lake lint` / `batteries/runLinter`: docBlame, simpNF, defLemma,
defsWithUnderscore, etc.) run only in `weekly-lints.yml` (cron), NOT on PR.** They are therefore
non-blocking for this PR, but worth pre-empting because the files are destined for a
lint-clean library:
- **docBlame**: every candidate `def`/`theorem`/`structure` already carries a docstring
  (verified via decl scan); the many `@[simp]` evaluation-equation lemmas (`Evaluate_atom`,
  `AlgEvaluate_imp`, `IForces_and`, …) are the only bare-named decls — confirm the repo's
  docBlame config exempts simp equation lemmas (existing CSLib practice suggests it does, since
  these files already live in the tree lint-clean).
- **simpNF**: the `@[simp]` equation lemmas are all `rfl`-shaped with the constructor on the LHS
  — standard and simpNF-safe.
- **Naming (defsWithUnderscore / dupNamespace)**: names like `BoolEvaluate_eq_iff`,
  `mvalid_implies_ivalid`, `setDeriv_deduction` mix camelCase with underscores; these already
  pass the local tree so the CSLib convention permits the `Thing_property` theorem-name shape.
  No `def` uses an underscore in a way that would trip `defsWithUnderscore`.

**Recommended pre-submission command sequence on the PR branch:**
```
lake exe mk_all                 # regenerate aggregate to include new files
lake build --wfail --iofail     # match CI strictness
lake test
lake exe checkInitImports
lake exe lint-style             # (or the lint-style-action locally)
lake shake --add-public --keep-implied --keep-prefix Cslib   # advisory; not a live gate
```

## 6. Zulip Thread Reference for the PR Description

The CSLib "Propositional Logic" coordination topic is on the **CSLib** Zulip channel (513188):

```
https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic
```

(Confirmed via `specs/archive/267_verify_zulip_propositional_logic_claims/reports/…` and
`specs/400_reconcile_connectives_pr607/pr-response.md`, which cite
`.../513188-CSLib/topic/Propositional.20Logic/near/604219492` and `.../near/605813681`.) The PR
description should link this topic, note the follow-up stacks on #648, and acknowledge the
Waring/Doty algebraic-semantics direction plus the settled `bot`-primitive decision.

## 7. Summary of Findings

- **Four target files total 819 LOC, all sorry-free** — the full set is ~64% over the <500 budget;
  a subset must be chosen. (Paths/LOC in §1.)
- **PR #648 contains only `Defs.lean` + `NaturalDeduction/{Basic,Theory}.lean`** — no Semantics,
  ProofSystem, or Metalogic. This fixes the dependency baseline. (§2.)
- **Algebra, Bool, Kripke, and Bridge.lean are all dependency-clean** (Defs + Mathlib only).
  **SemanticConsequence.lean is NOT** — it imports non-upstream `ProofSystem/Derivation`,
  `Metalogic/DeductionTheorem`, and `NaturalDeduction/Equivalence`. (§2, §2.1.)
- **Recommended PR = Package A: Algebra + Bool + Bridge = 487 LOC** — under budget, clean,
  sorry-free, and the only package that delivers the item-(2) AlgEvaluate bridge literally.
  Alternative Package B (Algebra + Bool + Kripke = 524, trim ~24 LOC) if Kripke is preferred
  over the bridge. (§3.)
- **Defer SemanticConsequence.lean** (item 3): full form needs the non-upstream Hilbert/metalogic
  layer; even its trimmed semantic-only half (~110 LOC) overflows the budget alongside the other
  files. **Defer Kripke** unless chosen for Package B. (§3.)
- **CI gate correction**: the task's list is right except (a) it omits **`lake exe mk_all --check`**,
  the most likely gate to trip (new files must be registered), and (b) **`lake shake` is currently
  commented out** in PR CI. `--wfail` makes warnings fatal. All four files already pass the
  line-length lint-style check (0 lines >100 cols). (§5.)
- **Zulip reference**: `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic`. (§6.)

## 8. Open Questions for Planning

1. **Package choice**: A (bridge, 487, recommended) vs B (Kripke, 524-with-trim)? They are
   mutually exclusive under budget; the two can't both fully fit.
2. **Is #648 still open?** Cut the follow-up branch from #648's head if open, else from `main`.
3. **Does the maintainer want item (3) at all now?** If yes, the only viable form is the trimmed
   semantic-consequence half (~110 LOC), replacing a larger file — which drops the bridge and Kripke.
4. **docBlame on `@[simp]` equation lemmas**: confirm the repo config exempts them (weekly lint,
   non-blocking, but worth settling before the file lands in a lint-clean namespace).
