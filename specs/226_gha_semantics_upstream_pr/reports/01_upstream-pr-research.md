# Research Report: Cherry-Pick GHA Algebraic Semantics for Upstream PR

**Task**: 226 -- Cherry-pick GHA algebraic semantics from main to create a PR stacked on PR #648
**Session**: sess_1750123500_research226
**Date**: 2026-06-16

## 1. PR #648 Branch State

### 1.1 PR #648 Summary

- **Title**: `feat(Logics/Propositional): five-primitive formula type with primitive bot`
- **State**: OPEN
- **Base**: `main` (upstream leanprover/cslib)
- **Head**: `benbrastmckie/cslib:feat/propositional-v2`
- **Head SHA** (local): `7cc09612`
- **Stacked on**: Merged PR #536 (InferenceSystem-parameterized typeclasses)

### 1.2 PR #648 File Structure

PR #648 touches 6 files and adds NO semantics files (explicitly deferred):

| File | Change | Notes |
|------|--------|-------|
| `Cslib.lean` | MODIFIED | Adds `Cslib.Foundations.Logic.Connectives` import |
| `Cslib/Foundations/Logic/Connectives.lean` | ADDED | `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives` |
| `Cslib/Logics/Propositional/Defs.lean` | MODIFIED | 5-primitive `Proposition` with primitive `bot`; `imp` naming; typeclass instances |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | MODIFIED | `impI`/`impE` naming; explicit `Gamma` arguments |
| `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` | MODIFIED | `[Bot Atom]` removed; `instIsIntuitionisticIntuitionisticCompletion` added |
| `references.bib` | MODIFIED | Added `Avigad2022` entry |

**Critical**: PR #648 has NO `Semantics/` directory at all. The PR description says:
> "Semantics (`Basic.lean`, `Bool.lean`) deferred to a follow-up PR per thomaskwaring's request. The question of `Prop` vs `Bool` vs `GeneralizedHeytingAlgebra` for evaluation (raised by thomaskwaring and ctchou) will be addressed there."

### 1.3 PR #648 `IsIntuitionistic`/`IsClassical` Design

PR #648 uses the **InferenceSystem-parameterized** design (from merged #536):

```lean
class IsIntuitionistic (Atom : Type u) (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  efq (A : Proposition Atom) : S⇓(⊥ → A)

class IsClassical (Atom : Type u) (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  dne (A : Proposition Atom) : S⇓(¬¬A → A)
```

Main has **refactored** these to Theory-parameterized:

```lean
class IsIntuitionistic (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T

class IsClassical (T : Theory Atom) where
  dne (A : Proposition Atom) : (¬¬A → A) ∈ T
```

**Impact on Semantics**: The Algebra.lean and Soundness.lean files do NOT use `IsIntuitionistic` or `IsClassical` at all -- they work with `MinPropAxiom`/`IntPropAxiom`/`PropositionalAxiom` directly. Therefore this structural difference has NO impact on the cherry-pick.

### 1.4 PR #648 `Connectives.lean` vs Main `Connectives.lean`

PR #648's `Connectives.lean` is a **subset** of main's version:

| Feature | PR #648 | Main |
|---------|---------|------|
| `HasBot` | Yes | Yes |
| `HasImp` | Yes | Yes |
| `HasAnd` | Yes | Yes |
| `HasOr` | Yes | Yes |
| `PropositionalConnectives` | Yes | Yes |
| `HasBox` | No | Yes |
| `HasUntil` | No | Yes |
| `HasSince` | No | Yes |
| `HasNext` | No | Yes |
| `ModalConnectives` | No | Yes |
| `TemporalConnectives` | No | Yes |
| `BimodalConnectives` | No | Yes |

Main has extended `Connectives.lean` with modal/temporal classes. The PR #648 version is fine for the semantics follow-up since `Algebra.lean` only needs `PL.Proposition`, not the modal/temporal connectives.

## 2. Task 225 Commits to Cherry-Pick

### 2.1 Relevant Commits

Only one commit (`c50fca9a`) contains the substantive implementation changes:

```
c50fca9a task 225: complete implementation
```

This commit creates/modifies:

| File | Action | Relevance to Upstream PR |
|------|--------|--------------------------|
| `Cslib/Logics/Propositional/Semantics/Algebra.lean` | CREATED | **YES** -- core new file |
| `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean` | CREATED | **YES** -- core new file |
| `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` | CREATED | **YES** -- bridges to Bool.lean |
| `Cslib/Logics/Propositional/Semantics/Bool.lean` | MODIFIED | **YES** -- consolidated from Basic.lean |
| `Cslib/Logics/Propositional/Semantics/Basic.lean` | DELETED | **YES** -- absorbed into Bool.lean |
| `Cslib.lean` | MODIFIED | **YES** -- import updates |
| 5 downstream importers | MODIFIED | **DEPENDS** -- import path changes |
| `specs/` artifacts | MODIFIED | NO -- not for upstream |

The other task 225 commits (metadata, orchestration) are irrelevant to the cherry-pick.

### 2.2 Files NOT on PR #648

PR #648 has NO Semantics/ directory, so adding these files is purely additive. However, the PR #648 branch also lacks the following files that exist on main and that our Semantics files depend on:

**ProofSystem/ directory** (needed by Soundness.lean):
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- defines `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom`
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- defines `DerivationTree`, `Deriv`, `Derivable`

These files are NOT in PR #648. They exist only on our main branch.

**Implication**: We cannot just cherry-pick the Algebra/Soundness.lean files -- we also need the ProofSystem/ files or the Soundness.lean proof needs to be reimplemented against PR #648's `Theory.Derivation` infrastructure.

## 3. HasImp vs HasImpl Naming Conflict

### 3.1 PR #587 (thomaskwaring) -- `HasImpl` / `impl`

PR #587 ("feat(Foundations/Logic): Notation typeclasses and models") creates:

```lean
-- Cslib/Foundations/Logic/Connectives.lean
class HasImpl (alpha : Type*) where
  impl : alpha -> alpha -> alpha
```

Also introduces `HasAnd`, `HasOr`, `HasNot`, and a full `Model.lean` with `HasEntails`, `HasInterp`, `HasInterpEntails`, plus `HeytingModel` soundness sketches (with `sorry`s).

PR #587 uses `Proposition.impl` (the old constructor name, matching upstream pre-#648).

### 3.2 PR #607 (fmontesi) -- `HasImpl` / `impl`

PR #607 ("feat(Logic): logical operators") creates per-operator files:

```lean
-- Cslib/Foundations/Logic/Operators/Impl.lean
class HasImpl (alpha : Type*) where
  impl (a b : alpha) : alpha
```

Both PRs agree on `HasImpl` / `impl` naming.

### 3.3 PR #648 (ours) -- `HasImp` / `imp`

PR #648 renames the constructor from `impl` to `imp` and the typeclass from `HasImpl` to `HasImp`:

```lean
-- Cslib/Foundations/Logic/Connectives.lean  
class HasImp (F : Type*) where
  imp : F -> F -> F
```

PR #648 description explicitly notes:
> "Constructor naming uses `imp`/`impI`/`impE` (renamed from `impl`/`implI`/`implE` for consistency with FormalizedFormalLogic convention; open to reverting if reviewers prefer `impl`)"

### 3.4 Resolution Status

- No Zulip design thread decision has been found
- thomaskwaring (PR #587) and fmontesi (PR #607) both use `HasImpl` / `impl`
- Our PR #648 uses `HasImp` / `imp`
- PR #648 description says "open to reverting if reviewers prefer `impl`"

**Recommendation**: Since this PR stacks on #648, use `HasImp` / `imp` (matching #648). If reviewers of #648 request revert to `impl`, both PRs change together. If #587 or #607 merge first with `HasImpl`, a follow-up rename is needed -- but since both those PRs are still open, priority goes to consistency with the PR we are stacking on.

## 4. File Path and Import Adaptation Plan

### 4.1 What Exists on PR #648 vs What We Need

| Need | On PR #648 | On Main | Action |
|------|-----------|---------|--------|
| `Proposition` type with primitive `bot` | YES (Defs.lean) | YES | Use PR #648's |
| `HasImp` typeclass | YES (Connectives.lean) | YES | Use PR #648's |
| `ProofSystem/Axioms.lean` | NO | YES | Must add |
| `ProofSystem/Derivation.lean` | NO | YES | Must add |
| `Semantics/Bool.lean` | NO | YES | Must add |
| `Semantics/Algebra.lean` | NO | YES | Must add |
| `Semantics/Algebra/Soundness.lean` | NO | YES | Must add |
| `Semantics/Algebra/Bridge.lean` | NO | YES | Must add |

### 4.2 Import Chain Analysis

```
Algebra.lean imports:
  - Cslib.Init
  - Cslib.Logics.Propositional.Defs (on PR #648 -- OK)
  - Mathlib.Order.Heyting.Basic (Mathlib -- OK)
  - Mathlib.Order.BooleanAlgebra.Basic (Mathlib -- OK)

Soundness.lean imports:
  - Cslib.Init
  - Cslib.Logics.Propositional.Semantics.Algebra (new file)
  - Cslib.Logics.Propositional.ProofSystem.Derivation (NOT on PR #648!)
  - Cslib.Logics.Propositional.ProofSystem.Axioms (NOT on PR #648!)

Bridge.lean imports:
  - Cslib.Init
  - Cslib.Logics.Propositional.Semantics.Algebra (new file)
  - Cslib.Logics.Propositional.Semantics.Bool (new file)

Bool.lean imports:
  - Cslib.Logics.Propositional.Defs (on PR #648 -- OK)
```

### 4.3 ProofSystem/ Dependency Problem

The Soundness.lean file depends on `ProofSystem/Axioms.lean` and `ProofSystem/Derivation.lean`, which are substantial files (232 and 165 lines respectively). These define:

1. `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom` (axiom predicates)
2. `DerivationTree`, `Deriv`, `Derivable` (Hilbert-style proof trees)
3. Subsumption theorems between axiom levels
4. `propDerivationSystem` (generic MCS integration)

**Options**:
- **Option A**: Include ProofSystem/ files in the same PR -- makes it a larger PR but self-contained
- **Option B**: Create a separate ProofSystem PR first, then stack the Semantics PR on top of that
- **Option C**: Refactor Soundness.lean to work against PR #648's existing `Theory.Derivation` instead of `DerivationTree`

**Recommendation**: Option A -- include ProofSystem/ in the same PR. The ProofSystem/ files are clean, self-contained, and already pass CI on main. They provide the Hilbert-style axiom hierarchy that is a natural complement to the ND-style `Theory.Derivation`. The PR description can frame this as "Layer 2 proof system + algebraic semantics follow-up."

However, an alternative framing is Option B -- stack as THREE PRs:
1. PR #648 (already open): Primitive bot + connective typeclasses + ND
2. New PR stacked on #648: ProofSystem/ (Hilbert-style axiom hierarchy + derivation trees)
3. New PR stacked on #2: Semantics/ (Bool.lean + Algebra.lean + Soundness.lean + Bridge.lean)

This is cleaner for review but more coordination overhead.

### 4.4 Downstream Import Changes

On main, these files import `Semantics.Basic` (which is being absorbed into `Semantics.Bool`):

| File | Import Change Needed |
|------|---------------------|
| `Modal/FromPropositional.lean` | `Semantics.Basic` -> `Semantics.Bool` |
| `Temporal/ConservativeExtension.lean` | `Semantics.Basic` -> `Semantics.Bool` |
| `Metalogic/Soundness.lean` | `Semantics.Basic` -> `Semantics.Bool` |
| `Metalogic/StrongCompleteness.lean` | `Semantics.Basic` -> `Semantics.Bool` |
| `Semantics/SemanticConsequence.lean` | `Semantics.Basic` -> `Semantics.Bool` |

**On PR #648 branch**: None of these files exist in PR #648's diff. The Modal/Temporal files exist on upstream main but do NOT reference any Semantics files (since Semantics was removed from PR #648). So for the stacked PR, we only need to handle new files, not downstream import updates.

### 4.5 Constructor Name Compatibility

PR #648 uses `imp` (not `impl`). Our files on main already use `imp`. No constructor rename needed.

PR #648 uses `.imp a b` / `.and a b` / `.or a b` / `.bot` / `.atom x` -- exact same as main. Our Algebra.lean pattern-matches on these exact constructors. No adaptation needed.

## 5. Potential Merge Conflicts

### 5.1 With PR #648 (Base)

No merge conflicts expected. PR #648 does not touch any Semantics/ files, and our new files are purely additive.

### 5.2 With PR #587 (thomaskwaring)

**File conflict**: `Cslib/Foundations/Logic/Connectives.lean` -- both PRs create this file with different content. However, since we are stacking on #648 which already has Connectives.lean, and our stacked PR does not modify Connectives.lean, there is no conflict from our PR specifically. The conflict is between #648 and #587.

**Semantic conflict**: PR #587 defines `HeytingModel` and `HasInterpEntails` with algebraic semantics sketches (with `sorry`). Our Algebra.lean takes a different approach (standalone `AlgEvaluate` function, not bundled into a typeclass). These are complementary, not conflicting -- our `AlgEvaluate` could be instantiated as a `HasInterp.interp` for thomaskwaring's framework.

### 5.3 With PR #607 (fmontesi)

**File conflict**: Creates `Operators/Impl.lean` etc. separate from `Connectives.lean`. Our PR doesn't touch these. No conflict.

**Naming conflict**: Uses `HasImpl` vs our `HasImp`. This is already a known conflict between #607 and #648; our stacked PR inherits #648's choice.

## 6. thomaskwaring's GHA Proposal Context

From PR #587's `Model.lean`, thomaskwaring sketched:

```lean
structure HeytingModel (Atom : Type*) where
  H : Type*
  [inst : GeneralizedHeytingAlgebra H]
  v : Atom -> H

instance : HasInterpEntails (HeytingModel Atom) (Proposition Atom) where
  Ground M := M.H
  interp := HeytingModel.interp
  filter _ := {top}

theorem HeytingModel.sound [DecidableEq Atom] {T : Theory Atom} :
    SoundFor (HeytingModel Atom) (Proposition Atom) T {M | forall A in T, interp M A = top} :=
  sorry -- i have this in a branch
```

Our `AlgEvaluate` is essentially `HeytingModel.interp` but:
1. Unbundled (standalone function, not a typeclass method)
2. Parameterized by `bot_val : H` (since GHA lacks `bot`)
3. Soundness proven for all 3 axiom tiers (not just one sorry)

The `bot_val` parameter is the key design contribution that thomaskwaring raised as important.

**PR description should reference**: thomaskwaring's observation that `bot_val` needs to be explicit in GHA, and that at the HA/BA level `bot_val = bot` is canonical.

## 7. Implementation Plan

### 7.1 Recommended Approach

**Branch strategy**: Create a new branch from `origin/feat/propositional-v2` (the PR #648 head).

**File additions** (in dependency order):
1. `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- Hilbert-style proof trees
2. `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- 3-tier axiom hierarchy
3. `Cslib/Logics/Propositional/Semantics/Bool.lean` -- consolidated Prop+Bool evaluators
4. `Cslib/Logics/Propositional/Semantics/Algebra.lean` -- GHA evaluator + validity predicates
5. `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean` -- 3-tier soundness proofs
6. `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` -- prop/bool bridge lemmas
7. `Cslib.lean` -- add import lines
8. `references.bib` -- add any new references if needed

### 7.2 Adaptation Needed

**Minimal adaptation expected**. The key files (`Algebra.lean`, `Soundness.lean`, `Bridge.lean`, `Bool.lean`) work against `PL.Proposition Atom` constructors `.atom`, `.bot`, `.imp`, `.and`, `.or` -- which are identical between PR #648 and main.

The only adaptation needed:

1. **Derivation.lean**: Uses `PL.Proposition` constructor `.imp` in `modus_ponens`. On PR #648 the constructor is `.imp` (same). No change needed.

2. **Axioms.lean**: Uses `.imp`, `.and`, `.or`, `.bot` constructors. All match PR #648. No change needed.

3. **Bool.lean**: Main's version has `import Cslib.Init` at top. PR #648 has no Basic.lean, so no conflict. The consolidated Bool.lean should import `Cslib.Logics.Propositional.Defs` (same as main).

4. **ProofSystem/Derivation.lean**: Imports `Cslib.Logics.Propositional.Defs` and `Cslib.Foundations.Logic.Metalogic.Consistency`. The latter does NOT exist on PR #648's upstream base.

### 7.3 Metalogic Dependency Problem

`ProofSystem/Derivation.lean` imports `Cslib.Foundations.Logic.Metalogic.Consistency` for the `Metalogic.DerivationSystem` instance (`propDerivationSystem`). This file is a main-only addition.

**Options**:
- **Option A**: Also include the Metalogic/ framework files (Consistency.lean, etc.) -- makes PR very large
- **Option B**: Remove the `propDerivationSystem` definition from the upstream version of Derivation.lean, since Soundness.lean doesn't use it. Keep it as a main-only addition.
- **Option C**: Split Derivation.lean: basic `DerivationTree` definition (no Metalogic import) + separate Instances.lean (with Metalogic integration)

**Recommendation**: Option B. The `propDerivationSystem` at the bottom of Derivation.lean is not used by Algebra/Soundness.lean. Remove it from the upstream version to avoid pulling in the entire Metalogic framework. The Soundness.lean file uses `DerivationTree` directly, not via `DerivationSystem`.

### 7.4 Simplified Dependency Chain for Upstream PR

After removing the Metalogic dependency:

```
Defs.lean (PR #648)
  |
  +-- ProofSystem/Axioms.lean (new)  -- MinPropAxiom, IntPropAxiom, PropositionalAxiom
  |
  +-- ProofSystem/Derivation.lean (new, simplified)  -- DerivationTree, Deriv, Derivable
  |
  +-- Semantics/Bool.lean (new)  -- Valuation, Evaluate, BoolValuation, BoolEvaluate
  |
  +-- Semantics/Algebra.lean (new)  -- AlgEvaluate, GHAValid, HAValid, BAValid
       |
       +-- Semantics/Algebra/Soundness.lean (new)  -- 3-tier soundness
       |
       +-- Semantics/Algebra/Bridge.lean (new)  -- propEvaluateEq, boolEvaluateEq
```

### 7.5 Estimated Effort

| Phase | Files | Lines | Effort |
|-------|-------|-------|--------|
| Create branch from #648 | 0 | 0 | 5 min |
| Add ProofSystem/Axioms.lean (trimmed) | 1 | ~180 | Copy + verify |
| Add ProofSystem/Derivation.lean (trimmed) | 1 | ~130 | Copy + trim Metalogic |
| Add Semantics/Bool.lean | 1 | ~150 | Copy |
| Add Semantics/Algebra.lean | 1 | ~117 | Copy |
| Add Semantics/Algebra/Soundness.lean | 1 | ~264 | Copy |
| Add Semantics/Algebra/Bridge.lean | 1 | ~84 | Copy |
| Update Cslib.lean | 1 | ~10 | Add imports |
| CI verification | 0 | 0 | Run full CI pipeline |
| Write PR description | 0 | 0 | Reference thomaskwaring |

Total: ~935 new lines across 7 files.

## 8. PR Description Outline

### Title

`feat(Logics/Propositional): algebraic semantics and Hilbert axiom system`

### Content Points

1. Follow-up to PR #648, adding the deferred semantics
2. **Hilbert axiom system** (ProofSystem/): 3-tier axiom hierarchy (Minimal/Intuitionistic/Classical) with derivation trees, complementing #648's natural deduction system
3. **Boolean and Prop-valued evaluators** (Bool.lean): bivalent `Evaluate`, computable `BoolEvaluate`, and bridge lemma `BoolEvaluate_eq_iff`
4. **Algebraic semantics** (Algebra.lean): generic `AlgEvaluate` parameterized over `GeneralizedHeytingAlgebra H` with explicit `bot_val : H` parameter
5. **3-tier soundness** (Soundness.lean): `MinPropAxiom` sound in all GHAs, `IntPropAxiom` sound in all HAs, `PropositionalAxiom` sound in all BAs
6. **Bridge lemmas** (Bridge.lean): `propEvaluateEq` and `boolEvaluateEq` showing existing evaluators as special cases of `AlgEvaluate`
7. **Design note on `bot_val`**: Following thomaskwaring's observation from PR #587 that GHA lacks a bottom element -- `AlgEvaluate` takes `bot_val : H` as an explicit parameter. At the HA/BA levels, `bot_val = bot` is the canonical choice.
8. Zero sorries in all new files

### Coordination Notes

- **PR #587** (thomaskwaring): Our `AlgEvaluate` implements what PR #587 sketched as `HeytingModel.interp` but unbundled. Compatible with PR #587's `HasEntails`/`HasInterpEntails` framework when that merges.
- **PR #607** (fmontesi): Inherits #648's `HasImp`/`imp` naming. If #607's `HasImpl`/`impl` is preferred, both #648 and this PR would need a coordinated rename.

## 9. Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| ProofSystem/ files too large for reviewer appetite | Medium | Can split into separate PRs if requested |
| HasImp/HasImpl naming bikeshed blocks PR | Low | Already noted as "open to reverting" in #648 |
| Metalogic framework dependency creep | Medium | Trim `propDerivationSystem` from upstream version |
| PR #587 merges first, conflicts with Connectives.lean | Low | Conflict is with #648, not our stacked PR |
| PR #648 itself requires revisions | Medium | Our PR must track #648 revisions |
| Upstream main advances, requiring rebase | Low | Standard rebase workflow |

## 10. Key Findings Summary

1. **PR #648 has no Semantics/ files** -- our additions are purely additive, no merge conflicts.
2. **Constructor naming matches** -- both PR #648 and main use `.imp`, `.bot`, `.and`, `.or`, `.atom`.
3. **Soundness.lean needs ProofSystem/** -- must include Axioms.lean and (trimmed) Derivation.lean.
4. **Derivation.lean needs trimming** -- remove `propDerivationSystem` to avoid Metalogic dependency.
5. **HasImp/HasImpl is a known open question** -- our PR inherits #648's `HasImp` choice.
6. **IsIntuitionistic/IsClassical refactoring is irrelevant** -- Algebra/Soundness use axiom predicates directly.
7. **PR #587's GHA sketch** is complementary -- our `AlgEvaluate` implements what thomaskwaring sketched with `sorry`.
