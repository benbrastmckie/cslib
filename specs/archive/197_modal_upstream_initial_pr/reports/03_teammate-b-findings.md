# Teammate B Findings: Alternative Scoping Strategies for Modal/ Upstream PR

- **Task**: 197 -- Scope initial Modal/ upstream PR (~300 LOC)
- **Role**: Teammate B (Alternative Approaches)
- **Date**: 2026-06-14
- **Focus**: Local codebase analysis, import dependency mapping, alternative PR scoping options
- **Complements**: Teammate A (upstream PR review); does NOT duplicate that work

## Key Findings

### 1. Import Dependency Graph

The complete dependency graph for the local Modal/ directory:

```
Cslib.Foundations.Logic.Connectives           (126 LOC, NEW -- not in upstream)
    |
    v
Cslib.Logics.Modal.Basic                       (424 LOC local vs 277 upstream)
    |
    +---> Cslib.Logics.Modal.Denotation        (85 LOC local vs 53 upstream)
    |
    +---> Cslib.Logics.Modal.Cube              (141 LOC, UNCHANGED)
    |
    +---> Cslib.Logics.Modal.LogicalEquivalence  (84 LOC local vs 132 upstream)
    |
    +---> Cslib.Logics.Modal.FromPropositional    (165 LOC, NEW -- not in upstream)
    |
    +---> Cslib.Logics.Modal.Metalogic.DerivationTree  (218 LOC, NEW)
              |
              +---> ProofSystem/Instances/*.lean (13 files, ~112 LOC for K, smaller for others)
              |          |
              |          v
              +---> Metalogic/Soundness.lean (84 LOC)
              |           |
              +---> Metalogic/DeductionTheorem.lean
              |           |
              +---> Metalogic/MCS.lean
              |           |
              +---> Metalogic/Completeness.lean
              |           |
              +---> Metalogic/Systems/{K,T,D,S4,S5,...}/(Soundness|Completeness).lean
```

**Critical structural fact**: `Cslib.Foundations.Logic.Connectives` does NOT exist in upstream. `Basic.lean` imports it (line 10) and registers a `ModalConnectives` instance (lines 113-117). This is the single external dependency that does not resolve against upstream's module tree.

**Upstream path mismatch**: Local uses `Cslib.Foundations.Data.Relation`; upstream has `Cslib.Foundations.Relation.Euclidean`. The same `Relation.RightEuclidean`, `Relation.Serial` types exist in both, just at different paths. This is a mechanical fix, not a semantic issue.

### 2. Upstream vs Local File Status

| File | Upstream | Local | Change |
|------|---------|-------|--------|
| `Modal/Basic.lean` | 277 LOC (primitives: atom, not, and, diamond) | 424 LOC (primitives: atom, bot, imp, box) | +248/-101 |
| `Modal/Denotation.lean` | 53 LOC | 85 LOC | +43/-9 |
| `Modal/Cube.lean` | Same | Same | 0 changes |
| `Modal/LogicalEquivalence.lean` | 132 LOC (uses not/and/diamond constructors) | 84 LOC (uses impL/impR/box constructors) | +64/-112 |
| `Modal/FromPropositional.lean` | Does not exist | 165 LOC | New file |
| `Foundations/Logic/Connectives.lean` | Does not exist | 126 LOC | New file |
| `Modal/Metalogic/` + `ProofSystem/` | Does not exist | ~55 files | New subtrees |

### 3. What the Local LogicalEquivalence.lean Changed

The upstream `LogicalEquivalence.lean` (132 LOC) uses the `Cslib.Foundations.Logic.LogicalEquivalence` generic framework (contexts, congruence, `HasContext`) and defines `Context` constructors matching `{not, and, diamond}` primitives:
- `| not (c : Context Atom)`
- `| andL`, `| andR`
- `| diamond (c : Context Atom)`

The local version (84 LOC) replaces this with a self-contained approach matching `{imp, box}` primitives:
- `| impL (c : Context Atom) (φ : Proposition Atom)`
- `| impR (φ : Proposition Atom) (c : Context Atom)`
- `| box (c : Context Atom)`

The local version drops the dependency on `Cslib.Foundations.Logic.LogicalEquivalence` (and hence `Cslib.Foundations.Syntax.Context`, `Cslib.Foundations.Syntax.Congruence`). Instead it defines `LogicallyEquivalent` directly as a `def` and proves `congruence` as a standalone theorem. This is a meaningful simplification: 48 fewer net LOC, no external framework dependency.

### 4. Connectives.lean Dependency Is Real but Narrow

The entire dependency on `Connectives.lean` from `Basic.lean` reduces to exactly 3 lines:

```lean
-- Line 10 of Basic.lean
public import Cslib.Foundations.Logic.Connectives

-- Lines 113-117 of Basic.lean
/-- Register `Modal.Proposition` as an instance of `ModalConnectives`. -/
instance : ModalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
  box := .box
```

These 3 lines are the ONLY dependency on `Connectives.lean`. Everything else in Basic.lean -- the `Proposition` inductive, all `Satisfies` theorems, axiom validity theorems (K, T, B, 4, 5, D), `Judgement`, `theory`, `TheoryEq`, `valid`, `logic` -- compiles without `Connectives.lean`.

This means the dependency is cleanly isolatable: remove these 3 lines and Basic.lean has zero dependency on any non-upstream module.

### 5. PR #648 Context and Alternative Strategies

PR #647 (Propositional PR, which would have introduced `Connectives.lean` upstream) was CLOSED on 2026-06-14 without merge. This means `Connectives.lean` is not in upstream and the Modal PR cannot depend on it being there.

Three dependency resolution strategies exist:

**Strategy 1 (Stack)**: Re-submit PR #647, wait for merge, then submit Modal PR stacked on it. Requires PR #647 to be accepted first. Maximum architectural coherence.

**Strategy 2 (Bundle)**: Include a subset of `Connectives.lean` directly in the Modal PR -- specifically just `HasBot`, `HasImp`, `HasBox`, `ModalConnectives` (dropping `PropositionalConnectives`, `HasAnd`, `HasOr`, `HasUntil`, `HasSince`, `TemporalConnectives`, `BimodalConnectives`). Adds ~30 LOC from Connectives.lean to the PR but makes it self-contained.

**Strategy 3 (Defer)**: Remove the 3-line `ModalConnectives` registration from Basic.lean, submit purely the formula type refactoring without any typeclass hierarchy. Add the typeclass instance as a follow-up PR after `Connectives.lean` is accepted.

## Alternative Scoping Options

### Option A: Basic.lean + Denotation.lean (Prior Recommendation)

**Files**: `Basic.lean` (modified), `Denotation.lean` (modified)
**LOC**: +248 insertions / -101 deletions (Basic) + +43/-9 (Denotation) = **291 insertions total**
**Dependency**: Hard dependency on PR 198 (`Connectives.lean`) via 3 lines -- use Strategy 2 (Bundle ~30 LOC of `HasBox`/`HasBot`/`HasImp`/`ModalConnectives`) to make self-contained, or Strategy 3 (remove 3 lines, defer typeclass instance)
**Upstream impact**: `Cube.lean` unchanged (no breakage); `LogicalEquivalence.lean` will break (pattern match on removed constructors) -- must be noted in PR description

**Assessment**: This is the core change. Correctly scoped for a first PR. The `Cube.lean` safety (zero changes needed) is a strong practical argument. The key risk is breaking `LogicalEquivalence.lean` as a side effect, which means the PR either fixes it too (expanding scope) or documents the expected failure explicitly.

**LOC estimate (standalone, Strategy 3)**: 288 insertions / 101 deletions

### Option B: Basic.lean + Denotation.lean + LogicalEquivalence.lean (Expanded)

**Files**: `Basic.lean` (modified), `Denotation.lean` (modified), `LogicalEquivalence.lean` (modified)
**LOC**: 248+43+64 = **355 insertions** / 101+9+112 = **222 deletions**
**Dependency**: Same as Option A (only via ModalConnectives instance)
**Upstream impact**: All three modified files compile together; `Cube.lean` unchanged

**Assessment**: Exceeds 300 LOC target at 355 insertions. However, this is the COMPLETE set of upstream file changes -- nothing else in upstream is modified. Including `LogicalEquivalence.lean` has the key advantage that it PREVENTS the "expected failure" problem: after the PR, all upstream Modal files compile without error. The local `LogicalEquivalence.lean` is actually SHORTER than upstream (84 vs 132 LOC) and drops a dependency on `Cslib.Foundations.Logic.LogicalEquivalence` (a simplification).

**Counter-argument for inclusion**: The local `LogicalEquivalence.lean` is a COMPLETE REWRITE -- it changes both the context constructors AND removes the external framework dependency. This design decision (self-contained vs. using the `HasContext`/`Congruence` framework) may need separate review discussion. Including it risks derailing the formula type refactoring review into a framework debate.

**LOC estimate**: 355 insertions / 222 deletions (net -133, so the PR removes more than it adds when LogicalEquivalence is included)

### Option C: Basic.lean Only (Minimal)

**Files**: `Basic.lean` (modified, minus ModalConnectives lines)
**LOC**: ~244 insertions / 101 deletions
**Dependency**: None (Strategy 3 -- no Connectives.lean import)
**Upstream impact**: `Denotation.lean` will break (match on removed constructors), `LogicalEquivalence.lean` will break, `Cube.lean` unchanged

**Assessment**: Too disruptive for too little coherence. Removes the ability to demonstrate semantic correctness (no updated Denotation). The PR description would need to document 2 expected breakages rather than 1. Not recommended.

### Option D: Connectives.lean Subset + Basic.lean + Denotation.lean (Bundle Strategy)

**Files**: `Foundations/Logic/Connectives.lean` (new, subset), `Basic.lean` (modified), `Denotation.lean` (modified)
**LOC**: ~30 (Connectives subset) + 248 + 43 = **~321 insertions**
**Dependency**: Self-contained
**Upstream impact**: `Cube.lean` unchanged; `LogicalEquivalence.lean` breaks

**Assessment**: Slightly over 300 LOC target. The advantage is that the PR is completely self-contained AND includes the typeclass registration. The bundled `Connectives.lean` subset would contain only:
- `HasBot`, `HasImp`, `HasBox` (3 classes, ~15 LOC)
- `PropositionalConnectives`, `ModalConnectives` (2 bundled classes, ~10 LOC)
- No `HasAnd`, `HasOr`, `HasUntil`, `HasSince`, `TemporalConnectives`, `BimodalConnectives`

This is a viable approach if PR #647 cannot be re-submitted and the typeclass instance is architecturally important.

**LOC estimate**: ~321 insertions / 101 deletions

### Option E: Connectives.lean + Basic.lean + Denotation.lean + LogicalEquivalence.lean (Complete Bundle)

**Files**: `Connectives.lean` (new, subset), `Basic.lean`, `Denotation.lean`, `LogicalEquivalence.lean`
**LOC**: ~30 + 248 + 43 + 64 = **~385 insertions** / 222 deletions
**Dependency**: Self-contained
**Upstream impact**: All upstream Modal/ files compile correctly after PR

**Assessment**: Exceeds 300 LOC significantly. The benefit of a complete state (no broken files) does not outweigh the review scope. Not recommended for an initial PR.

## Recommended Approach

**Primary recommendation**: Option A (Basic.lean + Denotation.lean) with Strategy 3 (defer `ModalConnectives` instance).

**Rationale**:

1. **Minimizes surface area** for the initial PR: exactly 2 files modified, ~288 insertions
2. **Zero external dependencies**: removing 3 lines eliminates all dependency on the missing `Connectives.lean`
3. **Core value delivered**: the formula type refactoring (atom/bot/imp/box) and updated denotation are the central contribution; the typeclass registration is valuable but secondary
4. **One documented breakage**: `LogicalEquivalence.lean` will fail, but this is predictable, documentable, and fixed in the immediate follow-up PR
5. **`Cube.lean` still compiles**: proves the refactoring is structurally safe
6. **Clear follow-up path**: LogicalEquivalence.lean comes in PR 3; ModalConnectives instance comes either with Connectives.lean acceptance or bundled in a separate PR

**Alternative recommendation if typeclass hierarchy is essential**: Option D (Bundle strategy) at ~321 insertions. This is 7% over the 300 LOC target but makes the PR fully self-contained with the typeclass registration. The bundled subset of `Connectives.lean` (~5 classes, ~30 LOC) is a reasonable addition to avoid the "you need to accept another PR first" coordination problem.

**Decision point**: The choice between Strategy 3 and Strategy D hinges on whether the PR reviewer community considers the `ModalConnectives` instance essential to the PR's narrative or a follow-up concern. Given that PR #607 review showed active interest in typeclass organization, including it proactively (Option D) may strengthen the PR's reception -- but requires slightly more scope.

## Evidence and Examples

### Evidence 1: The 3-Line Dependency Boundary

Removing these lines from Basic.lean (lines 10 and 113-117) produces a version with zero dependency on non-upstream modules:

```lean
-- Remove line 10:
public import Cslib.Foundations.Logic.Connectives

-- Remove lines 113-117:
instance : ModalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
  box := .box
```

All remaining 419 lines of Basic.lean are independent of Connectives.lean.

### Evidence 2: LogicalEquivalence Compatibility Issue

Upstream `LogicalEquivalence.lean` uses `Context` constructors that match the UPSTREAM primitives:
```lean
-- Upstream constructors
| not (c : Context Atom)
| andL (c : Context Atom) (φ : Proposition Atom)
| andR (φ : Proposition Atom) (c : Context Atom)
| diamond (c : Context Atom)
```

After the formula type refactoring, `.not`, `.and`, `.diamond` constructors no longer exist on `Proposition`. Any PR that changes Basic.lean primitives MUST also update LogicalEquivalence.lean or it will fail to compile. This means Option A requires explicitly noting the expected downstream breakage.

### Evidence 3: Denotation.lean Coherence

The local Denotation.lean perfectly mirrors the new primitives:

```lean
-- Local (new)
| .bot => ∅
| .imp φ₁ φ₂ => (φ₁.denotation m)ᶜ ∪ φ₂.denotation m
| .box φ => {w | ∀ w', m.r w w' → w' ∈ φ.denotation m}
```

vs upstream:
```lean
-- Upstream
| .not φ => (φ.denotation m)^c
| .and φ1 φ2 => φ1.denotation m INTER φ2.denotation m
| .diamond φ => {w | ∃ w', m.r w w' ∧ w' ∈ φ.denotation m}
```

The `satisfies_mem_denotation` theorem in local Denotation.lean uses an induction proof (explicit) vs upstream's `grind`. This is self-contained and does not require any additional imports.

### Evidence 4: Cube.lean Independence

Cube.lean imports only `Cslib.Logics.Modal.Basic` and uses the `Proposition.valid` and `logic` definitions (which are unchanged between local and upstream in terms of their signatures). The only issue is that `Cube.lean`'s `grind` proofs use `Satisfies.*` theorems that may have name changes:

- Upstream: `Satisfies.iff_iff_iff` (removed in local)
- Local: `Satisfies.and_iff_and`, `Satisfies.diamond_iff_exists` (new)

However, examining `Cube.lean` shows it uses `Satisfies.k`, `Satisfies.t` -- both of which exist with the same signature in the local version. The `grind` calls in Cube.lean use `= setOf_true, = logic, = Proposition.valid` which are definition-level rewrites, unchanged. Cube.lean should compile unchanged after the formula type refactoring.

## LOC Summary Table

| Option | Files | Insertions | Deletions | Self-Contained | Expected Breakages |
|--------|-------|------------|-----------|----------------|-------------------|
| A (Recommended) | Basic + Denotation (no ModalConnectives) | ~288 | 101 | Yes | LogicalEquivalence |
| B (Expanded) | Basic + Denotation + LogicalEquivalence | 355 | 222 | Yes (if +ModalConnectives skipped) | None |
| C (Minimal) | Basic only | ~244 | 101 | Yes | Denotation + LogicalEquivalence |
| D (Bundle) | Connectives subset + Basic + Denotation | ~321 | 101 | Yes | LogicalEquivalence |
| E (Complete) | Connectives + Basic + Denotation + LogicalEquivalence | ~385 | 222 | Yes | None |

## Confidence Level

**High** on the import dependency graph (directly verified from source files and git diff).

**High** on the 3-line nature of the `Connectives.lean` dependency (read Basic.lean lines 10, 113-117 directly).

**High** on the LOC counts (git diff --stat verified; insertion counts verified with grep).

**High** on the LogicalEquivalence.lean breakage (upstream constructors vs local constructors directly compared).

**Medium** on Option D feasibility -- would need to verify that the bundled 30-LOC Connectives subset compiles correctly without the rest of the module and that `ModalConnectives` resolves properly from that subset alone.

**Medium** on Option B's 355 LOC assessment being acceptable -- the previous plan flagged 300 LOC as a target, but 355 may be acceptable given the net reduction (-133 lines from removing upstream code) and the benefit of leaving no broken files. This judgment call depends on upstream maintainer preferences.
