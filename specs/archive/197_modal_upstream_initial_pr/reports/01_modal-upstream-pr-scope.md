# Research Report: Modal/ Upstream PR Scope (~300 LOC)

**Task**: 197 -- Scope initial Modal/ upstream PR
**Session**: sess_1781469976_273d9b
**Date**: 2026-06-14

## 1. Executive Summary

The local Modal/ directory has undergone a complete formula type refactoring from
`{atom, not, and, diamond}` primitives to `{atom, bot, imp, box}` primitives, affecting
every file. The total diff against upstream is ~355 insertions / ~222 deletions (577 churn
lines) across 3 modified files, plus 2 new files. This exceeds the ~300 LOC target for a
single PR.

**Recommendation**: Submit `Basic.lean` + `Denotation.lean` as the initial Modal PR. This
covers the formula type refactoring (the essential breaking change) plus the updated
denotational semantics, totaling ~290 insertions. `LogicalEquivalence.lean` and
`FromPropositional.lean` should follow in subsequent PRs.

## 2. Dependency Analysis

### 2.1 What Depends on PR 198 (Connectives.lean)

The local `Basic.lean` line 10 imports `Cslib.Foundations.Logic.Connectives` and line 114
registers the `ModalConnectives` instance:

```lean
instance : ModalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
  box := .box
```

**This creates a hard dependency on PR 198**: `Connectives.lean` defines `ModalConnectives`,
`HasBot`, `HasImp`, and `HasBox`. Without PR 198, this import and instance do not compile.

### 2.2 What Is Independent of PR 198

Everything else in the Modal PR is independent:

- The `Proposition` inductive type refactoring (atom/bot/imp/box constructors)
- All derived connectives (neg, top, or, and, diamond, iff as `abbrev`s)
- The `Bot` instance (`instance : Bot (Proposition Atom) := ...`)
- The `Satisfies` definition and all satisfaction theorems
- All axiom validity theorems (K, T, B, 4, 5, D and their converses)
- The `Judgement`, `theory`, `TheoryEq` infrastructure
- `Denotation.lean` (imports only `Modal.Basic`)
- `Cube.lean` (imports only `Modal.Basic`, currently identical to upstream)

### 2.3 Can ModalConnectives Be Registered Without Connectives.lean?

No. The `ModalConnectives` class is defined in `Connectives.lean`. Two options:

1. **Depend on PR 198** (recommended): Include `Connectives.lean` import and
   `ModalConnectives` instance. This is the architecturally correct approach since the
   typeclass hierarchy is the whole point.

2. **Defer the instance**: Submit the formula type refactoring without the
   `ModalConnectives` instance. Add it in a follow-up PR after 198 merges. This achieves
   maximum independence but loses the typeclass registration that motivates the
   refactoring.

**Recommendation**: Depend on PR 198. The Modal PR should be submitted after (or stacked on)
the Propositional PR. The dependency is small (one import, one instance) and the typeclass
registration is a key selling point.

### 2.4 Interaction with PR #607 (fmontesi's Operator Typeclasses)

PR #607 introduces per-operator typeclass files under `Operators/` with classes like
`HasAnd`, `HasOr`, `HasImpl`, `HasNot`, `HasBox`, `HasDiamond`, `HasIff`. It also modifies
`Modal/Basic.lean` to register instances of these classes.

**Key differences from our approach**:

| Aspect | PR #607 | Our PR 198 + this PR |
|--------|---------|---------------------|
| Primitives | Keeps `{atom, not, and, diamond}` | Changes to `{atom, bot, imp, box}` |
| Naming | `HasImpl` (uses `impl`) | `HasImp` (uses `imp`) |
| Has-classes | Per-file: `Operators/And.lean`, etc. | Single file: `Connectives.lean` |
| Bundled classes | None | `PropositionalConnectives`, `ModalConnectives` |
| `HasBot` | Not included | Included (critical for `bot` primitive) |
| `HasDiamond` | Included (diamond is primitive) | Not included (diamond is derived) |
| Negation | `HasNot` (neg is primitive) | None (neg is derived from `imp`+`bot`) |

**Coordination strategy**: These PRs are structurally incompatible because they disagree on
which operators are primitive. If PR #607 merges first, our PR must refactor away from those
primitives. If ours merges first, PR #607 must adapt. The most productive path is to discuss
on the Zulip thread to align on primitives before either merges.

**Risk**: PR #607 has been open since 2026-05-29 and modifies the same files. A merge
conflict is inevitable. Early communication with @fmontesi is essential.

## 3. Breaking Changes Analysis

### 3.1 Formula Type Refactoring (MAJOR)

The `Proposition` inductive changes from:

```lean
-- UPSTREAM
| atom | not | and | diamond   -- 4 constructors
```

to:

```lean
-- LOCAL
| atom | bot | imp | box       -- 4 constructors
```

This is a **complete breaking change** for any downstream code that pattern-matches on
`Proposition`. Every `| .not`, `| .and`, `| .diamond` match becomes invalid.

**Affected upstream files**:
- `Denotation.lean`: 4 match cases change (not->imp with complement union, and->imp with bot fallthrough, diamond->box)
- `LogicalEquivalence.lean`: Context constructors completely change
- `Cube.lean`: No pattern matching, no changes needed

### 3.2 Import Path Change

| Upstream | Local |
|----------|-------|
| `Cslib.Foundations.Relation.Euclidean` | `Cslib.Foundations.Data.Relation` |

The local codebase has consolidated the Relation modules into `Cslib.Foundations.Data.Relation`.
This is a separate refactoring that the Modal PR should NOT include. Instead, the Modal PR
should keep the upstream import path `Cslib.Foundations.Relation.Euclidean`.

**Action**: When preparing the PR branch, revert the import to
`Cslib.Foundations.Relation.Euclidean` and verify that `Relation.RightEuclidean` and
`Relation.Serial` resolve correctly from upstream's module structure.

### 3.3 New Import: Connectives.lean

The PR adds `public import Cslib.Foundations.Logic.Connectives` (from PR 198). This is the
only new CSLib import; all Mathlib imports remain unchanged.

### 3.4 Derived Connective API Changes

| Upstream | Local | Change |
|----------|-------|--------|
| `Proposition.not` (constructor) | `Proposition.neg` (abbrev) | Renamed + derived |
| `Proposition.and` (constructor) | `Proposition.and` (abbrev) | Same name, now derived |
| `Proposition.diamond` (constructor) | `Proposition.diamond` (abbrev) | Same name, now derived |
| `Proposition.impl` (def) | `Proposition.imp` (constructor) | Renamed + now primitive |
| `Proposition.box` (def) | `Proposition.box` (constructor) | Now primitive |
| (none) | `Proposition.bot` (constructor) | New primitive |
| (none) | `Proposition.top` (abbrev) | New derived |
| (none) | `Proposition.neg` (abbrev) | New derived |

### 3.5 Notation Changes

The notation symbols are identical (`¬`, `∧`, `∨`, `→`, `□`, `◇`, `↔`), but they now
bind to different definitions. The `neg_satisfies` theorem is renamed from `not_satisfies`
in upstream.

### 3.6 Theorem Removals

- `Satisfies.iff_iff_iff` is removed. The biconditional characterization is subsumed by
  `Satisfies.and_iff` + `Satisfies.impl_iff_impl`. (Our `iff` is defined as `and` of two
  `imp`s, so no separate characterization theorem is needed.)

### 3.7 New Theorems (not in upstream)

- `Satisfies.neg_iff` -- unbundled negation satisfaction
- `Satisfies.diamond_iff` -- unbundled diamond satisfaction (with existential)
- `Satisfies.and_iff` -- unbundled conjunction satisfaction
- `Satisfies.or_iff` -- unbundled disjunction satisfaction
- `Satisfies.diamond_iff_exists` -- bundled diamond satisfaction
- `Satisfies.and_iff_and` -- bundled conjunction satisfaction

These theorems are essential because `neg`, `and`, `or`, `diamond` are no longer primitives
in the inductive type, so their semantic behavior must be proved as lemmas.

## 4. Recommended PR Scope

### Option A: Basic.lean + Denotation.lean (RECOMMENDED)

**Files**:

| File | Status | Insertions | Deletions | Net |
|------|--------|------------|-----------|-----|
| `Basic.lean` | Modified | 248 | 101 | +147 |
| `Denotation.lean` | Modified | 43 | 9 | +34 |
| **Total** | | **291** | **110** | **+181** |

**Why this scope**:

1. **~290 insertions** fits the ~300 LOC target
2. `Denotation.lean` depends only on `Basic.lean` (no additional dependencies)
3. The formula type refactoring is the essential breaking change; including
   `Denotation.lean` ensures the denotational semantics compiles with the new constructors
4. `Cube.lean` has zero changes -- it can stay as-is with no action needed
5. `LogicalEquivalence.lean` is a complete rewrite (self-contained vs upstream's
   `Foundations.Logic.LogicalEquivalence` import) and is better as a separate PR
6. `FromPropositional.lean` is new and depends on `Propositional.Defs` -- cannot be
   independent of PR 198

**Dependency on PR 198**: Yes, for the `Connectives.lean` import and `ModalConnectives`
instance (3 lines of code). This is acceptable; the PR should be submitted as PR 2 in
the contribution roadmap, stacked on PR 198.

### Option B: Basic.lean Only (Maximum Independence)

**Files**:

| File | Status | Insertions | Deletions | Net |
|------|--------|------------|-----------|-----|
| `Basic.lean` (minus ModalConnectives) | Modified | ~244 | 101 | +143 |

Remove the `Connectives.lean` import and `ModalConnectives` instance to eliminate all
dependency on PR 198. This makes the PR fully independent but loses the typeclass
registration that motivates the refactoring series.

**Not recommended** because the typeclass hierarchy is a key design contribution. Without
it, the PR is "just" a primitive-set change with no polymorphic payoff.

### Option C: All Three Modified Files

**Files**:

| File | Status | Insertions | Deletions | Net |
|------|--------|------------|-----------|-----|
| `Basic.lean` | Modified | 248 | 101 | +147 |
| `Denotation.lean` | Modified | 43 | 9 | +34 |
| `LogicalEquivalence.lean` | Modified | 64 | 112 | -48 |
| **Total** | | **355** | **222** | **+133** |

This is 355 insertions (above 300 target) and includes a complete rewrite of
`LogicalEquivalence.lean` that removes the `Foundations.Logic.LogicalEquivalence` dependency
in favor of a self-contained approach. This is a design decision that may require separate
review discussion. **Not recommended for the initial PR** -- save for PR 3.

## 5. PR Description Draft

**Title**: `feat(Logics/Modal): refactor to {atom, bot, imp, box} primitives with derived connectives`

**Body**:

```markdown
## Summary

This PR refactors `Modal.Proposition` to use `{atom, bot, imp, box}` as primitive
constructors, replacing the current `{atom, not, and, diamond}`. Negation, conjunction,
disjunction, and diamond become derived connectives via classical encodings. The denotational
semantics in `Denotation.lean` is updated to match.

This follows the convention established by PR #NNN (Propositional five-primitive formula
type), where `bot` and `imp` are primitive and negation is derived as `neg phi := imp phi bot`.

Key changes:
1. **Formula type**: `Proposition` primitives changed from `{atom, not, and, diamond}`
   to `{atom, bot, imp, box}`
2. **Derived connectives**: `neg`, `top`, `and`, `or`, `diamond`, `iff` defined as
   `abbrev`s using Lukasiewicz convention
3. **Satisfaction lemmas**: New theorems `neg_iff`, `diamond_iff`, `and_iff`, `or_iff`
   characterize derived connectives semantically
4. **ModalConnectives instance**: Registers `Modal.Proposition` in the typeclass hierarchy
5. **Denotation update**: `Proposition.denotation` match cases updated for new constructors

## Design Rationale

### Why `{atom, bot, imp, box}` instead of `{atom, not, and, diamond}`?

Box (necessity) is the canonical primitive modal operator in classical systems
([Blackburn2001] Ch. 1, [ChagrovZakharyaschev1997] S. 1.1). It corresponds to universal
quantification over accessible worlds, preserves conjunction, distributes over implication
(axiom K), and is the subject of necessitation.

The `{bot, imp}` pair is standard in formalizations of propositional and modal logic
([Bentzen2023], [Trufas2024], [Johansson1937]). Making `bot` primitive avoids the
`[Bot Atom]` constraint pattern and ensures substitution preserves falsum by construction.

### Proof style

Satisfaction theorems use explicit term-mode proofs rather than `grind`, following the
convention that core semantic lemmas should be human-readable and tactic-independent.
The axiom validity theorems (K, T, B, 4, 5, D) use lightweight tactic proofs with explicit
structure.

## Relationship to Other PRs

- **Depends on PR #NNN** (Propositional): Uses `Connectives.lean` for `ModalConnectives`
  typeclass
- **Coordinates with PR #607** (@fmontesi): Both PRs modify `Modal/Basic.lean`. Our PR
  changes the primitive constructor set; PR #607 adds operator typeclass instances for the
  existing primitives. These are structurally incompatible and need alignment on the Zulip
  thread before merging.
- **Independent of PR #536** (@thomaskwaring): Propositional inference system refactoring
  does not touch Modal files.
- **Independent of PR #587** (@thomaskwaring): Semantic typeclasses operate at a different
  layer.

## Breaking Changes

- `Proposition.not` -> `Proposition.neg` (now derived, was primitive)
- `Proposition.and` -> still named `.and` but now derived (was primitive)
- `Proposition.diamond` -> still named `.diamond` but now derived (was primitive)
- `Proposition.impl` -> `Proposition.imp` (now primitive, was derived)
- `Proposition.box` -> now primitive (was derived)
- New primitive: `Proposition.bot`
- `not_satisfies` -> `neg_satisfies`
- `Satisfies.iff_iff_iff` removed (subsumed by `and_iff` + `impl_iff_impl`)
- Import: `Cslib.Foundations.Relation.Euclidean` unchanged;
  adds `Cslib.Foundations.Logic.Connectives`

## Changed Files

- `Cslib/Logics/Modal/Basic.lean` -- refactored formula type, derived connectives,
  satisfaction lemmas, axiom validity proofs, ModalConnectives instance
- `Cslib/Logics/Modal/Denotation.lean` -- updated denotation match cases for new constructors

## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used
for research, diff analysis, and PR description drafting. The mathematical content, proof
architecture, and design decisions were verified by the author.
```

## 6. Contribution Roadmap (Modal PRs)

| PR | Title | Files | Depends On | LOC Est. |
|----|-------|-------|------------|----------|
| **PR 2** (this) | Formula type refactoring + denotation | `Basic.lean`, `Denotation.lean` | PR 198 (Connectives) | ~290 |
| **PR 3** | Self-contained LogicalEquivalence | `LogicalEquivalence.lean` | PR 2 | ~85 |
| **PR 4** | PL-to-Modal embedding | `FromPropositional.lean` | PR 2 + PR 198 | ~165 |
| **PR 5** | Hilbert proof system (K) | `ProofSystem/Instances/K.lean` + infrastructure | PR 2 | ~300 |
| **PR 6** | Proof system instances (T, D, S4, S5, ...) | `ProofSystem/Instances/*.lean` | PR 5 | ~400 |
| **PR 7** | Soundness infrastructure | `Metalogic/Soundness.lean` + per-system | PR 5 | ~300 |
| **PR 8** | Deduction theorem + MCS | `Metalogic/DeductionTheorem.lean`, `MCS.lean` | PR 5 | ~400 |
| **PR 9** | Completeness (K) | `Metalogic/Completeness.lean`, `Systems/K/` | PR 7 + PR 8 | ~500 |
| **PR 10+** | Completeness (other systems) | `Systems/{T,D,S4,...}/` | PR 9 | ~200/ea |

Note: `Cube.lean` requires no PR -- it is identical between local and upstream.

## 7. Risk Assessment

### 7.1 PR #607 Conflict (HIGH RISK)

PR #607 by @fmontesi modifies the same file (`Modal/Basic.lean`) with a structurally
incompatible approach. Both PRs change the relationship between primitive and derived
operators.

**Mitigation**: Open a Zulip discussion BEFORE submitting the PR. Key points to align:
- Primitive set: `{atom, not, and, diamond}` vs `{atom, bot, imp, box}`
- Naming: `HasImpl`/`impl` vs `HasImp`/`imp`
- Architecture: per-file Operators/ vs single-file Connectives.lean
- Whether `HasBot` should be included (PR #607 omits it)

### 7.2 Upstream Relation Module Path (MEDIUM RISK)

Local uses `Cslib.Foundations.Data.Relation` which does not exist upstream. The PR must use
`Cslib.Foundations.Relation.Euclidean` (upstream path). Both provide `Relation.RightEuclidean`
and `Relation.Serial`, so the switch is safe, but it must be verified on the PR branch.

**Mitigation**: Create PR branch from upstream/main, cherry-pick or manually apply changes,
verify `lake build Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Denotation` compiles.

### 7.3 Proof Style Divergence (LOW RISK)

Upstream uses `grind` extensively in proofs (e.g., `by grind` for axiom T, B, 4, 5, D
converses). Local uses explicit term-mode or lightweight tactic proofs. Reviewers may
prefer one style. The explicit style is more robust against `grind` regressions but
less concise.

**Mitigation**: Include a note in the PR description about proof style rationale. Offer to
switch to `grind` if reviewers prefer it. The explicit proofs have value as documentation
of the proof structure.

### 7.4 `derivation_def` Attribute Change (LOW RISK)

Upstream uses `@[scoped grind =_]` on `derivation_def`; local uses `@[scoped grind =]`.
The `=_` vs `=` distinction affects grind's rewriting direction. Must verify this does not
break downstream proofs in `Cube.lean`.

### 7.5 DecidableEq Deriving (LOW RISK)

The local `Proposition` adds `deriving DecidableEq, BEq` which upstream lacks. This is
needed for the proof system infrastructure (decidable equality on formulas). It should
compile without issues but adds a dependency on Lean's `DecidableEq` deriving handler.

## 8. Technical Verification Checklist

Before submitting the PR:

- [ ] Create branch from `upstream/main`
- [ ] Apply PR 198's `Connectives.lean` (or stack on PR 198 branch)
- [ ] Copy local `Basic.lean` with import adjusted to `Cslib.Foundations.Relation.Euclidean`
- [ ] Copy local `Denotation.lean`
- [ ] Run `lake build Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Denotation`
- [ ] Run `lake build Cslib.Logics.Modal.Cube` (must still compile unchanged)
- [ ] Run `lake build Cslib.Logics.Modal.LogicalEquivalence` -- EXPECTED TO FAIL (will be
      updated in PR 3); document in PR description
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`
- [ ] Verify `Relation.RightEuclidean`, `Relation.Serial`, `Std.Refl`, `Std.Symm`,
      `IsTrans` resolve correctly from upstream imports
- [ ] Verify `ModalConnectives` instance compiles with PR 198's definitions
- [ ] Open Zulip thread re: coordination with PR #607
