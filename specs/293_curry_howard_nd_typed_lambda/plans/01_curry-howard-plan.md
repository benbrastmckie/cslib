# Implementation Plan: Curry-Howard Isomorphism for ND Proofs

- **Task**: 293 - Curry-Howard Isomorphism between ND Proofs and Typed Lambda Terms
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: None (core isomorphism independent of task 290; Reduction.lean deferred)
- **Research Inputs**: specs/293_curry_howard_nd_typed_lambda/reports/01_curry-howard-research.md
- **Artifacts**: plans/01_curry-howard-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Establish the formal Curry-Howard isomorphism between `Theory.Derivation` (propositional natural
deduction proofs with Finset contexts) and a purpose-built intrinsically-typed simply-typed lambda
calculus with `PL.Proposition Atom` as the type language. The term language mirrors Derivation
constructor-for-constructor (10 constructors), making the forward and backward maps structural
recursion and the roundtrip proofs structural induction with each case reducing to rfl. The core
isomorphism is packaged as an `Equiv`. Reduction correspondence (beta-reduction on terms vs detour
elimination on derivations) is deferred to a future phase after task 290 delivers normalization.

### Research Integration

Key findings from the research report (01_curry-howard-research.md):
- Existing STLC infrastructure (`Cslib/Languages/LambdaCalculus/`) is NOT reusable: wrong
  representation (locally nameless, extrinsic typing, List contexts, arrow-only types).
- Recommended approach: purpose-built intrinsically-typed `Term : Ctx Atom -> Proposition Atom -> Type u`
  with 10 constructors mirroring `Derivation` 1-to-1.
- Isomorphism is structurally trivial: both maps are constructor-renaming by structural recursion.
- Roundtrip proofs: structural induction, each case is rfl/congr.
- Core isomorphism is INDEPENDENT of task 290 (normalization). Only reduction correspondence needs 290.
- Potential pitfall: explicit context parameter `G` must appear in same position in both types.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Propositional module infrastructure. While not explicitly listed as a
remaining roadmap item, it extends `Logics/Propositional/` with proof-theoretic content
(Curry-Howard correspondence) that complements the existing NaturalDeduction module.

## Goals & Non-Goals

**Goals**:
- Define intrinsically-typed `Term` inductive mirroring `Theory.Derivation` constructor-for-constructor
- Implement `curryHowardForward : T.Derivation G A -> Term G A` (derivation to term)
- Implement `curryHowardBackward : Term G A -> T.Derivation G A` (term to derivation)
- Prove roundtrip properties (`forward_backward` and `backward_forward`)
- Bundle as `curryHowardEquiv : T.Derivation G A ≃ Term G A`
- Pass CSLib CI pipeline (build, lint, checkInitImports, lint-style)

**Non-Goals**:
- Beta-reduction on terms (deferred to post-task-290 Reduction.lean)
- Normalization correspondence (requires task 290 `isNormal`, `reduceStep`)
- Reusing or bridging with existing STLC infrastructure
- Term weakening or substitution operations (can be added later)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Explicit `G` parameter mismatch between Derivation and Term constructors | M | L | Mirror exact parameter positions from Derivation source (verified in research) |
| Finset equality in roundtrip proofs not definitionally equal | M | L | Both sides use identical Finset operations; constructor renaming preserves definitional equality |
| Universe polymorphism complications | L | L | Match Derivation's `Type u` universe parameter exactly |
| Lean kernel timeout on large structural induction | M | L | 10 cases with simple rfl/congr; well within kernel capacity |
| CSLib lint failures on new file | L | M | Follow CSLib import and docstring conventions from the start |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Term Type Definition (Defs.lean) [COMPLETED]

**Goal**: Define the intrinsically-typed `Term` inductive with 10 constructors mirroring
`Theory.Derivation`, plus any basic utility definitions.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Propositional/CurryHoward/`
- [ ] Create `Cslib/Logics/Propositional/CurryHoward/Defs.lean` with `import Cslib.Init` and `import Cslib.Logics.Propositional.NaturalDeduction.Basic`
- [ ] Define `inductive Term {T : Theory Atom} : Ctx Atom -> Proposition Atom -> Type u` with constructors: `const` (ax), `var` (ass), `lam` (impI), `app` (impE), `pair` (andI), `fst` (andE1), `snd` (andE2), `inl` (orI1), `inr` (orI2), `case` (orE)
- [ ] Add docstrings to Term and each constructor documenting the Curry-Howard correspondence
- [ ] Verify file builds: `lake build Cslib.Logics.Propositional.CurryHoward.Defs`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/CurryHoward/Defs.lean` - new file, Term inductive definition

**Verification**:
- `lake build Cslib.Logics.Propositional.CurryHoward.Defs` succeeds
- Term type has exactly 10 constructors with matching signatures to Derivation
- All constructors have docstrings

---

### Phase 2: Isomorphism Maps and Roundtrip Proofs (Isomorphism.lean) [COMPLETED]

**Goal**: Define the forward/backward maps between `Derivation` and `Term`, prove both roundtrip
properties, and bundle as an `Equiv`.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/CurryHoward/Isomorphism.lean` importing `Defs`
- [ ] Define `curryHowardForward : T.Derivation G A -> Term (T := T) G A` by structural recursion on Derivation (10 cases, each mapping one constructor to its Term counterpart)
- [ ] Define `curryHowardBackward : Term (T := T) G A -> T.Derivation G A` by structural recursion on Term (10 cases, inverse mapping)
- [ ] Prove `theorem curryHoward_forward_backward : curryHowardForward (curryHowardBackward t) = t` by structural induction on `t`
- [ ] Prove `theorem curryHoward_backward_forward : curryHowardBackward (curryHowardForward d) = d` by structural induction on `d`
- [ ] Define `def curryHowardEquiv : T.Derivation G A ≃ Term (T := T) G A` bundling the above
- [ ] Add docstrings documenting the Curry-Howard correspondence theorem
- [ ] Verify file builds: `lake build Cslib.Logics.Propositional.CurryHoward.Isomorphism`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/CurryHoward/Isomorphism.lean` - new file, forward/backward maps, roundtrip proofs, Equiv

**Verification**:
- `lake build Cslib.Logics.Propositional.CurryHoward.Isomorphism` succeeds
- `lean_verify` confirms no sorry or axiom usage beyond standard foundations
- Both roundtrip theorems type-check
- `curryHowardEquiv` bundles correctly as an `Equiv`

---

### Phase 3: Module Integration and CI Verification [COMPLETED]

**Goal**: Register the new files in the CSLib module hierarchy, update barrel imports, and pass
the full CI pipeline.

**Tasks**:
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import with new CurryHoward modules
- [ ] Run `lake exe checkInitImports` to verify all files import `Cslib.Init`
- [ ] Run `lake exe lint-style` and fix any style issues
- [ ] Run `lake lint` and fix any linter warnings (docBlame, etc.)
- [ ] Run `lake build` for full project build verification
- [ ] Run `lake test` to ensure no regressions

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib.lean` - barrel import update (automated by `mk_all`)
- `Cslib/Logics/Propositional/CurryHoward/Defs.lean` - lint fixes if needed
- `Cslib/Logics/Propositional/CurryHoward/Isomorphism.lean` - lint fixes if needed

**Verification**:
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake lint` passes (or only pre-existing warnings)
- `lake build` succeeds
- `lake test` passes

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.CurryHoward.Defs` compiles without errors
- [ ] `lake build Cslib.Logics.Propositional.CurryHoward.Isomorphism` compiles without errors
- [ ] `lean_verify` on `curryHowardEquiv` reports no sorry, no non-standard axioms
- [ ] `curryHoward_forward_backward` and `curryHoward_backward_forward` are proven (not sorry)
- [ ] Full CI pipeline passes: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Term type has exactly 10 constructors matching the 10 Derivation constructors

## Artifacts & Outputs

- `Cslib/Logics/Propositional/CurryHoward/Defs.lean` - Term inductive type definition
- `Cslib/Logics/Propositional/CurryHoward/Isomorphism.lean` - Forward/backward maps, roundtrip proofs, Equiv
- `specs/293_curry_howard_nd_typed_lambda/plans/01_curry-howard-plan.md` - This plan file

## Rollback/Contingency

If the full 10-constructor isomorphism encounters unexpected difficulties (e.g., Finset equality
issues in roundtrip proofs for `orE`/`case` constructors):
1. Fall back to the {arrow, and} fragment: implement only `lam`, `app`, `pair`, `fst`, `snd`
   (5 constructors) as a self-contained milestone.
2. Mark the full isomorphism as [BLOCKED] with specific blocker details.
3. The {arrow, and} fragment is a complete deliverable per the task description.

If CI issues arise that are unrelated to this task (pre-existing lint warnings, unrelated build
failures), document them and proceed with task-scoped verification only.
