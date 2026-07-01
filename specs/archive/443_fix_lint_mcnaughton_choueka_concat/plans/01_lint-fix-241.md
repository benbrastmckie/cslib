# Implementation Plan: Task #443

- **Task**: 443 - Fix 2 lake lint violations introduced by task 241
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/443_fix_lint_mcnaughton_choueka_concat/reports/01_lint-fix-241.md
- **Artifacts**: plans/01_lint-fix-241.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Two environment-linter violations introduced by task 241 must be cleared. Both fixes are
mechanical, independent, and backed by direct codebase precedent: (1) rename the `Monoid`
instance `buchiCongruence_instMonoid` to `buchiCongruenceMonoid` to satisfy `defsWithUnderscore`
(zero downstream references — resolved only by typeclass resolution), and (2) add
`@[nolint unusedArguments]` above `mullerAccConcat` to satisfy `unusedArguments` while preserving
its three API-required binders (supplied at three call sites for uniformity with `concat`). No
signature changes, no call-site edits, no new definitions, axioms, or sorries.

### Research Integration

The research report confirms both fixes with grounded evidence:
- FIX 1: `grep -rn "buchiCongruence_instMonoid" Cslib/ CslibTests/` returns only the declaration
  line (BuchiCongruence.lean:268). The instance is never referenced by name, so renaming is safe
  with zero call-site updates. `buchiCongruenceMonoid` is lowerCamelCase, underscore-free, and
  mirrors the surrounding `buchiCongruence*` family. `dupNamespace`/`topNamespace` are not
  triggered.
- FIX 2: `mullerAccConcat` (Concat.lean:162) has three genuinely-unused binders (`da1`, `acc1`,
  `da2`, already written as `_`) that CANNOT be removed — they are supplied at Concat.lean:722,
  OmegaRegularLanguage.lean:109, and :422 for API parallelism with `concat`. Bare `_` does not
  silence the linter; the canonical CSLib mechanism is `@[nolint unusedArguments]` (10+ precedent
  sites, e.g. DeductionTheorem.lean:114). Add the attribute; leave binders as `_`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this scoped fix task (roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Clear the `defsWithUnderscore` violation on the Buchi congruence `Monoid` instance.
- Clear the `unusedArguments` violation on `mullerAccConcat`.
- Keep `lake lint` and `lake build` green.

**Non-Goals**:
- Do NOT change the signature of `mullerAccConcat` or remove any binder.
- Do NOT edit any call site (both fixes are call-site-neutral).
- Do NOT introduce new definitions, restructure code, or add lint suppression beyond the standard
  `@[nolint unusedArguments]` attribute.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Hidden by-name reference to `buchiCongruence_instMonoid` breaks after rename | M | L | Research grep already confirmed zero references; scoped build of BuchiCongruence + full `lake build` will catch any regression |
| Attribute placed on wrong declaration or wrong syntax | L | L | Place `@[nolint unusedArguments]` directly above `noncomputable def mullerAccConcat`, mirroring precedent (DeductionTheorem.lean:114); scoped build of Concat confirms |
| Downstream consumer of `mullerAccConcat` affected | M | L | Build OmegaRegularLanguage (the consumer) explicitly; attribute changes no term-level content |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single phase; both edits are independent and verified together.

### Phase 1: Apply both lint fixes and verify [COMPLETED]

**Goal**: Rename the Buchi congruence `Monoid` instance and add the `nolint` attribute to
`mullerAccConcat`, then confirm `lake lint` and `lake build` are clean.

**Tasks**:
- [x] Edit `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean:268`: rename
      `instance buchiCongruence_instMonoid` to `instance buchiCongruenceMonoid` (no other change on
      the line; body unchanged).
- [x] Edit `Cslib/Computability/Automata/DA/Concat.lean:162`: add the line
      `@[nolint unusedArguments]` directly above `noncomputable def mullerAccConcat ...`. Leave the
      three `_` binders and the signature exactly as-is.
- [x] Run scoped build: `lake build Cslib.Computability.Languages.Congruences.BuchiCongruence`.
- [x] Run scoped build: `lake build Cslib.Computability.Automata.DA.Concat`.
- [x] Run scoped build of consumer: `lake build Cslib.Computability.Languages.OmegaRegularLanguage`.
- [x] Run `lake lint` and confirm zero `defsWithUnderscore` and zero `unusedArguments` warnings for
      these two declarations.
- [x] Run full `lake build` for CI parity.

**Timing**: 0.5 hours (dominated by build/lint time, not editing)

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` - rename instance
  `buchiCongruence_instMonoid` -> `buchiCongruenceMonoid` (line 268).
- `Cslib/Computability/Automata/DA/Concat.lean` - add `@[nolint unusedArguments]` above
  `mullerAccConcat` (line 162).

**Verification**:
- All three scoped builds succeed.
- `lake lint` reports no `defsWithUnderscore` / `unusedArguments` warnings for the two declarations.
- Full `lake build` succeeds.

---

## Testing & Validation

- [x] `lake build Cslib.Computability.Languages.Congruences.BuchiCongruence` succeeds.
- [x] `lake build Cslib.Computability.Automata.DA.Concat` succeeds.
- [x] `lake build Cslib.Computability.Languages.OmegaRegularLanguage` succeeds.
- [x] `lake lint` clears both violation categories at the two edited sites.
- [x] `lake build` (full) succeeds (CI parity).

## Artifacts & Outputs

- Modified `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` (1-line rename).
- Modified `Cslib/Computability/Automata/DA/Concat.lean` (1-line attribute addition).
- Clean `lake lint` output.

## Rollback/Contingency

Each edit is a single self-contained line change. To revert, restore the original instance name
`buchiCongruence_instMonoid` and/or remove the `@[nolint unusedArguments]` line via
`git checkout -- <file>`. No call sites or downstream modules are touched, so rollback is
isolated and risk-free. If the rename unexpectedly breaks a build, grep for the new name to locate
any missed reference (research indicates none exist).
