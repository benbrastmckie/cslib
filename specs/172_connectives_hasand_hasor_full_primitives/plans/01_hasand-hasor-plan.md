# Implementation Plan: HasAnd/HasOr Atomic Typeclasses

- **Task**: 172 - connectives_hasand_hasor_full_primitives
- **Status**: [IMPLEMENTING]
- **Effort**: 1.5 hours
- **Dependencies**: None (task 171 research complete; no code prerequisites)
- **Research Inputs**: reports/01_team-research.md
- **Artifacts**: plans/01_hasand-hasor-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Extend `Cslib/Foundations/Logic/Connectives.lean` to support the hybrid five-primitive signature `{atom, bot, imp, and, or}` by adding `HasAnd` and `HasOr` atomic typeclasses, updating the bundled `PropositionalConnectives` class to include them, and trimming `ImpBotDerived` to retain only the logic-neutral defaults (`neg`, `top`). All changes are confined to a single file. The build should remain green because the four downstream formula types already define `.and` and `.or` as `abbrev`s over `imp`/`bot`, which Lean's typeclass synthesizer resolves transparently.

### Research Integration

Integrated findings from `reports/01_team-research.md` (team research, 4 teammates):
- **Recommendation 1**: `HasAnd`/`HasOr` follow the single-field `HasBot`/`HasImp` pattern.
- **Recommendation 2**: Extend `PropositionalConnectives` only; downstream bundled classes inherit automatically. The 4 instance sites need no changes (abbrev-pathway resolution confirmed by Teammate D).
- **Recommendation 3**: Trim `ImpBotDerived` to `neg`/`top` -- Lukasiewicz `and`/`or` are classical-only (Wajsberg 1938, McKinsey 1939).
- **Recommendation 4**: Update module docstring to replace "{imp, bot} functionally complete" framing.
- **Recommendations 5-6**: No notation at typeclass level; no changes outside `Connectives.lean`.
- **Recommendation 8**: Defer `iff` to task 173 (requires `HasAnd` instantiation on `Proposition`).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the Foundations/Logic infrastructure layer in the ROADMAP. The `Connectives.lean` file is the root of the module hierarchy; extending it with `HasAnd`/`HasOr` enables the downstream tasks 173-178 (formula type extensions, metalogic proofs).

## Goals & Non-Goals

**Goals**:
- Add `HasAnd` and `HasOr` as standalone atomic typeclasses mirroring `HasBot`/`HasImp`
- Update `PropositionalConnectives` to extend `HasAnd F, HasOr F`
- Trim `ImpBotDerived` to `neg` and `top` only (remove classical-only `and`/`or` defaults)
- Update module docstring and `ImpBotDerived` docstring to reflect five-primitive design
- Verify the build remains green via `lake build Cslib.Foundations.Logic.Connectives`

**Non-Goals**:
- Adding notation for `HasAnd`/`HasOr` (belongs in each logic's namespace, tasks 173+)
- Modifying any file outside `Connectives.lean` (instance sites, Axioms.lean, ProofSystem.lean)
- Adding `HasAtom`, `HasNeg`, `HasTop`, or `HasIff` typeclasses
- Changing any formula type inductives or their `abbrev` definitions
- Adding `iff` to `ImpBotDerived` (deferred to task 173 when `HasAnd` is instantiated)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Abbrev-pathway fails: existing instances cannot auto-satisfy `HasAnd`/`HasOr` | H | L | Verify with `lake build` after Phase 1. If it fails, revert bundled class extension and defer to task 173 per research fallback plan. |
| Field name collision: `and`/`or` conflict with Lean builtins | M | L | Research confirms `HasImp.imp` (also a keyword) works without conflict. Same pattern applies. |
| Downstream import breakage from changed `ImpBotDerived` signature | M | L | `ImpBotDerived` is intentionally uninstantiated (docstring says so explicitly). No downstream code references `ImpBotDerived.and` or `ImpBotDerived.or`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Add HasAnd/HasOr and Update PropositionalConnectives [COMPLETED]

**Goal**: Add the two new atomic typeclasses and extend the bundled class hierarchy.

**Tasks**:
- [ ] Add `HasAnd` typeclass after `HasSince`, following the `HasBot`/`HasImp` pattern:
  ```lean
  /-- A type has a conjunction connective. -/
  class HasAnd (F : Type*) where
    /-- The conjunction connective. -/
    and : F → F → F
  ```
- [ ] Add `HasOr` typeclass immediately after `HasAnd`:
  ```lean
  /-- A type has a disjunction connective. -/
  class HasOr (F : Type*) where
    /-- The disjunction connective. -/
    or : F → F → F
  ```
- [ ] Update `PropositionalConnectives` to extend `HasAnd F, HasOr F`:
  ```lean
  class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F, HasAnd F, HasOr F
  ```
- [ ] Do NOT change `ModalConnectives`, `TemporalConnectives`, or `BimodalConnectives` (they inherit via `PropositionalConnectives`)
- [ ] Run `lake build Cslib.Foundations.Logic.Connectives` to verify compilation
- [ ] If build fails on downstream instance sites, check whether abbrev-pathway resolution works; if not, revert bundled class extension and document deferral

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - add typeclasses, update bundled class

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` compiles without errors
- Downstream modules that instantiate `PropositionalConnectives` still build (spot-check with `lake build Cslib.Logics.Propositional.Defs`)

---

### Phase 2: Trim ImpBotDerived [COMPLETED]

**Goal**: Remove the classical-only `and`/`or` defaults from `ImpBotDerived`, retaining only `neg` and `top`.

**Tasks**:
- [ ] Remove the `or` field and its docstring from `ImpBotDerived`
- [ ] Remove the `and` field and its docstring from `ImpBotDerived`
- [ ] Update the `ImpBotDerived` docstring to:
  - Remove references to `or` and `and` as derived connectives
  - Explain that `and`/`or` were removed because the Lukasiewicz encoding is classical-only (Wajsberg 1938, McKinsey 1939)
  - Note that conjunction and disjunction are now primitives via `HasAnd`/`HasOr`
  - Retain explanation that `neg` and `top` are valid in minimal/intuitionistic/classical logic
- [ ] Run `lake build Cslib.Foundations.Logic.Connectives` to verify

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - trim `ImpBotDerived` class body and docstring

**Verification**:
- `ImpBotDerived` has exactly two fields: `neg` and `top`
- Module compiles without errors

---

### Phase 3: Update Module Docstring and Final Build Verification [COMPLETED]

**Goal**: Replace the "{imp, bot} functionally complete" module docstring with the five-primitive design rationale, and run full build verification.

**Tasks**:
- [ ] Update the module-level `/-! ... -/` docstring:
  - Replace the paragraph starting "Falsum and implication are taken as the only propositional primitives..." with five-primitive rationale
  - Update the `## Design` section's atomic class list to include `HasAnd` and `HasOr`
  - Update the bundled class descriptions to reflect `HasAnd`/`HasOr` inclusion
  - Keep the existing `## References` section intact
- [ ] Run `lake build Cslib.Foundations.Logic.Connectives` for final module-level verification
- [ ] Run `lake build` (full project) to confirm no downstream breakage
- [ ] Run `lake exe lint-style` to check style compliance

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - update module docstring

**Verification**:
- Module docstring no longer claims "{imp, bot} is functionally complete"
- Module docstring lists `HasAnd` and `HasOr` in the atomic class enumeration
- `lake build` (full project) passes
- `lake exe lint-style` passes for `Connectives.lean`

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Connectives` passes after each phase
- [ ] `lake build Cslib.Logics.Propositional.Defs` passes (abbrev-pathway test)
- [ ] `lake build` (full project) passes after Phase 3
- [ ] `lake exe lint-style` passes
- [ ] `lake exe checkInitImports` passes
- [ ] Grep confirms no `ImpBotDerived` `and`/`or` field references in codebase: `grep -r "ImpBotDerived\.\(and\|or\)" Cslib/`

## Artifacts & Outputs

- `specs/172_connectives_hasand_hasor_full_primitives/plans/01_hasand-hasor-plan.md` (this plan)
- Modified `Cslib/Foundations/Logic/Connectives.lean` (implementation output)

## Rollback/Contingency

All changes are in a single file (`Connectives.lean`). Rollback is a single `git checkout -- Cslib/Foundations/Logic/Connectives.lean`. If the abbrev-pathway fails (Phase 1 build breaks on downstream instances), the fallback is to revert the `PropositionalConnectives` extension and defer bundled class updates to task 173, keeping only the standalone `HasAnd`/`HasOr` typeclasses and the `ImpBotDerived` trim.
