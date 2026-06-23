# Implementation Plan: Task #252

- **Task**: 252 - Acceptance Conditions Zoo
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: None (existing infOcc, DA.Buchi, DA.Muller infrastructure sufficient)
- **Research Inputs**: specs/252_acceptance_conditions_zoo/reports/01_team-research.md
- **Artifacts**: plans/01_acceptance-conditions-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Formalize Rabin, Streett, and parity acceptance conditions for deterministic automata in CSLib, and prove the classical same-state-space conversions between them. The implementation creates three new files (`Rabin.lean`, `Parity.lean`, `Conversions.lean`) in `Cslib/Computability/Automata/DA/`, following the structural pattern established by `DA.Buchi`, `DA.Muller`, and `BuchiChar.lean`. Same-state-space conversions (Buchi-to-Rabin, Rabin-to-Muller, Parity-to-Rabin, Rabin-Streett duality) are fully proved; the hard direction (Rabin-to-Parity via LAR) is stated as `proof_wanted`. Total scope: approximately 400-600 lines across three files.

### Research Integration

The team research report (4 teammates, all high confidence) produced several key design decisions integrated into this plan:

1. **Rabin pairs as `Set (Set State x Set State)`** -- mirrors `DA.Muller.accept : Set (Set State)` for structural consistency. Avoids ordering concerns inherent in `List`-based alternatives.
2. **Parity acceptance via `Nat.sInf`** on `color '' infOcc` -- cleaner than `Finset.min'` because it requires no `[DecidableEq State]` on acceptance definition. `Nat.sInf empty = 0` (even) is handled by placing `[Finite State]` on the `omegaAcceptor` instance.
3. **Piterman 2007 citation corrected** -- DRA-to-DPA uses LAR (Kupferman-Vardi 1998, Zielonka 1998), not Piterman (which converts NBA-to-DPA).
4. **Muller-to-Rabin direction deferred** -- requires exponentially many pairs on the same state space. Only Rabin-to-Muller (trivial) is proved in this PR.
5. **Streett inclusion confirmed** -- dual of Rabin, 30-50 lines, architecturally required for Piterman/NSA context.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `DA.Rabin` with `pairs : Set (Set State x Set State)` and `omegaAcceptor` instance
- Define `DA.Streett` as the dual of Rabin with complemented acceptance
- Define `DA.Parity` with `color : State -> Nat` and `Nat.sInf`-based acceptance
- Prove `Buchi.toRabin` and `Buchi.toRabin_language_eq`
- Prove `Rabin.toMuller` and `Rabin.toMuller_language_eq`
- Prove `Parity.toRabin` and `Parity.toRabin_language_eq`
- Prove `Rabin.toStreett` / `Streett.toRabin` with duality theorem
- State `Rabin.toParity` as `proof_wanted` with LAR references
- Pass CSLib CI pipeline (lake build, checkInitImports, lint-style, lake test)

**Non-Goals**:
- Muller-to-Rabin conversion (exponential same-state-space, separate task)
- Rabin-to-Parity correctness proof (LAR construction, separate task)
- Nondeterministic variants (NA.Rabin, NA.Parity)
- Language-level characterization theorems (depend on McNaughton, task 241)
- NBA-to-DPA (Piterman determinization)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `[Finite State]` on Parity `omegaAcceptor` instance complicates downstream use | M | L | Follow BuchiChar.lean precedent; add helper lemmas for common use patterns |
| Parity-to-Rabin proof more involved than expected (need to enumerate color preimages) | M | M | Start with the definition and `sorry` the language equality; fill proof incrementally |
| `lake shake` flags unused imports in new files | L | M | Run shake after each file; add `public` annotation on needed re-exports |
| `Set (Set State x Set State)` representation causes `simp` lemma issues | M | L | Use explicit `Set.mem_setOf_eq` rewrites; add `@[simp]` lemmas for pair membership |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Rabin and Streett Definitions with Buchi Conversion [COMPLETED]

**Goal**: Create `Rabin.lean` containing the `DA.Rabin` and `DA.Streett` structures, their `omegaAcceptor` instances, the `Buchi.toRabin` conversion, the `Rabin.toMuller` conversion, and the Rabin-Streett duality.

**Tasks**:
- [ ] Create `Cslib/Computability/Automata/DA/Rabin.lean` with module header, copyright, imports from `DA.Basic` and `BuchiChar`
- [ ] Define `DA.Rabin` structure extending `DA` with `pairs : Set (Set State x Set State)`
- [ ] Define `omegaAcceptor` instance for `DA.Rabin`: accepts iff there exists `(E, F) in pairs` such that `infOcc inter E = empty` and `infOcc inter F` is nonempty
- [ ] Define `DA.Streett` structure extending `DA` with `pairs : Set (Set State x Set State)`
- [ ] Define `omegaAcceptor` instance for `DA.Streett`: accepts iff for all `(E, F) in pairs`, `infOcc inter F` nonempty implies `infOcc inter E` nonempty
- [ ] Define `Buchi.toRabin` converting a DBA to a DRA with 1 pair `(empty, accept)`
- [ ] Prove `Buchi.toRabin_language_eq [Finite State]`
- [ ] Define `Rabin.toMuller` converting a DRA to a DMA with `accept := {S | exists EF in pairs, S inter EF.1 = empty and (S inter EF.2).Nonempty}`
- [ ] Prove `Rabin.toMuller_language_eq`
- [ ] Define `Rabin.toStreett` and `Streett.toRabin` (flip E and F components)
- [ ] Prove duality: `Rabin.toStreett_language_eq` and `Streett.toRabin_language_eq`
- [ ] Add `Cslib.Computability.Automata.DA.Rabin` to `Cslib.lean` barrel import via `lake exe mk_all --module`
- [ ] Verify: `lake build Cslib.Computability.Automata.DA.Rabin`

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Automata/DA/Rabin.lean` - NEW: ~150-200 lines
- `Cslib.lean` - Add barrel import (via `lake exe mk_all --module`)

**Verification**:
- `lake build Cslib.Computability.Automata.DA.Rabin` succeeds
- `lean_verify` confirms no sorry in Rabin.lean
- `lake exe checkInitImports` passes

---

### Phase 2: Parity Definition with Parity-to-Rabin Conversion [COMPLETED]

**Goal**: Create `Parity.lean` containing the `DA.Parity` structure, its `omegaAcceptor` instance with `[Finite State]`, the `Parity.toRabin` conversion, and its language equality proof.

**Tasks**:
- [ ] Create `Cslib/Computability/Automata/DA/Parity.lean` with module header, copyright, imports from `DA.Basic` and `Rabin`
- [ ] Define `DA.Parity` structure extending `DA` with `color : State -> Nat`
- [ ] Define `omegaAcceptor` instance for `DA.Parity` with `[Finite State]`: accepts iff `Even (Nat.sInf (a.color '' (a.run xs).infOcc))`
- [ ] Define `Parity.toRabin [Finite State]`: for each odd priority `2i+1` up to some bound, create pair `(color^{-1}({2i+1}), color^{-1}({2i}))`. Concretely: `pairs := {(color ⁻¹' {2*i+1}, color ⁻¹' {2*i}) | i : Nat}`
- [ ] Prove `Parity.toRabin_language_eq [Finite State]` -- the min-even priority in infOcc corresponds to a Rabin pair being satisfied
- [ ] Add `Cslib.Computability.Automata.DA.Parity` to barrel import
- [ ] Verify: `lake build Cslib.Computability.Automata.DA.Parity`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Automata/DA/Parity.lean` - NEW: ~120-160 lines
- `Cslib.lean` - Add barrel import (via `lake exe mk_all --module`)

**Verification**:
- `lake build Cslib.Computability.Automata.DA.Parity` succeeds
- `lean_verify` confirms no sorry in Parity.lean
- `lake exe checkInitImports` passes

---

### Phase 3: Rabin-to-Parity proof_wanted and Conversions File [COMPLETED]

**Goal**: Create `Conversions.lean` containing the `proof_wanted` for `Rabin.toParity` (LAR construction) and a comment in `OmegaRegularLanguage.lean` noting the downstream corollaries.

**Tasks**:
- [ ] Create `Cslib/Computability/Automata/DA/Conversions.lean` with module header, copyright, imports from `Rabin` and `Parity`
- [ ] State `proof_wanted Rabin.toParity_exists`: the existential language-level formulation `forall (a : DA.Rabin State Symbol) [Finite State], exists (S : Type) (_ : Finite S) (da : DA.Parity S Symbol), language da = language a`
- [ ] Add docstring referencing LAR construction (Kupferman-Vardi 1998, Zielonka 1998), explicitly noting this is NOT Piterman 2007
- [ ] State `proof_wanted Muller.toRabin_exists`: `forall (a : DA.Muller State Symbol) [Finite State], exists (S : Type) (_ : Finite S) (da : DA.Rabin S Symbol), language da = language a`
- [ ] Add docstring noting the exponential pair blowup on same state space
- [ ] Add a brief comment in `Cslib/Computability/Languages/OmegaRegularLanguage.lean` noting that `IsRegular.iff_da_rabin` and `IsRegular.iff_da_parity` follow as corollaries once McNaughton (task 241) is proved, via the Rabin/Parity conversion chain
- [ ] Add barrel import for Conversions.lean
- [ ] Verify: `lake build Cslib.Computability.Automata.DA.Conversions`

**Timing**: 1.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Computability/Automata/DA/Conversions.lean` - NEW: ~80-120 lines
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - Add comment (~5 lines)
- `Cslib.lean` - Add barrel import (via `lake exe mk_all --module`)

**Verification**:
- `lake build Cslib.Computability.Automata.DA.Conversions` succeeds
- All `proof_wanted` stubs have comprehensive docstrings

---

### Phase 4: CI Verification and Cleanup [IN PROGRESS]

**Goal**: Run the full CSLib CI pipeline, fix any lint or style issues, and verify the complete build.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports` -- verify all new files import `Cslib.Init`
- [ ] Run `lake exe lint-style` -- fix any style violations
- [ ] Run `lake test` -- verify no test regressions
- [ ] Run `lake exe mk_all --module` -- ensure barrel import is up to date
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` on each new file -- verify import minimality
- [ ] Fix any issues found by the above checks
- [ ] Final `lake build` to confirm everything is green

**Timing**: 2 hours

**Depends on**: 1, 2, 3

**Files to modify**:
- `Cslib/Computability/Automata/DA/Rabin.lean` - Potential lint/style fixes
- `Cslib/Computability/Automata/DA/Parity.lean` - Potential lint/style fixes
- `Cslib/Computability/Automata/DA/Conversions.lean` - Potential lint/style fixes

**Verification**:
- All CI checks pass: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`
- `lake shake` reports no unnecessary imports
- Zero sorry in all new files (verified via `lean_verify`)

## Testing & Validation

- [ ] `lake build` succeeds with no errors
- [ ] `lake exe checkInitImports` passes for all new files
- [ ] `lake exe lint-style` passes with no violations
- [ ] `lake test` passes with no regressions
- [ ] `lean_verify` confirms no sorry in `Rabin.lean` and `Parity.lean`
- [ ] `proof_wanted` stubs in `Conversions.lean` have correct type signatures
- [ ] `Buchi.toRabin_language_eq` correctly states DBA language = DRA language
- [ ] `Rabin.toMuller_language_eq` correctly states DRA language = DMA language
- [ ] `Parity.toRabin_language_eq` correctly states DPA language = DRA language

## Artifacts & Outputs

- `Cslib/Computability/Automata/DA/Rabin.lean` -- DA.Rabin, DA.Streett, Buchi.toRabin, Rabin.toMuller, duality
- `Cslib/Computability/Automata/DA/Parity.lean` -- DA.Parity, Parity.toRabin
- `Cslib/Computability/Automata/DA/Conversions.lean` -- proof_wanted stubs for Rabin.toParity, Muller.toRabin
- `plans/01_acceptance-conditions-plan.md` -- This plan file

## Rollback/Contingency

All changes are additive (three new files plus a comment in OmegaRegularLanguage.lean). Rollback consists of deleting the three new files and removing the comment. No existing files are structurally modified. If the Parity-to-Rabin language equality proof proves intractable, it can be demoted to `proof_wanted` while retaining the definition and conversion function.
