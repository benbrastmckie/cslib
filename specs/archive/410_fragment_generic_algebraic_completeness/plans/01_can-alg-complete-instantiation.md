# Implementation Plan: Task #410

- **Task**: 410 - Fragment-generic algebraic completeness for MPL-base derivability
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours
- **Dependencies**: 407 (delivers FragmentGeneric.lean; status [PR READY])
- **Research Inputs**: specs/410_fragment_generic_algebraic_completeness/reports/01_fragment-generic-algebraic-completeness.md
- **Artifacts**: plans/01_can-alg-complete-instantiation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Abstract the per-fragment algebraic completeness (already proved piecewise across
`MplConservativeChain.lean`, `HilbertCompleteness.lean`, and `BrouwerianCompleteness*.lean`) into a
single generic `CanAlgComplete P` structure, then instantiate it for the three fragment predicates
by reuse. This is an abstraction/instantiation task, not new mathematics: every required theorem
already exists sorry-free, and each instance is a small term-level composition of existing
`.mp`/`.mpr` projections. All work lands in one new additive file
`Cslib/Logics/Propositional/Semantics/Algebra/CanAlgComplete.lean`, leaving existing files
untouched except an optional documentation note in `FragmentGeneric.lean`.

### Research Integration

Key findings driving this plan (report 01):
- **F1**: The per-fragment `Derivable Ax_P φ ↔ GHAValid φ` links already exist for every fragment
  named in the residual. `MPL.hilbert_alg_complete` is **total** (all φ); `mplAxiom_iff_conjImpAxiom`,
  `mplAxiom_iff_impAxiom`, `mplAxiom_iff_conjImpBotMinAxiom` cover the rest.
- **F2**: `CanAlgComplete P` bundles a target axiom system `Ax` + `complete` (P φ → GHAValid φ →
  Derivable Ax φ) + `sound` (Derivable Ax φ → GHAValid φ). `canAlgComplete_iff` packages the
  equivalence; composing with 407's `AlgEvalIndependent` + `ghaValid_iff_haValid_of_botFree` upgrades
  to `HAValid` on ⊥-free fragments (`canAlgComplete_haValid_iff`).
- **F3 / Goal 4 (KEY CORRECTION)**: `IsImpTopOnly` is recoverable **today** via
  `mplAxiom_iff_impAxiom` routed through `IsImpTopOnly_implies_IsOrBotFree → LowerSet B`. The
  Rasiowa free implicative algebra is **declined** — it is large net-new work with no zero-debt
  payoff for this task.
- **F6**: A literally single-`AlgEvaluate` generic proof is not achievable (three evaluators over
  three algebra classes). The typeclass-instance bundling is the idiomatic closure; precedent is
  `ConjImpAxioms`.
- Design choice: `structure` (not `class`) because `Ax` is output data that varies per fragment and
  is not instance-inferable. Pin universes as `.{u,u}` to match the existing chain.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found / roadmap flag not set. This task completes the task-407 residual
(FragmentGeneric.lean lines 40-53) by delivering the unifying abstraction the residual called open.

## Goals & Non-Goals

**Goals**:
- Define `CanAlgComplete P` as a `structure` bundling `Ax`, `complete`, `sound`.
- Prove `canAlgComplete_iff` (Derivable Ax φ ↔ GHAValid φ on the fragment) and
  `canAlgComplete_haValid_iff` (Derivable Ax φ ↔ HAValid φ for ⊥-free fragments).
- Provide three instances by reuse: `IsBotFree → MinPropAxiom`, `IsOrBotFree → ConjImpAxiom`,
  `IsImpTopOnly → ImpAxiom`.
- Keep the build green and lint-clean: barrel import, `checkInitImports`, docBlame docstrings, no
  `sorry`, no new axioms.

**Non-Goals**:
- Building the Rasiowa free implicative algebra (explicitly declined per F3/Goal 4).
- Refactoring or re-proving any existing theorem in `MplConservativeChain.lean`,
  `HilbertCompleteness.lean`, or `BrouwerianCompleteness*.lean`.
- A single literally-uniform `AlgEvaluate`-generic completeness proof (F6: not achievable).
- Exposing the canonical algebra on `CanAlgComplete` (keep minimal; widen only if a consumer needs it).
- The optional `IsOrFree → ConjImpBotMinAxiom` instance (nice-to-have, scoped out of the core).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe-polymorphism friction passing `GHAValid` through a structure field | M | M | Pin `.{u,u}` exactly as `GHAValid_implies_BrouwerianValid_direct` / `brouwerianBot_complete` do; copy their signature shape |
| `structure` vs `class` causes instance-search confusion | L | L | Use `structure`; consume instances explicitly by name, never via instance resolution |
| Diamond on `Preorder B` in `LowerSet.Iic` (seen in chain) | M | M | Do NOT re-prove the chain; reuse `mplAxiom_iff_*` / `GHAValid_implies_BrouwerianValid_direct` as-is so the diamond stays inside already-working lemmas |
| Exact existing signatures (implicit vs explicit args, `Bool` vs `Prop` for P) differ from sketch | M | M | Before writing each instance, `lean_hover_info` / Read the exact signature; adjust field types to match rather than forcing the sketch |
| `complete` field for `IsImpTopOnly` needs the `hφ : P φ = true` hypothesis threaded into `mplAxiom_iff_impAxiom` | M | M | Verify `mplAxiom_iff_impAxiom`'s exact hypothesis (`IsImpTopOnly φ`) and pass `hφ` through; covered by Phase 2 verification |
| New file omitted from barrel / missing `import Cslib.Init` | M | M | Run `lake exe mk_all --module` and `lake exe checkInitImports` in Phase 3 before declaring done |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. Here the three phases are strictly
sequential (each edits the same new file and builds on the previous), so each wave holds one phase.

---

### Phase 1: CanAlgComplete structure and packaged theorems [COMPLETED]

**Goal**: Create the new additive file with the `CanAlgComplete` structure and the two packaged
theorems, building green.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/CanAlgComplete.lean` with header,
  `import Cslib.Init`, and imports of `FragmentGeneric`, `MplConservativeChain`,
  `HilbertCompleteness` (verify exact module paths before importing).
- [ ] Confirm exact existing signatures with `lean_hover_info` / Read: `GHAValid`, `HAValid`,
  `Derivable`, `AlgEvalIndependent`, `ghaValid_iff_haValid_of_botFree`, and the `Proposition`/`P`
  type (`→ Bool` vs `→ Prop`) and namespace (`Cslib.Logic.PL`).
- [ ] Define `structure CanAlgComplete (P) where Ax / complete / sound`, with a docstring on the
  structure and each field, universes pinned `.{u,u}` to match the chain.
- [ ] Prove `canAlgComplete_iff (C) (hφ) : Derivable C.Ax φ ↔ GHAValid φ` via `⟨C.sound, C.complete hφ⟩`.
- [ ] Prove `canAlgComplete_haValid_iff (C) (_hInd : AlgEvalIndependent P) (hsub : P ⊆ IsBotFree)
  (hφ) : Derivable C.Ax φ ↔ HAValid φ` via `rw [canAlgComplete_iff C hφ]; exact
  ghaValid_iff_haValid_of_botFree (hsub hφ)`.
- [ ] Add docstrings to both theorems (docBlame).

**Timing**: 1.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/CanAlgComplete.lean` - new file: structure +
  `canAlgComplete_iff` + `canAlgComplete_haValid_iff`.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.CanAlgComplete` is green.
- No `sorry` and no new `axiom` in the file (`grep -n "sorry\|admit\|axiom" <file>` returns nothing
  unexpected).
- `lean_diagnostic_messages` on the file shows no errors/warnings.

---

### Phase 2: Three instances by reuse [COMPLETED]

**Goal**: Add the three `CanAlgComplete` instances (`def`s) built entirely from existing sorry-free
theorems, building green.

**Tasks**:
- [ ] `canAlgComplete_isBotFree : CanAlgComplete IsBotFree` with `Ax := MinPropAxiom`,
  `complete := fun _ h => MPL.hilbert_alg_complete.mpr h`, `sound := fun h =>
  MPL.hilbert_alg_complete.mp h` (total iff; ⊥-freeness unused in the field).
- [ ] `canAlgComplete_isOrBotFree : CanAlgComplete IsOrBotFree` with `Ax := ConjImpAxiom`,
  `complete := fun hφ h => conjImp_brouwerian_complete hφ (GHAValid_implies_BrouwerianValid_direct hφ h)`,
  `sound := fun h => MPL.hilbert_alg_complete.mp (derivableMinOfDerivableConjImp h)`.
- [ ] `canAlgComplete_isImpTopOnly : CanAlgComplete IsImpTopOnly` with `Ax := ImpAxiom`,
  `complete := fun hφ h => (mplAxiom_iff_impAxiom hφ).mp (MPL.hilbert_alg_complete.mpr h)`,
  `sound := fun h => MPL.hilbert_alg_complete.mp (derivableMinOfDerivableImp h)`.
- [ ] Before/while writing each: verify the exact hypothesis shape of `mplAxiom_iff_impAxiom`,
  `conjImp_brouwerian_complete`, `GHAValid_implies_BrouwerianValid_direct`,
  `derivableMinOfDerivableConjImp`, `derivableMinOfDerivableImp` with `lean_hover_info`; adjust the
  field lambdas to the real signatures (implicit args, `hOBF` naming) rather than forcing the sketch.
- [ ] Add a docstring to each instance `def`.

**Timing**: 1.25 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/CanAlgComplete.lean` - append the three instance `def`s.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.CanAlgComplete` is green.
- Optionally exercise composition: an example/`#check` deriving `Derivable MinPropAxiom φ ↔ HAValid φ`
  for ⊥-free φ via `canAlgComplete_haValid_iff canAlgComplete_isBotFree` to confirm the wiring (can
  be removed before commit).
- No `sorry`, no new axiom (re-run grep).

---

### Phase 3: CI integration, docs, and residual note [COMPLETED]

> Deviation notes:
> - `lake exe mk_all --module` blindly re-added the deliberately-stubbed `IntFMPSpike` import to
>   `Cslib.lean`; restored the manual stub comment (kept the new `CanAlgComplete` import) to avoid
>   regressing the barrel.
> - Renamed the three instances to lowerCamelCase (`canAlgCompleteIsBotFree`, etc.) to satisfy the
>   `defsWithUnderscore` env linter (the report sketch used underscores).
> - Full `lake build` / `lake test` are RED due to PRE-EXISTING, UNRELATED broken files
>   (`SequentCalculus.LJ.Completeness`: unknown constant `LJProof.cut`, "No goals"; parked
>   `Metalogic.IntFMPSpike`). Neither imports nor is imported by task-410 files; both are committed
>   and unmodified by this task. Task-410-scoped verification all passes (see below).

**Goal**: Wire the new file into the build barrel, satisfy the full CSLib CI pipeline, and update
the `FragmentGeneric.lean` residual note.

**Tasks**:
- [ ] Run `lake exe mk_all --module` (or update the relevant barrel/`Cslib.lean` aggregator) so the
  new file is imported by the library barrel.
- [ ] Run `lake exe checkInitImports` and confirm the new file imports `Cslib.Init`.
- [ ] Run `lake exe lint-style` and `lake shake --add-public --keep-implied --keep-prefix`; fix any
  style/import findings (lowerCamelCase names, no underscores in new identifiers beyond the existing
  `canAlgComplete_*` convention, docBlame docstrings present).
- [ ] Run `lake test` (CslibTests) and a full `lake build` to confirm library-wide green.
- [ ] Update `FragmentGeneric.lean` residual note (lines 40-53): point to `CanAlgComplete`, and
  correct the "open research" / "Rasiowa free algebra required" framing (per F3/Goal 4). Keep the
  edit minimal and documentation-only.

**Timing**: 1.0 hour

**Depends on**: 2

**Files to modify**:
- Library barrel (`Cslib.lean` or `mk_all` output) - add import of the new module.
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentGeneric.lean` - update residual note
  (lines 40-53), documentation only.

**Verification**:
- `lake build` (full) green.
- `lake test` green.
- `lake exe checkInitImports` passes.
- `lake exe lint-style` passes.
- `lake shake --add-public --keep-implied --keep-prefix` reports no actionable issues for the new file.

---

## Testing & Validation

- [ ] `lake build` succeeds for the new module and the full library.
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes (new file imports `Cslib.Init`; barrel updated).
- [ ] `lake exe lint-style` passes (docstrings, naming).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` clean for the new file.
- [ ] No `sorry`, no `admit`, no new `axiom` in `CanAlgComplete.lean`.
- [ ] Composition spot-check: `Derivable MinPropAxiom φ ↔ HAValid φ` derivable for ⊥-free φ through
  the new API.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/CanAlgComplete.lean` (new): `CanAlgComplete`
  structure, `canAlgComplete_iff`, `canAlgComplete_haValid_iff`, and three instances.
- Updated library barrel import.
- Updated `FragmentGeneric.lean` residual note (documentation only).

## Rollback/Contingency

The work is additive and isolated to one new file plus a doc-only note. To revert: delete
`CanAlgComplete.lean`, remove its barrel import line, and revert the `FragmentGeneric.lean` note.
No existing proofs are modified, so rollback cannot break the rest of the library. If an instance
signature proves harder than the sketch (e.g. an unexpected hypothesis on `mplAxiom_iff_impAxiom`),
fall back to the alternative `Ax := MinPropAxiom` target with `complete`/`sound` from the
`mplAxiom_iff_*` iff composed with `MPL.hilbert_alg_complete` (noted as equivalent in report §3),
keeping the phase green. If `IsImpTopOnly` unexpectedly resists reuse, ship Phases 1-2 with only the
`IsBotFree` and `IsOrBotFree` instances and spawn a follow-up — do NOT build the Rasiowa free algebra.
