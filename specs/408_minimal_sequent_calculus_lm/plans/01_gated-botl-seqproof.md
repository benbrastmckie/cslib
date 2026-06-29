# Implementation Plan: Task #408 — Property-Gated `botL` Sequent Calculus

- **Task**: 408 - Sequent calculus: property-gated botL (single calculus, MPL/IPL one inductive; cut/subformula proved once)
- **Status**: [NOT STARTED]
- **Effort**: 15 hours
- **Dependencies**: 407 (gated-rule design + property modules; green main)
- **Research Inputs**: specs/408_minimal_sequent_calculus_lm/reports/01_minimal-sequent-calculus-gated-botl.md
- **Artifacts**: plans/01_gated-botl-seqproof.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Unify the MPL and IPL single-conclusion sequent calculi into one inductive `SeqProof T`
parameterized by a theory `T : Theory Atom`, with the explosion rule `botL` gated by
`[IsIntuitionistic T]` — the exact analogue of the shipped gated `efq` in `Theory.Derivation`
(task 398/407 W1). Structural metatheory (`height`, `mono`, `CutFree`, `cutAdmissibility`,
`cutElim`, subformula property) is proved **once** generically over `T`; `LJProof := SeqProof IPL`
recovers every existing LJ result with identical public signatures. Soundness and completeness
stay IPL-specific (recovered at `T = IPL`). The work is a mechanical, file-scoped refactor of
~36 `botL` match arms across six LJ files plus `OrImpConservative.lean`, each switched to the
`@SeqProof.botL _ _ _ inst h` qualified pattern (with `letI := inst` on every reconstruction
site). **Definition of done**: full `lake build` green, all CI checks pass, no `sorry`/axiom/
vacuous def introduced, LK untouched and every preserved result type-stable.

### Research Integration

Report 01 verified (4 `lean_run_code` experiments) that a typeclass-gated constructor compiles
and, critically, that the anonymous `.botL _ _ _` pattern fails (Lean tries to *synthesize* the
instance) while the `@`-qualified pattern *binds* the stored instance. Every `botL` reconstruction
in the LJ proofs happens inside a branch that just matched a `botL`, so the instance is always in
hand — the gate is inert to the cut-elimination recursion (`termination_by sizeOf` unchanged).
The report's per-file `botL` site counts drive the phase boundaries below: Basic 8,
CutElimination 13, Interpolation 9, Soundness 2, SubformulaProperty 2, Completeness 2,
OrImpConservative 3. The FALLBACK (separate `LMProof` inductive) is explicitly NOT pursued —
research showed it costs strictly more and still requires the trivial `botL` arms.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set). Task 408 is Wave 5 of the task 407
MPL structure-first redesign and closes report 01 §3.4/§7.1's "largest structural gap".

## Goals & Non-Goals

**Goals**:
- Introduce a single inductive `SeqProof (T : Theory Atom) : @Sequent Atom → Type u` with all ten
  connective/structural rules ungated and `botL` gated by `[IsIntuitionistic T]`.
- Prove the structural metatheory generically over `T` (one proof, reused for MPL and IPL).
- Define `LJProof := SeqProof IPL` and re-export `LJProof.height`, `LJProof.mono`, `LJCutFree`,
  `CutFreeLJProof`, `ljCutAdmissibility`, `LJProof.cutElim`, subformula property, `LJProof.sound`,
  `hilbert_iff_lj` with byte-identical public signatures.
- Reuse existing gate primitives `IsIntuitionistic` / `MPL` / `IPL` (Defs.lean:154–183); define no
  new gate classes.
- Keep every external consumer (`OrImpConservative.lean`, `ProofSystemEquivalence.lean`)
  type-stable.
- Zero technical debt: no `sorry`, no new axiom, no vacuous definition.

**Non-Goals**:
- Unifying or modifying LK (multiple-conclusion, different structural shape — stays its own
  calculus; symmetric gating noted only as future work).
- Weakening or restating any existing LJ/LK theorem.
- Posting any LLM-authored prose to Zulip (honor the Zulip AI policy; docstrings/reports are
  internal artifacts and fine).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Anonymous `.botL` match arms re-introduced, triggering instance-synthesis failure | M | M | Use `@SeqProof.botL _ _ _ inst h` everywhere; `letI := inst` before any reconstruction (research §3, §8 template). |
| A specific cut-elim arm unexpectedly resists the gate | H | L | Research found none across 13 sites; if it occurs, mark that phase `[BLOCKED]` for user review — do NOT introduce `sorry`. |
| `InferenceSystem` instance / `@[expose] public section` left pointing at the old inductive | M | M | Re-point to `SeqProof IPL` in Phase 1; verify `Nonempty (LJProof …)` and `induction` on `LJProof` still work. |
| Downstream public signature drift breaks `OrImpConservative`/`ProofSystemEquivalence` | H | L | `LJProof` is an `abbrev` (definitionally `SeqProof IPL`); re-export wrappers preserve exact types; dedicated audit phase. |
| `ljCutAdm_right` heartbeat budget exceeded after edits | M | L | Keep `set_option maxHeartbeats 400000` (CutElimination.lean:541); the gate adds no compile cost (`sizeOf` unchanged). |
| Decidability.lean relies on `LJProof` constructor shape | M | L | Audit for type stability (no `botL` sites listed, but it consumes `LJProof`). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4, 5 | 2 |
| 4 | 6 | 3, 4, 5 |
| 5 | 7 | 6 |

Phases within the same wave can execute in parallel (subject to file-level territory). Phases 3,
4, 5 touch disjoint files and may run in parallel once Phase 2 is green.

---

### Phase 1: Generic `SeqProof T` inductive + `LJ/Basic.lean` migration [COMPLETED]

**Goal**: Define the single gated inductive and its generic basic structural definitions; retarget
`LJProof` to `SeqProof IPL` while preserving the public surface of `LJ/Basic.lean`.

**Tasks**:
- [ ] Add `inductive SeqProof (T : Theory Atom) : @Sequent Atom → Type u` with `ax`, `andL`, `andR`,
      `orL`, `orR1`, `orR2`, `impL`, `impR`, `weakL`, `cut` ungated and
      `| botL (Γ) (C) [IsIntuitionistic T] (_ : (⊥ : Proposition Atom) ∈ Γ)` gated. Placement:
      `SequentCalculus/Defs.lean` (or a new `SequentCalculus/Basic.lean`); carry full
      `T : Theory Atom` for ND parity (research Q1 recommendation).
- [ ] Define `abbrev LJProof (seq) := SeqProof IPL seq`, `abbrev SeqProofMinimal … := SeqProof MPL …`,
      and `def SeqProof.IsBotRuleFree` (`botL ↦ False`), reusing `IsIntuitionistic`/`MPL`/`IPL`.
- [ ] Move/define generic `SeqProof.height`, `SeqProof.mono`, `SeqProof.CutFree` and
      `CutFreeLJProof`/`LJCutFree` over `SeqProof T`; re-export at `IPL` with identical signatures.
      Use the `@SeqProof.botL _ _ _ _ _` pattern on read-only arms and `letI := inst` on `mono`'s
      reconstruction arm (8 `botL` sites in this file).
- [ ] Re-point the `InferenceSystem` instance (`LJ/Basic.lean:211`) and any `@[expose] public
      section` to `SeqProof IPL`; confirm `Nonempty (LJProof …)` and `induction`/`cases` on
      `LJProof` still elaborate.
- [ ] `lake build` the two touched modules (new base + `LJ/Basic.lean`) to green.

**Timing**: 3 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/Defs.lean` (or new `SequentCalculus/Basic.lean`) — new `SeqProof` inductive, fragment names, generic basic defs.
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` — `LJProof := SeqProof IPL`, re-exports, `InferenceSystem` re-point, 8 `botL` arms.

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Basic` succeeds.
- No new `sorry`/axiom (`grep -rn "sorry\|admit" <files>` empty); public names `LJProof`,
  `CutFreeLJProof`, `LJCutFree`, `LJProof.height`, `LJProof.mono` resolve with original types.

---

### Phase 2: Generic cut elimination — `LJ/CutElimination.lean` [NOT STARTED]

**Goal**: Carry `ljCutAdmissibility`/`LJProof.cutElim` over the gate generically over `T`,
preserving signatures and termination measures.

**Tasks**:
- [ ] Convert the principal helpers (`ljCutAdm_principal_andR/orR/impR`), `ljCutAdm_left`, and
      `ljCutAdm_right` to operate on `SeqProof T`; switch all 13 `botL` occurrences to the
      `@SeqProof.botL _ _ _ inst hbot` pattern and add `letI := inst` before every `botL`
      reconstruction (incl. the `⊥`-cut arm at ~line 558).
- [ ] Convert the `LJProof.cutElim` tactic arm (~line 678) to
      `| @botL Γ C inst hbot => letI := inst; exact ⟨⟨.botL Γ C hbot, trivial⟩⟩`.
- [ ] Keep `set_option maxHeartbeats 400000`; confirm `termination_by sizeOf …` measures are
      unchanged. Re-export `LJProof.cutElim`/`ljCutAdmissibility` at `IPL` with identical types.
- [ ] `lake build` `LJ/CutElimination.lean` to green.

**Timing**: 4 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` — 13 `botL` arms + cutElim arm; generic-over-`T` helpers.

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination` succeeds.
- `LJProof.cutElim` and `ljCutAdmissibility` keep their original public signatures.
- No `sorry`/axiom introduced.

---

### Phase 3: Subformula property — `LJ/SubformulaProperty.lean` [NOT STARTED]

**Goal**: Recover the subformula property over the gated calculus (generic where applicable).

**Tasks**:
- [ ] Switch the 2 `botL` match arms to the `@`-qualified pattern (+ `letI := inst` if rebuilding).
- [ ] Keep the public subformula-property statement type-stable at `LJProof = SeqProof IPL`.
- [ ] `lake build` `LJ/SubformulaProperty.lean` to green.

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/SubformulaProperty.lean` — 2 `botL` arms.

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.SubformulaProperty` succeeds.
- Subformula-property theorem signature unchanged; no `sorry`/axiom.

---

### Phase 4: Soundness + Completeness (IPL-specific) — `LJ/Soundness.lean`, `LJ/Completeness.lean` [NOT STARTED]

**Goal**: Recover `LJProof.sound` and `hilbert_iff_lj` unchanged; these stay strength-specific at
`T = IPL`.

**Tasks**:
- [ ] `LJ/Soundness.lean`: switch the 2 `botL` arms to the `@`-pattern; the intuitionistic-Kripke
      `botL` discharge (`IForces … ⊥ = False`) is unchanged since `LJProof = SeqProof IPL`.
- [ ] `LJ/Completeness.lean`: switch the 2 `botL` arms to the `@`-pattern; keep `hilbert_iff_lj`
      keyed to `IntPropAxiom` with its original signature.
- [ ] `lake build` both files to green.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Soundness.lean` — 2 `botL` arms.
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Completeness.lean` — 2 `botL` arms.

**Verification**:
- `lake build` of both modules succeeds.
- `LJProof.sound` and `hilbert_iff_lj` keep original signatures; no `sorry`/axiom.

---

### Phase 5: Interpolation + Decidability — `LJ/Interpolation.lean`, `LJ/Decidability.lean` [NOT STARTED]

**Goal**: Recover interpolation (9 `botL` arms) and confirm decidability type stability.

**Tasks**:
- [ ] `LJ/Interpolation.lean`: switch all 9 `botL` match arms to the `@`-pattern (+ `letI := inst`
      on any reconstruction).
- [ ] `LJ/Decidability.lean`: audit for type stability (no `botL` sites listed but it consumes
      `LJProof`); apply `@`-pattern only where a `botL` arm appears; otherwise confirm it builds
      unchanged against `LJProof = SeqProof IPL`.
- [ ] `lake build` both files to green.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` — 9 `botL` arms.
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` — type-stability audit.

**Verification**:
- `lake build` of both modules succeeds.
- Interpolation and decidability theorem signatures unchanged; no `sorry`/axiom.

---

### Phase 6: External consumer audit — `OrImpConservative.lean`, `ProofSystemEquivalence.lean` [NOT STARTED]

**Goal**: Keep the external public surface type-stable under `LJProof = SeqProof IPL`.

**Tasks**:
- [ ] `Semantics/Algebra/OrImpConservative.lean`: switch the 3 `botL` arms in the
      `induction dp : LJProof seq` block to the `@`-pattern; confirm `CutFreeLJProof`,
      `LJProof.cutElim`, `hilbert_iff_lj` usages still type-check (lines 35–184).
- [ ] `ProofSystemEquivalence.lean`: confirm `Nonempty (LJProof …)` in the TFAE (lines 84–105)
      still elaborates against the abbrev; no `botL` arms expected — audit only.
- [ ] `lake build` both files to green.

**Timing**: 1.5 hours

**Depends on**: 3, 4, 5

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` — 3 `botL` arms.
- `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` — type-stability audit.

**Verification**:
- `lake build` of both modules succeeds; no `sorry`/axiom.

---

### Phase 7: Full CI verification + LK regression check [NOT STARTED]

**Goal**: Confirm the whole tree is green, LK is untouched and intact, and zero debt was added.

**Tasks**:
- [ ] Full `lake build` (whole library) green.
- [ ] `lake test` (CslibTests) green.
- [ ] `lake exe checkInitImports`, `lake exe lint-style`, and
      `lake shake --add-public --keep-implied --keep-prefix` pass.
- [ ] Verify LK files (`LK/*`) unchanged and building; `LKProof`, `LKProof.cutElim`,
      `hilbert_iff_lk`, LK `CutFreeCompleteness` intact.
- [ ] Repository-wide `grep -rn "sorry\|admit\|axiom"` over touched files confirms zero debt.

**Timing**: 1 hour

**Depends on**: 6

**Files to modify**:
- None (verification only; minor import/barrel fixes in `SequentCalculus/LJ.lean` if needed).

**Verification**:
- All CI commands exit 0; no `sorry`/axiom anywhere in task scope; LK results preserved.

---

## Testing & Validation

- [ ] `lake build` green after each phase (per-file gate) and a full-library `lake build` in Phase 7.
- [ ] `lake test` passes (CslibTests suite).
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes.
- [ ] Preserved-signature spot check: `LJProof`, `CutFreeLJProof`, `LJCutFree`, `LJProof.height`,
      `LJProof.mono`, `LJProof.cutElim`, `ljCutAdmissibility`, `LJProof.sound`, `hilbert_iff_lj`,
      subformula property — all resolve with original public types.
- [ ] No `sorry`, no new axiom, no vacuous definition introduced (grep + `lean_verify` on key
      theorems if needed).
- [ ] LK unchanged: `LKProof`, `LKProof.cutElim`, `hilbert_iff_lk`, LK cut-free completeness intact.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/Defs.lean` (or new `SequentCalculus/Basic.lean`) — generic `SeqProof T` + fragment names + generic basic defs.
- Modified LJ files: `LJ/Basic.lean`, `LJ/CutElimination.lean`, `LJ/SubformulaProperty.lean`,
  `LJ/Soundness.lean`, `LJ/Completeness.lean`, `LJ/Interpolation.lean`, `LJ/Decidability.lean`.
- Modified consumers: `Semantics/Algebra/OrImpConservative.lean`, `ProofSystemEquivalence.lean`.
- `specs/408_minimal_sequent_calculus_lm/summaries/01_gated-botl-seqproof-summary.md` (on completion).

## Rollback/Contingency

- Each phase is a green-gated, file-scoped commit; revert the offending phase's commit to return to
  the last green state without losing earlier phases.
- If a specific cut-elimination `botL` arm resists the gate (none anticipated per research §3.1),
  mark Phase 2 `[BLOCKED]` for user review rather than introducing `sorry`; the documented FALLBACK
  (separate `LMProof` inductive) remains available only as a last resort.
- Since `LJProof` is an `abbrev` for `SeqProof IPL`, reverting the base definition cleanly restores
  the original per-system inductive if the unification must be abandoned.
