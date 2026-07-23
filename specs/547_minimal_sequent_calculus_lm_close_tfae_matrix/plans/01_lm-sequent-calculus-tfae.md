# Implementation Plan: Minimal Sequent Calculus (LM) and Three-Way MPL TFAE

- **Task**: 547 - minimal_sequent_calculus_lm_close_tfae_matrix
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/547_minimal_sequent_calculus_lm_close_tfae_matrix/reports/01_minimal-sequent-calculus-lm.md
- **Artifacts**: plans/01_lm-sequent-calculus-tfae.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/context/formats/plan-format.md
  - status-markers.md
  - artifact-management.md
  - tasks.md
- **Type**: cslib

## Overview

Close the `(SequentCalculus, Minimal)` hole in the proof-system × logic equivalence matrix by
building a thin LM sequent-calculus tree that reuses the already-generic `SeqProof T` machinery at
`T = MPL`, then extending the current two-way `mplHilbertIffNd` to a symmetric three-way
`mplProofSystemsTfae` (Hilbert ↔ ND ↔ LM). The research report established (with live
`lean_run_code` verification) that the minimal calculus rules already exist as
`SeqProofMinimal := SeqProof MPL` in `LJ/Basic.lean`, that `botL` is structurally unconstructible
at `MPL` (no `IsIntuitionistic ∅` instance), and that the semantic completeness backend and the
Hilbert–ND bridge already exist sorry-free. The new work is therefore three thin files
(`LM/Basic`, `LM/Soundness`, `LM/Completeness`, each bounded by its LJ counterpart), a barrel, and
the TFAE extension plus stale-docstring corrections. Definition of done: all new declarations
build with **zero sorry**, the full CSLib CI order passes, and `mplProofSystemsTfae` /
`mplProofSystemsTfaeClosed` are established.

### Research Integration

Report `01_minimal-sequent-calculus-lm.md` is fully integrated. Key findings drive the plan:
- **Reuse-first**: no new rule inductive; `abbrev LMProof := SeqProofMinimal` is a discoverability
  alias over the existing generic `SeqProof MPL`.
- **Two verified minimal-specific discharges**: `botL` case closed by
  `exact absurd (by assumption) not_isIntuitionistic_mpl`; `impR` over arbitrary `bot_forces`
  closed by `iforces_persistence v_uc bf_uc hw' (hant C hC)`. Both compiled live (report Section 6).
- **Path correction**: the TFAE file is `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`
  (NOT under `Metalogic/`); stale docstrings live at lines 19–20 and 116.
- **Reuse-verbatim backend**: `min_strong_completeness`, `min_soundness_completeness`,
  `hilbert_iff_nd_ctx_min` are sorry-free and consumed directly.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; ROADMAP alignment not evaluated in this
plan. The task itself is the roadmap item ("close the (SequentCalculus, Minimal) matrix hole"):
completing it makes the MPL row structurally symmetric with the CPL (`LK`) and IPL (`LJ`) rows.

## Goals & Non-Goals

**Goals**:
- Add `LM/Basic.lean` exposing `LMProof` and the reusable `not_isIntuitionistic_mpl` helper.
- Prove `SeqProofMinimal.sound` against minimal Kripke semantics with **arbitrary** upward-closed
  `bot_forces`, plus the `lm_msemantic_entails` corollary.
- Prove completeness: 8 `lmAxiom…` schemata, `lmOfMinAxiom`, `ndToLM`, and the bridges
  `nd_iff_lm`, `hilbert_iff_lm`, `lm_iff_mvalid`.
- Register `LM.lean` barrel; wire it into `SequentCalculus.lean` and `Cslib.lean` (via `mk_all`).
- Add `mplProofSystemsTfae` and `mplProofSystemsTfaeClosed`; fix stale docstrings (lines 19–20,
  116) in `ProofSystemEquivalence.lean`; retain `mplHilbertIffNd` for backward compatibility.
- Zero sorry, zero new axioms; full CI order passes.

**Non-Goals**:
- Tableau membership in the TFAE (owned by task 375) — MUST NOT add a 4th disjunct.
- `LM/CutElimination.lean`, `LM/SubformulaProperty.lean`, `LM/Interpolation.lean`,
  `LM/Decidability.lean` — not required for the TFAE; do not build.
- Renaming or removing `SeqProofMinimal`; it stays the canonical name with `LMProof` as an alias.
- Any PR creation or push (agents never push; task terminates at implementation complete).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `botL` induction case fails to discharge at `MPL` | H | L | Verified live in report Section 6 (`absurd (by assumption) not_isIntuitionistic_mpl`); if it regresses, escalate `[BLOCKED]`, never insert sorry. |
| `impR` case over arbitrary `bot_forces` mis-threads `bf_uc` | M | L | Verified live; LM version passes real `bf_uc` (strictly more uniform than LJ). Compare against `LJ/Soundness.lean:53` arm structure. |
| Linter failures (`docBlame`, `defLemma`, `unusedSectionVars`, `unusedDecidableInType`) | M | M | Docstring every new decl (LJ files are the template); `theorem` for Prop-valued, `def`/`noncomputable def` for proof-tree constructions; add `omit [DecidableEq Atom] in` where unused (report Section 7). |
| `shake`/`checkInitImports` flags import hygiene on new files | M | M | Copy the exact header block from LJ files; run `lake exe checkInitImports` and `lake shake --add-public --keep-implied --keep-prefix` before completion. |
| `mk_all --module` not run, leaving `Cslib.lean` unregistered | M | L | Explicit Phase 4 task; mirror LJ registration (currently lines 574–581). |
| A completeness arm unexpectedly needs `botL` | H | L | Report confirms only `ljAxiomEfq` and the ND `efq` case use `botL`, both dropped/discharged; if another arm needs it, escalate `[BLOCKED]`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each Lean
module imports the one before it, so no two phases share a wave.

### Phase 1: LM/Basic.lean — re-export and minimal-strength helper [COMPLETED]

- **Goal:** Create the `LM/` directory entry point that surfaces the mirror-symmetric surface name
  and the reusable non-intuitionistic-MPL lemma the soundness/completeness discharges depend on.
- **Tasks:**
  - [x] Create `Cslib/Logics/Propositional/SequentCalculus/LM/Basic.lean` with the standard CSLib
        header (Apache 2.0, Benjamin Brast-McKie), `import Cslib.Init`, `module`,
        `@[expose] public section`, copying the exact header block used by `LJ/Basic.lean`.
  - [x] Add `abbrev LMProof (seq : @Sequent Atom) : Type u := SeqProofMinimal seq` with docstring
        (discoverability alias over the existing generic `SeqProof MPL`).
  - [x] Add `theorem not_isIntuitionistic_mpl : ¬ Theory.IsIntuitionistic (∅ : Theory Atom)` with
        the report Section 6 proof body; apply `omit [DecidableEq Atom] in` (or `classical`) to
        silence `unusedSectionVars`/`unusedDecidableInType`.
  - [x] Optionally add `LMCutFree`/`CutFreeLMProof` re-exports only if trivially free (skip if they
        add lint surface without TFAE value). *(deviation: skipped -- not needed for TFAE, per
        plan's own "optionally" qualifier and Non-Goals scope guard)*
  - [x] Docstring every new declaration (`docBlame` is a weekly-cron lint; fix proactively).
- **Timing:** ~45 min
- **Depends on:** none
- **Files to create/modify:**
  - `Cslib/Logics/Propositional/SequentCalculus/LM/Basic.lean` — new file (~30 lines).
- **Verification:**
  - `lake build Cslib.Logics.Propositional.SequentCalculus.LM.Basic` succeeds, zero sorry.
  - `not_isIntuitionistic_mpl` typechecks; no linter warnings on the new file.

### Phase 2: LM/Soundness.lean — soundness against minimal Kripke semantics [COMPLETED]

- **Goal:** Prove `SeqProofMinimal.sound` generalizing `bot_forces` from `fun _ => False` to an
  arbitrary upward-closed `bf`, plus the `MSemanticEntails` corollary that feeds completeness/TFAE.
- **Tasks:**
  - [x] Create `Cslib/Logics/Propositional/SequentCalculus/LM/Soundness.lean` with standard header,
        importing `...LM.Basic` and the Kripke semantics / `SemanticConsequence` modules used by
        `LJ/Soundness.lean`.
  - [x] State and prove `SeqProofMinimal.sound` per report Section 5.1 (induction on the proof `d`):
        arms `ax, andL, andR, orL, orR1, orR2, impL, weakL, cut` transfer verbatim from
        `LJProof.sound` (`LJ/Soundness.lean:53`), threading the real `bf`/`bf_uc` in place of
        `fun _ => False`.
  - [x] Close the `impR` arm with `iforces_persistence v_uc bf_uc hw' (hant C hC)` (report Section 6).
  - [x] Close the `botL` arm with `exact absurd (by assumption) not_isIntuitionistic_mpl`.
  - [x] Add corollary `lm_msemantic_entails {Γ A} (d : SeqProofMinimal (Γ ⊢ A)) :
        MSemanticEntails (↑Γ) A` (mirror `lj_sound`), routing through
        `MSemanticEntails_of_MValid` where appropriate. *(deviation: altered -- proved directly via
        `d.sound` mirroring the inline `h_entail` pattern used in `nd_iff_lj`
        (`LJ/Completeness.lean:261`) rather than via `MSemanticEntails_of_MValid`, since the source
        is a proof tree, not an `MValid` fact; both routes are equivalent here)*
  - [x] Docstring every new declaration; use `theorem` for these Prop-valued results.
- **Timing:** ~75 min
- **Depends on:** 1
- **Files to create/modify:**
  - `Cslib/Logics/Propositional/SequentCalculus/LM/Soundness.lean` — new file (~100–156 lines,
    bounded by `LJ/Soundness.lean` at 156).
- **Verification:**
  - `lake build …LM.Soundness` succeeds, zero sorry.
  - `SeqProofMinimal.sound` and `lm_msemantic_entails` typecheck; no linter warnings.

### Phase 3: LM/Completeness.lean — axiom proofs, ND→LM, and bridges [NOT STARTED]

- **Goal:** Establish completeness for LM: 8 minimal axiom proof-trees, the axiom dispatch, the
  ND→LM translation, and the `nd_iff_lm` / `hilbert_iff_lm` / `lm_iff_mvalid` bridges.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LM/Completeness.lean` with standard
        header, importing `...LM.Soundness`, the `Metalogic` completeness backend
        (`min_strong_completeness`, `min_soundness_completeness`), and the Hilbert–ND bridge
        (`hilbert_iff_nd_ctx_min`).
  - [ ] Port the 8 `lmAxiom…` schemata mirroring `ljAxiom…` (`LJ/Completeness.lean:71–167`):
        `implyK, implyS, andI, andE1, andE2, orI1, orI2, orE`. **Drop `ljAxiomEfq`** (uses `botL`).
        Keep as `def`/`noncomputable def` (Type-valued proof-tree constructions).
  - [ ] Add `lmOfMinAxiom : MinPropAxiom φ → Nonempty (SeqProofMinimal (Γ ⊢ φ))` mirroring
        `ljOfIntAxiom` with 8 cases (no `efq` case).
  - [ ] Add `ndToLM` (mirror `ndToLJ`, `LJ/Completeness.lean:193`): arms
        `ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE` transfer directly; the `efq`
        arm is discharged via `absurd` on the uninhabited `[IsIntuitionistic (AxiomTheory
        MinPropAxiom)]`. Mark `noncomputable` (Prop-valued axioms → `Classical.choice`).
  - [ ] Add `nd_iff_lm` (→ via `ndToLM`; ← via `SeqProofMinimal.sound → MSemanticEntails →
        min_strong_completeness → SetDerivable MinPropAxiom → (rw ← hilbert_iff_nd_ctx_min) →
        weakening`), `hilbert_iff_lm := hilbert_iff_nd_ctx_min.trans nd_iff_lm`, and
        `lm_iff_mvalid`.
  - [ ] Docstring every new declaration; `theorem` for the Prop-valued bridges, `def`/`noncomputable
        def` for the proof-tree constructions (`defLemma` compliance).
- **Timing:** ~90 min
- **Depends on:** 1, 2
- **Files to create/modify:**
  - `Cslib/Logics/Propositional/SequentCalculus/LM/Completeness.lean` — new file (~200–312 lines,
    bounded by `LJ/Completeness.lean` at 312).
- **Verification:**
  - `lake build …LM.Completeness` succeeds, zero sorry.
  - `nd_iff_lm`, `hilbert_iff_lm`, `lm_iff_mvalid` typecheck; no linter warnings.

### Phase 4: Barrel registration + three-way TFAE + docstring fixes [NOT STARTED]

- **Goal:** Wire the new modules into the build, extend the equivalence matrix with the three-way
  MPL TFAE, correct the stale docstrings, and pass the full CI order.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LM.lean` barrel (mirror `LJ.lean`),
        with `public import` of `...LM.Basic`, `...LM.Soundness`, `...LM.Completeness`.
  - [ ] Add `public import Cslib.Logics.Propositional.SequentCalculus.LM` to
        `Cslib/Logics/Propositional/SequentCalculus.lean`.
  - [ ] In `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`: add
        `public import Cslib.Logics.Propositional.SequentCalculus.LM.Completeness`; add
        `mplProofSystemsTfae` (tfae 1↔2 via `hilbert_iff_nd_ctx_min`, 2↔3 via `nd_iff_lm`,
        `tfae_finish`) and `mplProofSystemsTfaeClosed` per report Section 5.3; **retain**
        `mplHilbertIffNd`.
  - [ ] Fix stale docstrings: lines 19–20 (module docstring "no minimal sequent calculus exists")
        and line 116 (the `mplHilbertIffNd` docstring); update the "Main Results" list to mention
        `mplProofSystemsTfae`/`mplProofSystemsTfaeClosed`.
  - [ ] Run `lake exe mk_all --module` to register the new files in `Cslib.lean`
        (mirror LJ registration).
  - [ ] Docstring every new theorem.
  - [ ] Run the full CI order: `lake exe cache get` → `lake build` →
        `lake exe checkInitImports` → `lake lint` → `lake exe lint-style` →
        `lake exe mk_all --module` → `lake shake --add-public --keep-implied --keep-prefix`.
        Fix any issues fix-forward (never discard uncommitted work; never insert sorry).
- **Timing:** ~60 min
- **Depends on:** 1, 2, 3
- **Files to create/modify:**
  - `Cslib/Logics/Propositional/SequentCalculus/LM.lean` — new barrel.
  - `Cslib/Logics/Propositional/SequentCalculus.lean` — add LM import.
  - `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` — TFAE theorems + docstring fixes.
  - `Cslib.lean` — regenerated by `mk_all --module`.
- **Verification:**
  - `mplProofSystemsTfae` and `mplProofSystemsTfaeClosed` typecheck; zero sorry across all new decls.
  - Full CI order passes clean.
  - Stale docstrings (lines 19–20, 116) no longer claim absence of a minimal sequent calculus.

## Testing & Validation

- [ ] `lake build` of the whole `Cslib.Logics.Propositional.SequentCalculus.LM` tree succeeds.
- [ ] Zero `sorry` and zero new `axiom` in all new declarations (grep the new files; use
      `lean_verify` / `#print axioms` on `mplProofSystemsTfae` to confirm no unexpected axioms
      beyond `Classical.choice`/`propext`/`Quot.sound`).
- [ ] `SeqProofMinimal.sound`, `lm_msemantic_entails`, `nd_iff_lm`, `hilbert_iff_lm`,
      `lm_iff_mvalid` all typecheck.
- [ ] `mplProofSystemsTfae Γ φ` and `mplProofSystemsTfaeClosed φ` established.
- [ ] Full CI order passes: `lake exe cache get` → `lake build` → `lake exe checkInitImports` →
      `lake lint` → `lake exe lint-style` → `lake exe mk_all --module` →
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `mplHilbertIffNd` still compiles (backward compatibility preserved).
- [ ] No tableau disjunct added to any MPL TFAE (scope guard for task 375 respected).

## Artifacts & Outputs

- `plans/01_lm-sequent-calculus-tfae.md` (this file)
- `Cslib/Logics/Propositional/SequentCalculus/LM/Basic.lean` (new)
- `Cslib/Logics/Propositional/SequentCalculus/LM/Soundness.lean` (new)
- `Cslib/Logics/Propositional/SequentCalculus/LM/Completeness.lean` (new)
- `Cslib/Logics/Propositional/SequentCalculus/LM.lean` (new barrel)
- Modified: `Cslib/Logics/Propositional/SequentCalculus.lean`,
  `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`, `Cslib.lean` (via `mk_all`)
- `summaries/01_lm-sequent-calculus-tfae-summary.md` (produced at implementation completion)

## Rollback/Contingency

- All new work is additive (new files + additive edits to two barrels and the TFAE module).
  Reverting is safe: remove the three `LM/*.lean` files and `LM.lean`, revert the `SequentCalculus.lean`
  import, revert the `ProofSystemEquivalence.lean` additions and docstring edits, and re-run
  `lake exe mk_all --module` to regenerate `Cslib.lean`.
- Zero-debt gate: if any proof arm unexpectedly fails to close (e.g. a `botL`-dependent obligation
  surfaces where the report predicted none), escalate the task to `[BLOCKED]` with the failing goal
  state recorded — do NOT insert `sorry` or a placeholder axiom to reach a green build.
- Follow the recovery ladder in `.claude/context/contracts/recovery.md` (fix-forward first); never
  use destructive git on uncommitted work to reach a passing build.
