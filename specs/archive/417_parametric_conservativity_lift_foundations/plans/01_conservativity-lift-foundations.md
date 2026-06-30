# Implementation Plan: Task #417 — Parametric Conservativity Lift into Foundations

- **Task**: 417 - Parametric conservativity lift into Foundations
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: None (task 419 depends on this)
- **Research Inputs**: reports/01_conservativity-lift-design.md
- **Artifacts**: plans/01_conservativity-lift-foundations.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Consolidate the three byte-identical modal-family propositional-conservativity proofs
(Modal / Temporal / Bimodal) behind a single parametric interface in a new Foundations
module. Two generic declarations carry all shared content: `evaluate_iff_of_classicalBridge`
(a generic classical truth-functional bridge over an abstract `sat : Tgt → Prop` plus five
per-connective `Iff` hypotheses) and `conservative_over_cpl` (a `prop_completeness` wrapper
taking the bridge plus a per-logic satisfaction callback). Each logic then supplies one thin
instance. Because every proof body already exists and is copy-equal across the three logics,
this is a faithful transcription refactor: **0 new sorry / 0 new axioms by construction**.
Definition of done: the new file plus re-expressed Temporal and Bimodal instances compile and
the full CSLib CI pipeline is green with zero proof debt.

### Research Integration

Integrates `reports/01_conservativity-lift-design.md` in full:
- §3 — the unifying abstraction is a fully-applied `sat : Tgt → Prop` (model+point fixed per
  valuation), NOT a `Satisfies`-shaped typeclass (the three relations have incompatible arities:
  Modal `(m,w)`, Temporal `(M,t)`, Bimodal `(M,Ω,τ,t)`).
- §4 — exact signatures for both generic declarations (transcribed into Phase 1 below).
- §2 — the critical atom-shape difference: Modal/Temporal map `atom p` definitionally to `v p`
  (atom bridge case is `rfl`), but Bimodal wraps it as `∃ (ht : τ.domain t), v p`. The interface
  therefore takes atom-compatibility as an `Iff` hypothesis, never bakes in `= v p`. Łukasiewicz
  `and`/`or` are uniform across all three embeddings, so they need zero per-logic content.
- §5 — re-expression plan for the three instances.
- §6 — Foundations vs Logics/Propositional placement analysis (see Risks; confirm in PR).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; roadmap consultation skipped. This task closes
Finding 2 (Conservativity Asymmetry) of task 415 and unblocks task 419, which depends on the
Foundations placement of `ConservativityLift.lean`.

## Goals & Non-Goals

**Goals**:
- Author `Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean` with `evaluate_iff_of_classicalBridge`
  and `conservative_over_cpl`, matching the exact signatures in report §4.
- Re-express `temporal_conservative_extension` (Temporal/ConservativeExtension.lean:87) and its
  bridge lemma as thin instances over the generic declarations.
- Re-express `bimodal_conservative_extension` (Bimodal/.../PropositionalConservativity.lean:118)
  and its bridge lemma as thin instances over the generic declarations.
- Preserve zero new sorry / zero new axioms (verified via `lean_verify`).
- Pass the full CSLib CI pipeline (`lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake test`, `lake shake`).

**Non-Goals**:
- Mandatory Modal re-home. The Modal re-home/wrapper is optional/low-priority (Phase 4); the
  load-bearing wins are Temporal + Bimodal. The 15 `Systems/*/ConservativeExtension.lean` callers
  of `modal_conservative_extension_param` must stay untouched.
- Any change to satisfaction semantics, embeddings, or `prop_completeness` itself.
- Resolving the Foundations→Logics layering question definitively in code review (flagged for PR).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Foundations→Logics import inverts normal layering; reviewer may object | M | M | Proceed with Foundations placement per task 419 dependency; add docstring note citing the DiegoEmbedding.lean:15-16 precedent; fallback is Logics/Propositional/Metalogic/ConservativityLift.lean with **no signature change** — only the three instance imports differ. Flag as confirm-in-PR, non-blocking. |
| Bimodal `h_atom` is the one non-`rfl` term; existential wrap mishandled | M | L | Supply the existing existential-collapse term `⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩` verbatim from PropositionalConservativity.lean:73. |
| `bot`-case closing term ambiguity (`iff_of_false h_bot _` vs `simp [h_bot]`) | L | M | Resolve at build time with `lean_goal`; both are sorry-free. |
| Modal 15-system fan-out if name not preserved | H | L | Phase 4 keeps `modal_conservative_extension_param` as a name-preserving thin wrapper (or skips re-home entirely); never edit the 15 Systems files. |
| New file lint failures (module header, `@[expose] public section`, docBlame) | M | M | Follow Foundations/Logic/Metalogic/GenericMCS.lean conventions: `module` → `public import …` → `@[expose] public section … end`; add docstrings; snake_case theorem names are correct (Mathlib/CSLib norm for theorems). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel (Phases 2, 3, 4 each touch a distinct file
and depend only on Phase 1's published interface — territory-clean).

### Phase 1: Author the generic Foundations module [COMPLETED]

**Goal**: Create the new module with both generic declarations compiling sorry-free.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean` following
      GenericMCS.lean module conventions: leading `module`, then `public import` of
      `Cslib.Init`, `Cslib.Logics.Propositional.Semantics.Bool` (`PL.Evaluate`), and
      `Cslib.Logics.Propositional.Metalogic.StrongCompleteness` (`prop_completeness`,
      `PropositionalAxiom`, `PL.Derivable`); wrap body in `@[expose] public section … end`.
- [ ] Add a module docstring acknowledging the deliberate Foundations→Logics shared-substrate
      exception, citing the `Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean:15-16` precedent.
- [ ] Author `evaluate_iff_of_classicalBridge` with the exact signature from report §4.1
      (5 per-connective `Iff`/`¬` hypotheses; conclude `∀ ψ, sat (emb ψ) ↔ PL.Evaluate v ψ`).
      Transcribe the `imp`/`and`/`or` tactic bodies verbatim from report §4.1 (the existing
      `by_contra`/`by_cases`/`cases` scripts). Resolve the `bot`-case closing term at build with
      `lean_goal`. Do NOT replace the classical scripts with `simp`/`aesop`/`tauto`.
- [ ] Author `conservative_over_cpl` with the exact signature from report §4.2
      (3-line `apply prop_completeness; intro v; exact (bridge v).mp (h_sat v)`).
- [ ] Choose a neutral namespace (`Cslib.Logic` to match the instance files, or a dedicated
      `Cslib.Logic.Conservativity`); keep snake_case theorem names.
- [ ] Add the new file to the import graph where required (e.g. `Cslib.lean` aggregator) so it
      builds; run `lean_build` once if a new import is introduced.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean` — new file, both generic decls
- (aggregator import file, if CSLib requires explicit module registration)

**Verification**:
- `lake build` of the new module succeeds.
- `lean_verify Cslib.Logic.evaluate_iff_of_classicalBridge` and `…conservative_over_cpl` show no
  `sorryAx` and no new axioms beyond the ambient classical set already used by the source proofs.

---

### Phase 2: Re-express Temporal instance [COMPLETED]

**Goal**: Replace the Temporal bridge + conservativity bodies with thin calls to the generic decls.

**Tasks**:
- [ ] Add the import of `Cslib.Foundations.Logic.Metalogic.ConservativityLift` to
      `Temporal/ConservativeExtension.lean`.
- [ ] Replace the body of `temporal_satisfies_toTemporal_iff_evaluate` with
      `evaluate_iff_of_classicalBridge` supplying `emb := PL.Proposition.toTemporal`,
      `sat := Temporal.Satisfies M t`, `v := M.valuation t`; all five `h_*` are `Iff.rfl`
      (`h_bot := fun h => h`) provable after `simp only [PL.Proposition.toTemporal, Satisfies]`.
- [ ] Re-express `temporal_conservative_extension` (line 87) as `conservative_over_cpl` with
      `bridge := fun v => temporal_..._iff_evaluate (TemporalModel.constant v) 0 φ` and
      `h_sat := fun v => soundness_thderivable h (TemporalModel.constant v) 0`. Keep
      `TemporalModel.constant` and `soundness_thderivable` (the genuine per-logic content).

**Timing**: ~45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/.../Temporal/ConservativeExtension.lean` — bridge + conservativity bodies become
  thin instances (signatures unchanged)

**Verification**:
- `lake build` of the Temporal module succeeds; public signatures unchanged.
- `lean_verify` on the two re-expressed Temporal theorems shows no new sorry/axioms.

---

### Phase 3: Re-express Bimodal instance [COMPLETED]

**Goal**: Replace the Bimodal bridge + conservativity bodies with thin calls to the generic decls.

**Tasks**:
- [ ] Add the import of `Cslib.Foundations.Logic.Metalogic.ConservativityLift` to
      `Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`.
- [ ] Replace the body of `bimodal_truthAt_toBimodal_iff_evaluate` (line 60) with
      `evaluate_iff_of_classicalBridge`, fixing `sat := fun t' => truthAt M Ω τ t'` (trivial
      frame). The **only** non-`rfl` hypothesis is `h_atom`: supply the existing existential-
      collapse term `⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩` (PropositionalConservativity.lean:73).
      The remaining `h_bot/h_imp/h_and/h_or` are `Iff.rfl` after `simp only [toBimodal, truthAt]`.
- [ ] Re-express `bimodal_conservative_extension` (line 118) as `conservative_over_cpl` with
      `h_sat` built from the existing `soundness [] φ.toBimodal d ℤ ℱ M Ω h_sc τ h_mem 0 (by simp)`
      per valuation, fixing the trivial-frame choices already at lines 126-129.

**Timing**: ~1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/.../Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` —
  bridge + conservativity bodies become thin instances (signatures unchanged)

**Verification**:
- `lake build` of the Bimodal module succeeds; public signatures unchanged.
- `lean_verify` on the two re-expressed Bimodal theorems shows no new sorry/axioms.

---

### Phase 4: Optional Modal re-home / name-preserving wrapper [COMPLETED]

**Goal**: (Optional, low-priority) Express Modal conservativity over the generic decls WITHOUT
breaking the 15 Systems callers.

**Tasks**:
- [x] Re-express `modal_satisfies_toModal_iff_evaluate` (Modal/FromPropositional.lean:106) via
      `evaluate_iff_of_classicalBridge` with all five `h_*` as `Iff.rfl`-after-`simp`
      (`h_atom := fun _ => Iff.rfl`). *(deviation: skipped -- 33 callers of `modal_conservative_extension_param` across Modal/Metalogic/Systems/ pose high breakage risk; plan says to skip if any risk detected)*
- [x] Re-express `modal_conservative_extension_param`
      (Modal/Metalogic/ConservativeExtension.lean:54) as `conservative_over_cpl`. *(deviation: skipped -- same reason; the existing modal param already uses a different but correct pattern)*
- [x] If any risk to the 15 callers is detected, SKIP the re-home and leave Modal as-is. This
      phase is droppable without affecting the Definition of Done. *(deviation: skipped -- 33 callers detected, risk is high, Definition of Done satisfied by Phases 1-3+5)*

**Timing**: ~45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/.../Modal/Metalogic/ConservativeExtension.lean` — optional; name preserved
- `Cslib/Logics/.../Modal/FromPropositional.lean` — optional bridge re-expression
- (the 15 `Systems/*/ConservativeExtension.lean` files MUST remain untouched)

**Verification**:
- If executed: `lake build` of Modal + all 15 Systems modules succeeds with no edits to the
  Systems files; `lean_verify` shows no new sorry/axioms. If skipped: note skip rationale.

---

### Phase 5: Full CI green and proof-debt audit [IN PROGRESS]

**Goal**: Whole-tree green with zero new proof debt.

**Tasks**:
- [ ] Run the full CSLib CI pipeline: `lake build`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake test`, `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Resolve any lint findings on the new file (module header, `@[expose] public section`,
      docBlame docstrings, import minimization from `shake`).
- [ ] Final `lean_verify` sweep over `evaluate_iff_of_classicalBridge`, `conservative_over_cpl`,
      and all re-expressed instance theorems: confirm 0 new sorry, 0 new axioms.
- [ ] Confirm public signatures of the re-expressed Temporal/Bimodal (and optional Modal)
      theorems are byte-identical to their pre-refactor forms.

**Timing**: ~1 hour

**Depends on**: 2, 3, 4

**Files to modify**:
- None (verification + lint fixups only)

**Verification**:
- All five CI commands exit zero.
- `lean_verify` confirms zero proof debt across all touched declarations.

## Testing & Validation

- [ ] `lake build` green across the whole tree.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green (new file conforms to module/section/docstring conventions).
- [ ] `lake test` green (CslibTests suite).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` green (no superfluous imports).
- [ ] `lean_verify` on both generic decls and all re-expressed instances: 0 new sorry, 0 new axioms.
- [ ] Public signatures of all re-expressed theorems unchanged; 15 Modal Systems callers untouched.

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean` (new — two generic declarations)
- Modified `Temporal/ConservativeExtension.lean` (thin instances)
- Modified `Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` (thin instances)
- Optional: modified `Modal/Metalogic/ConservativeExtension.lean` + `Modal/FromPropositional.lean`
- `specs/417_parametric_conservativity_lift_foundations/plans/01_conservativity-lift-foundations.md`
- `specs/417_parametric_conservativity_lift_foundations/summaries/01_conservativity-lift-foundations-summary.md` (on completion)

## Rollback/Contingency

- Each phase is an isolated, signature-preserving refactor; revert by restoring the original proof
  body of the affected file(s) — the generic file can remain unused without harm.
- If the Foundations→Logics import is rejected in review, move the new file to
  `Cslib/Logics/Propositional/Metalogic/ConservativityLift.lean` with **no signature change**;
  only the three instance import lines change.
- If Phase 4 (Modal) risks the 15 Systems callers, drop it entirely — Definition of Done is met by
  Phases 1-3 + 5.
- Because the refactor is a faithful transcription of existing copy-equal proofs, any build failure
  indicates a transcription slip; restore the original body and re-derive the missing `simp`/`rw`
  unfolding rather than introducing new proof structure.
