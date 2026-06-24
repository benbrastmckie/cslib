# Implementation Plan: Parametric Modal Conservative Extension

- **Task**: 337 - parametric_modal_conservative_extension
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: Task 335 (soundness refactor, complete) — provides the `*_soundness` wrappers reused as callbacks
- **Research Inputs**: specs/337_parametric_modal_conservative_extension/reports/01_parametric-conservative-extension.md
- **Artifacts**: plans/01_parametric-conservative-extension.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; .claude/rules/artifact-formats.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Extract a single parametric conservative-extension theorem `modal_conservative_extension_param`
into a new file `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean`, then rewrite the 15
near-identical `Systems/*/ConservativeExtension.lean` files (896 lines total) to ~5-line
instantiations that supply only their system-specific `*_soundness` term as an opaque
satisfaction callback. The research report contains a BUILD-VERIFIED parametric design (compiled
with S5/D/K instantiations) and the complete per-system frame-condition discharge table. This is
a pure, mechanical refactor with zero new proof obligations and zero `sorry` risk; the parametric
theorem factors out the shared `prop_completeness`/Unit-model/bridge-lemma boilerplate, and each
system retains only its `*_soundness …` call. Definition of done: the new theorem builds, all 15
public theorem names are preserved (`<sys>_conservative_extension`, and `modal_conservative_extension`
for K), the full CI pipeline passes, and net reduction reaches the ~400-line target.

### Research Integration

The plan integrates the report's findings directly:
- **Parametric theorem signature** (report lines 96-106): takes `{Axioms : Modal.Proposition Atom → Prop}`,
  the derivability hypothesis `h`, and a callback `h_sat : ∀ v, Modal.Satisfies (universal model) () φ.toModal`.
- **Callback design rationale** (report lines 111-119): the 15 `*_soundness` wrappers have
  heterogeneous 0-3 frame-condition signatures (seriality is a `Relation.Serial` instance), so the
  theorem MUST take the already-discharged satisfaction term as a callback — it must NOT attempt to
  parameterize over named frame conditions.
- **Frame-Condition Discharge Table** (report lines 61-89): the per-system specification for all 15
  instantiations, reproduced in Phase 3 below.
- **Reuse** (report lines 29-31): `modal_satisfies_toModal_iff_evaluate` and `prop_completeness` are
  reused directly; no new Mathlib lemmas.
- **File plan** (report lines 159-171): new Metalogic file + 15 rewrites + `mk_all` barrel update.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Add `modal_conservative_extension_param` to a new `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean`.
- Rewrite all 15 `Systems/*/ConservativeExtension.lean` files as ~5-line instantiations.
- Preserve every public theorem name exactly: `<sys>_conservative_extension` for 14 systems and
  `modal_conservative_extension` for K (note: K's theorem is NOT named `k_conservative_extension`).
- Achieve ~400+ line net reduction (896 → roughly 220 lines plus the ~40-line shared theorem).
- Pass the full CSLib CI pipeline (lake build, lake test, checkInitImports, lint-style, shake).

**Non-Goals**:
- No change to any `*_soundness` wrapper, `FromPropositional`, or `StrongCompleteness`.
- No change to `InterSystem/Conservativity.lean` (unrelated — modal-cube monotonicity).
- No new abstractions beyond the single parametric theorem.
- No renaming of public theorems (statements are preserved verbatim).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| K's distinct proof style (uses `toModal_valid_implies_tautology`, not the Unit model) fails to fit the callback | M | L | Report verified `k_test` fits via `k_soundness d _ () (...)`; build K instantiation first as the canary in Phase 3, before the bulk rewrite |
| A `*_soundness` callback signature mismatch (wrong frame-condition arg order) | M | L | Follow the Frame-Condition Discharge Table exactly; verify each file with per-file `lake build` reading errors via lean-lsp diagnostics |
| Missing barrel import / new file not in `Cslib.lean` | M | M | Run `lake exe mk_all --module` (or update `Cslib.lean` manually) in Phase 4 and confirm with `lake exe checkInitImports` |
| `module`/`public import` header convention mismatch in new file | L | L | Copy the exact header block from an existing sibling (e.g. S5's CE file); `module` then `public import …` |
| Benign `unused binder name` linter warning on callback type | L | M | Name the callback's bound valuation `_` (per report line 155); confirm lint-style is clean |
| Downstream module depends on a concrete proof term rather than the statement | H | VL | Already verified by grep: only `Systems/*/` define these; `bimodal_conservative_extension` is unrelated. Statements are preserved, so no downstream break |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are sequential (each builds on a verified prior state). Within Phase 3 the 15 file rewrites
are independent of one another, but they all depend on the Phase 2 parametric theorem and are
verified together by a single full build.

### Phase 1: Pre-flight Verification and Baseline [COMPLETED]

- **Goal:** Establish a green baseline and confirm the facts the rewrite depends on, before any edit.
- **Tasks:**
  - [ ] Confirm clean working tree / note current state for the 15 target files.
  - [ ] Run `lake build` on the Modal metalogic to confirm a green baseline (or capture the
        current build state if a full build is too slow — scope to
        `Cslib.Logics.Modal.Metalogic.Systems.S5.ConservativeExtension` and K).
  - [ ] Re-confirm theorem names per file: 14 are `<sys>_conservative_extension`; K is
        `modal_conservative_extension`. Record the exact name for each of the 15 files.
  - [ ] Confirm no external module references the concrete proof terms:
        `grep -rn "conservative_extension" Cslib/ --include=*.lean | grep -v "/Systems/" | grep -v "Bimodal" | grep -v "Temporal"`.
  - [ ] Confirm the new file path `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean` does
        not already exist.
- **Timing:** 20 minutes
- **Depends on:** none
- **Files to modify:** none (read-only verification)
- **Verification:** Baseline build is green (at least for the canary modules); name map recorded;
  grep confirms no external dependents.

### Phase 2: Add the Parametric Theorem [COMPLETED]

- **Goal:** Create `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean` containing
  `modal_conservative_extension_param`, and verify it builds in isolation.
- **Tasks:**
  - [ ] Create the new file with the standard CSLib header: copyright block, `module`, then
        `public import Cslib.Logics.Modal.FromPropositional`,
        `public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness`, and
        `public import Cslib.Logics.Modal.Metalogic.DerivationTree` (per report file plan).
  - [ ] Add module docstring (`/-! … -/`), `@[expose] public section`, `namespace Cslib.Logic`,
        `open PL Cslib.Logic.Modal`.
  - [ ] Add the theorem (verbatim from report lines 96-106), with a `/-- … -/` docstring (docBlame):
        ```lean
        theorem modal_conservative_extension_param {Atom : Type*}
            {Axioms : Modal.Proposition Atom → Prop} {φ : PL.Proposition Atom}
            (h : Derivable Axioms φ.toModal)
            (h_sat : ∀ (v : Atom → Prop),
              Modal.Satisfies (⟨fun _ _ => True, fun _ => v⟩ : Modal.Model Unit Atom) () φ.toModal) :
            PL.Derivable PropositionalAxiom φ := by
          apply prop_completeness; intro v
          exact (modal_satisfies_toModal_iff_evaluate _ () φ).mp (h_sat v)
        ```
  - [ ] Resolve the benign `unused binder name` warning (name the callback's bound valuation `_`
        where applicable; ensure no shadowed `h`).
  - [ ] Build the new file: `lake build Cslib.Logics.Modal.Metalogic.ConservativeExtension`.
- **Timing:** 25 minutes
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean` — new file, parametric theorem.
- **Verification:** `lake build Cslib.Logics.Modal.Metalogic.ConservativeExtension` succeeds with
  zero errors; lean-lsp diagnostics show no warnings beyond (at most) a resolved binder note.

### Phase 3: Rewrite the 15 System Instantiations [COMPLETED]

- **Goal:** Replace each `Systems/*/ConservativeExtension.lean` proof body with a ~5-line
  instantiation of `modal_conservative_extension_param`, preserving the public theorem name and
  statement, and adding the import of the new Metalogic file.
- **Tasks:**
  - [ ] **Canary first — K**: rewrite `Systems/K/ConservativeExtension.lean` (theorem
        `modal_conservative_extension`) using `k_soundness d _ () (fun _ h => nomatch h)` in the
        callback. Build it alone and confirm green before touching the others (K is the only file
        with a distinct original proof style).
  - [ ] Rewrite the remaining 14 files per the Frame-Condition Discharge Table below. For each
        file: keep the existing imports (`FromPropositional`, that system's `Soundness`,
        `StrongCompleteness`), add `public import Cslib.Logics.Modal.Metalogic.ConservativeExtension`,
        preserve the docstring/header, and replace the body with the instantiation pattern
        (report lines 124-131):
        ```lean
        theorem <name> {Atom : Type*} {φ : PL.Proposition Atom}
            (h : Derivable (@<Sys>Axiom Atom) φ.toModal) :
            PL.Derivable PropositionalAxiom φ :=
          modal_conservative_extension_param h fun _ => by
            obtain ⟨d⟩ := h
            exact <sys>_soundness d _ <FRAME-CONDITIONS> () (fun _ h => nomatch h)
        ```
  - [ ] **Frame-Condition Discharge Table** (the only per-file variation):

        | System | Axiom | Theorem name | `*_soundness` frame-condition args (in order) |
        |--------|-------|--------------|-----------------------------------------------|
        | K | `KAxiom` | `modal_conservative_extension` | *(none)* — `k_soundness d _ () (…)` |
        | T | `TAxiom` | `t_conservative_extension` | refl `fun _ => trivial` |
        | D | `DAxiom` | `d_conservative_extension` | serial instance `⟨fun w => ⟨w, trivial⟩⟩` |
        | B | `BAxiom` | `b_conservative_extension` | symm `fun _ _ _ => trivial` |
        | D4 | `D4Axiom` | `d4_conservative_extension` | serial `⟨fun w => ⟨w, trivial⟩⟩`, trans `fun _ _ _ _ _ => trivial` |
        | D5 | `D5Axiom` | `d5_conservative_extension` | serial `⟨fun w => ⟨w, trivial⟩⟩`, eucl `fun _ _ _ _ _ => trivial` |
        | K4 | `K4Axiom` | `k4_conservative_extension` | trans `fun _ _ _ _ _ => trivial` |
        | K5 | `K5Axiom` | `k5_conservative_extension` | eucl `fun _ _ _ _ _ => trivial` |
        | K45 | `K45Axiom` | `k45_conservative_extension` | trans `…`, eucl `…` |
        | D45 | `D45Axiom` | `d45_conservative_extension` | serial `⟨fun w => ⟨w, trivial⟩⟩`, trans `…`, eucl `…` |
        | DB | `DBAxiom` | `db_conservative_extension` | serial `⟨fun w => ⟨w, trivial⟩⟩`, symm `fun _ _ _ => trivial` |
        | TB | `TBAxiom` | `tb_conservative_extension` | refl `fun _ => trivial`, symm `fun _ _ _ => trivial` |
        | S4 | `S4Axiom` | `s4_conservative_extension` | refl `fun _ => trivial`, trans `fun _ _ _ _ _ => trivial` |
        | S5 | `ModalAxiom` | `s5_conservative_extension` | refl `fun _ => trivial`, trans `…`, eucl `…` |
        | KB5 | `KB5Axiom` | `kb5_conservative_extension` | symm `fun _ _ _ => trivial`, eucl `fun _ _ _ _ _ => trivial` |

        Frame-condition arg shapes: refl `fun _ => trivial`; trans/eucl `fun _ _ _ _ _ => trivial`;
        symm `fun _ _ _ => trivial`; seriality is a `Relation.Serial` instance `⟨fun w => ⟨w, trivial⟩⟩`.
  - [ ] After each batch (or each file), capture lean-lsp diagnostics to catch arg-order mismatches early.
- **Timing:** 60 minutes
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Systems/{K,T,D,B,D4,D5,K4,K5,K45,D45,DB,TB,S4,S5,KB5}/ConservativeExtension.lean`
    — 15 files, each rewritten to a ~5-line instantiation with the new import added.
- **Verification:** Each rewritten file builds; theorem names and statements unchanged
  (`grep -oh "theorem [a-z_0-9]*conservative_extension"` matches the recorded name map from Phase 1).

### Phase 4: Barrel Update, Full CI, and Reduction Check [COMPLETED]

- **Goal:** Register the new file in the barrel, run the full CSLib CI pipeline green, and confirm
  the line-reduction target.
- **Tasks:**
  - [ ] Add the new module to the barrel: run `lake exe mk_all --module` (preferred) OR manually
        insert `public import Cslib.Logics.Modal.Metalogic.ConservativeExtension` into `Cslib.lean`
        in correct sorted position (near the existing `Modal.Metalogic` imports).
  - [ ] `lake build` — full library build green.
  - [ ] `lake test` — CslibTests suite passes.
  - [ ] `lake exe checkInitImports` — Cslib.Init imports verified.
  - [ ] `lake exe lint-style` — style linting clean (confirm no leftover `unused binder` or docBlame).
  - [ ] `lake shake --add-public --keep-implied --keep-prefix` — dependency analysis clean (no
        unused imports left in the rewritten files; e.g. a system no longer needing
        `toModal_valid_implies_tautology` should not import it spuriously).
  - [ ] Measure net reduction: `wc -l` over the 15 files + the new file vs the 896-line baseline;
        confirm ~400+ line reduction.
- **Timing:** 25 minutes
- **Depends on:** 3
- **Files to modify:**
  - `Cslib.lean` — add the new barrel import (if `mk_all` does not handle it).
- **Verification:** All five CI commands pass; net reduction meets the ~400-line target; no `sorry`
  anywhere (`grep -rn "sorry" Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean Cslib/Logics/Modal/Metalogic/Systems/*/ConservativeExtension.lean` returns nothing).

## Testing & Validation

- [ ] `lake build` — full build green (new file + 15 rewrites).
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — init imports verified.
- [ ] `lake exe lint-style` — no style violations (docBlame, unused binder all clean).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports.
- [ ] All 15 public theorem names preserved (14 `<sys>_conservative_extension`, K `modal_conservative_extension`).
- [ ] Zero `sorry` in any touched file.
- [ ] Net line reduction ≥ ~400 lines vs the 896-line baseline.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean` — new parametric theorem (~40 lines).
- 15 rewritten `Cslib/Logics/Modal/Metalogic/Systems/*/ConservativeExtension.lean` files (~5-line bodies).
- `Cslib.lean` — one added barrel import.
- specs/337_parametric_modal_conservative_extension/summaries/01_parametric-conservative-extension-summary.md (on completion).

## Rollback/Contingency

- The change is uniform and confined to 16 Lean files plus one barrel line. If CI fails and cannot
  be fixed within the phase, revert the touched files with `git checkout -- <files>` to restore the
  896-line baseline (all 15 original proofs are self-contained and known-good).
- If a single system's callback fails to typecheck (frame-condition arg-order mismatch), revert only
  that file and re-derive its `*_soundness` arguments from the system's existing `Soundness.lean`
  signature, then re-apply. Other systems are unaffected.
- If K's distinct style cannot be made to fit the callback (low likelihood — verified in research),
  leave K's original file unchanged and apply the parametric refactor to the other 14 only; the
  ~400-line target is still met.
