# Implementation Plan: Task #492 — IK Soundness + Completeness

- **Task**: 492 - IK (intuitionistic modal logic K) soundness + completeness over birelational semantics
- **Status**: [COMPLETED]
- **Effort**: 2.5 hours
- **Dependencies**: 480 (birelational intuitionistic modal framework), 490 (BFrame F1/F2) — both COMPLETED
- **Research Inputs**: specs/492_IK_intuitionistic_modal_soundness_completeness/reports/01_ik-instantiation-map.md
- **Artifacts**: plans/01_ik-soundness-completeness.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Task 492 is a small, low-risk **instantiation** of the completed task-480 birelational
intuitionistic modal framework, plus **one genuinely new soundness proof**. Research (report 01,
adversarially verified) established that the 480 framework's five modal hypotheses
`{h_K, h_Kdia, h_Cd, h_Idb, h_dbot}` map 1:1 onto Simpson's IK modal axioms k1–k5, that `h_dbot`
**IS** Nd (`◇⊥→⊥`, no extra axiom), and that **no IK axiom needs a frame condition beyond F1/F2
already present in `BFrame`**. Nd is vacuously `IValid`-sound because `IValid` fixes
`botForces = fun _ => False`. Definition of done: a single new file
`Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` defining `IKModalAxiom`, proving
`ik_soundness_derivable`, and instantiating `ivalid_completeness` — ZERO-DEBT (no `sorry`, no new
`axiom`), registered in the root barrel, passing full CSLib CI.

### Research Integration

Report 01 (`01_ik-instantiation-map.md`) is fully integrated:
- **Deliverable 1** (datatype + discharge map) → Phase 1.
- **Deliverable 2** (`ik_soundness_derivable`, the only substantial new proof, per-axiom soundness
  table, necessitation case template) → Phase 2.
- **Deliverables 3 & 4** (completeness/consistency instantiations, reuse-first gate) → Phase 3.
- Adversarial verdicts carried forward: Nd needs no frame condition (vacuous under `IValid`);
  Idb consumes `BFrame.f2`; the and/or hypotheses discharge by `rfl` via `Axioms.*` abbrevs.

### Prior Plan Reference

No prior plan. This is the first plan for task 492.

### Roadmap Alignment

No ROADMAP.md consulted (no `roadmap_path` / `roadmap_flag` in delegation). Task advances the
intuitionistic modal metalogic line begun by parent task 480 and 490.

## Goals & Non-Goals

**Goals**:
- Define `IKModalAxiom : Proposition Atom → Prop` (9 intuitionistic propositional schemata + 5 modal
  schemata k1–k5), mirroring `IntPropAxiom` + `ModalAxiom`.
- Prove `ik_soundness_derivable : Derivable IKModalAxiom φ → IValid φ` over birelational frames.
- Instantiate 480's `ivalid_completeness` at `Axioms := IKModalAxiom` to obtain `ik_completeness`,
  plus `ik_consistent` and the `ik_soundness_completeness` biconditional.
- Register the new module in the root `Cslib.lean` barrel; pass full CSLib CI, zero debt.

**Non-Goals**:
- No new canonical-model machinery (480 supplies `canonicalBModel`, `canonical_f1/f2`,
  `canonical_truth_lemma`, `modal_prime_exclusion`, `diaOr_of_diaDisj`, consistency hook,
  `ivalid_completeness`/`mvalid_completeness` — all reused, all `Axioms`-parametric).
- No new `BFrame` frame condition (F1/F2 suffice).
- No bare-CK / Wijesekera fallible-model work (that is task 493, out of scope).
- No `MValid` (minimal logic) instantiation (Nd is only `IValid`-sound; minimal logic is task 495).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Discharge-shape mismatch: 480 and/or hypotheses want `Axioms (Axioms.OrI1 φ ψ)` but constructor produces a different reducible form | M | L | Report §5 verified `Axioms.OrI1` is a `protected abbrev` (reducible) so `IKModalAxiom.orI1 φ ψ` discharges by `rfl`; `ModalAxiom` already uses this convention. If `rfl` fails, add explicit `(by rfl)`/shape-matching lambda. |
| `ik_soundness` necessitation case harder than templated | M | L | Mirror classical `Soundness.lean:168–170` exactly: empty-context premise closes the box goal by recursion with `fun _ h => nomatch h`. |
| Idb soundness F2 application detail | M | L | Per-axiom table (report Deliverable 2) pins the F2 (down-confluence) usage: relocate the witness world upward via `BFrame.f2`. Use `lean_goal` to inspect the exact obligation. |
| Import/barrel omission breaks CI (`checkInitImports`) | L | L | Phase 3 registers `IK` in `Cslib.lean` (after `...Intuitionistic.Completeness`, before `...Intuitionistic.PrimeTheory`); run `lake exe checkInitImports` + full CI in Phase 3. |
| Universe-polymorphism mismatch in `ivalid_completeness` instantiation (`.{u,u}`) | L | L | Report Deliverable 3 gives the exact `IValid.{u, u}` signature; copy verbatim. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is strictly sequential (one phase
per wave): each phase builds on the prior phase's definitions in the same file, so the file must
compile after each phase before the next begins.

### Phase 1: `IKModalAxiom` datatype + module scaffold [COMPLETED]

- **Goal:** Create the new file with header, imports, namespace, and the `IKModalAxiom` inductive
  (9 intuitionistic propositional schemata + 5 modal schemata k1–k5), compiling cleanly. Confirm
  the five modal dischargers typecheck against the 480 hypothesis shapes.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` with CSLib copyright header,
        `module`, and `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness`
        (transitively pulls in the datatype/axiom/semantics infrastructure).
  - [ ] Open the correct namespace/`open` (`Cslib.Logic.Modal`, `open Cslib.Logic`) matching
        report Deliverable 1; declare `variable {Atom : Type*}`.
  - [ ] Define `inductive IKModalAxiom : Proposition Atom → Prop` with constructors
        `implyK, implyS, efq, andI, andE1, andE2, orI1, orI2, orE` (and/or using the `Axioms.*`
        abbrev shapes) and modal `k, kdia, cd, idb, dbot` (direct `Proposition`/`◇`/`□` shapes),
        exactly per report §Deliverable 1.
  - [ ] Add a compile-time sanity check that the five modal dischargers match 480 hypothesis types
        (e.g. `example ... := fun φ ψ => IKModalAxiom.k φ ψ` shaped to `h_K`'s type, or a
        `#check`), ensuring the `rfl`-discharge for and/or holds.
  - [ ] `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IK` (or targeted build of the
        file); confirm no errors.
- **Timing:** ~30 min
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` (new) — datatype + scaffold.
- **Verification:**
  - File compiles: `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IK` exits 0.
  - No-debt: `grep -nE 'sorry|admit|^ *axiom ' Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean`
    returns nothing.
  - Dischargers typecheck (no red in `lean_diagnostic_messages` for the sanity `example`/`#check`).

### Phase 2: `ik_soundness_derivable` (birelational soundness) [COMPLETED]

- **Goal:** Prove IK soundness over birelational frames — the only substantial new proof
  (~130–170 lines), templated on `PL.IntSoundness.lean` + classical `Soundness.lean` necessitation.
- **Tasks:**
  - [ ] `ik_axiom_sound : IKModalAxiom φ → IValid φ` — one `cases` per constructor. Non-modal cases
        mirror `PL.int_axiom_sound` (uses `≤`-refl/trans + `bforces_persistence`). Modal cases per
        report Deliverable 2 table:
    - [ ] k1 (`k`): box quantifies `≤∘r`; apply `□(φ→ψ)` at `w'`-refl and same `r`-successor (no
          frame condition).
    - [ ] k2 (`kdia`): `◇φ` yields `u` with `r w u ∧ φ@u`; apply hyp, repackage `◇ψ`.
    - [ ] k3 (`cd`): `◇(φ∨ψ)` yields `u`; case-split into `◇φ`/`◇ψ` at same `u`.
    - [ ] k4 (`idb`): goal `□(φ→ψ)`; **use `BFrame.f2` (down-confluence)** to relocate the witness
          world upward so `◇φ` becomes available; then hyp gives `□ψ`, yielding `ψ@v'`.
    - [ ] k5 (`dbot`): under `IValid`, `botForces = fun _ => False`, so `BForces w' (◇⊥) = False`;
          `◇⊥→⊥` holds vacuously (no frame condition).
  - [ ] `ik_soundness : DerivationTree IKModalAxiom Γ φ → ... → BForces r val (fun _ => False) w φ`
        — induction on the derivation, mirroring `int_soundness` (`IntSoundness.lean:93`); handle
        the **necessitation** case as classical `Soundness.lean:168–170` (empty-context premise →
        box goal closes by recursion with `fun _ h => nomatch h`); MP via `≤`-refl.
  - [ ] `ik_soundness_derivable : Derivable IKModalAxiom φ → IValid φ` — unfold `Derivable`, apply
        `ik_soundness` at empty context (mirrors `int_soundness_derivable`, `IntSoundness.lean:120`).
  - [ ] Use `lean_goal`/`lean_diagnostic_messages` to close each obligation; keep the proof
        `sorry`-free at every checkpoint.
  - [ ] `lake build` the file; confirm no errors.
- **Timing:** ~1.5 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` — append the three soundness lemmas.
- **Verification:**
  - File compiles: `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IK` exits 0.
  - No-debt: `grep -nE 'sorry|admit|^ *axiom ' .../IK.lean` returns nothing.
  - `ik_soundness_derivable` has the exact target type `Derivable IKModalAxiom φ → IValid φ`
    (check via `lean_hover_info` / `#check`).

### Phase 3: Completeness/consistency instantiation + barrel + full CI [COMPLETED]

- **Goal:** Instantiate 480's completeness at IK, add consistency + biconditional, register the
  module in the barrel, and pass the full CSLib CI pipeline.
- **Tasks:**
  - [ ] `ik_completeness {φ} (h_valid : IValid.{u,u} φ) : Derivable IKModalAxiom φ :=
        ivalid_completeness <15 dischargers> h_valid` — each discharger the matching constructor,
        per report Deliverable 3 (verbatim signature, incl. universe annotation).
  - [ ] `ik_consistent : ¬ Derivable IKModalAxiom (Proposition.bot) :=` corollary of soundness
        (`ik_soundness_derivable h : IValid ⊥` contradicted by any inhabited model, per report
        Deliverable 3).
  - [ ] `ik_soundness_completeness : IValid φ ↔ Derivable IKModalAxiom φ :=
        ⟨ik_completeness, ik_soundness_derivable⟩` (mirrors `PL.int_soundness_completeness`).
  - [ ] Register the new module in the root barrel `Cslib.lean`: add
        `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IK` in alphabetical position
        (after `...Intuitionistic.Completeness`, before `...Intuitionistic.PrimeTheory`).
  - [ ] Run the full CSLib CI pipeline: `lake build`, `lake test`, `lake exe checkInitImports`,
        `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`.
  - [ ] Resolve any style/import/shake findings (e.g. remove unused imports flagged by shake).
- **Timing:** ~30 min
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` — append completeness/consistency/biconditional.
  - `Cslib.lean` — add the barrel import entry.
- **Verification:**
  - Full CI green: `lake build` && `lake test` && `lake exe checkInitImports` &&
    `lake exe lint-style` && `lake shake ...` all exit 0.
  - No-debt: `grep -nE 'sorry|admit|^ *axiom ' .../IK.lean` returns nothing.
  - `ik_soundness_completeness` typechecks as `IValid φ ↔ Derivable IKModalAxiom φ`.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IK` succeeds (per-phase).
- [ ] Full pipeline in Phase 3: `lake build`, `lake test`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` all pass.
- [ ] ZERO-DEBT: no `sorry`, `admit`, or new `axiom` anywhere in `IK.lean`
      (`grep -nE 'sorry|admit|^ *axiom '`).
- [ ] `ik_soundness_derivable`, `ik_completeness`, `ik_consistent`, `ik_soundness_completeness`
      each have the exact types specified in report Deliverable 2/3.
- [ ] `IK` module imported in `Cslib.lean` so it is part of the CI build closure.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` (new) — `IKModalAxiom`,
  `ik_axiom_sound`, `ik_soundness`, `ik_soundness_derivable`, `ik_completeness`, `ik_consistent`,
  `ik_soundness_completeness`.
- `Cslib.lean` (modified) — barrel import entry for the new module.
- `specs/492_IK_intuitionistic_modal_soundness_completeness/plans/01_ik-soundness-completeness.md`
  (this plan).
- `specs/492_IK_intuitionistic_modal_soundness_completeness/summaries/01_ik-soundness-completeness-summary.md`
  (produced by /implement).

## Rollback/Contingency

- All new logic is confined to the single new file `IK.lean` plus one additive import line in
  `Cslib.lean`. To revert: delete `IK.lean` and remove its `Cslib.lean` import entry, then
  `lake build` to confirm the framework returns to its pre-492 state. No existing 480/490 files are
  modified, so rollback cannot regress the framework.
- If Phase 2 soundness stalls, the phase is independently resumable: Phase 1's datatype compiles
  standalone, and the plan can be re-dispatched from Phase 2 without redoing Phase 1.
