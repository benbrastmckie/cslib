# Implementation Plan: Task #490 — Birelational (Intuitionistic Kripke) Modal Semantics

- **Task**: 490 - Birelational (intuitionistic Kripke) modal SEMANTICS for CSLib (Lean 4)
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours
- **Dependencies**: None (both prerequisites — `Modal/Basic.lean` primitive `Proposition` and `Propositional/Semantics/Kripke.lean` pattern — already in tree)
- **Research Inputs**: specs/490_birelational_intuitionistic_modal_semantics/reports/01_birelational-intuitionistic-modal-semantics.md
- **Artifacts**: plans/01_birelational-modal-semantics.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add a single new file `Cslib/Logics/Modal/Semantics/Birelational.lean` (new `Semantics/`
subdirectory) defining the intuitionistic-Kripke birelational semantic layer for the
fully-primitive modal `Proposition {atom, bot, imp, and, or, box, diamond}` from
`Modal/Basic.lean` (task 487 / PR #662). The file is a direct extension of the existing
propositional pattern in `Propositional/Semantics/Kripke.lean`: a birelational frame carrying a
preorder `≤` and a modal accessibility relation `r` with the F1/F2 confluence conditions
(`BFrame`), a heredity-carrying model (`BModel`), a 7-case forcing relation (`BForces`) whose
`box` clause quantifies over `≤ ∘ r` and `diamond` clause over `r`, the persistence/monotonicity
lemma proved by structural induction (`bforces_persistence`), and intuitionistic/minimal
validity definitions (`IValid`/`MValid` + `mvalid_implies_ivalid`). Definition of done: the file
compiles with zero `sorry` and zero new axioms, is registered in the `Cslib.lean` barrel, and
passes the full CSLib CI pipeline.

### Research Integration

Integrates report `01_birelational-intuitionistic-modal-semantics.md` in full:
- **Ground truth**: Simpson 1994 (LFCS ECS-LFCS-94-308), Ch. 3 clauses 3.2 (□ over `≤ ∘ R`) and
  3.5 (◇ over `R`), frame conditions F1 (up-confluence `≤;R ⊆ R;≤`) and F2 (down-confluence
  `R;≤ ⊆ ≤;R`). Persistence = Simpson's monotonicity lemma; `diamond` case uses **F1** only.
- **Reuse-first gate satisfied**: reuse `Cslib.Logic.Modal.Proposition` (primitive box/diamond),
  the `HasBox`/`HasDia`/`HasAnd`/`HasOr`/`Bot` connective instances from `Modal/Basic.lean`, and
  the `Preorder`/upward-closure pattern from `PL.KripkeModel`. No new `Proposition` datatype and
  no new connective typeclasses.
- **Design decisions adopted from the report's risk section**:
  1. `BForces` takes **loose** `r`/`v`/`botForces` parameters (mirrors `PL.IForces`), while
     `BModel` bundles them and is used only for the validity definitions.
  2. Include **both F1 and F2** in `BFrame` now (task brief requires them; F2 is unused by
     task-490 lemmas but is the correct IK frame class for downstream tasks 492–495).
  3. Name the forcing relation `BForces` (not `Satisfies`) to avoid shadowing the existing
     classical `Modal.Satisfies` in the same `Cslib.Logic.Modal` namespace.
  4. Use `Preorder World` (antisymmetry never needed), matching the PL file.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; no ROADMAP.md consulted. This task is the
semantic base that intuitionistic completeness (tasks 492/493/494) and minimal completeness
(task 495) build on.

## Goals & Non-Goals

**Goals**:
- Define `BFrame` (preorder `≤` + relation `r` + F1/F2 confluence) with docstrings on every field.
- Define `BModel` extending `BFrame` with an upward-closed valuation `v` and upward-closed
  `botForces` (heredity).
- Define `BForces` as a 7-case recursion on `Modal.Proposition`, with `box` over `≤ ∘ r` and
  `diamond` over `r`, plus `@[simp]` reduction lemmas per constructor.
- Prove `bforces_persistence` (Simpson monotonicity) by structural induction with `generalizing`,
  using F1 for the `diamond` case.
- Define `IValid`/`MValid` and prove `mvalid_implies_ivalid`, mirroring the PL file.
- Register the new file in `Cslib.lean`; pass the full CSLib CI pipeline with zero debt.

**Non-Goals**:
- No IK axiom validations (`K□`, `K◇`, `◇⊥→⊥`, ◇/∨ distribution) — those belong to
  soundness/completeness tasks 492–495.
- No CK (Wijesekera / Bierman-de Paiva) variant; task 490 targets the IK birelational clauses.
- No frame-class variants (S4-style reflexive/transitive intuitionistic modal frames).
- No changes to `Modal/Basic.lean` or `Propositional/Semantics/Kripke.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `induction φ` IH arity / `generalizing w w'` shape differs from PL (PL does not generalize; modal `diamond` needs IH at a different world `u`) | M | M | Use `lean_goal`/`lean_multi_attempt` to inspect each branch's goal before committing tactics; the report's sketch already flags `generalizing w w'` as required |
| Naming collision with existing classical `Modal.Satisfies` / `Modal.valid` in same namespace | M | L | Use `BFrame`/`BModel`/`BForces` prefixed names; verify no clashes via `lean_local_search` before writing |
| `@[simp]` reduction lemmas fail `simpNF` lint (RHS not in simp-normal form) | L | L | Follow PL file's exact `= ... := rfl` shape; run `lake lint` in Phase 5 and adjust |
| Missing/incorrect imports for `Preorder`/`le_trans` cause build failure | L | L | Copy the PL file's import header (`Mathlib.Order.Defs.PartialOrder`, `.Unbundled`) plus `Cslib.Logics.Modal.Basic` |
| New file breaks `checkInitImports` / `shake` (import minimization) | L | M | Ensure `import Cslib.Init` (via `Cslib.Init` transitively or directly) and run `lake shake` in Phase 5, applying `--fix` suggestions if needed |
| `docBlame` lint on any undocumented declaration | L | M | Write a docstring for every `structure`, field, `def`, and `theorem` as they are introduced |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |

Phases 3 and 4 both depend only on Phase 2 (they are logically independent: persistence does not
feed the validity definitions, and `mvalid_implies_ivalid` does not use persistence). Because they
edit the same file, they will in practice be applied sequentially, but either order is valid.

---

### Phase 1: File scaffold — imports, namespace, `BFrame`, `BModel` [COMPLETED]

**Goal**: Create the new file with header/imports, open namespace `Cslib.Logic.Modal`, and define
the birelational frame (`BFrame` with `r`, F1, F2) and model (`BModel` extending `BFrame` with
`v`, `botForces`, and the two upward-closure heredity fields).

**Tasks**:
- [ ] Create directory `Cslib/Logics/Modal/Semantics/` (lazy: only when writing the file).
- [ ] Write the license header (copy the 4-line Apache header from `Kripke.lean`), `module`
      declaration, and imports: `public import Cslib.Logics.Modal.Basic`,
      `public import Mathlib.Order.Defs.PartialOrder`, `public import Mathlib.Order.Defs.Unbundled`.
      Confirm `Cslib.Init` is transitively imported via `Modal.Basic` (else add it explicitly).
- [ ] Write a module docstring (`/-! # Birelational Modal Kripke Semantics ... -/`) summarizing
      Main Definitions and a Design Notes section (mirror `Kripke.lean`); cite `[Simpson1994]`.
- [ ] Open `@[expose] public section`, `universe u v`, `namespace Cslib.Logic.Modal`,
      `variable {Atom : Type u}`.
- [ ] Define `structure BFrame (World : Type*) [Preorder World]` with fields `r`, `f1`, `f2` and
      a docstring on the structure and each field (F1 = up-confluence, F2 = down-confluence, per
      report sketch lines 163–169).
- [ ] Define `structure BModel (World : Type*) (Atom : Type*) [Preorder World] extends BFrame World`
      with fields `v`, `botForces`, `v_upward_closed`, `bf_upward_closed` (report lines 174–182),
      each documented.
- [ ] Verify no name collisions with `Modal.Basic` via `lean_local_search` (`BFrame`, `BModel`).

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Semantics/Birelational.lean` - new file: header, imports, docstring,
  `BFrame`, `BModel`.

**Verification**:
- `lake build Cslib.Logics.Modal.Semantics.Birelational` compiles the scaffold (structures only).
- `lean_goal`/no errors on the two structure declarations; every field has a docstring.

---

### Phase 2: `BForces` recursion + `@[simp]` reduction lemmas [COMPLETED]

**Goal**: Define the 7-case forcing relation with loose `r`/`v`/`botForces` parameters, `box` over
`≤ ∘ r` (clause 3.2) and `diamond` over `r` (clause 3.5), and add one `@[simp]` reduction lemma
per constructor.

**Tasks**:
- [ ] Define `def BForces [Preorder World] (r : World → World → Prop) (v : World → Atom → Prop)
      (botForces : World → Prop) (w : World) : Proposition Atom → Prop` with the seven cases from
      report lines 193–202: `atom` → `v w p`; `bot` → `botForces w`; `imp` → `∀ w', w ≤ w' → …`;
      `and` → `∧`; `or` → `∨`; `box` → `∀ w', w ≤ w' → ∀ u, r w' u → BForces … u φ`;
      `diamond` → `∃ u, r w u ∧ BForces … u φ`. Add a docstring.
- [ ] Add `@[simp]` reduction lemmas `BForces_atom`, `BForces_bot`, `BForces_imp`, `BForces_and`,
      `BForces_or`, `BForces_box`, `BForces_diamond`, each `= … := rfl` (mirror `IForces_*` in
      `Kripke.lean` lines 90–116, extended with the two modal cases). Docstring optional per PL
      precedent but add short ones if `docBlame` flags them.
- [ ] Confirm each `rfl` reduction closes via `lean_multi_attempt`/`lean_goal` before finalizing.

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Semantics/Birelational.lean` - add `BForces` and seven `@[simp]` lemmas.

**Verification**:
- `lake build Cslib.Logics.Modal.Semantics.Birelational` compiles.
- Each `BForces_*` lemma type-checks by `rfl`.

---

### Phase 3: `bforces_persistence` (Simpson monotonicity) [COMPLETED]

**Goal**: Prove persistence of forcing under `≤` by structural induction on the formula, using F1
for the `diamond` case; zero `sorry`.

**Tasks**:
- [ ] State `theorem bforces_persistence [Preorder World] {F : BFrame World}
      {v : World → Atom → Prop} {botForces : World → Prop}` with hypotheses `v_uc`, `bf_uc`
      (upward-closure), `{w w'} (hww' : w ≤ w') {φ}` and conclusion
      `BForces F.r v botForces w φ → BForces F.r v botForces w' φ` (report lines 211–227). Add a
      docstring citing Simpson's monotonicity lemma and noting F1 is used only in `diamond`.
- [ ] Prove by `induction φ generalizing w w'`: `atom`→`v_uc`; `bot`→`bf_uc`; `imp`→`intro`+
      `le_trans`; `and`→pair of IHs; `or`→`Or.elim` of IHs; `box`→`intro`+`le_trans`; `diamond`→
      `obtain` the witness, apply `F.f1 hww' hru` to get `⟨u', hru', huu'⟩`, then IH at `u`.
- [ ] Use `lean_goal` to confirm the IH arity/shape in each branch (PL file does not generalize;
      the modal `diamond` case here needs the IH at a different world, so `generalizing` is
      required — verify the generated induction principle before locking tactics).
- [ ] Run `lean_verify Cslib.Logic.Modal.bforces_persistence` to confirm no `sorry`/no new axioms.

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Semantics/Birelational.lean` - add `bforces_persistence`.

**Verification**:
- `lake build Cslib.Logics.Modal.Semantics.Birelational` compiles with no errors/warnings.
- `lean_verify` reports only standard axioms (no `sorryAx`).

---

### Phase 4: `IValid` / `MValid` / `mvalid_implies_ivalid` [COMPLETED]

**Goal**: Define intuitionistic and minimal modal validity and prove minimal ⟹ intuitionistic,
mirroring `PL.IValid`/`MValid`/`mvalid_implies_ivalid`.

**Tasks**:
- [ ] Define `def IValid (φ : Proposition Atom) : Prop` — forced at every world of every
      birelational model with `botForces = fun _ => False` (quantify over `World`, `Preorder`,
      relation `r` with F1/F2, upward-closed valuation). Mirror `Kripke.lean` lines 145–148,
      threading the `r`/F1/F2 frame data. Add a docstring.
- [ ] Define `def MValid (φ : Proposition Atom) : Prop` — same but with an arbitrary upward-closed
      `botForces` (mirror `Kripke.lean` lines 153–158). Add a docstring.
- [ ] Prove `theorem mvalid_implies_ivalid {φ} (h : MValid.{u, v} φ) : IValid.{u, v} φ` by
      instantiating `botForces := fun _ => False` (trivially upward-closed), mirroring
      `Kripke.lean` lines 165–168. Add a docstring.
- [ ] Decide the exact shape of the frame quantification in `IValid`/`MValid` (loose `r`+`f1`+`f2`
      args vs. a `BFrame`/`BModel` bundle). Recommended: quantify over `BModel` for `MValid` and
      over `BModel` with `botForces = fun _ => False` for `IValid`, OR keep loose to match PL
      exactly — pick one and keep both definitions consistent so `mvalid_implies_ivalid` goes
      through cleanly. Confirm with `lean_goal`.
- [ ] `end Cslib.Logic.Modal`.

**Timing**: 40 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Semantics/Birelational.lean` - add `IValid`, `MValid`,
  `mvalid_implies_ivalid`, close namespace.

**Verification**:
- `lake build Cslib.Logics.Modal.Semantics.Birelational` compiles.
- `mvalid_implies_ivalid` type-checks; `lean_verify` shows no `sorry`/no new axioms.

---

### Phase 5: Barrel registration + full CI pipeline (zero-debt gate) [COMPLETED]

**Goal**: Register the new file in `Cslib.lean` and pass the complete CSLib CI verification order
with zero `sorry`, zero new axioms, and no lint violations.

**Tasks**:
- [ ] `lake exe cache get` (once, to avoid a long Mathlib rebuild) if not already cached.
- [ ] `lake exe mk_all --module` to add
      `public import Cslib.Logics.Modal.Semantics.Birelational` to `Cslib.lean` (verify it lands
      in the `Modal` block near line 345).
- [ ] `lake build` — full build, syntax linters clean.
- [ ] `lake exe checkInitImports` — confirm the new file imports `Cslib.Init` (transitively OK).
- [ ] `lake lint` — resolve any `docBlame`, `simpNF`, `defLemma`, `unusedSectionVars` warnings on
      the new declarations.
- [ ] `lake exe lint-style` (use `--fix` for text/whitespace issues).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — apply import-minimization
      suggestions for the new file (drop any unused Mathlib import).
- [ ] `lake test` — confirm `CslibTests/` still passes (no regressions).
- [ ] Final `lean_verify` on `bforces_persistence` and `mvalid_implies_ivalid` (no `sorryAx`, no
      new axioms).

**Timing**: 35 minutes

**Depends on**: 3, 4

**Files to modify**:
- `Cslib.lean` - add barrel import entry (via `mk_all`).
- `Cslib/Logics/Modal/Semantics/Birelational.lean` - lint/shake-driven touch-ups only.

**Verification**:
- All CI commands exit 0.
- `Cslib.lean` contains the new import; `git status` shows only the new file + barrel change.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Semantics.Birelational` — file compiles standalone (Phases 1–4).
- [ ] `lake build` — whole project compiles after barrel registration (Phase 5).
- [ ] `lake exe checkInitImports` — passes.
- [ ] `lake lint` — zero warnings on new declarations (especially `docBlame`, `simpNF`).
- [ ] `lake exe lint-style` — passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports flagged.
- [ ] `lake test` — `CslibTests/` passes.
- [ ] `lean_verify Cslib.Logic.Modal.bforces_persistence` and
      `lean_verify Cslib.Logic.Modal.mvalid_implies_ivalid` — no `sorryAx`, no new axioms.
- [ ] Manual check: every `structure`/field/`def`/`theorem` has a docstring; `box` quantifies over
      `≤ ∘ r`, `diamond` over `r`; F1 used in the `diamond` persistence case.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Semantics/Birelational.lean` — the new semantic-layer file (`BFrame`,
  `BModel`, `BForces` + `@[simp]` lemmas, `bforces_persistence`, `IValid`, `MValid`,
  `mvalid_implies_ivalid`).
- `Cslib.lean` — updated barrel with the new `public import`.
- `specs/490_birelational_intuitionistic_modal_semantics/plans/01_birelational-modal-semantics.md`
  (this plan).
- `specs/490_birelational_intuitionistic_modal_semantics/summaries/01_birelational-modal-semantics-summary.md`
  (produced at implementation time).

## Rollback/Contingency

- The change is additive and isolated to one new file plus one barrel line. To revert:
  `git rm Cslib/Logics/Modal/Semantics/Birelational.lean`, remove the `Cslib.lean` import line
  (or re-run `lake exe mk_all --module` after deletion), then `lake build` to confirm the tree is
  green.
- If `bforces_persistence` (Phase 3) cannot be closed for the `diamond` case, do **not** insert a
  vacuous placeholder or `sorry`: mark Phase 3 `[BLOCKED]`, record the exact `lean_goal` state and
  the F1-application attempt, and return `status: partial` with `requires_user_review: true`.
  Phases 1–2 and 4 remain valid, committable progress.
- If `IValid`/`MValid` frame-quantification shape causes friction (risk item), fall back to the
  loose-parameter phrasing that exactly mirrors `PL.IValid`/`MValid`, which is known to compile.
