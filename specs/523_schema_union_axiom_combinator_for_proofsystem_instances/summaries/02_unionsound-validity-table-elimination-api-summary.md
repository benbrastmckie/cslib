# Implementation Summary: Phase 2 — `unionSound` Combinator + Per-Tag Validity Table

- **Task**: 523 - Schema-Union Axiom Combinator for Modal ProofSystem Instances
- **Phase**: 2 of 8 (`unionSound` combinator + per-tag validity table + elimination API)
- **Plan**: plans/02_schema-union-per-file-rollout.md
- **Status**: [COMPLETED]

## What Was Built

### `Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean` (new file)

- `FrameValidatesTag {World : Type*} (m : Model World Atom) : ModalSchemaTag → Prop` — the
  per-tag semantic validity obligation, defined uniformly over all 18 tags via a single pattern
  match: `True` for the 13 frame-unconditional tags (`implyK, implyS, efq, peirce, modalK, andI,
  andE1, andE2, orI1, orI2, orE, diaDualityFwd, diaDualityBack`), and the exact frame-condition
  hypothesis for the 5 differentiators:
  - `modalT ↦ ∀ w, m.r w w` (reflexivity)
  - `modalD ↦ Relation.Serial m.r` (seriality)
  - `modalB ↦ ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁` (symmetry)
  - `modalFour ↦ ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃` (transitivity)
  - `modalFive ↦ ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃` (right-Euclideanness)

- `unionSound` — the single master soundness lemma:

  ```lean
  theorem unionSound {World : Type*} (S : Finset ModalSchemaTag) (m : Model World Atom)
      (hfc : ∀ t ∈ S, FrameValidatesTag m t) {φ : Proposition Atom} (h : SchemaUnion S φ)
      (w : World) : Satisfies m w φ
  ```

  Proof structure: `obtain ⟨t, ht, hφ⟩ := h; have hval := hfc t ht; cases t with | tag =>
  obtain ⟨…, rfl⟩ := hφ; exact Satisfies.<tag>_axiom …`.
  - The 13 frame-unconditional branches call the pre-existing atoms in `Metalogic/Soundness.lean`
    directly (`Satisfies.implyK_axiom`, `Satisfies.implyS_axiom`, `Satisfies.efq_axiom`,
    `Satisfies.peirce_axiom`, `Satisfies.modalK_axiom`, `Satisfies.andI_axiom`,
    `Satisfies.andE1_axiom`, `Satisfies.andE2_axiom`, `Satisfies.orI1_axiom`,
    `Satisfies.orI2_axiom`, `Satisfies.orE_axiom`, `Satisfies.diaDualityFwd_axiom`,
    `Satisfies.diaDualityBack_axiom`) — read-only reuse, no re-derivation.
  - The 5 differentiator branches pass `hval : FrameValidatesTag m t` (already exactly the frame
    hypothesis those lemmas expect) straight through to the task-522 `FrameCorrespondence.lean`
    lemmas: `Satisfies.modalT_axiom m hval w φ'`, `Satisfies.modalD_axiom m hval w φ'`,
    `Satisfies.modalB_axiom m hval w φ'`, `Satisfies.modalFour_axiom m hval w φ'`,
    `Satisfies.modalFive_axiom m hval w φ'`. No frame argument is re-proved inline — this is the
    522/523 composition the design invariant requires.

### `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` (additively extended)

Phase 1's declarations (`ModalSchemaTag`, `.Holds`, `SchemaUnion`, `SchemaUnion.subsumption`)
are unchanged. Added the generic elimination API:

- `SchemaUnion.empty_iff : SchemaUnion (∅ : Finset ModalSchemaTag) φ ↔ False` (`@[simp]`)
- `SchemaUnion.insert_iff : SchemaUnion (insert t S) φ ↔ t.Holds φ ∨ SchemaUnion S φ` (`@[simp]`)
- `SchemaUnion.union_iff : SchemaUnion (Sa ∪ Sb) φ ↔ SchemaUnion Sa φ ∨ SchemaUnion Sb φ` (`@[simp]`)

Together these let a concrete `SchemaUnion sysTags φ` (built from `insert`/`∪` on the 18-tag
alphabet) unfold via `simp` into the named disjunction of its tags' `.Holds`, so Phases 3/4/6/7
destructure by named rewrite rather than raw `fin_cases t <;> simp_all`.

## Verification

- Scoped `lake build Cslib.Logics.Modal.Metalogic.SchemaSoundness` — green, first attempt.
- Scoped `lake build Cslib.Logics.Modal.ProofSystem.SchemaUnion` — green, first attempt.
- `grep -n sorry` on both files — empty.
- `lean_verify` on `unionSound`, `SchemaUnion.insert_iff`, `SchemaUnion.union_iff`,
  `SchemaUnion.empty_iff` — all report only `propext` / `Classical.choice` / `Quot.sound`
  (standard Lean/Mathlib axioms; no new axiom introduced).
- `lake exe checkInitImports` — exit 0, no violations.
- `lake lint` (full library) — "Linting passed for Cslib."
- `lake exe lint-style` — clean, no output.

## Plan Deviations

None. The `FrameValidatesTag` hypothesis shapes match the `FrameCorrespondence.lean` lemma
signatures exactly (as required); the file placements match the plan's proposed locations
(`Metalogic/SchemaSoundness.lean` new, `ProofSystem/SchemaUnion.lean` additively extended);
`Soundness.lean` and `FrameCorrespondence.lean` were read-only, no edits made to either.

## Next Steps

Phase 3 (per-system tag sets + 15 bridge equivalences) is next, per the wave map. It depends
only on Phase 1 (`SchemaUnion`) and is independent of Phase 2, so it could in principle run in
parallel with further Phase 2 work — but Phase 2 is now fully closed. Phase 3 is split into four
sub-phases (3.1: `kCore`+K/T/D/B; 3.2: K4/K5/K45/S4; 3.3: S5/TB/KB5; 3.4: D4/D5/D45/DB), each
defining that group's `Finset ModalSchemaTag` tag set and proving `SchemaUnion sysTags φ ↔
<Sys>Axiom φ` in a new file, `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean`.
