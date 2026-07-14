# Implementation Summary: Task #494, Phase 2 (IT.lean)

- **Task**: 494 - Intuitionistic modal extensions IT / IS4 / IS5
- **Phase**: 2 of 4 (IT.lean)
- **Status**: [COMPLETED]
- **Plan**: `specs/494_intuitionistic_modal_extensions_IT_IS4_IS5/plans/01_it-is4-is5-extensions.md`

## What Was Built

`Cslib/Logics/Modal/Metalogic/Intuitionistic/IT.lean` instantiates the task-494 Phase 1 scaffold
(`Extension.lean`: `IValidFC`, `ivalidFC_completeness`, `axiom_mem`) at Simpson's `IT`
([Simpson1994] Ch. 3): `IT = IK + reflexivity`.

- **`ITModalAxiom`**: the 14 `IKModalAxiom` constructors verbatim, plus `tBox (φ) : (□φ).imp φ`
  and `tDia (φ) : φ.imp (◇φ)`. Both box and diamond forms are required since `◇` is primitive
  (not `□`-definable) in this framework, matching `canonicalR`'s two-clause shape.
- **`itFC`**: the reflexivity frame condition on the raw relation `r` (`∀ w, r w w`).
- **`it_axiom_sound`**: extends `ik_axiom_sound`'s 14 cases verbatim, plus:
  - `tBox`: `hbox w' (le_refl w') w' (hrefl w')` -- direct box-clause instantiation at `w'`
    against itself via reflexivity.
  - `tDia`: `⟨w', hrefl w', hφ⟩` -- the diamond witness is `w'` itself; no persistence relocation
    needed (unlike, e.g., `andI`), since the single `imp`-unfold already delivers `φ` forced
    exactly at the target world.
- **`it_canonical_reflexive`**: `itFC (@canonicalR Atom ITModalAxiom)`, proved fully positively
  (no `by_contra`, no negation) via `axiom_mem (tBox/tDia)` + `canonical_imp_property` (MP
  closure) for each of the two `canonicalR` clauses.
- **`it_completeness`/`it_consistent`/`it_soundness_completeness`**: instantiations of
  `ivalidFC_completeness` with `it_canonical_reflexive` as `h_canonFC`, mirroring
  `ik_completeness`/`ik_consistent`/`ik_soundness_completeness` verbatim in structure.

## Plan Deviations

**Frame-condition naming**: the plan (and research report) recommended reusing Mathlib's
`Reflexive`/`Transitive`/`Symmetric` directly as `FC` instantiations. On reading the pinned
Mathlib source (`Mathlib/Order/Defs/Unbundled.lean:219`), `Reflexive` (along with `Symmetric`/
`Transitive`) is `@[deprecated (since := "2026-03-27")]`, superseded by the typeclass `Std.Refl`.
`Std.Refl`'s shape (`class Std.Refl (r : α → α → Prop) : Prop`) does structurally match
`IValidFC`'s bare-predicate `FC` parameter, but using the deprecated `Reflexive` name would emit
a build warning at every use site, violating the zero-warnings verification gate. Instead,
`IT.lean` defines a local `itFC {World : Type*} (r : World → World → Prop) : Prop := ∀ w, r w w`,
mirroring the codebase's own established convention: the classical (non-intuitionistic)
`Systems/T/Completeness.lean` file already defines its own local `tFC` for exactly this purpose
rather than using a Mathlib name. This is a naming substitution only -- the semantic content
(`∀ w, r w w`) and the frame-condition correspondence with `tBox`/`tDia` are unchanged from the
plan. Documented in the plan file's Phase 2 task list and in the orchestrator handoff.

No other deviations. All task-480/492/Phase-1 assets (`canonicalR`, `canonical_f1`/`canonical_f2`,
`canonical_imp_property`, `axiom_mem`, `IValidFC`, `ivalidFC_completeness`, `IKModalAxiom`,
`ik_axiom_sound`) were reused unchanged; `git diff --stat` confirms only `Cslib.lean` (+1 line)
and the new `IT.lean` file were touched.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IT`: succeeded, 600/600 jobs, no
  warnings in the build log.
- `lake exe checkInitImports`: passed (no output).
- `grep -n sorry IT.lean`: zero matches.
- `lean_verify` on all four top-level results (`it_axiom_sound`, `it_canonical_reflexive`,
  `it_consistent`, `it_soundness_completeness`): axioms limited to
  `propext`/`Classical.choice`/`Quot.sound` (or a strict subset), zero warnings on all four.

## Next Steps

Phase 3 (IS4.lean): reflexive+transitive frame class, `fourBox`/`fourDia` axioms, canonical
transitivity closure (chaining `canonicalR`'s box/dia clauses through `axiom_mem(fourBox)`/
`axiom_mem(fourDia)`), building on this Phase 2 `IT.lean` file via nested import.
