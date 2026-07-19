# Implementation Summary: Migrate 15 Per-System Soundness Proofs to `unionSound`

- **Task**: 523 - Replace the 15 hand-written per-system axiom inductives with a compositional
  schema-union combinator
- **Phase**: 4 of 8 (Migrate 15 per-system soundness proofs to `unionSound`)
- **Plan**: `plans/02_schema-union-per-file-rollout.md`
- **Status**: [COMPLETED]

## What Was Done

All 15 per-system `<sys>_axiom_sound` theorems in
`Cslib/Logics/Modal/Metalogic/Systems/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}/Soundness.lean`
were migrated from a hand-written 13-branch `cases h_ax with | ctor => exact
Satisfies.<tag>_axiom ...` case-split to a single call into the master soundness combinator
`unionSound` (Phase 2, `Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean`), fed by that
system's Phase-3 tag set and bridge equivalence
(`Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean`):

```lean
theorem t_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : TAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (w : World) : Satisfies m w φ :=
  unionSound tTags m (fun t ht => by fin_cases ht <;> trivial)
    (schemaUnion_tTags_iff_TAxiom.mpr h_ax) w
```

`fin_cases ht` substitutes the concrete tag for each element of the system's tag set, then
Lean's `trivial` tactic closes every resulting goal: the 13 core-tag obligations because they
are literally `True`, and every differentiator-tag obligation via `trivial`'s `assumption`
fallback, since the system's frame hypothesis (`h_refl`/`h_trans`/`h_symm`/`h_serial`/`h_eucl`)
is already in local context with exactly the required type after substitution.

Executed as four sequential sub-phases, each independently green and committed:

- **4.1** — K, T, D, B
- **4.2** — K4, K5, K45, S4
- **4.3** — S5, TB, KB5 (plus a retroactive simplification of the `hfc` term across 4.1-4.3)
- **4.4** — D4, D5, D45, DB

## Key Findings / Deviations

1. **`fin_cases` needs an explicit import.** `Mathlib.Tactic.FinCases` is not transitively
   available via `Cslib.Init`, `SchemaBridges.lean`, or `SchemaSoundness.lean`. The first build
   attempt (on `K/Soundness.lean`) failed with `unknown tactic`; fixed by adding
   `public import Mathlib.Tactic.FinCases` directly to each of the 15 files — permitted since
   only the `Systems/*/Soundness.lean` files were in scope for this phase.

2. **`trivial`'s `assumption` fallback makes explicit `exact h_*` branches dead code.** The
   first-attempt `hfc` term used the task prompt's suggested shape,
   `fun t ht => by fin_cases ht <;> first | trivial | exact h_refl | exact h_trans | …`. This
   built green on K45/S4 (sub-phase 4.2), but `lake build` surfaced
   `linter.unreachableTactic`/`linter.unusedTactic` warnings: `trivial` (which tries
   `rfl`/`contradiction`/`assumption`) already discharges every differentiator-tag goal via
   `assumption`, since the matching frame hypothesis is in context after `fin_cases`
   substitutes the concrete tag. The `exact h_*` branches were unreachable. Root-caused and
   simplified to `fun t ht => by fin_cases ht <;> trivial` uniformly, applied retroactively to
   the already-committed 4.1/4.2 files in the same dispatch (documented as a plan deviation, not
   silent) and used from the start in 4.3/4.4. All nine previously-built files were re-verified
   green with zero warnings after the simplification.

3. **S5's `modalB` (symmetry) obligation has no direct hypothesis.** S5 = T+4+B (not
   T+4+B+5), so `s5_axiom_sound` never took an `h_symm` parameter; the pre-migration proof
   derived `m.r w' w` from `m.r w w'` inline via `h_eucl w w' w hr (h_refl w)`. The migrated
   proof reproduces this exactly as a local
   `have h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁ := fun w₁ w₂ hr => h_eucl w₁ w₂ w₁ hr (h_refl w₁)`
   feeding the same uniform `hfc` term (closed by `trivial`'s `assumption` step, since `h_symm`
   is in local context). `s5_axiom_sound`'s original signature
   (`h_refl`/`h_trans`/`h_eucl`, no `h_symm`) is preserved exactly.

## Plan Deviations

- The `hfc` proof term shape was simplified mid-phase from
  `first | trivial | exact h_*` to bare `trivial` (see Key Finding 2 above), applied
  retroactively to sub-phases 4.1 and 4.2 within this same dispatch to keep the codebase
  warning-free and consistent. This is a proof-term simplification only — no change to public
  names, signatures, tag sets, or bridge lemmas. Documented in the plan's Phase 4 completion
  note and sub-phase 4.3 completion note.
- No other deviation from the plan's task sequence, phase scope, or postmortem constraints.

## Verification

- Zero `sorry` across all 15 files (full `grep -rn '\bsorry\b'`, exit 1 / no matches).
- Zero new axiom: `lean_verify` spot-checked on `k_soundness`, `k45_soundness`, `s5_soundness`,
  `d45_soundness`, `b_axiom_sound`, `s4_axiom_sound`, `kb5_axiom_sound`, `db_axiom_sound` — all
  report only `propext`/`Classical.choice`/`Quot.sound`.
- Scoped `lake build` of all 15 modules green, zero warnings.
- `lake exe checkInitImports` green.
- `lake exe lint-style` on all 15 files green.
- Every public theorem/instance name byte-stable (`k_soundness`, `k_soundness_derivable`, all 15
  `<sys>_axiom_sound`, all 15 `<sys>_soundness`) — only the `_axiom_sound` proof bodies changed.
- Net line delta vs. the pre-Phase-4 baseline (`git diff --stat`): 149 insertions, 277
  deletions = **-128 lines net**.

## Files Modified

- `Cslib/Logics/Modal/Metalogic/Systems/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}/Soundness.lean`
- `specs/523_schema_union_axiom_combinator_for_proofsystem_instances/plans/02_schema-union-per-file-rollout.md`

No file outside `Systems/*/Soundness.lean` was touched. `SchemaUnion.lean`,
`SchemaSoundness.lean`, `SchemaBridges.lean` (Phases 1-3), the 15 instance files, and
`DerivationTree.lean` are all unmodified.

## Next Steps

Phase 5 (`AxiomSubsumption.lean` → `Finset.subset` facts) and Phase 6 (`IntToClassical.lean`
hand-migration) both depend only on Phase 3 (already complete) and are independent of Phase 4
and of each other — both are wave-3 phases per the plan's dependency map and may proceed next,
in parallel across distinct file territories.
