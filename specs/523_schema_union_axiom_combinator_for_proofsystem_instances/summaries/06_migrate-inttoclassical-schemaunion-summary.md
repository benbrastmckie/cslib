# Summary: Phase 6 — Hand-migrate `IntToClassical.lean` to the `SchemaUnion` bridge

- **Task**: 523 - Replace the 15 hand-written per-system axiom inductives with a compositional
  schema-union combinator
- **Plan**: plans/02_schema-union-per-file-rollout.md, Phase 6
- **Status**: [COMPLETED]

## What Was Done

Migrated the raw-constructor witness-construction sites in
`Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean` (774 lines) that build classical
`KAxiom`/`TAxiom`/`S4Axiom` proofs directly via `<Sys>Axiom.ctor` applications, so they instead
build the same proof by constructing a `SchemaUnion` existential witness and pushing it through
the Phase-3 bridge (`schemaUnion_kTags_iff_KAxiom.mp`, `schemaUnion_tTags_iff_TAxiom.mp`,
`schemaUnion_s4Tags_iff_S4Axiom.mp`). This removes the direct dependence on the constructor names
that Phase 8 will retire (when `<Sys>Axiom` is redefined in place as a constructorless
`SchemaUnion` `def`), while leaving every migrated theorem's name and type unchanged.

### Site Enumeration (Ground-Truthed, Superseding the ~36 Estimate)

A full grep of the file for constructor patterns (`⟨.ax [] _ (`, `<Sys>Axiom.`, `match h with`,
`cases h with`, `obtain`/`rcases` on axiom-typed hypotheses) found:

- **12 real in-scope witness-construction sites**: 10 on `KAxiom` (`implyK`, `implyS`, `efq`,
  `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `modalK`), 1 on `TAxiom` (`modalT`, the
  cross-family `IT → T` bridge), 1 on `S4Axiom` (`modalFour`, the cross-family `IS4 → S4`
  bridge).
- **0 in-scope destructuring sites**: the file's four `match h with` blocks
  (`ikAxiom_derivable_in_K`, `itAxiom_derivable_in_T`, `is4Axiom_derivable_in_S4`,
  `is5Axiom_derivable_in_S5`) all destructure the permanently out-of-scope intuitionistic
  inductives (`IKModalAxiom`/`ITModalAxiom`/`IS4ModalAxiom`/`IS5ModalAxiom`) and need no
  elimination-API migration. All `obtain`/`rcases` sites destructure the single-field `Derivable`
  wrapper, unrelated to axiom representation.
- The `HasAxiom*` typeclass field accesses (the representation-agnostic insulation layer) are
  correctly untouched throughout.

The plan's ~36 estimate over-counted arms of the out-of-scope `match` statements; the actual
in-scope count is 12, and all 12 are migrated below.

### 3-Cluster Partition (Recorded at Start of 6.1, Fixed and Non-Overlapping)

- **Cluster 1 (6.1)**: `implyK`, `implyS`, `efq`, `andI` (`KAxiom`).
- **Cluster 2 (6.2)**: `andE1`, `andE2`, `orI1`, `orI2` (`KAxiom`).
- **Cluster 3 (6.3)**: `orE`, `modalK` (`KAxiom`) + `modalT` (`TAxiom`, cross-family) +
  `modalFour` (`S4Axiom`, cross-family).

### Migration Pattern

Each `⟨.ax [] _ (<Sys>Axiom.ctor args)⟩` became
`⟨.ax [] _ (schemaUnion_<sys>Tags_iff_<Sys>Axiom.mp ⟨.ctor, by decide, args, rfl⟩)⟩` — the
`SchemaUnion` existential witness has the byte-identical shape to the retired constructor's
argument (per `ModalSchemaTag.Holds`, design invariant 3), so every witness closes with a bare
`rfl`; membership in the tag set (`kTags`/`tTags`/`s4Tags`) discharges with `by decide`. All 12
sites used the elimination-API + bridge route (per the plan's stated preference); none required
raw `fin_cases <;> simp_all`.

## Cross-Family Witness Sites (the Sharpest Risk, per Report §4.1)

The two cross-family sites (`TAxiom.modalT` inside `itAxiom_derivable_in_T`'s `.tBox` arm,
`S4Axiom.modalFour` inside `is4Axiom_derivable_in_S4`'s `.fourBox` arm) were migrated with no
difficulty: only the leaf witness term changed; the enclosing `match` on the out-of-scope
intuitionistic inductive (`ITModalAxiom`, `IS4ModalAxiom`) was left completely untouched. Neither
site required any adjustment beyond the direct bridge substitution — the byte-identical
`.Holds`/constructor-argument shape meant no genuine derivation work was needed here (unlike, say,
`k_derivable_of_ik_kdia`/`cd`/`idb`, which are pre-existing intuitionistic→classical derivations
in this same file, untouched by this phase since they route through `HasAxiom*` typeclass
accessors, not raw constructors).

## Verification

- Scoped `lake build Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical`: green after every
  cluster (6.1, 6.2, 6.3).
- `grep -n sorry`: empty throughout.
- `lake exe checkInitImports`: clean.
- `lake lint --builtin-lint Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical`: no
  environment linters registered for this module; overall workspace lint passed. The text-linter
  warnings present (`Modal/Basic.lean` flexible-tactic warnings) are pre-existing and unrelated
  to this file.
- `lake exe lint-style Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`: clean, no
  output.
- `lean_verify` on `k_derivable_of_ik_implyK`, `itAxiom_derivable_in_T`, and
  `is4Axiom_derivable_in_S4`: all report only `propext`/`Quot.sound` (no `sorryAx`, no new axiom).
- No `<Sys>Axiom`/`ModalAxiom` inductive deleted (all five live inductives, plus the five
  out-of-scope intuitionistic families, remain exactly as before).
- Public API unchanged: every migrated theorem keeps its original name and type.

## Sorry Inventory

None. Zero `sorry` in the file before or after this phase.

## Plan Deviations

- **Site count**: the plan estimated ~36 sites; the actual in-scope count, ground-truthed by
  grep, is 12. This is not a design re-opening — it is the site-count ground-truthing the plan
  itself commissions ("the implementer partitions the ~36 sites... at the start of 6.1"). All 12
  real sites were migrated; none were skipped or deferred.
- **Cluster shape**: because 0 real destructuring sites exist in this file (the plan anticipated
  `cases … with | ctor` sites in clusters 1/2), clusters 1 and 2 are witness-construction sites
  from the `KAxiom` "Direct Schemata" section rather than destructuring sites. This reflects the
  actual code, not a scope reduction — the plan's Phase 8 notes confirm the goal is that no
  `.ctor` construction/destructuring site targets a to-be-redefined inductive, which is achieved.
- No sites were left `[BLOCKED]`; no `sorry`/placeholder was committed anywhere.

## Files Modified

- `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean` (12 witness sites migrated, 2
  docstrings updated for accuracy, 1 new `public import` of `SchemaBridges.lean`).
- `specs/523_schema_union_axiom_combinator_for_proofsystem_instances/plans/02_schema-union-per-file-rollout.md`
  (Phase 6 marked [COMPLETED]; enumeration, partition, and per-sub-phase completion notes
  recorded).

## Next Phase

Phase 7 (swap the 15 instance registrations to build from `SchemaUnion`) may now proceed — it
depends on Phase 6 being complete precisely so that no live cross-family witness site in
`IntToClassical.lean` is stranded when Phase 7/8 touch the instance files and inductives.
