# Implementation Summary: Phase 5 -- Axiom Subsumption Collapse

- **Task**: 523 - Schema-Union Axiom Combinator for ProofSystem Instances
- **Phase**: 5 of 8 (`AxiomSubsumption.lean` -> `Finset.subset` facts)
- **Plan**: plans/02_schema-union-per-file-rollout.md

## What Was Done

### Sub-phase 5.1 -- 24 subsumption facts

Replaced every one of the 24 hand-written `XAxiom_implies_YAxiom` lemmas in
`Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` (previously ~13-20 line
`match h with | .ctor => .ctor | ...` proofs) with the uniform two-line form:

```lean
lemma XAxiom_implies_YAxiom {φ : Proposition Atom} (h : XAxiom φ) : YAxiom φ :=
  schemaUnion_yTags_iff_YAxiom.mp
    (SchemaUnion.subsumption (by decide) (schemaUnion_xTags_iff_XAxiom.mpr h))
```

Each `xTags ⊆ yTags` obligation discharges by `decide` against the concrete `Finset
ModalSchemaTag` values defined in `SchemaBridges.lean` (Phase 3). Elaboration order matters
here but required no explicit type ascriptions: the outer `.mp`'s expected type
`SchemaUnion yTags φ` propagates down through `SchemaUnion.subsumption`'s implicit `Sb`, and
the inner `bridgeX.mpr h : SchemaUnion xTags φ` fixes `Sa`, so both implicit tag-set arguments
are resolved before `decide` runs on the fully-instantiated goal.

The deliberately-omitted `KB5 → S5` edge stays absent: `kb5Tags = kCore ∪ {modalB, modalFive}`
is not a subset of `s5Tags = kCore ∪ {modalT, modalFour, modalB}` (S5 = T+4+B, carries `modalB`
not `modalFive`), so no `hsub : kb5Tags ⊆ s5Tags` term exists and no lemma was written for it —
the same intentional omission as the pre-refactor file, now mechanically explained in the module
doc rather than asserted by comment alone.

Added `public import` of `Cslib.Logics.Modal.ProofSystem.SchemaUnion` and
`Cslib.Logics.Modal.ProofSystem.SchemaBridges` (previously only `...ProofSystem.Instances` was
imported).

### Sub-phase 5.2 -- call-site investigation

Read `Lifting.lean` and `Modularity.lean` line-by-line (excluding doc comments) for actual code
references to any of the 24 lemma names. Found none:

- `Lifting.lean`'s `liftDerivation`/`Derivable_mono`/etc. are fully parametric over free
  `Axioms1 Axioms2 : Proposition Atom → Prop` and `h_sub : ∀ φ, Axioms1 φ → Axioms2 φ`
  hypotheses. The single mention of `KAxiom_implies_TAxiom` (line 37) is a usage example in the
  module doc comment ("apply `Derivable_mono` with `KAxiom_implies_TAxiom` ... as the
  callback"), which remains accurate verbatim since the lemma's name and type signature are
  unchanged.
- `Modularity.lean` references the axiom *predicates* (`KAxiom`, `TAxiom`, `S4Axiom`,
  `ModalAxiom`, plus the out-of-scope minimal/intuitionistic families) directly, never any of
  the 24 subsumption lemma *names* as terms.

Both files already built green against the 5.1 changes with zero edits, confirming the plan's
"insulated... no structural change" framing. This sub-phase resolved to a verification-only
step: no file was modified.

## Verification

- Scoped `lake build` of `AxiomSubsumption`, `Lifting`, `Modularity`: green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `grep -rn '\bsorry\b' Cslib/`: zero hits in any of the three touched/verified files (all other
  hits belong to unrelated, pre-existing tasks 36/37/317/etc.).
- `lean_verify` on `KAxiom_implies_TAxiom`, `K45Axiom_implies_D45Axiom`,
  `S4Axiom_implies_ModalAxiom`: all report only `propext`/`Quot.sound` — no new axiom.
- `KB5 → S5` edge: grep-confirmed absent.

## Net Line Delta

`AxiomSubsumption.lean`: 73 insertions, 368 deletions = **-295 lines net** (git diff --stat
across the two phase-5 commits, vs. the pre-Phase-5 524-line baseline).

## Plan Deviations

None. Both sub-phases executed exactly as specified. Sub-phase 5.2's "few call sites" turned out
to be zero actual call sites (only one accurate doc-comment mention) — this is a discovery, not
a deviation, since the plan itself hedged with "the (few) call sites" rather than asserting a
specific count.

## Commits

- `521eb00e` — task 523 phase 5.1: collapse 24 subsumption lemmas to generic
  `SchemaUnion.subsumption`
- `cfaa2a11` — task 523 phase 5.2: confirm Lifting/Modularity call sites need no changes; mark
  Phase 5 complete

## Next Phase

Phase 6 (`IntToClassical.lean` hand-migration, ~36 sites) — independent of Phase 5, depends only
on Phase 3. Phase 7 (instance registration swap) depends on Phase 6. Phase 8 (inductive deletion)
depends on Phases 4, 5, 6, 7 — 4 and 5 are both now complete.
