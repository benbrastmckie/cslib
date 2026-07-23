# Implementation Summary: Phase 3 — Per-System Tag Sets + 15 Bridge Equivalences

- **Task**: 523 - Schema-Union Axiom Combinator for Modal ProofSystem Instances
- **Phase**: 3 of 8 (per-system tag sets + 15 bridge equivalences), sub-phases 3.1-3.4
- **Plan**: plans/02_schema-union-per-file-rollout.md
- **Status**: [COMPLETED]

## What Was Built

### `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean` (new file, 786 lines)

- `kCore : Finset ModalSchemaTag` — the 13 shared tags (`implyK, implyS, efq, peirce, modalK,
  andI, andE1, andE2, orI1, orI2, orE, diaDualityFwd, diaDualityBack`), defined as **explicit
  nested `insert` terminating in `∅`** rather than the `{a, b, c, …}` literal set-builder sugar.
  The sugar's last element desugars via the `Singleton` instance, not `insert _ ∅`, so the
  Phase-2 elimination API (`SchemaUnion.insert_iff`, `SchemaUnion.empty_iff`) does not fire on
  it — discovered on the first build attempt (a `subst` failure on the trailing element) and
  fixed by switching `kCore`'s definition to explicit nested inserts.
- 15 per-system tag sets, each `kCore` unioned with that system's modal-strength differentiator
  tag(s): `kTags = kCore` (K has none beyond `modalK`, already in `kCore`); `tTags, dTags,
  bTags, k4Tags, k5Tags` each `kCore` + 1 differentiator; `k45Tags, s4Tags, tbTags, kb5Tags,
  d4Tags, d5Tags, dbTags` each `kCore` + 2; `s5Tags, d45Tags` each `kCore` + 3.
- 15 bridge equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` (S5 bridges to the pre-existing
  `ModalAxiom` inductive in `Metalogic/DerivationTree.lean`, per the resolved design decision
  that S5 = T+4+B and generalizes toward `ModalAxiom` rather than gaining a bespoke branch).

### Proof pattern (uniform across all 15 bridges)

- **Forward** (`SchemaUnion sysTags φ → <Sys>Axiom φ`): `simp only [sysTags, kCore,
  SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false, ModalSchemaTag.Holds] at h` unfolds
  the hypothesis into the named disjunction of `.Holds` existentials, `rcases h with ⟨…, rfl⟩ |
  …` destructures each disjunct, then `all_goals first | exact <Sys>Axiom.<ctor> _ … | …` closes
  every resulting goal against whichever constructor type-checks (arity mismatches simply fail
  and `first` tries the next alternative, so goal order need not match the `first` list order).
- **Backward** (`<Sys>Axiom φ → SchemaUnion sysTags φ`): `cases h with | ctor args => exact
  ⟨.tag, by decide, args…, rfl⟩` — a direct `SchemaUnion` witness (tag + `by decide` membership
  proof + the `.Holds` existential witness), needing no simp unfolding.

### Tag-set-to-constructor cross-check

Every tag set was verified against its target inductive's *actual* constructors (not assumed
from the plan's prose) via `awk '/^inductive/,0' Instances/{sys}.lean | grep -E '^\s*\|'` on
all 14 `Instances/*.lean` files plus a direct read of `ModalAxiom` in `DerivationTree.lean`.
Confirmed: K = `kCore` exactly; T/D/B/K4/K5 = `kCore ∪ {1 tag}`; K45/S4/TB/KB5/D4/D5/DB =
`kCore ∪ {2 tags}`; S5/D45 = `kCore ∪ {3 tags}` — matching the plan's §1.3-derived table
exactly, with zero deviation.

## Deviations Found and Fixed (both root-caused before proceeding, per plan-compliance)

1. **`kCore` literal-sugar elaboration failure** (sub-phase 3.1, first build attempt): see
   above. Fixed by switching to explicit nested `insert … ∅`.
2. **`rcases`-slot miscounts on 2- and 3-differentiator systems** (sub-phase 3.2's K45/S4, and
   again on sub-phase 3.3's S5): the `rcases` pattern needs exactly
   `(differentiator count) + 13` slots in the correct arity sequence; the first attempt at each
   multi-differentiator shape silently dropped one slot (`orI2`) mid-list, desyncing every
   subsequent arity and producing a `subst` failure several slots later. Root-caused by
   re-deriving the exact tag order and arity list before rewriting the `rcases` line. Once the
   15-slot (2-differentiator) and 16-slot (3-differentiator) patterns were corrected, every
   subsequent system of the same shape (TB/KB5/D4/D5/DB for 2-differentiator; D45 for
   3-differentiator) reused the corrected pattern and built green on the first attempt.

## Verification

- Scoped `lake build Cslib.Logics.Modal.ProofSystem.SchemaBridges` — green after each of the
  four sub-phases (3.1-3.4), each committed independently per the commit-per-green-substep
  mandate.
- `grep -n sorry` on the file — empty, throughout.
- `lean_verify` spot-checked one bridge per sub-phase (`schemaUnion_kTags_iff_KAxiom`,
  `schemaUnion_bTags_iff_BAxiom`, `schemaUnion_k45Tags_iff_K45Axiom`,
  `schemaUnion_s4Tags_iff_S4Axiom`, `schemaUnion_s5Tags_iff_ModalAxiom`,
  `schemaUnion_kb5Tags_iff_KB5Axiom`, `schemaUnion_d45Tags_iff_D45Axiom`,
  `schemaUnion_dbTags_iff_DBAxiom`) — all report only `propext`/`Quot.sound` (standard
  Lean/Mathlib axioms; zero new axiom).
- `lake exe checkInitImports` — exit 0, no violations.
- Full `lake lint` — "Linting passed for Cslib." (run after the final sub-phase).
- `lake exe lint-style` — clean, no output.
- No line exceeds the 100-character limit.
- No instance file, `SchemaUnion.lean`, or `DerivationTree.lean` was modified — fully additive.
- The deliberately-omitted `KB5 → S5` subsumption edge was grep-confirmed absent (subsumption
  is Phase 5's scope, not Phase 3's).

## Plan Deviations

None beyond the two proof-mechanics fixes documented above (both within-scope tactical fixes to
make the plan's specified bridge proofs compile, not changes to what was proved or where).
`SchemaBridges.lean` landed at the plan's proposed location with the plan's proposed imports
(the 15 instance files via the `ProofSystem.Instances` barrel, plus `SchemaUnion.lean`). All 15
bridges proved as genuine `↔` (no `sorry`, no one-directional weakening).

## Next Steps

Phase 4 (migrate the 15 per-system soundness proofs to `unionSound`) and Phase 5 (collapse
`AxiomSubsumption.lean`'s 24 lemmas to `Finset.subset` facts) both depend on this phase's tag
sets and bridges and can now proceed; Phase 6 (`IntToClassical.lean` hand-migration) also
depends on the bridges landed here. Per the wave map, Phases 4/5/6 are wave 3 and may run in
parallel across distinct file territories.
