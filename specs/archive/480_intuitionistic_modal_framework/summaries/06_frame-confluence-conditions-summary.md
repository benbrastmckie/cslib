# Phase 2d Summary: Frame Confluence Conditions (`canonical_f1` / `canonical_f2`)

**Task**: 480 (intuitionistic modal framework) | **Plan**: v4 | **Phase**: 2d | **Status**: COMPLETED

## What Was Proved

`Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` gained a final
`CanonicalFrameConditions` section proving the two birelational frame-confluence obligations
required by `BFrame` (`Cslib/Logics/Modal/Semantics/Birelational.lean`):

- `canonical_f1` -- up-confluence, matching `BFrame.f1 : ∀ {w w' v}, w ≤ w' → r w v → ∃ v', r w' v' ∧ v ≤ v'`.
- `canonical_f2` -- down-confluence, matching `BFrame.f2 : ∀ {w v v'}, r w v → v ≤ v' → ∃ w', w ≤ w' ∧ r w' v'`.

With these two theorems, `CanonicalModel.lean` is now feature-complete: it contains all of
Phase 2's definitions (`CanonicalPrimeWorld`, `canonicalVal`, `canonicalR`), both witness lemmas
(`canonical_box_witness`, `canonical_diamond_witness`), and both frame conditions, sorry-free and
without introducing any new Lean `axiom`.

## Construction

**`canonical_f2` (down-confluence)** reuses Phase 2b's `box_witness_pair_underivable` and
`modal_set_exclusion` directly as black boxes. `canonicalR w v`'s box clause
(`∀ψ, □ψ∈w.val → ψ∈v.val`) combined with `v ≤ v'` gives exactly the `h_wu` precondition
`box_witness_pair_underivable` requires (with `u := v'`, already given -- no fresh prime
extension needed for the "diamond side" world). The seeded prime extension `w'` of
`w.val ∪ {◇A | A ∈ v'.val}` excluding `{□B | B ∉ v'.val}` is built exactly as in
`canonical_box_witness`'s Step 2.

**`canonical_f1` (up-confluence)** generalizes Phase 2c's `diamond_witness_underivable` from a
singleton seed formula `{φ}` to the full prime theory `v.val` as seed. A new private lemma
`canonical_f1_underivable` proves `Σ := {χ|◇χ∉w'.val}` is unreachable from
`Γ := v.val ∪ {ψ|□ψ∈w'.val}`: the finitely many `v.val`-drawn hypotheses in any derivation are
packed into a single conjunction `bigAnd Lv` (reusing `unpack_conj_partial` from Phase
2b-sublemma), so `canonicalR w v`'s diamond clause (`∀ψ∈v.val, ◇ψ∈w.val`) applies to this ONE
formula, giving `◇(bigAnd Lv) ∈ w.val ⊆ w'.val` directly -- sidestepping the invalid
"conjunction of diamonds implies diamond of conjunction" direction that would otherwise be
needed. A new generic private helper `extract_split_union` (2-way list partition by pointwise
`P ∨ Q`) supports the split of the derivation context into the `v.val`-part and the
`{ψ|□ψ∈w'.val}`-part.

## Axioms Consumed (machine-verified via `lean_verify`)

| Theorem | Modal axioms threaded (beyond intuitionistic base) |
|---------|------------------------------------------------------|
| `canonical_f1` | `h_K`, `h_Kdia`, `h_Cd`, `h_dbot` |
| `canonical_f2` | `h_K`, `h_Kdia`, `h_Idb` |

Both `lean_verify` results: `{propext, Classical.choice, Quot.sound}` only -- the three standard
classical axioms, no new axiom introduced. This is a superset of the plan v4 table's highlighted
`h_Kdia + h_Cd` (f1) / `h_Kdia + h_Idb` (f2) -- `h_K` and (for f1) `h_dbot` are also genuinely
required, transitively via the reused Phase 2b/2c machinery (`box_context_deriv`,
`box_witness_pair_underivable`, `diaOr_of_diaDisj`). No axiom outside the framework's confirmed
minimal set `{h_K, h_Kdia, h_Idb, h_Cd, h_dbot}` is used.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel` -- succeeded (595 jobs), no warnings.
- `lake exe checkInitImports` -- passed (exit 0).
- `grep -rn '\bsorry\b' Cslib/` -- zero hits in the touched file.
- `lean_verify canonical_f1` / `lean_verify canonical_f2` -- both `{propext, Classical.choice, Quot.sound}`.

## Plan Deviations

None in substance. The plan v4 table's per-lemma axiom row for Phase 2d listed only the
"headline" new modal hypotheses (`h_Kdia, h_Cd` for f1; `h_Kdia, h_Idb` for f2); the actual
threaded signatures also include `h_K` (both) and `h_dbot` (f1 only), which are structurally
unavoidable since both proofs reuse the full Phase 2b/2c machinery. This was anticipated by the
task's instruction to "confirm actual consumed set with lean_verify" and is recorded in the plan
file's Phase 2d completion note. No workaround, shortcut, or debt was introduced.

## Files Touched

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (append-only, +289 lines: 985 -> 1274)
- `specs/480_intuitionistic_modal_framework/plans/04_intuitionistic-modal-framework-hard-v4.md` (Phase 2d marked `[COMPLETED]`)
- `specs/480_intuitionistic_modal_framework/progress/phase-2d-progress.json` (new)
- `specs/480_intuitionistic_modal_framework/.orchestrator-handoff.json` (overwritten)

## Next Action

Phase 3a: create `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` (a NEW file,
importing the now-complete `CanonicalModel.lean`), transliterating the five non-modal
truth-lemma case helpers (`atom`/`bot`/`and`/`or`/`imp`) from `IntStrongCompleteness.lean:108-214`.
`CanonicalModel.lean` is frozen from this point forward.
