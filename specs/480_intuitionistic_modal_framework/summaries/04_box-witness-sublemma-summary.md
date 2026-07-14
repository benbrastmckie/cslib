# Implementation Summary: Phase 2b-sublemma — box_witness_pair_underivable

- **Task**: 480 - Intuitionistic modal metalogic FRAMEWORK
- **Phase**: 2b-sublemma (of 12; plan v4, hard-mode, single-phase dispatch)
- **Plan**: `specs/480_intuitionistic_modal_framework/plans/04_intuitionistic-modal-framework-hard-v4.md`
- **Status**: COMPLETED
- **File modified**: `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (additive only)

## What was proved

`box_witness_pair_underivable`: given `w u : CanonicalPrimeWorld Axioms` with
`{ψ | □ψ ∈ w.val} ⊆ u.val`, no finite disjunction of `Σ := {□B | B ∉ u.val}` is derivable from
`Γ := w.val ∪ {◇A | A ∈ u.val}`. This discharges the `DerivExcludes` precondition that Phase 2b's
seeded prime extension `w'` needs.

This resolves the v3 STOP contingency (recorded in
`specs/480_intuitionistic_modal_framework/progress/phase-2b-sublemma-progress.json`, prior
`design_blocker`): the argument genuinely requires the Fischer-Servi axiom `h_Idb` beyond
`h_K`/`h_Kdia`, exactly as report 03 (`reports/03_complete-axiom-requirements-ik-ck.md`) predicted
from a verbatim read of ianshil/CK `general_th_completeness.v`'s box case (~L211-249, `Idb`
selector at ~L231).

## Proof structure (transliterated from ianshil/CK)

1. `extract_box_list` / `extract_split`: given a finite derivation-context list drawn from
   `Σ`/`Γ`, split it into the bare excluded witnesses and the `w.val`/diamond-witness parts.
2. `boxOr_of_boxDisj`: a disjunction of already-boxed formulas implies the box of the (unboxed)
   disjunction (K + necessitation of `OrI1`/`OrI2`, combined via `OrE`).
3. `unpack_conj_partial`: combines the finitely many separately-used `◇A` context members into
   one `bigAnd`-conjunction hypothesis (`AndE1`/`AndE2`), analogous to ianshil/CK's
   `prv_list_left_conj`.
4. `dia_bigAnd_to_bigAnd_dia`: the valid monotonicity direction `◇(⋀Aⱼ) → ⋀(◇Aⱼ)` (`h_Kdia` +
   `AndE1`/`AndE2`/`AndI`), analogous to `list_conj_Diam_obj`.
5. Composing 2-4 places `(bigAnd Aⱼ → □(bigOr Bᵢ)) ∈ w.val`; bridging the antecedent to a single
   diamond via step 4 gives `(◇(bigAnd Aⱼ)).imp(□(bigOr Bᵢ)) ∈ w.val`; **`h_Idb`** then gives
   `□(bigAnd Aⱼ → bigOr Bᵢ) ∈ w.val`.
6. `{ψ | □ψ ∈ w.val} ⊆ u.val` places this implication in `u.val`; since `u.val` is deductively
   closed and contains each `Aⱼ` (`bigAnd_mem_u`), `bigOr Bᵢ ∈ u.val`.
7. `bigOr_mem_disjunct` (`u.val`'s disjunction property) forces some `Bᵢ ∈ u.val`, contradicting
   `Bᵢ ∉ u.val` (from `Σ`'s definition) — done.

## Plan Deviations

The general (multi-hypothesis) case of the argument additionally required `h_andI`/`h_andE1`/
`h_andE2` (`Cslib.Logic.Axioms.AndI`/`AndE1`/`AndE2`) as three parametric hypotheses beyond
report 03's per-lemma table (`h_K`, `h_Kdia`, `h_Idb` + intuitionistic base), needed to combine
finitely many diamond hypotheses into one conjunction before `h_Idb` applies (step 3-4 above;
mirrors ianshil/CK's `prv_list_left_conj` + `list_conj_Diam_obj`, which use the analogous `Idb`/
`Kd`-conjunction machinery under the hood). These are **not new axioms** — they are the standard
intuitionistic `and`-introduction/elimination schemata, already used elsewhere in this framework
(e.g. `MCS.lean`'s `mcs_and_mem_iff`) — only additional *parametric hypotheses* threaded through
this one lemma's signature, in the same style as `h_implyK`/`h_implyS`/etc. The four-axiom modal
set `{h_K, h_Kdia, h_Idb, h_Cd}` established by report 03 is **unchanged**. Recorded in the plan
v4 file (Phase 2b-sublemma task list) and in `.orchestrator-handoff.json`
(`deviation_from_report_03`), and flagged forward for Phase 2b to thread the same three
hypotheses into `canonical_box_witness`.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel` — succeeded, no warnings.
- `lake exe checkInitImports` — passed.
- `grep -nE "\bsorry\b|\badmit\b"` on the module — no matches.
- `lean_verify` on `box_witness_pair_underivable` — axioms: `[propext, Classical.choice]` only
  (standard Lean/Mathlib foundations; no new global axiom).
- `git diff --stat` — only `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean`
  changed, additively (Phase 2a's committed definitions, above the new content, untouched).

## sorry_inventory

None. Zero remaining `sorry`/`admit` in the module.

## Next phase

Phase 2b (`canonical_box_witness` + `modal_set_exclusion` wrapper), same file. Thread `h_K`,
`h_Kdia`, `h_Idb`, plus the newly-surfaced `h_andI`/`h_andE1`/`h_andE2`, and reuse
`box_witness_pair_underivable` directly to discharge the `DerivExcludes` precondition for the
seeded prime extension.
