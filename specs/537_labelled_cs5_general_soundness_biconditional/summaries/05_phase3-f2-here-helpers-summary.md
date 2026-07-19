# Implementation Summary: Phase 3 — F2 target-raise + reflexive here-extraction helper

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm
  8.1.4's biconditional
- **Plan**: plans/02_direct-route.md (v2), Phase 3
- **Status**: [COMPLETED]

## What Landed

File: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, inserted immediately
after the landed `cs5FCIncest_lift` (F1) and before the Phase 1 base-lemma section.

1. **`cs5FCIncest_raise`** (= plan's `F2`): `r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u'`. Proved via
   `hsymbox hwu huu'` (raises the target `u` across `≤`, landing at a fresh `t` with `w ≤ t`),
   then `hincest` on the resulting `r u' t` (giving a `≤`-successor `w'` of `t` with `r w' u'`),
   composed by `Preorder.trans`. 6 lines including the `obtain`s.
2. **`box_gives_here`**: `CKForces … w (□A) → CKForces … w A`, via `hbox w (le_refl w) w
   (hrefl w)` — the same instantiation as the `tBox` axiom case (`CS5Canonical.lean:313`).

Both are sorry-free and axiom-clean (`lean_verify`: `{"axioms":[],"warnings":[]}` for each).
`lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` is green;
`lake exe checkInitImports` passes; `grep -n '\bsorry\b'` finds no tactic `sorry` (only prose
mentions of "sorry" inside docstrings/comments, all pre-existing).

## Plan Deviations

- **Dual diamond here-helper deferred to Phase 5.** The plan's third Phase 3 task ("Prove the
  dual diamond here-helper IF needed for `diaI` (dia-iff + `hrefl` + `ckforces_persistence`,
  Forcing.lean:122)") is explicitly conditional and, unlike `F2`/`box_gives_here`, carries no
  concrete target type in the plan text. Phase 5 (the main `NIK` soundness induction, which
  contains the `diaI` case that would consume this helper) has not been written yet, so the
  helper's actual required shape is not yet determined by any goal state. Landing a guessed
  signature now risks either (a) an unused lemma that doesn't match what `diaI`'s goal actually
  needs, or (b) a wrongly-shaped lemma masquerading as "done" that has to be redone in Phase 5
  anyway. This exercises the plan's own "IF needed" conditional rather than deviating from it —
  no scope was dropped, the item is explicitly carried forward to Phase 5 where its concrete
  shape will be dictated by the `diaI` goal state. No `sorry`, no axiom, no vacuous placeholder
  was used as a stand-in.

## Preserved Assets

Unregressed, confirmed by the same green scoped build: `cs5FCIncest_lift` (F1), `box_iff_base`,
`dia_iff_base`, `box_iff_TClosure`, `dia_iff_TClosure`, `nik_soundness_onePoint`,
`nik_TS5_consistent`, `cs5_soundness_derivable_incest`. `cs5FCIncest` itself is untouched (no
conjunct weakened).

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`: green.
- `lake exe checkInitImports`: clean (no output).
- `lean_verify` on `cs5FCIncest_raise` and `box_gives_here`: both `{"axioms":[],"warnings":[]}`.
- `grep -n '\bsorry\b' Soundness.lean`: 3 hits, all inside prose/docstrings (lines 237, 241, 292),
  zero tactic `sorry`.
- Full `lake lint` / `lint-style` / `shake` / `mk_all` / `test` deferred to the Phase 6 regression
  gate per the plan's dependency table (single-phase dispatch scope, matching Phase 2's
  precedent).

## Next Steps

Phase 4 (`boxI` tree-lifting lemma, split 4.1/4.2) is next per the plan's dependency table
(`Depends on: 3`). This is the plan's sole concentrated-risk phase.
