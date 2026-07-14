# Phase 3b Summary: TruthLemma.lean — .box Case Helper

**Task**: 480 (intuitionistic modal framework) | **Plan**: v4 | **Phase**: 3b | **Status**: COMPLETED

## What Was Proved

`Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` gains a new theorem,
`truth_box_case`, the `.box` constructor case of the (to-be-assembled) `canonical_truth_lemma`:

```
BForces canonicalR canonicalVal botForces w (□φ) ↔ (□φ) ∈ w.val
```

taking the induction hypothesis for `φ` as an explicit parameter **universally quantified over
all canonical worlds** (matching the `truth_imp_case` 3a design note exactly), so this helper
builds sorry-free independently of the full recursion (assembled in Phase 3c).

- **Forward direction** (contrapositive): assuming `□φ ∉ w.val`, `canonical_box_witness`
  (Phase 2b, `CanonicalModel.lean`) produces `w' ≥ w` and a prime world `u` with
  `canonicalR w' u` and `φ ∉ u.val`. Instantiating the `BForces_box`-unfolded forcing hypothesis
  at this `w'`/`u` and applying `ih u` yields `φ ∈ u.val`, contradicting `φ ∉ u.val`.
- **Backward direction** (heredity over `≤ ∘ R`): assuming `□φ ∈ w.val`, any `w' ≥ w` inherits
  `□φ ∈ w'.val` by plain set inclusion (`w ≤ w'` is `w.val ⊆ w'.val`); `canonicalR w' u`'s box
  clause (`.1`) then gives `φ ∈ u.val` for any `u` with `canonicalR w' u`; `ih u` transports this
  to forcing.

`truth_box_case` threads `h_K`, `h_Kdia`, `h_Idb` (report 03 §4 row 6) — together with the base
intuitionistic hypotheses (`h_implyK`/`h_implyS`/`h_efq`/`h_orI1`/`h_orI2`/`h_orE`/`h_andI`/
`h_andE1`/`h_andE2`) that `canonical_box_witness` itself requires — **solely via the call to
`canonical_box_witness`**; no new axiom is introduced.

## Reference Grounding

- [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3, clause 3.2 (`.box` birelational forcing clause).
- ianshil/CK `general_th_completeness.v`, box case (~L211-249) — the construction consumed here
  is `canonical_box_witness`, already proved and frozen in Phase 2b.
- Report 03 §4 row 6 (axiom-requirement table): `truth_box_case` requires exactly
  `{h_K, h_Kdia, h_Idb}`, all consumed transitively through `canonical_box_witness`.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.TruthLemma` — succeeded (596 jobs), no
  warnings.
- `lake build` (full project) — succeeded (3190 jobs); the only warnings/sorries present are
  pre-existing and unrelated (`Cslib/Logics/Propositional/Tableau/*`), outside this task's scope.
- `lake exe checkInitImports` — passed (no output).
- `lake exe lint-style Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` — passed (no
  output).
- `lean_verify` on `truth_box_case`: `{propext, Classical.choice, Quot.sound}` only — no new
  axiom.
- `grep -rn "\bsorry\b"` on `TruthLemma.lean`: no real matches (only the substring inside
  "sorry-free" in docstrings).
- `git status --porcelain`: only `TruthLemma.lean` modified under `Cslib/`; `CanonicalModel.lean`
  and `PrimeTheory.lean` untouched.

## Plan Deviations

None. Followed the plan's design note exactly: IH as an explicit hypothesis universally
quantified over canonical worlds (matching 3a's `truth_imp_case` style), consuming the
pair-shaped `canonical_box_witness` witness, with the outer `∀ w' ≥ w` from `BForces_box`
matching the witness's `w ≤ w'` obligation. `simp only [BForces_box]` was the only `simp` use
(the permitted `@[simp]` unfold), per the postmortem's no-`simp`/`aesop` constraint.

## Next Steps

Phase 3c (HIGHEST RISK): prove `truth_diamond_case` (threading `h_Kdia`, `h_Cd`, and possibly
`h_Idb`, consuming `canonical_diamond_witness`), then assemble `canonical_truth_lemma` by
induction on `Proposition`, dispatching each of the seven constructors to its helper
(`truth_atom_case`/`truth_bot_case`/`truth_and_case`/`truth_or_case`/`truth_imp_case`/
`truth_box_case`/`truth_diamond_case`) and threading the full four-axiom union
`{h_K, h_Kdia, h_Idb, h_Cd}`.
