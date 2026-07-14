# Phase 3a Summary: TruthLemma.lean — 5 Non-Modal Case Helpers

**Task**: 480 (intuitionistic modal framework) | **Plan**: v4 | **Phase**: 3a | **Status**: COMPLETED

## What Was Proved

New file `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` (~330 lines), importing
the now-frozen `CanonicalModel.lean` (through Phase 2d, commit `10730569`). It contains the five
non-modal cases of the (to-be-assembled) `canonical_truth_lemma` as standalone, named helper
lemmas, each sorry-free and axiom-free:

- `truth_atom_case` — `BForces canonicalR canonicalVal botForces w (.atom p) ↔ (.atom p) ∈ w.val`
  (`Iff.rfl`, by definition of `canonicalVal`).
- `truth_bot_case` — parametric in `botForces`, taking an explicit bridging hypothesis
  `h_bot : ∀ w, botForces w ↔ (⊥ : Proposition Atom) ∈ w.val`. `botForces` is never hard-coded to
  `fun _ => False`, per the plan's Goals/Postmortem, so the minimal (495) / CK (493)
  fallible-world instantiations can reuse this helper unmodified.
- `truth_and_case` — takes `ihφ`/`ihψ` (the induction hypothesis for each conjunct, at the
  current world) as explicit hypothesis parameters.
- `truth_or_case` — same IH-as-hypothesis pattern; the backward direction uses the canonical
  prime world's disjunction property (`w.property.2`), the reason prime theories (not maximal
  consistent sets) are used as canonical worlds.
- `truth_imp_case` — takes `ihφ`/`ihψ` **universally quantified over all canonical worlds**
  (not just the current one), since the forward direction constructs a fresh successor world
  `T ≥ w` via `modal_imp_witness` + `modal_prime_exclusion` and needs the IH there; this matches
  exactly what the assembled recursive `canonical_truth_lemma` will supply in Phase 3c.

Two small supporting lemmas were added to keep the case proofs `simp`/`aesop`-free (matching
the existing `CanonicalModel.lean` style, which never uses `simp` for list-membership
bookkeeping):

- `canonical_bot_not_mem` — `⊥` is never a member of a canonical prime world's theory (modal
  analogue of `Cslib.Logic.PL.int_dccs_bot_not_mem`); this is the fact that discharges
  `truth_bot_case`'s `h_bot` hypothesis for the intuitionistic instantiation
  (`botForces := fun _ => False`), to be wired up in Phase 4.
- `canonical_imp_property` — modus-ponens closure for canonical prime worlds (modal analogue of
  `Cslib.Logic.PL.int_dccs_imp_property`), used by `truth_imp_case`'s backward direction.

## Transliteration

All five cases are line-for-line transliterations of `Cslib.Logic.PL.int_truth_lemma`
(`Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean:108-214`), substituting
`PL.Proposition Atom` → `Proposition Atom`, `IntPropAxiom` → the abstract `Axioms` predicate
(with `h_andI`/`h_andE1`/`h_andE2`/`h_orI1`/`h_orI2`/`h_implyK`/`h_implyS`/`h_efq`/`h_orE` as
explicit hypotheses in the framework's established style, mirroring `CanonicalModel.lean`), and
`int_imp_witness`/`int_prime_exclusion` → `modal_imp_witness`/`modal_prime_exclusion`
(`PrimeTheory.lean`, Phase 1, preserved/imported unmodified). No modal axiom
(`h_K`/`h_Kdia`/`h_Idb`/`h_Cd`/`h_dbot`) is threaded anywhere in this file — the non-modal cases
need none (report 03 §4 row 8).

All proofs use explicit `DerivationTree` term-mode combinators (`.ax`/`.assumption`/
`.modus_ponens`/`.weakening`) and `List.mem_cons.mp`/`.mpr` + `nomatch`/`rcases` for membership
bookkeeping — no `simp`/`aesop` anywhere in the file (postmortem constraint honored).

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.TruthLemma` — succeeded (596 jobs), no
  warnings.
- `lake exe checkInitImports` — passed (no output).
- `lake exe lint-style Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` — passed (no
  output).
- `lean_verify` on all five cases + the two supporting helpers: only standard axioms
  (`propext`, `Classical.choice`, `Quot.sound` — the last two only in `truth_imp_case`, via
  `Set.Subset.trans`/classical existentials in the underlying infra); no new axiom introduced.
- `grep -rn "\bsorry\b\|\badmit\b"` on the new file: no matches (the only "sorry" occurrences are
  the substring inside "sorry-free" in docstrings).
- `git diff --stat -- Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` — empty:
  the frozen Phase 2 file is untouched.

## Plan Deviations

None. The design note (each case as a named helper taking the IH as an explicit hypothesis) was
followed exactly as specified in plan v4. The two supporting lemmas
(`canonical_bot_not_mem`/`canonical_imp_property`) were not explicitly named in the plan but are
direct, expected transliterations of `IntLindenbaum.lean`'s `int_dccs_bot_not_mem`/
`int_dccs_imp_property`, needed as internal plumbing for `truth_bot_case`/`truth_imp_case` to
stay `simp`/`aesop`-free; this matches the plan's estimated-output note allowing "docstrings +
supporting helpers."

## Next Steps

Phase 3b: prove `truth_box_case` (or equivalent), consuming `canonical_box_witness` and
threading `h_K`/`h_Kdia`/`h_Idb`. Phase 3c: prove `truth_diamond_case` (threading `h_Kdia`,
`h_Cd`, `h_dbot`) and assemble the full `canonical_truth_lemma` recursion dispatching to all
seven case helpers (the five here + `truth_box_case` + `truth_diamond_case`).
