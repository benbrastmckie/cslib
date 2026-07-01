# Phase 3 Handoff — omegaPow_da_muller COMPLETE (task 241, McNaughton's theorem)

## Status: COMPLETED

Phase 3 is marked `[COMPLETED]` in
`specs/241_mcnaughton_theorem/plans/02_mcnaughton-choueka-route.md`. This supersedes
`phase3-partial-handoff.md` (which documented the state after Milestones 1-2 landed in a
prior dispatch). All 3 planned milestones are now green and committed.

## What is done (committed, scoped-build green, sorry-free, standard axioms only)

- Commit `11807051` (prior dispatch): `Cslib/Computability/Automata/DA/Choueka.lean` created
  with `DA.chouekaLang` (definition) and `DA.chouekaLang_regular` (regularity proof).
- Commit `602293de` (prior dispatch): same file, `DA.greater_subseq` (private helper) and
  `DA.chouekaLang_omega_limit_subset_omega_power` (the easier inclusion direction).
- Commit `8ba346f8` (this dispatch): same file, `DA.chouekaLang_omega_power_subset_omega_limit`
  (the harder, Ramsey-based reverse inclusion — the main remaining blocker) and
  `DA.chouekaLang_omega_power_eq_omega_limit` (the full Choueka identity, via antisymmetry).
- Commit `29ba3eb2` (this dispatch): `Cslib/Computability/Languages/OmegaRegularLanguage.lean`,
  `IsRegular.omegaPow_da_muller` — the final Phase 3 assembly (`M^ω` is DMA-recognizable for
  regular `M`), plus two new imports (`DA.Choueka`, `DA.Concat`).

Verified via `lake build Cslib.Computability.Automata.DA.Choueka
Cslib.Computability.Automata.DA.Concat Cslib.Computability.Automata.DA.MullerClosure
Cslib.Computability.Languages.OmegaRegularLanguage` (all green together, only warning is a
pre-existing out-of-scope `show`/`change` style lint inside the dead `buchiCongr_DMA` cluster
at OmegaRegularLanguage.lean:548, not touched this dispatch). `lean_verify` /
`#print axioms` on all three new theorems report only `propext`, `Classical.choice`,
`Quot.sound`. `grep -n "sorry\|admit"` on both touched files returns nothing.

## Two build-fix notes for future Choueka-adjacent work

1. The Kleene-star postfix notation `∗` is `scoped[Computability]` (declared in
   `Mathlib.Algebra.Order.Kleene`) — `Choueka.lean` needed `open scoped Computability` added
   (it previously only opened `Cslib.FLTS`/`Automata.DA.FinAcc` scopes). Without this, `l∗` in
   a theorem signature fails to parse with a cryptic "expected token" error pointing at the
   preceding identifier, not the `∗` itself.
2. Order lemmas like `kstar_mul_le_kstar : a∗ * a ≤ a∗` and `le_hmul_congr` do not unfold to a
   raw `Set.Subset`-shaped Pi type at default transparency when applied as a function while
   their implicit type-class argument (`a`) is still an unresolved metavariable — "Function
   expected" errors result. Fix: supply the implicit explicitly, e.g.
   `kstar_mul_le_kstar (a := l)`, before applying it to a membership proof. Separately,
   `ωLanguage`'s `⊆` is literally defined as `HasSubset.Subset := ⟨(· ≤ ·)⟩`, so `≤`- and
   `⊆`-stated facts about `ωLanguage`/`Language` interchange freely via `exact`/`rw` once the
   value is concrete, but proving an *equality* of `ωLanguage`s needs `le_antisymm` (not
   `Set.Subset.antisymm`, which fails to unify against the `ωLanguage`-typed goal).

## What remains (next steps for this task)

Phase 3 is done. Per the plan's dependency table (Wave 3), **Phase 5** (`IsRegular.to_da_muller`,
the forward assembly) is now unblocked (it depends on Phases 2, 3, 4 — all green). Phase 5's
recipe (already in the plan, `plans/02_mcnaughton-choueka-route.md`, Phase 5 section):
1. `obtain ⟨n, l, m, hreg, rfl⟩ := (eq_fin_iSup_hmul_omegaPow p).mp hp` → `p = ⨆ i, (l i)*(m i)^ω`.
2. For each `i`: `(m i)^ω` DMA-recognizable via `IsRegular.omegaPow_da_muller` (this dispatch);
   `(l i) * (m i)^ω` DMA-recognizable via `DA.concat_language_eq` (Phase 2, green) with regular
   `l i`.
3. Fold the finite family into a single DMA via `Muller.exists_iSup`/`Muller.exists_iSup_univ`
   (Phase 4, green, in `Cslib/Computability/Automata/DA/MullerClosure.lean`).
4. Thread `Finite`/universe bookkeeping (`isRegular_iff`); conclude
   `∃ S (_ : Finite S) (da : DA.Muller S Symbol), language da = p`.

After Phase 5, **Phase 6** assembles the final `iff_da_muller` theorem and deletes the dead
`buchiCongr_DMA` cluster (5 declarations, all `private` or a superseded `proof_wanted`,
self-contained per the plan's Disposition section) plus runs the full CI pipeline.

## Key files

- `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/DA/Choueka.lean` (473 lines total
  after this dispatch; Milestone 3 additions are the bottom ~150 lines)
- `/home/benjamin/Projects/cslib/Cslib/Computability/Languages/OmegaRegularLanguage.lean`
  (`IsRegular.omegaPow_da_muller` at approximately line 96, right after
  `IsRegular.omegaLim_da_muller`; `IsRegular.eq_fin_iSup_hmul_omegaPow` at ~line 205 is Phase 5's
  starting point; the dead `buchiCongr_DMA` cluster — untouched — spans roughly lines 388-560)
- `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/DA/Concat.lean` (Phase 2, unchanged,
  already green — `concat_language_eq`)
- `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/DA/MullerClosure.lean` (Phase 4,
  unchanged, already green — `Muller.union`, `Muller.exists_iSup_univ`)
- `/home/benjamin/Projects/cslib/specs/241_mcnaughton_theorem/plans/02_mcnaughton-choueka-route.md`
  (Phase 3 section now `[COMPLETED]`; Phase 5 section has the next recipe)

## Environment note

An unrelated concurrent-task file set (`Cslib/Logics/Modal/Tableau/*`,
`Cslib/Logics/Temporal/*`, `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`) is
mid-edit in this shared working tree (tasks 180/442), which blocks `lake exe checkInitImports`,
whole-project `lake build`/`lake test`, and `lake shake`/`lake lint`. This is outside this
task's scope and was not touched, per the dispatch instructions. All Phase-3-relevant modules'
scoped builds (individually and combined) are green independent of that unrelated breakage.

## Sorry inventory

Empty. No `sorry`/`admit` were introduced. No new axioms.
