# Task 180: Primitive G/H Metalogic — Implementation Summary

## Overview

Task 180 promoted `Temporal.Formula.allFuture` (𝐆, "always in the future") and
`Temporal.Formula.allPast` (𝐇, "always in the past") from derived abbreviations
(`𝐆φ := ¬𝐅¬φ`, `𝐇φ := ¬𝐏¬φ`) to **primitive inductive constructors** of `Temporal.Formula`,
so that intuitionistic temporal logics — where `𝐆φ` is strictly stronger than `¬𝐅¬φ`
([Boudou2017]) — are expressible in CSLib. This is the completion summary for the full
9-phase plan (`plans/03_primitive-gh-metalogic-plan.md`), with Phase 9 (this dispatch)
closing out the final classical-equivalence theorems, the missing BibKey, the downstream
sweep, and the full CI pipeline.

## What Changed, By Phase

- **P1 (Syntax):** `allFuture`/`allPast` promoted to `Formula` constructors; `someFuture`/
  `somePast` remain derived abbreviations (`𝐅φ := ⊤ U φ`, `𝐏φ := ⊤ S φ`).
- **P2 (Semantics):** `Satisfies` given direct clauses `∀ s, t < s → Satisfies M s φ` /
  `∀ s, s < t → Satisfies M s φ` for the two new constructors; semantic classical duality
  (`sat_allFuture_iff_neg_someFuture_neg`) proved as a genuine theorem (definitional at the
  semantic level, since `Satisfies` is a `Prop`-valued function, not a syntactic proof system).
- **P3 (ProofSystem):** Four bridge axioms added to the `Axiom` inductive:
  `allFuture_to_classic`, `classic_to_allFuture`, `allPast_to_classic`, `classic_to_allPast`.
  `allFuture_to_classic`/`allPast_to_classic` hold constructively; `classic_to_allFuture`/
  `classic_to_allPast` require Peirce's law (classical).
- **P4 (Soundness):** All four bridge axioms proved sound in both `Soundness.lean` and
  `DenseSoundness.lean`.
- **P5 (MCS/WitnessSeed):** Two reusable MCS-level bridge lemmas, `mcs_allFuture_iff` /
  `mcs_allPast_iff` (plus negated-form companions `mcs_not_allFuture_iff` /
  `mcs_not_allPast_iff`), route every MCS-level site that used to rely on the old defeq.
- **P6-P7 (Chronicle/TruthLemma):** Chronicle construction and the truth lemma made total
  over the new primitive constructors, closing the F1 root-cause defeq breakage identified in
  `reports/03`.
- **P8 (Tableau):** Tableau subtree (Defs/Rules/Closure/Branch/Saturation/TimeOrdering/
  Soundness/Completeness) made scoped-green with G/H constructor cases added throughout.
- **P9 (this dispatch):** see below.

## Phase 9: Classical-Equivalence Theorems, BibKey, Downstream Sweep, Full CI

### 1. Classical-equivalence theorems (`Theorems.lean`)

Added `Cslib.Logic.Temporal.Metalogic.allFuture_iff_neg_someFuture_neg` and
`allPast_iff_neg_somePast_neg`:

```
def allFuture_iff_neg_someFuture_neg (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.allFuture ↔ ¬𝐅¬φ)
```

Each is a thin wrapper: the two bridge-axiom directions
(`allFuture_to_classic`/`classic_to_allFuture`, resp. past) are combined via the existing
`pairing` propositional combinator (`Metalogic.pairing : ⊢ A → B → A ∧ B`) and two
`modus_ponens` applications, since `Formula.iff φ ψ := (φ→ψ) ∧ (ψ→φ)`.

**D3 honesty caveat** (stated in both the module docstring and the theorem docstrings):
this `Iff` is a theorem *about* `HilbertBX`, assembled from two axioms — it is **not**
derived from the propositional/mono axiom fragment. Such a derivation is impossible once
G/H are primitive (F2): `classic_to_allFuture`/`classic_to_allPast` genuinely require
Peirce's law. Soundness of the bridge (proved in Phase 4) is an *assertion* of
conservativity over the classical fragment, not a syntactic *proof* of it. PM4/PM6 were
honored: no attempt was made to re-derive the equivalence from the mono axioms, and Phase 9
was not reordered earlier.

### 2. Completeness.lean / DenseCompleteness.lean

`Completeness.lean` built unchanged, as expected (F7: TruthLemma is total).
`DenseCompleteness.lean` had one **genuine (non-mechanical) defeq break**, not anticipated
by the "no constructor match, build-only" plan wording:

- `limit_satisfies_c4` (in `ChronicleConstruction.lean`) is stated in the raw
  `¬(Formula.untl ξ η) ∈ limitF ...` encoding.
- `g_dense_indicator_in_dense_mcs` produces a `𝐆(¬utb) ∈ limitF A h_base_mcs 0` membership
  (primitive-constructor form).
- Pre-task-180, these were defeq (`allFuture` was *defined* as `¬(⊤ U ¬·)`); now they are not.

**Fix** (`DenseCompleteness.lean:203-210`): route through the existing `mcs_allFuture_iff`
bridge lemma (the exact F4 reuse pattern the plan anticipated for MCS-level sites) to convert
the `𝐆(¬utb)` membership into the raw `¬(⊤ U ¬¬utb)` form that `limit_satisfies_c4` expects,
rather than touching `limit_satisfies_c4` itself.

### 3. Boudou2017 BibKey

Added to `references.bib` (root):

```bibtex
@inproceedings{Boudou2017,
  author = {Boudou, Jo{\"e}l and Di{\'e}guez, Mart{\'i}n and Fern{\'a}ndez-Duque, David},
  title  = {A Decidable Intuitionistic Temporal Logic},
  booktitle = {26th EACSL Annual Conference on Computer Science Logic (CSL 2017)},
  series = {LIPIcs}, volume = {82}, pages = {14:1--14:17}, year = {2017},
  doi    = {10.4230/LIPIcs.CSL.2017.14}
}
```

Burgess 1982 (referenced at `TruthLemma.lean:34`) remains absent from `references.bib` —
flagged as a follow-up, **not added** in this dispatch (exact publication metadata was not
verified against a citation database here; adding an unverified BibTeX entry would violate
the citation-accuracy standard more than leaving the gap documented).

### 4. Lint cleanup

Fixed the recurring `unusedSimpArgs` warning in `Metalogic/TemporalContent.lean` (two sites,
12 individual unused-argument warnings): both `simp only` calls unfolded
`Formula.allFuture, Formula.allPast, Formula.someFuture, Formula.somePast, Formula.neg,
PropositionalConnectives.neg, Formula.top, PropositionalConnectives.top` to prove a
`swapTemporal`-commutation equation, but (now that `allFuture`/`allPast` are primitive,
not defined via `top`) only `Formula.swapTemporal` unfolding was actually needed. Reduced
both `simp only` lists to `[Formula.swapTemporal]`; both proofs still close, zero warnings.

The pre-existing, out-of-scope space-before-semicolon errors in
`Cslib/Logics/Modal/Tableau/Completeness.lean:432,491` were left untouched per the dispatch
scope (unrelated to task 180).

### 5. Downstream sweep

Built and, where necessary, mechanically repaired every consumer of `Temporal.Formula`
outside the `Cslib/Logics/Temporal/` tree:

- **`Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean`** — `Temporal.Formula.toBimodal`
  was missing the `allFuture`/`allPast` cases (`Missing cases` error). Added:
  ```
  | .allFuture φ => Bimodal.Formula.allFuture (φ.toBimodal)
  | .allPast φ => Bimodal.Formula.allPast (φ.toBimodal)
  ```
  mapping the temporal primitives to Bimodal's own **classical** `allFuture`/`allPast`
  abbreviations (`Bimodal.Formula` has no primitive G/H). This is a syntactic translation
  choice for the embedding target, not a re-derivation of the Temporal-side bridge — documented
  in the `toBimodal` docstring. Added matching `toBimodal_allFuture`/`toBimodal_allPast` simp
  lemmas following the file's existing pattern.
- **`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean`** —
  `bimodal_truthAt_toBimodal_iff_temporal_satisfies` (structural induction on
  `Temporal.Formula`) was missing the `allFuture`/`allPast` induction cases (`Alternative ...
  has not been provided` error). Closed using the pre-existing Bimodal semantic lemmas
  `Truth.future_iff`/`Truth.past_iff` (`truthAt M Omega τ t φ.allFuture ↔ ∀ s, t < s →
  truthAt ... φ`), which already exactly match the temporal `Satisfies` clause shape — no new
  semantic lemmas were needed, only wiring the induction hypothesis through.
- **Clean (no changes needed):** `Core.DerivationTree`, `Core.DeductionTheorem`,
  `Core.GenericMCSBridge`, `Embedding.PropositionalEmbedding`, `Syntax/Formula.lean`,
  `Cslib.Foundations.Data.OmegaSequence.Temporal`,
  `Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived`.

No downstream consumer required substantial rework; **no follow-up task was needed** for the
Bimodal/Foundations subtree (the Rollback/Contingency "independent PR-ready" clause was not
triggered).

### 6. `mk_all --module`

Not run — no new files were added in this dispatch (only edits to existing files); the
`Cslib.lean` barrel is unchanged.

## The Four Bridge Axioms (Recap)

| Axiom | Statement | Direction |
|---|---|---|
| `allFuture_to_classic φ` | `𝐆φ → ¬𝐅¬φ` | constructive |
| `classic_to_allFuture φ` | `¬𝐅¬φ → 𝐆φ` | classical (Peirce) |
| `allPast_to_classic φ` | `𝐇φ → ¬𝐏¬φ` | constructive |
| `classic_to_allPast φ` | `¬𝐏¬φ → 𝐇φ` | classical (Peirce) |

Proved sound in `Soundness.lean`/`DenseSoundness.lean` (Phase 4); packaged as the `Iff`
theorems `allFuture_iff_neg_someFuture_neg`/`allPast_iff_neg_somePast_neg` in `Theorems.lean`
(Phase 9, this dispatch).

## Full CI Results (Phase 9 completion gate)

| Step | Result |
|---|---|
| `lake build` (whole project) | **PASS** — 3186/3186 jobs, first full green since Phase 1 |
| `lake exe checkInitImports` | **PASS** — no output |
| `lake exe lint-style` | **PASS** on all task-180-touched files (2 pre-existing, out-of-scope errors remain in `Cslib/Logics/Modal/Tableau/Completeness.lean:432,491`, unrelated to task 180) |
| `lake test` | **PASS** — 9177/9177 jobs, `CslibTests` suite green |
| `lake shake --add-public --keep-implied --keep-prefix` | **PASS** — none of the task-180-touched files appear in the shake suggestion list; all suggestions are pre-existing, in unrelated Propositional/Modal/LTL modules |
| `lean_verify` (`chronicle_truth_lemma`, `completeness`, `soundness_thderivable`, `dense_indicator_in_all_limit_points`, `allFuture_iff_neg_someFuture_neg`, `allPast_iff_neg_somePast_neg`) | **PASS** — all report only `[propext, Classical.choice, Quot.sound]` (standard Lean/Mathlib axioms); zero `sorry`, zero new custom axioms |

## Files Modified (Phase 9)

- `Cslib/Logics/Temporal/Theorems.lean` — added the two classical-equivalence theorems + module docstring
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` — lint fix (unusedSimpArgs), 2 sites
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` — MCS-bridge fix for a genuine (not merely missing-case) defeq break
- `references.bib` — added `Boudou2017`
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` — added `allFuture`/`allPast` cases + simp lemmas
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` — added `allFuture`/`allPast` induction cases

## Plan Deviations

1. **DenseCompleteness.lean required a genuine fix, not a build-only verification.** The plan
   text ("verify they carry through unchanged... no constructor match; build-only") was
   correct for `Completeness.lean` but not for `DenseCompleteness.lean`, which had a
   `limit_satisfies_c4` call site relying on the pre-task-180 `allFuture`-defeq. Closed via
   the established `mcs_allFuture_iff` bridge pattern (no scope expansion — same lemma family
   the plan already anticipated for MCS-level sites).
2. **Burgess 1982 BibKey not added.** The plan listed this as optional ("Optionally flag...
   as a follow-up"); left as a documented follow-up rather than adding an unverified BibTeX
   entry.
3. **No downstream follow-up tasks were needed.** The plan's Rollback/Contingency anticipated
   possible "substantial rework" consumers requiring a separate follow-up task; both
   downstream breaks found (`TemporalEmbedding.lean`, `TemporalConservativity.lean`) were
   cleanly mechanical and closed inline.

## Preserved Assets (Unmodified)

Phases 1-8's committed content (Syntax, Semantics, ProofSystem, Soundness, MCS/WitnessSeed,
Chronicle, TruthLemma, Tableau subtree) was not touched in this dispatch except for the one
genuine `DenseCompleteness.lean` fix described above, which does not touch any Phase 1-8 file
outside `Metalogic/DenseCompleteness.lean` itself.
