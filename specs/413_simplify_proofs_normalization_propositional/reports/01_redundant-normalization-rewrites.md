# Research Report: Simplify Verbose Proofs Using Existing Normalization Lemmas

**Task**: 413
**Type**: cslib
**Session**: sess_1785258473_63f7b4_413
**Date**: 2026-07-28

---

## 1. Executive Summary

The task premise required a **second reconciliation**. The description scopes the work to
"verbose `Propositional/` proofs (manual `simp only [listImp_*, bigconj_*]` lists)". A repo-wide
grep confirms:

- **Zero** `simp only [...listImp...]` or `simp only [...bigconj...]` occurrences exist anywhere
  under `Cslib/Logics/Propositional/`.
- `bigconj` is referenced in exactly two files repo-wide
  (`Cslib/Foundations/Logic/Theorems/BigConj.lean`,
  `Cslib/Logics/Temporal/Syntax/BigConj.lean`) — **never** in `Propositional/`.
- All **20** `simp only [listImp_*|bigconj_*]` sites live in `Foundations/`, `Modal/`,
  `Temporal/`, and `Bimodal/`, plus one file under `Propositional/Metalogic/`.

So the *named files* are wrong, but the *underlying defect is real and larger than described*.
The actual finding is stronger than proof-golf:

> **Every one of the 20 `simp only [listImp_*|bigconj_*]` invocations in the repository is
> redundant, along with 15 accompanying `unfold ListDeriv` / `simp only [<DS-def>]` unfolds.
> All 20 are `rfl`-lemma rewrites that `exact` already discharges by defeq.**

This was **verified empirically**, not inferred: all 8 affected files were edited, a **full
`lake build` (3309 jobs) completed green**, and `lake lint` reports nothing on any changed file.
The verified diff is **62 net lines removed across 8 files** and is saved at
`/home/benjamin/Projects/cslib/specs/413_simplify_proofs_normalization_propositional/verified-simplification.patch`.

**Recommended scope change**: retarget the task from "Propositional/ proof golf" to
"remove redundant `listImp`/`bigconj` normalization rewrites repo-wide". One file
(`Propositional/Metalogic/GenericMCSBridge.lean`) is still in the originally-named directory,
so the retarget is a superset, not a pivot.

---

## 2. Reuse Check Protocol (CSLib reuse-first)

Mandatory before any recommendation. **No new definitions, lemmas, or abstractions are
recommended by this report.** The work is purely deletion of redundant tactic steps.

| Check | Result |
|-------|--------|
| Does `Cslib.Foundations` already have the normalization lemmas? | Yes — `listImp_nil`, `listImp_cons`, `listImp_axiom_k`, `listImp_axiom_s` in `Foundations/Logic/Metalogic/ListImplication.lean`; `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`, `negBigconj_def` in `Foundations/Logic/Theorems/BigConj.lean`. |
| Are they already tagged for automation? | Yes — every one is `@[simp, scoped grind =]`. |
| Do they need co-tags / new attributes? | **No.** The original premise (task-268 "co-tags") is moot: the lemmas are already `@[simp]` AND `scoped grind =`. |
| Is a new abstraction needed? | **No.** |
| Existing typeclass hierarchy touched? | `HasImp`, `HasBot`, `InferenceSystem`, `ModusPonens`, `MinimalHilbert`, `HilbertTree` — all reused unchanged. |
| Namespaces searched (both `Foundations/Logic/` and `Logics/`) | Yes — `Cslib.Logic.Metalogic.ListImplication`, `Cslib.Logic.Theorems.BigConj`, `Cslib.Logic.Metalogic.GenericMCS`, and the four per-logic `GenericMCSBridge` files. |

---

## 3. Root Cause: Why All 20 Sites Are Redundant

Three definitional identities collapse the entire rewrite chain:

1. **`listImp` reduces by `rfl`.** In
   `Cslib/Foundations/Logic/Metalogic/ListImplication.lean:46-55`:
   ```lean
   def listImp : List F → F → F
     | [], φ => φ
     | (ψ :: Ψ), φ => HasImp.imp ψ (listImp Ψ φ)
   ```
   Both `listImp_nil` and `listImp_cons` are proved `:= rfl`.

2. **`ListDeriv` is a transparent `def`.**
   `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean:48-49`:
   ```lean
   def ListDeriv (Γ : List F) (φ : F) : Prop :=
     InferenceSystem.DerivableIn S (listImp Γ φ)
   ```

3. **The derivation-system `Deriv` projection is a structure field.**
   `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean:127-128`
   (`algebraicDerivationSystem` with `Deriv := ListDeriv (S := S)`) and
   `GenericMCS.lean:234-236` (`@[reducible] def treeAlgDS ... := algebraicDerivationSystem ...`).

Therefore `(propAlgDS Axioms).Deriv Γ φ`, `ListDeriv Γ φ`, and
`InferenceSystem.DerivableIn S (listImp Γ φ)` are all **definitionally equal**, and for `Γ = []`
so is `DerivableIn S φ`. `exact` elaborates up to defeq, so every
`simp only [propAlgDS, treeAlgDS, algebraicDerivationSystem]`, `unfold ListDeriv`, and
`simp only [listImp_nil]` preceding an `exact` is a no-op on the elaboration outcome.

The same argument applies to `bigconj`: `bigconj_nil`, `bigconj_singleton`, and
`bigconj_cons_cons` are all `:= rfl` (`Foundations/Logic/Theorems/BigConj.lean:70-84`).

**Note**: the source files' own docstrings already assert this defeq — e.g.
`Temporal/Metalogic/GenericMCSBridge.lean` says the two systems "are definitionally equal (both
reduce to `Nonempty (DerivationTree fc [] (listImp Γ φ))`)". The proofs simply did not act on
what the docstrings already knew.

---

## 4. Verified Change Set (all empirically confirmed)

Diff stat from the verified experiment:

```
 Cslib/Foundations/Logic/Metalogic/GenericMCS.lean            |  3 +--
 Cslib/Foundations/Logic/Metalogic/ListDeduction.lean         |  5 +----
 Cslib/Foundations/Logic/Metalogic/MCSProperties.lean         |  4 ++--
 Cslib/Foundations/Logic/Theorems/BigConj.lean                |  4 ----
 Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean    | 25 +++-----------
 Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean           | 17 +----------
 Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean   |  5 -----
 Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean        | 19 ++---------
 8 files changed, 10 insertions(+), 72 deletions(-)
```

### 4.1 Tier A — The four `GenericMCSBridge` forward proofs (largest win)

All four `derivTreeToList*` proofs share an identical, copy-pasted shape. Each induction arm is
preceded by a `simp only [<algDS alias>, treeAlgDS, algebraicDerivationSystem]` that does nothing.
The `necessitation` / `temporal_necessitation` / `temporal_duality` arms additionally build a
`have h_thm : DerivableIn ... ψ := by unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih`
whose entire purpose is to restate `ih` at a defeq type — `ih` can be used directly.

| File | Proof | Tactic lines before | after |
|------|-------|--------------------:|------:|
| `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` | `derivTreeToList` (L116-133) | 12 | 7 |
| `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` | `derivTreeToList` (L117-146) | 24 | 11 |
| `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` | `derivTreeToListFc` (L152-181) | 26 | 12 |
| `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` | `derivTreeToListFc` (L168-205) | 32 | 13 |

Representative before/after (Modal `necessitation` arm — 12 lines to 2):

```lean
-- BEFORE
| @necessitation ψ _d ih =>
  simp only [modalAlgDS, treeAlgDS, algebraicDerivationSystem] at *
  have h_thm : InferenceSystem.DerivableIn (ClosedHilbert (DerivationTree Axioms)) ψ := by
    unfold ListDeriv at ih
    simp only [listImp_nil] at ih
    exact ih
  unfold ListDeriv
  simp only [listImp_nil]
  exact ⟨DerivationTree.necessitation ψ h_thm.toDerivation⟩

-- AFTER
| @necessitation ψ _d ih =>
  exact ⟨DerivationTree.necessitation ψ ih.toDerivation⟩
```

### 4.2 Tier B — Foundations sites

| File:line | Before | After |
|-----------|--------|-------|
| `Foundations/Logic/Metalogic/MCSProperties.lean:110` | `unfold ListDeriv; simp only [listImp_nil]; exact h_ax` | `exact h_ax` |
| `Foundations/Logic/Metalogic/MCSProperties.lean:125` | `unfold ListDeriv; simp only [listImp_nil]; exact h_thm` | `exact h_thm` |
| `Foundations/Logic/Metalogic/ListDeduction.lean:80-84` | 4 lines (`have ih' := ih h` / `unfold ListDeriv at ih' ⊢` / `simp only [listImp_cons]` / `exact ...`) | `exact ModusPonens.mp HasAxiomImplyK.implyK (ih h)` |
| `Foundations/Logic/Metalogic/GenericMCS.lean:242` | `\| [], d, _ => by simpa only [listImp_nil] using d` | `\| [], d, _ => d` |
| `Foundations/Logic/Metalogic/GenericMCS.lean:244` | `simp only [listImp_cons] at d` | (deleted) |
| `Foundations/Logic/Theorems/BigConj.lean:114` | `simp only [bigconj_cons_cons] at hconj` | (deleted) |
| `Foundations/Logic/Theorems/BigConj.lean:127,132,135` | `simp only [bigconj_nil]` / `[bigconj_singleton]` / `[bigconj_cons_cons]` | (all deleted) |

**Special attention — `GenericMCS.lean:242`.** `unfoldListImp` is a `noncomputable def`
returning **data** (`D Γ φ`), not a `Prop`. Changing `by simpa only [listImp_nil] using d` to
plain `d` alters the produced *term* (removes an `Eq.mpr` wrapper), which could in principle
affect downstream reduction. This is exactly why full-project verification (§5) was run rather
than per-module builds. It is green. Any implementation must re-run the **full** build, not just
the changed modules.

---

## 5. Verification Performed (this is not a proposal — it compiles)

| Check | Command | Result |
|-------|---------|--------|
| Per-module (Propositional) | `lake build Cslib.Logics.Propositional.Metalogic.GenericMCSBridge` | green |
| Per-module (Modal) | `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` | green |
| Per-module (Temporal + Bimodal) | `lake build ...Temporal... ...Bimodal.Core...` | green |
| Foundations batch across whole project | `lake build` (3309 jobs) | green |
| **All 8 files simultaneously** | `lake build` (3309 jobs) | **green** |
| Environment linters | `lake lint`, filtered to the 8 changed files | **no output** |
| Residual target sites | `grep -c "simp only \[.*\(listImp\|bigconj\|negBigconj\)"` | **0** |

### Zero-Debt / sorry accounting

No `sorry` is introduced. The full build emits 4 pre-existing `sorry` warnings, all in files
**not touched** by this change set and all replayed from cache (not rebuilt):

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:570`, `:2583`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:124`
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118`

These are the baseline and are out of scope for this task.

The working tree was reverted to clean after verification (`git status --porcelain Cslib/` empty).
The verified diff is preserved at
`specs/413_simplify_proofs_normalization_propositional/verified-simplification.patch`.

---

## 6. Tactic Survey Results

Tactics evaluated against the target goals:

| Tactic | Verdict |
|--------|---------|
| `exact` (bare, relying on defeq) | **Chosen.** Closes every one of the 20 sites with no rewriting. Fastest and most robust. |
| `simp` (unrestricted) | Rejected. Works (lemmas are `@[simp]`) but is strictly worse than `exact`: slower, less predictable, and against CSLib/Mathlib library style. |
| `grind` | Rejected for these sites. The lemmas carry `scoped grind =`, so `grind` would close them, but invoking a search procedure where defeq suffices is a regression in both build time and reviewability. `grind` remains appropriately used at `ListDeduction.lean:78` (`grind [listImp_axiom_k]`), which should be left alone. |
| `aesop` | Rejected — same objection as `grind`, plus higher cost. |
| `simp only [...]` (status quo) | Rejected — the rewrites are provably no-ops here. |
| `omega` / `decide` / `norm_num` / `ring` / `linarith` | Not applicable (no arithmetic). |

**Important nuance for the planner**: the general CSLib guidance "prefer `simp only` over `simp`"
is about *lemma-set control*, not about inserting rewrites that do nothing. Deleting a no-op
`simp only` is not a move toward unrestricted `simp` — the resulting proofs contain **no** simp
call at all. This change makes the proofs *more* deterministic, not less.

---

## 7. Risks and Trade-Offs

1. **Defeq fragility (the real trade-off).** The simplified proofs rely on `ListDeriv` being a
   transparent `def` and `DerivationSystem.Deriv` being a plain field. If `ListDeriv` were ever
   made a `structure`, `irreducible`, or `@[reducible]`-gated, the bare `exact`s would break —
   whereas the `simp only [listImp_nil]` versions would (partly) survive.
   **Mitigation**: the surrounding docstrings already document and depend on this defeq
   (`listDerivToTree` in all four bridges delegates *purely* by defeq, with no tactic at all).
   The bridges are therefore already committed to this dependency; removing the rewrites just
   makes the commitment uniform. Recommend the implementer add a one-line comment at each
   `derivTreeToList*` noting the defeq reliance, replacing the deleted tactic noise with a real
   explanation.

2. **`unfoldListImp` is data.** See §4.2. Mitigated by full-project verification; must be
   re-verified with a full `lake build`.

3. **Comment loss.** Several deleted blocks carried useful explanatory comments (e.g. Modal's
   `-- ih : modalAlgDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn (ClosedHilbert ...) ψ`).
   These comments are *more* valuable now that the tactic steps are gone. Preserve them as
   standalone comments; do not delete them along with the tactics.

4. **Scope-creep risk.** 7 of the 8 files are outside `Propositional/`. This must be surfaced in
   the PR description and the task description should be updated. It is not a silent expansion.

5. **`lake shake` / import minimization.** Removing `simp only [listImp_nil]` from
   `MCSProperties.lean` does not remove the `listImp` dependency (the *statement* of `ListDeriv`
   still needs it), so no imports become removable. Confirmed by full build. The implementer
   should still run the standard 7-step CI order.

---

## 8. Recommended Implementation Plan Shape

The verified patch makes this a low-risk, near-mechanical task. Suggested phasing:

- **Phase 1 — Foundations (Tier B).** Apply the 4 Foundations file edits
  (`GenericMCS.lean`, `ListDeduction.lean`, `MCSProperties.lean`, `BigConj.lean`).
  Verify: `lake build` (full, because of the `unfoldListImp` data change).
  ~10 lines removed.
- **Phase 2 — Per-logic bridges (Tier A).** Apply the 4 `GenericMCSBridge` edits, preserving
  and re-siting the explanatory comments per §7.3, adding the defeq note per §7.1.
  Verify: `lake build` (full).
  ~52 lines removed.
- **Phase 3 — CI + task-description reconciliation.** Run the CSLib CI order
  (`lake build` → `lake exe checkInitImports` → `lake lint` → `lake exe lint-style` →
  `lake test` → `lake shake --add-public --keep-implied --keep-prefix`). Update the task
  description in `specs/state.json` to reflect the corrected scope (repo-wide, not
  `Propositional/`-only).

Phases 1 and 2 could be merged; they are kept separate only because Phase 1 contains the single
data-level change (`unfoldListImp`) that warrants isolated verification.

**Optional follow-on (do NOT bundle).** A repo-wide sweep for the same anti-pattern with *other*
`rfl`-simp lemmas is plausible but unbounded and unverified. If wanted, it should be a separate
task with its own detection recipe (candidate mechanical detector: for each `simp only [L]`
immediately preceding an `exact`, check whether every `L` is proved by `rfl`). This report makes
no claim about that broader set.

---

## 9. Zero-Debt and Standards Compliance

- **No `sorry` deferral proposed.** Every recommended edit is compile-verified.
- **No new axioms.**
- **No new declarations** — hence no new docBlame/defLemma/naming obligations. `lake lint`
  produced no output for any changed file.
- **No `@[simp]` set changes** — no simpNF risk.
- **No notation added** — the notation-option question (A/B/C) does not arise.
- **No `Cslib.Init` import changes** — `checkInitImports` unaffected.
- **No task-number references** will appear in the `Cslib/` deliverables.

---

## 10. Key File References

| Path | Role |
|------|------|
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/ListImplication.lean` | Source of `listImp`, `listImp_nil`/`_cons` (both `rfl`), `listImp_axiom_k`/`_s` |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Theorems/BigConj.lean` | Source of `bigconj` + the 4 `rfl` simp lemmas; also a Tier-B edit site |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` | `ListDeriv` def (L48); Tier-B edit site (L80-84) |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` | `algebraicDerivationSystem` (L127), `treeAlgDS` (L234), `unfoldListImp` (L240) — Tier-B data-level edit |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` | Tier-B edit sites (L110, L125) |
| `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` | Tier-A; the only edit site inside `Propositional/` |
| `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` | Tier-A |
| `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` | Tier-A |
| `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` | Tier-A (largest single win) |
| `/home/benjamin/Projects/cslib/specs/413_simplify_proofs_normalization_propositional/verified-simplification.patch` | **The complete verified diff** — apply with `git apply` |

---

## 11. Open Questions for the User

1. **Scope confirmation.** Accept the retarget from "`Propositional/` proofs" to "repo-wide
   `listImp`/`bigconj` redundant-rewrite removal" (8 files, 62 lines)? The alternative — restrict
   to `Propositional/GenericMCSBridge.lean` only — yields 5 lines and leaves three near-identical
   copies of the same anti-pattern in place, which is worse for the library.
2. **Defeq-reliance policy.** Is the maintainer comfortable with bridge proofs that depend on
   `ListDeriv`'s transparency (already the case for `listDerivToTree`), given the §7.1 mitigation
   of documenting it in a comment?
