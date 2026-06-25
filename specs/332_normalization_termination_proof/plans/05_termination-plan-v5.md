# Implementation Plan (v5 — accuracy revision): Task #332

- **Task**: 332 — Prove the normalization termination theorem for CSLib `Theory.Derivation`
- **Status**: [IN PROGRESS]
- **Effort**: ~2 hours remaining (Phases 1, 2 committed green; Phase 3 in progress; Phases 4, 5, 6 remaining)
- **Dependencies**: Task 333 (module refactor) — **COMPLETED** (`28d3ac65`); Task 290 is [PARTIAL]
  and shares this exact termination obligation (it closes automatically once Phase 5 lands).
- **Research Inputs**: reports/01_termination-research.md; reports/02_lit-termination-strategy.md
  (height-free DM measure); reports/03_commuting-and-wf-bridge.md (commuting-case tactics + WF bridge)
- **Artifacts**: plans/01–03 (superseded); plans/04_termination-plan-v4.md (superseded — its
  strategy is valid but its on-disk-state bookkeeping drifted; see "Why v5" below); this file
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, literature-fidelity-policy.md
- **Type**: cslib
- **Lean Intent**: true

## Why v5 (revision rationale)

v5 replaces v4 to be **fully accurate**. v4's "Ground-Truth On-Disk State" and "What Changed From
v3" sections were optimistic and wrong: they claimed the file built with 1 sorry and 7/8 decrease
cases proved, but the version they described (`88862dd1`, the monolithic `Normalization.lean`) was
**red** (whnf timeouts + an `apply` unification failure) with **6 sorries** in
`reduceRoot_decreases_normMeasure`. v4 also predated the task-333 refactor, so its file/line
references point at a monolith that no longer exists.

**The strategy is unchanged** — height-free Dershowitz–Manna measure → `exists_stronglyNormal_form`
by well-founded induction → re-point `subformula_property` (Route 1) → delete the dead fuel proof.
Only the bookkeeping and structure are corrected here.

## Overview

Discharge the single substantive termination obligation for Prawitz-style normalization of
`Theory.Derivation` (propositional IPL/MPL). The committed `Normalization/Termination.lean` carries
a fuel-based sorry, `normalize_isStronglyNormal : d.normalize.isStronglyNormal = true`, whose goal
after `apply redexWeight_zero_sn` is `d.normalize.redexWeight = 0`. **That fuel route is a dead
end** (the `2^height` bound is hyper-exponential per T&S; see Non-Goals). The proof instead proceeds
via a height-free measure:

`normMeasure d = (maximalFormulas d, commutingSum d) : Multiset ℕ × ℕ`, well-founded under
`Prod.Lex IsDershowitzMannaLT (· < ·)` (`normMeasure_wf`). A single root reduction strictly
decreases this measure (`reduceRoot_decreases_normMeasure`), which drives a well-founded induction
proving `exists_stronglyNormal_form : ∃ d', d'.isStronglyNormal = true`. The public
`subformula_property` then consumes that existence statement directly, and the fuel theorem +
sorry are deleted.

### File structure (post task-333 refactor)

All termination work lives in
`Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean`. The former monolith is
now a barrel over `Normalization/{Basic,Reduction,Termination,SubformulaProperty}.lean`. **Locate
declarations by name, not line number.**

### Accurate on-disk state (HEAD, committed)

`Normalization/Termination.lean` builds **green with exactly 2 sorries**:
1. `reduceRoot_decreases_normMeasure`, case **h_8** (impE·orE commuting) — isolated as a documented
   sorry pending Phase 3.
2. `normalize_isStronglyNormal` — the pre-existing fuel sorry, to be **deleted** in Phase 5.

Proved and committed (green):
- **Measure infra** (Phase 1, `352c04dd`): `nodeCount`, `maximalFormulas` (+ ~12 lemmas),
  `subsOne_new_redex_complexity_lt`, `commutingSum`, `maximalFormulas_sn_eq_zero`, `reduceRootSubSN`,
  the `Multiset.isDershowitzMannaLT_*` helpers, `normMeasure`, `normMeasure_wf`.
- **Decrease lemma 7/8** (Phase 2, `7ef4ea42`): `reduceRoot_decreases_normMeasure` cases h_1/h_4/h_5
  (substitution β), h_2/h_3 (conjunction β), h_6/h_7 (andE·orE commuting); plus weakening-preservation
  helpers `nodeCount_weak`, `nodeCount_weakCtx`, `commutingSum_weak`, `commutingSum_weakCtx`. The
  lemma carries a local `set_option maxHeartbeats 1200000`.

## Goals & Non-Goals

**Goals**:
- Close h_8 of `reduceRoot_decreases_normMeasure` (Phase 3).
- Prove `exists_stronglyNormal_form` by `WellFounded.induction normMeasure_wf` (Phase 4).
- Re-point `subformula_property` at `exists_stronglyNormal_form`; delete the fuel
  `normalize_isStronglyNormal` and any now-dead fuel lemmas (Phase 5).
- Sorry-free, axiom-clean `Normalization/` passing full CSLib CI (Phase 6).

**Non-Goals**:
- The `2^height` fuel sufficiency proof (dead — growth is hyper-exponential, report 03 §B.4).
- Reverting to `normTriple`/`sizeOf`/height/fuel measures.
- Confluence / uniqueness of normal forms (separate theorem — report 03 §B.3 / T&S 6.8.6).
- First-order / modal extensions.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| h_8: commuting conversion duplicates `E` into both branches, so `maximalFormulas`/`commutingSum` gain an extra `E`-copy | H | — (root cause known) | Extract `E` strong-normality from `reduceRootSubSN` (`(impE DA E').isStronglyNormal ∧ (impE DB E').isStronglyNormal`), giving `E.maximalFormulas = 0` and `E.commutingSum = 0`; the extra copies cancel. May require a `commutingSum_sn_eq_zero` helper (mirror `maximalFormulas_sn_eq_zero`). Near-complete attempt in `handoffs/termination-h8-attempt-needs-Esn.lean.bak` |
| `exists_stronglyNormal_form` step-1 "normalize subterms first" sub-obligation | H | M | Helper `normSubterms : ∃ d₀, sameConclusion ∧ subtermsSN ∧ normMeasure d₀ ≤ normMeasure d` by structural recursion reusing the IH; additivity of `maximalFormulas`/`commutingSum` over subterms (report 03 §B.5) |
| whnf heartbeat timeouts on `cases … <;> simp_all` over 10 constructors | M | M (already hit) | Local `set_option maxHeartbeats`; do the fst `maximalFormulas`-equality rewrite FIRST; prefer targeted `simp only` + per-case helper lemmas over `simp_all` |
| Single-agent dispatch overflows context on the proof | H | H (hit 3× on the monolith) | **Bounded one-lemma-per-dispatch** + orchestrator surgical fixes; verify each milestone with a real `lake build` before committing |
| Removing `normalize_isStronglyNormal` breaks a consumer | L | L | grep-confirmed only `subformula_property` used it (now re-pointed). Fallback Route 2: redefine `normalize` via `WellFounded.fix normMeasure_wf` (SN immediate from `fix_eq`) |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phase | Blocked by |
|------|-------|------------|
| — | 1, 2 | (COMPLETED, committed green) |
| 1 | 3 | — |
| 2 | 4 | Phase 3 |
| 3 | 5 | Phase 4 |
| 4 | 6 | Phase 5 |

### Phase 1: Recover DM-measure infrastructure [COMPLETED]

Ported `nodeCount`, `maximalFormulas` (+ lemmas), `subsOne_new_redex_complexity_lt`, `commutingSum`,
`maximalFormulas_sn_eq_zero`, `reduceRootSubSN`, `isDershowitzMannaLT_*` helpers, `normMeasure`,
`normMeasure_wf` into `Termination.lean`; added `import Mathlib.Data.Multiset.DershowitzManna`.
Green (627 jobs), no new sorries.

### Phase 2: Strict-decrease lemma, 7/8 cases [COMPLETED]

`reduceRoot_decreases_normMeasure`: h_1/h_4/h_5 (substitution β via `subsOne_new_redex_complexity_lt`
+ `Prod.Lex.left`), h_2/h_3 (conjunction β), h_6/h_7 (andE·orE commuting via `maximalFormulas`-equality
+ `Prod.Lex.right` + `commutingSum` decrease). Added `nodeCount_weak(_Ctx)` / `commutingSum_weak(_Ctx)`.
Green, h_8 isolated as documented sorry.

### Phase 3: Close the impE·orE commuting case [IN PROGRESS]

**Goal**: prove h_8 of `reduceRoot_decreases_normMeasure`.

**Tasks**:
- [ ] Extract `(Ecc.weakCtx _).isStronglyNormal = true` from `h_subsSN`'s
      `(impE DAcc (Ecc.weakCtx _)).isStronglyNormal` conjunct.
- [ ] Derive `Ecc.maximalFormulas = ∅` (`maximalFormulas_sn_eq_zero` + `maximalFormulas_weakCtx`)
      and `Ecc.commutingSum = 0` (add `commutingSum_sn_eq_zero` if absent, mirroring
      `maximalFormulas_sn_eq_zero`).
- [ ] Reuse the four correct `have`s (`hDA_mf`/`hDB_mf`/`hDA_cs`/`hDB_cs`) from the preserved attempt;
      feed `E`-SN facts into the final `maximalFormulas`-equality rewrite and the `commutingSum`
      `omega` step so the duplicated-`E` copies cancel.
- [ ] `lake build …Normalization.Termination`; `reduceRoot_decreases_normMeasure` fully sorry-free
      → file back to 1 sorry (fuel).

**Verification**: build green; only the fuel sorry remains.

### Phase 4: `exists_stronglyNormal_form` via WF induction [NOT STARTED]

**Goal**: prove `exists_stronglyNormal_form (d) : ∃ d', d'.isStronglyNormal = true` (report 03 §B.4
Route 1).

**Tasks**:
- [ ] Helper `normSubterms` (report 03 §B.5): `∃ d₀, sameConclusion d₀ d ∧ <subterms of d₀ SN> ∧
      normMeasure d₀ ≤ normMeasure d`, by structural recursion reusing the IH at strictly smaller
      subterms; monotonicity from additivity of `maximalFormulas`/`commutingSum`.
- [ ] `exists_stronglyNormal_form` by `WellFounded.induction normMeasure_wf`:
      1. `normSubterms d → d₀` (SN subterms, `normMeasure d₀ ≤ normMeasure d`).
      2. `d₀.reduceRoot = none` ⇒ `d₀` SN (base case via `redexWeight_zero_sn` or a
         `reduceRoot_none_subSN_isStronglyNormal` lemma; T&S 6.12). Return `d₀`.
      3. `d₀.reduceRoot = some d'` ⇒ SN subterms discharge `reduceRootSubSN d₀`, so
         `reduceRoot_decreases_normMeasure` gives `normMeasure d' < normMeasure d₀ ≤ normMeasure d`;
         apply `ih d'`.
- [ ] `lake build …Termination`; `lean_verify` — no axioms, no sorry on the new theorem.

**Verification**: `exists_stronglyNormal_form` compiles axiom-clean.

### Phase 5: Bridge `subformula_property`; delete the fuel sorry [NOT STARTED]

**Goal**: eliminate the last sorry.

**Tasks**:
- [ ] Re-point `subformula_property` (in `Normalization/SubformulaProperty.lean`):
  ```lean
  theorem Theory.Derivation.subformula_property (d : T.Derivation G A) :
      ∃ d', d'.isStronglyNormal = true ∧ d'.SubformulaProperty := by
    obtain ⟨d', hsn⟩ := d.exists_stronglyNormal_form
    exact ⟨d', hsn, d'.subformula_property_of_isStronglyNormal hsn⟩
  ```
- [ ] **Delete** `normalize_isStronglyNormal` (the fuel sorry) and any now-dead `normalizeAux`
      fuel lemmas (grep-confirm no other consumers). Fallback Route 2 if a consumer surfaces.
- [ ] Rewrite stale fuel docstrings to the WF/DM argument (cite `[Troelstra-Schwichtenberg2000]`
      6.1.8/6.12, `[NegriVonPlato2001]` §2.4).
- [ ] `lake build …Normalization`; confirm **0 sorries** across `Normalization/`.

**Verification**: zero sorry; `subformula_property` axiom-clean.

### Phase 6: CI verification and cleanup [NOT STARTED]

**Tasks**:
- [ ] `lake build` (full); `lake exe checkInitImports`; `lake exe lint-style`; `lake lint`;
      `lake test`; `lake exe mk_all --module`; `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Docstrings on new public defs; tidy section headers; remove dead fuel-era definitions flagged
      by `shake`/`lint`.

**Verification**: all CI green; `grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/Normalization/` empty.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds.
- [ ] `lake build` (full project) succeeds (note: unrelated Bimodal/Temporal modules may be red
      independently of this task — confirm `Normalization/` is clean).
- [ ] `lean_verify` on `reduceRoot_decreases_normMeasure`, `exists_stronglyNormal_form`,
      `subformula_property` — no sorry, no axioms.
- [ ] `lake exe checkInitImports`, `lake exe lint-style`, `lake lint`, `lake test`, `lake shake` pass.
- [ ] `grep -rn "sorry" …/Normalization/` returns empty.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` (sorry eliminated)
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/SubformulaProperty.lean` (re-pointed bridge)
- `specs/332_normalization_termination_proof/reports/03_commuting-and-wf-bridge.md` (verified tactics)
- `handoffs/termination-h8-attempt-needs-Esn.lean.bak` (near-complete h_8 attempt)

## Helper-Lemma Checklist

| Helper | Need | Status |
|---|---|---|
| `nodeCount_weak`, `nodeCount_weakCtx` | weakening preserves nodeCount (h_8) | **present** (Phase 2) |
| `commutingSum_weak`, `commutingSum_weakCtx` | weakening preserves commutingSum (h_8) | **present** (Phase 2) |
| `maximalFormulas_weakCtx`, `maximalFormulas_sn_eq_zero` | h_8 / SN ⇒ mf = 0 | **present** (Phase 1) |
| `commutingSum_sn_eq_zero` | h_8: SN ⇒ commutingSum = 0 | **to write** (mirror `maximalFormulas_sn_eq_zero`) |
| `reduceRoot_none_subSN_isStronglyNormal` (or reuse `redexWeight_zero_sn`) | Phase 4 base case | reuse existing |
| `normSubterms` | Phase 4 step 1 | to write |
| `exists_stronglyNormal_form` | Phase 4 main | to write |

No new imports beyond `Mathlib.Data.Multiset.DershowitzManna` (Phase 1). No axioms. No `2^height`
fuel proof. No confluence.

## Rollback/Contingency

1. **Green commits are the baseline**: Phase 1 (`352c04dd`) and Phase 2 (`7ef4ea42`) are green; restore
   from the latest green commit on trouble. Never restore the red monolith state.
2. **If h_8 resists**: keep it isolated as the documented sorry (current committed state); the rest of
   the decrease lemma stands. Do not let the file go red.
3. **If `exists_stronglyNormal_form` step-1 (`normSubterms`) stalls**: use `normalizeAux`'s structural
   (reduceRoot-free) subterm pass for step 1, invoking the WF IH for the root (report 03 §B.5).
4. **If Route 1 surfaces a `normalize` SN consumer**: switch to Route 2 (`WellFounded.fix`-defined
   `normalize`); only then is `normalize_isStronglyNormal` needed, immediate from `WellFounded.fix_eq`.
5. **Process discipline**: bounded one-lemma-per-dispatch; verify every "done" with a real `lake build`
   before committing; never trust a status marker over the compiler.
