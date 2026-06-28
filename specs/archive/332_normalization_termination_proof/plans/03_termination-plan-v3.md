# Implementation Plan (Revised v3): Task #332

- **Task**: 332 - Prove normalization termination theorem for CSLib Theory.Derivation
- **Status**: [IN PROGRESS]
- **Effort**: 6 hours remaining (Phases 0/1/2a complete on disk)
- **Dependencies**: None (Task 290 is [PARTIAL] with this same sorry; this task directly resolves it)
- **Research Inputs**: reports/01_termination-research.md; reports/02_lit-termination-strategy.md (literature-grounded strategy, T&S §6.1.8 / NvP §2.4); handoffs/phase-2-handoff-20260624T163704Z.md
- **Artifacts**: plans/01_termination-plan.md (superseded), plans/02_termination-plan-revised.md (superseded), plans/03_termination-plan-v3.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, literature-fidelity-policy.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a **revision** of plan v2 (`02_termination-plan-revised.md`). v2's mathematical approach
was **correct** — the height-free `normMeasure = (maximalFormulas, commutingSum)` under
`Prod.Lex IsDershowitzMannaLT (· < ·)`. v3 exists for two reasons:

1. **The on-disk state has advanced past v2's Phases 0–2a.** A prior implementation session
   reverted to the clean baseline, re-built the measure infrastructure, proved the Phase 2a
   subformula-complexity lemma (`subsOne_new_redex_complexity_lt`), and *scaffolded* the
   decrease lemma `reduceRoot_decreases_normMeasure` with a **real** `reduceRootSubSN`
   hypothesis (the conjunction-β cases h_2/h_3 are proved). The file currently has **7 sorries**
   and builds parseably. v3 marks those phases [COMPLETED] and re-scopes the remaining work
   against the *actual* line numbers.

2. **Literature report 02 supplies the precise closing strategy and confirms the design.**
   Troelstra–Schwichtenberg *Basic Proof Theory* §6.1.8 and Negri–von Plato *Structural Proof
   Theory* §2.4 confirm the height-free measure is the textbook strong-normalization measure and
   that `subsOne`'s height increase is irrelevant because height never enters the measure — it is
   isolated in a secondary component that `Prod.Lex.left` ignores. Report 02 also names the exact
   Lean lemmas to close each remaining sorry and prescribes a **leaner bridge** for the strategic
   sorry than v2's "replace `normalize`'s definition wholesale."

### What Changed From v2

| Aspect | v2 | v3 |
|--------|----|----|
| Measure | `(maximalFormulas, commutingSum)`, height-free | **unchanged** (confirmed by T&S §6.1.8) |
| Baseline | revert to `2826b053`, rebuild | already rebuilt on disk; do **not** revert |
| Phase 2b closing lemmas | "construct DM witness" (vague) | named: `isDershowitzMannaLT_remove_add_lt` + `subsOne_new_redex_complexity_lt` + `reduceRootSubSN`; new helper `maximalFormulas_subsOne_eq` |
| Strategic sorry bridge | "replace `normalize` to call `normalizeWF`" | prove `exists_stronglyNormal_form` by `WellFounded.induction normMeasure_wf`, then bridge `normalize` via `WellFounded.fix` (report 02 §4; low-risk — `subformula_property` consumes only the SN property, not the fuel definition) |
| `2^height` fuel | rejected | **rejected** (report 02 confirms T&S growth is hyper-exponential — retire it as a witness) |

### Ground-Truth On-Disk State (verified by Read + git diff)

`Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`:

- `normMeasure`, `commutingSum`, `maximalFormulas`, `normMeasure_wf` — **present and compiling**
  (line ~1685; `normMeasure_wf` via `InvImage.wf … WellFounded.prod_lex
  Multiset.wellFounded_isDershowitzMannaLT Nat.lt_wfRel.wf`).
- `subsOne_new_redex_complexity_lt` — **proved** (Phase 2a, axiom-clean).
- `reduceRoot_decreases_normMeasure` (line 1702) — scaffolded with **real** hypothesis
  `h_subsSN : d.reduceRootSubSN`. Cases **proved**: h_2, h_3 (conjunction β via
  `Multiset.isDershowitzMannaLT_cons_add` + `Prod.Lex.left`). Cases **sorry** (6):
  - h_1 (line 1711): `impE (impI _ D) E → D.subsOne E` (substitution β)
  - h_4 (1724): `orE _ (orI1 _ D) DA _ → DA.subsOne D`
  - h_5 (1726): `orE _ (orI2 _ D) _ DB → DB.subsOne D`
  - h_6 (1728): `andE1 (orE …) → orE … (andE1 …)` (commuting)
  - h_7 (1730): `andE2 (orE …) → …` (commuting)
  - h_8 (1732): `impE (orE …) E → …` (commuting)
- `normalize_isStronglyNormal` (line 1742) — strategic **sorry** at line 1748. Its docstring
  still describes the **old fuel/`2^height`** approach and MUST be rewritten to the WF route.
- `subformula_property` (line 1757) — depends on `normalize_isStronglyNormal`, not on
  `normalize`'s definition (confirmed by report 02 — the bridge is therefore low-risk).

### Research Integration (report 02)

- **§1–2 (obstacle resolution):** Height is never in the measure. The primary DM-multiset
  component strictly drops on every reduction; `subsOne` raising height affects only the
  secondary `commutingSum`, ignored by `Prod.Lex.left`. NvP §2.4 hit the identical
  "cut-height not monotone" obstacle and resolve it this way. → Keep `normMeasure` as is.
- **§3 (mapping):** literature measure ↔ `normMeasure`; cut-rank lex ordering ↔
  `Prod.Lex IsDershowitzMannaLT (· < ·)`; "main induction on cutrank, subinduction on length"
  ↔ `normMeasure_wf`.
- **§4 (skeleton):** the six strict-decrease sorries close via
  `isDershowitzMannaLT_remove_add_lt` + `subsOne_new_redex_complexity_lt` + `reduceRootSubSN`,
  plus one helper `maximalFormulas_subsOne_eq` for multiset bookkeeping. The strategic sorry
  closes by `exists_stronglyNormal_form` (WF induction) bridged through `WellFounded.fix`.
- **Citations:** T&S, NvP, Gentzen grounded in the converted corpus; Prawitz 1965 and
  Dershowitz–Manna 1979 referenced indirectly (not in corpus) — flagged for `/cite`.

### Roadmap Alignment

Advances the Propositional Natural Deduction module within `Logics/Propositional/`. Foundational
proof-theory infrastructure; resolves the long-standing single sorry also blocking Task 290.

## Goals & Non-Goals

**Goals**:
- Close the 6 strict-decrease sorries in `reduceRoot_decreases_normMeasure` using the named
  lemmas from report 02 §4.
- Add the helper `maximalFormulas_subsOne_eq` (or `_le`) for the substitution-β multiset
  bookkeeping if required by the substitution cases.
- Replace the strategic sorry in `normalize_isStronglyNormal` via the WF route: prove
  `exists_stronglyNormal_form` by `WellFounded.induction normMeasure_wf`, then bridge `normalize`
  through `WellFounded.fix`.
- Rewrite the stale fuel-based docstrings on `normalize_isStronglyNormal` and
  `subformula_property` to describe the WF/DM termination argument (cite T&S §6.1.8, NvP §2.4).
- Produce a sorry-free, axiom-clean Normalization.lean passing full CSLib CI.

**Non-Goals**:
- Reverting the on-disk progress (Phases 0–2a are correct and preserved).
- Reintroducing `normTriple`/`sizeOf` or any height/fuel-based measure.
- Proving `2^height` fuel sufficiency (retired per report 02).
- Extending normalization to first-order or modal natural deduction.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Substitution-β multiset bookkeeping (`maximalFormulas` after `subsOne`) resists | H | M | Prove helper `maximalFormulas_subsOne_eq`: `(D.subsOne E).maximalFormulas = D.maximalFormulas + <new redexes>` from `subsOne`'s recursion equations; combine with `subsOne_new_redex_complexity_lt` (all new elements `< complexity C`) and `isDershowitzMannaLT_remove_add_lt` |
| Commuting cases (h_6–h_8): proving `maximalFormulas` *equality* | H | M | Use `reduceRootSubSN`: an SN major premise cannot expose a matching introduction at the redex position, so pushing the elimination inside adds no new maximal formula → equality; strict decrease then comes from `commutingSum` via `Prod.Lex.right` |
| `WellFounded.fix` unfolding difficulties in the SN proof | M | M | Introduce `normalize_unfold`/`WellFounded.fix_eq` immediately; prove `exists_stronglyNormal_form` first (pure ∃ statement, no defeq fights), bridge afterward |
| Bridge changes `normalize`'s definition and breaks downstream | M | L | report 02 confirms `subformula_property` uses only the SN *property*; re-check every `normalize`/`normalizeAux` reference after the bridge edit and run scoped build |
| `isDershowitzMannaLT_remove_add_lt` has a different name/signature in Mathlib | M | M | `lean_local_search`/`lean_loogle` for the actual DM remove-add lemma; `Multiset.isDershowitzMannaLT_cons_add` (already used in h_2/h_3) is the confirmed-present cousin |
| Heartbeat/timeout on case analyses | M | L | per-case private helpers; `set_option maxHeartbeats` locally |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| — | 0, 1, 2a | (COMPLETED on disk) |
| 1 | 2b | — |
| 2 | 3 | 2b |
| 3 | 4 | 3 |
| 4 | 5 | 4 |

---

### Phase 0: Revert to Clean Baseline [COMPLETED]

Done in a prior session; the file was rebuilt from the clean baseline. Do **not** re-revert.

---

### Phase 1: Termination Measure Infrastructure [COMPLETED]

`maximalFormulas`, `commutingSum`, `normMeasure`, `normMeasure_wf` present and compiling;
axiom-clean. `normTriple`/`sizeOf` deliberately omitted.

---

### Phase 2a: subsOne Subformula-Complexity Lemma [COMPLETED]

`subsOne_new_redex_complexity_lt` proved by induction on the input `body` (Blocker 1 resolved);
axiom-clean.

---

### Phase 2b: Close the 6 Strict-Decrease Sorries [COMPLETED]

**Goal**: Discharge the 6 remaining sorries in `reduceRoot_decreases_normMeasure` (lines 1711,
1724, 1726, 1728, 1730, 1732) using report 02 §4's named lemmas. The `reduceRootSubSN`
hypothesis is already in place and must be genuinely used in the commuting cases.

**Tasks**:
- [ ] **Helper (if needed) `maximalFormulas_subsOne_eq`**: characterize
      `(D.subsOne E).maximalFormulas` in terms of `D.maximalFormulas` and the newly-created
      redexes, from `subsOne`'s recursion equations (reuse the Phase 2a membership lemma
      `subs_maximalFormulas_mem`). Needed for the multiset bookkeeping in the substitution-β cases.
- [ ] **h_1 (impE β, 1711)**, **h_4 / h_5 (orE β, 1724/1726)**: the cut formula `C` is removed and
      every newly-created redex has complexity `< complexity C` (`subsOne_new_redex_complexity_lt`).
      Build the DM witness via `isDershowitzMannaLT_remove_add_lt` (verify exact name with
      `lean_local_search`; `Multiset.isDershowitzMannaLT_cons_add` is the confirmed-present
      relative used in h_2/h_3). Close with `Prod.Lex.left`.
- [ ] **h_6 / h_7 / h_8 (commuting, 1728/1730/1732)**: use `h_subsSN : d.reduceRootSubSN` to show
      the major premise (SN) exposes no matching introduction at the redex position, so pushing the
      elimination inward creates **no new maximal formula** ⇒ `maximalFormulas` EQUAL. Then the
      `orE` site is no longer directly below an elimination ⇒ `commutingSum` strictly decreases ⇒
      `Prod.Lex.right`. The SN hypothesis MUST be used here (not discharged by `trivial`).
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`; confirm sorry count
      drops from 7 to 1 (only the strategic sorry at `normalize_isStronglyNormal` remains).
- [ ] `lean_verify Theory.Derivation.reduceRoot_decreases_normMeasure` — no axioms, no sorry.

**Timing**: 3 hours · **Depends on**: 2a · **Files**: Normalization.lean

**Verification**: all 8 patterns proved; SN hypothesis genuinely used in commuting cases;
axiom-clean; build green with exactly 1 sorry remaining.

---

### Phase 3: Existence of Strongly-Normal Form via WF Induction [NOT STARTED]

**Goal**: Prove the core termination result as a pure existence statement (report 02 §4), avoiding
`WellFounded.fix` definitional-equality fights.

**Tasks**:
- [ ] State and prove `exists_stronglyNormal_form (d : T.Derivation G A) :`
      `∃ d', d'.isStronglyNormal = true ∧ <relation to d>` by `WellFounded.induction normMeasure_wf`.
      Base case: `reduceRoot d = none` + SN immediate subterms ⇒ `d` is SN. Step case: apply
      `reduceRoot_decreases_normMeasure` (Phase 2b) to land in the IH (measure strictly decreased).
- [ ] Establish/confirm the SN-subterm invariant feeding `reduceRootSubSN` at the recursive call
      (immediate subterms normalized first, mirroring `normalizeAux`'s inner step).
- [ ] `lake build …Normalization`; `lean_verify` the new lemma — no axioms, no sorry.

**Timing**: 2 hours · **Depends on**: 2b · **Files**: Normalization.lean

**Verification**: `exists_stronglyNormal_form` compiles, axiom-clean; the decrease lemma's SN
hypothesis is actually discharged from the normalized subterms.

---

### Phase 4: Bridge and Eliminate the Strategic Sorry [NOT STARTED]

**Goal**: Close the strategic sorry at line 1748 and rewrite the stale fuel docstrings.

**Tasks**:
- [ ] Bridge `normalize` to the WF result: redefine `normalize` (or add `normalizeWF` via
      `WellFounded.fix normMeasure_wf` and repoint `normalize`) so that
      `normalize_isStronglyNormal` follows from `exists_stronglyNormal_form` /
      `redexWeight_zero_sn`. Keep the change minimal — report 02 confirms downstream
      `subformula_property` consumes only the SN property.
- [ ] Replace the sorry in `normalize_isStronglyNormal` with the real proof.
- [ ] **Rewrite the stale docstrings** on `normalize_isStronglyNormal` (lines ~1734–1741) and
      `subformula_property` (lines ~1752–1756): remove the `2^d.height` / fuel narrative; describe
      the height-free Dershowitz–Manna WF termination argument and cite `[Troelstra-Schwichtenberg2000]`
      §6.1.8 and `[NegriVonPlato2001]` §2.4 (per literature-fidelity-policy and report 02).
- [ ] Confirm `subformula_property` still compiles after the bridge.
- [ ] `lake build …Normalization`; `lean_verify Theory.Derivation.normalize_isStronglyNormal` and
      `…subformula_property` — no axioms, no sorry.

**Timing**: 1.5 hours · **Depends on**: 3 · **Files**: Normalization.lean

**Verification**: zero sorry in the file; both target theorems axiom-clean; docstrings reflect the
WF/DM argument, not fuel.

---

### Phase 5: CI Verification and Cleanup [NOT STARTED]

**Goal**: Pass the full CSLib CI pipeline.

**Tasks**:
- [ ] `lake build` (full project) — no regressions.
- [ ] `lake exe checkInitImports`.
- [ ] `lake exe lint-style`.
- [ ] `lake lint`.
- [ ] `lake test`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Docstrings on all new public definitions; section headers tidy.

**Timing**: 1 hour · **Depends on**: 4 · **Files**: Normalization.lean

**Verification**: all CI commands pass;
`grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` empty.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds.
- [ ] `lake build` (full project) succeeds.
- [ ] `lean_verify` on `reduceRoot_decreases_normMeasure`, `exists_stronglyNormal_form`,
      `normalize_isStronglyNormal`, `subformula_property` — no sorry, no axioms.
- [ ] `lake exe checkInitImports`, `lake exe lint-style`, `lake lint`, `lake test`, `lake shake` pass.
- [ ] `grep -rn "sorry" …/Normalization.lean` returns empty.

## Artifacts & Outputs

- `specs/332_normalization_termination_proof/plans/03_termination-plan-v3.md` (this file)
- `specs/332_normalization_termination_proof/reports/02_lit-termination-strategy.md` (strategy input)
- `specs/332_normalization_termination_proof/reports/01_termination-research.md` (research input)
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` (sorry eliminated)

## Rollback/Contingency

1. **On-disk progress is the new baseline**: the file builds parseably with the height-free
   measure and proved 2a lemma. If a phase goes wrong, restore from the last green commit — never
   `git checkout` back to `2826b053` (that discards the rebuilt infrastructure).
2. **If a commuting case (h_6–h_8) resists** the no-new-maximal-formulas equality argument: fall
   back to a `maximalFormulas` *inequality* and strengthen the threaded invariant to "fully
   normalized subterms".
3. **If the bridge (Phase 4) destabilizes downstream**: keep `normalize`'s original definition and
   instead prove `normalize_isStronglyNormal` by relating `normalizeAux` output to
   `exists_stronglyNormal_form` via `redexWeight_zero_sn`, without redefining `normalize`.
4. **Minimal fallback**: if the WF bridge cannot be completed within budget, leave the strict-decrease
   lemma (Phase 2b) proved and the strategic sorry isolated; mark Phase 4 [BLOCKED] with the exact
   goal state — never leave the file in a multi-error state.
