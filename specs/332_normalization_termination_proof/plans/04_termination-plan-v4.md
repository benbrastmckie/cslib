# Implementation Plan (Revised v4): Task #332

- **Task**: 332 - Prove normalization termination theorem for CSLib Theory.Derivation
- **Status**: [IN PROGRESS]
- **Effort**: see "Session Update 2026-06-24" below for the accurate on-disk state
- **Last accurate sync**: 2026-06-24 (Session Update section). The body below (written against the
  monolith) is retained for its strategy and verified tactics but its on-disk-state claims are
  superseded by the Session Update.
- **Dependencies**: None (Task 290 is [PARTIAL] with this same sorry; this task directly resolves it)
- **Research Inputs**: reports/01_termination-research.md; reports/02_lit-termination-strategy.md (height-free DM measure); reports/03_commuting-and-wf-bridge.md (verified commuting-case tactics + WF bridge); handoffs/phase-2-handoff-20260624T163704Z.md
- **Artifacts**: plans/01_termination-plan.md (superseded), plans/02_termination-plan-revised.md (superseded), plans/03_termination-plan-v3.md (superseded), plans/04_termination-plan-v4.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, literature-fidelity-policy.md
- **Type**: cslib
- **Lean Intent**: true

## Session Update — 2026-06-24 (accurate on-disk state; supersedes drifted claims below)

**Drift correction.** The "Ground-Truth On-Disk State" and "What Changed From v3" sections below
were **optimistic and inaccurate**. The committed version they describe (`88862dd1`,
monolithic `Normalization.lean`) was in fact **red** (whnf timeouts + an `apply` unification
failure in `reduceRoot_decreases_normMeasure`) and carried **6 sorries** in that lemma — NOT
"builds with 1 sorry and 7/8 cases proved." Only h_2/h_3 were actually closed there.

**Structural change (task 333 ran first).** The 1099-line monolith was reverted to its green
phase-0 baseline and **refactored into submodules** (task 333, committed `28d3ac65`):
`Normalization/{Basic,Reduction,Termination,SubformulaProperty}.lean` + a barrel. All termination
work now lives in `Normalization/Termination.lean`, NOT the monolith. Locate declarations by
name; ignore the monolith line numbers below.

**Actual phase status (this session, each a committed green milestone):**

| Phase | Work | State |
|-------|------|-------|
| A | Recover DM-measure infra (nodeCount, maximalFormulas + lemmas, subsOne_new_redex_complexity_lt, commutingSum, maximalFormulas_sn_eq_zero, reduceRootSubSN, isDershowitzMannaLT helpers, normMeasure, normMeasure_wf) into Termination.lean | **DONE** — committed `352c04dd`, green |
| B | `reduceRoot_decreases_normMeasure`: h_1/h_4/h_5 (subst β), h_2/h_3 (conj β), h_6/h_7 (andE commuting) proved; added nodeCount_weak(_Ctx)/commutingSum_weak(_Ctx); local `maxHeartbeats 1200000` | **DONE (7/8)** — committed `7ef4ea42`, green, h_8 isolated as documented sorry |
| B-h8 | h_8 (impE-orE commuting): the conversion duplicates `E` into both branches, so the maximalFormulas equality + commutingSum decrease need `E` strongly normal (`E.maximalFormulas = 0`, `E.commutingSum = 0`), obtainable from `reduceRootSubSN`'s `(impE DA E').isStronglyNormal ∧ (impE DB E').isStronglyNormal`. May need a `commutingSum_sn_eq_zero` helper. Near-complete attempt in `handoffs/termination-h8-attempt-needs-Esn.lean.bak` | **IN PROGRESS** |
| C | `normSubterms` + `exists_stronglyNormal_form` via `WellFounded.induction normMeasure_wf` (Phase 3 below) | NOT STARTED |
| D | Re-point `subformula_property` at `exists_stronglyNormal_form`; **delete** the dead fuel `normalize_isStronglyNormal` sorry (`d.normalize.redexWeight = 0` — the 2^height fuel route is dead, see Non-Goals) → 0 sorries (Phase 4 below) | NOT STARTED |
| E | Full CSLib CI (Phase 5 below) | NOT STARTED |

**Current file state:** `Normalization/Termination.lean` builds green with **2 sorries** — h_8
(above) and the pre-existing fuel `normalize_isStronglyNormal` (deleted in Phase D). The
overarching strategy (height-free DM measure → `exists_stronglyNormal_form` → re-point
`subformula_property`, Route 1) is unchanged and being followed.

## Overview

This is a **revision** of plan v3 (`03_termination-plan-v3.md`). v3's approach is **fully
validated** — no direction changes. v4 exists to (a) record the on-disk advance (the substitution-β
and conjunction-β cases of the decrease lemma are now **closed**), and (b) capture the
**`lean_multi_attempt`-verified** closing tactics from literature report 03 as a durable,
self-contained record — previously these lived only in the report and a live agent message.

**This is bookkeeping over a confirmed approach, not a redirection.** The height-free
`normMeasure = (maximalFormulas, commutingSum)` under `Prod.Lex IsDershowitzMannaLT (· < ·)` is
unchanged and now triply confirmed (reports 02 and 03 against Troelstra–Schwichtenberg,
Negri–von Plato, Gentzen).

### What Changed From v3

| Aspect | v3 | v4 |
|--------|----|----|
| Substitution-β cases (h_1/h_4/h_5) | open (sorry) | **CLOSED on disk** (`subsOne_new_redex_complexity_lt` + `isDershowitzMannaLT_all_lt[_add]` + `Prod.Lex.left`) |
| Commuting cases (h_6/h_7/h_8) | "use SN invariant ⇒ equality ⇒ `Prod.Lex.right`" (strategy) | **verified tactic block** (report 03 §A.2, tested via `lean_multi_attempt` to zero goals) |
| `maximalFormulas` under permutation | "equality, mitigated risk" | **equality CONFIRMED** (report 03 §A.3 / T&S 6.1.2: cutrank = \|segment formula\|) |
| Bridge | "redefine `normalize` via `WellFounded.fix`" (Route 2) | **Route 1 preferred**: `subformula_property` consumes `exists_stronglyNormal_form` directly; `normalize` left untouched (report 03 §B.4 — grep-confirmed no external consumers) |
| Confluence/uniqueness | not discussed | **NOT needed** (report 03 §B.3 / T&S 6.8.6 — uniqueness is a separate theorem) |

### Ground-Truth On-Disk State (report 03 §0, verified via `lean_goal` + grep)

`Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` — **exactly 4 sorries**:

- `reduceRoot_decreases_normMeasure`:
  - h_2/h_3 (conjunction β) — **PROVED**
  - h_1/h_4/h_5 (substitution β: impE, orE-left, orE-right) — **PROVED**
  - **h_6/h_7/h_8 (commuting: andE1·orE, andE2·orE, impE·orE) — SORRY** (lines ~1782/1784/1786)
- `normalize_isStronglyNormal` — **SORRY** (~line 1802), goal `d.normalize.redexWeight = 0`
- Present + compiling: `maximalFormulas_sn_eq_zero`, `maximalFormulas_weakCtx`, `reduceRootSubSN`,
  `commutingSum`, `nodeCount`, `normMeasure_wf`, `redexWeight_zero_sn`, `subformula_property_of_isStronglyNormal`

*Line numbers drift as the live agent edits; locate by theorem name, not line.*

### Roadmap Alignment

Advances the Propositional Natural Deduction module within `Logics/Propositional/`. Foundational
proof-theory infrastructure; resolves the long-standing single sorry also blocking Task 290.

## Goals & Non-Goals

**Goals**:
- Close h_6/h_7/h_8 in `reduceRoot_decreases_normMeasure` using report 03 §A.2's verified pattern.
- Prove `exists_stronglyNormal_form` by `WellFounded.induction normMeasure_wf` (report 03 §B.4 Route 1).
- Re-point `subformula_property` at `exists_stronglyNormal_form`; resolve/remove the strategic sorry.
- Rewrite stale fuel-based docstrings to the WF/DM argument (cite T&S 6.1.8/6.12, NvP §2.4).
- Sorry-free, axiom-clean Normalization.lean passing full CSLib CI.

**Non-Goals**:
- Reverting on-disk progress; reintroducing `normTriple`/`sizeOf`/height/fuel measures.
- Proving `2^height` fuel sufficiency (dead — T&S growth hyper-exponential, report 03 §B.4).
- Proving confluence/uniqueness of normal forms (not required — report 03 §B.3).
- First-order/modal extensions.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `rename_i` binder order in h_6/h_7/h_8 differs from report 03's sketch | L | H | The `split at hd'` leaves discriminees anonymous; `rename_i` them to match the real order, or use `next … =>`. The tactic body is otherwise verified. |
| `Prod.Lex.right` type-mismatch | M | M | Do the fst `maximalFormulas` equality `rw` FIRST so both first components are syntactically identical (report 03 §A.2) |
| h_8 fst-equality misses the `weakCtx` rewrite | M | M | Add `maximalFormulas_weakCtx` (already in file, line ~1139) to the `simp_all` set for h_8 |
| `exists_stronglyNormal_form` step-1 "normalize subterms first" sub-obligation | H | M | Helper `normSubterms : ∃ d₀, sameConclusion ∧ subtermsSN ∧ normMeasure d₀ ≤ normMeasure d` by structural recursion reusing the IH; additivity of `maximalFormulas`/`commutingSum` over subterms (report 03 §B.5) |
| Removing `normalize_isStronglyNormal` breaks a consumer | L | L | grep-confirmed no external consumers; only `subformula_property` used it, now re-pointed (report 03 §B.4). If a consumer surfaces, keep it via Route 2 (`WellFounded.fix`-defined `normalize`) |
| Heartbeat on `cases DA <;> cases DB <;> simp_all` | M | L | per-case helpers `maximalFormulas_{andE1,andE2,impE}_commute` (report 03 §A.3); `set_option maxHeartbeats` locally |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| — | 0, 1, 2a, 2b-β | (COMPLETED on disk) |
| 1 | 2b-commuting | — |
| 2 | 3 | 2b-commuting |
| 3 | 4 | 3 |
| 4 | 5 | 4 |

---

### Phases 0–2a [COMPLETED]

Clean baseline rebuilt; height-free measure infrastructure (`maximalFormulas`, `commutingSum`,
`normMeasure`, `normMeasure_wf`) present and axiom-clean; `subsOne_new_redex_complexity_lt` proved.

### Phase 2b-β: Conjunction- and Substitution-β Decrease Cases [COMPLETED]

h_2/h_3 (andE β) and h_1/h_4/h_5 (impE/orE substitution β) of `reduceRoot_decreases_normMeasure`
proved via `subsOne_new_redex_complexity_lt` + `isDershowitzMannaLT_*` + `Prod.Lex.left`.

---

### Phase 2b-commuting: Close h_6/h_7/h_8 [IN PROGRESS]

**Goal**: Discharge the 3 commuting-conversion sorries in `reduceRoot_decreases_normMeasure`. The
primary `maximalFormulas` multiset is **preserved (equality)** because a permutative conversion
keeps the cut formula's complexity fixed (T&S 6.1.2) and the SN side condition `reduceRootSubSN`
excludes a new maximal segment; the strict decrease is the secondary `commutingSum` (`Prod.Lex.right`).

**Tasks** (report 03 §A.2 — verified pattern; fix only the `rename_i` order):
- [ ] **h_6** (`andE1 (orE D DA DB) → orE D (andE1 DA) (andE1 DB)`):
  ```lean
  rename_i … D DA DB
  rw [Option.some.injEq] at hd'; subst hd'
  rcases h_subsSN with ⟨hA, hB⟩
  show Prod.Lex _ _ (_, _) (_, _)
  rw [show (andE1 G (orE G D DA DB)).maximalFormulas
        = (orE G D (andE1 _ DA) (andE1 _ DB)).maximalFormulas from by
      cases DA <;> cases DB <;> simp_all [maximalFormulas, isStronglyNormal, conclusionComplexity]]
  refine Prod.Lex.right _ ?_
  cases D <;> simp_all [commutingSum, nodeCount, isStronglyNormal] <;> omega
  ```
- [ ] **h_7**: identical to h_6 with `andE2`/`andE1` swapped.
- [ ] **h_8** (`impE (orE D DA DB) E → orE D (impE DA E.weakCtx) (impE DB E.weakCtx)`): same shape,
      one extra binder `E`; **add `maximalFormulas_weakCtx`** to the fst-equality `simp_all` set so
      `(E.weakCtx …).maximalFormulas = E.maximalFormulas`.
- [ ] (Optional) extract `maximalFormulas_{andE1,andE2,impE}_commute` helpers if heartbeats spike;
      do **not** block on this.
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`; sorry count 4 → 1.
- [ ] `lean_verify Theory.Derivation.reduceRoot_decreases_normMeasure` — no axioms, no sorry; confirm
      `hA`/`hB` are genuinely used (not `trivial`).

**Timing**: 1 hour · **Depends on**: 2b-β · **Files**: Normalization.lean

**Verification**: all 8 patterns proved; SN hypothesis used in commuting cases; axiom-clean;
build green with 1 sorry (strategic) remaining.

---

### Phase 3: `exists_stronglyNormal_form` via WF Induction [NOT STARTED]

**Goal**: Prove the core termination result as a pure existence statement (report 03 §B.4 Route 1).

**Tasks**:
- [ ] **Helper `normSubterms`** (report 03 §B.5): `∃ d₀, sameConclusion d₀ d ∧ <subterms of d₀ SN> ∧
      normMeasure d₀ ≤ normMeasure d`, by structural recursion on `d` reusing the IH at strictly
      smaller subterms; monotonicity from additivity of `maximalFormulas`/`commutingSum` over subterms.
- [ ] **`exists_stronglyNormal_form (d) : ∃ d', d'.isStronglyNormal = true`** by
      `WellFounded.induction normMeasure_wf`:
      1. `normSubterms d → d₀` (SN subterms, `normMeasure d₀ ≤ normMeasure d`).
      2. `d₀.reduceRoot = none` ⇒ `d₀` SN via base case (`redexWeight_zero_sn` / a
         `reduceRoot_none_subSN_isStronglyNormal` lemma; T&S 6.12). Return `d' := d₀`.
      3. `d₀.reduceRoot = some d'` ⇒ SN subterms discharge `reduceRootSubSN d₀`, so
         `reduceRoot_decreases_normMeasure` gives `normMeasure d' < normMeasure d₀ ≤ normMeasure d`;
         apply `ih d'`.
- [ ] `lake build …Normalization`; `lean_verify` — no axioms, no sorry.

**Timing**: 1.5 hours · **Depends on**: 2b-commuting · **Files**: Normalization.lean

**Verification**: `exists_stronglyNormal_form` compiles axiom-clean; the decrease lemma's SN
hypothesis is discharged from `normSubterms`.

---

### Phase 4: Bridge `subformula_property` and Resolve the Strategic Sorry [NOT STARTED]

**Goal**: Make the public theorem consume `exists_stronglyNormal_form`; eliminate the last sorry;
fix stale docstrings.

**Tasks** (report 03 §B.4 Route 1):
- [ ] Re-point `subformula_property`:
  ```lean
  theorem Theory.Derivation.subformula_property (d : T.Derivation G A) :
      ∃ d', d'.isStronglyNormal = true ∧ d'.SubformulaProperty := by
    obtain ⟨d', hsn⟩ := d.exists_stronglyNormal_form
    exact ⟨d', hsn, d'.subformula_property_of_isStronglyNormal hsn⟩
  ```
- [ ] **Strategic sorry**: with `subformula_property` no longer depending on it,
      `normalize_isStronglyNormal` (the `d.normalize.redexWeight = 0` sorry) has **no consumers**
      (grep-confirm). Preferred: **remove it** (and any now-dead `normalizeAux` fuel lemmas). If a
      consumer is found, fall back to **Route 2** — redefine `normalize` via `WellFounded.fix
      normMeasure_wf` so SN is immediate from `WellFounded.fix_eq`. Do **NOT** attempt the `2^height`
      fuel proof.
- [ ] **Rewrite stale docstrings** on `normalize_isStronglyNormal` (if kept) and `subformula_property`:
      remove the `2^d.height`/fuel narrative; describe the height-free DM WF termination
      (cite `[Troelstra-Schwichtenberg2000]` 6.1.8/6.12, `[NegriVonPlato2001]` §2.4).
- [ ] `lake build …Normalization`; `lean_verify Theory.Derivation.subformula_property` — no axioms,
      no sorry; confirm zero sorries in the file.

**Timing**: 0.5 hours · **Depends on**: 3 · **Files**: Normalization.lean

**Verification**: zero sorry; `subformula_property` axiom-clean; docstrings reflect WF/DM argument.

---

### Phase 5: CI Verification and Cleanup [NOT STARTED]

**Goal**: Pass the full CSLib CI pipeline.

**Tasks**:
- [ ] `lake build` (full project); `lake exe checkInitImports`; `lake exe lint-style`; `lake lint`;
      `lake test`; `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Docstrings on new public defs; tidy section headers; remove any dead fuel-era definitions
      flagged by `shake`/`lint`.

**Timing**: 1 hour · **Depends on**: 4 · **Files**: Normalization.lean

**Verification**: all CI green;
`grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` empty.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds.
- [ ] `lake build` (full project) succeeds.
- [ ] `lean_verify` on `reduceRoot_decreases_normMeasure`, `exists_stronglyNormal_form`,
      `subformula_property` — no sorry, no axioms.
- [ ] `lake exe checkInitImports`, `lake exe lint-style`, `lake lint`, `lake test`, `lake shake` pass.
- [ ] `grep -rn "sorry" …/Normalization.lean` returns empty.

## Artifacts & Outputs

- `specs/332_normalization_termination_proof/plans/04_termination-plan-v4.md` (this file)
- `specs/332_normalization_termination_proof/reports/03_commuting-and-wf-bridge.md` (verified tactics)
- `specs/332_normalization_termination_proof/reports/02_lit-termination-strategy.md`
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` (sorry eliminated)

## Helper-Lemma Checklist (report 03 §C)

| Helper | Need | Status |
|---|---|---|
| `maximalFormulas_{andE1,andE2,impE}_commute` (or inline `rw [show …]`) | Phase 2b-commuting fst-equality | inline verified; extract only if heartbeats spike |
| `maximalFormulas_weakCtx` (h_8) | rewrite `(E.weakCtx).mf = E.mf` | **already present** (line ~1139) |
| `reduceRoot_none_subSN_isStronglyNormal` (or reuse `redexWeight_zero_sn`) | Phase 3 base case | reuse existing |
| `normSubterms` | Phase 3 step 1 | to write |
| `exists_stronglyNormal_form` | Phase 3 main | to write |

No new imports. No axioms. No `2^height` fuel proof. No confluence.

## Rollback/Contingency

1. **On-disk progress is the baseline** — the file builds with 1 sorry and 7 of 8 decrease cases
   proved. Restore from the last green commit on trouble; never `git checkout 2826b053`.
2. **If a commuting case resists** the inline `cases <;> simp_all` equality: extract the named
   `maximalFormulas_*_commute` helper and prove it in isolation (report 03 §A.3).
3. **If `exists_stronglyNormal_form` step-1 (`normSubterms`) stalls**: use `normalizeAux`'s
   structural (reduceRoot-free) subterm pass for step 1 only, invoking the WF IH for the root
   (report 03 §B.5, second option).
4. **If Route 1 surfaces a `normalize` SN consumer**: switch to Route 2 (`WellFounded.fix`-defined
   `normalize`); only then is `normalize_isStronglyNormal` needed, and it is immediate from
   `WellFounded.fix_eq`.
5. **Minimal fallback**: leave the decrease lemma fully proved and the strategic sorry isolated;
   mark Phase 4 [BLOCKED] with the exact goal state — never leave the file multi-error.
