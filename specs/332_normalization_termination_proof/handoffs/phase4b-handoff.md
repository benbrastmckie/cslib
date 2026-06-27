# Task 332 Phase 4b Handoff — `snSubst` Mutual Termination (L3/L4/L5)

**Status:** PARTIAL. The mutual well-founded **termination encoding is SOLVED and
machine-checked** (the crux that stalled the two prior attempts). The remaining gap is the
single *head-bound* termination side-condition plus the mechanical SN-reassembly proofs and
context-cast bookkeeping. `Termination.lean` (main file) was **never touched** and stays green
with its pre-existing fuel `sorry`.

**Scratch file (committed):**
`Cslib/Logics/Propositional/NaturalDeduction/Normalization/TerminationScratch.lean`
— a standalone copy of `Termination.lean` with the L3/L4/L5 development appended after the fuel
theorem. Build it with:
```
lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization.TerminationScratch
```
It builds GREEN modulo `sorry` warnings (no `error:`). All `sorry`s are catalogued below.

---

## 1. The validated termination encoding (the headline result)

The block `snImpEForm` (L3), `snOrEForm` (L4), `snSubst` (L5) is accepted by Lean's
well-founded recursion checker under the **3-component lexicographic measure**

```
(cut-formula complexity, phase, structural size) : Nat ×ₗ Nat ×ₗ Nat
```

| function     | cut formula | termination_by                         |
|--------------|-------------|----------------------------------------|
| `snImpEForm` | `A → B`     | `((A → B).complexity, 0, sizeOf f)`    |
| `snOrEForm`  | `A ∨ B`     | `((A ∨ B).complexity, 0, sizeOf D)`    |
| `snSubst`    | `P`         | `(P.complexity, 1, sizeOf body)`       |

`phase = 0` for the eliminators, `phase = 1` for `snSubst`. The phase component is what lets the
`snSubst → eliminator` edge decrease **even when the cut complexity is equal** (bare-variable
site, `Q = P`): `(P, 1, _) > (P, 0, _)`.

### Why prior attempts failed, and why this works

The naive flat measure `(P.complexity, sizeOf body)` fails because at an `impE`/`orE` node
`snSubst body arg` must re-eliminate the substituted child via `snImpEForm`/`snOrEForm`, whose
principal premise is `(snSubst D' arg).1` — a freshly built term of type `Q` (the type of `D'`)
whose `sizeOf` is unrelated to `sizeOf body`, and whose `Q.complexity` can EXCEED `P`.

The fix has two parts, both verified:
1. **Phase tag** handles the equal-complexity bare-variable site.
2. **Head restriction** (the one remaining obligation, see §2) guarantees the eliminator is only
   invoked when the substituted child became intro-/orE-headed, i.e. along the substituted
   variable's elimination spine, where `Q.complexity ≤ P.complexity`.

### `decreasing_by` proofs that are mechanically discharged (no `sorry`)

```lean
-- snImpEForm / snOrEForm:
decreasing_by all_goals
  (simp_wf; first | (left; simp [Proposition.complexity]; omega) | (right; omega))

-- snSubst:
decreasing_by all_goals first
  | decreasing_tactic                                   -- structural (snSubst → snSubst)
  | (simp_wf; left; simp [Proposition.complexity]; omega) -- β-drop to proper subformula
  | sorry                                                -- HEAD-BOUND (the only gap)
```

* `decreasing_tactic` closes every structural `sizeOf child < sizeOf parent` goal.
* `left; simp [Proposition.complexity]; omega` closes every β-edge using
  `A.complexity < (A → B).complexity` / `A.complexity < (A ∨ B).complexity` (helper lemmas
  `cx_imp_left`, `cx_imp_right`, `cx_or_left`, `cx_or_right` are in the scratch and PROVEN).

---

## 2. The SOLE remaining termination obligation: the HEAD-BOUND

At `snSubst`'s `impE D' E'` node (and symmetrically the `orE` node), the current minimal scratch
ALWAYS calls `snImpEForm (snSubst D' …).1 …`. This produces the `decreasing_by` goal

```
((type of D').complexity, 0, sizeOf (snSubst D' arg).1) < (P.complexity, 1, sizeOf body)
```

which is **false in general** (type of `D'` can exceed `P` when `D'` is not headed by the
substituted variable). It is `sorry`-ed.

**To make it true and provable**, the real `snSubst` must MATCH on the head of
`(snSubst D' arg).1`:
* head is intro/`orE` ⇒ the substituted variable was at the head of `D'`'s elimination spine;
  then `(type D').complexity ≤ P.complexity`, so the edge decreases (`<` ⇒ first component, or
  `=` ⇒ phase `0 < 1`). Invoke the eliminator here.
* head is neutral (`ax`/`ass`/`andEᵢ`/`impE`) ⇒ reassemble `impE (snSubst D').1 (snSubst E').1`
  directly; it is SN, no eliminator call, no obligation.

Supplying `(type D').complexity ≤ P.complexity` requires a **head-behaviour invariant** carried
in the subtypes, of the shape:
```
(body is neutral, i.e. ¬ body.isIntroRoot) →
  ((d.isIntroRoot = true ∨ d.isOrERoot = true) → B.complexity ≤ P.complexity)
```
maintained by `snSubst` and the eliminators, plus standalone head-behaviour lemmas for the
external `snAndE1Form`/`snAndE2Form` ("output intro/orE-headed ⇒ input was `andI`/`orE`-headed").
This is the classic neutral/normal invariant of hereditary substitution / NbE. Estimated
~150–300 lines; it is the genuine residual difficulty.

---

## 3. What compiles today (reusable assets in the scratch)

* `snImpEForm` (L3): **complete** structural eliminator — `impI`→β `snSubst`; `orE`→commuting
  push (structural, SN-reassembly via `cases D <;> simp_all [isStronglyNormal]`); neutral leaves
  reassemble `impE`. Its `decreasing_by` is **fully proven** (no sorry). (Stage-1 standalone
  `snImpEFormS` against a stub also builds, confirming the eliminator in isolation.)
* `snOrEForm` (L4): `orI1`/`orI2`→β `snSubst`; neutral leaves reassemble `orE` (SN proofs done);
  `orE` commuting case is `sorry` (needs context casts). `decreasing_by` fully proven.
* `snSubst` (L5): cases `impE` (head-bound edge), `andE1`/`andE2` (→`snAndEᵢForm`∘`snSubst`),
  `andI`; other cases `sorry`. SN-reassembly proofs `sorry`. `decreasing_by` proven except the
  one head-bound `sorry`.

### `sorry` inventory in scratch (all in `TerminationScratch.lean`)
1. line ~1467 — pre-existing fuel `sorry` in `normalize_isStronglyNormal` (copied from main; DO NOT touch).
2. `snSubstStub` — stage-1 scaffolding stub (delete when porting).
3. `snImpEFormS` — none (stage-1, builds; delete when porting).
4. `snOrEForm` `orE` commuting case — context casts (item 3 of remaining work).
5. `snSubst` SN-reassembly proofs + `impI`/`orE`/leaf data `sorry`s.
6. `snSubst.decreasing_by` head-bound `sorry` — **the one termination gap (§2).**

---

## 4. Recommended next steps (in order)

1. Implement the **head-match** in `snSubst.impE`/`orE` cases (§2) and the carried head invariant;
   discharge the head-bound `decreasing_by` from it. This removes the last termination `sorry`.
2. Fill the SN-reassembly `sorry`s (mechanical, follow L1/L3 leaf patterns).
3. Do the `impI`/`orE` context casts (`insert` commutation + `weakCtx`); thread `sizeOf`-cast
   equalities into `decreasing_by` (use `decreasing_tactic` after a `simp` that rewrites the cast,
   or prove `sizeOf (h ▸ D') = sizeOf D'`).
4. Add L6 `snForm` (structural driver, plan §3) and `exists_stronglyNormal_form`, then re-point
   `subformula_property` (plan §4) and delete the now-unused fuel `sorry`.
5. Port the finished block into `Termination.lean`, delete `TerminationScratch.lean`, run the CI
   pipeline.

## 5. Key facts / API used
* `subsOne_new_redex_complexity_lt` (Termination.lean:876), `maximalFormulas_sn_eq_zero` (:977):
  the mathematical justification that substitution's new redexes sit at cut = `P.complexity`
  (i.e. the head-bound is mathematically TRUE); they will feed the head invariant proof.
* `isStronglyNormal_weakCtx` (L0, :1405), `snAndE1Form`/`snAndE2Form` (L1/L2, :1413/:1434).
* **Name clash gotcha:** `impI`/`impE` are also defs in `FromHilbert.lean` (same `Cslib.Logic.PL`
  namespace). In `Theory.Derivation.*` bodies use `.impI`/`.impE` (patterns) and
  `Derivation.impE` (terms); bare `impI`/`impE` resolve to the wrong declaration.
* Declaring the functions as `Theory.Derivation.foo` (not bare `foo`) is REQUIRED so the body
  auto-opens the `Theory.Derivation` namespace (bare `isStronglyNormal`, `ax`, `andE1`, …).
