# Implementation Plan (Revised v2): Task #332

- **Task**: 332 - Prove normalization termination theorem for CSLib Theory.Derivation
- **Status**: [NOT STARTED]
- **Effort**: 12 hours
- **Dependencies**: None (Task 290 is [PARTIAL] with this same sorry; this task directly resolves it)
- **Research Inputs**: specs/332_normalization_termination_proof/reports/01_termination-research.md; specs/332_normalization_termination_proof/handoffs/phase-2-handoff-20260624T163704Z.md
- **Artifacts**: plans/01_termination-plan.md (superseded), plans/02_termination-plan-revised.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a **revision** of plan v1 (`01_termination-plan.md`). It exists because v1's
assumptions about the starting state were wrong and the codebase is now in a *worse* state
than v1 assumed.

**Ground-truth state of `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`
(verified by `lake build` and `git`):**

- The file is **1379 lines** and **does NOT build**. It contains **8 sorries** plus ~30 hard
  elaboration errors in lines 1097-1292.
- Lines <1097 build cleanly (the `weak_isStronglyNormal` regression at 837-879 was repaired and
  committed at `86d46c99`).
- Lines 1097-1292 are the "Phase 1 measure infrastructure" + "Phase 2 decrease lemmas" region
  that prior orchestration sessions added and committed **in a broken state**:
  - Line 1097 `normTriple` - "Failed to find LCNF signature for ..._sizeOf_inst" (codegen
    failure on the triple-measure definition).
  - Lines 1116-1229 `maximalFormulas_le_andI_*`, `sn_maximalFormulas_empty`,
    `sn_commutingSum_zero` - unsolved goals and application type mismatches.
  - Lines 1278-1292 `reduceRoot_decreases_normMeasure`, `normalize_isStronglyNormal` - type
    mismatches + unsolved goals.
- The original **clean baseline** is commit `2826b053` ("task 290: orchestration paused - 1 sorry
  remains"). At that commit the file is **1099 lines** and builds with **exactly ONE sorry**
  (in `normalize_isStronglyNormal`, at the goal `d.normalize.redexWeight = 0`). Since then ~280
  net lines were added across several orchestration commits, leaving the file broken.

Two genuine **mathematical blockers** surfaced during the (broken) Phase 2 work and must be
designed around, not merely retried:

1. **subsOne induction infeasible.** `subsOne_maximalFormulas_complexity_bound` cannot be proved
   by structural induction because `subsOne` routes through `subs`, which uses opaque tactic
   blocks (`by grind`, `weakCtx` rewrites). Induction on its *output* is blocked.
2. **Vacuous / false hypothesis.** `reduceRoot_decreases_normMeasure` carried
   `h_allSubsSN : ∀ {G' A'} (D), True` - literally vacuous. Commuting conversions can *increase*
   `maximalFormulas` when subterms aren't strongly normal, so the theorem **is false as stated**.
   The SN-subterm invariant must thread through the well-founded recursion (a Phase 2/Phase 3
   interface redesign).

### Strategic Decision: Path A (Revert and Rebuild Clean) — RECOMMENDED

Two paths were weighed:

**Path A — Revert and rebuild clean.** Restore the clean 1-sorry baseline, then implement the
well-founded approach fresh with the lessons learned baked into the design (proper SN-threading
invariant; avoid the `subsOne`-induction trap). Pro: starts from a compiling file; no time wasted
debugging committed-broken code. Con: discards the partial measure definitions — but those can be
re-derived in minutes, and several of them (`normTriple`, the vacuous `h_allSubsSN`) are *wrong*
and would be discarded anyway.

**Path B — Repair in place.** Fix the ~30 hard errors in 1097-1292, then complete Phase 2. Pro:
preserves existing definitions. Con: debugging another agent's broken committed code is typically
slower than rewriting; and the two most load-bearing artifacts are structurally wrong — the
`normTriple` codegen failure (the `sizeOf` component is the wrong way to handle structural
recursion under `WellFounded.fix`) and the **false** `reduceRoot_decreases_normMeasure` statement.
Repairing them means rewriting them anyway, while also carrying the risk of subtle leftover
breakage in the surrounding 30-error region.

**Recommendation: Path A.** Reasoning:

1. **The broken artifacts are not assets — they are liabilities.** Path B's only claimed benefit
   is "preserves existing definitions," but the central definition (`reduceRoot_decreases_normMeasure`
   with vacuous `h_allSubsSN`) encodes a *false theorem*, and `normTriple` has a codegen failure
   indicating the recursion structure is wrong. Preserving wrong scaffolding is negative value.
2. **A compiling baseline is worth more than partial definitions.** Path A starts from a file that
   builds (`2826b053`), so every subsequent phase has a green build to verify against. Path B starts
   from a 30-error file where it is hard to tell whether a new error is yours or pre-existing.
3. **The cheap parts re-derive trivially.** `maximalFormulas`, `commutingSum`, `nodeCount`,
   `normMeasure`, and `normMeasure_wf` are all short (<10 lines each) and several are correct in the
   broken file — they can be transcribed back verbatim. The expensive parts (the decrease lemmas)
   must be rewritten under either path because the old statements are false.
4. **The SN-threading redesign is incompatible with the committed structure.** The fix for Blocker 2
   changes the *interface* of the decrease lemma (it must consume real SN hypotheses on subterms).
   That is a redesign, not a repair.

### How the Two Blockers Are Addressed in the Phase Design

**Blocker 1 (subsOne induction).** Do **not** prove a bound by inducting on `subsOne`'s output.
Instead, prove the complexity bound by induction on the **input derivation `body`** with a
generalized statement about `subs`, OR — preferred — avoid the bound entirely by choosing the
measure so that the substitution beta-cases are discharged by a *subformula-complexity* argument
that never inspects `subsOne`'s structure. Concretely, the maximal-formula multiset decrease for a
beta-redex of cut formula `C` is witnessed by removing `{complexity C}` and adding only elements
`< complexity C`; the elements added are bounded by `subsOne`'s newly-created redexes, each of which
sits at a *proper subformula* of `C`. We prove "every redex `subsOne body arg` introduces has cut
complexity `< complexity C`" via induction on `body` (the structural input), stated over the general
`subs` so the `weakCtx`/`grind` branches are covered by the IH rather than re-analyzed. Phase 2a
isolates this as a single, self-contained lemma with a clearly-stated induction motive on `body`.

**Blocker 2 (SN-subterm invariant).** The decrease lemma must **not** be stated with a vacuous
`h_allSubsSN`. Instead, the SN-subterm invariant threads through `normalizeWF` as follows: the WF
recursion normalizes immediate subterms *first* (structural recursion), so by the time `reduceRoot`
is applied at the root, all immediate subterms are already strongly normal. The decrease lemma
therefore takes the shape

```
reduceRoot_decreases_normMeasure :
  (∀ each immediate subterm s of d, s.isStronglyNormal = true) →
  d.reduceRoot = some d' →
  normMeasure d' < normMeasure d   -- in Prod.Lex IsDershowitzMannaLT (· < ·)
```

with a *real* SN hypothesis. For commuting cases, SN of subterms rules out introduction forms at
redex positions (an `orE`/`andE` whose major premise is SN cannot expose a matching introduction),
so pushing the elimination inside creates **no new maximal formulas** — giving `maximalFormulas`
*equality*, and the strict decrease comes from `commutingSum` via `Prod.Lex.right`. This invariant is
*supplied by the caller* (`normalizeWF`), which is exactly why the structure must be a Phase 2/3
co-design rather than two independent phases.

### Research Integration

Newly integrated since plan v1: the **Phase 2 handoff**
(`handoffs/phase-2-handoff-20260624T163704Z.md`), which is the authoritative record of *why* the
committed Phase 2 is broken (Blocker 1 and Blocker 2 above) and which decrease cases were genuinely
proved (the two conjunction beta-projection cases via explicit Dershowitz-Manna witnesses).

Carried forward from the research report (`01_termination-research.md`):

- **Section 3**: Simple measures fail (`redexWeight` not monotone; `2^height` fuel insufficient;
  height does not decrease under commuting conversions). This kills Approaches B and C from the
  report and confirms the WF approach (A) is the only sound path.
- **Section 4**: Correct measure is `(maxFormulaMultiset, commutingSum)` ordered by
  `Prod.Lex IsDershowitzMannaLT (· < ·)`. Section 4.4's subformula-complexity sub-lemma is the seed
  for the Blocker-1 fix.
- **Section 6**: `Mathlib.Data.Multiset.DershowitzManna` provides `wellFounded_isDershowitzMannaLT`
  (already imported and confirmed usable; `normMeasure_wf` compiled in the broken file).

### Prior Plan Reference

This supersedes `01_termination-plan.md`. In v1, **Phase 1 was marked [COMPLETED]** and **Phase 2
[PARTIAL]** — but those statuses are not trustworthy: the committed code from those phases does not
build. Under Path A those phases are **discarded** (the file reverts to a pre-Phase-1 state) and
re-executed with corrected designs. No phase from v1 is preserved as [COMPLETED], because none of
the committed Phase 1/2 code compiles in the current tree.

### Roadmap Alignment

Advances the Propositional Natural Deduction module within `Logics/Propositional/`. Not directly in
ROADMAP.md (which focuses on BimodalLogic porting) but is foundational proof-theory infrastructure.

## Goals & Non-Goals

**Goals**:
- Restore a compiling file from the clean `2826b053` baseline (1 sorry).
- Define the Dershowitz-Manna based termination measure `(maximalFormulas, commutingSum)`.
- Prove `reduceRoot_decreases_normMeasure` with a **real** SN-subterm hypothesis (no vacuous `True`).
- Resolve Blocker 1 via a subformula-complexity lemma proved by induction on the *input* `body`.
- Define `normalizeWF` via `WellFounded.fix`, threading the SN-subterm invariant.
- Prove `normalizeWF_isStronglyNormal`, bridge to `normalize`, eliminate the sorry.
- Produce a sorry-free, axiom-clean Normalization.lean that passes full CSLib CI.

**Non-Goals**:
- Repairing the committed 1097-1292 region in place (explicitly rejected; see Path A decision).
- Optimizing computational behavior of `normalize`.
- Proving tight `2^height` fuel bounds (the WF approach avoids fuel reasoning).
- Extending normalization to first-order or modal natural deduction.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Reverting loses a *correct* committed lemma worth keeping | L | L | Before reverting, transcribe the two proved conjunction-projection DM witnesses from the handoff into the new Phase 2; they are short and re-applied verbatim |
| Blocker-1 induction on `body` still blocked by `subs` tactic blocks | H | M | State the lemma over `subs` (not `subsOne`) with an explicit motive; if `subs`'s `grind` branches resist, prove a `subs_preserves_maxFormula_bound` helper that only needs `subs`'s *recursion equations*, not its internal tactics |
| SN-subterm invariant hard to thread through `WellFounded.fix` | H | M | Co-design Phase 2/3: prove the decrease lemma with the SN hypothesis as an explicit argument, then `normalizeWF` discharges it from the already-normalized subterms (structural recursion runs first) |
| `WellFounded.fix` unfolding difficulties in proofs | M | M | Define `normalizeWF_unfold` via `WellFounded.fix_eq` immediately after the definition |
| `normTriple`/`sizeOf` codegen failure recurs | M | L | Do NOT reintroduce the `sizeOf` triple; use the *pair* measure `normMeasure` and handle subterm recursion structurally (subterms normalized before the WF call), not via a `sizeOf` lex component |
| Bridge from `normalizeWF` to `normalize` blocked by fuel insufficiency | H | M | Replace `normalize`'s definition to call `normalizeWF` directly (research Section 3.2 shows `2^height` is likely insufficient, so equivalence-via-fuel is not attempted) |
| Heartbeat/timeout on large case analyses | M | M | Split decrease lemma into per-pattern private helpers; `set_option maxHeartbeats` locally if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2a | 1 |
| 4 | 2b | 2a |
| 5 | 3 | 2b |
| 6 | 4 | 3 |
| 7 | 5 | 4 |

Phases within the same wave can execute in parallel (here each wave is a single phase).

---

### Phase 0: Revert to Clean Baseline [NOT STARTED]

**Goal**: Restore the compiling 1-sorry baseline so all later phases verify against a green build.

**Tasks**:
- [ ] Confirm the only uncommitted/divergent content in the target file is the broken Phase 1/2
      work: `git log --oneline 2826b053..HEAD -- Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`
- [ ] **Preserve the two correct DM witnesses first**: copy the proved
      `reduceRoot_andE_maxFormulas_lt` and `reduceRoot_andE2_maxFormulas_lt` bodies (conjunction
      beta-projection cases, per the handoff) into the plan's scratch notes / a comment block for
      reuse in Phase 2b.
- [ ] Revert the file:
      `git checkout 2826b053 -- Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` — expect SUCCESS
      with exactly one `sorry` warning (in `normalize_isStronglyNormal`).
- [ ] Confirm `grep -c "sorry"` returns 1 and the file is 1099 lines.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` — reverted to `2826b053`.

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds.
- Exactly 1 sorry; 0 hard errors.

---

### Phase 1: Termination Measure Infrastructure [COMPLETED]

**Goal**: Re-introduce the **pair** measure `(maximalFormulas, commutingSum)` and its
well-foundedness. Deliberately omit the broken `normTriple`/`sizeOf` triple.

**Tasks**:
- [x] Confirm `import Mathlib.Data.Multiset.DershowitzManna` is present (it is, transitively). *(altered: added explicitly as `public import` since clean baseline only imported Basic; module syntax requires `public import`)*
- [x] Define `nodeCount : T.Derivation G A → Nat` (total node count) if not already present. *(completed)*
- [x] Define `maximalFormulas : T.Derivation G A → Multiset Nat` — multiset of `complexity(F)` for
      each beta-redex pattern (the 5 proper redex patterns in `reduceRoot`); recurses into subterms. *(completed)*
- [x] Define `commutingSum : T.Derivation G A → Nat` — sum over commuting-conversion sites of the
      node count of the sub-derivation rooted at each site. *(completed)*
- [x] Define `normMeasure d := (d.maximalFormulas, d.commutingSum) : Multiset Nat × Nat`. *(completed)*
- [x] Prove `normMeasure_wf : WellFounded (InvImage (Prod.Lex Multiset.IsDershowitzMannaLT (· < ·)) normMeasure)`
      via `InvImage.wf _ (WellFounded.prod_lex Multiset.wellFounded_isDershowitzMannaLT Nat.lt_wfRel.wf)`.
      (This exact proof compiled in the broken file — transcribe it.) *(completed; lean_verify confirms only propext/Classical.choice/Quot.sound axioms)*
- [x] **Do NOT** define `normTriple` or any `sizeOf`-based lex measure (this was the LCNF codegen
      failure). Structural subterm recursion is handled inside `normalizeWF` (Phase 3), not via a
      measure component. *(honored: normTriple and sizeOf deliberately omitted)*
- [ ] Add monotonicity helpers as needed (e.g. `maximalFormulas_le_andI_left/right`) but only those
      that compile cleanly; prefer `Multiset.le_add_right`/`le_add_left`. *(deviation: skipped — not required by Phase 1 verification; prior versions had unsolved goals. Defer to the phase that needs them.)*
- [x] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`. *(completed: builds successfully, 1 sorry, 0 errors)*

**Timing**: 1.5 hours

**Depends on**: 0

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` — add definitions after the
  existing `redexWeight` section.

**Verification**:
- All new definitions compile; build still has exactly 1 sorry (the original one).
- `lean_verify` confirms no axioms/sorry in the new definitions.

---

### Phase 2a: subsOne Subformula-Complexity Lemma [COMPLETED]

**Goal**: Resolve **Blocker 1**. Prove that any new beta-redex created by `subsOne` has cut-formula
complexity strictly less than the original cut formula's complexity, WITHOUT inducting on `subsOne`'s
output.

**Tasks**:
- [x] State the lemma over the structural input `body` (and generalized over `subs`, not `subsOne`):
      every maximal formula appearing in `subs σ body` that is not already present in `body` has
      complexity `< complexity C`, where `C` is the type being substituted. The induction motive is
      on the structure of `body`. *(completed — `subs_maximalFormulas_mem`: characterizes membership
      as `∈ body.mf ∨ (∃ A'∈Γ', ∈ (Ds A').mf) ∨ (∃ A'∈Γ', k = A'.complexity)`, proved by induction
      on `body`)*
- [x] Prove by induction on `body`. For the `ass`/`orE`/`impI` branches where `subs` uses
      `weakCtx`/`by grind`, rely on `subs`'s recursion equations so the IH covers them.
      *(altered — introduced the `subs_maxFormula_mem`-style helper as planned, plus supporting
      lemmas `maximalFormulas_weak/_weakCtx/_cast/_castType/_heq/_cast_weakCtx` to strip the
      `weakCtx`/`cast` wrappers `subs` inserts; bounds `maximalFormulas_andE1_le/_andE2_le/_impE_le/
      _orE_le` and decomposition `maximalFormulas_subs_orE` handle the elimination cases)*
- [x] Specialize to `subsOne` to obtain `subsOne_new_redex_complexity_lt`. *(completed — yields
      `k ∈ E.maximalFormulas ∨ k = A.complexity` for new redexes; Phase 2b discharges the
      `E.maximalFormulas` disjunct via the SN invariant and notes `A.complexity < complexity(cut)`)*
- [x] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`. *(completed —
      builds with exactly 1 (pre-existing) sorry; new lemmas verified axiom-free via `lean_verify`)*

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`.

**Verification**:
- Lemma compiles with no sorry; `lean_verify` confirms no axioms.
- The statement quantifies over the *input* `body`, never over `subsOne`'s output structure.

---

### Phase 2b: Measure Decrease Lemma (with real SN hypothesis) [IN PROGRESS]

**Goal**: Resolve **Blocker 2**. Prove `reduceRoot_decreases_normMeasure` with a **non-vacuous**
SN-subterm hypothesis, covering all 8 `reduceRoot` patterns.

**Tasks**:
- [ ] State:
      `(h_subsSN : ∀ immediate subterm s of d, s.isStronglyNormal = true) → d.reduceRoot = some d' → `
      `Prod.Lex Multiset.IsDershowitzMannaLT (· < ·) (normMeasure d') (normMeasure d)`.
      The hypothesis is an explicit, real SN predicate — never `True`.
- [ ] **Conjunction beta cases (h_2, h_3)**: transcribe the two DM witnesses preserved in Phase 0
      (`X = D₁.mf`, `Y = ∅`, `Z = {conclusionComplexity} + D₂.mf`), via `Prod.Lex.left`.
- [ ] **Substitution beta cases (h_1, h_4, h_5: impE/orE)**: apply Phase 2a
      (`subsOne_new_redex_complexity_lt`) to construct the DM witness — remove `{complexity C}`, add
      only elements `< complexity C`. `Prod.Lex.left`.
- [ ] **Commuting cases (h_6, h_7, h_8)**: use `h_subsSN` to show subterms are not introduction
      forms at redex positions, hence pushing the elimination inside creates NO new maximal formulas
      ⇒ `maximalFormulas` EQUAL. Then `commutingSum` strictly decreases (the `orE` site's node count
      is removed) ⇒ `Prod.Lex.right`.
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`.

**Timing**: 3 hours

**Depends on**: 2a

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`.

**Verification**:
- All 8 patterns proved with no sorry; `lean_verify` confirms no axioms.
- The SN hypothesis is genuinely used in the commuting cases (not discharged by `trivial`).

---

### Phase 3: Well-Founded Normalization Function [NOT STARTED]

**Goal**: Define `normalizeWF` via `WellFounded.fix` on `normMeasure`, threading the SN-subterm
invariant so Phase 2b's hypothesis is discharged.

**Tasks**:
- [ ] Define `normalizeSubterms` — structurally normalize all immediate subterms (mirrors the inner
      step of `normalizeAux`). This runs FIRST, establishing SN of immediate subterms.
- [ ] Define `normalizeWF : T.Derivation G A → T.Derivation G A` via `WellFounded.fix normMeasure_wf`.
      Body: normalize subterms; if `reduceRoot = some d'`, recurse on `d'` (WF recursion);
      if `none`, return.
- [ ] Discharge the WF obligation using Phase 2b: at the recursive call, subterms are already SN
      (from `normalizeSubterms`), so `h_subsSN` holds, and `reduceRoot_decreases_normMeasure` gives
      `normMeasure d' < normMeasure d`.
- [ ] Prove `normalizeWF_unfold` via `WellFounded.fix_eq`.
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`.

**Timing**: 2 hours

**Depends on**: 2b

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`.

**Verification**:
- `normalizeWF` and `normalizeWF_unfold` compile, no sorry, no axioms.
- The SN-subterm invariant is actually consumed when discharging the decrease obligation.

---

### Phase 4: Main Termination Theorem and Bridge [NOT STARTED]

**Goal**: Prove `normalizeWF` produces SN output; bridge to `normalize`; eliminate the sorry.

**Tasks**:
- [ ] Prove `normalizeWF_isStronglyNormal` by WF induction on `normMeasure`: base case
      (`reduceRoot = none` + SN subterms ⇒ SN); step case (IH applies since measure decreased).
- [ ] **Bridge**: replace `normalize`'s definition (currently `normalizeAux (2^d.height) d`) to call
      `normalizeWF d` directly. (Research Section 3.2 argues `2^height` is insufficient, so do NOT
      attempt `normalize = normalizeWF` via fuel sufficiency.)
- [ ] Update any `normalizeAux`-based downstream lemmas affected by the definition change.
- [ ] Replace the sorry in `normalize_isStronglyNormal` with the real proof
      (`normalizeWF_isStronglyNormal`, possibly via `redexWeight_zero_sn`).
- [ ] Verify `subformula_property` still compiles (it depends on `normalize_isStronglyNormal`, not on
      `normalize`'s definition).
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`.

**Verification**:
- Zero sorry in the file; `lean_verify` on `normalize_isStronglyNormal` and `subformula_property`
  shows no axioms, no sorry.

---

### Phase 5: CI Verification and Cleanup [NOT STARTED]

**Goal**: Pass the full CSLib CI pipeline and clean up style/docs.

**Tasks**:
- [ ] `lake build` (full project) — no regressions.
- [ ] `lake exe checkInitImports`.
- [ ] `lake exe lint-style`.
- [ ] `lake lint`.
- [ ] `lake test`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Fix any lint/style issues; add docstrings to all new public definitions.
- [ ] Ensure new code is organized under appropriate `/-! ## ... -/` section headers.

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` — style/lint/docstrings.

**Verification**:
- All CI commands pass without warnings.
- `grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` is empty.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds.
- [ ] `lake build` (full project) succeeds.
- [ ] `lean_verify` on `normalize_isStronglyNormal` and `subformula_property` — no sorry, no axioms.
- [ ] `lake exe checkInitImports`, `lake exe lint-style`, `lake lint`, `lake test`, `lake shake` pass.
- [ ] `grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` returns empty.

## Artifacts & Outputs

- `specs/332_normalization_termination_proof/plans/02_termination-plan-revised.md` (this file)
- `specs/332_normalization_termination_proof/reports/01_termination-research.md` (research input)
- `specs/332_normalization_termination_proof/handoffs/phase-2-handoff-20260624T163704Z.md` (handoff input)
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` (reverted, then rebuilt; sorry eliminated)

## Rollback/Contingency

1. **Baseline always recoverable**: `git checkout 2826b053 -- <file>` restores the clean 1-sorry
   state at any time.
2. **If Blocker 1 (Phase 2a) proves intractable** even with the input-induction approach: fall back
   to refactoring `subsOne` to a pattern-matching definition (handoff option (b)). This is a larger
   change but makes structural properties provable; spin it out as a dependency task if it exceeds
   the effort budget.
3. **If Blocker 2 (Phase 2b) commuting cases resist** the no-new-maximal-formulas argument: prove the
   weaker `maximalFormulas` *inequality* and lift the SN invariant to a stronger "fully normalized
   subterms" predicate threaded through `normalizeWF`.
4. **Minimal fallback**: if the WF approach cannot be completed within budget, revert to the clean
   baseline, mark the phase [BLOCKED], and document the precise goal state reached — never leave the
   file in a broken multi-error state as the prior sessions did.
