# Research Report: Measure-Decrease Termination for Classical Tableau Fuel Sufficiency (Task 376)

- **Task**: 376 — close the single `sorry` at `Completeness.lean:~801` in `classicalExpandBranches_hintikka`
- **Type**: cslib (Lean 4, hard mode)
- **Reference grounding tier**: Tier 1 (literature-backed: Smullyan1968, Fitting1983; plus Dershowitz–Manna ordering)
- **Recommended approach**: **(b-exp-bound)** — additive base-3 exponential measure + raise fuel bound to `3 ^ φ.complexity`
- **Feasibility**: VALIDATED via `lean_run_code` (core arithmetic + base-case discharge compile sorry-free)

## TL;DR

The characterized gap is **correct and is a genuine correctness bug, not just a proof obstacle**:
the current fuel bound `4*(φ.complexity+1)+1` is **linear** but the number of global expansion
steps is **exponential** in `φ.complexity` (beta rules duplicate the whole branch). So the existing
`classicalTableau` can return `.openBranch` for a tautology once fuel is exhausted prematurely —
the proof cannot be closed because the statement, at the standard bound, is effectively false for
`complexity ≥ 3`.

The fix is to (i) replace the additive count measure `classicalTotalMeasure` with an additive
**base-3 exponential** measure `Φ = Σ_branches 3 ^ (branchComplexity branch expandedSet)` that
strictly decreases by ≥1 per expansion step (beta-robust), and (ii) raise the fuel bound in
`Expansion.lean` to `3 ^ φ.complexity` (which is exactly `Φ` of the initial state). This keeps the
entire existing Nat-fuel induction intact, reuses all invariant/Hintikka machinery, and even
*simplifies* the `fuel = 0` base case to a one-line contradiction.

## Source-to-Implementation Mapping

| Source Claim | BibKey | Lean Target | Translation Notes |
|--------------|--------|-------------|-------------------|
| Analytic tableau rules produce strict subformulas (uniform notation α/β) | Smullyan1968 (Ch. V) | `classicalApplyOne` / `applyPropRule` (8 rules) | Each rule output's total complexity = `complexity(sf) - 1`; per child branch ≤ `complexity(sf) - 1` |
| Tableau termination via decreasing measure | Fitting1983 (Ch. 2) | `classicalExpandBranches_hintikka` fuel induction | Measure must be beta-robust; additive count is NOT |
| Multiset path order well-founded (remove x, add finitely many < x) | Dershowitz–Manna | `Multiset.IsDershowitzMannaLT` (`Mathlib.Data.Multiset.DershowitzManna`) | Mathematically exact characterization of the step; but its use forces a function refactor (rejected, see §Decision) |

BibKey note: `Smullyan1968` and `Fitting1983` are cited in the module headers of
`Expansion.lean` (lines 33–34) and `PropositionalRules.lean`. I did not open
`references.bib` directly; the citation keys are taken from the in-file `[Author1968]`
references already used in the codebase. If `references.bib` lacks these keys they should be
added, but they are already in active use across the Tableau modules.

## Findings

### F1. The gap is real and is a correctness defect (4-element defect record)

- **Counterexample (current behavior)**: with the linear bound, for a formula of `complexity = c`
  whose tableau has an exponential number of nodes (e.g. a wide conjunction of disjunctions),
  `classicalExpandBranches` consumes one fuel unit per single-formula expansion *per branch*.
  Beta rules (`andNeg`, `orPos`, `impPos`) copy the entire branch into 2 children
  (`Branch.extendMany b out = out ++ b`), so total steps grow like the node count of the tableau
  tree — exponential. The plan's own counterexample (`classicalExpandBranches [[T(p∧q)]] [[]] 0
  → .openBranch [T(p∧q)]`, not Hintikka) is the degenerate `fuel = 0` symptom of this.
- **Current behavior**: at `complexity ≥ 3`, `4*(c+1)+1 < 3^c`; fuel can hit 0 with unexpanded
  applicable formulas remaining; the `fuel = 0` arm returns a non-saturated open branch.
- **Required behavior**: fuel must dominate the global step count, i.e. `fuel ≥ Φ_initial = 3^c`.
- **Isolation**: `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean:158`
  (`let fuel := 4 * (φ.complexity + 1) + 1`) and the measure in
  `Completeness.lean` (`classicalTotalMeasure`, lines 482–485).

This refutes the implicit premise of the original plan that the *existing* bound is sufficient;
it confirms the planner's own correction (plan §Overview point 2).

### F2. Per-branch complexity strictly decreases; the additive *count* does not

`classicalBranchComplexity b e = Σ over (b filtered to unexpanded) of sf.formula.complexity`
(infra present in reverted commit `29e9d5b0`, with `_append` and `_mono_expanded`).

For the expansion step `classicalStepBranch b e = some (newBs, newExp)` (chosen formula `sf`,
`newExp = e ++ [sf]`, `sf ∈ b`, `sf ∉ e`):
- `extendMany b out = out ++ b`, and by `_append`:
  `bc (out ++ b) (e++[sf]) = bc out (e++[sf]) + bc b (e++[sf])`.
- `bc out (e++[sf]) ≤ Σ_{x∈out} complexity x = complexity(sf) − 1` (rule output identity, all 8 cases).
- `bc b (e++[sf]) ≤ bc b e − complexity(sf)` (NEW "drop" lemma: removing `sf ∈ b\e` from the
  unexpanded set drops its complexity; strengthening of the existing `_mono_expanded`).
- Therefore **each child branch** satisfies `bc child newExp ≤ bc b e − 1` (strict per-branch
  decrease), for BOTH alpha (1 child) and beta (2 children) — duplicates in `out` only lower `bc`.

The additive count `classicalTotalMeasure` fails because beta replaces one branch (count `n`) by
two branches (count `~2(n−1)`): the sum grows. Confirmed.

### F3. Base-3 exponential aggregation is beta-robust and minimal

Define `Φ branches expandedSets := ((branches.zip expandedSets).map
  (fun p => 3 ^ classicalBranchComplexity p.1 p.2)).sum` (mirrors `classicalTotalMeasure`'s shape
exactly, so the existing zip/index bookkeeping transfers).

`Φ` is additive over branch-list concatenation. At an expansion step the `done` and `restBs`
branches are unchanged; the replaced branch `b` (term `3^C`, `C = bc b e ≥ 1`) becomes
`Σ_{child} 3^(bc child newExp)` with each child exponent `≤ C−1`. The required strict decrease is:

- alpha/persistent (1 child): `3^a + 1 ≤ 3^C` for `a ≤ C−1`, `C ≥ 1`.
- beta (exactly 2 children): `3^a₀ + 3^a₁ + 1 ≤ 3^C` for `a₀,a₁ ≤ C−1`, `C ≥ 1`.

Base **3 is minimal**: any sum-over-branches Nat measure `f(C)` must satisfy `f(C) > 2 f(C−1)`
to absorb a balanced 2-way split, forcing at-least-exponential growth; base 2 fails
(`2·2^(C−1)+1 > 2^C`), base 3 works (`3^(C−1)(3−2) ≥ 1`). Branching is always exactly 2-way
(`applyPropRule` emits 2-element `branching` lists), so base 3 suffices universally.

`Φ_initial = 3 ^ classicalBranchComplexity [F φ] [] = 3 ^ φ.complexity` exactly, so the new fuel
bound `3 ^ φ.complexity` discharges `Φ_initial ≤ fuel` by `le_refl`.

### F4. The `fuel = 0` base case becomes a contradiction (simplification)

Under `Φ`, `Φ = 0` is impossible when `branches ≠ []` (each summand `3^x ≥ 1`, so `Φ ≥
branches.length ≥ 1`). When `branches = []`, `classicalExpandBranches` returns `.closed`, so the
hypothesis `… = .openBranch b` is false. Either way the `fuel = 0` arm is discharged WITHOUT the
old `classicalTotalMeasure_zero_mem_subset` / `classicalRemMeasure_zero_subset` lemmas (which
become dead code and can be removed). This is strictly simpler than the current base case.

### F5. Soundness is fuel-generic — raising the bound is safe

`classicalTableau_sound` (`Soundness.lean:621`) proves `closed → Tautology` via
`classicalExpandBranches_closed_unsat`, which is quantified over arbitrary fuel; it never inspects
the bound's value. Raising the bound only enlarges the iteration ceiling; the loop exits at
saturation/closure long before. No soundness regression. (The bound is referenced *syntactically*
at completeness call sites — see Risks R2 — but only as a literal to reconstruct, not semantically.)

### F6. Mathlib reconnaissance

| Concept | Mathlib name (verified) | Module | Verdict |
|---------|--------------------------|--------|---------|
| Dershowitz–Manna multiset order | `Multiset.IsDershowitzMannaLT` | `Mathlib.Data.Multiset.DershowitzManna` | Exact match for the step; **not used** (needs function refactor) |
| DM well-foundedness | `Multiset.wellFounded_isDershowitzMannaLT`, `Multiset.instWellFoundedIsDershowitzMannaLT` | same | available |
| Multiset WF (subset) | `Multiset.instWellFoundedLT` | `Mathlib.Data.Multiset.Defs` | available |
| Power monotonicity | `Nat.pow_le_pow_right`, `Nat.one_le_pow`, `pow_succ`, `Nat.sub_add_cancel` | core/Mathlib | used in validated arithmetic |

Generic well-founded recursion helpers (`termination_by` / `decreasing_by`, `invImage`,
`Prod.Lex`) exist and *could* retarget `classicalExpandBranches` onto the DM order or a
lexicographic `(multiset, fuel)` measure. Rejected: see Decision.

## Decision (lowest-risk option)

| Option | Verdict | Reason |
|--------|---------|--------|
| **(a-max)** per-branch MAX | **REJECTED (unsound)** | A step touches only the first open branch; other branches keep the max, so MAX does NOT strictly decrease per step. |
| **(a-multiset)** DM multiset order | rejected for this proof | Mathematically exact, but it is not a `Nat`; using it requires reformulating `classicalExpandBranches` with `termination_by`/`decreasing_by`, discarding the existing fuel-generic soundness proof and the whole `classicalExpandBranches_hintikka` Nat-fuel induction. High rework, high risk. |
| **(wf-recursion-refactor)** | rejected | Same objection as (a-multiset), plus the nested `processNext` inner recursion complicates `termination_by`. |
| **(b-exp-bound)** base-3 additive exponential + raised fuel | **RECOMMENDED** | Keeps the existing Nat-fuel induction and all invariant machinery; only swaps the measure and its two uses; simplifies the base case; *also fixes a genuine correctness bug*. All arithmetic validated. |

### Exact measure to add

```lean
/-- Beta-robust termination measure: base-3 exponential of per-branch complexity, summed. -/
private def classicalExpMeasure
    (branches : List (Branch (Proposition Atom) Unit))
    (expandedSets : List (List (SignedFormula (Proposition Atom) Unit))) : Nat :=
  ((branches.zip expandedSets).map
    fun p => 3 ^ classicalBranchComplexity p.1 p.2).sum
```

plus restored `classicalBranchComplexity` (+ `_append`, `_mono_expanded`) from commit `29e9d5b0`.

### Exact decrease lemma(s) to add

```lean
-- NEW: removing an unexpanded sf∈b from the unexpanded set drops its complexity.
private lemma classicalBranchComplexity_drop
    (b : Branch (Proposition Atom) Unit) (e) (sf)
    (hmem : sf ∈ b) (hne : e.any (· == sf) = false) :
    classicalBranchComplexity b (e ++ [sf]) + sf.formula.complexity
      ≤ classicalBranchComplexity b e

-- NEW: rule output total complexity, and applicability ⇒ complexity ≥ 1.
private lemma classicalApplyOne_output_complexity (sf) : … -- Σ complexity(out) = complexity(sf) - 1, applicable ⇒ complexity sf ≥ 1

-- KEY single-step decrease (wires L801):
private lemma classicalExpMeasure_step_lt
    (done restBs newBs) (doneExp restEs newExp) (b e)
    (hstep : classicalStepBranch b e = some (newBs, newExp)) :
    classicalExpMeasure (done ++ newBs ++ restBs)
        (doneExp ++ newBs.map (fun _ => newExp) ++ restEs) + 1
      ≤ classicalExpMeasure (done ++ b :: restBs) (doneExp ++ e :: restEs)
```

### Wiring at L801

Replace the measure hypothesis type of `classicalExpandBranches_hintikka` from
`classicalTotalMeasure … ≤ fuel` to `classicalExpMeasure … ≤ fuel`. At the recursive call
(L801), the current `sorry` discharges as:
`classicalExpMeasure (done++newBs++restBs) (…) ≤ fuel'` from `classicalExpMeasure_step_lt`
combined with the inner-induction `hmeas : classicalExpMeasure (…) ≤ fuel'+1` (the same
`hmeas`/`convert hmeas` plumbing already present for `classicalTotalMeasure` at line ~750 — closed
branches preserve `Φ` identically because `Φ` is additive).

## Validation via lean-lsp (what compiled)

Run through `lean_run_code` (`import Mathlib`), all **sorry-free, no errors**:

1. Beta decrease: `(hC : 1 ≤ C) (h0 : a0 ≤ C-1) (h1 : a1 ≤ C-1) → 3^a0 + 3^a1 + 1 ≤ 3^C`
   — proof: `Nat.pow_le_pow_right`, `3^C = 3^(C-1)*3` via `← pow_succ`/`Nat.sub_add_cancel`,
   `Nat.one_le_pow`, `omega`. COMPILED.
2. Alpha decrease: `3^a0 + 1 ≤ 3^C` (same lemmas). COMPILED.
3. Base-case discharge: `bcs ≠ [] → 1 ≤ (bcs.map (3 ^ ·)).sum`. COMPILED.

Not separately re-proved (reasoned from source, not yet Lean-checked): the rule-output complexity
identity `Σ complexity(out) = complexity(sf) − 1` (mechanical per-connective, follows from
`applyPropRule` + `propAndOf?_and` etc.) and the `classicalBranchComplexity_drop` lemma
(strengthening of the already-proven `_mono_expanded`, same induction). These are R1 below.

No scratch edits were left in any file.

## Adversarial Self-Verification (H4)

Actively tried to refute (b-exp-bound):

- **"Does the `fuel = 0` base case still discharge?"** YES — and more cleanly. `Φ = 0` ⇒ no
  branches ⇒ no `openBranch` (contradiction with `h`); `branches ≠ []` ⇒ `Φ ≥ 1 > 0`
  (contradiction with `Φ ≤ 0`). Validated (test 3). The old zero-subset lemmas are no longer
  needed. CONFIRMED.
- **"Does raising the fuel bound break `classicalTableau_sound`?"** NO — soundness is fuel-generic
  (`classicalExpandBranches_closed_unsat`, no value dependence). CONFIRMED by reading `Soundness.lean:621`.
- **"Does per-branch decrease hold for EVERY rule, incl. closure/no-op?"** Closure/saturation
  (`classicalStepBranch = none`) takes no recursion — measure unused. notApplicable formulas are
  skipped by `findSome?`; when a step fires, the chosen `sf` is a connective ⇒ `complexity(sf) ≥ 1`
  ⇒ `C ≥ 1` precondition holds. Closed branches in `processNext` preserve `Φ` (additive). CONFIRMED
  (modulo the small "applicable ⇒ complexity ≥ 1" lemma, R1).
- **"Do `extendMany` duplicates inflate the child measure?"** NO — `bc` filters the unexpanded set;
  duplicates can only be filtered out, lowering `bc`. The bound `bc out ≤ Σ complexity(out)` holds
  unconditionally. CONFIRMED.
- **"Is base 3 actually enough, or is branching sometimes >2-way?"** `applyPropRule` emits only
  2-element `branching` lists; `linear`/`persistent` are 1 child. Base 3 covers 2-way. CONFIRMED
  from `PropositionalRules.lean`.
- **"Is `3 ^ φ.complexity` fuel computable / acceptable?"** Yes; `classicalTableau` is computable,
  fuel is a decremented Nat counter never materialized as data, and the loop exits early at
  saturation, so the large literal is never iterated to exhaustion. CONFIRMED.

Confidence: HIGH on the measure design, the decrease arithmetic, the base-case discharge, and
soundness-safety (all either Lean-validated or read directly from source). MEDIUM on total
implementation effort, concentrated in R1.

## Residual Risks

- **R1 (medium, effort)**: `classicalExpMeasure_step_lt` requires a 4-way case analysis over
  `classicalApplyOne` (linear/branching/persistent/notApplicable) to establish the rule-output
  complexity identity and combine with the `drop` lemma. This is the bulk of new proof work.
  Mitigation: `classicalStepBranch_hintikka_inv` (Completeness.lean:551) already provides the exact
  destructuring template (`findSome?` → `split_ifs` → `rcases classicalApplyOne …`).
- **R2 (low, ripple)**: the literal `4 * (φ.complexity + 1) + 1` is referenced at completeness call
  sites — `hfuel_init` (~line 1024), the `h'` reconstruction in `classicalOpenBranch_countermodel`
  (~line 1060), and the `classicalExpandBranches_openBranch_initial_mem` call. All must switch to
  `3 ^ φ.complexity`; `hfuel_init` then closes by `le_refl` after `simp`.
- **R3 (low)**: re-scope-build `Soundness.lean` and `DecisionProcedure.lean` after the bound change
  to confirm no incidental literal dependence.
- **R4 (low)**: removing the now-dead `classicalTotalMeasure*` / `classicalRemMeasure*` lemmas must
  not orphan other users — they are `private` and used only in the rewritten lemma.

## Phase Plan for Implementation (each ≤ one bounded agent run)

1. **Phase 1 — Measure infra**: restore `classicalBranchComplexity` (+ `_append`, `_mono_expanded`)
   from commit `29e9d5b0`; add `classicalBranchComplexity_drop` and
   `classicalApplyOne_output_complexity` (incl. applicable ⇒ complexity ≥ 1); define
   `classicalExpMeasure` (+ additivity, + `nonempty ⇒ ≥ 1`). Each lemma sorry-free; scoped build.
2. **Phase 2 — Step decrease**: prove `classicalExpMeasure_step_lt` using Phase 1 lemmas + the
   validated base-3 arithmetic. Scoped build. (Highest-risk phase, R1.)
3. **Phase 3 — Rewire L801**: switch `classicalExpandBranches_hintikka` measure to
   `classicalExpMeasure`; rewrite `fuel = 0` arm as contradiction; discharge the L801 `sorry` via
   Phase 2 lemma threaded through the existing inner-induction `hmeas`. **Re-verify** the
   `fuel = succ` saturation path and Hintikka-propagation are untouched. Scoped build, 0 sorry.
4. **Phase 4 — Raise fuel bound**: set `classicalTableau` fuel to `3 ^ φ.complexity` in
   `Expansion.lean`; update the 3 completeness call sites (R2); reprove `hfuel_init` by `le_refl`.
   Scoped build of `Completeness`, `Soundness`, `DecisionProcedure`.
5. **Phase 5 — CI + zero-debt gate**: `lake build`, `checkInitImports`, `lake lint`,
   `lake exe lint-style`, `lake test`, `lake shake`; `lean_verify` to confirm 0 sorry / no new axioms.

Re-verification of the `fuel = 0` / Hintikka-propagation logic is concentrated in Phase 3.
