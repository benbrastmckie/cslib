# Implementation Plan: Task #427 — `temporalTruthLemma_propositional` (atom/bot/imp)

- **Task**: 427 - Prove `temporalTruthLemma_propositional` (atom/bot/imp cases) sorry-free
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: None (independent of tasks 423/425; no FMP, no `ordConstraints` fix)
- **Research Inputs**: specs/427_temporal_tableau_propositional_truth_lemma/reports/01_propositional-truth-lemma.md
- **Artifacts**: plans/01_propositional-truth-lemma.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Introduce and prove `temporalTruthLemma_propositional` sorry-free in
`Cslib/Logics/Temporal/Tableau/Completeness.lean`, restricted to the propositional fragment
(atom / bot / imp) of the temporal tableau. The target is currently a commented-out BLOCKED
stub (lines 269–282) and must be added as a real declaration. The single decisive constraint,
established by research, is that the temporal `Formula` type is **Łukasiewicz-encoded**:
`and`/`or`/`neg` are `abbrev`s expanding into nested `imp`/`bot`, and the tableau's propositional
rule dispatch (`tryAllPropRules`) recognises those shapes and fires `andPos`/`orPos`/`negPos`
**before** `impPos`, emitting `T`/`F` for **deep** sub-formulas. Consequently neither structural
`induction φ` nor `induction (hprop : IsPropositional φ)` supplies the needed induction
hypotheses (both give IHs only for the *immediate* sub-formulas). The fix is **strong induction on
`Formula.complexity`**, encoded robustly as a fuel-bounded `_aux` lemma proved by plain `Nat.rec`
(`induction n`), with the public lemma instantiating `n := φ.complexity`.

Definition of done: the file builds with the new public lemma present, `lake build` and
`lake test` are green, and `grep -n "sorry\|admit\|axiom" ` over the new declarations returns
nothing. The CI gate (`lake exe lint-style`, etc.) must also pass.

### Research Integration

This plan integrates `reports/01_propositional-truth-lemma.md` in full:
- Root cause (Łukasiewicz encoding → deep sub-formulas) → mandates strong induction on
  `complexity` (Phase 3 driver).
- Rule-firing decision table (§4a) → the per-rule case skeleton of Phase 3.
- Reusable base cases (`extractModel_atomPos_sat`, `extractModel_atom_neg_notSat`,
  `extractModel_bot_false`, `openBranch_noBotPos`) verified to exist at
  `Completeness.lean` lines 117 / 191 / 125 / 133 → reused as-is, not re-proved.
- The four `any ↔ ∈` bridge lemmas and `IsPropositional` are ported verbatim from the WIP
  (`specs/301_temporal_tableau/.wip-Completeness-truthlemma-attempt.lean` lines 230–276).
- The WIP's nested-`induction hprop` skeleton is explicitly **avoided** (its diagnosed trap);
  only its base cases and bridge lemmas are reused.
- Required `Satisfies` lemmas (`imp_iff`, `bot_false`, `atom_iff`, `neg_iff`) verified to exist
  at `Satisfies.lean` lines 85 / 73 / 79 / 112; the `tempXOf?` `@[simp]` lemmas already exist.

### Prior Plan Reference

No prior plan. A 1150-line WIP proof attempt exists (`specs/301_temporal_tableau/.wip-...lean`);
it is a reference asset (reuse base cases + bridge lemmas), not a template — its
nested-induction strategy is the trap this plan structurally eliminates.

### Roadmap Alignment

No `roadmap_flag` set for this dispatch; ROADMAP.md not consulted as a gating input. This task is
a decomposed sub-obligation of task 301 (temporal tableau completeness), blocker B.

## Goals & Non-Goals

**Goals**:
- Add `IsPropositional` predicate (closed under atom/bot/imp) and a one-line
  `Formula.one_le_complexity`.
- Port the four `any ↔ ∈` bridge lemmas from the WIP.
- Prove the fuel-bounded `temporalTruthLemma_propositional_aux` sorry-free by `induction n`,
  with both T- and F-directions for atom/bot/imp, drawing all IHs from the single coherent `ih`.
- Add the public `temporalTruthLemma_propositional` as a one-line instantiation.
- Keep `lake build` and `lake test` green; new declarations sorry-free and axiom-free.

**Non-Goals**:
- The `untl`/`snce` (temporal/eventuality) cases — out of scope, FMP-blocked (tasks 423/425).
  `IsPropositional` has no such constructors, so `cases hp` never generates those branches.
- Any change to FMP, `ordConstraints`, `extractModel`, the tableau rules, or the `Satisfies`
  semantics. No new Mathlib dependency and no new axiom.
- Touching any file other than `Cslib/Logics/Temporal/Tableau/Completeness.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `complexity` arithmetic per leaf does not close with `omega` (special untl/snce `imp` cases at `Formula.lean` lines 208–216 precede the generic `imp` at 218) | M | M | For purely propositional φ the special cases never match; `simp only [Formula.complexity]` at the matched shape exposes the generic-imp equation, then `omega`. Verify each leaf via `lean_goal`/`lean_multi_attempt` before committing. This is the single most likely friction point (research §risk 1). |
| Extracting `IsPropositional a`/`IsPropositional b` for deep `and`/`or` parts needs the right inversion depth | M | M | Use shallow `cases hφ'`/`cases hψ'` *inversions* (not inductions), 1–2 levels only, mirroring the §4a shapes. Keep them bounded. |
| `hrule` let-binding (`temporalHintikkaSet` second component uses `let (result, _) := temporalApplyOne ...`) obscures the rule result | M | M | Replicate the WIP's `simp only [temporalApplyOne] at hout` (WIP line 324) to expose the `tryAllPropRules` result before reading the shape. |
| Rule-result simp set drift (fails to reduce `tryAllPropRules` at a leaf) | M | L | Use the exact simp set the WIP uses at every leaf: `simp only [tryAllPropRules, applyPropRule, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?, RuleResult.isApplicable, List.map, List.find?]` (WIP line 333). |
| Phase 3 (the imp case, both directions) exceeds one agent run | H | M | Phase 3 is scoped to the T-direction primary path with the F-direction leaves ported from WIP lines 721–1000; if interrupted, mark phase [PARTIAL] with the remaining rule leaves enumerated and resume. Per-rule structure is independent, enabling incremental green commits at each closed direction. |
| Lint failures on new decls (docBlame: missing docstrings) | L | M | Add docstrings to `IsPropositional`, `one_le_complexity`, the public lemma; keep decls inside `namespace Cslib.Logic.Temporal.Tableau`; run `lake exe lint-style` in Phase 4. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase
adds declarations the next depends on, and each ends at a green build.

### Phase 1: Add `IsPropositional` + `Formula.one_le_complexity` helpers [NOT STARTED]

**Goal**: Introduce the propositional-fragment predicate and the complexity lower bound that the
strong-induction base case (`n = 0` vacuity) requires, with a green build.

**Tasks**:
- [ ] In `Completeness.lean`, inside `namespace Cslib.Logic.Temporal.Tableau`, add the
  `IsPropositional` inductive (atom/bot/imp constructors) ported from WIP lines 230–237, with a
  docstring. Since `and`/`or`/`neg` are `imp`/`bot` encodings, this predicate covers the whole
  classical propositional fragment automatically.
- [ ] Add `Formula.one_le_complexity (φ : Formula Atom) : 1 ≤ φ.complexity` (one line: `cases φ`
  / `simp [Formula.complexity]` / `omega`, or `Nat.rec`-free `cases` over the match). Place it
  with the `Formula.complexity` API (it may live in `Completeness.lean` next to its use, or be a
  local `private` lemma) with a docstring. Confirm via `lean_goal` that the `omega` closes for
  every constructor branch including the untl/snce special cases at `Formula.lean` lines 208–224.
- [ ] Verify no other declaration is disturbed; the commented stub at lines 269–282 stays
  commented for now.

**Timing**: ~45 min

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `IsPropositional`, `one_le_complexity`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` succeeds.
- `lake build` green overall.
- `grep -n "sorry\|admit" ` over the two new decls returns nothing.

### Phase 2: Port the four `any ↔ ∈` bridge lemmas [NOT STARTED]

**Goal**: Bring the trivial `any ↔ ∈` membership bridges into `Completeness.lean` so the `_aux`
proof can move between `b.any (...)` Booleans and `∈ b` membership facts.

**Tasks**:
- [ ] Port `any_pos_mem`, `any_neg_mem`, `mem_to_any_pos`, `mem_to_any_neg` from the WIP
  (lines 242–276) as `private` lemmas, with docstrings. These are `List.any_eq_true` /
  `List.mem_cons` plumbing — no new mathematics.
- [ ] Confirm signatures match the calling convention used in research §4b/§4c
  (`any_pos_mem b t φ hmem : ⟨.pos, φ, t⟩ ∈ b`, and duals).
- [ ] Keep them adjacent to the existing base-case lemmas (after line ~191) for locality.

**Timing**: ~30 min

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add four bridge lemmas.

**Verification**:
- `lake build` green.
- Each bridge lemma is sorry-free (`grep`); spot-check one direction with `lean_goal` if needed.

### Phase 3: Fuel-bounded `_aux` lemma with per-rule case skeleton [NOT STARTED]

**Goal**: Prove `temporalTruthLemma_propositional_aux` sorry-free by `induction n` (fuel), with
atom/bot/imp handled in both T- and F-directions, drawing all sub-formula IHs from the single
coherent strong IH. This is the only nontrivial phase.

**Tasks**:
- [ ] Declare the `private lemma temporalTruthLemma_propositional_aux` with the strengthened
  signature from research §4b: parameters `b ord tracker`, `hopen : isTemporalClosed ... = false`,
  `hrule : ∀ sf ∈ b, ...` (the second component of `temporalHintikkaSet`), `n : Nat`, and the
  `∀ φ, φ.complexity ≤ n → IsPropositional φ → ∀ t, (T-dir) ∧ (F-dir)` conclusion.
- [ ] `induction n with`
  - `| zero =>` intro `φ hle hp t`; close by `absurd hle` using `Formula.one_le_complexity φ`
    + `omega` (complexity ≥ 1 contradicts `≤ 0`).
  - `| succ n ih =>` intro `φ hle hp t`; `cases hp with` (inversion on `IsPropositional`, NOT
    induction — yields only atom/bot/imp branches).
- [ ] **atom case**: `refine ⟨fun hmem => ?_, fun hmem => ?_⟩`; T-dir via
  `extractModel_atomPos_sat b t p (any_pos_mem ...)`; F-dir via
  `extractModel_atom_neg_notSat b ord tracker hopen t p (any_neg_mem ...)`.
- [ ] **bot case**: T-dir via `absurd ⟨t, any_pos_mem b t .bot hmem⟩ (openBranch_noBotPos ...)`;
  F-dir via `extractModel_bot_false b t`.
- [ ] **imp case** (`φ = .imp φ' ψ'`, hyps `hφ' hψ' : IsPropositional ...`): determine the fired
  rule by a **bounded** `cases ψ'` then `cases φ'` shape split (NOT induction), mirroring the §4a
  decision table. Reduce `tryAllPropRules ... = .linear/.branching [...]` at each leaf with the
  WIP simp set (`simp only [tryAllPropRules, applyPropRule, tempAndOf?, tempOrOf?, tempImpOf?,
  tempNegOf?, RuleResult.isApplicable, List.map, List.find?]`). Expose `hrule` output with
  `simp only [temporalApplyOne] at hout`. Pull branch outputs with `mem_to_any_pos`/
  `mem_to_any_neg`. Apply `ih χ (by omega) χ_prop t` to each output sub-formula `χ` (one of
  `φ'`, `ψ'`, `a`, `b` — all strict sub-formulas, complexity `≤ n` by `Formula.complexity`
  arithmetic + `hle`), obtaining `IsPropositional χ` by shallow `cases hφ'`/`cases hψ'`
  inversion. Close with `simp only [Satisfies.imp_iff, Satisfies.bot_false]` (and `Satisfies.neg_iff`
  for negPos/negNeg convenience). Per-rule logic (research §4c):
  - `andPos` (`and a b`, linear `T(a),T(b)`): goal unfolds to `Satisfies a ∧ Satisfies b`; supply
    `(ih a ...).1` and `(ih b ...).1`.
  - `orPos` (`or a ψ'`, branch `T(a) | T(ψ')`): `rcases` the branch hyp, feed matching IH `.1`.
  - `impPos` (proper, branch `F(φ') | T(ψ')`): `(ih φ' ...).2` resp. `(ih ψ' ...).1`;
    `rw [Satisfies.imp_iff]`.
  - `negPos` (`neg φ'`, linear `F(φ')`): `rw [Satisfies.imp_iff]; intro; exact absurd ... ((ih φ' ...).2 ...)`.
  - F-direction duals `andNeg`/`orNeg`/`impNeg`/`negNeg`: port the leaf logic from WIP lines
    721–1000 verbatim, but draw IHs from the single `ih` (not nested-induction IHs).
- [ ] After each closed rule leaf, run `lean_goal` to confirm "no goals"; commit incrementally at
  each green milestone (per-direction or per-rule) so an interruption leaves a recoverable state.

**Timing**: ~2 hours (the bulk of the task)

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add `temporalTruthLemma_propositional_aux`.

**Verification**:
- `lake build` green with the `_aux` lemma present and **no `sorry`** in its body.
- `grep -n "sorry\|admit" ` over the `_aux` body returns nothing.
- Optional: `lean_verify Cslib.Logic.Temporal.Tableau.temporalTruthLemma_propositional_aux`
  shows no unexpected axioms.

### Phase 4: Public lemma instantiation + sorry-free green build [NOT STARTED]

**Goal**: Add the public `temporalTruthLemma_propositional` as a one-line instantiation of `_aux`,
remove/replace the commented BLOCKED stub, and confirm a fully green, sorry-free, lint-clean build.

**Tasks**:
- [ ] Add the public `lemma temporalTruthLemma_propositional` (signature from research §4b:
  takes `hH : temporalHintikkaSet b ord tracker`, `φ`, `hprop : IsPropositional φ`, `t`) with a
  docstring. Body: `obtain ⟨hopen, hrule⟩ := hH; exact temporalTruthLemma_propositional_aux b ord
  tracker hopen hrule φ.complexity φ le_rfl hprop t`.
- [ ] Delete the now-obsolete commented stub block (lines ~269–282) so the file has a single
  authoritative declaration; update the file header doc (lines ~47–51) note if it references the
  stub as BLOCKED.
- [ ] Run the full CI gate.

**Timing**: ~45 min

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — add public lemma, remove commented stub,
  touch header doc note.

**Verification**:
- `lake build` green.
- `lake test` green (CslibTests suite).
- `lake exe checkInitImports` passes.
- `lake exe lint-style` passes.
- `grep -nE "sorry|admit" Cslib/Logics/Temporal/Tableau/Completeness.lean` returns nothing.
- `lean_verify Cslib.Logic.Temporal.Tableau.temporalTruthLemma_propositional` reports no new axiom.

## Testing & Validation

- [ ] `lake build` succeeds with all five new declarations present.
- [ ] `lake test` green.
- [ ] `lake exe checkInitImports` and `lake exe lint-style` pass.
- [ ] No `sorry`/`admit`/new `axiom` anywhere in the new declarations (acceptance criterion).
- [ ] `temporalTruthLemma_propositional` is the only authoritative declaration (commented stub
  removed).
- [ ] Scope confined to `Cslib/Logics/Temporal/Tableau/Completeness.lean` — `git diff --stat`
  shows exactly one file changed.

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — `IsPropositional`,
  `Formula.one_le_complexity`, four `any ↔ ∈` bridge lemmas,
  `temporalTruthLemma_propositional_aux` (private), `temporalTruthLemma_propositional` (public),
  all sorry-free; commented stub removed.
- `specs/427_temporal_tableau_propositional_truth_lemma/summaries/01_propositional-truth-lemma-summary.md`
  — execution summary (written by /implement).

## Rollback/Contingency

- All work is additive to a single file from green commit `7f052834`. If a phase fails to close,
  `git checkout -- Cslib/Logics/Temporal/Tableau/Completeness.lean` restores the green baseline.
- If Phase 3 stalls on a specific rule leaf (most likely `andPos`/`andNeg` deep-IH arithmetic),
  mark Phase 3 [PARTIAL] with the failing leaf and its `lean_goal` state recorded, keep the
  closed leaves committed, and resume — do NOT fall back to nested induction (the WIP trap).
- The `untl`/`snce` cases remain out of scope; do not introduce `sorry` placeholders for them —
  `IsPropositional` structurally excludes them, so no placeholder is needed.
