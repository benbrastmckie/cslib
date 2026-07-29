# Phase 4A Summary: `intFuelExt` + Per-Branch-Fuel B-Engine + Init Bound

- **Task**: 317
- **Plan**: plans/14_fuel-materialization-repair.md (v14, binding)
- **Phase**: 4A (parallel build; no consumer flipped)
- **Session**: sess_1785275816_a84520_317
- **Status**: [COMPLETED]
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD

## What Was Proven / Built

All new declarations land in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` as pure insertions —
zero edits to existing declarations.

1. **`intFuelExt`** (after `WBound_pos`): the materializable per-branch fuel budget in
   the mandated closed arithmetic form
   `4 * (2 * φ.complexity + 1) * (WBound φ + 1) + 1`. The docstring records the
   prohibition on any `(intUniverseExt φ).length`-based definition (postmortem
   constraint 11: the list has Θ(WBound) elements and is unmaterializable), the
   domination of `2 * |intUniverseExt φ| + 1` via `intUniverseExt_length_le`, and the
   `s ≲ 22` corpus-row feasibility envelope (~0.5 GB numeral at `s ≈ 25`).

2. **`intExpandBranchesB` + `intExpandBranchesB.go`**: the per-branch-fuel B-engine.
   Same worklist shape and parallel lists as `intExpandBranches` (Expansion.lean), with
   the global `fuel : Nat` replaced by `fuels : List Nat` as a fourth parallel list.
   `go` is lifted to a top-level def (so WF elaboration and functional induction are
   available). Arm discipline exactly per spec: persistence receives the active
   branch's remaining fuel; skip-closed unchanged in content (branch moves to `done`
   with its fuel); open active branch at `f = 0` returns `.openBranch bPers`
   (exhaustion arm — closed branches are still skipped first, preserving the
   `openBranch → open` invariant needed by the 4B `openBranch_closed` port);
   linear/world-creating/reuse arms step `f + 1 → f`; beta children each inherit `f`.
   `termination_by` the lex measure `(Σ 3^fuelᵢ over pending ++ done, pending.length)`;
   `decreasing_by` UNCONDITIONAL (no invariant premises anywhere in the definition):
   skip-closed permutes the fuel multiset and shrinks pending; single-successor arms
   use `3^f < 3^(f+1)`; the beta arm uses `2·3^f < 3^(f+1)`.

3. **Supporting lemmas** (new, needed to make the beta-arm decrease sound as a
   proof-time fact — the report's "all three branchingResult sites emit literal
   2-element lists"):
   - `intApplyRuleFull_branchingResult_length`: every `branchingResult` has exactly 2
     children (case analysis over the rule table).
   - `intStepBranch_branchingResult_length`: the `intStepBranch` lift, consumed by
     `decreasing_by` via a `match _hstep : intStepBranch …` discriminant equation.
   - `sum_map_pow_const`, `lex_lt_of_le_of_lt` (private): termination bookkeeping.

4. **`intWork_init_lt_intFuelExt`**: the init bound
   `intWork (intUniverseExt φ) [⟨.neg, φ, 0⟩] [] < intFuelExt φ` — Phase 6's call-site
   `hFuel` discharge, replacing plan-13's `intExpMeasureExt_init_le_fuel`. Proof shape
   exactly as specified: the countP bookkeeping of `intExpMeasure_init_le_fuel` +
   `intUniverseExt_length_le`, closing by `omega` (one `ring` step for the
   `2·(2·…) = 4·…` regrouping, mirroring the old lemma) — no pow manipulation.

## Verification

- Scoped build green; full `lake build` green (3311 jobs).
- `lake exe checkInitImports` exit 0; `lake exe lint-style` exit 0; `lake test` exit 0
  (conformance corpus untouched, zero row edits).
- `lake lint` run at phase end (see handoff JSON for result).
- `lean_verify` on `intFuelExt`, `intExpandBranchesB`, `intExpandBranchesB.go`,
  `intWork_init_lt_intFuelExt`, `intStepBranch_branchingResult_length`: axioms ⊆
  `{propext, Classical.choice, Quot.sound}`, **no `sorryAx`**.
- **Parity probe** (temporary, NOT committed; run from scratchpad via
  `lake env lean`): `intVerdictB = intVerdict` on all 20 propositional corpus rows —
  **all 20 match** (14 CLOSED, 6 OPEN including the divergence-witness row);
  aggregate check `true`. B-side ran `intExpandBranchesB` with
  `fuels := [intFuelExt φ]`; probe wall time ~67 s total including the
  ~13.0-million-digit row-20 numeral materialization + bignum stepping.
- **`lake test` timing baseline recorded** (pre-change, HEAD bb597c9d):
  real 0m7.231s (user 0m8.888s, sys 0m3.998s) — the 4C timing-gate reference
  (progress/phase-4A-progress.json).
- **Bare-sorry census: exactly 4 in the subtree, unchanged** — Scheme.lean:619
  (truthLemma T-imp), Scheme.lean:3361 (fuel-0, drifted from :3055 by this phase's
  insertions), Intuitionistic/Completeness.lean:133, Minimal/Completeness.lean:125.

## Plan Deviations

- **None of substance.** Two new public supporting lemmas
  (`intApplyRuleFull_branchingResult_length`, `intStepBranch_branchingResult_length`)
  and two private helpers were added beyond the three named artifacts; the plan grants
  naming/structure latitude ("the constraint set is binding, the naming is implementer
  latitude") and the beta-arm termination step the report specifies is unprovable
  without the 2-element fact as a lemma. No existing declaration was touched.
- The parity probe was kept out of the repository entirely (scratchpad file), taking
  the plan's "not committed" option; nothing to remove at 4C.
- Note for 4B/4C: the fuel-0 sorry the plan cites as Scheme.lean:3055 now sits at
  Scheme.lean:3361 (line drift from this phase's insertions; same declaration).

## Commits

- `33416bc8` task 317 phase 4A.1: intFuelExt + per-branch-fuel B-engine + init bound
- (phase-end commit: plan checkboxes, progress, summary, handoff)
