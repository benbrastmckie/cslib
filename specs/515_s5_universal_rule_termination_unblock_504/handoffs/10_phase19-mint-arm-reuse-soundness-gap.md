# Handoff 10: Phase 19 -- three more green sub-milestones landed; NEW mint-arm witness-reuse soundness gap discovered

**Task**: 515 (`s5_universal_rule_termination_unblock_504`)
**Plan**: `plans/06_s5-termination-machinery.md` (v5)
**Phase**: 19 (`modalTableauFive_sound`) -- `[BLOCKED]` (re-blocked this dispatch; distinct from the
resolved Route-1 propagation gap v4/v5 already closed)
**Prior state**: Phases 0-18 landed. Phase 19 Route (1) propagation fix + cod-equivalence
soundness core (`accReachableInv_related_five`) landed in the immediately preceding dispatch
(commits `58458c07`, `4ae8eac5`, handoff 09). This dispatch continued the fuel-induction assembly
per handoff 09's continuation order.

## What landed this dispatch (3 green, committed milestones, all still valid and useful)

### Milestone 1 (commit `1a9ec45a`): `FiveSimplification.lean` bridge lemmas

- `modalApplyOneFiveProp_knownWorlds_step`: Five analogue of `modalApplyOneS5_knownWorlds_step`,
  stated directly over `modalApplyOneFiveProp` (the non-reuse propagation rule).
- `modalApplyOneFive_agree_or_reuse`: Five analogue of `modalApplyOneS5w_s5SoundSpec`, stated
  directly (no `RuleApply`/`S5SoundSpec` abstraction, since Five has only the one shipped rule).

### Milestone 2 (commit `da05c424`): `modalStepBranchFive_preserves_accReachableInv`

Direct (non-Gen) specialization of `modalStepBranchS5Gen_preserves_accReachableInv` at
`apply := modalApplyOneFive`. Added the `FiveSimplification.lean` import to `FrameSoundness.lean`
(no cycle). **This lemma is purely structural** (about `acc.hasEdge`-reachability, not about the
model's `m.r`), so it is entirely unaffected by the semantic gap found in Milestone 4 below --
still valid, still needed by the eventual fuel induction.

### Milestone 3 (commit `6f7872b8`): `FiveSoundInv` + `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn`

Five analogues of `S5SoundInv`/`modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn`: frame-relativized
semantic soundness of `modalApplyOneFiveProp`'s two **propagation** shapes under `fiveFC`, given
`accReachableInv`. Root-triggered targets discharge via `hacc` on the
`modalFiveBoxAll_root_hasEdge`/`modalFiveDiaNegAll_root_hasEdge` witness; non-root-triggered targets
discharge via `accReachableInv_related_five`. **These are about the PROPAGATION arms only** (Route 1
already fixed those), so they remain entirely valid.

All three milestones: CI green (full `lake build`, `checkInitImports`, `lake lint`, `lint-style`
all clean on touched files), zero sorries, axioms `[propext, Classical.choice, Quot.sound]` or a
subset, verified via `lake env lean` + `#print axioms` (not `lean_verify` alone).

## The new blocker (Milestone 4, NOT landed -- this is the actual finding)

Continuing to the next item, `modalStepBranchFive_preserves_satIn` (the direct analogue of
`modalStepBranchS5Gen_preserves_satIn`), its **witness-reuse** branch (mirroring S5's "Witness
reuse" case at the top of that theorem) exposed a genuine, independent semantic soundness gap in
the **mint arms** of `modalApplyOneFive` -- `T(◇φ)@w`/`F(□φ)@w`, driven by `witnessWorldS5`.

**In one sentence**: `witnessWorldS5` searches *all* known worlds (root included) for a reuse
witness with *no* restriction tying the found world to the trigger's root/non-root identity or to
any recorded edge, and Route (1) explicitly left the mint arms untouched
(`reports/07_phase19-soundness-blocker-remediation.md`: "Mint-arm fields are untouched") --
because Route (1) was scoped to the **propagation** arms only. The witness-reuse soundness
argument S5 uses (`accReachableInv_related_s5`: any two known worlds are related, because `s5FC`
is an equivalence) has no Five analogue when either the reuse trigger or the found witness is the
root: `accReachableInv_related_five` requires **both** endpoints non-root.

Full diagnosis, including a concrete adversarial two-island `RightEuclidean` model realizing the
failure, and why a naive rule-level guard (mirroring Route 1) is **not** a bounded patch (it
threatens the already-landed termination bound, which needs "at most one mint per
`(sign, subformula)` tag" -- a guard that sometimes rejects reuse for an already-minted tag would
let that tag mint a second time), is recorded in the plan file
`plans/06_s5-termination-machinery.md`, Phase 19's task list, under "**NEW BLOCKER (this dispatch,
distinct from the resolved Route-1 propagation gap above)**".

## Why this is NOT a proof-search problem

This was derived, not merely asserted: the two sub-cases (root-as-trigger, root-as-witness) were
each traced to a concrete adversarial-model shape where the needed relatedness fact is genuinely
false, mirroring the rigor of the already-resolved `Fin 3` counterexample that motivated Route (1)
itself. No amount of additional tactic effort on the current rule/lemma set closes this; it needs
either (a) a Route-1b rule-level fix to the mint arms with the termination bound re-derived
alongside it, or (b) a genuinely new "Euclidean-closure preserves already-satisfied formulas"
argument (related to, but not yet present as, the completeness-side `Relation.EuclGen` machinery
Phase 20 will build).

## Recommendation for the next dispatch

**Do not attempt to write `modalStepBranchFive_preserves_satIn` until a Route-1b remediation
decision exists.** Dispatch a `/research` cycle (or `/plan` revision) specifically for the
mint-arm witness-reuse gap:

1. Decide between (a) restricting `witnessWorldS5`'s search (root-trigger `hasEdge` guard,
   symmetric to Route 1's propagation guard, PLUS excluding `0` from witness candidacy) with a
   from-scratch re-derivation of the tag-injection termination bound under the new, more
   restrictive reuse condition, or (b) a semantic/model-repair argument (Euclidean-closure of
   `m.r` at the one new pair, plus a "closure preserves satisfaction" lemma).
2. Whichever route is chosen, the diagnosis in the plan file should be preserved verbatim (as the
   v4 Route-1 diagnosis was preserved for this dispatch), and the three milestones landed this
   dispatch (all still valid) should be consumed, not re-derived.
3. `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn`/`FiveSoundInv`/
   `modalStepBranchFive_preserves_accReachableInv`/`modalApplyOneFiveProp_knownWorlds_step`/
   `modalApplyOneFive_agree_or_reuse` are all reusable inputs to whatever the Route-1b fix produces.

## Files touched this dispatch

- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (2 new bridge lemmas)
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (import + 3 new lemmas/defs)
- `specs/515_s5_universal_rule_termination_unblock_504/plans/06_s5-termination-machinery.md`
  (Phase 19 re-marked `[BLOCKED]`, new blocker documented)

## Verification state

- `lake build` (full project): green, no new sorries/errors beyond documented baselines.
- `lake exe checkInitImports`: clean.
- `lake lint` / `lake exe lint-style`: clean for both touched files.
- Axiom checks via `lake env lean <scratch>.lean` + `#print axioms`: all new declarations depend
  on at most `[propext, Classical.choice, Quot.sound]`. No `sorryAx` anywhere.
