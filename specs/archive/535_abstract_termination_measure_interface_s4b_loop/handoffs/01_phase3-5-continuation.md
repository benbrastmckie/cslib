# Continuation Handoff: Phases 3-5 (Keyed S4 Driver)

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma
- **Plan**: `specs/535_abstract_termination_measure_interface_s4b_loop/plans/01_keyed-s4-driver-plan.md`
- **Status at handoff**: Phases 1-2 COMPLETED and committed (lake-build-green, zero sorry,
  `lean_verify` axiom-clean). Phases 3-5 BLOCKED — see the plan file's per-phase blocker notes
  for the short version; this document is the full technical map for a follow-on dispatch.
- **Recommended mode for the follow-on dispatch**: `--hard` (H8 phase-sizing), given the scale
  below is far larger than a single-phase dispatch comfortably absorbs.

## What Landed (Phases 1-2, do not re-derive)

In `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (end of file, after
`modalStepBranchS4_preserves_S4LoopInv`):

- `modalExpandBranchesS4Keyed` / `modalTableauS4Keyed`: the bespoke `keys`-threaded fuel driver,
  structurally mirroring `modalExpandBranchesGen`/`processNext`/`modalTableauGen`
  (`Saturation.lean`), with a fourth `keyss` worklist column carrying each branch's own `keys`
  list, stepped by the already-landed `modalStepBranchS4Keyed`. Entry fuel is currently
  `modalFuel φ` (K's fuel) — **this will very likely need to change** (see Root Cause 3 below).
- `hintikka_congr_S4`: `modalHintikkaSetGen (modalApplyOneS4Keyed φ₀ keys) b acc ↔
  modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc`, proved **unconditionally** (no saturation
  hypothesis needed) for any `keys`. This resolved much easier than the research survey feared:
  `modalHintikkaSetGen`'s conjunct 2 returns literal `True` at exactly the two shapes where the
  keyed/live rules can differ, and at every other shape `modalApplyOneS4Keyed` falls through to
  `modalApplyOneS4` by the definitional `| _, _ =>` catch-all (`rfl`). Use this freely in Phase 3
  to bridge the final keyed-rule Hintikka conclusion to the concrete `modalHintikkaSetS4` form via
  `modalHintikkaSetS4_eq`.

Both are committed (see commit "task 535 phase 1-2: keyed S4 driver definitions +
hintikka_congr_S4 crux").

## The Core Structural Obstacle (affects Phases 3, 4, 5 alike)

Every landed "top-loop" lemma this plan's Phases 3-5 were modeled on
(`modalExpandBranchesHintikka` in `CompletenessLoop.lean`, `modalExpandBranchesGen_closed_unsatIn`
in `FrameSoundness.lean`) is hard-wired to a **single fixed** `apply : RuleApply Atom`, used
identically at every step of its fuel induction. The keyed S4 rule
`modalApplyOneS4Keyed φ₀ keys` is NOT fixed across a run — `keys` grows monotonically at every
step (`modalStepBranchS4Keyed`'s own `keys'` output). So none of the landed generic top-loop
machinery can be *instantiated* for the keyed driver; a bespoke, keys-threaded analogue of each
must be built. This is why Phases 3-5 are much larger than "wire together landed pieces" — they
require original (though structurally well-precedented) proof engineering.

## Phase 3: Termination / Hintikka Top-Loop

**Target**: `modalExpandBranchesS4Keyed_hintikka` — an open branch produced by the keyed driver
is a Hintikka set for the keyed rule (then bridge to the concrete `modalHintikkaSetS4` form via
`hintikka_congr_S4` + `modalHintikkaSetS4_eq`).

### 3a. Re-derive the generic combinatorial primitives (mechanical, low risk)

`FmpMeasure.lean`'s `modalWork`/`modalExpMeasure` (public defs — reusable as-is) need a
strict-decrease-per-step engine, but its combinatorial core is `private` to that file:
- `modalCount_notMem_append_drop` (`FmpMeasure.lean:2788-2859`, ~70 lines): generic over any
  `BEq`/`LawfulBEq` type, no `apply`/`φ0` dependence. Copy verbatim (rename to avoid clash, e.g.
  `modalCount_notMem_append_drop_S4` or reuse the exact name in a `private` S4-local copy since
  it is not exported anyway).
- `modalCount_notMem_mono` (`:2865-2878`, ~15 lines): same, generic.
- `modalWork_drop_linear` (`:2887-2895`, ~10 lines) and `modalWork_drop_persistent`
  (`:2904-2922`, ~20 lines): build on the two above; generic over any `U`/`b`/`b'`/`e`.

None of these four require deep insight — they are pure list-counting facts. Re-derive them as
`private` lemmas in `LoopChecking.lean` (territory-legal; `FmpMeasure.lean` is out of scope per
this task's additive-only territory constraint).

### 3b. Per-call obligations for `modalApplyOneS4Keyed φ₀ keys`, ∀ `keys`

`modalExpMeasure_step_lt_gen`'s three raw hypotheses
(`hBranchingLength`/`hPersistentFresh`/`hOutputsSubsetUniverse`, `FmpMeasure.lean:3227-3246`) need
S4Keyed analogues, each **universally quantified over `keys`** so a single lemma serves every
step (mirroring how `hintikka_congr_S4` is `∀ keys`). Case-split exactly as
`modalStepBranchS4_preserves_bClosure` already does (`LoopChecking.lean`, search
`modalStepBranchS4_preserves_bClosure` for the template):
- **Mint-unblocked** (reduces to raw `modalApplyOne`): reuse `modalApplyOne_persistent_props`/
  `modalApplyOne_branching_length` (`FmpMeasure.lean:3062,3125`) directly — these already exist
  for K and apply verbatim once the rewrite to `modalApplyOne` is made
  (`modalApplyOneS4Keyed_boxNeg_unblocked_eq`/`_diaPos_unblocked_eq`, already landed at
  `LoopChecking.lean:727,749`).
- **Mint-blocked** (`.linear []`): trivially satisfies all three vacuously (empty output, not
  `.persistent`/`.branching`).
- **Non-mint** (reduces to `modalApplyOneS4Rules`/`modalApplyOneT`): the already-landed
  `modalApplyOneS4Keyed_nonMint_universe_S4` (`LoopChecking.lean:2456`, `private` but
  same-file-accessible since Phase 3 content also lives in `LoopChecking.lean`) supplies the
  outputs-subset-universe half directly; `persistentFresh`/`branchingLength` for this case likely
  need small new lemmas mirroring the T/S4Rules dispatch already used in
  `modalStepBranchS4_preserves_bClosure`'s non-mint branch.

### 3c. Fuel value — CONFIRMED not free (do not skip this step)

Direct arithmetic check (not conjecture): at `modalComplexity φ₀ = 0`,
`modalWorldBoundS4 φ₀ = 2^(2·|Sf|) ≤ 2^2 = 4` (since `|Sf| ≤ 2·0+1 = 1`), while K's own
`modalWorldBound φ₀ = (2·0+1)^(0+1) = 1`. **S4's pigeonhole bound exceeds K's at small
complexity**, so `modalFuel φ₀` (Phase 1's current fuel choice, K's closed form, independent of
`modalWorldBoundS4`) is not provably sufficient in general — confirms the research survey's Open
Question 3. Define `modalFuelS4 φ₀` directly from `modalUniverseS4 φ₀`'s length (mirror
`modalExpMeasure_entry_le_fuel`'s proof shape, `FmpMeasure.lean:208-247`: show the entry
configuration's measure is `≤ 3 ^ (2 · (modalUniverseS4 φ₀).length)` via `modalWork`'s
`|U\b| + |U\e|` shape, then set `modalFuelS4 φ₀ := 3 ^ (2 * (modalUniverseS4 φ₀).length + 1)` or
similar and prove the inequality directly — no need for the K-fuel comparison at all). Update
`modalTableauS4Keyed`'s fuel argument (Phase 1 def, small edit) to use `modalFuelS4 φ₀`.

### 3d. Keys-threaded Hintikka-tracking invariant bundle

Needs a bespoke analogue of `ModalLoopInvHintikka`/`AuxStepPreserved`
(`CompletenessLoop.lean:262-337`), threading `keys` through an extra argument. Encouraging
finding: `modalHintikkaClauseGen` (`Completeness.lean:652`) carves out **all** box/diamond shapes
(both signs) as vacuous `True` — coarser than `modalHintikkaSetGen`'s conjunct 2, which only
carves out 2 of 4. This means the real tracking burden is:
- **Propositional shapes** (atom/bot/imp/and/or): branch/`acc`-independent
  (`modalApplyOne_fst_eq_of_not_box`-style fact), so once discharged, trivially monotone as the
  branch only grows.
- **Box-positive/diamond-negative persistent shapes** (T's 4-rule propagation): need an
  `eBoxOnlyNeg`/`eDiamondOnlyPos`-style fact that these never enter `e` (persistent rules never
  get added to the expanded set by design — same argument as K/S5/B, should transcribe directly
  since `modalApplyOneS4Keyed`/`modalApplyOneS4` both fall through non-mint shapes to
  `modalApplyOneS4Rules`/`modalApplyOneT`, same persistent-rule design).
- **Box-negative/diamond-positive mint shapes**: carved out entirely by
  `modalHintikkaClauseGen`, so `hintikkaInv` is trivially satisfied there regardless of `e`
  membership; still need `eBoxNegWitness`/`eDiamondPosWitness`-style witness-existence facts,
  which are permanent once recorded (`acc`/`b` only ever grow — same monotonicity argument as
  K/S5/B's landed fields).

### 3e. Assemble the top-loop induction

Mirror `modalExpandBranchesHintikka`'s ~250-line structure (`CompletenessLoop.lean:1430-1650+`),
substituting the keys-threaded stepper/invariant/measure from 3a-3d. On reaching the `none`
(saturated) case, use an S4Keyed-specific `_none_saturated` lemma (small, ~25-line analogue of
`modalStepBranchGen_none_saturated`, `Completeness.lean:809`) plus the same per-shape dispatch
pattern as `modalExpandBranchesHintikka`'s own proof (`CompletenessLoop.lean:1538-1618`) to derive
each Hintikka conjunct. Close with `hintikka_congr_S4` + `modalHintikkaSetS4_eq` to reach the
concrete `modalHintikkaSetS4 φ₀ b acc` target.

## Phase 4: Soundness — `modalTableauS4Keyed_sound`

Two independent gaps, not merely assembly:

1. **No S4 minting-shape soundness lemma exists anywhere** (confirmed via `grep` — the research
   survey's finding holds). The landed `branchSatisfiableIn_s4FC_boxPos_trans_mem`/
   `_diaNeg_trans_mem` (`FrameSoundness.lean:1085,1106`) cover only the *persistent* 4-rule
   propagation arms, not the guarded minting shapes. A new semantic lemma is needed: redirecting
   a blocked mint to an existing `wBlock` (instead of minting fresh) preserves
   `branchSatisfiableIn s4FC` — built from `S4LoopInv.keyLowerBd`/`keysDistinct` (the birth key is
   a *lower bound* on the live relevant set, not an equality, since relevant sets grow after
   birth) and the reflexive-transitive frame condition.
2. **Same fixed-`apply` obstacle as Phase 3** for the top-loop wrapper
   (`modalExpandBranchesGen_closed_unsatIn`, `FrameSoundness.lean:731`) — needs a bespoke
   keys-threaded soundness induction, sharing much of Phase 3's measure/invariant machinery.

Recommend building Phase 4 *after* Phase 3's shared infrastructure (3a-3c) lands, since the
soundness induction needs the same fuel-sufficiency argument.

## Phase 5: Completeness + Decidability

Blocked transitively on Phases 3-4. Once those land, `modalTableauS4Keyed_complete` should follow
the `modalTableauS5_complete` template (`FrameCompleteness.lean:2336`) fairly directly — the
truth-lemma/countermodel/`modalHintikkaSetS4_eq` bridges are all already landed and
apply-agnostic; only Phase 3's Hintikka witness and Phase 4's soundness are the new inputs.
`s4Valid_decides`/`instDecidableS4Valid` are then a mechanical two-constructor dichotomy, mirroring
`s5Valid_decides`/`instDecidableS5Valid` (`FrameCompleteness.lean:2407-2421`).

## Suggested Phase Decomposition for the Follow-On Dispatch

| Sub-phase | Content | Rough size |
|---|---|---|
| 3a | Re-derive 4 generic combinatorial primitives | ~150-200 lines |
| 3b | Per-call obligations for `modalApplyOneS4Keyed φ₀ keys`, ∀ keys | ~150-300 lines |
| 3c | `modalFuelS4`, entry-measure sufficiency, Phase-1 fuel edit | ~100-150 lines |
| 3d | Keys-threaded Hintikka invariant bundle + step-preservation | ~400-700 lines |
| 3e | Top-loop induction assembly | ~250-400 lines |
| 4 | S4 mint-redirect soundness lemma + soundness top-loop | ~300-500 lines |
| 5 | Completeness + decidability assembly | ~150-250 lines |

Total estimate: ~1500-2500 new lines, materially larger than this plan's original 10-16 hour
estimate for the whole task. Recommend re-planning Phases 3-5 as their own dedicated task (or a
`--hard` `/implement` with per-phase dispatch) rather than continuing under this plan's original
phase boundaries.

## Hard Constraints Carried Forward (unchanged)

- Zero `sorry`, zero new `axiom`, every new public declaration `lean_verify`-clean.
- Do not modify frozen task-511 Phase 1-6 deliverables (`S4LoopInv`, `modalStepBranchS4Keyed`,
  `modalStepBranchS4_worldBound`, `modalHintikkaSetS4_eq`) except to consume them.
- Do not regress S5's `ModalLoopAuxS5w`/`modalExpandBranchesHintikka` call site or B's
  `modalExpandBranchesB`/decidability.
- Territory: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` and
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, additive only.
