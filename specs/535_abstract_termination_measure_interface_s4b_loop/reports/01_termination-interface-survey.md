# Research Report: Abstract Termination-Measure Interface for the S4/B Loop Lemma (Task 511 Phase 7 Follow-On)

- **Task**: 535 — abstract_termination_measure_interface_s4b_loop
- **Type**: cslib
- **Session**: sess_1784888487_837ef1_535
- **Date**: 2026-07-24
- **Report**: reports/01_termination-interface-survey.md
- **Scope surveyed**: `Cslib/Logics/Modal/Tableau/{GenericDriver,CompletenessLoop,LoopChecking,Saturation,S5Simplification,BDriver,FrameCompleteness,FrameSoundness}.lean`; archived tasks 505 (B-system) and 513 (generalized soundness chain).

## Executive Summary

The task presents two acceptable resolution paths for closing `Decidable (s4Valid φ)`:
**(a) 9-A** — generalize the shared generic driver / `Aux`-parametrized top-loop lemma to thread
extra opaque per-branch state; and **(b) 9-B** — a bespoke S4-specific keyed driver
(`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed`) around the already-landed
`modalStepBranchS4Keyed`.

**Recommendation: path (b), the bespoke keyed S4 driver.** Three findings from the survey drive
this, two of which materially change the picture the plan's Planner Decision 2 was written under:

1. **The shared-beneficiary premise for path (a) no longer holds.** Both cited beneficiaries
   already reached decidability *without* threaded state: the B-system (task 505) landed
   `modalTableauB = modalTableauGen modalApplyOneB` with `modalExpandBranchesB_hintikka` as a
   **one-line instantiation** of the existing `Aux`-parametrized lemma, and S5 (task 515) landed
   `modalTableauS5 = modalTableauGen modalApplyOneS5w` the same way. Their rules read only
   `(sf, b, acc)` — all in `RuleApply`'s signature — so a `Prop`-valued `Aux` suffices. Threading
   opaque `State` through the generic driver would benefit *only* S4; every other logic (K, T, B,
   S5, Five) would carry a `State := Unit` parameter as pure overhead. Generalizing shared
   infrastructure to serve a single consumer is the wrong trade.

2. **The hardest remaining work is required by BOTH paths identically, so path (a) buys nothing
   on it.** `Decidable (s4Valid φ)` needs a soundness half and a completeness half. Neither exists
   yet at top level for *any* S4 driver (finding below): there is **no `modalTableauS4_sound`**,
   no `modalTableauS4_complete`, no `s4Valid_decides`. Both paths must assemble these from scratch
   and must repoint the `Decidable` instance to a keyed driver. Path (a)'s large refactor does not
   reduce that work at all.

3. **Reuse of the frozen Phases 1-6 is maximal and clean under path (b), and zero-regression.**
   `modalStepBranchS4_preserves_S4LoopInv` is already shaped as a *bundled* induction step
   (S4LoopInv + `keysWorldsKnown` + `worldsContiguousS4` for every child branch), and
   `modalStepBranchS4_worldBound` is already proven. A bespoke `processNext`-style loop threads
   `keys` (plus the two aux invariants) as extra worklist columns and discharges its per-step
   obligation with these landed theorems verbatim. It touches none of the generic definitions
   that B (505) and S5 (515) depend on, so it cannot regress them — a hard constraint of this task.

Path (a) remains a legitimate, more-reusable *future* refactor and is documented below as the
alternative, but it is deprioritized here for the reasons above.

## Confirmed Root Cause (re-verified against source)

The driver/shadow-invariant mismatch documented in task 511's Phase-7 handoff is confirmed
exactly:

- The real driver is `modalTableauS4 φ := modalTableauGen (modalApplyOneS4 φ) φ`
  (`LoopChecking.lean:671-672`). `modalTableauGen`/`modalExpandBranchesGen`/`modalStepBranchGen`
  (`Saturation.lean:122, 201-243, 363-366`) all take a **fixed** `apply : RuleApply Atom`
  (`Saturation.lean:108-111`) and recurse a worklist of `(branch, expanded, acc)` triples only —
  **no channel for extra threaded state**.
- The landed termination machinery is proven for `modalStepBranchS4Keyed`
  (`LoopChecking.lean:770-797`), whose rule `modalApplyOneS4Keyed φ₀ keys`
  (`LoopChecking.lean:700-710`) takes a `keys : List (WorldIndex × Finset (Sign × Proposition
  Atom))` argument that **evolves every step** (`keys' := keys ++ [(modalNextWorld b, …)]` on an
  unblocked mint). This is genuine per-branch threaded state, **not** recoverable from `(b, acc)`:
  keys freeze the birth content at minting time, while the live `relevantSetFinset` grows
  monotonically (`keyLowerBd` is `k ⊆ relevantSetFinset φ₀ b w`, a **subset, not equality** —
  `S4LoopInv`, `LoopChecking.lean:4373`). The frozen historical content is lost once the branch
  grows, so no fixed `RuleApply` closure reading `(sf, b, acc)` can reproduce it.
- Consequently the two guards `blockingWorldS4` (live, `:391`) and `blockingWorldS4Keyed`
  (frozen keys, `:459`) are genuinely different decision procedures that can diverge at the two
  minting shapes, so `modalStepBranchS4_worldBound` (proven about the keyed stepper) cannot be
  applied as fuel-sufficiency for the live `modalTableauS4` by a one-line bridge.

This is why an existential `Aux(b,e,acc) := ∃ keys, S4LoopInv-fields` does not rescue path (a) as
originally scoped: `AuxStepPreserved` (`CompletenessLoop.lean:262`) is a fact re-derived from
`(b,e,acc)` at each point with no memory of *which* `keys` witnessed the previous step, so it
would have to re-establish `keysDistinct` preservation from the live guard — the exact
insufficient argument that forced `blockingWorldS4Keyed` into existence in the first place.

## New Scope Finding (not in the plan or prior handoffs)

**`s4Valid` occurs exactly once in the entire codebase — its own definition**
(`FrameSoundness.lean:1051`, `def s4Valid φ := frameValid s4FC φ`). There is:

- **No `modalTableauS4_sound`** (`modalTableauS4 φ = .closed → s4Valid φ`) anywhere.
- **No `modalTableauS4_complete`**, no `s4Valid_decides`, no `instDecidableS4Valid`.
- **No theorem connecting `modalTableauS4` to `s4Valid` at all.**

The task description's reference to "soundness (`modalTableauS4_sound`, task 506)" as an existing
asset is **inaccurate** — that theorem does not exist. What *does* exist is the full set of
**ingredients** for both halves:

| Ingredient | Location | Role |
|---|---|---|
| `s4FC`, `s4Valid` | `FrameSoundness.lean:1047,1051` | target validity notion (Refl ∧ Trans) |
| `branchSatisfiableIn_s4FC_*` family | `FrameSoundness.lean:1085,1102,…` | soundness building blocks |
| `extractModelS4` (+ `_refl`, `_trans`, `_hasEdge_imp_r`) | `FrameCompleteness.lean:143-185` | countermodel construction |
| `modalTruthLemmaS4` | `FrameCompleteness.lean:232` | truth lemma; consumes `modalHintikkaSetS4 φ₀ b acc` |
| `modalOpenBranchS4_countermodel` | `FrameCompleteness.lean:401` | open-branch → refutes `φ₀` |
| `modalHintikkaSetS4_eq` | `LoopChecking.lean:3874` | `rfl` bridge: `modalHintikkaSetS4 = modalHintikkaSetGen (modalApplyOneS4 φ₀)` |

**Implication:** Phase 7 is materially larger than "wire the world bound into fuel sufficiency."
It is the full **soundness + completeness + decidability assembly** for S4, none of which is
landed at top level. This holds regardless of path (a) vs (b). The world bound (Phases 1-6) is a
necessary input to the completeness/termination half, not the deliverable itself.

## The State-Free Precedent (S5) and Why S4 Differs

S5's completeness assembly is the direct template (`FrameCompleteness.lean:2336-2421`):

1. `modalExpandBranchesHintikka modalApplyOneS5w modalApplyOneS5w_specCore φ₀ (ModalLoopAuxS5w φ₀)
   … → modalHintikkaSetGen modalApplyOneS5w b a` (open branch is Hintikka for the *witness* rule).
2. `hintikka_congr` (`S5Simplification.lean:604`) converts to `modalHintikkaSetGen modalApplyOneS5
   b a` (the *reference* rule) — "the two rules agree on Hintikka-set-hood."
3. Truth lemma + countermodel + soundness dichotomy → `s5Valid_decides` → `instDecidableS5Valid`
   (`:2407-2421`).

S5 needs no threaded state because `modalApplyOneS5w` mints only on a fresh `(sign, formula)`
**tag** — a stable quantity read directly off the current branch — rather than on a growing
relevant-set. S4's chosen design (task 511 Option A, birth-keys) deliberately compares
relevant-set *content*, which grows, forcing the frozen-`keys` shadow. That design decision is
what creates the threaded-state requirement; it is landed and sorry-free (Phases 1-6) and the task
forbids discarding it.

> Note for the record — a **considered-and-rejected** third direction: re-derive S4 with a
> tag-based live witness-reuse guard (à la `modalApplyOneS5w`/`modalApplyOneB`), which would fit
> the existing `Prop`-valued `Aux` interface with no driver change at all. This is rejected: it
> would discard the entire frozen, sorry-free Phases 1-6 birth-key machinery and re-open the
> task 511 research design, contradicting this task's hard constraint ("Do not modify the frozen
> … Phases 1-6 deliverables except as needed to wire"). It is mentioned only so the planner knows
> it was evaluated.

## Recommended Design — Path (b): Bespoke Keyed S4 Driver

All new declarations live in `LoopChecking.lean` (driver + termination + Hintikka congruence) and
`FrameCompleteness.lean` (completeness/soundness/decidability assembly), mirroring the S5 layout.
The generic driver files are **not touched**.

### Component map

| New declaration | Models on (precedent) | Consumes (landed) |
|---|---|---|
| `modalExpandBranchesS4Keyed` (fuel loop threading `keys` + aux invariants as extra worklist columns) | `modalExpandBranchesGen`/`processNext` (`Saturation.lean:201-243`) | `modalStepBranchS4Keyed` (`:770`) |
| `modalTableauS4Keyed φ` (entry: `F(φ)@0`, `keys := []`) | `modalTableauGen` (`Saturation.lean:363`) | `modalExpandBranchesS4Keyed` |
| `modalExpandBranchesS4Keyed_hintikka` (open branch ⇒ `modalHintikkaSetGen (modalApplyOneS4Keyed φ₀ keys) b a`) | S5 invocation of `modalExpandBranchesHintikka` (`FrameCompleteness.lean:2342-2360`); `modalExpandBranchesB_hintikka` (`BDriver.lean:862`) | `modalStepBranchS4_preserves_S4LoopInv` (`:4614`), `modalStepBranchS4_worldBound` (`:3806`) |
| `hintikka_congr_S4` (keyed ⇔ live agree on Hintikka-set-hood) | `hintikka_congr` (`S5Simplification.lean:604`) | pointwise non-minting agreement `heq1` already used at `LoopChecking.lean:2042,2470,2758` |
| `modalTableauS4Keyed_sound` | `modalTableauS5_sound` / `modalTableauB_sound` (`FrameCompleteness.lean:1877`) | `branchSatisfiableIn_s4FC_*` (`FrameSoundness.lean`) |
| `modalTableauS4Keyed_complete` | `modalTableauS5_complete` (`:2336`) | `modalTruthLemmaS4`, `extractModelS4`, `modalOpenBranchS4_countermodel`, `hintikka_congr_S4`, `modalHintikkaSetS4_eq` |
| `s4Valid_decides` + `instDecidableS4Valid` | `s5Valid_decides` + `instDecidableS5Valid` (`:2407-2421`) | the two halves above |

### Why the termination half is nearly free

`modalStepBranchS4_preserves_S4LoopInv` (`LoopChecking.lean:4614-4651`) already returns, for every
child branch `b'`:
`S4LoopInv φ₀ b' e' newAcc keys' ∧ (keysWorldsKnown for b') ∧ (worldsContiguousS4 b')`.
That is exactly the induction hypothesis a `processNext` port needs to carry across the worklist,
and `modalStepBranchS4_worldBound` (`:3806`) already gives `modalMaxWorld b < modalWorldBoundS4 φ₀`
from `S4LoopInv`. So the fuel-sufficiency argument (fuel `= modalFuel φ₀` suffices because world
creation is bounded) is a direct transcription of the generic loop's own termination reasoning,
with `keys`/aux-invariants threaded alongside.

### The one genuinely novel obligation (gate early)

`hintikka_congr_S4`: on a **saturated open branch**, `modalHintikkaSetGen (modalApplyOneS4Keyed φ₀
keys) b a ↔ modalHintikkaSetGen (modalApplyOneS4 φ₀) b a`. Plausibility is high — the two rules
already agree at all non-minting shapes (`heq1`, three existing call sites), and Hintikka-set-hood
is a *saturation* property (no new content generated), where on a saturated branch neither guard
mints. But it is unverified and is the crux the planner should schedule as an early gating lemma;
if it resists within budget, mark that phase `[BLOCKED]` with the exact `lean_goal`, never a
placeholder.

### Suggested phase decomposition (for the planner)

1. **Driver defs** — `modalExpandBranchesS4Keyed`, `modalTableauS4Keyed`, `keys`-threaded
   `processNext`; compiles green (no proofs). *(Repoint decision: define `modalTableauS4Keyed`
   fresh; do NOT redefine the existing live `modalTableauS4` — leave it as the reference artifact
   the `heq1`/bridge lemmas consume, and point `instDecidableS4Valid` at the keyed driver.)*
2. **Termination/Hintikka top-loop** — `modalExpandBranchesS4Keyed_hintikka` via the bundled
   preservation theorem + world bound (the "nearly free" half).
3. **Congruence gate** — `hintikka_congr_S4` (the crux; `[BLOCKED]`-eligible).
4. **Soundness** — `modalTableauS4Keyed_sound` from `branchSatisfiableIn_s4FC_*`.
5. **Completeness + decidability** — `modalTableauS4Keyed_complete`, `s4Valid_decides`,
   `instDecidableS4Valid`; resume task 511 Phase 7 by wiring these against Phases 1-6.

## Alternative — Path (a): Generalize the Driver to Thread State (documented, deprioritized)

Introduce a `State`-parametrized generic layer, e.g. a `RuleApplyState (σ) := σ → RuleApply`-style
wrapper with a `stepState : σ → sf → b → acc → σ` transition, and thread `σ` through
`modalStepBranchGen`/`modalExpandBranchesGen`/`processNext`/`modalExpandBranchesHintikka`. K/T/B/S5/
Five instantiate `σ := Unit`; S4 instantiates `σ := List (WorldIndex × Finset (Sign × Proposition
Atom))`. Task 515's `Aux`-parametrized `modalExpandBranchesHintikka` (`CompletenessLoop.lean:1430`,
with `AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka`) is a partial head start but is **not**
sufficient alone (its `Aux` is `Prop`-valued and re-derived from `(b,e,acc)`, per the root cause).

**Why deprioritized:**
- **Regression surface.** It edits the exact generic definitions B (505) and S5 (515) already
  depend on (`modalExpandBranchesB_eq`, `modalStepBranchS5_eq` are `rfl`-locked to them). The task
  forbids regressing S5's landed decidability; a `State` refactor risks every K/T/B/S5/Five
  consumer.
- **No shared upside.** Per Executive-Summary finding 1, no current consumer needs threaded state,
  so the generalization serves only S4.
- **Does not reduce the hard half.** Soundness/completeness/congruence assembly (Executive-Summary
  finding 2) is identical work under either path.

Path (a) is the right investment only if a *future* logic genuinely needs content-based (not
tag-based) witness reuse with threaded state; at that point the S4 bespoke driver from path (b)
becomes the concrete template to generalize from, with two consumers to justify the abstraction.

## Reuse-First Check (CSLib philosophy)

Ran the reuse protocol against `Cslib.Logics.Modal.Tableau.*`:
- **Do not** introduce a new top-loop abstraction if path (b) is chosen — reuse
  `modalExpandBranchesGen`/`processNext` as the *structural template* (copy-and-thread), and reuse
  every landed Phase 1-6 lemma directly.
- **Do not** re-derive S4 soundness/completeness ingredients — `extractModelS4`,
  `modalTruthLemmaS4`, `modalOpenBranchS4_countermodel`, `modalHintikkaSetS4_eq` all exist and
  mirror the S5 assets one-for-one.
- The only genuinely new lemma with no existing analog-by-instantiation is `hintikka_congr_S4`,
  and even it has a direct structural precedent (`hintikka_congr`) plus a landed pointwise
  agreement fact (`heq1`).

## Hard-Constraint Compliance Notes for Implementation

- Zero sorry / zero new axiom; every new public declaration `lean_verify`-clean
  (`propext`/`Classical.choice`/`Quot.sound` only). If a phase cannot close, `[BLOCKED]` with the
  exact reached `lean_goal` — never a vacuous placeholder (`def X := True`, etc. are prohibited).
- Do not modify the frozen Phases 1-6 deliverables (`S4LoopInv`, `modalStepBranchS4Keyed`,
  `modalStepBranchS4_worldBound`, `modalHintikkaSetS4_eq`) except to wire the new driver against
  them. Path (b) requires **no** edits to them; it only consumes them.
- Do not touch S5's `ModalLoopAuxS5w`/`modalExpandBranchesHintikka` call site
  (`FrameCompleteness.lean:2342`) or B's `modalExpandBranchesB` — path (b) leaves the generic
  layer untouched, satisfying this automatically. (Path (a) would put both at risk.)
- Keep the existing live `modalTableauS4` in place; add `modalTableauS4Keyed` and point the
  `Decidable` instance at it (avoids disturbing the `heq1` consumers and the reference Hintikka
  bridge `modalHintikkaSetS4_eq`).

## Open Questions for the Planner

1. Is `hintikka_congr_S4` provable at the saturated-branch minting shapes, or does saturation of
   the keyed branch fail to imply saturation under the live guard at a blocked mint? (The gating
   risk; schedule early.)
2. Should the soundness half be proven about `modalTableauS4Keyed` directly, or about the live
   `modalTableauS4` and transported via a driver-level congruence? (Direct is simpler and avoids
   needing a full driver-equality; recommended.)
3. Fuel value: confirm `modalFuel φ₀` (K's fuel) is sufficient for the S4 keyed loop given
   `modalWorldBoundS4 φ₀ = 2^(2·|Sf|)`, or whether an S4-specific fuel is needed (compare
   `modalUniverseS4_length_le`, `LoopChecking.lean`).

## Tactic-Survey Note

This is an interface/architecture survey, not a single-goal proof task, so the advisory tactic
portfolio (`aesop`/`simp`/`omega`/…) does not apply to a specific goal here. Tactic selection is
deferred to the per-lemma implementation phases, where `lean_multi_attempt` should gate each novel
obligation (especially `hintikka_congr_S4`) before committing edits.
