# Implementation Plan: S5 Universal-Rule Termination Machinery (v2)

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Status**: [COMPLETED]
- **Effort**: 12-18 hours
- **Dependencies**: Task 514 (literature grounding, anchor), Task 504 (parent; S5 rule/driver + `extractModelS5*` landed CI-green), Task 511 (shared S4 guard-vs-live-set obstruction; keys-aware guard redesign findings)
- **Research Inputs**: reports/01_s5-termination-implementation-blueprint.md; summaries/01_s5-termination-machinery-summary.md (v1 implementation, P1/P2 landed, P3/P5 blocked); task 511 reports/01_s4-termination-guard-redesign.md; task 511 summaries/01_s4-termination-bound-decidability-summary.md
- **Artifacts**: plans/02_s5-termination-machinery.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The v1 plan landed Phases 1-2 sorry-free and CI-green (frame surface, world bound, universe, and the live-set minting guard + `modalApplyOneS5g`), then blocked at Phase 3 on a genuine structural obstruction — the exact S5 mirror of sibling task 511's S4 Phase-5 blocker. The blocker is two coupled gaps: (1) an **infrastructure gap** — the v1 four-field `S5LoopInv` lacks the `accTargetsKnown` and subformula-closure invariants that `modalApplyOne_knownWorlds_step` (`FmpMeasure.lean:2042`) demands to prove `keysTotal`/`keyLowerBd`/`keysInUniverse`; and (2) a **design gap (the crux)** — `blockingWorldS5`'s minting guard compares a fresh key against the *live* `relevantSetFinset`, but `keyLowerBd` only records stored keys as *lower bounds*, so a freshly-minted key can collide with an *old* world's frozen historical key, and `keysDistinct` is therefore NOT preserved per step. This v2 re-architects the termination chain to defeat both gaps: it extends `S5LoopInv` to the full ten-field shape mirroring the landed `S4LoopInv` (`LoopChecking.lean:1127`), and redesigns the guard to compare the prospective birth content against the threaded **stored keys** directly (not live relevant sets), so `blockingWorldS5Keyed_none_fresh` discharges `keysDistinct` as a genuine invariant. It also addresses the *independent* soundness blocker with a new reachability-threading fuel-induction bridge. **Definition of done**: the extended invariant, the corrected preservation lemmas, and the pigeonhole bound land sorry-free and CI-green; the soundness bridge lands sorry-free (independent of the termination chain); the frontier phases (Hintikka lift + decidability, 5/KB5) are pursued and, if they resist within budget, honestly `[BLOCKED]`-with-open-goal — never a `sorry`, never a re-added rank axiom (D2/D5). Strategy 2 (semantic bounded-model FMP via the landed `extractModelS5`) stays baked into the decidability phase as the pre-authorized sorry-free fallback.

### Research Integration

This revision synthesizes three authoritative inputs:

- **v1 implementation summary** (`summaries/01_s5-termination-machinery-summary.md`): the primary evidence. Documents exactly what landed (P1/P2 green + Phase 3's four-field `S5LoopInv` scaffolding, keyed step, and three `modalKnownWorlds` re-derivations) and the two concrete Phase-3 obstructions (infrastructure gap on `keysTotal`/`keyLowerBd`/`keysInUniverse`; the `keysDistinct` design gap) plus the independent Phase-5 soundness blocker (`modalExpandBranchesGen_closed_unsatIn` threads no reachability fact). Its "Resume Point" prescribes exactly the two design decisions this v2 makes: extend `S5LoopInv` to the full `S4LoopInv` field shape, and redesign the guard to compare against stored keys.
- **Task 511 guard-redesign findings** (`reports/01_s4-termination-guard-redesign.md` + `summaries/01_*.md`): task 511 hit the **identical** obstruction in S4 (blocked at its Phase 5, `_preserves_keysDistinct`). Its report Section 4 specifies the birth-key invariant and Section 2 proves live-set distinctness is not a loop invariant (Gap 1 monotone-collapse, Gap 2 source-vs-successor). Critically, task 511's *implementation* then discovered that even the Option-A guard comparing against *current relevant sets* is mathematically insufficient (511 summary Phase-5 concrete scenario: world `A` born with key `{a}` grows to `{a,b}`; fresh world `B` computes key `{a}`; guard compares against `A`'s live `{a,b} ≠ {a}` and does not block; `B` records key `{a} = A`'s key; `keysDistinct` violated). 511's documented fix — **compare against the recorded `keys` list directly** — is the shared solution this v2 adopts for S5. The real ten-field `S4LoopInv` (grep-verified in `LoopChecking.lean:1127`) grounds the extended `S5LoopInv` field list below.
- **Blueprint report** (`reports/01_s5-termination-implementation-blueprint.md`): confirms path (b) loop-checking (D1), the permanently-abandoned rank route (D2), the spec-bound generic lift wall (F4), the achievable-but-new soundness route (F5), the fuel wiring (F6), and Strategy 2 as the honest fallback (F8).

### Prior Plan Reference

This v2 supersedes `plans/01_s5-termination-machinery.md`. Phases 1-2 (frame surface + world bound + universe; live-set guard + `modalApplyOneS5g` + agreement lemmas) landed CI-green and are preserved verbatim as `[COMPLETED]` with commit hashes. Phase 3's *partial* v1 scaffolding (the four-field `S5LoopInv` structure, `modalStepBranchS5gKeyed`, and the three re-derived `modalKnownWorlds_*_S5` helpers, committed at `21b4ec03`) remains committed and reusable, but its four-field invariant is **extended** and its live-set minting decision is **superseded** by this v2's re-architected Phase 3 (marked `[NOT STARTED]` because the corrected structure/guard are new work).

## Goals & Non-Goals

**Goals**:
- Extend `S5LoopInv` from four fields to the full ten-field shape mirroring the landed `S4LoopInv` (`LoopChecking.lean:1127`), naming each new generic field and what it guarantees.
- Redesign the minting guard to compare the prospective birth content against the threaded **stored keys** (`blockingWorldS5Keyed`), so `blockingWorldS5Keyed_none_fresh` makes `keysDistinct` a genuine per-step invariant (the crux fix).
- Prove the corrected preservation lemmas over the ten-field invariant and the pigeonhole `#worlds ≤ 2^(2·|Sf|)` bound under the corrected guard.
- Land `modalTableauS5_sound` via a new reachability-threading fuel-induction bridge (`modalExpandBranchesGen_closed_unsatIn_reachable`), independent of the termination chain (F5).
- Deliver the spec-free Hintikka lift + fuel bridge + `Decidable (s5Valid φ)` against `Cube.S5`, with Strategy 2 (semantic FMP) baked in as the sorry-free fallback.
- Deliver 5/KB5 validity + completeness via `Satisfies.five` and `Euclidean.lean`'s `RightEuclidean` API.
- REUSE the CI-green landed assets (P1/P2 surface, `modalStepBranchS5gKeyed`, the `modalKnownWorlds_*_S5` re-derivations, `extractModelS5*`) and the φ₀-parametric engine (`signedSubfmls`, `relevantSetFinset`, `modalUniverseS5`).
- Zero sorry, zero new axiom; full CSLib CI at every milestone; incremental commit at each green milestone; narrow `git add`.

**Non-Goals**:
- Path (a) restricted rank-compatible rule; any `RuleApplicationSpec modalApplyOneS5` witness (proven false, D2).
- Genuine pure-K5 / pure-5 (Euclidean-without-equivalence) completeness — explicitly OUT OF SCOPE (`S5Simplification.lean:365-384`).
- Building S4's own decidability capstone. This plan may factor a shared interface and its keys-aware guard is deliberately transposable to S4, but it does not owe S4 decidability.
- Any edit to K/T/B declarations, `GenericDriver.lean`'s `RuleApplicationSpec` core, or `FmpMeasure.lean` (zero regression).
- Re-verifying or rewriting the already-landed, still-valid live-set `modalApplyOneS5g` and its agreement lemmas: the keys-aware minting decision lives in the keyed stepper, so the non-minting Hintikka/truth-lemma bridges that consume `modalApplyOneS5g` stay untouched.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **R1 (task-511 coupling)** — S4 (task 511) and S5 (task 515) share the *identical* guard-vs-live-set obstruction; neither has resolved it. A wrong or divergent keys-aware guard design here would fail to unblock either. | H | M | Adopt task 511's documented fix verbatim in shape: compare against the recorded `keys` list, not live sets (511 summary "Next Steps"; report Section 4 R1-R4). Cite the S4 analogue lemma names (`blockingWorldS4_none_fresh`, `S4LoopInv`) so the S5 fix is a faithful transposition, not a fresh guess. A single shared guard redesign could unblock both — see the sequencing note below. |
| **R2 (guard/stepper re-derivation)** — the keys-aware guard needs `keys` threaded, but `modalApplyOneS5g` is a plain `RuleApply` with no `keys` parameter and is already consumed (unparametrized) by the P2 agreement lemmas and the Hintikka bridges (511 summary Phase-5 documents this scope). | H | M | Do NOT rewrite `modalApplyOneS5g`. Compute the keys-aware block/mint decision *inside* `modalStepBranchS5gKeyed` (the "keys-aware bypass inside a redesigned stepper" of the 511 summary), leaving the live-set `modalApplyOneS5g` and its agreement lemmas as still-valid artifacts for the non-minting bridges. This contains the blast radius to the keyed stepper + `S5LoopInv`. |
| **R3 (keysDistinct crux)** — even a birth-content guard against *current relevant sets* is provably insufficient (511 summary concrete scenario: proper-subset key collides with a grown live set). | H | M | The v2 guard compares against **stored keys** directly, so `blockingWorldS5Keyed_none_fresh` yields `newkey ≠ k` for every `(w',k) ∈ keys` — discharging `keysDistinct`'s new-vs-old case with no live-set reasoning. Keys never change after birth, so no later step violates distinctness (511 report R1/R3). |
| **R4 (infrastructure gap)** — `keysTotal`/`keyLowerBd`/`keysInUniverse` need `accTargetsKnown b acc` (the standing hypothesis of `modalApplyOne_knownWorlds_step`, `FmpMeasure.lean:2042`) and a subformula-closure fact, absent from the v1 four-field invariant. | M | M | Extend `S5LoopInv` with the six generic `S4LoopInv` fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`); `accKnown` (= `accTargetsKnown`) feeds `modalApplyOne_knownWorlds_step`, `bClosure` (⊆ `modalUniverseS5 φ₀`) supplies the subformula-closure. Reuse the FmpMeasure invariant primitives (`accFreshInv`, `accTargetsKnown`, `outDeg`, `isMintingShaped`) verbatim (511 report Section 6 reuse table). |
| **R5 (soundness reachability bridge)** — `modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:728`) threads only `accFreshInv` and hands per-shape lemmas only direct-edge relatedness; S5's universal arms need `m.r (f lbl) (f w')` for `w'` many mint-tree edges away (v1 summary Phase-5 blocker, F5). | M | M | Author a *new* top-level bridge `modalExpandBranchesGen_closed_unsatIn_reachable` threading `∀ w ∈ modalKnownWorlds b, ReflTransGen acc.hasEdge 0 w` alongside `accFreshInv`; reuse `modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean:193`) as a black box for the satisfiability half; re-derive `hBoxPos`/`hDiaNeg` via `s5FC`'s `Std.Refl`/`RightEuclidean` projections on the reachability witness. Independent of the termination chain — forks after P1. |
| **R6 (spec-free lift, the frontier)** — `modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:876`) is hard-wired to `RuleApplicationSpec` + `ModalLoopInvGen` (rank); S4 never built a spec-free analogue (F4, 511 Section 3). | H | H | Sequence the lift last and isolated; attempt by generalizing the induction over `S5LoopInv` (world bound) instead of `ModalLoopInvGen` (rank). If it resists, land `[BLOCKED]` with the exact open goal and pivot decidability to Strategy 2 (F8, pre-authorized). |
| **R7 (fuel domination)** — `modalTableauGen` hardwires K's `modalFuel φ` (`Saturation.lean:363/366`); K's depth-fuel may not dominate the S5 world-bounded re-broadcast (F6). | M | M | Option (i) first: prove `modalExpMeasureS5 (modalUniverseS5 φ) … ≤ modalFuel φ`. Fallback Option (ii): define `modalTableauS5g` with `modalFuelS5` derived from `modalWorldBoundS5`. Downstream of the pigeonhole. |
| **R8 (scope realism)** — landing all frontier phases sorry-free in one task is optimistic given the shared S4/S5 precedent. | M | H | Task success = extended invariant + corrected preservation + pigeonhole + soundness bridge green (concrete, sorry-free). Keep the frontier phases isolated with `[BLOCKED]`-with-open-goal branches; never `sorry`. |

**Task-511 sequencing note (R1)**: because tasks 511 and 515 are blocked at the identical wall, the keys-aware guard + ten-field invariant + preservation-lemma pattern proved here transposes directly to S4. Two coordination options: (a) land this S5 fix first (it carries the pre-existing v1 P1/P2 scaffold, so it is closer to a running start) and then port the pattern to S4 as a follow-up, or (b) spawn a single shared keys-aware-guard task that both consume. Prefer (a) unless a shared `LoopTermination` interface is independently authorized; either way, avoid duplicating the guard-redesign proof effort across the two tasks.

## Testing & Validation

Run the full CSLib CI pipeline at **every** phase milestone (zero-debt contract) before committing:

- [ ] `lake build` — full project green (baseline: 3236/3236 jobs)
- [ ] `lake exe checkInitImports` — clean
- [ ] `lake exe lint-style` — clean
- [ ] `lake exe lint` — 0 new errors on task-touched files (1 pre-existing unrelated `unusedArguments` error in `PrimeExclusion.lean` predates this task; do not action)
- [ ] `lake test` — `CslibTests` suite exit 0
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — clean for task-touched files
- [ ] `grep -c 'sorry' <touched files>` — 0 (prose mentions excepted)
- [ ] `grep -c '^axiom ' <touched files>` — 0 new axioms

Per-milestone commit discipline: narrow `git add` (only the specific `.lean` file(s) touched by the phase + this plan/state), commit message `task 515 phase {P}: {name}`.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 0 (landed) | 1, 2 | -- |
| 1 | 3, 7 | -- (P3 needs P2 landed; P7 needs P1 landed) |
| 2 | 4 | 3 |
| 3 | 5 | 4 |
| 4 | 6 | 5 |
| 5 | 8 | 6 |
| 6 | 9 | 8 |

Phases within the same wave can run in parallel. **Phase 7 (soundness) forks immediately after the landed Phase 1 and runs parallel to the P3 -> P4 -> P5 -> P6 termination chain** (F5: it consumes only `freshLocal` + reachability, never `rankStep`, so a blockage in the termination chain does not strand it). The decidability capstone (P8) depends on the pigeonhole (P6) and the extended `S5LoopInv` (P3); P9 depends on P8.

### Phase 1: Frame surface + S5 world bound + universe [COMPLETED]

**Completed:** commit `66021669` (`task 515 phase 1: S5 frame surface + world bound + universe`).

Landed sorry-free: `s5FC`, `s5Valid`, `fiveFC`, `fiveValid`, `kb5FC`, `kb5Valid` (`FrameSoundness.lean`, mirroring `s4FC`/`symmFC`); `modalWorldBoundS5`, `modalUniverseS5`, `modalUniverseS5_length_le` (`S5Simplification.lean`, verbatim mirror of `modalWorldBoundS4`/`modalUniverseS4`/`modalUniverseS4_length_le`, `LoopChecking.lean:229/235/245`). `Cube.Five`/`Cube.KB5` are `Set (Proposition Atom)` objects, not `FrameCondition` values, so `fiveFC`/`kb5FC` predicates were authored and `fiveValid`/`kb5Valid` defined via `frameValid`, matching every `*Valid` shape in the file.

**Goal**: Author the missing frame-class definitions and the world-bound/universe scaffolding, reusing the φ₀-parametric engine verbatim.

**Tasks**:
- [x] `s5FC`, `s5Valid`, `fiveFC`, `fiveValid`, `kb5FC`, `kb5Valid` (`FrameSoundness.lean`).
- [x] `modalWorldBoundS5`, `modalUniverseS5`, `modalUniverseS5_length_le` (`S5Simplification.lean`).
- [x] Reuse `signedSubfmls` + `relevantSetFinset` verbatim.

**Timing**: 1 hour (done)

**Depends on**: none

**Files**: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

---

### Phase 2: Live-set guard + guarded rule (preserved scaffold) [COMPLETED]

**Completed:** commit `aa9015d6` (`task 515 phase 2: S5 minting guard + guarded rule`).

Landed sorry-free in `S5Simplification.lean`: `successorBirthContentS5`/`blockingWorldS5` (+3 guard lemmas), reusing `successorBirthContent` from `LoopChecking.lean` verbatim; `modalApplyOneS5g` (guarded rule routing K's two minting shapes through the guard, universal arms unchanged); 6 agreement lemmas. Added `public import Cslib.Logics.Modal.Tableau.LoopChecking` (read-only reuse; zero regression to S4/K/T/B).

**Preservation note for v2**: the guard landed here is the **live-set** guard (`blockingWorldS5` compares birth content against `relevantSetFinset`). v2 has established (via the task-511 precedent and the v1 Phase-3 blocker) that the live-set guard is insufficient for `keysDistinct`. It is **not discarded**: `modalApplyOneS5g` and its agreement lemmas remain valid for the non-minting Hintikka/truth-lemma bridges (which depend only on non-minting-shape agreement). The keys-aware minting decision is layered on top in Phase 3's stepper, not by rewriting `modalApplyOneS5g`.

**Goal**: Transpose the S4 blocking guard to S5 and establish agreement lemmas against `modalApplyOneS5`/K.

**Tasks**:
- [x] `successorBirthContentS5`, `blockingWorldS5` (+3 guard lemmas).
- [x] `modalApplyOneS5g` + 6 agreement lemmas.

**Timing**: 1.5 hours (done)

**Depends on**: 1

**Files**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

---

### Phase 3: Keys-aware guard redesign + extended ten-field `S5LoopInv` [COMPLETED]

**Goal**: Re-architect the termination bundle to defeat both v1 blocker gaps. Redesign the minting guard to compare the prospective birth content against the threaded **stored keys** (not live relevant sets), and extend `S5LoopInv` from four fields to the full ten-field shape mirroring the landed `S4LoopInv` (`LoopChecking.lean:1127`). **This is the crux structural fix; it supersedes the v1 four-field structure and the live-set minting decision.** Budget generously.

**Tasks**:
- [x] Define the keys-aware guard `blockingWorldS5Keyed φ₀ keys b s φ w : Option WorldIndex` that searches the threaded `keys : List (WorldIndex × Finset (Sign × Proposition Atom))` for a stored `(w', k)` with `k = successorBirthContentS5 φ₀ b s φ w` (reusing the landed `successorBirthContentS5`). Mirror the *intent* of `blockingWorldS4` (`LoopChecking.lean:391`) but key the comparison on stored keys, per task 511's documented fix (511 summary "Next Steps"; report Section 4 Option A2).
- [x] Prove `blockingWorldS5Keyed_none_fresh : blockingWorldS5Keyed φ₀ keys b s φ w = none → ∀ w' k, (w', k) ∈ keys → k ≠ successorBirthContentS5 φ₀ b s φ w`. **This is the birth-key invariant that makes `keysDistinct` a genuine per-step invariant** (directly discharges the new-vs-old case). Cite S4 analogue `blockingWorldS4_none_fresh` (`LoopChecking.lean:426`).
- [x] Extend `S5LoopInv` to ten fields, mirroring `S4LoopInv` (`LoopChecking.lean:1127`), each grounded in the real S4 field of the same name (see field list below). *(deviation: altered -- added an 11th field `keysKnown : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b`. Necessary because `blockingWorldS5Keyed` filters over the threaded `keys` list rather than `modalKnownWorlds b` directly, so unlike `blockingWorldS5`/`blockingWorldS4` -- which get "returned world is known" for free via `_mem_modalKnownWorlds`, a corollary of filtering over `modalKnownWorlds b` -- the keyed guard's loop-back target needs this as an explicit invariant to discharge `accKnown` preservation at a blocked/loop-back step (Phase 4). Documented in `S5LoopInv.keysKnown`'s docstring as the converse-membership companion to `keysTotal`.)*
  - `bClosure : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀` — every branch formula in the finite S5 universe; supplies the **subformula-closure** fact (`φ ∈ modalSubfmls φ₀`) needed to place a newly-inserted birth-key pair `(s,φ)` inside `signedSubfmls φ₀` (closes the `keysInUniverse` infrastructure gap).
  - `eNodup : e.Nodup` — expanded set has no duplicates (bookkeeping for `outDegEq`).
  - `eClosure : ∀ x ∈ e, x ∈ modalUniverseS5 φ₀` — expanded formulas in the universe.
  - `accFresh : accFreshInv b acc` — all `acc`-recorded worlds `< modalNextWorld b` (fresh-world confinement); reuse `accFreshInv` verbatim.
  - `accKnown : accTargetsKnown b acc` — every `acc`-edge target is a known branch label. **This is the exact standing hypothesis `modalApplyOne_knownWorlds_step` (`FmpMeasure.lean:2042`) requires** — closes the `keysTotal`/`keyLowerBd` infrastructure gap. Reuse `accTargetsKnown` verbatim.
  - `outDegEq : ∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length` — `outDeg` counts the minting-shaped formulas in `e` at each world; reuse `outDeg`/`isMintingShaped` verbatim.
  - `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse` — carried from v1 (unchanged statements), but `keysDistinct` is now discharged by the keys-aware guard.
  - `keysKnown` (deviation, see above) — converse of `keysTotal`.
- [x] Update `modalStepBranchS5gKeyed` (landed at `21b4ec03`) to compute the keys-aware block/mint decision itself on the two minting shapes (bypassing `modalApplyOneS5g`'s live-set dispatch on those shapes), appending the fresh key to `keys` on an unblocked mint. Leave all non-minting behavior delegated to `modalApplyOneS5` unchanged. *(deviation: altered -- delegates non-minting shapes to `modalApplyOneS5` directly rather than routing through `modalApplyOneS5g`, since the v2 stepper no longer calls `modalApplyOneS5g` at all on the minting shapes; calling it on the remaining shapes would be a distinction without difference since `modalApplyOneS5g` reduces to `modalApplyOneS5` there anyway (`modalApplyOneS5g_eq_of_not_boxNeg_diaPos`). `modalApplyOneS5g` and its Phase 2 agreement lemmas remain untouched, valid reference artifacts, just no longer invoked from this stepper.)*
- [x] Reuse the landed `modalKnownWorlds_fold_spec_S5`/`mem_modalKnownWorlds_S5`/`modalKnownWorlds_mono_append_S5` re-derivations (committed `21b4ec03`).

**Timing**: 2.5 hours

**Depends on**: 2 (landed)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — `blockingWorldS5Keyed` (+ `_none_fresh`), extended ten-field `S5LoopInv`, updated `modalStepBranchS5gKeyed`

**Verification**: full CI pipeline green; the extended structure typechecks; `blockingWorldS5Keyed_none_fresh` closes sorry-free; the keyed stepper's non-minting arms remain definitionally aligned with `modalApplyOneS5g` (so the P2 agreement lemmas and non-minting bridges are undisturbed).

---

### Phase 4: Generic-field preservation lemmas [BLOCKED]

**Goal**: Prove that a `modalStepBranchS5gKeyed` step preserves the six generic (rule-independent) `S5LoopInv` fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`). These are the bookkeeping invariants S4 never landed (it stopped at the structure). **No template — author from scratch, reusing FmpMeasure invariant primitives.**

**Tasks**:
- [ ] Prove `modalStepBranchS5g_preserves_bClosure` — new branch formulas stay in `modalUniverseS5 φ₀` (the S5 arms broadcast unwrapped bodies already in the universe; the mint case adds bodies confined by `bClosure` of the source). Consumes `modalUniverseS5_length_le` (P1). *(deviation: BLOCKED this dispatch (cycle 2) after landing Phase 6's pigeonhole bound and attempting to consume it. **Root cause identified**: `modalKnownWorlds_length_le_worldBoundS5` (Phase 6) bounds the *count* of known worlds, but placing a freshly-minted formula (label `modalNextWorld b`) into `modalUniverseS5 φ₀` needs a bound on the *numeric value* `modalNextWorld b ≤ modalWorldBoundS5 φ₀`, which requires an ADDITIONAL, currently-absent invariant connecting `modalMaxWorld b`'s value to `(modalKnownWorlds b).length` -- concretely, `modalMaxWorld b + 1 = (modalKnownWorlds b).length` (worlds are minted contiguously as `maxWorld + 1`, so known-world labels are exactly `{0, ..., modalMaxWorld b}` with no gaps, PROVIDED the branch is reachable from a singleton root by this driver's own step semantics). This is true and provable by induction (base case: singleton root branch, trivial; step case: blocked steps leave `b` unchanged so both sides are stable; minting steps append at label `modalNextWorld b = modalMaxWorld b + 1`, incrementing both `modalMaxWorld` and the known-world count by exactly 1), but it is a genuinely NEW invariant field not among `S5LoopInv`'s current 11 fields, requiring its own dedicated preservation lemma before `bClosure`'s mint case can close. Confirmed via targeted grep that no existing lemma in `FmpMeasure.lean`/`LoopChecking.lean`/`S5Simplification.lean` connects `modalMaxWorld`/`modalNextWorld`'s VALUE to `modalKnownWorlds`'s LENGTH (only `modalKnownWorlds_le_modalMaxWorld`, a one-directional per-element bound, exists). No `sorry` used; NOT attempted as a rushed/unsound shortcut. See handoff `02_phase4-bclosure-contiguity-gap.md` for the exact next-step recommendation (a 12th `S5LoopInv` field, e.g. `worldsContiguous : modalMaxWorld b + 1 = (modalKnownWorlds b).length`, proven preserved alongside the others).)*
- [x] Prove `modalStepBranchS5g_preserves_eNodup` -- landed sorry-free, direct case analysis on `modalStepBranchS5gKeyed`'s three-way dispatch (see `modalStepBranchS5gKeyed_expanded_shape` private helper). `_preserves_eClosure` remains *(deviation: same contiguity-gap blocker as `bClosure` above -- BLOCKED, not started, see handoff `02_phase4-bclosure-contiguity-gap.md`.)*
- [x] Prove `modalStepBranchS5g_preserves_accFresh` (reuse `accFreshInv` monotonicity) and `_preserves_accKnown` (reuse `accTargetsKnown` step lemmas; new/loop-back edges target known worlds) -- both landed sorry-free this dispatch (cycle 2), recovered from stashed WIP and fixed to build.
- [x] Prove `modalStepBranchS5g_preserves_outDegEq` -- landed sorry-free this dispatch (cycle 2). *(deviation: the stashed draft's final `rw [modalApplyOne_outDeg_step ..., ← modalApplyOneS5_eshape_eq ...]` failed with a "did not find pattern" error caused by Lean's per-declaration match-auxiliary-function identity -- two syntactically identical `match ... with` expressions in different lemma statements compile to distinct matcher constants, which `rw`'s kabstract cannot unify even though `exact`/term-mode elaboration can via defeq. Fixed by bridging the two lemmas' matches through a `have hfull := (modalApplyOne_outDeg_step ...).trans (congrArg (fun l => ...) (modalApplyOneS5_eshape_eq ...).symm)` term composition (which type-checks via `isDefEq`, not syntactic rw), then `rw [hfull]` and case-splitting cleanly. Also required an `omit [Hashable Atom] in` before the lemma to clear a new `unusedSectionVars` warning caught by `lake shake`.)*

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — six `modalStepBranchS5g_preserves_*` generic-field lemmas

**Verification**: full CI pipeline green; all six generic-field preservation lemmas close sorry-free.

**Blocked-branch**: if a generic-field preservation resists within budget (most likely `accKnown` under the universal re-broadcast), mark `[BLOCKED]` with the exact `lean_goal` open state at the failing step, preserve P1-P3 + whatever generic fields did land, and defer P5. No `sorry`.

---

### Phase 5: Birth-key preservation lemmas (the `keysDistinct` crux) [NOT STARTED]

**Goal**: Prove that a `modalStepBranchS5gKeyed` step preserves the four birth-key fields, using the corrected keys-aware guard. **`keysDistinct` is the deep v1 blocker; it is now discharged directly by `blockingWorldS5Keyed_none_fresh`.**

**Tasks**:
- [ ] Prove `modalStepBranchS5g_preserves_keysDistinct` — keys never change on any step; on a *minting* step the fresh key is `≠` every stored key by `blockingWorldS5Keyed_none_fresh` (P3), so distinctness is preserved. **This is the fix for the v1 design gap** (cf. S4 analogue `modalStepBranchS4_preserves_keysDistinct`, unbuilt in `LoopChecking.lean`; 511 report Section 4).
- [ ] Prove `modalStepBranchS5g_preserves_keyLowerBd` — birth keys never change, live relevant sets only grow (`relevantSetFinset_mono`), so `⊆` is preserved (monotone; survives the v1 Gap-1 collapse by construction).
- [ ] Prove `modalStepBranchS5g_preserves_keysTotal` — every newly-known world gets a recorded key; consumes `accKnown` (P3) feeding `modalApplyOne_knownWorlds_step` (`FmpMeasure.lean:2042`) for the label-provenance dichotomy.
- [ ] Prove `modalStepBranchS5g_preserves_keysInUniverse` — new keys `⊆ signedSubfmls φ₀`; consumes `bClosure` (P3) for the subformula-closure of inserted `(s,φ)` pairs.

**Timing**: 2.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — four `modalStepBranchS5g_preserves_key*` lemmas

**Verification**: full CI pipeline green; all four birth-key preservation lemmas close sorry-free; in particular `_preserves_keysDistinct` closes via the keys-aware guard contract with no live-set reasoning.

**Blocked-branch**: if `_preserves_keysDistinct` still resists (it should not, given the keys-aware guard), the most likely residual cause is a stepper/guard mismatch — mark `[BLOCKED]` with the exact `lean_goal` open state and the specific unmet hypothesis, preserve P1-P4, and defer P6. No `sorry`, no weakening of `keysDistinct` to saturated-worlds-only (the 511-documented false shortcut).

---

### Phase 6: Pigeonhole world bound [COMPLETED]

**Goal**: Prove the finite world bound `modalKnownWorlds_length_le_worldBoundS5` via the Mathlib pigeonhole lemmas, consuming the corrected `S5LoopInv` key fields. **No template — the pigeonhole S4 also never landed (511 Section 5).**

**Tasks**:
- [x] Prove `modalKnownWorlds_length_le_worldBoundS5` -- landed sorry-free this dispatch (cycle 2), as a **static** private-adjacent lemma taking `keysTotal`/`keysDistinct`/`keysInUniverse` directly as hypotheses on a fixed `(b, keys)` pair (per the resume-task's directive: no step-preservation reasoning needed). Used `Finset.card_le_card_of_injOn` + `List.toFinset_card_of_nodup` + the pre-existing `signedSubfmls_powerset_card_le` (`LoopChecking.lean`, reused as-is since `modalWorldBoundS5 φ₀` is definitionally `modalWorldBoundS4 φ₀`). *(deviation: used `List.toFinset_card_of_nodup` in place of the plan's suggested `List.Nodup.length_le_card`, which does not exist under that name in this Mathlib snapshot; the injection function is built via a classical dependent-if choice over `∃ k, (w,k) ∈ keys` rather than `Finset.card_powerset` directly, since the powerset cardinality bound was already available pre-proven.)*
- [x] Map each known world to its key via `keysTotal`; `keysDistinct` ⇒ injectivity (`hDistinct`/`hinj`); `keysInUniverse` ⇒ keys `∈ (signedSubfmls φ₀).powerset` (`hInUniv`/`hmapsto`); cardinality `2^(2·|Sf|) = modalWorldBoundS5 φ₀` via `signedSubfmls_powerset_card_le`.
- [x] Added `modalKnownWorlds_nodup_S5` (+ its `modalKnownWorlds_fold_nodup_S5` foldl-induction helper) as a local re-derivation of `FmpMeasure.lean`'s private `modalKnownWorlds_nodup` (unavailable cross-file), mirroring the file's existing `_S5`-suffixed local-re-derivation pattern.

**Timing**: 1.5 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — `modalKnownWorlds_length_le_worldBoundS5`

**Verification**: full CI pipeline green; the pigeonhole bound closes sorry-free against `modalWorldBoundS5`.

**Blocked-branch**: if the injectivity/subset feed from `S5LoopInv` to the Mathlib pigeonhole cannot close within budget, mark `[BLOCKED]` with the exact un-discharged `Finset.card_le_card_of_injOn` obligation, preserve P1-P5 + P7 green, and defer P8/P9. No `sorry`.

---

### Phase 7: Soundness bridge `modalTableauS5_sound` [NOT STARTED]

**Goal**: Land S5 soundness via a **new reachability-threading fuel-induction bridge**. The v1 blocker showed the existing `modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:728`) threads only `accFreshInv` and hands per-shape lemmas only direct-edge relatedness, insufficient for S5's whole-known-world propagation. **Independent of the termination chain (F5): forks after P1, runs parallel to P3-P6.**

**Tasks**:
- [ ] Author `modalExpandBranchesGen_closed_unsatIn_reachable` (or an S5-specialized variant) threading `∀ w ∈ modalKnownWorlds b, Relation.ReflTransGen (fun a c => acc.hasEdge a c) 0 w` alongside `accFreshInv` through the fuel induction, reusing `modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean:193`) as a black box for the satisfiability half.
- [ ] Prove a new single-step reachability-preservation lemma: a `modalApplyOneS5` step keeps "every known world `acc`-reachable from 0" (use the landed `modalS5BoxAll_mem`/`modalS5DiaNegAll_mem` from P1 for the non-mint universal arms — target labels are `∈ modalKnownWorlds b` — and `modalApplyOne_fresh_local` (`FmpMeasure.lean:802`) for the mint case).
- [ ] Prove per-shape `modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn` under `s5FC`, re-deriving `m.r (f lbl) (f w')` from the reachability witness via `s5FC`'s `Std.Refl`/`Relation.RightEuclidean` cluster-collapse projections (not direct `hacc`).
- [ ] Assemble `modalTableauS5_sound` against the already-landed unguarded `modalApplyOneS5`/`modalTableauS5` (task 504), using `(modalApplyOneS5 sf b acc).snd = (modalApplyOne sf b acc).snd` (unconditional; every match arm returns K's `kAcc`) so the `freshLocal`-style dichotomy reduces to `modalApplyOne_fresh_local`. Mirror `modalTableauT_sound` (`FrameCompleteness.lean:1182`).

**Timing**: 2 hours

**Depends on**: 1 (landed)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — `modalExpandBranchesGen_closed_unsatIn_reachable`, the reachability-preservation lemma, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn`, `modalTableauS5_sound`

**Verification**: full CI pipeline green; `modalTableauS5_sound` closes sorry-free with the reachability bridge and the two `soundIn` lemmas.

**Blocked-branch**: if the reachability-threading bridge cannot close within budget, mark `[BLOCKED]` with the exact `lean_goal` open state at the failing induction step; this does not block the termination chain (P3-P6) or the frontier. No `sorry`.

---

### Phase 8: Spec-free Hintikka lift + fuel + completeness + decidability [NOT STARTED]

**Goal**: Build the frontier capstone: the `S5LoopInv`-parametrized Hintikka lift replacing the rank-bound generic lift, the fuel bridge, completeness, and `Decidable (s5Valid φ)` against `Cube.S5`. **No template; the hard frontier (F4). HIGH risk — the primary `[BLOCKED]`/Strategy-2 candidate.**

**Tasks**:
- [ ] Author `modalExpandBranchesS5_hintikka`: the (extended) `S5LoopInv`-parametrized analogue of `modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:876`), generalizing its induction over `S5LoopInv` (world bound from P3/P6) instead of `ModalLoopInvGen` (rank). The Hintikka-forcing fields survive as standalone lemmas re-targeted at `modalUniverseS5` (D2), NOT as a `RuleApplicationSpec` instance. Note the keyed-stepper's minting decision must align with the lift's loop-back semantics (the keys-aware guard's soundness for loop-back edges is re-derived here).
- [ ] Fuel bridge (F6), Option (i) first: prove `modalExpMeasureS5 (modalUniverseS5 φ) … ≤ modalFuel φ` to keep the `modalTableauS5` surface (`Saturation.lean:363/366`). If domination is false (R7), Option (ii): define `modalTableauS5g` with `modalFuelS5` derived from `modalWorldBoundS5` (P1).
- [ ] Prove `modalTableauS5_complete` from the spec-free lift + fuel bridge.
- [ ] Prove `s5Valid_decides` and build `instDecidableS5Valid : Decidable (s5Valid φ)`, mirroring `instDecidableTValid` (`FrameCompleteness.lean:1281`) — routed through the loop-checking lift, not the rank spec.

**Timing**: 3 hours

**Depends on**: 6 (pigeonhole) and 3 (extended `S5LoopInv`)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalExpandBranchesS5_hintikka`, fuel bridge, `modalTableauS5_complete`, `s5Valid_decides`, `instDecidableS5Valid`
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — ONLY if a spec-free `LoopTermination` interface extension is required (F4/F9); otherwise untouched (do not edit the `RuleApplicationSpec` core)

**Verification**: full CI pipeline green; `instDecidableS5Valid` typechecks and evaluates; no `RuleApplicationSpec modalApplyOneS5` witness reintroduced; no rank axiom.

**Blocked-branch**: if `modalExpandBranchesS5_hintikka` cannot close within budget (R6), take the pre-authorized contingency in order: (1) mark P8 `[BLOCKED]` recording the exact `lean_goal` open state at the failing induction step; then (2) **Strategy 2 pivot (F8, pre-authorized)**: build `instDecidableS5Valid` via semantic bounded-model FMP — enumerate equivalence-relation models of size `≤ 2^(2·|Sf|)` over a `Fintype` and check refutation using the landed `extractModelS5` countermodel + a filtration truth lemma, bypassing the generic driver's termination entirely (Massacci Fact 9.1: S5 has polynomial single-cluster models). Strategy 2 does not depend on the spec-free lift. If neither closes sorry-free within budget, leave P8 `[BLOCKED]` with the open goal — never a `sorry`, never a re-added rank axiom (D2/D5).

---

### Phase 9: 5/KB5 validity + completeness [NOT STARTED]

**Goal**: Complete task 504 Phase 7: `fiveValid`/`kb5Valid` completeness via the landed semantic bridge. Low risk *given* P8.

**Tasks**:
- [ ] Prove `fiveValid` completeness via `Satisfies.five` (`Basic.lean:471`) + `extractModelS5_rightEuclidean` (`FrameCompleteness.lean`, landed sorry-free by task 504).
- [ ] Prove `kb5Valid` completeness via `modalTableauS5_complete` (P8) + `extractModelS5_rightEuclidean` + the `RightEuclidean` bridges (`Euclidean.lean:236` `symm_rightEuclidean_iff_trans`, `refl_cod`/`equiv_cod`).
- [ ] Confirm the pure-K5/pure-5 case remains explicitly OUT OF SCOPE with the existing in-file note (`S5Simplification.lean:365-384`).

**Timing**: 1 hour

**Depends on**: 8

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `fiveValid`/`kb5Valid` completeness theorems

**Verification**: full CI pipeline green; both completeness theorems close sorry-free against `Cube.Five`/`Cube.S5`.

**Blocked-branch**: P9 is gated on P8. If P8 landed `[BLOCKED]` (or only Strategy-2 decidability without a full `modalTableauS5_complete`), mark P9 `[BLOCKED]` with the specific missing prerequisite (`modalTableauS5_complete`), or deliver only the `Satisfies.five`-direct `fiveValid` fragment that does not route through the tableau engine. No `sorry`.

## Artifacts & Outputs

Expected sorry-free, axiom-free Lean outputs (per phase):
- **P1 [COMPLETED]**: `s5FC`, `s5Valid`, `fiveFC`, `fiveValid`, `kb5FC`, `kb5Valid` (`FrameSoundness.lean`); `modalWorldBoundS5`, `modalUniverseS5`, `modalUniverseS5_length_le` (`S5Simplification.lean`).
- **P2 [COMPLETED]**: `successorBirthContentS5`, `blockingWorldS5` (+3 guard lemmas), `modalApplyOneS5g`, 6 agreement lemmas (`S5Simplification.lean`).
- **P3**: `blockingWorldS5Keyed` (+ `_none_fresh`), extended ten-field `S5LoopInv`, updated `modalStepBranchS5gKeyed` (`S5Simplification.lean`).
- **P4**: six `modalStepBranchS5g_preserves_*` generic-field lemmas (`S5Simplification.lean`).
- **P5**: four `modalStepBranchS5g_preserves_key*` birth-key lemmas (`S5Simplification.lean`).
- **P6**: `modalKnownWorlds_length_le_worldBoundS5` (`S5Simplification.lean`).
- **P7**: `modalExpandBranchesGen_closed_unsatIn_reachable`, reachability-preservation lemma, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn`, `modalTableauS5_sound` (`FrameSoundness.lean`).
- **P8**: `modalExpandBranchesS5_hintikka`, fuel bridge, `modalTableauS5_complete`, `s5Valid_decides`, `instDecidableS5Valid` (`FrameCompleteness.lean`; possibly `GenericDriver.lean` interface) — OR Strategy-2 semantic `instDecidableS5Valid`.
- **P9**: `fiveValid`/`kb5Valid` completeness theorems (`FrameCompleteness.lean`).
- Implementation summary at `specs/515_*/summaries/02_*-summary.md` on completion, with an honest per-phase status ledger (including any `[BLOCKED]`-with-open-goal entries).

## Rollback/Contingency

- **Per-phase revert**: each phase commits narrowly and independently; a failing phase is reverted with `git revert` of that phase's single commit without disturbing earlier green phases. Never `git reset --hard` without explicit user request.
- **Zero-debt contract (D2/D5)**: no phase lands a `sorry`, a re-added rank axiom, a `RuleApplicationSpec modalApplyOneS5` witness, or a `keysDistinct` weakened to saturated-worlds-only (the 511-documented false shortcut). If a sub-piece cannot close sorry-free, its phase is marked `[BLOCKED]` with the exact `lean_goal` open state, earlier green phases are preserved, and downstream phases are transitively `[BLOCKED]`.
- **Frontier isolation**: P7 (soundness) forks after P1 and is independent of P3-P6, so a termination-chain blockage still leaves P1-P6 (whatever landed) + P7 as concrete sorry-free progress.
- **Strategy 2 fallback (F8, pre-authorized)**: if the P8 loop-checking capstone resists, pivot `instDecidableS5Valid` to semantic bounded-model FMP over `extractModelS5` (equivalence-relation model enumeration `≤ 2^(2·|Sf|)` + filtration truth lemma), which bypasses the generic driver's termination and the unbuilt spec-free lift entirely. The sorry-free escape hatch, not a `sorry`.
- **Task-511 coordination (R1)**: if the keys-aware guard redesign proves broadly reusable, recommend either porting the P3-P6 pattern to S4 (task 511 Phase 5-7) as a follow-up or authorizing a shared `LoopTermination` interface consumed by both — avoiding duplicated guard-redesign effort across 511 and 515.
- **Escalation**: if both the loop-checking lift and Strategy 2 resist within budget, land the task `[PARTIAL]` with the termination chain + soundness green and P8/P9 `[BLOCKED]`-with-open-goal.
