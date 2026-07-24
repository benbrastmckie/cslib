# Research Report: Remaining Work + Phase 9 Obstruction Analysis

- **Task**: 535 - Abstract termination-measure interface for S4/B loop-checking driver
- **Status at research time**: `[PARTIAL]` (Phases 1-7 landed, Phase 8 not started, Phase 9 `[BLOCKED]`, Phases 10-11 transitively blocked)
- **Type**: cslib (Lean 4)
- **Date**: 2026-07-24
- **Purpose**: Identify exactly what remains and the most tractable route to completion, ahead of a plan revision. Research only — no implementation performed.
- **Grounding**: Every claim below is checked against current source (`git` clean on the four `Tableau` files, matching committed Phase 7 `1ce152b6`) and a fresh `lake build` run this dispatch.

## 1. Current State (verified, not summarized)

**Build**: `lake build Cslib.Logics.Modal.Tableau.LoopChecking` — **GREEN, exit 0, 847 jobs**, re-run this dispatch. The four file_scope files are byte-identical to the committed Phase 7 landing (working tree clean on `Cslib/Logics/Modal/Tableau/*`; all dirty files are under `specs/`).

**`sorry` / `admit` / errors**: **Zero** in code across all four file_scope files. The only `grep` hits for `sorry` are docstring prose mentions (not tactic blocks):
- `LoopChecking.lean:4619` — "All ten fields are now fully closed, zero sorry"
- `FrameCompleteness.lean:576` — "(sorry-free, **zero axioms**)"
- `GenericDriver.lean:62` — "confirmed sorry-free/axiom-free"

There are 8 pre-existing `unusedSimpArgs` lint warnings in `LoopChecking.lean` (lines ~2533/3054/3058/3120/3124/3145/3152, none in Phase 6-7 additions) — cosmetic, non-blocking, pre-date this task's phases.

**Landed declarations verified present** (line numbers current as of this dispatch):

| Phase | Declaration | Location |
|-------|-------------|----------|
| 1 | `modalExpandBranchesS4Keyed` / `modalTableauS4Keyed` | `LoopChecking.lean:4689` / `4747` |
| 1 | `modalStepBranchS4Keyed` (per-branch stepper) | `LoopChecking.lean:780` |
| 2 | `hintikka_congr_S4` (crux, unconditional) | `LoopChecking.lean:4767` |
| 3 | 4 private combinatorial primitives (`modalCount_notMem_append_drop_S4`, `_mono_S4`, `modalWork_drop_linear_S4`, `_persistent_S4`) | `LoopChecking.lean:4793`–`4904` |
| 4 | `modalApplyOneS4Keyed_persistentFresh_S4` / `_branchingLength_S4` / `_outputsSubsetUniverse_S4` (the three per-call obligations, ∀ keys) | `LoopChecking.lean:5270` / `5318` / `5371` |
| 5 | `modalFuelS4` + `modalExpMeasure_entry_le_fuelS4` | `LoopChecking.lean:285` / `5432` |
| 6 | `S4KeyedHintikkaInv` (structure) + `_weaken` + `_append` | `LoopChecking.lean:5691` / `5721` / `5888` |
| 6/7 | `modalStepBranchS4Keyed_blocked_witness_mem` | `LoopChecking.lean:5750` |
| 7 | `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` | `LoopChecking.lean:5949` |

**Confirmed absent (nothing exists anywhere in the codebase)**: `modalTableauS4Keyed_sound`, `modalTableauS4Keyed_complete`, `s4Valid_decides`, `instDecidableS4Valid`, and any `modalTableauS4_sound`/`modalTableauS4_complete`. There is **no S4 soundness, completeness, or decidability result of any kind** — for either the live `modalTableauS4` (`LoopChecking.lean:681`) or the keyed driver. `s4Valid` is defined (`FrameSoundness.lean:1051`: `frameValid s4FC φ`). The task's definition-of-done target `Decidable (s4Valid φ)` is genuinely open and cannot be reached by any existing bypass.

## 2. What Remains (smallest obligation set)

Four phases remain (8, 9, 10, 11). They split cleanly into two independent lines:

**Completeness/termination line (Phase 8 → 11-complete-half)** — does NOT depend on Phase 9:
- **Phase 8**: `modalExpandBranchesS4Keyed_hintikka` — top-loop induction proving an open branch from the keyed driver is a Hintikka set, bridged to `modalHintikkaSetS4` via `hintikka_congr_S4` (Phase 2) + `modalHintikkaSetS4_eq` (`LoopChecking.lean:3884`). Est. 250-400 lines; the single largest remaining phase. **All dependencies (3,4,5,7) are landed.**
- **Phase 11 (completeness half)**: `modalTableauS4Keyed_complete` — wires Phase 8 into `modalTruthLemmaS4` (`FrameCompleteness.lean:232`), `extractModelS4`+`_refl`/`_trans`/`_hasEdge_imp_r` (`FrameCompleteness.lean:143`–`188`), `modalOpenBranchS4_countermodel`. All wiring targets exist and are verified present.

**Soundness line (Phase 9 → 10 → 11-decidability-half)** — **BLOCKED at the root**:
- **Phase 9**: blocked-mint-redirect soundness lemma — `[BLOCKED]` (see §3).
- **Phase 10**: `modalTableauS4Keyed_sound` — soundness top-loop; depends on Phase 9.
- **Phase 11 (decidability half)**: `s4Valid_decides` + `instDecidableS4Valid` — needs BOTH soundness (Phase 10) and completeness (Phase 8/11); template is `s5Valid_decides`/`instDecidableS5Valid` and `modalTableauB_sound`+`instDecidableBValid` (`FrameCompleteness.lean:1877`/`1925`), both verified present.

**Smallest path to a *complete* task**: Phase 8 + Phase 9 + Phase 10 + Phase 11. There is no partial "done" — `instDecidableS4Valid` requires the full soundness+completeness dichotomy. **Phase 9 is therefore the true gate on task completion**, and it is currently a mathematical wall, not an engineering one.

## 3. Obstruction Analysis (the crux — verified against source)

The obstruction is **Phase 9**, and it is a **genuine soundness gap, not a proof-engineering difficulty**. I independently re-derived and confirmed the prior dispatch's diagnosis against source:

**The redirect** (`modalApplyOneS4Keyed` at the two minting shapes `F(□φ)@w` / `T(◇φ)@w`, `LoopChecking.lean:710-722`) emits `(.linear [], acc.addEdge sf.label wBlock)` — a bare accessibility edge `lbl → wBlock` with **no new branch formula** (wBlock already carries the required content, which is the point of blocking). Adding an edge is a soundness *hazard*: extra edges add constraints that can force a *satisfiable* root's tableau to close, which would be **unsound**. So the edge must be semantically justified: for any model `(W, m, f)` witnessing `branchSatisfiableIn s4FC` of the pre-step branch, we must show `m.r (f lbl) (f wBlock)`.

**Why it cannot be discharged from the frozen invariants**:
- `blockingWorldS4Keyed` (`LoopChecking.lean:469-474`) selects `wBlock` as `((keys.filter (·.2 = successorBirthContent …)).map Prod.fst).min?` — the least world (by recorded birth key) among **all** recorded worlds whose birth key matches. **There is no restriction to worlds reachable from `lbl` via `acc`.** wBlock is chosen purely by matching relevant-set content, anywhere in the branch.
- `s4FC := Std.Refl r ∧ IsTrans World r` (`FrameSoundness.lean:1047`) — **reflexive + transitive, NO symmetry**. Two worlds both reachable from a common ancestor are *not* in general related to each other under a merely reflexive-transitive relation (tree with two unrelated siblings is the standard countermodel).
- None of `S4LoopInv`'s ten fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`/`keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse`) relate `wBlock` to `lbl` by any accessibility path. `keyLowerBd` only lower-bounds a world's own key against its own relevant set; `keysDistinct` only separates distinct worlds' keys.

**Why the only in-codebase precedent does not transfer**: S5's witness-reuse rule `modalApplyOneS5w` is proved sound via `accReachableInv` / `reachable_imp_related_s5` / `accReachableInv_related_s5` (`FrameSoundness.lean:1432-1482`). That argument **crucially uses symmetry**: `s5FC := Std.Refl r ∧ Relation.RightEuclidean r` (`FrameSoundness.lean:1275`) lets two worlds both reachable from origin `0` be folded back through the origin into pairwise-relatedness. B's driver (`modalApplyOneB`) is on the Brouwerian (reflexive+symmetric) frame and, per its own docstring (`BDriver.lean:53`), **never mints a world at all** at its relevant shapes — so B is not a redirect precedent either. **S4 is the unique frame class here that (a) does world-reuse and (b) lacks symmetry.** The S5 technique structurally cannot transfer.

**Assessment of whether the redirect is even *true***: The current unrestricted guard makes `modalTableauS4Keyed_sound` **likely false as stated**, not merely hard — an edge `lbl → wBlock` to a same-content-but-unreachable world is not semantically forced in an arbitrary S4 model. Standard S4 loop-checking tableaux avoid exactly this by reusing only **ancestors on the current path** (which transitivity then makes genuinely `r`-related). The frozen `blockingWorldS4Keyed` does not restrict to reachable ancestors, so it does not match the standard *sound* loop-check.

## 4. Recommended Path (concrete)

The two remaining lines have very different tractability. Recommendation: **decouple them in the plan revision and dispatch Phase 8 immediately; escalate Phase 9's guard question as a scoped decision.**

### 4a. Phase 8 — dispatch now (tractable, unblocked)

Phase 8 is the highest-value immediately-actionable work. Concrete leads discovered this dispatch that de-risk it beyond the existing handoff map:

- **The measure-decrease sub-lemma may not need bespoke re-derivation.** The generic `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean`, called publicly from `GenericDriver.lean:528,548` as `modalExpMeasure_step_lt_gen apply spec.branchingLength spec.persistentFresh …`) takes exactly the **three raw hypotheses** that Phase 4 already landed as `modalApplyOneS4Keyed_{persistentFresh,branchingLength,outputsSubsetUniverse}_S4`. It is generic over the `apply` function. So Phase 8's fuel-decrease step can likely be obtained by instantiating `modalExpMeasure_step_lt_gen` at `modalApplyOneS4Keyed φ₀ keys` and feeding the three landed `_S4` obligations — rather than assembling a bespoke decrease from the Phase 3 primitives. **Verify the exact visibility/signature of `modalExpMeasure_step_lt_gen` first** (it is reached generically, so it is accessible; confirm it is not `private`).
- **Integration subtlety**: the keyed stepper `modalStepBranchS4Keyed` returns a **4-tuple with `keys'` bolted on**, unlike the generic `modalStepBranchGen` (3-tuple) the measure lemma is phrased over (`LoopChecking.lean:2797` already flags this). Phase 8 must bridge the measure over the `(branch, expanded, acc)` projection of the keyed stepper to `modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys)`. This is the main real work in the measure component.
- **Template**: `modalExpandBranchesHintikka` (`CompletenessLoop.lean:1430`). Per-index invariant is the **conjunction** `S4LoopInv φ₀ … keysᵢ ∧ S4KeyedHintikkaInv φ₀ … keysᵢ` (Phase 6 deliberately did not bundle S4LoopInv), threaded exactly as Phase 7's call-site convention already establishes.
- **Saturated-case witness**: use Phase 7's `modalStepBranchS4Keyed_blocked_witness_mem` + `S4KeyedHintikkaInv.eBoxNegWitness`/`eDiamondPosWitness` in place of the generic `RuleApplicationSpecCore`'s `boxNegWitness'`/`diaPosWitness'` (the keyed driver has no `RuleApplicationSpec` instance).
- **`_none_saturated`**: no S4Keyed analogue exists; mirror Phase 7's own `findSome?_eq_some` + `split_ifs at hsf with hexp` case-split idiom (NOT the generic `modalStepBranchGen_none_saturated`, `Completeness.lean:809`). Note the `Sign` constructor order `pos, neg` gotcha documented in the Phase 7 handoff.

Dispatch Phase 8 `--hard` (H8 phase-sizing, H9 wrap-up) given its 250-400-line size and Phase 7's experience that even a near-complete skeleton needed non-trivial defeq debugging.

### 4b. Phase 9 — the plan revision's central decision

Phase 9 cannot be discharged as scoped. Two routes, both requiring a decision the research/plan layer cannot make unilaterally (they change the plan's stated Non-Goals or its scope):

- **Route (i) — reachability-restricted guard (recommended, aligns with standard theory).** Revise `blockingWorldS4Keyed` (currently frozen task-511 code) to restrict redirect candidates to worlds already `acc`-reachable from `lbl` (`Relation.ReflTransGen acc.hasEdge lbl wBlock`, or the ancestor-on-path variant). This supplies `m.r (f lbl) (f wBlock)` directly at the point of selection via S4 transitivity — the standard sound S4 loop-check. **Cost**: (1) editing frozen `blockingWorldS4Keyed` (out of this plan's Non-Goals — needs `/revise` or a spawned task); (2) re-verifying that `keyLowerBd`/`keysDistinct`/`keysInUniverse` preservation and the Phase 6-7 invariants still hold under the narrower guard; (3) re-checking termination/fuel is unaffected (candidate set only shrinks, so the fuel bound should be safe, but the guard's `none`-freshness contract `blockingWorldS4_none_fresh` changes meaning and must be re-proved). Mathlib API: `Relation.ReflTransGen` and its `trans`/`refl`/`single` lemmas; `Relation.ReflTransGen.head`/`tail` for path extension.
- **Route (ii) — different soundness argument (higher risk).** Build the witnessing model directly from the tableau's own construction (canonical-model style) rather than closing over an arbitrary `branchSatisfiableIn` witness, so the redirect edge is true by construction. This is a larger re-architecture of the soundness statement and is not supported by any existing `branchSatisfiableIn_s4FC_*` lemma (`FrameSoundness.lean:1085,1106` cover only persistent 4-rule propagation, not redirect edges). Not recommended as first choice.

**Recommended plan-revision shape**: (1) mark Phase 8 as the immediate next dispatch (unblocked, decoupled from soundness); (2) convert Phases 9-11 into a follow-on scope that begins with Route (i)'s guard revision as an explicit, user-approved expansion of Non-Goals (touching task-511 `blockingWorldS4Keyed`), OR spawn a dedicated research task to validate Route (i)'s invariant-preservation obligations before committing. Do not attempt Phase 9 as currently written — it is a genuine mathematical wall under the frozen guard.

## Open Questions for the Planner

1. **Guard-edit authorization**: Route (i) requires editing frozen task-511 `blockingWorldS4Keyed`. This is a scope/ownership decision (task owner + `/revise`), not one the implementer can make under the current Non-Goals.
2. **`modalExpMeasure_step_lt_gen` reuse for Phase 8**: confirm its visibility and that instantiating it at the keyed `apply` with the three landed Phase-4 `_S4` obligations discharges the fuel-decrease, avoiding bespoke measure assembly.
3. **Does Route (i) preserve completeness?** Narrowing the blocking candidates changes which branches saturate; Phase 8's Hintikka argument (if landed first under the *current* guard) may need re-checking if the guard later changes. Consider whether to settle the guard question BEFORE landing Phase 8, to avoid re-work.
