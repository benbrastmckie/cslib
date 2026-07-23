# Research Report: Task #515 — S5 Universal-Rule Termination Implementation Blueprint

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Started**: 2026-07-15T00:00:00Z
- **Completed**: 2026-07-15T00:00:00Z
- **Effort**: ~2 hours (read-only source verification + literature-anchored synthesis)
- **Dependencies**: task 514 (literature grounding, anchor), task 504 (Phases 1/3 landed assets),
  task 511 (`LoopChecking.lean` S4 scaffolding)
- **Sources/Inputs**:
  - `specs/514_*/reports/01_s5-termination-literature-grounding.md` (anchor recommendation)
  - `specs/504_*/summaries/01_*.md` and `specs/504_*/plans/01_*.md`
  - Lean sources (read-only, verified): `Cslib/Logics/Modal/Tableau/{S5Simplification,
    GenericDriver,FrameCompleteness,FrameSoundness,LoopChecking,CompletenessLoop,Saturation,
    FmpMeasure}.lean`; `Cslib/Logics/Modal/{Basic,Cube}.lean`;
    `Cslib/Foundations/Relation/Euclidean.lean`
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: `S5Simplification.lean` (rule + driver + obstruction, landed),
  `FrameCompleteness.lean` (`extractModelS5` + `RightEuclidean`, landed), `LoopChecking.lean`
  (S4 loop-checking scaffolding, **partial**), `CompletenessLoop.lean`
  (`modalExpandBranchesGen_hintikka`, `ModalLoopInvGen`, spec-bound), `Saturation.lean`
  (`modalTableauGen`, `modalFuel`), `FmpMeasure.lean` (`modalUniverse`, `modalExpMeasure`),
  `GenericDriver.lean` (`RuleApplicationSpec`), `Basic.lean` (`Satisfies.five`),
  `Euclidean.lean` (`RightEuclidean` API), `Cube.lean` (`Cube.S5`, `Five`).
- **Downstream Dependents**: task 504 Phases 4/5/6/7 (S5/KB5/5 decidability + completeness).
- **Alternative Paths**: semantic bounded-model FMP (Strategy 2) bypassing the tableau driver.
- **Potential Extensions**: a shared `LoopTermination` interface consumed by S4 and S5 alike.

## Executive Summary

- **Decision (objective 1): implement path (b) bespoke termination via loop-checking; path (a)
  restricted rank-compatible rule is RULED OUT.** Any S5 rule achieving equivalence-closure
  reachability must propagate transitively/universally, which is *precisely* what breaks the
  per-edge `rankStep` decrement — the mechanized obstruction
  (`modalApplyOneS5_rankStep_not_dischargeable`, S5Simplification.lean:342) generalizes to *every*
  transitive/euclidean rule, exactly as S4's own 4-rule is documented not to be a
  `RuleApplicationSpec` instance (GenericDriver.lean:126). This confirms task 514's recommendation.
- **CRITICAL CORRECTION to the 514 anchor report.** The 514 report characterizes
  `LoopChecking.lean` (S4) as a *complete, sorry-free, transposable template*
  ("mirror this file declaration-for-declaration"). **This is inaccurate.** `LoopChecking.lean`
  ends at the `S4LoopInv` **structure definition** (line 1127-1152). The preservation lemmas
  (`_preserves_key*`), the pigeonhole bound `modalKnownWorlds_length_le_worldBoundS4`, the
  fuel-sufficiency lemma, and any `Decidable (s4Valid ...)` instance **DO NOT EXIST** — they are
  named only in docstrings as unbuilt "Phase 5/6" work. There is **no `s4Valid` decidability
  instance** anywhere; only K, T, B are decidable (`instDecidableKValid/TValid/BValid`). S4 is
  blocked at the *same wall* S5 must cross.
- **The wall is the spec-bound generic lift.** `modalExpandBranchesGen_hintikka`
  (CompletenessLoop.lean:876) — the *only* lemma that turns an open tableau branch into a Hintikka
  set — **requires `spec : RuleApplicationSpec apply`** and threads `ModalLoopInvGen` (rank).
  Completeness (`modalTableauT_complete`) also needs `modalExpMeasure_entry_le_fuel` (rank-based
  fuel sufficiency). **Neither has a loop-checking/world-bound variant.** No `LoopTermination`
  interface exists (grep-verified). Task 515's hard phases must *build* this replacement, not
  reuse it.
- **Good news for Phase 5 (soundness).** `modalTableauT_sound` (FrameCompleteness.lean:1182)
  consumes only `spec.freshLocal`, per-shape `soundIn` lemmas, and the agreement lemma —
  **never `rankStep`**. S5 can supply `freshLocal` (its accessibility output is exactly K's). So
  `modalTableauS5_sound` is achievable *now*, independent of the termination breakthrough.
- **New definitional gaps (not flagged by 514).** `s5FC`, `s5Valid`, `fiveValid`, `kb5Valid`, and
  the per-shape S5 soundness lemmas (`modalS5BoxAll_soundIn`) **do not exist yet** and must be
  authored. `modalTableauGen` **hardwires K's `modalFuel φ`** (Saturation.lean:363/366), so a
  terminating S5 procedure needs either a proof that `modalFuel` dominates the S5 world-bounded
  expansion measure, or a new fuel-parametrized entry point.
- **Zero-debt posture: this task will likely land [PARTIAL].** Phases 4/6 (completeness +
  decidability) are gated on a novel spec-free termination lift that S4 has not built. Recommend
  scoping task 515 to deliver the *achievable* sorry-free sub-goals (frame class, soundness,
  guard + loop invariant + preservation + pigeonhole) and marking the decidability capstone
  [BLOCKED] with the exact open goal if the spec-free lift cannot close within budget — **not**
  a `sorry` and **not** a re-introduced rank axiom.

## Context & Scope

Task 515 implements the terminating S5 tableau machinery task 514 recommended, to unblock task
504's Phases 4/5/6/7. The rank route is PROVEN inapplicable (do not re-attempt). This report
verifies task 514's recommendation against the actual Lean sources, corrects its reuse
assumptions, and delivers a lemma-level, phase-sized blueprint with exact signatures, file
targets, and reuse verdicts. Research is read-only; no Lean files were edited.

## Findings

### F1 — Decision: path (b) loop-checking; path (a) is impossible [confirms 514]

- **Path (a) — a restricted, rank-compatible S5 rule with full equivalence-closure reachability —
  is ruled out.** The `rankStep` field (GenericDriver.lean:105-118) demands a rank witness with a
  per-edge decrement `acc.hasEdge w w' → rank w' + 1 = rank w` and a depth bound. Full
  equivalence-closure reachability requires content to reach worlds not edge-controlled by the
  trigger (transitively/universally). The mechanized counterexample makes this concrete: it is not
  "unproven", it is `¬∃ rank'` closed by `rfl`+`omega` (S5Simplification.lean:342-361). Any rule
  strong enough for S5 completeness inherits this obstruction, exactly as S4's transitive 4-rule
  does (GenericDriver.lean:126 "S4 is explicitly NOT an instance"). A "restricted" rule that stayed
  rank-compatible would be too weak to reach the whole cluster — it would fail completeness, not
  termination.
- **Path (b) — bespoke termination not routed through `rankStep` — is the only viable route**, and
  within (b), task 514's Strategy 1 (loop-checking world bound, Massacci2000 Technique 8.3 +
  Table IV + "works for K45 and S5", chunk 35) is the recommended primary. Strategy 2 (semantic
  filtration/bounded-model FMP) is the fallback (see F8).

### F2 — Reuse reality: what `LoopChecking.lean` actually provides [CORRECTS 514]

Grep-verified declaration frontier of `LoopChecking.lean` (S4, task 511):

| Asset | Exists? | Line | Reuse for S5 |
|---|---|---|---|
| `modalWorldBoundS4 := 2^(2·|modalSubfmls φ₀|)` | YES | 229 | Template for `modalWorldBoundS5` |
| `modalUniverseS4` + `_length_le` | YES | 235/245 | Template for `modalUniverseS5` |
| `signedSubfmls` + card lemmas | YES | 290/298/313 | **Reuse verbatim** (φ₀-parametric, rule-independent) |
| `relevantSetFinset` + `_mono`/`_subset` | YES | 323/333/344 | **Reuse verbatim** |
| `successorBirthContent` | YES | 374 | Template for `successorBirthContentS5` |
| `blockingWorldS4` + 3 guard lemmas | YES | 391/399/413/426 | Template for `blockingWorldS5` |
| `modalApplyOneS4` (guarded rule) + eq lemmas | YES | 461/479-522 | Template for `modalApplyOneS5g` |
| `modalStepBranchS4`/`modalExpandBranchesS4`/`modalTableauS4` | YES | 538/548/558 | Template (but see F6 fuel) |
| Hintikka forcing lemmas `hintikkaS4_*` | YES | 631-1109 | Template for `hintikkaS5_*` |
| `S4LoopInv` **structure** | YES | 1127 | Template for `S5LoopInv` |
| `_preserves_key*` preservation lemmas | **NO** | — | **Must be authored (no template)** |
| `modalKnownWorlds_length_le_worldBoundS4` pigeonhole | **NO** | — | **Must be authored (no template)** |
| Fuel-sufficiency-from-world-bound lemma | **NO** | — | **Must be authored (no template)** |
| `Decidable (s4Valid φ)` | **NO** | — | **Must be authored (no template)** |

Consequence: task 515 can *transpose* the scaffolding (bound, universe, guard, guarded rule,
Hintikka forcing lemmas, loop-invariant structure) but must *invent* the termination capstone
(preservation → pigeonhole → spec-free lift → fuel → decidability) that S4 never built. This is
the single most important planning fact and directly determines the risk register (F9).

### F3 — The rule as landed, and where divergence actually enters

- `modalApplyOneS5` (S5Simplification.lean:153): for the two S5 shapes (`T(□φ)@w`, `F(◇φ)@w`) it
  merges universal-propagation formulas into K's `.persistent` output at **existing known worlds**
  and leaves `acc` = K's `kAcc` unchanged (never mints in these arms). Outside the two shapes it is
  exactly `modalApplyOne` (agreement lemma `modalApplyOneS5_eq_of_not_boxPos_diaNeg`, l.181).
- **Divergence source (accurate mechanism).** The universal dia-negative arm broadcasts
  `F(φ)@w'` to all known `w'`. When `φ = □χ`, each emitted `F(□χ)@w'` is a *box-negative shape*;
  when the driver later processes it, the **K arm** mints a fresh world (K's `boxNeg`/`diaPos`
  witnesses). The new world re-enters `modalKnownWorlds`, so universal box-positives re-broadcast to
  it → potentially another mint. Absent a blocking guard this cascade is unbounded. The 514 report's
  Gap-1/Gap-2 analogy is correct; note the mint happens in the **K arm**, not in `modalS5*All`.
- **The file's own optimism is the bug.** `modalTableauS5` docstring (l.213) asserts "S5 never
  mints a world outside the K diamondPos/boxNeg arms, so `modalFuel` is sufficient here too." The
  *minting* claim is true, but *sufficiency of K's `modalFuel`* is exactly what the cascade above
  refutes: K's fuel is depth-based and does not bound the universal re-broadcast. Task 515 must
  replace this with a world-bounded fuel argument (F6).

### F4 — The completeness wall: `modalExpandBranchesGen_hintikka` is spec-bound [key blocker]

- `modalExpandBranchesGen_hintikka` (CompletenessLoop.lean:876) has signature
  `(apply) (spec : RuleApplicationSpec apply) (φ0) (fuel) → … → modalExpMeasure (modalUniverse φ0)
  … ≤ fuel → (∀ i …, ∃ rank, ModalLoopInvGen apply φ0 bi ei ai rank) → … → modalHintikkaSetGen`.
  It **requires the full `RuleApplicationSpec`** (hence `rankStep`) and a per-branch
  `ModalLoopInvGen` rank witness (structure at CompletenessLoop.lean:133). S5 cannot supply either.
- `modalTableauT_complete` (FrameCompleteness.lean:1222) shows the exact consumption pattern:
  it instantiates the lift with `modalApplyOneT_spec`, `hInv := ⟨fun _ => modalDepth φ0,
  modalLoopInvGen_initial …⟩`, and `hmeas := modalExpMeasure_entry_le_fuel φ0`. Both `hInv` and
  `hmeas` are rank-based.
- **No spec-free / loop-parametrized lift exists** (grep for `LoopTermination`, loop-based hintikka
  variants: none). Therefore Phase 4/6 require a *new* generic (or S5-local) lemma
  `modalExpandBranchesS5_hintikka` whose termination hypothesis is `S5LoopInv` (world bound), not
  `ModalLoopInvGen` (rank). This lemma is the crux deliverable and has **no existing template** —
  S4 stopped before building its analogue.

### F5 — Phase 5 (soundness) is achievable independent of termination [good news]

- `modalTableauT_sound` (FrameCompleteness.lean:1182) is built from
  `modalExpandBranchesGen_closed_unsatIn` fed: `modalApplyOneT_spec.freshLocal` (only that field),
  the agreement lemma `hAgreeT`, and two per-shape `soundIn` lemmas
  (`modalApplyOneT_boxPos_soundIn`, `modalApplyOneT_diaNeg_soundIn`). **`rankStep` is never used.**
- S5 supplies `freshLocal` trivially: `modalApplyOneS5` returns K's `kAcc` unchanged in the S5
  arms and equals `modalApplyOne` elsewhere, so world-creation confinement is exactly K's.
- **New soundness obligation and a subtlety the planner must budget for.** The per-shape lemma
  `modalS5BoxAll_soundIn` must prove: in any model satisfying the branch under `s5FC` (equivalence
  frame), `T(□φ)@w` satisfied ⇒ `T(φ)@w'` satisfied for every *known* `w'`. This needs
  `m.r (f w) (f w')`. In an arbitrary equivalence frame that does **not** hold for unrelated
  worlds — it holds because every known world is reachable from world 0 via recorded edges (mint
  tree), and an equivalence/transitive+symmetric+reflexive frame collapses that reachable set into
  one cluster (`f 0 R f w'` for all known `w'`, hence `f w R f w'`). So the soundness proof needs
  a **branch invariant "every known world is `acc`-reachable from 0"** plus the `s5FC` equivalence
  projections. Tractable, but genuinely new content (the K/T/B soundness proofs do not need it).

### F6 — Fuel wiring: `modalTableauGen` hardwires `modalFuel`

- `modalTableauGen apply φ = modalExpandBranchesGen apply [initialBranch] [[]] [empty]
  (modalFuel φ)` (Saturation.lean:363-366). `modalFuel φ` (Saturation.lean:98) is a triple-
  exponential over `modalComplexity φ`, *sufficient for K's depth measure only*.
- `modalTableauS5` currently reuses `modalFuel φ`. For a terminating S5 procedure the planner must
  either (i) prove `modalExpMeasureS5 (modalUniverseS5 φ) … ≤ modalFuel φ` (a domination lemma
  bridging the world-bounded measure to K's fuel — plausible since both are large closed forms but
  requires the pigeonhole first), or (ii) define a new `modalTableauS5g` entry with a
  world-bound-derived fuel `modalFuelS5 φ`. Option (i) keeps the existing `modalTableauS5` surface;
  Option (ii) is cleaner but adds a new driver entry. Recommend (i) if the domination is provable,
  else (ii). This choice is downstream of the pigeonhole (F2 gap) and belongs in the plan.

### F7 — Phase 7 assets (5/KB5) are landed and the semantic bridge is clean

- `Satisfies.five` (Basic.lean:471): `[Relation.RightEuclidean m.r] → ⇓Modal[m,w ⊨ ◇φ → □◇φ]`.
  Converse `Satisfies.five_rightEuclidean` (l.482). Both landed.
- `Euclidean.lean` provides `symm_rightEuclidean_iff_trans` (l.236), `refl_cod`/`equiv_cod`,
  and the `RightEuclidean`/`LeftEuclidean` ↔ trans bridges. `Cube.Five := {m | RightEuclidean
  m.r}` and `Cube.S5 := K ∪ T ∪ Four ∪ Five` (Cube.lean:45/85).
- `extractModelS5` + `extractModelS5_equiv` + `extractModelS5_rightEuclidean` +
  `instIsEquivEqvGen` (FrameCompleteness.lean:491-565) are landed sorry-free (task 504 Phase 3).
  The Euclidean frame condition is obtained "for free" from the `EqvGen` equivalence closure.
- Phase 7 is therefore *gated only* on the S5 tableau completeness engine (F4). Once
  `modalTableauS5_complete` exists, `fiveValid`/`kb5Valid` completeness follows via `Satisfies.five`
  + `extractModelS5_rightEuclidean`. The pure-K5/pure-5 (Euclidean-without-equivalence) case
  remains explicitly OUT OF SCOPE (S5Simplification.lean:365-384; no Mathlib `EuclGen` closure).

### F8 — Strategy 2 (semantic FMP) as the honest fallback

Given F4 (the spec-free lift is unbuilt for S4 too), the bounded-model-search decision procedure
deserves elevation from "not recommended" to "serious fallback". `extractModelS5` already yields an
equivalence-closure countermodel; a `Decidable (s5Valid φ)` could instead enumerate models of size
≤ `2^(2|Sf|)` over an equivalence relation and check refutation, bypassing the generic driver's
termination entirely (Massacci Fact 9.1: S5 has polynomial single-cluster models). This is a
*different* decision procedure (needs a `Fintype` model enumeration + a filtration truth lemma) and
does not reuse the S4 infrastructure — but it does not depend on inventing the spec-free lift. If
the loop-checking capstone (F2 gap) proves intractable within budget, Strategy 2 is the escape
hatch rather than a `sorry`.

### F9 — Coexistence / regression: zero risk to K/T/B

K/T/B keep `modalApplyOne`/`modalApplyOneT`/`modalApplyOneB` and their `RuleApplicationSpec`
witnesses untouched. The S5 guard/invariant/preservation/pigeonhole live in a new file or new
section (recommend new `S5LoopChecking.lean` mirroring `LoopChecking.lean`), consuming the
φ₀-parametric reusable engine (`signedSubfmls`, `relevantSetFinset`, `modalExpMeasure`,
`modalUniverse` counting). No edit to `GenericDriver.lean`'s spec, `FmpMeasure.lean`, or the K/T/B
declarations. No new notation, no new axiom.

## Decisions

- **D1**: Implement path **(b) bespoke loop-checking termination**; do not attempt path (a) or
  re-attempt the rank/B-T mirror (F1).
- **D2**: `modalApplyOneS5_spec : RuleApplicationSpec modalApplyOneS5` is **permanently
  abandoned** (rankStep provably false). It is *not* replaced by another `RuleApplicationSpec`
  witness. The replacement is an `S5LoopInv`-parametrized termination bundle + a spec-free
  Hintikka lift `modalExpandBranchesS5_hintikka` (F4). `freshLocal`/`persistentFresh`/`outDegStep`
  and the F8-F12 Hintikka forcing fields survive as *standalone lemmas* re-targeted at
  `modalUniverseS5`, not as a `RuleApplicationSpec` instance.
- **D3**: Define the missing frame surface: `s5FC := fun r => Std.Refl r ∧ Relation.RightEuclidean
  r` (equivalent to reflexive + euclidean = equivalence), `s5Valid := frameValid s5FC`, and
  `fiveValid`/`kb5Valid` per the Cube classes. (F7)
- **D4**: Phase 5 (soundness) proceeds immediately via `freshLocal` + new per-shape `soundIn`
  lemmas + the "known-worlds reachable-from-0" branch invariant; it does not wait on termination
  (F5).
- **D5**: Treat the completeness/decidability capstone as the high-risk frontier. If the spec-free
  lift or pigeonhole cannot close sorry-free within budget, land [BLOCKED] with the exact open goal
  and either (a) hand off to the shared-interface decision or (b) pivot the decidability proof to
  Strategy 2 (F8). Never `sorry`, never re-add a rank axiom (D2).

## Recommendations (phase breakdown, planner-sized ≈ one agent run each)

Ordered; each phase is independently CI-green and committable. Phases P1-P3, P5 are
achievable with existing templates/assets; P4, P6, P7-cap are the frontier.

- **P1 — Frame surface + S5 bound + universe.** New `S5LoopChecking.lean`. Define `s5FC`,
  `s5Valid`, `fiveValid`, `kb5Valid` (FrameSoundness.lean home, mirror `s4FC`:1044); `modalWorldBoundS5`,
  `modalUniverseS5`, `modalUniverseS5_length_le` (mirror LoopChecking.lean:229/235/245). Reuse
  `signedSubfmls`/`relevantSetFinset` verbatim. Low risk.
- **P2 — Guard + guarded rule.** `successorBirthContentS5`, `blockingWorldS5` (+ 3 guard lemmas),
  `modalApplyOneS5g` (route the K minting shapes through the guard, universal arms unchanged), and
  the agreement lemmas vs `modalApplyOneS5`/K. Mirror LoopChecking.lean:374-522. Medium risk
  (guard interaction with universal arms).
- **P3 — `S5LoopInv` + preservation lemmas.** Define `S5LoopInv` (mirror `S4LoopInv`:1127) and
  prove `modalStepBranchS5_preserves_key{LowerBd,Distinct,Total,InUniverse}`. **No template — this
  is the S4-unbuilt crux.** Budget generously. Medium-high risk.
- **P4 — Pigeonhole world bound.** `modalKnownWorlds_length_le_worldBoundS5` via `Finset.card_powerset`
  + `Finset.card_le_card_of_injOn` + `List.Nodup.length_le_card` (Mathlib, confirmed used by task
  511). Consumes `S5LoopInv.keysDistinct`/`keysInUniverse`. **No template.** High risk (this is the
  pigeonhole S4 also never landed).
- **P5 — Soundness `modalTableauS5_sound`.** Per-shape `modalS5BoxAll_soundIn`/`modalS5DiaNegAll_soundIn`
  under `s5FC` + the "known-worlds reachable-from-0" branch invariant; assemble via
  `modalExpandBranchesGen_closed_unsatIn` + `freshLocal` (mirror `modalTableauT_sound`:1182).
  **Independent of P3/P4** — can run in parallel. Medium risk (the reachability invariant is new).
- **P6 — Spec-free Hintikka lift + fuel + completeness + decidability.** Author
  `modalExpandBranchesS5_hintikka` (the `S5LoopInv`-parametrized analogue of
  `modalExpandBranchesGen_hintikka`), the fuel bridge (F6: dominate `modalFuel` or new
  `modalFuelS5`), `modalTableauS5_complete`, `s5Valid_decides`, and `instDecidableS5Valid`
  (mirror `instDecidableTValid`:1281). **No template; the hard frontier.** HIGH risk — candidate
  for [BLOCKED] handoff or Strategy 2 pivot (D5).
- **P7 — 5/KB5 validity + completeness.** `fiveValid`/`kb5Valid` completeness via `Satisfies.five`
  + `extractModelS5_rightEuclidean` (both landed). Gated only on P6. Low risk *given* P6.

Suggested parallelization: P1→P2→P3→P4 is the termination chain; P5 forks after P1; P6 joins P4;
P7 follows P6.

## Risks & Mitigations

- **R1 (highest) — the spec-free lift (P6) has no template and S4 never built it.** The 514
  report's "transpose a finished template" framing understates this. Mitigation: sequence P6 last;
  attempt `modalExpandBranchesS5_hintikka` by generalizing `modalExpandBranchesGen_hintikka`'s
  induction over `S5LoopInv` instead of `ModalLoopInvGen`; if it resists, land [BLOCKED] with the
  exact open goal and pivot decidability to Strategy 2 (F8). Coordinate with any S4
  `LoopTermination` interface effort — do not duplicate.
- **R2 — pigeonhole (P4) is genuinely new proof work.** Mitigation: reuse the Mathlib pigeonhole
  lemmas task 511 already imported; the `S5LoopInv` key fields are designed (in the S4 docstrings)
  precisely to feed this argument.
- **R3 — soundness reachability invariant (P5).** The universal rule's soundness needs "all known
  worlds reachable from 0" + `s5FC` cluster collapse (F5). Mitigation: prove the reachability
  invariant as a standalone branch lemma (it is a driver-level fact, not S5-specific) before the
  per-shape `soundIn` lemmas.
- **R4 — fuel domination (F6) may be false.** If `modalFuel φ` does *not* dominate the S5
  world-bounded measure, `modalTableauS5` (which hardwires `modalFuel`) is not obviously
  terminating-complete. Mitigation: define `modalTableauS5g` with `modalFuelS5` derived from
  `modalWorldBoundS5` (Option ii, F6).
- **R5 — scope realism.** Delivering *all* of P1-P7 sorry-free in one task is optimistic given the
  S4 precedent (S4 stopped at P3-equivalent). Mitigation: define task success as P1-P3 + P5 landed
  green (concrete, sorry-free progress), with P4/P6/P7 pursued and honestly [BLOCKED]-flagged if
  they resist — matching task 504's zero-debt discipline.

## Context Extension Recommendations

- **Topic**: Shared loop-checking termination interface for transitive/euclidean modal tableaux.
  **Gap**: Both S4 (`LoopChecking.lean`) and S5 need a `RuleApplicationSpec`-free Hintikka lift and
  a world-bound fuel argument; neither exists, and the 514 report assumed the S4 one was complete.
  **Recommendation**: capture (in `.memory/` or a project note) that `LoopChecking.lean` is
  scaffolding-only (ends at `S4LoopInv`) and that the termination capstone is unbuilt for the whole
  transitive/euclidean family — to prevent future tasks from repeating the "transpose a finished
  template" assumption.

## Appendix — References

- **Massacci2000** — Single Step Tableaux for Modal Logics, JAR 24(3), 2000. Technique 8.3,
  Table IV, Facts 9.1/9.3 (via task 514 report; BibKey in `references.bib`).
- **Gore1999**, **ChagrovZakharyaschev1997**, **Fitting1983** — as cited in the 514 report.
- Verified Lean identifiers (exact, do not invent): `modalApplyOneS5`,
  `modalApplyOneS5_rankStep_not_dischargeable`, `modalS5BoxAll`, `modalS5DiaNegAll`,
  `modalApplyOneS5_eq_of_not_boxPos_diaNeg`, `modalStepBranchS5`, `modalTableauS5`,
  `RuleApplicationSpec` (+ fields `freshLocal`, `rankStep`, `outputsSubsetUniverse`),
  `modalExpandBranchesGen_hintikka`, `ModalLoopInvGen`, `modalTableauGen`, `modalFuel`,
  `modalExpMeasure`, `modalUniverse`, `modalExpMeasure_entry_le_fuel`, `modalTableauT_sound`,
  `modalTableauT_complete`, `tValid_decides`, `instDecidableTValid`, `modalWorldBoundS4`,
  `modalUniverseS4`, `signedSubfmls`, `relevantSetFinset`, `blockingWorldS4`,
  `successorBirthContent`, `S4LoopInv`, `extractModelS5`, `extractModelS5_equiv`,
  `extractModelS5_rightEuclidean`, `instIsEquivEqvGen`, `Satisfies.five`, `s4FC`, `frameValid`,
  `Cube.S5`, `Cube.Five`, `Relation.EqvGen`, `Relation.RightEuclidean`,
  `symm_rightEuclidean_iff_trans`.
- Confirmed NON-existent (must be authored): `s5FC`, `s5Valid`, `fiveValid`, `kb5Valid`,
  `modalApplyOneS5_spec`, `modalWorldBoundS5`, `modalUniverseS5`, `blockingWorldS5`,
  `modalApplyOneS5g`, `S5LoopInv`, any `_preserves_key*S4/S5`,
  `modalKnownWorlds_length_le_worldBoundS4/S5`, `modalExpandBranchesS5_hintikka`,
  `modalTableauS5_sound`, `modalTableauS5_complete`, `instDecidableS5Valid`, and any
  `Decidable (s4Valid …)`.
