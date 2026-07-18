# Implementation Plan: Task #504 — S5 decidability DELIVERED; residual narrowed to the 5/KB5-Euclidean route (gated on KB5 completeness)

- **Task**: 504 - S5 universal-cluster decidability (DELIVERED) + 5/Euclidean coverage via the KB5/S5 equivalence route (residual)
- **Status**: PARTIAL
- **Effort**: 3 hours (residual only; gated — no 504-side work is executable until task 525 lands the KB5 redesign)
- **Dependencies**: 515 (S5 witness-rule termination — DELIVERED the S5 decidability half; live in-tree), which is itself gated on 525 (KB5 completeness + decidability redesign — the real remaining gate). Informational only (both archived-COMPLETED and causally irrelevant to what remains): 513 (generic soundness chain), 505 (B end-to-end).
- **Research Inputs**: reports/01_frame-specific-tableau-extensions.md; reports/02_spawn-analysis.md; reports/03_parent-phase-plan-reference.md; specs/ROADMAP-alignment-audit.md (sections A, C)
- **Artifacts**: plans/02_kb5-euclidean-residual.md (this file); plans/01_s5-kb5-euclidean-decidability.md (superseded — original universal-rule route)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a **corrective revision** driven by the consolidated alignment audit
(`specs/ROADMAP-alignment-audit.md`, sections A and C), ground-truthed against the repository. It
does not change any Lean code; it re-aligns the plan with audit-verified reality.

**The headline deliverable of task 504 is already delivered.** `Decidable (s5Valid φ)` is live and
sorry-free in the tree:

- `instance instDecidableS5Valid` — `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:2422`
- `theorem s5Valid_decides` — `FrameCompleteness.lean:2411`
- Landed via commit `af593180` as part of task 515's **witness-rule re-route**: the terminating
  witness-reuse rule `modalApplyOneS5w` supplies the finite-search half (recorded in the
  `instDecidableS5Valid` docstring, citing Blackburn–de Rijke–Venema §6.6 p.382).

The original plan (`plans/01_...`) pursued S5 decidability through a **universal** "propagate box to
ALL branch worlds" rule (`modalApplyOneS5`). That route hit a genuine, mechanized obstruction —
`modalApplyOneS5_rankStep_not_dischargeable` (`Cslib/Logics/Modal/Tableau/S5Simplification.lean:1921`,
sorry-free, closes by `omega`, commit `27b921c0`): `RuleApplicationSpec.rankStep` is provably FALSE
for the unrestricted universal rule. **This obstruction is real but was engineered around**, not
left as a live dead-end. Task 515 abandoned the universal rule and instead built a terminating
witness-reuse rule, which delivered the full S5 soundness + completeness + decidability stack. The
obstruction lemma remains in-tree as permanent documentation of why the universal route was
retired; it is not a blocker on anything.

**What genuinely remains for task 504** is only the **5/KB5-Euclidean** coverage — stating
`fiveValid`/`kb5Valid` and their *completeness* through the tableau. That residual flows through
**KB5 completeness**, and KB5 is genuinely blocked: task 525 proved that task 524's KB5 rule truth
lemma is FALSE, via `extractModelKb5_nonRoot_boxPos_gap` (`FrameCompleteness.lean:3544`, sorry-free,
commit `1d3da37e`) — the truth lemma's general (non-root) statement is false for that rule, so KB5
needs a *new* rule + extraction design (BdRV §4.8–4.9 option (i)/(ii)), not a re-run. Task 504's
residual therefore depends on the KB5 redesign, tracked through the chain **504 → 515 → 525**.

### Research Integration

Newly integrated: `specs/ROADMAP-alignment-audit.md` (the consolidated 13-task alignment audit).
Verified claims (each ground-truthed against the working tree during this revision):

- **A / "S5 DELIVERED — mislabeled blocked"** (audit §A row 1): `instDecidableS5Valid`
  (`FrameCompleteness.lean:2422`), `s5Valid_decides` (`:2411`) are live and sorry-free; the rank
  obstruction was *engineered around* via the witness rule. Confirmed by reading the file: the
  decision procedure runs `modalTableauS5` and is documented as backed by `modalApplyOneS5w`.
- **A / "KB5 NEEDS NEW DESIGN"** (audit §A row 2): `extractModelKb5_nonRoot_boxPos_gap`
  (`FrameCompleteness.lean:3544`) is a sorry-free proof that task 524's KB5 rule truth lemma is
  false for non-root triggers. Confirmed by reading the lemma statement and its docstring
  (`φ₀ := ¬(◇◇□p)` counterexample, raw edges `0→1→2`).
- **C / dependency corrections** (audit §C rows for `504→513, 504→505` and `515→524`): 513 and 505
  are both archived-COMPLETED and causally irrelevant; the real unblocker is 515 (named
  `s5_universal_rule_termination_unblock_504`), which itself now points at 525 (its `515→524` edge
  was re-pointed at 525, since 524 was proven insufficient). `state.json` deps for 504 already read
  `[515]`; this plan demotes 513/505 to informational and records the 504 → 515 → 525 gate.

### Supersession of plan 01

`plans/01_s5-kb5-euclidean-decidability.md` is retained for history but **superseded**. Its Phases
1–6 describe the universal-rule route that was retired; its Phase-2 `[BLOCKED]` record and mechanized
counterexample are accurate but no longer describe a live dead-end (the witness rule bypassed it).
Its Phase 3 (`extractModelS5`) and Phase 7-partial (`extractModelS5_rightEuclidean`, pure-K5
out-of-scope docstring) remain valid and are reflected below as delivered.

### Roadmap Alignment

**OFF-ROADMAP — no roadmap claims.** Per audit §A/§D, 0 of the 13 audited tasks are on
`specs/ROADMAP.md` (its "Remaining" section is Bimodal/Temporal completeness). This revision makes
no ROADMAP.md edits and asserts no roadmap items.

## Goals & Non-Goals

**Goals** (revised scope):
- Record the **S5 decidability deliverable as SATISFIED**, pointing at the live in-tree instances
  (`instDecidableS5Valid` / `s5Valid_decides`, `FrameCompleteness.lean:2422/2411`) delivered via
  task 515's witness-rule route. No further 504-side work on the S5 decision procedure.
- Record `extractModelS5` + `extractModelS5_rightEuclidean` (equivalence-route Euclidean exposure)
  as delivered.
- Narrow the **only remaining residual** to: state `fiveValid`/`kb5Valid` and their *completeness*
  through the tableau, via the KB5/S5 equivalence route.
- Make explicit that this residual is **gated on KB5 completeness** — the task 525 redesign (new KB5
  rule + extraction per BdRV §4.8–4.9), tracked via 504 → 515 → 525 — and NOT on the
  already-satisfied 513/505 nor on the (bypassed) universal-rule rank obstruction.
- Position task 504 for **near-term PARTIAL closure** of its S5 half.

**Non-Goals**:
- Any Lean code changes in this revision (revision is plan/description only).
- Re-attempting the universal-rule route or the `RuleApplicationSpec.rankStep` discharge — proven
  false, permanently retired.
- Re-running the KB5 completeness proof against task 524's refuted rule (audit §D Tier 2: needs a
  new design, not a re-run — that is task 525's charter, not 504's).
- Genuine **pure-K5 / pure-5** completeness (Euclidean without full equivalence): no Mathlib
  closure operator; documented in-file as out of scope (unchanged from plan 01).
- Any ROADMAP.md edits (off-roadmap).
- Any `sorry`, `axiom`, or vacuous placeholder if/when the residual is eventually implemented.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Residual is executed prematurely (before task 525 lands the KB5 redesign), re-hitting the refuted KB5 truth lemma | H | M | Phase 3 is explicitly `[BLOCKED]` on 525. Do NOT dispatch `/implement 504` for the KB5-completeness residual until 525 delivers a sorry-free KB5 completeness/decision result. The 504 → 515 → 525 gate is recorded in deps and here. |
| Confusion that the S5 half is still blocked (stale plan-01 `[BLOCKED]` markers) | M | H | This plan supersedes plan 01; the S5 decidability deliverable is recorded SATISFIED with exact live-instance line references. |
| The retired universal-rule obstruction lemma is mistaken for a live blocker | M | M | Explicitly documented: `modalApplyOneS5_rankStep_not_dischargeable` is permanent documentation of a *bypassed* route, not a live dead-end. |
| KB5 completeness (525) itself proves intractable through the equivalence route | M | L | Out of 504's scope; 504's residual is a thin statement layer *over* whatever KB5 decision engine 525 lands. If 525 abandons KB5, 504's residual should be re-scoped/closed accordingly. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| — | 1, 2 | already delivered in-tree (no work) |
| 1 | 3 | task 525 (KB5 redesign) landing a sorry-free KB5 completeness/decision result |

Phases 1 and 2 record already-delivered, in-tree results (no executable work). Phase 3 is the sole
residual and is gated on task 525.

---

### Phase 1: S5 decidability — SATISFIED via the task 515 witness-rule route [COMPLETED]

- **Status note:** SATISFIED. No 504-side work remains. Delivered by task 515's witness-reuse rule
  `modalApplyOneS5w` (the universal rule of plan 01 was retired; see Overview).
- **Delivered, live in-tree (sorry-free, commit `af593180`):**
  - `instance instDecidableS5Valid (φ₀) : Decidable (s5Valid φ₀)` —
    `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:2422`.
  - `theorem s5Valid_decides (φ₀) : modalTableauS5 φ₀ = .closed ↔ s5Valid φ₀` — `:2411`
    (`⟨modalTableauS5_sound, modalTableauS5_complete⟩`).
  - `modalTableauS5_sound` (`FrameSoundness.lean`) and `modalTableauS5_complete` (above the decide
    instance) — the soundness + completeness pair the witness route delivered.
- **Retired (permanent documentation, not a blocker):**
  `modalApplyOneS5_rankStep_not_dischargeable` — `S5Simplification.lean:1921` (sorry-free, `omega`,
  commit `27b921c0`): proves `RuleApplicationSpec.rankStep` FALSE for the universal rule. The route
  it obstructs was engineered around by the witness rule.
- **Verification:** Live-instance references above resolve; `Decidable (s5Valid φ)` is inhabited in
  the current tree with zero sorry/axiom on the S5 decision path.

---

### Phase 2: `extractModelS5` + equivalence-route Euclidean exposure — SATISFIED [COMPLETED]

- **Status note:** SATISFIED. Delivered under plan 01 Phase 3 / Phase 7-partial.
- **Delivered, live in-tree (sorry-free):**
  - `extractModelS5` (via `Relation.EqvGen`), `extractModelS5_r`, `extractModelS5_equiv`
    (`IsEquiv`), `extractModelS5_hasEdge_imp_r` — `FrameCompleteness.lean`.
  - `extractModelS5_rightEuclidean : Relation.RightEuclidean (extractModelS5 b acc).r` — built
    directly from `IsEquiv`'s `symm`/`trans` projections. This is the equivalence-route Euclidean
    exposure (the S5 model is `EqvGen`-closed, hence reflexive + Euclidean).
  - In-file docstring recording genuine **pure-K5** (Euclidean without full equivalence) as OUT OF
    SCOPE (no Mathlib closure operator), deferred to a dedicated `pure-k5-euclidean-closure` task.
- **Verification:** the `RightEuclidean` instance and the `extractModelS5_*` lemmas type-check in the
  current tree; zero sorry/axiom.

---

### Phase 3: 5/KB5-Euclidean validity + completeness via the KB5 route — RESIDUAL [BLOCKED]

**BLOCKER** (Phase 3): Gated on **task 525** (KB5 completeness + decidability redesign). The
5/KB5-Euclidean *completeness* statements this phase would land need a working KB5 decision engine
as their proof engine, and KB5 is genuinely blocked: task 525 proved task 524's KB5 rule truth
lemma FALSE via `extractModelKb5_nonRoot_boxPos_gap` (`FrameCompleteness.lean:3544`, sorry-free,
commit `1d3da37e`). Per audit §D Tier 2, KB5 needs a **new** rule + extraction design (BdRV
§4.8–4.9 option (i)/(ii)) — NOT a re-run against 524's refuted rule. This gate is **not** the
already-satisfied 513/505, and **not** the bypassed universal-rule rank obstruction; it is the
KB5 redesign, tracked via 504 → 515 → 525. Do not dispatch this phase until 525 lands a sorry-free
KB5 completeness/decision result.

- **Goal (when unblocked):** State `fiveValid`/`kb5Valid` and their completeness via the equivalence
  / KB5 route, reusing the KB5 decision engine that task 525 delivers; soundness arm via
  `Satisfies.five`.
- **Tasks (deferred until 525 unblocks):**
  - [ ] Add `fiveFC`/`kb5FC` frame-condition defs (`FrameSoundness.lean`) and `fiveValid`/`kb5Valid`
    (mirroring the established `*Valid` pattern).
  - [ ] State `fiveValid`/`kb5Valid` completeness through the KB5 decision engine from task 525
    (the sound+complete KB5 tableau), with the soundness arm via `Satisfies.five` (`Basic.lean:376`)
    and `Cslib/Foundations/Relation/Euclidean.lean` API.
  - [ ] Keep the pure-K5 out-of-scope docstring (already present from Phase 2) intact; no `EuclGen`.
- **Depends on:** task 525 landing a sorry-free KB5 completeness/decision result.
- **Files to modify (when unblocked):** `FrameSoundness.lean`, `FrameCompleteness.lean`.
- **Verification (when unblocked):** `lake build` green; zero sorry/axiom; `fiveValid`/`kb5Valid`
  completeness results type-check; full CSLib CI clean.
- **[BLOCKED] fallback:** If task 525 ultimately abandons KB5 completeness (banked negative result),
  re-scope this residual accordingly or close task 504 at its S5-half PARTIAL delivery. Never
  `sorry`/`axiom`.

---

## Testing & Validation

No Lean changes are made by this revision. For the eventual Phase 3 residual (once 525 unblocks),
run the full CSLib CI pipeline (order per `cslib.md`): `lake build` (zero `sorry` / zero new
`axiom`), `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`,
`lake exe mk_all --module`, `lake shake --add-public --keep-implied --keep-prefix`.

Acceptance for the current (revised) state — all verifiable in-tree now:
- [x] `instDecidableS5Valid` resolves `Decidable (s5Valid φ)` (`FrameCompleteness.lean:2422`).
- [x] `s5Valid_decides` live (`:2411`).
- [x] `extractModelS5_rightEuclidean` type-checks (equivalence-route Euclidean exposure).
- [ ] `fiveValid`/`kb5Valid` completeness (Phase 3 residual — blocked on 525).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — DELIVERED: `instDecidableS5Valid`,
  `s5Valid_decides`, `modalTableauS5_complete`, `extractModelS5` (+ `_r`/`_equiv`/`_hasEdge_imp_r`/
  `_rightEuclidean`). Residual (blocked): `fiveValid`/`kb5Valid` completeness through the 525 KB5
  engine.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — DELIVERED: `s5FC`, `s5Valid`,
  `modalTableauS5_sound`. Residual (blocked): `fiveFC`/`kb5FC`, `fiveValid`/`kb5Valid` defs +
  soundness arm.
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — DELIVERED (retired-route documentation):
  `modalApplyOneS5_rankStep_not_dischargeable`.
- No new artifacts written by this revision beyond this plan.

## Rollback/Contingency

- This revision is plan/description-only; there is nothing to roll back in code.
- The S5-half deliverables are purely additive and already committed (`af593180`, `27b921c0`).
- Preferred contingency for the Phase 3 residual is to keep it `[BLOCKED]` on task 525 and pursue
  **PARTIAL closure of task 504's S5 half now**, rather than holding the whole task open on a gate
  that belongs to the KB5 redesign line.

## Recommended status (for the skill postflight — not set by this agent)

Recommend transitioning task 504 to **PARTIAL** (S5 decidability + Euclidean exposure delivered;
only the 5/KB5-Euclidean completeness residual remains, gated on task 525). Keep the dependency
`[515]` (which chains to 525); demote 513/505 to informational.
