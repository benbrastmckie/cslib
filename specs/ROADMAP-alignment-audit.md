# Consolidated Alignment Audit — 13-Task Cluster

**Scope**: 430, 523, 226, 317, 511, 522 (ready) · 503, 504, 506, 512, 515, 517, 525 (blocked) + upstream deps 513, 505, 509, 514, 516, 524
**Mode**: read-only audit; ground-truth verified against repo (git, file contents, sorry/axiom counts). No status changed.
**Method**: 3 parallel research agents (ready cluster / blocked-math cluster / dependency+roadmap integrity).

---

## Executive summary — the reframe

Three findings dominate:

1. **The blocked "decidability cluster" is really four independent sub-efforts with four different verdicts** — not one converging effort. S5/T/B is *already delivered* (mislabeled blocked); S4 is *actively progressing*; KB5 needs a *new rule design*; CS5 is a *proven dead-end* awaiting a user go/no-go.
2. **The dependency graph is materially broken**: one circular edge (512↔517), five edges pointing at archived tasks, and a recurring "completed-but-doesn't-unblock" pattern (524→525, 509→512/517) that makes several `[blocked]` labels stale.
3. **0 of 13 tasks are on the ROADMAP.** `specs/ROADMAP.md`'s entire "Remaining" section is Bimodal/Temporal *completeness*; this whole cluster (Propositional-tableau cleanup + Modal-tableau decidability + axiom refactors) grew up beside the roadmap and was never folded in. A strategic decision, not a lifecycle default.

All obstruction lemmas cited in blockers were verified to genuinely exist **sorry-free** — the math claims are real, the *task metadata* is what's stale.

---

## A. Blocked-cluster: four-branch verdict

| Branch | Tasks | Verdict | Evidence |
|--------|-------|---------|----------|
| **S5 / T / B** | 503, 504(S5-half), 515(S5-half) | ✅ **DELIVERED — mislabeled blocked.** Decidable instances live & sorry-free; rank obstruction was *engineered around* via witness-rule. | `instDecidableTValid` FrameCompleteness.lean:1311; `instDecidableBValid` :1926; `instDecidableS5Valid` :2422 (commit af593180) |
| **KB5** | 525, 515(KB5-half), 504(KB5-half) | 🔶 **NEEDS NEW DESIGN.** 524 delivered a rule; 525 *proved* its truth lemma false. Completeness achievable (BdRV §4.8-4.9) but needs new rule+extraction, not a re-run. | `extractModelKb5_nonRoot_boxPos_gap` FrameCompleteness.lean:3544 (sorry-free, commit 1d3da37e) |
| **S4** | 506, 511 | 🟢 **ACTIVELY PROGRESSING.** 506's termination-bound gap is a design gap being rebuilt by 511 [partial] (agent live). Watch, don't re-scope. | `worldSetsDistinct` non-invariant LoopChecking.lean:676 |
| **CS5 (constructive)** | 512, 517 | ⛔ **PROVEN DEAD-END + user gate.** All prime-theory routes mechanically refuted; labelled escape's core type `TPrime` is provably empty. Needs user go/no-go. | `cs5Incest_forces_symm` CS5Canonical.lean:643; `tPrime_false` probes/prime-lemma-blockers.lean:92 |

**Key correction**: 503, 504, 515 are labeled `[blocked]` on prerequisites that are *already satisfied*. S5/T/B decidability is done in-tree.

---

## B. Ready-cluster verdicts

| Task | Stated | Verified | Verdict |
|------|--------|----------|---------|
| **511** s4_loop_termination | partial | 0 live sorries; work actively in flight | ✅ **READY** (already being worked) |
| **317** prop_tableau_completeness | implementing | "7 sorries"→ **4 live**; last commit self-marked BLOCKED at Phase 9 `sat_timp` gate; line numbers all stale | 🔶 **NEEDS /revise** (status + counts + deps stale) |
| **430** atom_persistence | planned, deps=[317] | dep direction correct (NOT inverted); real issue = scope absorbed by 317 Phase-10 + shared BLOCKED Phase-9 gate | 🔶 **NEEDS /revise → mark BLOCKED on 317** |
| **226** prop_semantics_upstream_pr | researched | PR #648 is **OPEN, not merged**; local files present | ⏸ **HOLD (external)** |
| **522** frame_condition_library | partial | Phase 1 green (e1b98339); Phases 2-5 correctly Zulip-gated (CONTRIBUTING.md:149) | ⏸ **HOLD (Zulip)** |
| **523** schema_union_combinator | planned | files verified; HIGH risk; Zulip-gated (cross-cutting abstraction) | ⏸ **HOLD (Zulip) — do NOT auto-implement** |

---

## C. Dependency-graph corrections

| Edge | Problem | Fix |
|------|---------|-----|
| 503→513 | 513 archived-**complete**; 503 blocker stale (target `instDecidableTValid` live) | Drop block; re-check 503 for closure |
| 504→513, 504→505 | both archived-complete but **causally irrelevant**; real unblocker is 515 (named `unblock_504`) with **no edge** | Add 504→(KB5 successor); demote 513/505 to informational |
| 512→517 & 517→512 | **CIRCULAR 2-cycle** | Drop 512→517; retire 512 to abandoned/superseded (like 516); keep 517→512 (real lemma reuse) |
| 517→516 | 516 is **abandoned** ("superseded by 517") — a dead blocking edge | Drop as blocking; keep as informational citation |
| 512→509, 517→509 | 509 completed but explicitly punted CS5-completeness to 512 ("satisfied-but-doesn't-unblock") | Annotate; 509 is not the real gate |
| 515→524 | 524 completed but proven insufficient by 525 (same pattern) | Re-point 515's gate at 525; demote 524 |
| 515→514 | 514 archived (research-only, genuinely delivered) | Drop stale dep |
| **file_scope gaps** | 504↔515↔525 share `S5Simplification.lean` with **no edges** (same shape as the 525/527 incident) | Populate `file_scope` on 503/504/506/511/512/515/517 so task-lock overlap check can see collisions |
| 522↔523 | both edit the same 14-15 `Systems/*/Soundness.lean`, no edge | Add coordinating edge before either implements |

---

## D. Recommended actions (prioritized)

**Tier 1 — low-risk, high-value (unblock/close):**
- `/revise 503` — prerequisite satisfied, `Decidable(tValid)` live; verify driver-generalization scope, move toward closure.
- `/revise 504` — mark S5-half delivered (point at `instDecidableS5Valid`); narrow to KB5-Euclidean; fix deps.
- `/revise 515` — record S5 deliverable as done; drop archived 514 dep; fold KB5 residual into the KB5-redesign task.

**Tier 2 — redesign (new work):**
- `/spawn 525` (or `/revise 525`) — scope a **new KB5 rule + extraction** per BdRV §4.8-4.9 option (i)/(ii). Do NOT re-run against 524's refuted rule.

**Tier 3 — corrective bookkeeping:**
- `/revise 317` — fix status (BLOCKED at Phase-9 `sat_timp`), sorry count (4), stale line numbers, deps.
- `/revise 430` — mark BLOCKED on 317's Phase-9 gate; resolve the single-writer ownership collision on the bridge sorries.

**Tier 4 — user decisions (no autonomous action):**
- **CS5 (512+517)**: break the cycle + one binary decision — (a) `/revise 517 → plan v4` re-transcribe labelled framework so `TPrime` is inhabited, or (b) abandon CS5 constructive completeness as a banked negative result; retire 512 as superseded.
- **ROADMAP**: 0/13 on-roadmap — either extend ROADMAP.md with a "Modal Tableau Decidability" section, or explicitly scope down further spawns into this side-program.

**Hold (external gates, no action):** 226 (PR #648 open), 522 (Zulip), 523 (Zulip).

**Watch (no action):** 506 — keep blocked on 511; re-evaluate when 511's keyed redesign lands.
