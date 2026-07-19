# Implementation Plan: General Labelled CS5 Soundness (nik_TS5_soundness)

- **Task**: 537 - Prove the general labelled soundness direction completing Simpson 1994 Thm 8.1.4's biconditional
- **Status**: [IMPLEMENTING]
- **Effort**: 6-40 hours (branch-dependent; probe phase is the sole guaranteed run)
- **Dependencies**: 517 (delivered completeness + anti-vacuity, all landed)
- **Research Inputs**: reports/01_general-soundness-strategies.md (Tier 1, H4-verified, 6/6 claims CONFIRMED)
- **Artifacts**: plans/01_general-soundness.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/context/formats/plan-format.md
- **Type**: cslib

## Overview

Prove `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` in the single file
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, closing the soundness
direction (2⟹1) of Simpson Thm 8.1.4 for CSLib constructive CS5/IS5. The completeness direction
and the anti-vacuity certificate are already landed sorry-free by parent task 517.

The research verdict (H4-verified, unchanged across a divergence audit) is that the **direct route
is GENUINELY OPEN**, sharpened to two exactness walls: Wall A (exact symmetry of `r` on
`cs5FCIncest` models = the `TClosure.symm` edge-validation case) and Wall B (box-introduction at
`Forcing.lean:75` quantifies the adversarial successor `u` universally, so clique closure is
necessary but NOT sufficient). Three prior task-517 dispatches exhausted the direct-implementation
route without closing either a proof or a countermodel.

This plan therefore sizes the direct route honestly as a **time-boxed decisive probe with a hard
pivot gate** (Phase 1), not a multi-phase build. The gate has three concrete outcomes, each wired
to concrete downstream phases so no pivot is ever improvised: proof lands → direct-route
continuation (Phases 2-3); countermodel lands → direct route provably dead → Strategy-3 adequacy
bridge (Phases 5-7); neither within budget → `[BLOCKED]` handoff + Strategy-3 scope-reopening
recommendation (Phase 4). **This is not a skeleton plan** (`plan_metadata.skeleton: false`): the
task forbids `sorry`, so the sanctioned response to a genuinely-blocked sub-goal is a documented
`[BLOCKED]` handoff routed to a follow-up task, never a strategic-sorry division point.

### Definition of Done

`nik_TS5_soundness` lands sorry-free and axiom-clean in `Soundness.lean`, full `lake build` green,
`lake lint` / `lint-style` / `shake` / `checkInitImports` / `test` unregressed. Acceptable
terminal alternative under the blocked-honesty flag: a `[BLOCKED]` status with a written handoff
routing to an authorized Strategy-3 follow-up task, with the build still green and no debt added.

### Research Integration

- reports/01_general-soundness-strategies.md — integrated in plan_version 1 (2026-07-19). Supplies
  the ranked strategy verdict, the Wall A / Wall B sharpening, the Source-to-Implementation mapping
  below, and the churn warning (3 prior direct attempts → mandatory no-loop gate).

### Preserved Assets

The following work is complete (landed sorry-free / axiom-clean by task 517) and MUST NOT regress:

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| `cs5_completeness` | Completeness.lean:132 | [COMPLETED] | task 517 (2026-07-19) |
| `nik_TS5_consistent` (anti-vacuity) | Soundness.lean:365 | [COMPLETED] | task 517 (2026-07-19) |
| `nik_soundness_onePoint` (anti-vacuity) | Soundness.lean:291 | [COMPLETED] | task 517 (2026-07-19) |
| `cs5FCIncest_lift` (single-edge building block) | Soundness.lean:268 | [COMPLETED] | task 517 (2026-07-19) |
| `ckforces_persistence` (upward closure) | Forcing.lean:122 | [COMPLETED] | task 517 (2026-07-19) |
| `cs5_soundness_derivable_incest` (Strategy-3 payoff) | CS5Canonical.lean:373 | [COMPLETED] | task 517 (2026-07-19) |

### Source-to-Implementation Mapping (Tier 1)

Load-bearing decisions cite these sources. Paper-specific numbers are `[UNVERIFIED against live
corpus]` (this session's literature retrieval degraded) but anchored to in-repo CI-green evidence.

| Source Claim | BibKey | Lean Target | Used By |
|--------------|--------|-------------|---------|
| Thm 8.1.4 biconditional, soundness direction (2⟹1) | Simpson1994 | `nik_TS5_soundness` (goal) | Phase 3 / Phase 7 |
| Lifting Lemma 8.1.3 (single-edge case) | Simpson1994 | `cs5FCIncest_lift` (landed) | Phase 1, Phase 3 |
| §8.1.2 modified sequent system `L_m(TS5,∅)` | Simpson1994 | Strategy 2 (reserve, not planned) | — |
| Thm 6.2.1 adequacy, labelled⟹Hilbert direction | Simpson1994 | `NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ` (new `Adequacy.lean`) | Phases 5-7 |
| Thm 7.1 incestuality frame conditions | MarinMoralesStrassburger2021 | `cs5Incest` (CS5Canonical.lean:234, landed) | Phase 1 |

Both BibKeys verified present: `Simpson1994` (references.bib:86), `MarinMoralesStrassburger2021`
(references.bib:962).

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the parent's three blocked
dispatches, the research risk factors, and the zero-debt task constraints.

**Do NOT**:
- Do NOT launch a fourth undirected direct-implementation attempt at `nik_TS5_soundness` via the
  same "chase `hincest`/`hfour`/`hsymbox` pairwise" route — three dispatches already exhausted it
  (churn warning in the orchestrator handoff). Phase 1 is a *bounded probe with a mandatory
  no-loop gate*, not an open-ended retry.
- Do NOT introduce `sorry` anywhere under `Cslib/` — not even a "temporary" or "strategic" one.
  This task explicitly forbids it; a genuinely blocked sub-goal routes to a `[BLOCKED]` handoff
  (Phase 4), never a placeholder. This plan is NOT a skeleton and has NO planned strategic sorries.
- Do NOT add any new `axiom` under `Cslib/`.
- Do NOT weaken `cs5FCIncest` (do not drop/relax any of its five conjuncts to force a proof through).
- Do NOT edit or re-derive the `[COMPLETED]` assets in Preserved Assets; `nik_TS5_consistent`,
  `nik_soundness_onePoint`, `cs5FCIncest_lift`, `cs5_completeness` must stay byte-identical in
  behavior (their proofs may not regress).
- Do NOT assume FLO machinery is a plug-in: it is off-mainline in task-517 `probes/`, carries two
  open sorries, and is a context-Lindenbaum engine, NOT a relational-clique closure. Only the
  generic Zorn/chain-union *pattern* is reusable, re-instantiated from scratch.
- Do NOT treat clique closure as sufficient for the `(□I)` case — Wall B (adversarial `u`) is a
  second, independent exactness obstruction that a positive symmetry lemma does not clear.
- Do NOT silently expand file scope to `Adequacy.lean` on the direct route; the new file is
  introduced ONLY on the Strategy-3 branch (Phases 5-7), and only after a countermodel (GATE-B)
  or an explicit scope authorization.

**MUST preserve**:
- All six Preserved Assets above (sorry-free, axiom-clean, unregressed).
- Existing full-project green state: `lake build`, `lake lint`, `lint-style`, `shake`,
  `checkInitImports`, `lake test` (pre-existing unrelated sorries in Propositional Tableau files
  are the known baseline — do not "fix" or count them).

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- The direct route reduces to Wall A + Wall B; base/refl/trans edge-validation cases are already
  discharged by exact `hrefl`/`htrans`, and `eucl` is provably vacuous for `TS5={T,B,Four}`
  (CS5Canonical.lean:255-260; Deduction.lean:198-208). Do not re-litigate these cases.
- Strategy ranking is fixed: Strategy 1 probe first, Strategy 3 as the sanctioned fallback,
  Strategy 2 (`L_m` sequent system) held in reserve and NOT planned here (no in-repo reuse; source
  §8.1.2 unreadable this session). Do not pivot to Strategy 2 without a fresh research pass.
- Strategy 3's payoff is a one-line corollary of the landed `cs5_soundness_derivable_incest`; the
  TB4 schema choice (`TS5={T,B,Four}`) deliberately sidesteps the `IKT5⟺IKTB4` sub-gap, so that
  sub-bridge does NOT bite. The C5 `pathSpine`/`addChild` commutation is "THE TRUE CRUX".

## Goals & Non-Goals

- **Goals**:
  - Deliver `nik_TS5_soundness` sorry-free/axiom-clean, OR a documented `[BLOCKED]` handoff with a
    concrete blocker (countermodel or budget-exhausted probe) and a Strategy-3 follow-up route.
  - Keep every intermediate state green and committed (H9 wrap-up discipline).
- **Non-Goals**:
  - Strategy 2 (`L_m` modified sequent system) — reserve only, not implemented here.
  - Any change to the completeness direction or the anti-vacuity certificate.
  - Proving the full Simpson Chapter 6 adequacy in both directions — only the labelled⟹Hilbert
    direction is in scope, and only on the Strategy-3 branch.

## Risks & Mitigations

- **Risk**: Phase 1 probe loops into a fourth thrash. **Mitigation**: hard budget cap + mandatory
  no-loop gate; GATE-C forces `[BLOCKED]`, never a retry.
- **Risk**: Wall B blocks completion even after Wall A is proven (Phase 2). **Mitigation**: Phase 2
  carries its own blocked-honesty exit routing to Phase 4; the plan does not assume Wall A ⟹ done.
- **Risk**: Strategy-3 C5 commutation crux (Phase 6) is research-grade / open-ended (bounded-unit
  hazard). **Mitigation**: Phase 6 carries a hard budget cap + `[BLOCKED]`→Phase 4 exit; it is not
  an open-ended retry.
- **Risk**: Scope creep to `Adequacy.lean` on the wrong branch. **Mitigation**: file-scope rule in
  Postmortem Constraints; new file only on GATE-B / authorized Strategy-3 branch.

## Implementation Phases

**Dependency Analysis**:

The gate outcomes are mutually exclusive: at most ONE Wave-2 branch executes per run, selected by
Phase 1's gate result. Same-wave phases below are conditional branches, NOT parallel work.

| Wave | Phases | Blocked by | Branch selector |
|------|--------|------------|-----------------|
| 1 | 1 | -- | always (probe + pivot gate) |
| 2 | 2 \| 4 \| 5 | 1 | 2=GATE-A(proof) \| 4=GATE-C(blocked) \| 5=GATE-B(countermodel) |
| 3 | 3 \| 6 | 2 (for 3); 5 (for 6) | 3=direct continuation \| 6=Strategy-3 crux |
| 4 | 7 | 6 | Strategy-3 completion |

Phase 4 is also the sanctioned escape for a Phase 2 or Phase 6 blocked-honesty exit.

### Phase 1: Decisive symmetry/clique-closure probe with hard pivot gate [BLOCKED]

**GATE-C recorded (2026-07-19).** Neither the exact-symmetry lemma nor a countermodel was landed
within this bounded run. Proof attempts (verified via live `lean_goal`/`lean_multi_attempt` state,
not just hand analysis) confirm the `hincest`/`hfour`/`hsymbox` cascade never re-pins the two
original fixed points (reproduces the third dispatch's finding independently). Countermodel
attempts (a hand-built `ℕ` candidate, plus a general translation-invariant `ℤ`
difference-semigroup argument showing any such semigroup unbounded both ways must be a subgroup,
hence symmetric) found no asymmetric example. The Zorn/chain-union pattern was assessed and found
structurally infeasible within this probe's budget (see `Soundness.lean` docstring, "Fourth
dispatch" section, for the full record) — building it is genuinely new, multi-dispatch-scale
infrastructure, not a bounded probe. Per the pivot gate, this is the **explicitly sanctioned**
GATE-C outcome: build green, zero debt, no `sorry`, no new axiom, `cs5FCIncest` unweakened, all
Preserved Assets unregressed. **Next: Phase 4** (`[BLOCKED]` handoff + Strategy-3 recommendation).

- **Goal:** In one bounded agent run, decisively resolve Wall A — either prove the exact-symmetry
  lemma `cs5FCIncest r → r a b → r b a` on the finitely-generated interpreted substructure (as a
  named sorry-free lemma in `Soundness.lean`), OR construct a concrete `cs5FCIncest`-satisfying
  countermodel with `r a b ∧ ¬ r b a` on such a substructure. This is the pivot gate; its outcome
  selects the entire downstream branch.
- **Tasks:**
  - [ ] State the closure/symmetry lemma precisely (smallest `r`-clique containing a finite seed,
        closed under the raised-witness clauses `hincest`/`hfour`/`hsymbox`, is symmetric), citing
        `CS5Canonical.lean:255-260` for the exact `cs5FCIncest` conjuncts.
  - [ ] Attempt the proof using exact `hrefl`/`htrans` plus the generic Zorn/chain-union *pattern*
        (re-instantiated for a relational-closure poset — NOT the FLO Lindenbaum engine).
  - [ ] In parallel, attempt a minimal asymmetric countermodel on `ℕ`/`Fin n` (seed `r a b`,
        escape upward via `≤`-room), checking it against all five conjuncts including the
        `hsymbox`+`htrans` collapse the parent hand-probe hit.
  - [ ] Record the gate outcome (A/B/C) in the `Soundness.lean` docstring and the handoff.
- **Timing:** one agent run, HARD budget cap (do not exceed the single-run tool budget; no
  continuation into a second run for this probe).
- **Depends on:** none
- **Zero-debt contract:** no `sorry`, no new axiom, do not weaken `cs5FCIncest`, do not regress any
  Preserved Asset. Any lemma landed here must be sorry-free before commit.
- **PIVOT GATE — exit criterion (exactly one fires):**
  - **GATE-A (proof landed):** the symmetry/clique-closure lemma is sorry-free and
    `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` is green →
    **proceed to Phase 2**.
  - **GATE-B (countermodel landed):** a concrete `cs5FCIncest` model exhibiting `r a b ∧ ¬ r b a`
    on a finitely-generated substructure is constructed and checked → the direct route is
    **provably dead** → **proceed to Phase 5** (Strategy 3), recording the countermodel in the
    docstring as the justification.
  - **GATE-C (neither within budget):** no proof, no countermodel at budget exhaustion → **DO NOT
    LOOP** (three prior dispatches already exhausted this) → **proceed to Phase 4** (`[BLOCKED]`
    handoff + Strategy-3 scope-reopening recommendation).
- **Verification:** `lake build` of `Soundness.lean` green (docstring/lemma change); if GATE-A,
  the new lemma is sorry-free (`grep` finds no tactic `sorry`); gate outcome explicitly recorded.

### Phase 2: Box-introduction adversarial-u absorption lemma (direct route) [NOT STARTED]

- **Goal:** Prove Wall B — the `(□I)` case where the fresh label's interpretation must equal the
  adversarially-quantified successor `u` (`Forcing.lean:75`), landing a sorry-free lemma that
  absorbs `u` into the `r`-clique against every already-used label. Clique closure alone (Phase 1)
  is necessary but not sufficient; this lemma supplies the missing exactness.
- **Tasks:**
  - [ ] State the absorption lemma against the exact `Forcing.lean:75` box clause
        (`∀ w' ≥ w, ∀ u, r w' u → CKForces u φ`), reusing `ckforces_persistence` (Forcing.lean:122).
  - [ ] Prove it using the Phase 1 symmetry/clique lemma + `cs5FCIncest_lift` (Soundness.lean:268).
  - [ ] If the lemma is genuinely unprovable even with Wall A in hand, STOP and route to Phase 4.
- **Timing:** ~100-250 lines output; one agent run.
- **Depends on:** 1 (GATE-A only)
- **Zero-debt contract:** no `sorry`, no new axiom, do not weaken `cs5FCIncest`, do not regress
  Preserved Assets.
- **Blocked-honesty sub-gate:** if Wall B cannot be closed within one bounded run, escalate to
  **Phase 4** (`[BLOCKED]`), NOT a sorry and NOT a fourth-style thrash.
- **Verification:** `lake build` of `Soundness.lean` green; the absorption lemma is sorry-free.
  Done when: the `(□I)`-case obligation is a named sorry-free lemma consuming Phase 1's result.

### Phase 3: Thread closure lemmas through NIK induction → nik_TS5_soundness (direct route) [NOT STARTED]

- **Goal:** Complete the NIK induction (docstring items 1-4), discharging the edge-validation
  obligation via Phase 1 (Wall A) and Phase 2 (Wall B) lemmas, landing `nik_TS5_soundness`
  sorry-free/axiom-clean. This closes Simpson Thm 8.1.4's biconditional.
- **Tasks:**
  - [ ] Thread the `TClosure` structural induction (base/refl/trans discharged by exact
        `hrefl`/`htrans`; `symm` by Phase 1; `eucl` vacuous for `TS5`) through the 12-constructor
        `NIK` induction.
  - [ ] Discharge the `(□I)` and `(□E)` cases using the Phase 2 absorption lemma.
  - [ ] Land `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`.
  - [ ] Update the `Soundness.lean` docstring status line; remove the parent's `[BLOCKED]` note.
- **Timing:** ~150-300 lines output; one agent run.
- **Depends on:** 2
- **Zero-debt contract:** no `sorry`, no new axiom, do not weaken `cs5FCIncest`, do not regress
  Preserved Assets.
- **Verification:** full `lake build` green; `lean_verify nik_TS5_soundness` axiom-clean; `grep`
  finds no tactic `sorry` in `Soundness.lean`; `lake lint` / `lint-style` / `shake` /
  `checkInitImports` / `lake test` unregressed. Done when: `nik_TS5_soundness` is sorry-free and
  axiom-clean and the biconditional is complete.

### Phase 4: BLOCKED handoff + Strategy-3 scope-reopening recommendation (contingency) [NOT STARTED]

- **Goal:** When Phase 1 hits GATE-C (or Phase 2 / Phase 6 escalates), record an honest `[BLOCKED]`
  terminal state on the direct route WITHOUT adding any debt, and write a handoff that routes to an
  authorized Strategy-3 follow-up task. This is the sanctioned no-loop, no-sorry response.
- **Tasks:**
  - [ ] Write a `[BLOCKED]` handoff under `specs/537.../handoffs/` documenting the exact blocker
        (which wall, budget exhausted vs. concrete obstruction) and the current green build state.
  - [ ] Recommend to the user/orchestrator that Strategy-3 (Ch.6 adequacy bridge) scope be
        authorized as a follow-up task — this is a scope escalation task 517 deliberately avoided,
        so it is a user/orchestrator call, not an autonomous continuation.
  - [ ] Set the task status to `[BLOCKED]`; leave the plan's downstream phases `[NOT STARTED]`.
  - [ ] Confirm no `sorry`/axiom/regression was introduced.
- **Timing:** short; one agent run (documentation only, no `.lean` proof edits).
- **Depends on:** 1 (GATE-C), or escalation from 2 or 6.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no regression — verified before
  writing the handoff.
- **Verification:** full `lake build` still green and unregressed; handoff file exists and names a
  concrete blocker + Strategy-3 route. Done when: `[BLOCKED]` recorded with a durable handoff and
  zero debt.

### Phase 5: Strategy-3 adequacy-bridge scaffolding (pathSpine/addChild) [NOT STARTED]

- **Goal:** Begin the Simpson Ch.6 labelled⟹Hilbert bridge in a NEW file `Adequacy.lean`: define
  the translation scaffolding (`pathSpine` / `addChild` and their basic lemmas) needed to state
  `NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ`. Entered only after GATE-B (direct route proven
  dead) or explicit Strategy-3 authorization.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Adequacy.lean` with imports and
        the `pathSpine`/`addChild` definitions (mirroring task-517 Track C report 02/11 structure).
  - [ ] Prove the basic structural lemmas about `pathSpine`/`addChild` (no `sorry`).
  - [ ] Register the new module (`mk_all`) scoped to this task only.
- **Timing:** ~150-300 lines output; one agent run.
- **Depends on:** 1 (GATE-B)
- **Zero-debt contract:** no `sorry`, no new axiom, do not weaken `cs5FCIncest`, do not regress
  Preserved Assets. File-scope expansion to `Adequacy.lean` is authorized ONLY on this branch.
- **Verification:** `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Adequacy` green;
  scaffolding lemmas sorry-free; `checkInitImports` pass. Done when: scaffolding compiles sorry-free.

### Phase 6: Strategy-3 C5 commutation crux [NOT STARTED]

- **Goal:** Prove the C5 `pathSpine`/`addChild` commutation lemma — the research's "TRUE CRUX" of
  the Ch.6 bridge. This is the single highest-risk unit (rated ~25-30%, source deliberately
  informal), so it carries the same bounded-probe discipline as Phase 1.
- **Tasks:**
  - [ ] State and attempt the C5 commutation lemma against the Phase 5 scaffolding.
  - [ ] If unprovable within one bounded run, STOP and route to Phase 4 (`[BLOCKED]`), do NOT loop.
- **Timing:** one agent run, HARD budget cap (bounded-unit hazard: research-grade proof).
- **Depends on:** 5
- **Zero-debt contract:** no `sorry`, no new axiom, do not weaken `cs5FCIncest`, do not regress.
- **Blocked-honesty sub-gate:** C5 unproven at budget → **Phase 4** (`[BLOCKED]`), never a sorry.
- **Verification:** `lake build` of `Adequacy.lean` green; C5 lemma sorry-free. Done when: the C5
  commutation lemma is a named sorry-free lemma, or a `[BLOCKED]` handoff is written.

### Phase 7: Strategy-3 remaining 6.2.1 direction + corollary assembly → nik_TS5_soundness [NOT STARTED]

- **Goal:** Complete the labelled⟹Hilbert direction of Thm 6.2.1
  (`NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ`) on top of the C5 crux, then obtain
  `nik_TS5_soundness` as the one-line corollary `cs5_soundness_derivable_incest ∘ bridge`.
- **Tasks:**
  - [ ] Finish the remaining induction cases of the bridge direction (sorry-free).
  - [ ] Land `nik_TS5_soundness` in `Soundness.lean` as the corollary composing the bridge with the
        landed `cs5_soundness_derivable_incest` (CS5Canonical.lean:373).
  - [ ] Update the `Soundness.lean` docstring; remove the parent's `[BLOCKED]` note.
- **Timing:** ~150-300 lines output; one agent run.
- **Depends on:** 6
- **Zero-debt contract:** no `sorry`, no new axiom, do not weaken `cs5FCIncest`, do not regress
  Preserved Assets.
- **Verification:** full `lake build` green; `lean_verify nik_TS5_soundness` axiom-clean; no tactic
  `sorry` in `Soundness.lean` or `Adequacy.lean`; lint/lint-style/shake/checkInitImports/test
  unregressed. Done when: `nik_TS5_soundness` is sorry-free and axiom-clean via the bridge.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every
      phase that touches `.lean`.
- [ ] Full `lake build` green at each phase completion (green-milestone commit per H9).
- [ ] `lean_verify nik_TS5_soundness` reports axiom-clean on the completing phase (3 or 7).
- [ ] `grep '\bsorry\b'` on modified `.lean` files: no *tactic* `sorry` (docstring prose excepted).
- [ ] `grep '^axiom '` on modified files: zero new axioms.
- [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
      `lake test`: all unregressed against the task-517 green baseline.
- [ ] Preserved Assets unregressed (spot-verify the six listed theorems still build sorry-free).

## Artifacts & Outputs

- plans/01_general-soundness.md (this file)
- Modified: Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean (all branches)
- New (Strategy-3 branch only): Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Adequacy.lean
- handoffs/ blocked handoff (contingency, Phase 4 only)
- summaries/01_general-soundness-summary.md (on completion)

## Rollback/Contingency

- Each phase commits only its own green result (H9 incremental commit). If a phase fails to reach
  green, leave the prior committed state intact; do not force a build green by discarding
  uncommitted changes (see recovery ladder: fix forward, never destructive git on dirty tree).
- The blocked-honesty path (Phase 4) IS the sanctioned contingency: a `[BLOCKED]` handoff with a
  concrete blocker and a Strategy-3 follow-up route, zero debt, build green — never a `sorry`
  skeleton and never a fourth undirected direct attempt.
