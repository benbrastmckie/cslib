# Implementation Plan (v2, hard mode): Task #180 — Primitive allFuture (G) / allPast (H)

- **Task**: 180 - Add allFuture (G) and allPast (H) as primitive constructors to Temporal.Formula
- **Status**: [IMPLEMENTING]
- **Effort**: 16-22 hours (9 phases, one agent run each)
- **Dependencies**: None (build-exclusive: must be implemented ALONE on an otherwise-green Temporal tree)
- **Research Inputs**:
  - reports/01_primitive-always-historically-research.md (settled syntax/semantics design)
  - reports/02_implementation-attempt-status.md (parked attempt; overflow + build-exclusivity constraints)
  - reports/03_metalogic-obligations-research.md (PRIMARY: metalogic obligations, defeq root cause, bridge axioms, TruthLemma reduction)
  - wip/01_primitive-gh-wip.patch (1063-line preserved WIP for the 7 early files)
- **Artifacts**: plans/03_primitive-gh-metalogic-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md; anti-analysis.md (H2); reference-grounding.md (H3)
- **Type**: cslib
- **Lean Intent**: true

## Overview

`Temporal.Formula` currently defines `𝐆φ` as the definitional abbreviation `¬𝐅¬φ`
(`Formula.allFuture φ := .neg (.someFuture (.neg φ))`, `Formula.lean:140`) and `𝐇φ` as
`¬𝐏¬φ`. These are only classically valid. This task promotes `allFuture`/`allPast` to primitive
inductive constructors with direct structural semantics, enabling intuitionistic temporal logics
where `𝐆φ` is strictly stronger than `¬𝐅¬φ`. Definition of done: `allFuture`/`allPast` are
constructors with structural satisfaction clauses; every recursive function and proof over
`Formula` carries the new cases; Soundness, MCS, Chronicle/TruthLemma, and Completeness compile;
the classical equivalences are recovered as (axiom-backed) theorems; **full CI is green**.

This is a v2 REVISION. A prior 8-phase plan (`plans/01`, `[PARTIAL]`) was attempted once and
overflowed a single agent's context window ("Prompt is too long") after editing only the 7 early
files; the metalogic layer was never reached. Fresh hard-mode research (`reports/03`) then diagnosed
the metalogic breakage precisely and critiqued plan 01. This plan integrates that critique: it
starts from the **preserved WIP patch** (not a clean tree), splits the metalogic work into
one-agent-run phases, replaces plan 01's under-scoped Phase 5 with the named break-site repairs, and
**dissolves** plan 01's Phase 5/6→Phase 8 ordering hazard.

### Research Integration

Grounded primarily in `reports/03_metalogic-obligations-research.md` (see Source-to-Implementation
Mapping and per-phase citations). Key findings that drive this plan:

- **Root cause (F1)**: Every metalogic break traces to one fact — today `𝐆φ ≡ ¬𝐅¬φ` is a *defeq*,
  and MCS/Chronicle proofs silently rely on it via `mcs_not_mem_of_neg`,
  `mcs_mem_iff_neg_not_mem`, and `change`. Promoting the constructor makes those steps
  *disconnected* (fail to type-check), not *false*. Named break sites: `MCS.lean:169/374/229/472`,
  `WitnessSeed.lean:53/65` (`*_neg_absurd`), `RRelation.lean:479-515`, `Seeds.lean:54`,
  `Structures.lean:157`.
- **Settled repair (F2, D1)**: The WIP's four bridge axioms — `allFuture_to_classic`,
  `classic_to_allFuture`, `allPast_to_classic`, `classic_to_allPast` — are **necessary for
  completeness** (adversarially verified: neither direction of `𝐆φ ↔ ¬𝐅¬φ` is derivable from the
  existing BX axioms once G is primitive). The classical equivalences are recovered as
  **axiom-backed theorems** (D3 honesty caveat).
- **Two reusable MCS lemmas (F4, D2)**: `mcs_allFuture_iff` / `mcs_allPast_iff` fix MCS + Chronicle
  centrally; every F1 defeq site routes through them rather than ad-hoc fixes.
- **TruthLemma de-risked (F6, D4)**: The two new inductive cases reduce to the *already-proven*
  standalone `truth_lemma_untl_forward/backward`, `truth_lemma_imp`, `truth_lemma_bot` (which take
  IHs as explicit arguments). **No new canonical-model / coherence lemma is required.** Plan 01's
  "highest risk, largest" Phase 6 is re-graded to medium.
- **Real risk relocated (Recommendation 2)**: The genuine risk concentrates in the defeq-audit
  fan-out — `MCS` + `WitnessSeed` + `RRelation` + `Seeds` + `Structures`. Plan 01's Phase 5 is
  split into 5a (Soundness) / 5b (MCS + WitnessSeed) / 5c (Chronicle repairs). Plan 01 OMITTED
  `WitnessSeed.lean`; its `*_neg_absurd` lemmas are the highest-fan-out breaks and are added here.
- **Ordering hazard dissolved (F8)**: Because the bridge is *axiomatic* and available from the
  ProofSystem layer (Phase 3) onward, MCS (Phase 5) and Chronicle (Phase 6) consume it immediately.
  Plan 01's Phase 5/6→Phase 8 reordering contingency is DELETED.
- **BibKey gap (F0)**: Boudou et al. is absent from `references.bib`; a plan task adds
  `Boudou2017`.

### Prior Plan Reference

`plans/01_primitive-gh-implementation.md` ([PARTIAL], 8 phases). Its Phases 1-4 (Syntax / Semantics /
ProofSystem) survive as the WIP's content and become this plan's P1-P3. Its Phase 5 is split (P4/P5/P6);
its Phase 6 is de-risked (P7); its Phase 8 is split into Tableau verification (P8) and the
theorems + BibKey + full CI (P9). The Phase 5/6→Phase 8 contingency is removed.

### Roadmap Alignment

No `roadmap_path` provided; ROADMAP.md not consulted. Advances the intuitionistic temporal logic
line (companion to 173/176).

## Goals & Non-Goals

**Goals**:
- Add `allFuture`/`allPast` as inductive constructors with direct structural semantics.
- Update every recursive function over `Formula` and the `swapTemporal` duality theorems.
- Add the four bridge axioms and rewire `Instances.lean` (per WIP).
- Add the two reusable MCS lemmas `mcs_allFuture_iff` / `mcs_allPast_iff` and route every defeq
  break site through them.
- Carry the new constructors through Soundness (4 `axiom_sound` arms), MCS, WitnessSeed, Chronicle
  (RRelation/Seeds/Structures), TruthLemma (2 cases via reduction), and Completeness.
- Recover the classical equivalences as axiom-backed theorems in `Theorems.lean`.
- Add `Boudou2017` to `references.bib`.
- Full CI green (`lake build`, `checkInitImports`, `lint-style`, `lake test`, `shake`).

**Non-Goals**:
- Promoting `and`/`or` or `someFuture`/`somePast` to constructors (deliberately kept as-is).
- Deriving `𝐆φ ↔ ¬𝐅¬φ` from the mono axioms (proven underivable, F2 — it must be axiomatic).
- Building an intuitionistic proof system/semantics (this is the enabling step; the classical
  axiomatization plus collapse axioms is retained; the intuitionistic variant drops the collapse
  axioms in future work).
- Changing the Pnueli guard/event convention for U/S.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|-----------|------------|
| Multi-phase single-agent dispatch overflows context ("Prompt is too long") — the documented failure of the first attempt | H | H | Postmortem constraint PM1: exactly ONE phase per agent run. Phases sized small (H8). |
| Build-exclusivity: promoting the constructor breaks the entire Temporal build until P9; interleaving with sibling Temporal tasks (#406, #321) corrupts both | H | H (expected) | PM2: implement #180 ALONE on a green Temporal tree; per-phase verification is a SCOPED `lake build Module`, full green only at P9. |
| WIP `Instances.lean` typeclass rewiring subtly wrong, so `right_mono_until` etc. fail to resolve downstream | H | M | P3 scoped build of `ProofSystem`; P5 canary: rebuild `someFuture_allFuture_neg_absurd` first (F1 highest-fan-out site). |
| `mcs_allFuture_iff` `.mp`/`.mpr` direction mismatch at sites holding the *negated* form (`𝐆ψ ∉ Ω`) | M | M | P5 provides companion `mcs_not_allFuture_iff : 𝐆φ ∉ Ω ↔ 𝐅(¬φ) ∈ Ω` from `mcs_allFuture_iff` + negation-completeness (report R2). |
| F6 step (1) IH-for-`¬φ` picks wrong MCS negation combinator, looping | M | M | Enumerated candidates (`mcs_mem_iff_neg_not_mem`/`mcs_neg_of_not_mem`/`mcs_not_mem_of_neg`, MCS.lean:119-132); test with `lean_multi_attempt` before editing. |
| `𝐆⊥` sites need `neg ⊥ = ⊤` which is not defeq under primitive G | L | M | One-line `simp only [Formula.neg, Formula.top, ...]` at the two `_witness` sites (F4). |
| `DenseSoundness.lean` re-matches Base axioms and needs its own 4 arms | M | L | P4 reads its `match`; delegate to `axiom_sound` if it re-dispatches, else mirror the 4 arms. |
| A single agent run cannot close a metalogic phase (P5c or P7) | M | M | Mark the phase `[PARTIAL]` with exact goal state and missing lemma; re-dispatch `--hard`; never insert `sorry`. |
| Downstream Bimodal/Foundations temporal consumers break at P9 | M | M | P9 sweep builds them; substantial rework is logged as a follow-up task, not force-fit. |

## Preserved-Assets Accounting

The prior attempt produced `wip/01_primitive-gh-wip.patch` (1063 lines, committed, applies cleanly
to HEAD `8833bbd3`, also in `git stash` `task180-wip-primitive-gh`). **This plan starts by applying
the WIP, not from a clean tree.** The patch touches the 7 early files below; the metalogic files it
never reached carry the remaining work (P4-P9).

| Component | File | WIP status | Verified | Consumed by |
|-----------|------|-----------|----------|-------------|
| Constructors + recursive fns + `swapTemporal` duality | `Syntax/Formula.lean` | Provided; builds green standalone per report 02 | Yes (scoped) | P1 (re-verify) |
| Subformula cases | `Syntax/Subformulas.lean` | Provided; edited, not independently verified | No | P1 (verify) |
| Structural G/H semantics | `Semantics/Satisfies.lean` | Provided; edited, incomplete (report 02) | No | P2 (complete + verify) |
| 4 bridge axioms + Base `minFrameClass` | `ProofSystem/Axioms.lean` | Provided (F2 confirms the 4 axioms are present) | No | P3 (verify) |
| Typeclass instance rewiring | `ProofSystem/Instances.lean` | Provided (routes through `classic_to_allFuture`) | No | P3 (verify; canary risk) |
| Tableau edits | `Tableau/Completeness.lean`, `Tableau/Rules.lean` | Provided; edited | No | P8 (complete + verify) |

**Not in the WIP (new work, P4-P9)**: all `Metalogic/*` repairs — Soundness 4 arms, MCS bridge
lemmas + witness repairs, WitnessSeed `*_neg_absurd`, Chronicle RRelation/Seeds/Structures,
TruthLemma 2 cases, Completeness/DenseCompleteness verification, `Theorems.lean` equivalence
wrappers, and the `Boudou2017` BibKey.

**Preserved-work regression bar (PM5)**: no phase may revert or rewrite the WIP-provided early
files except to fix a genuine downstream type error; the WIP's four bridge axioms and
`Instances.lean` rewiring are SETTLED (D1) and must not be re-litigated.

## Implementation Phases

**Build-exclusivity note (read first)**: Promoting the `Formula` constructor in P1 breaks the
entire Temporal build until P9. Phases are therefore **almost entirely sequential** — each phase
depends on the prior phase's module compiling. The wave table below is honest about this: there is
no genuine parallelism except the P8 Tableau subtree, which depends only on ProofSystem (P3) and is
independent of the metalogic chain (P4-P7). Per-phase verification is a **scoped `lake build
Module`**; the full project is legitimately RED between P1 and P9. Full `lake build` + CI runs only
at P9.

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 8 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |
| 8 | 9 | 7, 8 |

Only P8 (Tableau) is genuinely parallelizable with the metalogic chain (both depend on P3). Under
build-exclusivity a single implementer runs one phase per dispatch; the P4/P8 "wave" means P8 may be
scheduled at any point after P3 without blocking P4-P7, not that they run concurrently in one agent.

---

### Phase 1: Apply WIP; verify Syntax (Formula + Subformulas) scoped-green [COMPLETED]

- **Goal:** Apply the preserved WIP patch and establish the Syntax layer as scoped-green — the
  foundation every later phase builds on.
- **Tasks:**
  - [x] Confirm the working tree is clean and the Temporal tree is green at HEAD, then
    `git apply specs/180_temporal_primitive_always_historically/wip/01_primitive-gh-wip.patch`
    (or `git stash apply task180-wip-primitive-gh`).
  - [x] Verify `Syntax/Formula.lean`: constructors `allFuture`/`allPast` present with
    `deriving DecidableEq`; `complexity`/`temporalDepth`/`countImplications`/`swapTemporal`/`atoms`
    handle the new cases; `swapTemporal_involution`, `swapTemporal_allFuture`,
    `swapTemporal_allPast`, `atoms_swapTemporal` compile with no `sorry`.
  - [x] Verify `Syntax/Subformulas.lean` new cases compile; add explicit arms only if the existing
    `cases φ <;> simp [subformulas]` lemmas do not close.
  - [x] `Syntax/Context.lean`: verify no constructor match needs updating (grep showed abbreviation
    use only).
  - [x] Do NOT touch semantics/proof-system/metalogic in this phase.
- **Timing:** 1.5-2 hours
- **Depends on:** none
- **Estimated output:** ~50-150 lines (mostly verification + small fixups; WIP supplies the bulk)
- **Files to modify:** `Cslib/Logics/Temporal/Syntax/{Formula,Subformulas,Context}.lean` (verify/fixup)
- **Scoped verification (done when):**
  - `lake build Cslib.Logics.Temporal.Syntax.Formula` green
  - `lake build Cslib.Logics.Temporal.Syntax.Subformulas` green
  - Mark heading `[COMPLETED]` only after both scoped builds pass.

**Phase 1 result:** WIP patch applied cleanly to all 7 files (Formula, Subformulas, Satisfies,
Axioms, Instances, Tableau/Completeness, Tableau/Rules — no rejects, no fuzz). Both Syntax scoped
builds passed on first attempt with zero fixups needed: `lake build
Cslib.Logics.Temporal.Syntax.Formula` (576 jobs, success) and `lake build
Cslib.Logics.Temporal.Syntax.Subformulas` (577 jobs, success). Constructors, `deriving
DecidableEq`, all five recursive-function cases (`complexity`, `temporalDepth`,
`countImplications`, `swapTemporal`, `atoms`), and all four duality theorems
(`swapTemporal_involution`, `swapTemporal_allFuture`, `swapTemporal_allPast`, `atoms_swapTemporal`)
verified present and `sorry`-free by grep + green build. `Context.lean` has only a docstring
mention of `allFuture`, no constructor match — no change needed. No deviations from plan.

---

### Phase 2: Semantics — structural Satisfies clauses scoped-green [COMPLETED]

- **Goal:** Complete the WIP's `Satisfies.lean` edits so the structural G/H clauses are total and
  the characterization lemmas are definitional.
- **Tasks:**
  - [x] `Satisfies.lean` `Satisfies`: ensure `| .allFuture φ => ∀ s, t < s → Satisfies M s φ` and
    `| .allPast φ => ∀ s, s < t → Satisfies M s φ` are present and total.
  - [x] Re-prove `allFuture_iff` (`:151`) / `allPast_iff` (`:165`) structurally
    (`simp only [Satisfies]` / `Iff.rfl`); statements unchanged. Keep `@[simp]` consistent with
    `someFuture_iff`/`somePast_iff`.
  - [x] Add the semantic bridge lemma
    `sat_allFuture_iff_neg_someFuture_neg : Sat M t (𝐆φ) ↔ Sat M t (¬𝐅¬φ)` (and past dual) from
    `allFuture_iff` + `someFuture_iff` + `Classical.not_exists`/`not_not` (F3). This is consumed by
    the TruthLemma (P7) and mirrors the P4 soundness arms.
  - [x] `Semantics/Validity.lean` / `Model.lean`: verify no constructor match needs updating.
- **Timing:** 1.5-2 hours
- **Depends on:** 1
- **Estimated output:** ~100-200 lines
- **Files to modify:** `Cslib/Logics/Temporal/Semantics/{Satisfies,Validity}.lean`
- **Scoped verification (done when):**
  - `lake build Cslib.Logics.Temporal.Semantics.Satisfies` green
  - `lake build Cslib.Logics.Temporal.Semantics.Validity` green
  - `allFuture_iff`/`allPast_iff` reduce definitionally; `sat_allFuture_iff_neg_someFuture_neg`
    compiles with no `sorry`.

**Phase 2 result:** `Satisfies.lean`'s `Satisfies` match already carried the total
`.allFuture`/`.allPast` structural clauses from the P1 WIP apply, and `allFuture_iff`/`allPast_iff`
were already `Iff.rfl` (stronger than the plan's `simp only [Satisfies]` fallback — both compile
and reduce definitionally). Verified `lake build …Satisfies` green on the pre-existing content
before adding new work. Added `sat_allFuture_iff_neg_someFuture_neg` and
`sat_allPast_iff_neg_somePast_neg` (past dual) to `Satisfies.lean`, proved via `allFuture_iff`/
`neg_iff`/`someFuture_iff` (resp. past duals) with classical `by_contra` — no `Classical.not_exists`
import needed, `by_contra` sufficed. `lean_verify` on both: axioms = `{propext, Classical.choice,
Quot.sound}` only (no new axioms). `Validity.lean`/`Model.lean` have no `Formula` constructor match
— verified via grep, no change needed. Both scoped builds green:
`lake build Cslib.Logics.Temporal.Semantics.Satisfies` (578 jobs) and
`lake build Cslib.Logics.Temporal.Semantics.Validity` (638 jobs). No `sorry` in either file
(grep-verified). `lake exe lint-style` flagged 2 pre-existing unrelated errors in
`Cslib/Logics/Modal/Tableau/Completeness.lean` (space-before-semicolon) — confirmed via
`git diff --stat` that only `Satisfies.lean` was touched this phase; the Modal errors predate this
dispatch and are out of scope. No deviations from plan.

---

### Phase 3: ProofSystem — bridge axioms + Instances scoped-green [NOT STARTED]

- **Goal:** Establish the four bridge axioms and the rewired instances as scoped-green — the
  axiomatic foundation the entire metalogic repair consumes.
- **Tasks:**
  - [ ] `Axioms.lean`: verify the WIP's four bridge axioms `allFuture_to_classic`,
    `classic_to_allFuture`, `allPast_to_classic`, `classic_to_allPast` are present and elaborate;
    confirm they fall under the `_ => .Base` `minFrameClass` fallback (`Axioms.lean:233`) with no
    explicit arm needed (F2).
  - [ ] `Instances.lean`: verify the typeclass rewiring (`HasAxiomLeftMonoUntilG` etc.) routes
    through `classic_to_allFuture`; confirm `right_mono_until` and friends still resolve.
  - [ ] `Derivation.lean`, `Derivable.lean`: build; fix any constructor-match or `Formula`-recursive
    helper needing the new arms.
  - [ ] Confirm notation scoping (`𝐆`/`𝐇`) still resolves to the constructors.
- **Timing:** 1.5-2 hours
- **Depends on:** 2
- **Estimated output:** ~50-150 lines (verification-heavy; WIP supplies axioms/instances)
- **Files to modify:** `Cslib/Logics/Temporal/ProofSystem/{Axioms,Instances,Derivation,Derivable}.lean`
- **Scoped verification (done when):**
  - `lake build Cslib.Logics.Temporal.ProofSystem` green
  - The four bridge axioms are usable via `.axiom [] _ (.allFuture_to_classic φ) trivial` (spot-check
    with `lean_multi_attempt`).

---

### Phase 4: Metalogic — Soundness + DenseSoundness (4 axiom_sound arms) [NOT STARTED]

- **Goal:** Prove the four bridge axioms sound by adding four `axiom_sound` match arms; extend
  `DenseSoundness` only if it re-matches Base axioms. Self-contained (F5).
- **Tasks:**
  - [ ] `Soundness.lean` `axiom_sound` (`:75`): add arms `allFuture_to_classic`,
    `classic_to_allFuture`, `allPast_to_classic`, `classic_to_allPast`. Both sides denote
    `∀ s>t, Sat s φ`; use the `allFuture_iff`/`someFuture_iff` idiom (file uses it at `:87,:267,:408`).
    Tune `simp` sets against `Satisfies.imp_iff`/`neg_iff` (verified present, `:87,:114`).
  - [ ] `DenseSoundness.lean`: read its `match`; if it re-dispatches Base axioms to `axiom_sound`,
    no change; if it re-matches, mirror the 4 arms (`minFrameClass = .Base`, no dense side
    conditions).
- **Timing:** 2-3 hours
- **Depends on:** 3
- **Estimated output:** ~120-250 lines (4 arms + possible dense mirror)
- **Files to modify:** `Cslib/Logics/Temporal/Metalogic/{Soundness,DenseSoundness}.lean`
- **Scoped verification (done when):**
  - `lake build Cslib.Logics.Temporal.Metalogic.Soundness` green
  - `lake build Cslib.Logics.Temporal.Metalogic.DenseSoundness` green
  - `lean_verify` on `axiom_sound`: no `sorry`, no new axioms.

---

### Phase 5: Metalogic — MCS bridge lemmas + MCS/WitnessSeed defeq repairs [NOT STARTED]

- **Goal:** Add the two central MCS bridge lemmas and repair the highest-fan-out defeq break sites
  in `MCS.lean` and `WitnessSeed.lean`. **This is the genuine risk concentration (report Rec. 2).**
- **Tasks:**
  - [ ] `MCS.lean`: add `mcs_allFuture_iff` and `mcs_allPast_iff` (F4) from
    `temporal_implication_property` (`:79`) + `theoremInMcs` (`:97`) + the bridge axioms; add
    companion `mcs_not_allFuture_iff : 𝐆φ ∉ Ω ↔ 𝐅(¬φ) ∈ Ω` (+ past dual) via negation-completeness
    for negated-form sites (Risk R2).
  - [ ] Repair the defeq sites `mcs_g_mp` (`:169`), `mcs_g_witness` final (`:374`),
    `mcs_h_mp`/`mcs_h_witness` (`:229,:472`), and `derive_g_contradiction`/`derive_h_contradiction`:
    replace each broken `mcs_not_mem_of_neg`/`mcs_mem_iff_neg_not_mem` step with a rewrite through
    the new lemmas. `𝐆⊥` sites additionally use `neg ⊥ = ⊤` (one-line `simp`).
  - [ ] **Canary first**: repair `WitnessSeed.lean` `someFuture_allFuture_neg_absurd` (`:53`) — the
    highest-fan-out site — before the rest; convert `h_G_neg : 𝐆(¬ψ) ∈ M` to `¬(𝐅¬¬ψ) ∈ M` via
    `mcs_allFuture_iff` before the final `mcs_not_mem_of_neg`. Then
    `somePast_allPast_neg_absurd` (`:65`).
  - [ ] Keep the `*_neg_absurd` lemma **signatures** stable (D4) so Chronicle consumers
    (`OrderedSeedConsistency`, `Splitting`, `Structures`) are untouched.
  - [ ] Audit `TemporalContent.lean` / `DenseMCS.lean` for the same defeq class (grep hits); rewrite
    low-volume sites via the bridge. Verify `GenericMCSBridge.lean` needs no change (operator-agnostic).
- **Timing:** 3-4 hours
- **Depends on:** 4
- **Estimated output:** ~200-350 lines (2 lemmas + companion + ~6 site repairs)
- **Files to modify:** `Cslib/Logics/Temporal/Metalogic/{MCS,WitnessSeed,TemporalContent,DenseMCS}.lean`
- **Scoped verification (done when):**
  - `lake build Cslib.Logics.Temporal.Metalogic.MCS` green
  - `lake build Cslib.Logics.Temporal.Metalogic.WitnessSeed` green
  - `lean_verify` on the two new lemmas + repaired sites: no `sorry`.
  - If a single run cannot close all sites: mark `[PARTIAL]` with the exact remaining site, re-dispatch.

---

### Phase 6: Metalogic — Chronicle defeq-site repairs (RRelation/Seeds/Structures) [NOT STARTED]

- **Goal:** Route the remaining Chronicle defeq breaks through the P5 bridge lemmas; the proof
  bodies are otherwise unchanged (F3).
- **Tasks:**
  - [ ] `Chronicle/RRelation.lean`: `neg_allFuture_neg_to_someFuture` (`:499`),
    `neg_allPast_neg_to_somePast` (`:479`) — insert `mcs_allFuture_iff`/`mcs_allPast_iff` to convert
    the input membership `¬(𝐆¬γ) ∈ M` back into the U/S world; the DNE + `right_mono_until` body
    (`:503-515`) is unchanged.
  - [ ] `Chronicle/PointInsertion/Seeds.lean`: `:54` replace the "definitionally allFuture φ ∈ A"
    defeq conversion with `mcs_allFuture_iff`; `:92-113` G-DNE seed steps already use
    `right_mono_until` + necessitation — only the defeq membership hop breaks.
  - [ ] `Chronicle/CounterexampleElimination/Structures.lean`: `:157` replace
    `change Formula.allFuture φ ∈ A` with `(mcs_allFuture_iff …).mp/.mpr`.
  - [ ] `Chronicle/Frame.lean` (`:62,:72`): verify only — structural map over the constructor still
    works.
  - [ ] Verify consumers `OrderedSeedConsistency.lean`, `PointInsertion/Splitting.lean`,
    `PointInsertion/Since.lean` are untouched (signatures preserved in P5).
- **Timing:** 2.5-3.5 hours
- **Depends on:** 5
- **Estimated output:** ~150-300 lines (targeted site rewrites)
- **Files to modify:** `Cslib/Logics/Temporal/Metalogic/Chronicle/{RRelation,Frame}.lean`,
  `Chronicle/PointInsertion/Seeds.lean`, `Chronicle/CounterexampleElimination/Structures.lean`
- **Scoped verification (done when):**
  - `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation` green
  - `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Seeds` green
  - `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.Structures` green
  - No `sorry` introduced.

---

### Phase 7: Metalogic — TruthLemma two cases via reduction [NOT STARTED]

- **Goal:** Add the `allFuture`/`allPast` inductive cases to `chronicle_truth_lemma` by REDUCTION to
  the existing standalone case lemmas. **Re-graded medium (F6), not "highest risk" as in plan 01.**
- **Tasks:**
  - [ ] `Chronicle/TruthLemma.lean`: add `truth_lemma_allFuture` (F6 sketch): from the single IH
    `ih_φ`, derive IHs for `¬φ` and `⊤` (via MCS negation-completeness — enumerate the combinator
    with `lean_multi_attempt` first, Risk R3), assemble the compound `¬(⊤ U ¬φ)` truth lemma via
    `truth_lemma_imp` (`:75`) + `truth_lemma_untl_backward` (`:141`) + `truth_lemma_untl_forward`
    (`:120`) + `truth_lemma_bot` (`:66`), then bridge both sides to primitive `𝐆φ` via
    `sat_allFuture_iff_neg_someFuture_neg` (P2) and `mcs_allFuture_iff` (P5).
  - [ ] `truth_lemma_allPast`: mirror via `truth_lemma_snce_forward/backward` (`:171,:189`) and
    `mcs_allPast_iff`; or `swapTemporal` duality if a symmetry combinator exists.
  - [ ] Add the two arms to `chronicle_truth_lemma` (`:216`):
    `| allFuture φ ih_φ => exact truth_lemma_allFuture …`, `| allPast φ ih_φ => …`.
  - [ ] Confirm the guard/event slot mapping `𝐅X = untl ⊤ X` against `someFuture φ = untl ⊤ φ`
    (`Formula.lean:68`) — the `truth_lemma_untl_*` lemmas are stated for `ψ U φ` with `φ` the event
    (F6 caveats).
  - [ ] **No new canonical-model / coherence lemma** (D4): the coherence content is already
    discharged by `truth_lemma_untl_backward`.
- **Timing:** 3-4 hours
- **Depends on:** 6
- **Estimated output:** ~150-300 lines (2 reduction lemmas + 2 arms)
- **Files to modify:** `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean`
- **Scoped verification (done when):**
  - `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma` green
  - `lean_verify` on `chronicle_truth_lemma`, `truth_lemma_allFuture`, `truth_lemma_allPast`: no
    `sorry`, no axioms beyond those already accepted in the file.
  - If a single run stalls: mark `[PARTIAL]` with the exact open goal and missing combinator;
    re-dispatch `--hard`. Never insert `sorry`.

---

### Phase 8: Tableau subtree scoped-green [NOT STARTED]

- **Goal:** Complete the WIP's Tableau edits and add G/H constructor cases. Independent of the
  metalogic chain (depends only on P3) — may be scheduled any time after P3.
- **Tasks:**
  - [ ] `Tableau/Defs.lean`: add `allFuture`/`allPast` arms to `temporalFormulaHash` and the
    decomposition matchers (the `.imp …`-pattern extractors near `:109-164`); decide the universal
    expansion rule for primitive G/H.
  - [ ] `Tableau/Rules.lean` (WIP-edited), `Tableau/Completeness.lean` (WIP-edited),
    `Tableau/{Closure,Branch,Saturation,Soundness,TimeOrdering}.lean`: add G/H handling where they
    recurse on constructors or reference the abbreviations.
- **Timing:** 2-3 hours
- **Depends on:** 3
- **Estimated output:** ~150-300 lines
- **Files to modify:** `Cslib/Logics/Temporal/Tableau/{Defs,Rules,Closure,Branch,Saturation,Soundness,Completeness,TimeOrdering}.lean` (as needed)
- **Scoped verification (done when):**
  - `lake build Cslib.Logics.Temporal.Tableau.Defs` green
  - `lake build Cslib.Logics.Temporal.Tableau.Soundness Cslib.Logics.Temporal.Tableau.Completeness` green

---

### Phase 9: Classical-equivalence theorems + Boudou2017 BibKey + FULL CI [NOT STARTED]

- **Goal:** Package the classical equivalences as axiom-backed theorems, add the missing BibKey, run
  the downstream sweep, and pass the full CI pipeline. **This is the only phase that runs full
  `lake build`; full green returns here.**
- **Tasks:**
  - [ ] `Theorems.lean`: add
    `allFuture_iff_neg_someFuture_neg : DerivationTree FrameClass.Base [] (𝐆φ ↔ ¬𝐅¬φ)` and the past
    dual, as thin wrappers packaging the two bridge-axiom directions into an `Iff` (F8, D3). Note in
    the docstring the D3 honesty caveat: conservativity is asserted by (sound) axiom, not proved.
  - [ ] `Completeness.lean` / `DenseCompleteness.lean`: verify they carry through unchanged once
    TruthLemma is total (F7) — no constructor match; build-only.
  - [ ] Add `Boudou2017` to `references.bib` (root): Boudou, Diéguez & Fernández-Duque (2017),
    *A decidable intuitionistic temporal logic*, CSL 2017 (F0). Optionally flag the also-absent
    Burgess 1982 (`TruthLemma.lean:34`) as a follow-up.
  - [ ] Downstream sweep: build `Cslib.Logics.Bimodal.Embedding.TemporalEmbedding`, Bimodal
    metalogic/syntax temporal files, `Cslib.Foundations.*Temporal*`. Fix mechanical breakage; log a
    follow-up task if a consumer needs substantial rework.
  - [ ] Update `Cslib.lean` barrel via `lake exe mk_all --module` if any file was added (none
    expected).
  - [ ] Run the full CI pipeline (below).
- **Timing:** 2.5-3.5 hours
- **Depends on:** 7, 8
- **Estimated output:** ~150-300 lines (theorems + BibKey + downstream fixups)
- **Files to modify:** `Cslib/Logics/Temporal/Theorems.lean`,
  `Cslib/Logics/Temporal/Metalogic/{Completeness,DenseCompleteness}.lean` (verify),
  `references.bib`, `Cslib/Logics/Bimodal/**` and `Cslib/Foundations/**Temporal**` (as needed).
- **Full CI verification (done when, in order):**
  - `lake exe cache get`
  - `lake build` (whole project green — first full green since P1)
  - `lake exe checkInitImports`
  - `lake exe lint-style`
  - `lake test`
  - `lake shake --add-public --keep-implied --keep-prefix`

---

## Testing & Validation

Per-phase (scoped, mandatory before marking any phase `[COMPLETED]`):
- [ ] P1: `lake build …Syntax.Formula` and `…Syntax.Subformulas` green.
- [ ] P2: `lake build …Semantics.Satisfies` and `…Semantics.Validity` green; `allFuture_iff`
  definitional.
- [ ] P3: `lake build …ProofSystem` green; bridge axioms usable.
- [ ] P4: `lake build …Metalogic.Soundness` and `…DenseSoundness` green.
- [ ] P5: `lake build …Metalogic.MCS` and `…WitnessSeed` green.
- [ ] P6: `lake build …Chronicle.{RRelation, PointInsertion.Seeds, CounterexampleElimination.Structures}` green.
- [ ] P7: `lake build …Chronicle.TruthLemma` green; `lean_verify` clean.
- [ ] P8: `lake build …Tableau.{Defs, Soundness, Completeness}` green.

Final (P9, full CI):
- [ ] `lake build` green for the whole project.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` clean on all modified files (docstrings on new constructors, axioms,
  theorems).
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no import regressions.
- [ ] `lean_verify` on TruthLemma, Completeness, Soundness, and the new equivalence theorems: no new
  `sorry`; the only new axioms are the four intended bridge axioms.
- [ ] Classical equivalences `𝐆φ ↔ ¬𝐅¬φ`, `𝐇φ ↔ ¬𝐏¬φ` derivable as theorems.
- [ ] `Boudou2017` present in `references.bib`.

## Source-to-Implementation Mapping (H3, Tier 1)

| Source / finding | BibKey | Lean target | Phase | Translation notes |
|------------------|--------|-------------|-------|-------------------|
| G and F are *independent* primitives (intuitionistic temporal logic) | Boudou2017 *(add in P9)* | `Formula.allFuture`/`allPast` constructors | P1 | Design rationale (report 01); bridge axioms encode the classical collapse Boudou et al. reject. |
| Classical `𝐆φ ↔ ¬𝐅¬φ` duality — underivable once G primitive (F2) | folklore (Prior/Burgess) | `Axiom.allFuture_to_classic`/`classic_to_allFuture` (+ past duals) | P3 | Must be axiomatic; sound (P4); recovered as one-step theorem (P9). |
| Root-cause defeq breakage (F1) | reports/03 F1 | `MCS.lean:169/374/229/472`, `WitnessSeed.lean:53/65`, `RRelation.lean:479-515`, `Seeds.lean:54`, `Structures.lean:157` | P5, P6 | Route each site through `mcs_allFuture_iff`/`mcs_allPast_iff`. |
| Two reusable MCS bridge lemmas (F4) | reports/03 F4 | `mcs_allFuture_iff`/`mcs_allPast_iff` in `MCS.lean` | P5 | From `temporal_implication_property` + `theoremInMcs` + bridge axioms. |
| Soundness of the 4 bridge axioms (F5) | reports/03 F5 | `axiom_sound` arms in `Soundness.lean` | P4 | Both sides denote `∀ s>t, Sat s φ`. |
| TruthLemma reduction, no new coherence lemma (F6, D4) | reports/03 F6; Burgess 1982 (`TruthLemma.lean:34`, also absent from `references.bib`) | `truth_lemma_allFuture`/`allPast`; arms in `chronicle_truth_lemma` | P7 | Reuse `truth_lemma_untl_forward/backward`, `truth_lemma_imp`, `truth_lemma_bot` (explicit-IH lemmas). |
| Ordering hazard dissolved (F8) | reports/03 F8 | `Theorems.lean` wrappers only | P9 | Bridge axiomatic from P3, so no reordering; classical equivalences packaged last. |

## Artifacts & Outputs

- `specs/180_temporal_primitive_always_historically/plans/03_primitive-gh-metalogic-plan.md` (this plan)
- Modified Lean sources across `Cslib/Logics/Temporal/{Syntax,Semantics,ProofSystem,Metalogic,Tableau}/`
  plus `Theorems.lean`; `references.bib`; any affected Bimodal/Foundations temporal consumers.
- `specs/180_temporal_primitive_always_historically/summaries/03_primitive-gh-metalogic-summary.md` (on completion)

## Rollback/Contingency

- **Rollback anchor:** the WIP patch + `git stash` entry `task180-wip-primitive-gh` are the
  rollback anchor. All changes are in-place source edits with no new files; revert with
  `git checkout -- Cslib/Logics/Temporal/ references.bib` (and drop any task branch). The clean,
  green HEAD `8833bbd3` is always recoverable.
- **Build-green ordering (expected, not failure):** the full project is RED from P1 through P8; each
  phase verifies only its scoped `lake build Module`. Full `lake build` runs only at P9. This is by
  design (build-exclusivity).
- **Phase 5/6→Phase 9 ordering hazard: DISSOLVED (F8).** The bridge is axiomatic and available from
  P3; MCS/Chronicle consume it immediately. Do NOT attempt to reorder Phase 9 earlier or inline a
  local equivalence — this was plan 01's contingency and it is deleted.
- **Metalogic phase stall (P5c-style fan-out, or P7):** if a single agent run cannot close the phase,
  mark the `### Phase N` heading `[PARTIAL]` with the exact open goal state and the missing
  lemma/combinator; re-dispatch that single phase `--hard`. Never insert `sorry` or vacuous
  definitions. Do not advance to the next phase while the current one is RED.
- **Downstream consumer breakage (P9):** if a Bimodal/Foundations consumer needs rework beyond
  mechanical case additions, log a follow-up task and scope the consumer fix separately; the Temporal
  subtree may reach `[PR READY]` independently.

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from `reports/02` (parked-attempt
constraints), `reports/03` (metalogic research + plan-01 critique), and prior-plan failure modes.

**Do NOT**:
- **PM1 — No multi-phase single-agent dispatch.** Dispatch exactly ONE phase per agent run. The
  first attempt tried the whole task in one run and overflowed context ("Prompt is too long"). This
  is the single most important rule.
- **PM2 — No interleaving with sibling Temporal tasks.** #180 promotes the `Formula` constructor,
  which breaks the entire Temporal build until P9. Never run it concurrently with #406, #321, or any
  task that builds Temporal modules. Implement it ALONE on an otherwise-green Temporal tree.
- **PM3 — No `sorry`, no vacuous definitions, no axioms beyond the four intended bridge axioms.** If
  a phase cannot close, mark it `[PARTIAL]` and re-dispatch; do not fake green.
- **PM4 — Do NOT re-derive `𝐆φ ↔ ¬𝐅¬φ` from the mono axioms.** It is proven underivable (F2); it
  MUST be axiomatic. Do not spend dispatch budget attempting a derivation.
- **PM5 — Do NOT rewrite or revert the WIP-provided early files** (Formula/Subformulas/Satisfies/
  Axioms/Instances/Tableau) except to fix a genuine downstream type error. Start from the applied
  WIP, not a clean tree.
- **PM6 — Do NOT reorder Phase 9 earlier** or inline a local classical-equivalence lemma into
  P5/P6/P7. The F8 ordering hazard is dissolved; the bridge is axiomatic from P3.

**MUST preserve**:
- The 1063-line WIP patch content across the 7 early files (Preserved-Assets Accounting).
- The four bridge axioms and the `Instances.lean` rewiring (SETTLED, D1).
- The stable signatures of `WitnessSeed` `*_neg_absurd`, `RRelation`, `Seeds`, `Structures` lemmas
  so Chronicle consumers stay untouched (D4).
- All existing no-`sorry` metalogic proofs — repairs reconnect them, they do not weaken them.

**Verification discipline (MUST)**:
- **PM7 — Scoped-green per phase, full-green only at P9.** Mark each `### Phase N` heading
  `[COMPLETED]` ONLY after that phase's scoped `lake build Module` passes. Intermediate full-project
  RED is expected and legitimate.
- **PM8 — Canary the fan-out.** In P5, rebuild `someFuture_allFuture_neg_absurd`
  (WitnessSeed.lean:53) first — it is the highest-fan-out defeq site; if it compiles, the Chronicle
  fan-out largely follows.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **D1** — Four bridge axioms are the canonical mechanism (alternative: deriving the equivalence —
  rejected, proven underivable F2).
- **D2** — Exactly two reusable MCS lemmas `mcs_allFuture_iff`/`mcs_allPast_iff`; route all defeq
  sites through them (alternative: ad-hoc per-site fixes — rejected as unmaintainable).
- **D3** — Classical equivalences are axiom-backed theorems; conservativity is asserted by sound
  axiom, not proved. State this plainly in the PR description.
- **D4** — TruthLemma via reduction to existing standalone case lemmas; no new chronicle coherence
  lemma (alternative: new canonical construction — rejected, the coherence content is already in
  `truth_lemma_untl_backward`).
