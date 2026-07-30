# Implementation Plan: Task #430 — Gate B2, Statement-Shape Fix, then the Persistence Export

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Status**: [IMPLEMENTING]
- **Effort**: Phases 1-4 complete (3 dispatches, landed and committed). Phase 5 (Gate B2) ~1
  dispatch, **gating**. Phase 6 ~1 dispatch, independent. Phases 7-14: deliberately not given a
  firm aggregate budget — see "On cost estimates" in the Overview. Per-phase Timing lines are
  sizing targets (one agent run each), not a total.
- **Dependencies**: None blocking at dispatch time. Task 317's Route (a) frame plumbing has
  landed. Task 585 (DP-2) has **retired** its sorry (confirmed by direct grep at the Phase 3/4
  commits) — DP-2 remains that task's territory and must not be touched. Phases 3-4 of this plan
  touched task 574's settled work by coordinated agreement; that coordination is discharged and
  does not recur below.
- **Research Inputs**:
  - `reports/05_phase5-blocker-research.md` (**newly integrated — the blocker-escalation research
    driving this revision**; verdict `tractable_large`, NOT refuted)
  - `.blocker-research.json` (**newly integrated** — structured form of the above)
  - `scratch/HvalidShapeRefutation.lean` (**newly integrated** — machine-verified refutation
    artifact, `lake env lean` clean, zero sorries)
  - `handoffs/03_phase5-investigation-and-partial-progress.md` (**newly integrated** — Phase 5's
    partial-progress findings, superseding plan 04's Phase 5 draft)
  - `handoffs/01_gate-a-variant-selection.md` (Gate A verdict and measurement tables)
  - `handoffs/02_gate-b-verdict.md` (Gate B verdict, PASS conditional)
  - `specs/317_propositional_tableau_completeness/reports/17_timp-continuation-options.md`
    (the decision record driving plan 04)
  - `reports/01_atom-persistence-upward-closure.md` (seed)
  - `reports/02_team-research.md` (team, 4 teammates)
  - `reports/03_falsification-spike.md` (empirical)
  - `specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md`
    (probe methodology, reused by Gate A and reusable by Gate B2)
  - `specs/574_tableau_calculus_repair_ancestor_blocking/reports/01_phase6-blocker-resolution.md`
    (the in-repo quotient refutation)
- **Artifacts**: plans/06_gate-b2-then-origin-tracing-export.md (this file). Supersedes
  plans/04_positive-formula-persistence-augmented.md, which is preserved unmodified for history.
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md;
  lean4.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The goal is unchanged from plan 04: prove **positive-formula persistence along the augmented
accessibility relation** and use it to discharge three sorries at once.

```
∀ φ w w', w ≤ w' → T(φ)@w ∈ b → T(φ)@w' ∈ b
```

where `≤` is `intAccessPreorder edges` over the **augmented** edge list (the `augSets` witness
threaded through `intExpandBranches_openBranch_sat`) — not the algorithm's raw `edgeSets`.

**What changed in this revision.** Plan 04's Phase 5 returned `[PARTIAL]` with a blocker:
exporting augmented-edge persistence appeared to require an `IWorldHist`-scale origin-tracing
build-out, and the dispatch stopped rather than risk an unsound shortcut. Blocker research
(`reports/05`) returned verdict **`tractable_large` — NOT refuted** and changed the plan in three
ways:

1. **DP-3 and DP-4 are unprovable AS STATED — machine-verified, and independent of all
   persistence work.** `tableau_complete`'s `hvalid` premise (`Scheme.lean:7446`) quantifies over
   *arbitrary* `edges` and *arbitrary* `b` with no tableau provenance, while `IValid` supplies
   forcing only for upward-closed valuations. `scratch/HvalidShapeRefutation.lean` (`lake env
   lean` clean, zero sorries) proves `IValid (p → (q → p))` **and** refutes `hvalid`'s body at
   `edges=[(1,0)]`, `b=[T(p)@0, T(q)@1]`. The theorems themselves are not refuted — only the
   proof route, because `apply tableau_complete` discards `b`'s provenance. A signature change is
   therefore **mandatory**, and it is independent of the persistence effort. See Phase 6.
2. **A new refutation risk Gate B never considered.** Edges are `(child, parent)`; the reuse arm
   appends `(x, l)` with `l = w`, giving `w ≤ x`, while the reuse check already requires raw
   `x ≤ w`. So `x` and `w` are preorder-**equivalent** in the augmented frame and must *agree* on
   atoms. If both carry the same disjunction, their beta-splits are separate signed formulas
   expanded independently: one open branch can pick `T(r)@w` and `T(s)@x`, the copy channel gives
   `w` both but `x` only `s`, and `w ≤ x` then demands the missing `T(r)@x`. The reuse check is
   never re-run to invalidate the recorded edge. **Flagged UNVERIFIED** — no concrete `φ0`
   realizes it yet, and expansion ordering may prevent it. If realizable, the statement is
   **false** and permanent deferral of all three sorries is the terminal answer. This is why
   Phase 5 (Gate B2) gates everything below.
3. **Genuine de-risking.** The reuse check at `Expansion.lean:296-307` already enforces exactly
   the backward containment the loop-back edge needs: `sfor` **is** `{φ} ∪ posFormulasAt bPers w`,
   and the check requires it inside `posFormulasAt bPers x`. Since `bPers` is the fixpoint, `w`
   has already received every raw-ancestor copy (Phase 4's landed copy-completeness lemmas). The
   gap is therefore purely **temporal** — post-reuse arrivals — not "build `IWorldHist` again".
   And `IWorldHist`'s `par`/(H0)/(H1)/(H1-acc) already supply Gate B's assumed `ForestComparable`
   for free: an **export**, not a construction.

**Structure: one gating probe, one independent statement-shape fix, then the build-out.**
Phase 5 (Gate B2) is the option-killer and is scratch-only. Phase 6 is a statement-shape
correction the research explicitly authorizes to run in parallel with Phase 5, because it is
independent of all persistence work. **Phases 7-13 are the build-out and none of them may begin
before Phase 5 returns a verdict** — see "Gating contract" below. If Gate B2 refutes, permanent
deferral of DP-3/DP-4/DP-5 is the **sanctioned terminal answer**, and escalation to the
quotient/blocking-frame route remains prohibited.

**Line-number correction** (research report 05, verified by content): DP-5 is at
**`Scheme.lean:727`**, not `:633` as the task description and plan 04 both state. Exactly **3**
bare sorries remain in this task's scope: DP-3 (`Intuitionistic/Completeness.lean:140`), DP-4
(`Minimal/Completeness.lean:128`), DP-5 (`Scheme.lean:727`).

**On cost estimates.** Report 17's 600-1200 line figure was marked low confidence by its own
author and is still not used as a budget here. No phase below is sized against it. Phase-level
sizing uses per-phase Scope Hypotheses, confirmed at implementation time.

### Gating contract (Phase 5)

This is the single most important structural fact in this plan.

| Phase | May begin before Gate B2 returns a verdict? | Why |
|---|---|---|
| 5 (Gate B2) | — | It *is* the gate. Scratch-only; zero `Cslib/` writes. |
| 6 (statement-shape fix) | **YES** | Not build-out. It relocates a *mis-stated* obligation to where `b`'s provenance is in scope. Report 05 §1/§5 states it is independent of Gate B2 and of all persistence work, and it is a correctness improvement even under permanent deferral (the remaining sorry becomes honestly stated instead of unfillable). |
| 7, 8, 9, 10, 11 (build-out) | **NO** | These build the persistence machinery Gate B2 may refute outright. Starting any of them before the verdict risks spending an `IWorldHist`-scale effort on a false statement. |
| 12, 13 (discharges) | **NO** | They consume the build-out. |
| 14 (final CI) | **NO** | Terminal gate. |

A dispatch that opens Phase 7 (or any later build-out phase) without a recorded Gate B2 verdict in
`handoffs/04_gate-b2-verdict.md` is executing this plan incorrectly, regardless of how promising
the approach looks.

### Research Integration

Newly integrated in this revision:

- **`reports/05_phase5-blocker-research.md`** — the blocker-escalation research. Verdict
  `tractable_large`, NOT refuted. Findings consumed: the machine-verified `hvalid` statement-shape
  defect (§1 → Phase 6); the beta-split refutation risk and its probe design (§4 → Phase 5); the
  reuse-check containment de-risking discovery (§3 → Phases 8-9); the `IWorldHist` reuse audit
  (§2 → the Reusable Declarations table below); the 9-step decomposition (§5 → Phases 5-14); the
  line-number corrections (DP-5 at `:727`).
- **`.blocker-research.json`** — the structured verdict, including the explicit
  `weaker_sufficient_statement` (attempt saturation + copy-completeness before full origin
  tracing) and the `must_build_new` list, which Phases 8-11 map onto one-for-one.
- **`scratch/HvalidShapeRefutation.lean`** — the machine-verified refutation artifact. This is
  *evidence*, not conjecture: Phase 6 exists because a compiled Lean file proves the current
  route cannot work, not because a reviewer suspected it.
- **`handoffs/03_phase5-investigation-and-partial-progress.md`** — Finding 1 (the raw-edge
  terminal fact is cheap, from already-threaded `IAllUniv`/`IAllFuel` plus Phase 4's landed
  lemmas) becomes Phase 7 and **must not be re-derived**. Finding 2 (the augmented-edge case is
  the genuine gap, independently re-confirmed from live `genCopies` code) motivates Phases 8-11.

All `[UNVERIFIED]` markers from report 05 are respected verbatim and appear in Risks below. The
two most consequential are the beta-split refutation risk (Phase 5's whole reason for existing)
and the weaker-sufficient-statement route (Phase 9's first attempt, with Phase 10 as the declared
fallback).

### Preserved from plan 04 — complete, CI-verified, committed

Phases 1-4 below are carried forward as **done**, not re-planned. They are landed and committed
(`e52f2624`, `611e8f9d`, `8f504c77`) and their content is recorded in plan 04 in full detail; the
phase bodies below are deliberately abbreviated to their outcomes and preserved assets.

- **Gate A**: V4 (generalized copy channel) selected by measurement and landed.
- **Gate B**: PASS (conditional) — the descendant sub-case closes; the ancestor sub-case is the
  open one. Gate B did **not** consider the beta-split mechanism, which is why Gate B2 exists.
- **Phase 3**: generalized V4 `genCopies` copy channel reinstated in `Expansion.lean` /
  `Scheme.lean` / `Soundness.lean`, full CI green.
- **Phase 4**: `applyAllTImpRules_copy_complete_of_fixpoint` and
  `applyPersistenceFixpoint_copy_complete`, both **sorry-free and axiom-clean**.

Also preserved from plan 04, unchanged in substance: team S2's one-generic-lemma finding (atoms
and `⊥` are the same `b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w)`
shape) → Phase 13; the placement guidance (standalone corollaries, **not** new `IntMinScheme`
fields); the Route C / `≤`-on-ℕ exclusions; and the final-CI phase.

### Reusable declarations (from report 05 §2 — export, not construction)

Recorded here so no phase below re-derives or rebuilds any of it.

| Declaration | Location | Role |
|---|---|---|
| `IWorldHist` `par` witness, (H0) `par 0 = 0`, (H1) `(c, par c) ∈ edges ∧ par c < c` | `Scheme.lean:3213` | A total unique-parent function ⇒ ancestor chains are **linear**. This IS Gate B's assumed `ForestComparable`. Export it. |
| (H1-acc) `parAncestor par c' c → isAccessible edges c' c = true` | `Scheme.lean:3213`ff | The `par`-ancestry → raw-accessibility bridge. Load-bearing for the ancestor sub-case. |
| (H3) `∀ χ ∈ sfor c, χ ∈ posFormulasAt b c` | `Scheme.lean:3213`ff | A monotone planted positive-content fact — the closest existing analogue to what Phase 8 must build. |
| `IWorldHist_mono`, `IWorldHist_entry` | `Scheme.lean:3263`, `:3251` | Branch/expanded-set monotonicity transfer and vacuous entry discharge. Phase 8's companion clause copies this shape. |
| `IAllWorldHist`, `IAllWorldHist_append`, `_map_const`, `IAllWorldHistCounter` family | `Scheme.lean:3330`, `:3280-3328` | List-level plumbing for Phase 8's companion invariant. |
| `IAllUniv` + `_append`/`_map`; `IAllFuel` + `_append`/`_map` | `Scheme.lean:2834`, `:4537` | **Already threaded** through the entire `key` induction. Phase 7 consumes these directly. |
| `applyAllTImpRules_copy_complete_of_fixpoint`; `applyPersistenceFixpoint_copy_complete`; `applyPersistenceFixpoint_genuine_of_count_le_fuel` | `Scheme.lean` (Phase 4 + earlier) | All landed sorry-free. Phase 7's raw-edge conjunct is their composition. |
| `intFImpReuseWitnessAnc?_spec` (five conjuncts, incl. `hcont`) | `Expansion.lean:321` | The reuse-time containment Phase 8 exports. |
| `IBranchSaturation` (`sat_timp` and siblings) | already in `openBranch_sat`'s conclusion | Supplies decomposition closure at `x` for Phase 9's cheap route. |
| `intAccessPreorder_le_of_isAccessible`, `isAccessible_one_step`, `sfAccessSat_edges_mono`, `parAncestor`, `parAncestor_le` | `Scheme.lean:276` and nearby | Order/accessibility plumbing. |

**Explicitly NOT a reuse win** (report 05 §2, verbatim): `intWorldHist_chain_le` (`:3618`),
`pathOf` (`:3798`), `pathOf_some`/`pathOf_none`, `pathOf_injOn` (`:3843`), `intWorldHist_nw_le`
(`:3944`). These are pigeonhole/world-**bound** machinery, largely irrelevant to persistence. Do
not budget them as savings and do not reach for them when a persistence goal looks hard.

## Goals & Non-Goals

**Goals**:
- Resolve, by measurement, whether the augmented-edge persistence statement is **true at all**
  (Phase 5). A refutation is a legitimate, complete outcome of this plan.
- Fix the machine-verified statement-shape defect: strengthen `openBranch_countermodel`'s
  conclusion to carry upward-closure of `intExtractValuation b` along `intAccessPreorder edges`,
  and weaken `tableau_complete`'s `hvalid` to accept it (Phase 6). `tableau_complete` stays
  sorry-free; `Soundness.lean` is untouched.
- Prove positive-formula persistence along `intAccessPreorder augEdges` once and export it in
  `intExpandBranches_openBranch_sat`'s conclusion (Phases 7-11).
- Instantiate at `φ = φ'→ψ'` to close DP-5 (`Scheme.lean:727`), and at `φ = atom p` / `φ = .bot`
  to close DP-3 and DP-4 (Phases 12-13).
- Net effect: both public completeness theorems become sorry-free.
- No new `axiom`s; no statement weakened to dodge a gap; full CI green.

**Non-Goals**:
- Do **not** touch DP-2 (`intFreshMint_preserves_nw`) — task 585 territory, and already retired
  there. Confirm it is untouched at every phase boundary; do not re-prove or re-locate it.
- Do **not** rebuild a quotient / blocking-frame reconstruction under any circumstance, including
  as an escalation after a Gate B2 refutation. See Reasoned Exclusions.
- Do **not** pursue Route C (containment preorder) or `≤`-on-ℕ upward closure — both empirically
  refuted.
- Do **not** re-open task 574's termination design.
- Do **not** dispatch a T-imp-only or atom-only phase (zero public payoff either way).
- Do **not** re-derive handoff 03's Finding 1 (the raw-edge terminal fact) from scratch.
- Do **not** write to `Cslib/` or `CslibTests/` during Phase 5. It is scratch-only.
- Do **not** cite task numbers in any Lean source, docstring, or comment. Durable anchors only
  (lemma names, section headings, file paths). This applies to every phase that edits `Cslib/`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **The beta-split refutation shape is realizable** — independent disjunction splits at `w` and at the reused ancestor `x` leave the two preorder-equivalent worlds disagreeing on atoms, with no mechanism to invalidate the recorded loop-back edge. Report 05 §4, flagged **UNVERIFIED**. **If realizable, the statement is FALSE and all three sorries are permanently deferred.** | Critical | Medium | Phase 5 (Gate B2), gating, scratch-only, run before any build-out. A single failing instance is a refutation. Refutation ⇒ terminal deferral per Rollback/Contingency, NOT escalation. |
| **The weaker sufficient statement collapses back into full origin tracing** at the residual `x ≤ y ≤ w` case (a copy from a raw ancestor `y` of `w` where `y` is *below* `x`). Report 05 §3, flagged **UNVERIFIED**. | High | Medium | Phase 9 attempts the cheap route (saturation + copy-completeness) and is explicitly permitted to return "route collapsed" as its verdict. Phase 10 is the declared fallback, pre-planned rather than improvised mid-dispatch. |
| **Multi-hop composition fails** — a branch can accumulate several reuse events, and Gate B never re-checked that a single-hop transfer lemma composes under `Relation.ReflTransGen`. | High | Medium | Phase 11 checks it explicitly as its first task, before the mechanical export. If it fails, the phase records that rather than claiming a general result from a single-hop proof. |
| **Phase 6's signature change breaks more call sites than enumerated.** `openBranch_countermodel` and `tableau_complete` are consumed by both `Completeness.lean` files at minimum. | Medium | Medium | Phase 6 carries a Scope Hypothesis requiring a `grep -n` enumeration before editing, and declares `Verification Tier: interface` with `Commit Mode: atomic-batch` so no partial-signature state is committed. |
| **Territory collision on `Scheme.lean`** with a concurrently live 317/574/585 phase. Phases 6-13 nearly all write `Scheme.lean`. | High | Medium | `file_scope` is populated in this task's metadata so the orchestrator's footprint gate can serialize. Phases 7-13 are declared strictly sequential on `Scheme.lean` for this reason; Phases 5 and 6 are the only parallel pair and Phase 5 writes only `scratch/`. |
| **A build-out phase is opened before Gate B2's verdict**, spending an `IWorldHist`-scale effort on a possibly-false statement. | Critical | Medium | The Gating contract table above, plus a hard entry criterion on Phase 7: a recorded verdict in `handoffs/04_gate-b2-verdict.md` is required, and its absence means stop. |
| **Report 13's "no world bound of any size exists" is read as still binding.** | Medium | Medium | It is **superseded, not contradicted** — it measured the pre-repair calculus. Post-repair `WBound φ0` / `intUniverseExt` exist and the fixpoint lemma is landed sorry-free. Do not let a stale reading shape any phase. |
| **Report 17's C&Z citation rests on visibly degraded OCR.** | Low | Medium | The quotient no-go does not depend on it (the in-repo refutation is independent). Re-check against a physical copy before that citation appears in any Lean docstring. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 5, 6 | 4 |
| 5 | 7 | 5 |
| 6 | 8 | 7 |
| 7 | 9 | 8 |
| 8 | 10 | 9 |
| 9 | 11 | 9, 10 |
| 10 | 12 | 11 |
| 11 | 13 | 6, 12 |
| 12 | 14 | 12, 13 |

Phases within the same wave can execute in parallel. Waves 1-3 are complete. Wave 4's two phases
own disjoint territory (Phase 5: `scratch/` only; Phase 6: `Scheme.lean` +
`Completeness.lean` files) and Phase 6's parallelism is explicitly authorized — see the Gating
contract table. Phase 10 is **conditional**: it runs only if Phase 9 records that the cheap route
collapsed; otherwise it is closed as `[COMPLETED WITH EXCLUSIONS]` with Phase 9's verdict as
evidence.

### Phase 1: Gate A — variant selection probe (V1 vs V4) [COMPLETED]

- **Goal:** Determine by measurement which copy-channel form to reinstate: V1 (self-copy verbatim)
  or V4 (generalize to copy *every* positive formula).
- **Outcome:** **V4 selected.** Control fidelity reproduced against the prior task's recorded
  tables; V4 saturates on `φ0` at `fuel ≥ 120`; all 20 `TableauConformance.lean` propositional
  rows match. Full measurement tables in `handoffs/01_gate-a-variant-selection.md`.
- **Tasks:**
  - [x] Probe harness recreated in `scratch/VariantProbe.lean`; true control reproduced first.
  - [x] V1 and V4 measured on the fuel ladder; conformance rows checked read-only.
  - [x] Decision recorded in `handoffs/01_gate-a-variant-selection.md`.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** none
- **Verification Tier:** local
- **Files modified:** `scratch/VariantProbe.lean`. Zero `Cslib/` writes, confirmed.

### Phase 2: Gate B — persistence prototype (GATING, no algorithm change) [COMPLETED]

- **Goal:** Decide whether positive-formula persistence along the augmented relation is provable
  at all, before any calculus change.
- **Outcome:** **PASS (conditional).** The descendant sub-case closes. The **ancestor sub-case is
  the open one** and was carried forward. Verdict in `handoffs/02_gate-b-verdict.md`; prototype in
  `scratch/PersistPrototype.lean`.
- **Known limitation, recorded here because it is the reason Phase 5 exists:** Gate B analysed
  only the *copy* argument's descendant/ancestor sub-cases. It did **not** consider independent
  beta-split choices at `w` versus at the reused ancestor `x`. That mechanism (report 05 §4) may
  make the statement false, and Gate B's PASS does not cover it. Gate B also did not re-confirm
  multi-hop composition under `Relation.ReflTransGen` (carried into Phase 11).
- **Tasks:**
  - [x] Single-loop-back-hop prototype built and green in `scratch/`.
  - [x] The `bPers`-vs-final-branch survival question confronted directly.
  - [x] Explicit PASS/FAIL verdict recorded.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** none
- **Verification Tier:** local
- **Files modified:** `scratch/PersistPrototype.lean`. Zero `Cslib/` writes.

### Phase 3: Reinstate the copy channel — V4 generalized `genCopies` [COMPLETED]

- **Goal:** Restore the copy channel in the form Gate A selected, returning the tree to green with
  the channel present.
- **Outcome:** V4's generalized `genCopies` channel landed in `Expansion.lean` (copies every
  positive formula, appended alongside `newForms`), with the `rfl`-level pattern-match repairs and
  proof restructuring in `Scheme.lean` and `Soundness.lean`. Full detail, including every recorded
  deviation from a literal revert, is in plan 04's Phase 3 and is not restated here.
- **Verification results (recorded at the time):** `lake build` green; `lake exe checkInitImports`
  clean; `lake lint` zero new warnings in the three touched files; `lake exe lint-style` clean;
  `lake shake` no new findings in touched files; `lake test` green including
  `TableauConformance`. `intExpandBranches_closed_unsat` axiom-clean
  (`propext`, `Classical.choice`, `Quot.sound`); `Soundness.lean` sorry-free.
- **Tasks:**
  - [x] `Expansion.lean`: generalized `genCopies` channel plus docstring.
  - [x] `Scheme.lean`: pattern-match repairs, generalized `applyAllTImpRules_copy_notMem`, new
        shared helper `applyAllTImpRules_eq_self_of_length_eq`.
  - [x] `Soundness.lean`: `applyAllTImpRules_sat` and `freshAbove_applyAllTImpRules` restructured
        for the 3-way append.
  - [x] Axiom-cleanliness and conformance re-verified against the real library.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 1, 2
- **Verification Tier:** full
- **Commit Mode:** atomic-batch
- **Files modified:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`,
  `.../Intuitionistic/Scheme.lean`, `.../Intuitionistic/Soundness.lean`.

### Phase 4: Copy-completeness at a genuine `applyAllTImpRules` fixpoint [COMPLETED]

- **Goal:** Prove that at a genuine `applyAllTImpRules` fixpoint the copy channel has delivered
  every positive formula it owes along the **raw** edges.
- **Outcome:** Two lemmas landed, both **sorry-free and axiom-clean**:
  - `applyAllTImpRules_copy_complete_of_fixpoint` — given `applyAllTImpRules b edges = b`,
    `T(χ)@w ∈ b`, `w'` raw-accessible from `w`, and `w'` carrying some entry on `b`, then
    `T(χ)@w' ∈ b`.
  - `applyPersistenceFixpoint_copy_complete` — pairs the above with
    `applyPersistenceFixpoint_genuine_of_count_le_fuel`.
- **Preserved asset note:** these two lemmas are the copy side of the pairing whose fuel side was
  already retired, and they are what makes Phase 7 cheap. Do not re-prove them.
- **Verification results:** `lake build` green; `checkInitImports` and `lint-style` clean; zero new
  `lake lint` warnings in `Scheme.lean`.
- **Tasks:**
  - [x] Case-split on the same guard `genCopies` itself uses (rather than a `countP` drop
        argument, which termination needed but completeness does not).
  - [x] `applyAllTImpRules_copy_complete_of_fixpoint` stated and proved sorry-free.
  - [x] `applyPersistenceFixpoint_copy_complete` composed and verified.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 3
- **Verification Tier:** local
- **Files modified:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 5: Gate B2 — beta-split refutation probe (GATING) [COMPLETED]

- **Goal:** Determine empirically whether the beta-split shape (report 05 §4) refutes atom-level
  persistence along the **augmented** relation. **This is the option-killer for the entire
  remainder of the plan.** A refutation here is a complete and sanctioned outcome, not a failure.
- **Entry criterion:** none beyond Phase 4 being landed. Run this before Phase 7 unconditionally.
- **Outcome:** **PASS (with residual risk explicitly carried forward, not exhaustively
  refuted).** Eight `φ0` candidates tested; three (`phiRS`, `phiRS2`, `phiBeta2`) genuinely
  exercised the mechanism (reuse fired with a live shared disjunction confirmed by
  construction), all three found zero atom-level upward-closure violations. Full verdict,
  method, and the analytical explanation for why the mechanism resists accidental construction
  in `handoffs/04_gate-b2-verdict.md`.
- **Tasks:**
  - [x] Construct `φ0` forcing a **disjunction under nested implications**, so that a blocked
        world `w` and its reused ancestor `x` both carry the same disjunction. The two `T(r ∨ s)`
        occurrences must be at distinct labels so they expand as two independent beta-splits.
        *(deviation: altered -- eight candidates were constructed rather than one; see below)*
  - [x] Run `intExpandBranches` at `fuel ≥ 120` in `scratch/` (harness style per
        `scratch/VariantProbe.lean` and the prior task's probe methodology — a scratch-only `#eval`
        or `decide` harness with an explicit fuel argument). *(deviation: altered -- the heaviest
        candidates (`phiRS`/`phiRS2`) were run at fuel 40, not ≥120: the injected disjunction
        multiplies the branching factor of the already-heavy structural-duplication witness
        enough that fuel 55 alone exceeded a ~9-minute compute budget; fuel 40 already
        demonstrably exercises the mechanism (reuse fires with a live shared disjunction) and
        is the evidentiary basis for the verdict. The hand-built candidates (`phiBeta1`-`5`) were
        run at fuel 80, well past their own saturation points (max label ≤ 8 in every case).)*
  - [x] Take the open branch **and the AUGMENTED edge list** — the `augSets` witness, **not** the
        raw `edgeSets`. Getting this wrong invalidates the whole probe: raw-edge persistence is
        already known to be the easy half, and measuring it would produce a false PASS.
  - [x] Decide atom-level persistence computationally over `intAccessPreorder augEdges`: for all
        `w ≤ w'` and all atoms `p`, check
        `intExtractValuation b w p → intExtractValuation b w' p`. All three predicates are
        decidable, so a `Bool`-valued harness or `decide` suffices — Gate A's empirical style.
  - [x] Widen to a small family of `φ0` candidates if the first one does not exercise the shape
        (confirm a reuse event actually fired and that both worlds carry the disjunction before
        reading any PASS as meaningful — a probe that never triggers the mechanism is inconclusive,
        not a PASS).
  - [x] Record an explicit verdict in `handoffs/04_gate-b2-verdict.md`: **REFUTED** (a failing
        instance found — see Rollback/Contingency, terminal deferral), **PASS** (the shape does not
        arise across the tested family; proceed to Phase 7 with the residual risk recorded), or
        **INCONCLUSIVE** (the mechanism was never exercised; say so rather than claiming PASS).
- **Timing:** ~1 dispatch
- **Depends on:** 4
- **Verification Tier:** local
- **Scope Hypothesis:** a small family of hand-constructed `φ0` (order 1-5 formulas) suffices to
  exercise the beta-split-at-both-worlds shape at `fuel ≥ 120`. Confirm at implementation time by
  checking, per candidate, that (a) a reuse event fired, and (b) both `w` and `x` carry the same
  disjunction in the returned branch. If no candidate satisfies both, the verdict is INCONCLUSIVE
  and the phase must say so — an unexercised mechanism is not evidence of its absence.
- **Files to modify:** `specs/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/BetaSplitProbe.lean`
  (new). **Zero** writes to `Cslib/` or `CslibTests/` — confirm with
  `git status --short Cslib/ CslibTests/` (must be empty).

### Phase 6: Statement-shape fix — `openBranch_countermodel` and `hvalid` [COMPLETED]

- **Goal:** Close the machine-verified statement-shape defect. Move the upward-closure obligation
  to where `b`'s provenance is in scope, so that DP-3/DP-4 become fillable at all. **Independent
  of Phase 5 and of all persistence work** (report 05 §1/§5) — this phase is authorized to run in
  parallel with Gate B2, and remains worth landing even under a Gate B2 refutation, because it
  converts an unfillable sorry into an honestly-stated one.
- **Evidence this phase is necessary, not speculative:** `scratch/HvalidShapeRefutation.lean`
  compiles clean with zero sorries and proves both `IValid (p → (q → p))` and the falsity of
  `hvalid`'s body at `edges=[(1,0)]`, `b=[T(atom p)@0, T(atom q)@1]`. Read that file before
  editing anything.
- **Outcome:** Landed. `openBranch_countermodel`'s conclusion now carries the upward-closure
  conjunct (proved by a new, honestly-deferred `sorry` -- see rationale below);
  `tableau_complete`'s `hvalid` accepts it as a hypothesis and its proof is repaired
  (`obtain ⟨edges, huc, hcm⟩ := ...; exact absurd (hvalid edges b huc) hcm`), remaining
  sorry-free itself. Both `Completeness.lean` files' `intuitionisticOpenBranch_countermodel`/
  `minOpenBranch_countermodel` conclusions and `intuitionisticTableau_complete`/
  `minimalTableau_complete`'s proofs (now `intro edges _b _huc`) updated to match, with DP-3/DP-4
  re-annotated (still `sorry`, deliberately -- see below) rather than discharged. `lake build`
  on all three files green; exactly 4 sorries now: DP-5 (`Scheme.lean:671` per current line
  numbers), the new `openBranch_countermodel` conjunct (`Scheme.lean:7376`), DP-3
  (`Completeness.lean:137`), DP-4 (`Minimal/Completeness.lean:133`). `Soundness.lean` untouched
  (confirmed via `git diff --stat`).
- **Why DP-3/DP-4 are deliberately left `sorry` rather than discharged now:** report 05 states
  they "collapse to `exact h Nat (intExtractValuation b) huc 0`-shaped one-liners" once `huc` is
  available -- and syntactically this WOULD type-check today, since `huc` (sourced from
  `openBranch_countermodel`) is a valid term even though its own proof is `sorry`. Doing so
  would make the `sorry` token vanish from `Completeness.lean` while the actual underlying gap
  silently persists, hidden two files away inside `Scheme.lean` -- exactly the kind of
  laundering the plan's "no statement weakened to dodge a gap" goal forbids in spirit, even
  though no statement is technically weakened. Per the plan's own explicit instruction ("Leave
  DP-3 and DP-4 as sorry for now, but re-annotate them"), the deferred obligation is kept
  visible at its historical, honestly-load-bearing sites, re-pointed at
  `openBranch_countermodel`'s new conjunct as the thing that actually needs proving next
  (Phases 7-11), rather than silently discharged via a still-unproven dependency.
- **Tasks:**
  - [x] Re-read `scratch/HvalidShapeRefutation.lean` and confirm it still compiles against the
        current tree (`lake env lean` on the file). If it no longer does, stop and record why
        before changing any signature.
  - [x] Enumerate every consumer of `openBranch_countermodel` and `tableau_complete`
        (`grep -n` across `Cslib/Logics/Propositional/Tableau/`) before editing. Record the count.
        *(Confirmed: exactly the two `Completeness.lean` bridge sites plus `tableau_complete`'s
        own internal call, matching the Scope Hypothesis exactly -- no excess.)*
  - [x] Strengthen `openBranch_countermodel`'s conclusion to carry the upward-closure conjunct:
        `∃ edges, (upward-closure of intExtractValuation b along intAccessPreorder edges) ∧
        ¬IForces …`. Prefer this form over restricting `hvalid` to
        `intExpandBranches … = .openBranch b`, per report 05's stated preference.
  - [x] Weaken `tableau_complete`'s `hvalid` (`Scheme.lean:7446`) to accept the upward-closure
        fact as a hypothesis, and repair its proof (`:7451-7457`) — it already only ever uses
        `hvalid` at the `b` returned by `openBranch_countermodel`, so the premise is strictly
        stronger than the proof needs.
  - [x] Confirm `tableau_complete` remains **sorry-free** and `Soundness.lean` is **untouched**.
  - [x] Update the surrounding docstrings to describe the new shape. Do not leave prose claiming
        the old, refuted premise shape is what is needed.
  - [x] Leave DP-3 and DP-4 as `sorry` for now, but **re-annotate** them: the remaining obligation
        is now the upward-closure fact, stated where `b`'s provenance is in scope. The old comment
        text describing an unfillable goal must go.
  - [x] `lean_verify` `tableau_complete` and `openBranch_countermodel`: both report
        `["propext", "sorryAx", "Classical.choice", "Quot.sound"]` -- `sorryAx` appears
        TRANSITIVELY in both (`tableau_complete` calls `openBranch_countermodel`, which now
        carries the new, expected deferred `sorry` documented above), consistent with
        `tableau_complete`'s OWN proof body containing zero literal `sorry` tokens (confirmed by
        inspection: `by_contra hne; cases hresult ...; obtain ⟨edges, huc, hcm⟩ := ...; exact
        absurd (hvalid edges b huc) hcm`). No axioms beyond the standard
        `propext`/`Classical.choice`/`Quot.sound` plus the expected transitive `sorryAx` -- this
        is the intended state at this phase, not a violation; Phase 14's "no `sorryAx`" bar
        applies once DP-3/DP-4/DP-5 and this new conjunct are all discharged, not here.
- **Timing:** ~1 dispatch
- **Depends on:** 4
- **Verification Tier:** interface
- **Commit Mode:** atomic-batch
- **Scope Hypothesis:** the signature change breaks exactly the consumers of
  `openBranch_countermodel` and `tableau_complete`, expected to be the two `Completeness.lean`
  bridge sites plus any internal `Scheme.lean` use. Confirm at implementation time with the
  `grep -n` enumeration above and fix every hit; if the count exceeds the enumerated set, record
  the excess rather than silently widening the edit.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`,
  `.../Intuitionistic/Completeness.lean`, `.../Minimal/Completeness.lean` (annotation only in the
  latter two at this phase; the sorries close in Phase 13).

### Phase 7: Export the raw-edge persistence conjunct [COMPLETED]

- **Goal:** Add the **raw-edge** persistence conjunct to `intExpandBranches_openBranch_sat`'s
  conclusion. A cheap stepping stone that is explicitly **not sufficient alone** — the augmented
  version is what Phases 12-13 need.
- **Entry criterion (hard):** `handoffs/04_gate-b2-verdict.md` exists and records **PASS**. If it
  records REFUTED, do not start this phase — go to Rollback/Contingency. If INCONCLUSIVE, re-run
  Phase 5 with a widened `φ0` family rather than proceeding on an unmeasured statement.
- **Do not re-derive handoff 03's Finding 1.** It is established: `IAllFuel φ0 bs es fuels` gives
  `intWork (intUniverseExt φ0) b e < f`, whose non-negative summands yield exactly the `hfuel`
  premise `applyPersistenceFixpoint_genuine_of_count_le_fuel` needs, at the *same* fuel `f` that
  `applyPersistenceFixpoint` is called with in `intExpandBranches.go`; `IAllUniv φ0 bs` supplies
  `hb`; both are already threaded through the whole `key` induction as `hUniv`/`hFuel`.
- **Outcome:** Landed. `IPosPersistRaw edges b` defined exactly as proposed. The conclusion of
  `intExpandBranches_openBranch_sat` is now `∃ (edges rawEdges : IEdges), IBranchSaturation Atom
  b ∧ IFimpAccess edges b ∧ IPosPersistRaw rawEdges b` -- a SECOND existential (`rawEdges`),
  distinct from the augmented `edges` witness `IFimpAccess` uses, since `IPosPersistRaw`'s
  accessibility hypothesis is genuinely over the RAW edge list (`edgesH`, the same `edges`
  argument `applyPersistenceFixpoint`/`applyAllTImpRules` were actually called with at this
  step), not the augmented one -- these are different quantities and `applyPersistenceFixpoint_
  copy_complete`'s `hacc` hypothesis only holds for the raw relation (this was not spelled out
  in the plan's proposed shape and is recorded as a genuine, necessary refinement, not a
  deviation from intent). Only the one substantive terminal case (`case4`, `intStepBranch bPers
  eH nwH = none`) needed new work; the `f = 0` and `.notApplicable` arms remain discharged by
  contradiction, unchanged. `lake build` (full project) green; exactly the same 4 sorries as
  after Phase 6 (Phase 7 added zero new sorries).
- **Tasks:**
  - [x] Define the raw-edge invariant predicate (proposed `IPosPersistRaw edges b`; implementer
        confirms or renames per CSLib conventions) capturing
        `∀ χ w w', isAccessible edges w w' = true → T(χ)@w ∈ b → T(χ)@w' ∈ b`, carrying whatever
        side-condition at `w'` Phase 4's lemma requires.
  - [x] At the substantive terminal return site (`intStepBranch bPers e nw = none`), compose the
        already-in-scope specialized `hUnivP_head`/`hFuelP` facts with
        `applyPersistenceFixpoint_genuine_of_count_le_fuel` and then
        `applyAllTImpRules_copy_complete_of_fixpoint`. *(deviation: altered -- composed via
        `applyPersistenceFixpoint_copy_complete` directly, the Phase 4 lemma that already
        pairs the two named lemmas; re-deriving the pairing by hand would have duplicated
        already-landed work.)*
  - [x] Confirm the other return sites need no new work: `f = 0` and `intStepBranch`'s
        `.notApplicable` result are already discharged by contradiction in the existing proof
        (`intWork < 0` absurd; `intStepBranch_result_ne_notApplicable`).
  - [x] Extend the conclusion and repair the destructuring call sites. *(The single consumer,
        `openBranch_countermodel`'s `obtain`, updated to bind and discard the two new
        components: `⟨edges, _rawEdges, hsat, hfimp, _hpp⟩`.)*
  - [x] `lean_verify`: `tableau_complete`/`openBranch_countermodel` report `sorryAx`
        TRANSITIVELY (via the still-deferred Phase-6 conjunct), as expected at this phase --
        see Phase 6's own note on this; no NEW axioms beyond the pre-existing
        `propext`/`Classical.choice`/`Quot.sound`.
- **Timing:** ~1 dispatch
- **Depends on:** 5
- **Verification Tier:** interface
- **Scope Hypothesis:** the conclusion change breaks exactly the destructuring call sites of
  `intExpandBranches_openBranch_sat`, which is `private` with a small enumerable consumer set.
  Confirm with `grep -n "intExpandBranches_openBranch_sat"` and fix every hit; if the count
  exceeds the enumerated set, record it. Plan 04's Phase 5 asserted this hypothesis but never
  confirmed it (the conclusion was never changed) — it is therefore still unconfirmed, not
  inherited as established.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 8: Export reuse-time containment as a companion invariant [COMPLETED]

- **Continuation note (read before starting):** `handoffs/05_phase7-complete-phase8-handoff.md`
  records a design subtlety worth resolving before writing Lean: the naive "bare `(x, l) ∈ augH`
  membership → containment on the CURRENT branch" invariant shape is NOT preserved by the
  induction as an invariant (proving it would BE Phase 9). Two candidate encodings that avoid
  this trap (a per-edge finite `Sfor` record, or a `∃ bSnap` existential-snapshot shape) are
  proposed there, with a recommendation to compare both against the real reuse-arm proof
  context before committing.
- **Goal:** Thread `posFormulasAt bPers w ⊆ posFormulasAt bPers x` as a monotone planted fact per
  **recorded loop-back edge**, surviving to the final branch. This is the one thing no existing
  clause covers: `sfor c` records only a *created* world's mint-time set, and the reuse arm
  (`Scheme.lean:4705-4714`) creates no world — it leaves `edges` and `nw` unchanged — so nothing
  today covers the reuse pair `(x, w)`.
- **The fact already exists at reuse time and only needs exporting.** `intFImpReuseWitnessAnc?`
  (`Expansion.lean:296-307`) computes
  `sfor := newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none` and
  requires `sfor.all (forcedAtX.contains ·)`. Because `propagatePersistence` puts every positive
  formula of `w` into `newForms`, `sfor` **is** `{φ} ∪ posFormulasAt bPers w`, so that conjunct
  states exactly the containment above. It is already exported as `hcont` by
  `intFImpReuseWitnessAnc?_spec` (`Expansion.lean:321`) and currently consumed locally.
- **Outcome:** Landed. Adopted the handoff's **existential-snapshot** encoding (candidate 2):
  `IReuseContain (lbH : IEdges) (b : IBranch Atom) : Prop := ∀ x l, (x, l) ∈ lbH → ∃ bSnap, (∀ y ∈
  bSnap, y ∈ b) ∧ ∀ χ, T(χ)@l ∈ bSnap → T(χ)@x ∈ bSnap`, plus its list companion
  `IAllReuseContain` (2-list zip over `(bs, lbSets)`) and `_append`/`_map_const` lemmas, all
  mirroring `IAllAccessConsistent`'s shape but threaded through a genuinely **separate** parallel
  list (`lbSets`/`pendingLB`/`doneLB`), NOT the existing `augSets`/`pendingAug`/`doneAug` --
  `IReuseContain` only concerns recorded loop-back pairs, a strict subset of the full augmented
  edge list `IAllAccessConsistent` already tracks, and folding it into the same list would have
  required re-establishing the fact at the MINT arm too (redundant with, and weaker than, Phase
  7's `IPosPersistRaw`). `intExpandBranches_openBranch_sat`'s conclusion gained a THIRD existential
  (`lbEdges`, distinct from `edges` and `rawEdges`) plus `IReuseContain lbEdges b`. The reuse arm
  (`case6`) plants the new fact via a new `hcontGen` lemma (the GENERALIZATION of the existing
  `houtPhi`/`hphi` derivation from the single formula `φ` to every `χ` with `T(χ)@l ∈ bPers`,
  since `hcont` already ranges over all of `sfor = {φ} ∪ posFormulasAt bPers l`) composed with a
  new `IReuseContain_snoc` lemma (bSnap := the current `bPers`, reflexively contained in itself).
  Every OTHER arm that touches `pendingLB`/`hPendingARC` (cases 2, 4, 5, 7, 8) performs only a
  monotone lift via `IReuseContain_mono`, mirroring exactly how `hACC`/`hWH` are carried at those
  same arms -- confirmed by locating every site that extends `augH`/`doneAug` (Scope Hypothesis
  below): only the reuse arm (`case6`) appends a genuinely new loop-back pair; the mint arm
  (`case7`) extends the (separate) RAW/augmented edge list with `newE` but the LB-only list
  `lbH` is carried unchanged in value, requiring only the mono-lift, not a new plant. `lake
  build` (full project, 3311 jobs) green; `lean_verify` on `openBranch_countermodel` reports only
  the expected `["propext", "sorryAx", "Classical.choice", "Quot.sound"]` (the transitive
  `sorryAx` from its own still-deferred upward-closure conjunct, unchanged from Phase 6/7);
  `checkInitImports` and `lint-style` clean on the touched file; `TableauConformance` still green.
  Exactly the same 4 sorries as after Phase 7 (Phase 8 added zero new sorries).
- **Tasks:**
  - [x] Define a companion invariant (proposed `IAllReuseContain`, or a new clause on a sibling of
        `IAllAccessConsistent`) recording, per recorded loop-back edge `(x, l)` in the augmented
        list, the containment `posFormulasAt b l ⊆ posFormulasAt b x`. *(deviation: altered --
        the existential-snapshot shape `∃ bSnap` was used, not a bare current-branch containment
        claim, per the handoff's own recommended candidate 2, since only that shape is preserved
        automatically under branch growth.)*
  - [x] Mirror `IAllAccessConsistent`'s **companion-not-merged** pattern relative to
        `IAllConsistent` — a parallel invariant threaded alongside, not new fields merged into an
        existing structure. *(Threaded via its own parallel list `lbSets`, not reusing `augSets`
        -- see Outcome for why.)*
  - [x] Reuse `IWorldHist_mono`'s shape for the monotonicity transfer and
        `IAllWorldHist_append`/`_map_const` for the list-level plumbing. Do not invent a parallel
        mechanism. *(`IReuseContain_mono`/`IAllReuseContain_append`/`IAllReuseContain_map_const`
        are direct structural mirrors of `IWorldHist_mono`/`IAllWorldHist_append`/`_map_const`.)*
  - [x] Thread it through the `key` induction. The intermediate (non-terminal) cases delegate to
        `ih` polymorphically; the reuse arm is the one arm that must plant the new fact, and the
        terminal sites are where it is read.
  - [x] Confirm branch-append monotonicity carries the planted fact to the final branch (handoff
        03 Finding 2 records this half as **not hard** — ordinary append monotonicity, the
        ubiquitous `hmemP`/`IWorldHist_mono` pattern). Do not conflate this with the general
        persistence guarantee, which is Phase 9's job. *(Confirmed: `case4`, the terminal
        saturated-branch return site, mono-lifts `pendingLB`'s head from `bh` to `bPers` and
        exports it as the third existential.)*
  - [x] `lean_verify`: axiom-clean, no `sorryAx` beyond the pre-existing transitive one from the
        Phase-6 conjunct.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 7
- **Verification Tier:** interface
- **Scope Hypothesis:** the reuse arm is the only arm of `intExpandBranches.go` that appends to the
  augmented list beyond the raw edges, so exactly one arm must plant the new fact and the rest
  delegate to `ih`. Confirm at implementation time by locating every site that extends `augH` /
  `doneAug`; if more than the reuse arm does so, record it before threading. *(Confirmed by
  enumeration of all 10 cases of the `key` induction: only `case6` (reuse) appends a new
  loop-back pair; `case7` (mint) appends only to the RAW/augmented list, not the LB-only list,
  and needs a mono-lift, same as every other non-planting arm.)*
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 9: Post-reuse closure lemma — the cheap route first [NOT STARTED]

- **Goal:** Prove the residual obligation: **no positive formula arrives at `w` after the reuse
  event without also being at `x`.** This is the genuinely large piece. Attempt the
  saturation + copy-completeness route **first**; full origin tracing is Phase 10's fallback, not
  this phase's opening move.
- **Why the cheap route is plausible** (report 05 §3, flagged **UNVERIFIED**): post-reuse arrivals
  at `w` have exactly two sources.
  - **Decomposition at `w`** of a premise already present at reuse time. That premise is at `x` by
    Phase 8's containment, and the final branch is **saturated** (`IBranchSaturation` is already in
    `intExpandBranches_openBranch_sat`'s conclusion), so the same decomposition is available at `x`.
  - **A copy from a raw ancestor `y` of `w`.** `par`-linearity (report 05 §2: `par` is a total
    unique-parent function with `par c < c`, so ancestor chains are linear) makes `y` and `x`
    comparable. If `y ≤ x`, the V4 copy channel delivers to `x` too, since it copies to all raw
    descendants. If `x ≤ y ≤ w`, it does not, and one recurses on `y`.
- **The `x ≤ y ≤ w` case is where this can collapse.** That is the declared failure mode, and
  recording "route collapsed, escalate to Phase 10" is a legitimate outcome of this phase.
- **Tasks:**
  - [ ] State the residual obligation precisely as a lemma over the final branch, taking Phase 8's
        containment and `IBranchSaturation` as hypotheses.
  - [ ] Discharge the decomposition source using saturation at `x`.
  - [ ] Discharge the `y ≤ x` copy source using the V4 channel plus Phase 4's copy-completeness.
  - [ ] Attack the residual `x ≤ y ≤ w` case. Set an explicit budget for it and stop when the
        budget is spent rather than open-endedly grinding.
  - [ ] Export `par`-linearity and (H1-acc) from `IWorldHist` as the `ForestComparable` fact the
        comparability step needs — **export, not construction** (report 05 §2).
  - [ ] Record the verdict: **CLOSED** (the cheap route works; Phase 10 becomes
        `[COMPLETED WITH EXCLUSIONS]`) or **COLLAPSED** (the `x ≤ y ≤ w` recursion forces full
        origin tracing; Phase 10 runs), in `handoffs/05_post-reuse-closure-verdict.md`.
  - [ ] **Prohibited workarounds** (carried forward from Phase 5's blocker record, where they were
        correctly avoided): no `sorry`, no vacuous placeholder, no weakened statement. If the route
        collapses, stop and hand off — do not force a result.
- **Timing:** ~1 dispatch
- **Depends on:** 8
- **Verification Tier:** interface
- **Scope Hypothesis:** post-reuse arrivals at `w` have exactly the two sources enumerated above
  (decomposition at `w`; copy from a raw ancestor `y`). Confirm at implementation time by
  enumerating every site that appends a positive formula at an existing label in
  `intStepBranch`/`applyAllTImpRules`/`applyPersistenceFixpoint`. If a third source exists, the
  enumeration is wrong and must be corrected before the lemma is claimed — a two-case proof over a
  three-source reality is exactly the unsound shortcut this plan forbids.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 10: Fallback — full origin tracing (CONDITIONAL) [NOT STARTED]

- **Goal:** If and only if Phase 9 recorded **COLLAPSED**, build the origin-tracing extension:
  track, for every positive formula's branch presence, a traceable point of origin, and show that
  origin is raw-accessible to any loop-back edge's source.
- **Entry criterion:** `handoffs/05_post-reuse-closure-verdict.md` records **COLLAPSED**. If it
  records CLOSED, this phase is closed immediately as `[COMPLETED WITH EXCLUSIONS]` with a
  `#### Reasoned Exclusions` record citing that verdict — do not build machinery Phase 9 made
  unnecessary.
- **Scope honesty:** this is the piece the prior implementation dispatch assessed as comparable in
  scope to building `IWorldHist` itself, and it stopped rather than risk an unsound shortcut. That
  assessment stands. This phase is budgeted as its own dispatch (possibly more than one) precisely
  so it is not compressed into the tail of another.
- **Tasks:**
  - [ ] Extend `IWorldHist`'s witness functions — or thread a sibling invariant alongside them,
        mirroring `IAllAccessConsistent`'s companion-not-merged pattern — to record a traceable
        origin world for every positive formula's presence on the branch.
  - [ ] Generalize (H3)'s planted-positive-content shape from "the mint-time `Sfor` set" to "every
        positive formula's point of origin".
  - [ ] Prove that the recorded origin is raw-accessible to any `x` a loop-back edge points from,
        using (H1-acc) and `par`-linearity.
  - [ ] Reuse `IWorldHist_mono` for the transfer in every non-minting arm and `IWorldHist_entry`
        for the vacuous entry discharge. Do not re-derive either.
  - [ ] Reuse `IAllWorldHist_append`/`_map_const` and the `IAllWorldHistCounter` family for the
        list-level plumbing.
  - [ ] Do **not** reach for `intWorldHist_chain_le`, `pathOf`, `pathOf_injOn`, or
        `intWorldHist_nw_le` — report 05 §2 records these as world-**bound** machinery, largely
        irrelevant to persistence.
  - [ ] If this phase itself cannot complete within its dispatch, record a `[PARTIAL]` handoff with
        the same discipline Phase 5's blocker record used: zero `Cslib/` writes left in a red
        state, no `sorry`, no weakened statement.
  - [ ] `lean_verify`: axiom-clean, no `sorryAx`.
- **Timing:** ~1-2 dispatches (the largest phase in this plan; sized honestly rather than
  optimistically)
- **Depends on:** 9
- **Verification Tier:** interface
- **Scope Hypothesis:** the origin-tracing extension can be threaded as a companion invariant
  without modifying `IWorldHist`'s existing clauses, so no landed `IWorldHist` consumer breaks.
  Confirm at implementation time with `grep -n "IWorldHist"` before choosing extend-vs-companion;
  if the companion route proves impossible and `IWorldHist` itself must change, record the
  divergence and re-check every consumer rather than editing in place.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 11: Multi-hop composition and augmented-edge export [NOT STARTED]

- **Goal:** Confirm the single-hop transfer lemma composes under `Relation.ReflTransGen` when a
  branch accumulates **several** reuse events, then export the augmented-edge persistence conjunct
  in `intExpandBranches_openBranch_sat`'s conclusion.
- **Why this is a real phase and not a formality:** Gate B's verdict never re-confirmed multi-hop
  composition (handoff 03 item 3; report 05 §5 step 5). Plan 04's Phase 2 Scope Hypothesis assumed
  it on the grounds that the augmented list differs from the raw list only by loop-back edges and
  multi-hop reachability is their reflexive-transitive closure — **that assumption is still
  unconfirmed** and is checked here, first, before the mechanical export.
- **Tasks:**
  - [ ] Check composition explicitly: does the one-step transfer lemma from Phase 9 (or 10) chain
        under `Relation.ReflTransGen` across two or more recorded loop-back edges? Construct the
        two-hop case concretely before asserting the general one.
  - [ ] If composition fails, **stop and record it** — do not claim a general result from a
        single-hop proof. A failure here is a blocker, not a rounding error.
  - [ ] Provide the lift from the one-step form to the `intAccessPreorder edges` order using
        `intAccessPreorder_le_of_isAccessible` (`Scheme.lean:276`) rather than redefining it.
  - [ ] Define the augmented-edge invariant predicate (proposed `IPosPersist edges b`) and extend
        `intExpandBranches_openBranch_sat`'s conclusion from
        `∃ edges, IBranchSaturation Atom b ∧ IFimpAccess edges b` to also carry it.
  - [ ] Repair every `obtain ⟨edges, hsat, hfimp⟩`-style destructuring call site.
  - [ ] `lean_verify`: axiom-clean, no `sorryAx`.
- **Timing:** ~1 dispatch
- **Depends on:** 9, 10
- **Verification Tier:** interface
- **Scope Hypothesis:** multi-hop reachability in the augmented frame is exactly the
  reflexive-transitive closure of raw accessibility plus the recorded loop-back edges, so a
  verified two-hop case plus induction suffices for the general case. Confirm by constructing the
  two-hop case; if the induction step needs a fact the single-hop lemma does not provide, record
  that as a blocker rather than strengthening the claim.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 12: Discharge DP-5 (`Scheme.lean:727`) [NOT STARTED]

- **Goal:** Close the T-implication sorry at **`Scheme.lean:727`** (not `:633` — the task
  description and plan 04 are both stale on this; re-locate by content if it has shifted again) by
  instantiating the exported invariant at `φ = φ'→ψ'`, letting the reflexive `sat_timp` field fire
  at `w'`.
- **Tasks:**
  - [ ] Consume the augmented-edge persistence conjunct in `truthLemma`'s `imp` case to obtain
        `T(φ'→ψ')@w'` from `T(φ'→ψ')@w` and `w ≤ w'` at the `intAccessPreorder edges` frame.
  - [ ] Fire `sat_timp` at `w'`; close the case via `ih_φ'` / `ih_ψ'`.
  - [ ] Replace the `sorry`; use `lean_goal` at each step to confirm closure.
  - [ ] Update the surrounding STOP-gate docstrings to record that the gap is closed, replacing the
        deferral prose rather than leaving it stale. **No task numbers in the docstring** — cite
        lemma names and section headings only.
  - [ ] `lean_verify` `truthLemma`: axiom-clean, no `sorryAx`.
- **Timing:** ~1 dispatch
- **Depends on:** 11
- **Verification Tier:** interface
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 13: Discharge DP-3 and DP-4 at atom shape [NOT STARTED]

- **Goal:** Close `Intuitionistic/Completeness.lean:140` and `Minimal/Completeness.lean:128`
  sorry-free. Mechanical once Phase 6 (statement shape) and Phase 12 (the exported invariant) have
  both landed — and **not** attemptable before Phase 6, since without the signature change the
  goal is machine-verified unfillable.
- **Tasks:**
  - [ ] Package the upward-closure fact **once**, order-agnostically, as a standalone corollary
        parametric in the formula slot — atoms and `⊥` are the same
        `b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w)` shape. Do **not**
        add fields to `IntMinScheme`.
  - [ ] Derive `intExtractValuation_upward_closed` (φ := `.atom p`) and
        `minBranchBotForces_upward_closed` (φ := `.bot`) as one-line specializations.
  - [ ] `Intuitionistic/Completeness.lean`: instantiate `IValid φ` at `World = ℕ`,
        `Preorder := intAccessPreorder edges`, `val := intExtractValuation b`, supplying the
        upward-closure corollary through Phase 6's weakened `hvalid`; reconcile
        `modelBot b = fun _ => False`; replace the `sorry`.
  - [ ] `Minimal/Completeness.lean`: instantiate `MValid φ` with
        `botForces := minBranchBotForces b`, supplying both corollaries for `MValid`'s two
        upward-closure obligations; replace the `sorry`.
  - [ ] Update both files' "Notes on sorry" module sections — they currently describe the
        deferral. No task numbers in the replacement prose.
  - [ ] `lean_verify` both public theorems: axiom-clean, no `sorryAx`.
- **Timing:** ~1 dispatch
- **Depends on:** 6, 12
- **Verification Tier:** interface
- **Scope Hypothesis:** the shared corollary can live in the `Completeness.lean` files or a small
  new module without needing private access to `Scheme.lean` internals. Confirm at implementation
  time; if privacy forces it into `Scheme.lean`, that edit must be serialized behind Phase 12
  (same file, single writer). Record the conversion rather than editing concurrently.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`,
  `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (fallback:
  `.../Intuitionistic/Scheme.lean` for the shared corollary, serialized behind Phase 12).

### Phase 14: CI and final verification [NOT STARTED]

- **Goal:** Confirm all three sorries are gone with no regressions, and full CI green.
- **Tasks:**
  - [ ] Bare-sorry census: `grep -n sorry` on both `Completeness.lean` files returns no bare
        `sorry`; DP-5 is gone from `Scheme.lean`.
  - [ ] Confirm **DP-2 is untouched** — `intFreshMint_preserves_nw` is another task's territory and
        was already retired there. Verify by content, not line number.
  - [ ] `lean_verify` on `intuitionisticTableau_complete`, `minimalTableau_complete`, `truthLemma`,
        `tableau_complete`, `openBranch_countermodel`, and `intExpandBranches_closed_unsat`: no new
        axioms, no `sorryAx`.
  - [ ] Full CI pipeline: `lake build`; `lake exe checkInitImports`; `lake lint`;
        `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix`; `lake test`.
  - [ ] `CslibTests/TableauConformance.lean` fully green.
  - [ ] Confirm no stray scratch modules under `Cslib/`, and that every probe artifact stayed in
        `specs/.../scratch/`.
  - [ ] Confirm **no task-number references** appear in any touched Lean file
        (`grep -nE 'task [0-9]+|tasks [0-9]+' Cslib/Logics/Propositional/Tableau/` returns
        nothing).
- **Timing:** ~30-45 min
- **Depends on:** 12, 13
- **Verification Tier:** full
- **Files to modify:** none (verification only; lint/shake auto-fixes if flagged).

## Planned Strategic Sorries

| Division Point | File / Line / Statement | Assumption | Why Deferred | Follow-Up Task |
|-----------------|--------------------------|------------|---------------|----------------|
| DP-2 fresh-mint `hNW` preservation | `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — `intFreshMint_preserves_nw` (re-locate by content; line numbers are stale in every prior artifact) | The creation-count invariant holds: a fresh mint preserves `nw + 1 ≤ WBound φ0` | Owned by task 585, **already retired there**. Recorded here only so no phase above touches it or re-proves it. Not a live sorry in this task's scope | 585 |
| Gate B2 refutation ⇒ terminal deferral of DP-3/DP-4/DP-5 | `Scheme.lean:727`; `Intuitionistic/Completeness.lean:140`; `Minimal/Completeness.lean:128` | None — this row records the *absence* of a viable route, not an assumed fact | Conditional on Phase 5 returning REFUTED. If the beta-split shape is realizable, the augmented-edge statement is **false**, and permanent deferral is the **sanctioned terminal answer** for all three at once. Escalation to the quotient/blocking-frame route is explicitly prohibited. Note that Phase 6's statement-shape fix remains worth landing even in this branch, since it converts an unfillable sorry into an honestly-stated one | none (terminal — see Rollback/Contingency) |
| Phase 9 COLLAPSED and Phase 10 exhausts its budget ⇒ deferral of DP-5 and, via it, DP-3/DP-4 | same three sites | The origin-tracing extension is constructible in principle (report 05 verdict `tractable_large`) but was not completed within budget | Conditional and non-terminal, unlike the row above: this is a *budget* outcome, not a refutation. The correct response is a `[PARTIAL]` handoff and a further dispatch, not deferral-as-answer | none (resumed by re-dispatch) |

**Note on follow-up tokens**: no `{{FOLLOWUP:i}}` placeholders appear above because this revision
creates no new follow-up tasks. Task 585 already exists and owns DP-2; the second row is a
terminal-deferral contingency with no follow-up by construction; the third is resumed by
re-dispatching this same plan.

## Reasoned Exclusions

Recorded pre-emptively at plan time (permitted by plan-format.md's "Relationship to Scope
Hypothesis"). No phase above currently carries `[COMPLETED WITH EXCLUSIONS]`; this section exists
so these decisions are not re-litigated mid-implementation.

| Item | Reason | Evidence |
|------|--------|----------|
| **Quotient / blocking-frame reconstruction** | **NO-GO, and explicitly not an escalation path after a Gate B2 refutation.** Two independent refutations. (1) In-repo: the ~480-line `intBlockRep` / `intAccessPreorderQ` stack was built, then refuted and deleted — `intBlockRep` is a function of the *final* branch and is not monotone under branch growth, so it cannot carry `intExpandBranches_openBranch_sat`'s **forward** induction. (2) Published: a filtration relation in the interval `S̲ ⊆ S ⊆ S̄` may be nontransitive even when `R` is transitive, and not all such `S` give filtrations of intuitionistic models. It also does not *sidestep* the `Force → T(_)@w' ∈ b` gap; it **relocates** it. | `574/reports/01_phase6-blocker-resolution.md` (§Executive Verdict, §Secondary Defect); 574 phase commits `b70eadc0`…`1ebf52ad` (built) and `175f7ea6` (deleted, grep-confirmed zero external references); `ChagrovZakharyaschev1997` §The Filtration Method — OCR visibly degraded, but the in-repo refutation is independent of it. |
| **The objection "the quotient refutation was about `openBranch_sat`, so it may not bind `truthLemma`"** | **The objection fails.** `truthLemma` runs over the final branch, so a quotient *could* be defined there — but `truthLemma` consumes `IBranchSaturation` / `IFimpAccess`, both produced by the forward induction, which is exactly where `intBlockRep`'s non-monotonicity bites. | Report 17 adversarial pass (H4) row 3; the conclusion `truthLemma` consumes. |
| **A T-imp-only or atom-only phase** | Excluded: zero public payoff either way. Both public completeness theorems carry independent sorries and both delegate to `truthLemma`; discharging one shape alone moves no public theorem from sorry-carrying to sorry-free. The obstruction is at the invariant level, not the formula shape, so the atom-only statement costs no less than the general one. | Report 17 F3, F6; `Intuitionistic/Completeness.lean:140`, `Minimal/Completeness.lean:128`, `Scheme.lean:727` (all three still `sorry`). |
| **Route C (containment preorder) and `≤`-on-ℕ upward closure** | Both empirically refuted before plan 04. Raw edge upward-closure FAILS (phi4); Route C containment REFUTED at imp-F (phi4); the raw valuation is provably not upward-closed under `≤`-on-ℕ (sibling worlds). | `reports/03_falsification-spike.md` (EXPERIMENT 1a and the imp-F refutation); `reports/02_team-research.md` S1. |
| **Restricting `hvalid` to `intExpandBranches … = .openBranch b` instead of strengthening `openBranch_countermodel`** | Not excluded as unsound — it is a valid alternative and report 05 lists it as such. Excluded as the *default* because the strengthening route keeps the obligation stated in terms of the mathematical fact (upward closure) rather than the algorithm's provenance, which is the more reusable shape. Phase 6 may adopt it if the preferred route hits an obstruction, recording the switch. | Report 05 §1 ("Required fix", the two bulleted options, with "(preferred)" on the strengthening route). |
| **`intWorldHist_chain_le`, `pathOf`, `pathOf_injOn`, `intWorldHist_nw_le` as reuse wins** | Excluded from every phase's reuse budget. These are pigeonhole/world-**bound** machinery, relevant to bounding rather than persistence. Counting them as savings would understate Phase 10's real cost. | Report 05 §2, verbatim: "Relevant to *bounding*, largely **not** to persistence; do not budget these as reuse wins." |
| **Report 13's "no world bound of any size exists"** | **Superseded, not contradicted.** It measured the *pre-repair* calculus and is correct about it. Post-repair, `WBound φ0` and `intUniverseExt` exist and `applyPersistenceFixpoint_genuine_of_count_le_fuel` is landed sorry-free over them. Do not let a stale reading shape any phase. | Report 17 F4 and H4 row 4; `Scheme.lean:1692` (`WBound`), `:1721` (`intUniverseExt`), the landed fixpoint lemma. |
| **Report 17's 600-1200 line cost estimate as a budget** | The author marks it **low confidence**, anchored on the ~480-line quotient stack and a ~92-line prototype as reference class. Recorded as context, never as a budget; no phase is sized against it. | Report 17 F8 and its Confidence Levels section. |

## Testing & Validation

- [x] **Phase 5 (Gate B2)**: probe builds green in `scratch/`; a reuse event demonstrably fired and
      both `w` and `x` carry the same disjunction (otherwise INCONCLUSIVE, not PASS); the
      **augmented** edge list was used, not the raw one; explicit REFUTED/PASS/INCONCLUSIVE verdict
      recorded in `handoffs/04_gate-b2-verdict.md`. Verdict: **PASS** (residual risk carried
      forward, not exhaustively refuted).
- [x] `git status --short Cslib/ CslibTests/` empty of Phase-5-attributable changes (Phase 6's
      three files, landed in parallel per the Gating contract, are the only `Cslib/` changes).
- [x] **Phase 6**: `scratch/HvalidShapeRefutation.lean` re-confirmed to compile before any
      signature edit; `tableau_complete`'s own proof body sorry-free after the change (it
      transitively reports `sorryAx` via `openBranch_countermodel`'s new, deliberately-deferred
      conjunct -- expected at this phase, not a violation); `Soundness.lean` untouched
      (`git diff --stat` shows no change to it).
- [ ] **Phase 7**: raw-edge conjunct exported; every `intExpandBranches_openBranch_sat` call site
      repaired; `lean_verify` axiom-clean.
- [ ] **Phase 9**: verdict CLOSED or COLLAPSED recorded in
      `handoffs/05_post-reuse-closure-verdict.md`; no `sorry`, no vacuous placeholder, no weakened
      statement introduced in either branch.
- [ ] **Phase 11**: two-hop composition constructed concretely before the general claim.
- [ ] `grep -n sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` → no
      bare `sorry`.
- [ ] `grep -n sorry Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` → no bare
      `sorry`.
- [ ] DP-5 closed in `Scheme.lean` (at `:727` or wherever content-relocation finds it); DP-2
      untouched.
- [ ] `lean_verify` on `intuitionisticTableau_complete`, `minimalTableau_complete`, `truthLemma`,
      `tableau_complete`, `openBranch_countermodel`, `intExpandBranches_closed_unsat`: no new
      axioms, no `sorryAx`.
- [ ] `Soundness.lean` remains sorry-free and `intExpandBranches_closed_unsat` axiom-clean at every
      phase boundary.
- [ ] Full CI: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`, `lake test`, `TableauConformance`.
- [ ] Docstrings updated, not left stale: `Scheme.lean`'s STOP-gate note and both
      `Completeness.lean` "Notes on sorry" sections reflect the closed state.
- [ ] No task-number references in any touched Lean file.

## Artifacts & Outputs

- plans/06_gate-b2-then-origin-tracing-export.md (this file)
- plans/04_positive-formula-persistence-augmented.md (superseded, preserved unmodified)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/BetaSplitProbe.lean`
  (Phase 5, scratch only)
- Existing scratch, preserved: `VariantProbe.lean` (Gate A), `PersistPrototype.lean` (Gate B),
  `HvalidShapeRefutation.lean` (the machine-verified statement-shape refutation — **do not
  delete**; it is Phase 6's evidence)
- handoffs/04_gate-b2-verdict.md (Phase 5 verdict — the gating record)
- handoffs/05_post-reuse-closure-verdict.md (Phase 9 verdict — CLOSED or COLLAPSED)
- Existing handoffs, preserved: 01 (Gate A), 02 (Gate B), 03 (Phase 5 investigation)
- Edited: `Intuitionistic/Scheme.lean`, `Intuitionistic/Completeness.lean`,
  `Minimal/Completeness.lean`. `Intuitionistic/Expansion.lean` and `Intuitionistic/Soundness.lean`
  were edited in Phase 3 and are **not** expected to change again.
- summaries/06_gate-b2-then-origin-tracing-export-summary.md (on implementation)

## Rollback/Contingency

- **Phase 5 returns REFUTED**: **the statement is false and the approach is over.** Permanent
  deferral becomes the **sanctioned terminal answer** for DP-3, DP-4 and DP-5 at once. Record the
  failing instance in `handoffs/04_gate-b2-verdict.md`, re-annotate all three sorries as terminally
  deferred with the Gate B2 evidence, and mark the task `[BLOCKED]`. **Do NOT escalate to the
  quotient / blocking-frame route** — it is refuted twice over and a Gate B2 refutation is not new
  evidence in its favour. Phase 6 may still be landed independently as a statement-shape
  correction; that is the only remaining work in this branch. No `Cslib/` writes have been made by
  Phase 5, so there is nothing to roll back.
- **Phase 5 returns INCONCLUSIVE**: re-run with a widened `φ0` family. Do **not** treat
  INCONCLUSIVE as PASS and do not open Phase 7 on it.
- **Phase 6's signature change breaks more than the enumerated call sites**: the phase is
  `atomic-batch`; nothing is committed until the batch is green, so `git checkout` of the touched
  files to HEAD restores the pre-phase state. Record which consumer was missed and re-enumerate.
- **Phase 9 returns COLLAPSED**: proceed to Phase 10. This is a planned branch, not a failure.
- **Phase 10 exhausts its budget**: record a `[PARTIAL]` handoff with zero `Cslib/` writes left
  red, no `sorry`, no weakened statement — the same discipline Phase 5's blocker record followed.
  Re-dispatch rather than deferring.
- **Phase 11 finds composition fails**: stop and record it as a blocker. Do not export a general
  invariant justified only by a single-hop proof.
- **A later proof phase fails**: revert that file to the last green commit. Phases 7-13 are
  strictly sequential on `Scheme.lean`, so at most one file is in flight at a time.
- **Territory conflict detected mid-flight** (317, 574, or 585 writing `Scheme.lean`): stop, yield
  the file to the single writer, and re-synchronize at the next phase boundary. `file_scope` is
  populated in this task's metadata so the orchestrator can serialize this in advance.
