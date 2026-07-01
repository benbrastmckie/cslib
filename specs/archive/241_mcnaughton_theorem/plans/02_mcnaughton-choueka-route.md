# Implementation Plan: McNaughton's Theorem — Choueka Route (Task #241, v2)

- **Task**: 241 - mcnaughton_theorem
- **Status**: [COMPLETED]
- **Effort**: 12 hours
- **Dependencies**: None blocking. All prerequisite CSLib infrastructure compiles. This plan
  **supersedes the `buchiCongr_DMA`-quotient implementation path** taken by subtasks 433–436
  (see Disposition below); it does not depend on completing subtask 434 (a confirmed dead end).
- **Research Inputs**:
  - specs/241_mcnaughton_theorem/reports/02_mcnaughton-ctchou-port-path.md (Choueka lemma DAG)
  - specs/241_mcnaughton_theorem/reports/01_ctchou-coordination-seed.md (literature seed)
  - specs/434_prove_backward_inclusion_buchicongr_dma_language_backward/.orchestrator-handoff.json
    (backward-inclusion soundness-gap writeup — the revision blocker)
  - specs/434_prove_backward_inclusion_buchicongr_dma_language_backward/plans/01_backward-inclusion-buchicongr-dma.md
    (Phase 2 [BLOCKED] root-cause analysis)
- **Artifacts**: plans/02_mcnaughton-choueka-route.md (this file); supersedes plans/01_mcnaughton-da-muller.md
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md; lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Discharge `proof_wanted Cslib.ωLanguage.IsRegular.iff_da_muller`
(`Cslib/Computability/Languages/OmegaRegularLanguage.lean:653`), proving McNaughton's theorem:
an ω-language is ω-regular (recognized by a finite-state nondeterministic Büchi automaton) **iff**
it is recognized by a finite-state deterministic Muller automaton.

This is **plan v2**. It is an *architectural pivot*, not a refinement of v1's execution. The v1
implementation waves (subtasks 433–436) attempted the forward direction (ω-regular ⊆ DMA) via a
`buchiCongr_DMA` construction — a DMA whose **states are Büchi-congruence classes** and whose
accept condition is a Muller condition on the run's `infOcc`. That path hit a **genuine soundness
gap** in its backward inclusion (`buchiCongr_DMA_language_backward`, subtask 434): the accept set
`{S | ∃ b ∈ S, ∃ a, (buchiFamily (a,b) ⊓ language na).Nonempty}` is too permissive — `xs`'s own
Ramsey factorization yields a companion class `c` not provably equal to the accept-set witness
`a`, and "goodness of `(b, X)`" is not provably companion-independent. Closing it would require a
linked-pair / Wilke-algebra independence theorem absent from CSLib. The upstream reference project
`ctchou/AutomataTheory` (which CSLib's automata stack is a first-party port of) **does not use this
quotient-as-DMA construction** for McNaughton — it uses the **Choueka decomposition** route.

Plan v2 therefore **commits the forward direction to the Choueka route** and **routes around
`buchiCongr_DMA` entirely**. Crucially, ground-truth inspection of the current tree (done during
this revision) shows the Choueka infrastructure is far more complete than v1's reports assumed:

- **Reverse direction `(⇐)` is already DONE and green**: `IsRegular.of_da_muller`
  (`OmegaRegularLanguage.lean:278`, sorry-free).
- **Base case is already DONE and green**: `IsRegular.omegaLim_da_muller`
  (`OmegaRegularLanguage.lean:81`) — "the ω-limit of a regular language is recognized by a
  finite-state DMA", explicitly "the base case of McNaughton's compositional determinization".
- **The Choueka flag-construction concat automaton already EXISTS** as a construction:
  `DA.concat` + `mullerAccConcat` + structural helpers (`concat_run_fst`,
  `concat_run_stabilizes`, `concat_freeSlot`, …) in `Cslib/Computability/Automata/DA/Concat.lean`
  — "produces a DMA recognizing the product `L₁ · L₂` of a regular language `L₁` and a Muller
  language `L₂`". **What is missing is its top-level language-correctness theorem.**

So the genuine remaining work is three new analytic lemmas plus assembly, all phased as
single-agent-run green checkpoints. Done means: `proof_wanted IsRegular.iff_da_muller` is replaced
by a complete `theorem`, full CI green, zero `sorry`, zero new axioms (verified via `lean_verify`),
and the dead `buchiCongr_DMA` cluster is removed.

### Research Integration

- **02_mcnaughton-ctchou-port-path.md** (primary): establishes CSLib's automata stack is Chou's
  own Apache-2.0 port of AutomataTheory, recommends the **Choueka congruence/saturation route
  (NOT Safra, NOT quotient-as-DMA)**, sequences easy `(⇐)` before hard `(⇒)`, and supplies the
  literature proof structure (Choueka identity `Vᵒᵐᵉᵍᵃ = V*·U↗ᵒᵐᵉᵍᵃ`; ω-limits are
  DMA-recognizable; DMA closure under finite union). This plan operationalizes that route.
- **task-434 handoff + plan** (revision driver): documents the `buchiCongr_DMA` backward-inclusion
  soundness gap and confirms (via cross-reference to `AutomataTheory/Languages/DetMullerLang.lean`)
  that the reference McNaughton proof avoids the quotient-as-DMA construction. This is the evidence
  base for deprecating that path.
- **01_ctchou-coordination-seed.md** (context): literature references (McNaughton 1966; Thomas
  1990; Perrin–Pin 2004); superseded by report 02 on architecture.

### Lemma-Location Verification (directive #5)

All cited Choueka-route lemmas were re-verified against the current tree during this revision.
**Present and green**, with two line-number shifts since report 02 was written (the file grew as
subtasks 433–435 landed):

| Lemma | Report-stated loc | Current loc | Status |
|-------|-------------------|-------------|--------|
| `IsRegular.regular_omegaLim` | :73 | OmegaRegularLanguage.lean:74 | green |
| `IsRegular.omegaLim_da_muller` | (not noted) | OmegaRegularLanguage.lean:81 | green — **base case already done** |
| `IsRegular.eq_fin_iSup_hmul_omegaPow` | :195 | OmegaRegularLanguage.lean:205 | green (moved) |
| `IsRegular.fin_cover_saturates` | :224 | OmegaRegularLanguage.lean:234 | green (moved) |
| `IsRegular.of_da_muller` | (not noted) | OmegaRegularLanguage.lean:278 | green — **reverse already done** |
| `DA.buchi_eq_finAcc_omegaLim` | DA/Buchi.lean:26 | DA/Buchi.lean:26 | green |
| `DA.Buchi.toMuller` / `…_language_eq` | DA/BuchiChar.lean:88 | DA/BuchiChar.lean:76 / :88 | green |
| `DA.Rabin.toMuller_language_eq` | DA/Rabin.lean:163 | DA/Rabin.lean:163 | green |
| `DA.concat` / `mullerAccConcat` | (not noted) | DA/Concat.lean:137 / :163 | green — `concat_language_eq` proved in Phase 2 (construction itself fixed for an empty-prefix bug; see Phase 2 completion note) |
| `DA.prod` / `prod_run_eq` | (not noted) | DA/Prod.lean:27 / :41 | green |
| `DA.Buchi.union` / `…_language_eq` | (not noted) | DA/BuchiClosure.lean:44 / :54 | green (template for Muller union) |
| `toNABuchi` / `…_language_eq` | DA/ToNA.lean:74/80 | DA/ToNA.lean:74 / :80 | green |

No cited lemma is missing or removed. The `buchiFamily_*` / `fin_cover_saturates` saturation
cluster remains in place (used by `IsRegular.compl`); it is **not** consumed by the Choueka
forward route below (it was the analytic core of the *abandoned* quotient path).

### Prior Plan Reference

Supersedes **plan v1** (`plans/01_mcnaughton-da-muller.md`). v1 named the Choueka route in its
prose but its Phase 3 ("Muller-packaging lemma") was implemented as the `buchiCongr_DMA`
quotient-as-DMA construction (subtasks 433–436), which is the path this revision abandons. v1
Phases 0–1 (coordination; reverse direction `of_da_muller`) and Phase 2 (decomposition scaffold)
produced green assets that this plan **reuses or supersedes** as itemized in the Disposition.

## Disposition of the `buchiCongr_DMA` Cluster (directive #2)

The Choueka forward route assembles ω-regular ⊆ DMA from `eq_fin_iSup_hmul_omegaPow` + `DA.concat`
+ a new `omegaPow_da_muller` + a new Muller-union closure — it **never references `buchiCongr_DMA`**.
The quotient cluster is therefore **dead code under the pivot**. Explicit disposition (no silent
orphaning; deletions of working code are stated openly here):

| Declaration (OmegaRegularLanguage.lean) | Subtask | State | Disposition |
|------|------|------|------|
| `buchiCongr_DMA_language_backward` (:546, **`sorry` at :588**) | 434 | BLOCKED, carries the only `sorry` in the file | **DELETE in Phase 1** (restores sorry-free build; structurally unprovable as written) |
| `proof_wanted buchiCongr_DMA_language_eq` (:602) | 436 | stub, unprovable via this construction | **DELETE in Phase 1** |
| `buchiCongr_DMA_accept_mem` (:447) | 433 | **green, sorry-free** | **Dead code → remove in Phase 6.** NOT reusable in the Choueka assembly. Its `infinite_graph_ramsey` recurrence reasoning is noted as a *reference* the implementer may consult for `concat_language_eq` / `omegaPow_da_muller`, but it is not a code dependency. |
| `buchiCongr_DMA_language_forward` (:530) | 435 | **green, sorry-free** | **Dead code → remove in Phase 6** (depends on `accept_mem`; not reused). |
| `buchiCongr_DMA` def (:388), `buchiCongr_DMA_run_eq` (:406) | — | green | **Remove in Phase 6** (support for the above). |
| `IsRegular.to_da_muller_scaffold` (:625) | 241/v1-ph2 | green scaffold, `h_pkg` over the congruence quotient | **Remove in Phase 6** — superseded by the Choueka forward assembly (Phase 5). |
| `buchiFamily_component_isRegular` (:364) | 241/v1-ph2 | green | **Retain** — independently meaningful (ω-regularity of a Büchi-family component); keep unless `lake lint`/`shake` flags it unused after Phase 6, in which case remove. |

**Why remove rather than retain the green cluster.** Leaving a `proof_wanted`
(`buchiCongr_DMA_language_eq`) that is known-unprovable as written, plus its supporting private
lemmas, is misleading dead infrastructure, and CSLib's `lake lint` / `lake shake` would flag the
orphaned privates once the `proof_wanted` is removed. The sorry-bearing `language_backward` is
removed **first** (Phase 1) so the build is sorry-free immediately; the remaining green cluster is
preserved until the Choueka forward direction is green (Phase 5), then removed in the final cleanup
(Phase 6) — so a working replacement always exists before old code is deleted and no green
milestone is lost mid-flight.

**Safety**: all cluster members are `private` (or a `proof_wanted`) and referenced only within
this file; deletion is self-contained. The `IsRegular.iff_da_muller` docstring (lines 647–652)
references `to_da_muller_scaffold` and must be updated to the Choueka route (Phase 1).

## Goals & Non-Goals

**Goals**:
- Replace `proof_wanted IsRegular.iff_da_muller` with a complete, sorry-free `theorem`.
- Forward `(⇒)` ω-regular → DMA via the Choueka route: `eq_fin_iSup_hmul_omegaPow` decomposition +
  `DA.concat` correctness + `omegaPow_da_muller` + DMA finite-union closure.
- Reuse the already-green reverse direction `IsRegular.of_da_muller` for `(⇐)`.
- Restore and keep a **sorry-free** build (delete the subtask-434 `sorry`).
- Remove the dead `buchiCongr_DMA` cluster per the Disposition.
- Pass the full CSLib CI pipeline; zero `sorry`, zero new axioms
  (`lean_verify Cslib.ωLanguage.IsRegular.iff_da_muller`).

**Non-Goals**:
- Downstream corollaries `IsRegular.iff_da_rabin` / `iff_da_parity` (separate `proof_wanted`s).
- Any Safra-style determinization.
- Reviving or repairing the `buchiCongr_DMA` accept set / linked-pair-independence lemma.
- Refactoring the `buchiFamily_*` saturation cluster (it remains in service of `IsRegular.compl`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `DA.concat` language-correctness (`concat_language_eq`, Phase 2) is the deepest single proof (flag/dedup construction); the structural helpers may not compose cleanly into the language equality. | H | M | Phase 2 is isolated to one agent run against the **existing** helpers. Map the proof obligation directly to `AutomataTheory/Languages/DetMullerLang.lean`'s concat-correctness lemma (Phase 1 extracts this reference DAG). Use `lean_goal`/`lean_multi_attempt` at each step. If it cannot close, mark Phase 2 [BLOCKED] with the exact goal state — do NOT add `sorry`. |
| `omegaPow_da_muller` (Phase 3): bridging ω-power `M^ω` to a DMA may need the Choueka identity `M^ω = M*·U↗ᵒᵐᵉᵍᵃ`, which is **not yet in CSLib**. | H | M | Phase 1 confirms (from Chou's source) whether the reference proof goes through the identity or a direct flag/omega construction over `DA.concat`. Phase 3 builds exactly that lemma; flag the identity as a NEW sub-lemma if required (see "New Supporting Lemmas"). |
| DMA finite-union closure (Phase 4) does not exist (only DBA `Buchi.union`). | M | L | Mirror `DA.Buchi.union` / `union_language_eq` (BuchiClosure.lean) over `DA.prod`; the Muller accept family on the product is `{S | π₁''S ∈ acc₁ ∨ π₂''S ∈ acc₂}`. Mechanical. |
| `Finite`/universe bookkeeping between `IsRegular`'s existential `State` and the assembled DMA state. | M | M | Use `isRegular_iff` universe lifting (already in file) and thread `Finite` instances explicitly, as `of_da_muller` and `omegaLim_da_muller` already do. |
| A Choueka sub-goal cannot close without new mathematics. | H | L | Zero-debt policy: mark the phase [BLOCKED], record `lean_goal` + attempts, transition task to [BLOCKED]. Unlike the abandoned quotient path, this route **has a verified reference proof** in AutomataTheory, lowering this risk. |
| `lake shake` flags imports after adding `DA/Concat` correctness / a new Muller-union file. | L | M | Run `lake shake --add-public --keep-implied --keep-prefix` at each phase end; apply `--fix`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 4 | -- |
| 2 | 3 | 2 |
| 3 | 5 | 2, 3, 4 |
| 4 | 6 | 1, 5 |

Phases within a wave are independent and may run in parallel by different agents (disjoint
files/declarations): Phase 1 edits the `buchiCongr_DMA` region of `OmegaRegularLanguage.lean`;
Phase 2 edits `DA/Concat.lean`; Phase 4 adds a new `DA/MullerClosure.lean`. Phase 5 assembles in
`OmegaRegularLanguage.lean` after Phases 2–4 land.

### Phase 1: Deprecate the `buchiCongr_DMA` path; restore sorry-free build [COMPLETED]

- **Goal:** Remove the soundness-gap `sorry` and the unprovable `proof_wanted`, update the target
  docstring to the Choueka route, and extract the reference lemma DAG for Phases 2–4.
- **Tasks:**
  - [x] Read `AutomataTheory/Languages/DetMullerLang.lean` (and `OmegaRegLang.lean`) for the
    reference McNaughton forward proof; extract the exact lemma DAG and map each node to: an
    existing CSLib lemma, or a Phase 2/3/4 obligation. Record the 5-column mapping in the
    completion summary scaffold. Confirm whether `M^ω` recognizability goes via the Choueka
    identity `M^ω = M*·U↗ᵒᵐᵉᵍᵃ` or a direct `DA.concat`-based omega construction (drives Phase 3).
    *(Done: reference DAG recorded below; confirmed route (a) — the Choueka identity `M^ω = M*·U↗ᵒᵐᵉᵍᵃ` — is required for Phase 3.)*
  - [x] Delete `buchiCongr_DMA_language_backward` (the `sorry` at :588) and
    `proof_wanted buchiCongr_DMA_language_eq` (:602). *(Committed ce381c24.)*
  - [x] Update the `IsRegular.iff_da_muller` docstring (:647–652) to describe the Choueka route
    (decomposition → concat → omega-power → finite union) and drop the `to_da_muller_scaffold` /
    quotient references. *(Committed ce381c24.)*
  - [x] Leave the remaining green cluster (`buchiCongr_DMA` def, `run_eq`, `accept_mem`,
    `language_forward`, `to_da_muller_scaffold`) in place **for now** (removed in Phase 6). If
    `lake build` / `lake lint` flags any as unused after deleting `language_eq`, delete it here.
    *(Done: cluster retained for Phase 6 removal; build green sorry-free.)*
- **Timing:** 1.5 hours
- **Depends on:** none
- **Files to modify:** `Cslib/Computability/Languages/OmegaRegularLanguage.lean`
- **Proof obligations:** none (deletions + docstring). Output: sorry-free build + reference DAG.
- **Verification:** `lake build Cslib.Computability.Languages.OmegaRegularLanguage` green;
  `grep -n "sorry\|admit" …/OmegaRegularLanguage.lean` returns nothing; reference DAG recorded.

**Phase 1 result (COMPLETED)**: Deleted `buchiCongr_DMA_language_backward` (the subtask-434
`sorry`) and `proof_wanted buchiCongr_DMA_language_eq`. Build green
(`lake build Cslib.Computability.Languages.OmegaRegularLanguage`), zero `sorry`/`admit` in the
file. Docstring of `IsRegular.iff_da_muller` updated to describe the Choueka route. Remaining
green cluster (`buchiCongr_DMA`, `buchiCongr_DMA_run_eq`, `buchiCongr_DMA_accept_mem`,
`buchiCongr_DMA_language_forward`, `IsRegular.to_da_muller_scaffold`) left in place per
disposition, to be removed in Phase 6.

**Reference DAG (extracted from `ctchou/AutomataTheory`, cached copies of
`Languages/DetMullerLang.lean` and `Languages/OmegaRegLang.lean` found in a prior session's
scratchpad)**:

| AutomataTheory node | Maps to CSLib | Status |
|---|---|---|
| `omega_reg_lang_iff_finite_union_form` | `IsRegular.eq_fin_iSup_hmul_omegaPow` | green (already in CSLib) |
| `det_muller_lang_omega_limit` | `IsRegular.omegaLim_da_muller` | green (base case, already done) |
| `choueka_lemma : L^ω = L* * L'↗ω` (L' regular) | **NEW**, needed by Phase 3 `omegaPow_da_muller` | missing — confirmed required (route (a) in Phase 3, not route (b)) |
| `det_muller_lang_concat` (`M0.Concat acc0 M1` + `MullerAcc_Concat`) | `DA.concat` + `mullerAccConcat` correctness = **Phase 2 `concat_language_eq`** | green — proved in Phase 2 |
| `det_muller_lang_biUnion` / `det_muller_lang_union` (`Automata.DA.Prod` + `MullerAcc_Union`) | **Phase 4 `DA.Muller.union`** (new `MullerClosure.lean`, mirrors `DA.Buchi.union`) | missing |
| `omega_reg_lang_imp_det_muller_lang` (assembly: biUnion over `det_muller_lang_concat (U i) ((V i)^ω)`) | **Phase 5 `IsRegular.to_da_muller`** | to assemble |
| `omega_reg_lang_iff_det_muller_lang` | **Phase 6 `IsRegular.iff_da_muller`** | to assemble |

**Choueka identity confirmed required**: the reference proof does NOT build the ω-iteration DMA
directly (Phase 3 route (b)); it goes through `choueka_lemma : L^ω = L* * L'↗ω` for some *new*
regular `L'` (route (a)), then `det_muller_lang_concat (L*) (L'↗ω)` using the already-green
ω-limit base case. Phase 3 must therefore either port `choueka_lemma`'s content (a nontrivial
regular-language construction over the determinized loop automaton — in AutomataTheory this is
`M.ChouekaLang acc` via `Automata.choueka_lang_regular` /
`Automata.choueka_lang_omega_power_eq_omega_limit`, neither of which exists in CSLib) or find an
equivalent CSLib-native construction of `L'`. This is flagged as the deepest remaining risk,
worse than stated in the original Phase 3 risk table: it is not just "may need the identity" —
the reference proof structure **requires** it, and its supporting regular-language construction
(`ChouekaLang`) is entirely new to CSLib, not just the top-level identity lemma.

### Phase 2: `DA.concat` language correctness (`concat_language_eq`) [COMPLETED]

- **Goal:** Prove the top-level correctness theorem for the existing Choueka flag-construction
  concat automaton: `language (DA.concat da1 acc1 da2) = (language of L₁) * (Muller language of da2)`
  (exact statement per `DetMullerLang.lean` reference and the `mullerAccConcat` accept family).
- **Tasks:**
  - [x] State `concat_language_eq` for `DA.concat da1 acc1 da2` with accept `mullerAccConcat …`.
  - [x] Prove using the existing structural helpers: `concat_run_fst` (first component = `da1` run),
    `concat_run_stabilizes`, `concat_freeSlot`, `concat_tr_snd'` (flag dedup), plus
    `option_some_pigeonhole` / `antitone_fin_eventually` (already in the file).
    *(deviation: also required fixing a genuine off-by-one bug in the `concat`/`concatF2`
    construction itself — see completion note below — plus ~20 new private lemmas beyond the
    ones the plan anticipated reusing.)*
  - [x] `lean_goal` at each step; `lean_multi_attempt` before edits.
- **Timing:** 4 hours (deepest single proof)
- **Depends on:** none (uses only existing Concat.lean helpers; Phase 1's DAG is advisory)
- **Files to modify:** `Cslib/Computability/Automata/DA/Concat.lean`
- **Proof obligations:** `language (DA.concat …) = L₁ * (DMA language)`; both inclusions via the
  flag-stabilization argument already scaffolded by the helpers.
- **Verification:** `lake build Cslib.Computability.Automata.DA.Concat`;
  `lean_verify` on `concat_language_eq` shows no `sorry`/new axioms. **If unclosable:** mark
  [BLOCKED] with the `lean_goal` state; do not add `sorry`.

**Phase 2 result (COMPLETED)**: `concat_language_eq` proved and committed. Build green
(`lake build Cslib.Computability.Automata.DA.Concat`), zero `sorry`/`admit` in the file,
`lean_verify` reports only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Construction bug found and fixed (deviation from the plan's "prove using the existing
construction unchanged" framing)**: before writing the correctness proof, a concrete
counterexample was constructed and checked: let `da1` be a 2-state automaton whose *only*
accepted string is `[]` (start state in `acc1`, every transition leaves `acc1` forever), and
let `da2` be a trivial single-state DMA with `accSet2 = {univ}` (accepts everything). Then
`language (FinAcc.mk da1 acc1) * language (Muller.mk da2 accSet2) = univ` (via the empty-prefix
decomposition), but the *original* `concat`/`concatF2` (as committed by task 432) checked the
**post**-transition M1 state (`da1.tr s1 a ∈ acc1`) to decide slot activation, which can never
fire from the automaton's very first step — so it could never witness `da1.start ∈ acc1`
accepting the empty prefix, making its language `∅ ≠ univ`. This traces to a genuine deviation
from the reference construction (`ctchou/AutomataTheory`'s `DA.Concat`, cached at
`/tmp/Automata_DetConcat.lean`), which checks the **pre**-transition state `s1 ∈ acc1` and
immediately advances the freshly-activated copy by the current symbol (`M2.next M2.init a`,
not raw `M2.init`) — the two changes exactly compensate for each other's off-by-one.
Fixed `concatF2` and `concat`'s `tr` field accordingly (check `s1 ∈ acc1` instead of
`da1.tr s1 a ∈ acc1`; activate with `some (da2.tr da2.start a)` instead of `some da2.start`);
updated `concat_tr_snd`/`concat_tr_snd'` to match (still `rfl`); `concat_tr_nodup` and
`concat_freeSlot`'s existing proofs were unaffected (activation-condition-agnostic) and
required no changes. This fix is confined to `Concat.lean`, self-contained, and necessary for
`concat_language_eq` to be true as a general (unconditional) equality — the alternative
(adding a side condition excluding `da1.start ∈ acc1`) would have propagated a hole into
Phase 5's assembly, since components of the `eq_fin_iSup_hmul_omegaPow` decomposition may
contain the empty word.

**New private lemmas added** (all sorry-free, docstring-complete, mirroring
`ctchou/AutomataTheory`'s `DetConcat.lean` proof strategy but re-derived against CSLib's actual
flag-array/dedup encoding, which differs structurally from the reference's per-slot recursive
`next`): `concatF2_of_some`, `concat_tr_snd_of_some`, `concat_tr_snd_of_none` (per-slot
characterization of transition outputs), `concat_dedup_exists_of_f2` (dedup preserves
existence of any pre-dedup value, at an index `≤` the input witness), `concat_run_activate`,
`concat_run_advance`, `concat_run_activate_exists`, `concat_run_tracks` (run-level
persistence/tracking lemmas), `concat_ptr_exists`, `concat_run_unique_of_some`, `ConcatPtr` +
`concat_ptr_spec`, `concat_ptr_antitone`, `concat_ptr_eventually` (the forward-direction
"shifting witness slot stabilizes" argument, via `antitone_fin_eventually`), `concat_persist_from_activity`
(backward-direction breakpoint extraction via `Nat.findGreatest`), `eventually_mem_infOcc`
(general finite-state fact: the run is eventually always in its own `infOcc`),
`concat_slot_infOcc_eq`, `concat_slot_isSome_of_infOcc` (assembly glue for both directions).

**Proof structure actually used** (differs from the plan's sketch in using a `Nat.findGreatest`
breakpoint search for the backward direction, and an antitone-stabilizing-pointer construction
for the forward direction, rather than the plan's more informal "last activation"/"most recent
entry" framing — same underlying mathematical content as `ctchou/AutomataTheory`'s
`da_concat_det_run_2`/`da_concat_ptr2_exists`, ported to CSLib's construction):
- **Forward** (`⊇`, given `n` with `da1.run xs n ∈ acc1` and `da2.run (xs.drop n)` Muller-accepted):
  `concat_ptr_eventually` produces a witness slot `i` that stabilizes from some time `m` onward;
  `concat_slot_infOcc_eq` (parameterized by a bound `m0`, here `m`) transports the `accSet2`
  membership; `concat_slot_isSome_of_infOcc` shows every recurring state has `i` active.
- **Backward** (`⊆`, given a `mullerAccConcat` witness slot `i`): `eventually_mem_infOcc` gives a
  time `N` after which the run is always in its own `infOcc` (hence slot `i` is `isSome` from
  `N` on); `concat_persist_from_activity` uses `Nat.findGreatest` (the latest inactivity of
  slot `i` at or before `N`) to extract the breakpoint `n`; `concat_slot_infOcc_eq` (with
  `m0 = 0`) transports the `accSet2` membership back.

Full CI for this module: `lake build Cslib.Computability.Automata.DA.Concat` green;
`lake exe lint-style` reports 2 pre-existing errors in `Cslib/Logics/Modal/Tableau/Completeness.lean`,
a file untouched by this dispatch and not in `git status` as modified — belongs to a concurrent
task in this shared working tree (same pattern flagged by the Phase 1/4 dispatch for
`SoundnessStep.lean`). `lake lint`/`lake shake` could not be run project-wide this dispatch:
the shared tree currently has out-of-date/broken oleans in unrelated modules
(`Cslib.Logics.Temporal.*`, `Cslib.Logics.Propositional.Tableau.Minimal.Completeness` has an
existing `sorry`) belonging to other concurrent tasks, so any whole-project command fails before
reaching our file. Manually verified instead: every new declaration has a docstring (docBlame
prevention), names are lowerCamelCase, no new axioms (`lean_verify`), and the file's own
imports are unchanged from the version that already passed `checkInitImports` at commit
`068f91cf`.

### Phase 3: `omegaPow_da_muller` — `Mᵒᵐᵉᵍᵃ` is DMA-recognizable [COMPLETED]

- **Goal:** Prove that for a regular language `M`, the ω-power `M^ω` is recognized by a
  finite-state DMA: `(M.IsRegular) → ∃ (S) (_ : Finite S) (da : DA.Muller S Symbol), language da = M^ω`
  (or the exact shape the assembly consumes).
- **Tasks:**
  - [x] Per Phase 1's DAG decision route (a): prove the Choueka identity
    `M^ω = M* · U↗ᵒᵐᵉᵍᵃ` (NEW sub-lemma, regular `U`) and combine `regular_omegaLim` /
    `omegaLim_da_muller` (base case, already green) with `concat_language_eq` (Phase 2).
    *(deviation: split into 3 milestones, all 3 now landed across two dispatches — see below)*
  - [x] Discharge `Finite` of the resulting state space. Done in Milestone 3/3's
    `IsRegular.omegaPow_da_muller`: `Finite (State1 × (Fin (Nat.card State2 + 2) → Option State2))`
    via `inferInstance`, threading `Finite` from `Language.IsRegular.iff_dfa` and
    `IsRegular.omegaLim_da_muller`'s existentials.
  - [x] `lean_goal` / `lean_multi_attempt` throughout (used via lean-lsp MCP during all three
    milestones).

**Milestone 1/3 (COMPLETED, committed `11807051`)**: New file
`Cslib/Computability/Automata/DA/Choueka.lean` — `DA.chouekaLang` (the Choueka language of a
`DA`/accept-set pair, ported from `ctchou/AutomataTheory`'s `ChouekaLemma.lean`) and
`DA.chouekaLang_regular` (regularity, via an algebraic decomposition
`chouekaLang = ⨆ s ∈ acc, chouekaA s * (chouekaB s ⊓ (chouekaB s * 1ᶜ)ᶜ)` into finitary
regular-language operations). Scoped build green, sorry-free, standard axioms only.

**Milestone 2/3 (COMPLETED, committed `602293de`)**: Added `greater_subseq` (interleaving
lemma for a strictly monotone/injective pair of breakpoint sequences) and
`DA.chouekaLang_omega_limit_subset_omega_power` — the *easier* inclusion of the Choueka
identity: `(chouekaLang da acc)↗ω ⊆ (language (FinAcc.mk da acc))^ω`, requiring no finiteness
of `State`. Uses CSLib's `ωSequence.frequently_iff_strictMono`, `omegaPow_seq_prop`,
`take_extract`/`drop_extract`/`length_extract`/`append_extract_extract`. Scoped build green,
sorry-free, standard axioms only.

**Milestone 3/3 (COMPLETED, committed `8ba346f8` + `29ba3eb2`)**: The harder, Ramsey-based
reverse inclusion `DA.chouekaLang_omega_power_subset_omega_limit` and the identity assembly
`DA.chouekaLang_omega_power_eq_omega_limit` landed in `Choueka.lean` (commit `8ba346f8`), and
the final `IsRegular.omegaPow_da_muller` assembly landed in `OmegaRegularLanguage.lean` (commit
`29ba3eb2`). The proof follows the route below verbatim (steps 1-4 mechanical, step 5 the
Ramsey + `Nat.find`-based breakpoint search), plus two build fixes discovered along the way:
(a) `∗` (Kleene star postfix notation) is `scoped[Computability]` and required adding
`open scoped Computability` to `Choueka.lean` (previously only had `Cslib.FLTS`/`FinAcc`
scoped opens); (b) `kstar_mul_le_kstar`/`le_hmul_congr`-style `≤`-lemmas for `Language`/
`ωLanguage` do not unfold to a raw `Set.Subset` Pi-type at default transparency when applied as
functions with an unresolved implicit argument — fixed by supplying the implicit explicitly
(`kstar_mul_le_kstar (a := l)`) and by using `le_antisymm`/`⊆`-defeq (`ωLanguage`'s `⊆` is
literally `HasSubset.Subset := ⟨(· ≤ ·)⟩`, so `≤`- and `⊆`-stated facts interchange freely once
the implicit type/value is concrete). `Finite` of the assembled state space
(`State1 × (Fin (Nat.card State2 + 2) → Option State2)`) is discharged by `inferInstance`,
threading `Finite State1`/`Finite State2` from `Language.IsRegular.iff_dfa` and
`IsRegular.omegaLim_da_muller`'s existentials via explicit `haveI`. `OmegaRegularLanguage.lean`
required two new imports (`Cslib.Computability.Automata.DA.Choueka`,
`Cslib.Computability.Automata.DA.Concat`) to reach `DA.chouekaLang`/`DA.concat_language_eq`.
All three Phase-3 modules (`Choueka.lean`, `Concat.lean`, `MullerClosure.lean`,
`OmegaRegularLanguage.lean`) build green together; zero `sorry`/`admit`; `lean_verify` /
direct `#print axioms` report only `propext`, `Classical.choice`, `Quot.sound` for both new
theorems and for `IsRegular.omegaPow_da_muller`.

Exact target statement and proof route that was followed (mirrors `ctchou/AutomataTheory`'s
`choueka_lang_omega_power_subset_omega_limit`, cross-referenced against CSLib's own
`buchiCongr_DMA_accept_mem`/`buchiFamily_cover` Ramsey idiom in `OmegaRegularLanguage.lean`
and `BuchiCongruence.lean`, which already use `infinite_graph_ramsey` on a `Finset ℕ`-indexed
`min'`/`max'` coloring — the exact pattern used here):

```lean
theorem chouekaLang_omega_power_subset_omega_limit [Inhabited Symbol] [Finite State]
    (da : DA State Symbol) (acc : Set State) {l : Language Symbol}
    (h_lang : language (FinAcc.mk da acc) = l∗) :
    l^ω ⊆ l∗ * (chouekaLang da acc)↗ω
```

Proof route (steps 1-4 are mechanical/short; step 5 is the deep part):
1. `rw [omegaPow_seq_prop] ; rintro xs ⟨φ, h_φ_mono, h_φ_0, h_φ_l⟩` — destructure `xs ∈ l^ω`.
2. `h_kstar : ∀ i n, xs.extract (φ i) (φ (i + n)) ∈ l∗` by induction on `n`: base case
   `Language.nil_mem_kstar`; step case via `append_extract_extract` (already imported) +
   `KleeneAlgebra.kstar_mul_le_kstar l : l∗ * l ≤ l∗` (Mathlib, confirmed to exist) applied to
   `Language.mem_mul.mpr ⟨_, ih, _, h_φ_l (i+n), rfl⟩`.
3. `color i j := da.mtr da.start (xs.extract i j) : State` ; `h_color : ∀ i j, i < j →
   color (φ i) (φ j) ∈ acc` via `h_kstar i (j-i)` (rewrite `i+(j-i)=j`) then `rw [← h_lang]`
   (turns `∈ l∗` into `∈ language (FinAcc.mk da acc)`, defeq to `∈ acc` via `Acceptor.Accepts`).
4. Ramsey step: `colIdx (t : Finset ℕ) := if h : t.Nonempty then
   color (φ (t.min' h)) (φ (t.max' h)) else color (φ 0) (φ 0)` ; `infinite_graph_ramsey colIdx`
   gives `⟨b, ns, h_ns, h_colIdx⟩` ; `strictMono_of_infinite h_ns` gives `⟨σ, h_σ_mono, rfl⟩`
   (`range σ = ns`). Derive `hcol : ∀ i j, i < j → color (φ (σ i)) (φ (σ j)) = b` by **copying
   the `hcol` block of `buchiCongr_DMA_accept_mem`** (`OmegaRegularLanguage.lean:456-474`)
   verbatim, substituting `φ ∘ σ` for its `f` and `color` for its `⟦xs.extract · ·⟧` (same
   `Finset.card_pair`/`Finset.min'_pair`/`Finset.max'_pair`/`min_eq_left`/`max_eq_right` steps).
   Then `hb_acc : b ∈ acc` via `h_color (σ 0) (σ 1) (h_σ_mono (by omega))` rewritten by
   `hcol 0 1 (by omega)`.
5. **The hard part** — construct the witness `⟨xs.extract 0 (φ (σ 0)), _, xs.drop (φ (σ 0)), _, append_extract_drop⟩`:
   - First component `∈ l∗`: `h_kstar 0 (σ 0)` + `h_φ_0 : φ 0 = 0`.
   - Second component `∈ (chouekaLang da acc)↗ω`: via `frequently_iff_strictMono`, witness
     `g k := φ (σ (k+1)) - φ (σ 0)`, reducing (via `extract_drop`) to showing
     `xs.extract (φ (σ 0)) (φ (σ (k+1))) ∈ chouekaLang da acc` for each `k`. This needs an
     explicit breakpoint inside that window — port the reference's `Nat.find`-based
     construction (`ξ k' := Nat.find (h_p_ex k')`, where `p k' j := φ (σ k') < j ∧
     j ≤ φ (σ (k'+1)) ∧ da.mtr da.start (xs.extract (φ (σ k')) j) = da.mtr da.start
     (xs.extract (φ (σ 0)) j)`, witnessed at `j := φ (σ (k'+1))` via `hcol k' (k'+1)` and
     `hcol 0 (k'+1)` both `= b`) — this is
     `AutomataTheory/Languages/ChouekaLemma.lean:187-212` (cached at
     `/tmp/claude-1000/-home-benjamin-Projects-cslib-refactor-prop-logic/f23f339a-287d-446f-96b9-dad43b56c569/scratchpad/Languages_ChouekaLemma.lean`,
     lines 181-212) — transcribe using `da.mtr`/`List.take`/`List.drop` in place of `M.RunOn`/
     `extract`, following the same pattern as the `mtr_append`-based composition already used
     throughout `Choueka.lean`'s Milestone 1/2 proofs.
6. Once step 5 lands: `chouekaLang_omega_power_eq_omega_limit` (the full `=`, via
   `Subset.antisymm` + `kstar_omegaPow_eq_omegaPow`/`kstar_hmul_omegaPow_eq_omegaPow`, both
   **already in CSLib** at `OmegaLanguage.lean:443,449` — no new lemma needed here) is a
   ~10-line assembly.
7. Then `omegaPow_da_muller` in `OmegaRegularLanguage.lean`: given `l.IsRegular`, obtain
   `dfa : DA.FinAcc State Symbol` with `language dfa = l∗` via
   `Language.IsRegular.iff_dfa.mp (Language.IsRegular.kstar h)`; let
   `U := chouekaLang dfa.toDA dfa.accept` (regular via `chouekaLang_regular`); obtain a DMA for
   `U↗ω` via `IsRegular.omegaLim_da_muller` (already green); combine with the DFA for `l∗` via
   `DA.concat_language_eq` (Phase 2, already green) to get a DMA for
   `l∗ * U↗ω = l^ω` (via `chouekaLang_omega_power_eq_omega_limit`, step 6). `Finite` bookkeeping
   threads through `Language.IsRegular.iff_dfa`'s existential and `omegaLim_da_muller`'s.

**Timing:** 3 hours (original estimate for the whole phase); actual: Milestones 1-2 in the first
dispatch, Milestone 3 + final assembly in a second dispatch (comparable depth to Phase 2, as
anticipated).
- **Depends on:** 2
- **Files to modify:** `Cslib/Computability/Automata/DA/Choueka.lean` (Milestone 3);
  `Cslib/Computability/Languages/OmegaRegularLanguage.lean` (final `omegaPow_da_muller`, step 7).
- **Proof obligations:** `language (assembled DMA) = M^ω`; `Finite` of the state space. Both
  discharged — see Milestone 3/3 above.
- **Verification (all passed):** `lake build Cslib.Computability.Automata.DA.Choueka
  Cslib.Computability.Automata.DA.Concat Cslib.Computability.Automata.DA.MullerClosure
  Cslib.Computability.Languages.OmegaRegularLanguage` green together; zero `sorry`/`admit`;
  `lean_verify`/`#print axioms` on `chouekaLang_omega_power_subset_omega_limit`,
  `chouekaLang_omega_power_eq_omega_limit`, and `IsRegular.omegaPow_da_muller` all report only
  `propext`, `Classical.choice`, `Quot.sound`.

### Phase 4: DMA finite-union closure (`Muller.union`) [COMPLETED]

- **Goal:** DMAs are closed under (finite) union: `Muller.union` + `union_language_eq`, mirroring
  `DA.Buchi.union` over `DA.prod`.
- **Tasks:**
  - [x] Define `DA.Muller.union (a1 : Muller S1) (a2 : Muller S2) : Muller (S1 × S2)` with
    `toDA := a1.toDA.prod a2.toDA` and accept `{S | π₁''S ∈ a1.accept ∨ π₂''S ∈ a2.accept}`
    (or the `infOcc`-correct formulation; verify against `prod_run_eq`).
  - [x] Prove `language (a1.union a2) = language a1 ⊔ language a2` via `prod_run_eq` and `infOcc`
    of a product run (mirror `Buchi.union_language_eq`).
  - [x] Provide the finite `⨆ i, …` lift (fold over `Fin n`) used by Phase 5. *(implemented as
    `Muller.exists_iSup` / `Muller.exists_iSup_univ`, an existential-packaging lift mirroring
    `IsRegular.iSup`'s `ncard` induction, rather than a concrete "big union" automaton — this is
    the form Phase 5 actually needs to consume.)*
- **Timing:** 2 hours
- **Depends on:** none

**Phase 4 result (COMPLETED)**: New file `Cslib/Computability/Automata/DA/MullerClosure.lean`
(added to `Cslib.lean` via `lake exe mk_all --module`). Contains, all built green and sorry-free:
- `prod_run_infOcc_fst` / `prod_run_infOcc_snd`: the `infOcc`/image pigeonhole facts (via
  `ωSequence.frequently_in_finite_type`) connecting a product run's `infOcc` to each component's.
- `Muller.union` + `Muller.union_language_eq` (`language (a1.union a2) = language a1 ⊔ language a2`,
  requires `[Finite State1] [Finite State2]`).
- `Muller.empty` + `Muller.empty_language_eq` (one-state DMA with `accept = ∅`, language `⊥`;
  base case for the fold).
- `Muller.exists_iSup` / `Muller.exists_iSup_univ`: the finite-union lift, proved by `Set.ncard`
  induction exactly mirroring `IsRegular.iSup`.

Verified: `lake build Cslib.Computability.Automata.DA.MullerClosure` green; zero `sorry`/`admit`;
`lake lint` / `lake exe lint-style` / `lake shake` report nothing for this file.
Committed as `task 241 phase 4: DMA finite-union closure (Muller.union)`.

**Environment note**: at the time of this dispatch, an unrelated file
(`Cslib/Logics/Modal/Tableau/SoundnessStep.lean`, belonging to a different in-flight task) was in
a broken/mid-edit state in the shared working tree, which blocks `lake exe checkInitImports` and
a full `lake build`/`lake test` run (both require the whole project to build). This is outside
this task's scope and was not touched. `MullerClosure.lean`'s and `OmegaRegularLanguage.lean`'s
own scoped builds are green independent of that unrelated breakage.
- **Files to modify:** new `Cslib/Computability/Automata/DA/MullerClosure.lean` (sibling of
  `BuchiClosure.lean`); add to `mk_all` if new file.
- **Proof obligations:** `language (Muller.union …) = ⊔`; finite-union lift.
- **Verification:** `lake build` green; `lean_verify` clean.

### Phase 5: Forward assembly `IsRegular.to_da_muller` [COMPLETED]

- **Goal:** Assemble the forward direction `(⇒)`: every ω-regular `p` is DMA-recognizable.
- **Tasks:**
  - [x] `obtain ⟨n, l, m, hreg, rfl⟩ := (eq_fin_iSup_hmul_omegaPow p).mp hp` →
    `p = ⨆ i, (l i) * (m i)^ω`.
  - [x] For each `i`: `(m i)^ω` DMA-recognizable (Phase 3); `(l i) * (m i)^ω` DMA-recognizable via
    `concat_language_eq` (Phase 2) with regular `l i`.
  - [x] Fold the finite family into a single DMA via `Muller.union` (Phase 4).
    *(deviation: used `DA.Muller.exists_iSup_univ` directly — the existential-packaging finite-
    union lift built in Phase 4 — rather than manually folding `Muller.union`; this is the exact
    form Phase 4 designed for this consumer.)*
  - [x] Thread `Finite` / universe bookkeeping (`isRegular_iff`); conclude
    `∃ S (_ : Finite S) (da : DA.Muller S Symbol), language da = p`.
- **Timing:** 2 hours (actual: single dispatch, no blockers — all four dependency lemmas were
  already green and slotted together mechanically, mirroring `omegaPow_da_muller`'s own
  `concat_language_eq` usage pattern)
- **Depends on:** 2, 3, 4
- **Files to modify:** `Cslib/Computability/Languages/OmegaRegularLanguage.lean` —
  `IsRegular.to_da_muller` (forward lemma).
- **Proof obligations:** `language (assembled DMA) = p`.
- **Verification:** `lake build` green; `lean_verify` clean on `to_da_muller`.

**Phase 5 result (COMPLETED, committed)**: `IsRegular.to_da_muller` added to
`OmegaRegularLanguage.lean` (inserted between the dead `buchiCongr_DMA_language_forward` and the
`to_da_muller_scaffold`, both removed in Phase 6). Required adding one new import,
`Cslib.Computability.Automata.DA.MullerClosure` (for `DA.Muller.exists_iSup_univ`), to
`OmegaRegularLanguage.lean`'s import list. Proof: decompose via `eq_fin_iSup_hmul_omegaPow`;
`apply DA.Muller.exists_iSup_univ`; per-component `i`, obtain a DFA for `l i`
(`Language.IsRegular.iff_dfa`) and a DMA for `(m i)^ω` (`omegaPow_da_muller`); assemble via
`DA.concat`/`DA.mullerAccConcat` and `DA.concat_language_eq` (identical pattern to
`omegaPow_da_muller`'s own assembly at line 96-112). Scoped build
`lake build Cslib.Computability.Languages.OmegaRegularLanguage` green (only a pre-existing
`linter.style.show` warning inside the doomed `buchiCongr_DMA_accept_mem`, unrelated to this
edit and removed in Phase 6). Zero `sorry`/`admit` in the file.
`#print axioms Cslib.ωLanguage.IsRegular.to_da_muller` (via `lean_run_code`; `lean_verify`'s
theorem-name validator rejects the `ω` in the namespace) reports only `propext`,
`Classical.choice`, `Quot.sound`.

### Phase 6: Assemble `iff_da_muller`, delete dead cluster, full CI [COMPLETED]

- **Goal:** Replace the `proof_wanted` with the complete theorem, remove the dead `buchiCongr_DMA`
  cluster, and green the full pipeline.
- **Tasks:**
  - [x] Replace `proof_wanted IsRegular.iff_da_muller` (:653) with
    `theorem … := ⟨fun hp => IsRegular.to_da_muller hp, fun ⟨_,_,da,h⟩ => h ▸ IsRegular.of_da_muller da⟩`
    (exact binder shape per the original signature; namespace `Cslib.ωLanguage`).
    *(deviation: had to explicitly re-bind `{Symbol : Type}` on `iff_da_muller` — shadowing the
    file's ambient `variable {Symbol : Type*}` — because `IsRegular.of_da_muller`'s `Symbol` is
    fixed at `Type` (not universe-polymorphic); without this the `▸ IsRegular.of_da_muller da`
    branch fails with a universe mismatch. Mirrors the same explicit `{Symbol : Type}` rebinding
    already used by `IsRegular.compl`.)*
  - [x] Delete the dead cluster per the Disposition: `buchiCongr_DMA`, `buchiCongr_DMA_run_eq`,
    `buchiCongr_DMA_accept_mem`, `buchiCongr_DMA_language_forward`, `to_da_muller_scaffold`.
    Re-check `buchiFamily_component_isRegular`: keep if still referenced/independently useful, else
    delete. Confirm no dangling references.
    *(deviation: also deleted `buchiCongr_recurrentClass` — a `buchiCongr_DMA`-dependent private
    lemma omitted from the plan's Disposition table (an oversight there), which would otherwise
    dangle on the deleted `buchiCongr_DMA` def. `buchiFamily_component_isRegular` retained per
    the Disposition's default; it is now unreferenced anywhere in the file since its only
    consumer, `to_da_muller_scaffold`, was removed, but project-wide `lake lint`/`shake` — the
    stated trigger for removing it — could not be run this dispatch due to the known concurrent-
    task tree breakage (see Environment note below), so it is left in place per the
    conservative default.)*
  - [x] Update the corollary comment block (:658–664) if the "Once McNaughton's theorem is proved"
    phrasing should now read as proved. *(Changed "Once McNaughton's theorem is proved" to "Now
    that McNaughton's theorem is proved".)*
  - [x] Run the full CSLib CI pipeline (Testing & Validation) and fix lint/style/shake findings.
    *(deviation: whole-project `lake build`/`lake test`/`checkInitImports` are blocked by
    unrelated concurrent tasks' broken files, per the known environment issue — see Verification
    below for the scoped substitute actually run, including a `lake shake --force` scoped run
    that found and fixed one pre-existing unused import in `Concat.lean` (Phase 2's file,
    `Cslib.Computability.Automata.DA.Prod`, unused since Concat.lean never calls `DA.prod`).)*
- **Timing:** 1.5 hours (actual: single dispatch alongside Phase 5, no blockers)
- **Depends on:** 1, 5
- **Files to modify:** `Cslib/Computability/Languages/OmegaRegularLanguage.lean` (+ any file with
  lint/shake fixes).
- **Proof obligations:** `p.IsRegular ↔ ∃ State (_ : Finite State) (da : DA.Muller State Symbol), language da = p`.
- **Verification:** full pipeline green;
  `lean_verify Cslib.ωLanguage.IsRegular.iff_da_muller` — zero `sorry`, zero new axioms;
  `grep -n "sorry\|admit\|buchiCongr_DMA" …/OmegaRegularLanguage.lean` returns nothing.

**Phase 6 result (COMPLETED, committed)**: `IsRegular.iff_da_muller` is now a complete, sorry-free
`theorem` (McNaughton's theorem). The dead `buchiCongr_DMA` cluster (def, `run_eq`,
`recurrentClass`, `accept_mem`, `language_forward`) and `to_da_muller_scaffold` were deleted
(182 lines removed net). `buchiFamily_component_isRegular` retained per Disposition default.

**Verification actually run** (scoped, due to the documented environment issue — see below):
- `lake build Cslib.Computability.Automata.DA.Choueka Cslib.Computability.Automata.DA.Concat
  Cslib.Computability.Automata.DA.MullerClosure Cslib.Computability.Languages.OmegaRegularLanguage`
  — green, zero warnings.
- `lake exe lint-style` on the same four modules — no findings.
- `lake shake --add-public --keep-implied --keep-prefix --force` on the same four modules —
  found and fixed one unused import (`Concat.lean`'s `DA.Prod` import); re-run confirms clean.
- `lake exe mk_all --module` — "No update necessary"; `git diff --stat Cslib.lean` empty.
- `grep -n "sorry\|admit"` across all four touched files — no matches.
- `grep -n "^axiom "` across all four touched files — no matches (no new axioms introduced).
- `#print axioms Cslib.ωLanguage.IsRegular.iff_da_muller` (via `lean_run_code`, since
  `lean_verify`'s theorem-name validator rejects the `ω` in the namespace) — only `propext`,
  `Classical.choice`, `Quot.sound`.
- `lake exe checkInitImports` — attempted; fails with `object file
  .../Cslib/Logics/Temporal/Tableau/Completeness.olean does not exist`, an unrelated concurrent
  task's broken file (tasks 180/442), not touched by this dispatch. No mention of any of the
  four files this dispatch modified.

**Deferred to the orchestrator**: whole-project `lake build`, `lake test`,
`lake exe checkInitImports`, project-wide `lake lint`, and project-wide `lake shake` could not be
run this dispatch because the shared working tree currently has unrelated, concurrently-edited
files in a broken/mid-edit state (`Cslib/Logics/Modal/Tableau/*`, `Cslib/Logics/Temporal/*`,
belonging to tasks 180 and 442 — not owned by task 241 and not touched by this dispatch). Once
those trees are fixed, run the full CSLib CI pipeline for a final whole-project confirmation.

## New Supporting Lemmas Flagged (directive #4)

These do not yet exist in CSLib and are built by this plan:

1. **`concat_language_eq`** (Phase 2, `DA/Concat.lean`) — top-level correctness of the
   `DA.concat` flag construction. **DONE (green, sorry-free).** Required fixing a genuine
   empty-prefix bug in `concat`/`concatF2` itself (see Phase 2 completion note) in addition to
   the correctness theorem.
2. **`omegaPow_da_muller`** (Phase 3, `OmegaRegularLanguage.lean`) — `M^ω` DMA-recognizable, the
   omega-iteration core. **DONE (green, sorry-free).** Required the new Choueka identity
   sub-lemma `M^ω = M* · U↗ᵒᵐᵉᵍᵃ` (`DA.chouekaLang_omega_power_eq_omega_limit`, regular `U` via
   `DA.chouekaLang_regular`), built entirely in the new `Cslib/Computability/Automata/DA/Choueka.lean`.
3. **`DA.Muller.union` + `union_language_eq`** (Phase 4, new `DA/MullerClosure.lean`) — DMA finite-
   union closure (only DBA `Buchi.union` exists today).
4. **`IsRegular.to_da_muller`** (Phase 5) — forward assembly lemma.

Already present (no new work, reused): `IsRegular.of_da_muller`, `IsRegular.omegaLim_da_muller`,
`IsRegular.regular_omegaLim`, `IsRegular.eq_fin_iSup_hmul_omegaPow`, `DA.concat`/`mullerAccConcat`
(construction), `DA.Buchi.toMuller(_language_eq)`, `DA.Rabin.toMuller_language_eq`,
`DA.buchi_eq_finAcc_omegaLim`, `DA.prod`/`prod_run_eq`.

## Testing & Validation

Run in CSLib CI order (per cslib.md):
- [ ] `lake exe cache get` (once per branch)
- [ ] `lake build` (full project)
- [ ] `lake exe checkInitImports` (all touched files import `Cslib.Init`)
- [ ] `lake lint` (docBlame on new public lemmas)
- [ ] `lake exe lint-style`
- [ ] `lake test` (CslibTests suite)
- [ ] `lake exe mk_all --module` (if `DA/MullerClosure.lean` is added)
- [ ] `lake shake --add-public --keep-implied --keep-prefix`
- [ ] `lean_verify Cslib.ωLanguage.IsRegular.iff_da_muller` — zero `sorry`, zero new axioms
- [ ] `grep -n "sorry\|admit\|proof_wanted IsRegular.iff_da_muller\|buchiCongr_DMA" Cslib/Computability/Languages/OmegaRegularLanguage.lean` returns nothing

## Artifacts & Outputs

- `specs/241_mcnaughton_theorem/plans/02_mcnaughton-choueka-route.md` (this plan)
- `specs/241_mcnaughton_theorem/summaries/02_mcnaughton-choueka-route-summary.md` (on completion)
- Modified: `Cslib/Computability/Automata/DA/Concat.lean` (concat_language_eq)
- Added: `Cslib/Computability/Automata/DA/MullerClosure.lean` (Muller.union)
- Modified: `Cslib/Computability/Languages/OmegaRegularLanguage.lean`
  (omegaPow_da_muller, to_da_muller, iff_da_muller theorem; deletion of the buchiCongr_DMA cluster
  and the subtask-434 `sorry`)

## Rollback/Contingency

- Each phase commits at a green boundary (`task 241 phase N: …`); a later failure never loses an
  earlier green milestone. Phase 1's deletions restore a sorry-free build immediately and are
  independently committable.
- The dead-cluster removal (Phase 6) is gated on the Choueka forward direction (Phase 5) being
  green, so a working replacement exists before old code is deleted. To revert any single phase:
  `git checkout -- <touched file>`.
- If a Choueka sub-goal (Phase 2 or 3) cannot close without new mathematics: keep all prior green
  phases committed, mark the affected phase **[BLOCKED]** with the recorded `lean_goal` state and
  attempts, transition the task to **[BLOCKED]**, and coordinate with Chou (the file author; the
  reference proof exists in `AutomataTheory/Languages/DetMullerLang.lean`). Do **not** commit
  `sorry` or axioms. Unlike the abandoned quotient path, this route has a verified reference proof,
  so a genuine new-mathematics block is unlikely.
