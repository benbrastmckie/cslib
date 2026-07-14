# Implementation Plan: Task #510 — Generalize the Completeness/Hintikka Chain over RuleApplicationSpec

- **Task**: 510 - `generalize_completeness_loop_hintikka_chain_over_spec`
- **Status**: [NOT STARTED]
- **Effort**: 18 hours
- **Dependencies**: None to start (builds on task 503's committed `Saturation.lean` generic driver
  + `GenericDriver.lean` spec bundle, and task 507's committed 7-field
  `RuleApplicationSpec` + generic step lemmas, commit `009cc348`). **Blocks**: task 503 Phase 5
  (needs `modalExpandBranchesT_hintikka`), task 505 (B), task 506 Phase 9 (needs
  `modalHintikkaSetGen`'s statement shape).
- **Research Inputs**: specs/510_generalize_completeness_loop_hintikka_chain_over_spec/reports/01_generalize-hintikka-chain-over-spec.md
- **Artifacts**: plans/01_generalize-hintikka-chain-over-spec.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md;
  cslib.md; CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Generalize the Hintikka-set / saturation-characterisation chain (`Completeness.lean:665-935` +
`CompletenessLoop.lean:57-746`, ~850 lines) over an abstract `apply : RuleApply Atom` mediated by
`RuleApplicationSpec`, so that T (task 503), B (505), and S5 (504) each instantiate ONE generic
development rather than re-deriving an ~850-line system-specific analogue apiece. The interface
grows from 7 to 11 fields; the four new shape-class fields (F9-F12) plus the branch-independence
field (F8) are the entire content of the abstraction. Definition of done: `modalExpandBranchesGen_hintikka`
holds for an abstract `(apply, spec)` and **concludes in `modalHintikkaSetGen apply bR aR`**; K's
public surface (`kValid`, `modalTableau_decides`, `instDecidableKValid`) is byte-identical; T's
`modalExpandBranchesT_hintikka` — the exact lemma task 503 Phase 5 is blocked on — is delivered as a
one-liner; everything is genuinely sorry-free and axiom-free at every phase boundary.

The chain abstracts because every rule-dependent step turns on a three-way **shape classification**
(Structural / Minting / Propagating) that K, T, B, and S5 share exactly — and the chain never reads a
Propagating *payload*, it only uses class membership to derive a contradiction. That is what makes
the interface blind to T's appended self-conjunct.

### Research Integration

Adopted directly from `reports/01_generalize-hintikka-chain-over-spec.md`, whose findings were
derived from what the proofs actually *consume* rather than from the docstrings. That discipline is
preserved here: every phase below names the specific field each rule-specific step is discharged
from.

- **Interface**: `RuleApplicationSpec` grows 7 → 11 (F8 `localShapeInvariance`, F9 `boxPosNotExpanding`,
  F10 `diaNegNotExpanding`, F11 `boxNegWitness`, F12 `diaPosWitness`). Exact Lean statements are in
  report §3 and are to be used verbatim.
- **The stated task hypothesis is superseded.** The original description proposed "abstract saturation
  predicate + `noneIffSaturated` + Hintikka-lift hook". Per report §2, the abstract saturation predicate
  is a **definition** (one-token substitution, no field); `noneIffSaturated` is a **free rule-agnostic
  lemma** (no field, and only the `none → saturated` direction is ever used); and the lift hook is
  **branch-independence (F8)**, not saturation-implies-clause. **Follow the research, not the task
  description.**
- **Not anticipated by the hypothesis**: F9-F12, which are the actual content.
- **A candidate field that is NOT needed**: `modalApplyOne_hasEdge_mono` (Loop:451) is derivable from
  the existing `freshLocal` + `hasEdge_addEdge_mono`. `modalLoop_snd_eq_or_addEdge` (Loop:432) is
  verbatim `freshLocal` and is **deleted**. Field count lands at 11, not 12.
- **Scope seam**: `hintikka_box_pos` (Comp:146) and `hintikka_diamond_neg` (Comp:230) unfold
  `modalApplyOne` and read the Propagating payload — they are **irreducibly per-system and OUT of
  scope**. They are the exact complement of the `∃ out` weakening: the chain never reads the payload
  (so it abstracts), the truth-lemma bridges do nothing but read it (so they cannot). 505/506 must
  budget their own; do not attempt them here. The two *projection* bridges (`hintikka_box_neg`,
  `hintikka_diamond_pos`) generalize for free and are delivered in Phase 3.
- **507 reuse**: `modalStepBranchGen_potential_step` / `_worldBound` / `_preserves_accTargetsKnown` /
  `_preserves_outDegEq` / `_eClosure` / `_expMeasure_step_lt` are already bundled and cover the entire
  non-Hintikka half of `ModalLoopInv`. The one gap is `modalStepBranch_preserves_accFreshInv`
  (Soundness:113), closed in Phase 4.

### Verification Performed During Planning

Every load-bearing claim below was re-checked against source before being encoded as a criterion:

- **Import topology CONFIRMED**: `FmpMeasure.lean:17` imports `Completeness`, and
  `GenericDriver.lean:10` imports `FmpMeasure` — so `Completeness.lean` is strictly upstream of the
  spec and must take raw hypotheses. `CompletenessLoop.lean` is imported **only** by the `Cslib.lean`
  barrel (line 464) — confirmed leaf, so it may import `GenericDriver` and take a bundled `spec`.
- **The `∃ out` design decision is CORROBORATED BY EXISTING SOURCE.** `TDriver.lean:96` already
  carries `modalApplyOne_boxPos_shape` stated in exactly the `∃ kForms, … = .persistent kForms` form,
  with the docstring: *"restated here with an opaque `kForms` witness since the T spec-discharge below
  never needs the concrete `boxPropagation` shape, only this dichotomy."* A prior implementer
  independently reached the research's conclusion **because T's discharge forced it**. F9/F10 are that
  statement, promoted to the interface. The proof delta from the concrete form is one tactic token
  (`right; rfl` → `right; exact ⟨_, rfl⟩`).
- **Relocation necessity CONFIRMED**: `modalApplyOne_posBox_eq` (Loop:248), `_negDia_eq` (:274),
  `_boxNeg_witness` (:464), `_diamondPos_witness` (:566) are all `private` in `CompletenessLoop.lean`,
  downstream of `GenericDriver.lean:223`'s `modalApplyOne_spec`. Relocation to `Rules.lean` (159 lines,
  holds `def modalApplyOne` at :70) is required, and reaches both spec witnesses.
- **Crux re-derivation CONFIRMED**: `modalExpandBranchesGen` (Sat:197) and `modalExpandBranches`
  (Sat:259) are separate defs, each with its own `processNext` well-founded helper. The Phase 7 proof
  must be re-derived against `modalExpandBranchesGen.processNext`, not reused.
- **`FrameCompleteness.lean` also imports `Completeness.lean`** (not noted in the research) but
  references **none** of `modalHintikkaSet`/`modalHintikkaClause`/`modalStepBranch`/`modalApplyOne` —
  verified by grep. No regression surface; noted so Phase 8 need not investigate it.

**Sequencing correction to the research's phase plan (IMPORTANT).** Report §8 puts the F8-F12 field
addition in P2 and T's discharges in an optional P9. That ordering **cannot produce a green build**.
There are exactly **two** `RuleApplicationSpec` instances in the tree — `modalApplyOne_spec`
(GenericDriver:223) and `modalApplyOneT_spec` (TDriver:759) — and adding fields to a `structure`
breaks *every* instance immediately. Phase 2 below therefore discharges F8-F12 for **both**
`modalApplyOne` **and** `modalApplyOneT` in the same phase. This is not extra work, only re-sequenced:
per report §9 T's discharges are mechanical, and the TDriver helpers they need
(`modalApplyOneT_boxPos_fst` :214, `modalApplyOneT_diamondNeg_fst` :249,
`modalApplyOneT_eq_of_not_boxPos_diaNeg`) already exist. It makes the final T phase a genuine
one-liner.

### Prior Plan Reference

`specs/507_.../plans/01_generalize-fmp-termination-measure.md` (task 507, [COMPLETED], commit
`009cc348`) is reference-only; no phases are copied. Learned from it:

1. **Proven phase shape**: front-load the field extension; allow incremental field refinement in later
   phases (each re-discharged and kept green); isolate the crux in its own phase with an explicit
   `[BLOCKED]` fallback; end with a dedicated verification phase. Adopted.
2. **Effort calibration**: 507's 8 phases at ~14 hours delivered a comparable ~900-line
   re-derivation. 510's surface is ~850 lines but structurally easier (leaf module + bundled spec +
   4 of 5 conjuncts have rule-agnostic statements), against which the crux is harder. 18 hours.
3. **Field-set provisionality is real and expected**: 507's Phase 7 discovered a genuinely new needed
   field (`branchingLength`) at the *last* implementation phase and added it green. Phases 3-7 here
   may likewise add fields; each addition must re-discharge for **both** K and T in the same phase.
4. **The raw-hypothesis / bundled-wrapper pattern** (507's "Architectural Note"): a `_gen` lemma
   upstream of `GenericDriver.lean` takes the raw per-field hypothesis; `GenericDriver.lean` supplies
   a thin `spec`-bundled wrapper. Applies here to `Completeness.lean` and `Soundness.lean` only —
   `CompletenessLoop.lean` is a leaf and takes `spec` directly (strictly better than 507 achieved).
5. **`never sorry; mark [BLOCKED] with documented goal state`** discipline preserved verbatim.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md was consulted or modified.
Task 510 is the sole unblock for task 503 Phase 5, a prerequisite for 505 (B) and 504 (S5), and gates
506 Phase 9 at the statement level.

## Goals & Non-Goals

**Goals**:
- Extend `RuleApplicationSpec` 7 → 11 with F8-F12 per report §3 **verbatim**, discharged sorry-free for
  both `modalApplyOne` (K) and `modalApplyOneT` (T).
- `modalHintikkaSetGen apply` in `Saturation.lean` (spec-free, upstream — consumable by S4) +
  `modalHintikkaSet_eq` by `rfl`.
- `modalHintikkaClauseGen apply` + `_eq` by `rfl`; both originals retained.
- Generic chain over `(apply, spec)`: `modalHintikkaClauseGen_lift`, `modalStepBranchGen_none_saturated`,
  `modalStepBranchGen_hintikka_inv`, `ModalLoopInvGen`, the four witness-invariant helpers,
  `modalStepGen_preserves_invariant`, and `modalExpandBranchesGen_hintikka`.
- `modalExpandBranchesT_hintikka` delivered — unblocking task 503 Phase 5.
- The two free projection bridges `hintikka_box_neg_gen` / `hintikka_diamond_pos_gen` for 505/506.
- Zero regression: `kValid` / `modalTableau_decides` / `instDecidableKValid` **untouched**;
  `ModalLoopInv` byte-identical via the keep-both-plus-`Iff` bridge.
- Full CSLib CI green at every phase boundary; zero sorry, zero axiom throughout.

**Non-Goals**:
- `hintikka_box_pos` / `hintikka_diamond_neg` analogues for any system (payload-reading, per-system;
  T's belongs to 503 Phase 5's already-scoped remainder; 505/506 budget their own).
- Any S4 work. S4 discharges no spec (`GenericDriver.lean:105-108`) and is out of scope; 510 offers it
  the **statement shape only**, via the spec-free `modalHintikkaSetGen`.
- B / S5 / S4 instantiation (tasks 505 / 504 / 506); T's truth lemma and `Decidable (tValid φ)` (503).
- New files. Extend the six existing files (report §5: new files buy nothing and add barrel churn).
- Any change to K's observable behavior or public theorem statements.
- Any `sorry`, `axiom`, or vacuous `def X := True` / `trivial` placeholder to "close" a phase.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **F9/F10 stated with K's concrete `boxPropagation` payload** to match `modalApplyOne_posBox_eq` verbatim — T/B/S5 discharge becomes IMPOSSIBLE and the task silently regresses to a K-only refactor that lands green | **H** | **M** | The single most important correctness constraint in this task. Encoded as a blocking acceptance criterion in Phase 2 with the wrong-form shown explicitly. `TDriver.lean:96`'s existing `∃ kForms` form is the reference. Phase 2 cannot close until T's F9/F10 discharge typechecks — which is itself the proof the weakening is right. |
| **Crux (P7) concludes in concrete `modalHintikkaSet`** — 510 lands green, CI passes, and 503/505/506 STAY BLOCKED (total mission failure despite green CI) | **H** | **M** | Blocking acceptance criterion in Phase 7, restated in Phase 8's verification and in Phase 9's one-liner (which cannot typecheck if P7 concluded concretely — a structural check, not a review check). |
| **P7 volume**: `modalExpandBranches_hintikka` is ~305 lines of triple-nested induction that must be re-derived against `modalExpandBranchesGen.processNext` (separate def — no reuse) | **H** | **M** | The only plausible `[BLOCKED]` site. Pre-authorized 7a/7b split. Pure substitution port except the saturated-leaf discharge (Loop:849-928), which report §4 maps exactly onto F9-F12. Explicit `[BLOCKED]` fallback with required goal-state documentation. |
| Adding F8-F12 to the structure breaks `modalApplyOneT_spec` mid-phase (red build) | M | **H** (certain if unsequenced) | Already resolved: Phase 2 discharges both instances in the same phase. Enumerated exhaustively — there are exactly two. |
| Field set proves insufficient once P6/P7 attempt the real obligations | H | M | Expected, per 507's precedent (`branchingLength` surfaced at its last phase). Phases 3-7 may add fields; each re-discharges for **both** K and T in-phase and stays green. Never weaken a spec witness with `sorry`. |
| `ModalLoopInv` bridging: the 7-field anonymous destructure (Loop:683) and 7-field `refine ⟨…⟩` (Loop:1228) | M | M | Keep-both-plus-`Iff` (report §7 option 1). Do **not** take the `abbrev` shortcut — it changes the declaration kind and risks both elaboration sites. |
| `Rules.lean` relocation surfaces `shake`/`dupNamespace`/`topNamespace` findings (file currently holds a single `def`) | L | M | Contained to Phase 1; full CI at phase end. |
| **Concurrent sessions in this repo** clobber or entangle changes | M | **H** | Every phase scopes `git add` to its named files only — never `git add -A`/`git add .`. Commit at each green milestone. Never revert or restage another session's files (507 Phase 8 hit exactly this with `mk_all --module` wanting to reorder concurrent `Cslib.lean` imports — leave them alone). |
| Context exhaustion mid-phase (esp. P7) | M | M | Each phase ends at a green committed milestone; write an 80%-context handoff at a green intermediate lemma. |
| Lint (docBlame/defLemma/simpNF/unusedSectionVars) on new decls | L | M | Docstring every new decl; Prop-valued results as `lemma`/`theorem`; full CI each phase end. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 4 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 5 | 3 |
| 5 | 6 | 5 |
| 6 | 7 | 4, 6 |
| 7 | 8 | 7 |
| 8 | 9 | 8 |

Phases within the same wave can execute in parallel. Phases 1 and 4 are genuinely independent:
Phase 4 consumes only the **existing** `freshLocal` field via a raw hypothesis and touches only
`Soundness.lean`, which is disjoint from Phase 1's territory (`Rules.lean`, `Completeness.lean`,
`CompletenessLoop.lean`). If running them in parallel, hold the file territories strictly. Everything
else is intrinsically sequential: the fields (P2) must exist before any consumer; the
`Completeness.lean` layer (P3) is the input to the `CompletenessLoop.lean` layer (P5); the four
witness-invariant helpers (P6) are the direct inputs to the crux (P7), which also needs P4's
accFreshInv gap closed; K re-instantiation (P8) needs all generics; T (P9) needs P8.

Every phase ends at a green `lake build` + full CSLib CI + a narrowly-scoped commit.

---

### Phase 1: Relocate K shape/witness lemmas to Rules.lean with payload weakening [COMPLETED]

- **Goal:** Make the four K shape/witness facts reachable from `modalApplyOne_spec`
  (`GenericDriver.lean:223`) by relocating them upstream to `Rules.lean`, stating the two Propagating
  ones in the `∃ out`-weakened form F9/F10 will require. De-privatize F8's K discharge. Pure
  relocation — zero proof-content change beyond the one-token payload weakening.
- **Tasks:**
  - [ ] Relocate to `Rules.lean` (public, docstringed), keeping the `(sf, hsign, ψ, hform, b, acc)`
    parameter shape that `CompletenessLoop.lean`'s call sites need (the `sf`-with-projections form —
    see the rationale docstring at Loop:246-248; do **not** switch to TDriver's concrete-constructor
    shape):
    - `modalApplyOne_boxPos_eq` — from `CompletenessLoop.lean:248` (`modalApplyOne_posBox_eq`),
      **payload weakened** to `∨ ∃ out, (modalApplyOne sf b acc).1 = .persistent out`.
    - `modalApplyOne_diamondNeg_eq` — from `:274` (`modalApplyOne_negDia_eq`), likewise weakened.
    - `modalApplyOne_boxNeg_witness` — from `:464`, statement unchanged.
    - `modalApplyOne_diamondPos_witness` — from `:566`, statement unchanged.
  - [ ] Weakening mechanics: the existing proofs end `· right; rfl`; the weakened form ends
    `· right; exact ⟨_, rfl⟩`. `TDriver.lean:96-135` already carries both weakened proofs verbatim
    (`modalApplyOne_boxPos_shape` / `modalApplyOne_diamondNeg_shape`) — reuse those bodies.
  - [ ] Delete the four `CompletenessLoop.lean` privates; rewire their call sites (`:331`, `:349`,
    `:392`, `:410`, `:514`, and the `_witness` uses) to the relocated public lemmas. The `∃ out` form
    is drop-in at every site: each discards `out` and only contradicts the `.linear`/`.branching`
    split (`rcases … with h | h <;> rw [h] at hfstc <;> simp at hfstc` becomes
    `rcases … with h | ⟨_, h⟩ <;> rw [h] at hfstc <;> simp at hfstc`).
  - [ ] Drop `TDriver.lean`'s four now-redundant privates (`modalApplyOne_boxPos_shape` :96,
    `_diamondNeg_shape` :118, `_boxPos_acc_eq` :140, `_diamondNeg_acc_eq` :153), rewiring their uses to
    the canonical `Rules.lean` versions. (`_boxPos_acc_eq`/`_diamondNeg_acc_eq` are derived facts —
    relocate them too if still needed, or re-derive locally from the canonical shape lemmas.)
  - [ ] De-privatize `modalApplyOne_fst_eq_of_not_box` (`Completeness.lean:684`) and docstring it —
    this is F8's K discharge, already upstream of `GenericDriver.lean`; no relocation needed.
  - [x] `lake build` + full CI; `#print axioms` on each relocated lemma. *(deviation: the four
    relocated shape/witness lemmas' proofs call `tryAllPropRules_pos`/`tryAllPropRules_neg`, which
    were previously defined in `Completeness.lean` -- downstream of `Rules.lean` in the import
    chain. Discovered only when building `Rules.lean` after the initial relocation. Both lemmas
    are entirely generic (`{F L : Type*}`, no `Atom`-specific content), so they were additionally
    relocated to `Rules.lean` (ahead of the four shape/witness lemmas); `Completeness.lean` retains
    access transitively via `Completeness → Saturation → Rules`. This is a pure relocation with
    zero proof-content change, consistent with the phase's stated scope.)*
- **Timing:** 2 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/Rules.lean` — four relocated public lemmas (two payload-weakened).
  - `Cslib/Logics/Modal/Tableau/Completeness.lean` — de-privatize F8's K discharge.
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — delete four privates; rewire call sites.
  - `Cslib/Logics/Modal/Tableau/TDriver.lean` — drop four redundant privates; rewire.
- **Verification:**
  - `lake build` green; zero sorry/axiom; full CI (`checkInitImports`, `lake lint`, `lint-style`,
    `lake test`, `shake --add-public --keep-implied --keep-prefix`).
  - No behavior change: this phase is a pure move + one-token weakening.
- **Commit:** `task 510 phase 1: relocate K shape/witness lemmas to Rules.lean` (scope `git add` to the
  four named files only).

---

### Phase 2: Extend RuleApplicationSpec to 11 fields; modalHintikkaSetGen [COMPLETED]

- **Goal:** Add `modalHintikkaSetGen` (spec-free, `Saturation.lean`) and the five new spec fields
  F8-F12, discharged for **both** `modalApplyOne` and `modalApplyOneT`. This phase carries the task's
  single most important correctness constraint.
- **Tasks:**
  - [ ] `Saturation.lean`, beside `modalHintikkaSet` (:423): add `modalHintikkaSetGen (apply : RuleApply Atom)`
    — report §3's body **verbatim**. It is a one-token substitution (`modalApplyOne` → `apply` in
    conjunct 2's `let (result, _) := …`); conjuncts 1/3/4 mention no rule function. Add
    `theorem modalHintikkaSet_eq … := rfl`. **Retain** `modalHintikkaSet` unchanged (six `unfold`/
    `simp only` sites depend on its normal form; mirrors the deliberate `modalStepBranch`/`_Gen`+`_eq`
    precedent at Sat:140-178).
  - [ ] `GenericDriver.lean`: append F8-F12 to `structure RuleApplicationSpec` (:126) using report §3's
    Lean **verbatim**, including the docstrings recording each field's provenance and forcing lemma.
    All five are statable without new imports.
  - [ ] **ACCEPTANCE CRITERION (blocking).** F9 `boxPosNotExpanding` and F10 `diaNegNotExpanding` MUST
    be stated with an existentially-quantified payload:
    ```lean
    (apply sf b acc).1 = .notApplicable ∨ ∃ out, (apply sf b acc).1 = .persistent out
    ```
    They MUST NOT name a concrete payload. The following is **WRONG** and silently regresses this task
    to a K-only refactor that still lands green:
    ```lean
    -- WRONG. T's payload is `kForms ++ selfNew.filter …`, not this. T/B/S5 cannot discharge it.
    ∨ (apply sf b acc).1 = .persistent (boxPropagation b acc ψ sf.label)
    ```
    Every use site discards `out` — it serves only to contradict the `.linear`/`.branching` case split
    (Loop:331, 349, 392, 410). The existential is exactly what absorbs T's self-conjunct, B's symmetric
    propagation, and S5's universal propagation. `TDriver.lean:96`'s pre-existing `∃ kForms` form is the
    reference. **The T discharge below is the proof this is right — if F9/F10 were concrete, it could
    not typecheck.**
  - [ ] Extend `modalApplyOne_spec` (:223) with the five K discharges: F8 ←
    `modalApplyOne_fst_eq_of_not_box` (de-privatized in P1); F9/F10/F11/F12 ← the four `Rules.lean`
    lemmas relocated in P1.
  - [ ] **Extend `modalApplyOneT_spec` (`TDriver.lean:759`) with the five T discharges — MANDATORY in
    this phase.** Adding fields to the structure breaks this instance immediately; there is no green
    build without it. There are exactly two instances in the tree (verified) — this and
    `modalApplyOne_spec`. Per report §9, each is mechanical:
    - F8 ← `modalApplyOneT_eq_of_not_boxPos_diaNeg` + K's `modalApplyOne_fst_eq_of_not_box`
      (non-box/non-diamond φ falls into `modalApplyOneT`'s `| _, _ => (kResult, kAcc)` arm).
    - F9 ← `modalApplyOneT_boxPos_fst` (TDriver:214) + K's `modalApplyOne_boxPos_eq`
      (T maps `.persistent ↦ .persistent`, `.notApplicable ↦ .notApplicable | .persistent selfNew` —
      **stays in the Propagating class**, different payload).
    - F10 ← `modalApplyOneT_diamondNeg_fst` (TDriver:249) + K's `modalApplyOne_diamondNeg_eq`.
    - F11 ← K's `modalApplyOne_boxNeg_witness` **directly** (`⟨.neg, .box ψ, w⟩` has sign `.neg`, so it
      misses T's `.pos, .box` arm → `_, _` arm → `= modalApplyOne`).
    - F12 ← K's `modalApplyOne_diamondPos_witness` **directly** (misses T's `.neg, .diamond` arm).
  - [ ] Update `GenericDriver.lean`'s module docstring: field count 7 → 11; provenance entry per new
    field; preserve the S4-exclusion note (:105-108) unchanged.
  - [x] `lake build` + full CI; `#print axioms` on `modalApplyOne_spec` and `modalApplyOneT_spec` — both
    sorry-free. *(deviation: discovered `FmpMeasure.lean:17`'s `import Cslib.Logics.Modal.Tableau.
    Completeness` was non-`public`, so `GenericDriver.lean` could not reach the de-privatized
    `modalApplyOne_fst_eq_of_not_box` (F8's K discharge) transitively despite Completeness.lean
    being file-order upstream. Fixed by flipping that one import to `public import` -- a pure
    visibility change, zero content change. `lake test`'s overall exit code was flaky due to a
    concurrent-session build race on `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (task 506's
    untracked WIP file, not touched by this task); `lake build` (full project, 3233/3233) and
    targeted module builds for every phase-2 file are green and sorry/axiom-free.)*
- **Timing:** 3 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/Saturation.lean` — `modalHintikkaSetGen` + `modalHintikkaSet_eq`.
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — F8-F12; `modalApplyOne_spec`; module docstring.
  - `Cslib/Logics/Modal/Tableau/TDriver.lean` — `modalApplyOneT_spec` five new discharges.
- **Verification:**
  - `lake build` green; **both** spec witnesses typecheck sorry-free with 11 fields.
  - `modalHintikkaSet_eq` closes by `rfl` (confirms the substitution is faithful).
  - F9/F10 use `∃ out` — verify by reading the committed statements, not by intent.
  - Full CI clean.
- **Commit:** `task 510 phase 2: extend RuleApplicationSpec to 11 fields; add modalHintikkaSetGen`.

---

### Phase 3: Completeness.lean layer — clause lift, saturation, hintikka_inv (raw F8) [COMPLETED]

- **Goal:** Generalize the `Completeness.lean` half of the chain. `Completeness.lean` is **upstream** of
  `GenericDriver.lean` (via `FmpMeasure.lean:17`), so its `_gen` lemmas take **raw unbundled
  hypotheses** — 507's pattern. Mitigating factor: they need only **one** raw parameter (F8).
  `GenericDriver.lean` supplies the bundled wrappers.
- **Tasks:**
  - [ ] `modalHintikkaClauseGen (apply) s φ w X Y` beside `modalHintikkaClause` (:665) — report §3
    verbatim; `modalHintikkaClause_eq … := rfl`. **Retain** the original (six unfold sites rely on its
    normal form). Note the clause carve-out is deliberately **coarser** than the set's: vacuous for
    *any* box/diamond-shaped φ (both signs), whereas `modalHintikkaSetGen` conjunct 2 carves out only
    `.neg,.box` / `.pos,.diamond`. That gap is exactly what F9/F10 exist to close, and the coarseness is
    forced (the clause must lift along branch growth; both Propagating shapes are `b`/`acc`-dependent).
  - [ ] `modalHintikkaClauseGen_lift` (from `modalHintikkaClause_lift` :718) taking a raw
    `hLocalShapeInvariance` parameter (textually F8's field type). F8 is its **only** input; the body is
    5 identical case blocks + 2 `trivial`.
  - [ ] `modalStepBranchGen_none_saturated` (from `modalStepBranch_none_saturated` :784) — takes **no**
    field. Verified rule-agnostic: `simp only [modalStepBranch]`, `List.findSome?_eq_none_iff`, `rcases`
    on the `RuleResult` constructor; touches `apply` only opaquely. Only the `none → saturated`
    direction is used — do not build the `iff`.
  - [ ] `modalStepBranchGen_hintikka_inv` (from `:822`) — raw F8, via `_lift` + F8 directly; the rest is
    driver case-split.
  - [ ] Free projection bridges for 505/506 (~6 lines each, no field): `hintikka_box_neg_gen` (from
    `:198`, `hH.2.2.1 ψ w hmem` — pure projection of conjunct 3) and `hintikka_diamond_pos_gen` (from
    `:211`, conjunct 4). **Do NOT attempt** `hintikka_box_pos` (:146) or `hintikka_diamond_neg` (:230) —
    they unfold `modalApplyOne` and read the Propagating payload; irreducibly per-system, out of scope.
  - [ ] Re-derive each K original as a byte-identical-statement one-line corollary via `_eq`.
  - [x] Bundled `spec`-taking wrappers in `GenericDriver.lean` for each new `_gen` lemma.
    *(deviation: skipped -- `modalHintikkaClauseGen_lift`/`modalStepBranchGen_none_saturated`/
    `modalStepBranchGen_hintikka_inv` are already named with the plan's own "Gen inserted
    mid-name" convention (matching `modalHintikkaClauseGen`/`modalStepBranchGen`, the driver
    defs), which collides with GenericDriver.lean's established bundled-wrapper naming pattern
    for the SAME name. Rather than invent a third naming variant, `modalStepBranchGen_hintikka_inv`
    (the only one Phase 7 needs directly) was de-privatized instead, so `CompletenessLoop.lean`
    (which imports both `Completeness.lean` and `GenericDriver.lean`) calls it directly with
    `spec.localShapeInvariance` inline -- functionally equivalent to a bundled wrapper, without
    the name collision. `modalHintikkaClauseGen_lift` stays `private` (used only internally by
    `modalStepBranchGen_hintikka_inv` and the K corollary); `modalStepBranchGen_none_saturated`
    needs no field so a wrapper adds nothing.)*
  - [x] `lake build` + full CI; `#print axioms` sweep.
- **Timing:** 2.5 hours
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/Completeness.lean` — clause gen + `_eq`; `_lift`; `_none_saturated`;
    `_hintikka_inv`; two projection bridges; K corollaries.
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — bundled wrappers.
- **Verification:**
  - `lake build` green; zero sorry/axiom; K statements byte-unchanged; `modalHintikkaClause_eq` by `rfl`.
  - Full CI clean.
- **Commit:** `task 510 phase 3: generalize Completeness.lean Hintikka clause layer`.

---

### Phase 4: Close the 507 accFreshInv gap in Soundness.lean [COMPLETED]

- **Goal:** Deliver `modalStepBranch_preserves_accFreshInv_gen` — the one step lemma
  `modalStep_preserves_invariant` composes that task 507 did not generalize (report §6). Needs only the
  **existing** `freshLocal` field, so this phase depends on nothing.
- **Tasks:**
  - [ ] `modalStepBranch_preserves_accFreshInv_gen` (from `Soundness.lean:113`) over
    `modalStepBranchGen apply`, taking a raw `hFreshLocal` parameter (keeping `Soundness.lean`'s import
    surface minimal and shake-clean — do **not** import `GenericDriver` here).
  - [ ] Re-derive K's `modalStepBranch_preserves_accFreshInv` as a byte-identical-statement one-line
    corollary via `modalStepBranch_eq`.
  - [ ] No wrapper needed in `GenericDriver.lean`: `CompletenessLoop.lean` imports both `Soundness` and
    (from P5) `GenericDriver`, so it will call
    `modalStepBranch_preserves_accFreshInv_gen apply spec.freshLocal …` directly.
  - [ ] `lake build` + full CI; `#print axioms`.
- **Timing:** 1 hour
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/Soundness.lean` — `_gen` lemma + K corollary.
- **Verification:**
  - `lake build` green; zero sorry/axiom; K statement byte-unchanged; `Soundness.lean`'s import list
    unchanged. Full CI clean.
- **Commit:** `task 510 phase 4: generalize modalStepBranch_preserves_accFreshInv`.
- **Note:** If run in parallel with Phase 1, hold territory strictly — `Soundness.lean` only.

---

### Phase 5: CompletenessLoop.lean layer — import GenericDriver, ModalLoopInvGen [COMPLETED]

- **Goal:** Open the leaf module to the bundled `spec` and establish `ModalLoopInvGen`. This is the
  ergonomic win over 507: `CompletenessLoop.lean` is imported only by the `Cslib.lean` barrel
  (verified), so it may import `GenericDriver` with no cycle and take `spec : RuleApplicationSpec apply`
  **directly** — covering ~700 of the ~850 lines.
- **Tasks:**
  - [ ] Add `public import Cslib.Logics.Modal.Tableau.GenericDriver` to `CompletenessLoop.lean`. Confirm
    no cycle (`lake build`).
  - [ ] `ModalLoopInvGen apply` alongside `ModalLoopInv` (:57). Only the `hintikkaInv` conjunct mentions
    `apply` (via `modalHintikkaClause`); the other six are already rule-agnostic.
  - [ ] **Keep `ModalLoopInv` as its own byte-identical `structure`** (it is public and listed in the
    module's "Main Definitions") and bridge with
    `ModalLoopInv_iff_gen : ModalLoopInv φ0 b e acc rank ↔ ModalLoopInvGen modalApplyOne φ0 b e acc rank`
    (~6 lines, constructor/destructor). **Do NOT** take the `abbrev ModalLoopInv := ModalLoopInvGen modalApplyOne`
    shortcut: it changes the declaration kind and puts the 7-field anonymous destructure at `:683` and
    the 7-field `refine ⟨…⟩` at `:1228` at elaboration risk. This is the one at-risk declaration for
    byte-identity; the keep-both option makes it total.
  - [ ] `modalLoopGen_bClosure` (from `:162`) ← `spec.outputsSubsetUniverse`.
  - [ ] `modalStepBranchGen_newExps_const` (from `:216`) — no field, driver-structural.
  - [ ] `modalApplyGen_hasEdge_mono` (from `modalApplyOne_hasEdge_mono` :451) ← `spec.freshLocal` +
    `hasEdge_addEdge_mono` (:423, already rule-agnostic, reuse unchanged). **No new field.**
  - [ ] **Delete** `modalLoop_snd_eq_or_addEdge` (:432) — its statement is verbatim the existing
    `freshLocal` field (`GenericDriver.lean:131-135`); its own docstring says it is a "local restatement
    of the `private` `modalApplyOne_fresh_local`". Rewire its single caller (:456) to `spec.freshLocal`.
  - [ ] `modalMaxWorld_lt_worldBound_of_phiBound` (:127) is pure arithmetic — reuse unchanged.
  - [x] `lake build` + full CI; `#print axioms` sweep. *(deviation: `lake test`/`lake lint`
    intermittently failed on `Cslib/Logics/Modal/Tableau/LoopChecking.lean` -- task 506's own
    concurrently-edited, untracked-then-tracked file, exhibiting genuine mid-edit unsolved-goal
    errors and missing `.olean` artifacts at different points during this phase. Verified this is
    not caused by this task: a scoped `lake build` over exactly this phase's eight touched modules
    (`CompletenessLoop`, `TDriver`, `GenericDriver`, `Completeness`, `Saturation`, `Rules`,
    `Soundness`, `FmpMeasure`) succeeds cleanly (781/781) in isolation, and none of them import or
    are imported by `LoopChecking.lean`.)*
- **Timing:** 2 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — import; `ModalLoopInvGen` + `Iff` bridge; three
    generic helpers; one deletion.
- **Verification:**
  - `lake build` green (no import cycle); zero sorry/axiom; `ModalLoopInv` byte-identical and still a
    `structure`; `ModalLoopInv_iff_gen` closes. Full CI clean.
- **Commit:** `task 510 phase 5: import GenericDriver into CompletenessLoop; add ModalLoopInvGen`.

---

### Phase 6: The four witness-invariant preservation helpers (F9-F12) [COMPLETED]

- **Goal:** Generalize the four `ModalLoopInv` rule-dependent conjunct-preservation helpers. Their
  **statements mention no `apply` at all** — they are already rule-agnostic; only their preservation
  proofs need fields. This is where F9-F12 first do real work.
- **Tasks:**
  - [ ] `modalLoopGen_eBoxOnlyNeg` (from `:303`, ~60 lines) ← **F9**. The discharge shape:
    `rcases spec.boxPosNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;> rw [h] at hfstc <;> simp at hfstc`
    — the payload is discarded, contradicting the `.linear`/`.branching` split.
  - [ ] `modalLoopGen_eDiamondOnlyPos` (from `:364`) ← **F10**, dual.
  - [ ] `modalLoopGen_eBoxNegWitness` (from `:487`, ~80 lines) ← **F11** + `spec.freshLocal`, using P5's
    `modalApplyGen_hasEdge_mono` (acc-edges only grow) for the pre-existing case and F11's minted
    witness+edge for the freshly-appended `boxNeg`-shaped `sf_exp` case.
  - [ ] `modalLoopGen_eDiamondPosWitness` (from `:589`) ← **F12** + `spec.freshLocal`, dual.
  - [ ] Re-derive K's four as byte-identical-statement corollaries via `modalStepBranch_eq`.
  - [ ] `lake build` + full CI; `#print axioms` sweep.
- **Timing:** 2.5 hours
- **Depends on:** 5
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — four `_gen` helpers + K corollaries.
- **Verification:**
  - `lake build` green; zero sorry/axiom; K statements byte-unchanged. Full CI clean.
- **Commit:** `task 510 phase 6: generalize the four witness-invariant preservation helpers`.
- **Note:** If the field set proves insufficient here, extend `RuleApplicationSpec` and re-discharge for
  **both** `modalApplyOne` and `modalApplyOneT` in this phase, staying green. Never `sorry`.

---

### Phase 7: CRUX — modalStepGen_preserves_invariant + modalExpandBranchesGen_hintikka [COMPLETED]

- **Goal:** The task's crux and its bulk (~380 lines). Deliver the generic top-loop lemma concluding in
  the **generic** Hintikka set.
- **ACCEPTANCE CRITERION (blocking).** `modalExpandBranchesGen_hintikka` MUST conclude in
  `modalHintikkaSetGen apply bR aR` — **NOT** the concrete `modalHintikkaSet bR aR`. If it concludes
  concretely, task 510 lands green with passing CI and tasks 503 / 505 / 506 **stay blocked** — total
  mission failure despite green CI, and the entire purpose of the task is defeated. K's corollary
  recovers the concrete form via `modalHintikkaSet_eq` (a `rfl`), so zero-regression is unaffected.
  Phase 9's one-liner is the structural check: it cannot typecheck if this criterion was missed.
- **Tasks:**
  - [ ] `modalStepGen_preserves_invariant` (from `modalStep_preserves_invariant` :671). It composes
    exactly eight step lemmas; **seven are already available** from task 507 as bundled `(apply, spec)`
    forms — reuse them, do not re-derive:
    `modalStepBranchGen_potential_step` (GenericDriver:341), `_preserves_accTargetsKnown` (:284),
    `_preserves_outDegEq` (:241), `modalStepBranch_preserves_expandedNodup_gen` (FmpMeasure:825, takes
    no field), `_eClosure` (:319), `_expMeasure_step_lt` (:386), and the rule-agnostic
    `modalMaxWorld_lt_worldBound_of_phiBound` (:685). The eighth —
    `modalStepBranch_preserves_accFreshInv_gen` — comes from Phase 4, called as
    `… apply spec.freshLocal …`. The genuinely new surface is only the five rule-dependent conjuncts,
    fed by Phase 6's helpers and Phase 3's `modalStepBranchGen_hintikka_inv`.
  - [ ] `modalExpandBranchesGen_hintikka` (from `modalExpandBranches_hintikka` :746, ~305 lines): outer
    `induction fuel`, a `suffices key` inner induction over the `processNext` worklist, three-parallel-list
    threading. **Must be re-derived against `modalExpandBranchesGen.processNext`** — `modalExpandBranches`
    (Sat:259) and `modalExpandBranchesGen` (Sat:197) are separate defs each with their own
    well-founded `processNext` helper (verified), so the proof cannot be reused. It is otherwise a pure
    substitution port (`modalApplyOne ↦ apply`, `modalStepBranch ↦ modalStepBranchGen apply`).
  - [ ] The only semantically-loaded region is the saturated-leaf discharge (Loop:849-928). Per report
    §4 it reduces exactly to F9-F12 — a `cases φ` over 7 constructors × 2 signs collapsing to three
    patterns:
    - **Structural** (:853-887): `hintikkaInv` gives the clause, definitionally equal to
      `modalHintikkaSetGen`'s conjunct-2 body for that shape; else `.notApplicable → simp [hna]`. Both
      survive substitution of `apply`.
    - **Minting** (:896-898, :901-904): `trivial` — carved out of conjunct 2.
    - **Propagating** (:890-895, :905-911): `eBoxOnlyNeg`/`eDiamondOnlyPos` contradict `sf ∈ e`
      (**F9/F10** via Phase 6); else `.notApplicable → simp [hna]`.
    - Conjuncts 3/4 (:912-928): `eBoxNegWitness`/`eDiamondPosWitness` plus F11/F12's always-applicability
      to rule out the `.notApplicable` alternative.
  - [ ] Re-derive K's `modalExpandBranches_hintikka` as a byte-identical-statement corollary via
    `modalExpandBranches_eq` (Sat:308, already proved via a processNext-level agreement lemma) +
    `modalHintikkaSet_eq`.
  - [x] `lake build` + full CI; `#print axioms` on both new lemmas. Full project build (3233/3233),
    `checkInitImports`, `lake lint` (only pre-existing/unrelated findings: PrimeExclusion.lean and
    two concurrent-session `defsWithUnderscore` findings in task 509's `SegmentLindenbaum.lean`,
    neither touched by this task), `lint-style`, and `lake test` all green. The port compiled
    clean on first full attempt with zero new warnings beyond the established baseline.
- **Timing:** 3.5 hours (exceeds the 1-2h guideline by design — this is the crux; single-agent-run
  bounded; write an 80%-context handoff at a green intermediate lemma if approaching the limit).
- **Depends on:** 4, 6
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — both generic lemmas + K corollaries.
- **Verification:**
  - `lake build` green; zero sorry/axiom.
  - **Conclusion-type gate**: `modalExpandBranchesGen_hintikka`'s conclusion is
    `modalHintikkaSetGen apply bR aR`. Confirm by reading the committed statement.
  - K's `modalExpandBranches_hintikka` statement byte-unchanged. Full CI clean.
- **Overrun split (pre-authorized):** if this phase exceeds one agent run, split at the top-loop
  boundary — **7a** = `modalStepGen_preserves_invariant`, **7b** = `modalExpandBranchesGen_hintikka` —
  appending 7b to this plan. Both must end green and committed.
- **[BLOCKED] fallback:** if `modalExpandBranchesGen_hintikka` cannot be closed sorry-free, mark this
  phase **[BLOCKED]** recording (a) the exact open lemma name, (b) the full goal state at the failing
  step, (c) which spec field is insufficient and what statement would suffice, and (d) whether 7a
  landed. Preserve Phases 1-6 green and committed — they stand alone and advance the interface. **Never**
  introduce `sorry` or `axiom`, and never close the phase with a vacuous placeholder. On the evidence
  (every rule-specific step in the leaf discharge already mapped to a field, report §4), this is judged
  unlikely.
- **Commit:** `task 510 phase 7: generic modalExpandBranchesGen_hintikka over the spec`.

---

### Phase 8: K re-instantiation and zero-regression verification [NOT STARTED]

- **Goal:** Deliver the remaining free generics and prove the zero-regression claim by diff, not by
  assertion.
- **Tasks:**
  - [ ] `modalLoopInvGen_initial` (from `:1217`) — no field; the 5 rule-dependent conjuncts are vacuous
    over `e = []`. Uses 507's `modalStepBranchGen_worldBound` (:365) via `phiBound`.
  - [ ] `modalStepBranchGen_mem_preserved` (from `:1058`) — no field; branches only grow.
  - [ ] `modalExpandBranchesGen_openBranch_initial_mem` (from `:1096`) — no field; needed by 503.
  - [ ] `modalTableau_complete` (:1290) — K corollary, statement byte-identical, unchanged modulo
    `modalHintikkaSet_eq`.
  - [ ] **Byte-identity gate.** `diff` against the pre-510 baseline (`git show <pre-510-sha>:…`) for:
    `kValid`, `modalTableau_decides` (:1334), `instDecidableKValid` (:1346) — these are expected
    **untouched entirely** (they reference only `modalTableau_complete`/`modalTableau_sound`, whose
    statements are preserved) — a stronger result than 507's, which had to re-prove its three
    corollaries. Also diff `ModalLoopInv`, `modalHintikkaSet`, `modalHintikkaClause`,
    `modalExpandBranches_hintikka`, `modalStep_preserves_invariant`, `modalStepBranch_hintikka_inv`,
    `modalStepBranch_none_saturated`, `modalStepBranch_preserves_accFreshInv`. Any drift is a defect.
  - [ ] Re-confirm the Phase 7 conclusion-type criterion holds in the committed source.
  - [ ] Module docstrings: `GenericDriver.lean` (11-field sufficiency note; S4 exclusion preserved),
    `Saturation.lean` / `Completeness.lean` / `CompletenessLoop.lean` "Main Definitions" updated for the
    new `_gen` decls.
  - [ ] Full CSLib CI in order: `lake build`, `lake exe checkInitImports`, `lake lint`,
    `lake exe lint-style`, `lake test`, `lake shake --add-public --keep-implied --keep-prefix`. No new
    files were added, so `lake exe mk_all --module` should be a no-op — if it wants to reorder unrelated
    imports in `Cslib.lean` from concurrent sessions, **leave them alone** (507 Phase 8 hit exactly this).
  - [ ] Exhaustive `#print axioms` sweep over every new/changed top-level declaration: zero sorry, zero
    new axiom.
- **Timing:** 1.5 hours
- **Depends on:** 7
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — three free generics; K corollary; docstrings.
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — sufficiency docstring.
  - `Cslib/Logics/Modal/Tableau/Saturation.lean`, `Completeness.lean` — docstring updates.
- **Verification:**
  - Full CI green; zero sorry/axiom on all touched decls; byte-identity diffs clean;
    conclusion-type criterion confirmed in source.
- **Commit:** `task 510 phase 8: K re-instantiation and zero-regression verification`.

---

### Phase 9: T instantiation — deliver modalExpandBranchesT_hintikka [NOT STARTED]

- **Goal:** Deliver the exact lemma task 503 Phase 5 is blocked on. This phase is **required**, not a
  convenience: it is the deliverable that discharges 510's reason for existing, and it is the structural
  proof that Phases 2 and 7 met their acceptance criteria.
- **Tasks:**
  - [ ] `modalExpandBranchesT_hintikka` in `TDriver.lean`. `TDriver.lean:76` defines
    `modalExpandBranchesT := modalExpandBranchesGen modalApplyOneT …` **definitionally**, and
    `modalApplyOneT_spec` (:759) is complete with all 11 fields as of Phase 2, so this is a one-liner:
    ```lean
    theorem modalExpandBranchesT_hintikka (φ0 : Proposition Atom) (fuel : Nat) : … :=
      modalExpandBranchesGen_hintikka modalApplyOneT modalApplyOneT_spec φ0 fuel …
    ```
    It concludes in `modalHintikkaSetGen modalApplyOneT bR aR`.
  - [ ] **This one-liner is the acceptance test for the whole task.** If it fails to typecheck, one of
    two upstream criteria was violated: F9/F10 were stated with a concrete payload (Phase 2 — T cannot
    discharge), or the crux concluded in concrete `modalHintikkaSet` (Phase 7 — the T conclusion is not
    expressible). Do **not** paper over a failure here with a T-specific re-derivation; fix the upstream
    phase.
  - [ ] Convenience `rfl` bridges if useful to 503: `modalStepBranchT_eq` / `modalExpandBranchesT_eq` /
    `modalTableauT_eq` (all `rfl`, ~15 lines).
  - [ ] Record the handoff for 503 in the completion summary: 503 Phase 5's remaining work is its own
    `hintikka_box_pos` / `hintikka_diamond_neg` analogues (payload-reading, irreducibly T-specific — see
    Non-Goals) plus its truth lemma. **510 does not deliver those**; 505/506 must likewise budget their
    own.
  - [ ] `lake build` + full CI; `#print axioms` on `modalExpandBranchesT_hintikka`.
  - [ ] Write `specs/510_.../summaries/01_generalize-hintikka-chain-over-spec-summary.md`.
- **Timing:** 1 hour
- **Depends on:** 8
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/TDriver.lean` — `modalExpandBranchesT_hintikka` + optional `rfl` bridges.
  - `specs/510_generalize_completeness_loop_hintikka_chain_over_spec/summaries/01_generalize-hintikka-chain-over-spec-summary.md` (new).
- **Verification:**
  - `lake build` green; zero sorry/axiom; `modalExpandBranchesT_hintikka` typechecks as a one-liner
    instantiation. Full CI clean.
- **Commit:** `task 510 phase 9: deliver modalExpandBranchesT_hintikka (unblocks task 503 phase 5)`.

---

## Testing & Validation

Run the full CSLib CI pipeline at the end of **every** phase (order per `cslib.md`):
- [ ] `lake build` — green, and **zero `sorry` / zero new `axiom`** in all delivered decls (`#print axioms`
  on each new `_gen` lemma, each spec witness, and each re-instantiated K corollary; prefer
  `lake env lean` + `#print axioms` over the `lean_verify` MCP tool, which 507 Phase 2 caught reporting
  a spurious stale `sorryAx` immediately after an edit).
- [ ] `lake exe checkInitImports` — every touched file imports `Cslib.Init`.
- [ ] `lake lint` — docstrings on every new decl (docBlame); Prop-valued results as `lemma`/`theorem`
  (defLemma); lowerCamelCase names; `@[simp]` only with verified LHS (simpNF); `omit`/`include` unused
  section vars. (507 recorded one pre-existing unrelated failure in `PrimeExclusion.lean` — not ours.)
- [ ] `lake exe lint-style` — style clean (watch the 100-char limit in new docstrings).
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no new findings vs. baseline.
- [ ] `lake exe mk_all --module` — no new files are added by this task, so expect a no-op; do not
  restage unrelated concurrent-session import reordering.

**Acceptance criteria (task-level, all blocking):**
- [ ] **F9/F10 are stated with `∃ out, (apply sf b acc).1 = .persistent out`** — not a concrete payload.
- [ ] **`modalExpandBranchesGen_hintikka` concludes in `modalHintikkaSetGen apply bR aR`** — not
  `modalHintikkaSet bR aR`.
- [ ] **`modalExpandBranchesT_hintikka` typechecks as a one-liner** instantiation (the structural proof
  of the two criteria above).
- [ ] `modalHintikkaSetGen` lives in `Saturation.lean` and is **spec-free** (S4/506 can consume the
  statement shape without discharging the spec it is excluded from).
- [ ] `RuleApplicationSpec` has 11 fields, discharged sorry-free for **both** `modalApplyOne` and
  `modalApplyOneT`.
- [ ] Zero regression: `kValid` / `modalTableau_decides` / `instDecidableKValid` untouched;
  `ModalLoopInv` byte-identical and still a `structure`; all K corollaries byte-identical by diff.
- [ ] Zero sorry, zero axiom, zero vacuous placeholders across the whole task.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Rules.lean` — four relocated public K shape/witness lemmas (two
  payload-weakened to `∃ out`).
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — `modalHintikkaSetGen` (spec-free) + `modalHintikkaSet_eq`.
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — `RuleApplicationSpec` 7 → 11 (F8-F12);
  `modalApplyOne_spec` extended; bundled wrappers; sufficiency docstring.
- `Cslib/Logics/Modal/Tableau/Completeness.lean` — `modalHintikkaClauseGen` + `_eq`; `_lift`;
  `_none_saturated`; `_hintikka_inv`; two free projection bridges; K corollaries.
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — `modalStepBranch_preserves_accFreshInv_gen` + K corollary.
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — imports `GenericDriver`; `ModalLoopInvGen` +
  `Iff` bridge; the four witness-invariant helpers; `modalStepGen_preserves_invariant`;
  `modalExpandBranchesGen_hintikka`; three free generics; K corollaries; one deletion.
- `Cslib/Logics/Modal/Tableau/TDriver.lean` — `modalApplyOneT_spec` extended to 11 fields;
  `modalExpandBranchesT_hintikka`; four redundant privates dropped.
- `specs/510_.../summaries/01_generalize-hintikka-chain-over-spec-summary.md` (on completion).

## Rollback/Contingency

- Each phase is a self-contained, task-scoped commit at a green milestone; revert an individual phase's
  commit to roll back without disturbing prior phases. **Concurrent sessions run in this repo**: scope
  every `git add` to the phase's named files — never `git add -A` / `git add .` — and never revert or
  restage another session's files.
- The generalization is behavior-preserving for K: all public statements are retained as
  byte-identical corollaries and every generic decl is additive, so reverting the six touched
  `Cslib/Logics/Modal/Tableau/*.lean` files restores the original hard-coded K chain intact. The one
  subtractive change (deleting `modalLoop_snd_eq_or_addEdge`, Phase 5) removes a `private` lemma whose
  statement is verbatim an existing spec field — no external surface.
- Preferred contingency for the crux (Phase 7) is a documented **[BLOCKED]** handoff with the open goal
  state and the exact insufficient spec field — never a `sorry` or `axiom`. Phases 1-6 stand alone and
  advance the interface (the 11-field spec, both witnesses, and the whole `Completeness.lean` layer)
  even if 7-9 must be deferred; any deferred residue is sequenced as new phases appended to this plan.
- If Phase 9's one-liner fails, the defect is upstream (Phase 2's F9/F10 form or Phase 7's conclusion
  type). Fix the upstream phase and re-run; do **not** work around it with a T-specific re-derivation,
  which would reproduce the exact ~850-line duplication this task exists to eliminate.
