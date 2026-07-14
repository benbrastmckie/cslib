# Implementation Plan: CK Soundness + Completeness via Segment / Fallible-World Construction

- **Task**: 493 - CK (constructive modal logic K) soundness + completeness over birelational semantics
- **Status**: [NOT STARTED]
- **Effort**: 22-32 hours (9 phases + 1 conditional contingency phase; see Effort Estimate)
- **Dependencies**: 480 (IK framework — reference/pattern only, NOT instantiated), 490 (Birelational.lean — reused verbatim)
- **Research Inputs**: reports/01_ck-segment-construction-scope.md (Tier 1, adversarially verified)
- **Artifacts**: plans/01_ck-segment-completeness.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/context/contracts/reference-grounding.md (H3, Tier 1)
- **Type**: cslib
- **Mode**: `--hard --lit` (H2 anti-analysis, H3 BibKey grounding, H7 territory, H8 phase sizing, H9 wrap-up)

---

## Overview

**Corrected approach (read this first).** The task-493 description says CK should be built by
"instantiating the intuitionistic modal framework (task 480)." Research report 01 proves, with
three independent arguments plus ground-truth confirmation (ianshil/CK ships
`Completeness_seg/CK_seg_completeness.v` and deliberately **no** `CK_th_completeness.v`), that
**this premise is false for bare CK**. Bare CK cannot reuse 480's prime-pair / consistent-prime-theory
canonical model at all: under `IValid`, `◇⊥→⊥` (Nd) is vacuously valid but is not a CK theorem, so
CK is provably *incomplete* for any consistent-prime-theory model. **This plan therefore builds a
separate segment / fallible-world canonical construction stated over `MValid`, not `IValid`.** The
`CanonicalModel.lean`/`Completeness.lean` machinery of 480 is used as a *pattern source only*; it is
neither imported nor instantiated for the modal core.

**Scope.** Add ~4 new files under `Cslib/Logics/Modal/Metalogic/Constructive/` (namespace
`Cslib.Logic.Modal`), mirroring the existing `Intuitionistic/` layout:

- `Segment.lean` — `CKSegment ⟨head, tail⟩`, `cexpl`, `QuasiPrime`, `cireach`/`Preorder`, `cmreach`, `cval`.
- `SegmentLindenbaum.lean` — the segment saturation / realization lemma (**highest risk**).
- `CKTruthLemma.lean` — 5 non-modal cases (transliterated) + box/diamond cases + `f1`/`f2`.
- `CK.lean` — `CKModalAxiom`, `ck_axiom_sound`/`ck_soundness` (over `MValid`), `ck_completeness`, `ck_consistent`, `ck_soundness_completeness`.

**Definition of done.** All four files build under `lake build`; zero `sorry`/`axiom`/`native_decide`
in the new files; the full CI pipeline (`lake test`, `checkInitImports`, `lint-style`, `shake`) is
green; `ck_soundness : Derivable CKModalAxiom φ → MValid φ` and
`ck_completeness : MValid φ → Derivable CKModalAxiom φ` are both proved; and no file outside
`Constructive/` is modified **except** (a) the aggregating import module and (b), only if the
Phase 4 contingency fires, one additive lemma in `Cslib/Foundations/Logic/Metalogic/`.

### Preserved Assets

The following work is complete and MUST NOT regress. Phases that touch shared modules must leave
these byte-identical (verified by the untouched-480 / untouched-classical gates in each phase).

| Component | File | Status | Reuse form |
|-----------|------|--------|------------|
| Birelational semantics (BFrame/BModel/BForces/MValid/IValid/persistence) | `Cslib/Logics/Modal/Semantics/Birelational.lean` (task 490) | [COMPLETED] | Verbatim, no change |
| `prime_set_exclusion` (free `Cons` param) | `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean:558` | [COMPLETED] | Reused with a quasi-consistency `Cons`; **read-only unless Phase 4 contingency fires** |
| DerivationTree / Derivable / deductionTheorem / DerivExcludes / modalDeductiveClosure / DeductivelyClosed | `Metalogic/DeductionTheorem.lean`, `MCS.lean`, `PrimeTheory.lean` (generic parts) | [COMPLETED] | Verbatim, parametric over `Axioms` |
| IK framework (IKModalAxiom, canonicalR, box_witness_pair_underivable, IK/IS4/IS5/IT) | `Cslib/Logics/Modal/Metalogic/Intuitionistic/*` (task 480) | [COMPLETED] | **Pattern reference only — never imported/instantiated for the CK modal core** |
| Non-modal truth-lemma cases (atom/bot/and/or/imp) | `Intuitionistic/TruthLemma.lean` | [COMPLETED] | Reused as *proof pattern*, re-stated over `cmreach`/`cval` |

### Source-to-Implementation Mapping (H3, Tier 1)

Ground truth = ianshil/CK Coq mechanization + `Wijesekera1990`. BibKeys verified in report 01
against `references.bib`: `Wijesekera1990` (line 885), `Simpson1994` (86), `ChagrovZakharyaschev1997` (75).
No new BibKey required.

| Source claim | BibKey / artifact | Lean target | Phase |
|--------------|-------------------|-------------|-------|
| Bare CK = int.prop. + Kb + Kd + nec (no Cd/Idb/Nd) | ianshil `CKH.v` `NoAdAx := fun _ => False`; `Wijesekera1990` §2 | `CKModalAxiom` = `IKModalAxiom` minus `cd`/`idb`/`dbot` | 1 |
| Segment world `⟨head, tail⟩` + 4 constraints; exploding `cexpl` | ianshil `general_seg_completeness.v` (`segment`, `cexpl`) | `CKSegment`, `cexpl` | 2 |
| `cmreach P Q := Q.head ∈ P.tail`; `cireach = head ⊆`; `cval = atom ∈ head` | ianshil `general_seg_completeness.v` | `cmreach`/`cireach`/`cval` | 2 |
| Soundness over fallible-world (`MValid`) semantics | `Simpson1994` Ch.3; `IK.lean` `ik_axiom_sound` | `ck_axiom_sound`/`ck_soundness` | 3 |
| Generic Lindenbaum / prime-set exclusion, `Cons` parametric | `ChagrovZakharyaschev1997` Lemma 5.5; `PrimeExclusion.lean:558` | segment saturation lemma | 4 (+4a) |
| Segment-model up/down confluence | `Simpson1994` (F1/F2) | `f1`/`f2` for `cireach`/`cmreach` | 5 |
| Truth lemma coincides with head-membership; `botForces := (⊥ ∈ ·.head)` | ianshil `CK_seg_completeness.v`; `Wijesekera1990` | `ck_truth_lemma` | 6, 7 |
| Bare-CK completeness routed through segments, target `MValid` | ianshil `CK_seg_completeness.v` | `ck_completeness` | 8 |

---

## Postmortem Constraints

Binding rules for all implementation dispatches. No prior CK implementation attempts exist; these
derive from report 01's risk factors, the adversarial-verification findings, and the 480 experience.

**Do NOT**:
- **Do NOT instantiate 480's `mvalid_completeness` / `canonicalR` / `CanonicalPrimeWorld` for the CK modal core.** Adversarially confirmed impossible: `mvalid_completeness` (`Completeness.lean:263-283`) *requires* `h_Idb`/`h_Cd`/`h_dbot` dischargers that do not exist for CK, and consistent prime theories cannot contain `⊥`, collapsing any `botForces` to `IValid` and proving the non-theorem Nd. Reusing it would produce an unsound result.
- **Do NOT state completeness over `IValid`.** CK is incomplete for `IValid`. The target is `MValid` with a genuinely fallible `botForces := (⊥ ∈ ·.head)`. Any phase that writes `IValid` in a CK completeness/soundness statement is wrong by construction.
- **Do NOT add `cd`, `idb`, or `dbot` constructors to `CKModalAxiom`.** Bare CK is the strict sub-system. Adding them silently reintroduces IK and makes `◇⊥→⊥` derivable.
- **Do NOT import or re-derive 480's `box_witness_pair_underivable` / `bigAnd`/`boxOr_of_boxDisj` / `dia_bigAnd_to_bigAnd_dia` cast, `canonical_box_witness`, or `canonical_diamond_witness`.** These are Cd+Idb-specific; CK's diamond/box witnesses are *structural* fields of the segment. Pulling them in is wasted effort and a category error.
- **Do NOT close any goal with `sorry`, `admit`, `axiom`, `native_decide`, or a vacuously-true definition.** Every modal assumption must enter as a `CKModalAxiom` constructor, exactly as 480 threads its `h_*` hypotheses. Zero-debt is a hard gate per phase.
- **Do NOT let the saturation phase (4) sprawl past its budget by inlining what should be a reusable Foundations lemma.** If the outer tail-assembly fixpoint proves unwieldy, STOP and escalate to the Phase 4a contingency (a dedicated additive Foundations lemma) rather than accreting a 700-line monolith.

**MUST preserve** (regression-forbidden):
- `Cslib/Logics/Modal/Semantics/Birelational.lean` — byte-identical.
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/*` (all 480 files) — byte-identical.
- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` — read-only, unless Phase 4a fires (then *append-only*: a new lemma, no edits to `prime_set_exclusion`'s signature or body).
- Existing `lake test` suite — must remain green after every phase.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **Separate segment/fallible construction, not a 480 instantiation** — settled by report 01 §4 + three-way adversarial check. The alternative (clever `botForces` over prime pairs) was rejected because it is *logically impossible*, not merely inconvenient.
- **`MValid` target, `botForces := (⊥ ∈ ·.head)`** — settled; forced by CK-incompleteness-for-`IValid`.
- **`CKModalAxiom = IKModalAxiom − {cd, idb, dbot}`** — settled, pinned against ianshil `NoAdAx` in Phase 1. (Plan-time caveat resolved in Phase 1: bare CK excludes Nd; do not confuse with Wijesekera's CK+Nd.)
- **Diamonds witnessed by construction via `tail`** — settled; this is *why* CK needs neither Cd nor Idb.

---

## Goals & Non-Goals

- **Goals**:
  - `ck_soundness : Derivable CKModalAxiom φ → MValid φ` (easy; subset of `ik_axiom_sound`).
  - `ck_completeness : MValid φ → Derivable CKModalAxiom φ` (segment canonical model).
  - `ck_soundness_completeness` (bi-conditional) and `ck_consistent`.
  - Zero-debt, CI-green, parametric-over-`Axioms` design so task 501 can extend it.
- **Non-Goals**:
  - CT/CS4/CS5 extensions (task 501) — only the parametric hook is provided, not the instances.
  - Any change to IK / classical / Birelational semantics.
  - Decidability, finite-model property, or complexity results for CK.
  - Wijesekera's CK+Nd variant.

## Risks & Mitigations

- **Risk (HIGHEST): segment saturation/realization lemma (Phase 4).** Two-level "theory of theories"
  construction (saturate `head` + populate `tail` so each member is realizable, diamond-witnessed,
  box-reflecting) with no direct 480 analogue. *Mitigation*: isolated as its own phase with an
  explicit sub-lemma budget, a STOP/partial contingency, and a pre-declared escape hatch (Phase 4a)
  that lifts the reusable core into an additive Foundations lemma.
- **Risk (moderate): `f1`/`f2` up/down confluence for the segment model (Phase 5).** Interaction of
  head-inclusion (`cireach`) with tail-membership (`cmreach`), including at `cexpl`. *Mitigation*:
  `cexpl` self-accessibility (`cexpl.head ∈ cexpl.tail`) checked first; small dedicated phase.
- **Risk (low): axiom-list drift.** Accidentally including Nd/Cd/Idb. *Mitigation*: Phase 1 pins the
  list against ianshil `NoAdAx` and adds a comment-level provenance note; postmortem gate forbids the
  three constructors.
- **Risk (low): territory collisions in parallel waves.** *Mitigation*: H7 file-ownership table; each
  parallel phase owns a distinct file.

---

## Implementation Phases

**Per-phase gates (apply to EVERY phase; a phase is not [COMPLETED] until all pass):**
1. **BUILD**: `lake build` of the phase's target file(s) succeeds.
2. **ZERO-DEBT**: `grep -nE 'sorry|admit|\baxiom\b|native_decide' <new files>` returns nothing.
3. **UNTOUCHED-480**: `git diff --stat` shows no changes under `Cslib/Logics/Modal/Metalogic/Intuitionistic/` or `Cslib/Logics/Modal/Semantics/`.
4. **UNTOUCHED-CLASSICAL**: `git diff --stat` shows no changes under `Cslib/Logics/Modal/Metalogic/Systems/` or any classical modal file.
5. **INCREMENTAL COMMIT** (H9): commit at the green milestone as `task 493 phase P: {name}`.
Final phase additionally runs the full CI pipeline (`lake test`, `checkInitImports`, `lint-style`, `shake`).

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 (+4a if triggered), 5 | 2 |
| 4 | 6 | 2, 5 |
| 5 | 7 | 4, 6 |
| 6 | 8 | 7 |
| 7 | 9 | 3, 8 |

Phases within the same wave can execute in parallel (distinct file ownership per H7). The genuine
parallel opportunities are **2 ‖ 3** (structure ‖ soundness) and **4 ‖ 5** (saturation ‖ confluence);
the remainder is a tight proof-dependency chain.

**H7 file ownership** — Phase → file it may write:
- P1 → `CK.lean` (axioms only) · P2, P5-frame → `Segment.lean` · P3 → `CK.lean` (soundness block; wave-serialized after P1) · P4/P4a → `SegmentLindenbaum.lean` (+ additive Foundations lemma if 4a) · P5 → `CKTruthLemma.lean` (f1/f2) · P6, P7 → `CKTruthLemma.lean` · P8, P9 → `CK.lean` (completeness + capstone).
- Note: `CK.lean` is a capstone touched by P1/P3/P8/P9, all in **different waves**, so never a live conflict.

---

### Phase 1: `CKModalAxiom` — pin the exact bare-CK axiom list [IN PROGRESS]
- **Goal:** Define `CKModalAxiom : Proposition Atom → Prop` = `IKModalAxiom` minus `cd`, `idb`, `dbot`, with a provenance comment tying each constructor to ianshil `CKH.v`/`NoAdAx` and `Wijesekera1990`.
- **Tasks:**
  - [ ] Read `IK.lean`'s `IKModalAxiom` constructor list; enumerate the 9 int-prop + `k` + `kdia` to keep and the 3 (`cd`/`idb`/`dbot`) to drop.
  - [ ] Confirm bare CK excludes Nd (resolve the "some authors call CK+Nd `CK`" caveat from report §5 against ianshil `NoAdAx`); record the decision in a doc comment.
  - [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/CK.lean` with `namespace Cslib.Logic.Modal`, imports, and only `CKModalAxiom`.
- **Estimated output:** ~80-140 lines. **Done when:** `CKModalAxiom` compiles; no `cd`/`idb`/`dbot`; provenance comment present; ZERO-DEBT + gates pass.
- **Timing:** 1.5-2.5h
- **Depends on:** none

### Phase 2: `CKSegment` structure, `cexpl`, accessibility, valuation [NOT STARTED]
- **Goal:** Define the segment world type and the birelational model data over it.
- **Tasks:**
  - [ ] `QuasiPrime Axioms S := Prime … S ∨ S = Set.univ`.
  - [ ] `structure CKSegment (Axioms)` with fields `head`, `tail`, `head_closed`, `head_qprime`, `tail_realizable`, `box_reflect`, `diam_witness` (per report §2.1 sketch).
  - [ ] `def cexpl : CKSegment Axioms` with `head := univ`, `tail := {univ}`; discharge all field obligations (univ is quasi-prime, closed, reflects/witnesses trivially).
  - [ ] `cireach P Q := P.head ⊆ Q.head` + `Preorder (CKSegment Axioms)` instance (pattern from `CanonicalModel.lean:85`).
  - [ ] `cmreach P Q := Q.head ∈ P.tail`; `cval s p := Proposition.atom p ∈ s.head`.
- **Estimated output:** ~150-250 lines. **Done when:** file builds; `cexpl` fully constructed (no field left as `sorry`); `Preorder` instance accepted; gates pass.
- **Timing:** 3-4h
- **Depends on:** 1

### Phase 3: `ck_axiom_sound` / `ck_soundness` over `MValid` [NOT STARTED]
- **Goal:** Prove soundness (the easy direction) directly over arbitrary `botForces`.
- **Tasks:**
  - [ ] Adapt `ik_axiom_sound`'s `k`/`kdia` + 9 non-modal cases (`IK.lean:137-170`) to `CKModalAxiom`, re-generalized to arbitrary upward-closed `botForces` (non-modal cases route through `bforces_persistence`, generic over `botForces`).
  - [ ] Drop the `idb` case (used `f2`) and the vacuous `dbot` case — CK has neither.
  - [ ] Conclude `ck_soundness : Derivable CKModalAxiom φ → MValid φ` and `ck_soundness_derivable` helper.
- **Estimated output:** ~120-200 lines. **Done when:** `ck_soundness` builds sorry-free over `MValid`; no `IValid` anywhere; gates pass.
- **Timing:** 2-3h
- **Depends on:** 1 (independent of the segment construction — runs parallel to Phase 2; wave-serialized on `CK.lean` after Phase 1)

### Phase 4: Segment saturation / realization lemma [NOT STARTED] — HIGHEST RISK
- **Goal:** Given a formula `φ` underivable in CK, build a `CKSegment` whose `head` is quasi-prime,
  deductively closed, excludes `φ`, and whose `tail` simultaneously (a) witnesses every `◇A ∈ head`
  with some `t ∈ tail, A ∈ t`, (b) makes every `t ∈ tail` itself a realizable (quasi-prime, closed)
  head, and (c) satisfies `□`-reflection.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean`.
  - [ ] Instantiate `prime_set_exclusion` (`PrimeExclusion.lean:558`) with a **quasi-consistency** `Cons` (trivially-true / "prime-or-univ") to saturate each *individual* head and tail-member (admits the exploding theory).
  - [ ] Build the **outer** fixpoint that assembles `tail` and threads the box-reflect / diamond-witness constraints (this is the genuinely new work with no 480 analogue).
  - [ ] Prove the realization lemma: `¬ Derivable CKModalAxiom φ → ∃ s : CKSegment, φ ∉ s.head`.
  - [ ] Sub-lemma budget (target ≤ 6 named sub-lemmas): head saturation; tail-member realizability; diamond saturation closure; box-reflection preservation; `cexpl` as the `⊥`-witness; assembly.
- **STOP / partial contingency:** If after the read budget the outer tail-assembly fixpoint is not
  converging (e.g., the box/diamond constraints are not simultaneously satisfiable inline within the
  sub-lemma budget), **STOP**, mark this phase `[PARTIAL]`, commit the proven sub-lemmas, and
  **escalate to Phase 4a** rather than growing a monolith. Report the exact stuck goal state.
- **Estimated output:** ~300-500 lines. **Done when:** the realization lemma is stated and proved
  sorry-free (or `[PARTIAL]` with a precise handoff to 4a); gates pass on what compiles.
- **Timing:** 6-9h (dominant uncertainty of the whole plan)
- **Depends on:** 2

### Phase 4a (CONDITIONAL — only if Phase 4 STOPs): additive Foundations "saturated witness-family" lemma [NOT STARTED]
- **Goal:** Lift the reusable core of the two-level construction into a generic, append-only lemma in
  `Cslib/Foundations/Logic/Metalogic/` (a "saturated witness-family" analogous to how 480 needed the
  new `prime_set_exclusion` infra), then discharge Phase 4 by instantiating it.
- **Tasks:**
  - [ ] Read `prime_set_exclusion` (`:558-579`) and its neighbours to find the right generalization seam.
  - [ ] State a generic lemma: given a base theory + a family of "demands" (diamond formulas) and a
        reflection constraint, produce a saturated family of quasi-prime closed sets realizing all demands.
  - [ ] Prove it **append-only** (new lemma; no edits to existing `PrimeExclusion.lean` declarations).
  - [ ] Return to Phase 4 and instantiate; complete the realization lemma.
- **Estimated output:** ~200-400 lines (Foundations lemma) + ~100-150 lines (Phase 4 instantiation).
- **Done when:** the Foundations lemma builds sorry-free; `PrimeExclusion.lean` diff is append-only; Phase 4 realization lemma completes; gates pass.
- **Timing:** +6-10h **if triggered** (this is the plan's largest schedule risk; see Effort Estimate).
- **Depends on:** 4 (STOP signal). **Escalation note for the user:** authorizing this plan authorizes Phase 4a *only if* Phase 4 hits its STOP condition; the orchestrator/user should be re-prompted before committing the Foundations edit.

### Phase 5: `f1` / `f2` up-down confluence for the segment model [NOT STARTED]
- **Goal:** Prove the Birelational frame conditions (F1 up-confluence, F2 down-confluence) relating
  `cireach` (head-inclusion) and `cmreach` (tail-membership), including the `cexpl` corner.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/CKTruthLemma.lean`; state `f1`/`f2` for the segment model.
  - [ ] Check `cexpl` self-accessibility (`cexpl.head ∈ cexpl.tail`) and that fallibility does not obstruct confluence.
  - [ ] Prove `f1`/`f2` sorry-free.
- **Estimated output:** ~100-200 lines. **Done when:** `f1`/`f2` build; gates pass. (Independent of Phase 4 — runs parallel to it; distinct file.)
- **Timing:** 2.5-4h
- **Depends on:** 2

### Phase 6: Non-modal truth-lemma cases over `cmreach`/`cval` [NOT STARTED]
- **Goal:** Transliterate `truth_atom/bot/and/or/imp_case` from `Intuitionistic/TruthLemma.lean`,
  re-stated over `cmreach`/`cval` with `botForces := (⊥ ∈ ·.head)`.
- **Tasks:**
  - [ ] Port the 5 cases; `truth_bot_case` discharges its `botForces ↔ ⊥ ∈ ·` bridge by `Iff.rfl`.
  - [ ] Verify each proof uses only closure, quasi-primality, `≤`-inclusion, and the `botForces` bridge (no modal axiom).
- **Estimated output:** ~150-250 lines. **Done when:** 5 non-modal cases build sorry-free; gates pass.
- **Timing:** 3-4h
- **Depends on:** 2, 5

### Phase 7: Box/diamond truth-lemma cases + assemble `ck_truth_lemma` [NOT STARTED]
- **Goal:** Prove the `.box` and `.diamond` cases via the structural `box_reflect`/`diam_witness`
  fields (+ IH + saturation), and assemble the full `ck_truth_lemma : BForces cmreach cval (⊥∈·.head) s φ ↔ φ ∈ s.head`.
- **Tasks:**
  - [ ] `.box` case: `□A ∈ head → ∀ t ∈ tail, A ∈ t` (field) + IH.
  - [ ] `.diamond` case: forward via `diam_witness` + `cexpl` as the `◇⊥` witness; backward via the saturation guarantee that tail-members reflect to diamonds in `head` (from Phase 4).
  - [ ] Assemble `ck_truth_lemma` by induction on `φ`, combining Phase 6 cases.
- **Estimated output:** ~150-250 lines. **Done when:** `ck_truth_lemma` builds sorry-free; gates pass.
- **Timing:** 3-4.5h
- **Depends on:** 4, 6

### Phase 8: `ck_completeness` [NOT STARTED]
- **Goal:** Assemble the canonical segment model + realization lemma + truth lemma into
  `ck_completeness : MValid φ → Derivable CKModalAxiom φ`.
- **Tasks:**
  - [ ] Contrapositive: from `¬ Derivable CKModalAxiom φ`, use Phase 4 to get a segment `s` with `φ ∉ s.head`; by `ck_truth_lemma`, `s` does not force `φ`; the segment model (with `botForces := ⊥∈·.head`, upward-closed under `cireach` for free) refutes `MValid φ`.
  - [ ] Confirm the canonical `botForces` upward-closure obligation `bf_upward_closed` holds under head-inclusion.
- **Estimated output:** ~150-250 lines. **Done when:** `ck_completeness` builds sorry-free over `MValid`; gates pass.
- **Timing:** 3-4h
- **Depends on:** 7

### Phase 9: Capstone — `ck_soundness_completeness`, `ck_consistent`, import wiring, full CI [NOT STARTED]
- **Goal:** Bi-conditional, consistency corollary, module aggregation, and the full CI pipeline green.
- **Tasks:**
  - [ ] `ck_soundness_completeness : Derivable CKModalAxiom φ ↔ MValid φ`; `ck_consistent : ¬ Derivable CKModalAxiom ⊥`.
  - [ ] Wire the four new files into the aggregating import module (`Cslib.lean` / the Modal metalogic aggregator); run `checkInitImports`.
  - [ ] Run full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`.
  - [ ] Final ZERO-DEBT sweep across all four new files.
- **Estimated output:** ~80-150 lines. **Done when:** all CI gates green; both headline theorems proved; zero debt; gates pass.
- **Timing:** 2-3h
- **Depends on:** 3, 8

---

## Highest-Risk Phases (for the authorization decision)

1. **Phase 4 — segment saturation/realization lemma (SEVERE).** The single dominant uncertainty.
   Two-level theory-of-theories with no 480 analogue. This is the CK counterpart of the moment 480
   discovered it needed new `prime_set_exclusion` infrastructure. It carries an explicit STOP/partial
   contingency and an escape hatch (4a).
2. **Phase 4a — additive Foundations lemma (SCHEDULE RISK, conditional).** Fires only if Phase 4
   STOPs. If it fires it adds ~6-10h and touches `Foundations/` (append-only). This is the main reason
   the effort range is wide. **Recommend the user pre-authorize 4a as append-only, with a re-prompt
   before the Foundations commit.**
3. **Phase 7 — box/diamond truth-lemma cases (MODERATE).** Backward diamond direction couples to the
   saturation guarantees from Phase 4; if Phase 4 lands `[PARTIAL]`, Phase 7 is blocked.
4. **Phase 5 — f1/f2 confluence (MODERATE).** Head-inclusion vs. tail-membership interaction at `cexpl`.

All other phases (1, 2, 3, 6, 8, 9) are low-to-moderate: mechanical adaptation, structural definitions,
or assembly.

---

## Effort Estimate

| Scenario | Phases | Hours |
|----------|--------|-------|
| **Base case** (Phase 4 inline, no contingency) | 1,2,3,5,6,7,8,9 + inline 4 | **22-28h** |
| **With contingency** (Phase 4a fires) | + 4a | **28-38h** |

Point estimate for the user: **~25h base, ~34h if the Foundations escape hatch is needed.** Line
scale ~900-1450 across 4 new files (report 01 estimate), comparable to 480's modal portion but
*without* 480's hardest lemma (`box_witness_pair_underivable`, ~250 lines skipped entirely). The
risk profile is *inverted* vs 480: it trades that lemma away for the segment-saturation risk (Phase 4).

---

## Testing & Validation

- [ ] `lake build` green after each phase (per-phase BUILD gate).
- [ ] `grep -nE 'sorry|admit|\baxiom\b|native_decide'` empty across the 4 new files (ZERO-DEBT gate).
- [ ] `git diff --stat` shows no changes under `Intuitionistic/`, `Semantics/`, or classical `Systems/` (UNTOUCHED gates) — except the append-only Foundations lemma if Phase 4a fires.
- [ ] Full CI at Phase 9: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Headline theorems type-check with expected statements: `ck_soundness` (→ `MValid`), `ck_completeness` (from `MValid`), `ck_soundness_completeness`, `ck_consistent`.
- [ ] `lean_verify` (or equivalent) confirms no unexpected axioms in the two headline theorems.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean`
- `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean` (+ possible additive lemma in `Cslib/Foundations/Logic/Metalogic/` if Phase 4a fires)
- `Cslib/Logics/Modal/Metalogic/Constructive/CKTruthLemma.lean`
- `Cslib/Logics/Modal/Metalogic/Constructive/CK.lean`
- Aggregating import-module update
- `specs/493_CK_constructive_modal_soundness_completeness/summaries/01_ck-segment-completeness-summary.md` (at completion)

## Downstream Note: Task 501 (CT / CS4 / CS5)

The segment/fallible model extends cleanly, mirroring how 480's `IValid` framework extended to
IT/IS4/IS5. In ianshil this is the `ClassF` + `AdAx` parametrization of `general_seg_completeness.v`:
bare CK is `ClassF := fun _ => True`, `NoAdAx`; CT/CS4/CS5 set `ClassF` to reflexive /
reflexive-transitive / equivalence frame classes and add T/4/5 to `AdAx`. **This plan therefore keeps
`CKSegment` and the truth/completeness machinery parametric over `Axioms`** so 501 instantiates by
adding constructors + a frame-class hypothesis on `cmreach`, with no re-derivation of the segment core.
`cexpl` satisfies reflexivity/transitivity (`cmreach cexpl cexpl` holds since `cexpl.head = univ ∈ {univ} = cexpl.tail`), so fallibility does not obstruct frame conditions. **Primary 501 risk (flag now,
resolve in 501):** the euclidean-vs-symmetry concern from task 494 propagates to CS5 — proving
`cmreach` euclidean from axiom 5 over segments-with-`cexpl` is where 501's difficulty will concentrate.

## Rollback / Contingency

- Each phase commits independently; revert a single phase's commit to roll back without losing prior phases.
- Phase 4 STOP → `[PARTIAL]` with proven sub-lemmas committed; resume via Phase 4a.
- If the whole approach must be abandoned, deleting `Constructive/` and the import-module line fully
  reverts the change (all reused assets are read-only and untouched).
