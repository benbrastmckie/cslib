# Implementation Plan: Uniform Frame-Condition-to-Axiom Correspondence Library

- **Task**: 522 - Uniform frame-condition-to-axiom correspondence library
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours (Phase 1 complete ~1.5h; Phases 3-5 ~4.5h — unblocked, design decision resolved 2026-07-18)
- **Dependencies**: None (research complete)
- **Research Inputs**: reports/01_frame-condition-correspondence-survey.md
- **Artifacts**: plans/01_frame-correspondence-library.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib (Lean 4)
- **Lean Intent**: false

## Overview

Build a uniform frame-condition-to-axiom correspondence library so per-system Hilbert soundness
proofs consume shared correspondence lemmas instead of reproving each modal-axiom case inline.
The correspondence infrastructure is already half-built: `Metalogic/Soundness.lean` factors 13
`Satisfies.*_axiom` lemmas, `Tableau/FrameSoundness.lean` already abstracts frame conditions over
`Std.Refl`/`IsTrans`/`Std.Symm`/`Relation.RightEuclidean`, and `Foundations/Relation/Euclidean.lean`
provides `Relation.RightEuclidean` with correspondence theorems. The fix is 5 more lemmas in the
same established pattern (modalT/Four/B/D/Five), then rewiring the ~23 byte-identical inlined modal
cases across the 14 `Systems/*/Soundness.lean` files that carry a frame axiom.

Definition of done: (Phase 1) a new additive core file compiles sorry-free and lint-clean, wired
into the import graph, changing no existing proof; (Phases 3-5) the 14 consumer soundness files
delegate their modal cases to the new lemmas with public signatures unchanged, and the full
`lake build` + `lake lint` pass. The interface design is resolved (user, 2026-07-18), so Phases
3-5 are unblocked; the Zulip step is a non-blocking pre-PR heads-up (Phase 2).

### Research Integration

Key findings encoded directly into this plan:

- **REUSE-FIRST**: Do NOT define new frame-property predicates. Reuse Mathlib `Std.Refl`,
  `IsTrans`, `Std.Symm`, `Relation.Serial` and Cslib `Relation.RightEuclidean`
  (`Foundations/Relation/Euclidean.lean`). `Relation.Serial` is already used at
  `Systems/D/Soundness.lean`.
- **PROBLEM CONFINED to the Hilbert soundness path**: only the 5 modal frame-axiom cases remain
  inlined and duplicated. The shared `Metalogic/Soundness.lean` already factors the propositional/
  K/and-or/dia-duality cases; adding 5 modal lemmas is the identical move.
- **RECOMMENDED DESIGN**: 5 `Satisfies.modalX_axiom` lemmas, exposed with an **explicit-hypothesis
  primary form** (taking the raw `h_refl`/`h_trans`/… the 14 consumers already thread) so consumer
  public signatures stay stable and downstream `Completeness.lean` adapters need no edits; plus
  optional instance-backed forms for new systems.
- **DO NOT build a single unifying typeclass**: classical/birelational/constructive have 3
  incompatible `ValidFC` shapes; only predicate shapes overlap, not soundness theorems. Birelational
  and constructive families are explicitly out of scope.
- **Zero sorry**: each lemma body is a copy of an existing verified inline case (e.g. T's
  `| modalT φ => intro h_box; exact h_box w (h_refl w)`).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (no roadmap flag).

## Goals & Non-Goals

**Goals**:
- Add 5 correspondence lemmas (`Satisfies.modalT_axiom`, `modalFour_axiom`, `modalB_axiom`,
  `modalD_axiom`, `modalFive_axiom`) in one new file, sorry-free and lint-clean.
- Consume existing Std/Foundations classes; define no new frame-property predicates.
- Rewire the 14 `Systems/*/Soundness.lean` frame-axiom cases to single-line `exact` calls while
  keeping `<sys>_axiom_sound` / `<sys>_soundness` public signatures byte-stable.
- Land the multi-file consumer refactor to CI-green; the user posts a Zulip heads-up before the PR.

**Non-Goals**:
- No unifying typeclass across classical + birelational + constructive semantics.
- No changes to birelational (`Minimal/`, `Intuitionistic/`) or constructive (`Constructive/`) FC
  predicates (tracked as separate follow-ups).
- No re-expression of the 14 `Model → Prop` completeness FC predicates (separate follow-up).
- No new frame-property predicate definitions, no `@[simp]` attributes on the new lemmas.
- No PR creation or push (agents mark [PR READY] only; user runs `/pr`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Multi-file consumer refactor lands without library-maintainer alignment (CONTRIBUTING.md:149) | H | M | Design decision resolved (user, 2026-07-18); implementation proceeds to CI-green, but the user posts a Zulip heads-up (Phase 2) before the PR lands. No PR/push is autonomous (pr-prohibition.md). |
| New file not registered in import/build graph → not compiled or unreachable | M | M | Phase 1 wires `FrameCorrespondence` into `Metalogic/Soundness.lean` import and verifies via scoped `lake build` of a downstream consumer + checks any root aggregator glob. |
| Lint failure (docBlame/defLemma/lowerCamelCase/topNamespace) blocks PR | M | M | Follow the sibling `Satisfies.implyK_axiom` convention exactly; docstring every lemma; run `lake lint` in Phase 1. |
| `modalFive`/`modalD` box-neg-bot encodings mismatch the concrete axiom constructor shape | M | M | Phase 1 copies the exact goal shape from an existing consumer inline case (K5/D) and confirms with `lean_goal` before finalizing. |
| S5's inline symmetry derivation complicates its refactor | L | M | Batch S5 into the multi-property batch (Phase 4) with a note to preserve any non-frame-axiom inline derivation untouched. |
| Consumer signature drift breaks downstream `Completeness.lean` adapters | M | L | Keep explicit-hypothesis primary form so `<sys>_axiom_sound` args are unchanged; Phase 5 runs full build to confirm no downstream breakage. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 3, 4 | 1 |
| 3 | 5 | 3, 4 |
| — | 2 (non-blocking pre-PR heads-up) | user, before `/pr` |

Phases within the same wave can execute in parallel. Phase 1 (additive core) is complete. The
public-interface design decision is **resolved** (user, 2026-07-18): explicit-hypothesis primary
signature form, one coherent PR wiring the 14 consumers via one-line delegation. Phases 3-5 are
therefore unblocked and autonomously implementable to CI-green; the remaining Zulip step is a
pre-PR *heads-up* to the modal-logic group (Phase 2), performed by the user before the PR lands —
not a design gate on implementation.

---

### Phase 1: Additive correspondence core (5 lemmas) [COMPLETED]

**Goal**: Add the 5 modal-axiom correspondence lemmas in one new file, wired into the import graph,
sorry-free and lint-clean, changing no existing proof. This phase is **autonomously implementable
and CI-green on its own** — it is the sanctioned split from the gated consumer refactor.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean` with the standard header,
      `module` / `@[expose] public section`, `namespace Cslib.Logic.Modal`, `open Cslib.Logic`,
      `variable {Atom : Type*}`, and `public import Cslib.Logics.Modal.Metalogic.DerivationTree`
      (matching `Metalogic/Soundness.lean`'s imports for `Model`/`Satisfies`/`Proposition`/`Axioms`).
- [x] Add the 5 **explicit-hypothesis primary** lemmas, each body copied from the corresponding
      verified inline case, each with a docstring:
      - `Satisfies.modalT_axiom (m) (h_refl : ∀ w, m.r w w) (w) (φ) : Satisfies m w ((□φ).imp φ)`
        — body: `fun h_box => h_box w (h_refl w)` (copies `T/Soundness.lean` modalT case).
      - `Satisfies.modalFour_axiom (m) (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) (w) (φ)`
        — copies the `S4/K4` modalFour case.
      - `Satisfies.modalB_axiom (m) (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) (w) (φ)`
        — copies the `B` modalB case (`Axioms.AxiomB φ` shape).
      - `Satisfies.modalD_axiom (m) (h_serial : Relation.Serial m.r) (w) (φ)`
        — copies the `D` modalD case (box-neg-bot shape; `Relation.Serial` already imported there).
      - `Satisfies.modalFive_axiom (m) (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) (w) (φ)`
        — copies the `K5` modalFive case (box-neg-bot shape).
- [x] For each lemma, confirm the exact goal-statement shape against the existing consumer inline
      case using `lean_goal` before finalizing (guard against axiom-constructor encoding mismatch).
      *(verified by direct comparison against the T/K4/B/D/K5 `Soundness.lean` inline case bodies
      plus `lean_verify` axiom checks on all 5 lemmas post-build — all report `axioms: []`)*
- [ ] (Optional, per research) add instance-backed sibling forms
      (`[Std.Refl m.r]` / `[IsTrans World m.r]` / `[Std.Symm m.r]` / `[Relation.Serial m.r]` /
      `[Relation.RightEuclidean m.r]`) for new systems; name them so they do not collide with the
      explicit-hypothesis primaries and pass lint. If lint/naming friction arises, defer these to a
      follow-up and keep only the explicit forms — the explicit forms are what the consumers need.
      *(deviation: skipped -- optional per plan text, deferred to avoid lint/naming risk; only the
      5 explicit-hypothesis primaries were landed)*
- [x] Wire the new file into the import graph: add `public import Cslib.Logics.Modal.Metalogic.FrameCorrespondence`
      to `Cslib/Logics/Modal/Metalogic/Soundness.lean` (so all 14 consumers get it transitively),
      and verify the file is reached by any root aggregator/lakefile glob (check `Cslib.lean` or the
      Modal aggregator; add an entry only if the build system requires explicit registration).
      *(added the import line to Soundness.lean and registered `FrameCorrespondence` in `Cslib.lean`
      at its alphabetical position between `DerivationTree` and `GenericMCSBridge`)*

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean` — new file, 5 lemmas (+ optional instance forms).
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` — add one `public import` line.
- (conditional) root aggregator (`Cslib.lean` or Modal import file) — register new module only if required.

**Verification**:
- `mcp__lean-lsp__lean_diagnostic_messages` on `FrameCorrespondence.lean` shows no errors/sorries.
- Scoped `lake build Cslib.Logics.Modal.Metalogic.FrameCorrespondence` succeeds.
- Scoped `lake build` of one downstream consumer (e.g. `...Systems.T.Soundness`) still succeeds
  (import wiring reaches consumers, no regression).
- `lake lint` (or `#lint`) clean for the new lemmas: docBlame, defLemma, lowerCamelCase,
  topNamespace all pass; no `@[simp]` added.
- Zero `sorry` in the new file.

---

### Phase 2: Zulip pre-PR heads-up [IN PROGRESS]

**Goal**: Give the modal-logic working group a courtesy heads-up on the multi-file consumer
refactor before the PR lands. The *design decision is resolved* (user, 2026-07-18): explicit-
hypothesis primary interface, one coherent PR. Per `CONTRIBUTING.md:149`, major development across
a shared, actively-developed subtree is coordinated on Zulip — here that coordination is a pre-PR
heads-up, since the interface choice is settled, not an open design question blocking implementation.

**This heads-up is a user step performed before the PR lands; it does NOT block Phases 3-5.**
Autonomous implementation may proceed to CI-green independently. No PR is created autonomously
(pr-prohibition.md): the user runs `/pr` after posting the heads-up.

**Tasks** (user-performed, before PR lands — not before implementation):
- [ ] Post a Zulip scope heads-up to the modal-logic working group: the axiom⇔property map
      (research §2), the placement decision (new `FrameCorrespondence.lean` imported by
      `Soundness.lean`), the explicit-hypothesis-primary interface choice, and confirmation that the
      §1.2 completeness-FC family and birelational de-duplication are deferred to separate follow-ups.
- [ ] Note the 14-file blast radius and stable-signature approach.

**Timing**: Asynchronous / user-performed (not agent execution time; runs before `/pr`, in parallel
with or after CI-green implementation).

**Depends on**: 1

**Verification**:
- A Zulip heads-up thread exists before the PR lands. (Implementation of Phases 3-5 does not wait
  on it.)

---

### Phase 3: Consumer refactor — single-property systems [COMPLETED]

**Goal**: Rewire the 5 single-frame-property systems' `<sys>_axiom_sound` modal cases to single-line
`exact` calls into the Phase 1 lemmas, keeping public signatures byte-stable.

**Tasks**:
- [x] `Systems/T/Soundness.lean` — `| modalT φ => exact Satisfies.modalT_axiom m h_refl w φ`.
- [x] `Systems/B/Soundness.lean` — `| modalB φ => exact Satisfies.modalB_axiom m h_symm w φ`.
- [x] `Systems/D/Soundness.lean` — `| modalD φ => exact Satisfies.modalD_axiom m h_serial w φ`.
- [x] `Systems/K4/Soundness.lean` — `| modalFour φ => exact Satisfies.modalFour_axiom m h_trans w φ`.
- [x] `Systems/K5/Soundness.lean` — `| modalFive φ => exact Satisfies.modalFive_axiom m h_eucl w φ`.
- [x] Confirm each `<sys>_axiom_sound` / `<sys>_soundness` signature (and threaded hypothesis names)
      is unchanged. *(verified via `git diff` — only modal case bodies changed, signatures byte-identical)*

**Timing**: ~1 hour

**Depends on**: 1 (Phase 2 is a non-blocking pre-PR heads-up)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/{T,B,D,K4,K5}/Soundness.lean` — one modal case each.

**Verification**:
- Scoped `lake build` of each of the 5 modules succeeds.
- `git diff` shows only the modal case bodies changed; signatures identical.
- Zero `sorry`.

---

### Phase 4: Consumer refactor — multi-property systems [COMPLETED]

**Goal**: Rewire the 9 multi-frame-property systems' modal cases to `exact` the Phase 1 lemmas,
keeping signatures byte-stable. Runs in parallel with Phase 3 (disjoint file sets).

**Tasks**:
- [x] `Systems/S4/Soundness.lean` — modalT→`h_refl`, modalFour→`h_trans`.
- [x] `Systems/S5/Soundness.lean` — modalT→`h_refl`, modalFour→`h_trans`, modalFive→`h_eucl`;
      **preserve any inline symmetry derivation** (non-frame-axiom logic) untouched.
      *(confirmed: S5's modalB case, which derives symmetry from h_eucl+h_refl inline, was left
      untouched — only modalT and modalFour were rewired to the FrameCorrespondence lemmas)*
- [x] `Systems/K45/Soundness.lean` — modalFour→`h_trans`, modalFive→`h_eucl`.
- [x] `Systems/KB5/Soundness.lean` — modalB→`h_symm`, modalFive→`h_eucl`.
- [x] `Systems/D4/Soundness.lean` — modalD→`h_serial`, modalFour→`h_trans`.
- [x] `Systems/D5/Soundness.lean` — modalD→`h_serial`, modalFive→`h_eucl`.
- [x] `Systems/D45/Soundness.lean` — modalD→`h_serial`, modalFour→`h_trans`, modalFive→`h_eucl`.
- [x] `Systems/DB/Soundness.lean` — modalD→`h_serial`, modalB→`h_symm`.
- [x] `Systems/TB/Soundness.lean` — modalT→`h_refl`, modalB→`h_symm`.

**Timing**: ~1.5 hours

**Depends on**: 1 (Phase 2 is a non-blocking pre-PR heads-up)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/{S4,S5,K45,KB5,D4,D5,D45,DB,TB}/Soundness.lean`.

**Verification**:
- Scoped `lake build` of each of the 9 modules succeeds.
- `git diff` shows only modal case bodies changed; signatures identical; S5 inline symmetry
  derivation intact.
- Zero `sorry`.

---

### Phase 5: Full verification and PR preparation [NOT STARTED]

**Goal**: Confirm the whole change set builds and lints cleanly end-to-end, then hand off for PR.

**Tasks**:
- [ ] Full `lake build` (all modal metalogic + downstream) succeeds with no regressions.
- [ ] `lake lint` clean across the new file and all 14 refactored files.
- [ ] Confirm no `Completeness.lean` adapter (`<sys>_sound_cb`) required a change (downstream stable).
- [ ] Confirm total `sorry` count unchanged (zero introduced).
- [ ] Prepare PR description (axiom⇔property map, placement, blast radius, Zulip thread link);
      transition task to [PR READY]. Do NOT create the PR or push (user runs `/pr`).

**Timing**: ~1 hour

**Depends on**: 3, 4

**Files to modify**:
- `specs/522_uniform_frame_condition_axiom_correspondence_library/pr-description.md` (if pr flow).

**Verification**:
- `lake build` and `lake lint` both green repo-wide for the touched subtree.
- Grep confirms zero new `sorry`.
- Task marked [PR READY].

## Testing & Validation

- [ ] `FrameCorrespondence.lean` compiles sorry-free (Phase 1).
- [ ] `lake lint` clean for the 5 new lemmas: docBlame, defLemma, lowerCamelCase, topNamespace (Phase 1).
- [ ] Import wiring verified via a downstream consumer build (Phase 1).
- [ ] Each of the 14 refactored consumer modules builds scoped-green (Phases 3-4).
- [ ] Public signatures of all `<sys>_axiom_sound` / `<sys>_soundness` unchanged (Phases 3-4).
- [ ] Full `lake build` + `lake lint` green; downstream `Completeness.lean` untouched (Phase 5).
- [ ] Zero `sorry` introduced anywhere.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean` (new; 5 correspondence lemmas).
- Edited: `Cslib/Logics/Modal/Metalogic/Soundness.lean` (import line).
- Edited (gated): 14 `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean` files.
- `specs/522_uniform_frame_condition_axiom_correspondence_library/summaries/01_frame-correspondence-library-summary.md` (on implementation).
- (gated) `pr-description.md` for the multi-file PR.

## Rollback/Contingency

- **Phase 1 additive core is isolated**: if the new file or import wiring causes any regression,
  revert the single `public import` line in `Soundness.lean` and delete `FrameCorrespondence.lean`;
  no existing proof depends on it, so the tree returns to its prior green state.
- **Consumer refactor (Phases 3-4)** is per-file and mechanical: if any `<sys>/Soundness.lean` fails
  to build, revert that one file to its inline case (the original body is preserved in git) and
  continue with the others; the additive core remains valid independently.
- **If maintainers object on the pre-PR heads-up**, ship Phase 1 alone as a standalone additive PR
  (research §5: additive-only core is a straightforward, low-risk PR) and leave the consumer
  refactor for a later coordinated change. (The design decision is resolved, so this is a
  fallback-on-objection, not the expected path.)
