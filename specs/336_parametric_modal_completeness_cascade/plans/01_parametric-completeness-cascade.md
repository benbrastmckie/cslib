# Implementation Plan: Task #336 - Parametric Modal Completeness Cascade

- **Task**: 336 - Parametric modal completeness cascade
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours
- **Dependencies**: Task 335 (soundness refactor) — complete
- **Research Inputs**: specs/336_parametric_modal_completeness_cascade/reports/01_parametric-completeness-cascade.md
- **Artifacts**: plans/01_parametric-completeness-cascade.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Current State (verified 2026-06-24)

Snapshot after the orchestrated implementation run whose agent overflowed its context
mid-Phase-5. Verified against committed history + working tree + `lake build`:

| Phase | Plan marker | Verified reality |
|-------|-------------|------------------|
| 1 — parametric core | COMPLETED | ✅ committed (`3098ec2b`), parametric `strong_soundness`/`strong_completeness` in `Metalogic/Completeness.lean` |
| 2 — wrappers + K | COMPLETED | ✅ committed (`86a7e238`), K cascade delegates; 5 K names preserved |
| 3 — T-family (T, S4, S5, TB) | COMPLETED | ✅ committed (`97126905`), all 4 delegated |
| 4 — K-family (B, K4, K5, K45, KB5) | COMPLETED | ✅ committed (`d64b8331`), all 5 delegated |
| 5 — D-family (D, D4, D5, D45, DB) | PARTIAL | ⚠️ **incomplete** — see below |
| 6 — full CI + line audit | NOT STARTED | ❌ not started |

**Phase 5 per-system status:**
- `D` — ✅ delegated, **builds green**, but **uncommitted**.
- `D4` — ⚠️ delegated but **BROKEN**: syntax error at `Systems/D4/Completeness.lean:57:7`
  (`unexpected token 'fun'`) in `d4_canonical_FC`; agent died mid-edit. **Uncommitted.**
- `D5` — ❌ not started (original full-cascade proof, 187 lines).
- `D45` — ❌ not started (original, 205 lines).
- `DB` — ❌ not started (original, 190 lines).

**What was missed (remaining work to reach Definition of Done):**
1. Fix `D4` syntax error and verify `D4` builds green.
2. Refactor `D5`, `D45`, `DB` to thin parametric instantiations (using `d_truth_lemma`).
3. Commit Phase 5 (`task 336 phase 5: D-family completeness cascade delegation`).
4. Execute Phase 6 in full: `lake build` (full tree + Bimodal `ModalConservativity` consumer),
   `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`; grep-confirm
   all 75 public cascade theorem names; record net line reduction.

## Overview

The 15 `Systems/*/Completeness.lean` files (3,205 lines) each carry a mechanically
identical five-theorem "completeness cascade" (`*_strong_soundness`,
`*_strong_completeness`, `*_strong_completeness_iff`, `*_compactness`,
`*_completeness`) differing only in (a) axiom-constructor callbacks, (b) truth-lemma
variant (`truth_lemma` / `k_truth_lemma` / `d_truth_lemma`), and (c) frame-condition
hypotheses. This plan adds a single parametric cascade (5 generic theorems) to
`Metalogic/Completeness.lean`, parameterized over `Axioms`, the frame-class predicate
`FC` (via the existing-but-underused `ModalSemanticEntails`), the four propositional-axiom
callbacks, a pre-applied `truthLemma`, and a `canonical_FC` proof; then refactors all 15
systems to thin instantiations. K's cascade tail (`K/Completeness.lean:268-365`) is the
ready-made template — it already uses `ModalSemanticEntails (fun _ => True)`. **Definition
of done**: full `lake build` green, CI clean (test, checkInitImports, lint-style, shake),
zero `sorry`, no public signature break for downstream consumers, ~1,200-1,500 lines net
reduction.

### Research Integration

Key findings from `reports/01_parametric-completeness-cascade.md` incorporated:
- The parametric theorems go in `Metalogic/Completeness.lean` after
  `ModalSemanticEntails_of_Valid`. The new `strong_completeness` body is K's
  `Completeness.lean:286-323` with `k_truth_lemma … w` → `truthLemma w` and `True.intro`
  → `canonical_FC` (Section 7.2).
- Three truth-lemma families (T / K / D) all reduce to the same result type once applied
  to their axiom callbacks, so the cascade accepts one pre-applied `truthLemma` and is
  family-agnostic (Section 3).
- `strong_soundness` threads each per-system 335 `*_soundness` via a thin FC-destructuring
  adapter `fun m hFC => <sys>_soundness …` (Section 7.1, planner flag 2).
- Unify all systems on `ModalSemanticEntails FC` — the single largest line-saving move
  (Section 4). Frame conditions become a per-system `<sys>FC` predicate.
- Pure plumbing, no Mathlib lemmas needed, no `sorry` risk (Section 6, 9).

### Prior Plan Reference

No prior plan for task 336. Effort is calibrated against the now-complete task 335
soundness refactor, which validated this exact "shared parametric core + per-system thin
delegation" structure for the soundness leg. The 335 `*_soundness` theorems are reused
directly as callbacks here.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; ROADMAP.md not consulted. No roadmap
phases added.

## Goals & Non-Goals

**Goals**:
- Add 5 parametric cascade theorems to `Metalogic/Completeness.lean`, generic over
  `Axioms`, `FC`, axiom callbacks, `truthLemma`, and `canonical_FC`.
- Refactor all 15 `Systems/*/Completeness.lean` cascade tails to thin instantiations.
- Preserve K's and D's unique truth-lemma infra (`k_*` / `d_*` definitions); replace only
  their cascade tails (K:262-367, D:339-467).
- Achieve ~1,200-1,500 lines net reduction with full CI green and zero `sorry`.
- Preserve all public theorem signatures that have external consumers (see Risks).

**Non-Goals**:
- No change to truth-lemma machinery, canonical-model construction, or `ModalSemanticEntails`
  definition itself.
- No new Mathlib dependencies; no changes to `InterSystem/` or `ProofSystem/Instances/`.
- No refactor of the soundness leg (done in 335).
- No change to the K-family / D-family `import` structure (B/K4/… still import K's infra;
  D4/D5/… still import D's infra).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Switching public `*_completeness` signatures to `ModalSemanticEntails FC` breaks downstream consumers. **Confirmed**: `s5_completeness` is consumed by `Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean:209` (`apply s5_completeness`) with the current inlined-`∀` weak signature. | H | H (confirmed) | Keep the weak `*_completeness` public theorems with their **current inlined-∀ signatures** as the stable public API. Internally they delegate to the parametric cascade via `ModalSemanticEntails_of_Valid`. The parametric `strong_*` theorems become internal plumbing, not signature replacements. Build-verify `ModalConservativity.lean` in Phase 6. |
| FC-shape mismatch when threading per-system `*_soundness` into parametric `strong_soundness`. | M | M | Thin per-system adapter `fun m hFC => <sys>_soundness d m <destructured hFC> w …`; `<sys>FC` def chosen so destructuring is a trivial `obtain ⟨…⟩ := hFC`. K (`fun _ => True`) needs no destructuring. |
| Lint failures on new `<sys>FC` defs (docBlame, lowerCamelCase, topNamespace). | M | M | Add docstrings, use lowerCamelCase (`s5FC`, `tFC`), place inside `Cslib.Logic.Modal` namespace; mirror existing Completeness.lean section discipline; run `lint-style` per phase. |
| `unusedSectionVars` on universe `u` / `variable {Atom}` in the new parametric block. | L | M | Mirror the existing `Metalogic/Completeness.lean` section variable discipline; verify with `lake build` in Phase 1. |
| Net line reduction falls short of the ~1,200-1,500 target. | L | L | Unifying on `ModalSemanticEntails` removes per-system quantifier prose across all five theorems (largest source per research §4); measure with `wc -l` in Phase 6 and report. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4, 5 | 2 |
| 4 | 6 | 3, 4, 5 |

Phases within the same wave can execute in parallel. Phases 3, 4, 5 (the three
truth-lemma families) are independent once the parametric core (Phases 1-2) is proven
against K, and may be dispatched in parallel with file-ownership territory per family.

---

### Phase 1: Parametric core — strong_soundness + strong_completeness [COMPLETED]

**Goal**: Add the two load-bearing parametric theorems to `Metalogic/Completeness.lean`
and prove them by re-instantiating against K (in-place sanity, not yet replacing K's tail).

**Tasks**:
- [ ] Read `Metalogic/Completeness.lean:465-471` (`ModalSemanticEntails`,
  `ModalSemanticEntails_of_Valid`) and K's cascade `Systems/K/Completeness.lean:268-323`
  to confirm exact lemma names and section-variable discipline.
- [ ] Add parametric `strong_soundness {Axioms} {FC} {Γ} {φ}` taking a soundness callback
  `(sound : ∀ {World} (m : Model World Atom) (w), FC m → ModalSetDerivable … → (∀ γ ∈ Γ, Satisfies m w γ) → Satisfies m w φ)` returning `ModalSemanticEntails FC Γ φ`.
- [ ] Add parametric `strong_completeness {Axioms} {FC} {Γ} {φ}` with params
  `(h_implyK)(h_implyS)(h_efq)(h_peirce)`, `(truthLemma : ∀ S φ, Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)`, `(canonical_FC : FC (CanonicalModel Axioms))`, hypothesis `(h : ModalSemanticEntails FC Γ φ)`, returning `ModalSetDerivable Axioms Γ φ`. Body = K:286-323 with `k_truth_lemma … w` → `truthLemma w`, `True.intro` → `canonical_FC`.
- [ ] Add docstrings; use `theorem` (Prop-valued, avoid defLemma); place in
  `Cslib.Logic.Modal` namespace; mirror section-variable discipline (`unusedSectionVars`).
- [ ] Temporarily instantiate against K inline (scratch) to confirm typecheck before Phase 2.

**Timing**: ~2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` — add 2 parametric theorems after
  `ModalSemanticEntails_of_Valid`.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Completeness` succeeds, zero `sorry`.
- `lake exe lint-style` clean on the modified file.

---

### Phase 2: Parametric wrappers + K instantiation [COMPLETED]

**Goal**: Add the three thin parametric wrappers and convert K's cascade tail to the
parametric instantiation, proving the full pattern end-to-end on K.

**Tasks**:
- [ ] Add parametric `strong_completeness_iff`, `compactness`, `weak_completeness` to
  `Metalogic/Completeness.lean` (thin wrappers, generic over the same params; pattern =
  K:330-365).
- [ ] In `Systems/K/Completeness.lean`, replace the cascade tail (lines ~262-367) with
  five thin delegations to the parametric cascade: define `kFC := fun _ => True`,
  `k_canonical_FC : kFC (CanonicalModel (@KAxiom Atom)) := trivial`, pre-apply
  `k_truth_lemma` to its axiom callbacks, thread `k_soundness` via the adapter.
- [ ] **Preserve K's public theorem names** (`k_strong_soundness`, `k_strong_completeness`,
  `k_strong_completeness_iff`, `k_compactness`, `k_completeness`) and their signatures —
  bodies become one-line delegations.
- [ ] Keep K's unique truth-lemma infra (`k_derive_box_from_inconsistency`,
  `k_mcs_box_witness`, `k_truth_lemma`) untouched.

**Timing**: ~1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` — add 3 wrapper theorems.
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` — replace cascade tail.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Systems.K.Completeness` succeeds, zero `sorry`.
- K public theorem names unchanged (grep confirms five `theorem k_*` still present).
- `lake exe lint-style` clean.

---

### Phase 3: Refactor T-family (T, S4, S5, TB) [COMPLETED]

**Goal**: Instantiate the parametric cascade for the four T-family systems using
`truth_lemma` (from `Metalogic/Completeness.lean`), preserving public weak-completeness
signatures.

**Tasks**:
- [ ] For each of T, S4, S5, TB: define `<sys>FC` (refl; refl+trans; refl+trans+eucl;
  refl+symm) with docstring + lowerCamelCase; prove `<sys>_canonical_FC` from
  `canonical_refl`/`canonical_trans`/`canonical_eucl`/`canonical_symm` callbacks.
- [ ] Replace each system's cascade tail with thin delegations, pre-applying `truth_lemma`
  to its axiom callbacks (incl. `h_T`) and threading `<sys>_soundness` via the FC-destructuring
  adapter.
- [ ] **Preserve the public weak `*_completeness` signature for S5** (inlined-∀ form) —
  required by `Bimodal/.../ModalConservativity.lean`. The weak theorem delegates internally
  via `ModalSemanticEntails_of_Valid`. Apply the same signature-preservation discipline to
  T/S4/TB weak `*_completeness` for consistency.
- [ ] Confirm `s5_completeness` still accepts `apply` with refl/trans/eucl hypotheses.

**Timing**: ~2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/{T,S4,S5,TB}/Completeness.lean`

**Verification**:
- `lake build` for each T-family Completeness module succeeds, zero `sorry`.
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity`
  succeeds (S5 consumer intact).
- `lake exe lint-style` clean.

---

### Phase 4: Refactor K-family (B, K4, K5, K45, KB5) [COMPLETED]

**Goal**: Instantiate the parametric cascade for the five K-family systems using
`k_truth_lemma` (imported from `Systems/K`).

**Tasks**:
- [ ] For each of B, K4, K5, K45, KB5: define `<sys>FC` (symm; trans; eucl; trans+eucl;
  symm+eucl) with docstring; prove `<sys>_canonical_FC` from
  `canonical_symm`/`canonical_trans`/`canonical_eucl_from_5` callbacks.
- [ ] Replace each cascade tail with thin delegations, pre-applying `k_truth_lemma` and
  threading `<sys>_soundness` via the adapter.
- [ ] Preserve public theorem names and weak `*_completeness` inlined-∀ signatures.
- [ ] Keep each file's `import` of K's truth-lemma infra unchanged.

**Timing**: ~1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/{B,K4,K5,K45,KB5}/Completeness.lean`

**Verification**:
- `lake build` for each K-family Completeness module succeeds, zero `sorry`.
- `lake exe lint-style` clean.

---

### Phase 5: Refactor D-family (D, D4, D5, D45, DB) [COMPLETED]

**Goal**: Instantiate the parametric cascade for the five D-family systems using
`d_truth_lemma`, including replacing D's own cascade tail while preserving D's truth-lemma
infra.

**Status note (2026-06-24)**: D done (green, uncommitted); D4 attempted but broken
(syntax error at line 57); D5/D45/DB not started. See "Current State" section at top.

**Tasks**:
- [x] In `Systems/D/Completeness.lean`, replace only the cascade tail (lines ~339-467);
  keep `d_canonical_serial`, `d_mcs_box_witness`, `d_truth_lemma`. (D builds green; uncommitted.)
- [~] For each of D, D4, D5, D45, DB: define `<sys>FC` (serial; serial+trans; serial+eucl;
  serial+trans+eucl; serial+symm) with docstring (uses `Relation.Serial`); prove
  `<sys>_canonical_FC` from `d_canonical_serial` + `canonical_trans`/`canonical_eucl_from_5`/
  `canonical_symm`. (Done: D. Broken: D4. Not started: D5, D45, DB.)
- [~] Replace each cascade tail with thin delegations, pre-applying `d_truth_lemma` (incl.
  `h_D`) and threading `<sys>_soundness` via the adapter. (Done: D. Broken: D4. Not started: D5, D45, DB.)
- [ ] Preserve public theorem names and weak `*_completeness` inlined-∀ signatures.
- [ ] **REMAINING**: fix D4 `d4_canonical_FC` syntax error; refactor D5, D45, DB; commit Phase 5.

**Timing**: ~1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/{D,D4,D5,D45,DB}/Completeness.lean`

**Verification**:
- `lake build` for each D-family Completeness module succeeds, zero `sorry`.
- `lake exe lint-style` clean.

---

### Phase 6: Full build, CI pipeline, and line-reduction audit [COMPLETED]

**Goal**: Run the full CSLib CI pipeline, confirm no signature break anywhere, and record
the net line reduction.

**Tasks**:
- [ ] `lake build` (full) — entire Modal tree + Bimodal consumer green, zero `sorry`.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — Cslib.Init imports verified.
- [ ] `lake exe lint-style` — style clean across all 16 modified files.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — dependency analysis; remove
  any now-unused imports surfaced by the refactor.
- [ ] Grep-confirm all 75 public cascade theorem names (`*_strong_soundness`,
  `*_strong_completeness`, `*_strong_completeness_iff`, `*_compactness`, `*_completeness`)
  are still declared (no accidental rename/removal).
- [ ] `wc -l` before/after across the 15 Systems files + `Metalogic/Completeness.lean`;
  confirm net reduction in the ~1,200-1,500 line target band; record the number.

**Timing**: ~0.5 hours

**Depends on**: 3, 4, 5

**Files to modify**: none (verification + minor import cleanup only)

**Verification**:
- All five CI commands exit 0.
- Net line delta recorded and within target band.
- No `sorry`, no public signature break (Bimodal `ModalConservativity` builds).

---

## Testing & Validation

- [ ] `lake build` full tree succeeds with zero `sorry`.
- [ ] `lake test` passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes (docstrings on new `<sys>FC` defs, lowerCamelCase,
  topNamespace).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (no stale imports).
- [ ] `Bimodal/.../ModalConservativity.lean` builds (S5 weak-completeness consumer intact).
- [ ] All 75 public cascade theorem names still declared.
- [ ] Net line reduction in ~1,200-1,500 band, recorded in summary.

## Artifacts & Outputs

- `plans/01_parametric-completeness-cascade.md` (this file)
- Modified: `Cslib/Logics/Modal/Metalogic/Completeness.lean` (+5 parametric theorems)
- Modified: `Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean` (15 files, cascade
  tails replaced with thin instantiations)
- `summaries/01_parametric-completeness-cascade-summary.md` (on completion)

## Rollback/Contingency

- Work on a feature branch; each phase is an atomic commit (`task 336 phase P: …`).
- If a per-system instantiation fails to typecheck, the research confirms it indicates an
  FC-shape mismatch (resolvable by adapter), **not** a `sorry` situation — do not introduce
  `sorry`; fix the adapter.
- If signature normalization is attempted and breaks a consumer, revert that system's weak
  `*_completeness` to the inlined-∀ public signature (the mandated approach) and keep only
  the internal delegation change.
- Full revert: `git revert` the phase commits; the parametric additions in
  `Metalogic/Completeness.lean` are additive and harmless if systems are reverted.
