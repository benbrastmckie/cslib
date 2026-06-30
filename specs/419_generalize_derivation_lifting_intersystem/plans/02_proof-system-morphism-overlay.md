# Implementation Plan: Task #419 — Morphism-of-Proof-Systems Unification (A1 Foundations overlay)

- **Task**: 419 - Generalize derivation lifting to a cross-logic layer (virtuous unification, realization A1)
- **Status**: [NOT STARTED]
- **Effort**: 16 hours (6 phases; P5 is the long pole)
- **Dependencies**: 417 (Foundations placement, soft — `ConservativityLift.lean` already landed)
- **Research Inputs**:
  - reports/02_virtuous-unification.md (primary — design, A1 vs A2 vs A3, source evidence, phase spine §7)
  - reports/01_derivation-lifting-spike.md (round-1 obstacles A1 must clear; verdict superseded)
- **Artifacts**: plans/02_proof-system-morphism-overlay.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md; ORGANISATION.md; NOTATION.md
- **Type**: cslib
- **Lean Intent**: false
- **Mode**: hard (strict phase sizing, per-phase file territory, Non-Goals, Risks/Rollback)

## Overview

Build the **non-invasive Foundations overlay (realization A1)** that expresses every existing
CSLib derivation lift as the functorial action `Deriv.map` of a **morphism of proof systems**
`ProofSigHom σ₁ σ₂`. A new Foundations file defines a generic branching derivation type `Deriv`
over a rule signature `ProofSig` (hand-built, since Mathlib ships no indexed free-multicategory),
the morphism `ProofSigHom` (formula map `g` respecting `imp` + a **Type-valued** axiom-family
morphism `∀ φ, Ax₁ φ → Ax₂ (g φ)` + closure-operator coherence `g (m φ) = m' (g φ)`), and the
functor `Deriv.map`. For each of the four existing lifts (Modal `liftDerivation`/`Derivable_mono`,
PL `liftDerivationTree`, Bimodal frame-monotone `DerivationTree.lift`, and Bimodal
`liftDerivationWith`) a constructor-preserving equivalence exhibits the lift as a `Deriv.map`
corollary **without modifying the 190+ downstream proof files** that pattern-match on the existing
`DerivationTree` inductives.

Adoption is gated behind an **A3 PL pilot first** (prove the PL lift as a `Deriv.map` corollary
before wiring Modal/Bimodal), so each phase is independently CI-green and reversible. This is
explicitly **NOT** A2 (replace the three inductives, 193 files touched). **Definition of done**:
all four lifts factor through `Deriv.map`; full `lake build` green; **0 new `sorry`, 0 new
`axiom`, 0 vacuous defs** throughout.

### Research Integration

- **Report 02 (primary)** supplies the full design: the `ProofSig`/`Deriv`/`ProofSigHom`/`Deriv.map`
  signature (§3), the source-to-instance mapping for all four lifts (§2 table), the verified
  coherence evidence (`liftFormula_imp` definitional at `Lifting.lean:571`; `liftFormula_swapTemporal`
  propositional `▸` at `Lifting.lean:576`), the A1-vs-A2-vs-A3 cost/benefit (§6), and the phase
  spine P1–P5 (§7). This plan adopts §7's frame-lift-before-cross-syntax ordering and splits the
  combined report-P4 into two hard-mode-sized phases (Phase 4 frame, Phase 5 cross-syntax).
- **Report 01 (superseded verdict, live facts)** enumerates the three obstacles A1 must clear:
  (1) parameterization-axis mismatch, (2) "Bimodal has no axiom predicate", (3) three formula
  types / constructor sets. Report 02 dissolves each (axiom **family** not **predicate**;
  `Deriv.map` parametric in `F`; freshness orthogonal). The plan honors the resolutions as hard
  acceptance constraints (see Risks).

### Prior Plan Reference

No prior plan exists in `plans/` (this is the first plan for task 419). Round-1 spike recommended
`[BLOCKED]`; round-2 deep re-investigation refuted it. Effort calibration therefore comes from the
report's per-phase line estimates (P1 ~120–160, P2 ~60–100) and the §6 caveat that each
equivalence costs ~3–4× one lift body.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (`roadmap_flag` not set). Task 419 was spawned from the
task-415 lifting audit (Rank 4) and advances the "structure-first" propositional/modal lifting
vision: a single reusable "morphism of proof systems" Foundations layer.

## Goals & Non-Goals

**Goals**:
- Author one self-contained Foundations file `ProofSystemMorphism.lean` defining `ProofSig`,
  `Deriv`, `ProofSigHom`, `Deriv.map`, plus the generic functor laws (`map_id`, `map_comp`,
  height preservation) proved once and reused by every logic.
- Exhibit each of the four existing lifts as a `Deriv.map` corollary via a constructor-preserving
  definitional equivalence, in a **new per-logic file each**, leaving the existing lift defs and
  all downstream proofs untouched.
- Keep Bimodal's axiom family **Type-valued** (`Ax := fun φ => {h : Axiom φ // h.minFrameClass ≤ fc}`);
  reuse existing `liftFormula_imp`, `liftFormula_swapTemporal`, `liftAxiom`,
  `liftAxiom_preserves_minFrameClass` verbatim as morphism fields.
- Maintain a per-phase invariant: independently buildable and `sorry`/`axiom`-free, or the phase is
  reported `[BLOCKED]` (never papered over).

**Non-Goals**:
- **A2 (maximal unification) is an explicit Non-Goal.** Do NOT replace the three per-logic
  `DerivationTree` inductives by `Deriv σ`. That touches 193 files (Modal 55, Bimodal 69, PL 38,
  Temporal 28), migrates 79 Bimodal + 23 Modal constructor-match sites to list-membership rule
  dispatch, and degrades soundness/completeness/canonical-model inductions — ergonomic regression
  with no proof-side payoff.
- Do NOT predicate-ify Bimodal's `Axiom` (do NOT replace `Axiom : Formula → Type u` by
  `Formula → Prop`): it erases the constructor data `liftAxiom`/`liftAxiom_preserves_minFrameClass`
  require and breaks `liftDerivationWith`.
- Do NOT modify any of the four existing lift definitions or any downstream proof file that
  pattern-matches on the existing inductives. The overlay is additive only.
- **Line-count reduction is NOT a goal.** The honest caveat (report §6, §8 item 4): A1 unifies
  *concept + reusable metatheory*, not LOC — each equivalence is ~3–4× one lift body. The payoff
  is a documented, reusable "morphism of proof systems" layer, not fewer lines.
- Do NOT add a `references.bib` BibKey: the abstraction is category-theory folklore (Lawvere
  functorial semantics / Lambek–Scott free-category proof theory); it transcribes Mathlib/CT
  patterns, not a specific paper.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `Deriv.map` `▸` rewrites (`g_imp`, `clMap` coherence) do not typecheck cleanly in the generic setting | H | M | Mirror the existing lift bodies: the Bimodal `mp` arm typechecks with **no** `▸` (imp-hom is definitional), the duality arm uses one `▸`. Keep `g_imp`/`clMap` as `Eq` fields so `▸` mirrors source. If the indexed `Deriv` makes `▸` rebinds painful, use `Eq.mpr`/`cast` with the same equalities. |
| Bimodal cross-syntax equivalence (P5) costs more than re-deriving `liftDerivationWith` directly | M | M | **Descope path (pre-authorized):** descope P5 to "frame lift only" (Phase 4) and leave the unembedding as a *documented by-hand `ProofSigHom` instance* of the same shape — still delivers the unification claim without forcing the equivalence. P5 is independently revertible (its own file). |
| Hand-built indexed `Deriv` inductive triggers Lean universe / positivity / `match`-completeness issues | H | M | Keep `Ax : F → Type` (not `Type*` gymnastics); model `close` with `Γ = []` and `weak` with `Γ ⊆ Δ` exactly as the existing inductives do (they compile, proving Lean accepts the recursion). Build the file in isolation (Phase 1 gate) before any instance work. |
| Predicate-ifying Bimodal by reflex (round-1 framing) | H | L | Non-Goal pinned; Phase 4 uses the Type-valued subtype family. Acceptance check greps the new Bimodal file for `Prop` axiom families. |
| New file not registered in `Cslib.lean` → CI `checkInitImports` / build miss | M | M | Each phase's territory includes the `Cslib.lean` import line; run `lake exe checkInitImports` in every phase gate. |
| Equivalence accidentally forces an edit to a downstream proof | M | L | Territory contracts mark all existing lift/downstream files **READ-ONLY**; corollaries live in new files. If an edit seems required, STOP and report (do not modify). |
| `Deriv.map` introduces `noncomputable`/`sorry` to close round-trip proofs | H | L | Zero-debt gate every phase: `grep -rn "sorry\|admit" <new files>` must be empty; `lean_verify` axiom check on the headline decl of each phase. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 4 |
| 4 | 6 | 2, 3, 5 |

Phases within the same wave can execute in parallel (disjoint file territories). Phase 5 reuses the
Bimodal `ProofSig` (Type-valued axiom family + 3 closures) authored in Phase 4, so it follows 4.
Phase 6 (full-tree CI + audit) depends on every instance phase.

---

### Phase 1: Foundations — `ProofSig`, `Deriv`, `ProofSigHom`, `Deriv.map` + functor laws [IN PROGRESS]

**Goal**: Author the self-contained generic layer. Builds in isolation; no logic instance yet.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean`.
- [ ] Define `ProofSig (F) [HasImp F]` with `Ax : F → Type` and `closures : List (F → F)`.
- [ ] Define the indexed inductive `Deriv (σ : ProofSig F) : List F → F → Type _` with constructors
      `ax`, `assum`, `mp`, `close` (`Γ = []` → `m φ`), `weak` (`Γ ⊆ Δ`) per report §3.
- [ ] Define `ProofSigHom σ₁ σ₂` with fields `g`, `g_imp`, `axMap : ∀ φ, σ₁.Ax φ → σ₂.Ax (g φ)`,
      `clMap` (closure coherence `∃ m', m' ∈ σ₂.closures ∧ ∀ φ, g (m φ) = m' (g φ)`).
- [ ] Define `Deriv.map (H : ProofSigHom σ₁ σ₂) : Deriv σ₁ Γ φ → Deriv σ₂ (Γ.map H.g) (H.g φ)`
      by structural recursion (report §3 body); mirror the `▸` placement from the source lift arms.
- [ ] Prove the generic functor laws: `Deriv.map_id`, `Deriv.map_comp`, and `height` preservation
      (`Deriv.height` + `Deriv.map_height`).
- [ ] Add `ProofSigHom.id` and `ProofSigHom.comp` (needed for `map_comp`).
- [ ] Register the new module: add the `import Cslib.Foundations.Logic.Metalogic.ProofSystemMorphism`
      line to `Cslib.lean` (alphabetical position among Foundations imports).
- [ ] Module docstring framing the abstraction (Lawvere functorial semantics / Lambek–Scott; cite
      Mathlib precedents `FirstOrder.Language.LHom`, `CategoryTheory.Cat.freeMap` as analogues).

**Timing**: ~3 hours (~120–160 lines).

**Depends on**: none

**File territory**:
- CREATE (owned): `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean`
- EDIT (owned): `Cslib.lean` (single import line only)
- READ-ONLY: existing `Cslib/Foundations/Logic/Metalogic/*` (for `HasImp` / style reference)

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.ProofSystemMorphism` green in isolation.
- `Deriv.map`, `map_id`, `map_comp` typecheck `sorry`-free; `lean_verify` shows no new axioms.
- `grep -n "sorry\|admit\|noncomputable" ProofSystemMorphism.lean` empty (or `noncomputable`
  justified and confined).
- `lake exe checkInitImports` passes.

---

### Phase 2: PL pilot (A3) — equivalence + `liftDerivationTree`/`derivable_mono` corollaries [IN PROGRESS]

**Goal**: Prove the abstraction earns its keep on the smallest logic (no closures) before Modal/Bimodal.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/LiftViaMorphism.lean`.
- [ ] Define `plSig (Ax) : ProofSig PL.Proposition` with `closures = ∅`.
- [ ] Define the constructor-preserving equivalence `plEquiv : PL.DerivationTree Ax Γ φ ≃ Deriv (plSig Ax) Γ φ`
      (forward + backward recursion + two round-trip proofs). Add `@[match_pattern]` shims if needed.
- [ ] Define `plHom : ProofSigHom (plSig A₁) (plSig A₂)` from `h_sub : ∀ ψ, A₁ ψ → A₂ ψ`
      (`g = id`, `g_imp = rfl`, `axMap = h_sub`, `clMap` vacuous).
- [ ] Re-derive `liftDerivationTree` as `plEquiv.symm ∘ Deriv.map plHom ∘ plEquiv`; prove a theorem
      that it agrees with the existing `liftDerivationTree`.
- [ ] Re-prove `derivable_mono` as a corollary of `Deriv.map plHom`.
- [ ] Register import in `Cslib.lean`.

**Timing**: ~2.5 hours (~60–100 lines).

**Depends on**: 1

**File territory**:
- CREATE (owned): `Cslib/Logics/Propositional/Semantics/Algebra/LiftViaMorphism.lean`
- EDIT (owned): `Cslib.lean` (single import line)
- READ-ONLY: `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` (existing
  `liftDerivationTree`:59, `derivable_mono`) — must NOT be modified.

**Verification**:
- `lake build` of the new file + `ConjImpConservative` green; `ConjImpConservative.lean` unchanged
  (`git diff --stat` shows only the new file + `Cslib.lean`).
- `derivable_mono` re-proved via `Deriv.map`; agreement theorem `sorry`-free.
- Zero-debt grep + `lean_verify` on the corollary.

---

### Phase 3: Modal instance — `liftDerivation`/`Derivable_mono` corollaries [COMPLETED]

**Goal**: One-closure instance (`box`/necessitation); validates `clMap` with a non-empty closure list.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/LiftViaMorphism.lean`.
- [ ] Define `modalSig (Ax) : ProofSig Modal.Proposition` with `closures = [box]`.
- [ ] Define `modalEquiv : Modal.DerivationTree Ax Γ φ ≃ Deriv (modalSig Ax) Γ φ` (5 ctors;
      `necessitation` ↔ `close box`).
- [ ] Define `modalHom` from `h_sub` (`g = id`; `clMap` for `box` is `⟨box, mem, fun _ => rfl⟩`).
- [ ] Re-derive `liftDerivation` and `Derivable_mono` as `Deriv.map modalHom` corollaries; agreement
      theorems vs existing defs.
- [ ] Register import in `Cslib.lean`.

**Timing**: ~2.5 hours.

**Depends on**: 1

**File territory**:
- CREATE (owned): `Cslib/Logics/Modal/Metalogic/InterSystem/LiftViaMorphism.lean`
- EDIT (owned): `Cslib.lean` (single import line)
- READ-ONLY: `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean` (existing `liftDerivation`:47,
  `Derivable_mono`) — must NOT be modified.

**Verification**:
- New file + Modal stack build green; `Lifting.lean` unchanged.
- `Derivable_mono` factors through `Deriv.map`; `close box` coherence is `rfl`.
- Zero-debt grep + `lean_verify`.

---

### Phase 4: Bimodal frame lift — Type-valued axiom family + `DerivationTree.lift` corollary [NOT STARTED]

**Goal**: Author the Bimodal `ProofSig` (the hardest signature) and re-derive the **frame-monotone**
`DerivationTree.lift` first — the easier Bimodal arm, which validates the Type-valued axiom family
and 3-closure list before the cross-syntax phase.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean`.
- [ ] Define `bimodalSig (fc) : ProofSig Bimodal.Formula` with
      `Ax := fun φ => {h : Axiom φ // h.minFrameClass ≤ fc}` (Type-valued — NOT a Prop predicate)
      and `closures = [box, allFuture, swapTemporal]`.
- [ ] Define `bimodalEquiv : Bimodal.DerivationTree fc Γ φ ≃ Deriv (bimodalSig fc) Γ φ` (7 ctors;
      `necessitation`/`temporal_necessitation`/`temporal_duality` ↔ three `close` instances).
- [ ] Define the frame morphism `frameHom (h_le : fc₁ ≤ fc₂) : ProofSigHom (bimodalSig fc₁) (bimodalSig fc₂)`
      with `g = id`, `axMap = fun φ ⟨h, hfc⟩ => ⟨h, le_trans hfc h_le⟩`, `clMap` = three `rfl`s.
- [ ] Re-derive `DerivationTree.lift` (`Derivation.lean:92`) as `Deriv.map frameHom`; agreement theorem.
- [ ] Register import in `Cslib.lean`.

**Timing**: ~3 hours.

**Depends on**: 1

**File territory**:
- CREATE (owned): `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean`
- EDIT (owned): `Cslib.lean` (single import line)
- READ-ONLY: `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` (`DerivationTree`:53, `lift`:92),
  `Cslib/Logics/Bimodal/.../Axioms.lean` (`Axiom`:79, `minFrameClass`) — must NOT be modified.

**Verification**:
- New file builds; Bimodal stack green; `Derivation.lean`/`Axioms.lean` unchanged.
- `bimodalSig.Ax` is Type-valued: `grep` confirms subtype family, no `: Prop` axiom family.
- `DerivationTree.lift` factors through `Deriv.map frameHom`; zero-debt grep + `lean_verify`.

---

### Phase 5: Bimodal cross-syntax — `liftDerivationWith` corollary (highest risk, descope-able) [IN PROGRESS]

**Goal**: Re-derive the conservative-extension unembedding `liftDerivationWith` as `Deriv.map` of the
**cross-syntax** `liftFormula a` morphism — the only instance exercising full generality
(`g : ExtFormula → Formula`). Freshness retained as the orthogonal `liftDerivationQfree` lemma.

**Tasks**:
- [ ] Extend the Phase-4 file (or add `LiftViaMorphismUnembed.lean` in the same directory) with the
      cross-syntax morphism `unembedHom (a : Atom) : ProofSigHom (extSig fc) (bimodalSig fc)`:
      `g = liftFormula a`, `g_imp = liftFormula_imp` (definitional, `Lifting.lean:571`),
      `axMap = liftAxiom a` (+ `liftAxiom_preserves_minFrameClass`, `Lifting.lean:581/628`),
      `clMap` for `swapTemporal` via `liftFormula_swapTemporal` (`Lifting.lean:576`).
- [ ] Re-derive `liftDerivationWith` (`ConservativeExtension/Lifting.lean:636`) as `Deriv.map unembedHom`
      composed with the ext/target equivalences; agreement theorem.
- [ ] Keep freshness `h_fresh : a ∉ collectDerivInl d` **outside** the functor — confirm the
      `Deriv.map` action is total (threaded-but-unused, report §5.2) and re-state `liftDerivationQfree`
      (`:691`) over the corollary unchanged in meaning.
- [ ] Register any new import in `Cslib.lean`.

**Timing**: ~3 hours (long pole). **Descope checkpoint** at the 50% mark (see contingency).

**Depends on**: 4 (reuses `bimodalSig`, `bimodalEquiv`, the Type-valued axiom family).

**File territory**:
- CREATE/EXTEND (owned): the Phase-4 Bimodal `LiftViaMorphism.lean` (or sibling
  `LiftViaMorphismUnembed.lean` in `Bimodal/Metalogic/ConservativeExtension/`).
- EDIT (owned): `Cslib.lean` (import line if new file).
- READ-ONLY (reuse verbatim, do NOT modify): `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean`
  (`liftDerivationWith`:636, `liftFormula_imp`:571, `liftFormula_swapTemporal`:576, `liftAxiom`:581,
  `liftAxiom_preserves_minFrameClass`:628, `liftDerivationQfree`:691).

**Verification**:
- New/extended file builds; `ConservativeExtension/Lifting.lean` unchanged.
- `liftDerivationWith` factors through `Deriv.map unembedHom`; `mp` arm uses no `▸` (imp-hom
  definitional), duality arm uses the `liftFormula_swapTemporal ▸`.
- Freshness confirmed orthogonal (map total without it); `liftDerivationQfree` meaning preserved.
- Zero-debt grep + `lean_verify`. If descoped (contingency), the by-hand instance is `sorry`-free
  and documented as such.

---

### Phase 6: Docs, optional deprecation shims, full CI + proof-debt audit [NOT STARTED]

**Goal**: Document the abstraction, add optional `@[deprecated]` aliases pointing old lift names at
the corollaries, and run the full CI pipeline + a final zero-debt audit across all new files.

**Tasks**:
- [ ] Expand the `ProofSystemMorphism.lean` module docs with the four worked instances (table from
      report §2) and the A1-vs-A2 rationale (one paragraph; cite report §6 caveat).
- [ ] Optionally add `@[deprecated]` aliases (only if they do not force downstream edits; otherwise
      skip — Non-Goal protects downstream files).
- [ ] Run full pipeline: `lake build`, `lake test`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Proof-debt audit: `grep -rn "sorry\|admit\|axiom " <all new files>` empty; `lean_verify` on
      each headline decl (`Deriv.map`, four corollaries); confirm `git diff --stat` shows only new
      files + `Cslib.lean` import lines (no downstream proof file modified).
- [ ] Record the audit result in the task summary; surface the A1-cost judgment call (report §6, §8
      item 4) for the user.

**Timing**: ~2 hours.

**Depends on**: 2, 3, 5

**File territory**:
- EDIT (owned): `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` (docs only).
- READ-ONLY: all four existing lift files and downstream proofs (audit confirms untouched).

**Verification**:
- Full CI pipeline green (`lake build` + `lake test` + `checkInitImports` + `lint-style` + `shake`).
- Audit confirms 0 new `sorry`, 0 new `axiom`, 0 vacuous defs; 0 downstream proof files modified.

## Testing & Validation

- [ ] Phase 1: `Deriv.map`/`map_id`/`map_comp` typecheck `sorry`-free; file builds in isolation.
- [ ] Phases 2–5: each existing lift (`liftDerivationTree`, `derivable_mono`, `liftDerivation`,
      `Derivable_mono`, `DerivationTree.lift`, `liftDerivationWith`) factors through `Deriv.map`,
      proven by an agreement theorem; the corresponding existing source file is unmodified.
- [ ] Bimodal axiom family is Type-valued (subtype), never `Prop`.
- [ ] `mp` arm coherence holds definitionally (no `▸`); duality arm uses the single
      `liftFormula_swapTemporal ▸`.
- [ ] Freshness side-condition confirmed orthogonal to the functorial action (map total without it).
- [ ] Full CI pipeline green at Phase 6: `lake build`, `lake test`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake shake`.
- [ ] Zero-debt: `lean_verify` on every headline declaration shows no new axioms; grep finds no
      `sorry`/`admit`.
- [ ] `git diff --stat` shows only new files + `Cslib.lean` import lines.

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` (new — generic layer)
- `Cslib/Logics/Propositional/Semantics/Algebra/LiftViaMorphism.lean` (new — PL pilot)
- `Cslib/Logics/Modal/Metalogic/InterSystem/LiftViaMorphism.lean` (new — Modal instance)
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean` (new — Bimodal frame +
  cross-syntax; optionally split into a sibling `LiftViaMorphismUnembed.lean`)
- `Cslib.lean` (modified — import registration lines only)
- `specs/419_generalize_derivation_lifting_intersystem/summaries/02_proof-system-morphism-overlay-summary.md`
  (on completion)

## Rollback/Contingency

- **Per-phase reversibility**: every phase adds a self-contained new file + one `Cslib.lean` import
  line. Reverting a phase = delete its file and remove its import; no downstream proof depends on the
  overlay, so the tree returns to green immediately.
- **Phase 5 descope (pre-authorized, report §7 / §8 item 4)**: if the cross-syntax equivalence proves
  costlier than re-deriving `liftDerivationWith` directly, descope P5 to "frame lift only" (Phase 4
  stands alone) and leave the unembedding as a *documented by-hand `ProofSigHom` instance* of the same
  shape. The unification claim (all lifts share one morphism abstraction) still holds; only the
  mechanized equivalence is deferred. Record as `[PARTIAL]` with the descope rationale.
- **Hard stop on downstream edits**: if any phase appears to require modifying an existing lift def or
  a downstream proof file, STOP and mark the phase `[BLOCKED]` with the precise reason — do NOT edit
  downstream files (that would drift toward A2, an explicit Non-Goal).
- **Zero-debt floor**: never introduce `sorry`/`axiom`/vacuous defs to close a phase. A phase that
  cannot be closed cleanly is `[BLOCKED]` and reported, per the report's zero-debt note.
