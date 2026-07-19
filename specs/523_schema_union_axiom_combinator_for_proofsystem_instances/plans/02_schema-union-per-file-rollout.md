# Implementation Plan: Schema-Union Axiom Combinator for Modal ProofSystem Instances (v2)

- **Task**: 523 - Replace the 15 hand-written per-system axiom inductives with a compositional schema-union combinator
- **Status**: [COMPLETED]
- **Effort**: ~24-32 hours (Representation A, staged additive rollout across ~20 agent runs)
- **Dependencies**: Tasks 520 and 521 (both COMPLETED — sequencing prerequisite satisfied)
- **Research Inputs**: reports/01_schema-union-combinator-blast-radius.md
- **Artifacts**: plans/02_schema-union-per-file-rollout.md (this file); plans/01_schema-union-staged-rollout.md (superseded design + staging doc, retained for history)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The design decision for this task is **RESOLVED** (user, 2026-07-18). Representation **A**
(schema-tag union) is selected; the mandatory Zulip design gate that blocked plan v1 is
**lifted**. This plan (v2) expands the v1 staging document's Stages A-D into concrete,
per-file / per-small-group sub-phases, each sized to one agent run (~100-500 lines of output,
per hard-mode H8 phase sizing).

The 15 per-system modal axiom predicates in `Cslib/Logics/Modal/ProofSystem/Instances/*.lean`
(`KAxiom`, `TAxiom`, ..., plus S5's `ModalAxiom` at `Metalogic/DerivationTree.lean:64`) each
re-list a byte-identical 13-constructor propositional + K + diamond-duality core and differ only
in a subset of 5 modal-strength schemata (`modalT/D/B/Four/Five`), forming a clean 18-tag
alphabet. The refactor introduces:

- `inductive ModalSchemaTag` (18 tags, `deriving DecidableEq`)
- `ModalSchemaTag.Holds : ModalSchemaTag → Proposition Atom → Prop` (per-tag formula meaning)
- `def SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop := fun χ => ∃ t ∈ S, t.Holds χ`

so each of the 14 `<Sys>Axiom` predicates plus S5 becomes a one-line `SchemaUnion` over its tag
set. The 24 `XAxiom_implies_YAxiom` subsumption lemmas collapse to one generic subsumption lemma
+ `Finset.subset` facts; the 15 per-system soundness case-splits collapse to a per-tag validity
table + one generic `unionSound` combinator.

**Resolved design parameters** (from the 2026-07-18 decision, binding on all phases):

- Representation = **A** (schema-tag union). S5 generalizes toward `Modal.ModalAxiom` as the
  existing pattern (S5 = T+4+B; carries `modalB`, NOT `modalFive`).
- ACCEPT the elimination-form change downstream: `cases … with | ctor` / `match` becomes
  `obtain ⟨t, ht, hφ⟩ := h; fin_cases t <;> …`.
- ACCEPT the ~36 genuine intuitionistic→classical hand-rewrites in
  `InterSystem/IntToClassical.lean`.
- Keep the intuitionistic/minimal families (`IKModalAxiom`, `MKModalAxiom`, `CKModalAxiom`,
  `IS5ModalAxiom`, `MTModalAxiom`) OUT of scope — but keep their witness-construction sites into
  classical `KAxiom`/`ModalAxiom` valid.
- Additive, zero-debt staging: every intermediate commit CI-green, no `sorry`, no new axiom.
  Every public theorem name stays stable or lives behind a deprecated alias across all
  intermediate states.

### Preserved Assets

The following work is complete and must not regress:

| Component | Reference | Status | Verified |
|-----------|-----------|--------|----------|
| Task 520 — composite conservativity bridges in `Modularity.lean` | `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean` | [COMPLETED] | 2026-07-18 (sequencing prereq) |
| Task 521 — minimal-canonical trio deletion; MK routed through generic `mkvalidFC_completeness` | InterSystem / minimal-base surface | [COMPLETED] | 2026-07-18 (sequencing prereq) |
| 15 per-system axiom inductives (live until Phase 8) | `Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}.lean` | live | must stay live until all consumers migrated |
| S5 `ModalAxiom` inductive (live until Phase 8) | `Cslib/Logics/Modal/Metalogic/DerivationTree.lean:64` | live | referenced by MCS/Soundness/ModalConservativity |
| Public API names (`k_soundness`, `s5_*` soundness, `KAxiom_implies_TAxiom`, the 24 subsumption lemmas, the `HasAxiom*` instances) | across Metalogic/InterSystem | stable | must resolve at every intermediate stage (stable or deprecated alias) |
| 13 frame-unconditional schema-validity atoms | `Cslib/Logics/Modal/Metalogic/Soundness.lean` (`Satisfies.implyK_axiom`, …, `diaDualityBack`) | reused | not modified — read-only reuse by `unionSound` |
| `HasAxiom*` typeclass hierarchy (the insulation layer) | `Cslib/Foundations/Logic/ProofSystem.lean` | untouched | representation-agnostic; changing it defeats feasibility |

### Source-to-Implementation Mapping (Tier: code — the existing tree is ground truth)

| Load-bearing decision | Source citation |
|-----------------------|-----------------|
| `DerivationTree` is predicate-parametric, so each `<Sys>Axiom` may become a `def : Proposition Atom → Prop` | report §3; `Lifting.lean` `liftDerivation`/`Derivable_mono` (`h_sub : ∀ φ, Axioms1 φ → Axioms2 φ`) |
| `HasAxiom*` layer is representation-agnostic — the load-bearing feasibility fact | report §2; `Cslib/Foundations/Logic/ProofSystem.lean` |
| 13 of 18 tags reuse existing frame-unconditional validity atoms; only 5 carry a frame condition | report §5; `Cslib/Logics/Modal/Metalogic/Soundness.lean` |
| S5 = T+4+B (carries `modalB`, not `modalFive`) → the `KB5 → S5` subsumption edge stays omitted | report §1.2, §1.3; `AxiomSubsumption.lean` (edge deliberately absent) |
| `IntToClassical.lean` is the irreducible hand cost (36 sites, genuine derivation work + cross-family witness construction `⟨.ax _ _ h⟩`) | report §4, §4.1; `InterSystem/IntToClassical.lean` (774 lines) |

### Research Integration

Integrated from `reports/01_schema-union-combinator-blast-radius.md`: inventory (§1), the
representation-agnostic consumption layer (§2), Representation A design (§3), the net-line-negative
blast radius (§4), compositional soundness via `unionSound` (§5), and the staged additive
sequencing (§6). §7's Zulip coordination is now a pre-PR courtesy heads-up (design already
decided), not a gate.

### Prior Plan Reference

Supersedes plans/01_schema-union-staged-rollout.md. That document was a design + staging artifact
whose Phase 1 was a mandatory Zulip design gate with Phases 2-7 `[BLOCKED]`. The gate resolved to
Representation A; this v2 lifts the block and expands Stages A-D into per-file sub-phases. v1 is
retained for history only.

### Roadmap Alignment

No `roadmap_path` provided for this dispatch; ROADMAP.md not consulted. No roadmap phases added.

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the v1 risk table, the research
blast-radius findings, and the resolved design decision.

**Do NOT**:
- Delete ANY `<Sys>Axiom` inductive (or S5's `ModalAxiom`) before Phase 8. Every deletion waits
  until no construction/destructuring site targets it. Deleting an inductive while a
  witness-construction site (`⟨.ax _ _ h⟩` producing a `KAxiom`) still targets it breaks the
  build. Inductive deletion is strictly the LAST step (Phase 8).
- Commit any `sorry` or introduce any new `axiom` at any intermediate state. If a phase cannot
  close sorry-free, mark THAT phase `[BLOCKED]` with the open goal state recorded — do not defer
  silently or commit debt.
- Modify the `HasAxiom*` typeclass hierarchy in `Cslib/Foundations/Logic/ProofSystem.lean`. It is
  the insulation layer; changing it defeats the entire feasibility argument.
- Rename or drop any public theorem/instance name without leaving a `@[deprecated]` alias.
  `k_soundness`, the S5 soundness lemmas, `KAxiom_implies_TAxiom` (and the 23 sibling subsumption
  lemmas), and the `HasAxiom*` instances must resolve at every intermediate stage.
- Introduce a `KB5 → S5` subsumption edge. S5 = T+4+B, not `modalFive`; the omission is
  deliberate and correct.
- Touch the intuitionistic/minimal axiom families (`IKModalAxiom`, `MKModalAxiom`, `CKModalAxiom`,
  `IS5ModalAxiom`, `MTModalAxiom`) beyond keeping their existing witness-construction call sites
  into the classical `KAxiom`/`ModalAxiom` valid.
- Batch multiple files into a single un-verified commit. Each per-file / per-group sub-phase
  builds green and commits on its own (commit-per-green-substep mandate).

**MUST preserve**:
- Every public theorem/instance name (stable or deprecated alias) at every stage.
- CI-green build after every sub-phase.
- The 13 frame-unconditional validity atoms in `Metalogic/Soundness.lean` (read-only reuse).
- Cross-family witness-construction validity in `IntToClassical.lean` throughout.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- Representation A (schema-tag `def` + `Finset` union) — Representation B (macro-generated
  inductives) is rejected and lives only in Rollback/Contingency as a break-glass fallback.
- S5 generalizes toward `Modal.ModalAxiom`; its disposition (unify vs. keep + bridge) is decided
  at Phase 8 per the migration state, not re-litigated mid-flight.
- The elimination-form change and the ~36 `IntToClassical.lean` hand-rewrites are ACCEPTED costs,
  not risks to be avoided.

**Design invariants (the principled foundations this refactor exists to establish)** — these are
what make Representation A *elegant* rather than merely de-duplicated; treat them as binding, not
aspirational:

1. **Subsumption IS `Finset.subset`; the modal cube IS a computation on tag sets.** The system
   hierarchy (K ⊂ T ⊂ S4 ⊂ S5, …) must be *literally* the ⊆-order on per-system tag sets, so each
   `XAxiom_implies_YAxiom` reduces to a `Finset.subset` fact discharged by `decide` through the
   single generic subsumption lemma. Do not reintroduce per-edge hand proofs. This is the primary
   structural payoff.
2. **Soundness is a syntax/semantics factorization, and it COMPOSES WITH TASK 522.** `unionSound`
   separates *which schemata* (the tag set — syntax) from *why each is valid* (the per-tag frame
   condition — semantics). The five frame-conditioned tags (`modalT/D/B/Four/Five`) map one-to-one
   onto the five lemmas already delivered in `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`
   (`Satisfies.modalT_axiom`/`modalFour_axiom`/`modalB_axiom`/`modalD_axiom`/`modalFive_axiom`,
   explicit-hypothesis form). The per-tag validity table (Phase 2) MUST consume those library
   lemmas as its witnesses — not re-prove the frame arguments inline. 522 (semantic side) and 523
   (syntactic side) are the two halves of one abstraction; `unionSound` is the hinge.
3. **`.Holds` is the faithful "schema = set of its instances" encoding.** Keep the existential-
   over-metavariables form (`∃ φ ψ, χ = …`) and `Finset` (not `Set`) for the tag collection — the
   alphabet is finite (18), so `Finset` gives `DecidableEq`, decidable membership, and the
   subsumption lattice for free. Do not swap to a decidable-pattern or `Set` encoding for local
   convenience.
4. **S5 unification removes a special case, it does not add one.** `S5Axiom` becomes
   `SchemaUnion (core ∪ {modalT, modalFour, modalB})`, folding legacy `ModalAxiom` into the same
   scheme behind a `@[deprecated]` alias — never a bespoke branch retained alongside the combinator.
5. **Scope-open, not forked.** Build the combinator for the classical 15; keep `ModalSchemaTag` /
   `SchemaUnion` free of classical-only assumptions so the intuitionistic/minimal families are a
   *future instance* of the same abstraction, not a parallel copy — WITHOUT generalizing to cover
   them now (out of scope; YAGNI).

## Goals & Non-Goals

**Goals**:
- Introduce `ModalSchemaTag`, `.Holds`, `SchemaUnion`, a generic subsumption lemma, and a generic
  `unionSound` combinator alongside the existing inductives (zero downstream blast).
- Prove the 15 bridge equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` (per-group sub-phases).
- Migrate the 15 per-system soundness proofs to `unionSound` (per-group sub-phases).
- Collapse `AxiomSubsumption.lean`'s 24 lemmas to `Finset.subset` facts.
- Hand-migrate `IntToClassical.lean`'s ~36 sites (per-cluster sub-phases).
- Swap the 15 instance registrations to build `HasAxiom*` fields from `SchemaUnion`, then delete
  the 15 inductives (+ `ModalAxiom` if fully superseded) strictly last.
- Every intermediate commit CI-green, zero-debt; net line-negative final tree.

**Non-Goals**:
- Representation B (macro inductives) — rejected by the design decision (break-glass only).
- Touching the intuitionistic/minimal modal axiom families beyond keeping their in-scope
  classical witness sites valid.
- Changing the `HasAxiom*` typeclass hierarchy in `Foundations/Logic/ProofSystem.lean`.
- Re-opening the S5 unification or elimination-form questions.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cross-family coupling breaks: intuitionistic/minimal families construct classical `KAxiom`/`ModalAxiom` witnesses (`⟨.ax _ _ h⟩`) | H | M | Keep Stage-A bridge lemmas live until Phase 8; migrate `IntToClassical.lean` (Phase 6) BEFORE swapping instances (Phase 7) and deleting inductives (Phase 8); never delete an inductive while a witness-construction site targets it. |
| Elimination-form change ripples beyond the mapped sites | M | M | Additive rollout: combinator lands ALONGSIDE inductives with bridge equivalences (Phases 1-3); migrate one file/group at a time, each independently CI-green; the bridge lets old and new coexist. |
| A sub-phase cannot close sorry-free | M | L | Zero-debt discipline: mark that sub-phase `[BLOCKED]` with the open goal recorded; never commit a `sorry` or new axiom. |
| `unionSound` frame-condition plumbing for the 5 differentiator tags harder than estimated | M | L | 13 of 18 tags reuse existing frame-unconditional atoms; only 5 carry a frame condition, each already proved inline in the current per-system soundness files — port those proofs into the tag→validity table (Phase 2). |
| Deleting S5's `ModalAxiom` breaks `MCS.lean` / `Metalogic/Soundness.lean` / `Bimodal/…/ModalConservativity.lean` | M | M | Phase 8 decides disposition from the migration state: if not fully superseded, leave `ModalAxiom` in place and only bridge it; delete only after all 3 referencing files are re-routed and green. |
| Large blast-radius PR surprises maintainers | L | L | Non-blocking pre-PR Zulip heads-up (courtesy, see below) before the user runs `/pr`; design is already decided, so this is a notice, not a gate. |

## Implementation Phases

**Dependency Analysis (wave map)**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5, 6 | 2 & 3 (Phase 4); 1 & 3 (Phase 5); 3 (Phase 6) |
| 4 | 7 | 3, 6 |
| 5 | 8 | 4, 5, 6, 7 |

Phases within the same wave may execute in parallel (distinct file territories). Sub-phases
(N.M) within a phase are sequential unless noted. New files proposed below (`SchemaUnion.lean`,
`SchemaSoundness.lean`, `SchemaBridges.lean`) are recommended locations; the implementer confirms
exact placement/imports at Phase 1 and keeps them consistent thereafter.

---

### Phase 1: Core scaffolding — `ModalSchemaTag` + `SchemaUnion` + generic subsumption [COMPLETED]

**Goal**: Land the tag alphabet, per-tag `Holds`, the `SchemaUnion` combinator, and the single
generic subsumption lemma in a new file — purely additive, no existing file altered.

**Tasks**:
- [x] Define `inductive ModalSchemaTag` (18 tags: `implyK implyS efq peirce modalK modalT modalD
      modalB modalFour modalFive andI andE1 andE2 orI1 orI2 orE diaDualityFwd diaDualityBack`) with
      `deriving DecidableEq`.
- [x] Define `ModalSchemaTag.Holds : ModalSchemaTag → Proposition Atom → Prop` — one existential
      clause per tag (formula-level meaning; cite report §3 code block for the shapes).
- [x] Define `SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop := fun χ => ∃ t ∈ S, t.Holds χ`.
- [x] Prove the generic subsumption lemma: `Sᴬ ⊆ Sᴮ → SchemaUnion Sᴬ φ → SchemaUnion Sᴮ φ`.

**Completion note**: Landed in `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` (confirmed
location, matching the proposed path). Depends only on `Cslib.Logics.Modal.Basic`,
`Cslib.Foundations.Logic.Axioms`, and `Mathlib.Data.Finset.Basic` (added for `Finset`) — no
system-specific file (`Instances/*.lean`, `DerivationTree.lean`, `ProofSystem.lean`) imported.
Each `.Holds` clause's proposition shape was cross-checked against the real constructors in
`Instances/{K,T,D,B,K4,K5}.lean` and S5's `ModalAxiom` (`Metalogic/DerivationTree.lean:64`).
Deviation from the literal report §3 sketch: existential binders needed an explicit
`: Proposition Atom` type ascription (`∃ φ ψ : Proposition Atom, …`) because dot-notation
field projection (`φ.imp …`) cannot resolve before the binder's type is known — the report's
code sketch omitted this and was elaboration-order-fragile as written. Zero `sorry`, zero new
axiom (`lean_verify` on `SchemaUnion` and `SchemaUnion.subsumption` reports only
`propext`/`Quot.sound`). Scoped `lake build`, `lake exe checkInitImports`, and full `lake lint`
all green.

**Estimated output**: ~150-250 lines. **Depends on**: none.

**Files to modify**:
- NEW `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` (proposed location).

**Verification**:
- Scoped `lake build Cslib.Logics.Modal.ProofSystem.SchemaUnion` green.
- Zero-`sorry` check on the new file (`grep -n sorry` empty; `lean_verify` on `SchemaUnion`,
  the subsumption lemma).
- No existing file modified.
- **Done when**: `SchemaUnion`, `ModalSchemaTag.Holds`, and the generic subsumption lemma compile
  sorry-free and no downstream file changed.

---

### Phase 2: `unionSound` combinator + per-tag validity table [COMPLETED]

**Goal**: Provide the generic soundness combinator, the 18-entry tag→validity table (13
frame-unconditional atoms reused; 5 frame-conditioned entries delegated to the task-522
`FrameCorrespondence` lemmas), AND a generic `SchemaUnion` elimination API, so Phases 4/6/7 can
collapse the per-system case-splits into named lemma applications rather than raw `fin_cases`.

**Tasks**:
- [x] Define `FrameValidatesTag m t` (per-tag semantic obligation) **uniformly over all 18 tags**:
      it returns `True` for the 13 frame-unconditional tags and, for the 5 differentiators, returns
      *exactly the frame hypothesis its task-522 lemma takes* (`∀ w, m.r w w` for `modalT`;
      seriality/symmetry/transitivity/Euclideanness for `modalD/B/Four/Five`). Uniformity over all
      18 — not a conditional/unconditional split at the type level — is a design invariant: the 13
      trivial obligations discharge by `trivial`, keeping `unionSound`'s `hfc` interface uniform.
- [x] State and prove `unionSound (S) (m) (hfc : ∀ t ∈ S, FrameValidatesTag m t) {φ}
      (h : SchemaUnion S φ) (w) : Satisfies m w φ` (report §5 signature) as the SINGLE master
      soundness lemma; every per-system soundness proof (Phase 4) specializes it — no per-system
      soundness structure survives.
- [x] **Elimination API (design invariant — tame the ~50 destructuring sites with named lemmas,
      not raw `fin_cases`)**: extend `SchemaUnion.lean` (additive) with the generic membership /
      unfolding lemmas for `SchemaUnion` over `Finset` structure — at minimum `SchemaUnion`
      unfolding over `∅` / `insert` / `∪`, and a `@[simp]` `mem`-style characterization — so that a
      downstream `SchemaUnion sysTags φ` rewrites to the named disjunction of its tags' `.Holds`
      via `simp`, and destructuring sites read as named rewrites rather than copy-pasted
      `fin_cases t <;> simp_all`. Complete this API ONCE here; Phases 4/6/7 consume it.
- [x] Populate the 13 frame-unconditional entries by reusing the existing atoms in
      `Metalogic/Soundness.lean` (`Satisfies.implyK_axiom`, …, `diaDualityBack`) — read-only reuse.
- [x] Populate the 5 frame-conditioned entries (`modalT/D/B/Four/Five`) by **delegating to the
      task-522 library lemmas** in `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`
      (`Satisfies.modalT_axiom (m) (h_refl) (w) (φ)`, `modalFour_axiom (h_trans)`,
      `modalB_axiom (h_symm)`, `modalD_axiom (h_serial)`, `modalFive_axiom (h_eucl)`) — do NOT
      re-prove the frame arguments inline (design invariant 2, the 522 composition). `FrameValidatesTag`
      for these five is exactly the explicit frame hypothesis those lemmas take; `unionSound`'s
      `hfc` obligation threads it. Add `public import ...FrameCorrespondence` here.

**Completion note**: Landed in NEW `Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean`
(`FrameValidatesTag`, `unionSound`) and additively extended `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`
(`SchemaUnion.empty_iff`, `SchemaUnion.insert_iff`, `SchemaUnion.union_iff`, all `@[simp]`).
`unionSound` proceeds by `obtain ⟨t, ht, hφ⟩ := h; have hval := hfc t ht; cases t with | tag => obtain ⟨…, rfl⟩ := hφ; exact Satisfies.<tag>_axiom …` — 13 branches invoke the `Metalogic/Soundness.lean` atoms directly; the 5 differentiator branches (`modalT/D/B/Four/Five`) pass `hval : FrameValidatesTag m t` straight through as the explicit frame-hypothesis argument to the corresponding `FrameCorrespondence.lean` lemma (`Satisfies.modalT_axiom m hval w φ'`, etc.) with no inline frame reasoning. Built green on the first attempt for both files; zero `sorry`, zero new axiom (`lean_verify` on `unionSound`, `SchemaUnion.insert_iff`, `SchemaUnion.union_iff`, `SchemaUnion.empty_iff` all report only `propext`/`Classical.choice`/`Quot.sound`). Scoped builds, `checkInitImports`, full `lake lint`, and `lake exe lint-style` all green. No deviation from the plan's task sequence or file placement.

**Estimated output**: ~200-350 lines. **Depends on**: 1.

**Files to modify**:
- NEW `Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean` (proposed location) — `FrameValidatesTag`,
  `unionSound`, the 18-entry validity table.
- `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` — extend additively with the generic
  elimination API (membership / unfolding `@[simp]` lemmas over `∅`/`insert`/`∪`). Additive only;
  the Phase-1 declarations are unchanged.
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` — read-only reuse (no edits, or minimal
  `FrameValidatesTag` glue only if unavoidable).
- `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean` — read-only reuse (the 5 frame-condition
  lemmas as the differentiator-tag validity witnesses).

**Verification**:
- Scoped `lake build Cslib.Logics.Modal.Metalogic.SchemaSoundness` green.
- Zero-`sorry`; `lean_verify` on `unionSound`.
- **Done when**: `unionSound` compiles sorry-free and every one of the 18 tag-validity obligations
  is discharged.

---

### Phase 3: Per-system tag sets + 15 bridge equivalences [COMPLETED]

**Goal**: Define `kCore` and the 15 per-system `Finset ModalSchemaTag` tag sets, and prove the
bridge equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` — additive; the inductives stay live.
Split into per-group sub-phases (~4 systems each, one agent run per group).

Per-system tag sets (report §1.3):
`K:{modalK} T:{modalK,modalT} D:{modalK,modalD} B:{modalK,modalB} K4:{modalK,modalFour}
K5:{modalK,modalFive} K45:{modalK,modalFour,modalFive} S4:{modalK,modalT,modalFour}
S5:{modalK,modalT,modalFour,modalB} TB:{modalK,modalT,modalB} KB5:{modalK,modalB,modalFive}
D4:{modalK,modalD,modalFour} D5:{modalK,modalD,modalFive} D45:{modalK,modalD,modalFour,modalFive}
DB:{modalK,modalD,modalB}` — each unioned with the 13-tag `kCore` (propositional + and/or + diaDuality).

**Sub-phase 3.1 — `kCore` + K, T, D, B** [COMPLETED]
- [x] Define `kCore` (the 13 shared tags) and the K/T/D/B tag sets.
- [x] Prove bridges `SchemaUnion kTags φ ↔ KAxiom φ`, and the T/D/B analogues.
- Estimated output: ~150-250 lines.
- **Completion note**: Landed in NEW `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean`.
  `kCore` defined as explicit nested `insert` terminating in `∅` (NOT the `{a, b, c}` literal
  sugar — that sugar's last element desugars to a `Singleton` instance, not `insert _ ∅`, so
  `SchemaUnion.insert_iff`/`empty_iff` do not fire on it; discovered via a failed first build
  attempt, fixed by switching to explicit nested `insert … ∅`). All four tag sets
  cross-checked against their inductive's actual constructors (`Instances/{K,T,D,B}.lean`):
  K = `kCore` exactly (no differentiator beyond `modalK`, already in `kCore`); T/D/B each
  `insert .modal{T,D,B} kCore`. Forward direction: `simp only [tag, kCore,
  SchemaUnion.insert_iff, SchemaUnion.empty_iff, or_false, ModalSchemaTag.Holds] at h` then
  `rcases`/`all_goals first | exact <Sys>Axiom.<ctor> _ … | …`. Backward direction: `cases h`
  then direct `SchemaUnion` witness `⟨.ctor, by decide, …, rfl⟩` (no simp needed). Zero `sorry`,
  zero new axiom (`lean_verify` on `schemaUnion_kTags_iff_KAxiom` and
  `schemaUnion_bTags_iff_BAxiom` report only `propext`/`Quot.sound`). Scoped `lake build`,
  `lake exe checkInitImports`, `lake exe lint-style` all green. No instance file modified.

**Sub-phase 3.2 — K4, K5, K45, S4** [COMPLETED]
- [x] Define the four tag sets; prove the four bridge equivalences.
- Estimated output: ~150-250 lines.
- **Completion note**: Appended to `SchemaBridges.lean`. Tag sets cross-checked against
  `Instances/{K4,K5,K45,S4}.lean` constructors: K4 = `kCore ∪ {modalFour}`, K5 = `kCore ∪
  {modalFive}`, K45 = `kCore ∪ {modalFour, modalFive}`, S4 = `kCore ∪ {modalT, modalFour}`.
  First build attempt on K45/S4 (the two-differentiator cases) failed with `subst` errors from
  a miscounted `rcases` pattern (15 disjuncts expected — 2 single-arg differentiators + 13
  `kCore` — but the pattern had only 14 slots and silently dropped `orI2` mid-sequence); fixed
  by re-deriving the exact 15-slot arity sequence and rewriting both `rcases` lines. Zero
  `sorry`, zero new axiom (`lean_verify` on `schemaUnion_k45Tags_iff_K45Axiom` and
  `schemaUnion_s4Tags_iff_S4Axiom` report only `propext`/`Quot.sound`). Scoped `lake build`,
  `checkInitImports`, `lint-style` all green. No instance file modified.

**Sub-phase 3.3 — S5, TB, KB5** [COMPLETED]
- [x] Define the three tag sets; prove bridges. For S5, bridge `SchemaUnion s5Tags φ ↔ ModalAxiom φ`
      (S5 = T+4+B; generalize toward `Modal.ModalAxiom` per the decision).
- Estimated output: ~120-200 lines.
- **Completion note**: Appended to `SchemaBridges.lean`. `s5Tags = kCore ∪ {modalT, modalFour,
  modalB}` cross-checked against `ModalAxiom`'s actual 16 constructors in
  `Metalogic/DerivationTree.lean` (13 core + `modalT`/`modalFour`/`modalB`, confirming S5 = T+4+B
  and carries `modalB` NOT `modalFive`, per the resolved design decision — the `KB5 → S5`
  subsumption edge stays deliberately absent; grep-confirmed no such edge was introduced here,
  as expected since Phase 3 is tag sets + bridges only, not subsumption, which is Phase 5).
  `tbTags = kCore ∪ {modalT, modalB}`, `kb5Tags = kCore ∪ {modalB, modalFive}`, both
  cross-checked against `Instances/{TB,KB5}.lean`. Same `rcases`-arity mistake as 3.2 recurred
  on the first `s5Tags` build attempt (3-differentiator case needs 16 slots, not 15; `orI2`
  under-counted again) — fixed by re-deriving the exact slot sequence; `tbTags`/`kb5Tags`
  (2-differentiator, same shape as 3.2's K45/S4) built green on the first attempt by reusing the
  already-corrected 15-slot pattern. Zero `sorry`, zero new axiom (`lean_verify` on
  `schemaUnion_s5Tags_iff_ModalAxiom` and `schemaUnion_kb5Tags_iff_KB5Axiom` report only
  `propext`/`Quot.sound`). Scoped `lake build`, `checkInitImports`, `lint-style` all green. No
  instance file or `DerivationTree.lean` modified.

**Sub-phase 3.4 — D4, D5, D45, DB** [NOT STARTED]
- [ ] Define the four tag sets; prove the four bridge equivalences.
- Estimated output: ~150-250 lines.

**Depends on**: 1 (needs `SchemaUnion`; independent of Phase 2).

**Files to modify**:
- NEW `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean` (proposed location) — imports the 15
  instance files + `SchemaUnion.lean`; holds tag sets + bridges. Existing instance files unchanged.

**Verification (each sub-phase)**:
- Scoped `lake build Cslib.Logics.Modal.ProofSystem.SchemaBridges` green after each group.
- Zero-`sorry`; each bridge proved as a genuine `↔` (no `sorry`, no `admit`).
- No instance file modified.
- **Done when**: all 15 bridge equivalences compile sorry-free; commit per group.

**Phase completion note**: All four sub-phases (3.1-3.4) landed in NEW
`Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean` (786 lines): `kCore` (13 shared tags,
defined as explicit nested `insert … ∅`, not the `{a,b,c}` literal sugar — that sugar's last
element is a `Singleton`, not `insert _ ∅`, so the elimination API's `insert_iff`/`empty_iff`
don't fire on it) plus the 15 per-system tag sets and their 15 bridge equivalences
(`SchemaUnion sysTags φ ↔ <Sys>Axiom φ`, S5 bridging to the pre-existing `ModalAxiom`). Every
tag set was cross-checked against its target inductive's actual constructors (`awk`-extracted
from `Instances/{K,T,D,B,K4,K5,K45,S4,TB,KB5,D4,D5,D45,DB}.lean` and `ModalAxiom` in
`Metalogic/DerivationTree.lean`) before being finalized, confirming: K = `kCore` exactly (no
differentiator beyond `modalK`); T/D/B/K4/K5 each `kCore ∪ {1 differentiator}`; K45/S4/D4/D5/DB
each `kCore ∪ {2 differentiators}`; S5/D45 each `kCore ∪ {3 differentiators}`; TB/KB5 each
`kCore ∪ {2 differentiators}`. The elimination API (`SchemaUnion.insert_iff`,
`SchemaUnion.empty_iff`) sufficed for every forward direction once `kCore` was redefined via
explicit `insert`; the two-and-three-differentiator cases (K45/S4 in 3.2, S5 in 3.3) each
tripped a miscounted `rcases` slot count on the first attempt (a slot silently dropped mid-list,
desyncing all subsequent arities) — both were root-caused and fixed by re-deriving the exact
slot-count arithmetic (differentiator count + 13) before writing the pattern; every
2-differentiator case afterward (TB/KB5/D4/D5/DB) reused the once-corrected 15-slot pattern and
built green on the first attempt. Backward directions used the direct `SchemaUnion` witness
construction (`⟨.tag, by decide, …, rfl⟩`) uniformly, needing no simp unfolding. Zero `sorry`,
zero new axiom across all 15 bridges (`lean_verify` spot-checked on one bridge per sub-phase:
`schemaUnion_kTags_iff_KAxiom`, `schemaUnion_bTags_iff_BAxiom`,
`schemaUnion_k45Tags_iff_K45Axiom`, `schemaUnion_s4Tags_iff_S4Axiom`,
`schemaUnion_s5Tags_iff_ModalAxiom`, `schemaUnion_kb5Tags_iff_KB5Axiom`,
`schemaUnion_d45Tags_iff_D45Axiom`, `schemaUnion_dbTags_iff_DBAxiom` — all report only
`propext`/`Quot.sound`). Full `lake lint` and scoped `lake build` both green after the final
sub-phase; `lake exe checkInitImports` and `lake exe lint-style` green throughout. No instance
file, `SchemaUnion.lean`, or `DerivationTree.lean` was modified — fully additive, as scoped. The
deliberately-omitted `KB5 → S5` subsumption edge was grep-confirmed absent (subsumption itself
is out of scope for Phase 3; that is Phase 5).

---

### Phase 4: Migrate 15 per-system soundness proofs to `unionSound` [COMPLETED]

**Goal**: Replace each `Systems/*/Soundness.lean` case-split with a `unionSound` call fed by that
system's tag→validity table (net deletion), one small group per agent run. Public soundness
theorem names stay stable; use the Phase 3 bridge where a caller still expects the inductive form.

**Sub-phase 4.1 — K, T, D, B** [COMPLETED]
- [x] Rewrite `<sys>_axiom_sound` (K/T/D/B) through `unionSound` + the per-system tag→validity table.
- Files: `Systems/{K,T,D,B}/Soundness.lean`. Estimated output: ~120-220 lines net (deletion-heavy).
- **Completion note**: Each `<sys>_axiom_sound` is now `unionSound sysTags m hfc (bridge.mpr h_ax) w`
  where `hfc := fun t ht => by fin_cases ht <;> first | trivial | exact <frame_hyp>` (K has no
  frame hyp — all 13 goals close by `trivial`; T/D/B each supply exactly one: `h_refl`/`h_serial`/
  `h_symm`). `fin_cases ht` required an explicit `public import Mathlib.Tactic.FinCases` in each
  file — not transitively available via `Cslib.Init`/`SchemaBridges`/`SchemaSoundness` (first
  build attempt failed with "unknown tactic"; fixed by adding the direct import, permitted since
  only the 15 `Systems/*/Soundness.lean` files are in scope for this phase). Public names
  (`k_axiom_sound`, `k_soundness`, `k_soundness_derivable`, `t_axiom_sound`, `t_soundness`,
  `d_axiom_sound`, `d_soundness`, `b_axiom_sound`, `b_soundness`) all byte-stable — only the
  `_axiom_sound` bodies changed; the `_soundness`/`_soundness_derivable` wrappers were untouched
  since they already just call `<sys>_axiom_sound`. Zero `sorry`, zero new axiom (`lean_verify` on
  `k_soundness` and `b_axiom_sound` report only `propext`/`Classical.choice`/`Quot.sound`). Scoped
  `lake build` of all four modules, `lake exe checkInitImports`, and `lake exe lint-style` all
  green.

**Sub-phase 4.2 — K4, K5, K45, S4** [COMPLETED]
- [x] Rewrite the four soundness proofs through `unionSound`.
- Files: `Systems/{K4,K5,K45,S4}/Soundness.lean`. Estimated output: ~120-220 lines.
- **Completion note**: Same `unionSound sysTags m hfc (bridge.mpr h_ax) w` pattern as 4.1. K4/K5
  each supply one frame hyp (`h_trans`/`h_eucl`); K45/S4 each supply two
  (`h_trans`/`h_eucl` and `h_refl`/`h_trans` respectively) via
  `first | trivial | exact h1 | exact h2` — confirms the pattern scales to multi-differentiator
  tag sets without change. Public names byte-stable. Zero `sorry`, zero new axiom (`lean_verify`
  on `k45_soundness` and `s4_axiom_sound` report only `propext`/`Classical.choice`/`Quot.sound`).
  Scoped `lake build` of all four modules, `checkInitImports`, `lint-style` all green.

**Sub-phase 4.3 — S5, TB, KB5** [COMPLETED]
- [x] Rewrite the three soundness proofs; keep the S5 public soundness names stable.
- Files: `Systems/{S5,TB,KB5}/Soundness.lean`. Estimated output: ~100-200 lines.
- **Completion note**: Same `unionSound sysTags m hfc (bridge.mpr h_ax) w` pattern. S5's original
  `modalB` case derived symmetry inline from `h_refl`+`h_eucl` (S5 = T+4+B, so it never took an
  `h_symm` parameter); the migrated proof reproduces that derivation as a local
  `have h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁ := fun w₁ w₂ hr => h_eucl w₁ w₂ w₁ hr (h_refl w₁)`
  fed into `unionSound`'s `hfc`, preserving `s5_axiom_sound`'s exact original signature (still
  `h_refl`/`h_trans`/`h_eucl`, no `h_symm` parameter). TB/KB5 both take their differentiator
  hyps (`h_refl`/`h_symm` and `h_symm`/`h_eucl` respectively) directly.
  **Mid-phase simplification (applies retroactively to 4.1 and 4.2 too)**: the `hfc` term was
  first written as `fun t ht => by fin_cases ht <;> first | trivial | exact h1 | exact h2 | …`
  (mirroring the plan prompt's suggested shape), but `lake build` on K45/S4 surfaced
  `linter.unreachableTactic`/`linter.unusedTactic` warnings — Lean's built-in `trivial` tactic
  already tries `assumption` as a fallback after `rfl`, so it alone closes every one of the 13
  core-tag `True` goals AND every differentiator-tag goal (since the matching frame hypothesis
  is already in local context after `fin_cases` substitutes the concrete tag), making every
  `exact h_*` branch dead code. Simplified uniformly to `fun t ht => by fin_cases ht <;> trivial`
  across all 9 systems built so far (K/T/D/B/K4/K5/K45/S4/S5) — zero warnings, same proof term
  shape, no docstring content changed (the "discharged by h_*" prose remains accurate: `trivial`'s
  `assumption` step is exactly that discharge). All nine re-verified green after the
  simplification. `fin_cases ht` required an explicit `public import Mathlib.Tactic.FinCases`
  in every file (not transitively available; permitted since only the 15
  `Systems/*/Soundness.lean` files are in scope this phase). Public names all byte-stable. Zero
  `sorry`, zero new axiom (`lean_verify` on `s5_soundness` and `kb5_axiom_sound` report only
  `propext`/`Classical.choice`/`Quot.sound`). Scoped `lake build` of all nine modules touched so
  far, `checkInitImports`, `lint-style` all green with no warnings.

**Sub-phase 4.4 — D4, D5, D45, DB** [COMPLETED]
- [x] Rewrite the four soundness proofs through `unionSound`.
- Files: `Systems/{D4,D5,D45,DB}/Soundness.lean`. Estimated output: ~120-220 lines.
- **Completion note**: Same `unionSound sysTags m (fun t ht => by fin_cases ht <;> trivial)
  (bridge.mpr h_ax) w` pattern as 4.1-4.3 (the simplified, warning-free `hfc` form from the start
  — no retroactive fix needed for this group). D4/D5/DB each carry two differentiators
  (`modalD`+`modalFour`/`modalFive`/`modalB`); D45 carries three (`modalD`, `modalFour`,
  `modalFive`). Public names byte-stable. Zero `sorry`, zero new axiom (`lean_verify` on
  `d45_soundness` and `db_axiom_sound` report only `propext`/`Classical.choice`/`Quot.sound`).
  Scoped `lake build` of all four modules, `checkInitImports`, `lint-style` all green with no
  warnings.

**Depends on**: 2 (needs `unionSound`) and 3 (needs bridges + tag sets).

**Verification (each sub-phase)**:
- Scoped `lake build` of each touched `Systems/*/Soundness.lean` module green after the group.
- Public soundness theorem names unchanged (or deprecated alias); zero-`sorry`.
- **Done when**: every migrated soundness theorem discharges via `unionSound` with its original
  public name and no `sorry`; commit per group.

**Phase completion note**: All four sub-phases (4.1-4.4) landed across the 15
`Systems/*/Soundness.lean` files. Every `<sys>_axiom_sound` (and S5's `s5_axiom_sound`) now reads
`unionSound sysTags m (fun t ht => by fin_cases ht <;> trivial) (bridge.mpr h_ax) w` — the
per-system case-split structure is gone; `unionSound` (Phase 2) is the single point where any
per-tag proof obligation is discharged. `fin_cases ht` substitutes the concrete tag for each
element of `sysTags`; Lean's `trivial` tactic (which tries `rfl`/`contradiction`/`assumption`)
closes the 13 core-tag `True` goals via its `True.intro`/`rfl` path and every differentiator-tag
goal via its `assumption` fallback, since the matching frame hypothesis (`h_refl`/`h_trans`/
`h_symm`/`h_serial`/`h_eucl`) is already in local context with the exact required type — no
system needed an explicit `exact h_*` branch once this was discovered (a first-attempt
`first | trivial | exact h_*` form on K45/S4 in 4.2 surfaced
`linter.unreachableTactic`/`linter.unusedTactic` warnings, root-caused and simplified
retroactively across 4.1-4.3 in the same dispatch; 4.4 used the simplified form from the start).
S5's `modalB` (symmetry) obligation, which pre-migration was proved inline from `h_refl`+`h_eucl`
(S5 = T+4+B, never took an `h_symm` parameter), is now a local `have h_symm := fun w₁ w₂ hr =>
h_eucl w₁ w₂ w₁ hr (h_refl w₁)` feeding the same uniform `hfc` term — `s5_axiom_sound`'s original
signature (`h_refl`/`h_trans`/`h_eucl`, no `h_symm`) is preserved exactly. `fin_cases` required an
explicit `public import Mathlib.Tactic.FinCases` added to each of the 15 files (not transitively
available via `Cslib.Init`/`SchemaBridges`/`SchemaSoundness`) — permitted since only the 15
`Systems/*/Soundness.lean` files are in scope for Phase 4. Every public theorem/instance name
(`k_soundness`, `k_soundness_derivable`, all 15 `<sys>_axiom_sound`, all 15 `<sys>_soundness`)
is byte-stable — only the `_axiom_sound` bodies changed; the `_soundness`/`_soundness_derivable`
wrappers already just called `<sys>_axiom_sound` and needed no edits. Zero `sorry` across all 15
files (full grep), zero new axiom (spot-checked via `lean_verify` on `k_soundness`,
`k45_soundness`, `s5_soundness`, `d45_soundness`, and four `_axiom_sound` lemmas — all report only
`propext`/`Classical.choice`/`Quot.sound`). Scoped `lake build` of all 15 modules,
`lake exe checkInitImports`, and `lake exe lint-style` all green with zero warnings. No file
outside `Systems/*/Soundness.lean` was touched; `SchemaUnion.lean`, `SchemaSoundness.lean`,
`SchemaBridges.lean`, the 15 instance files, and `DerivationTree.lean` are all unmodified. Net
line delta across the 15 files (`git diff --stat` vs. the pre-Phase-4 baseline): 149 insertions,
277 deletions = **-128 lines net** (each ~13-20-line `cases h_ax with | ctor => exact
Satisfies.<tag>_axiom ...` block collapsed to a 2-4 line `unionSound` term, offset by ~4 new
import lines and a short doc-comment addition per file).

---

### Phase 5: Replace `AxiomSubsumption.lean` with `Finset.subset` facts [COMPLETED]

**Goal**: Collapse the 24 hand-written `XAxiom_implies_YAxiom` lemmas (~524 lines) to
`Finset.subset`-backed facts via the Phase 1 generic subsumption lemma, then update the few call
sites. Net deletion.

**Sub-phase 5.1 — 24 subsumption facts** [COMPLETED]
- [x] Replace each of the 24 subsumption lemmas with a `Finset.subset` fact fed to the generic
      `subsumption` lemma; preserve each public lemma name (or provide a `@[deprecated]` alias).
- [x] Verify the deliberately-omitted `KB5 → S5` edge stays omitted (S5 = T+4+B, not `modalFive`).
- File: `InterSystem/AxiomSubsumption.lean`. Estimated output: ~120-220 lines net (deletion-heavy).
- **Completion note**: Every one of the 24 lemmas now reads
  `schemaUnion_yTags_iff_YAxiom.mp (SchemaUnion.subsumption (by decide)
  (schemaUnion_xTags_iff_XAxiom.mpr h))` — no hand-written `match`/`cases` on constructors
  remains. `by decide` discharges each `xTags ⊆ yTags` obligation against the concrete `Finset`s
  from `SchemaBridges.lean`; elaboration order (expected-type propagation from the outer `.mp`
  down through `SchemaUnion.subsumption`'s implicit `Sb`, then from the inner `.mpr h` up through
  `Sa`) resolves both implicit tag-set arguments before `decide` runs, so no explicit type
  ascription was needed on any of the 24 sites. Added `public import` of `SchemaUnion.lean` and
  `SchemaBridges.lean` (previously only `Instances` was imported). The deliberately-omitted
  `KB5 → S5` edge stays absent and is now mechanically explained in the module doc: `kb5Tags`
  carries `modalFive`, which is not a member of `s5Tags` (S5 = T+4+B, carries `modalB` not
  `modalFive`), so no `hsub : kb5Tags ⊆ s5Tags` term exists — grep-confirmed no such lemma was
  introduced. Zero `sorry`, zero new axiom (`lean_verify` on `KAxiom_implies_TAxiom`,
  `K45Axiom_implies_D45Axiom`, and `S4Axiom_implies_ModalAxiom` all report only
  `propext`/`Quot.sound`). Scoped `lake build`, `lake exe checkInitImports`, and
  `lake exe lint-style` all green. Net line delta: 73 insertions, 368 deletions = **-295 lines
  net** (`git diff --stat`).

**Sub-phase 5.2 — call-site name updates** [COMPLETED]
- [x] Update the (few) call sites in `Lifting.lean` / `Modularity.lean` that reference subsumption
      lemma names — call-site NAMES only, no structural change (these files are insulated).
- Files: `InterSystem/Lifting.lean`, `InterSystem/Modularity.lean`. Estimated output: ~30-80 lines.
- **Completion note**: Investigated both files line-by-line (excluding doc comments) for actual
  code references to any of the 24 subsumption lemma names. Found none: `Lifting.lean` is fully
  parametric (`Derivable_mono`/`liftDerivation`/etc. take `Axioms1 Axioms2 : Proposition Atom →
  Prop` and `h_sub : ∀ φ, Axioms1 φ → Axioms2 φ` as free hypotheses — the 24 lemmas are usage
  *examples* in the module doc comment only, e.g. `KAxiom_implies_TAxiom` at line 37, which
  remains accurate verbatim since the name/signature is preserved). `Modularity.lean` references
  the axiom *predicates* directly (`KAxiom`, `TAxiom`, `S4Axiom`, `ModalAxiom`, plus the
  out-of-scope minimal/intuitionistic families) but never applies any of the 24 subsumption
  lemma *names* as terms. Both files already built green against the Phase-5.1 changes with zero
  edits (confirming the plan's "insulated... no structural change" framing was correct and, in
  this instance, the "few call sites" resolved to zero actual call sites needing a name change —
  only the one accurate doc-comment mention). Scoped `lake build` of both modules green; no file
  modified in this sub-phase.

**Depends on**: 1 (generic subsumption) and 3 (tag sets). Independent of Phase 4.

**Verification**:
- Scoped `lake build` of `AxiomSubsumption`, `Lifting`, `Modularity` green.
- All 24 subsumption facts proved via the generic lemma; zero-`sorry`; no `KB5 → S5` edge.
- **Done when**: `AxiomSubsumption.lean` contains no hand-written per-edge `match`, all 24 names
  resolve, and dependent files build; commit per sub-phase.

**Phase completion note**: Both sub-phases land together as intended. `AxiomSubsumption.lean`
went from 524 lines of 24 near-identical 13-20-line `match`-on-constructor proofs to 24
two-line generic-lemma applications (net -295 lines). `Lifting.lean`/`Modularity.lean` required
no edits since neither has an actual code call site for any of the 24 lemma names — both were
already insulated as the plan anticipated. Zero `sorry`, zero new axiom across all three files.
Next phase: Phase 6 (hand-migrate `IntToClassical.lean`, ~36 sites) — independent of Phase 5,
depends only on Phase 3.

---

### Phase 6: Hand-migrate `IntToClassical.lean` (~36 sites) [COMPLETED]

**Site enumeration (recorded at start of 6.1, ground-truthed against the actual file, superseding
the ~36 estimate)**: a full grep of `IntToClassical.lean` for constructor patterns
(`⟨.ax [] _ (`, `KAxiom.`/`TAxiom.`/`S4Axiom.`/`ModalAxiom.`, `match h with`, `cases h with`,
`obtain`/`rcases` on axiom-typed hypotheses) found:

- **12 raw-constructor witness-construction sites** (`⟨.ax [] _ (<Sys>Axiom.ctor …)⟩`): 10 on
  `KAxiom` (`implyK`, `implyS`, `efq`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `modalK` —
  lines 64/69/74/79/84/89/94/99/104/110), 1 on `TAxiom` (`modalT`, line 535, inside the
  `itAxiom_derivable_in_T` match), 1 on `S4Axiom` (`modalFour`, line 646, inside
  `is4Axiom_derivable_in_S4`). These are exactly the sites that break once Phase 8 redefines
  `<Sys>Axiom` as a constructorless `SchemaUnion` `def` — hence in scope.
- **0 in-scope destructuring sites**: the file's four `match h with` blocks
  (`ikAxiom_derivable_in_K`, `itAxiom_derivable_in_T`, `is4Axiom_derivable_in_S4`,
  `is5Axiom_derivable_in_S5`) all destructure the OUT-OF-SCOPE intuitionistic inductives
  (`IKModalAxiom`/`ITModalAxiom`/`IS4ModalAxiom`/`IS5ModalAxiom`), which are permanent (never
  redefined) per the postmortem constraints — these matches need no elimination-API migration and
  must NOT be touched. All `obtain`/`rcases` sites destructure the single-field `Derivable`
  wrapper (`⟨d⟩`), unrelated to axiom representation, and also need no change.
- The `HasAxiom*` typeclass field accesses (`HasAxiomK.K`, `HasAxiomB.B`,
  `HasAxiomDiaDualityFwd.diaDualityFwd`, etc.) are the representation-agnostic insulation layer
  (Preserved Assets) and are correctly left untouched throughout.

**Ground-truth deviation from the plan's ~36 estimate**: the actual in-scope site count is 12, not
~36 (the estimate over-counted arms of the out-of-scope intuitionistic-family `match` statements,
which do not need migration). All 12 real sites are migrated below; no site is skipped.

**Recorded 3-cluster partition (fixed, non-overlapping, ~4 sites each)**:
- Cluster 1 (6.1): `implyK`, `implyS`, `efq`, `andI` (`KAxiom`, lines 64/69/74/79).
- Cluster 2 (6.2): `andE1`, `andE2`, `orI1`, `orI2` (`KAxiom`, lines 84/89/94/99).
- Cluster 3 (6.3): `orE`, `modalK` (`KAxiom`, lines 104/110) + `modalT` (`TAxiom`, line 535,
  cross-family: `IT`→`T` bridge) + `modalFour` (`S4Axiom`, line 646, cross-family: `IS4`→`S4`
  bridge) — the two cross-family witness sites prioritized per the dispatch instructions.

**Migration pattern used (elimination API + Phase-3 bridge, not raw `fin_cases`)**: each
`⟨.ax [] _ (<Sys>Axiom.ctor args)⟩` becomes `⟨.ax [] _ (schemaUnion_<sys>Tags_iff_<Sys>Axiom.mp
⟨.ctor, by decide, args, rfl⟩)⟩` — i.e. construct the `SchemaUnion` existential witness directly
(byte-identical shape to the retired constructor argument, per `ModalSchemaTag.Holds`) and push it
through the Phase-3 bridge's `.mp` direction. This removes the direct dependence on
`<Sys>Axiom.ctor` (which disappears when Phase 8 redefines `<Sys>Axiom` as a `SchemaUnion` `def`)
while keeping the resulting term's type unchanged (`<Sys>Axiom φ`), so no downstream caller of
these theorems needs any change.

**Goal**: Perform the irreducible hand-migration of the ~36 constructor/destructuring sites in
`IntToClassical.lean` (774 lines) — genuine intuitionistic→classical derivation work plus
cross-family witness construction. NO inductive is deleted here. Split into per-cluster sub-phases;
the implementer partitions the ~36 sites into three balanced clusters at the start of 6.1 and
records the partition so 6.2/6.3 have fixed, non-overlapping scope.

**Sub-phase 6.1 — cluster 1 (`implyK`/`implyS`/`efq`/`andI`)** [COMPLETED]
- [x] Migrate the 4 `KAxiom` raw-constructor witness sites to `schemaUnion_kTags_iff_KAxiom.mp`
      over a directly-constructed `SchemaUnion` witness.
- **Completion note**: site enumeration (12 real sites, not ~36 — see the enumeration note above
  the sub-phases) and the 3-cluster partition were recorded above. Scoped build green, zero
  `sorry`, `checkInitImports` clean.

**Sub-phase 6.2 — cluster 2 (`andE1`/`andE2`/`orI1`/`orI2`)** [COMPLETED]
- [x] Migrate the 4 `KAxiom` raw-constructor witness sites the same way.
- **Completion note**: scoped build green, zero `sorry`, `checkInitImports` clean. No destructuring
  sites existed in this cluster (all 4 are witness-construction, per the enumeration note).

**Sub-phase 6.3 — cluster 3 (`orE`/`modalK` + cross-family `modalT`/`modalFour`)** [COMPLETED]
- [x] Migrate `orE`, `modalK` (`KAxiom`) to the `SchemaUnion` bridge.
- [x] Migrate the two cross-family witness sites: `TAxiom.modalT` (inside
      `itAxiom_derivable_in_T`'s `.tBox` arm) via `schemaUnion_tTags_iff_TAxiom.mp`, and
      `S4Axiom.modalFour` (inside `is4Axiom_derivable_in_S4`'s `.fourBox` arm) via
      `schemaUnion_s4Tags_iff_S4Axiom.mp`. Updated the two enclosing theorems' docstrings
      (`itAxiom_derivable_in_T`, `is4Axiom_derivable_in_S4`) to describe the bridge-based
      construction accurately instead of the retired constructor names.
- **Completion note**: all 4 sites in this cluster migrated; both cross-family witness sites
  (`tBox`, `fourBox`) kept their enclosing `match` on the out-of-scope `ITModalAxiom`/
  `IS4ModalAxiom` inductives completely untouched — only the leaf witness term changed. Confirmed
  by grep that zero `⟨.ax [] _ (<Sys>Axiom.ctor …)⟩` raw-constructor sites remain anywhere in the
  file. Scoped build green, zero `sorry`, `checkInitImports` clean, `lake lint --builtin-lint`
  clean (no environment linters registered for this module; text-linter warnings present are
  pre-existing in `Modal/Basic.lean`, unrelated to this file), `lake exe lint-style` clean.
  `lean_verify` on `k_derivable_of_ik_implyK`, `itAxiom_derivable_in_T`, and
  `is4Axiom_derivable_in_S4` all report only `propext`/`Quot.sound` (no `sorryAx`, no new axiom).

**Depends on**: 3 (needs bridges). Independent of Phases 4/5.

**Files to modify**: `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`.

**Verification (each sub-phase)**:
- Scoped `lake build Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical` green after each cluster.
- Zero-`sorry`; cross-family witness-construction sites still valid; no inductive deleted.
- **Done when**: all ~36 sites migrated across the three clusters, file builds sorry-free, and no
  `<Sys>Axiom`/`ModalAxiom` inductive has been removed; commit per cluster.

**Phase completion note**: all 12 real in-scope sites (ground-truthed against the ~36 estimate,
see the enumeration note above) migrated across 6.1/6.2/6.3. Zero `sorry`, zero new axiom, no
inductive deleted (`KAxiom`, `TAxiom`, `S4Axiom`, `ModalAxiom`, and all 5 out-of-scope
intuitionistic families remain live inductives, exactly as required). Public API unchanged: every
migrated theorem (`k_derivable_of_ik_*`, `itAxiom_derivable_in_T`, `is4Axiom_derivable_in_S4`)
keeps its original name and type; only the internal witness-construction term changed. This
pre-empts the Phase 8 break: once `KAxiom`/`TAxiom`/`S4Axiom` are redefined in place as
constructorless `SchemaUnion` `def`s, these 12 sites no longer reference a retired constructor
name and continue to typecheck without further edits to this file.

---

### Phase 7: Swap 15 instance registrations to `SchemaUnion` [COMPLETED]

**Goal**: Rewrite each `HasAxiom*` instance registration in `Instances/*.lean` to discharge its
fields from `SchemaUnion` (via the Phase 3 bridge where convenient), replacing witness
constructions like `KAxiom.implyK _`. Inductives are NOT deleted here (that is Phase 8). Split into
per-cluster sub-phases (~4 files each).

**Import-cycle finding (recorded at start of 7.1, binding on all of Phase 7)**: the plan's stated
mechanism (`schemaUnion_kTags_iff_KAxiom.mp ⟨.implyK, by decide, φ, ψ, rfl⟩`, reusing the exact
Phase-3 bridge lemma from `SchemaBridges.lean`) is **not importable** from any `Instances/*.lean`
file. Empirically confirmed via a direct `lake build` attempt (adding
`public import Cslib.Logics.Modal.ProofSystem.SchemaBridges` to `Instances/K.lean` and building):
`error: Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean: bad import
'Cslib.Logics.Modal.ProofSystem.Instances'` plus a `build cycle detected` diagnostic. Root cause:
`SchemaBridges.lean` (Phase 3, untouched, correctly so per Preserved Assets) imports the
`Instances` barrel, which imports every individual `Instances/{sys}.lean` file — so any
`Instances/{sys}.lean` importing `SchemaBridges.lean` back is a genuine cycle in the acyclic
import DAG, not a workaround-able name resolution issue. **Resolution** (does not touch
`SchemaBridges.lean`/`SchemaUnion.lean`, only edits the target `Instances/*.lean` file, per
territory): each `Instances/{sys}.lean` file additionally imports only
`Cslib.Logics.Modal.ProofSystem.SchemaUnion` (verified acyclic: `SchemaUnion.lean` imports only
`Modal.Basic`, `Foundations.Logic.Axioms`, `Mathlib.Data.Finset.Basic` — none of which depend on
`Instances`), and gains one `private theorem {sys}Tags_of_schemaUnion` per file: a file-local
forward-direction (`SchemaUnion → <Sys>Axiom`) discharge lemma, structurally identical to the
`.mp` half of that system's Phase-3 bridge (same tag-set shape, same `SchemaUnion.insert_iff` /
`SchemaUnion.empty_iff` unfolding, same per-constructor `all_goals first | exact …`), but
re-derived locally since the canonical copy in `SchemaBridges.lean` cannot be imported. `private`
scoping means the (identical-across-files-in-spirit but locally-named) theorem cannot collide
with `SchemaBridges.lean`'s public bridge names even though both exist in the merged environment
for any downstream file that imports both. Every registration field now reads
`({sys}Tags_of_schemaUnion ⟨.tag, by decide, _, …, rfl⟩)` instead of a raw `<Sys>Axiom.ctor`
call — the only remaining raw-constructor references in each file are the ~13-16 `exact
<Sys>Axiom.ctor _ …` lines *inside* that file's own private helper (unavoidable: constructing an
inhabitant of a still-live `inductive` requires applying one of its constructors somewhere; the
canonical `SchemaBridges.lean` bridge has the same property). This preserves the real Phase-8
payoff: once Phase 8 redefines `inductive <Sys>Axiom` as `def <Sys>Axiom := SchemaUnion sysTags`,
each field's `⟨.tag, by decide, _, …, rfl⟩` witness becomes directly usable as `<Sys>Axiom …` by
defeq, so Phase 8 only needs to delete the (now-dead) private helper and strip the
`{sys}Tags_of_schemaUnion` wrapper text from each field — a small, mechanical diff — rather than
re-deriving `SchemaUnion` witnesses from scratch in 15 files. This finding and resolution apply
uniformly to sub-phases 7.1-7.4; it is not re-litigated per sub-phase below.

**Sub-phase 7.1 — K, T, D, B** [COMPLETED]
- [x] Rewrite the `HasAxiom*` instance fields in `Instances/{K,T,D,B}.lean` to build from `SchemaUnion`.
- Estimated output: ~150-260 lines.
- **Completion note**: Per the import-cycle finding above, each file gained a `public import
  Cslib.Logics.Modal.ProofSystem.SchemaUnion` and one `private theorem {k,t,d,b}Tags_of_schemaUnion`
  (placed inside `namespace Cslib.Logic.Modal` / `section ModalInstances`, immediately before the
  registrations it serves). K's tag set is `kCore` alone (13 tags, no differentiator beyond
  `modalK`); T/D/B each add one differentiator (`modalT`/`modalD`/`modalB`) — 14 tags. Every
  `HasAxiomImplyK`/…/`HasAxiomT`/`HasAxiomD`/`HasAxiomB`/`HasAxiomAndI`/…/`HasAxiomDiaDualityBack`
  field across all four files now reads `⟨Modal.DerivationTree.ax [] _
  ({sys}Tags_of_schemaUnion ⟨.tag, by decide, _, …, rfl⟩)⟩`, replacing the prior raw
  `Modal.{Sys}Axiom.ctor _ …` call. All four `inductive {K,T,D,B}Axiom` definitions are
  unmodified and still present (grep-confirmed: `^inductive {Sys}Axiom` present exactly once per
  file). Zero `sorry` (grep-confirmed empty across all four files), zero new axiom (`lean_verify`
  on `kTags_of_schemaUnion`, `tTags_of_schemaUnion`, `bTags_of_schemaUnion` all report only
  `propext`/`Quot.sound`). Scoped `lake build` of all four modules green; additionally rebuilt the
  `Instances` barrel, `SchemaBridges.lean`, `AxiomSubsumption.lean`, and `IntToClassical.lean`
  (the four files whose imports transitively touch these four instance files) to confirm no
  downstream breakage — all green. `lake exe checkInitImports` clean. `lake lint --builtin-lint`
  on all four modules: "No environment linters registered" (matches the pre-existing pattern for
  these modules per Phase 6's notes) plus a clean final "Linting passed for Cslib". `lake exe
  lint-style` clean (no line-length or other text-lint violations after wrapping the inlined
  `Finset` literal and `rcases` pattern to stay under the 100-column limit — an early attempt
  without wrapping tripped `linter.style.longLine`, fixed by word-wrapping both to a 70-column
  budget before the enclosing indent). Net line delta: +210/-55 across the four files (the private
  per-file helper is the dominant addition, as expected from the import-cycle finding above).

**Sub-phase 7.2 — K4, K5, K45, S4** [COMPLETED]
- [x] Rewrite `Instances/{K4,K5,K45,S4}.lean`.
- Estimated output: ~150-260 lines.
- **Completion note**: Same private-per-file-helper pattern as 7.1 (see the import-cycle finding
  above 7.1). K4/K5 each add one differentiator (`modalFour`/`modalFive`, 14 tags); K45 adds two
  (`modalFour`, `modalFive`, 15 tags); S4 adds two (`modalT`, `modalFour`, 15 tags) — confirming
  the pattern scales to multi-differentiator tag sets with no change beyond the tag list. Every
  `HasAxiom*` field (including the differentiator fields `HasAxiom4.four`, `HasAxiom5.five`) now
  routes through its file's `{k4,k5,k45,s4}Tags_of_schemaUnion` private helper. All four
  `inductive {K4,K5,K45,S4}Axiom` definitions unmodified and still present (grep-confirmed). Zero
  `sorry`, zero new axiom (`lean_verify` on `k45Tags_of_schemaUnion` and `s4Tags_of_schemaUnion`
  report only `propext`/`Quot.sound`). Scoped `lake build` of all four modules green; rebuilt the
  `Instances` barrel, `SchemaBridges.lean`, `AxiomSubsumption.lean`, `IntToClassical.lean` green
  (no downstream breakage). `checkInitImports` clean; `lint-style` clean; `lake lint --builtin-lint`
  clean ("No environment linters registered" per-file, "Linting passed for Cslib" overall). Net
  line delta: +216/-58 across the four files.

**Sub-phase 7.3 — S5, TB, KB5** [COMPLETED]
- [x] Rewrite `Instances/{S5,TB,KB5}.lean` (S5 discharges via the `ModalAxiom` bridge).
- Estimated output: ~120-220 lines.
- **Completion note**: Same private-per-file-helper pattern as 7.1/7.2 (see the import-cycle
  finding above 7.1) — including for S5, which is the special case: `S5.lean` does not define its
  own inductive (it reuses `Modal.ModalAxiom` from `Metalogic/DerivationTree.lean`), but is still
  part of the `Instances` barrel that `SchemaBridges.lean` imports, so the same cycle applies and
  the same private-helper resolution is needed; `s5Tags_of_schemaUnion`'s target type is
  `ModalAxiom χ` (16 tags: `kCore` + `modalT`/`modalFour`/`modalB`, cross-checked against
  `ModalAxiom`'s 16 constructors in `DerivationTree.lean` — confirms S5 = T+4+B, carries `modalB`
  not `modalFive`, matching Phase 3's finding; the deliberately-omitted `KB5 → S5` subsumption
  edge is Phase 5 territory, untouched here). TB adds two differentiators (`modalT`, `modalB`, 15
  tags); KB5 adds two (`modalB`, `modalFive`, 15 tags). All three target inductives
  (`TBAxiom`, `KB5Axiom`, and `ModalAxiom` in `DerivationTree.lean`) unmodified and still present
  (grep-confirmed). Zero `sorry`, zero new axiom (`lean_verify` on `s5Tags_of_schemaUnion` and
  `kb5Tags_of_schemaUnion` report only `propext`/`Quot.sound`). Scoped `lake build` of all three
  modules green; rebuilt the `Instances` barrel, `SchemaBridges.lean`, `AxiomSubsumption.lean`,
  `IntToClassical.lean`, and `Metalogic.DerivationTree` green (no downstream breakage, including
  no breakage to `DerivationTree.lean` from S5's registrations still resolving against
  `ModalAxiom`). `checkInitImports` clean; `lint-style` clean; `lake lint --builtin-lint` clean.
  Net line delta: +168/-46 across the three files.

**Sub-phase 7.4 — D4, D5, D45, DB** [COMPLETED]
- [x] Rewrite `Instances/{D4,D5,D45,DB}.lean`.
- Estimated output: ~150-260 lines.
- **Completion note**: Same private-per-file-helper pattern as 7.1-7.3. D4/D5 each add two
  differentiators (`modalD`+`modalFour`/`modalFive`, 15 tags); D45 adds three (`modalD`,
  `modalFour`, `modalFive`, 16 tags); DB adds two (`modalD`, `modalB`, 15 tags). All four
  `inductive {D4,D5,D45,DB}Axiom` definitions unmodified and still present (grep-confirmed). Zero
  `sorry`, zero new axiom (`lean_verify` on `d45Tags_of_schemaUnion` and `dbTags_of_schemaUnion`
  report only `propext`/`Quot.sound`). Scoped `lake build` of all four modules green; rebuilt the
  `Instances` barrel, `SchemaBridges.lean`, `AxiomSubsumption.lean`, `IntToClassical.lean` green.
  `checkInitImports` clean; `lint-style` clean; `lake lint --builtin-lint` clean. Net line delta:
  +223/-61 across the four files.

**Depends on**: 3 (bridges) and 6 (IntToClassical migrated first, so instance-side changes never
strand a live cross-family witness site).

**Files to modify**: `Cslib/Logics/Modal/ProofSystem/Instances/{15 files}.lean` (registrations
only; inductive definitions untouched until Phase 8).

**Verification (each sub-phase)**:
- Scoped `lake build` of each touched `Instances/*.lean` module green after the group.
- Every `HasAxiom*` instance still resolves under its original name; zero-`sorry`; inductives still present.
- **Done when**: all 15 instances discharge their fields from `SchemaUnion` and build sorry-free,
  with the inductives still defined; commit per group.

**Phase completion note**: All four sub-phases (7.1-7.4) landed across the 15
`Cslib/Logics/Modal/ProofSystem/Instances/*.lean` files. The plan's literal mechanism (importing
`SchemaBridges.lean`'s bridge lemma directly into each `Instances/*.lean` file) is architecturally
blocked by a genuine import cycle — empirically confirmed at the start of 7.1 via a direct
`lake build` attempt (`SchemaBridges.lean` imports the `Instances` barrel, which imports every
individual `Instances/{sys}.lean` file, so the reverse import is a cycle, not a naming issue).
The resolution (recorded in full above 7.1, applied uniformly across 7.1-7.4): each
`Instances/{sys}.lean` file imports only `Cslib.Logics.Modal.ProofSystem.SchemaUnion` (verified
acyclic) and gains one `private theorem {sys}Tags_of_schemaUnion`, a file-local reproduction of
that system's Phase-3 bridge's forward (`SchemaUnion → <Sys>Axiom`) direction — structurally
identical to (and independently re-derived from, not copy-imported from) the corresponding
`schemaUnion_{sys}Tags_iff_{Sys}Axiom.mp` proof in `SchemaBridges.lean`. `private` scoping
prevents any name collision with `SchemaBridges.lean`'s public bridge names in any downstream
file that imports both. Every one of the ~211 `HasAxiom*` registration fields across the 15 files
now reads `({sys}Tags_of_schemaUnion ⟨.tag, by decide, _, …, rfl⟩)` instead of a raw
`<Sys>Axiom.ctor _ …` / `ModalAxiom.ctor _ …` call — S5 is the one structural special case (no
local inductive; discharges against the pre-existing `Modal.ModalAxiom` in
`Metalogic/DerivationTree.lean`, subject to the identical cycle and identical resolution since
`Instances/S5.lean` is still part of the barrel `SchemaBridges.lean` imports). All 15 target
inductives (`KAxiom, TAxiom, DAxiom, BAxiom, K4Axiom, K5Axiom, K45Axiom, S4Axiom, TBAxiom,
KB5Axiom, D4Axiom, D5Axiom, D45Axiom, DBAxiom` in their respective `Instances/*.lean` files, plus
`ModalAxiom` in `Metalogic/DerivationTree.lean`) are grep-confirmed still defined and completely
unmodified — ready for Phase 8's redefinition. Zero `sorry` across all 15 files (full grep), zero
new axiom (spot-checked via `lean_verify` on one private helper per sub-phase group — all report
only `propext`/`Quot.sound`). Every `HasAxiom*` instance still resolves under its original
name/signature (confirmed by successful typeclass-directed elaboration during scoped builds — a
field-name or signature mismatch would have failed to elaborate against the `HasAxiom*` class).
Scoped `lake build` of all 15 modules green; `Instances` barrel, `SchemaBridges.lean`,
`AxiomSubsumption.lean`, and `IntToClassical.lean` (every file that transitively imports any of
the 15) rebuilt green after each sub-phase, confirming no downstream breakage at any point.
`lake exe checkInitImports`, `lake exe lint-style`, and `lake lint --builtin-lint` all clean
throughout (no new environment or text lint violations; the only build warnings seen anywhere are
pre-existing `linter.flexible` notes in `Modal/Basic.lean`, unrelated to this phase). Net line
delta across the 15 files: +817/-220 = **+597 lines net** (the file-local private bridge
duplication, one clear, disclosed, and necessary consequence of the import-cycle finding, is the
entire reason this phase is line-positive rather than roughly neutral — Phase 8 is expected to
delete all 15 private helpers alongside their target inductives, recovering a large net deletion
at that point). Next phase: Phase 8 (delete the 15 inductives + `ModalAxiom` disposition,
finalize) — depends on 4, 5, 6, 7 (all now complete).

---

### Phase 8: Redefine-in-place finish — retire inductives + full scaffolding removal [COMPLETED]

**Goal**: The terminal, once-everything-else-is-green step: **redefine each `<Sys>Axiom` in place**
as `SchemaUnion sysTags` (preserving the public name, retiring the inductive), resolve S5's
`ModalAxiom` the same way, and — per the resolved THOROUGH-finish decision (user, 2026-07-19) —
remove ALL scaffolding: simplify the ~78 now-trivial bridge call sites, delete `SchemaBridges.lean`
and the 15 Phase-7 private helpers entirely, and confirm the net-line-negative result.

**End-state design decision (redefine, do NOT delete-and-alias)** — replace each `<Sys>Axiom`
*inductive* with `<Sys>Axiom := SchemaUnion sysTags` (the same name, now compositionally defined).
The 13-line duplication dies; the *name* survives by redefinition, so downstream references and the
`HasAxiom*` instances keep resolving with NO rename and NO deprecated alias. The elimination-form
migration already happened in Phases 4/6/7, so the constructorless form is safe here.

**Reducibility (THOROUGH finish, user 2026-07-19)**: prefer `abbrev <Sys>Axiom := SchemaUnion
sysTags` so `<Sys>Axiom φ` and `SchemaUnion sysTags φ` are definitionally interchangeable and the
~78 bridge conversions collapse to identities that can be dropped outright. If `abbrev` causes
over-eager unfolding, `simp`-loop, elaboration-perf, or unreadable-goal problems anywhere, fall
back to `def <Sys>Axiom := SchemaUnion sysTags` + a `@[simp]` unfolding lemma per system, and
record which systems needed the fallback and why. Either way the end state has NO surviving
`SchemaBridges.lean` and NO private helpers.

**Architecture note (import-cycle finding, Phase 7)**: `SchemaBridges.lean` imports the `Instances`
barrel, so `Instances/*.lean` cannot import it. The tag sets (`kCore` + the 15 `sysTags`) currently
live in `SchemaBridges.lean` and MUST be relocated to a foundational file importing only
`SchemaUnion.lean` before the inductives can be redefined in terms of them — this is sub-phase 8.1.
The tag sets belong at the foundation anyway (a system's tag set is its essence, not scaffolding).

**Sub-phase 8.1 — relocate tag sets to a foundational file** [COMPLETED]
- [x] Create `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (imports only `SchemaUnion.lean`);
      move `kCore` + the 15 `sysTags` definitions there from `SchemaBridges.lean`.
- [x] Point `SchemaBridges.lean` (and any other current user of the tag sets) at `SchemaTags.lean`;
      bridges stay intact and green for now. Pure move, no semantic change.
- Verify: scoped `lake build` of `SchemaTags`, `SchemaBridges`, and downstream green; zero `sorry`.
      DONE — `lake build Cslib.Logics.Modal.ProofSystem.SchemaTags`,
      `...SchemaBridges`, and `...Metalogic.InterSystem.AxiomSubsumption` all green;
      `lake exe checkInitImports` clean; zero `sorry` in touched files.

**Sub-phase 8.2 — migrate the 15 `Completeness.lean` witness sites (additive)** [COMPLETED]

Discovered during the first 8.2 attempt (finding preserved below under the old 8.2 heading, now
8.3): all 15 `Systems/*/Completeness.lean` files construct axiom witnesses via constructors
(~364 sites total, e.g. `(fun φ ψ => .implyK φ ψ)` and `(fun φ => D4Axiom.modalD φ)` callbacks
passed into the canonical-model/truth-lemma machinery). The research blast-radius table wrongly
marked `Completeness.lean` "insulated"; it is in fact the LARGEST constructor consumer, and no
earlier phase touched it. These must be migrated BEFORE the inductives can be redefined (8.3).

**Approach — additive, bridge-based, proof-internals UNTOUCHED**: convert each construction
callback to the `SchemaUnion` existential-witness form wrapped through the Phase-3 bridge, so it
still yields a genuine `<Sys>Axiom` value while the inductive is LIVE:
`(fun φ ψ => .implyK φ ψ)` → `(fun φ ψ => (schemaUnion_sysTags_iff_SysAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)`.
Because the callback still produces a `<Sys>Axiom` value, the generic completeness lemmas that
CONSUME these callbacks (`d_canonical_serial`, `canonical_trans`, the truth lemmas, …) are NOT
touched — only the witness *construction* changes. `Completeness.lean` imports `SchemaBridges.lean`
+ `SchemaTags.lean` (no cycle: `SchemaBridges` imports the `ProofSystem/Instances` barrel, not
`Metalogic/Systems/*/Completeness`). After the 8.3 `abbrev` redefinition these bridge wrappers
become identities and are dropped in 8.4.

- [x] 8.2a — `Systems/{K,T,D,B}/Completeness.lean`: migrate all constructor-witness sites to the
      bridge form above. Scoped `lake build` of each module green; zero `sorry`. Commit.
      DONE — commit `30d3c807` (110 sites: K 33, T 25, D 27, B 25).
- [x] 8.2b — `Systems/{K4,K5,K45,S4}/Completeness.lean`. Commit.
      DONE — commit `837b6551`.
- [x] 8.2c — `Systems/{S5,TB,KB5}/Completeness.lean` (S5 via the `ModalAxiom` bridge). Commit.
      DONE — commit `8068ef15`.
- [x] 8.2d — `Systems/{D4,D5,D45,DB}/Completeness.lean` (these carry explicit named `<Sys>Axiom.ctor`
      forms too — migrate both the named and the anonymous-dot shapes). Commit.
      DONE — commit `d0c319aa` (126 sites: D4 30 = 8 named + 22 anon, D5 31 = 9 named + 22 anon,
      D45 34 = 12 named + 22 anon, DB 31 = 9 named + 22 anon).
- Verify (each group): scoped `lake build` of each touched `Completeness.lean` green; the generic
  completeness lemmas unchanged; zero `sorry`, no new axiom. The inductives stay LIVE.
      DONE — all 15 modules build green together (`lake build` of all 15 `Completeness`
      targets, 696 jobs, zero errors); `grep -rn sorry` over all 15 files returns nothing;
      `lean_verify` spot-checks (one per group) show only `propext`, `Classical.choice`,
      `Quot.sound`; `lake exe checkInitImports` and scoped `lake lint` clean.
- **Done when**: grep finds NO remaining constructor-construction site (`.ctor` / `<Sys>Axiom.ctor`)
  for any `<Sys>Axiom`/`ModalAxiom` across all of `Cslib/` — i.e. 8.3's grep-gate will pass.
      CONFIRMED — final repo-wide grep-gate (run once, after all four groups landed):
      `grep -rnE '\(fun [^=]*=> \.[A-Za-z0-9]+ [^)]*\)' Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean`
      and
      `grep -rnE '(K|T|D|B|K4|K5|K45|S4|S5|TB|KB5|D4|D5|D45|DB)Axiom\.(implyK|implyS|efq|peirce|modalK|modalT|modalD|modalB|modalFour|modalFive|andI|andE1|andE2|orI1|orI2|orE|diaDualityFwd|diaDualityBack) ' Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean`
      both return **no matches** (exit 1) across all 15 files. A supplementary check of the
      previously-migrated consumer files (`Systems/*/Soundness.lean`, `InterSystem/*.lean`,
      `ProofSystem/Instances/*.lean`, `Metalogic/DerivationTree.lean`) also returns no matches
      outside `SchemaBridges.lean`/`IntToClassical.lean` (the bridge definitions and their
      Phase-6 reference usage, which are supposed to contain these forms). 8.3's grep-gate is
      confirmed clean; sub-phase 8.3 (redefine the inductives) may proceed as a separate
      dispatch. Note: intuitionistic/constructive families (`IS4Axiom`, `CS5Canonical`,
      `OrImpConservative`) also use `.implyK`/`.efq`/etc.-style anonymous constructors against
      their OWN unrelated inductives — these are explicitly out of scope for the schema-union
      rollout (SchemaUnion.lean's design invariants exclude intuitionistic/minimal families) and
      were excluded from the grep-gate scope.

**Sub-phase 8.3 — redefine the inductives; trivialize bridges; delete private helpers** [COMPLETED]

*(Unblocked once 8.2 lands and the grep-gate below passes. The blocker finding from the first
attempt is preserved verbatim as the first task's note.)*
- [x] Confirm (grep) no *constructor* (`.ctor`) construction/destructuring site targets any
      `<Sys>Axiom`/`ModalAxiom` inductive (migrated in Phases 4/6/7 AND now 8.2). Predicate references remain.
      **FIRST-ATTEMPT FINDING (now addressed by 8.2): this check FAILED on the first try.** All 15 `Systems/*/Completeness.lean` files
      (`K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB`) contain live constructor-construction
      sites for the very inductives Phase 8.2 would retire — NOT migrated in Phases 4/6/7 (those
      phases touched `Soundness.lean`, `AxiomSubsumption.lean`, `IntToClassical.lean`, and the
      instance registrations; `Completeness.lean` was out of scope for all of them and is not
      listed anywhere in this Phase 8 section's "Files to modify"). Two concrete shapes found:
      1. Explicit named constructors in `D4`, `D5`, `D45`, `DB`'s `Completeness.lean` (e.g.
         `Cslib/Logics/Modal/Metalogic/Systems/D4/Completeness.lean:60-64`:
         `(fun φ ψ => D4Axiom.implyK φ ψ) (fun φ ψ χ => D4Axiom.implyS φ ψ χ) (fun φ => D4Axiom.efq φ)
         (fun φ ψ => D4Axiom.modalK φ ψ) (fun φ => D4Axiom.modalD φ) ... (fun φ => D4Axiom.modalFour φ)`,
         passed as constructor-witness callbacks into the generic lemmas `d_canonical_serial` /
         `canonical_trans` (from `Systems/D/Completeness.lean`) and `Systems/S4/Completeness.lean`'s
         analogue). `D4Axiom.implyK` etc. are literal declared-name dot-projections onto the
         `D4Axiom` inductive's constructors; they do not exist once `D4Axiom` is redefined as
         `abbrev/def := SchemaUnion d4Tags` (a `def`, not an inductive/structure) — this is a
         hard "unknown identifier" compile failure, not a warning.
      2. Anonymous-constructor dot-notation in ALL 15 files' `..._truth_lemma`-shaped call sites
         (e.g. `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean:425-450`,
         `Systems/K/Completeness.lean:341-353`, `Systems/S5/Completeness.lean:76-84`, etc.):
         `(fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) (fun φ => .efq φ) ...` — elaborated
         against the expected type `∀ φ ψ, Axioms (...)` with `Axioms` unified to the concrete
         `<Sys>Axiom`/`ModalAxiom` from the enclosing theorem's `CanonicalWorld (@<Sys>Axiom Atom)`
         argument, so `.implyK` resolves to `<Sys>Axiom.implyK` (a constructor projection) exactly
         as in case 1 — same failure mode once the inductive is retired.
      Per this sub-phase's own instruction ("If any live constructor site remains, STOP and
      report it — do not proceed to redefinition") and the dispatch's plan-compliance escalation
      rule, redefinition is NOT performed. Fixing `Completeness.lean` (15 files, not listed in
      this phase's file scope, and explicitly reserved call-site work belongs with 8.3-style
      call-site simplification) is out of scope for this dispatch. See handoff for the full
      blocker record and next-step recommendation (a dedicated sub-phase, e.g. 8.1.5 or folded
      into 8.2, to migrate these 15 `Completeness.lean` files to the `SchemaUnion`
      existential-witness form — mirroring the `⟨.tag, by decide, …, rfl⟩` pattern already used
      in `IntToClassical.lean` and the Phase-7 private helpers — BEFORE the inductives can be
      redefined).
- [x] Redefine the 14 `<Sys>Axiom` in `Instances/*.lean` and S5's `ModalAxiom`
      (`Metalogic/DerivationTree.lean:64`) as `abbrev/def := SchemaUnion sysTags` (per the
      reducibility decision above), importing `SchemaTags.lean`. Delete the 15 Phase-7 private
      `{sys}Tags_of_schemaUnion` helpers (now redundant).
      DONE — `abbrev` used for all 15 systems (no fallback to `def` was needed anywhere;
      no over-eager-unfolding/simp-loop/elaboration-perf/readability problems observed).
      Landed in 4 committed sub-groups: 8.3a (K,T,D,B — commit `d9fe0c8b`), 8.3b
      (K4,K5,K45,S4 — commit `4d0383b1`), 8.3c (S5 via `ModalAxiom`,TB,KB5 — commit
      `6a51dfaa`), 8.3d (D4,D5,D45,DB — commit `87560f3a`). Each system's private helper's
      callers (the `HasAxiom*` instance registrations in the same file) were updated to use
      the bare `⟨tag, by decide, …, rfl⟩` witness directly (now type-checks against the
      abbrev-unfolded `SchemaUnion` form).
- [x] Replace each bridge proof in `SchemaBridges.lean` with `Iff.rfl` (or delete it if unused after
      8.3) so the file still compiles at this checkpoint.
      DONE — all 15 bridge theorems in `SchemaBridges.lean` now read `:= Iff.rfl`; the file
      is kept (not deleted) per this sub-phase's scope — deletion is 8.4.
- Verify: scoped `lake build` of Instances barrel, DerivationTree, SchemaBridges, and the three S5
      consumers (`MCS.lean`, `Metalogic/Soundness.lean`, `Bimodal/…/ModalConservativity.lean`) green;
      inductives grep-confirmed gone; every public name still resolves; zero `sorry`, no new axiom.
      DONE — all scoped builds green (`lake build` of the Instances barrel, SchemaBridges,
      DerivationTree, MCS, Metalogic/Soundness, and
      Bimodal/.../ModalConservativity all succeed); repo-wide grep for `inductive
      <Sys>Axiom `/`inductive ModalAxiom ` returns no matches (all 15 retired); `lean_verify`
      on `k_soundness`, `s5_soundness`, and `KAxiom_implies_TAxiom` shows only
      `propext`/`Classical.choice`/`Quot.sound` (no new axiom); zero `sorry` in any file
      touched this sub-phase; `lake exe checkInitImports` clean.

**Sub-phase 8.4 — simplify ALL bridge call sites; delete scaffolding; final full verify** [COMPLETED]
- [x] Simplify the bridge call sites now that the `abbrev` forms are interchangeable (drop the
      `(bridge.mp/.mpr …)` wrappers, leaving the bare `SchemaUnion` witness / hypothesis):
      `Systems/*/Completeness.lean` (~364 sites from 8.2), `Systems/*/Soundness.lean` (15 files),
      `InterSystem/AxiomSubsumption.lean` (48 refs), `InterSystem/IntToClassical.lean` (15 refs).
      Do this per-group with scoped green builds, not one monolithic edit.
      DONE — 8.4a (432 sites across all 15 `Completeness.lean` files, 4 sub-groups:
      K/T/D/B, K4/K5/K45/S4, S5/TB/KB5, D4/D5/D45/DB, each scoped-build green and
      committed); 8.4b (15 `Soundness.lean` files, one site each, same 4 sub-groups);
      8.4c (`AxiomSubsumption.lean`, all 24 direct-edge lemmas simplified to
      `SchemaUnion.subsumption (by decide) h`); 8.4d (`IntToClassical.lean`, 12 code
      sites + stale docstring references updated). Every `SchemaBridges` import dropped
      from all 32 consumer files.
- [x] Delete `SchemaBridges.lean` entirely (its bridges are now identities with no remaining users);
      keep any lemma that is genuinely public API only behind a `@[deprecated]` alias in an acyclic
      location — expected: none survive.
      DONE — repo-wide grep confirmed zero remaining `schemaUnion_..._iff_...` call sites and
      zero remaining imports of `ProofSystem.SchemaBridges` outside the file itself before
      deletion; none of the 15 bridge lemmas were public API relied on elsewhere, so no
      `@[deprecated]` alias was needed. File deleted; full `lake build` green immediately
      after.
- [x] Final FULL `lake build`; `lake exe checkInitImports`; `lake lint`; `lake exe lint-style`;
      `lake test`; `lake exe mk_all --module` (barrel update for the new/removed files);
      `lean_verify` on `k_soundness`, an S5 soundness lemma, `KAxiom_implies_TAxiom`, and `unionSound`
      to confirm no `sorry` and no new axiom.
      DONE — all 7 CI steps green: full `lake build` (3250/3250 jobs), `checkInitImports`
      clean, `lake lint` clean, `lake exe lint-style` clean, `lake test` green (9242/9242
      jobs), `mk_all --module` added `SchemaSoundness`/`SchemaTags`/`SchemaUnion` to the
      barrel (previously missing) with `SchemaBridges` naturally absent, `lake shake`
      flagged zero of this sub-phase's touched files (repo-wide pre-existing shake debt
      in unrelated Propositional/Temporal modules only, out of scope). `lean_verify`:
      `k_soundness`, `s5_soundness`, `KAxiom_implies_TAxiom`, `unionSound` all show only
      `propext`/`Classical.choice`/`Quot.sound` (or a subset), zero `sorry`.
- [x] Confirm net line count is negative vs. the pre-refactor baseline (the Phase-7 +597 reverses here).
      DONE — `git diff --numstat ad2d13d6^ HEAD -- Cslib/Logics/Modal/` (baseline = parent
      of the first task-523 code commit) excluding the two files touched by the
      concurrent task-517/537 session (`Constructive/Labelled/{Completeness,Soundness}.lean`,
      pure additions unrelated to this refactor): **+1483/-2105, net -622 lines**. Even
      including those two unrelated files the whole-`Modal/` net is still negative (-40).

**Estimated output**: ~400-700 lines of net deletion + re-route edits, across three committed
sub-phases. **Depends on**: 4, 5, 6, 7.

**Files to modify**:
- NEW `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (relocated tag sets).
- `Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}.lean`
  (inductive → `abbrev/def := SchemaUnion sysTags`; private helper deleted).
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` — `ModalAxiom` redefinition.
- `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean`, `InterSystem/AxiomSubsumption.lean`,
  `InterSystem/IntToClassical.lean` — bridge-call-site simplification (8.3).
- DELETE `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean`.
- `MCS.lean`, `Metalogic/Soundness.lean`, `Bimodal/…/ModalConservativity.lean` — only if the S5
  redefinition needs a re-route (expected: none, since `ModalAxiom` keeps its name).
- `Cslib.lean` barrel — via `mk_all --module` (new `SchemaTags`, removed `SchemaBridges`).

**Verification**:
- Full `lake build` + `lake lint` + `lake exe lint-style` + `lake test` green; zero-`sorry`; no new
  axiom (`lean_verify`).
- All 15 inductives retired; `SchemaBridges.lean` and the 15 private helpers gone; every prior public
  theorem/instance name resolves (direct, since names are preserved by redefinition).
- Net line count negative vs. baseline.
- **Done when**: the whole library builds sorry-free with the inductives gone, no scaffolding
  remaining, and public API intact.

---

### Pre-PR user step (non-blocking courtesy — NOT a phase, NOT a gate)

Before the user runs `/pr` on the completed branch, post a brief Zulip heads-up to the #CSLib
channel noting the large-blast-radius (but net-line-negative) landing of the schema-union
combinator, so maintainers are not surprised by the diff. **The design decision has already
landed** — this is a courtesy notice, not a design gate, and it does not block any implementation
phase. A ready-to-post draft is in plans/01 Appendix A (trim to a "landing shortly" note). This
step is the user's to perform; agents do not post to Zulip or create the PR.

## Testing & Validation

- [x] Scoped `lake build` green after EVERY sub-phase (additive/staged discipline — every
      intermediate commit CI-green).
- [x] No `sorry` and no new `axiom` at any intermediate state (`grep -n sorry` on touched files;
      `lean_verify` spot-checks on `k_soundness`, an S5 soundness lemma, a representative
      `XAxiom_implies_YAxiom` fact, and `unionSound`).
- [x] Public API surface unchanged: `k_soundness`, the S5 soundness lemmas, `KAxiom_implies_TAxiom`
      (+ 23 siblings), the `HasAxiom*` instances resolve at every stage (stable or deprecated alias).
- [x] The deliberately-absent `KB5 → S5` subsumption edge remains absent.
- [x] Final full `lake build` green and net line-negative vs. the pre-refactor baseline.
- [x] CSLib CI pipeline / `/vet` clean before the user runs `/pr`.

## Artifacts & Outputs

- plans/02_schema-union-per-file-rollout.md (this per-file execution plan)
- plans/01_schema-union-staged-rollout.md (superseded design + staging doc; Appendix A Zulip draft)
- NEW Lean files (proposed): `ProofSystem/SchemaUnion.lean`, `Metalogic/SchemaSoundness.lean`,
  `ProofSystem/SchemaBridges.lean`
- summaries/NN_{short-slug}-summary.md (after implementation completes)

## Rollback/Contingency

- **Additive-rollout revert**: because the combinator is introduced alongside the inductives with
  bridge lemmas (Phases 1-3), any later sub-phase can be reverted independently by dropping its
  commit — the prior green state is preserved. Inductive deletion (Phase 8) is deliberately last
  and reversible until the PR merges.
- **If a sub-phase cannot close sorry-free**: mark that sub-phase `[BLOCKED]` with the open goal
  state recorded; never commit a `sorry` or new axiom (zero-debt mandate).
- **S5 disposition branch**: if deleting `ModalAxiom` at Phase 8 proves to strand a consumer, take
  the "keep + bridge" branch instead of forcing the deletion — the refactor still succeeds with
  `ModalAxiom` retained behind its bridge.
- **Break-glass (Representation B)**: only if Representation A hits an unforeseen hard blocker
  (e.g. `fin_cases`/`Finset` elaboration cost proves intractable at scale), fall back to
  macro-generated flat inductives (v1 Contingency). This reverses the settled design decision and
  therefore requires explicit user sign-off — it is NOT an in-flight option.
