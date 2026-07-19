# Implementation Plan: Schema-Union Axiom Combinator for Modal ProofSystem Instances (v2)

- **Task**: 523 - Replace the 15 hand-written per-system axiom inductives with a compositional schema-union combinator
- **Status**: [IMPLEMENTING]
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

### Phase 4: Migrate 15 per-system soundness proofs to `unionSound` [NOT STARTED]

**Goal**: Replace each `Systems/*/Soundness.lean` case-split with a `unionSound` call fed by that
system's tag→validity table (net deletion), one small group per agent run. Public soundness
theorem names stay stable; use the Phase 3 bridge where a caller still expects the inductive form.

**Sub-phase 4.1 — K, T, D, B** [NOT STARTED]
- [ ] Rewrite `<sys>_axiom_sound` (K/T/D/B) through `unionSound` + the per-system tag→validity table.
- Files: `Systems/{K,T,D,B}/Soundness.lean`. Estimated output: ~120-220 lines net (deletion-heavy).

**Sub-phase 4.2 — K4, K5, K45, S4** [NOT STARTED]
- [ ] Rewrite the four soundness proofs through `unionSound`.
- Files: `Systems/{K4,K5,K45,S4}/Soundness.lean`. Estimated output: ~120-220 lines.

**Sub-phase 4.3 — S5, TB, KB5** [NOT STARTED]
- [ ] Rewrite the three soundness proofs; keep the S5 public soundness names stable.
- Files: `Systems/{S5,TB,KB5}/Soundness.lean`. Estimated output: ~100-200 lines.

**Sub-phase 4.4 — D4, D5, D45, DB** [NOT STARTED]
- [ ] Rewrite the four soundness proofs through `unionSound`.
- Files: `Systems/{D4,D5,D45,DB}/Soundness.lean`. Estimated output: ~120-220 lines.

**Depends on**: 2 (needs `unionSound`) and 3 (needs bridges + tag sets).

**Verification (each sub-phase)**:
- Scoped `lake build` of each touched `Systems/*/Soundness.lean` module green after the group.
- Public soundness theorem names unchanged (or deprecated alias); zero-`sorry`.
- **Done when**: every migrated soundness theorem discharges via `unionSound` with its original
  public name and no `sorry`; commit per group.

---

### Phase 5: Replace `AxiomSubsumption.lean` with `Finset.subset` facts [NOT STARTED]

**Goal**: Collapse the 24 hand-written `XAxiom_implies_YAxiom` lemmas (~524 lines) to
`Finset.subset`-backed facts via the Phase 1 generic subsumption lemma, then update the few call
sites. Net deletion.

**Sub-phase 5.1 — 24 subsumption facts** [NOT STARTED]
- [ ] Replace each of the 24 subsumption lemmas with a `Finset.subset` fact fed to the generic
      `subsumption` lemma; preserve each public lemma name (or provide a `@[deprecated]` alias).
- [ ] Verify the deliberately-omitted `KB5 → S5` edge stays omitted (S5 = T+4+B, not `modalFive`).
- File: `InterSystem/AxiomSubsumption.lean`. Estimated output: ~120-220 lines net (deletion-heavy).

**Sub-phase 5.2 — call-site name updates** [NOT STARTED]
- [ ] Update the (few) call sites in `Lifting.lean` / `Modularity.lean` that reference subsumption
      lemma names — call-site NAMES only, no structural change (these files are insulated).
- Files: `InterSystem/Lifting.lean`, `InterSystem/Modularity.lean`. Estimated output: ~30-80 lines.

**Depends on**: 1 (generic subsumption) and 3 (tag sets). Independent of Phase 4.

**Verification**:
- Scoped `lake build` of `AxiomSubsumption`, `Lifting`, `Modularity` green.
- All 24 subsumption facts proved via the generic lemma; zero-`sorry`; no `KB5 → S5` edge.
- **Done when**: `AxiomSubsumption.lean` contains no hand-written per-edge `match`, all 24 names
  resolve, and dependent files build; commit per sub-phase.

---

### Phase 6: Hand-migrate `IntToClassical.lean` (~36 sites) [NOT STARTED]

**Goal**: Perform the irreducible hand-migration of the ~36 constructor/destructuring sites in
`IntToClassical.lean` (774 lines) — genuine intuitionistic→classical derivation work plus
cross-family witness construction. NO inductive is deleted here. Split into per-cluster sub-phases;
the implementer partitions the ~36 sites into three balanced clusters at the start of 6.1 and
records the partition so 6.2/6.3 have fixed, non-overlapping scope.

**Sub-phase 6.1 — cluster 1 (destructuring sites, ~first third)** [NOT STARTED]
- [ ] Migrate the first ~12 sites: `cases … with | ctor` → `obtain ⟨t, ht, hφ⟩ := h; fin_cases t <;> …`
      (or via the Phase 3 bridge where cleaner).
- Estimated output: ~120-260 lines.

**Sub-phase 6.2 — cluster 2 (destructuring sites, ~second third)** [NOT STARTED]
- [ ] Migrate the next ~12 sites.
- Estimated output: ~120-260 lines.

**Sub-phase 6.3 — cluster 3 (witness-construction sites, `⟨.ax _ _ h⟩`)** [NOT STARTED]
- [ ] Migrate the remaining ~12 sites, prioritizing the cross-family witness constructions that
      build classical `KAxiom`/`ModalAxiom` witnesses; keep every out-of-scope intuitionistic/minimal
      call site typechecking (via the Phase 3 bridge).
- Estimated output: ~120-260 lines.

**Depends on**: 3 (needs bridges). Independent of Phases 4/5.

**Files to modify**: `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`.

**Verification (each sub-phase)**:
- Scoped `lake build Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical` green after each cluster.
- Zero-`sorry`; cross-family witness-construction sites still valid; no inductive deleted.
- **Done when**: all ~36 sites migrated across the three clusters, file builds sorry-free, and no
  `<Sys>Axiom`/`ModalAxiom` inductive has been removed; commit per cluster.

---

### Phase 7: Swap 15 instance registrations to `SchemaUnion` [NOT STARTED]

**Goal**: Rewrite each `HasAxiom*` instance registration in `Instances/*.lean` to discharge its
fields from `SchemaUnion` (via the Phase 3 bridge where convenient), replacing witness
constructions like `KAxiom.implyK _`. Inductives are NOT deleted here (that is Phase 8). Split into
per-cluster sub-phases (~4 files each).

**Sub-phase 7.1 — K, T, D, B** [NOT STARTED]
- [ ] Rewrite the `HasAxiom*` instance fields in `Instances/{K,T,D,B}.lean` to build from `SchemaUnion`.
- Estimated output: ~150-260 lines.

**Sub-phase 7.2 — K4, K5, K45, S4** [NOT STARTED]
- [ ] Rewrite `Instances/{K4,K5,K45,S4}.lean`.
- Estimated output: ~150-260 lines.

**Sub-phase 7.3 — S5, TB, KB5** [NOT STARTED]
- [ ] Rewrite `Instances/{S5,TB,KB5}.lean` (S5 discharges via the `ModalAxiom` bridge).
- Estimated output: ~120-220 lines.

**Sub-phase 7.4 — D4, D5, D45, DB** [NOT STARTED]
- [ ] Rewrite `Instances/{D4,D5,D45,DB}.lean`.
- Estimated output: ~150-260 lines.

**Depends on**: 3 (bridges) and 6 (IntToClassical migrated first, so instance-side changes never
strand a live cross-family witness site).

**Files to modify**: `Cslib/Logics/Modal/ProofSystem/Instances/{15 files}.lean` (registrations
only; inductive definitions untouched until Phase 8).

**Verification (each sub-phase)**:
- Scoped `lake build` of each touched `Instances/*.lean` module green after the group.
- Every `HasAxiom*` instance still resolves under its original name; zero-`sorry`; inductives still present.
- **Done when**: all 15 instances discharge their fields from `SchemaUnion` and build sorry-free,
  with the inductives still defined; commit per group.

---

### Phase 8: Delete the 15 inductives (+ `ModalAxiom` disposition), finalize [NOT STARTED]

**Goal**: The terminal, once-everything-else-is-green step: **redefine each `<Sys>Axiom` in place**
as a one-line `SchemaUnion` def (preserving the public name, retiring the inductive), resolve S5's
`ModalAxiom`, drop dead scaffolding bridges, and confirm the net-line-negative result.

**End-state design decision (redefine, do NOT delete-and-alias)** — the elegant, lower-churn
finish: replace each `<Sys>Axiom` *inductive* with `def <Sys>Axiom : Proposition Atom → Prop :=
SchemaUnion sysTags` (the same name, now compositionally defined). The 13-line duplication dies;
the *name* `<Sys>Axiom` survives by redefinition, so downstream references and the `HasAxiom*`
instances keep resolving with NO rename and NO deprecated alias for these names. The
elimination-form migration (`cases | ctor` → the Phase-2 elimination API) already happened in
Phases 4/6/7, so the constructorless `def` form is safe here. Once redefined, each Phase-3 bridge
`SchemaUnion sysTags φ ↔ <Sys>Axiom φ` becomes `Iff.rfl` and its lemma is deleted as dead
scaffolding.

**Tasks**:
- [ ] Confirm (grep) that no *constructor* construction/destructuring site (`.ctor` patterns)
      targets any `<Sys>Axiom` inductive — all such sites were migrated to the elimination API in
      Phases 4/6/7. (References to `<Sys>Axiom` as a *predicate* are expected and remain valid
      after redefinition.)
- [ ] Redefine the 14 `<Sys>Axiom` in `Instances/*.lean`: replace each `inductive <Sys>Axiom` with
      `def <Sys>Axiom : Proposition Atom → Prop := SchemaUnion sysTags` (name preserved). Add a
      `@[simp]` unfolding lemma per system where it aids downstream rewriting.
- [ ] Resolve S5's `ModalAxiom` (`Metalogic/DerivationTree.lean:64`) by the SAME redefine-in-place
      principle: prefer `def ModalAxiom : Proposition Atom → Prop := SchemaUnion s5Tags`, preserving
      the name so `MCS.lean`, `Metalogic/Soundness.lean`, and `Bimodal/…/ModalConservativity.lean`
      need no rewrite. Only if a constructor-level dependency in those three files genuinely blocks
      redefinition, fall back to keep-inductive-plus-bridge (record which branch was taken and why).
- [ ] Remove now-dead bridge lemmas that were pure scaffolding; keep any that remain public API
      (with `@[deprecated]` alias if a name was public).
- [ ] Final full `lake build`; `lean_verify` on `k_soundness`, an S5 soundness lemma, and a
      representative subsumption fact to confirm no `sorry` and no new axiom.
- [ ] Confirm net line count is negative vs. the pre-refactor baseline.

**Estimated output**: ~150-300 lines of net deletion + re-route edits. **Depends on**: 4, 5, 6, 7.

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}.lean`
  (each `inductive <Sys>Axiom` redefined in place as `def <Sys>Axiom := SchemaUnion sysTags`; name preserved).
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` — `ModalAxiom` disposition (conditional).
- `MCS.lean`, `Metalogic/Soundness.lean`, `Bimodal/…/ModalConservativity.lean` — conditional
  re-route if S5 unified.

**Verification**:
- Full `lake build` green; zero-`sorry`; no new axiom (`lean_verify`).
- All 15 inductives removed (or `ModalAxiom` retained per the recorded branch); every prior public
  theorem/instance name resolves (direct or via alias).
- Net line count negative vs. baseline.
- **Done when**: the whole library builds sorry-free with the inductives gone and public API intact.

---

### Pre-PR user step (non-blocking courtesy — NOT a phase, NOT a gate)

Before the user runs `/pr` on the completed branch, post a brief Zulip heads-up to the #CSLib
channel noting the large-blast-radius (but net-line-negative) landing of the schema-union
combinator, so maintainers are not surprised by the diff. **The design decision has already
landed** — this is a courtesy notice, not a design gate, and it does not block any implementation
phase. A ready-to-post draft is in plans/01 Appendix A (trim to a "landing shortly" note). This
step is the user's to perform; agents do not post to Zulip or create the PR.

## Testing & Validation

- [ ] Scoped `lake build` green after EVERY sub-phase (additive/staged discipline — every
      intermediate commit CI-green).
- [ ] No `sorry` and no new `axiom` at any intermediate state (`grep -n sorry` on touched files;
      `lean_verify` spot-checks on `k_soundness`, an S5 soundness lemma, a representative
      `XAxiom_implies_YAxiom` fact, and `unionSound`).
- [ ] Public API surface unchanged: `k_soundness`, the S5 soundness lemmas, `KAxiom_implies_TAxiom`
      (+ 23 siblings), the `HasAxiom*` instances resolve at every stage (stable or deprecated alias).
- [ ] The deliberately-absent `KB5 → S5` subsumption edge remains absent.
- [ ] Final full `lake build` green and net line-negative vs. the pre-refactor baseline.
- [ ] CSLib CI pipeline / `/vet` clean before the user runs `/pr`.

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
