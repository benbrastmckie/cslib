# Implementation Plan: Modal Axiom-Schema Architecture Documentation

- **Task**: 536 - Document the modal axiom-schema architecture in a new docs/ directory
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours
- **Dependencies**: 523 (schema-union axiom combinator; status: completed)
- **Research Inputs**: reports/01_modal-axiom-schema-architecture.md
- **Artifacts**: plans/01_modal-axiom-schema-architecture.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; .claude/rules/no-task-references-in-deliverables.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Author one durable architecture document, `docs/modal-axiom-schema-architecture.md` (new file in a
new repo-root `docs/` directory), explaining the compositional design that the `SchemaUnion`
combinator and the `FrameCorrespondence` library together establish across CSLib's modal-logic
layer. The document covers seven areas (schema-tag alphabet, subsumption-as-`Finset.subset`,
compositional soundness via `unionSound`, the `HasAxiom*` insulation layer, the S5=T+4+B
disposition, the Representation A vs B rationale, and the intuitionistic/minimal scope boundary),
each anchored to real module paths, def/lemma/typeclass names, and verified Lean signatures — never
to task numbers. Definition of done: a single self-contained markdown file whose every code claim
is traceable to a named on-disk anchor, that reconciles the "14 retired inductives + S5's
pre-existing `ModalAxiom`" count correctly, that disambiguates the pre-existing semantic
`Cube.lean` from the new syntactic tag-set cube, and that contains zero task-number citations.

### Research Integration

The research report (`reports/01_modal-axiom-schema-architecture.md`) is the primary input and is
already verified against the landed, CI-green code. It supplies: the exact 18-constructor
`ModalSchemaTag` listing (grouped 4+1+5+6+2), the verified signatures for `ModalSchemaTag.Holds`,
`SchemaUnion`, `SchemaUnion.subsumption`, the three `@[simp]` elimination lemmas, `FrameValidatesTag`,
`unionSound`, and the five `Satisfies.modal*_axiom` frame-correspondence lemmas; the 15 per-system
tag-set definitions and the 24 subsumption edges; the confirmation that `ModalAxiom` is
`abbrev ModalAxiom := SchemaUnion s5Tags` (DerivationTree.lean:69) so S5 is the 15th system in the
one-line-abbrev pattern, not an outlier; the mechanical `modalFive ∈ kb5Tags`, `modalFive ∉ s5Tags`
account of the omitted KB5→S5 edge; the Representation A/B trade-off; and a complete durable-anchor
index (report Appendix) the writer cross-references directly. Two report-flagged nuances are
elevated to hard constraints below.

### Prior Plan Reference

No prior plan for this task. (The rollout plans under `specs/523_.../plans/` are source material
already distilled into the research report, not templates for this documentation plan.)

### Roadmap Alignment

No roadmap context was provided to this planning dispatch; no ROADMAP.md phases are included.

## Goals & Non-Goals

**Goals**:
- Produce `docs/modal-axiom-schema-architecture.md` covering all seven areas, each mapped to a
  dedicated top-level section.
- Ground every structural claim in a durable anchor (module path, def/lemma/typeclass name) and
  embed the verified Lean signatures from the research report as fenced `lean` code blocks where
  they clarify the prose.
- Present the design's two payoffs explicitly: subsumption collapses to one generic
  `SchemaUnion.subsumption` + `decide`-able `Finset.subset` facts, and soundness collapses to one
  `unionSound` consuming an 18-entry `FrameValidatesTag` table plus the five frame-correspondence
  lemmas.
- Reconcile the axiom-inductive count precisely: **14 retired per-system `<Sys>Axiom` inductives +
  S5's pre-existing `ModalAxiom` (now `abbrev SchemaUnion s5Tags`)**, unifying 15 classical normal
  modal systems.
- Disambiguate `Cslib/Logics/Modal/Cube.lean` (pre-existing SEMANTIC frame-class cube) from the new
  SYNTACTIC `Finset`-tag-set cube in `AxiomSubsumption.lean` / `SchemaTags.lean`.

**Non-Goals**:
- No Lean code is written, edited, or built; this is a prose deliverable only.
- No generalization of the design to intuitionistic/minimal families (documented as future scope,
  not implemented).
- No modification of any `specs/**` artifact beyond this task's own plan/summary/metadata, and no
  edits to existing repo-root prose files (`README.md`, `CONTRIBUTING.md`, etc.).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task-number citation (522/523/536) leaks into `docs/` from copied source-docstring prose | H | M | Hard-constraint callout in every phase; dedicated grep scan in Phase 4 (`grep -nE 'task[ -]?[0-9]|522\|523\|536'`) before completion; substitute the module/file name for any task-number phrase encountered |
| Casual "15 inductives" phrasing contradicts the reconciled 14+ModalAxiom count | M | M | Phase 1 fixes the canonical phrasing in the overview and Area 1; later phases reuse that exact wording |
| Conflating `Cube.lean`'s semantic cube with the new syntactic tag-set cube | M | M | Phase 2 adds an explicit disambiguation note/footnote citing both file paths and their distinct meanings |
| Citing intuitionistic/minimal family file paths the research did not re-read directly | M | L | Phase 4 runs a `grep -rn` for `IKModalAxiom\|MKModalAxiom\|CKModalAxiom\|IS5ModalAxiom\|MTModalAxiom` to pin exact paths before citing them |
| Signature drift: a quoted signature no longer matches on-disk code | M | L | Signatures come from the already-verified report; Phase 4 spot-checks any quoted signature against the named source file with `grep`/`Read` if in doubt |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. All four phases edit the single deliverable
file `docs/modal-axiom-schema-architecture.md`, so they are inherently sequential (one wave each).

### Phase 1: Scaffold, overview, and Area 1 (schema-tag alphabet) [COMPLETED]

**Goal**: Create the `docs/` directory and the document skeleton, write the overview, and author
Area 1 (the vocabulary the whole design rests on).

**Tasks**:
- [x] Create the `docs/` directory at the repository root if absent (`mkdir -p docs`). *(completed)*
- [x] Create `docs/modal-axiom-schema-architecture.md` with a title, a short abstract/overview, and
      an ordered section outline whose seven content sections map 1:1 to the task's seven areas
      (headings may be reworded for prose flow but must cover areas 1-7 in order). *(completed)*
- [x] In the overview, state the canonical count phrasing exactly once and reuse it verbatim
      elsewhere: **"15 classical normal modal systems, unified under 14 renamed `<Sys>Axiom`
      abbreviations plus S5's pre-existing `ModalAxiom`"** — do NOT write "15 inductives".
      *(completed)*
- [x] Write the Area 1 section covering: the 18-constructor `ModalSchemaTag` inductive (embed the
      verified `inductive ModalSchemaTag` block and reproduce the 4+1+5+6+2 role grouping —
      propositional core / K-distribution / 5 modal-strength differentiators / and-or / diamond
      duality); `ModalSchemaTag.Holds` as the existential "schema = set of its instances" meaning
      function (embed the signature with 2-3 representative clauses); the
      `SchemaUnion (S : Finset ModalSchemaTag)` combinator (embed signature); and the ergonomics
      half — the three `@[simp]` elimination lemmas `SchemaUnion.empty_iff` / `insert_iff` /
      `union_iff`. State that every one of the 15 systems' axiom predicate is now a one-line
      `abbrev <Sys>Axiom := SchemaUnion sysTags`, and that S5's `ModalAxiom` is the 15th such
      abbrev (`abbrev ModalAxiom := SchemaUnion s5Tags`, `DerivationTree.lean:69`), not a special
      case. *(completed)*
- [x] Durable anchors this section must name: `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`,
      `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`,
      `Cslib/Logics/Modal/ProofSystem/Instances/{K,...,S5}.lean`. *(completed)*

**Timing**: ~1 hour

**Depends on**: none

**Files to modify**:
- `docs/modal-axiom-schema-architecture.md` - create; add header, overview, section outline, Area 1.

**Verification**:
- File exists and is non-empty; the seven-area outline is present in order.
- The canonical count phrasing appears and "15 inductives" does not.
- The `ModalSchemaTag` block lists exactly 18 constructors.

---

### Phase 2: Area 2 (subsumption as `Finset.subset`) and Area 3 (`unionSound` hinge) [COMPLETED]

**Goal**: Author the two "collapse" sections that are the core elegance argument — the syntactic
tag-set cube and the syntax/semantics soundness factorization.

**Tasks**:
- [x] Write the Area 2 section: `SchemaUnion.subsumption` (embed signature) as the single generic
      lemma replacing hand-written per-edge subsumption; explain that each `XAxiom_implies_YAxiom`
      is now `SchemaUnion.subsumption (by decide) h`, a `decide`-able `Finset.subset` fact holding
      because `ModalSchemaTag` is finite + `DecidableEq` and the 15 tag sets are concrete `Finset`
      literals over `kCore`. Reproduce the 15 per-system tag-set definitions (from
      `SchemaTags.lean`) and summarize the 24 direct edges (from `AxiomSubsumption.lean`); framing
      point: the modal cube K ⊂ T ⊂ S4 ⊂ S5 IS the `⊆`-order on tag sets. *(completed)*
- [x] Add the REQUIRED disambiguation note/footnote: `Cslib/Logics/Modal/Cube.lean` is a
      pre-existing, SEMANTIC frame-class cube (each system a `Set (Model World Atom)`), authored for
      a different purpose; it MUST NOT be conflated with the new SYNTACTIC tag-set cube in
      `AxiomSubsumption.lean` / `SchemaTags.lean`. Name both file paths explicitly. *(completed)*
- [x] Write the Area 3 section: the five frame-condition→validity lemmas
      `Satisfies.modalT_axiom` / `modalFour_axiom` / `modalB_axiom` / `modalD_axiom` /
      `modalFive_axiom` in `FrameCorrespondence.lean` (embed at least the `modalT` and `modalFour`
      signatures); `FrameValidatesTag` as the uniform 18-tag semantic obligation (`True` for the 13
      frame-unconditional tags, the raw frame condition for the 5 differentiators — embed
      signature); and `unionSound` (embed signature) as the master combinator whose proof is a
      single `cases t` over 18 tags, the 5 differentiator cases delegating to the corresponding
      `FrameCorrespondence` lemma. State plainly: the frame-correspondence library (semantic side)
      and the schema-union combinator (syntactic side) are two halves of one abstraction, with
      `unionSound` as the hinge. Reproduce the Blackburn/de Rijke/Venema *Modal Logic* Ch. 4 (Def
      4.9, Table 4.1) citation as a durable provenance anchor. *(completed)*
- [x] When drawing on `SchemaSoundness.lean`'s module docstring, replace its task-number phrasing
      (522/523) with the module names (`FrameCorrespondence.lean` semantic side /
      `SchemaUnion.lean` + `SchemaTags.lean` syntactic side). *(completed)*

**Timing**: ~1 hour

**Depends on**: 1

**Files to modify**:
- `docs/modal-axiom-schema-architecture.md` - append Area 2 and Area 3 sections.

**Verification**:
- Both sections present with embedded verified signatures.
- The `Cube.lean` disambiguation note is present and names both cube artifacts.
- No task-number phrase appears in the newly written prose.

---

### Phase 3: Area 4 (`HasAxiom*` insulation) and Area 5 (S5=T+4+B, omitted KB5→S5) [COMPLETED]

**Goal**: Author the insulation-layer section and the disposition section.

**Tasks**:
- [x] Write the Area 4 section: `Cslib/Foundations/Logic/ProofSystem.lean` defines one `HasAxiom*`
      typeclass per schema, each asserting `InferenceSystem.DerivableIn S (Axioms.X …)` — an
      assertion about *derivability of the axiom instance*, never about how the underlying
      `<Sys>Axiom` predicate is constructed (embed the representative `class HasAxiomT` signature).
      Explain the `extends` bundling into the `MinimalHilbert ⊂ IntuitionisticHilbert ⊂
      ClassicalHilbert ⊂ ModalHilbert ⊂ … ⊂ ModalS5Hilbert` hierarchy, and why this is
      "representation-agnostic insulation": an instance is discharged by constructing a
      `DerivationTree` witness (e.g. `⟨.modalT, by decide, _, rfl⟩`), so the typeclass never
      inspects `inductive` vs `SchemaUnion`. Note this is the load-bearing fact that made the
      refactor additive with zero blast radius at the `Systems/*/Completeness.lean` and
      `Systems/*/ConservativeExtension.lean` layers. *(completed)*
- [x] Write the Area 5 section: `s5Tags = kCore ∪ {modalT, modalFour, modalB}` (T+4+B, carries
      `modalB`, NOT `modalFive`) vs `kb5Tags = kCore ∪ {modalB, modalFive}`; since `modalFive ∈
      kb5Tags` but `modalFive ∉ s5Tags`, `kb5Tags ⊆ s5Tags` is false and `SchemaUnion.subsumption`
      cannot produce a `KB5Axiom_implies_ModalAxiom` lemma — the omission is a decidable
      consequence of the tag-set definitions, not an oversight. Use this as a worked example of the
      design's self-documenting property: a missing cube edge is now a mechanical `decide` failure
      readable straight from the two tag-set defs. Anchor to `s5Tags`/`kb5Tags` in `SchemaTags.lean`
      and the omission doc comment in `AxiomSubsumption.lean`. *(completed)*

**Timing**: ~45 minutes

**Depends on**: 2

**Files to modify**:
- `docs/modal-axiom-schema-architecture.md` - append Area 4 and Area 5 sections.

**Verification**:
- Both sections present with embedded signatures/tag-set equalities.
- Area 5 states the `modalFive ∈ kb5Tags`, `modalFive ∉ s5Tags` fact explicitly.

---

### Phase 4: Area 6 (Rep A vs B rationale), Area 7 (scope boundary), and final consistency pass [COMPLETED]

**Goal**: Author the rationale and scope-boundary sections, then run the whole-document consistency
and hard-constraint verification pass.

**Tasks**:
- [x] Write the Area 6 section: contrast Representation A (chosen — schema-tag `def` + `.Holds` +
      `SchemaUnion` over `Finset ModalSchemaTag`) against Representation B (rejected — macro-generated
      per-system inductives). Present the recorded trade-off in code/architecture vocabulary only
      (NO task numbers): Rep A collapses subsumption to one lemma + `decide` and soundness to one
      `unionSound` + an 18-entry table, ended net line-negative, and makes the cube's algebraic
      structure (a lattice of finite tag sets under `⊆`) directly visible and machine-checkable; Rep
      B minimizes downstream blast radius but only hides the same bespoke facts behind
      metaprogramming and does not deliver subsumption-as-`⊆` or soundness-as-per-tag-table.
      Conclude with why A was chosen for long-term foundations. *(completed)*
- [x] Write the Area 7 section: the scope boundary. `ModalSchemaTag`/`SchemaUnion` are kept free of
      classical-only assumptions so the intuitionistic/minimal families are a *future instance of
      the same abstraction, not a fork* — quote the "Design Invariants" docstring in
      `SchemaUnion.lean`. Explain that today's intuitionistic/minimal families
      (`IKModalAxiom`, `MKModalAxiom`, `CKModalAxiom`, `IS5ModalAxiom`, `MTModalAxiom`) were kept out
      of scope and construct witnesses *into* the classical predicates (cross-family coupling in
      `InterSystem/IntToClassical.lean`); the correct future move is to extend/parametrize the
      existing tag alphabet, not build a parallel `IntSchemaTag`/`IntSchemaUnion`. *(completed)*
- [x] Before citing the intuitionistic/minimal family paths, run
      `grep -rn "IKModalAxiom\|MKModalAxiom\|CKModalAxiom\|IS5ModalAxiom\|MTModalAxiom" Cslib/Logics/Modal/`
      to pin the exact file paths, and cite only paths confirmed to exist. *(completed: confirmed
      IK.lean, IS5.lean under Metalogic/Intuitionistic/, CK.lean under Metalogic/Constructive/,
      MK.lean and MT.lean under Metalogic/Minimal/, via `grep -rln "inductive
      IKModalAxiom\|inductive MKModalAxiom\|inductive CKModalAxiom\|inductive
      IS5ModalAxiom\|inductive MTModalAxiom" Cslib/Logics/Modal/`)*
- [x] Final consistency pass over the whole file:
      - [x] Run `grep -nE 'task[ -]?[0-9]|\b52[23]\b|\b536\b' docs/modal-axiom-schema-architecture.md`
            and confirm zero matches (no task-number citations anywhere). *(completed: zero matches,
            exit code 1)*
      - [x] Confirm the count phrasing is consistent throughout (14 retired inductives + S5's
            `ModalAxiom`; never "15 inductives"). *(completed: "15 inductives" grep also returns
            zero matches; canonical phrasing appears in Overview and is reused consistently)*
      - [x] Confirm the `Cube.lean` disambiguation is present. *(completed: Section 2's
            "Disambiguation" subsection with comparison table)*
      - [x] Spot-check any quoted Lean signature against its named source file (`grep`/`Read`) if
            there is any doubt about drift. *(completed: all signatures re-verified directly
            against source files during authoring — SchemaUnion.lean, SchemaTags.lean,
            FrameCorrespondence.lean, SchemaSoundness.lean, ProofSystem.lean,
            AxiomSubsumption.lean, Instances/S5.lean, DerivationTree.lean)*

**Timing**: ~45 minutes

**Depends on**: 3

**Files to modify**:
- `docs/modal-axiom-schema-architecture.md` - append Area 6 and Area 7 sections; whole-file review.

**Verification**:
- All seven areas are present and complete.
- The task-number grep returns zero matches.
- The intuitionistic/minimal file paths cited were confirmed via grep.

## Testing & Validation

- [x] `docs/modal-axiom-schema-architecture.md` exists and is non-empty. *(508 lines)*
- [x] All seven task areas are covered, each in a dedicated section, in order.
- [x] `grep -nE 'task[ -]?[0-9]|\b52[23]\b|\b536\b' docs/modal-axiom-schema-architecture.md` returns
      no matches (hard constraint: no task-number citations). *(verified: exit code 1, zero matches)*
- [x] The count is reconciled as "14 retired `<Sys>Axiom` inductives + S5's pre-existing
      `ModalAxiom`"; the phrase "15 inductives" does not appear. *(verified via grep)*
- [x] The `Cube.lean` (semantic) vs syntactic tag-set cube disambiguation is present and names both
      file paths. *(Section 2, "Disambiguation" subsection)*
- [x] Every embedded Lean signature matches the verified signatures in the research report; any
      family file path (intuitionistic/minimal) cited was confirmed on disk via grep.
- [x] Durable anchors used throughout: `SchemaUnion.lean`, `SchemaTags.lean`,
      `FrameCorrespondence.lean`, `SchemaSoundness.lean`, `DerivationTree.lean`,
      `Foundations/Logic/ProofSystem.lean`, `InterSystem/AxiomSubsumption.lean`, `Cube.lean`.

## Artifacts & Outputs

- `docs/modal-axiom-schema-architecture.md` - the durable architecture document (primary deliverable).
- `specs/536_document_modal_axiom_schema_architecture/summaries/01_modal-axiom-schema-architecture-summary.md`
  - implementation summary (written at completion).

## Rollback/Contingency

The deliverable is a single new file in a new `docs/` directory with no build or runtime coupling.
If the document must be reverted, delete `docs/modal-axiom-schema-architecture.md` (and the empty
`docs/` directory if it holds nothing else); no other file is touched, so there is no cascading
rollback. Partial progress is safe to leave in place between phases — each phase appends a
self-contained section to the same file.
