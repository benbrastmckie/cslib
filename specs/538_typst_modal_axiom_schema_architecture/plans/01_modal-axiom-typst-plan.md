# Implementation Plan: Typst Rendering of the Modal Axiom-Schema Architecture

- **Task**: 538 - Turn docs/modal-axiom-schema-architecture.md into a clear and concise Typst document that presents the architecture lucidly and directly
- **Status**: [NOT STARTED]
- **Effort**: 4.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/538_typst_modal_axiom_schema_architecture/reports/01_modal-axiom-typst-research.md
- **Artifacts**: plans/01_modal-axiom-typst-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; no-task-references-in-deliverables.md
- **Type**: typst

## Overview

Produce a single, self-contained Typst document that renders the CSLib architecture note at
`docs/modal-axiom-schema-architecture.md` (the `SchemaUnion` / `ModalSchemaTag` refactor) as a
clear, concise, typeset deliverable. The document reuses the house style established by the only
existing Typst precedent in the repo (`typst/MPL/`): the `@preview/thmbox:0.3.0` theorem
environments, the austere AMS/journal aesthetic (black-only body, no fill boxes), New Computer
Modern fonts, and the `nec`/`poss` (`square.stroked`/`diamond.stroked`) notation macros. Work is
authored section-by-section following the outline in the research report (Section 4), collapsing
the source's highest-redundancy passages into tables and one `fletcher` cube diagram, then
compiled and verified with `typst compile` (exit 0) and reviewed for fidelity and concision.
Definition of done: `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ` compiles
cleanly to `typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf`, faithfully
covers all seven source sections plus a source-anchor appendix, and contains no ephemeral
task-number references.

### Research Integration

The plan integrates `reports/01_modal-axiom-typst-research.md`:
- **Output path and granularity**: single self-contained file at
  `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ`, build output to
  `build/modal-axiom-schema-architecture.pdf` (report Section 5) — no multi-file MPL-style
  scaffold, matching the "concise" mandate.
- **House style**: thmbox environments, New Computer Modern, `nec`/`poss` macros, `stroke: none`
  tables with `table.hline()` rules, `#quote(block: true)` for the docstring excerpt, `remark(...)`
  for callouts (report Section 2, Section 3).
- **Verbosity trims**: collapse Section 3's five near-duplicate `Satisfies.modal*_axiom` Lean
  signatures into one 5-row correspondence table; render the 18-tag alphabet and the 15 tag-set
  `def`s as tables; replace the 24-edge prose list with a `fletcher` cube diagram (report
  Sections 1.3, 3.3, 3.4, 3.7).
- **Fidelity boundary**: keep ~6-7 singular, load-bearing Lean signatures as literal fenced
  `lean` code blocks (report Sections 1.5, 3.5); transcribe axiom-schema shapes from the literal
  Lean `Satisfies.*_axiom` conclusions, not textbook memory (report Section 1.4).
- **Verified environment**: `typst` 0.14.2 on PATH; `thmbox` 0.3.0 and `fletcher` cached offline;
  a smoke test of a Lean-fenced block + `square.stroked`/`diamond.stroked` math + a table
  compiled with exit 0 (report Section 6).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and `roadmap_flag` is not set; this
plan makes no ROADMAP.md changes.

## Goals & Non-Goals

**Goals**:
- Render all seven sections of `docs/modal-axiom-schema-architecture.md`, plus front matter and a
  consolidated source-anchor appendix, as one self-contained `.typ` document.
- Match the `typst/MPL/` house style (thmbox environments, austere aesthetic, notation macros,
  table conventions).
- Improve lucidity over the source by collapsing its highest-redundancy passages into tables and
  one `fletcher` cube diagram, while preserving fidelity of load-bearing Lean signatures.
- Compile cleanly (`typst compile`, exit 0) to a committed PDF under `build/`.
- Resolve the one open item flagged by research: verify the exact expansion of `Axioms.AxiomB`
  against live Lean source before printing it.

**Non-Goals**:
- No modification, move, or deletion of the source `docs/modal-axiom-schema-architecture.md` (the
  Typst document is a derived, differently-purposed artifact, not a replacement).
- No new colored callout/admonition box or any deviation from the "no background colors" house
  style.
- No multi-file `template.typ`/`notation/`/`chapters/` scaffold — a single file is the right
  granularity for a ~500-line source.
- No custom Lean syntax-highlighting grammar (unhighlighted monospace rendering is acceptable and
  expected).
- No changes to any `.lean` source (the `AxiomB` step is a read-only confirmatory grep).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `Axioms.AxiomB` expansion differs from the textbook `φ → □◇φ` | M | M | Phase 1 greps live Lean source (`Cslib/Logics/Modal/`) and records the exact definition before it is printed; if it cannot be confirmed, cite `AxiomB(φ)` opaquely with a note rather than assert an unverified shape |
| `fletcher` cube layout (15 nodes / 24 edges) proves fiddly and eats time | M | M | Treat the diagram as a stretch enhancement (research Section 3.4); fall back to the grouped Source-system-to-edges table if pixel-perfect layout is not reached — do not block the phase on it |
| Transcribing axiom schemas from memory instead of the literal Lean conclusions introduces errors | M | L | Transcribe each schema symbol-for-symbol from the `Satisfies.*_axiom` statement quoted in the source; cross-check against the source doc during the verification phase |
| Long tables (appendix anchor table) overflow a page | L | M | Apply the MPL breakability shows (`#show figure: set block(breakable: true)`) in the preamble; wrap the dense appendix table in `#text(size: 9.5pt)[...]` per MPL precedent |
| An ephemeral task-number reference leaks into the deliverable | L | L | The `.typ` deliverable lives outside `specs/**`; Phase 5 explicitly greps the file for task-number citation patterns per the no-task-references rule |
| Compilation fails late after all content is authored | M | L | Each authoring phase ends with an incremental `typst compile` so errors surface early, not only in Phase 5 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential: all phases
edit the same single `.typ` file, so each authoring phase builds on the previous one's output and
none may run concurrently.

### Phase 1: Scaffold, Preamble, Front Matter, and Resolve the AxiomB Open Item [NOT STARTED]

**Goal**: Stand up the project directory and a compiling skeleton document (preamble, notation
macros, title/front matter), and resolve the exact `Axioms.AxiomB` expansion against live Lean
source so the Section 3 correspondence table (Phase 3) can print it faithfully.

**Tasks**:
- [ ] Read `docs/modal-axiom-schema-architecture.md` in full to work from exact source content.
- [ ] Create `typst/ModalAxiomArchitecture/` and `typst/ModalAxiomArchitecture/build/`.
- [ ] Author the preamble in `modal-axiom-schema-architecture.typ`: `#import "@preview/thmbox:0.3.0"`,
      `thmbox-init`, `#set text(font: "New Computer Modern", size: 11pt)`,
      `#set heading(numbering: "1.1")`, `#set par(justify: true, ...)`,
      `#set page(margin: 1.75in, numbering: "1")`, the theorem-environment shows, and the two
      breakability shows (`#show figure: set block(breakable: true)`).
- [ ] Define the local notation macros: `nec = $square.stroked$`, `poss = $diamond.stroked$`,
      `imp = $arrow.r$`, `falsum = $bot$` (matching `typst/MPL/notation/shared-notation.typ`
      verbatim), plus any local helpers needed.
- [ ] Author the unnumbered title block: title, subtitle, "CSLib — Internal Document" byline,
      date; decide (lightweight) whether to include a `#outline()` — recommended omitted at this
      length, but record the decision.
- [ ] Run `grep -rn "AxiomB" Cslib/Logics/Modal/` (and widen to `Cslib/**/*.lean` if needed) to
      confirm the exact definition of `Axioms.AxiomB`; record the confirmed expansion (e.g.
      `φ → □◇φ`) or, if unresolved, the decision to cite it opaquely as `AxiomB(φ)`.
- [ ] `typst compile` the skeleton to `build/modal-axiom-schema-architecture.pdf`; confirm exit 0.

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ` - new file: preamble,
  notation, title/front matter.
- `typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf` - new compiled output.

**Verification**:
- Directory and file exist; `typst compile` exits 0 producing a non-empty PDF.
- The exact `Axioms.AxiomB` expansion (or the explicit opaque-citation decision) is recorded for
  use in Phase 3.

### Phase 2: Sections 1-2 — Schema-Tag Alphabet and the Syntactic Modal Cube [NOT STARTED]

**Goal**: Author Section 1 (The Schema-Tag Alphabet) and Section 2 (Subsumption as
`Finset.subset` — the syntactic modal cube), applying the research's table/diagram collapses.

**Tasks**:
- [ ] Section 1: render `ModalSchemaTag`'s 18 tags as a table (tag x schema, grouped by role)
      instead of the source's partial `.Holds` code excerpt; keep the `SchemaUnion` definition and
      the three `@[simp]` elimination lemmas as short literal `lean` code blocks; include the
      literal `abbrev ModalAxiom := SchemaUnion s5Tags` line and the "14 renamed abbrevs + S5"
      fact.
- [ ] Section 2: keep `SchemaUnion.subsumption` as a short `lean` code block; render the 15
      tag-set `def`s as a table (System | `kCore ∪ {differentiators}`).
- [ ] Section 2: author the `fletcher` cube diagram (15 nodes, 24 edges) per research Section 3.4
      to replace the 24-edge prose list; iterate on `(row, col)` placement for legibility. If
      layout proves too fiddly, fall back to the grouped Source-system-to-edges table (do not
      block on pixel-perfect layout).
- [ ] Section 2: keep the disambiguation table vs. `Cube.lean` (already table-shaped in the source).
- [ ] Transcribe all axiom-schema shapes from the literal Lean `Satisfies.*_axiom` conclusions /
      source text, not from memory.
- [ ] `typst compile`; confirm exit 0.

**Timing**: 1.25 hours

**Depends on**: 1

**Files to modify**:
- `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ` - append Sections 1-2.
- `typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf` - recompiled.

**Verification**:
- Sections 1-2 present with the tag table, tag-set table, `SchemaUnion`/`subsumption`/`@[simp]`
  code blocks, cube diagram (or documented fallback table), and disambiguation table.
- `typst compile` exits 0.

### Phase 3: Sections 3-4 — The unionSound Hinge and the HasAxiom* Insulation Layer [NOT STARTED]

**Goal**: Author Section 3 (`unionSound`: the syntax/semantics hinge) and Section 4 (the
`HasAxiom*` insulation layer), collapsing the five near-duplicate correspondence lemmas into one
table and the dense `extends`-chain paragraph into a legible tree/list.

**Tasks**:
- [ ] Section 3: build the frame-correspondence table (5 rows: Tag | Axiom schema | Frame
      condition | Lemma name) replacing the five near-identical `Satisfies.modal*_axiom` blocks;
      use the confirmed `Axioms.AxiomB` expansion from Phase 1 (or its opaque citation) for the B
      row.
- [ ] Section 3: keep `FrameValidatesTag` (the 18-arm match) and `unionSound`'s signature as
      literal `lean` code blocks.
- [ ] Section 4: keep a representative `HasAxiomT` signature and the `HasAxiomT Modal.HilbertS5`
      instance witness as `lean` code blocks; render the `extends` typeclass hierarchy as a small
      `fletcher` tree or nested list; add the explicit callout that this hierarchy has the same
      shape as the Section 2 cube.
- [ ] `typst compile`; confirm exit 0.

**Timing**: 1.0 hour

**Depends on**: 2

**Files to modify**:
- `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ` - append Sections 3-4.
- `typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf` - recompiled.

**Verification**:
- Section 3 correspondence table has five rows with faithful schema/frame-condition/lemma cells
  and the B row reflects the Phase 1 finding; `FrameValidatesTag` and `unionSound` blocks present.
- Section 4 hierarchy rendered with the same-shape-as-cube callout.
- `typst compile` exits 0.

### Phase 4: Sections 5-7 and the Source-Anchor Appendix [NOT STARTED]

**Goal**: Author the remaining sections (S5 = T+4+B; Design Rationale A vs. B; Scope Boundary) and
the consolidated source-anchor appendix table.

**Tasks**:
- [ ] Section 5: render `s5Tags` vs. `kb5Tags` side by side (math or a 2-row table) and the short
      prose explaining why the `KB5 -> S5` edge is mechanically absent (the `decide`-false
      consequence).
- [ ] Section 6: render the Representation A vs. B trade-off as the two-column comparison table
      (research Section 3.7) replacing the source's prose bullets.
- [ ] Section 7: render the module-docstring excerpt via `#quote(block: true)` (optionally inside a
      `remark(...)`); list the out-of-scope intuitionistic/minimal families with their anchors.
- [ ] Appendix: build one consolidated source-anchor table (File:lines | Declaration — section
      supported), mirroring `typst/MPL/chapters/06-appendix.typ`; wrap in `#text(size: 9.5pt)[...]`
      if needed to fit page width.
- [ ] `typst compile`; confirm exit 0.

**Timing**: 1.0 hour

**Depends on**: 3

**Files to modify**:
- `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ` - append Sections 5-7 and
  the appendix.
- `typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf` - recompiled.

**Verification**:
- Sections 5, 6, 7 and the appendix anchor table all present and rendering.
- `typst compile` exits 0.

### Phase 5: Compile, Verify, and Concision/Fidelity Review [NOT STARTED]

**Goal**: Confirm the finished document compiles cleanly and that its rendered content is faithful
to the source and genuinely concise, and that no ephemeral task-number references leak into the
deliverable.

**Tasks**:
- [ ] Run a clean `typst compile
      typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ
      typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf`; confirm exit code 0
      with no warnings that indicate missing content.
- [ ] Read the compiled PDF (or its structure) and cross-check every one of the seven source
      sections is represented; confirm each collapsed table/diagram is faithful to the source it
      replaced (especially the five-row correspondence table and the transcribed axiom schemas).
- [ ] Confirm the `Axioms.AxiomB` cell matches the Phase 1 finding (verified expansion or opaque
      citation), not an unverified textbook shape.
- [ ] Confirm concision: no partial "… 15 further clauses" ellipsis excerpts remain where a table
      is more complete; prose reads clean with anchors deferred to the appendix.
- [ ] `grep -nE "task [0-9]+|tasks [0-9]+|\(task [0-9]+\)"
      typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ` returns no matches
      (no-task-references-in-deliverables rule; the `.typ` file is outside `specs/**`).
- [ ] Confirm the source `docs/modal-axiom-schema-architecture.md` is unchanged (derived artifact,
      not a replacement).

**Timing**: 0.75 hours

**Depends on**: 4

**Files to modify**:
- `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ` - final corrections from
  review, if any.
- `typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf` - final recompiled output.

**Verification**:
- `typst compile` exits 0; PDF is non-empty and current.
- All seven sections + appendix present and faithful; concision checks pass.
- Task-number grep returns no matches; source `.md` unchanged.

## Testing & Validation

- [ ] `typst compile typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf` exits 0.
- [ ] The compiled PDF exists, is non-empty, and reflects the latest source.
- [ ] All seven source sections plus front matter and the source-anchor appendix are represented.
- [ ] The five-row frame-correspondence table and the 18-tag alphabet table are faithful to the
      literal source content (schemas transcribed from Lean conclusions, not memory).
- [ ] The `Axioms.AxiomB` rendering matches the live-Lean-source finding from Phase 1.
- [ ] No ephemeral task-number references appear anywhere in the `.typ` deliverable.
- [ ] `docs/modal-axiom-schema-architecture.md` is unchanged.

## Artifacts & Outputs

- `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ` - the Typst source document.
- `typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf` - the compiled PDF
  (committed alongside the source, matching the `typst/MPL/build/` precedent).
- `specs/538_typst_modal_axiom_schema_architecture/summaries/01_modal-axiom-typst-summary.md` -
  implementation summary (produced at /implement time).

## Rollback/Contingency

- The deliverable is a new, isolated directory (`typst/ModalAxiomArchitecture/`) that touches no
  existing files; reverting is a clean removal of that directory with no blast radius on the rest
  of the repo.
- If the `fletcher` cube diagram cannot be made legible in the available time, fall back to the
  grouped Source-system-to-edges table (already prose-present in the source) — this is a planned
  degradation, not a failure.
- If `Axioms.AxiomB` cannot be confirmed against live Lean source, cite it opaquely as `AxiomB(φ)`
  with a footnote rather than assert an unverified expansion; the document still compiles and
  remains faithful.
- If compilation regresses at any phase, the prior phase's committed `.typ` + PDF is the restore
  point; fix forward against the compiler error rather than discarding uncommitted work.
