# Implementation Plan: Task #420

- **Task**: 420 - Doc: record native intuitionistic-embedding prerequisites
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: None (parent task 415; coordination note with task 418 — see Risks)
- **Research Inputs**: specs/420_native_embedding_prerequisites_doc/reports/01_native-embedding-prerequisites.md
- **Artifacts**: plans/01_native-embedding-prerequisites-doc.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

DOC-ONLY task: record the four prerequisites for a future native, intuitionistic-faithful
propositional embedding so the current classical-only embedding boundary is well-specified and
not re-litigated when CSLib eventually adds an intuitionistic modal/temporal logic. The change is
a new subsection in `ORGANISATION.md` (Option A, the canonical actively-maintained design
overview) plus an optional docstring parity edit bringing the Bimodal embedding's forward-looking
limitation note in line with the Modal and Temporal modules (Option C). No Lean semantics change,
no new `sorry`, no axioms. The build must remain green; only docstring/comment/Markdown text is
touched.

### Research Integration

The research report (`01_native-embedding-prerequisites.md`) confirmed all four prerequisites
accurate against the live codebase and supplies confirmed file anchors:
- **Prereq 1** — no native `and`/`or` constructors on Modal/Temporal/Bimodal syntax (Łukasiewicz
  encoding used); native `and`/`or` exist only on `PL.Proposition`
  (`Propositional/Defs.lean:89,91,118-123`).
- **Prereq 2** — no `IsIntuitionistic`-gated modal/temporal proof system; gating lives only at the
  PL level (`Propositional/NaturalDeduction/Basic.lean:182`, `SequentCalculus/LJ/Basic.lean:100`).
- **Prereq 3** — PL `IForces` (`Propositional/Semantics/Kripke.lean:58-130`) is the real bridge
  target (parametric `botForces`, persistence). Refinement: "birelational" describes the TARGET
  intuitionistic-modal semantics (preorder `≤` + accessibility `R`); PL `IForces` is itself
  single-relation. The note must state the `≤`-vs-`R` distinction explicitly.
- **Prereq 4** — current preservation is classical-semantic (`Tautology ↔ valid` via
  `PL.Evaluate`, `Modal/FromPropositional.lean:106,162`), not the proof-theoretic
  `IPL.Derivable φ → IModal.Derivable φ.toIModal` a faithful embedding needs.

New finding integrated: the forward-looking `## Limitations` note is asymmetric — present in
`Modal/FromPropositional.lean:36-41` and `Temporal/FromPropositional.lean:34-40` but MISSING from
`Bimodal/Embedding/PropositionalEmbedding.lean` (which carries only the classical-equivalence
rationale at `:33-41`). Phase 2 closes this parity gap.

The report's §5 scaffold is explicitly marked `[SCAFFOLD — human-author before committing]`. Per
the CSLib/Mathlib AI usage policy, prose intended for upstream surfaces (PR descriptions, Zulip)
must be human-authored. In-repo `ORGANISATION.md` / docstring text MAY be authored as part of
implementation, but the design-note prose drafted here must be flagged as a scaffold draft
requiring human review before any upstream use.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no `roadmap_path` / `roadmap_flag` in delegation context). This task
advances the PL-Docs topic and closes the Finding 1 design question spawned from task 415.

## Goals & Non-Goals

**Goals**:
- Record the four native-embedding prerequisites and the classical-scope boundary in a
  discoverable in-repo location (`ORGANISATION.md`, Option A).
- State the `≤`-vs-`R` (preorder-vs-accessibility) distinction so "birelational" is not misread as
  describing PL `IForces`.
- Bring the Bimodal embedding docstring to parity with Modal and Temporal (Option C, optional).
- Cross-reference the new ORGANISATION.md subsection from the three embedding module docstrings.
- Keep the build green; zero new `sorry`, zero axioms.

**Non-Goals**:
- Any Lean semantics change (no new constructors, proof systems, or theorems).
- Implementing the native intuitionistic embedding itself (XL, out of scope, future work).
- Creating a standalone `docs/design/` directory (Option B) — deferred unless maintainers object
  to design prose in `ORGANISATION.md`.
- Committing any prose to an upstream surface (PR/Zulip) — that prose must be human-authored
  separately under the AI policy.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Bimodal docstring edit (Phase 2) collides with task 418, which restructures `Bimodal/Embedding/PropositionalEmbedding.lean` | M | M | Phase 2 is OPTIONAL and isolated to a docstring block. Coordinate ordering with task 418: if 418 is in flight, defer the Bimodal parity edit and apply it after 418 lands (or hand the one-sentence note to 418 to incorporate). Modal/Temporal cross-refs and the ORGANISATION.md subsection (Phases 1, 3) are unaffected. |
| AI-authored prose leaks to upstream without human review | M | L | Mark the design-note prose as a SCAFFOLD draft in the plan; in-repo ORGANISATION.md/docstring text is allowed but any PR/Zulip copy must be human-authored separately. |
| Design prose is "off-genre" for ORGANISATION.md (otherwise a pure directory map) | L | M | Keep the subsection tight: four-item list + one-line pointer to the three module docstrings, per report §3 caveat. |
| Docstring edit breaks parsing / lint-style | L | L | Phase 3 runs `lake build` + `lake exe lint-style` on edited files to confirm docstrings parse and lint clean. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel. Phase 1 (ORGANISATION.md) and Phase 2
(docstrings) touch disjoint files and are independent; Phase 3 verification depends on both.

### Phase 1: Add ORGANISATION.md prerequisites subsection [COMPLETED]

**Goal**: Add a short, discoverable subsection to `ORGANISATION.md` recording the four
prerequisites and the classical-scope boundary, co-located with the per-logic Logics entries.

**Tasks**:
- [ ] Author a new subsection (suggested heading `### Propositional Embeddings and the Classical-Scope Boundary`) placed under the Logics section (`ORGANISATION.md` `:76-211`), near the per-logic embedding entries (Modal `:108`, Temporal `:124`, Bimodal `:155`).
- [ ] State that `toModal`/`toTemporal`/`toBimodal` map `{atom, bot, imp}` structurally and encode `{and, or}` via Łukasiewicz definitions — classically but not intuitionistically valid — certifying the classical (CPL) fragment only.
- [ ] List the four prerequisites for a future native intuitionistic-faithful embedding: (1) native `and`/`or` constructors; (2) gated `[IsIntuitionistic]` modal/temporal proof system; (3) birelational target semantics (preorder `≤` + accessibility `R`) bridging to PL single-relation `IForces` at `Propositional/Semantics/Kripke.lean`; (4) proof-theoretic preservation/faithfulness (`IPL.Derivable φ → IModal.Derivable φ.toIModal` and converse), not classical `Tautology ↔ valid`.
- [ ] Explicitly state the `≤`-vs-`R` distinction so "birelational" is not read as "PL is birelational".
- [ ] Add a one-line pointer to the `## Limitations` notes in the three embedding modules.
- [ ] Keep the subsection tight (list + pointer; avoid multi-paragraph rationale that is off-genre for the directory map).

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `ORGANISATION.md` - add one subsection under the Logics section (~`:76-211`)

**Verification**:
- The subsection exists, names all four prerequisites, includes the `≤`-vs-`R` distinction, and points to the three module docstrings.
- Markdown renders cleanly (no broken headings/lists).

---

### Phase 2: Optional Bimodal docstring parity edit + cross-references [NOT STARTED] *(deviation: skipped -- task 418 owns Bimodal/Embedding/PropositionalEmbedding.lean concurrently; Bimodal parity edit deferred to task 418's restructure per orchestrator scope note; Modal/Temporal cross-ref additions also deferred this cycle to avoid partial parity)*

**Goal**: Bring `Bimodal/Embedding/PropositionalEmbedding.lean` to parity with the Modal and
Temporal embeddings by adding the forward-looking limitation note, and cross-reference the new
ORGANISATION.md subsection from all three modules.

**Tasks**:
- [ ] COORDINATION CHECK: confirm task 418 status before editing `Bimodal/Embedding/PropositionalEmbedding.lean`. If 418 is actively restructuring this file, defer the Bimodal parity edit (hand the sentence to 418 or apply after 418 lands). Modal/Temporal cross-refs proceed regardless.
- [ ] Add a forward-looking `## Limitations` sentence to the Bimodal embedding docstring (`Bimodal/Embedding/PropositionalEmbedding.lean:33-41`) mirroring the note in `Modal/FromPropositional.lean:36-41` and `Temporal/FromPropositional.lean:34-40` ("if CSLib adds an intuitionistic modal/temporal logic, a separate native embedding will be required").
- [ ] Add a one-line cross-reference to the new ORGANISATION.md subsection in each of the three embedding docstrings (`Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`, `Bimodal/Embedding/PropositionalEmbedding.lean`).
- [ ] Do NOT change any Lean code, definitions, or proofs — docstring/comment text only.

**Timing**: 0.5 hours

**Depends on**: none (independent of Phase 1; disjoint files)

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` - add ORGANISATION.md cross-reference to existing `## Limitations` note
- `Cslib/Logics/Temporal/FromPropositional.lean` - add ORGANISATION.md cross-reference to existing `## Limitations` note
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` - add forward-looking `## Limitations` note + cross-reference (DEFER if task 418 in flight)

**Verification**:
- All three module docstrings carry a forward-looking limitation note and a pointer to the ORGANISATION.md subsection.
- No Lean code outside docstrings/comments changed (confirm via `git diff` showing only comment-block lines).

---

### Phase 3: Verify build still green (no Lean semantics change) [COMPLETED]

**Goal**: Confirm the docstring/comment edits parse and lint clean and that no semantics changed.

**Tasks**:
- [ ] Run `lake exe lint-style` on the edited `.lean` files to confirm style/text lint passes.
- [ ] Run `lake build` to confirm the edited docstrings parse and the tree compiles (doc-only edits should not change build outcome).
- [ ] Confirm `git diff` shows only Markdown (ORGANISATION.md) and Lean docstring/comment lines — no code, no new `sorry`, no axioms.

**Timing**: 0.25 hours

**Depends on**: 1, 2

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` succeeds (green tree).
- `lake exe lint-style` passes on edited files.
- `git diff` confirms zero non-comment Lean changes and zero new `sorry`.

## Testing & Validation

- [ ] `lake build` succeeds (no parse regressions from docstring edits).
- [ ] `lake exe lint-style` passes on `Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`, and (if edited) `Bimodal/Embedding/PropositionalEmbedding.lean`.
- [ ] ORGANISATION.md subsection lists all four prerequisites and the `≤`-vs-`R` distinction.
- [ ] `git diff` shows only Markdown + Lean comment/docstring lines; 0 new `sorry`, 0 axioms.

## Artifacts & Outputs

- Updated `ORGANISATION.md` with the new prerequisites subsection.
- Updated embedding-module docstrings with cross-references (and Bimodal parity note, unless deferred for task 418 coordination).
- This plan file.
- SCAFFOLD draft prose (report §5) flagged as requiring human authorship before any upstream (PR/Zulip) use.

## Rollback/Contingency

All edits are doc-only and isolated. To revert, `git checkout` the affected files
(`ORGANISATION.md` and the three embedding `.lean` files). Since no Lean semantics change, no
build state is at risk. If the Phase 2 Bimodal edit conflicts with task 418, drop Phase 2's
Bimodal sub-edit and reapply after 418 lands — Phases 1 and 3 remain valid independently.
