# Research Report: Modal Axiom-Schema Architecture -> Typst Document

- **Task**: 538
- **Type**: typst
- **Date**: 2026-07-19

## Objective

Gather everything needed to plan and author a clear, concise Typst rendering of
`docs/modal-axiom-schema-architecture.md` — the CSLib architecture document describing the
`SchemaUnion` / `ModalSchemaTag` refactor that unified 15 classical normal modal systems' axiom
predicates.

## 1. Source Document Analysis

`docs/modal-axiom-schema-architecture.md` (508 lines) has a clean 7-section structure already,
each anchored to real Lean module paths. Read in full. Summary of content and structure:

### 1.1 Core architectural narrative

Two libraries, two halves of one abstraction:
- **Syntactic side** — `SchemaUnion.lean` + `SchemaTags.lean`: an 18-constructor tag alphabet
  (`ModalSchemaTag`), an existential `.Holds` meaning function ("schema = set of instances"), the
  `SchemaUnion (S : Finset ModalSchemaTag)` combinator, and three `@[simp]` elimination lemmas.
- **Semantic side** — `FrameCorrespondence.lean` + `SchemaSoundness.lean`: five
  frame-condition-to-validity lemmas for the five modal-strength differentiators (T, D, B, 4, 5),
  `FrameValidatesTag`, and the master soundness lemma `unionSound`.

Two payoffs: subsumption collapses from 24 hand-written lemmas to one generic
`SchemaUnion.subsumption` (decidable `Finset.subset`); soundness collapses from 15 per-system
case-splits to one `unionSound` application.

### 1.2 Section-by-section map

1. **The Schema-Tag Alphabet** — `ModalSchemaTag` (18 ctors, grouped 4+1+5+6+2), `.Holds`
   (partial 3-clause excerpt of 18), `SchemaUnion` def, 3 `@[simp]` lemmas, the "14 renamed
   abbrevs + S5's `ModalAxiom`" fact with the literal `abbrev ModalAxiom := SchemaUnion s5Tags`
   line.
2. **Subsumption as `Finset.subset`** — `SchemaUnion.subsumption` (3-line proof sketch), the
   15 tag-set `def`s (`kCore` + 14 `insert`-built sets), the 24 edges enumerated as a **prose
   bulleted list grouped by source system** (K: 5 edges, D: 3, T: 2, B: 3, K4: 3, K5: 3, K45: 1,
   D4: 1, D5: 1, into S5: 2 = 24 total), and a disambiguation subsection distinguishing this
   syntactic tag cube from the pre-existing semantic frame-class cube in `Cube.lean` (already
   rendered as a 2-row comparison table in the source).
3. **`unionSound`: The Syntax/Semantics Hinge** — **the highest-redundancy section**: five
   near-identical Lean lemma signatures (`Satisfies.modalT_axiom` … `modalFive_axiom`), each
   differing only in the frame-condition hypothesis and the axiom-schema conclusion, printed as
   five separate multi-line Lean blocks (lines 254-274 of the source). Then `FrameValidatesTag`
   (an 18-arm match, mostly `True`), then `unionSound`'s signature.
4. **The `HasAxiom*` Insulation Layer** — the `HasAxiom*` typeclass family, a dense run-on
   prose paragraph describing the `extends` chain `MinimalHilbert -> IntuitionisticHilbert ->
   ClassicalHilbert -> ModalHilbert -> {ModalTHilbert, ModalDHilbert, ModalBHilbert,
   ModalK4Hilbert, ModalK5Hilbert} -> {composites} -> ModalS5Hilbert`, and one worked instance
   example (`HasAxiomT Modal.HilbertS5`).
5. **S5 = T+4+B** — short section: `s5Tags` vs `kb5Tags` set-difference argument for why the
   `KB5 -> S5` edge is mechanically absent.
6. **Design Rationale** — Representation A (chosen) vs. B (rejected, hypothetical macro
   approach), argued in prose bullets ("wins on three fronts" / "costs" for each).
7. **Scope Boundary** — future-instance-not-a-fork framing; a blockquoted module-docstring
   excerpt; enumerates the existing intuitionistic/minimal families kept out of scope.

### 1.3 Redundancy/verbosity to trim in the Typst rendering

- **Section 3's five lemma signatures** are the single biggest win: they share an identical
  shape (`Model`, frame-condition hypothesis, `w`, `φ`, `Satisfies m w <schema>`) and differ only
  in three cells' worth of information. Collapse to **one table**: Tag | Axiom schema (math) |
  Frame condition (math) | Lemma name — five rows instead of five ~5-line code blocks (~40 lines
  of near-duplicate signatures become one 7-line table).
- **Section 1's `.Holds` "representative excerpt (18 clauses total)"** is explicitly partial in
  the source ("… 15 further clauses"). A Typst table of all 18 tags with their schema in proper
  math notation is both *more complete* and *more concise* than a partial code excerpt with an
  ellipsis comment.
- **Section 2's 15 tag-set `def`s** (a 15-line Lean block with trailing `--` comments used to
  label the tag-count breakdown) reads better as a table: System | Tags = `kCore ∪ {…}`.
- **Section 2's 24-edge bulleted list** ("From K: K→T, K→D, …") is the modal cube's Hasse
  diagram in prose form. A `fletcher` diagram (15 nodes, 24 directed edges) is a genuinely more
  lucid rendering than ten grouped bullet sub-lists — this is the single best diagram
  opportunity in the whole document, and it directly visualizes the thing the document keeps
  calling "the cube."
- **Section 4's `extends`-chain paragraph** is a dense run-on sentence describing a tree. Either
  a second small `fletcher` tree diagram or a simple indented list renders it more legibly; note
  in the prose that this hierarchy has the *same shape* as the Section 2 cube (worth calling out
  explicitly — it is a genuine architectural insight the source states but does not visually
  reinforce).
- **Section 6's "wins on three fronts" / "costs" prose bullets** for A vs. B compress well into
  a two-column (or four-row) comparison table.
- The **Overview**'s dense opening paragraph (lines 5-14) crams the full system list, the
  "14 renamed + S5's pre-existing" fact, and the combinator/tag-alphabet names into one paragraph.
  Split into a short lead sentence + the existing two-bullet "two libraries" list (already
  well-structured in the source) + a compact "payoffs" callout for the 24→1 / 15→1 collapse
  numbers.
- Every section's "**Durable anchor(s)**" line is repo-appropriate provenance, not
  reader-facing narrative. Recommend rendering these as a small monospace footer/caption per
  section (or footnote), and additionally collecting all of them into one appendix table at the
  end (mirroring the pattern already used in `typst/MPL/chapters/06-appendix.typ`, see below) so
  the body prose reads clean while anchors remain fully auditable.

### 1.4 Math/logic notation inventory

Symbols and schemas that need Typst math rendering:
- `□φ` (box/necessity), `◇φ` (diamond/possibility) — modal operators.
- Axiom schemas: **T**: `□φ → φ`; **D**: `□φ → ◇φ` (source states `AxiomD` via
  `□φ → ¬□¬φ`-style formulation, i.e. `□φ → (□(φ→⊥) → ⊥)` — keep the exact clause shape shown in
  `Satisfies.modalD_axiom`'s statement, which is
  `Proposition.imp (Proposition.box φ) (Proposition.imp (Proposition.box (Proposition.imp φ
  Proposition.bot)) Proposition.bot)`, i.e. `□φ → (□(φ→⊥) → ⊥)`); **B**: `Axioms.AxiomB φ`
  (source doesn't spell it out — worth resolving to `φ → □◇φ`, the standard B schema, when
  writing the table, or citing `Axioms.AxiomB` as an opaque reference if the implementer prefers
  not to inline an unverified expansion); **4**: `□φ → □□φ`; **5**: (as literally written in the
  source) `((□(φ→⊥))→⊥) → □((□(φ→⊥))→⊥)`, i.e. `◇φ → □◇φ` once `◇` is read as `¬□¬`.
- Frame conditions: reflexive (`∀w, wRw`), serial (`Relation.Serial m.r`), symmetric
  (`∀w₁w₂, wRw' → w'Rw`), transitive, euclidean (`∀w₁w₂w₃, wRw₂ ∧ wRw₃ → w₂Rw₃`).
- Set/lattice notation: `⊆` (Finset.subset), `∪` (Finset.union), `∈`, `∃`.
- The modal cube inclusion chain: `K ⊂ T ⊂ S4 ⊂ S5` and 11 further systems/edges.
- Existential "Holds" encoding: `SchemaUnion S χ := ∃ t ∈ S, t.Holds χ`.

**Caution for the implementer**: several of the exact schema shapes above (especially B and D)
are only implicit in the source (it shows the Lean `Satisfies.*_axiom` *statement* shape, not a
plain-English "the B schema is…" gloss for all five). When rendering the axiom-schema table, the
faithful move is to transcribe the *literal* Lean formula shown in each `Satisfies.*_axiom`
conclusion (already quoted in Section 1.3 above), translated symbol-for-symbol into `□`/`◇`/`→`
math notation — not to substitute a textbook schema from memory. `Axioms.AxiomB` is referenced by
name only in the source and not unfolded; if its definition isn't independently verified, the
report recommends either citing it as `AxiomsAxiomB(φ)` (opaque) with a note, or having the
implementation agent do a quick `grep -n "AxiomB" Cslib/**/*.lean` against the live codebase
before asserting `φ → □◇φ` in the table (this repo's Lean source is available at
`Cslib/Logics/Modal/` for a fast confirmatory grep — no new research dispatch needed, a single
Grep call suffices).

### 1.5 Diagrams/tables/code already in the source

- 1 disambiguation table (2 rows, already table-shaped in Markdown) — Section 2.
- 0 existing diagrams (everything is prose or Lean code blocks) — this is a document that would
  clearly benefit from 1-2 added diagrams (the cube, and optionally the `HasAxiom*` tree) that
  the *source* doesn't have but a "lucid" Typst rendering should add.
- ~12 Lean code blocks of varying size (inductive/def/theorem/lemma declarations), several of
  which (Section 3's five lemmas, Section 2's 15 tag-set defs) are prime candidates for
  table-collapse per Section 1.3 above; the remainder (the `ModalSchemaTag` inductive,
  `SchemaUnion` def, the three `@[simp]` lemmas, `unionSound`'s signature, `FrameValidatesTag`,
  the `HasAxiomT` instance witness) are singular, load-bearing signatures worth keeping as
  literal Lean code blocks for fidelity — this document's whole point is precise verified
  signatures, so wholesale translation of *every* signature into prose/math would lose fidelity.
  Recommendation: keep ~6-7 singular definitions/lemmas as real Lean raw code blocks; convert the
  ~2 repetitive/enumerable groups (Section 3's five lemmas, Section 2's 15 tag-set defs and its
  24-edge list) into tables/diagram.

## 2. Codebase Typst Conventions (Precedent: `typst/MPL/`)

CSLib already has one established Typst project, `typst/MPL/` (task 464's "MPL: Arguments for a
Structure-First Design" internal report), which is the load-bearing house-style precedent. Files:

```
typst/MPL/
├── MplReport.typ              # main file: config, title page, abstract, #include chapters
├── template.typ               # thmbox init + theorem-environment styling
├── notation/
│   ├── shared-notation.typ    # cross-theory macros (nec/poss, proves, model, leansrc/leanref…)
│   └── mpl-notation.typ       # theory-specific macros, imports shared-notation.typ
├── chapters/00-...06-....typ  # one file per chapter, #import "../template.typ": *
└── build/MplReport.pdf        # compiled output, committed alongside sources
```

**Key style facts verified by reading these files directly** (not inferred):

- **Package**: `#import "@preview/thmbox:0.3.0" as thmbox`. Confirmed cached locally at
  `~/.cache/typst/packages/preview/thmbox/0.3.0/` — no network fetch needed to compile.
- **Aesthetic** (stated verbatim in `template.typ`'s header comment): *"AMS/journal aesthetic:
  austere, black-only body text, no background colors on theorem environments. Link colors
  (URLblue) are preserved for digital usability."* All theorem/definition/axiom/remark
  environments use `fill: none, stroke: none`; only `theorem`/`lemma`/`axiom` get `bodyfmt: it =>
  emph(it)` (italic body, AMS "plain" style), `definition`/`remark` stay upright.
- **Environments available**: `definition`, `theorem`, `lemma`, `axiom`, `remark`, `proof` (all
  `thmbox.*` presets, re-exported with the styling above). No custom colored callout/admonition
  box exists anywhere in the codebase — introducing one would be a deviation from house style;
  if a "key insight" callout is wanted for this document, prefer `remark(...)` (already used for
  meta-notes like "On the status of this chapter" in `04-debate.typ`) over a new colored `#block`.
- **Document setup** (`MplReport.typ`): `#set text(font: "New Computer Modern", size: 11pt)`
  (confirmed installed: `typst fonts` lists both "New Computer Modern" and "New Computer Modern
  Math"), `#set heading(numbering: "1.1")`, `#set par(justify: true, leading: 0.55em, spacing:
  0.55em, first-line-indent: 1.8em)`, `#set page(numbering: "1", number-align: center, margin:
  1.75in)`, `#show heading: set block(above: 1.4em, below: 1em)`, `#show: thmbox-show`, `#show
  link: set text(fill: URLblue)`, and two breakability shows: `#show figure.where(kind:
  "thmbox"): set block(breakable: true)` and `#show figure: set block(breakable: true)` (needed
  so long tables — this document's appendix anchor table in particular — don't overflow a page).
- **Title page + abstract**: a two-page unnumbered front matter (`#page(numbering: none)[...]`)
  with a centered title block (`HRule`, bold 24pt title, italic 16pt subtitle, italic 12pt
  "CSLib — Internal Report" byline, date via `datetime.today().display(...)`), followed by an
  abstract page with a styled "Contents" header and `#outline(title: none, indent: auto)`.
- **Notation macros** (from `shared-notation.typ`, directly reusable for this task): `nec =
  $square.stroked$`, `poss = $diamond.stroked$`, `imp = $arrow.r$`, `lneg = $not$`, `falsum =
  $bot$`, `proves = $tack.r$`, `model = $cal(M)$`, `tuple(..args)`, and — directly relevant here
  — `leansrc(module, name) = raw(module + "." + name)` / `leanref(name) = raw(name)` for inline
  monospaced Lean identifiers in prose (used throughout `01-syntax.typ` etc., e.g. `` `Defs.lean`
  ``-style backticked names render via plain `` ` `` markdown-style raw in body text, or via
  these helpers when composed from parts).
- **Math notation pattern**: formulas are written as Typst math using these macros, e.g. `$
  not phi.alt := phi.alt arrow.r bot $`, not as pasted Lean expressions. Greek metavariables:
  `phi.alt` (φ), `psi` (ψ), `chi` (χ) map to the source doc's φ/ψ/χ.
- **Tables**: consistently `stroke: none` with two `table.hline()` rules (top+header-separator,
  bottom) via `table.header(...)`, `align: left`, explicit `columns:` (either fixed counts or
  `(auto, auto, 1fr)`-style flexible last column), wrapped in `#figure(table(...), caption:
  [...])`. The appendix anchor table additionally wraps in `#text(size: 9.5pt)[...]` to fit a
  dense reference table on one page width.
- **Lean code / raw blocks**: **not used anywhere in `typst/MPL/`** — that report translates Lean
  definitions into math + prose + `raw()`-wrapped inline identifiers rather than pasting literal
  Lean code blocks. This document (`modal-axiom-schema-architecture.md`) is different in kind: it
  *is* source-code documentation whose whole point is exact verified Lean signatures, so — per
  Section 1.5 above — the Typst rendering should reintroduce literal fenced Lean code blocks
  (```` ```lean ... ``` ````) for the load-bearing singular signatures, which the MPL precedent
  simply never needed. **Verified this compiles cleanly**: a `typst compile` smoke test with a
  ` ```lean ... ``` ` fenced block containing the `ModalSchemaTag` inductive compiled to PDF with
  exit code 0. Typst's bundled syntax-highlighter set does not include a Lean4 grammar, so the
  block renders as plain unhighlighted monospace (no error, no missing-syntax warning) — acceptable
  for this use case; no custom `.sublime-syntax` file for Lean was found anywhere on this machine,
  so syntax-highlighted Lean is not readily available without importing one, and is not needed for
  faithful rendering.

## 3. Typst Technique Reference

### 3.1 Document structure

```typst
#import "@preview/thmbox:0.3.0" as thmbox
#let thmbox-show = thmbox.thmbox-init()

#set document(title: "...", author: "CSLib (internal document)")
#set text(font: "New Computer Modern", size: 11pt)
#set heading(numbering: "1.1")
#set par(justify: true, leading: 0.55em, spacing: 0.55em, first-line-indent: 1.8em)
#set page(numbering: "1", number-align: center, margin: 1.75in)
#show heading: set block(above: 1.4em, below: 1em)
#show: thmbox-show
#show figure: set block(breakable: true)   // long tables must not overflow

= Section Heading
== Subsection Heading <label-for-cross-ref>
```

Given the source is a single ~500-line document (not a multi-chapter report), a **single
self-contained `.typ` file** is the right granularity — reuse the MPL house style (fonts,
theorem environments, table conventions) inline rather than standing up a full
`template.typ` + `notation/` + `chapters/` split, which is scaled for MPL's 7-file, title-page +
abstract report and would be over-engineered for this document's size and "concise" mandate.

### 3.2 Modal axiom-schema math notation

Reuse `shared-notation.typ`'s existing `nec`/`poss` macros for consistency across CSLib Typst
docs, plus a few local additions:

```typst
#let nec = $square.stroked$      // □ (necessity) — matches shared-notation.typ verbatim
#let poss = $diamond.stroked$    // ◇ (possibility) — matches shared-notation.typ verbatim
#let imp = $arrow.r$
#let falsum = $bot$

// Axiom schema table entries, e.g.:
$ nec phi.alt imp phi.alt $                          // T:  □φ → φ
$ nec phi.alt imp nec nec phi.alt $                  // 4:  □φ → □□φ
$ nec phi.alt imp (nec (phi.alt imp falsum) imp falsum) $   // D, literal source shape
```

### 3.3 Tables (schema tags, tag sets, frame correspondence)

```typst
#figure(
  table(
    columns: (auto, 1fr, auto),
    stroke: none,
    align: left,
    table.hline(),
    table.header([*Tag*], [*Axiom schema*], [*Frame condition*]),
    table.hline(),
    [`modalT`],    [$nec phi.alt imp phi.alt$], [reflexive: $forall w, w R w$],
    [`modalD`],    [$nec phi.alt imp poss phi.alt$], [serial],
    [`modalB`],    [$phi.alt imp nec poss phi.alt$], [symmetric],
    [`modalFour`], [$nec phi.alt imp nec nec phi.alt$], [transitive],
    [`modalFive`], [$poss phi.alt imp nec poss phi.alt$], [euclidean],
    table.hline(),
  ),
  caption: [The five modal-strength differentiators: schema, frame condition, and
    (@sec:hinge) the correspondence lemma each backs.],
)
```

### 3.4 Fletcher diagram for the modal cube (recommended addition)

`fletcher` (pinned `@preview/fletcher:0.5.8` per other CSLib/Logos Typst projects; confirmed
cached at `~/.cache/typst/packages/preview/fletcher/`) renders a genuine Hasse-diagram
replacement for the source's 24-edge bulleted list:

```typst
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#figure(
  diagram(
    cell-size: (14mm, 10mm),
    node-stroke: 0.6pt,
    edge-stroke: 0.6pt,
    mark-scale: 70%,

    node((0, 1), [K], name: <k>),
    node((1, 0), [T], name: <t>),  node((1, 1), [D], name: <d>),
    node((1, 2), [B (KB)], name: <b>), node((1, 3), [K4], name: <k4>),
    node((1, 4), [K5], name: <k5>),
    node((2, 0), [S4], name: <s4>), node((2, 1), [TB], name: <tb>),
    node((2, 2), [D4], name: <d4>), node((2, 3), [D5], name: <d5>),
    node((2, 4), [K45], name: <k45>), node((2, 5), [KB5], name: <kb5>),
    node((3, 0), [DB], name: <db>), node((3, 1), [D45], name: <d45>),
    node((4, 0.5), [S5 (ModalAxiom)], name: <s5>),

    edge(<k>, <t>, "->"), edge(<k>, <d>, "->"), edge(<k>, <b>, "->"),
    edge(<k>, <k4>, "->"), edge(<k>, <k5>, "->"),
    edge(<d>, <d4>, "->"), edge(<d>, <d5>, "->"), edge(<d>, <db>, "->"),
    edge(<t>, <s4>, "->"), edge(<t>, <tb>, "->"),
    edge(<b>, <tb>, "->"), edge(<b>, <db>, "->"), edge(<b>, <kb5>, "->"),
    edge(<k4>, <s4>, "->"), edge(<k4>, <d4>, "->"), edge(<k4>, <k45>, "->"),
    edge(<k5>, <d5>, "->"), edge(<k5>, <k45>, "->"), edge(<k5>, <kb5>, "->"),
    edge(<k45>, <d45>, "->"), edge(<d4>, <d45>, "->"), edge(<d5>, <d45>, "->"),
    edge(<s4>, <s5>, "->"), edge(<tb>, <s5>, "->"),
  ),
  caption: [The syntactic modal cube: 15 systems, 24 subsumption edges (@sec:subsumption). Every
    edge is a decidable `Finset.subset` fact; the missing KB5 -> S5 edge (@sec:s5) is the
    diagram's one visibly absent arrow.],
)
```

This is a nontrivial layout (15 nodes / 24 edges) — the implementer should expect to iterate on
`(row, col)` placement for legibility (fletcher lets fractional coordinates like `(4, 0.5)` center
a node between two columns, useful for the S5 apex). If layout proves too fiddly for a "concise"
document, a clean fallback is the grouped-bullet-list-as-table the source already uses in prose
form (Source system | Edges), which is still a improvement in scannability over free prose even
without a diagram. Treat the diagram as a stretch enhancement, not a blocking requirement.

### 3.5 Code blocks for singular Lean signatures

```typst
```lean
def SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop :=
  fun χ => ∃ t ∈ S, t.Holds χ
```
```

Confirmed via local `typst compile` smoke test (see Section 2) that triple-backtick fenced code
blocks compile without error and render as monospace (unhighlighted, since Typst's bundled
syntax set has no Lean grammar). No package or setup needed beyond Typst's built-in raw-block
support.

### 3.6 Callouts / remarks

Reuse the existing `remark(...)` thmbox environment (no new colored-box package needed — the
house style is explicitly "no background colors"):

```typst
#remark("Design invariant (module docstring, verbatim)")[
  #quote(block: true)[
    `ModalSchemaTag` / `SchemaUnion` stay free of classical-only assumptions: the
    intuitionistic/minimal axiom families are a possible future instance of this same
    abstraction, not generalized to cover them here (out of scope for this task).
  ]
]
```

`#quote(block: true)[...]` is Typst's built-in block-quote (available without any package),
suitable for the Section 7 module-docstring excerpt the source already blockquotes in Markdown.

### 3.7 Two-column comparison table (Representation A vs. B)

```typst
#figure(
  table(
    columns: (1fr, 1fr),
    stroke: none,
    align: left,
    table.hline(),
    table.header([*Representation A (chosen)*], [*Representation B (rejected)*]),
    table.hline(),
    [Subsumption: 24 lemmas -> 1 generic + `decide`],
    [Subsumption: still O(edges) proofs, macro-generated],

    [Soundness: 15 case-splits -> 1 `unionSound` + table],
    [Soundness: unchanged per-system case-splits],

    [Elimination form changes at call sites (tamed by `_iff` `@[simp]` lemmas)],
    [Elimination form (`cases`/`match`) unchanged everywhere — near-zero blast radius],

    [Net line-negative in the landed diff],
    [Adds metaprogramming maintenance burden; less auditable],
    table.hline(),
  ),
  caption: [Representation A vs. B trade-off, condensed from the source's prose bullets.],
)
```

## 4. Proposed Document Outline

Single file, `= `-level headings numbered `1.1` style, each section closing with either an inline
`remark` for a durable-anchor footer or deferring anchors to a final appendix table (recommend
the appendix-table approach, mirroring `06-appendix.typ`, to keep body prose clean):

```
Title block (no numbered page) — title, subtitle, "CSLib — Internal Document", date
Abstract / Overview — condensed lead paragraph + "two libraries" list (kept, already good)
  + a short "payoffs" callout (24->1, 15->1) + outline (#outline())

1. The Schema-Tag Alphabet
   - ModalSchemaTag as a table (18 tags x 5 role groups) instead of partial code excerpt
   - SchemaUnion definition (math + short Lean def block)
   - The 3 @[simp] elimination lemmas (kept as Lean code, they're short and singular)
   - The "14 abbrevs + S5's ModalAxiom" fact, with the literal `abbrev ModalAxiom := ...` line

2. Subsumption as Finset.subset — The Syntactic Modal Cube
   - SchemaUnion.subsumption (kept as Lean code, singular + short)
   - 15 tag-set table (System | kCore ∪ {differentiators})
   - Fletcher cube diagram (24 edges) — replaces the 24-edge bulleted list
   - Disambiguation table vs. Cube.lean (kept, already table-shaped in source)

3. unionSound: The Syntax/Semantics Hinge
   - Frame-correspondence table (5 rows: tag, schema, frame condition, lemma name) —
     replaces 5 near-duplicate Lean lemma blocks
   - FrameValidatesTag (kept as Lean code, singular, worth showing the 18-arm shape)
   - unionSound signature (kept as Lean code, the hinge itself)

4. The HasAxiom* Insulation Layer
   - HasAxiomT representative signature (kept as Lean code)
   - Typeclass hierarchy as a small tree (fletcher, optional) or nested list —
     replace the dense run-on `extends`-chain paragraph
   - Note: same shape as the Section 2 cube (explicit callout)
   - HasAxiomT instance witness for S5 (kept as Lean code, the "verified not merely asserted" bit)

5. S5 = T+4+B — The Deliberately Omitted KB5 -> S5 Edge
   - s5Tags / kb5Tags side-by-side (math or 2-row table)
   - Short prose explaining the decide-false consequence

6. Design Rationale: Representation A vs. Representation B
   - Comparison table (Section 3.7 above) replacing the prose-bullet trade-off list

7. Scope Boundary: A Future Instance, Not a Fork
   - Module-docstring quote (#quote block)
   - Short list of existing out-of-scope families (IKModalAxiom, IS5ModalAxiom, CKModalAxiom,
     MKModalAxiom, MTModalAxiom) with anchors

Appendix: Source Anchors
   - One consolidated table, mirroring typst/MPL/chapters/06-appendix.typ's pattern:
     File:lines | Declaration — section supported
```

## 5. Output Location and Filename

**Recommendation**: `typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ`, following
the one-project-per-directory-under-`typst/` convention already established by `typst/MPL/`
(the only existing precedent in this repo), but as a **single self-contained file** (no separate
`template.typ`/`notation/` split, no chapter-per-file split) since the source is a single ~500-line
document, not a multi-chapter report — matching the "clear and concise" mandate and avoiding the
over-engineering a full MPL-style scaffold would add for content this size.

- Compiled output: `typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf`,
  matching the `build/` subdirectory convention observed in `typst/MPL/build/MplReport.pdf`
  (present in the working tree, not `.gitignore`d — no `.gitignore` entry for `typst`/`.pdf`/
  `build` was found, so the PDF should be committed alongside the source, matching precedent).
- Compile command: `typst compile
  typst/ModalAxiomArchitecture/modal-axiom-schema-architecture.typ
  typst/ModalAxiomArchitecture/build/modal-axiom-schema-architecture.pdf` — verified `typst`
  0.14.2 is on `PATH` in this environment and successfully compiles a smoke-test file using the
  same font (`New Computer Modern`, confirmed installed) and a Lean-fenced code block.
- The original `docs/modal-axiom-schema-architecture.md` should be left in place; the Typst
  document is a derived, differently-purposed artifact (a typeset/printable rendering), not a
  replacement — no reason found to move or delete the Markdown source, and nothing in the task
  description asks for that.

**Alternative considered and rejected**: co-locating the `.typ` file directly in `docs/` (e.g.
`docs/modal-axiom-schema-architecture.typ`). Rejected because `docs/` currently holds only
Markdown, and `typst/` is this repo's established convention for Typst-authored deliverables
(with its own `build/` output convention) — keeping Typst sources there is more consistent with
existing repo structure than introducing a mixed-format `docs/` directory.

## 6. Verification Performed

- Read `docs/modal-axiom-schema-architecture.md` in full (508 lines).
- Read `typst/MPL/template.typ`, `typst/MPL/MplReport.typ`,
  `typst/MPL/notation/{shared,mpl}-notation.typ`, `typst/MPL/chapters/{00,03,04,06}-*.typ` in
  full to extract house-style conventions.
- Confirmed `typst` 0.14.2 is installed and on `PATH`.
- Confirmed `@preview/thmbox:0.3.0` and `@preview/fletcher` (0.5.x family) are cached locally at
  `~/.cache/typst/packages/preview/{thmbox,fletcher}/` — no network fetch required to compile
  either.
- Ran a local `typst compile` smoke test combining a fenced ` ```lean ` code block, `□`/`◇` via
  `square.stroked`/`diamond.stroked`, an existential-quantifier math expression, and a table —
  compiled to PDF with exit code 0, confirming the core techniques recommended above (Sections
  3.2, 3.3, 3.5) work in this environment without further setup.
- Grepped the whole repository for existing `.typ` files and confirmed `typst/MPL/` is the only
  existing precedent (no other `.typ` files found).
- Confirmed no `.gitignore` entries exclude `typst/`, `*.pdf`, or `build/`, consistent with the
  observation that `typst/MPL/build/MplReport.pdf` exists in the working tree.

## 7. Open Questions for the Planning/Implementation Phase

1. Should the fletcher cube diagram (Section 3.4) be attempted, or is the grouped-table fallback
   preferred for a strictly "concise" first pass? The diagram is the single highest-value addition
   but is also the highest layout-effort item; recommend attempting it but not blocking on
   pixel-perfect layout.
2. Should `Axioms.AxiomB`'s expansion (`φ → □◇φ`) be inlined in the frame-correspondence table, or
   cited opaquely as `AxiomsAxiomB(φ)`? Recommend a quick `grep -n "AxiomB"
   Cslib/Logics/Modal/**/*.lean` during implementation to confirm the exact definition before
   asserting the standard-textbook expansion in print (this repo's own axiom naming has in the
   past differed subtly from textbook defaults — verify, don't assume).
3. Whether to add a `#outline()` table of contents given the document is single-file and only
   7 sections + appendix (arguably unnecessary at this length, unlike MPL's 6-chapter report) —
   recommend a lightweight decision left to planning, not research.
