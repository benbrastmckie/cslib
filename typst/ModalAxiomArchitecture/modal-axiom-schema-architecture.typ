// ============================================================================
// modal-axiom-schema-architecture.typ
// The Modal Axiom-Schema Architecture: SchemaUnion, ModalSchemaTag, and the
// unionSound hinge.
//
// A single, self-contained Typst rendering of docs/modal-axiom-schema-architecture.md,
// reusing the house style established by typst/MPL/ (thmbox theorem
// environments, austere AMS/journal aesthetic, New Computer Modern, the
// nec/poss modal-operator macros). Source content is derived from the
// CI-green, landed Lean code cited in each section's durable anchors.
// ============================================================================

// ============================================================================
// Package Imports
// ============================================================================

#import "@preview/thmbox:0.3.0" as thmbox
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

// ============================================================================
// Document Configuration
// ============================================================================

#set document(
  title: "The Modal Axiom-Schema Architecture",
  author: "CSLib (internal document)",
)

// Typography settings, matching typst/MPL/MplReport.typ
#set text(font: "New Computer Modern", size: 11pt)
#set heading(numbering: "1.1")
#set par(
  justify: true,
  leading: 0.55em,
  spacing: 0.55em,
  first-line-indent: 1.8em,
)

// Page layout with LaTeX-like margins
#set page(
  numbering: "1",
  number-align: center,
  margin: 1.75in,
)

// Heading spacing
#show heading: set block(above: 1.4em, below: 1em)

// ============================================================================
// Color Definitions (link color only -- austere, no fill/background colors)
// ============================================================================

#let URLblue = rgb(30, 144, 255)

// ============================================================================
// Theorem Environment Initialization (thmbox, AMS austere aesthetic)
// ============================================================================

#let thmbox-show = thmbox.thmbox-init()

#let theorem-style = (
  fill: none,
  stroke: none,
  bodyfmt: it => emph(it), // Italic body per AMS plain style
)

#let definition-style = (
  fill: none,
  stroke: none, // Upright body (thmbox default) per AMS definition style
)

#let remark-style = (
  fill: none,
  stroke: none, // Upright body (thmbox default) per AMS remark style
)

#let definition = thmbox.definition.with(..definition-style)
#let theorem = thmbox.theorem.with(..theorem-style)
#let lemma = thmbox.lemma.with(..theorem-style)
#let remark = thmbox.remark.with(..remark-style)

#show: thmbox-show

// Style hyperlinks in URLblue color
#show link: set text(fill: URLblue)

// Allow theorem boxes and figures (tables, diagrams) to break across pages
#show figure.where(kind: "thmbox"): set block(breakable: true)
#show figure: set block(breakable: true)

// Fenced Lean signatures render as hairline-ruled monospace blocks: austere,
// black-only, no fill, consistent with the house style. Language tags are
// dropped so no syntax-highlighting color is applied (Non-Goal: no custom
// Lean grammar; unhighlighted monospace is the intended rendering) -- this
// also keeps code blocks visually consistent with the rest of the austere,
// black-only body.
#show raw.where(block: true): it => if it.lang == none {
  block(
    width: 100%,
    inset: (x: 0.9em, y: 0.7em),
    stroke: (top: 0.4pt + black, bottom: 0.4pt + black),
    breakable: true,
    text(size: 9.3pt, fill: black, it),
  )
} else {
  raw(it.text, lang: none, block: true)
}

// ============================================================================
// Notation Macros
// ============================================================================

// Modal operators, copied verbatim from typst/MPL/notation/shared-notation.typ
#let nec = $square.stroked$
#let poss = $diamond.stroked$
#let imp = $arrow.r$
#let falsum = $bot$

// Local helpers for this document
#let lean(name) = raw(name) // inline Lean identifier, monospace
#let iff = $arrow.l.r$
#let subs = $subset.eq$ // Finset.subset

// Horizontal rule (matches typst/MPL/MplReport.typ)
#let HRule = line(length: 100%, stroke: 0.5pt)

// ============================================================================
// Title Page
// ============================================================================

#page(numbering: none)[
  #v(2cm)
  #align(center)[
    #HRule
    #v(0.4cm)
    #text(size: 22pt, weight: "bold")[The Modal Axiom-Schema Architecture]
    #v(0.2cm)
    #HRule
    #v(0.5cm)

    #text(size: 14pt, style: "italic")[
      #lean("SchemaUnion"), #lean("ModalSchemaTag"), and the #lean("unionSound") hinge
    ]
    #v(1cm)

    #text(size: 12pt, style: "italic")[CSLib --- Internal Document]
    #v(0.2cm)
    --- #datetime.today().display("[month repr:long] [day], [year]") ---
    #v(1cm)

    #v(1fr)

    #block(width: 82%)[
      #set text(size: 10pt)
      #set par(justify: true, first-line-indent: 0em)
      #align(left)[
        *Internal document.* This report renders the architecture note
        `docs/modal-axiom-schema-architecture.md` as a typeset deliverable. It
        is a derived, differently-purposed artifact -- the Markdown source
        remains the primary reference and is unchanged by this document.
        Definitions, lemma signatures, and axiom schemas are transcribed from
        the landed, CI-green Lean source cited in each section's anchors, not
        from memory.
      ]
    ]
    #v(1cm)
  ]
]

// No #outline() at this length (seven short sections plus a one-table
// appendix) -- a table of contents would add a page without aiding
// navigation. Decision recorded here per the plan's front-matter step.

#pagebreak()

// ============================================================================
// Overview
// ============================================================================

= Overview

CSLib's modal-logic layer formalizes 15 classical normal modal systems --- K, T,
D, B (a.k.a.\ KB), K4, K5, K45, S4, S5, TB, KB5, D4, D5, D45, DB --- each as a
Hilbert-style proof system over a shared propositional/modal `Proposition`
language. Each system's axiom set was historically a bespoke, hand-written
`inductive` with its own 13--18 constructors, byte-identical to its siblings on
a shared propositional/K/and-or/diamond-duality core and differing only in
which modal-strength schemata (T, D, B, 4, 5) it admits. This document
describes the compositional architecture that replaced those hand-written
inductives: *15 systems, unified under 14 renamed `<Sys>Axiom` abbreviations
plus S5's pre-existing `ModalAxiom`*, all expressed as one-line `abbrev`s over a
single combinator, #lean("SchemaUnion"), and a single 18-tag alphabet,
#lean("ModalSchemaTag").

The architecture rests on two libraries, two halves of one abstraction:

- *`SchemaUnion.lean`* (+ `SchemaTags.lean`) --- the _syntactic_ side: the tag
  alphabet, the existential "schema = set of instances" meaning function, the
  `SchemaUnion` combinator, and the elimination lemmas that make the modal
  cube's $subs$-order a `decide`-able computation on `Finset ModalSchemaTag`
  values.
- *`FrameCorrespondence.lean`* (+ `SchemaSoundness.lean`) --- the _semantic_
  side: the five frame-condition-to-validity correspondence lemmas for the
  modal-strength differentiators, and the master soundness lemma,
  #lean("unionSound"), hinging the two sides together.

Two payoffs fall out directly: *subsumption* collapses from 24 hand-written
per-edge lemmas to one generic `SchemaUnion.subsumption` application discharged
by `decide`-able `Finset.subset` facts (@sec:tags), and *soundness* collapses
from 15 per-system case-splits to one `unionSound` application consuming an
18-entry `FrameValidatesTag` table plus the five frame-correspondence lemmas
(Section 3, "`unionSound`: The Syntax/Semantics Hinge").

// ============================================================================
// Section 1: The Schema-Tag Alphabet
// ============================================================================

= The Schema-Tag Alphabet: `ModalSchemaTag`, `.Holds`, and `SchemaUnion` <sec:tags>

*Durable anchor*: `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`.

Every one of the 15 classical systems' axiom set is built from the same finite
vocabulary of axiom _schemata_. `ModalSchemaTag` names that vocabulary as an
18-constructor alphabet, grouping into five roles (4 + 1 + 5 + 6 + 2 = 18):

#figure(
  table(
    columns: (auto, auto, 1fr),
    stroke: none,
    align: (left, left, left),
    column-gutter: 0.8em,
    table.hline(),
    table.header([*Role*], [*Tag*], [*Schema*]),
    table.hline(),
    table.cell(rowspan: 4)[Propositional core],
      [`implyK`], [$phi.alt imp (psi imp phi.alt)$],
    [`implyS`], [$(phi.alt imp (psi imp chi)) imp ((phi.alt imp psi) imp (phi.alt imp chi))$],
    [`efq`], [$falsum imp phi.alt$],
    [`peirce`], [$((phi.alt imp psi) imp phi.alt) imp phi.alt$],
    table.hline(),
    table.cell(rowspan: 1)[K-distribution],
      [`modalK`], [$nec (phi.alt imp psi) imp (nec phi.alt imp nec psi)$],
    table.hline(),
    table.cell(rowspan: 5)[Modal-strength\ differentiators],
      [`modalT`], [$nec phi.alt imp phi.alt$],
    [`modalD`], [$nec phi.alt imp poss phi.alt$],
    [`modalB`], [$phi.alt imp nec poss phi.alt$],
    [`modalFour`], [$nec phi.alt imp nec nec phi.alt$],
    [`modalFive`], [$poss phi.alt imp nec poss phi.alt$],
    table.hline(),
    table.cell(rowspan: 6)[And/or],
      [`andI`], [$phi.alt imp (psi imp (phi.alt and psi))$],
    [`andE1`], [$(phi.alt and psi) imp phi.alt$],
    [`andE2`], [$(phi.alt and psi) imp psi$],
    [`orI1`], [$phi.alt imp (phi.alt or psi)$],
    [`orI2`], [$psi imp (phi.alt or psi)$],
    [`orE`], [$(phi.alt imp chi) imp ((psi imp chi) imp ((phi.alt or psi) imp chi))$],
    table.hline(),
    table.cell(rowspan: 2)[Diamond duality],
      [`diaDualityFwd`], [$poss phi.alt imp not nec not phi.alt$],
    [`diaDualityBack`], [$not nec not phi.alt imp poss phi.alt$],
    table.hline(),
  ),
  caption: [The 18 `ModalSchemaTag` constructors, grouped by role. Schemas are
    transcribed verbatim from each constructor's doc comment in
    `SchemaUnion.lean`.],
) <fig:tags>

A tag by itself is just a label; #lean("ModalSchemaTag.Holds") gives each tag
its formula-level meaning as an existential over the schema's metavariables ---
the "schema = set of its instances" encoding used throughout:

```lean
def ModalSchemaTag.Holds : ModalSchemaTag → Proposition Atom → Prop
  | .implyK, χ => ∃ φ ψ : Proposition Atom, χ = φ.imp (ψ.imp φ)
  | .modalT, χ => ∃ φ : Proposition Atom, χ = (Proposition.box φ).imp φ
  | .modalB, χ => ∃ φ : Proposition Atom, χ = Axioms.AxiomB φ
  -- … 15 further clauses, one per remaining tag
```

Every clause's proposition shape matches, byte-for-byte, the corresponding
constructor of the pre-existing per-system axiom inductives, which is what
makes it possible to replace those inductives with a single combinator,
parametrized by a chosen `Finset` of tags:

```lean
def SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop :=
  fun χ => ∃ t ∈ S, t.Holds χ
```

`SchemaUnion S χ` holds iff `χ` is an instance of some tag in `S`. Because the
alphabet is finite and carries `DecidableEq`, choosing `S` to be a concrete
`Finset` literal turns each system's axiom predicate into a one-line
declaration. Fourteen of the fifteen systems now read `abbrev <Sys>Axiom :=
SchemaUnion sysTags` in `ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,TB,KB5,
D4,D5,D45,DB}.lean`. S5 is not a structural exception: `Metalogic/
DerivationTree.lean` line 69 reads exactly

```lean
abbrev ModalAxiom : Proposition Atom → Prop := SchemaUnion s5Tags
```

so `ModalAxiom` is the 15th system folded into the same
one-line-abbrev-over-`SchemaUnion` pattern as the other 14, its name and public
API preserved by redefinition-in-place.

Alongside the combinator, three `@[simp]` elimination lemmas give the
ergonomic half of the design: a concrete `SchemaUnion sysTags φ` obligation
rewrites via `simp` into the named disjunction of its tags' `.Holds` clauses,
rather than requiring raw `fin_cases` destructuring at every call site:

```lean
theorem SchemaUnion.empty_iff {φ : Proposition Atom} :
    SchemaUnion (∅ : Finset ModalSchemaTag) φ ↔ False

theorem SchemaUnion.insert_iff {t : ModalSchemaTag} {S : Finset ModalSchemaTag}
    {φ : Proposition Atom} :
    SchemaUnion (insert t S) φ ↔ t.Holds φ ∨ SchemaUnion S φ

theorem SchemaUnion.union_iff {Sa Sb : Finset ModalSchemaTag} {φ : Proposition Atom} :
    SchemaUnion (Sa ∪ Sb) φ ↔ SchemaUnion Sa φ ∨ SchemaUnion Sb φ
```

*Durable anchors*: `SchemaUnion.lean` (`ModalSchemaTag`, `.Holds`,
`SchemaUnion`, the three `@[simp]` lemmas); `Metalogic/DerivationTree.lean`
(`ModalAxiom`, line 69); `ProofSystem/Instances/{K,…,S5}.lean` (the 15
per-system instance-registration files).

// ============================================================================
// Section 2: Subsumption as Finset.subset
// ============================================================================

= Subsumption as `Finset.subset`: The Syntactic Modal Cube <sec:cube>

*Durable anchors*: `SchemaUnion.subsumption` (`SchemaUnion.lean`),
`SchemaTags.lean` (the 15 per-system tag sets), `Metalogic/InterSystem/
AxiomSubsumption.lean` (the 24 direct-edge lemmas).

The modal cube --- the familiar inclusion order K $subs$ T $subs$ S4 $subs$ S5,
and its 11 further systems and their edges --- used to be witnessed by 24
hand-written, per-edge subsumption lemmas, each proved by a bespoke case
analysis over the source system's axiom inductive. `SchemaUnion` replaces all
24 with one generic lemma:

```lean
theorem SchemaUnion.subsumption {Sa Sb : Finset ModalSchemaTag} (hsub : Sa ⊆ Sb)
    {φ : Proposition Atom} (h : SchemaUnion Sa φ) : SchemaUnion Sb φ
```

Enlarging the tag set only weakens the resulting predicate --- the proof is
three lines (`obtain ⟨t, ht, hφ⟩ := h; exact ⟨t, hsub ht, hφ⟩`). Every
`XAxiom_implies_YAxiom` lemma across the cube is now `SchemaUnion.subsumption
(by decide) h`: a `decide`-able `Finset.subset` fact, discharged automatically
because `ModalSchemaTag` is a finite `DecidableEq` type and every system's tag
set is a concrete `Finset` literal built from `insert`/`kCore`. This is the
framing point of the whole design: *the modal cube's $subs$-order IS the
$subs$-order on tag sets* --- subsumption is no longer a proved fact about 15
independent inductives, it is a computation on 15 `Finset` values.

== The 15 tag sets

Each of the 15 per-system tag sets (`SchemaTags.lean`) is the shared 13-tag
core, `kCore`, unioned with a subset of the 5 modal-strength differentiator
tags:

```lean
def kCore : Finset ModalSchemaTag :=  -- 13 tags: implyK, implyS, efq, peirce,
  …                                    -- modalK, andI, andE1, andE2, orI1,
                                        -- orI2, orE, diaDualityFwd, diaDualityBack
```

#figure(
  table(
    columns: (auto, 1fr),
    stroke: none,
    align: left,
    column-gutter: 1em,
    table.hline(),
    table.header([*System*], [*Tag set*]),
    table.hline(),
    [K], [`kCore`],
    [T], [`kCore` $union$ {modalT}],
    [D], [`kCore` $union$ {modalD}],
    [B (KB)], [`kCore` $union$ {modalB}],
    [K4], [`kCore` $union$ {modalFour}],
    [K5], [`kCore` $union$ {modalFive}],
    [K45], [`kCore` $union$ {modalFour, modalFive}],
    [S4], [`kCore` $union$ {modalT, modalFour}],
    [S5], [`kCore` $union$ {modalT, modalFour, modalB}],
    [TB], [`kCore` $union$ {modalT, modalB}],
    [KB5], [`kCore` $union$ {modalB, modalFive}],
    [D4], [`kCore` $union$ {modalD, modalFour}],
    [D5], [`kCore` $union$ {modalD, modalFive}],
    [D45], [`kCore` $union$ {modalD, modalFour, modalFive}],
    [DB], [`kCore` $union$ {modalD, modalB}],
    table.hline(),
  ),
  caption: [The 15 per-system tag sets, each `kCore` unioned with a subset of
    the 5 differentiator tags (`SchemaTags.lean`).],
) <fig:tagsets>

== The syntactic modal cube

The 24 direct edges in `AxiomSubsumption.lean` --- each now a one-line
`SchemaUnion.subsumption (by decide) h` proof, where previously each was a
hand-written per-edge `match`/`cases` lemma --- form a layered DAG on the 15
tag sets, ordered by number of differentiators:

#figure(
  diagram(
    node-stroke: 0.6pt,
    spacing: (2.1em, 3.4em),

    node((3, 0), [K], name: <K>),

    node((0, 1), [T], name: <T>),
    node((1.5, 1), [D], name: <D>),
    node((3, 1), [KB], name: <B>),
    node((4.5, 1), [K4], name: <K4>),
    node((6, 1), [K5], name: <K5>),

    node((0, 2), [S4], name: <S4>),
    node((1, 2), [TB], name: <TB>),
    node((2, 2), [D4], name: <D4>),
    node((3, 2), [D5], name: <D5>),
    node((4, 2), [DB], name: <DB>),
    node((5, 2), [KB5], name: <KB5>),
    node((6, 2), [K45], name: <K45>),

    node((0.5, 3), [S5], name: <S5>),
    node((4, 3), [D45], name: <D45>),

    edge(<K>, <T>, "-|>"),
    edge(<K>, <D>, "-|>"),
    edge(<K>, <B>, "-|>"),
    edge(<K>, <K4>, "-|>"),
    edge(<K>, <K5>, "-|>"),

    edge(<T>, <S4>, "-|>"),
    edge(<T>, <TB>, "-|>"),
    edge(<D>, <D4>, "-|>"),
    edge(<D>, <D5>, "-|>"),
    edge(<D>, <DB>, "-|>"),
    edge(<B>, <TB>, "-|>"),
    edge(<B>, <DB>, "-|>"),
    edge(<B>, <KB5>, "-|>"),
    edge(<K4>, <S4>, "-|>"),
    edge(<K4>, <D4>, "-|>"),
    edge(<K4>, <K45>, "-|>"),
    edge(<K5>, <D5>, "-|>"),
    edge(<K5>, <KB5>, "-|>"),
    edge(<K5>, <K45>, "-|>"),

    edge(<S4>, <S5>, "-|>"),
    edge(<TB>, <S5>, "-|>"),
    edge(<K45>, <D45>, "-|>"),
    edge(<D4>, <D45>, "-|>"),
    edge(<D5>, <D45>, "-|>"),
  ),
  caption: [The 24-edge syntactic modal cube (`AxiomSubsumption.lean`),
    layered by differentiator count. Every edge is a `decide`-able
    `Finset.subset` fact between the two systems' tag sets (@fig:tagsets).
    Notably absent: KB5 $arrow.r$ S5 (Section 5, "S5 = T+4+B").],
) <fig:cube>

#remark("Reading the diagram")[
  Row 0 is `kCore` alone (K); row 1 adds one differentiator; row 2 adds two;
  row 3 (S5, D45) adds three. Every edge points from a smaller tag set to a
  `Finset.insert`/`∪`-larger one. The two into-S5 edges (from S4 and TB) are
  the only edges terminating at row 3 from a single-parent T/4/B combination;
  D45 gathers edges from all three of its two-differentiator predecessors
  (K45, D4, D5).
]

== Disambiguation: this is not `Cslib/Logics/Modal/Cube.lean`

CSLib has a second, pre-existing artifact also called "the modal cube":
`Cube.lean` defines each classical system as a *semantic* frame-class --- a
`Set (Model World Atom)` characterized by a frame property, e.g.

```lean
def T World Atom := logic {m : Model World Atom | Std.Refl m.r}
```

`Cube.lean` was authored for a different purpose and predates the
schema-union combinator. It must not be conflated with the syntactic tag-set
cube of this section:

#text(size: 9.5pt)[
#figure(
  table(
    columns: (1fr, 1.5fr, 1.1fr, 1.3fr),
    stroke: none,
    align: left,
    column-gutter: 0.8em,
    table.hline(),
    table.header([*Artifact*], [*File*], [*Kind*], [*Each system is a…*]),
    table.hline(),
    [Semantic frame-class cube], [`Cube.lean`], [pre-existing, frame-based],
      [`Set (Model World Atom)`],
    [Syntactic tag-set cube], [`AxiomSubsumption.lean`\ + `SchemaTags.lean`],
      [new, proof-theoretic], [`Finset ModalSchemaTag`],
    table.hline(),
  ),
  caption: [The two independent "modal cube" artifacts living side by side.
    This document is about the syntactic tag-set cube only.],
)
]
