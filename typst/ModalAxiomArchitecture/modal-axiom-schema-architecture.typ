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
// no fill, consistent with the "no background colors" house style.
#show raw.where(block: true): it => block(
  width: 100%,
  inset: (x: 0.9em, y: 0.7em),
  stroke: (top: 0.4pt + black, bottom: 0.4pt + black),
  breakable: true,
  text(size: 9.3pt, it),
)

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
