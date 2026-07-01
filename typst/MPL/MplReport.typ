// ============================================================================
// MplReport.typ
// MPL: Arguments for a Structure-First Design
//
// An internal report presenting the case for the structure-first design of
// Minimal Propositional Logic (MPL) in CSLib: one fixed signature
// Sigma = {bot, imp, and, or} in which bot is a designated but unconstrained
// nullary operator at MPL strength, strengthened to IPL by adjoining leastness
// plus efq, then to CPL by classicality.
//
// Structure adapted from BimodalLogic/Theories/Bimodal/typst/BimodalReference.typ.
// ============================================================================

// ============================================================================
// Package Imports
// ============================================================================

// Local notation and template (includes thmbox theorem environments)
#import "notation/mpl-notation.typ": *
#import "template.typ": thmbox-show, URLblue, definition, theorem, lemma, axiom, remark, proof

// ============================================================================
// Document Configuration
// ============================================================================

#set document(
  title: "MPL: Arguments for a Structure-First Design",
  author: "CSLib (internal report)",
)

// Typography settings - LaTeX-like appearance
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
// Theorem Environment Initialization
// ============================================================================

#show: thmbox-show

// Style hyperlinks in URLblue color
#show link: set text(fill: URLblue)

// Allow theorem boxes to break across pages
#show figure.where(kind: "thmbox"): set block(breakable: true)

// ============================================================================
// Custom Commands
// ============================================================================

// Horizontal rule
#let HRule = line(length: 100%, stroke: 0.5pt)

// ============================================================================
// Title Page
// ============================================================================

#page(numbering: none)[
  #v(2cm)
  #align(center)[
    #HRule
    #v(0.4cm)
    #text(size: 24pt, weight: "bold")[MPL: Arguments for a Structure-First Design]
    #v(0.2cm)
    #HRule
    #v(.5cm)

    #text(size: 16pt, style: "italic")[One signature, a tower of properties: why $bot$ is a primitive]
    #v(1cm)

    #text(size: 12pt, style: "italic")[CSLib --- Internal Report]
    #v(0.2cm)
    #text(size: 11pt)[Task 464]
    #v(0.2cm)
    --- #datetime.today().display("[month repr:long] [day], [year]") ---
    #v(1cm)

    #v(1fr)

    #block(width: 82%)[
      #set text(size: 10pt)
      #set par(justify: true, first-line-indent: 0em)
      #align(left)[
        *Internal document.* This report is written for internal design review
        of the `Cslib/Logics/Propositional/` development. Per the CSLib AI
        policy (raised on the source Zulip thread, messages #605827029 /
        #605840135), any prose later adapted for an upstream, community-facing
        post must be human-authored; this document itself is an internal
        artifact and is not a publication.
      ]
    ]
    #v(1cm)
  ]
]

// ============================================================================
// Abstract
// ============================================================================

#page(numbering: none)[
  #v(1em)
  #align(center)[
    #text(size: 14pt, weight: "bold")[Abstract]
  ]
  #v(1em)

  This report argues for the *structure-first* design of Minimal Propositional
  Logic (MPL) as realized in the `Cslib/Logics/Propositional/` development.
  On this design there is *one* fixed signature $sig$, and the type of formulas
  is the free monad on that signature: $bot$ is a designated but wholly
  unconstrained *nullary operation* at MPL strength. The logics
  $"MPL" subset "IPL" subset "CPL"$ then form a descending chain of
  *varieties* over that single signature --- pointed generalized-Heyting
  (Johansson) $supset$ Heyting $supset$ Boolean --- each step adjoining *one*
  identity. The keystone argument is that only when $bot$ is a nullary operation
  is "explosion $=$ leastness" a *variety-defining identity*
  ($bot inter x = bot$); this is what makes the whole
  "strengthen-by-a-property $=$ take-a-subvariety" architecture well-formed.
  We give equal weight to the realized Lean 4 engineering: the single gate
  `[IsIntuitionistic T]` instantiated across four proof systems, the Option-C
  resolution of the Hilbert-vs-ND controversy, graded faithfulness, and the
  exact sorry-free scope. A dedicated chapter states the honest limits.

  #v(0.8em)

  #figure(
    table(
      columns: 4,
      stroke: none,
      align: left,
      table.hline(),
      table.header(
        [*Logic*], [*Constraint on $bot$*], [*Rule added*], [*Lean theory*],
      ),
      table.hline(),
      [MPL], [none (free nullary op)], [---], [`MinPropAxiom` / `GHAValid`],
      [IPL], [leastness ($bot inter x = bot$)], [`efq`], [`IntPropAxiom` / `HasLeastBot`],
      [CPL], [+ classicality], [`peirce`], [`PropositionalAxiom` / Boolean],
      table.hline(),
    ),
    caption: [The $"MPL" subset "IPL" subset "CPL"$ ladder: one signature, one
      evaluator; only the constraint on the single element $bot$ (and the
      matching proof rule) changes.],
  )

  #v(1cm)

  // Styled Contents header
  #align(center)[
    #text(size: 14pt, weight: "bold")[Contents]
  ]
  #v(1em)

  #show outline.entry.where(level: 1): it => {
    v(0.5em)
    strong(it)
  }
  #outline(title: none, indent: auto)
]

#pagebreak()

// ============================================================================
// Content
// ============================================================================

#include "chapters/00-introduction.typ"
#include "chapters/01-syntax.typ"
#include "chapters/02-semantics.typ"
#include "chapters/03-proof-theory.typ"
#include "chapters/04-debate.typ"
#include "chapters/05-honest-limits.typ"
#include "chapters/06-appendix.typ"
