// ============================================================================
// template.typ
// Shared template with theorem environments for all chapters
//
// Styling follows the AMS/journal aesthetic: austere, black-only body text,
// no background colors on theorem environments. Link colors (URLblue) are
// preserved for digital usability.
//
// Adapted near-verbatim from BimodalLogic/Theories/Bimodal/typst/template.typ;
// only the notation import is re-pointed to notation/mpl-notation.typ.
// ============================================================================

#import "@preview/thmbox:0.3.0" as thmbox
#import "notation/mpl-notation.typ": *

// ============================================================================
// Color Definitions
// ============================================================================

// URLblue color for hyperlinks
#let URLblue = rgb(30, 144, 255)  // Light blue (Dodger Blue)

// ============================================================================
// thmbox initialization function
// ============================================================================

// thmbox-init sets up the theorem environment system
#let thmbox-show = thmbox.thmbox-init()

// ============================================================================
// Custom Theorem Environment Styling
// ============================================================================

// Journal-style theorem environments - AMS aesthetic with no background colors
//
// AMS convention:
// - Theorems/lemmas: italic body text (plain style)
// - Definitions: upright body, defined terms in italic (definition style)
// - Remarks: upright body, less prominent (remark style)

#let theorem-style = (
  fill: none,
  stroke: none,
  bodyfmt: it => emph(it),  // Italic body per AMS plain style
)

#let definition-style = (
  fill: none,
  stroke: none,
  // Upright body (thmbox default) per AMS definition style
)

#let axiom-style = (
  fill: none,
  stroke: none,
  bodyfmt: it => emph(it),  // Italic body like theorems
)

#let remark-style = (
  fill: none,
  stroke: none,
  // Upright body (thmbox default) per AMS remark style
)

// ============================================================================
// Theorem Environments (using thmbox predefined environments with custom styling)
// ============================================================================

// Chapters use: definition, theorem, lemma, axiom, remark, proof
#let definition = thmbox.definition.with(..definition-style)
#let theorem = thmbox.theorem.with(..theorem-style)
#let lemma = thmbox.lemma.with(..theorem-style)
#let axiom = thmbox.axiom.with(..axiom-style)
#let remark = thmbox.remark.with(..remark-style)
#let proof = thmbox.proof
