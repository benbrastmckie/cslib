// ============================================================================
// mpl-notation.typ
// MPL report notation macros.
//
// Imports the shared notation package (reusing imp, lneg, falsum, proves, ctx,
// metaphi/metapsi/metachi, leansrc/leanref) and adds only the propositional
// and algebraic macros this report needs on top of it. Modal/temporal macros
// from shared-notation.typ (nec/poss) are simply not used.
// ============================================================================

#import "shared-notation.typ": *

// ============================================================================
// Propositional Connectives (not in shared-notation.typ)
// ============================================================================

#let pand = $and$          // conjunction
#let por = $or$            // disjunction
#let ptop = $top$          // truth (derived: bot imp bot)
#let iff = $arrow.l.r$     // biconditional

// The ex-falso-quodlibet schema (explosion)
#let efqschema = $falsum arrow.r metaphi$

// ============================================================================
// Order / Algebra Notation
// ============================================================================

#let ale = $lt.eq$         // algebraic order
#let ameet = $inter$       // meet (greatest lower bound)
#let ajoin = $union$       // join (least upper bound)
#let himp = $arrow.r.double$   // Heyting/relative-pseudocomplement implication
#let subvar = $supset$     // "is a subvariety of" (used informally in prose)

// ============================================================================
// Signature
// ============================================================================

// The fixed propositional signature Sigma = {bot, imp, and, or}
#let sig = ${ falsum, arrow.r, and, or }$

// ============================================================================
// Lean identifier helper
// ============================================================================

// Short alias for an inline Lean identifier rendered as monospace.
#let lean(name) = raw(name)
