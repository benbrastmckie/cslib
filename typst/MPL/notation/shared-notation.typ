// ============================================================================
// shared-notation.typ
// Shared notation package for CSLib logic documentation
//
// This module provides standard notation used across theory-specific
// documentation. Theory-specific notation files should import this module
// and add specialized notation.
//
// Copied verbatim from BimodalLogic/Theories/Bimodal/typst/notation/.
// ============================================================================

// ============================================================================
// Modal Operators
// ============================================================================

#let nec = $square.stroked$
#let poss = $diamond.stroked$

// ============================================================================
// Truth and Satisfaction Relations
// ============================================================================

#let trueat = $tack.r.double$
#let ntrueat = $tack.r.double.not$

// ============================================================================
// Proof Theory
// ============================================================================

#let proves = $tack.r$
#let ctx = $Gamma$

// ============================================================================
// Meta-Variables
// ============================================================================

#let metaphi = $phi.alt$
#let metapsi = $psi$
#let metachi = $chi$

// ============================================================================
// Model Notation
// ============================================================================

#let model = $cal(M)$
#let tuple(..args) = $lr(angle.l #args.pos().join(", ") angle.r)$
#let define = $:=$

// ============================================================================
// Propositional Connectives
// ============================================================================

#let imp = $arrow.r$
#let lneg = $not$
#let falsum = $bot$

// ============================================================================
// Lean Cross-Reference Commands
// ============================================================================

#let leansrc(module, name) = raw(module + "." + name)
#let leanref(name) = raw(name)
