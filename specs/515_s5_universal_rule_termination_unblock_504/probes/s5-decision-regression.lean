/-
S5 tableau decision-procedure regression corpus (task 515 phase 14).

RUN WITH: `lake env lean specs/515_s5_universal_rule_termination_unblock_504/probes/s5-decision-regression.lean`
Exit 0 with no output means every `#guard` passed.

WHY A PROBE, NOT A `CslibTests/` MODULE: this file runs the shipped decision procedure
`modalTableauS5` at build time via `#guard` (interpreter evaluation). That requires native
compiled code for the tableau's transitive dependencies (`modalFuel._redArg`, ...). This repo's
`Cslib` lean_lib is not built with `precompileModules := true`, and every file reachable from the
`CslibTests` barrel is a `module`, so a `module`-mode `#guard` fails to link those native symbols
("Could not find native implementation of external declaration 'modalFuel._redArg'"). A
non-`module` probe run under `lake env lean` has no such restriction and executes cleanly. This
file therefore lives in the task-scoped `probes/` directory (the same convention as
`five-s5-separation.lean` / `phase8-r1-reuse-soundness.lean`), not in `CslibTests/`.

The decision procedure's correctness is established by proof, not by this corpus:
`modalTableauS5_sound` (`FrameSoundness.lean`) and `modalTableauS5_complete` / `s5Valid_decides`
(`FrameCompleteness.lean`). Per the plan's risk R5, "the soundness+completeness theorems are the
proof; the corpus is the safety net" against a computational regression in the witness-reuse rule
`modalApplyOneS5w`.
-/

import Cslib.Logics.Modal.Tableau.FrameCompleteness

open Cslib.Logic.Modal.Tableau Cslib.Logic.Modal

/-- First test atom. -/
def p : Proposition Nat := .atom 0

/-- Second test atom. -/
def q : Proposition Nat := .atom 1

/-- `true` exactly when the S5 tableau closes on `φ` (reports `φ` S5-valid). -/
def s5Closes (φ : Proposition Nat) : Bool :=
  match modalTableauS5 φ with
  | .closed => true
  | .openBranch _ _ => false

-- S5 axiom schemata -- all valid, tableau must close.
#guard s5Closes (.imp (.box (.imp p q)) (.imp (.box p) (.box q)))  -- K
#guard s5Closes (.imp (.box p) p)                                   -- T
#guard s5Closes (.imp (.box p) (.box (.box p)))                     -- 4
#guard s5Closes (.imp (.diamond p) (.box (.diamond p)))             -- 5
#guard s5Closes (.imp p (.box (.diamond p)))                        -- B
#guard s5Closes (.imp p (.diamond p))                               -- dual T
#guard s5Closes (.imp (.box (.and p q)) (.and (.box p) (.box q)))   -- box/and
#guard s5Closes (.imp p (.imp q p))                                 -- weakening

-- Non-theorems -- all invalid, tableau must stay open.
#guard !s5Closes (.imp (.diamond p) p)              -- ◇p → p (S5's named falsifier)
#guard !s5Closes (.imp (.diamond p) (.box p))       -- ◇p → □p
#guard !s5Closes (.box p)                           -- □p
#guard !s5Closes (.imp p (.box p))                  -- p → □p
#guard !s5Closes (.diamond p)                       -- ◇p
#guard !s5Closes p                                  -- p
