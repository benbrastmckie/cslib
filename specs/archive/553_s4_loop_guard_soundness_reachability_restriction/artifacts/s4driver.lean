import Cslib.Logics.Modal.Tableau.LoopChecking
open Cslib.Logic.Modal Cslib.Logic.Tableau Cslib.Logic.Modal.Tableau
abbrev P := Proposition Nat
def p0 : P := .atom 0
def p1 : P := .atom 1
def nt (x : P) : P := .imp x .bot
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))
def alphaL : P := .or (.box p0) (nt (.box p1))
def cex : P := .or (.box alphaA) (.box alphaL)

def isClosedRes : ModalTableauResult Nat → String
  | .closed => "CLOSED"
  | .openBranch _ _ => "OPEN"

-- the real keyed driver, with an explicit (small) fuel in place of modalFuelS4
#eval IO.println s!"modalExpandBranchesS4Keyed cex, fuel 400 = {isClosedRes (modalExpandBranchesS4Keyed cex [[(⟨.neg, cex, 0⟩ : SignedFormula P WorldIndex)]] [[]] [Accessibility.empty] [[((0:WorldIndex), (∅ : Finset (Sign × P)))]] 400)}"
-- the live-set (non-keyed) S4 driver for comparison
#eval IO.println s!"modalExpandBranchesS4 cex, fuel 400 = {isClosedRes (modalExpandBranchesS4 cex [[(⟨.neg, cex, 0⟩ : SignedFormula P WorldIndex)]] [[]] [Accessibility.empty] 400)}"
-- controls
#eval IO.println s!"B axiom keyed = {isClosedRes (modalExpandBranchesS4Keyed (.imp p0 (.box (.diamond p0))) [[(⟨.neg, (.imp p0 (.box (.diamond p0))), 0⟩ : SignedFormula P WorldIndex)]] [[]] [Accessibility.empty] [[((0:WorldIndex), (∅ : Finset (Sign × P)))]] 400)}"
#eval IO.println s!"T axiom keyed = {isClosedRes (modalExpandBranchesS4Keyed (.imp (.box p0) p0) [[(⟨.neg, (.imp (.box p0) p0), 0⟩ : SignedFormula P WorldIndex)]] [[]] [Accessibility.empty] [[((0:WorldIndex), (∅ : Finset (Sign × P)))]] 400)}"
