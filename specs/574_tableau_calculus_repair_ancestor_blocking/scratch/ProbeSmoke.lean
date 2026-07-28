module

import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion

open Cslib.Logic.PL

def a : Proposition Nat := .atom 0
def b : Proposition Nat := .atom 1
def c : Proposition Nat := .atom 2
def d : Proposition Nat := .atom 3
def e : Proposition Nat := .atom 4
def f : Proposition Nat := .atom 5
def u1 : Proposition Nat := .atom 6
def v1 : Proposition Nat := .atom 7
def u2 : Proposition Nat := .atom 8
def v2 : Proposition Nat := .atom 9

def phi0 : Proposition Nat :=
  (((a → b) → c) ∧ ((d → e) → f)) → ((u1 → v1) ∨ (u2 → v2))

def worldStats : IntTableauResult Nat → String
  | .closed => "CLOSED"
  | .openBranch br =>
    let labels := br.map (·.label)
    let maxLabel := labels.foldl max 0
    let distinctLabels := labels.eraseDups.length
    s!"OPEN len={br.length} maxLabel={maxLabel} distinctLabels={distinctLabels}"

#eval worldStats (intExpandBranches [[(⟨.neg, phi0, 0⟩ : ISF Nat)]] [[]] [1] [[]] 60
  isIntuitionisticallyClosed)
