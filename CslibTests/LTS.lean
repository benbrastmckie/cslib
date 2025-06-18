import Cslib.Semantics.LTS.Basic
import Cslib.Semantics.LTS.Bisimulation
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity

-- A simple LTS on natural numbers

inductive NatTr : ℕ → ℕ → ℕ → Prop where
| one : NatTr 1 2 2
| one' : NatTr 1 1 1
| two : NatTr 2 1 1
| two' : NatTr 2 2 2

theorem NatTr.dom : NatTr n μ m → (n = 1 ∨ n = 2) ∧ (m = 1 ∨ m = 2) := by
  intro h
  cases h <;> simp

def natLts : LTS ℕ ℕ := ⟨NatTr⟩

inductive NatBisim : Rel ℕ ℕ where
| one_one : NatBisim 1 1
| one_two : NatBisim 1 2
| two_one : NatBisim 2 1
| two_two : NatBisim 2 2

example : 1 ~[natLts] 2 := by
  constructor
  exists NatBisim
  constructor
  . constructor
  . simp [Bisimulation]
    intro s1 s2 hr μ
    constructor
    . intro s1' htr
      cases htr <;> (cases hr <;> repeat constructor)
    . intro s2' htr
      cases htr <;> (cases hr <;> repeat constructor)
