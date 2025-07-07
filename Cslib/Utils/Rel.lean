import Mathlib.Data.Rel

/-- Union of two relations. -/
def Rel.union {α β} (r s : Rel α β) : Rel α β :=
  fun x y => r x y ∨ s x y

/-- The relation `r` 'up to' the relation `s`. -/
def Rel.upTo {α} (r s : Rel α α) : Rel α α := s.comp (r.comp s)

/-- The identity relation. -/
inductive Rel.Id {α} : Rel α α where
| id {x : α} : Rel.Id x x
