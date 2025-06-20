import Mathlib.Data.Rel

/-- The relation `r` 'up to' the relation `s`. -/
def Rel.upTo {α} (r s : Rel α α) : Rel α α := s.comp (r.comp s)

inductive Rel.Id {α} : Rel α α where
| id {x : α} : Rel.Id x x
