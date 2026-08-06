import Cslib.Logics.Modal.Tableau.LoopChecking

/-!
# ARCHIVED (Boneyard)

This file archives two declarations excised from
`Cslib/Logics/Modal/Tableau/LoopChecking.lean`:

- `keysRootEmpty`
- `keysRootEmpty_entry`

Both are sorry-free and proven. `keysRootEmpty` states that every key recorded for world `0` is
empty; `keysRootEmpty_entry` establishes it at the driver's seed state `keys = [(0, ∅)]`. They
were archived as zero-consumer: outside `keysRootEmpty_entry` itself (which travels with it as
the pair's only code consumer), a word-boundary grep of `keysRootEmpty` over `Cslib/`,
`CslibTests/`, `scripts/`, and `Cslib.lean` returned zero code consumers at the time of
archival. See `../README.md` for the Boneyard convention and `README.md` in this directory
(including the travelled consumer-audit paragraphs) for why this pair was archived.

Do not import from live code.
-/

#exit

/-- **`keysRootEmpty`**: every key recorded for world `0` is empty. -/
def keysRootEmpty
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop :=
  ∀ k, (0, k) ∈ keys → k = ∅

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Entry establishment**: holds at the ordered driver's seed state `keys = [(0, ∅)]`. -/
lemma keysRootEmpty_entry :
    keysRootEmpty [(0, (∅ : Finset (Sign × Proposition Atom)))] := by
  intro k hk
  simp only [List.mem_singleton, Prod.mk.injEq] at hk
  exact hk.2
