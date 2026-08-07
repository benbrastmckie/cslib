import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat

/-!
Scratch probe (task territory only): given a list `edges` of length `nw - 1` that is known to
CONTAIN `nw - 1` pairwise-distinct required pairs `(c, par c)` for `c ∈ [1, nw)`, show `edges`
contains NO other pairs -- i.e. every member of `edges` is one of the required pairs. This is
the counting/pigeonhole step needed to convert `IWorldHist`'s existence-only (H1) clause plus
`IWorldHistCounter`'s length fact into a full characterization of `edges`, which in turn should
let `isAccessible`'s DFS be shown equivalent to `parAncestor`.
-/

example (nw : Nat) (par : Nat → Nat) (edges : List (Nat × Nat))
    (hlen : edges.length = nw - 1)
    (hmem : ∀ c, 1 ≤ c → c < nw → (c, par c) ∈ edges) :
    ∀ p ∈ edges, ∃ c, 1 ≤ c ∧ c < nw ∧ p = (c, par c) := by
  classical
  set S : Finset (Nat × Nat) := (Finset.Ico 1 nw).image (fun c => (c, par c)) with hS
  have hSinj : Set.InjOn (fun c => (c, par c)) (Finset.Ico 1 nw) := by
    intro a _ b _ hab
    simpa using congrArg Prod.fst hab
  have hScard : S.card = nw - 1 := by
    rw [hS, Finset.card_image_of_injOn hSinj, Nat.card_Ico]
  have hSsub : S ⊆ edges.toFinset := by
    intro p hp
    simp only [hS, Finset.mem_image, Finset.mem_Ico] at hp
    obtain ⟨c, ⟨hc1, hc2⟩, hceq⟩ := hp
    rw [List.mem_toFinset, ← hceq]
    exact hmem c hc1 hc2
  have htoFinsetCard_le : edges.toFinset.card ≤ S.card := by
    calc edges.toFinset.card ≤ edges.length := List.toFinset_card_le (l := edges)
      _ = nw - 1 := hlen
      _ = S.card := hScard.symm
  have hSeq : S = edges.toFinset := Finset.eq_of_subset_of_card_le hSsub htoFinsetCard_le
  intro p hp
  have hpS : p ∈ S := by rw [hSeq]; exact List.mem_toFinset.mpr hp
  simp only [hS, Finset.mem_image, Finset.mem_Ico] at hpS
  obtain ⟨c, ⟨hc1, hc2⟩, hceq⟩ := hpS
  exact ⟨c, hc1, hc2, hceq.symm⟩
