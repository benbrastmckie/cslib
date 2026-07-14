import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! Probe B for task 509: the canonical side of the symmetric-tail CS5 construction.

C4: `⊢ (□B₁ ∨ □B₂) → □(B₁ ∨ B₂)` (pure CK) — the "disjunction of boxes" identity that
    makes the `prime_set_exclusion` side conditions discharge for CS5.
C5: `⊢ ◇(□B₁ ∨ □B₂) → (B₁ ∨ B₂)` in CS5 — C4 + Kd + bDia. This is the n-ary shape needed
    to discharge `DerivExcludes` against `E := {□B | B ∉ H}`.
C6: `FCbdia` structurally FORCES canonical symmetry (`boxInv u.head ⊆ w.head`) for any
    segment-based world type — so the symmetric tail is not a choice, it is the only option.
C7: the box-backward gap: in a symmetric tail, `□(p ∨ □q) ∈ H` and `q ∉ H` force `p` into
    EVERY tail member of `H`. Purely structural (no CS5 axiom used).
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## C4/C5: the disjunction-of-boxes identity -/

/-- `⊢ □B → □(B ∨ B')` — necessitation + `Kb` on `orI1`/`orI2`. -/
private def box_mono_or_left (B B' : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.box B).imp (Proposition.box (B.or B'))) :=
  .modus_ponens _ _ _ (.ax [] _ (.k B (B.or B')))
    (.necessitation _ (.ax [] _ (.orI1 B B')))

/-- `⊢ □B' → □(B ∨ B')`. -/
private def box_mono_or_right (B B' : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.box B').imp (Proposition.box (B.or B'))) :=
  .modus_ponens _ _ _ (.ax [] _ (.k B' (B.or B')))
    (.necessitation _ (.ax [] _ (.orI2 B B')))

/-- **C4: `⊢ (□B ∨ □B') → □(B ∨ B')`.** The key identity: a *disjunction of boxes* implies
the *box of the disjunction*. Pure `CK` (necessitation + `Kb` + `orI`/`orE`); no `T`/`4`/`B`.
This is what lets an n-ary `DerivExcludes` side condition against the exclusion set
`E := {□B | B ∉ H}` be collapsed to the single formula `□(⋁Bᵢ)`, and is exactly the step
that task 508 §4(c) believed was unavailable (it rejected simultaneous exclusion because
`◇(A ∨ B) → ◇A ∨ ◇B` is underivable — true, but irrelevant: the exclusion set here is a set
of BOXES, not of diamonds, and boxes distribute the right way). -/
theorem or_box_imp_box_or (B B' : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      (((Proposition.box B).or (Proposition.box B')).imp (Proposition.box (B.or B'))) :=
  ⟨.modus_ponens _ _ _
    (.modus_ponens _ _ _ (.ax [] _ (.orE (Proposition.box B) (Proposition.box B')
      (Proposition.box (B.or B')))) (box_mono_or_left B B'))
    (box_mono_or_right B B')⟩

/-- **C5: `⊢ ◇(□B ∨ □B') → (B ∨ B')` in CS5.** Chain: `C4` under `◇` (necessitation + `Kd`),
then `bDia` at `B ∨ B'`. Together with primality of `H` this discharges the `DerivExcludes`
precondition of `prime_set_exclusion` against `E := {□B | B ∉ H}`: if `◇(⋁□Bᵢ) ∈ H` then
`⋁Bᵢ ∈ H`, so some `Bᵢ ∈ H` — contradicting `Bᵢ ∉ H`. -/
theorem dia_or_box_imp_or (B B' : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((◇((Proposition.box B).or (Proposition.box B'))).imp (B.or B')) := by
  obtain ⟨d4⟩ := or_box_imp_box_or B B'
  -- ◇(□B ∨ □B') → ◇□(B ∨ B')
  have hkd : DerivationTree (@CS5ModalAxiom Atom) []
      ((◇((Proposition.box B).or (Proposition.box B'))).imp
        (◇(Proposition.box (B.or B')))) :=
    .modus_ponens _ _ _
      (.ax [] _ (.kdia ((Proposition.box B).or (Proposition.box B'))
        (Proposition.box (B.or B'))))
      (.necessitation _ d4)
  -- ◇□(B ∨ B') → (B ∨ B')   [bDia]
  have hbd : DerivationTree (@CS5ModalAxiom Atom) []
      ((◇(Proposition.box (B.or B'))).imp (B.or B')) := .ax [] _ (.bDia (B.or B'))
  let X := ◇((Proposition.box B).or (Proposition.box B'))
  have hctx : DerivationTree (@CS5ModalAxiom Atom) [X] (B.or B') := by
    have a0 : DerivationTree (@CS5ModalAxiom Atom) [X] X :=
      .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
    exact .modus_ponens _ _ _ (.weakening [] [X] _ hbd (fun _ h => nomatch h))
      (.modus_ponens _ _ _ (.weakening [] [X] _ hkd (fun _ h => nomatch h)) a0)
  exact ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) []
    X (B.or B') hctx⟩

/-! ## C6: `FCbdia` structurally forces canonical symmetry -/

/-- **C6: any frame condition adequate for `bDia` forces the canonical tail to be symmetric.**
`FCbdia` (`r w u → ∃ u' ≥ u, ∃ t, r u' t ∧ t ≤ w`) is the *minimal* requirement for `bDia`
(`◇□A → A`): forcing `A` at `w` is only obtainable by persistence from some `t ≤ w`. On ANY
segment-based world type, `FCbdia` implies `boxInv u.head ⊆ w.head` whenever `r w u` — because
`box_reflect` gives `boxInv u'.head ⊆ t.head` and `t ≤ w` gives `t.head ⊆ w.head`.

So the symmetric tail is not one design among many: it is *forced*. Task 508 read this as an
obstruction; it is in fact a specification. -/
theorem fcbdia_forces_symmetry {Axioms : Proposition Atom → Prop}
    {w u : CKSegment Axioms} (hru : cmreach w u)
    (hfc : ∀ {w u : CKSegment Axioms}, cmreach w u →
      ∃ u', u ≤ u' ∧ ∃ t, cmreach u' t ∧ t ≤ w) :
    boxInv u.head ⊆ w.head := by
  obtain ⟨u', hle, t, hrt, htw⟩ := hfc hru
  intro B hB
  exact htw (u'.box_reflect B (hle hB) t.head hrt)

/-! ## C7: the box-backward gap -/

/-- **C7: the remaining gap, mechanized.** In the symmetric tail
`cs5Tail H = {t | QuasiPrime t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}`, if `□(p ∨ □q) ∈ H` and
`q ∉ H`, then EVERY tail member `T` of `H` contains `p`.

Consequence: for `H` prime with `□(p ∨ □q) ∈ H`, `□p ∉ H`, `q ∉ H`, the truth lemma's
box-backward case has NO witness at `H` — no `T` in `H`'s symmetric tail omits `p`. The
box-backward case must therefore move to a strictly larger head `H' ⊇ H` (here: one
containing `q`), which enlarges `boxInv H'` in turn. That circularity is the real open
problem: `H'` and `T` must be built as a simultaneous maximal pair, not sequentially.

Note this argument is purely structural — it uses only primality of `T` and the two tail
clauses, no CS5 axiom. It therefore applies to every symmetric-tail design, and by C6 the
tail must be symmetric. -/
theorem cs5_symmetric_tail_box_gap {H T : Set (Proposition Atom)}
    (hT : QuasiPrime (@CS5ModalAxiom Atom) T) {p q : Proposition Atom}
    (hbox : Proposition.box (p.or (Proposition.box q)) ∈ H)
    (hsub : boxInv H ⊆ T) (hsym : boxInv T ⊆ H) (hq : q ∉ H) : p ∈ T := by
  rcases hT.disj (hsub hbox) with h | h
  · exact h
  · exact absurd (hsym h) hq

end Cslib.Logic.Modal

#print axioms Cslib.Logic.Modal.or_box_imp_box_or
#print axioms Cslib.Logic.Modal.dia_or_box_imp_or
#print axioms Cslib.Logic.Modal.fcbdia_forces_symmetry
#print axioms Cslib.Logic.Modal.cs5_symmetric_tail_box_gap
