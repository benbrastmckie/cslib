import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! Probe E for task 509: **CS5 proves `k3` (diamond distributes over disjunction).**

Arisaka–Das–Straßburger (LMCS 11(3:7) 2015) report that the `B` axioms entail `k3`
(`◇(A ∨ B) → ◇A ∨ ◇B`) and `k5` (`◇⊥ → ⊥`) — the very axioms `CK` drops. `k5` is task 508's
`cs5_dia_bot_imp_bot`. This probe mechanizes `k3`.

This matters because task 508 §4(c) rejected simultaneous Lindenbaum exclusion **on the ground
that `◇(A ∨ B) → ◇A ∨ ◇B` is underivable**. That is true in `CK`/`CT`/`CS4` but **false in
`CS5`**. So 508's §4(c) impossibility argument does not apply to `CS5` at all, and Pacheco's
`◇`-inverse canonical relation (`∆ ⊆ Γ^◇`) becomes viable in this setting.

Derivation: `bBox` on each disjunct, then `or_box_imp_box_or`, then `Kd` + `bDia`.
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

private def box_mono_or_l (B B' : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.box B).imp (Proposition.box (B.or B'))) :=
  .modus_ponens _ _ _ (.ax [] _ (.k B (B.or B')))
    (.necessitation _ (.ax [] _ (.orI1 B B')))

private def box_mono_or_r (B B' : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.box B').imp (Proposition.box (B.or B'))) :=
  .modus_ponens _ _ _ (.ax [] _ (.k B' (B.or B')))
    (.necessitation _ (.ax [] _ (.orI2 B B')))

/-- `⊢ (□B ∨ □B') → □(B ∨ B')` (pure CK; same as probe B's `or_box_imp_box_or`). -/
private def or_box_box_or (B B' : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      (((Proposition.box B).or (Proposition.box B')).imp (Proposition.box (B.or B'))) :=
  .modus_ponens _ _ _
    (.modus_ponens _ _ _ (.ax [] _ (.orE (Proposition.box B) (Proposition.box B')
      (Proposition.box (B.or B')))) (box_mono_or_l B B'))
    (box_mono_or_r B B')

/-- Chain two empty-context implications. -/
private noncomputable def impTrans {a b c : Proposition Atom}
    (h1 : DerivationTree (@CS5ModalAxiom Atom) [] (a.imp b))
    (h2 : DerivationTree (@CS5ModalAxiom Atom) [] (b.imp c)) :
    DerivationTree (@CS5ModalAxiom Atom) [] (a.imp c) :=
  deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) [] a c
    (.modus_ponens _ _ _ (.weakening [] [a] _ h2 (fun _ h => nomatch h))
      (.modus_ponens _ _ _ (.weakening [] [a] _ h1 (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))))

/-- **`CS5 ⊢ ◇(A ∨ B) → ◇A ∨ ◇B`** — the `k3` / `Cd` axiom that bare `CK` deliberately lacks.

Derivation:
1. `bBox` gives `⊢ A → □◇A` and `⊢ B → □◇B`; `orE` gives `⊢ (A ∨ B) → (□◇A ∨ □◇B)`.
2. `or_box_box_or` gives `⊢ (□◇A ∨ □◇B) → □(◇A ∨ ◇B)`; chain: `⊢ (A ∨ B) → □(◇A ∨ ◇B)`.
3. Necessitation + `Kd`: `⊢ ◇(A ∨ B) → ◇□(◇A ∨ ◇B)`.
4. `bDia` at `◇A ∨ ◇B`: `⊢ ◇□(◇A ∨ ◇B) → (◇A ∨ ◇B)`. Chain 3 and 4. -/
theorem cs5_dia_or (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) ((◇(A.or B)).imp ((◇A).or (◇B))) := by
  -- Step 1: (A ∨ B) → (□◇A ∨ □◇B)
  have hA : DerivationTree (@CS5ModalAxiom Atom) []
      (A.imp ((Proposition.box (◇A)).or (Proposition.box (◇B)))) :=
    impTrans (.ax [] _ (.bBox A)) (.ax [] _ (.orI1 (Proposition.box (◇A))
      (Proposition.box (◇B))))
  have hB : DerivationTree (@CS5ModalAxiom Atom) []
      (B.imp ((Proposition.box (◇A)).or (Proposition.box (◇B)))) :=
    impTrans (.ax [] _ (.bBox B)) (.ax [] _ (.orI2 (Proposition.box (◇A))
      (Proposition.box (◇B))))
  have h1 : DerivationTree (@CS5ModalAxiom Atom) []
      ((A.or B).imp ((Proposition.box (◇A)).or (Proposition.box (◇B)))) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _
      (.ax [] _ (.orE A B ((Proposition.box (◇A)).or (Proposition.box (◇B))))) hA) hB
  -- Step 2: (A ∨ B) → □(◇A ∨ ◇B)
  have h2 : DerivationTree (@CS5ModalAxiom Atom) []
      ((A.or B).imp (Proposition.box ((◇A).or (◇B)))) :=
    impTrans h1 (or_box_box_or (◇A) (◇B))
  -- Step 3: ◇(A ∨ B) → ◇□(◇A ∨ ◇B)
  have h3 : DerivationTree (@CS5ModalAxiom Atom) []
      ((◇(A.or B)).imp (◇(Proposition.box ((◇A).or (◇B))))) :=
    .modus_ponens _ _ _
      (.ax [] _ (.kdia (A.or B) (Proposition.box ((◇A).or (◇B)))))
      (.necessitation _ h2)
  -- Step 4: bDia
  exact ⟨impTrans h3 (.ax [] _ (.bDia ((◇A).or (◇B))))⟩

end Cslib.Logic.Modal

#print axioms Cslib.Logic.Modal.cs5_dia_or
