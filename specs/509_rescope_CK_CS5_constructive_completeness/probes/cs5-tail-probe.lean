import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! Probe D for task 509: the symmetric tail delivers the canonical frame conditions.

Verifies, at the level of theories (the segment structure adds nothing to these arguments):
D1 reflexivity (from `tBox`), D2 symmetry (definitional), D3 transitivity (from `fourBox`,
used twice), D4 `Set.univ`-freeness (free — no appeal to `cs5_dia_bot_imp_bot`), D5 the
truth lemma's diamond-backward case (free, from `bBox`).
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Closure helpers -/

/-- `□B ∈ H → □□B ∈ H` — axiom `4` (box form). -/
theorem cs5_box_four {H : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    {B : Proposition Atom} (h : Proposition.box B ∈ H) :
    Proposition.box (Proposition.box B) ∈ H :=
  mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5ModalAxiom.fourBox B)) h

/-- `boxInv H ⊆ H` — axiom `T` (box form). -/
theorem cs5_boxInv_subset {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) : boxInv H ⊆ H :=
  fun B hB => mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5ModalAxiom.tBox B)) hB

/-! ## The symmetric tail -/

/-- **The CS5 symmetric tail.** The `boxInv t ⊆ H` clause is not a design choice: probe B's
`fcbdia_forces_symmetry` shows every `bDia`-adequate frame condition forces it. -/
def cs5Tail (H : Set (Proposition Atom)) : Set (Set (Proposition Atom)) :=
  {t | QuasiPrime (@CS5ModalAxiom Atom) t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}

/-- **D1 — reflexivity.** `H ∈ cs5Tail H`, from `tBox` on both clauses. -/
theorem cs5Tail_refl {H : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H) :
    H ∈ cs5Tail H :=
  ⟨hH, cs5_boxInv_subset hH, cs5_boxInv_subset hH⟩

/-- **D2 — symmetry, definitional.** The two tail clauses simply swap. No axiom, no
maximality, nothing derived — this is the step task 508 called "the known-hard core of
constructive S5 canonical completeness". -/
theorem cs5Tail_symm {H T : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    (h : T ∈ cs5Tail H) : H ∈ cs5Tail T :=
  ⟨hH, h.2.2, h.2.1⟩

/-- **D3 — transitivity.** Uses `cs5_box_four` on each side: forward,
`□B ∈ H → □□B ∈ H → □B ∈ U → B ∈ T`; backward, `□B ∈ T → □□B ∈ T → □B ∈ U → B ∈ H`. -/
theorem cs5Tail_trans {H U T : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) (hT : QuasiPrime (@CS5ModalAxiom Atom) T)
    (h1 : U ∈ cs5Tail H) (h2 : T ∈ cs5Tail U) : T ∈ cs5Tail H :=
  ⟨hT,
   fun _B hB => h2.2.1 (h1.2.1 (cs5_box_four hH hB)),
   fun _B hB => h1.2.2 (h2.2.2 (cs5_box_four hT hB))⟩

/-- **D4 — `Set.univ`-freeness is free.** `boxInv Set.univ = Set.univ`, so an exploding tail
member forces an exploding head. Hence for every consistent head the symmetric tail contains
no exploding member — with **no** appeal to `cs5_dia_bot_imp_bot`, which task 508 nominated as
"the one lead". This is what voids 508's canonical refutation of `FCbdia` (which took
`u := cexpl ∈ w.tail` for consistent `w`). -/
theorem cs5Tail_univ_free {H : Set (Proposition Atom)}
    (h : (Set.univ : Set (Proposition Atom)) ∈ cs5Tail H) : H = Set.univ :=
  Set.eq_univ_of_univ_subset (fun _B _ => h.2.2 (Set.mem_univ _))

/-- **D5 — the truth lemma's diamond-backward case is free.** If any member of `H`'s
symmetric tail contains `A`, then `◇A ∈ H` — by `bBox` (`A → □◇A`) and the `boxInv t ⊆ H`
clause. So `◇A ∉ H` refutes `◇A` at `H` *itself* (take `s' := s`).

Consequence: CS5 needs **no** exclusion parameter, no `cs5Tail` `E` argument, no
`dia_refuting_theory` and no `diamRefutingSegment` — all of which CS4 required. The tail is
determined by the head alone, which is exactly what makes D2 definitional. -/
theorem cs5Tail_dia_of_mem {H T : Set (Proposition Atom)}
    (hT : QuasiPrime (@CS5ModalAxiom Atom) T) (h : T ∈ cs5Tail H)
    {A : Proposition Atom} (hA : A ∈ T) : (◇A) ∈ H :=
  h.2.2 (mem_head_mp hT.closed (mem_of_axiom hT.closed (CS5ModalAxiom.bBox A)) hA)

/-! ## D6 — the tail condition IS Pacheco's, in box-inverse form -/

/-- **D6 — `boxInv T ⊆ H ↔ T ⊆ diaInv H`** for quasi-prime `H`, `T`.

Pacheco (arXiv:2408.16428v2, chunk `01990319adea2569`) defines the CKB canonical relation as
`Γ ∼c ∆ iff Γ□ ⊆ ∆ and ∆ ⊆ Γ♦` — a **diamond**-inverse containment on the right, where this
report's `cs5Tail` uses a **box**-inverse containment (`boxInv t ⊆ H`). This lemma shows the two
are **equivalent** over CS5: `→` is `bBox` (his Lemma 15, second half); `←` is `bDia` (his Lemma
15, first half). So `cs5Tail H = {t | QuasiPrime t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}` and Pacheco's
`∼c` are the *same relation*, and his Lemma 15 ("`∼c` is symmetric") is this report's
`cs5Tail_symm` with the equivalence inlined.

The presentations differ in what comes free: Pacheco derives symmetry (two `B` applications);
the box-inverse form makes it definitional but must pay `bBox` back at the diamond clause
(`cs5Tail_dia_of_mem`). Same content, different bookkeeping. -/
theorem cs5_boxInv_subset_iff {H T : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) (hT : QuasiPrime (@CS5ModalAxiom Atom) T) :
    boxInv T ⊆ H ↔ T ⊆ diaInv H := by
  constructor
  · intro h A hA
    exact h (mem_head_mp hT.closed (mem_of_axiom hT.closed (CS5ModalAxiom.bBox A)) hA)
  · intro h B hB
    exact mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5ModalAxiom.bDia B)) (h hB)

end Cslib.Logic.Modal

#print axioms Cslib.Logic.Modal.cs5_boxInv_subset_iff
#print axioms Cslib.Logic.Modal.cs5Tail_refl
#print axioms Cslib.Logic.Modal.cs5Tail_symm
#print axioms Cslib.Logic.Modal.cs5Tail_trans
#print axioms Cslib.Logic.Modal.cs5Tail_univ_free
#print axioms Cslib.Logic.Modal.cs5Tail_dia_of_mem
