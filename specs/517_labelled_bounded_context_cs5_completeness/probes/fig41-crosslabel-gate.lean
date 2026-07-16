import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context

/-! # Task 517 — DECISION GATE: is CSLib's label-local `(⊥E)`/`(∨E)` a defect?

**Raster fact (not in question).** Simpson1994 Figure 4-1, printed p. 69 (= PDF p. 78, offset
+9), read from the page raster, prints:

    x : ⊥                       [x:A]     [x:B]
    ----- (⊥E)                    ⋮         ⋮
    y : A            x : A ∨ B  y : C     y : C
                     ------------------------- (∨E)
                              y : C

Both are cross-label, and Figure 4-1 attaches **no** side condition to either (the only marked
restrictions are `*` on `(□I)` and `†` on `(◇E)`). CSLib transcribes both label-local
(`Deduction.lean:206` `efq`, `:225` `orE`).

**The question this file settles**: does that difference *cost* anything?

**VERDICT: it does not, for every use these rules have.** The three theorems below are
sorry-free. `efq_crossLabel_of_edge` shows the cross-label `(⊥E)` is a *derived rule* of the
label-local system whenever the two labels are joined by a 𝒯-closure edge — for **every** 𝒯,
needing no frame axiom at all. `dia_bot_elim_TS5` and `dia_or_dist_TS5` then derive Simpson's
two IK axioms that motivate cross-labelling in the first place — `k3 : ◇⊥ ⊃ ⊥` and
`k4 : ◇(A∨B) ⊃ ◇A ∨ ◇B` — inside the label-local system at the task's target theory `TS5`.

**Why the recovery works.** `(⊥E)` label-local yields `x : C` for *any* `C`, in particular
`x : □C`; `(□E)` then walks that `□` across any 𝒗-closure edge to `y : C`. The `∨` case runs
the same trick one level up, case-splitting to `y : □(◇A ∨ ◇B)` and walking it back. The
label-walking is done by the modal rules, which CSLib *did* transcribe cross-label
(`boxE`/`diaI` take independent `x y`; `diaE` takes independent `x z`).

**Where the edge comes from.** The cross-label instances are only ever *needed* under `(◇E)`,
which supplies the edge `xRy` itself (`G.addEdge x y`). The direction needed there is `y → x`,
delivered by `χ_B ∈ TS5`. So the edge hypothesis of `efq_crossLabel_of_edge` is discharged
exactly where it is needed.

**Scope of the negative part.** As a *rule schema* over disconnected labels the label-local
form is genuinely weaker: with `G.R = ∅` and `𝒯 = TS5`, `TClosure` adds only reflexive pairs,
so `x:⊥ ⊢ y:A` is underivable for `y ≠ x`. That instance is sound but never used: `(◇E)` is
the only rule that relates two labels without an antecedent edge, and it manufactures the edge.
-/

namespace Cslib.Logic.Modal.Labelled

universe u
variable {Atom : Type u}

/-! ## 1. The cross-label `(⊥E)` is a derived rule, for every `𝒯` -/

/-- **Cross-label `(⊥E)`, derived.** Simpson's Figure 4-1 `(⊥E)` (`x:⊥ / y:A`) is admissible in
the label-local system as soon as `x` and `y` are joined by a 𝒯-closure edge — for **any** `𝒯`,
using no frame axiom.

`efq` at `x` is instantiated at `□A` rather than at `A`, and `(□E)` carries it along the edge.
This is the whole content of the claimed "strict weakening": the label walk is performed by the
modal rules instead of being built into `(⊥E)`. -/
theorem efq_crossLabel_of_edge {𝒯 : Set GeomAxiom} {G : Graph Atom}
    {Γ : List (LabelledFormula Atom)} {x y : Label Atom} {A : Proposition Atom}
    (hR : TClosure 𝒯 G.R x y) (h : NIK 𝒯 G Γ (x ∶ .bot)) : NIK 𝒯 G Γ (y ∶ A) :=
  NIK.boxE G Γ x y A hR (NIK.efq G Γ x (.box A) h)

/-- The edge `(◇E)` manufactures, pointed back the way the `(⊥E)`/`(∨E)` recoveries need it.
`χ_B ∈ TS5` is what makes the return trip available. -/
theorem tclosure_addEdge_symm {G : Graph Atom} (x y : Label Atom) :
    TClosure TS5 (G.addEdge x y).R y x :=
  TClosure.symm GeomAxiom.B_mem_TS5 (TClosure.base (Or.inr ⟨rfl, rfl⟩))

/-! ## 2. Simpson's `k3 : ◇⊥ ⊃ ⊥`, label-local, at `TS5` -/

/-- **`k3`, derived label-locally.** `x:◇⊥ ⊢ x:⊥`. This is the axiom whose *only* natural
derivation in Simpson's system routes through cross-label `(⊥E)`: eliminate `◇` to reach
`y:⊥`, then jump to `x:⊥`. The label-local system reaches the same conclusion by
`efq_crossLabel_of_edge` along the `y → x` edge that `(◇E)` itself supplied. -/
theorem dia_bot_elim_TS5 {G : Graph Atom} {Γ : List (LabelledFormula Atom)} {x : Label Atom}
    (h : NIK TS5 G Γ (x ∶ .diamond .bot)) : NIK TS5 G Γ (x ∶ .bot) := by
  refine NIK.diaE ∅ Set.finite_empty G Γ x x .bot .bot h ?_
  intro y _
  exact efq_crossLabel_of_edge (tclosure_addEdge_symm x y)
    (NIK.assumption _ _ _ List.mem_cons_self)

/-! ## 3. Simpson's `k4 : ◇(A ∨ B) ⊃ ◇A ∨ ◇B`, label-local, at `TS5` -/

/-- **`k4`, derived label-locally.** `x:◇(A∨B) ⊢ x:◇A ∨ ◇B`. The cross-label `(∨E)` of
Figure 4-1 would case-split `y:A∨B` straight to the conclusion `x:◇A ∨ ◇B`. Label-locally we
case-split to `y : □(◇A ∨ ◇B)` instead — provable in each branch by `(□I)`, since from `y:A`
and the edge `y → w` (symmetrised to `w → y`) `(◇I)` gives `w:◇A` — and then walk the `□` back
to `x` along the `y → x` edge. -/
theorem dia_or_dist_TS5 {G : Graph Atom} {Γ : List (LabelledFormula Atom)} {x : Label Atom}
    {A B : Proposition Atom} (h : NIK TS5 G Γ (x ∶ .diamond (.or A B))) :
    NIK TS5 G Γ (x ∶ .or (.diamond A) (.diamond B)) := by
  refine NIK.diaE ∅ Set.finite_empty G Γ x x (.or A B)
    (.or (.diamond A) (.diamond B)) h ?_
  intro y _
  -- Goal: `G.addEdge x y, (y ∶ A ∨ B) :: Γ ⊢ x : ◇A ∨ ◇B`.
  -- Walk a boxed conclusion back from `y` to `x` along the edge `(◇E)` gave us.
  refine NIK.boxE _ _ y x _ (tclosure_addEdge_symm x y) ?_
  -- Goal: `... ⊢ y : □(◇A ∨ ◇B)`, by label-local `(∨E)` on `y : A ∨ B`.
  refine NIK.orE _ _ y A B (.box (.or (.diamond A) (.diamond B)))
    (NIK.assumption _ _ _ List.mem_cons_self) ?_ ?_
  · -- Branch `y : A`.
    refine NIK.boxI ∅ Set.finite_empty _ _ y _ ?_
    intro w _
    exact NIK.orI1 _ _ w _ _
      (NIK.diaI _ _ w y A (tclosure_addEdge_symm y w)
        (NIK.assumption _ _ _ List.mem_cons_self))
  · -- Branch `y : B`.
    refine NIK.boxI ∅ Set.finite_empty _ _ y _ ?_
    intro w _
    exact NIK.orI2 _ _ w _ _
      (NIK.diaI _ _ w y B (tclosure_addEdge_symm y w)
        (NIK.assumption _ _ _ List.mem_cons_self))

/-! ## 4. The repair, and its true blast radius

Sections 1-3 show the label-local system recovers every *edge-connected* cross-label instance.
It does **not** recover the *disconnected* ones, and Simpson's Lemma 5.3.1 (p. 93 raster) needs
exactly those: consistency is "immediate, because `Δ ⊬ x:A`" only if `Δ ⊢ z:⊥` collapses to the
fixed, unrelated target `x:A`; and the disjunction property is proved "by an application of
`(∨E)`" from `y:B∨C ∈ Δ` with conclusion `x:A`, for `y` ranging over `ℋ` and `x` fixed. No edge
joins them. So the repair is needed.

**But the repair is two constructor signatures wide.** `NIKX` below is `NIK` verbatim except
that `efq` and `orE` take an independent conclusion label, exactly as Figure 4-1 prints them.
`NIKX.weaken` is the *only* induction over the relation anywhere in the library (`NIK` occurs in
`Deduction.lean` and `Context.lean` and nowhere else; `CK`/`CT`/`CS4`/`CS5` never import
`Labelled`). It is reproduced below and goes through with the two cases' proofs unchanged modulo
threading one extra label. -/

/-- `N_IK(𝒯)` with `(⊥E)` and `(∨E)` transcribed cross-label, as Figure 4-1 prints them. Every
other constructor is character-for-character the mainline `NIK`. -/
inductive NIKX (𝒯 : Set GeomAxiom) : Graph Atom → List (LabelledFormula Atom) →
    LabelledFormula Atom → Prop where
  | assumption (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (φ : LabelledFormula Atom)
      (h : φ ∈ Γ) : NIKX 𝒯 G Γ φ
  /-- `(⊥E)` **cross-label**, per Figure 4-1: premise `x:⊥`, conclusion `y:A`, `y` independent. -/
  | efq (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
      (A : Proposition Atom) (h : NIKX 𝒯 G Γ (x ∶ .bot)) : NIKX 𝒯 G Γ (y ∶ A)
  | andI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (hA : NIKX 𝒯 G Γ (x ∶ A)) (hB : NIKX 𝒯 G Γ (x ∶ B)) :
      NIKX 𝒯 G Γ (x ∶ .and A B)
  | andE1 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKX 𝒯 G Γ (x ∶ .and A B)) : NIKX 𝒯 G Γ (x ∶ A)
  | andE2 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKX 𝒯 G Γ (x ∶ .and A B)) : NIKX 𝒯 G Γ (x ∶ B)
  | orI1 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKX 𝒯 G Γ (x ∶ A)) : NIKX 𝒯 G Γ (x ∶ .or A B)
  | orI2 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKX 𝒯 G Γ (x ∶ B)) : NIKX 𝒯 G Γ (x ∶ .or A B)
  /-- `(∨E)` **cross-label**, per Figure 4-1: major premise `x:A∨B`, minor premises and
  conclusion at an independent `y`, branch assumptions still discharged at `x`. -/
  | orE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
      (A B C : Proposition Atom) (hor : NIKX 𝒯 G Γ (x ∶ .or A B))
      (hA : NIKX 𝒯 G ((x ∶ A) :: Γ) (y ∶ C)) (hB : NIKX 𝒯 G ((x ∶ B) :: Γ) (y ∶ C)) :
      NIKX 𝒯 G Γ (y ∶ C)
  | impI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKX 𝒯 G ((x ∶ A) :: Γ) (x ∶ B)) :
      NIKX 𝒯 G Γ (x ∶ .imp A B)
  | impE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (himp : NIKX 𝒯 G Γ (x ∶ .imp A B)) (hA : NIKX 𝒯 G Γ (x ∶ A)) :
      NIKX 𝒯 G Γ (x ∶ B)
  | boxE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
      (A : Proposition Atom) (hR : TClosure 𝒯 G.R x y) (h : NIKX 𝒯 G Γ (x ∶ .box A)) :
      NIKX 𝒯 G Γ (y ∶ A)
  | boxI (L : Set (Label Atom)) (hL : L.Finite) (G : Graph Atom)
      (Γ : List (LabelledFormula Atom)) (x : Label Atom) (A : Proposition Atom)
      (h : ∀ y ∉ L, NIKX 𝒯 (G.addEdge x y) Γ (y ∶ A)) : NIKX 𝒯 G Γ (x ∶ .box A)
  | diaI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
      (A : Proposition Atom) (hR : TClosure 𝒯 G.R x y) (h : NIKX 𝒯 G Γ (y ∶ A)) :
      NIKX 𝒯 G Γ (x ∶ .diamond A)
  | diaE (L : Set (Label Atom)) (hL : L.Finite) (G : Graph Atom)
      (Γ : List (LabelledFormula Atom)) (x z : Label Atom) (A B : Proposition Atom)
      (hdia : NIKX 𝒯 G Γ (x ∶ .diamond A))
      (h : ∀ y ∉ L, NIKX 𝒯 (G.addEdge x y) ((y ∶ A) :: Γ) (z ∶ B)) : NIKX 𝒯 G Γ (z ∶ B)

/-- **The whole cost of the repair.** `NIK.weaken` (Prop. 4.4.1) is the only induction over the
derivation relation in the library. It survives the cross-label generalisation with the `efq`
and `orE` cases threading one extra label and their proof scripts otherwise untouched. -/
theorem NIKX.weaken {𝒯 : Set GeomAxiom} {G G' : Graph Atom} {Γ Δ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : NIKX 𝒯 G Γ φ) (hG : G ≤ G') (hΓ : ∀ ψ ∈ Γ, ψ ∈ Δ) :
    NIKX 𝒯 G' Δ φ := by
  induction h generalizing G' Δ with
  | assumption G Γ φ hmem => exact .assumption G' Δ φ (hΓ _ hmem)
  | efq G Γ x y A _ ih => exact .efq G' Δ x y A (ih hG hΓ)
  | andI G Γ x A B _ _ ihA ihB => exact .andI G' Δ x A B (ihA hG hΓ) (ihB hG hΓ)
  | andE1 G Γ x A B _ ih => exact .andE1 G' Δ x A B (ih hG hΓ)
  | andE2 G Γ x A B _ ih => exact .andE2 G' Δ x A B (ih hG hΓ)
  | orI1 G Γ x A B _ ih => exact .orI1 G' Δ x A B (ih hG hΓ)
  | orI2 G Γ x A B _ ih => exact .orI2 G' Δ x A B (ih hG hΓ)
  | orE G Γ x y A B C _ _ _ ihor ihA ihB =>
      refine .orE G' Δ x y A B C (ihor hG hΓ) (ihA hG ?_) (ihB hG ?_)
      · intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΓ _ hψ)
      · intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΓ _ hψ)
  | impI G Γ x A B _ ih =>
      refine .impI G' Δ x A B (ih hG ?_)
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hΓ _ hψ)
  | impE G Γ x A B _ _ ihimp ihA => exact .impE G' Δ x A B (ihimp hG hΓ) (ihA hG hΓ)
  | boxE G Γ x y A hR _ ih => exact .boxE G' Δ x y A (TClosure.mono hG.2 hR) (ih hG hΓ)
  | boxI L hL G Γ x A _ ih =>
      refine .boxI L hL G' Δ x A ?_
      intro y hy
      exact ih y hy (Graph.addEdge_mono hG x y) hΓ
  | diaI G Γ x y A hR _ ih => exact .diaI G' Δ x y A (TClosure.mono hG.2 hR) (ih hG hΓ)
  | diaE L hL G Γ x z A B _ _ ihdia ih =>
      refine .diaE L hL G' Δ x z A B (ihdia hG hΓ) ?_
      intro y hy
      refine ih y hy (Graph.addEdge_mono hG x y) ?_
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hΓ _ hψ)

/-! ### The repaired rules deliver Simpson's Lemma 5.3.1 steps verbatim -/

/-- Simpson p. 93, "Consistency is immediate, because `Δ ⊬^𝒯_ℋ x:A`": with the repaired
`(⊥E)` this is the one-liner Simpson's word "immediate" advertises. `z` and `x` are unrelated
and no edge joins them — which is why §1's `efq_crossLabel_of_edge` cannot supply this step. -/
theorem NIKX.consistency_step {𝒯 : Set GeomAxiom} {G : Graph Atom}
    {Γ : List (LabelledFormula Atom)} {z x : Label Atom} {A : Proposition Atom}
    (h : NIKX 𝒯 G Γ (z ∶ .bot)) : NIKX 𝒯 G Γ (x ∶ A) :=
  NIKX.efq G Γ z x A h

/-- Simpson p. 93, the disjunction-property step: from `y:B∨C ∈ Δ` and both branches deriving
the fixed target `x:A`, conclude `Δ ⊢ x:A` "by an application of `(∨E)`". Again `y` and `x` are
unrelated. -/
theorem NIKX.disjunction_step {𝒯 : Set GeomAxiom} {G : Graph Atom}
    {Γ : List (LabelledFormula Atom)} {y x : Label Atom} {B C A : Proposition Atom}
    (hor : NIKX 𝒯 G Γ (y ∶ .or B C)) (hB : NIKX 𝒯 G ((y ∶ B) :: Γ) (x ∶ A))
    (hC : NIKX 𝒯 G ((y ∶ C) :: Γ) (x ∶ A)) : NIKX 𝒯 G Γ (x ∶ A) :=
  NIKX.orE G Γ y x B C A hor hB hC

end Cslib.Logic.Modal.Labelled
