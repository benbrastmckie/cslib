import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Deduction
import Cslib.Logics.Modal.Metalogic.DerivationTree

/-! # Task 517 Phase 3 — Adequacy Gate Probe (dispatch 1 of 2)

**GATE VERDICT (this dispatch): FAIL.** Lemma 6.2.2's hard direction (`(R_χ)`-elimination) is
proved below, complete and sorry-free (`NIK_to_NIKAx`/`TClosure.hilbertTransport`). Lemma 6.1.2 /
6.2.3 (the tree internalization) is **not** completed -- see
`specs/517_labelled_bounded_context_cs5_completeness/handoffs/adequacy-gate-blocker-handoff.md`
for the full diagnosis. Per the plan's Phase 3 failure branch, this file lives in `probes/`
(outside `Cslib/`, never imported by it) rather than under `Cslib/Logics/...`; it is otherwise
identical to the working file built during this dispatch, and it is included here **sorry-free**
(no probe `sorry` was actually needed -- the reason for exclusion from `Cslib/` is that the
*whole* Phase 3 gate did not close, not that this file itself has any gap).

## The Phase-2 TClosure re-check (mandatory per this dispatch)

Phase 2 (`Deduction.lean`) encoded the geometric rules `{(R_χ) | χ ∈ 𝒯}` via a `TClosure` closure
operator on the graph relation, flagged because report 01 cited Simpson's Figure 4-3 (`:4940`)
only by location, not by transcribed rule shape. **This dispatch re-read Figure 4-3/4-4 directly
from the source PDF** (`Simpson_1994_IntuitionisticModalLogic.ocr.pdf`, pages 65 and 74): the
literal `(R_χ)` rule is a natural-deduction rule with a **locally discharged** relational
assumption (in the style of `(⊃I)`), *not* a permanent graph extension. **Verdict: `TClosure` is
NOT the literal Figure 4-3 rule shape, but it IS adequate** for Lemma 6.2.2's purposes --
precisely because `TClosure.hilbertTransport` below shows every `TClosure`-derived edge used by
`(□E)`/`(◇I)` can be *replaced* by a genuine Hilbert derivation using the corresponding Figure
3-7 axiom schema (p. 56 of the source PDF, read directly, page 65 in the PDF's own pagination)
plus modus ponens -- exactly the content Lemma 6.2.2 needs to prove. The literal discharge-style
`(R_χ)` rule would have proved the *same* theorem-set; `TClosure` merely front-loads the closure
into the graph instead of discharging it rule-by-rule, and this file's translation shows that
front-loading is harmless. **No correction to Phase 2 is required.**

## The Hilbert system `IK + Ax(𝒯)`

Rather than building a new Hilbert derivation-tree type, this reuses
`Cslib.Logic.Modal.DerivationTree`/`Deriv`/`Derivable` (`Metalogic/DerivationTree.lean`), already
parameterized over an arbitrary axiom predicate `Axioms : Proposition Atom → Prop`. The only new
ingredient is the axiom predicate itself, `IKAx 𝒯`, built from Figure 3-7's intuitionistic modal
axiom schemata (p. 56 of the source PDF, read directly via the `Read` tool, page 65): `D : ◇⊤`,
`T : (□A → A) ∧ (A → ◇A)`, `B : (◇□A → A) ∧ (A → □◇A)`, `4 : (□A → □□A) ∧ (◇◇A → ◇A)`,
`5 : (◇□A → □A) ∧ (◇A → □◇A)`. This exactly parallels `CS5ModalAxiom`'s `tBox`/`tDia`/`fourBox`/
`fourDia`/`bBox`/`bDia` pairs (`CS5.lean:182`), but fixes Simpson's own `𝒯_S5 := {χ_T, χ_5}`
axiomatization rather than CS5's `{χ_T, χ_4, χ_B}` one -- the two are Hilbert-equivalent
(`CS5 ≡ IS5`, Pacheco's Theorem 13) but *structurally different* axiom sets, and relating them was
always explicitly Phase 9's job (`C0`), not this gate's.

## Status

- **Lemma 6.2.2 (hard direction): COMPLETE, sorry-free, axiom-clean** (`#print axioms` reports
  only `propext`). `NIK_to_NIKAx` below.
- **Lemma 6.1.2 / 6.2.3 (tree internalization): NOT attempted to completion.** See the handoff
  document for the diagnosis (why it needs a reified tree/path structure this dispatch did not
  build, and why Simpson's own omission of `(⊥E)`/`(∨E)` (`:6544`) reflects genuine complexity,
  confirmed here by attempting the construction, not merely his presentational choice).

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  §3.3 (Figure 3-7, intuitionistic modal axioms, p.56), Chapter 4 (Figure 4-3/4-4, the geometric
  rules, pp. 73-74), and §6.2 (Lemma 6.2.2, Lemma 6.1.2, Theorem 6.2.1, pp. 154-165).
-/

namespace Cslib.Logic.Modal.Labelled

open Cslib.Logic.Modal (DerivationTree Deriv Derivable)

universe u

variable {Atom : Type u}

/-! ## The Hilbert system `IK + Ax(𝒯)` -/

/-- The axiom predicate for `IK + Ax(𝒯)`: the intuitionistic-K propositional/modal base
(`implyK`, `implyS`, `efq`, `andI/E1/E2`, `orI1/I2/E`, box-`K` and diamond-`K`) plus, for each
`χ ∈ 𝒯`, the corresponding Figure 3-7 schema/schema-pair. **No `peirce`/DNE**: `IK` is
intuitionistic, matching `CS5ModalAxiom`'s omission of classical axioms (`CS5.lean:182`). -/
inductive IKAx (𝒯 : Set GeomAxiom) : Proposition Atom → Prop where
  | implyK (φ ψ : Proposition Atom) : IKAx 𝒯 (φ.imp (ψ.imp φ))
  | implyS (φ ψ χ : Proposition Atom) :
      IKAx 𝒯 ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | efq (φ : Proposition Atom) : IKAx 𝒯 (Proposition.bot.imp φ)
  | andI (φ ψ : Proposition Atom) : IKAx 𝒯 (Cslib.Logic.Axioms.AndI φ ψ)
  | andE1 (φ ψ : Proposition Atom) : IKAx 𝒯 (Cslib.Logic.Axioms.AndE1 φ ψ)
  | andE2 (φ ψ : Proposition Atom) : IKAx 𝒯 (Cslib.Logic.Axioms.AndE2 φ ψ)
  | orI1 (φ ψ : Proposition Atom) : IKAx 𝒯 (Cslib.Logic.Axioms.OrI1 φ ψ)
  | orI2 (φ ψ : Proposition Atom) : IKAx 𝒯 (Cslib.Logic.Axioms.OrI2 φ ψ)
  | orE (φ ψ χ : Proposition Atom) : IKAx 𝒯 (Cslib.Logic.Axioms.OrE φ ψ χ)
  | kBox (φ ψ : Proposition Atom) :
      IKAx 𝒯 ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  | kDia (φ ψ : Proposition Atom) :
      IKAx 𝒯 ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  | dDia (h : GeomAxiom.D ∈ 𝒯) : IKAx 𝒯 (◇(Proposition.top))
  | tBox (h : GeomAxiom.T ∈ 𝒯) (φ : Proposition Atom) :
      IKAx 𝒯 ((Proposition.box φ).imp φ)
  | tDia (h : GeomAxiom.T ∈ 𝒯) (φ : Proposition Atom) :
      IKAx 𝒯 (φ.imp (◇φ))
  | bDia (h : GeomAxiom.B ∈ 𝒯) (φ : Proposition Atom) :
      IKAx 𝒯 ((◇(Proposition.box φ)).imp φ)
  | bBox (h : GeomAxiom.B ∈ 𝒯) (φ : Proposition Atom) :
      IKAx 𝒯 (φ.imp (Proposition.box (◇φ)))
  | fourBox (h : GeomAxiom.Four ∈ 𝒯) (φ : Proposition Atom) :
      IKAx 𝒯 ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  | fourDia (h : GeomAxiom.Four ∈ 𝒯) (φ : Proposition Atom) :
      IKAx 𝒯 ((◇◇φ).imp (◇φ))
  | fiveA (h : GeomAxiom.Five ∈ 𝒯) (φ : Proposition Atom) :
      IKAx 𝒯 ((◇(Proposition.box φ)).imp (Proposition.box φ))
  | fiveB (h : GeomAxiom.Five ∈ 𝒯) (φ : Proposition Atom) :
      IKAx 𝒯 ((◇φ).imp (Proposition.box (◇φ)))

/-- Shorthand for `Derivable` specialized to `IKAx 𝒯`, i.e. theoremhood in `IK + Ax(𝒯)`. -/
abbrev IKDerivable (𝒯 : Set GeomAxiom) (φ : Proposition Atom) : Prop :=
  Derivable (IKAx (Atom := Atom) 𝒯) φ

theorem IKDerivable.mp {𝒯 : Set GeomAxiom} {φ ψ : Proposition Atom}
    (h1 : IKDerivable 𝒯 (φ.imp ψ)) (h2 : IKDerivable 𝒯 φ) : IKDerivable 𝒯 ψ :=
  Cslib.Logic.Modal.mp_deriv h1 h2

/-- Lift an `IKAx 𝒯`-instance to a labelled fact `x ∶ φ`, available at *any* label with *no*
graph or context requirement. Used by `NIKAx.ax` below. -/
theorem IKAx.toIKDerivable {𝒯 : Set GeomAxiom} {φ : Proposition Atom} (h : IKAx 𝒯 φ) :
    IKDerivable 𝒯 φ :=
  ⟨.ax [] φ h⟩

/-! ## `N_IK` augmented with `Ax(𝒯)`-instances (the target of Lemma 6.2.2) -/

/-- The labelled deduction relation for the plain (non-geometrically-extended) system `N_IK`,
augmented with an unconditional axiom-injection rule making every `IKAx 𝒯`-instance available at
every label. This is Simpson's "`Ax(𝒯);Γ ⊢_G x:A`" (`:6989`) -- the target of Lemma 6.2.2's
`(R_χ)`-elimination. Its `(□E)`/`(◇I)` rules consume only **literal** edges of `G.R` (no
`TClosure`), matching the plain `N_IK` system (Figure 4-1) exactly; the geometric content of `𝒯`
is now carried entirely by the `ax` constructor rather than by graph closure. -/
inductive NIKAx (𝒯 : Set GeomAxiom) : Graph Atom → List (LabelledFormula Atom) →
    LabelledFormula Atom → Prop where
  | assumption (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (φ : LabelledFormula Atom)
      (h : φ ∈ Γ) : NIKAx 𝒯 G Γ φ
  | ax (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom) (φ : Proposition Atom)
      (h : IKAx 𝒯 φ) : NIKAx 𝒯 G Γ (x ∶ φ)
  | efq (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A : Proposition Atom) (h : NIKAx 𝒯 G Γ (x ∶ .bot)) : NIKAx 𝒯 G Γ (x ∶ A)
  | andI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (hA : NIKAx 𝒯 G Γ (x ∶ A)) (hB : NIKAx 𝒯 G Γ (x ∶ B)) :
      NIKAx 𝒯 G Γ (x ∶ .and A B)
  | andE1 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKAx 𝒯 G Γ (x ∶ .and A B)) : NIKAx 𝒯 G Γ (x ∶ A)
  | andE2 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKAx 𝒯 G Γ (x ∶ .and A B)) : NIKAx 𝒯 G Γ (x ∶ B)
  | orI1 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKAx 𝒯 G Γ (x ∶ A)) : NIKAx 𝒯 G Γ (x ∶ .or A B)
  | orI2 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKAx 𝒯 G Γ (x ∶ B)) : NIKAx 𝒯 G Γ (x ∶ .or A B)
  | orE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B C : Proposition Atom) (hor : NIKAx 𝒯 G Γ (x ∶ .or A B))
      (hA : NIKAx 𝒯 G ((x ∶ A) :: Γ) (x ∶ C)) (hB : NIKAx 𝒯 G ((x ∶ B) :: Γ) (x ∶ C)) :
      NIKAx 𝒯 G Γ (x ∶ C)
  | impI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIKAx 𝒯 G ((x ∶ A) :: Γ) (x ∶ B)) :
      NIKAx 𝒯 G Γ (x ∶ .imp A B)
  | impE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (himp : NIKAx 𝒯 G Γ (x ∶ .imp A B)) (hA : NIKAx 𝒯 G Γ (x ∶ A)) :
      NIKAx 𝒯 G Γ (x ∶ B)
  | boxE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
      (A : Proposition Atom) (hR : G.R x y) (h : NIKAx 𝒯 G Γ (x ∶ .box A)) :
      NIKAx 𝒯 G Γ (y ∶ A)
  | boxI (L : Set (Label Atom)) (hL : L.Finite) (G : Graph Atom)
      (Γ : List (LabelledFormula Atom)) (x : Label Atom) (A : Proposition Atom)
      (h : ∀ y ∉ L, NIKAx 𝒯 (G.addEdge x y) Γ (y ∶ A)) : NIKAx 𝒯 G Γ (x ∶ .box A)
  | diaI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
      (A : Proposition Atom) (hR : G.R x y) (h : NIKAx 𝒯 G Γ (y ∶ A)) :
      NIKAx 𝒯 G Γ (x ∶ .diamond A)
  | diaE (L : Set (Label Atom)) (hL : L.Finite) (G : Graph Atom)
      (Γ : List (LabelledFormula Atom)) (x z : Label Atom) (A B : Proposition Atom)
      (hdia : NIKAx 𝒯 G Γ (x ∶ .diamond A))
      (h : ∀ y ∉ L, NIKAx 𝒯 (G.addEdge x y) ((y ∶ A) :: Γ) (z ∶ B)) : NIKAx 𝒯 G Γ (z ∶ B)

/-! ## `TClosure`-elimination: Lemma 6.2.2's hard direction -/

/-- **The key Hilbert-transport lemma.** A `TClosure 𝒯 G.R x y` edge -- however it was built
(literal, or via reflexivity/symmetry/transitivity/Euclideanness closure) -- can always be
"crossed" using only `NIKAx`'s own resources: a box fact at the source transports to a plain fact
at the target (`.1`), and a plain fact at the target transports to a diamond fact at the source
(`.2`). This is exactly Lemma 6.2.2's content, proved by induction on the closure derivation and
using, at each closure step, the corresponding Figure 3-7 axiom schema plus modus ponens
(`NIKAx.impE`) -- never `TClosure` itself. -/
theorem TClosure.hilbertTransport {𝒯 : Set GeomAxiom} {G : Graph Atom}
    {Γ : List (LabelledFormula Atom)} {x y : Label Atom} (hR : TClosure 𝒯 G.R x y) :
    (∀ A : Proposition Atom, NIKAx 𝒯 G Γ (x ∶ .box A) → NIKAx 𝒯 G Γ (y ∶ A)) ∧
    (∀ A : Proposition Atom, NIKAx 𝒯 G Γ (y ∶ A) → NIKAx 𝒯 G Γ (x ∶ .diamond A)) := by
  induction hR with
  | @base x y h =>
    exact ⟨fun A hbox => .boxE G Γ x y A h hbox, fun A ha => .diaI G Γ x y A h ha⟩
  | @refl h x =>
    refine ⟨fun A hbox => ?_, fun A ha => ?_⟩
    · exact .impE G Γ x _ A (.ax G Γ x _ (.tBox h A)) hbox
    · exact .impE G Γ x A _ (.ax G Γ x _ (.tDia h A)) ha
  | @symm x y h _ ih =>
    refine ⟨fun A hbox => ?_, fun A ha => ?_⟩
    · have h1 : NIKAx 𝒯 G Γ (x ∶ .diamond (.box A)) := ih.2 (.box A) hbox
      exact .impE G Γ x _ A (.ax G Γ x _ (.bDia h A)) h1
    · have h1 : NIKAx 𝒯 G Γ (x ∶ .box (.diamond A)) :=
        .impE G Γ x A _ (.ax G Γ x _ (.bBox h A)) ha
      exact ih.1 (.diamond A) h1
  | @trans x y z h _ _ ihxy ihyz =>
    refine ⟨fun A hbox => ?_, fun A ha => ?_⟩
    · have h1 : NIKAx 𝒯 G Γ (x ∶ .box (.box A)) :=
        .impE G Γ x _ _ (.ax G Γ x _ (.fourBox h A)) hbox
      have h2 : NIKAx 𝒯 G Γ (y ∶ .box A) := ihxy.1 (.box A) h1
      exact ihyz.1 A h2
    · have h1 : NIKAx 𝒯 G Γ (y ∶ .diamond A) := ihyz.2 A ha
      have h2 : NIKAx 𝒯 G Γ (x ∶ .diamond (.diamond A)) := ihxy.2 (.diamond A) h1
      exact .impE G Γ x _ _ (.ax G Γ x _ (.fourDia h A)) h2
  | @eucl x y z h _ _ ihxy ihxz =>
    refine ⟨fun A hbox => ?_, fun A ha => ?_⟩
    · have h1 : NIKAx 𝒯 G Γ (x ∶ .diamond (.box A)) := ihxy.2 (.box A) hbox
      have h2 : NIKAx 𝒯 G Γ (x ∶ .box A) :=
        .impE G Γ x _ _ (.ax G Γ x _ (.fiveA h A)) h1
      exact ihxz.1 A h2
    · have h1 : NIKAx 𝒯 G Γ (x ∶ .diamond A) := ihxz.2 A ha
      have h2 : NIKAx 𝒯 G Γ (x ∶ .box (.diamond A)) :=
        .impE G Γ x _ _ (.ax G Γ x _ (.fiveB h A)) h1
      exact ihxy.1 (.diamond A) h2

/-- **Lemma 6.2.2, hard direction** (`:6989`): every `N_IK(𝒯)` derivation (using the geometric
rules `{(R_χ) | χ ∈ 𝒯}`, encoded via `TClosure`) translates to a derivation of the plain system
augmented with `Ax(𝒯)`-instances (`NIKAx`), by structural induction, eliminating each
`TClosure`-mediated `(□E)`/`(◇I)` step via `TClosure.hilbertTransport`. Every other rule maps
constructor-for-constructor (`NIKAx` was built with exactly the same shape). Complete,
sorry-free. -/
theorem NIK_to_NIKAx {𝒯 : Set GeomAxiom} {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : NIK 𝒯 G Γ φ) : NIKAx 𝒯 G Γ φ := by
  induction h with
  | assumption G Γ φ hmem => exact .assumption G Γ φ hmem
  | efq G Γ x A _ ih => exact .efq G Γ x A ih
  | andI G Γ x A B _ _ ihA ihB => exact .andI G Γ x A B ihA ihB
  | andE1 G Γ x A B _ ih => exact .andE1 G Γ x A B ih
  | andE2 G Γ x A B _ ih => exact .andE2 G Γ x A B ih
  | orI1 G Γ x A B _ ih => exact .orI1 G Γ x A B ih
  | orI2 G Γ x A B _ ih => exact .orI2 G Γ x A B ih
  | orE G Γ x A B C _ _ _ ihor ihA ihB => exact .orE G Γ x A B C ihor ihA ihB
  | impI G Γ x A B _ ih => exact .impI G Γ x A B ih
  | impE G Γ x A B _ _ ihimp ihA => exact .impE G Γ x A B ihimp ihA
  | boxE G Γ x y A hR _ ih => exact (TClosure.hilbertTransport hR).1 A ih
  | boxI L hL G Γ x A _ ih => exact .boxI L hL G Γ x A (fun y hy => ih y hy)
  | diaI G Γ x y A hR _ ih => exact (TClosure.hilbertTransport hR).2 A ih
  | diaE L hL G Γ x z A B _ _ ihdia ih =>
      exact .diaE L hL G Γ x z A B ihdia (fun y hy => ih y hy)

end Cslib.Logic.Modal.Labelled
