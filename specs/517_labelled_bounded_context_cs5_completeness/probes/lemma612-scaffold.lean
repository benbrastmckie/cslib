import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Deduction
import Cslib.Logics.Modal.Metalogic.DerivationTree
import Cslib.Logics.Modal.Metalogic.DeductionTheorem

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
  /-- **Task 517 A1 repair.** Simpson's Figure 3-7 base-IK axiom 3, `¬◇⊥`
  (source PDF p.56): possibility never witnesses absurdity. Unconditional (part of bare `IK`,
  not gated by `𝒯` membership) -- unlike `dDia`/`tBox`/... below, which are the *geometric
  extension* schemata. CS5's analogue is `cs5_dia_bot_imp_bot` (`CS5.lean:740`), there *derived*
  from `efq`+`bDia`, not primitive; here it is primitive since plain `IKAx` (no `B` gate) has no
  `bDia` to derive it from. -/
  | diaBot : IKAx 𝒯 (¬(◇(Proposition.bot : Proposition Atom)))
  /-- **Task 517 A1 repair.** Simpson's Figure 3-7 base-IK axiom 4,
  `◇(A∨B) ⊃ (◇A∨◇B)` (source PDF p.56): possibility distributes over disjunction. Unconditional.
  CS5's analogue is `cs5_dia_or` (`CS5.lean:555`, Arisaka-Das-Straßburger's `k3`), there *derived*
  from `bBox`/`bDia`; here primitive for the same reason as `diaBot`. -/
  | diaOr (φ ψ : Proposition Atom) :
      IKAx 𝒯 ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- **Task 517 A1 repair.** Simpson's Figure 3-7 base-IK axiom 5, the Fischer-Servi
  confluence schema `FS := (◇A ⊃ □B) ⊃ □(A ⊃ B)` (source PDF p.56) -- the exact axiom task 517's
  report 02 identifies as the shared missing link for both this task and task 512 (Simpson's
  canonical-model confluence condition F2, p.53). Unconditional: `FS` is a base-`IK` requirement,
  present even with `𝒯 = ∅`, *not* implied by any of `D`/`T`/`B`/`4`/`5`(-Euclidean) individually
  since those are stated as independent box/diamond schema pairs rather than derived from a
  single shared accessibility relation. `CS5ModalAxiom` (`CS5.lean:182`) has **no** analogue of
  this axiom -- see `probes/fischer-servi-probe.lean` (this dispatch) for the syntactic-derivation
  attempt against `CS5ModalAxiom`'s `T`/`4`/`B`/`K`/`Kdia` alone (negative outcome, precisely
  documented) and the semantic validity result (`CS5.lean`, this dispatch, `cs5_axiom_sound''`
  companion) showing `FS` nonetheless holds in every `cs5FC''` *model*. -/
  | fs (φ ψ : Proposition Atom) :
      IKAx 𝒯 (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
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

/-! ## Dispatch 2: Scaffold for Lemma 6.1.2 / 6.2.3 (tree internalization)

**STATUS: INCOMPLETE, GATE FAIL (final).** This section is *not* a completed proof of
Lemma 6.1.2. It is a verified, sorry-free *scaffold* -- the reified finite-tree type, the
`Γ@U`/`Star` internalizing formula (corrected against the source PDF, see the note below), and
the general-purpose combinator toolkit (`box_mono1`/`box_mono2`/`wrapClosed`) needed by the
tractable cases of Lemma 6.1.2's induction. It is preserved here, sorry-free and axiom-clean, for
reuse by any future attempt. See `handoffs/lemma612-final-blocker.md` for the precise remaining
obstruction (the `(◇E)` rule's `z`-scoping gap, which blocks completion even though the
"combine" step this scaffold enables turned out to be far easier than dispatch 1 or the plan's
own paraphrase suggested).

### Corrected transcription (dispatch 2 finding)

Dispatch 1's blocker handoff (and the plan/report 01 before it) paraphrased Simpson's
internalizing formula with **◇** as the *outer* telescoping connective:
`(Γ⊢_G x:A)* = Γ@T⁰ ⊃ ◇(Γ@T¹ ⊃ ◇(...))`. **This is backwards relative to the source.** Reading
the source PDF directly (`Simpson_1994_IntuitionisticModalLogic.ocr.pdf`, PDF pages 109-112,
book pages 100-103, Chapter 6) shows unambiguously:

- `Γ@U = ⋀{B | y:B∈Γ} ∧ (◇Γ@U₁) ∧ ... ∧ (◇Γ@U_k)` — **◇** for a subtree's own children.
- `(Γ⊢_G x_m:A)* = Γ@T⁰ ⊃ □(Γ@T¹ ⊃ □(... Γ@T^{m-1} ⊃ □(Γ@T^m ⊃ A)...))` — **□** for the outer,
  ancestor-to-target telescoping.

Confirmed against Simpson's own worked example (book p.100/PDF p.109: for the tree `x→y, x→z→w`,
`(x:◇A⊃□□B, y:A ⊢_G z:◇B)* = ((◇A⊃□□B)∧◇A)⊃□(⊤⊃◇B)` — `y`'s contribution is `◇A` (children use
`◇`), the outer wrap uses `□`). **This correction matters enormously**: under the plan's
(incorrect) ◇-outer reading, the "combine" step needed for multi-premise rules
(`andI`/`impE`/`orE`) requires combining two *independently existentially-witnessed* `◇`-facts
into one, which is **not K-valid in general** (`◇P ∧ ◇Q → ◇(P∧Q)` is not a modal validity — a
frame can have two distinct successors, one witnessing `P` and a different one witnessing `Q`,
with neither witnessing both). Under the *correct* □-outer reading, the analogous combine step
is `□P ∧ □Q → □(P∧Q)`, which **is** K-valid (standard, via necessitation + the `kBox` axiom) —
this is exactly what makes the scaffold below work, and is the reason this dispatch is able to
report the `(∧I)`/`(⊃E)`/`(∨E)`/`(⊥E)` combine step as *tractable*, contrary to what a naive
reading of the plan's (mistranscribed) formula would suggest.
-/

section Lemma612Scaffold

open Cslib.Logic.Modal (deductionTheorem DerivationTree)

attribute [local instance] Classical.propDecidable

variable {Atom : Type u}

/-! ### The reified finite tree -/

/-- A finite, reified rose tree of labels, used to co-index `NIKAx` derivations for Lemma 6.1.2
(dispatch 1's diagnosis: `Graph Atom` alone carries no finiteness/acyclicity guarantee, so the
`Γ@U` recursion needs a dedicated tree type built alongside the derivation, not read off `Graph`
after the fact). -/
inductive LTree (Atom : Type u) : Type u where
  /-- A node with its label and (finitely many, ordered) children. -/
  | node (lbl : Label Atom) (children : List (LTree Atom)) : LTree Atom

namespace LTree

/-- The label at a tree's root. -/
def lbl : LTree Atom → Label Atom
  | node l _ => l

/-- The immediate children. -/
def childList : LTree Atom → List (LTree Atom)
  | node _ cs => cs

/-- The single-leaf tree at `x`. -/
def leaf (x : Label Atom) : LTree Atom := node x []

/-- All labels occurring anywhere in the tree. -/
def labels : LTree Atom → List (Label Atom)
  | node l cs => l :: (cs.flatMap labels)

/-- Append a new leaf child `y` at the (assumed-occurring, assumed-unique) node labelled `x`.
Dead code (returns `t` unchanged) if `x` does not occur -- callers thread `x ∈ t.labels` as a
side hypothesis, not enforced by this function's type. -/
noncomputable def addChild (t : LTree Atom) (x y : Label Atom) : LTree Atom :=
  match t with
  | node l cs =>
    if l = x then node l (cs ++ [leaf y])
    else node l (cs.map (fun c => c.addChild x y))

-- The path of subtrees from the root down to the (assumed-occurring) node labelled `x`:
-- `some [t₀,...,tₘ]` with `t₀` the whole tree and `tₘ` the subtree rooted at `x`, or `none` if
-- `x` does not occur. Written as an explicit tree/list mutual recursion (rather than via
-- `List.findSome?`) so Lean's structural recursion checker can see the nested-inductive
-- descent directly.
mutual

noncomputable def pathTo (t : LTree Atom) (x : Label Atom) : Option (List (LTree Atom)) :=
  match t with
  | node l cs => if l = x then some [t] else (pathToList cs x).map (t :: ·)

-- Search a list of sibling subtrees for the first whose `pathTo x` succeeds. Mutually
-- recursive with `pathTo`.
noncomputable def pathToList (cs : List (LTree Atom)) (x : Label Atom) :
    Option (List (LTree Atom)) :=
  match cs with
  | [] => none
  | c :: cs' =>
    match c.pathTo x with
    | some p => some p
    | none => pathToList cs' x

end

end LTree

/-! ### The internalizing formula `Γ@U` and the telescoped `Star` -/

/-- The conjunction of a list of propositions, `⊤` for the empty list (Simpson's convention,
`:6512`, "when empty, the above conjunction is taken to be `⊤`"). -/
def bigAnd : List (Proposition Atom) → Proposition Atom
  | [] => Proposition.top
  | [φ] => φ
  | φ :: rest => φ.and (bigAnd rest)

/-- Simpson's `Γ@U` (`:6512`): the internalizing formula for the subtree `U`, using **◇** for
each child (a subtree's own content is only *possible*, not *necessary*, from its parent's
point of view -- confirmed against the worked example, see the module-level correction note). -/
noncomputable def star (Γ : List (LabelledFormula Atom)) : LTree Atom → Proposition Atom
  | .node y cs => (bigAnd ((Γ.filter (·.lbl = y)).map (·.prop))).and
      (bigAnd (cs.map (fun c => Proposition.diamond (star Γ c))))

/-- Simpson's `(Γ⊢_G x_m:A)*` (`:6512`): the telescoped internalizing formula along a path
`[T⁰,...,Tᵐ]` from the root to the target label, using **□** for the outer (ancestor-to-target)
wrap (confirmed against the worked example; see the module-level correction note). -/
noncomputable def Star (Γ : List (LabelledFormula Atom)) : List (LTree Atom) → Proposition Atom →
    Proposition Atom
  | [], A => A
  | [t], A => (star Γ t).imp A
  | t :: t2 :: rest, A => (star Γ t).imp (Proposition.box (Star Γ (t2 :: rest) A))

/-! ### The combinator toolkit -/

/-- `⊃`-introduction for `IKAx 𝒯`, via CSLib's generic parameterized deduction theorem
(`Metalogic/DeductionTheorem.lean`), instantiated at `IKAx 𝒯`'s `implyK`/`implyS` constructors. -/
noncomputable def IK.impIntro {𝒯 : Set GeomAxiom} {Γ : List (Proposition Atom)}
    {φ ψ : Proposition Atom} (h : Deriv (IKAx (Atom := Atom) 𝒯) (φ :: Γ) ψ) :
    Deriv (IKAx 𝒯) Γ (φ.imp ψ) := by
  obtain ⟨d⟩ := h
  exact ⟨deductionTheorem (fun a b => IKAx.implyK a b) (fun a b c => IKAx.implyS a b c) Γ φ ψ d⟩

/-- **Box monotonicity** (single antecedent): if `⊢φ→ψ` (closed) then `⊢□φ→□ψ`, via
necessitation + the `kBox` axiom. Standard K-modal fact. -/
theorem box_mono1 {𝒯 : Set GeomAxiom} {φ ψ : Proposition Atom}
    (h : IKDerivable 𝒯 (φ.imp ψ)) :
    IKDerivable 𝒯 ((Proposition.box φ).imp (Proposition.box ψ)) := by
  obtain ⟨d⟩ := h
  have hnec : IKDerivable 𝒯 (Proposition.box (φ.imp ψ)) := ⟨.necessitation _ d⟩
  exact IKDerivable.mp ⟨.ax [] _ (IKAx.kBox φ ψ)⟩ hnec

/-- **Box monotonicity** (two antecedents): if `⊢φ→(ψ→χ)` (closed) then
`⊢□φ→(□ψ→□χ)`. Derived from `box_mono1` plus one more application of `kBox`, discharged via
the deduction theorem. -/
theorem box_mono2 {𝒯 : Set GeomAxiom} {φ ψ χ : Proposition Atom}
    (h : IKDerivable 𝒯 (φ.imp (ψ.imp χ))) :
    IKDerivable 𝒯 ((Proposition.box φ).imp ((Proposition.box ψ).imp (Proposition.box χ))) := by
  have h1 : IKDerivable 𝒯 ((Proposition.box φ).imp (Proposition.box (ψ.imp χ))) := box_mono1 h
  have hk : IKDerivable 𝒯
      ((Proposition.box (ψ.imp χ)).imp ((Proposition.box ψ).imp (Proposition.box χ))) :=
    ⟨.ax [] _ (IKAx.kBox ψ χ)⟩
  set Γ2 : List (Proposition Atom) := [Proposition.box ψ, Proposition.box φ] with hΓ2
  have ha1 : Deriv (IKAx 𝒯) Γ2 (Proposition.box φ) := assumption_deriv (by simp [hΓ2])
  have ha2 : Deriv (IKAx 𝒯) Γ2 (Proposition.box ψ) := assumption_deriv (by simp [hΓ2])
  have hw1 : Deriv (IKAx 𝒯) Γ2 ((Proposition.box φ).imp (Proposition.box (ψ.imp χ))) :=
    weakening_deriv h1 (by simp [hΓ2])
  have hw2 : Deriv (IKAx 𝒯) Γ2
      ((Proposition.box (ψ.imp χ)).imp ((Proposition.box ψ).imp (Proposition.box χ))) :=
    weakening_deriv hk (by simp [hΓ2])
  have hstep1 : Deriv (IKAx 𝒯) Γ2 (Proposition.box (ψ.imp χ)) := mp_deriv hw1 ha1
  have hstep2 : Deriv (IKAx 𝒯) Γ2 ((Proposition.box ψ).imp (Proposition.box χ)) :=
    mp_deriv hw2 hstep1
  have hstep3 : Deriv (IKAx 𝒯) Γ2 (Proposition.box χ) := mp_deriv hstep2 ha2
  have hd1 := IK.impIntro (Γ := [Proposition.box φ]) (φ := Proposition.box ψ) hstep3
  have hd2 := IK.impIntro (Γ := []) (φ := Proposition.box φ) hd1
  exact hd2

/-- **Wrap a closed theorem in an arbitrary `Star` prefix.** If `⊢X` (closed) then, for *any*
`Γ` and path, `⊢Star Γ path X`. Proved by induction on the path via `implyK` (base) and
necessitation (step). -/
theorem wrapClosed {𝒯 : Set GeomAxiom} {Γ : List (LabelledFormula Atom)}
    (path : List (LTree Atom)) {X : Proposition Atom} (h : IKDerivable 𝒯 X) :
    IKDerivable 𝒯 (Star Γ path X) := by
  induction path with
  | nil => simpa [Star] using h
  | cons t rest ih =>
    cases rest with
    | nil =>
      simp only [Star]
      exact IKDerivable.mp ⟨.ax [] _ (IKAx.implyK X (star Γ t))⟩ h
    | cons t2 rest' =>
      have hbox : IKDerivable 𝒯 (Proposition.box (Star Γ (t2 :: rest') X)) := by
        obtain ⟨d⟩ := ih
        exact ⟨.necessitation _ d⟩
      simp only [Star]
      exact IKDerivable.mp
        ⟨.ax [] _ (IKAx.implyK (Proposition.box (Star Γ (t2 :: rest') X)) (star Γ t))⟩ hbox

/-- **Single-hypothesis `Star` monotonicity**: if `⊢A→B` (closed) then
`⊢(Star Γ path A) → (Star Γ path B)`. Proved by induction on the path using `box_mono1` at each
level and the deduction theorem to discharge the peeled-off antecedents. -/
theorem Star_imp1 {𝒯 : Set GeomAxiom} {Γ : List (LabelledFormula Atom)}
    (path : List (LTree Atom)) {A B : Proposition Atom} (h : IKDerivable 𝒯 (A.imp B)) :
    IKDerivable 𝒯 ((Star Γ path A).imp (Star Γ path B)) := by
  induction path with
  | nil => simpa [Star] using h
  | cons t rest ih =>
    cases rest with
    | nil =>
      simp only [Star]
      set Γ1 : List (Proposition Atom) := [(star Γ t).imp A] with hΓ1
      have hant : Deriv (IKAx 𝒯) Γ1 ((star Γ t).imp A) := assumption_deriv (by simp [hΓ1])
      have hp : Deriv (IKAx 𝒯) (star Γ t :: Γ1) (star Γ t) :=
        assumption_deriv (by simp)
      have hantw : Deriv (IKAx 𝒯) (star Γ t :: Γ1) ((star Γ t).imp A) :=
        weakening_deriv hant (fun z hz => List.mem_cons_of_mem _ hz)
      have hA : Deriv (IKAx 𝒯) (star Γ t :: Γ1) A := mp_deriv hantw hp
      have hAB : Deriv (IKAx 𝒯) (star Γ t :: Γ1) (A.imp B) := by
        obtain ⟨d⟩ := h
        exact ⟨.weakening [] _ _ d (by simp)⟩
      have hB : Deriv (IKAx 𝒯) (star Γ t :: Γ1) B := mp_deriv hAB hA
      have hd1 := IK.impIntro (Γ := Γ1) (φ := star Γ t) hB
      have hd2 := IK.impIntro (Γ := []) (φ := (star Γ t).imp A) hd1
      exact hd2
    | cons t2 rest' =>
      have hinner : IKDerivable 𝒯 ((Star Γ (t2 :: rest') A).imp (Star Γ (t2 :: rest') B)) := ih
      have hbox : IKDerivable 𝒯 ((Proposition.box (Star Γ (t2 :: rest') A)).imp
          (Proposition.box (Star Γ (t2 :: rest') B))) := box_mono1 hinner
      simp only [Star]
      set Γ1 : List (Proposition Atom) :=
        [(star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))] with hΓ1
      have hant : Deriv (IKAx 𝒯) Γ1
          ((star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))) :=
        assumption_deriv (by simp [hΓ1])
      have hp : Deriv (IKAx 𝒯) (star Γ t :: Γ1) (star Γ t) := assumption_deriv (by simp)
      have hantw : Deriv (IKAx 𝒯) (star Γ t :: Γ1)
          ((star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))) :=
        weakening_deriv hant (fun z hz => List.mem_cons_of_mem _ hz)
      have hboxA : Deriv (IKAx 𝒯) (star Γ t :: Γ1)
          (Proposition.box (Star Γ (t2 :: rest') A)) := mp_deriv hantw hp
      have hboxw : Deriv (IKAx 𝒯) (star Γ t :: Γ1)
          ((Proposition.box (Star Γ (t2 :: rest') A)).imp
            (Proposition.box (Star Γ (t2 :: rest') B))) := by
        obtain ⟨d⟩ := hbox
        exact ⟨.weakening [] _ _ d (by simp)⟩
      have hboxB : Deriv (IKAx 𝒯) (star Γ t :: Γ1)
          (Proposition.box (Star Γ (t2 :: rest') B)) := mp_deriv hboxw hboxA
      have hd1 := IK.impIntro (Γ := Γ1) (φ := star Γ t) hboxB
      have hd2 := IK.impIntro (Γ := []) (φ := (star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))) hd1
      exact hd2

/-- **Two-hypothesis `Star` combination**: if `⊢A→(B→C)` (closed) then
`⊢(Star Γ path A) → ((Star Γ path B) → (Star Γ path C))`. This is the "combine" step needed for
`(∧I)`/`(⊃E)`/`(∨E)`-shaped multi-premise rules (all label-local in `NIKAx`, sharing the same
`(Γ,path)` prefix). Tractable *only* because the outer telescope is `□` (see the corrected
transcription note): the analogous fact with `◇` as the outer connective would need to combine
two independently-witnessed possibilities, which is not K-valid. Proved by induction on the
path using `box_mono2` at each level. -/
theorem Star_imp2 {𝒯 : Set GeomAxiom} {Γ : List (LabelledFormula Atom)}
    (path : List (LTree Atom)) {A B C : Proposition Atom}
    (h : IKDerivable 𝒯 (A.imp (B.imp C))) :
    IKDerivable 𝒯 ((Star Γ path A).imp ((Star Γ path B).imp (Star Γ path C))) := by
  induction path with
  | nil => simpa [Star] using h
  | cons t rest ih =>
    cases rest with
    | nil =>
      simp only [Star]
      set Γ3 : List (Proposition Atom) :=
        [star Γ t, (star Γ t).imp B, (star Γ t).imp A] with hΓ3
      have hp : Deriv (IKAx 𝒯) Γ3 (star Γ t) := assumption_deriv (by simp [hΓ3])
      have hbimp : Deriv (IKAx 𝒯) Γ3 ((star Γ t).imp B) := assumption_deriv (by simp [hΓ3])
      have haimp : Deriv (IKAx 𝒯) Γ3 ((star Γ t).imp A) := assumption_deriv (by simp [hΓ3])
      have hA : Deriv (IKAx 𝒯) Γ3 A := mp_deriv haimp hp
      have hB : Deriv (IKAx 𝒯) Γ3 B := mp_deriv hbimp hp
      have hABC : Deriv (IKAx 𝒯) Γ3 (A.imp (B.imp C)) := by
        obtain ⟨d⟩ := h; exact ⟨.weakening [] _ _ d (by simp)⟩
      have hC : Deriv (IKAx 𝒯) Γ3 C := mp_deriv (mp_deriv hABC hA) hB
      have hd1 := IK.impIntro (Γ := [(star Γ t).imp B, (star Γ t).imp A]) (φ := star Γ t) hC
      have hd2 := IK.impIntro (Γ := [(star Γ t).imp A]) (φ := (star Γ t).imp B) hd1
      have hd3 := IK.impIntro (Γ := []) (φ := (star Γ t).imp A) hd2
      exact hd3
    | cons t2 rest' =>
      have hinner : IKDerivable 𝒯
          ((Star Γ (t2 :: rest') A).imp
            ((Star Γ (t2 :: rest') B).imp (Star Γ (t2 :: rest') C))) := ih
      have hbox : IKDerivable 𝒯 ((Proposition.box (Star Γ (t2 :: rest') A)).imp
          ((Proposition.box (Star Γ (t2 :: rest') B)).imp
            (Proposition.box (Star Γ (t2 :: rest') C)))) := box_mono2 hinner
      simp only [Star]
      set Γ3 : List (Proposition Atom) :=
        [star Γ t, (star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') B)),
          (star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))] with hΓ3
      have hp : Deriv (IKAx 𝒯) Γ3 (star Γ t) := assumption_deriv (by simp [hΓ3])
      have hbimp : Deriv (IKAx 𝒯) Γ3
          ((star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') B))) :=
        assumption_deriv (by simp [hΓ3])
      have haimp : Deriv (IKAx 𝒯) Γ3
          ((star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))) :=
        assumption_deriv (by simp [hΓ3])
      have hboxA : Deriv (IKAx 𝒯) Γ3 (Proposition.box (Star Γ (t2 :: rest') A)) :=
        mp_deriv haimp hp
      have hboxB : Deriv (IKAx 𝒯) Γ3 (Proposition.box (Star Γ (t2 :: rest') B)) :=
        mp_deriv hbimp hp
      have hABC : Deriv (IKAx 𝒯) Γ3
          ((Proposition.box (Star Γ (t2 :: rest') A)).imp
            ((Proposition.box (Star Γ (t2 :: rest') B)).imp
              (Proposition.box (Star Γ (t2 :: rest') C)))) := by
        obtain ⟨d⟩ := hbox; exact ⟨.weakening [] _ _ d (by simp)⟩
      have hboxC : Deriv (IKAx 𝒯) Γ3 (Proposition.box (Star Γ (t2 :: rest') C)) :=
        mp_deriv (mp_deriv hABC hboxA) hboxB
      have hd1 := IK.impIntro
        (Γ := [(star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') B)),
              (star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))])
        (φ := star Γ t) hboxC
      have hd2 := IK.impIntro
        (Γ := [(star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))])
        (φ := (star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') B))) hd1
      have hd3 := IK.impIntro (Γ := [])
        (φ := (star Γ t).imp (Proposition.box (Star Γ (t2 :: rest') A))) hd2
      exact hd3

/-- **Path-append unfolding**: appending one more (leaf-ward) tree `t` to a nonempty path
telescopes `Star` by exactly one `□`-wrapped level. This is what boxI/diaI/boxE/diaE need to
relate `Star` for the *extended* tree/target to `Star` for the ambient one: extending the tree
by one child always adds exactly one more `□`-hop at the *end* of the path (never touching the
ancestor prefix). Requires the path to be nonempty (always true in practice: `pathTo` never
returns the empty list). -/
theorem Star_append {Γ : List (LabelledFormula Atom)} (path : List (LTree Atom))
    (hpath : path ≠ []) (t : LTree Atom) (A : Proposition Atom) :
    Star Γ (path ++ [t]) A = Star Γ path (Proposition.box ((star Γ t).imp A)) := by
  induction path with
  | nil => exact absurd rfl hpath
  | cons p prest ih =>
    cases prest with
    | nil => simp [Star]
    | cons p2 prest' =>
      have hne : (p2 :: prest' : List (LTree Atom)) ≠ [] := by simp
      have hrec := ih hne
      rw [List.cons_append] at hrec
      show Star Γ (p :: (p2 :: prest' ++ [t])) A =
          Star Γ (p :: p2 :: prest') (Proposition.box ((star Γ t).imp A))
      rw [List.cons_append]
      simp only [Star, hrec]

end Lemma612Scaffold

end Cslib.Logic.Modal.Labelled
