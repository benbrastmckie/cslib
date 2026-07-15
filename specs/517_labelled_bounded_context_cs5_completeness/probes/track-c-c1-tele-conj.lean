import Cslib.Init
import Cslib.Logics.Modal.Metalogic.DerivationTree
import Cslib.Logics.Modal.Metalogic.DeductionTheorem

/-! # Task 517 Track C — C1: `Tele`/`Conj` over `List (Proposition Atom)`

**Executed only because A3 (this dispatch) returned NO-GO for Track B** — see
`specs/517_labelled_bounded_context_cs5_completeness/plans/02_decomposed-track-a-b-c.md`'s A3
entry for the full GO/NO-GO analysis and named blocking obligation.

This is the C1 part of the plan's Track C fallback (Simpson tree surgery, decomposed): define
`Tele`/`Conj` over `List (Proposition Atom)` (source PDF p.104, transcribed in report 02 §2.5),
and port `Star_imp1`/`Star_imp2` (`probes/lemma612-scaffold.lean:450`/`:507`) to
`Tele`-congruence. Per the plan, C1 has **ZERO tree dependency** — `Tele`/`Conj` operate directly
on `List (Proposition Atom)`, with none of `LTree`/`LabelledFormula`/`star`/`GeomAxiom`'s
label/tree machinery from the scaffold. That is why this file is self-contained (no import of
`lemma612-scaffold.lean`) rather than extending it: `Tele_imp1`/`Tele_imp2` are additionally
generalized to be parametric over an arbitrary axiom predicate `Axioms : Proposition Atom → Prop`
carrying `implyK`/`implyS`/`kBox`-shaped hypotheses (exactly CSLib's established idiom, e.g.
`Metalogic/DeductionTheorem.lean:65-68`'s `deductionTheorem` signature), so they are directly
reusable against `IKAx 𝒯` (`lemma612-scaffold.lean:78`) in a future C2/C3 dispatch *and* against
`CS5ModalAxiom` (`CS5.lean:182`) without redeclaration — a strict generalization of the scaffold's
`IK.impIntro`/`box_mono1`/`box_mono2`/`Star_imp1`/`Star_imp2`, not a re-transcription tied to one
axiom system.

## Definitions (source PDF p.104, report 02 §2.5)

`Tele([p₁,…,pₙ], C) := p₁ ⊃ □(p₂ ⊃ □(… ⊃ □(pₙ ⊃ C)))` (no `□` after the last) and
`Conj([p₁,…,pₙ]) := p₁ ∧ ◇(p₂ ∧ ◇(… ∧ ◇pₙ))`. Both mirror the scaffold's `Star`/`star`
recursion shape exactly (`Star Γ [t] A = (star Γ t).imp A`, `Star Γ (t::t2::rest) A =
(star Γ t).imp (□(Star Γ (t2::rest) A))`), with `star Γ t` replaced directly by a
`Proposition Atom` list element — `Tele`/`Conj` need no `Γ`/tree-evaluation indirection since
their list elements already *are* propositions. `Conj`'s empty-list case (`⊤`) and singleton
case (no dangling `◇`) follow the same convention as the scaffold's `bigAnd`
(`lemma612-scaffold.lean:386`, "Simpson's convention, `:6512`, 'when empty, the above conjunction
is taken to be `⊤`'").

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 6, Figure 6-2 (p.103) and formulas (6.7)/(6.8) (p.104).
-/

namespace Cslib.Logic.Modal.TeleConj

open Cslib.Logic.Modal (DerivationTree Deriv Derivable mp_deriv weakening_deriv assumption_deriv
  deductionTheorem)

universe u

variable {Atom : Type u}

/-! ## `Conj` and `Tele` -/

/-- `Conj([p₁,…,pₙ]) := p₁ ∧ ◇(p₂ ∧ ◇(… ∧ ◇pₙ))` (source PDF p.104, report 02 §2.5). `⊤` for the
empty list, no dangling `◇` after the last element — same convention as `bigAnd`
(`lemma612-scaffold.lean:386`). -/
def Conj : List (Proposition Atom) → Proposition Atom
  | [] => Proposition.top
  | [p] => p
  | p :: rest => p.and (◇(Conj rest))

/-- `Tele([p₁,…,pₙ], C) := p₁ ⊃ □(p₂ ⊃ □(… ⊃ □(pₙ ⊃ C)))` (source PDF p.104, report 02 §2.5),
no `□` after the last antecedent. Structurally identical to the scaffold's `Star`
(`lemma612-scaffold.lean:401`) with `star Γ t` replaced by a bare `Proposition Atom`. -/
def Tele : List (Proposition Atom) → Proposition Atom → Proposition Atom
  | [], C => C
  | [p], C => p.imp C
  | p :: p2 :: rest, C => p.imp (Proposition.box (Tele (p2 :: rest) C))

/-! ## The combinator toolkit, generalized over `Axioms`

Ported from the scaffold's `IK.impIntro`/`box_mono1`/`box_mono2`
(`lemma612-scaffold.lean:385/393/403`), which were hard-wired to `IKAx 𝒯`. Here they are
parametric over any `Axioms : Proposition Atom → Prop` carrying the three hypotheses every one
of those three lemmas actually uses: `implyK`, `implyS` (both needed by CSLib's
`deductionTheorem`), and `kBox` (needed by `box_mono1`/`box_mono2`'s necessitation step). -/

variable {Axioms : Proposition Atom → Prop}

/-- `⊃`-introduction, generalized from `IK.impIntro`
(`lemma612-scaffold.lean:385`). -/
noncomputable def impIntro
    (hK : ∀ φ ψ : Proposition Atom, Axioms (φ.imp (ψ.imp φ)))
    (hS : ∀ φ ψ χ : Proposition Atom,
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (h : Deriv Axioms (φ :: Γ) ψ) : Deriv Axioms Γ (φ.imp ψ) := by
  obtain ⟨d⟩ := h
  exact ⟨deductionTheorem hK hS Γ φ ψ d⟩

/-- **Box monotonicity** (single antecedent), generalized from `box_mono1`
(`lemma612-scaffold.lean:393`). -/
theorem box_mono1
    (hBoxK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    {φ ψ : Proposition Atom} (h : Derivable Axioms (φ.imp ψ)) :
    Derivable Axioms ((Proposition.box φ).imp (Proposition.box ψ)) := by
  obtain ⟨d⟩ := h
  have hnec : Derivable Axioms (Proposition.box (φ.imp ψ)) := ⟨.necessitation _ d⟩
  exact mp_deriv ⟨.ax [] _ (hBoxK φ ψ)⟩ hnec

/-- **Box monotonicity** (two antecedents), generalized from `box_mono2`
(`lemma612-scaffold.lean:403`). -/
theorem box_mono2
    (hK : ∀ φ ψ : Proposition Atom, Axioms (φ.imp (ψ.imp φ)))
    (hS : ∀ φ ψ χ : Proposition Atom,
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (hBoxK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    {φ ψ χ : Proposition Atom} (h : Derivable Axioms (φ.imp (ψ.imp χ))) :
    Derivable Axioms ((Proposition.box φ).imp ((Proposition.box ψ).imp (Proposition.box χ))) := by
  have h1 : Derivable Axioms ((Proposition.box φ).imp (Proposition.box (ψ.imp χ))) :=
    box_mono1 hBoxK h
  have hk : Derivable Axioms
      ((Proposition.box (ψ.imp χ)).imp ((Proposition.box ψ).imp (Proposition.box χ))) :=
    ⟨.ax [] _ (hBoxK ψ χ)⟩
  set Γ2 : List (Proposition Atom) := [Proposition.box ψ, Proposition.box φ] with hΓ2
  have ha1 : Deriv Axioms Γ2 (Proposition.box φ) := assumption_deriv (by simp [hΓ2])
  have ha2 : Deriv Axioms Γ2 (Proposition.box ψ) := assumption_deriv (by simp [hΓ2])
  have hw1 : Deriv Axioms Γ2 ((Proposition.box φ).imp (Proposition.box (ψ.imp χ))) :=
    weakening_deriv h1 (by simp [hΓ2])
  have hw2 : Deriv Axioms Γ2
      ((Proposition.box (ψ.imp χ)).imp ((Proposition.box ψ).imp (Proposition.box χ))) :=
    weakening_deriv hk (by simp [hΓ2])
  have hstep1 : Deriv Axioms Γ2 (Proposition.box (ψ.imp χ)) := mp_deriv hw1 ha1
  have hstep2 : Deriv Axioms Γ2 ((Proposition.box ψ).imp (Proposition.box χ)) :=
    mp_deriv hw2 hstep1
  have hstep3 : Deriv Axioms Γ2 (Proposition.box χ) := mp_deriv hstep2 ha2
  have hd1 := impIntro hK hS (Γ := [Proposition.box φ]) (φ := Proposition.box ψ) hstep3
  have hd2 := impIntro hK hS (Γ := []) (φ := Proposition.box φ) hd1
  exact hd2

/-! ## `Tele`-congruence: `Tele_imp1`/`Tele_imp2`

Ported from `Star_imp1`/`Star_imp2` (`lemma612-scaffold.lean:450`/`:507`) — same induction on the
path, same combinator sequence, with `star Γ t` replaced by the bare list element `p`. -/

/-- **Single-hypothesis `Tele` monotonicity**, ported from `Star_imp1`
(`lemma612-scaffold.lean:450`): if `⊢A→B` (closed) then `⊢(Tele path A) → (Tele path B)`. -/
theorem Tele_imp1
    (hK : ∀ φ ψ : Proposition Atom, Axioms (φ.imp (ψ.imp φ)))
    (hS : ∀ φ ψ χ : Proposition Atom,
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (hBoxK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (path : List (Proposition Atom)) {A B : Proposition Atom} (h : Derivable Axioms (A.imp B)) :
    Derivable Axioms ((Tele path A).imp (Tele path B)) := by
  induction path with
  | nil => simpa [Tele] using h
  | cons p rest ih =>
    cases rest with
    | nil =>
      simp only [Tele]
      set Γ1 : List (Proposition Atom) := [p.imp A] with hΓ1
      have hant : Deriv Axioms Γ1 (p.imp A) := assumption_deriv (by simp [hΓ1])
      have hp' : Deriv Axioms (p :: Γ1) p := assumption_deriv (by simp)
      have hantw : Deriv Axioms (p :: Γ1) (p.imp A) :=
        weakening_deriv hant (fun z hz => List.mem_cons_of_mem _ hz)
      have hA : Deriv Axioms (p :: Γ1) A := mp_deriv hantw hp'
      have hAB : Deriv Axioms (p :: Γ1) (A.imp B) := by
        obtain ⟨d⟩ := h
        exact ⟨.weakening [] _ _ d (by simp)⟩
      have hB : Deriv Axioms (p :: Γ1) B := mp_deriv hAB hA
      have hd1 := impIntro hK hS (Γ := Γ1) (φ := p) hB
      have hd2 := impIntro hK hS (Γ := []) (φ := p.imp A) hd1
      exact hd2
    | cons p2 rest' =>
      have hinner : Derivable Axioms ((Tele (p2 :: rest') A).imp (Tele (p2 :: rest') B)) := ih
      have hbox : Derivable Axioms ((Proposition.box (Tele (p2 :: rest') A)).imp
          (Proposition.box (Tele (p2 :: rest') B))) := box_mono1 hBoxK hinner
      simp only [Tele]
      set Γ1 : List (Proposition Atom) :=
        [p.imp (Proposition.box (Tele (p2 :: rest') A))] with hΓ1
      have hant : Deriv Axioms Γ1
          (p.imp (Proposition.box (Tele (p2 :: rest') A))) :=
        assumption_deriv (by simp [hΓ1])
      have hp' : Deriv Axioms (p :: Γ1) p := assumption_deriv (by simp)
      have hantw : Deriv Axioms (p :: Γ1)
          (p.imp (Proposition.box (Tele (p2 :: rest') A))) :=
        weakening_deriv hant (fun z hz => List.mem_cons_of_mem _ hz)
      have hboxA : Deriv Axioms (p :: Γ1)
          (Proposition.box (Tele (p2 :: rest') A)) := mp_deriv hantw hp'
      have hboxw : Deriv Axioms (p :: Γ1)
          ((Proposition.box (Tele (p2 :: rest') A)).imp
            (Proposition.box (Tele (p2 :: rest') B))) := by
        obtain ⟨d⟩ := hbox
        exact ⟨.weakening [] _ _ d (by simp)⟩
      have hboxB : Deriv Axioms (p :: Γ1)
          (Proposition.box (Tele (p2 :: rest') B)) := mp_deriv hboxw hboxA
      have hd1 := impIntro hK hS (Γ := Γ1) (φ := p) hboxB
      have hd2 := impIntro hK hS
        (Γ := []) (φ := p.imp (Proposition.box (Tele (p2 :: rest') A))) hd1
      exact hd2

/-- **Two-hypothesis `Tele` combination**, ported from `Star_imp2`
(`lemma612-scaffold.lean:507`): if `⊢A→(B→C)` (closed) then
`⊢(Tele path A) → ((Tele path B) → (Tele path C))`. -/
theorem Tele_imp2
    (hK : ∀ φ ψ : Proposition Atom, Axioms (φ.imp (ψ.imp φ)))
    (hS : ∀ φ ψ χ : Proposition Atom,
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (hBoxK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (path : List (Proposition Atom)) {A B C : Proposition Atom}
    (h : Derivable Axioms (A.imp (B.imp C))) :
    Derivable Axioms ((Tele path A).imp ((Tele path B).imp (Tele path C))) := by
  induction path with
  | nil => simpa [Tele] using h
  | cons p rest ih =>
    cases rest with
    | nil =>
      simp only [Tele]
      set Γ3 : List (Proposition Atom) := [p, p.imp B, p.imp A] with hΓ3
      have hp' : Deriv Axioms Γ3 p := assumption_deriv (by simp [hΓ3])
      have hbimp : Deriv Axioms Γ3 (p.imp B) := assumption_deriv (by simp [hΓ3])
      have haimp : Deriv Axioms Γ3 (p.imp A) := assumption_deriv (by simp [hΓ3])
      have hA : Deriv Axioms Γ3 A := mp_deriv haimp hp'
      have hB : Deriv Axioms Γ3 B := mp_deriv hbimp hp'
      have hABC : Deriv Axioms Γ3 (A.imp (B.imp C)) := by
        obtain ⟨d⟩ := h; exact ⟨.weakening [] _ _ d (by simp)⟩
      have hC : Deriv Axioms Γ3 C := mp_deriv (mp_deriv hABC hA) hB
      have hd1 := impIntro hK hS (Γ := [p.imp B, p.imp A]) (φ := p) hC
      have hd2 := impIntro hK hS (Γ := [p.imp A]) (φ := p.imp B) hd1
      have hd3 := impIntro hK hS (Γ := []) (φ := p.imp A) hd2
      exact hd3
    | cons p2 rest' =>
      have hinner : Derivable Axioms
          ((Tele (p2 :: rest') A).imp
            ((Tele (p2 :: rest') B).imp (Tele (p2 :: rest') C))) := ih
      have hbox : Derivable Axioms ((Proposition.box (Tele (p2 :: rest') A)).imp
          ((Proposition.box (Tele (p2 :: rest') B)).imp
            (Proposition.box (Tele (p2 :: rest') C)))) := box_mono2 hK hS hBoxK hinner
      simp only [Tele]
      set Γ3 : List (Proposition Atom) :=
        [p, p.imp (Proposition.box (Tele (p2 :: rest') B)),
          p.imp (Proposition.box (Tele (p2 :: rest') A))] with hΓ3
      have hp' : Deriv Axioms Γ3 p := assumption_deriv (by simp [hΓ3])
      have hbimp : Deriv Axioms Γ3
          (p.imp (Proposition.box (Tele (p2 :: rest') B))) :=
        assumption_deriv (by simp [hΓ3])
      have haimp : Deriv Axioms Γ3
          (p.imp (Proposition.box (Tele (p2 :: rest') A))) :=
        assumption_deriv (by simp [hΓ3])
      have hboxA : Deriv Axioms Γ3 (Proposition.box (Tele (p2 :: rest') A)) :=
        mp_deriv haimp hp'
      have hboxB : Deriv Axioms Γ3 (Proposition.box (Tele (p2 :: rest') B)) :=
        mp_deriv hbimp hp'
      have hABC : Deriv Axioms Γ3
          ((Proposition.box (Tele (p2 :: rest') A)).imp
            ((Proposition.box (Tele (p2 :: rest') B)).imp
              (Proposition.box (Tele (p2 :: rest') C)))) := by
        obtain ⟨d⟩ := hbox; exact ⟨.weakening [] _ _ d (by simp)⟩
      have hboxC : Deriv Axioms Γ3 (Proposition.box (Tele (p2 :: rest') C)) :=
        mp_deriv (mp_deriv hABC hboxA) hboxB
      have hd1 := impIntro hK hS
        (Γ := [p.imp (Proposition.box (Tele (p2 :: rest') B)),
              p.imp (Proposition.box (Tele (p2 :: rest') A))])
        (φ := p) hboxC
      have hd2 := impIntro hK hS
        (Γ := [p.imp (Proposition.box (Tele (p2 :: rest') A))])
        (φ := p.imp (Proposition.box (Tele (p2 :: rest') B))) hd1
      have hd3 := impIntro hK hS (Γ := [])
        (φ := p.imp (Proposition.box (Tele (p2 :: rest') A))) hd2
      exact hd3

/-! ## Track C — C2: Simpson formula (6.7)

**Appended to this file (not a new file) because C1's combinators are directly reusable only
within the same compilation unit** — these `probes/` files are standalone (`lake env lean
<file>`, not registered under any `lean_lib` source root), so cross-probe `import` by module
name does not resolve; physically sharing the file is the only way to reuse C1's `Conj`/`Tele`/
`impIntro`/`box_mono1` without redeclaration, honoring the plan's C1 entry
("directly reusable by C2/C3 ... without redeclaration or drift risk").

**Goal (source PDF p.104, report 02 §2.5, table row C2)**: for nonempty `V = p :: rest`,
`◇Conj(V) ⊃ □Tele(V,◇A) ⊃ ◇Conj(V++[A])`, *"derived by repeated applications of axiom 2 of IK
(together with intuitionistic propositional reasoning)"*.

**V must be nonempty.** The literal schema fails for `V = []`: it would read
`◇⊤ ⊃ □◇A ⊃ ◇A`, which is *not* a bare-IK theorem (a two-relation countermodel exists: root `w₀`
with `w₀Rw₁`, `w₁Rw₂`, `A` true only at `w₂` — then `w₀⊩◇⊤` and `w₀⊩□◇A` but `w₀⊮◇A`). This is
consistent with Simpson's own usage: `V := [Γ@U¹,…,Γ@U^j]` is always nonempty at every call site
(`y_j`, the `(◇E)`-introduced witness, is always present). The theorem below is therefore stated
for `V = p :: rest` (`p` the head, `rest` the possibly-empty tail), proved by induction on `rest`
— exactly matching `Tele`/`Conj`'s own 3-way pattern match (`nil`/`[p]`/`p :: p2 :: rest`), the
same induction shape C1's `Tele_imp1`/`Tele_imp2` used.

## Two more combinators needed beyond C1 (kDia + And-axioms)

C1's toolkit (`impIntro`/`box_mono1`/`box_mono2`) only carried `implyK`/`implyS`/`kBox` — enough
for `Tele`-only congruence (no `∧`, no `◇` elimination). `Conj` introduces `∧`, and (6.7)'s proof
needs axiom 2 (`kDia`) directly (not just `kBox`), so three more generic hypotheses are added
here: `hDiaK` (`kDia`, Figure 3-7 axiom 2), `hAndI`/`hAndE1`/`hAndE2` (`Cslib.Logic.Axioms.AndI`/
`AndE1`/`AndE2`, the same schemas `IKAx.andI`/`andE1`/`andE2` instantiate). -/

/-- **Diamond monotonicity from an already-boxed implication**, using axiom 2 (`kDia`) directly:
no necessitation step is needed since the hypothesis is already `□(φ→ψ)` (contrast `box_mono1`,
which necessitates an *unconditional* `⊢φ→ψ`). -/
theorem dia_mono1
    (hDiaK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    {φ ψ : Proposition Atom} (h : Derivable Axioms (Proposition.box (φ.imp ψ))) :
    Derivable Axioms ((◇φ).imp (◇ψ)) :=
  mp_deriv ⟨.ax [] _ (hDiaK φ ψ)⟩ h

/-- **(6.7), base case `V = [p]`** (the singleton case): `◇p ⊃ □(p ⊃ ◇A) ⊃ ◇(p ∧ ◇A)`. Uses
axiom 2 (`hDiaK`) once, plus `andI` for the pure-propositional half-step
`(p ⊃ ◇A) ⊃ (p ⊃ (p ∧ ◇A))`. -/
theorem formula_6_7_base
    (hK : ∀ φ ψ : Proposition Atom, Axioms (φ.imp (ψ.imp φ)))
    (hS : ∀ φ ψ χ : Proposition Atom,
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (hBoxK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (hDiaK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (hAndI : ∀ φ ψ : Proposition Atom, Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (p A : Proposition Atom) :
    Derivable Axioms ((◇p).imp ((Proposition.box (p.imp (◇A))).imp (◇ (p.and (◇A))))) := by
  have step1 : Derivable Axioms ((p.imp (◇A)).imp (p.imp (p.and (◇A)))) := by
    set Γ1 : List (Proposition Atom) := [p, p.imp (◇A)] with hΓ1
    have hp' : Deriv Axioms Γ1 p := assumption_deriv (by simp [hΓ1])
    have hpa : Deriv Axioms Γ1 (p.imp (◇A)) := assumption_deriv (by simp [hΓ1])
    have hA' : Deriv Axioms Γ1 (◇A) := mp_deriv hpa hp'
    have handI : Deriv Axioms Γ1 (Cslib.Logic.Axioms.AndI p (◇A)) :=
      ⟨.ax _ _ (hAndI p (◇A))⟩
    have hstep : Deriv Axioms Γ1 (p.and (◇A)) := mp_deriv (mp_deriv handI hp') hA'
    have hd1 := impIntro hK hS (Γ := [p.imp (◇A)]) (φ := p) hstep
    exact impIntro hK hS (Γ := []) (φ := p.imp (◇A)) hd1
  have step2 : Derivable Axioms
      ((Proposition.box (p.imp (◇A))).imp (Proposition.box (p.imp (p.and (◇A))))) :=
    box_mono1 hBoxK step1
  set Γ2 : List (Proposition Atom) := [Proposition.box (p.imp (◇A)), ◇p] with hΓ2
  have hY : Deriv Axioms Γ2 (Proposition.box (p.imp (◇A))) :=
    assumption_deriv (by simp [hΓ2])
  have hX : Deriv Axioms Γ2 (◇p) := assumption_deriv (by simp [hΓ2])
  have hstep2w : Deriv Axioms Γ2
      ((Proposition.box (p.imp (◇A))).imp (Proposition.box (p.imp (p.and (◇A))))) := by
    obtain ⟨d⟩ := step2; exact ⟨.weakening [] _ _ d (by simp)⟩
  have hboxed : Deriv Axioms Γ2 (Proposition.box (p.imp (p.and (◇A)))) :=
    mp_deriv hstep2w hY
  have hdia : Deriv Axioms Γ2
      ((Proposition.box (p.imp (p.and (◇A)))).imp ((◇p).imp (◇ (p.and (◇A))))) :=
    ⟨.weakening [] _ _ (.ax [] _ (hDiaK p (p.and (◇A)))) (by simp)⟩
  have hZ : Deriv Axioms Γ2 (◇ (p.and (◇A))) := mp_deriv (mp_deriv hdia hboxed) hX
  have hd1 := impIntro hK hS (Γ := [◇p]) (φ := Proposition.box (p.imp (◇A))) hZ
  exact impIntro hK hS (Γ := []) (φ := ◇p) hd1

/-- **(6.7), full statement**: for every nonempty `V = p :: rest`,
`◇Conj(V) ⊃ □Tele(V,◇A) ⊃ ◇Conj(V++[A])`. Induction on `rest` (generalizing `p`), matching
`Tele`/`Conj`'s own `nil`/`cons`-of-`cons` pattern-match structure — `nil` is
`formula_6_7_base`; the `cons p2 rest'` step reduces (via `andE1`/`andE2`/`andI` and one
application of axiom 2, `hDiaK`) to the induction hypothesis instantiated at head `p2`. -/
theorem formula_6_7
    (hK : ∀ φ ψ : Proposition Atom, Axioms (φ.imp (ψ.imp φ)))
    (hS : ∀ φ ψ χ : Proposition Atom,
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (hBoxK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (hDiaK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (hAndI : ∀ φ ψ : Proposition Atom, Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (hAndE1 : ∀ φ ψ : Proposition Atom, Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (hAndE2 : ∀ φ ψ : Proposition Atom, Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (rest : List (Proposition Atom)) :
    ∀ (p A : Proposition Atom),
      Derivable Axioms ((◇ (Conj (p :: rest))).imp
        ((Proposition.box (Tele (p :: rest) (◇A))).imp
          (◇ (Conj ((p :: rest) ++ [A]))))) := by
  induction rest with
  | nil => intro p A; simpa [Conj, Tele] using formula_6_7_base hK hS hBoxK hDiaK hAndI p A
  | cons p2 rest' ih =>
    intro p A
    -- Abbreviate the `rest' `-level quantities via the induction hypothesis at head `p2`.
    have ihp2 : Derivable Axioms ((◇ (Conj (p2 :: rest'))).imp
        ((Proposition.box (Tele (p2 :: rest') (◇A))).imp
          (◇ (Conj ((p2 :: rest') ++ [A]))))) := ih p2 A
    set C : Proposition Atom := Conj (p2 :: rest') with hC
    set T : Proposition Atom := Tele (p2 :: rest') (◇A) with hT
    set C' : Proposition Atom := Conj ((p2 :: rest') ++ [A]) with hC'
    -- Step A: the pure (unboxed, un-diamonded) propositional-plus-IH fact
    -- `(p ⊃ □T) ⊃ ((p ∧ ◇C) ⊃ (p ∧ ◇C'))`.
    have Lraw : Derivable Axioms
        ((p.imp (Proposition.box T)).imp ((p.and (◇C)).imp (p.and (◇C')))) := by
      set Γ2 : List (Proposition Atom) := [p.and (◇C), p.imp (Proposition.box T)] with hΓ2
      have hX : Deriv Axioms Γ2 (p.imp (Proposition.box T)) := assumption_deriv (by simp [hΓ2])
      have hY : Deriv Axioms Γ2 (p.and (◇C)) := assumption_deriv (by simp [hΓ2])
      have hAndE1w : Deriv Axioms Γ2 ((p.and (◇C)).imp p) :=
        ⟨.weakening [] _ _ (.ax [] _ (hAndE1 p (◇C))) (by simp)⟩
      have hAndE2w : Deriv Axioms Γ2 ((p.and (◇C)).imp (◇C)) :=
        ⟨.weakening [] _ _ (.ax [] _ (hAndE2 p (◇C))) (by simp)⟩
      have hp : Deriv Axioms Γ2 p := mp_deriv hAndE1w hY
      have hdiaC : Deriv Axioms Γ2 (◇C) := mp_deriv hAndE2w hY
      have hboxT : Deriv Axioms Γ2 (Proposition.box T) := mp_deriv hX hp
      have hIHw : Deriv Axioms Γ2 ((◇C).imp ((Proposition.box T).imp (◇C'))) := by
        obtain ⟨d⟩ := ihp2; exact ⟨.weakening [] _ _ d (by simp)⟩
      have hdiaC' : Deriv Axioms Γ2 (◇C') := mp_deriv (mp_deriv hIHw hdiaC) hboxT
      have hAndIw : Deriv Axioms Γ2 (Cslib.Logic.Axioms.AndI p (◇C')) :=
        ⟨.weakening [] _ _ (.ax [] _ (hAndI p (◇C'))) (by simp)⟩
      have hZ : Deriv Axioms Γ2 (p.and (◇C')) := mp_deriv (mp_deriv hAndIw hp) hdiaC'
      have hd1 := impIntro hK hS (Γ := [p.imp (Proposition.box T)]) (φ := p.and (◇C)) hZ
      exact impIntro hK hS (Γ := []) (φ := p.imp (Proposition.box T)) hd1
    -- Step B: box both sides of `Lraw`.
    have Lbox : Derivable Axioms
        ((Proposition.box (p.imp (Proposition.box T))).imp
          (Proposition.box ((p.and (◇C)).imp (p.and (◇C'))))) :=
      box_mono1 hBoxK Lraw
    -- Step C: assemble the goal `◇(p∧◇C) ⊃ □(p ⊃ □T) ⊃ ◇(p∧◇C')` from `Lbox` + axiom 2.
    set Γo : List (Proposition Atom) :=
      [Proposition.box (p.imp (Proposition.box T)), ◇ (p.and (◇C))] with hΓo
    have hXo : Deriv Axioms Γo (◇ (p.and (◇C))) := assumption_deriv (by simp [hΓo])
    have hYo : Deriv Axioms Γo (Proposition.box (p.imp (Proposition.box T))) :=
      assumption_deriv (by simp [hΓo])
    have hLboxw : Deriv Axioms Γo
        ((Proposition.box (p.imp (Proposition.box T))).imp
          (Proposition.box ((p.and (◇C)).imp (p.and (◇C'))))) := by
      obtain ⟨d⟩ := Lbox; exact ⟨.weakening [] _ _ d (by simp)⟩
    have hboxImp : Deriv Axioms Γo (Proposition.box ((p.and (◇C)).imp (p.and (◇C')))) :=
      mp_deriv hLboxw hYo
    have hkdia : Deriv Axioms Γo
        ((Proposition.box ((p.and (◇C)).imp (p.and (◇C')))).imp
          ((◇ (p.and (◇C))).imp (◇ (p.and (◇C'))))) :=
      ⟨.weakening [] _ _ (.ax [] _ (hDiaK (p.and (◇C)) (p.and (◇C')))) (by simp)⟩
    have hZo : Deriv Axioms Γo (◇ (p.and (◇C'))) := mp_deriv (mp_deriv hkdia hboxImp) hXo
    have hd1 := impIntro hK hS (Γ := [◇ (p.and (◇C))])
      (φ := Proposition.box (p.imp (Proposition.box T))) hZo
    have hd2 := impIntro hK hS (Γ := []) (φ := ◇ (p.and (◇C))) hd1
    simpa [Conj, Tele, hC, hT, hC', Derivable] using hd2

end Cslib.Logic.Modal.TeleConj
