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

/-! ## Track C — C3: Simpson formula (6.8)

**Goal (source PDF p.104, report 02 §2.5, table row C3)**: for *every* `W : List (Proposition
Atom)` (empty list included — see the base-case sanity check below, this is the one place C3
diverges from C2's scoping restriction), `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)`, *"derived by
repeated applications of axiom 5 of IK"* (`hFS`, `IKAx.fs`, `lemma612-scaffold.lean:117`,
`((◇φ).imp(□ψ)).imp(□(φ.imp ψ))`, added by A1).

**Base-case sanity check, done BEFORE writing any Lean (per the C2 resume-pointer warning)**:
unlike (6.7)'s `V = []` instance (refuted by a countermodel, see C2 above), *(6.8)'s `W = []`
instance is a genuine IK theorem — no restatement needed*. At `W = []`: `Conj [] = ⊤`,
`Tele [] B = B`, so the instance reads `(◇⊤ ⊃ □B) ⊃ □B`. Semantic check: fix any birelational IK
model and world `w`. If `w` has no `R`-successor, `◇⊤` is false at `w` (vacuously), so the whole
implication holds vacuously. If `w` has an `R`-successor, `⊤` holds everywhere so `◇⊤` is *true*
at `w`, and then `◇⊤ ⊃ □B` forces `□B` directly by modus ponens. Either way `(◇⊤⊃□B)⊃□B` holds at
every world — a genuine unconditional validity, not one requiring `W` nonempty. The Lean proof
below confirms this syntactically via `hFS ⊤ B` plus the pure-IPL fact `⊢(⊤⊃B)⊃B` (the only role
`Proposition.top` plays is being *provable*, `⊢⊤`, which needs no `GeomAxiom.D`/seriality
assumption — contrast `IKAx.dDia`, gated on `D ∈ 𝒯`, which asserts the *stronger* unconditional
`⊢◇⊤`, not needed here).

**Why the self-referential shape does not collapse to a single `hFS` instantiation** (per the
dispatch's warning that (6.8)'s shape differs structurally from (6.7)'s): naively substituting
`φ := Conj(W)`, `ψ := Tele(W,B)` directly into `hFS` gives
`(◇Conj(W)⊃□Tele(W,B)) ⊃ □(Conj(W).imp Tele(W,B))`, whose consequent is
`□(Conj(W)⊃Tele(W,B))`, *not* the target `□Tele(W,B)` — these coincide only via a further
`(Conj(W)⊃Tele(W,B)) ⊃ Tele(W,B)`-shaped fact, which is *not* a bare IPL tautology once `Conj(W)`
contains a `◇`-guarded tail (checked directly by hand: for `W=[p,q]`,
`((p∧◇q)⊃(p⊃□(q⊃B)))⊃(p⊃□(q⊃B))` gets stuck deriving `◇q` from `p` alone — assuming the
antecedent and `p`, there is no way to invoke it without `◇q` in hand). The actual induction
(below, sorry-free) instead uses the **IH itself, relativized one `Tele [p]`-layer deeper via
`Tele_imp1`**, composed with `hFS` and one *pure-IPL* currying step per list element — genuinely
"repeated application of axiom 5" (once per recursion level, bottoming out at the base case),
not a single flat instantiation. -/

/-- **Transitivity of `Derivable`-implication** (Hilbert-style compose): from `⊢A→B` and `⊢B→C`
derive `⊢A→C`. New combinator needed by C3 — Simpson's own (◇E) argument (§2.5) composes exactly
three such steps ((6.4)+(6.7), then +(6.5), then +(6.8)); this is that composition primitive,
and C3's own inductive step needs it twice internally. -/
theorem derivable_imp_trans
    (hK : ∀ φ ψ : Proposition Atom, Axioms (φ.imp (ψ.imp φ)))
    (hS : ∀ φ ψ χ : Proposition Atom,
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {A B C : Proposition Atom}
    (h1 : Derivable Axioms (A.imp B)) (h2 : Derivable Axioms (B.imp C)) :
    Derivable Axioms (A.imp C) := by
  set Γ : List (Proposition Atom) := [A] with hΓ
  have hA : Deriv Axioms Γ A := assumption_deriv (by simp [hΓ])
  have h1' : Deriv Axioms Γ (A.imp B) := weakening_deriv h1 (by simp [hΓ])
  have hB : Deriv Axioms Γ B := mp_deriv h1' hA
  have h2' : Deriv Axioms Γ (B.imp C) := weakening_deriv h2 (by simp [hΓ])
  have hC : Deriv Axioms Γ C := mp_deriv h2' hB
  exact impIntro hK hS (Γ := []) (φ := A) hC

/-- **(6.8), full statement, for every `W` (empty list included, see the base-case sanity check
above)**: `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)`. Induction on `W`, matching `Tele`/`Conj`'s own
`nil`/`[p]`/`p::p2::rest` 3-way pattern-match (same shape C1's `Tele_imp1`/`Tele_imp2` and C2's
`formula_6_7` used). Every case is closed using `hFS` (axiom 5) once, composed (via
`derivable_imp_trans`) with a box-lifted pure-IPL identity: `nil` uses `⊢(⊤⊃B)⊃B`; `[p]` uses
contraction `⊢(p⊃(p⊃B))⊃(p⊃B)`; `p::p2::rest'` uses currying
`⊢((p∧◇C')⊃(p⊃□T'))⊃(p⊃((◇C')⊃□T'))` (where `C' := Conj(p2::rest')`, `T' := Tele(p2::rest',B)`)
composed with the *induction hypothesis* relativized one `Tele [p]`-layer deeper via
`Tele_imp1`. -/
theorem formula_6_8
    (hK : ∀ φ ψ : Proposition Atom, Axioms (φ.imp (ψ.imp φ)))
    (hS : ∀ φ ψ χ : Proposition Atom,
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (hBoxK : ∀ φ ψ : Proposition Atom,
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (hAndI : ∀ φ ψ : Proposition Atom, Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (hFS : ∀ φ ψ : Proposition Atom,
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    (W : List (Proposition Atom)) (B : Proposition Atom) :
    Derivable Axioms
      (((◇ (Conj W)).imp (Proposition.box (Tele W B))).imp (Proposition.box (Tele W B))) := by
  induction W with
  | nil =>
    simp only [Conj, Tele]
    have htop : Derivable Axioms (Proposition.top : Proposition Atom) := by
      have h : Deriv Axioms [] (Proposition.bot.imp Proposition.bot) :=
        impIntro hK hS (Γ := []) (φ := Proposition.bot) (assumption_deriv (by simp))
      rw [Proposition.top_def]
      exact h
    have htopImpB : Derivable Axioms ((Proposition.top.imp B).imp B) := by
      set Γ1 : List (Proposition Atom) := [Proposition.top.imp B] with hΓ1
      have htopw : Deriv Axioms Γ1 Proposition.top := weakening_deriv htop (by simp [hΓ1])
      have himp : Deriv Axioms Γ1 (Proposition.top.imp B) := assumption_deriv (by simp [hΓ1])
      have hB : Deriv Axioms Γ1 B := mp_deriv himp htopw
      exact impIntro hK hS (Γ := []) (φ := Proposition.top.imp B) hB
    have hboxCongr : Derivable Axioms
        ((Proposition.box (Proposition.top.imp B)).imp (Proposition.box B)) :=
      box_mono1 hBoxK htopImpB
    have h5 : Derivable Axioms
        (((◇ Proposition.top).imp (Proposition.box B)).imp
          (Proposition.box (Proposition.top.imp B))) :=
      ⟨.ax [] _ (hFS Proposition.top B)⟩
    exact derivable_imp_trans hK hS h5 hboxCongr
  | cons p rest ih =>
    cases rest with
    | nil =>
      simp only [Conj, Tele]
      have hContraction : Derivable Axioms ((p.imp (p.imp B)).imp (p.imp B)) := by
        set Γc : List (Proposition Atom) := [p, p.imp (p.imp B)] with hΓc
        have hp' : Deriv Axioms Γc p := assumption_deriv (by simp [hΓc])
        have hpp : Deriv Axioms Γc (p.imp (p.imp B)) := assumption_deriv (by simp [hΓc])
        have hpb : Deriv Axioms Γc (p.imp B) := mp_deriv hpp hp'
        have hb : Deriv Axioms Γc B := mp_deriv hpb hp'
        have hd1 := impIntro hK hS (Γ := [p.imp (p.imp B)]) (φ := p) hb
        exact impIntro hK hS (Γ := []) (φ := p.imp (p.imp B)) hd1
      have hboxContraction : Derivable Axioms
          ((Proposition.box (p.imp (p.imp B))).imp (Proposition.box (p.imp B))) :=
        box_mono1 hBoxK hContraction
      have h5 : Derivable Axioms
          (((◇p).imp (Proposition.box (p.imp B))).imp
            (Proposition.box (p.imp (p.imp B)))) :=
        ⟨.ax [] _ (hFS p (p.imp B))⟩
      exact derivable_imp_trans hK hS h5 hboxContraction
    | cons p2 rest' =>
      simp only [Conj, Tele]
      set C' : Proposition Atom := Conj (p2 :: rest') with hC'
      set T' : Proposition Atom := Tele (p2 :: rest') B with hT'
      -- `ih : Derivable Axioms (((◇C').imp (Proposition.box T')).imp (Proposition.box T'))`
      have hCurry : Derivable Axioms
          (((p.and (◇C')).imp (p.imp (Proposition.box T'))).imp
            (p.imp ((◇C').imp (Proposition.box T')))) := by
        set Γcu : List (Proposition Atom) :=
          [◇C', p, (p.and (◇C')).imp (p.imp (Proposition.box T'))] with hΓcu
        have hdc' : Deriv Axioms Γcu (◇C') := assumption_deriv (by simp [hΓcu])
        have hp' : Deriv Axioms Γcu p := assumption_deriv (by simp [hΓcu])
        have hphi : Deriv Axioms Γcu ((p.and (◇C')).imp (p.imp (Proposition.box T'))) :=
          assumption_deriv (by simp [hΓcu])
        have handI : Deriv Axioms Γcu (Cslib.Logic.Axioms.AndI p (◇C')) :=
          weakening_deriv ⟨.ax [] _ (hAndI p (◇C'))⟩ (by simp)
        have hand : Deriv Axioms Γcu (p.and (◇C')) := mp_deriv (mp_deriv handI hp') hdc'
        have hpsi : Deriv Axioms Γcu (p.imp (Proposition.box T')) := mp_deriv hphi hand
        have hboxT' : Deriv Axioms Γcu (Proposition.box T') := mp_deriv hpsi hp'
        have hd1 := impIntro hK hS
          (Γ := [p, (p.and (◇C')).imp (p.imp (Proposition.box T'))]) (φ := ◇C') hboxT'
        have hd2 := impIntro hK hS
          (Γ := [(p.and (◇C')).imp (p.imp (Proposition.box T'))]) (φ := p) hd1
        exact impIntro hK hS (Γ := [])
          (φ := (p.and (◇C')).imp (p.imp (Proposition.box T'))) hd2
      have hBoxCurry : Derivable Axioms
          ((Proposition.box ((p.and (◇C')).imp (p.imp (Proposition.box T')))).imp
            (Proposition.box (p.imp ((◇C').imp (Proposition.box T'))))) :=
        box_mono1 hBoxK hCurry
      have hIhRel : Derivable Axioms
          ((p.imp ((◇C').imp (Proposition.box T'))).imp (p.imp (Proposition.box T'))) := by
        have h := Tele_imp1 hK hS hBoxK [p] ih
        simpa [Tele] using h
      have hBoxIhRel : Derivable Axioms
          ((Proposition.box (p.imp ((◇C').imp (Proposition.box T')))).imp
            (Proposition.box (p.imp (Proposition.box T')))) :=
        box_mono1 hBoxK hIhRel
      have hBoxPsi : Derivable Axioms
          ((Proposition.box ((p.and (◇C')).imp (p.imp (Proposition.box T')))).imp
            (Proposition.box (p.imp (Proposition.box T')))) :=
        derivable_imp_trans hK hS hBoxCurry hBoxIhRel
      have h5 : Derivable Axioms
          (((◇ (p.and (◇C'))).imp (Proposition.box (p.imp (Proposition.box T')))).imp
            (Proposition.box ((p.and (◇C')).imp (p.imp (Proposition.box T'))))) :=
        ⟨.ax [] _ (hFS (p.and (◇C')) (p.imp (Proposition.box T')))⟩
      exact derivable_imp_trans hK hS h5 hBoxPsi

end Cslib.Logic.Modal.TeleConj
