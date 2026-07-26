/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.Nested.Translation

/-! # Soundness Auxiliary Lemmas (Theorem 4.1's Lemma 4.2–4.9 Family)

This module lands Arisaka–Das–Straßburger's soundness auxiliary lemmas
(`doc_id: arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`, §4, page 9-10,
Lemmas 4.2–4.9), opening Stage D (`Theorem 4.1`, soundness of `NCS5` with respect to `HCS5`). Every
lemma is stated against `Derivable (@CS5ModalAxiom Atom)`, fixing `X = {t,4,b}` (`CS5`'s safe
pair, Phase 10), matching this development's `NCS5` instance rather than the source's generic
`X ⊆ {d,t,b,4,5}` parameterisation.

## Settled Design (binding this phase and successors)

* **Route**: nested-sequent soundness via Hilbert-derivability facts about `fm`, not a semantic
  argument (the source's own Theorem 4.1 proof route).
* **`InputCtx`-vs-`OutputCtx` convention** (Phase 9): LHS-typed hole content uses
  `InputCtx.fillLhs`; RHS-typed content uses `OutputCtx.fillRhs`/`.fillFull`.
* **Reused, not re-proved**: Phase 8's `OutputCtx.fillRhs_fm_mono`, `OutputCtx.fillLhs_fm_mono`,
  and `InputCtx.fillLhs_fm_antitone` are the compositionality engines Lemma 4.4/4.5 below cite
  directly, per this phase's own task list ("using Phase 8's compositionality lemmas").
* **Dead ends** (do not re-attempt): the semantic route via pair-axiom soundness is circular
  (would need the very soundness fact being proved); a signature-collapse via sum-elimination
  retraction is not schema-compatible with the `NestedProof` inductive's per-rule indexing.

## Lemma 4.7(i)/(ii): A Documented Source Duplication

Page 10 displays Lemma 4.7 parts (i) and (ii) with **literally the same visible formula**:
"If `(A ∧ B) ⊃ C` is provable in `HCK+X`, then so is `((D ⊃ A) ∧ (D ⊃ B)) ⊃ (D ⊃ C)`" — verified
against a direct render of page 10 (not just `pdftotext`, which independently corrupts this
region by dropping/misreading operator glyphs at exactly this position, consistent with this
development's already-documented `pdftotext` unreliability for this PDF's font encoding). Since
both parts cite the identical conclusion and Lemma 4.9's proof separately invokes "Lemma 4.7.(i)"
(for Lemma 4.8's congruence, alongside part (iii)) and "Lemma 4.7.(ii)" (for the `cut`-rule's
chain argument, alongside part (iv)), landing **one** Lean fact discharges both citations; this is
recorded here as an observed source duplication, not a silent invention of a different statement.

## References

* [R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal
  Logics*][ArisakaDasStrassburger2015], §4, Theorem 4.1 and Lemmas 4.2–4.9 (pages 9–10).
-/

@[expose] public section

namespace Cslib.Logic.Modal

universe u
variable {Atom : Type u}

/-! ## Local Hilbert-Combinator Toolkit

Reproduces (rather than imports) a small `Derivable CS5ModalAxiom` toolkit, mirroring the
established per-file pattern already used in `Nested/Translation.lean` (see that module's
docstring for why: avoiding an architecturally-confusing dependency on the unrelated
labelled-sequent metalogic subsystem for a handful of small propositional/modal combinators).
`private` declarations are file-scoped, so reusing the same names here does not clash with
`Translation.lean`'s own copies. -/

/-- **Identity**: `⊢ P ⊃ P`. -/
private theorem cs5DerivImpSelf (P : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) (P.imp P) := by
  have h1 : DerivationTree (@CS5ModalAxiom Atom) []
      ((P.imp ((P.imp P).imp P)).imp ((P.imp (P.imp P)).imp (P.imp P))) :=
    .ax [] _ (.implyS P (P.imp P) P)
  have h2 : DerivationTree (@CS5ModalAxiom Atom) [] (P.imp ((P.imp P).imp P)) :=
    .ax [] _ (.implyK P (P.imp P))
  have h3 : DerivationTree (@CS5ModalAxiom Atom) [] ((P.imp (P.imp P)).imp (P.imp P)) :=
    .modus_ponens [] _ _ h1 h2
  have h4 : DerivationTree (@CS5ModalAxiom Atom) [] (P.imp (P.imp P)) := .ax [] _ (.implyK P P)
  exact ⟨.modus_ponens [] _ _ h3 h4⟩

/-- **Constant weakening**: from a closed theorem `⊢ Q`, derive `⊢ P ⊃ Q` for any `P`. -/
private theorem cs5DerivImpOfDerivable (P : Proposition Atom) {Q : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) Q) : Derivable (@CS5ModalAxiom Atom) (P.imp Q) := by
  obtain ⟨d⟩ := h
  exact ⟨.modus_ponens [] Q (P.imp Q) (.ax [] _ (.implyK Q P)) d⟩

/-- **Empty-context implication transitivity**: from `⊢ P ⊃ Q` and `⊢ Q ⊃ R`, derive `⊢ P ⊃ R`. -/
private theorem cs5DerivImpTrans {P Q R : Proposition Atom}
    (h1 : Derivable (@CS5ModalAxiom Atom) (P.imp Q))
    (h2 : Derivable (@CS5ModalAxiom Atom) (Q.imp R)) :
    Derivable (@CS5ModalAxiom Atom) (P.imp R) := by
  obtain ⟨d1⟩ := h1
  obtain ⟨d2⟩ := h2
  have hk : DerivationTree (@CS5ModalAxiom Atom) [] ((Q.imp R).imp (P.imp (Q.imp R))) :=
    .ax [] _ (.implyK (Q.imp R) P)
  have hpqr : DerivationTree (@CS5ModalAxiom Atom) [] (P.imp (Q.imp R)) :=
    .modus_ponens [] (Q.imp R) (P.imp (Q.imp R)) hk d2
  have hs : DerivationTree (@CS5ModalAxiom Atom) []
      ((P.imp (Q.imp R)).imp ((P.imp Q).imp (P.imp R))) :=
    .ax [] _ (.implyS P Q R)
  have hstep : DerivationTree (@CS5ModalAxiom Atom) [] ((P.imp Q).imp (P.imp R)) :=
    .modus_ponens [] (P.imp (Q.imp R)) ((P.imp Q).imp (P.imp R)) hs hpqr
  exact ⟨.modus_ponens [] (P.imp Q) (P.imp R) hstep d1⟩

/-- **`□`-monotonicity**: from `⊢ X ⊃ Y`, derive `⊢ □X ⊃ □Y`. -/
private theorem cs5DerivBoxMono {X Y : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (X.imp Y)) :
    Derivable (@CS5ModalAxiom Atom) ((Proposition.box X).imp (Proposition.box Y)) := by
  obtain ⟨d⟩ := h
  obtain ⟨dnec⟩ : Derivable (@CS5ModalAxiom Atom) (Proposition.box (X.imp Y)) :=
    ⟨.necessitation _ d⟩
  exact ⟨.modus_ponens [] _ _ (.ax [] _ (.k X Y)) dnec⟩

/-- **`◇`-monotonicity**: from `⊢ X ⊃ Y`, derive `⊢ ◇X ⊃ ◇Y`. -/
private theorem cs5DerivDiaMono {X Y : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (X.imp Y)) :
    Derivable (@CS5ModalAxiom Atom) ((◇X).imp (◇Y)) := by
  obtain ⟨d⟩ := h
  obtain ⟨dnec⟩ : Derivable (@CS5ModalAxiom Atom) (Proposition.box (X.imp Y)) :=
    ⟨.necessitation _ d⟩
  exact ⟨.modus_ponens [] _ _ (.ax [] _ (.kdia X Y)) dnec⟩

/-- **Congruence in the consequent**: from `⊢ U ⊃ V`, derive `⊢ (P ⊃ U) ⊃ (P ⊃ V)`. -/
private theorem cs5DerivImpCongrRight (P : Proposition Atom) {U V : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (U.imp V)) :
    Derivable (@CS5ModalAxiom Atom) ((P.imp U).imp (P.imp V)) := by
  obtain ⟨ds⟩ := cs5DerivImpOfDerivable P h
  exact ⟨.modus_ponens [] _ _ (.ax [] _ (.implyS P U V)) ds⟩

/-- **Congruence in the antecedent (contravariant)**: from `⊢ a ⊃ a'`, derive
`⊢ (a' ⊃ b) ⊃ (a ⊃ b)`. -/
private theorem cs5DerivImpCongrLeft {a a' b : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (a.imp a')) :
    Derivable (@CS5ModalAxiom Atom) ((a'.imp b).imp (a.imp b)) := by
  obtain ⟨d⟩ := h
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] (a'.imp b) (a.imp b) ?_⟩
  exact deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [a'.imp b] a b
    (.modus_ponens _ _ _
      (.assumption [a, a'.imp b] _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
      (.modus_ponens _ _ _
        (.weakening [] [a, a'.imp b] _ d (fun _ h => nomatch h))
        (.assumption [a, a'.imp b] _ (List.mem_cons.mpr (Or.inl rfl)))))

/-- **Congruence in the right conjunct**: from `⊢ b ⊃ b'`, derive `⊢ (a ∧ b) ⊃ (a ∧ b')`. -/
private theorem cs5DerivAndCongrRight (a : Proposition Atom) {b b' : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (b.imp b')) :
    Derivable (@CS5ModalAxiom Atom) ((a.and b).imp (a.and b')) := by
  have h1 : Derivable (@CS5ModalAxiom Atom) ((a.and b).imp a) := ⟨.ax [] _ (.andE1 a b)⟩
  have h2 : Derivable (@CS5ModalAxiom Atom) ((a.and b).imp b') :=
    cs5DerivImpTrans ⟨.ax [] _ (.andE2 a b)⟩ h
  have step1 : Derivable (@CS5ModalAxiom Atom) ((a.and b).imp (b'.imp (a.and b'))) :=
    cs5DerivImpTrans h1 ⟨.ax [] _ (.andI a b')⟩
  obtain ⟨d1⟩ := step1
  obtain ⟨d2⟩ := h2
  exact ⟨.modus_ponens [] _ _
    (.modus_ponens [] _ _ (.ax [] _ (.implyS (a.and b) b' (a.and b'))) d1) d2⟩

/-- **`⊤`-elimination**: `⊢ (⊤ ⊃ X) ⊃ X`. -/
private theorem cs5DerivTopImpElim {X : Proposition Atom} :
    Derivable (@CS5ModalAxiom Atom) ((Proposition.top.imp X).imp X) := by
  obtain ⟨dtop⟩ := cs5DerivImpSelf (Atom := Atom) Proposition.bot
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] (Proposition.top.imp X) X ?_⟩
  exact .modus_ponens _ _ _
    (.assumption [Proposition.top.imp X] _ (List.mem_cons.mpr (Or.inl rfl)))
    (.weakening [] [Proposition.top.imp X] _ dtop (fun _ h => nomatch h))

/-- **`⊤`-introduction**: `⊢ X ⊃ ⊤`, for any `X`. -/
private theorem cs5DerivTopIntro (X : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) (X.imp Proposition.top) :=
  cs5DerivImpOfDerivable X (cs5DerivImpSelf Proposition.bot)

/-- **Uncurry, swapped order**: from `⊢ Q ⊃ (P ⊃ R)`, derive `⊢ (P ∧ Q) ⊃ R`. Built via nested
`deductionTheorem` discharge of the single hypothesis `P ∧ Q`, projecting `P`/`Q` via
`andE1`/`andE2` before re-applying the (weakened) curried fact. -/
private theorem cs5DerivUncurrySwap {P Q R : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (Q.imp (P.imp R))) :
    Derivable (@CS5ModalAxiom Atom) ((P.and Q).imp R) := by
  obtain ⟨d⟩ := h
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] (P.and Q) R ?_⟩
  have hP : DerivationTree (@CS5ModalAxiom Atom) [P.and Q] P :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE1 P Q)) (fun _ h => nomatch h))
      (.assumption [P.and Q] _ (List.mem_singleton.mpr rfl))
  have hQ : DerivationTree (@CS5ModalAxiom Atom) [P.and Q] Q :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE2 P Q)) (fun _ h => nomatch h))
      (.assumption [P.and Q] _ (List.mem_singleton.mpr rfl))
  have hd : DerivationTree (@CS5ModalAxiom Atom) [P.and Q] (Q.imp (P.imp R)) :=
    .weakening [] _ _ d (fun _ h => nomatch h)
  exact .modus_ponens _ _ _ (.modus_ponens _ _ _ hd hQ) hP

/-- **Curry**: from `⊢ (P ∧ Q) ⊃ R`, derive `⊢ P ⊃ (Q ⊃ R)`. Built via two nested
`deductionTheorem` discharges (`P` then `Q`), combining the two projected assumptions via `andI`
before re-applying the (weakened) and-shaped fact. -/
private theorem cs5DerivCurry {P Q R : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((P.and Q).imp R)) :
    Derivable (@CS5ModalAxiom Atom) (P.imp (Q.imp R)) := by
  obtain ⟨d⟩ := h
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] P (Q.imp R) ?_⟩
  refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [P] Q R ?_
  have hQ : DerivationTree (@CS5ModalAxiom Atom) [Q, P] Q :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hP : DerivationTree (@CS5ModalAxiom Atom) [Q, P] P :=
    .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have hand : DerivationTree (@CS5ModalAxiom Atom) [Q, P] (P.and Q) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (.andI P Q)) (fun _ h => nomatch h)) hP) hQ
  have hd : DerivationTree (@CS5ModalAxiom Atom) [Q, P] ((P.and Q).imp R) :=
    .weakening [] _ _ d (fun _ h => nomatch h)
  exact .modus_ponens _ _ _ hd hand

/-! ## Lemma 4.2 (page 9): Soundness of the Axioms Through an Output Context

`fm(buildFullChain l ΦΨ) = □(fm(OutputCtx.fillFull l ΦΨ))` holds definitionally: both functions
share the same three-way case split on `l`, and each branch's `fm`-image unfolds to the identical
term (verified case-by-case below, each closing by `rfl`). This is the bridge Lemma 4.2's
recursive case needs to move from the inductive hypothesis (a `fillFull`-shaped fact) to the
`buildFullChain`-shaped term one level up. -/
private theorem buildFullChain_fm (l : List (NestedLhs Atom)) (ΦΨ : NestedFull Atom) :
    (buildFullChain l ΦΨ).fm = Proposition.box (OutputCtx.fillFull l ΦΨ).fm := by
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- **Lemma 4.2** (page 9), `id` half: for every output context `Γ{ }` and atom `a`, `fm(Γ{a•,a°})`
is `CS5`-provable (the source's generic `HCK+X`, specialised to `X = {t,4,b}`). Proved by
induction on the structure of `Γ{ }`, matching `OutputCtx.fillFull`'s own three-way recursion: the
base case (`Γ = { }`) is the identity `a ⊃ a`; the singleton case (`Γ = [Γ₁]`) is `andE1` directly
(`(a ∧ Γ₁.fm) ⊃ a`); the general case necessitates the (structurally shorter) inductive hypothesis
and discharges the new head layer via constant weakening (`implyK`), mirroring
`buildFullChain`'s own `box Γ (buildFullChain rest ΦΨ)` step. -/
theorem lemma4_2_id (a : Atom) :
    ∀ (Γ : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom) (Γ.fillFull (.atom (.atom a), .atom (.atom a))).fm
  | [] => cs5DerivImpSelf (.atom a)
  | [Γ₁] => ⟨.ax [] _ (.andE1 (.atom a) Γ₁.fm)⟩
  | Γ :: (Γ₂ :: rest) => by
      have hIH := lemma4_2_id a (Γ₂ :: rest)
      obtain ⟨d⟩ := hIH
      change Derivable (@CS5ModalAxiom Atom)
        (Γ.fm.imp (buildFullChain (Γ₂ :: rest) (.atom (.atom a), .atom (.atom a))).fm)
      rw [buildFullChain_fm]
      exact cs5DerivImpOfDerivable Γ.fm ⟨.necessitation _ d⟩

/-- **Lemma 4.2** (page 9), `⊥•` half: for every output context `Γ{ }` and RHS-sequent `π°`
(spelled lowercase, not capital `Π`: Mathlib binds capital `Π` as a delaborator token for
Pi-types, unusable as a plain identifier here -- the same clash `Nested/Context.lean`'s docstring
already documents for its own `π` field), `fm(Γ{⊥•,π°})` is `CS5`-provable. Same induction shape
as `lemma4_2_id`: the base case is `efq` directly (`⊥ ⊃ π.fm`); the singleton case composes
`andE1` (`(⊥ ∧ Γ₁.fm) ⊃ ⊥`) with `efq` (`⊥ ⊃ π.fm`) via transitivity; the general case is
identical to `lemma4_2_id`'s. -/
theorem lemma4_2_bot (π : NestedRhs Atom) :
    ∀ (Γ : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom) (Γ.fillFull (.atom .bot, π)).fm
  | [] => ⟨.ax [] _ (.efq π.fm)⟩
  | [Γ₁] =>
      cs5DerivImpTrans (⟨.ax [] _ (.andE1 Proposition.bot Γ₁.fm)⟩ :
        Derivable (@CS5ModalAxiom Atom) ((Proposition.bot.and Γ₁.fm).imp Proposition.bot))
        ⟨.ax [] _ (.efq π.fm)⟩
  | Γ :: (Γ₂ :: rest) => by
      have hIH := lemma4_2_bot π (Γ₂ :: rest)
      obtain ⟨d⟩ := hIH
      change Derivable (@CS5ModalAxiom Atom)
        (Γ.fm.imp (buildFullChain (Γ₂ :: rest) (.atom .bot, π)).fm)
      rw [buildFullChain_fm]
      exact cs5DerivImpOfDerivable Γ.fm ⟨.necessitation _ d⟩

/-! ## Lemma 4.3 (page 9): Propositional/Modal Congruence Facts

All five parts are thin restatements of the local toolkit's combinators above, cross-referenced to
the source's own sub-labelling. -/

/-- **Lemma 4.3(i)**: if `A ⊃ B` is provable, so is `(C ⊃ A) ⊃ (C ⊃ B)`. -/
theorem lemma4_3_i (C : Proposition Atom) {A B : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (A.imp B)) :
    Derivable (@CS5ModalAxiom Atom) ((C.imp A).imp (C.imp B)) :=
  cs5DerivImpCongrRight C h

/-- **Lemma 4.3(ii)**: if `A ⊃ B` is provable, so is `(B ⊃ C) ⊃ (A ⊃ C)`. -/
theorem lemma4_3_ii {A B : Proposition Atom} (C : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (A.imp B)) :
    Derivable (@CS5ModalAxiom Atom) ((B.imp C).imp (A.imp C)) :=
  cs5DerivImpCongrLeft h

/-- **Lemma 4.3(iii)**: if `A ⊃ B` is provable, so is `(C ∧ A) ⊃ (C ∧ B)`. -/
theorem lemma4_3_iii (C : Proposition Atom) {A B : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (A.imp B)) :
    Derivable (@CS5ModalAxiom Atom) ((C.and A).imp (C.and B)) :=
  cs5DerivAndCongrRight C h

/-- **Lemma 4.3(iv)**: if `A ⊃ B` is provable, so is `□A ⊃ □B`. -/
theorem lemma4_3_iv {A B : Proposition Atom} (h : Derivable (@CS5ModalAxiom Atom) (A.imp B)) :
    Derivable (@CS5ModalAxiom Atom) ((Proposition.box A).imp (Proposition.box B)) :=
  cs5DerivBoxMono h

/-- **Lemma 4.3(v)**: if `A ⊃ B` is provable, so is `◇A ⊃ ◇B`. -/
theorem lemma4_3_v {A B : Proposition Atom} (h : Derivable (@CS5ModalAxiom Atom) (A.imp B)) :
    Derivable (@CS5ModalAxiom Atom) ((◇A).imp (◇B)) :=
  cs5DerivDiaMono h

end Cslib.Logic.Modal
