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

/-- **Uncurry**: from `⊢ P ⊃ (Q ⊃ R)`, derive `⊢ (P ∧ Q) ⊃ R`. Built via nested `deductionTheorem`
discharge of the single hypothesis `P ∧ Q`, projecting `P`/`Q` via `andE1`/`andE2` before
re-applying the (weakened) curried fact. -/
private theorem cs5DerivUncurry {P Q R : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (P.imp (Q.imp R))) :
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
  have hd : DerivationTree (@CS5ModalAxiom Atom) [P.and Q] (P.imp (Q.imp R)) :=
    .weakening [] _ _ d (fun _ h => nomatch h)
  exact .modus_ponens _ _ _ (.modus_ponens _ _ _ hd hP) hQ

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

/-! ## Lemma 4.4 (page 9): `OutputCtx.fillFull` Congruence -/

/-- **Congruence between a curried implication and its and-uncurried instances, under a shared
extra conjunct `D`**: from `⊢ (Φ ⊃ Ψ) ⊃ (Φ' ⊃ Ψ')`, derive `⊢ ((Φ ∧ D) ⊃ Ψ) ⊃ ((Φ' ∧ D) ⊃ Ψ')`.
This is Lemma 4.4's singleton-context step, isolated as a standalone propositional fact: the
`(Φ ∧ D) ⊃ Ψ` shape is exactly `OutputCtx.fillFull [Γ₁] (Φ, Ψ)`'s `fm`-image (`D := Γ₁.fm`).
Built directly via three nested `deductionTheorem` discharges (the two and-hypotheses, then the
inner `Φ` needed to re-derive the curried antecedent `Φ ⊃ Ψ` from the assumed `(Φ ∧ D) ⊃ Ψ` and
the projected `D`). -/
private theorem cs5DerivAndImpCongr {Φ Ψ Φ' Ψ' : Proposition Atom} (D : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) ((Φ.imp Ψ).imp (Φ'.imp Ψ'))) :
    Derivable (@CS5ModalAxiom Atom) (((Φ.and D).imp Ψ).imp ((Φ'.and D).imp Ψ')) := by
  obtain ⟨dh⟩ := h
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] ((Φ.and D).imp Ψ) ((Φ'.and D).imp Ψ') ?_⟩
  refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [(Φ.and D).imp Ψ] (Φ'.and D) Ψ' ?_
  -- context: [Φ'.and D, (Φ.and D).imp Ψ]
  have hΦ' : DerivationTree (@CS5ModalAxiom Atom) [Φ'.and D, (Φ.and D).imp Ψ] Φ' :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE1 Φ' D)) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
  have hD : DerivationTree (@CS5ModalAxiom Atom) [Φ'.and D, (Φ.and D).imp Ψ] D :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE2 Φ' D)) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
  have hAntFact : DerivationTree (@CS5ModalAxiom Atom)
      [Φ'.and D, (Φ.and D).imp Ψ] ((Φ.and D).imp Ψ) :=
    .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have hΦImpΨ : DerivationTree (@CS5ModalAxiom Atom) [Φ'.and D, (Φ.and D).imp Ψ] (Φ.imp Ψ) := by
    refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      [Φ'.and D, (Φ.and D).imp Ψ] Φ Ψ ?_
    -- context: [Φ, Φ'.and D, (Φ.and D).imp Ψ]
    have hΦassum : DerivationTree (@CS5ModalAxiom Atom) [Φ, Φ'.and D, (Φ.and D).imp Ψ] Φ :=
      .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
    have hDweak : DerivationTree (@CS5ModalAxiom Atom) [Φ, Φ'.and D, (Φ.and D).imp Ψ] D :=
      .weakening [Φ'.and D, (Φ.and D).imp Ψ] _ _ hD (fun x hx => List.mem_cons_of_mem _ hx)
    have hAndΦD : DerivationTree (@CS5ModalAxiom Atom) [Φ, Φ'.and D, (Φ.and D).imp Ψ] (Φ.and D) :=
      .modus_ponens _ _ _ (.modus_ponens _ _ _
        (.weakening [] _ _ (.ax [] _ (.andI Φ D)) (fun _ h => nomatch h)) hΦassum) hDweak
    have hAntFactWeak : DerivationTree (@CS5ModalAxiom Atom)
        [Φ, Φ'.and D, (Φ.and D).imp Ψ] ((Φ.and D).imp Ψ) :=
      .weakening [Φ'.and D, (Φ.and D).imp Ψ] _ _ hAntFact (fun x hx => List.mem_cons_of_mem _ hx)
    exact .modus_ponens _ _ _ hAntFactWeak hAndΦD
  have hdWeak : DerivationTree (@CS5ModalAxiom Atom) [Φ'.and D, (Φ.and D).imp Ψ]
      ((Φ.imp Ψ).imp (Φ'.imp Ψ')) := .weakening [] _ _ dh (fun _ h => nomatch h)
  have hΦ'ImpΨ' : DerivationTree (@CS5ModalAxiom Atom) [Φ'.and D, (Φ.and D).imp Ψ] (Φ'.imp Ψ') :=
    .modus_ponens _ _ _ hdWeak hΦImpΨ
  exact .modus_ponens _ _ _ hΦ'ImpΨ' hΦ'

/-- **Lemma 4.4** (page 9): let `Δ, Σ` be full sequents and `Γ{ }` an output context. If
`fm(Δ) ⊃ fm(Σ)` is provable, so is `fm(Γ{Δ}) ⊃ fm(Γ{Σ})`. Proved by induction on the structure of
`Γ{ }` (`OutputCtx.fillFull`'s three-way recursion), matching the source's proof exactly: the base
case (`Γ = { }`) is `h` itself; the singleton case (`Γ = [Γ₁]`) is `cs5DerivAndImpCongr`
(Lemma 4.3(i)'s congruence pattern specialised to the and-uncurried shape `fillFull` produces); the
general case lifts the (structurally shorter) inductive hypothesis through `□`
(Lemma 4.3(iv)/`cs5DerivBoxMono`) and then through the new head layer via congruence-in-the-
consequent (Lemma 4.3(i)/`cs5DerivImpCongrRight`), mirroring `buildFullChain`'s own
`box Γ (buildFullChain rest ΦΨ)` step (via the `buildFullChain_fm` bridge from Lemma 4.2). -/
theorem lemma4_4 {Δ Θ : NestedFull Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (Δ.fm.imp Θ.fm)) :
    ∀ (Γ : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom) ((Γ.fillFull Δ).fm.imp (Γ.fillFull Θ).fm)
  | [] => h
  | [Γ₁] => cs5DerivAndImpCongr Γ₁.fm h
  | Γ :: (Γ₂ :: rest) => by
      have hIH := lemma4_4 h (Γ₂ :: rest)
      change Derivable (@CS5ModalAxiom Atom)
        ((Γ.fm.imp (buildFullChain (Γ₂ :: rest) Δ).fm).imp
          (Γ.fm.imp (buildFullChain (Γ₂ :: rest) Θ).fm))
      rw [buildFullChain_fm, buildFullChain_fm]
      exact cs5DerivImpCongrRight Γ.fm (cs5DerivBoxMono hIH)

/-! ## Lemma 4.5 (page 9): `InputCtx.fillLhs` Contravariant Congruence -/

/-- **Lemma 4.5** (page 9): let `Γ{ }` be an input context and `Δ, Σ` be LHS-sequents. If
`fm(Σ) ⊃ fm(Δ)` is provable, so is `fm(Γ{Δ}) ⊃ fm(Γ{Σ})`. This is *exactly* Phase 8's
`InputCtx.fillLhs_fm_antitone`: the source's own proof ("`Γ{ } = Γ'{Λ{ },Π}`... induction on
`Λ{ }`, using Lemma 4.3(iii) and (v) ... [then] Lemma 4.3(ii) ... [then] Lemma 4.4") is precisely
what `fillLhs_fm_antitone` already carries out, composed from `OutputCtx.fillLhs_fm_mono`
(Lemma 4.3(iii)/(v) induction on `Λ{ }`), `cs5DerivImpCongrLeft`-shaped reasoning
(Lemma 4.3(ii)), and `OutputCtx.fillRhs_fm_mono` (the outer `Γ'{ }` lift -- an RHS-typed
specialisation of this phase's own Lemma 4.4). Restated here under this phase's source
cross-reference, per this phase's task list ("using Phase 8's compositionality lemmas"). -/
theorem lemma4_5 (ctx : InputCtx Atom) {Δ Θ : NestedLhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (Θ.fm.imp Δ.fm)) :
    Derivable (@CS5ModalAxiom Atom) ((ctx.fillLhs Δ).fm.imp (ctx.fillLhs Θ).fm) :=
  InputCtx.fillLhs_fm_antitone ctx h

/-! ## Lemma 4.6 (page 9): Soundness of the One-Premise Rules

The source's proof handles nine named rules (`w, c, ∨°, □°, ◇°, ⊃°, ∧•, ◇•, □•`) via Lemma 4.4 or
Lemma 4.5, plus a case distinction for `□•`. This module lands the seven rules whose premise and
conclusion share a single filling operation (`InputCtx.fillLhs` throughout, or `OutputCtx.fillRhs`
throughout): `w` (Figure `(3.1)`'s weakening, stated generically since it is not yet a landed
`NestedProof` constructor -- Phase 19's `Admissibility.lean` territory), `c` (`contract`), `∨°`
(`orRLeft`/`orRRight`), `□°` (`boxR`), `∧•` (`andL`), and `◇•` (`diaL`).

**Deferred to Phase 12/13** (not landed here): `◇°` (`diaR`), `⊃°` (`impR`), and `□•`'s
case-split (`boxL`) all mix `OutputCtx.fillRhs`-shaped and `OutputCtx.fillFull`-shaped sides
within the *same* rule (the premise uses one filling operation, the conclusion the other, or the
rule's own components straddle the `Γ'{ }`/`Λ{ }` boundary of `Definition 2.3`). Bridging
`fillRhs`'s "no extra `∅`-layer" shape against `fillFull`'s "`∅`-comma-inserted" shape needs its
own induction (mirroring the `Λ = []`-restricted pattern `Nested/Translation.lean`'s
`InputCtx.fillEmpty_imp_outputPruning_fillRhs` already documents as a genuinely separate
sub-project, not a corollary of Lemma 4.4/4.5 alone) -- landing a half-finished or silently
restricted version here would misrepresent this phase's scope. Phase 12/13 build the actual
`nested_sound` case analysis directly against the `NestedProof` constructors and are better
positioned to close these three rules with whatever derivation their concrete instantiation
admits, rather than needing the fully general Lemma 4.6 statement first. -/

/-- **Self-and**: `⊢ P ⊃ (P ∧ P)`. -/
private theorem cs5DerivSelfAnd (P : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) (P.imp (P.and P)) := by
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) [] P (P.and P) ?_⟩
  have hP : DerivationTree (@CS5ModalAxiom Atom) [P] P :=
    .assumption [P] _ (List.mem_singleton.mpr rfl)
  exact .modus_ponens _ _ _
    (.modus_ponens _ _ _ (.weakening [] [P] _ (.ax [] _ (.andI P P)) (fun _ h => nomatch h)) hP) hP

/-- **Lemma 4.6, `w`**: `fm(Γ{∅}) ⊃ fm(Γ{Δ})`, for any input context `Γ{ }` and LHS-sequent `Δ`
(Figure `(3.1)`'s weakening rule; not yet a landed `NestedProof` constructor, see the module
docstring's "`NestedProof.mono`" discussion in `Rules.lean` -- Phase 19's job). -/
theorem lemma4_6_w (ctx : InputCtx Atom) (Δ : NestedLhs Atom) :
    Derivable (@CS5ModalAxiom Atom) ((ctx.fillLhs .empty).fm.imp (ctx.fillLhs Δ).fm) :=
  lemma4_5 ctx (Δ := .empty) (Θ := Δ) (cs5DerivTopIntro Δ.fm)

/-- **Lemma 4.6, `c`** (`contract`): `fm(Γ{Δ,Δ}) ⊃ fm(Γ{Δ})`. -/
theorem lemma4_6_c (ctx : InputCtx Atom) (Δ : NestedLhs Atom) :
    Derivable (@CS5ModalAxiom Atom) ((ctx.fillLhs (.comma Δ Δ)).fm.imp (ctx.fillLhs Δ).fm) :=
  lemma4_5 ctx (Δ := .comma Δ Δ) (Θ := Δ) (cs5DerivSelfAnd Δ.fm)

/-- **Lemma 4.6, `∨°`** (left injection, `orRLeft`): `fm(Γ{A°}) ⊃ fm(Γ{(A ∨ B)°})`. -/
theorem lemma4_6_orRLeft (ctx : OutputCtx Atom) (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((ctx.fillRhs (.atom A)).fm.imp (ctx.fillRhs (.atom (A.or B))).fm) :=
  OutputCtx.fillRhs_fm_mono
    (show Derivable (@CS5ModalAxiom Atom) ((NestedRhs.atom A).fm.imp (NestedRhs.atom (A.or B)).fm)
      from ⟨.ax [] _ (.orI1 A B)⟩) ctx

/-- **Lemma 4.6, `∨°`** (right injection, `orRRight`): `fm(Γ{B°}) ⊃ fm(Γ{(A ∨ B)°})`. -/
theorem lemma4_6_orRRight (ctx : OutputCtx Atom) (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((ctx.fillRhs (.atom B)).fm.imp (ctx.fillRhs (.atom (A.or B))).fm) :=
  OutputCtx.fillRhs_fm_mono
    (show Derivable (@CS5ModalAxiom Atom) ((NestedRhs.atom B).fm.imp (NestedRhs.atom (A.or B)).fm)
      from ⟨.ax [] _ (.orI2 A B)⟩) ctx

/-- **Lemma 4.6, `□°`** (`boxR`): `fm(Γ{[A°]}) ⊃ fm(Γ{□A°})`. -/
theorem lemma4_6_boxR (ctx : OutputCtx Atom) (A : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((ctx.fillRhs (.box .empty (.atom A))).fm.imp
        (ctx.fillRhs (.atom (Proposition.box A))).fm) :=
  OutputCtx.fillRhs_fm_mono (cs5DerivBoxMono cs5DerivTopImpElim) ctx

/-- **Lemma 4.6, `∧•`** (`andL`): `fm(Γ{A•,B•}) ⊃ fm(Γ{(A ∧ B)•})`. -/
theorem lemma4_6_andL (ctx : InputCtx Atom) (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((ctx.fillLhs (.comma (.atom A) (.atom B))).fm.imp (ctx.fillLhs (.atom (A.and B))).fm) :=
  lemma4_5 ctx (Δ := .comma (.atom A) (.atom B)) (Θ := .atom (A.and B)) (cs5DerivImpSelf (A.and B))

/-- **Lemma 4.6, `◇•`** (`diaL`): `fm(Γ{[A•]}) ⊃ fm(Γ{♦A•})`. -/
theorem lemma4_6_diaL (ctx : InputCtx Atom) (A : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((ctx.fillLhs (.dia (.atom A))).fm.imp
        (ctx.fillLhs (.atom (Proposition.diamond A))).fm) :=
  lemma4_5 ctx (Δ := .dia (.atom A)) (Θ := .atom (Proposition.diamond A))
    (cs5DerivImpSelf (Proposition.diamond A))

/-! ## Lemma 4.7 (page 10): Branching-Rule Congruence Facts

See the module docstring's "Lemma 4.7(i)/(ii): A Documented Source Duplication" section: both
parts share the same conclusion here. -/

/-- **`(D ⊃ ·)`-congruence under a shared hypothesis**: from `⊢ (A ∧ B) ⊃ C`, derive
`⊢ ((D ⊃ A) ∧ (D ⊃ B)) ⊃ (D ⊃ C)`, for any fixed `D`. Built directly via three nested
`deductionTheorem` discharges: the outer two project `D ⊃ A`/`D ⊃ B` from the assumed conjunction
and `D` from the innermost assumption, combine `A`/`B` via `andI`, then apply the (weakened)
hypothesis. This is Lemma 4.7(i) *and* (ii) (see the module docstring). -/
theorem lemma4_7_i_ii (D : Proposition Atom) {A B C : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((A.and B).imp C)) :
    Derivable (@CS5ModalAxiom Atom) (((D.imp A).and (D.imp B)).imp (D.imp C)) := by
  obtain ⟨d⟩ := h
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] ((D.imp A).and (D.imp B)) (D.imp C) ?_⟩
  refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [(D.imp A).and (D.imp B)] D C ?_
  -- context: [D, (D.imp A).and (D.imp B)]
  set Hyp := (D.imp A).and (D.imp B)
  have hHyp : DerivationTree (@CS5ModalAxiom Atom) [D, Hyp] Hyp :=
    .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have hD : DerivationTree (@CS5ModalAxiom Atom) [D, Hyp] D :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hDA : DerivationTree (@CS5ModalAxiom Atom) [D, Hyp] (D.imp A) :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE1 (D.imp A) (D.imp B)))
      (fun _ h => nomatch h)) hHyp
  have hDB : DerivationTree (@CS5ModalAxiom Atom) [D, Hyp] (D.imp B) :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE2 (D.imp A) (D.imp B)))
      (fun _ h => nomatch h)) hHyp
  have hA : DerivationTree (@CS5ModalAxiom Atom) [D, Hyp] A := .modus_ponens _ _ _ hDA hD
  have hB : DerivationTree (@CS5ModalAxiom Atom) [D, Hyp] B := .modus_ponens _ _ _ hDB hD
  have hAB : DerivationTree (@CS5ModalAxiom Atom) [D, Hyp] (A.and B) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (.andI A B)) (fun _ h => nomatch h)) hA) hB
  have hd : DerivationTree (@CS5ModalAxiom Atom) [D, Hyp] ((A.and B).imp C) :=
    .weakening [] _ _ d (fun _ h => nomatch h)
  exact .modus_ponens _ _ _ hd hAB

/-- **`□`-distributivity over `∧`**: `⊢ (□A ∧ □B) ⊃ □(A ∧ B)`, via necessitated `andI` composed
with the `k`-axiom, then uncurried. -/
private theorem cs5DerivBoxAndDistrib (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      (((Proposition.box A).and (Proposition.box B)).imp (Proposition.box (A.and B))) :=
  cs5DerivUncurry (cs5DerivImpTrans (cs5DerivBoxMono ⟨.ax [] _ (.andI A B)⟩)
    ⟨.ax [] _ (.k B (A.and B))⟩)

/-- **`□`-`◇` distributivity over `∧`**: `⊢ (□A ∧ ◇B) ⊃ ◇(A ∧ B)`, via necessitated `andI`
composed with the `kdia`-axiom, then uncurried. -/
private theorem cs5DerivBoxDiaDistrib (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      (((Proposition.box A).and (◇B)).imp (◇(A.and B))) :=
  cs5DerivUncurry (cs5DerivImpTrans (cs5DerivBoxMono ⟨.ax [] _ (.andI A B)⟩)
    ⟨.ax [] _ (.kdia B (A.and B))⟩)

/-- **Lemma 4.7(iii)**: from `⊢ (A ∧ B) ⊃ C`, derive `⊢ (□A ∧ □B) ⊃ □C`. -/
theorem lemma4_7_iii {A B C : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((A.and B).imp C)) :
    Derivable (@CS5ModalAxiom Atom)
      (((Proposition.box A).and (Proposition.box B)).imp (Proposition.box C)) :=
  cs5DerivImpTrans (cs5DerivBoxAndDistrib A B) (cs5DerivBoxMono h)

/-- **Lemma 4.7(iv)**: from `⊢ (A ∧ B) ⊃ C`, derive `⊢ (□A ∧ ◇B) ⊃ ◇C`. -/
theorem lemma4_7_iv {A B C : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((A.and B).imp C)) :
    Derivable (@CS5ModalAxiom Atom) (((Proposition.box A).and (◇B)).imp (◇C)) :=
  cs5DerivImpTrans (cs5DerivBoxDiaDistrib A B) (cs5DerivDiaMono h)

/-- **Two-hypothesis and-uncurry congruence, under a shared extra conjunct `D`**: from
`⊢ ((Φ₁ ⊃ Ψ₁) ∧ (Φ₂ ⊃ Ψ₂)) ⊃ (Φ₃ ⊃ Ψ₃)`, derive
`⊢ (((Φ₁ ∧ D) ⊃ Ψ₁) ∧ ((Φ₂ ∧ D) ⊃ Ψ₂)) ⊃ ((Φ₃ ∧ D) ⊃ Ψ₃)`. This is Lemma 4.8's singleton-context
step (the branching analogue of `cs5DerivAndImpCongr`): built via nested `deductionTheorem`
discharges of the outer and-hypothesis and `Φ₃ ∧ D`, reconstructing `Φ₁ ⊃ Ψ₁` and `Φ₂ ⊃ Ψ₂` each
via their own local discharge of `Φᵢ` (combined with the shared, already-available `D`) before
re-applying the (weakened) branching hypothesis. -/
private theorem cs5DerivAndImpCongr2 {Φ₁ Ψ₁ Φ₂ Ψ₂ Φ₃ Ψ₃ D : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom)
      (((Φ₁.imp Ψ₁).and (Φ₂.imp Ψ₂)).imp (Φ₃.imp Ψ₃))) :
    Derivable (@CS5ModalAxiom Atom)
      ((((Φ₁.and D).imp Ψ₁).and ((Φ₂.and D).imp Ψ₂)).imp ((Φ₃.and D).imp Ψ₃)) := by
  obtain ⟨dh⟩ := h
  set Hyp := ((Φ₁.and D).imp Ψ₁).and ((Φ₂.and D).imp Ψ₂)
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] Hyp ((Φ₃.and D).imp Ψ₃) ?_⟩
  refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [Hyp] (Φ₃.and D) Ψ₃ ?_
  -- context: [Φ₃.and D, Hyp]
  have hAndAssum : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] (Φ₃.and D) :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hΦ₃ : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] Φ₃ :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE1 Φ₃ D)) (fun _ h => nomatch h))
      hAndAssum
  have hD : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] D :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE2 Φ₃ D)) (fun _ h => nomatch h))
      hAndAssum
  have hHyp : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] Hyp :=
    .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have hH1 : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] ((Φ₁.and D).imp Ψ₁) :=
    .modus_ponens _ _ _ (.weakening [] _ _
      (.ax [] _ (.andE1 ((Φ₁.and D).imp Ψ₁) ((Φ₂.and D).imp Ψ₂))) (fun _ h => nomatch h)) hHyp
  have hH2 : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] ((Φ₂.and D).imp Ψ₂) :=
    .modus_ponens _ _ _ (.weakening [] _ _
      (.ax [] _ (.andE2 ((Φ₁.and D).imp Ψ₁) ((Φ₂.and D).imp Ψ₂))) (fun _ h => nomatch h)) hHyp
  have hΦ₁ImpΨ₁ : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] (Φ₁.imp Ψ₁) := by
    refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      [Φ₃.and D, Hyp] Φ₁ Ψ₁ ?_
    -- context: [Φ₁, Φ₃.and D, Hyp]
    have hΦ₁assum : DerivationTree (@CS5ModalAxiom Atom) [Φ₁, Φ₃.and D, Hyp] Φ₁ :=
      .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
    have hDweak : DerivationTree (@CS5ModalAxiom Atom) [Φ₁, Φ₃.and D, Hyp] D :=
      .weakening [Φ₃.and D, Hyp] _ _ hD (fun x hx => List.mem_cons_of_mem _ hx)
    have hAndΦ₁D : DerivationTree (@CS5ModalAxiom Atom) [Φ₁, Φ₃.and D, Hyp] (Φ₁.and D) :=
      .modus_ponens _ _ _ (.modus_ponens _ _ _
        (.weakening [] _ _ (.ax [] _ (.andI Φ₁ D)) (fun _ h => nomatch h)) hΦ₁assum) hDweak
    have hH1weak : DerivationTree (@CS5ModalAxiom Atom) [Φ₁, Φ₃.and D, Hyp] ((Φ₁.and D).imp Ψ₁) :=
      .weakening [Φ₃.and D, Hyp] _ _ hH1 (fun x hx => List.mem_cons_of_mem _ hx)
    exact .modus_ponens _ _ _ hH1weak hAndΦ₁D
  have hΦ₂ImpΨ₂ : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] (Φ₂.imp Ψ₂) := by
    refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      [Φ₃.and D, Hyp] Φ₂ Ψ₂ ?_
    -- context: [Φ₂, Φ₃.and D, Hyp]
    have hΦ₂assum : DerivationTree (@CS5ModalAxiom Atom) [Φ₂, Φ₃.and D, Hyp] Φ₂ :=
      .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
    have hDweak : DerivationTree (@CS5ModalAxiom Atom) [Φ₂, Φ₃.and D, Hyp] D :=
      .weakening [Φ₃.and D, Hyp] _ _ hD (fun x hx => List.mem_cons_of_mem _ hx)
    have hAndΦ₂D : DerivationTree (@CS5ModalAxiom Atom) [Φ₂, Φ₃.and D, Hyp] (Φ₂.and D) :=
      .modus_ponens _ _ _ (.modus_ponens _ _ _
        (.weakening [] _ _ (.ax [] _ (.andI Φ₂ D)) (fun _ h => nomatch h)) hΦ₂assum) hDweak
    have hH2weak : DerivationTree (@CS5ModalAxiom Atom) [Φ₂, Φ₃.and D, Hyp] ((Φ₂.and D).imp Ψ₂) :=
      .weakening [Φ₃.and D, Hyp] _ _ hH2 (fun x hx => List.mem_cons_of_mem _ hx)
    exact .modus_ponens _ _ _ hH2weak hAndΦ₂D
  have hAnd12 : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp]
      ((Φ₁.imp Ψ₁).and (Φ₂.imp Ψ₂)) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (.andI (Φ₁.imp Ψ₁) (Φ₂.imp Ψ₂))) (fun _ h => nomatch h))
      hΦ₁ImpΨ₁) hΦ₂ImpΨ₂
  have hdWeak : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp]
      (((Φ₁.imp Ψ₁).and (Φ₂.imp Ψ₂)).imp (Φ₃.imp Ψ₃)) := .weakening [] _ _ dh (fun _ h => nomatch h)
  have hΦ₃ImpΨ₃ : DerivationTree (@CS5ModalAxiom Atom) [Φ₃.and D, Hyp] (Φ₃.imp Ψ₃) :=
    .modus_ponens _ _ _ hdWeak hAnd12
  exact .modus_ponens _ _ _ hΦ₃ImpΨ₃ hΦ₃

/-! ## Lemma 4.8 (page 10): `OutputCtx` Branching Congruence -/

/-- **Lemma 4.8** (page 10): let `Δ₁, Δ₂, Σ` be full sequents and `Γ{ }` an output context. If
`(fm(Δ₁) ∧ fm(Δ₂)) ⊃ fm(Σ)` is provable, so is `(fm(Γ{Δ₁}) ∧ fm(Γ{Δ₂})) ⊃ fm(Γ{Σ})`. Proved by
induction on the structure of `Γ{ }`, using Lemma 4.7(i) and (iii), matching the source's proof
exactly. -/
theorem lemma4_8 {Δ₁ Δ₂ Θ : NestedFull Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((Δ₁.fm.and Δ₂.fm).imp Θ.fm)) :
    ∀ (Γ : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom)
        (((Γ.fillFull Δ₁).fm.and (Γ.fillFull Δ₂).fm).imp (Γ.fillFull Θ).fm)
  | [] => h
  | [Γ₁] => cs5DerivAndImpCongr2 (D := Γ₁.fm) h
  | Γ :: (Γ₂ :: rest) => by
      have hIH := lemma4_8 h (Γ₂ :: rest)
      change Derivable (@CS5ModalAxiom Atom)
        (((Γ.fm.imp (buildFullChain (Γ₂ :: rest) Δ₁).fm).and
            (Γ.fm.imp (buildFullChain (Γ₂ :: rest) Δ₂).fm)).imp
          (Γ.fm.imp (buildFullChain (Γ₂ :: rest) Θ).fm))
      rw [buildFullChain_fm, buildFullChain_fm, buildFullChain_fm]
      exact lemma4_7_i_ii Γ.fm (lemma4_7_iii hIH)

end Cslib.Logic.Modal
