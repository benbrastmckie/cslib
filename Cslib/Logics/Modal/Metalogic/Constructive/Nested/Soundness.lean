/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.Nested.Translation
public import Cslib.Logics.Modal.Metalogic.Constructive.Nested.Rules

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

## Lemma 4.7(i) and (ii): Distinct Statements

Page 10's Lemma 4.7 parts (i) and (ii) are **different formulas**, verified against a direct
render of page 10 (not just `pdftotext`, which independently corrupts this region by
dropping/misreading operator glyphs at exactly this position, consistent with this development's
already-documented `pdftotext` unreliability for this PDF's font encoding): (i) is "If `(A ∧ B) ⊃
C` is provable in `HCK+X`, then so is `((D ⊃ A) ∧ (D ⊃ B)) ⊃ (D ⊃ C)`"; (ii) is "If `(A ∧ B) ⊃ C`
is provable in `HCK+X`, then so is `((D ⊃ A) ∧ (D ∧ B)) ⊃ (D ∧ C)`" — `∧`/`⊃` glyphs render
cleanly in this PDF at this position, only `□` drops elsewhere. Both are landed as separate Lean
facts: `lemma4_7_i_ii` (which retains its identifier for call-site stability but covers part (i)
only) and `lemma4_7_ii` (part (ii)), matching Lemma 4.9's proof, which separately invokes "Lemma
4.7.(i)" (for Lemma 4.8's congruence, alongside part (iii)) and "Lemma 4.7.(ii)" (for the
`cut`-rule's chain argument, alongside part (iv)).

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

See the module docstring's "Lemma 4.7(i) and (ii): Distinct Statements" section: parts (i) and
(ii) are different formulas, each landed as its own Lean fact below. -/

/-- **`(D ⊃ ·)`-congruence under a shared hypothesis**: from `⊢ (A ∧ B) ⊃ C`, derive
`⊢ ((D ⊃ A) ∧ (D ⊃ B)) ⊃ (D ⊃ C)`, for any fixed `D`. Built directly via three nested
`deductionTheorem` discharges: the outer two project `D ⊃ A`/`D ⊃ B` from the assumed conjunction
and `D` from the innermost assumption, combine `A`/`B` via `andI`, then apply the (weakened)
hypothesis. This is Lemma 4.7(i) only; see `lemma4_7_ii` below for part (ii). The `_i_ii` suffix
is retained for call-site stability. -/
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

/-- **Lemma 4.7(ii)** (page 10): from `⊢ (A ∧ B) ⊃ C`, derive
`⊢ ((D ⊃ A) ∧ (D ∧ B)) ⊃ (D ∧ C)`, for any fixed `D`. Built via a single `deductionTheorem`
discharge of the conjunctive hypothesis `(D ⊃ A) ∧ (D ∧ B)`: `D` and `B` are extracted from its
second conjunct via `andE1`/`andE2`, `A` follows by `modus_ponens` against the first conjunct,
`A ∧ B` is recombined via `andI` and fed to the (weakened) hypothesis to obtain `C`, and `D ∧ C`
is rebuilt via a final `andI`. See [ArisakaDasStrassburger2015], §4, page 10. -/
theorem lemma4_7_ii (D : Proposition Atom) {A B C : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((A.and B).imp C)) :
    Derivable (@CS5ModalAxiom Atom) (((D.imp A).and (D.and B)).imp (D.and C)) := by
  obtain ⟨d⟩ := h
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] ((D.imp A).and (D.and B)) (D.and C) ?_⟩
  -- context: [(D.imp A).and (D.and B)]
  set Hyp := (D.imp A).and (D.and B)
  have hHyp : DerivationTree (@CS5ModalAxiom Atom) [Hyp] Hyp :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hDA : DerivationTree (@CS5ModalAxiom Atom) [Hyp] (D.imp A) :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE1 (D.imp A) (D.and B)))
      (fun _ h => nomatch h)) hHyp
  have hDandB : DerivationTree (@CS5ModalAxiom Atom) [Hyp] (D.and B) :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE2 (D.imp A) (D.and B)))
      (fun _ h => nomatch h)) hHyp
  have hD : DerivationTree (@CS5ModalAxiom Atom) [Hyp] D :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE1 D B)) (fun _ h => nomatch h)) hDandB
  have hB : DerivationTree (@CS5ModalAxiom Atom) [Hyp] B :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE2 D B)) (fun _ h => nomatch h)) hDandB
  have hA : DerivationTree (@CS5ModalAxiom Atom) [Hyp] A := .modus_ponens _ _ _ hDA hD
  have hAB : DerivationTree (@CS5ModalAxiom Atom) [Hyp] (A.and B) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (.andI A B)) (fun _ h => nomatch h)) hA) hB
  have hd : DerivationTree (@CS5ModalAxiom Atom) [Hyp] ((A.and B).imp C) :=
    .weakening [] _ _ d (fun _ h => nomatch h)
  have hC : DerivationTree (@CS5ModalAxiom Atom) [Hyp] C := .modus_ponens _ _ _ hd hAB
  exact .modus_ponens _ _ _
    (.modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andI D C)) (fun _ h => nomatch h)) hD) hC

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

/-! ## Lemma 4.9 (page 10): Soundness of the Branching Rules

The source's proof covers `∧°, ∨•, ⊃•, cut` uniformly via Lemma 4.8. This module lands the
`OutputCtx.fillRhs` branching lift (`buildRhsChain_fm_and`/`lemma4_9_fillRhs`, mirroring
`Nested/Translation.lean`'s `buildRhsChain_fm_mono`/`OutputCtx.fillRhs_fm_mono` shape exactly --
`fillRhs`'s single, uniform base case avoids the `fillFull`-style singleton-case and-uncurry step
Lemma 4.8 needed) and its concrete `∧°` (`andR`) corollary.

**Deferred to Phase 12/13/14** (not landed here): `∨•` (`orL`) needs a *branching, contravariant*
`InputCtx.fillLhs` lift -- a genuinely new combinator beyond `lemma4_9_fillRhs`'s covariant
`OutputCtx.fillRhs` shape, not a corollary of it. `⊃•` (`impL`) needs the source's own
induction-on-`n` argument over the `Λ{ }` chain (page 10's `L_X, L_Y, L_Z` construction),
substantially more machinery than this phase's remaining scope. `cut` is not yet a landed
`NestedProof` constructor (Phase 14's `Completeness.lean` territory) -- Lemma 4.9's `cut` case has
no consumer to serve yet. All three are better closed by Phase 12/13 (which build `nested_sound`'s
actual case analysis and can tailor the derivation to each rule's concrete instantiation) and
Phase 14 (which introduces `cut` itself). -/

/-- **Branching congruence for `buildRhsChain`**: from `⊢ (Ψ₁ ∧ Ψ₂) ⊃ Θ` (at the `fm` level),
derive `⊢ ((buildRhsChain l Ψ₁) ∧ (buildRhsChain l Ψ₂)) ⊃ (buildRhsChain l Θ)`, by induction on
`l` matching `buildRhsChain`'s own recursion (mirrors `Translation.lean`'s
`buildRhsChain_fm_mono`, using Lemma 4.7(i) in place of plain congruence-in-the-consequent since
this is the two-hypothesis case). -/
private theorem buildRhsChain_fm_and {Ψ₁ Ψ₂ Θ : NestedRhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((Ψ₁.fm.and Ψ₂.fm).imp Θ.fm)) :
    ∀ (l : List (NestedLhs Atom)),
      Derivable (@CS5ModalAxiom Atom)
        (((buildRhsChain l Ψ₁).fm.and (buildRhsChain l Ψ₂).fm).imp (buildRhsChain l Θ).fm)
  | [] => h
  | Γ :: rest => lemma4_7_iii (lemma4_7_i_ii Γ.fm (buildRhsChain_fm_and h rest))

/-- **`OutputCtx.fillRhs` branching lift**: from `⊢ (fm(Ψ₁) ∧ fm(Ψ₂)) ⊃ fm(Θ)`, derive
`⊢ (fm(Γ{Ψ₁}) ∧ fm(Γ{Ψ₂})) ⊃ fm(Γ{Θ})`, for every output context `Γ{ }`. Mirrors
`OutputCtx.fillRhs_fm_mono`'s two-case shape exactly (`ctx = []` against the fixed `⊤`
antecedent via Lemma 4.7(i); `ctx = Γ :: rest` via `buildRhsChain_fm_and` then Lemma 4.7(i)),
with no singleton special case needed (unlike Lemma 4.8's `OutputCtx.fillFull` version). -/
theorem lemma4_9_fillRhs {Ψ₁ Ψ₂ Θ : NestedRhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((Ψ₁.fm.and Ψ₂.fm).imp Θ.fm)) :
    ∀ (ctx : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom)
        (((ctx.fillRhs Ψ₁).fm.and (ctx.fillRhs Ψ₂).fm).imp (ctx.fillRhs Θ).fm)
  | [] => lemma4_7_i_ii Proposition.top h
  | Γ :: rest => lemma4_7_i_ii Γ.fm (buildRhsChain_fm_and h rest)

/-- **Lemma 4.9, `∧°`** (`andR`): `(fm(Γ{A°}) ∧ fm(Γ{B°})) ⊃ fm(Γ{(A ∧ B)°})`, via
`lemma4_9_fillRhs` and the trivially-provable `(A ∧ B) ⊃ (A ∧ B)`. -/
theorem lemma4_9_andR (ctx : OutputCtx Atom) (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      (((ctx.fillRhs (.atom A)).fm.and (ctx.fillRhs (.atom B)).fm).imp
        (ctx.fillRhs (.atom (A.and B))).fm) :=
  lemma4_9_fillRhs
    (show Derivable (@CS5ModalAxiom Atom)
      (((NestedRhs.atom A).fm.and (NestedRhs.atom B).fm).imp (NestedRhs.atom (A.and B)).fm)
      from cs5DerivImpSelf (A.and B)) ctx

/-! ## Theorem 4.1, First Half: Identity, Propositional, `⊥•`, Contraction Cases

This section opens the soundness theorem itself, `nested_sound : NestedProof Γ → Derivable
(@CS5ModalAxiom Atom) (fm Γ)` (stated in full and assembled in the sibling that discharges the
modal/structural cases): each `NestedProof` constructor gets its own **case lemma**, taking the
already-translated soundness fact(s) of its premise(s) as hypotheses and producing the conclusion's
soundness fact -- exactly the shape `nested_sound`'s eventual structural recursion consumes at each
constructor. Landed here: `botL`, `andL`, `andR`, `orRLeft`, `orRRight`, `impR`, `contract` (seven
of this phase's ten target constructors).

**`impR` resolved, not deferred**: Phase 11 flagged `impR` as needing "a genuinely separate
`fillRhs`-vs-`fillFull` empty-layer bridging induction." That induction is landed below
(`buildFullChain_imp_buildRhsChain`/`fillFull_imp_fillRhs`), using only `tBox`, curry/uncurry, and
`cs5DerivImpCongrRight`/`cs5DerivBoxMono` -- no new axiom needed, since `OutputCtx.fillFull` and
`OutputCtx.fillRhs`'s recursions both bottom out through `.box`, and `tBox` (`□X ⊃ X`) is exactly
the tool that reconciles the "extra box" `fillFull`'s base case carries.

**`id` and `orL`: repaired, not a genuine gap.** A follow-up defect-repair dispatch verified this
phase's diagnosis against the recovered source PDF directly (Figure 2, page 6; Lemma 4.2, page 9;
Lemma 4.8/4.9 and their proofs, page 10) and found the diagnosis **confirmed but the conclusion
sharpened**: the obstruction was not real mathematics but a Phase 9 over-generalization, for
*both* `id` and `orL`, with the identical root cause.

Figure 2 writes `id`'s and `⊥•`'s rules with the companion output formula *inside the same
braces* as the principal formula (`Γ{a•,a°}`, `Γ{⊥•,Π°}`), and Lemma 4.2 makes this precise:
*"let `Γ{ }` be an output context... `fm(Γ{a•,a°})`... [is] provable"* -- `Γ{ }` here is an
`OutputCtx`, filled via `OutputCtx.fillFull` with the pair as one full-sequent filler, not an
`InputCtx` with a separately-nested `Λ`. `∨•`'s rule (`Γ{A•,Π°}`/`Γ{B•,Π°}`/`Γ{A∨B•,Π°}`) uses the
*identical* braces-together notation, and Lemma 4.9's proof confirms the same reading: *"For the
`∧°`- and `∨•`-rules, this follows immediately from Lemma 4.8"* -- Lemma 4.8 is likewise stated
for `Γ{ }` an output context. Phase 9 instead encoded both `id` and `orL` via `InputCtx.fillLhs`
(the family that genuinely needs a separately-tracked, arbitrarily-nested `Λ`, correct for rules
like `∧•`/`⊃•`/`□•` whose Figure-2 notation shows *only* the principal formula, companion
elsewhere) -- a strictly more general reading than the paper's own rule, and the extra generality
is exactly what manufactured the apparent obstruction: `OutputCtx.fillLhs`'s recursion (unlike
`OutputCtx.fillFull`'s) inserts a genuine `.dia` past depth 1, and no dual axiom `◇X ⊃ X` exists
in `CS5ModalAxiom` (nor should it). Repaired in `Rules.lean`: `id` now takes
`(ctx : OutputCtx Atom) (a : Atom)` with conclusion `ctx.fillFull (a•,a•)`; `orL` now takes
`(ctx : OutputCtx Atom) (A B : Proposition Atom) (π : NestedRhs Atom)` with premises/conclusion
`ctx.fillFull (A•, π)` / `(B•, π)` / `((A∨B)•, π)`. Both are now closed below via `lemma4_2_id`
and `lemma4_8` respectively, already landed in this file for exactly this purpose (`lemma4_8`'s
own docstring: "Lemma 4.9's proof for `∧°`/`∨•` cites this lemma directly") -- **no `kdisj`, no new
axiom, and no diamond ever appears**, since both `OutputCtx.fillFull`'s and `lemma4_8`'s
recursions are box-only.

`⊥•` (`botL`) is *not* touched by this repair: it has the identical braces-together shape and the
identical `InputCtx`-vs-`OutputCtx` mismatch relative to Lemma 4.2's minimal scope, but the extra
generality it carries stays *true* (not merely provable-by-accident): `⊥` implies everything via
`efq` regardless of how many `◇`s wrap it, so `nested_sound_botL`'s existing proof (via
`lemma_botL_lambda_core`'s `◇`-bridging induction, closing with `cs5DerivDiaBotElim`) is a
strictly *stronger*, still-sound theorem -- a generalization that happens to remain true is not a
defect, so it is left exactly as Phase 12 landed it. -/

/-- **Disjunction elimination combinator**: from `⊢ A ⊃ C` and `⊢ B ⊃ C`, derive `⊢ (A ∨ B) ⊃ C`
(`orE`'s curried schema, applied via two `modus_ponens` steps). -/
private theorem cs5DerivOrElim {A B C : Proposition Atom}
    (hA : Derivable (@CS5ModalAxiom Atom) (A.imp C))
    (hB : Derivable (@CS5ModalAxiom Atom) (B.imp C)) :
    Derivable (@CS5ModalAxiom Atom) ((A.or B).imp C) := by
  obtain ⟨dA⟩ := hA
  obtain ⟨dB⟩ := hB
  have h1 : DerivationTree (@CS5ModalAxiom Atom) [] ((B.imp C).imp ((A.or B).imp C)) :=
    .modus_ponens _ _ _ (.ax [] _ (.orE A B C)) dA
  exact ⟨.modus_ponens _ _ _ h1 dB⟩

/-- **`◇⊥ ⊃ ⊥`**: derived via `efq` (`⊥ ⊃ □⊥`), `◇`-monotonicity, and `bDia` (`◇□X ⊃ X`). This is
the one place a "diamond can be shed" step *is* available in `CS5` -- because the target `⊥` is
absorbing under `efq`, not because `◇X ⊃ X` holds in general (see the module docstring's `id`/`orL`
discussion for why the general schema fails). -/
private theorem cs5DerivDiaBotElim :
    Derivable (@CS5ModalAxiom Atom) ((◇Proposition.bot).imp Proposition.bot) :=
  cs5DerivImpTrans
    (cs5DerivDiaMono
      (show Derivable (@CS5ModalAxiom Atom)
        (Proposition.bot.imp (Proposition.box Proposition.bot))
        from ⟨.ax [] _ (.efq (Proposition.box Proposition.bot))⟩))
    ⟨.ax [] _ (.bDia Proposition.bot)⟩

/-- If `⊢ Ψ.fm` is a closed theorem, then `⊢ (buildRhsChain l Ψ).fm` for every layer list `l`:
necessitate and constant-weaken (`cs5DerivImpOfDerivable`) one layer at a time, mirroring
`buildRhsChain_fm_mono`'s own recursion but starting from a closed fact rather than an
implication. -/
private theorem buildRhsChain_of_derivable {Ψ : NestedRhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) Ψ.fm) :
    ∀ (l : List (NestedLhs Atom)), Derivable (@CS5ModalAxiom Atom) (buildRhsChain l Ψ).fm
  | [] => h
  | Γ :: rest => by
      obtain ⟨d⟩ := cs5DerivImpOfDerivable Γ.fm (buildRhsChain_of_derivable h rest)
      exact ⟨.necessitation _ d⟩

/-- **Lifting a closed theorem through `OutputCtx.fillRhs`**: if `⊢ Ψ.fm`, then
`⊢ (ctx.fillRhs Ψ).fm` for every output context `ctx`. The `n = 0` case weakens through the fixed
`⊤` antecedent directly; the `n ≥ 1` case routes through `buildRhsChain_of_derivable`. -/
private theorem cs5DerivFillRhsOfDerivable {Ψ : NestedRhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) Ψ.fm) :
    ∀ (ctx : OutputCtx Atom), Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs Ψ).fm
  | [] => cs5DerivImpOfDerivable Proposition.top h
  | Γ :: rest => cs5DerivImpOfDerivable Γ.fm (buildRhsChain_of_derivable h rest)

/-- **Core fact for `⊥•`'s `Λ`-chain**: `fm(Λ.fillLhs ⊥•) ⊃ ⊥` for every output-context chain `Λ`
(`Observation 2.2`'s recursion for `OutputCtx.fillLhs`). Base/singleton cases are direct
(`efq`/`andE2`); the general case bridges the extra `◇` layer via `cs5DerivDiaMono` composed with
`cs5DerivDiaBotElim`. -/
private theorem lemma_botL_lambda_core :
    ∀ (Λ : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom) ((Λ.fillLhs (.atom Proposition.bot)).fm.imp Proposition.bot)
  | [] => cs5DerivImpSelf Proposition.bot
  | [Γ₁] => ⟨.ax [] _ (.andE2 Γ₁.fm Proposition.bot)⟩
  | Γ :: (Γ₂ :: rest) => by
      have hIH := lemma_botL_lambda_core (Γ₂ :: rest)
      have hstep : Derivable (@CS5ModalAxiom Atom)
          ((◇(OutputCtx.fillLhs (Γ₂ :: rest) (.atom Proposition.bot)).fm).imp Proposition.bot) :=
        cs5DerivImpTrans (cs5DerivDiaMono hIH) cs5DerivDiaBotElim
      exact cs5DerivImpTrans
        (⟨.ax [] _ (.andE2 Γ.fm _)⟩ :
          Derivable (@CS5ModalAxiom Atom)
            ((Γ.fm.and (◇(OutputCtx.fillLhs (Γ₂ :: rest) (.atom Proposition.bot)).fm)).imp
              (◇(OutputCtx.fillLhs (Γ₂ :: rest) (.atom Proposition.bot)).fm)))
        hstep

/-- **Soundness of `⊥•`** (Figure 2's `botL` axiom): `fm(Γ{⊥•,Π°})` is `CS5`-provable for every
input context `ctx`. Reduces to `lemma_botL_lambda_core` (bridging `ctx.Λ`'s `◇`-chain down to
`⊥`), composed with `efq` (`⊥ ⊃ ctx.π.fm`), necessitated, then lifted through `ctx.Γ'` via
`cs5DerivFillRhsOfDerivable`. -/
theorem nested_sound_botL (ctx : InputCtx Atom) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom Proposition.bot)).fm := by
  have hL : Derivable (@CS5ModalAxiom Atom)
      ((ctx.Λ.fillLhs (.atom Proposition.bot)).fm.imp ctx.π.fm) :=
    cs5DerivImpTrans (lemma_botL_lambda_core ctx.Λ) ⟨.ax [] _ (.efq ctx.π.fm)⟩
  obtain ⟨d⟩ := hL
  have hBox : Derivable (@CS5ModalAxiom Atom)
      (NestedRhs.box (ctx.Λ.fillLhs (.atom Proposition.bot)) ctx.π).fm := ⟨.necessitation _ d⟩
  exact cs5DerivFillRhsOfDerivable hBox ctx.Γ'

/-- **Soundness of `∧•`** (`andL`): from the premise's soundness fact, `modus_ponens` against
`lemma4_6_andL`. -/
theorem nested_sound_andL (ctx : InputCtx Atom) (A B : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.comma (.atom A) (.atom B))).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom (A.and B))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_6_andL ctx A B
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-- **Soundness of `∧°`** (`andR`): from both premises' soundness facts, combine via `andI` and
`modus_ponens` against `lemma4_9_andR`. -/
theorem nested_sound_andR (ctx : OutputCtx Atom) (A B : Proposition Atom)
    (hA : Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom A)).fm)
    (hB : Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom B)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom (A.and B))).fm := by
  obtain ⟨dA⟩ := hA
  obtain ⟨dB⟩ := hB
  obtain ⟨dimp⟩ := lemma4_9_andR ctx A B
  have hand : DerivationTree (@CS5ModalAxiom Atom) []
      ((ctx.fillRhs (.atom A)).fm.and (ctx.fillRhs (.atom B)).fm) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _ (.ax [] _ (.andI _ _)) dA) dB
  exact ⟨.modus_ponens _ _ _ dimp hand⟩

/-- **Soundness of `∨°`, left injection** (`orRLeft`): from the premise's soundness fact,
`modus_ponens` against `lemma4_6_orRLeft`. -/
theorem nested_sound_orRLeft (ctx : OutputCtx Atom) (A B : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom A)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom (A.or B))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_6_orRLeft ctx A B
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-- **Soundness of `∨°`, right injection** (`orRRight`): from the premise's soundness fact,
`modus_ponens` against `lemma4_6_orRRight`. -/
theorem nested_sound_orRRight (ctx : OutputCtx Atom) (A B : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom B)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom (A.or B))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_6_orRRight ctx A B
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-- **Soundness of `c`** (`contract`): from the premise's soundness fact, `modus_ponens` against
`lemma4_6_c`. -/
theorem nested_sound_contract (ctx : InputCtx Atom) (Δ : NestedLhs Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.comma Δ Δ)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs Δ).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_6_c ctx Δ
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-! ## `⊃°` (`impR`): the `fillFull`-vs-`fillRhs` Bridge

See the module docstring: this closes Phase 11's deferred `impR` case, using only `tBox` and
curry/uncurry combinators (no new axiom). -/

/-- **Curry, swapped order**: from `⊢ (P ∧ Q) ⊃ R`, derive `⊢ Q ⊃ (P ⊃ R)` (curry with the
projections taken in the opposite order from `cs5DerivCurry`, matching `impR`'s singleton-case
comma order `comma Φ Γ`, filler first). Built from the closed schema `cs5DerivCurrySwapSchema`. -/
private theorem cs5DerivCurrySwapSchema (P Q R : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) (((P.and Q).imp R).imp (Q.imp (P.imp R))) := by
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] ((P.and Q).imp R) (Q.imp (P.imp R)) ?_⟩
  refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [(P.and Q).imp R] Q (P.imp R) ?_
  refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [Q, (P.and Q).imp R] P R ?_
  -- context: [P, Q, (P.and Q).imp R]
  have hP : DerivationTree (@CS5ModalAxiom Atom) [P, Q, (P.and Q).imp R] P :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hQ : DerivationTree (@CS5ModalAxiom Atom) [P, Q, (P.and Q).imp R] Q :=
    .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have hHyp : DerivationTree (@CS5ModalAxiom Atom) [P, Q, (P.and Q).imp R] ((P.and Q).imp R) :=
    .assumption _ _
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))))
  have hand : DerivationTree (@CS5ModalAxiom Atom) [P, Q, (P.and Q).imp R] (P.and Q) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (.andI P Q)) (fun _ h => nomatch h)) hP) hQ
  exact .modus_ponens _ _ _ hHyp hand

/-- **`buildFullChain` implies `buildRhsChain`** (at the `A ⊃ B` translation): for every LHS-layer
list `l`, `fm(buildFullChain l (A•,B°)) ⊃ fm(buildRhsChain l ((A ⊃ B)°))`. Proved by induction on
`l` matching both chain-builders' own recursion: the base case is `tBox` (unwrapping the one extra
`□` `buildFullChain`'s `box Φ Ψ` clause carries that `buildRhsChain`'s bare `Ψ` clause does not);
the singleton case is `cs5DerivBoxMono (cs5DerivCurrySwapSchema ..)` (uncurrying under a box); the
general case lifts the (structurally shorter) inductive hypothesis through congruence-in-the-
consequent (`cs5DerivImpCongrRight`) then through `□` (`cs5DerivBoxMono`), mirroring both
chain-builders' shared `box Γ (chain rest ..)` step. -/
private theorem buildFullChain_imp_buildRhsChain (A B : Proposition Atom) :
    ∀ (l : List (NestedLhs Atom)),
      Derivable (@CS5ModalAxiom Atom)
        ((buildFullChain l (.atom A, .atom B)).fm.imp (buildRhsChain l (.atom (A.imp B))).fm)
  | [] => ⟨.ax [] _ (.tBox (A.imp B))⟩
  | [Γ] => cs5DerivBoxMono (cs5DerivCurrySwapSchema A Γ.fm B)
  | Γ :: (Γ₂ :: rest) =>
      cs5DerivBoxMono
        (cs5DerivImpCongrRight Γ.fm (buildFullChain_imp_buildRhsChain A B (Γ₂ :: rest)))

/-- **`OutputCtx.fillFull` implies `OutputCtx.fillRhs`** (at the `A ⊃ B` translation): for every
output context `ctx`, `fm(ctx.fillFull (A•,B°)) ⊃ fm(ctx.fillRhs ((A ⊃ B)°))`. Matches
`OutputCtx.fillFull`/`fillRhs`'s own three-way case split: `n = 0` is `implyK` (weakening through
the fixed `⊤` antecedent `fillRhs` inserts that `fillFull` does not); `n = 1` is
`cs5DerivCurrySwapSchema` directly (no box yet at this level); `n ≥ 2` routes through
`buildFullChain_imp_buildRhsChain`, lifted through the shared head layer `Γ` via
`cs5DerivImpCongrRight`. -/
private theorem fillFull_imp_fillRhs (ctx : OutputCtx Atom) (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((ctx.fillFull (.atom A, .atom B)).fm.imp (ctx.fillRhs (.atom (A.imp B))).fm) :=
  match ctx with
  | [] => ⟨.ax [] _ (.implyK (A.imp B) Proposition.top)⟩
  | [Γ] => cs5DerivCurrySwapSchema A Γ.fm B
  | Γ :: (Γ₂ :: rest) =>
      cs5DerivImpCongrRight Γ.fm (buildFullChain_imp_buildRhsChain A B (Γ₂ :: rest))

/-- **Soundness of `⊃°`** (`impR`): from the premise's soundness fact, `modus_ponens` against
`fillFull_imp_fillRhs`. Closes Phase 11's deferred `impR` case (see the module docstring). -/
theorem nested_sound_impR (ctx : OutputCtx Atom) (A B : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillFull (.atom A, .atom B)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom (A.imp B))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := fillFull_imp_fillRhs ctx A B
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-! ## `id` and `∨•` (`orL`): Closed via the Constructor Repair

See the module docstring's "`id` and `orL`: repaired, not a genuine gap" section: both
constructors now take an `OutputCtx` (not `InputCtx`) and fill via `.fillFull`, matching Lemma
4.2/4.8's own scope exactly, so both close directly from already-landed lemmas with no new
axiom. -/

/-- **Disjunction-elimination schema**: `⊢ ((A ⊃ C) ∧ (B ⊃ C)) ⊃ ((A ∨ B) ⊃ C)`, for arbitrary
`A, B, C` -- the closed propositional fact Lemma 4.9's proof cites for `∨•` ("provable formula
`((A ⊃ C) ∧ (B ⊃ C)) ⊃ ((A ∨ B) ⊃ C)`"), built via one `deductionTheorem` discharge of the
and-hypothesis, projecting `A ⊃ C`/`B ⊃ C` via `andE1`/`andE2` before applying the curried
`orE` axiom. -/
private theorem cs5DerivOrElimSchema (A B C : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) (((A.imp C).and (B.imp C)).imp ((A.or B).imp C)) := by
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] ((A.imp C).and (B.imp C)) ((A.or B).imp C) ?_⟩
  set Hyp := (A.imp C).and (B.imp C)
  have hHyp : DerivationTree (@CS5ModalAxiom Atom) [Hyp] Hyp :=
    .assumption _ _ (List.mem_singleton.mpr rfl)
  have hAC : DerivationTree (@CS5ModalAxiom Atom) [Hyp] (A.imp C) :=
    .modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (.andE1 (A.imp C) (B.imp C))) (fun _ h => nomatch h)) hHyp
  have hBC : DerivationTree (@CS5ModalAxiom Atom) [Hyp] (B.imp C) :=
    .modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (.andE2 (A.imp C) (B.imp C))) (fun _ h => nomatch h)) hHyp
  have hOrE : DerivationTree (@CS5ModalAxiom Atom) [Hyp] ((B.imp C).imp ((A.or B).imp C)) :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.orE A B C)) (fun _ h => nomatch h)) hAC
  exact .modus_ponens _ _ _ hOrE hBC

/-- **Soundness of `id`** (Figure 2's `id` axiom, repaired signature): `fm(ctx.fillFull (a•,a°))`
for every output context `ctx` and atom `a` -- exactly `lemma4_2_id`'s statement, Lemma 4.2's own
scope. -/
theorem nested_sound_id (ctx : OutputCtx Atom) (a : Atom) :
    Derivable (@CS5ModalAxiom Atom)
      (ctx.fillFull (.atom (.atom a), .atom (.atom a))).fm :=
  lemma4_2_id a ctx

/-- **Soundness of `∨•`** (`orL`, repaired signature): from both premises' soundness facts,
`fm(ctx.fillFull ((A ∨ B)•, π))`. Combines the closed `cs5DerivOrElimSchema` (instantiated at
`C := π.fm`) with Lemma 4.8's output-context lift (`lemma4_8`), then `modus_ponens` against the
premises' conjunction -- exactly Lemma 4.9's own proof for `∨•` ("this follows immediately from
Lemma 4.8"). No diamond ever appears (both `.fillFull` and `lemma4_8`'s recursions are box-only),
so no `kdisj`-like fact is needed. -/
theorem nested_sound_orL (ctx : OutputCtx Atom) (A B : Proposition Atom) (π : NestedRhs Atom)
    (hA : Derivable (@CS5ModalAxiom Atom) (ctx.fillFull (.atom A, π)).fm)
    (hB : Derivable (@CS5ModalAxiom Atom) (ctx.fillFull (.atom B, π)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillFull (.atom (A.or B), π)).fm := by
  obtain ⟨dA⟩ := hA
  obtain ⟨dB⟩ := hB
  obtain ⟨dimp⟩ :=
    lemma4_8 (Δ₁ := (.atom A, π)) (Δ₂ := (.atom B, π)) (Θ := (.atom (A.or B), π))
      (cs5DerivOrElimSchema A B π.fm) ctx
  have hand : DerivationTree (@CS5ModalAxiom Atom) []
      ((ctx.fillFull (.atom A, π)).fm.and (ctx.fillFull (.atom B, π)).fm) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _ (.ax [] _ (.andI _ _)) dA) dB
  exact ⟨.modus_ponens _ _ _ dimp hand⟩

/-! ## `□•`, `4•`, `b^[]`: `InputCtx.fillLhs`-Shaped Cases via Lemma 4.5

`boxL`, `fourL`, and `bStruct` all share the same shape as `contract`/`andL`/`diaL`/`tL`: both
premise and conclusion fill the *same* `InputCtx` via `.fillLhs`, differing only in the LHS
filler, so each closes via Lemma 4.5 (`InputCtx.fillLhs_fm_antitone`) composed with a single
closed propositional/modal fact. Despite the plan's anticipation of a `boxL` "case-split" (the
same kind of obstruction Phase 12 hit for `id`/`orL`), no case-split or new axiom is actually
needed: `boxL`'s premise-to-conclusion step is exactly Lemma 4.7(iv)'s `(□A ∧ ◇B) ⊃ ◇(A ∧ B)`
(`cs5DerivBoxDiaDistrib`, already landed for Lemma 4.7(iv)/Lemma 4.8), evaluated with `B :=
Δ.fm`. `fourL`/`bStruct` need the same fact with an extra `fourBox`/`bBox` step first (to turn
the already-boxed/bare leaf into the shape `cs5DerivBoxDiaDistrib` expects), landed below as two
small combinators reusing `cs5DerivBoxDiaDistrib` directly -- no `kdisj`, no new axiom, box-only
throughout (matching the `id`/`orL` repair's own "no diamond appears" pattern). -/

/-- **Congruence in the left conjunct**: from `⊢ a ⊃ a'`, derive `⊢ (a ∧ b) ⊃ (a' ∧ b)` (the
left-conjunct analogue of `cs5DerivAndCongrRight`, built by the identical proof shape with the
projections swapped). -/
private theorem cs5DerivAndCongrLeft {a a' : Proposition Atom} (b : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (a.imp a')) :
    Derivable (@CS5ModalAxiom Atom) ((a.and b).imp (a'.and b)) := by
  have h1 : Derivable (@CS5ModalAxiom Atom) ((a.and b).imp a') :=
    cs5DerivImpTrans ⟨.ax [] _ (.andE1 a b)⟩ h
  have h2 : Derivable (@CS5ModalAxiom Atom) ((a.and b).imp b) := ⟨.ax [] _ (.andE2 a b)⟩
  have step1 : Derivable (@CS5ModalAxiom Atom) ((a.and b).imp (b.imp (a'.and b))) :=
    cs5DerivImpTrans h1 ⟨.ax [] _ (.andI a' b)⟩
  obtain ⟨d1⟩ := step1
  obtain ⟨d2⟩ := h2
  exact ⟨.modus_ponens [] _ _
    (.modus_ponens [] _ _ (.ax [] _ (.implyS (a.and b) b (a'.and b))) d1) d2⟩

/-- **`4`-lifted `□`-`◇` distributivity**: `⊢ (□A ∧ ◇B) ⊃ ◇(□A ∧ B)`, for `fourL`'s already-boxed
leaf: lift `□A` to `□□A` via `fourBox` (congruence in the left conjunct), then apply
`cs5DerivBoxDiaDistrib` at `□A` (not `A`). -/
private theorem cs5DerivFourBoxDiaDistrib (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      (((Proposition.box A).and (◇B)).imp (◇((Proposition.box A).and B))) :=
  cs5DerivImpTrans (cs5DerivAndCongrLeft (◇B) ⟨.ax [] _ (.fourBox A)⟩)
    (cs5DerivBoxDiaDistrib (Proposition.box A) B)

/-- **`b`-lifted `□`-`◇` distributivity**: `⊢ (σ ∧ ◇D) ⊃ ◇(◇σ ∧ D)`, for `bStruct`'s symmetric
structural step: lift `σ` to `□◇σ` via `bBox` (congruence in the left conjunct), then apply
`cs5DerivBoxDiaDistrib` at `◇σ`. -/
private theorem cs5DerivBStructDistrib (σ D : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) ((σ.and (◇D)).imp (◇((◇σ).and D))) :=
  cs5DerivImpTrans (cs5DerivAndCongrLeft (◇D) ⟨.ax [] _ (.bBox σ)⟩)
    (cs5DerivBoxDiaDistrib (◇σ) D)

/-- **Soundness of `□•`** (`boxL`): from the premise's soundness fact, `modus_ponens` against
Lemma 4.5 instantiated with `cs5DerivBoxDiaDistrib A Δ.fm`. No case-split needed (see the section
docstring above). -/
theorem nested_sound_boxL (ctx : InputCtx Atom) (A : Proposition Atom) (Δ : NestedLhs Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.dia (.comma (.atom A) Δ))).fm) :
    Derivable (@CS5ModalAxiom Atom)
      (ctx.fillLhs (.comma (.atom (Proposition.box A)) (.dia Δ))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_5 ctx
    (Δ := .dia (.comma (.atom A) Δ)) (Θ := .comma (.atom (Proposition.box A)) (.dia Δ))
    (cs5DerivBoxDiaDistrib A Δ.fm)
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-- **Soundness of `4•`**: from the premise's soundness fact, `modus_ponens` against Lemma 4.5
instantiated with `cs5DerivFourBoxDiaDistrib A Δ.fm`. -/
theorem nested_sound_fourL (ctx : InputCtx Atom) (A : Proposition Atom) (Δ : NestedLhs Atom)
    (h : Derivable (@CS5ModalAxiom Atom)
      (ctx.fillLhs (.dia (.comma (.atom (Proposition.box A)) Δ))).fm) :
    Derivable (@CS5ModalAxiom Atom)
      (ctx.fillLhs (.comma (.atom (Proposition.box A)) (.dia Δ))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_5 ctx
    (Δ := .dia (.comma (.atom (Proposition.box A)) Δ))
    (Θ := .comma (.atom (Proposition.box A)) (.dia Δ))
    (cs5DerivFourBoxDiaDistrib A Δ.fm)
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-- **Soundness of `b^[]`**: from the premise's soundness fact, `modus_ponens` against Lemma 4.5
instantiated with `cs5DerivBStructDistrib σ.fm Δ.fm`. -/
theorem nested_sound_bStruct (ctx : InputCtx Atom) (σ Δ : NestedLhs Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.dia (.comma (.dia σ) Δ))).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.comma σ (.dia Δ))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_5 ctx
    (Δ := .dia (.comma (.dia σ) Δ)) (Θ := .comma σ (.dia Δ))
    (cs5DerivBStructDistrib σ.fm Δ.fm)
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-! ## `□°`, `♦•`: Closing Phase 11's Landed Lemma 4.6 Cases

`lemma4_6_boxR`/`lemma4_6_diaL` were already landed in Phase 11; this section supplies their
`nested_sound` wrappers. -/

/-- **Soundness of `□°`** (`boxR`): from the premise's soundness fact, `modus_ponens` against
`lemma4_6_boxR`. -/
theorem nested_sound_boxR (ctx : OutputCtx Atom) (A : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.box .empty (.atom A))).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom (Proposition.box A))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_6_boxR ctx A
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-- **Soundness of `♦•`** (`diaL`): from the premise's soundness fact, `modus_ponens` against
`lemma4_6_diaL`. -/
theorem nested_sound_diaL (ctx : InputCtx Atom) (A : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.dia (.atom A))).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom (Proposition.diamond A))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_6_diaL ctx A
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-! ## `t°`, `t•`: the `NCS5` `T`-Axiom Rules

Both are single-filling-operation rules (`OutputCtx.fillRhs` for `t°`, `InputCtx.fillLhs` for
`t•`), closing directly from `tDia`/`tBox` via `OutputCtx.fillRhs_fm_mono`/Lemma 4.5, the same
pattern `orRLeft`/`andL`'s family already established. -/

/-- **Soundness of `t°`** (`tR`): from the premise's soundness fact, `modus_ponens` against
`OutputCtx.fillRhs_fm_mono` instantiated with `tDia`. -/
theorem nested_sound_tR (ctx : OutputCtx Atom) (A : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom A)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.atom (Proposition.diamond A))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := OutputCtx.fillRhs_fm_mono
    (show Derivable (@CS5ModalAxiom Atom)
      ((NestedRhs.atom A).fm.imp (NestedRhs.atom (Proposition.diamond A)).fm)
      from ⟨.ax [] _ (.tDia A)⟩) ctx
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-- **Soundness of `t•`** (`tL`): from the premise's soundness fact, `modus_ponens` against Lemma
4.5 instantiated with `tBox`. -/
theorem nested_sound_tL (ctx : InputCtx Atom) (A : Proposition Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom A)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom (Proposition.box A))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := lemma4_5 ctx (Δ := .atom A) (Θ := .atom (Proposition.box A))
    ⟨.ax [] _ (.tBox A)⟩
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-! ## `◇°` (`diaR`) and `4°` (`fourR`): the `fillRhs`-vs-`fillFull` Bridge, `kdia`-Flavoured

Both rules mix an `OutputCtx.fillRhs`-shaped premise (`Γ{[Δ,A°]}` / `Γ{[Δ,◇A°]}`) against a
`OutputCtx.fillFull`-shaped conclusion (`Γ{◇A°,[Δ]}`), the same family of obstruction Phase 11
deferred `impR` for (closed in this file's earlier section via `tBox` + curry/uncurry). Here the
modal content is `kdia` (`□(φ⊃ψ) ⊃ (◇φ⊃◇ψ)`) rather than `tBox`, since the leaf is genuinely
being *lifted* through a `◇` (not merely unwrapped): `Γ{[Δ,A°]}` (bare `A` reachable behind the
bracket) implies `Γ{◇A°,[Δ]}` (`◇A` reachable directly), matching `kdia`'s own shape exactly.
`fourR` additionally needs one `fourDia` (`◇◇A ⊃ ◇A`) step, since its leaf is already `◇A`
(`kdia` alone would only reach `◇◇A`). Neither needs a case-split or new axiom. -/

/-- **`kdia`-flavoured uncurry-swap schema**: `⊢ (Γ ⊃ □(Δ ⊃ A)) ⊃ ((◇Δ ∧ Γ) ⊃ ◇A)`, for arbitrary
`Γ, Δ, A` -- the closed schema `diaR`'s (and `fourR`'s) singleton-`ctx` case reduces to, built by
discharging the antecedent `Γ ⊃ □(Δ⊃A)` and the conjunction `◇Δ ∧ Γ` in turn, then composing the
projected `Γ` through the antecedent and `kdia` in sequence. -/
private theorem cs5DerivKdiaUncurrySwapSchema (Γ Δ A : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((Γ.imp (Proposition.box (Δ.imp A))).imp (((◇Δ).and Γ).imp (◇A))) := by
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] (Γ.imp (Proposition.box (Δ.imp A))) (((◇Δ).and Γ).imp (◇A)) ?_⟩
  refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [Γ.imp (Proposition.box (Δ.imp A))] ((◇Δ).and Γ) (◇A) ?_
  -- context: [(◇Δ).and Γ, Γ.imp (Proposition.box (Δ.imp A))]
  set H := Γ.imp (Proposition.box (Δ.imp A))
  have hAnd : DerivationTree (@CS5ModalAxiom Atom) [(◇Δ).and Γ, H] ((◇Δ).and Γ) :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hDiaΔ : DerivationTree (@CS5ModalAxiom Atom) [(◇Δ).and Γ, H] (◇Δ) :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE1 (◇Δ) Γ)) (fun _ h => nomatch h)) hAnd
  have hΓ : DerivationTree (@CS5ModalAxiom Atom) [(◇Δ).and Γ, H] Γ :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE2 (◇Δ) Γ)) (fun _ h => nomatch h)) hAnd
  have hH : DerivationTree (@CS5ModalAxiom Atom) [(◇Δ).and Γ, H] H :=
    .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have hBox : DerivationTree (@CS5ModalAxiom Atom) [(◇Δ).and Γ, H] (Proposition.box (Δ.imp A)) :=
    .modus_ponens _ _ _ hH hΓ
  have hKdia : DerivationTree (@CS5ModalAxiom Atom) [(◇Δ).and Γ, H]
      ((Proposition.box (Δ.imp A)).imp ((◇Δ).imp (◇A))) :=
    .weakening [] _ _ (.ax [] _ (.kdia Δ A)) (fun _ h => nomatch h)
  have hDiaImp : DerivationTree (@CS5ModalAxiom Atom) [(◇Δ).and Γ, H] ((◇Δ).imp (◇A)) :=
    .modus_ponens _ _ _ hKdia hBox
  exact .modus_ponens _ _ _ hDiaImp hDiaΔ

/-- **`buildRhsChain`/`buildFullChain` bridge, `diaR`'s inner recursion**: for every nonempty
tail `Γ₂ :: rest`, `⊢ (buildRhsChain (Γ₂::rest) [Δ,A°]).fm ⊃ (buildFullChain (Γ₂::rest) (◇Δ,A°)).fm`
(with the conclusion's leaf already diamond-wrapped as `◇A`, since this bridges into `diaR`'s
own conclusion). Indexed by an explicit head/tail pair (never a bare `l`, which would force an
unneeded and false
`l = []` case -- see the module's design note): the base case (`rest = []`) is
`cs5DerivKdiaUncurrySwapSchema` under one `□` (`cs5DerivBoxMono`); the general case lifts the
(structurally shorter) inductive hypothesis through congruence-in-the-consequent then `□`,
mirroring `buildFullChain_imp_buildRhsChain`'s own recursion shape. -/
private theorem buildRhsChain_imp_buildFullChain_dia (Δ : NestedLhs Atom) (A : Proposition Atom) :
    ∀ (Γ₂ : NestedLhs Atom) (rest : List (NestedLhs Atom)),
      Derivable (@CS5ModalAxiom Atom)
        ((buildRhsChain (Γ₂ :: rest) (.box Δ (.atom A))).fm.imp
          (buildFullChain (Γ₂ :: rest) (.dia Δ, .atom (Proposition.diamond A))).fm)
  | Γ₂, [] => cs5DerivBoxMono (cs5DerivKdiaUncurrySwapSchema Γ₂.fm Δ.fm A)
  | Γ₂, (Γ₃ :: rest) =>
      cs5DerivBoxMono
        (cs5DerivImpCongrRight Γ₂.fm (buildRhsChain_imp_buildFullChain_dia Δ A Γ₃ rest))

/-- **`fillRhs` implies `fillFull`, `◇°`-flavoured**: for every output context `ctx`,
`⊢ fm(ctx.fillRhs [Δ,A°]) ⊃ fm(ctx.fillFull (◇Δ°,A°))`. Matches `ctx`'s three-way case split
exactly like `fillFull_imp_fillRhs`: `n = 0` composes `cs5DerivTopImpElim` with `kdia` directly;
`n = 1` is `cs5DerivKdiaUncurrySwapSchema` directly (no box yet); `n ≥ 2` routes through
`buildRhsChain_imp_buildFullChain_dia`, lifted through the shared head layer via
`cs5DerivImpCongrRight`. -/
private theorem fillRhs_imp_fillFull_dia (ctx : OutputCtx Atom) (Δ : NestedLhs Atom)
    (A : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((ctx.fillRhs (.box Δ (.atom A))).fm.imp
        (ctx.fillFull (.dia Δ, .atom (Proposition.diamond A))).fm) :=
  match ctx with
  | [] => cs5DerivImpTrans cs5DerivTopImpElim ⟨.ax [] _ (.kdia Δ.fm A)⟩
  | [Γ] => cs5DerivKdiaUncurrySwapSchema Γ.fm Δ.fm A
  | Γ :: (Γ₂ :: rest) =>
      cs5DerivImpCongrRight Γ.fm (buildRhsChain_imp_buildFullChain_dia Δ A Γ₂ rest)

/-- **Soundness of `◇°`** (`diaR`): from the premise's soundness fact, `modus_ponens` against
`fillRhs_imp_fillFull_dia`. -/
theorem nested_sound_diaR (ctx : OutputCtx Atom) (A : Proposition Atom) (Δ : NestedLhs Atom)
    (h : Derivable (@CS5ModalAxiom Atom) (ctx.fillRhs (.box Δ (.atom A))).fm) :
    Derivable (@CS5ModalAxiom Atom)
      (ctx.fillFull (.dia Δ, .atom (Proposition.diamond A))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := fillRhs_imp_fillFull_dia ctx Δ A
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-- **`buildRhsChain`/`buildFullChain` bridge, `fourR`'s inner recursion**: identical shape to
`buildRhsChain_imp_buildFullChain_dia`, with the leaf fixed at `◇A` (already diamond-wrapped): the
base case additionally composes `fourDia` (`◇◇A ⊃ ◇A`) after `cs5DerivKdiaUncurrySwapSchema`'s
`◇◇A`-ending conclusion, descending to plain `◇A`. -/
private theorem buildRhsChain_imp_buildFullChain_four (Δ : NestedLhs Atom) (A : Proposition Atom) :
    ∀ (Γ₂ : NestedLhs Atom) (rest : List (NestedLhs Atom)),
      Derivable (@CS5ModalAxiom Atom)
        ((buildRhsChain (Γ₂ :: rest) (.box Δ (.atom (Proposition.diamond A)))).fm.imp
          (buildFullChain (Γ₂ :: rest) (.dia Δ, .atom (Proposition.diamond A))).fm)
  | Γ₂, [] =>
      cs5DerivBoxMono
        (cs5DerivImpTrans (cs5DerivKdiaUncurrySwapSchema Γ₂.fm Δ.fm (Proposition.diamond A))
          (cs5DerivImpCongrRight ((◇Δ.fm).and Γ₂.fm) ⟨.ax [] _ (.fourDia A)⟩))
  | Γ₂, (Γ₃ :: rest) =>
      cs5DerivBoxMono
        (cs5DerivImpCongrRight Γ₂.fm (buildRhsChain_imp_buildFullChain_four Δ A Γ₃ rest))

/-- **`fillRhs` implies `fillFull`, `4°`-flavoured**: for every output context `ctx`,
`⊢ fm(ctx.fillRhs [Δ,◇A°]) ⊃ fm(ctx.fillFull (◇Δ°,◇A°))`. Same three-way case split as
`fillRhs_imp_fillFull_dia`, each arm additionally composing `fourDia` to descend from `◇◇A` to
`◇A`. -/
private theorem fillRhs_imp_fillFull_four (ctx : OutputCtx Atom) (Δ : NestedLhs Atom)
    (A : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((ctx.fillRhs (.box Δ (.atom (Proposition.diamond A)))).fm.imp
        (ctx.fillFull (.dia Δ, .atom (Proposition.diamond A))).fm) :=
  match ctx with
  | [] => cs5DerivImpTrans cs5DerivTopImpElim
      (cs5DerivImpTrans ⟨.ax [] _ (.kdia Δ.fm (Proposition.diamond A))⟩
        (cs5DerivImpCongrRight (◇Δ.fm) ⟨.ax [] _ (.fourDia A)⟩))
  | [Γ] => cs5DerivImpTrans (cs5DerivKdiaUncurrySwapSchema Γ.fm Δ.fm (Proposition.diamond A))
      (cs5DerivImpCongrRight ((◇Δ.fm).and Γ.fm) ⟨.ax [] _ (.fourDia A)⟩)
  | Γ :: (Γ₂ :: rest) =>
      cs5DerivImpCongrRight Γ.fm (buildRhsChain_imp_buildFullChain_four Δ A Γ₂ rest)

/-- **Soundness of `4°`** (`fourR`): from the premise's soundness fact, `modus_ponens` against
`fillRhs_imp_fillFull_four`. -/
theorem nested_sound_fourR (ctx : OutputCtx Atom) (A : Proposition Atom) (Δ : NestedLhs Atom)
    (h : Derivable (@CS5ModalAxiom Atom)
      (ctx.fillRhs (.box Δ (.atom (Proposition.diamond A)))).fm) :
    Derivable (@CS5ModalAxiom Atom)
      (ctx.fillFull (.dia Δ, .atom (Proposition.diamond A))).fm := by
  obtain ⟨d⟩ := h
  obtain ⟨dimp⟩ := fillRhs_imp_fillFull_four ctx Δ A
  exact ⟨.modus_ponens _ _ _ dimp d⟩

/-! ## Λ-Chain Toolkit (Lemma 4.9, `⊃•`)

Four small propositional combinators consumed by the `⊃•` (`impL`) induction and its assembly
(next section): `mpAnd`/`topBase` are the base-case ingredients `lambdaChain_XZ_imp_Y` composes
with `lemma4_7_ii` at `Λ = []`/`Λ = [Λ₀]`; `andMP` is the closed-derivation `andI`+MP combinator
the final `impL` assembly applies; `lambdaChain_step2` is the source's own second step, "But this
follows from `(L_X ∧ L_Z) ⊃ L_Y`" (page 10). See [ArisakaDasStrassburger2015], §4, page 10. -/

/-- `⊢ (A ∧ (A ⊃ B)) ⊃ B`: modus ponens uncurried into a single conjunction. Built via
`cs5DerivUncurrySwap` fed the identity `⊢ (A ⊃ B) ⊃ (A ⊃ B)` -- the `Q ⊃ (P ⊃ R)` shape
`cs5DerivUncurrySwap` expects collapses to `cs5DerivImpSelf` exactly when `Q = P.imp R`. -/
private theorem mpAnd (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) ((A.and (A.imp B)).imp B) :=
  cs5DerivUncurrySwap (cs5DerivImpSelf (A.imp B))

/-- `⊢ ((⊤ ⊃ A) ∧ (A ⊃ B)) ⊃ B`: `mpAnd`'s `Λ = []` variant, with the left conjunct's `A`
replaced by `⊤ ⊃ A` (the `fillRhs []`/degenerate-chain antecedent). Built by curry-ing `mpAnd`
into `⊢ A ⊃ ((A ⊃ B) ⊃ B)`, composing with `cs5DerivTopImpElim : ⊢ (⊤ ⊃ A) ⊃ A` via transitivity,
then uncurry-ing back into the conjunctive shape. -/
private theorem topBase (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) (((Proposition.top.imp A).and (A.imp B)).imp B) :=
  cs5DerivUncurry (cs5DerivImpTrans cs5DerivTopImpElim (cs5DerivCurry (mpAnd A B)))

/-- **Closed `andI` + modus ponens combinator**: from `⊢ (U ∧ V) ⊃ W`, `⊢ U`, and `⊢ V`, derive
`⊢ W`. Used by the `impL` assembly to combine the branching-lift fact against its two premises. -/
private theorem andMP {U V W : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((U.and V).imp W))
    (hU : Derivable (@CS5ModalAxiom Atom) U) (hV : Derivable (@CS5ModalAxiom Atom) V) :
    Derivable (@CS5ModalAxiom Atom) W := by
  obtain ⟨d⟩ := h
  obtain ⟨dU⟩ := hU
  obtain ⟨dV⟩ := hV
  exact ⟨.modus_ponens _ _ _ d
    (.modus_ponens _ _ _ (.modus_ponens _ _ _ (.ax [] _ (.andI U V)) dU) dV)⟩

/-- **The source's step 2** (page 10): "To be able to apply Lemma 4.8, we need to show that
`(L_X ∧ (L_Y ⊃ P)) ⊃ (L_Z ⊃ P)` is provable in `HCK + X`. But this follows from
`(L_X ∧ L_Z) ⊃ L_Y`". From `⊢ (X ∧ Z) ⊃ Y`, derive `⊢ (X ∧ (Y ⊃ P)) ⊃ (Z ⊃ P)`. Built via two
nested `deductionTheorem` discharges (of the conjunction `X ∧ (Y ⊃ P)`, then of `Z`): `X`/`Y ⊃ P`
are projected from the conjunction via `andE1`/`andE2`, recombined with `Z` via `andI` into
`X ∧ Z`, fed to the (weakened) hypothesis to obtain `Y`, then discharged against `Y ⊃ P` to
reach `P`. See [ArisakaDasStrassburger2015], §4, page 10. -/
theorem lambdaChain_step2 {X Y Z P : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((X.and Z).imp Y)) :
    Derivable (@CS5ModalAxiom Atom) ((X.and (Y.imp P)).imp (Z.imp P)) := by
  obtain ⟨d⟩ := h
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] (X.and (Y.imp P)) (Z.imp P) ?_⟩
  refine deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [X.and (Y.imp P)] Z P ?_
  -- context: [Z, X.and (Y.imp P)]
  set Hyp := X.and (Y.imp P)
  have hHyp : DerivationTree (@CS5ModalAxiom Atom) [Z, Hyp] Hyp :=
    .assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have hZ : DerivationTree (@CS5ModalAxiom Atom) [Z, Hyp] Z :=
    .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
  have hX : DerivationTree (@CS5ModalAxiom Atom) [Z, Hyp] X :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE1 X (Y.imp P))) (fun _ h => nomatch h))
      hHyp
  have hYimpP : DerivationTree (@CS5ModalAxiom Atom) [Z, Hyp] (Y.imp P) :=
    .modus_ponens _ _ _ (.weakening [] _ _ (.ax [] _ (.andE2 X (Y.imp P))) (fun _ h => nomatch h))
      hHyp
  have hXZ : DerivationTree (@CS5ModalAxiom Atom) [Z, Hyp] (X.and Z) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (.andI X Z)) (fun _ h => nomatch h)) hX) hZ
  have hd : DerivationTree (@CS5ModalAxiom Atom) [Z, Hyp] ((X.and Z).imp Y) :=
    .weakening [] _ _ d (fun _ h => nomatch h)
  have hY : DerivationTree (@CS5ModalAxiom Atom) [Z, Hyp] Y := .modus_ponens _ _ _ hd hXZ
  exact .modus_ponens _ _ _ hYimpP hY

/-! ## The Λ-Chain Induction (Lemma 4.9, `⊃•`)

**The `Λ{ }`-chain induction** the task is named for. Page 10: "let `Λ{ } = Λ0, [Λ1, [. . . ,
[Λn, { }] . . .]]`. Now let `P = fm(Π◦)` and `Li = fm(Λi)` for `i = 0 . . . n`, and let
`LX = fm(Λ{A◦})`, `LY = fm(Λ{B•})`, `LZ = fm(Λ{A ⊃ B•})` ... `(LX ∧ LZ) ⊃ LY`, which can be
shown provable in `HCK + X` using an induction on `n` together with Lemma 4.7.(ii) and (iv)."
See [ArisakaDasStrassburger2015], §4, page 10.

**Induction motive, spelled out.** The recursion is structural on the `OutputCtx` list `Λ`,
using the file's established **three-way** split (`[]` / `[Λ₀]` / `Λ₀ :: Λ₁ :: rest`) — the same
split `OutputCtx.fillLhs` itself recurses on, and the same one `OutputCtx.fillLhs_fm_mono` and
`lemma4_8` already use. The motive is

`P(Λ) := ⊢ ((Λ.fillRhs A°).fm ∧ (Λ.fillLhs (A⊃B)•).fm) ⊃ (Λ.fillLhs B•).fm`

with `A`, `B` **fixed outside** the recursion (they are parameters, not part of the motive), and
the recursive call taken at the structurally smaller `Λ₁ :: rest`. Reading the three cases against
the source's `Λ{ } = Λ0, [Λ1, [. . . , [Λn, { }] . . .]]`: `[]` is the degenerate `Λ{ } = { }` (the
source's `n = 0` with no `Λ0` layer, where `fillRhs` supplies the `⊤` antecedent), `[Λ₀]` is
`n = 0`, and `Λ₀ :: Λ₁ :: rest` is `n ≥ 1`.

The cons-cons step relies on one definitional identity, which holds by `rfl`:
`(buildRhsChain (Λ₁::rest) Ψ).fm = □ ((OutputCtx.fillRhs (Λ₁::rest) Ψ).fm)` — both sides reduce to
`Proposition.box (Λ₁.fm.imp (buildRhsChain rest Ψ).fm)`. That is what lets `lemma4_7_iv`'s
`□A ∧ ◇B ⊃ ◇C` shape line up with the goal with no rewriting at all. -/

/-- **The `Λ{ }`-chain induction** (page 10): `⊢ (L_X ∧ L_Z) ⊃ L_Y`. The source's "induction on
`n` … together with Lemma 4.7.(ii) and (iv)", transcribed literally.

| Case | Goal | Discharged by |
|---|---|---|
| `[]` | `((⊤ ⊃ A) ∧ (A ⊃ B)) ⊃ B` | `topBase` (propositional; `⊤ = ⊥ ⊃ ⊥` via `efq`) |
| `[Λ₀]` | `((L₀ ⊃ A) ∧ (L₀ ∧ (A ⊃ B))) ⊃ (L₀ ∧ B)` | `lemma4_7_ii (D := L₀)` via `mpAnd` |
| `Λ₀::Λ₁::rest` | `((L₀⊃□X′) ∧ (L₀∧◇Z′)) ⊃ (L₀∧◇Y′)` | `lemma4_7_ii (D := L₀)` via `lemma4_7_iv` |

See [ArisakaDasStrassburger2015], §4, page 10. -/
theorem lambdaChain_XZ_imp_Y (A B : Proposition Atom) :
    ∀ (Λ : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom)
        (((Λ.fillRhs (.atom A)).fm.and (Λ.fillLhs (.atom (A.imp B))).fm).imp
          (Λ.fillLhs (.atom B)).fm)
  | []               => topBase A B
  | [Λ₀]             => lemma4_7_ii Λ₀.fm (mpAnd A B)
  | Λ₀ :: Λ₁ :: rest =>
      lemma4_7_ii Λ₀.fm (lemma4_7_iv (lambdaChain_XZ_imp_Y A B (Λ₁ :: rest)))

/-- Shape lemma for the `ctx.Λ = []` normalisation used by the `impL` assembly:
`InputCtx.outputPruning`'s `ctx.Λ.headD .empty :: ctx.Λ.tail` layer, run through `buildRhsChain`,
computes the same formula as `□` applied to `ctx.Λ.fillRhs (.atom A)`. Closed by `cases ctx.Λ <;>
rfl` — both branches (`Λ = []` giving the repaired `[∅]` layer, and `Λ = Γ :: rest` where
`headD .empty :: tail` is the identity) reduce definitionally. -/
theorem psiX_fm (ctx : InputCtx Atom) (A : Proposition Atom) :
    (buildRhsChain (ctx.Λ.headD .empty :: ctx.Λ.tail) (NestedRhs.atom A)).fm
      = Proposition.box ((ctx.Λ.fillRhs (.atom A)).fm) := by
  cases ctx.Λ <;> rfl

/-- Companion shape lemma to `psiX_fm`: the repaired `ctx.Λ.headD .empty :: ctx.Λ.tail` output
context, filled via `fillRhs`, computes the same full-sequent formula as `ctx.Λ.fillRhs (.atom
A)` itself. Closed by `cases ctx.Λ <;> rfl`. -/
theorem primeRhs_fm (ctx : InputCtx Atom) (A : Proposition Atom) :
    (OutputCtx.fillRhs (ctx.Λ.headD .empty :: ctx.Λ.tail) (NestedRhs.atom A)).fm
      = (ctx.Λ.fillRhs (.atom A)).fm := by
  cases ctx.Λ <;> rfl

/-! ## `⊃•` (`impL`): Deferred, Strategic Sorry

Per Phase 11's deviation note (restated in this module's docstring): `impL` needs the source's own
induction-on-`n` argument over the `Λ{ }` chain (page 10's `L_X, L_Y, L_Z` construction), which
mixes `ctx.outputPruning.fillRhs`-shaped and `ctx.fillLhs`-shaped premises against a `ctx.fillLhs`-
shaped conclusion in a way that does not reduce to Lemma 4.4/4.5/4.8's already-landed congruence
lemmas alone -- genuinely more machinery than this phase's remaining scope (not in Phase 13's own
task list, which names only `□•, □◦, ♦•, ♦◦, t•, t◦, 4•, 4◦, b[]`). Landed as a single,
tightly-scoped, documented `sorry` (the anti-analysis contract's strategic-sorry policy), tracked
in this dispatch's `sorry_inventory` with a follow-up to a later, not-yet-numbered phase. -/

/-- **Soundness of `⊃•`** (`impL`): deferred, see the section docstring above. -/
theorem nested_sound_impL (ctx : InputCtx Atom) (A B : Proposition Atom)
    (hA : Derivable (@CS5ModalAxiom Atom) (ctx.outputPruning.fillRhs (.atom A)).fm)
    (hB : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom B)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom (A.imp B))).fm := by
  -- sorry: assumes the `⊃•`/`impL` soundness fact holds for an arbitrary `InputCtx`; deferred
  -- because it needs the source's page-10 induction-on-`n` over the `Λ{ }` chain (the
  -- `L_X, L_Y, L_Z` construction), not yet formalized as of this dispatch; follow-up: a
  -- dedicated later phase building that induction (not yet numbered in the plan; flagged
  -- forward alongside Phase 13's `cut` non-target in the handoff)
  sorry

/-! ## Theorem 4.1, Assembled: `nested_sound`

The top-level soundness theorem, structurally recursive on the `NestedProof` term itself
(mirroring `NestedProof.height`'s own recursion shape), dispatching to each constructor's case
lemma above and threading the recursive soundness facts of its premises through. Every
constructor except `impL` is fully discharged; `impL` routes through the strategic `sorry` in
`nested_sound_impL` above (see that theorem's docstring). -/

/-- **Theorem 4.1** (page 9): every `NestedProof` derivation is sound with respect to `CS5`'s
Hilbert system -- `NestedProof Γ → Derivable (@CS5ModalAxiom Atom) (fm Γ)`. -/
theorem nested_sound :
    ∀ {Γ : NestedFull Atom}, NestedProof Γ → Derivable (@CS5ModalAxiom Atom) Γ.fm
  | _, .botL ctx => nested_sound_botL ctx
  | _, .id ctx a => nested_sound_id ctx a
  | _, .andL ctx A B p => nested_sound_andL ctx A B (nested_sound p)
  | _, .andR ctx A B p q => nested_sound_andR ctx A B (nested_sound p) (nested_sound q)
  | _, .orL ctx A B π p q => nested_sound_orL ctx A B π (nested_sound p) (nested_sound q)
  | _, .orRLeft ctx A B p => nested_sound_orRLeft ctx A B (nested_sound p)
  | _, .orRRight ctx A B p => nested_sound_orRRight ctx A B (nested_sound p)
  | _, .impL ctx A B p q => nested_sound_impL ctx A B (nested_sound p) (nested_sound q)
  | _, .impR ctx A B p => nested_sound_impR ctx A B (nested_sound p)
  | _, .boxL ctx A Δ p => nested_sound_boxL ctx A Δ (nested_sound p)
  | _, .boxR ctx A p => nested_sound_boxR ctx A (nested_sound p)
  | _, .diaL ctx A p => nested_sound_diaL ctx A (nested_sound p)
  | _, .diaR ctx A Δ p => nested_sound_diaR ctx A Δ (nested_sound p)
  | _, .contract ctx Δ p => nested_sound_contract ctx Δ (nested_sound p)
  | _, .tR ctx A p => nested_sound_tR ctx A (nested_sound p)
  | _, .tL ctx A p => nested_sound_tL ctx A (nested_sound p)
  | _, .fourR ctx A Δ p => nested_sound_fourR ctx A Δ (nested_sound p)
  | _, .fourL ctx A Δ p => nested_sound_fourL ctx A Δ (nested_sound p)
  | _, .bStruct ctx σ Δ p => nested_sound_bStruct ctx σ Δ (nested_sound p)

/-- **Corollary to Theorem 4.1**: a cut-free `NestedProof` of `(∅, A°)` -- the source's own
convention for "a proof of the formula `A`" (see `Rules.lean`'s `NestedProof` docstring) -- gives
`CS5`-Hilbert-derivability of `A` directly, discharging the fixed `⊤` antecedent via
`cs5DerivTopImpElim`. -/
theorem nested_sound_provable {A : Proposition Atom}
    (d : NestedProof ((NestedLhs.empty, NestedRhs.atom A) : NestedFull Atom)) :
    Derivable (@CS5ModalAxiom Atom) A := by
  obtain ⟨dtop⟩ := nested_sound d
  obtain ⟨delim⟩ := cs5DerivTopImpElim (X := A)
  exact ⟨.modus_ponens _ _ _ delim dtop⟩

end Cslib.Logic.Modal
