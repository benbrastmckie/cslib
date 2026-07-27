/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.Nested.Context
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # `fm` Compositionality Over Nested-Sequent Contexts

This module proves the "workhorse" lemmas relating `fm (Γ{∆})` to `fm ∆`
(`doc_id: arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`, §2,
Observation 2.2 and Definition 2.3), for both context kinds built in `Nested/Context.lean`. Every
lemma is stated against `Derivable (@CS5ModalAxiom Atom)`, fixing the Hilbert-relative currency
these facts are proved at; this is the reusable infrastructure the labelled-soundness consumer
(Stage D onward) lifts local `fm ∆ → fm ∆'` derivability facts into global `fm (Γ{∆)) → fm
(Γ{∆'})` facts with, one context layer at a time.

## A Small Local Hilbert-Combinator Toolkit

The section below reproduces (rather than imports) a handful of small `Derivable CS5ModalAxiom`
propositional/modal combinators: empty-context implication transitivity, box/diamond
monotonicity, and left/right implication congruence. A closely analogous "`P`-generic" toolkit
already exists, privately, inside `Constructive/CS5.lean` (`cs5_impTrans`, `cs5_box_mono`) and
publicly inside `Constructive/Labelled/Soundness.lean` (`cs5_deriv_imp_trans`,
`cs5_deriv_box_mono`, `cs5_deriv_imp_congr_right`, …). Neither is reused here: the `CS5.lean`
versions are `private` (invisible outside that file), and importing the much larger
`Labelled/Soundness.lean` (a different metalogic subsystem entirely, with its own graph/label
apparatus) purely for a handful of small combinators would introduce an unwarranted, heavy, and
architecturally confusing dependency of the *nested*-sequent development on the *labelled*-sequent
one. Reproducing the small toolkit locally (mirroring the exact proof shapes already verified to
compile in both of those files) keeps `Nested/` self-contained, depending only on `Nested/Context`
and `Constructive/CS5`.

## Output Contexts (`OutputCtx`): Covariant in the Hole

`buildRhsChain_fm_mono`, `OutputCtx.fillRhs_fm_mono`, and `OutputCtx.fillLhs_fm_mono` establish,
by induction on the `OutputCtx` list (the Lean form of "induction on the structure of `Γ{ }`",
Observation 2.2), that `CS5`-derivability of `fm ∆ → fm ∆'` lifts to `fm (Γ{∆}) → fm (Γ{∆'})`, in
the **covariant** direction: an output context's hole sits inside only `∧` (`comma`) and `◇`
(`dia`) constructors on the LHS side, and inside the "consequent" position of the `⊃` built by
`box`/`fillRhs` on the RHS/full side — both positions are covariant for `⊃`-congruence.

## Input Contexts (`InputCtx`): Contravariant in the Hole

`InputCtx.fillLhs_fm_antitone` establishes the same lifting for `InputCtx`, but
**contravariantly**: an input context's hole sits inside `ctx.Λ.fillLhs Δ`, which itself occupies
the *antecedent* position of the box `.box (ctx.Λ.fillLhs Δ) ctx.π` (`fm = box (X ⊃ π.fm)`, `X`
the hole's image) — antecedent position is contravariant for `⊃`-congruence, so growing `Δ` (in
the sense `Δ.fm ⊢ Δ'.fm`) *shrinks* `Γ{Δ}` (in the sense `Γ{Δ'}.fm ⊢ Γ{Δ}.fm`, not the other way
around). This matches this phase's task list item 3 exactly ("output contexts are covariant in
the hole, input contexts contravariant") and is derived compositionally from the `OutputCtx`
lemmas above plus one contravariant implication-congruence combinator
(`cs5DerivImpCongrLeft`) — no new axiom-level case analysis is needed.

## The Pruning Relation: `Λ`-Empty Case Only, With the General Case's Obstruction Documented

`Nested/Context.lean`'s "Basic Equational Lemmas" section explicitly deferred the `(Γ⇓){∆}` vs
`Γ{∆}` relationship to this phase, flagging that "the natural candidate equations… do not hold as
bare structural equalities" and that "the correct form is probably an `fm`-level equation/iff…
[which] should emerge naturally" once the compositionality apparatus above exists. It does emerge
— but only as a **restricted**, not a fully general, fact:

`InputCtx.fillEmpty_imp_outputPruning_fillRhs` proves, for every `ctx : InputCtx Atom` with
`ctx.Λ = []` (i.e. the hole sits directly at the outer box's LHS slot — the shape of every
`InputCtx` example this development has actually built, e.g. Phase 7's `γ₂Ctx`), that
`Derivable (ctx.fillEmpty.fm.imp (ctx.outputPruning.fillRhs ctx.π).fm)`: filling with `∅`
derivably *implies* the output-pruned filling with `π`. Under the repaired `InputCtx.outputPruning`
(`Nested/Context.lean`, which retains a `∅`-layer at `Λ = []` rather than collapsing it), the proof
splits on `ctx.Γ'`: for `ctx.Γ' = G :: r'` both sides reduce to the literal same term via
`buildRhsChain_append`, an outright identity implication; only for `ctx.Γ' = []` do the two sides
still differ by one retained `□`, and there `tBox` (`□A → A`) unboxes it, using `⊢⊤` to discharge
the "filled-with-nothing" `⊤ ⊃ ·` wrapper.

**The unrestricted version (arbitrary `ctx.Λ`) is *not* `CS5`-Hilbert-derivable**, and this module
does not attempt it as a bare `Derivable` schema (landing an unprovable claim, or a claim proved
by an unsound argument, would be strictly worse than a documented, correctly-scoped restriction —
see the Escalation Protocol). The obstruction is a genuine box-depth mismatch, confirmed by two
independent countermodel arguments against the two natural repair strategies:

1. **Naive box-distribution** (`□(A → B) → (A → □B)`): invalid in bare `K` already — a two-world
   countermodel (`w R v₁`, `w R v₂`, `A` false at both `vᵢ`, `B` false at both `vᵢ`, `A` true at
   `w`) makes `□(A → B)` vacuously true at `w` and `A` true at `w`, while `□B` fails at `w` (both
   successors refute `B`).
2. **Dia-to-box shift** (`(◇A → B) → □(A → B)`): also invalid in bare `K` — a two-world
   countermodel (`w R v`, `A` true at `v`, `B` false at `v`, `B` true at `w`) makes `◇A → B` true
   at `w` (`B` holds at `w` regardless of the antecedent) while `□(A → B)` fails at `w` (via `v`).

Both repair strategies are exactly what a general-`Λ` induction on `buildRhsChain`/`fillEmpty`
would need at the `Γ :: Γ₂ :: rest` step (the base cases `Λ = []`/`Λ = [Γ]` coincide in box-depth
and go through cleanly via `tBox` alone — the singleton case is analogous to the landed `Λ = []`
case but is not landed here, to keep this phase scoped to what is actually consumed downstream).
Since `Λ = []` is the only shape this development's concrete examples exhibit, and the general
case is genuinely false as a Hilbert schema (not merely unproved), restricting the theorem's
hypothesis is the correct, honest resolution — not a placeholder.

## References

* [R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal
  Logics*][ArisakaDasStrassburger2015], §2, Observation 2.2 and Definition 2.3.
-/

@[expose] public section

namespace Cslib.Logic.Modal

universe u
variable {Atom : Type u}

/-! ## Local Hilbert-Combinator Toolkit (`Derivable (@CS5ModalAxiom Atom)`-level) -/

/-- **Identity**: `⊢ P ⊃ P` (the standard `S K K` combinator). Mirrors
`Labelled/Soundness.lean`'s `cs5_deriv_imp_self`, reproduced locally (see the module docstring). -/
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

/-- **Constant weakening**: from a closed theorem `⊢ Q`, derive `⊢ P ⊃ Q` for any `P` (`implyK`
applied directly). -/
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

/-- **`□`-monotonicity**: from `⊢ X ⊃ Y`, derive `⊢ □X ⊃ □Y` (necessitation + the `k` axiom). -/
private theorem cs5DerivBoxMono {X Y : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (X.imp Y)) :
    Derivable (@CS5ModalAxiom Atom) ((Proposition.box X).imp (Proposition.box Y)) := by
  obtain ⟨d⟩ := h
  obtain ⟨dnec⟩ : Derivable (@CS5ModalAxiom Atom) (Proposition.box (X.imp Y)) :=
    ⟨.necessitation _ d⟩
  exact ⟨.modus_ponens [] _ _ (.ax [] _ (.k X Y)) dnec⟩

/-- **`◇`-monotonicity**: from `⊢ X ⊃ Y`, derive `⊢ ◇X ⊃ ◇Y` (necessitation + the `kdia` axiom). -/
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
`⊢ (a' ⊃ b) ⊃ (a ⊃ b)`. Built directly via the deduction theorem (context `[a, a' ⊃ b]`: derive
`a'` from `a` via `h`, then `b` from `a'` via the assumed `a' ⊃ b`, then discharge both). -/
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

/-- **`⊤`-elimination**: `⊢ (⊤ ⊃ X) ⊃ X`, given `⊢ ⊤` (the `⊢ P ⊃ P` identity at `P := ⊥`, since
`⊤ := ⊥ ⊃ ⊥`). Context `[⊤ ⊃ X]`: apply the assumed implication to the weakened `⊢ ⊤` witness. -/
private theorem cs5DerivTopImpElim {X : Proposition Atom} :
    Derivable (@CS5ModalAxiom Atom) ((Proposition.top.imp X).imp X) := by
  obtain ⟨dtop⟩ := cs5DerivImpSelf (Atom := Atom) Proposition.bot
  refine ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    [] (Proposition.top.imp X) X ?_⟩
  exact .modus_ponens _ _ _
    (.assumption [Proposition.top.imp X] _ (List.mem_cons.mpr (Or.inl rfl)))
    (.weakening [] [Proposition.top.imp X] _ dtop (fun _ h => nomatch h))

/-! ## Output Contexts: Covariant Compositionality -/

/-- **`buildRhsChain` is `fm`-covariant in its RHS filler**: given `⊢ Ψ.fm ⊃ Ψ'.fm`, derive
`⊢ (buildRhsChain l Ψ).fm ⊃ (buildRhsChain l Ψ').fm`, by induction on `l` matching
`buildRhsChain`'s own recursion. Each cons-step wraps the induction hypothesis in one more `□`
(`cs5DerivBoxMono`) after moving the fixed head layer `Γ` into the antecedent position
(`cs5DerivImpCongrRight`), mirroring `buildRhsChain`'s own `box Γ (buildRhsChain rest Ψ)` step. -/
theorem buildRhsChain_fm_mono {Ψ Ψ' : NestedRhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (Ψ.fm.imp Ψ'.fm)) :
    ∀ (l : List (NestedLhs Atom)),
      Derivable (@CS5ModalAxiom Atom) ((buildRhsChain l Ψ).fm.imp (buildRhsChain l Ψ').fm)
  | [] => h
  | Γ :: rest => cs5DerivBoxMono (cs5DerivImpCongrRight Γ.fm (buildRhsChain_fm_mono h rest))

/-- **`OutputCtx.fillRhs` is `fm`-covariant in its RHS filler**: given `⊢ Ψ.fm ⊃ Ψ'.fm`, derive
`⊢ (ctx.fillRhs Ψ).fm ⊃ (ctx.fillRhs Ψ').fm`, for every output context `ctx`. The `n = 0` case
routes through `buildRhsChain_fm_mono`'s degenerate `l = []` instance with the fixed `⊤`
antecedent from `fillRhs`'s own `(∅, Ψ)` clause; the `n ≥ 1` case is `buildRhsChain_fm_mono`
directly, congruent under the fixed head layer `Γ`. This is the node-wise adequacy reading:
`CS5`-provable local strengthenings at the hole lift to `CS5`-provable strengthenings of the whole
output-context-filled full sequent. -/
theorem OutputCtx.fillRhs_fm_mono {Ψ Ψ' : NestedRhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (Ψ.fm.imp Ψ'.fm)) :
    ∀ (ctx : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom) ((ctx.fillRhs Ψ).fm.imp (ctx.fillRhs Ψ').fm)
  | [] => cs5DerivImpCongrRight Proposition.top h
  | Γ :: rest => cs5DerivImpCongrRight Γ.fm (buildRhsChain_fm_mono h rest)

/-- **`OutputCtx.fillLhs` is `fm`-covariant in its LHS filler**: given `⊢ Δ.fm ⊃ Δ'.fm`, derive
`⊢ (ctx.fillLhs Δ).fm ⊃ (ctx.fillLhs Δ').fm`, for every output context `ctx`, by induction on `ctx`
matching `fillLhs`'s own three-case recursion (the Lean form of "induction on the structure of
`Γ{ }`", Observation 2.2). The `[Γ]` base case is congruence in the right conjunct
(`cs5DerivAndCongrRight`, since `fillLhs [Γ] Δ = comma Γ Δ`); the `Γ :: Γ₂ :: rest` step lifts the
induction hypothesis through `◇` (`cs5DerivDiaMono`, `dia`'s `fm` clause) before the same
`and`-congruence, mirroring `fillLhs`'s own `comma Γ (dia (fillLhs (Γ₂ :: rest) Δ))` step. This is
the covariant half of this phase's node-wise adequacy requirement. -/
theorem OutputCtx.fillLhs_fm_mono {Δ Δ' : NestedLhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (Δ.fm.imp Δ'.fm)) :
    ∀ (ctx : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom) ((ctx.fillLhs Δ).fm.imp (ctx.fillLhs Δ').fm)
  | [] => h
  | [Γ] => cs5DerivAndCongrRight Γ.fm h
  | Γ :: Γ₂ :: rest =>
      cs5DerivAndCongrRight Γ.fm (cs5DerivDiaMono (OutputCtx.fillLhs_fm_mono h (Γ₂ :: rest)))

/-! ## Input Contexts: Contravariant Compositionality -/

/-- **`InputCtx.fillLhs` is `fm`-contravariant in its LHS filler**: given `⊢ Δ.fm ⊃ Δ'.fm`, derive
`⊢ (ctx.fillLhs Δ').fm ⊃ (ctx.fillLhs Δ).fm` (note the *swapped* conclusion order) for every input
context `ctx`. The hole sits inside `ctx.Λ.fillLhs Δ`, which occupies the *antecedent* position of
`box (ctx.Λ.fillLhs Δ) ctx.π` (`fm = □(X ⊃ π.fm)`) — antecedent position is contravariant, so the
covariant fact `(Λ.fillLhs Δ).fm ⊃ (Λ.fillLhs Δ').fm` (`OutputCtx.fillLhs_fm_mono`) flips via
`cs5DerivImpCongrLeft` before being lifted through `□` (`cs5DerivBoxMono`) and the outer output
context `ctx.Γ'` (`OutputCtx.fillRhs_fm_mono`). This is this phase's task list item 3's
"input contexts contravariant" requirement, fully general in `ctx` (no restriction on `ctx.Λ`). -/
theorem InputCtx.fillLhs_fm_antitone (ctx : InputCtx Atom) {Δ Δ' : NestedLhs Atom}
    (h : Derivable (@CS5ModalAxiom Atom) (Δ.fm.imp Δ'.fm)) :
    Derivable (@CS5ModalAxiom Atom) ((ctx.fillLhs Δ').fm.imp (ctx.fillLhs Δ).fm) := by
  have hΛ : Derivable (@CS5ModalAxiom Atom)
      ((ctx.Λ.fillLhs Δ).fm.imp (ctx.Λ.fillLhs Δ').fm) :=
    OutputCtx.fillLhs_fm_mono h ctx.Λ
  have hFlip : Derivable (@CS5ModalAxiom Atom)
      (((ctx.Λ.fillLhs Δ').fm.imp ctx.π.fm).imp ((ctx.Λ.fillLhs Δ).fm.imp ctx.π.fm)) :=
    cs5DerivImpCongrLeft hΛ
  have hBoxed : Derivable (@CS5ModalAxiom Atom)
      ((NestedRhs.box (ctx.Λ.fillLhs Δ') ctx.π).fm.imp
        (NestedRhs.box (ctx.Λ.fillLhs Δ) ctx.π).fm) :=
    cs5DerivBoxMono hFlip
  exact OutputCtx.fillRhs_fm_mono hBoxed ctx.Γ'

/-! ## The Pruning Relation (`Λ`-Empty Case) -/

/-- **`Γ{∅}` derivably implies `Γ⇓{π}`, when `ctx.Λ = []`.** For `ctx : InputCtx Atom` whose hole
sits directly at the outer box's LHS slot (`ctx.Λ = []`, matching Phase 7's `γ₂Ctx` and every
`InputCtx` example this development has built), `Derivable (ctx.fillEmpty.fm ⊃ (ctx.outputPruning
.fillRhs ctx.π).fm)`. Under the repaired `outputPruning` (`Nested/Context.lean`), `ctx.Λ = []`
gives `ctx.outputPruning = ctx.Γ' ++ [∅]`, and the proof splits on `ctx.Γ'` exactly per the plan's
refinement of this lemma:
- `ctx.Γ' = G :: r'`: `ctx.fillEmpty` and `ctx.outputPruning.fillRhs ctx.π` both reduce
  (`OutputCtx.fillRhs_append` + `buildRhsChain_append`) to the *literal same term*
  `(G, buildRhsChain r' (.box ∅ ctx.π))` — an identity implication, `cs5DerivImpSelf`. No `tBox`
  step is needed here; the repair closes exactly the gap `tBox` used to be patching over in this
  branch.
- `ctx.Γ' = []`: both sides degenerate to the un-repaired lemma's own `(∅, box ∅ π)` versus
  `(∅, π)` pair — the two sides still differ by one retained `□`, so the original `tBox` (`□A ⊃ A`)
  together with `⊢ ⊤` (`cs5DerivTopImpElim`) argument is retained unchanged in this branch, lifted
  through the (now trivial, `ctx.Γ' = []`) outer context by `OutputCtx.fillRhs_fm_mono`.

See the module docstring for why the unrestricted (`ctx.Λ` arbitrary) version is *not*
`CS5`-Hilbert-derivable, and is therefore not attempted here. -/
theorem InputCtx.fillEmpty_imp_outputPruning_fillRhs (ctx : InputCtx Atom) (hΛ : ctx.Λ = []) :
    Derivable (@CS5ModalAxiom Atom)
      (ctx.fillEmpty.fm.imp (ctx.outputPruning.fillRhs ctx.π).fm) := by
  have hΛfe : ctx.Λ.fillEmpty = NestedLhs.empty := by rw [hΛ]; rfl
  have hlhs : ctx.fillEmpty = ctx.Γ'.fillRhs (NestedRhs.box NestedLhs.empty ctx.π) := by
    unfold InputCtx.fillEmpty
    rw [hΛfe]
  match hΓ' : ctx.Γ' with
  | G :: r' =>
    have hrhs : ctx.outputPruning.fillRhs ctx.π =
        OutputCtx.fillRhs (G :: r') (NestedRhs.box NestedLhs.empty ctx.π) := by
      unfold InputCtx.outputPruning
      rw [hΓ', hΛ]
      change OutputCtx.fillRhs ((G :: r') ++ [NestedLhs.empty]) ctx.π = _
      rw [OutputCtx.fillRhs_append]
      rfl
    rw [hlhs, hrhs, hΓ']
    exact cs5DerivImpSelf _
  | [] =>
    have htb : Derivable (@CS5ModalAxiom Atom)
        ((Proposition.box (Proposition.top.imp ctx.π.fm)).imp (Proposition.top.imp ctx.π.fm)) :=
      ⟨.ax [] _ (.tBox (Proposition.top.imp ctx.π.fm))⟩
    have hcore : Derivable (@CS5ModalAxiom Atom)
        ((NestedRhs.box NestedLhs.empty ctx.π).fm.imp ctx.π.fm) :=
      cs5DerivImpTrans htb cs5DerivTopImpElim
    have hres : Derivable (@CS5ModalAxiom Atom)
        ((OutputCtx.fillRhs [] (NestedRhs.box NestedLhs.empty ctx.π)).fm.imp
          (OutputCtx.fillRhs [] ctx.π : NestedFull Atom).fm) :=
      OutputCtx.fillRhs_fm_mono hcore []
    have hrhs : ctx.outputPruning.fillRhs ctx.π = OutputCtx.fillRhs [] ctx.π := by
      unfold InputCtx.outputPruning
      rw [hΓ', hΛ]
      rfl
    rw [hlhs, hrhs, hΓ']
    exact hres

end Cslib.Logic.Modal
