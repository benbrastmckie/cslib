import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # Task 517 Phase 19 — DECISION GATE: `CS5 ⊢ FS`. **VERDICT: DERIVED.**

**Target**: `FS := (◇A → □B) → □(A → B)` (Simpson's Figure 3-7 base-`IK` axiom 5, the
Fischer-Servi confluence schema), against `CS5ModalAxiom` (`CS5.lean:182`), i.e.
`Derivable (@CS5ModalAxiom Atom) (((◇A).imp (Proposition.box B)).imp (Proposition.box (A.imp B)))`.

**Result: POSITIVE. `cs5_fs` below is a sorry-free, axiom-clean Hilbert derivation.**

## How the gate was decided: the refutation attempt produced the derivation

Phase 19 was dispatched to prioritise the *untried* direction — a `CS5` countermodel refuting
`FS`. That attempt is what settled the gate, in the opposite direction: characterising the
class of algebras a countermodel would have to inhabit showed the class cannot contain one,
and the impossibility argument transcribes directly into the Hilbert derivation below.

**The algebraic characterisation.** Read a `CS5` algebra as a Heyting algebra `H` with
operators `□`, `◇`. Then:

1. `k`/`kdia` + necessitation force `□`, `◇` monotone (if `x ≤ y` then `x → y = ⊤`, so
   `□(x→y) = □⊤ = ⊤`).
2. `bBox` (`x ≤ □◇x`) and `bDia` (`◇□x ≤ x`) are exactly the unit and counit of an
   **adjunction `◇ ⊣ □`**. This is the key structural fact, and the one the earlier negative
   probe (`fischer-servi-probe.lean`) missed.
3. With `tBox`/`tDia`/`four`, `◇` is a closure operator and `□` an interior operator, and
   `Fix(◇) = Fix(□) =: J`: if `◇x = x` then `x ≤ □◇x = □x ≤ x`, and dually.
4. So `◇` is the reflector and `□` the coreflector onto `J`; `J` is a complete sublattice.
5. `k` is then **automatic**: `□(x→y) ∧ □x ∈ J` and is `≤ y`, so it is `≤ □y`.
6. The only remaining constraint is `kdia`, and it is equivalent to the **Frobenius
   condition** `◇(u ∧ x) = u ∧ ◇x` for `u ∈ J`. (`⇐` is immediate; for `⇒`, `kdia` says
   `u ∧ x ≤ y ⟹ u ∧ ◇x ≤ ◇y` for `u ∈ J`, and taking `y := u ∧ x` gives `u ∧ ◇x ≤ ◇(u ∧ x)`.)

**Why no countermodel exists.** In any such algebra, with `C := ◇A → □B`:
`◇C ∧ A ≤ ◇C ∧ ◇A = ◇(◇A ∧ C) ≤ ◇□B = □B ≤ B`, using `tDia`, Frobenius at `u := ◇A ∈ J`,
modus ponens, and `◇□B = □B` (as `□B ∈ J`). By the adjunction this is exactly
`C ≤ □(A → B)` — i.e. `FS` holds in **every** `CS5` algebra. Since the algebraic semantics is
complete for the Hilbert system (Lindenbaum), `CS5 ⊢ FS`. Each step of that argument is a
`CS5` theorem, so the argument transcribes into `cs5_fs` below with no algebra needed.

## What the earlier negative probe got wrong

`fischer-servi-probe.lean` recorded a NEGATIVE syntactic verdict with the diagnosis:
*"Every route to `A → B` from the hypothesis `H : ◇A → □B` genuinely needs `H` in context ...
so the resulting `A → B` fact is never closed, and `necessitation` is inapplicable."* It called
this "not a search failure ... a structural mismatch".

**That diagnosis is refuted here.** It is sound only for routes that keep `H` as a *context
hypothesis*. The derivation below never does: it treats `C := ◇A → □B` as a **formula**, proves
the **closed** theorem `⊢ ◇C → (A → B)` (`dia_hyp_imp`), necessitates *that* (legal — empty
context), and re-attaches the hypothesis through `bBox`'s `C → □◇C`. `bBox` is precisely the
"internalise a hypothesis under a box" move, and it is what the earlier obstruction argument
did not price in. The landed `fs_context_relative_half` obstruction is likewise circumvented,
not contradicted: it blocks the context-relative route, and this derivation is not that route.

## Axiom usage

`implyK`, `implyS`, `andI`, `andE1`, `andE2`, `k`, `kdia`, `tDia`, `fourDia`, `bBox`, `bDia`,
plus `necessitation`/`modus_ponens`/`assumption`/`weakening`. Notably **`tBox`, `fourBox`,
`efq`, `orI1`/`orI2`/`orE` are unused**: `FS` already holds in `CK + tDia + fourDia + B`.
(`fourDia` is needed only to promote `bBox`'s `◇A → □◇◇A` to `◇A → □◇A`.)

## Consequences

- Phase 16's `cs5_completeness ⟹ CS5 ⊢ FS` had made `CS5 ⊢ FS` a **necessary condition** of the
  target. That necessary condition is now **discharged**: it is no longer a risk term.
- The `~25%`-probability "target is FALSE" branch of the Phase 19 gate is **closed**.
- `dia_frobenius` and `box_hyp_internalise` are reusable: the first is the `kdia`-Frobenius
  transfer, the second is the general "`⊢ ◇C → ψ` gives `⊢ C → □ψ`" adjunction step.
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type u}

/-! ## Generic plumbing -/

/-- Chain two empty-context implications. -/
private noncomputable def fsImpTrans {a b c : Proposition Atom}
    (h1 : DerivationTree (@CS5ModalAxiom Atom) [] (a.imp b))
    (h2 : DerivationTree (@CS5ModalAxiom Atom) [] (b.imp c)) :
    DerivationTree (@CS5ModalAxiom Atom) [] (a.imp c) :=
  deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) [] a c
    (.modus_ponens _ _ _ (.weakening [] [a] _ h2 (fun _ h => nomatch h))
      (.modus_ponens _ _ _ (.weakening [] [a] _ h1 (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))))

/-- Box is monotone on **closed** implications: `⊢ a → b` gives `⊢ □a → □b`
(necessitation + `k`). -/
private noncomputable def fsBoxMono {a b : Proposition Atom}
    (h : DerivationTree (@CS5ModalAxiom Atom) [] (a.imp b)) :
    DerivationTree (@CS5ModalAxiom Atom) [] ((Proposition.box a).imp (Proposition.box b)) :=
  .modus_ponens _ _ _ (.ax [] _ (.k a b)) (.necessitation _ h)

/-- Diamond is monotone on **closed** implications: `⊢ a → b` gives `⊢ ◇a → ◇b`
(necessitation + `kdia`). -/
private noncomputable def fsDiaMono {a b : Proposition Atom}
    (h : DerivationTree (@CS5ModalAxiom Atom) [] (a.imp b)) :
    DerivationTree (@CS5ModalAxiom Atom) [] ((◇a).imp (◇b)) :=
  .modus_ponens _ _ _ (.ax [] _ (.kdia a b)) (.necessitation _ h)

/-- `⊢ (P ∧ (P → Q)) → Q` — modus ponens packaged as a conjunction elimination. -/
private noncomputable def fsAndImpElim (P Q : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) [] ((P.and (P.imp Q)).imp Q) :=
  deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) []
    (P.and (P.imp Q)) Q
    (.modus_ponens _ _ _
      (.modus_ponens _ _ _ (.ax _ _ (.andE2 P (P.imp Q)))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))))
      (.modus_ponens _ _ _ (.ax _ _ (.andE1 P (P.imp Q)))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))))

/-! ## The two structural lemmas -/

/-- **`⊢ □U → (◇X → ◇(U ∧ X))`** — the *Frobenius transfer*, the syntactic content of `kdia`.

Algebraically this is `u ∧ ◇x ≤ ◇(u ∧ x)` for `u` in the fixed-point sublattice `J`, which is
`kdia` restated (see the module docstring). Derivation: `andI` gives the closed theorem
`⊢ U → (X → U ∧ X)`; `k` + necessitation push it under `□` to get `□U → □(X → U ∧ X)`; then
`kdia` fires. Pure `CK` — no `T`, `4`, or `B`. -/
private noncomputable def fsDiaFrobenius (U X : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.box U).imp ((◇X).imp (◇(U.and X)))) :=
  fsImpTrans (fsBoxMono (.ax [] _ (.andI U X))) (.ax [] _ (.kdia X (U.and X)))

/-- **`⊢ ◇A → □◇A`** — every diamond is *boxed*, i.e. `◇A` lies in the fixed-point sublattice
`J` of the module docstring (`□◇A = ◇A`, the converse being `tBox`).

`bBox` at `◇A` gives `◇A → □◇◇A`; `fourDia` under `□` collapses `◇◇A` to `◇A`. This is what
licenses instantiating `fsDiaFrobenius` at `U := ◇A`. -/
private noncomputable def fsDiaBoxedDia (A : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) [] ((◇A).imp (Proposition.box (◇A))) :=
  fsImpTrans (.ax [] _ (.bBox (◇A))) (fsBoxMono (.ax [] _ (.fourDia A)))

/-! ## The gate -/

/-- **`⊢ ◇(◇A → □B) → (A → B)`** — the closed core of the derivation, and the step the earlier
negative probe's obstruction argument ruled out on the mistaken assumption that the hypothesis
`◇A → □B` must sit in the context.

Reading `C := ◇A → □B` as a formula, this is the algebraic chain
`◇C ∧ A ≤ ◇C ∧ ◇A = ◇(◇A ∧ C) ≤ ◇□B = □B ≤ B` transcribed: `tDia` (`A → ◇A`), then
`fsDiaBoxedDia` + `fsDiaFrobenius` at `U := ◇A` (`◇A ∧ ◇C → ◇(◇A ∧ C)`), then `fsAndImpElim`
under `◇` (`◇(◇A ∧ C) → ◇□B`), then `bDia` (`◇□B → B`). Crucially the result is **closed**, so
`necessitation` applies to it — which is exactly what `fsBoxInternalise` needs. -/
private noncomputable def fsDiaHypImp (A B : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      ((◇((◇A).imp (Proposition.box B))).imp (A.imp B)) := by
  set C : Proposition Atom := (◇A).imp (Proposition.box B) with hC
  -- `⊢ ◇(◇A ∧ C) → B`, via `kdia` on `fsAndImpElim` then `bDia`.
  have hElim : DerivationTree (@CS5ModalAxiom Atom) [] ((◇((◇A).and C)).imp B) :=
    fsImpTrans (fsDiaMono (fsAndImpElim (◇A) (Proposition.box B))) (.ax [] _ (.bDia B))
  -- Assemble in the context `[A, ◇C]`, then discharge both hypotheses.
  have hCtx : DerivationTree (@CS5ModalAxiom Atom) [A, ◇C] B := by
    have hA : DerivationTree (@CS5ModalAxiom Atom) [A, ◇C] A :=
      .assumption _ _ (by simp)
    have hdC : DerivationTree (@CS5ModalAxiom Atom) [A, ◇C] (◇C) :=
      .assumption _ _ (by simp)
    -- `A → ◇A → □◇A`
    have hDiaA : DerivationTree (@CS5ModalAxiom Atom) [A, ◇C] (◇A) :=
      .modus_ponens _ _ _
        (.weakening [] [A, ◇C] _ (.ax [] _ (.tDia A)) (fun _ h => nomatch h)) hA
    have hBoxDiaA : DerivationTree (@CS5ModalAxiom Atom) [A, ◇C] (Proposition.box (◇A)) :=
      .modus_ponens _ _ _
        (.weakening [] [A, ◇C] _ (fsDiaBoxedDia A) (fun _ h => nomatch h)) hDiaA
    -- Frobenius at `U := ◇A`, `X := C`.
    have hFrob : DerivationTree (@CS5ModalAxiom Atom) [A, ◇C] (◇((◇A).and C)) :=
      .modus_ponens _ _ _
        (.modus_ponens _ _ _
          (.weakening [] [A, ◇C] _ (fsDiaFrobenius (◇A) C) (fun _ h => nomatch h)) hBoxDiaA)
        hdC
    exact .modus_ponens _ _ _
      (.weakening [] [A, ◇C] _ hElim (fun _ h => nomatch h)) hFrob
  exact deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) [] (◇C) (A.imp B)
    (deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) [◇C] A B hCtx)

/-- **`⊢ C → □ψ` from `⊢ ◇C → ψ`** — the adjunction step, `◇ ⊣ □`, in syntactic form.

`bBox` internalises `C` as `□◇C`; `k` + necessitation on the **closed** premise turn `□◇C` into
`□ψ`. This is the general move the earlier obstruction argument overlooked. -/
private noncomputable def fsBoxInternalise {C ψ : Proposition Atom}
    (h : DerivationTree (@CS5ModalAxiom Atom) [] ((◇C).imp ψ)) :
    DerivationTree (@CS5ModalAxiom Atom) [] (C.imp (Proposition.box ψ)) :=
  fsImpTrans (.ax [] _ (.bBox C)) (fsBoxMono h)

/-- **`CS5 ⊢ (◇A → □B) → □(A → B)`** — the Fischer-Servi axiom `FS` (Simpson's base-`IK`
axiom 5, `Simpson1994` Figure 3-7), **derived**.

This decides task 517's Phase 19 gate in the DERIVED direction. Phase 16's
`cs5_completeness ⟹ CS5 ⊢ FS` had made this a *necessary condition* of the completeness target;
it is now discharged, and the "target is FALSE" branch of the gate is closed.

The derivation is `fsDiaHypImp` (the closed core `⊢ ◇(◇A → □B) → (A → B)`) followed by
`fsBoxInternalise` (the `◇ ⊣ □` adjunction step). See the module docstring for how the
countermodel attempt produced it, and for why `fischer-servi-probe.lean`'s NEGATIVE verdict and
the `fs_context_relative_half` obstruction do not apply: both concern routes that keep the
hypothesis in the context, and this one does not. -/
theorem cs5_fs (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      (((◇A).imp (Proposition.box B)).imp (Proposition.box (A.imp B))) :=
  ⟨fsBoxInternalise (fsDiaHypImp A B)⟩

end Cslib.Logic.Modal
