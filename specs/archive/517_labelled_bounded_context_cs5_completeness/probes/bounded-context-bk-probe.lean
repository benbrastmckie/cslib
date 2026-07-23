import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical

/-! # Task 517 Phase 17 — ROUTE PROBE: does Simpson's `B_K` satisfy `cs5FC''`?

**Target**: mechanize, abstractly over an *arbitrary* IL-model `K`, that the §8.1.1
bounded-context birelation model `B_K` satisfies all five `cs5FC''` conjuncts plus `cs5Incest`,
and does **NOT** satisfy the stronger `cs5FC`.

## Why this is statable now (and why it is decisive)

`B_K` is defined by Simpson over an arbitrary IL-model, so it does **not** need the canonical
model: the probe is available immediately and independently of Ch.5. A positive result:

1. **Confirms the target's frame class.** `cs5FC''` (task 509's pivot) is the *right* weakening:
   `B_K` — the route's own countermodel construction — lands inside it, while the stronger
   `cs5FC` provably excludes `B_K` (`BK_not_cs5FC` below). Had `B_K ⊭ cs5FC''`, the §8.1.1 leg
   would collapse.
2. **Interlocks with `fs_sound''`.** `fs_sound''`
   (`probes/fischer-servi-probe.lean`) proves `cs5FC'' ⊨ FS`. Since `B_K ⊨ cs5FC''`
   (`BK_cs5FC''` below), **every `B_K` validates `FS`**. So the route *cannot* produce a
   countermodel for `FS` via `B_K`, and therefore cannot prove completeness unless `CS5 ⊢ FS`.
   Together with `cs5_completeness_implies_fs_derivable`, this converts the `FS` obligation from
   a necessary condition of the *theorem* into a necessary condition of the *method*.

## Result of this dispatch: POSITIVE, sorry-free, axiom-clean

- `BK_cs5FC''`: all five conjuncts hold, using only `R_w` reflexivity/symmetry/transitivity and
  `≤`-monotonicity (`R_w ⊆ R_w'`) plus domain monotonicity (`D_w ⊆ D_w'`). **`Rdom` is not
  needed** — every conjunct that produces a fresh `B_K`-world reuses the *source* world's label,
  so its domain proof transports along `Dmono` alone. The hypothesis set is therefore minimal.
- `BK_cs5Incest` / `BK_cs5FCIncest`: also hold; `cs5Incest`'s witness is `u' := u` itself
  (`le_refl`), discharged by plain symmetry.
- `BK_not_cs5FC`: `cs5FC` **fails**, mechanized (not asserted) — see below.

## The obstruction, mechanized (`BK_not_cs5FC`)

`cs5FC`'s `≤`-composed transitivity `r w u → u ≤ u' → r u' t → r w t` demands an `R'`-edge
whose endpoints straddle two *different* `≤`-related contexts. But `R'` is **by definition** a
label-level, *within-context* relation: `(w,d) R' (w',d')` requires `w = w'`. `≤'` moves the
world component and fixes the label; `R'` moves the label component and fixes the world. The two
never compose into a cross-context edge, so the conclusion is unreachable whenever `w ≠ w'`.

The proof needs only reflexivity of `R_w`: instantiate at `w := (w,d)`, `u := (w,d)`,
`u' := (w',d)`, `t := (w',d)` for any `w ≤ w'` with `w ≠ w'`. Both `r`-premises are reflexivity
instances and the `≤`-premise is `w ≤ w'`, so `cs5FC` would yield `(w,d) R' (w',d)`, i.e. `w = w'`
— contradiction. `BKWitness_not_cs5FC` instantiates this at a concrete two-point model, so the
failure is a genuine separation and not a vacuous one: `BKWitness` satisfies `cs5FC''`
(`BKWitness_cs5FC''`) and refutes `cs5FC` (`BKWitness_not_cs5FC`) simultaneously.

## Guardrail content (why the theory-to-theory guardrails do not bind)

This file **is** the guardrail argument, mechanized. `BKR`'s definition makes `R'` a label-level,
within-context relation over an *arbitrary* `K` — its `R_w` component relates **labels** `d, d'`
inside one fixed context `w`, never two theories. By contrast `cs5Incest_forces_symm`
(`CS5Canonical.lean:643`) and `cs5TwoSidedR_iff_cs5Tail` (`CS5Canonical.lean:511`) are both
statements about the *canonical* model's theory-to-theory relation. Nothing in this file
mentions, constructs, or quantifies over theories, so neither guardrail is instantiable here and
neither fires. That independence is the point: `B_K ⊨ cs5FC''` is established over every
IL-model, so it cannot be an artifact of any canonical-model-specific collapse.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  §8.1.1 (the `B_K` construction and Lemma 8.1.2). **Citation verified by content**: the
  construction reads `W' = {(w,d) | w ∈ W and d ∈ D_w}`, `(w,d) ≤' (w',d')` iff `w ≤ w'` and
  `d = d'`, `(w,d) R' (w',d')` iff `w = w'` and `R_w(d,d')` — transcribed here verbatim. The
  source's `□` clause (`w,d ⊩ □B` iff for all `w' ≥ w`, for all `d' ∈ D_w'`, `R_w'(d,d')`
  implies `w',d' ⊩ B`) is what motivates the `Dmono`/`Rmono` fields of `ILModel`.
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

/-! ## The abstract IL-model interface -/

/-- An **IL-model** in the shape Simpson's §8.1.1 `B_K` construction consumes:
`K = (W, ≤, {D_w}, {R_w}, {α_w})`. The valuation component `α_w` is omitted — every result in
this file is a pure *frame* fact, and `cs5FC''`/`cs5FC` constrain only the relation.

`Dmono` and `Rmono` are exactly the monotonicity properties Simpson's `□` clause presupposes by
quantifying over `d' ∈ D_w'` and `R_w'` at contexts `w' ≥ w`. `Rrefl` is stated only for labels
in the domain (`D w d → R w d d`), which is all `B_K` ever needs, since `B_K`'s worlds carry
their domain proof. -/
structure ILModel where
  /-- The `≤`-ordered contexts (worlds) of the IL-model. -/
  World : Type u
  /-- The preorder on contexts. -/
  [worldPreorder : Preorder World]
  /-- The labels; `D w` carves out the per-context domain `D_w`. -/
  Label : Type v
  /-- `D w d` says label `d` inhabits context `w`'s domain `D_w`. -/
  D : World → Label → Prop
  /-- `R w d e` is the per-context accessibility `R_w(d,e)` on labels. -/
  R : World → Label → Label → Prop
  /-- Domains grow along `≤`: `w ≤ w' → D_w ⊆ D_w'`. -/
  Dmono : ∀ {w w' : World} {d : Label}, w ≤ w' → D w d → D w' d
  /-- `R_w` is reflexive on `D_w`. -/
  Rrefl : ∀ {w : World} {d : Label}, D w d → R w d d
  /-- `R_w` is symmetric. -/
  Rsymm : ∀ {w : World} {d e : Label}, R w d e → R w e d
  /-- `R_w` is transitive. -/
  Rtrans : ∀ {w : World} {d e f : Label}, R w d e → R w e f → R w d f
  /-- Accessibility grows along `≤`: `w ≤ w' → R_w ⊆ R_w'`. -/
  Rmono : ∀ {w w' : World} {d e : Label}, w ≤ w' → R w d e → R w' d e

attribute [instance] ILModel.worldPreorder

/-! ## The bounded-context birelation model `B_K` -/

/-- `B_K`'s carrier: `W' = {(w,d) | w ∈ W and d ∈ D_w}` (Simpson §8.1.1). A world bundles a
context with a label *and the proof that the label inhabits that context's domain* — the latter
is what lets every frame-condition proof below transport domain membership along `Dmono`. -/
abbrev BKWorld (K : ILModel.{u, v}) := {p : K.World × K.Label // K.D p.1 p.2}

/-- `B_K`'s order: `(w,d) ≤' (w',d')` iff `w ≤ w'` **and** `d = d'` — it moves the *context*
component and pins the label. -/
def BKle (K : ILModel.{u, v}) (p q : BKWorld K) : Prop :=
  p.1.1 ≤ q.1.1 ∧ p.1.2 = q.1.2

/-- `B_K`'s accessibility: `(w,d) R' (w',d')` iff `w = w'` **and** `R_w(d,d')` — it moves the
*label* component and pins the context. This is the definitional fact the whole probe turns on:
`R'` is a label-level, *within-context* relation, so it can never supply the cross-context edge
`cs5FC` demands (`BK_not_cs5FC`). -/
def BKR (K : ILModel.{u, v}) (p q : BKWorld K) : Prop :=
  p.1.1 = q.1.1 ∧ K.R p.1.1 p.1.2 q.1.2

/-- `≤'` is a preorder ("Clearly `≤'` is indeed a partial order", Simpson §8.1.1; a preorder is
all `cs5FC''`/`CKForces` require, and all that is used below). -/
instance BKPreorder (K : ILModel.{u, v}) : Preorder (BKWorld K) where
  le := BKle K
  le_refl _ := ⟨le_refl _, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨le_trans h₁.1 h₂.1, h₁.2.trans h₂.2⟩

theorem BKle_iff {K : ILModel.{u, v}} {p q : BKWorld K} :
    p ≤ q ↔ p.1.1 ≤ q.1.1 ∧ p.1.2 = q.1.2 := Iff.rfl

/-! ## The positive result: `B_K ⊨ cs5FC''` -/

/-- **`B_K` satisfies all five `cs5FC''` conjuncts, over an arbitrary IL-model `K`.** This is the
decisive confirmation that `cs5FC''` is the correct frame class for the §8.1.1 leg.

Per conjunct:
* *reflexivity* — `(w,d) R' (w,d)` is `rfl` plus `R_w`'s reflexivity at `d ∈ D_w` (the world's
  own domain proof).
* *plain transitivity* — both edges live in one context, so this is `R_w`'s transitivity.
* *plain symmetry* — likewise `R_w`'s symmetry.
* *`fourBox` re-basing* — the `≤`-composed premise straddles contexts `w ≤ w'`, but the
  *existential* conclusion `∃ v, w ≤ v ∧ r v t` lets us re-base to `v := (w', d)`: its domain
  proof is `Dmono`, and its edge is `Rmono` (lifting the first edge to `w'`) followed by
  `Rtrans`. This is exactly the weakening that `cs5FC`'s blanket conclusion `r w t` forbids.
* *`FCsym_box`* — dually, witness `t := (w', d)`: `Rmono` then `Rsymm`, domain by `Dmono`. -/
theorem BK_cs5FC'' (K : ILModel.{u, v}) : cs5FC'' (BKR K) := by
  refine ⟨fun p => ⟨rfl, K.Rrefl p.2⟩, ?_, ?_, ?_, ?_⟩
  · -- plain transitivity: both edges are within one context
    rintro p q s ⟨hpq1, hpq2⟩ ⟨hqs1, hqs2⟩
    rw [← hpq1] at hqs1 hqs2
    exact ⟨hqs1, K.Rtrans hpq2 hqs2⟩
  · -- plain symmetry
    rintro p q ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rw [← h1]
    exact K.Rsymm h2
  · -- `fourBox` re-basing: re-base to `(s.1.1, p.1.2)`
    rintro p q q' s ⟨hpq1, hpq2⟩ ⟨hle, hlab⟩ ⟨hq's1, hq's2⟩
    have hps : p.1.1 ≤ s.1.1 := by rw [hpq1, ← hq's1]; exact hle
    refine ⟨⟨(s.1.1, p.1.2), K.Dmono hps p.2⟩, ⟨hps, rfl⟩, rfl, ?_⟩
    have e1 : K.R s.1.1 p.1.2 q.1.2 := K.Rmono hps hpq2
    have e2 : K.R s.1.1 q.1.2 s.1.2 := by rw [hlab, ← hq's1]; exact hq's2
    exact K.Rtrans e1 e2
  · -- `FCsym_box`: witness `(q'.1.1, p.1.2)`
    rintro p q q' ⟨hpq1, hpq2⟩ ⟨hle, hlab⟩
    have hpq' : p.1.1 ≤ q'.1.1 := by rw [hpq1]; exact hle
    refine ⟨⟨(q'.1.1, p.1.2), K.Dmono hpq' p.2⟩, ⟨rfl, ?_⟩, hpq', rfl⟩
    rw [← hlab]
    exact K.Rsymm (K.Rmono hpq' hpq2)

/-- **`B_K` satisfies `cs5Incest`.** The witness is `u' := u` itself (via `le_refl`): `R'`'s edges
never leave their context, so the incestuality clause's `≤`-room is not needed and the claim
reduces to plain symmetry of `R_w`. -/
theorem BK_cs5Incest (K : ILModel.{u, v}) : cs5Incest (BKR K) := by
  rintro p q ⟨h1, h2⟩
  refine ⟨q, le_refl _, h1.symm, ?_⟩
  rw [← h1]
  exact K.Rsymm h2

/-- **`B_K` satisfies `cs5FCIncest`.** Immediate from `BK_cs5FC''` and `BK_cs5Incest`, since
`cs5FCIncest` is `cs5FC''` with its plain-symmetry conjunct replaced by `cs5Incest` — and `B_K`
satisfies both. So `B_K` lands in the canonical route's target frame class as well. -/
theorem BK_cs5FCIncest (K : ILModel.{u, v}) : cs5FCIncest (BKR K) :=
  ⟨(BK_cs5FC'' K).1, (BK_cs5FC'' K).2.1, (BK_cs5FC'' K).2.2.2.1, (BK_cs5FC'' K).2.2.2.2,
    BK_cs5Incest K⟩

/-! ## The negative result: `B_K ⊭ cs5FC`, mechanized -/

/-- **`cs5FC` FAILS on `B_K`** whenever `K` has two distinct `≤`-comparable contexts sharing an
inhabited label — mechanized, not asserted.

`cs5FC`'s `≤`-composed transitivity `r w u → u ≤ u' → r u' t → r w t` is instantiated at
`w := (w,d)`, `u := (w,d)`, `u' := (w',d)`, `t := (w',d)`. Both `r`-premises are mere
*reflexivity* instances of `R'` and the `≤`-premise is `(w,d) ≤' (w',d)`, i.e. `w ≤ w'`. The
conclusion would be `(w,d) R' (w',d)`, whose first component is `w = w'` — contradicting `w ≠ w'`.

The obstruction is structural, not incidental: `R'` pins its two endpoints to the *same* context
by definition, while the hypothesis chain has already moved from `w` to `w'` via `≤'`. No choice
of `K` can repair this, which is why the strengthening from `cs5FC''` to `cs5FC` is unavailable
to the §8.1.1 leg — and why task 509's `cs5FC''` pivot was necessary rather than cosmetic. -/
theorem BK_not_cs5FC (K : ILModel.{u, v}) {w w' : K.World} {d : K.Label}
    (hd : K.D w d) (hle : w ≤ w') (hne : w ≠ w') : ¬ cs5FC (BKR K) := by
  rintro ⟨_hrefl, htrans, _hsymm⟩
  exact hne (htrans (w := ⟨(w, d), hd⟩) (u := ⟨(w, d), hd⟩) (u' := ⟨(w', d), K.Dmono hle hd⟩)
    (t := ⟨(w', d), K.Dmono hle hd⟩) ⟨rfl, K.Rrefl hd⟩ ⟨hle, rfl⟩
    ⟨rfl, K.Rrefl (K.Dmono hle hd)⟩).1

/-! ## A concrete witness: the separation is not vacuous -/

/-- The minimal two-context IL-model (`World := Bool` ordered `false ≤ true`, one label, total
domain and accessibility). Its only role is to witness that `BK_not_cs5FC`'s hypotheses are
satisfiable, so that the `cs5FC''`/`cs5FC` separation below is genuine rather than vacuous. -/
def BKWitness : ILModel.{0, 0} where
  World := Bool
  worldPreorder := inferInstance
  Label := Unit
  D _ _ := True
  R _ _ _ := True
  Dmono _ _ := trivial
  Rrefl _ := trivial
  Rsymm _ := trivial
  Rtrans _ _ := trivial
  Rmono _ _ := trivial

/-- `B_{BKWitness}` satisfies `cs5FC''` — the positive half of the separation. -/
theorem BKWitness_cs5FC'' : cs5FC'' (BKR BKWitness) := BK_cs5FC'' BKWitness

/-- `B_{BKWitness}` refutes `cs5FC` — the negative half. Together with `BKWitness_cs5FC''` this
exhibits **one frame** that is a `cs5FC''`-frame and is *not* a `cs5FC`-frame, so the inclusion
`cs5FC ⊆ cs5FC''` (`cs5FC_implies_cs5FC''`) is **strict**, and `B_K` lies in the gap. -/
theorem BKWitness_not_cs5FC : ¬ cs5FC (BKR BKWitness) :=
  BK_not_cs5FC BKWitness (w := false) (w' := true) (d := ()) trivial
    (by exact Bool.false_le true) (by exact Bool.false_ne_true)

end Cslib.Logic.Modal
