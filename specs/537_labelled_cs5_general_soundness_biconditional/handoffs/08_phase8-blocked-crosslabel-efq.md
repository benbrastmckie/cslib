# Handoff: Phase 8 `[BLOCKED]` — cross-label `efq`/`orE` soundness gap

- **Task**: 537 — Labelled CS5 general soundness biconditional
- **Plan**: `plans/03_direct-route-forest.md` (v3)
- **Phase**: 8 (Main NIK induction, close `boxI` case, assemble `nik_TS5_soundness`)
- **Status**: `[BLOCKED]` — mathematical gap, not an engineering overrun
- **File touched**: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`
  (module docstring only — no proof/theorem code added or altered)
- **Build**: `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green
- **Zero-debt**: no `sorry`, no new axiom, `cs5FCIncest` unweakened, `Graph` unmodified, all
  fourteen Preserved Assets unregressed (untouched)

## What was attempted

Phase 8 as specified: generalize `nik_soundness_onePoint`'s 12-constructor induction over an
arbitrary interpretation `ρ : Label Atom → World` and an arbitrary `cs5FCIncest`/`CKValidFC` model,
with motive

```
∀ ρ, IsDerivationForest G → (∀ a b, G.R a b → r (ρ a) (ρ b)) →
  (∀ ψ ∈ Γ, CKForces r v botForces (ρ ψ.lbl) ψ.prop) →
  CKForces r v botForces (ρ φ.lbl) φ.prop
```

The plan's own risk assessment (§ Risks & Mitigations, Phase 8) states novel work is confined to
`boxI`/`diaE`/`boxE`/`diaI`, with the remaining 9 propositional constructors a direct transcription
of the landed `nik_soundness_onePoint` skeleton. This dispatch confirms `boxI`/`diaE`/`boxE`/`diaI`
ARE tractable exactly as the plan anticipated (via `boxI_lift`, `box_iff_TClosure`/
`dia_iff_TClosure`, `box_gives_here`) — but two of the "straightforward" propositional
constructors, `NIK.efq` and `NIK.orE` (`Deduction.lean:252,277`), are **not** transcribable under
this motive, for a genuine semantic reason.

## The gap, precisely

`NIK.efq (G) (Γ) (x y : Label Atom) (A) (h : NIK 𝒯 G Γ (x ∶ .bot)) : NIK 𝒯 G Γ (y ∶ A)` places
**no constraint whatsoever relating `x` and `y`** — unlike `boxE`/`diaI` (which always carry a
`TClosure` edge between their two labels) or `boxI`/`diaE` (whose fresh `y` is added to the graph,
`G.addEdge x y`, before any subderivation ever interprets it). Discharging the `efq` case under the
motive above requires: from `ih` (applied to `h`) we get `CKForces r v botForces (ρ x)
Proposition.bot`, i.e. `botForces (ρ x)`. The goal is `CKForces r v botForces (ρ y) A` for
**arbitrary** `A` and the **same, externally-supplied** `ρ`. When `y ∉ G.X ∪ ctxLabels Γ` — which
the constructor's type permits, since neither the raw edge-cond nor Γ-cond say anything about `ρ y`
in that case — the adversarial `ρ` may send `y` to a point in a different, `r`/`≤`-disconnected
region of the model where `A` fails while `botForces (ρ x)` still holds elsewhere. `orE`'s
cross-label conclusion (`y` independent of the major premise's label `x`) has the identical
structure and the identical gap.

## Machine-verified countermodel (this dispatch, `lean_run_code`)

```lean
inductive Pt where | one | two
deriving DecidableEq

instance : Preorder Pt where
  le := Eq
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ h1 h2 => h1.trans h2

def rr : Pt → Pt → Prop := fun a b => a = b
-- cs5FCIncest rr: PROVED (all five conjuncts collapse to reflexivity facts under r = ≤ = Eq).

def botF : Pt → Prop := fun w => w = Pt.one
def valF : Pt → Unit → Prop := fun w _ => w = Pt.one
-- botF_uc, valF_uc, bf_val, bf_r, bf_r_wit: ALL PROVED (again trivial, since ≤ = Eq).

example : CKForces rr valF botF Pt.one Proposition.bot := by change botF Pt.one; rfl        -- ✓
example : ¬ CKForces rr valF botF Pt.two (Proposition.atom ()) := by
  change ¬ valF Pt.two (); simp [valF]                                                       -- ✓
```

This is a genuine instance of every hypothesis `CKValidFC cs5FCIncest` quantifies over
(`cs5FCIncest r`, both upward-closure conditions, all three explosion conditions), in which
`botForces` holds at one point (`Pt.one`) and an atomic formula fails at a different,
`r`/`≤`-disconnected point (`Pt.two`). Setting `ρ x := Pt.one`, `ρ y := Pt.two` (with `x`, `y`
disconnected labels — permitted since `efq` imposes no relation between them) falsifies the
`efq` case of the naive "∀ ρ" motive for `A := Proposition.atom ()`.

**Why `nik_soundness_onePoint`'s `efq` case did not hit this**: there, `World := Unit`, so *every*
function `Label Atom → Unit` is trivially constant (`ρ x = ρ y = ()`, unconditionally). The
one-point trick masks the cross-label subtlety rather than resolving it; it does not generalize to
any non-degenerate `World` (which `boxI`/`diaE` require to carry non-trivial modal content at all).

## Why the natural fixes are out of this phase's scope

1. **Restrict to `y ∈ G.X ∪ ctxLabels Γ`, use "`TClosure TS5 G.R` is total on a connected forest"**
   (the module docstring's earlier "Refined analysis" observation that `TS5 = {T,B,Four}` makes
   `TClosure TS5` an equivalence closure, total on a *connected* component). This only half-works:
   `IsDerivationForest` (Phase 6, landed) deliberately allows a **disconnected** forest (finite +
   graded rank + unique parent — no "single root" conjunct), because that is exactly what stays
   provable by plain structural induction without threading construction history. The "always one
   connected tree, built from `Graph.trivial` via a chain of `addEdge`s" fact that would make
   `TClosure TS5 G.R` total on `G.X` is strictly stronger than `IsDerivationForest` and is not
   established anywhere in this file or its dependencies.
2. **Make the whole induction's motive existential**
   (`∃ ρ' agreeing with ρ on G.X ∪ ctxLabels Γ, ... ∧ CKForces r v botForces (ρ' φ.lbl) φ.prop`),
   giving `efq`/`orE` freedom to reassign `ρ` at a genuinely-fresh `y`. This is consistent with
   `boxI`/`diaE` (their fresh `y` is added to `G.X` by `addEdge`, hence "pinned" by the existential
   wrapper's own agreement clause, so they still get the exact value they need) and with the
   label-local rules (shared label pinned identically across every premise). But it still needs
   the `y ∈ G.X ∪ ctxLabels Γ` sub-case of `efq`/`orE` closed by the connectivity fact from (1),
   which remains unavailable — and it is itself a substantial redesign of the induction's shape,
   not a "transcribe the skeleton" step. Inventing this unilaterally, mid-phase, is exactly the
   kind of scope growth the plan's Postmortem Constraints warn against.

## Recommended follow-up scope

A dedicated phase/task scoped to:
1. Prove a connectivity lemma: `IsDerivationForest G` when `G` is additionally known to be built
   from `Graph.trivial` via a finite chain of `addEdge` calls (i.e. threading a "single connected
   component" invariant alongside or instead of `IsDerivationForest`) implies
   `∀ a b ∈ G.X, TClosure TS5 G.R a b`.
2. Reformulate the main induction's motive existentially as sketched above, closing `efq`/`orE`'s
   `y ∈ G.X ∪ ctxLabels Γ` sub-case via (1) and its `y ∉ G.X ∪ ctxLabels Γ` sub-case via the direct
   "reassign `ρ` at the unconstrained fresh label" argument already worked out in this dispatch's
   analysis (not yet reduced to Lean).
3. Re-verify `boxI`/`diaE`/`boxE`/`diaI` and the 8 remaining label-local constructors against the
   existential motive (expected to carry over with the "pinned at the shared/live label" argument,
   but must be re-checked, not assumed).

This is genuinely new proof-architecture work, estimated at re-plan scale (a new phase, likely
100-250 lines), not a continuation of the current dispatch's budget.

## Preserved / unaffected

All fourteen Preserved Assets, and Phases 1-7's landed lemmas (`box_iff_base`, `dia_iff_base`,
`box_iff_TClosure`, `dia_iff_TClosure`, `cs5FCIncest_raise`, `box_gives_here`, `boxI_raise_step`,
`boxI_lift_star`, `IsDerivationForest`, `forest_trivial`, `forest_addEdge_fresh`,
`ht_le_of_reflTransGen`, `raise_subtree`, `siblings_disjoint`, `boxI_lift_ancestor`, `boxI_lift`)
are completely unaffected — no proof code in this file was touched, only the module docstring
(a new "Fifth dispatch" section documenting this finding, appended after the existing "Fourth
dispatch" section; the stale `INTRACTABLE`/`GATE-C`/"What remains" notes were intentionally NOT
removed since Phase 8 did not complete).
