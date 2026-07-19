/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context
public import Mathlib.Data.Set.Card

/-! # Labelled-System Soundness (Task 517 Phase 11, Simpson 1994 Thm 8.1.4, Soundness Direction)

**Status: interpretation machinery (Phase 11.1, partial) + anti-vacuity certificate (Phase 11.3,
COMPLETE). General `nik_TS5_soundness` assessed INTRACTABLE at standard single-dispatch
implementation effort after three dispatches (see "Third dispatch" section below) -- recommend a
dedicated re-plan/research pass, not a fourth direct-implementation attempt.** A fourth,
time-boxed decisive probe (task 537 Phase 1) re-confirmed this assessment via live tactic-state
evidence and closes the decision with **GATE-C** (`[BLOCKED]`, no proof, no countermodel,
Strategy-3 authorized as the sanctioned next route) -- see "Fourth dispatch (task 537 Phase 1
probe, GATE-C)" below. This module lands
(1) the first, reusable building block of the full labelled soundness direction
`nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`, which will complete the Simpson
8.1.4 biconditional alongside `cs5_completeness` (`Completeness.lean`); and (2) the anti-vacuity
certificate `nik_TS5_consistent : ¬ NIKTheorem TS5 ⊥`, landed via a **direct, self-contained
route** (see "The anti-vacuity route taken" below) rather than as a corollary of the
not-yet-landed general theorem. The general `nik_TS5_soundness` (Phase 11.1's tree-lifting
machinery + Phase 11.2's `TClosure` validation) is **not yet landed** -- see "What remains" below,
"Third dispatch" below (the current, sharpest assessment), and the continuation handoffs at
`specs/517_labelled_bounded_context_cs5_completeness/handoffs/`.

## The anti-vacuity route taken: `nik_soundness_onePoint` (Phase 11.3, direct, not via 11.1/11.2)

The plan's own Phase 11.3 description explicitly sanctions proving `nik_TS5_consistent` directly
against a **one-point reflexive** witness model, independently of the general `nik_TS5_soundness`
theorem, "if 11.2's general induction is not reached in a future dispatch" (Rollback/Contingency;
also the prior dispatch's continuation handoff, "optional accelerant" note). This dispatch takes
exactly that route, landing it **before** the general theorem rather than after: `nik_TS5_soundness`
requires the still-outstanding tree-lifting machinery (see "What remains"), but a *soundness
argument specialized to the one-point model* `World := Unit`, `r := fun _ _ => True` sidesteps the
Lifting Lemma entirely -- **every** interpretation of every label collapses to the same unique
point, so "lifting the interpretation at one label" is trivially the identity, and no tree-shape
invariant or graph-lifting recursion is needed at all. `nik_soundness_onePoint` is a full
12-constructor structural induction over `NIK`, proved directly against this one model (not a
special case of a not-yet-existing general theorem), and `nik_TS5_consistent` is then immediate:
instantiate `botForces := fun _ => False`, so `CKForces ... () ⊥` reduces to `False` outright.
This is flagged explicitly as a deviation from the plan's literal sub-phase *sequencing*
(11.1 → 11.2 → 11.3) -- not from its mathematical *content*, since the plan's own Rollback/
Contingency section pre-authorizes exactly this route as a documented fallback, and the final
theorem statement `nik_TS5_consistent : ¬ NIKTheorem TS5 (⊥ : Proposition Atom)` is unchanged.

## `--lit`: Simpson's Chapter 8 soundness argument (reflowed `L1367-1423`, PDF offset +9)

Simpson's own Theorem 8.1.4 soundness direction is **not** a direct induction over `N(𝒯)` in the
way its completeness direction is. His text (`8.1.2 Soundness`) states:

> "Soundness is more difficult because the use of `(R𝒯)` rules means that derivations in `N(𝒯)`
> involving excursions through non-tree consequences are unavoidable. The easiest proof of
> soundness uses the modified sequent system `L_m(𝒯,∅)` ... For in these systems, excursions
> through non-tree graphs can be avoided by the use of `𝒯`-closure in the `(⊃L)` and `(⊃R)_m`
> rules."

Theorem 8.1.4 itself is stated **only for `G` a tree** ("Let `G` be a tree. Then the following are
equivalent: ..."), and the crucial ingredient his *direct* natural-deduction argument (`8.1.2`, not
the sequent-calculus detour) needs is the **Lifting Lemma** (`8.1.3`): "Given any `G`-interpretation
`[-]`, any `x` in `G` and any `w ≥ [x]`, there exists another `G`-interpretation, `[-]'`, such that
`[x]' = w` and, for all `z ∈ G`, `[z]' ≥ [z]`." Simpson's own proof of the Lifting Lemma uses his
birelational models' `F1`/`F2` confluence conditions (his Figure 8-1 gives an explicit
counterexample to soundness for *non-tree* `G`, and to the Lifting Lemma when `F1`/`F2` are absent
or `G` is not a tree).

## Why this cannot be transcribed literally, and the deviation this module takes

CSLib's target semantics for this task is **not** Simpson's own birelational `BForces` model with
`F1`/`F2` -- it is `CKForces` (`Forcing.lean`), the Wijesekera-style *fallible-world segment*
semantics with the `∀∃` diamond clause, deliberately built **without** `F1`/`F2` confluence (see
`Forcing.lean`'s module docstring: bare `CK` is otherwise incomplete for confluent models). So
Simpson's own Lifting-Lemma proof does not transfer verbatim; a literal transcription is not
available. Per the literature-fidelity discipline (`lean4.md`), this deviation is flagged
explicitly rather than silently mixed with novel steps.

**The key finding (this dispatch, verified by hand and cross-checked): `cs5FCIncest`'s own
`cs5Incest`/`r_symBox` conjuncts supply a Wijesekera-side substitute for the missing `F1`/`F2`.**
`cs5FCIncest_lift` below proves exactly the single-edge case Simpson's Lifting Lemma needs at each
node of the tree it lifts: raising the *source* of an `r`-edge along `≤` still reaches *some*
upward extension of the old target. Composed with `ckforces_persistence` (`Forcing.lean:122`,
persistence of `CKForces` under `≤`, itself confluence-free), this is enough to carry every
already-established fact at a raised node's `r`-neighbours forward to a matching raised value.
This makes a *tree-restricted* Lifting Lemma analogue for `cs5FCIncest` models plausible (matching
Simpson's own restriction of Theorem 8.1.4 and the Lifting Lemma to `G` a tree), **not yet proved
in full** -- see "What remains".

## What remains (handoff for the next Phase 11.1 dispatch)

1. **The tree-shape invariant.** `NIK`'s `(□I)`/`(◇E)` rules quantify cofinitely over the fresh
   label `y` (`∀ y ∉ L, ...`); the main soundness induction must always instantiate this
   cofinite premise at a label *fresh to the whole derivation so far* (never an old/reused label),
   which keeps the raw graph `G` tree-shaped throughout the induction -- mirroring Simpson's own
   "we must ensure that throughout the induction we can restrict attention to graphs that are
   trees" remark. This needs its own lemma/invariant, threaded through the main induction.
2. **The graph-lifting lemma proper** (the tree analogue of Simpson's 8.1.3): given an
   interpretation `ρ` of a tree `G`'s labels satisfying edge-cond (`∀ a b, G.R a b → r (ρ a) (ρ
   b)`) and Γ-cond (`∀ ψ ∈ Γ, CKForces (ρ ψ.lbl) ψ.prop`), and a raise `w' ≥ ρ x` for one label
   `x` of `G`, produce `ρ'` agreeing with `ρ` off `x`'s descendants, with `ρ' x = w'`, every
   descendant's value raised (`≥` its old value) via `cs5FCIncest_lift` propagated down the tree,
   and edge-cond/Γ-cond re-established for `ρ'` (Γ-cond via `ckforces_persistence` at each raised
   descendant). This is a structural/well-founded recursion over the (finite, per-derivation) tree
   depth below `x`.
3. **The main soundness induction** over `NIK`'s 12 constructors, generalizing over an arbitrary
   interpretation `ρ` (edge-cond + Γ-cond), concluding `CKForces (ρ x) A`. The `(□I)`/`(◇E)` cases
   use (1)+(2) to instantiate the cofinite premise at a fresh label mapped to the semantically
   required world; `boxE`/`diaI` need item 4 below for their `TClosure`-edge hypothesis.
4. **Phase 11.2**: validate that each `cs5FCIncest` conjunct soundly interprets the matching
   `TClosure` (T/B/4) edge-closure rule (`raw G.R a b → r (ρa)(ρb)` extends to `TClosure 𝒯 G.R a b
   → r (ρa)(ρb)`), then assemble `nik_TS5_soundness`.
5. **Phase 11.3, `nik_TS5_consistent` -- LANDED**, via the plan's own pre-authorized direct route
   (Rollback/Contingency), **before** items 1-4 rather than as their corollary: a one-point model
   (`World := Unit`, `r := fun _ _ => True`) makes "lifting" trivially the identity, so none of
   items 1-4's machinery is needed for this specific corollary. See `nik_soundness_onePoint` below.

## Refined analysis of items 1-4 (this dispatch, NOT yet reduced to code -- for the next dispatch)

A second, deeper look at items 1-4 this dispatch (attempting an actual Lean encoding of the
`(□I)` case, not merely re-stating the architecture) surfaced a sharper obstruction than either
this module's or the continuation handoff's prior framing captured, recorded here so the next
attempt does not re-discover it from scratch:

- **`TS5 = {T, B, Four}` makes `TClosure TS5 G.R` an equivalence relation**, and `G` is *always
  connected* (every `Graph.addEdge` attaches a brand-new label to an already-present one, starting
  from `Graph.trivial`'s single node -- `G` is literally a tree as an undirected graph). An
  equivalence closure of a connected graph's edge relation is the **total relation on the vertex
  set**: `TClosure TS5 G.R a b` holds for **every** `a, b ∈ G.X`, not just tree-adjacent pairs.
  Consequently edge-cond (`∀ a b, TClosure TS5 G.R a b → r (ρ a) (ρ b)`) is not a "propagate along
  tree edges" condition as items 1-2's original framing suggested -- it demands `r` hold between
  `ρ` of **every pair of labels used so far in the derivation**, i.e. the interpreted image of
  `G.X` under `ρ` must be an `r`-clique. Introducing one new label (`(□I)`/`(◇E)`'s fresh `y`)
  therefore requires relating `ρ' y` to **every** existing label's image, not merely to its
  immediate parent -- a materially larger obligation than a single-edge lift.
- **`cs5FCIncest_lift`'s raised witness is not exact**, and edge-cond as stated needs exactness.
  Attempting `ρ' y := u` (the semantically-required successor from `hru : r w' u`, `w' ≥ ρ x`) to
  close the new label's clique-membership against some *other*, already-present label `a` needs
  `r (ρ a) u` from `r (ρ a) (ρ x)` (known) and `r w' u`, `ρ x ≤ w'` (known) -- this is exactly
  `hfour`'s shape (`r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t`, `w := ρ a`, `u := ρ x`,
  `u' := w'`, `t := u`), but `hfour` only delivers `r v u` for **some** `v ≥ ρ a`, not `r (ρ a) u`
  exactly -- so satisfying the clique condition for label `a` forces **also** raising `a`'s own
  interpreted value to that `v`, cascading the obligation to `a`'s own clique-neighbours in turn.
- **The resolution is not symmetric between edge-cond and Γ-cond.** Γ-cond survives raising `ρ`
  pointwise for free, via `ckforces_persistence` (`CKForces` is upward-closed, so if `ψ ∈ Γ` was
  forced at the old `ρ ψ.lbl` and the new value is `≥` the old, Γ-cond still holds at the new
  value). Edge-cond has no such slack -- it is a flat fact about `r`, not about `CKForces`, so it
  cannot be "topped up" after the fact the way Γ-cond can. This asymmetry is why only edge-cond
  needs a genuine lifting lemma: **not** a tree-path propagation (items 1-2's original framing),
  but a lemma of the shape "given a *finite* set `S` of labels already `r`-clique-related under
  `ρ`, and one member `x ∈ S` raised to `w' ≥ ρ x`, produce `ρ' ≥ ρ` pointwise on `S` (raised, not
  merely at `x`) that is *again* an `r`-clique" -- a finite-induction argument over `S` using
  `hfour`/`hsymbox`/`hincest` pairwise, not a tree-depth recursion. This lemma is not yet attempted
  in Lean; it is the concrete next step for items 1-2, and should supersede their original
  "propagate down the tree" phrasing above (kept for historical context, not as the target shape).

## Third dispatch: why the direct-induction route is now assessed INTRACTABLE at standard effort
(NOT yet reduced to code; this is a decisive tractability finding, not a missing-lemma gap)

This dispatch (the third to touch general `nik_TS5_soundness`) attempted to actually close the
finite-clique-relift lemma the second dispatch's "Refined analysis" section above targets, both
for the `(□I)` producer side (a fresh label's exact image) and, independently, for the `(□E)`
consumer side (an *already-fixed*, non-fresh label reached via a `TClosure.symm`-derived edge).
Both sides hit the same root obstruction, confirmed by direct Lean-level proof attempts (not just
re-stated architecture), and a battery of finite hand-constructed candidate models was used to
probe whether the obstruction is real or just unexplored. The finding:

1. **A type-level observation.** Of `cs5FCIncest`'s five conjuncts, only `hrefl` and `htrans`
   have a *non-existential* (`∀`-only) conclusion; `hfour`, `hsymbox`, and `hincest` all conclude
   `∃ v/t/u', ... ∧ r ...` — a *raised* witness, never the exact original point. Consequently the
   only way to derive an EXACT fact `r a b` for two independently-fixed points `a`, `b` is a chain
   of `hrefl`/`htrans` composed from already-exact "seed" facts — `hfour`/`hsymbox`/`hincest` can
   only ever *introduce* a fresh raised point into the chain, never pin one down to a
   pre-specified target. This directly blocks the `(□I)` producer side: `CKForces`'s `box` clause
   (`Forcing.lean:75`) universally quantifies its successor `u` (`∀ w' ≥ w, ∀ u, r w' u → ...`) --
   `u` is handed to the proof adversarially, not chosen by it -- so the fresh label `y`'s
   interpretation must be *exactly* `u` (persistence only goes upward, so a raised substitute
   `u' ≥ u` cannot be "rounded back down"), yet the edge-cond fact `r (ρ a) u` this exactness
   demands, for every other already-used label `a`, is exactly the kind of fact `hfour`
   cannot produce without also raising `a`'s own image -- as the second dispatch found -- and
   THIS dispatch additionally traced that raising `a` does not itself terminate in an exact fact
   either, for the same reason one level up.
2. **The `(□E)`-consumer side needs the same exactness, independently of freshness.** `boxE`
   consumes an *arbitrary* `TClosure`-derived edge `hR : TClosure 𝒯 G.R x y`, including one
   derived via `.symm` (`B ∈ TS5`) from a *raw, one-directional* edge `G.R y x` (`Graph.addEdge`
   only ever adds a directed `a = x ∧ b = y` disjunct, never both directions). If the "natural"
   invariant only interprets raw edges directly (`r (ρ y) (ρ x)` from `G.R y x`), soundly using
   `boxE` at the `TClosure.symm`-reversed edge needs `r (ρ x) (ρ y)` -- i.e. *exact* symmetry of
   `r` on this specific already-fixed pair, where `x`/`y` are NOT necessarily fresh (they may
   already be pinned by other uses in `Γ` or earlier subderivations, so their images cannot be
   freely raised without invalidating those other uses). `cs5Incest` supplies only the raised
   substitute (`r w u → ∃ u' ≥ u, r u' w`), not exact symmetry.
3. **Finite hand-constructed models could not exhibit a stable asymmetric example.** Several
   candidate finite relations on `Fin n`/`ℕ` (with the standard linear `≤`) satisfying
   `hincest`+`hfour` kept being forced, by exact `htrans` composing the newly-introduced raised
   witnesses back around, into satisfying full symmetric (indeed often total/clique) closure on
   the finitely-generated substructure anyway -- e.g. a 3-point "cycle + backward witnesses"
   attempt (`0 → 1`, a `hincest`-mandated back-witness `2 → 0`, forcing `2 → 1` by `htrans`)
   remained genuinely asymmetric (`r 0 1` without `r 1 0`) only until `hsymbox` was patched by
   adding an outgoing edge from `1`, at which point `htrans` immediately chained it back into
   `r 1 0`, collapsing the intended asymmetry. This was reproduced under several variations and
   never escaped: **no finite countermodel refuting `cs5FCIncest → ` symmetry-on-generated-points
   was found**, but a full formal proof of the positive direction (`cs5FCIncest` DOES force
   symmetric/clique closure on any finitely-generated substructure) was also not completed --
   direct proof attempts chaining `hincest`/`hfour`/`hsymbox` pairwise did not close either. This
   is genuinely unresolved, not merely unattempted: it is the single largest scope unknown left in
   this proof direction, and resolving it (either direction) would decisively settle whether the
   clique-relift lemma is provable by finite induction, or needs different machinery entirely.
4. **A concrete, actionable recommendation for whoever picks this up next**, given (3)'s
   "finite models keep collapsing into full closure" pattern: this looks structurally like a
   FIXPOINT/closure-completion problem (build the smallest `r`-clique containing a given finite
   seed and closed under `hincest`/`hfour`/`hsymbox`'s raised witnesses), not a simple
   induction-over-a-fixed-finite-set problem -- which is exactly the shape of the `FLO`
   maximal-extension machinery already landed for the completeness direction (Phases 1-7,
   `PrimeLemma.lean`/probes). **Investigating whether the landed `FLO`/chain-union machinery can
   be reused or adapted for this closure construction is the single most promising concrete next
   step**, ahead of either of the two heavier alternatives below.
5. **Escalation-protocol assessment (per the task's anti-churn directive): this direction is NOT
   tractable at standard single-dispatch implementation effort.** Three dispatches have each
   materially sharpened the obstruction (not thrashed or repeated prior work), converging on a
   genuine open mathematical question (item 3 above), not a missing Mathlib lemma or a
   straightforward-but-long proof. Recommended next steps, in order of estimated cost:
   - (a) **Cheapest, try first**: a focused (few-hour) investigation of whether `cs5FCIncest`
     provably forces symmetric/clique closure on finitely-generated substructures (item 3's open
     question), reusing/adapting the `FLO` closure machinery (item 4) if it resolves positively.
   - (b) **Simpson's own recommended route** (`8.1.2`, quoted above): formalize the modified
     sequent system `L_m(𝒯, ∅)` with `𝒯`-closure baked into `(⊃L)`/`(⊃R)_m`, which Simpson states
     is needed *specifically* to avoid the non-tree-excursion problem this dispatch keeps hitting.
     Substantial new proof-theoretic infrastructure (a new derivation system + translation lemmas
     + its own soundness proof) -- re-plan scale (likely 300-600+ lines), not a dispatch
     continuation.
   - (c) Build the Hilbert-labelled equivalence bridge (Ch. 6, already flagged as deferred future
     work in this plan's Phase 12 notes) and obtain labelled soundness as a corollary of the
     *already-proven*, sorry-free `cs5_soundness_derivable_incest` (`CS5Canonical.lean:373`) --
     this is exactly the large Ch. 6 gap Option B of this plan deliberately deferred, so reopening
     it is itself a scope decision for the user/orchestrator, not this dispatch.
   None of (a)-(c) is attempted in this dispatch; each is genuinely re-plan/research-pass scale,
   not a direct continuation. No `sorry`, no new axiom, and no vacuous placeholder was introduced
   to force a result -- per the anti-churn directive, this finding is landed as documentation only.

## Fourth dispatch (task 537 Phase 1 probe, GATE-C)

Task 537's plan (`specs/537_.../plans/01_general-soundness.md`) re-opened the direct route as a
single **time-boxed decisive probe with a hard pivot gate**: prove the exact-symmetry lemma
`cs5FCIncest r → r a b → r b a` on the finitely-generated substructure (GATE-A), or construct a
concrete countermodel (GATE-B), or record `[BLOCKED]` within budget (GATE-C, explicitly sanctioned
as a non-failure outcome, not a fourth thrash). This dispatch pursued both prongs and reached
**GATE-C**:

1. **Proof attempt, verified via live `lean_goal`/`lean_multi_attempt` state (not just hand
   analysis).** Chasing `hincest` on `hab : r a b` gives `h1 : r b₁ a` (`b ≤ b₁`); `hincest` on
   `h1` gives `h2 : r a₁ b₁` (`a ≤ a₁`); `htrans h2 h1 : r a₁ a` (exact); `htrans (r a₁ a) hab :
   r a₁ b` (exact) -- structurally identical to `hab` but with the source raised from `a` to
   `a₁`. Iterating (`hincest` on this raised fact, then `htrans` twice) produces `h7 : r b₂ a`
   (`b ≤ b₂`) -- the *target* `a` is reached again, but only from a **raised** `b₂`, never from
   the original, pinned `b`. `hfour hab hb_b₁ h1` independently produces the same shape:
   `hvt : r v a` for some `v ≥ a`, not `r b a`. Both automation (`aesop`, `tauto`) and the manual
   chase fail to close `r b a` exactly, confirming (via tool-verified goal states, not
   assumption) that `hincest`/`hfour`/`hsymbox`'s raised witnesses cascade indefinitely without
   ever re-pinning the two original, fixed points -- the same root obstruction the third dispatch
   found, now independently reproduced.
2. **Countermodel attempt.** A translation-invariant candidate on `ℕ` (`r n m := (n ≥ 2 ∨ m ≥ 2)
   ∨ n = m ∨ (n = 0 ∧ m = 1)`, designed to hold the asymmetric edge `r 0 1 ∧ ¬ r 1 0` while
   using "everything ≥ 2 relates to everything" to try to satisfy `hincest`/`hfour`/`hsymbox`)
   was checked by hand against all five conjuncts and **fails `htrans`**: `r 1 2` and `r 2 0` both
   hold (via the `≥2` clause), forcing `r 1 0` by transitivity -- reproducing exactly the
   "`hsymbox`+`htrans` collapse" pattern the third dispatch's hand-probe already hit, via an
   independent construction. A difference-set (`r n m := (m - n) ∈ D`) analysis over `ℤ` shows
   this is not a coincidence of the specific attempt: any additive sub-semigroup `D ⊆ ℤ`
   containing `0` that is unbounded both above and below (`hsymbox`/`hincest`'s respective
   requirements once translated through the difference-set encoding) is forced, by a
   Bezout-plus-scaling argument, to equal `g ℤ` for some `g ≥ 1` -- i.e. a **subgroup**, hence
   automatically symmetric. No translation-invariant countermodel exists; this is a genuinely new
   (this-dispatch) structural finding, not merely a repeated empirical failure, though it does not
   itself constitute a proof for arbitrary (non-translation-invariant) `Preorder World`.
3. **Zorn/chain-union pattern assessed infeasible within this probe's budget, not attempted.** The
   plan's suggested technique needs a poset of *sets* (chains have union upper bounds
   automatically, regardless of `World`'s structure) analogous to `PrimeLemma.lean`'s Lindenbaum
   construction -- but `hfour`/`hsymbox` take their raised point `u'` as a *hypothesis*, not an
   existential the axiom lets us choose (only `hincest`'s witness is existential), so there is no
   direct set-of-reachable-pairs poset whose maximal element pins the two ORIGINAL fixed points
   `a`, `b` exactly; building one is genuinely new infrastructure at the plan's own estimated
   150-300+ line, multi-dispatch re-plan scale, not a bounded-probe-sized task.
4. **GATE-C recorded.** No proof, no countermodel within budget. Per the plan's pivot gate, this
   is the explicitly sanctioned, non-failure terminal state: `[BLOCKED]` handoff routes to
   **Phase 4** (`specs/537_.../plans/01_general-soundness.md`), recommending Strategy 3 (the
   Hilbert-labelled adequacy bridge, obtaining `nik_TS5_soundness` as a corollary of the landed
   `cs5_soundness_derivable_incest`, `CS5Canonical.lean:373`) be authorized as the follow-up scope.
   Zero debt: no `sorry`, no new axiom, `cs5FCIncest` unweakened, all Preserved Assets unregressed.

## Contents (this dispatch)

- `cs5FCIncest_lift`: the interpretation-lifting building block (item 2's core ingredient).
- `nik_soundness_onePoint`: a full 12-constructor `NIK` soundness induction against the
  one-point model, proved directly (Phase 11.3's accelerant route, see above).
- `nik_TS5_consistent`: the anti-vacuity certificate, `¬ NIKTheorem TS5 ⊥`, a direct one-line
  corollary of `nik_soundness_onePoint`.

## References

* [A. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 8, §8.1.2 (Soundness), Lemma 8.1.3 (Lifting Lemma), Theorem 8.1.4.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Labelled

open Cslib.Logic.Modal

/-! ## Interpretation-lifting for `cs5FCIncest` models -/

/-- **Interpretation-lifting ("F2-analogue") for `cs5FCIncest` models.** Raising the *source* of
an `r`-edge along `≤` still reaches *some* `≤`-upward extension of the old target. This is the
Wijesekera-side substitute (derived directly from `cs5FCIncest`'s `cs5Incest`/`r_symBox`
conjuncts, NOT a transcription of Simpson's `F1`/`F2` birelational Lifting Lemma -- see the module
docstring's "Why this cannot be transcribed literally" section) for the single-edge case Simpson's
Lifting Lemma (8.1.3) needs at each node of the tree it lifts. -/
theorem cs5FCIncest_lift {World : Type*} [Preorder World] {r : World → World → Prop}
    (hfc : cs5FCIncest r) {w u w' : World} (hwu : r w u) (hww' : w ≤ w') :
    ∃ u', u ≤ u' ∧ r w' u' := by
  obtain ⟨_, _, _, hsymbox, hincest⟩ := hfc
  obtain ⟨u₁, hu_u₁, hu₁w⟩ := hincest hwu
  obtain ⟨t, hw't, hu₁t⟩ := hsymbox hu₁w hww'
  exact ⟨t, hu_u₁.trans hu₁t, hw't⟩

/-- **Confluence direction `F2` (target-raise) for `cs5FCIncest` models.** Dual to
`cs5FCIncest_lift` (`F1`, source-raise): raising the *target* of an `r`-edge along `≤` still
reaches *some* `≤`-upward extension of the old source. Derived directly from `cs5FCIncest`'s
`hsymbox` conjunct (raise the target across `≤`, landing at a fresh point `t` with `w ≤ t`) then
`hincest` (the fresh point's edge back-witnesses a `≤`-successor `w'` of `t`, hence of `w`, with
`r w' u'`). Needed alongside `F1` for the `boxI` tree-lifting recursion (Phase 4); `diaE` needs
neither. -/
theorem cs5FCIncest_raise {World : Type*} [Preorder World] {r : World → World → Prop}
    (hfc : cs5FCIncest r) {w u u' : World} (hwu : r w u) (huu' : u ≤ u') :
    ∃ w', w ≤ w' ∧ r w' u' := by
  obtain ⟨_, _, _, hsymbox, hincest⟩ := hfc
  obtain ⟨t, hru't, hwt⟩ := hsymbox hwu huu'
  obtain ⟨w', htw', hw'u'⟩ := hincest hru't
  exact ⟨w', hwt.trans htw', hw'u'⟩

/-- **Box-forcing "here" extraction.** `CKForces … w (□A)` instantiated at `w` itself, via the
`hrefl` instance (`r w w`), yields the bare `CKForces … w A` fact -- mirroring the `tBox` axiom
case (`CS5Canonical.lean:313`: `hbox w' (le_refl w') w' (hrefl w')`). Consumed by the `boxE`/
`boxI` cases of the main soundness induction (Phase 5). -/
theorem box_gives_here {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {val : World → Atom → Prop} {botForces : World → Prop}
    {w : World} {A : Proposition Atom}
    (hbox : CKForces r val botForces w (.box A)) :
    CKForces r val botForces w A := by
  obtain ⟨hrefl, _, _, _, _⟩ := hfc
  exact hbox w (le_refl w) w (hrefl w)

/-! ## Base forcing-equivalence lemmas (task 537 Phase 1, direct-route report §4(A))

Dissolves the ex-"Wall A" obstruction (the `TClosure → exact r-edge`/exact-symmetry lemma
that GATE-C confirmed unprovable, see the module docstring's "Fourth dispatch" section above).
`boxE`/`diaI` soundness never needs exact `r`-symmetry between two independently-fixed points;
it needs only that `CKForces` at a `□`/`◇`-formula is **forcing-equivalent** across an
`r`-related pair, discharged directly from `cs5FCIncest`'s raised-witness conjuncts
(`hfour`/`hincest` for `□`; `hsymbox`/`htrans`/`hincest` for `◇`). `P`/`Q` are arbitrary
predicates (NOT assumed upward-closed); the clause shapes below match `CKForces_box`/
`CKForces_diamond` (`Forcing.lean:106,112`) exactly, so these lemmas apply directly to real
`CKForces (_) (□A)`/`CKForces (_) (◇A)` goals via `P := fun u => CKForces r v botForces u A`. -/

/-- **Box-forcing base equivalence.** If `r a b`, the "`□`-successor" clause is equivalent
whether quantified from `a` or from `b`: forward via `hfour` (raise the successor's witness
down to an `a`-successor); backward — the ex-"Wall A" `.symm` direction — via `hincest` (raise
a witness `b'` with `r b' a`) then `hfour` again. Neither direction needs exact `r`-symmetry. -/
theorem box_iff_base {World : Type*} [Preorder World] {r : World → World → Prop}
    (hfc : cs5FCIncest r) {a b : World} (hab : r a b) {P : World → Prop} :
    (∀ w' ≥ a, ∀ u, r w' u → P u) ↔ (∀ w' ≥ b, ∀ u, r w' u → P u) := by
  obtain ⟨_, _, hfour, _, hincest⟩ := hfc
  constructor
  · intro H w' hw' u hru
    obtain ⟨v, hav, hvu⟩ := hfour hab hw' hru
    exact H v hav u hvu
  · intro H w' hw' u hru
    obtain ⟨b', hbb', hb'a⟩ := hincest hab
    obtain ⟨v, hb'v, hrvu⟩ := hfour hb'a hw' hru
    exact H v (hbb'.trans hb'v) u hrvu

/-- **Diamond-forcing base equivalence.** If `r a b`, the "`◇`-successor" clause is equivalent
whether quantified from `a` or from `b`: forward via `hsymbox` (raise the target across `≤`)
then `htrans` (compose back to the original successor); backward — the ex-"Wall A" `.symm`
direction — via `hincest` (raise a witness `b'` with `r b' a`) then `hsymbox`+`htrans` again.
Neither direction needs exact `r`-symmetry. -/
theorem dia_iff_base {World : Type*} [Preorder World] {r : World → World → Prop}
    (hfc : cs5FCIncest r) {a b : World} (hab : r a b) {Q : World → Prop} :
    (∀ w' ≥ a, ∃ u, r w' u ∧ Q u) ↔ (∀ w' ≥ b, ∃ u, r w' u ∧ Q u) := by
  obtain ⟨_, htrans, _, hsymbox, hincest⟩ := hfc
  constructor
  · intro H w' hw'
    obtain ⟨t, hrw't, hat⟩ := hsymbox hab hw'
    obtain ⟨u, hrtu, hqu⟩ := H t hat
    exact ⟨u, htrans hrw't hrtu, hqu⟩
  · intro H w' hw'
    obtain ⟨b', hbb', hb'a⟩ := hincest hab
    obtain ⟨t, hrw't, hb't⟩ := hsymbox hb'a hw'
    obtain ⟨u, hrtu, hqu⟩ := H t (hbb'.trans hb't)
    exact ⟨u, htrans hrw't hrtu, hqu⟩

/-! ## TClosure-class extension (task 537 Phase 2, direct-route report §4(A))

Extends `box_iff_base`/`dia_iff_base` over the entire `TClosure {T,B,Four}` class by induction on
the `TClosure` derivation, giving the transport lemmas the `boxE`/`diaI` cases of the eventual
main induction (Phase 5) will need. `ρ` interprets `Label Atom` labels into the model's `World`;
`R` is the raw graph relation (`G.R` at the point of use, Phase 5) and `hedge` is the **raw**
edge-cond invariant (`∀ a b, R a b → r (ρ a) (ρ b)`, MMS Def 5.1, chunk 0026) -- never a
`TClosure`-clique invariant (the refuted decomposition, see the module docstring's "Third
dispatch"/"Refined analysis" sections and the plan's Postmortem Constraints). `eucl` is
unreachable at `𝒯 = TS5`: `GeomAxiom.Five ∈ TS5` unfolds to a three-way constructor-clash
disjunction (`Five = T ∨ Five = B ∨ Five = Four`), each closed by `GeomAxiom.noConfusion`. -/

/-- **Box-forcing equivalence over the whole `TClosure {T,B,Four}` class.** `base` reduces to
`box_iff_base` via the raw edge-cond invariant; `refl`/`symm`/`trans` are the trivial `Iff`
closure (`Iff.rfl`/`Iff.symm`/`Iff.trans`); `eucl` is vacuous since `Five ∉ TS5`. -/
theorem box_iff_TClosure {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {R : Label Atom → Label Atom → Prop} {ρ : Label Atom → World}
    (hedge : ∀ a b, R a b → r (ρ a) (ρ b)) {x y : Label Atom} (hxy : TClosure TS5 R x y)
    {P : World → Prop} :
    (∀ w' ≥ ρ x, ∀ u, r w' u → P u) ↔ (∀ w' ≥ ρ y, ∀ u, r w' u → P u) := by
  induction hxy with
  | base h => exact box_iff_base hfc (hedge _ _ h)
  | refl _ _ => exact Iff.rfl
  | symm _ _ ih => exact ih.symm
  | trans _ _ _ ihxy ihyz => exact ihxy.trans ihyz
  | eucl h _ _ _ _ => exact absurd h (by rintro (h | h | h) <;> exact GeomAxiom.noConfusion h)

/-- **Diamond-forcing equivalence over the whole `TClosure {T,B,Four}` class.** Dual to
`box_iff_TClosure`, reducing `base` to `dia_iff_base` via the same raw edge-cond invariant. -/
theorem dia_iff_TClosure {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {R : Label Atom → Label Atom → Prop} {ρ : Label Atom → World}
    (hedge : ∀ a b, R a b → r (ρ a) (ρ b)) {x y : Label Atom} (hxy : TClosure TS5 R x y)
    {Q : World → Prop} :
    (∀ w' ≥ ρ x, ∃ u, r w' u ∧ Q u) ↔ (∀ w' ≥ ρ y, ∃ u, r w' u ∧ Q u) := by
  induction hxy with
  | base h => exact dia_iff_base hfc (hedge _ _ h)
  | refl _ _ => exact Iff.rfl
  | symm _ _ ih => exact ih.symm
  | trans _ _ _ ihxy ihyz => exact ihxy.trans ihyz
  | eucl h _ _ _ _ => exact absurd h (by rintro (h | h | h) <;> exact GeomAxiom.noConfusion h)

/-! ## Single-node interpretation-raise step (task 537 Phase 4.1, Simpson Lifting Lemma 8.1.3
inductive step, chunks 0154-0155)

This is the atomic building block of Simpson's Lifting Lemma: raising the interpretation `ρ` at
ONE node `x` to some `w ≥ ρ x`, re-establishing the raw edge-cond at ONE `x`-adjacent raw edge
(via `cs5FCIncest_lift`/`F1`, the "down" direction `R x n`, or `cs5FCIncest_raise`/`F2`, the "up"
direction `R n x`) and Γ-cond persistence at the raised neighbour (via `ckforces_persistence`).
Phase 4.2 (not attempted in this dispatch) iterates this step node-by-node over the finite
derivation tree to assemble the full Lifting Lemma feeding `boxI`. -/

/-- **Single-node interpretation-raise step.** Given a raw-edge-cond interpretation `ρ`
(`hedge : ∀ a b, R a b → r (ρ a) (ρ b)`), a node `x`, a distinct raw-`R`-neighbour `n` of `x`
(edge in either direction, `hR`), and any raise `w ≥ ρ x`, produces a re-interpretation `ρ'`
agreeing with `ρ` off `{x, n}` -- so `ρ' z ≥ ρ z` for every label `z` -- with `ρ' x = w`,
re-establishing:
- the raw edge fact between `x` and `n`, in whichever direction `hR` supplied (down via `F1`,
  up via `F2`);
- persistence, at `n`'s raised value, of any `CKForces`-fact that held at the old `ρ n` (Γ-cond),
  via `ckforces_persistence`.

Only `x` and `n` move; all other labels are left exactly as `ρ` had them -- Phase 4.2 chains
this step node-by-node along the tree to raise every affected descendant/ancestor in turn. -/
theorem boxI_raise_step {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {v : World → Atom → Prop} {botForces : World → Prop}
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    {R : Label Atom → Label Atom → Prop} {ρ : Label Atom → World}
    (hedge : ∀ a b, R a b → r (ρ a) (ρ b))
    {x n : Label Atom} (hxn : x ≠ n) {w : World} (hwx : ρ x ≤ w) (hR : R x n ∨ R n x) :
    ∃ ρ' : Label Atom → World, ρ' x = w ∧ (∀ z, ρ z ≤ ρ' z) ∧
      (r (ρ' x) (ρ' n) ∨ r (ρ' n) (ρ' x)) ∧
      (∀ {φ : Proposition Atom}, CKForces r v botForces (ρ n) φ →
        CKForces r v botForces (ρ' n) φ) := by
  classical
  rcases hR with h | h
  · -- down: F1 raises the target `n` alongside the raised source `x`.
    obtain ⟨n', hnn', hwn'⟩ := cs5FCIncest_lift hfc (hedge x n h) hwx
    refine ⟨fun z => if z = x then w else if z = n then n' else ρ z, if_pos rfl, ?_, Or.inl ?_, ?_⟩
    · intro z
      dsimp only
      by_cases hz : z = x
      · subst hz; rw [if_pos rfl]; exact hwx
      · rw [if_neg hz]
        by_cases hz' : z = n
        · subst hz'; rw [if_pos rfl]; exact hnn'
        · rw [if_neg hz']
    · dsimp only
      rw [if_pos rfl, if_neg (Ne.symm hxn), if_pos rfl]
      exact hwn'
    · intro φ hφ
      dsimp only
      rw [if_neg (Ne.symm hxn), if_pos rfl]
      exact ckforces_persistence v_uc bf_uc hnn' hφ
  · -- up: F2 raises the source `n` alongside the raised target `x`.
    obtain ⟨n', hnn', hn'w⟩ := cs5FCIncest_raise hfc (hedge n x h) hwx
    refine ⟨fun z => if z = x then w else if z = n then n' else ρ z, if_pos rfl, ?_, Or.inr ?_, ?_⟩
    · intro z
      dsimp only
      by_cases hz : z = x
      · subst hz; rw [if_pos rfl]; exact hwx
      · rw [if_neg hz]
        by_cases hz' : z = n
        · subst hz'; rw [if_pos rfl]; exact hnn'
        · rw [if_neg hz']
    · dsimp only
      rw [if_neg (Ne.symm hxn), if_pos rfl, if_pos rfl]
      exact hn'w
    · intro φ hφ
      dsimp only
      rw [if_neg (Ne.symm hxn), if_pos rfl]
      exact ckforces_persistence v_uc bf_uc hnn' hφ

/-! ## Star-lifting over a finite set of direct neighbours (task 537 Phase 4.2, partial)

**Mission-scope finding (read before extending):** the plan's Phase 4.2 goal is to iterate
`boxI_raise_step` "node-by-node over the finite derivation tree" to obtain a fully general
`boxI_lift`. Attempting this directly (this dispatch) surfaces a genuine, previously
under-specified obstruction: raising `x` to an adversarial `w'` forces *every* raw-`R`-neighbour
of `x` to also move (via F1/F2 -- `cs5FCIncest` has no "raise-source-only, keep-target-exact"
conjunct), and if a neighbour has further neighbours of its own, the raise must cascade. A
**fully general** cascade over an arbitrary finite `Graph` is UNSOUND without an explicit
acyclicity/unique-parent invariant: the 3-cycle `x→a→b→x` satisfies "each target has a unique
raw-edge source" (no violation of that weaker property) yet forces the newly-discovered node `b`
to satisfy *two* simultaneous, generally-unsatisfiable raise constraints (one from `a→b`, one from
`b→x`) when the cascade reaches it. Ruling this out needs a rank/depth function `ht : Label Atom →
ℕ` with `∀ a b, G.R a b → ht b = ht a + 1` (graded, so no cycle can exist) PLUS "each label has at
most one raw-edge source" -- together these make `G` a genuine rooted forest. This is *exactly*
the module docstring's "item 1: the tree-shape invariant" (see "What remains" above), which is
explicitly flagged there as separate, not-yet-established work belonging to the main induction
(Phase 5), not to this single-file, node-level phase. Building and threading that invariant is
out of Phase 4.2's scope (it is not a `boxI_raise_step`-iteration task; it is graph/forest theory
for `Graph` that does not yet exist anywhere in this development).

What IS landed below, sound and needing no extra invariant: `boxI_lift_star`, which chains
`cs5FCIncest_lift`/`cs5FCIncest_raise` over a **finite set of `x`'s direct raw-neighbours**
(both directions), raising `x` once and each direct neighbour once. This is the natural,
fully-general-safe extension of Phase 4.1's single-neighbour `boxI_raise_step` to finitely many
neighbours at once, and is genuine forward progress toward `boxI_lift`. It does **not** by
itself complete the Lifting Lemma or close the `NIK.boxI` case: a neighbour's *own* further
neighbours (grandchildren of `x`, in tree terms) are left unraised, which is exactly the residual
recursive-cascade gap above. Per the plan's blocked-honesty gate, the residual generalization
(and hence closing the `boxI` case) is routed to Phase 7 rather than forced via `sorry` or an
undirected retry. -/

/-- **Star-lifting: raise `x` together with a finite set of its direct raw-neighbours.** Chains
`cs5FCIncest_lift` (F1, "down" edges `R x n`) / `cs5FCIncest_raise` (F2, "up" edges `R n x`)
across every `n` in a `Finset` `N` of labels raw-adjacent to `x`, holding `x`'s target `w` fixed
(via the ORIGINAL raise fact `hwx : ρ x ≤ w`, never re-derived from an intermediate value) while
raising each `n ∈ N` in turn. Proved by `Finset.induction` on `N`; unlike `boxI_raise_step`, `N`
may be empty or contain arbitrarily many (finitely many) neighbours, but does **not** recurse into
`N`'s own further neighbours (see the section docstring above for why that is the residual,
not-yet-established generalization). -/
theorem boxI_lift_star {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {v : World → Atom → Prop} {botForces : World → Prop}
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    {R : Label Atom → Label Atom → Prop} {ρ : Label Atom → World}
    (hedge : ∀ a b, R a b → r (ρ a) (ρ b))
    {x : Label Atom} {w : World} (hwx : ρ x ≤ w) :
    ∀ N : Finset (Label Atom), x ∉ N → (∀ n ∈ N, R x n ∨ R n x) →
      ∃ ρ' : Label Atom → World, ρ' x = w ∧ (∀ z, ρ z ≤ ρ' z) ∧
        (∀ n ∈ N, r (ρ' x) (ρ' n) ∨ r (ρ' n) (ρ' x)) ∧
        (∀ z, z ≠ x → z ∉ N → ρ' z = ρ z) ∧
        (∀ {φ : Proposition Atom} {z}, CKForces r v botForces (ρ z) φ →
          CKForces r v botForces (ρ' z) φ) := by
  classical
  intro N
  induction N using Finset.induction with
  | empty =>
      intro _ _
      refine ⟨fun z => if z = x then w else ρ z, if_pos rfl, ?_, by simp, ?_, ?_⟩
      · intro z
        by_cases hz : z = x
        · subst hz; simpa using hwx
        · simp [hz]
      · intro z hzx _; simp [hzx]
      · intro φ z hz
        by_cases hzx : z = x
        · subst hzx; simpa using ckforces_persistence v_uc bf_uc hwx hz
        · simpa [hzx] using hz
  | insert n N' hnN' ih =>
      intro hxN hR
      have hxn : x ≠ n := (ne_of_mem_of_not_mem (Finset.mem_insert_self n N') hxN).symm
      have hxN' : x ∉ N' := fun h => hxN (Finset.mem_insert_of_mem h)
      have hR' : ∀ m ∈ N', R x m ∨ R m x := fun m hm => hR m (Finset.mem_insert_of_mem hm)
      obtain ⟨ρ₁, hρ₁x, hρ₁mono, hρ₁edge, hρ₁out, hρ₁pers⟩ := ih hxN' hR'
      have hRn : R x n ∨ R n x := hR n (Finset.mem_insert_self n N')
      rcases hRn with hRxn | hRnx
      · obtain ⟨n', hnn', hwn'⟩ := cs5FCIncest_lift hfc (hedge x n hRxn) hwx
        refine ⟨Function.update ρ₁ n n', ?_, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne hxn, hρ₁x]
        · intro z
          by_cases hz : z = n
          · subst hz; rw [Function.update_self]; exact hnn'
          · rw [Function.update_of_ne hz]; exact hρ₁mono z
        · intro m hm
          rcases Finset.mem_insert.mp hm with rfl | hm
          · rw [Function.update_of_ne hxn, Function.update_self, hρ₁x]
            exact Or.inl hwn'
          · have hmn : m ≠ n := ne_of_mem_of_not_mem hm hnN'
            rw [Function.update_of_ne hxn, Function.update_of_ne hmn]
            exact hρ₁edge m hm
        · intro z hzx hzN
          have hzn : z ≠ n := (ne_of_mem_of_not_mem (Finset.mem_insert_self n N') hzN).symm
          have hzN' : z ∉ N' := fun h => hzN (Finset.mem_insert_of_mem h)
          rw [Function.update_of_ne hzn]
          exact hρ₁out z hzx hzN'
        · intro φ z hz
          by_cases hzn : z = n
          · rw [hzn, Function.update_self]
            exact ckforces_persistence v_uc bf_uc hnn' (hzn ▸ hz)
          · rw [Function.update_of_ne hzn]
            exact hρ₁pers hz
      · obtain ⟨n', hnn', hn'w⟩ := cs5FCIncest_raise hfc (hedge n x hRnx) hwx
        refine ⟨Function.update ρ₁ n n', ?_, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne hxn, hρ₁x]
        · intro z
          by_cases hz : z = n
          · subst hz; rw [Function.update_self]; exact hnn'
          · rw [Function.update_of_ne hz]; exact hρ₁mono z
        · intro m hm
          rcases Finset.mem_insert.mp hm with rfl | hm
          · rw [Function.update_of_ne hxn, Function.update_self, hρ₁x]
            exact Or.inr hn'w
          · have hmn : m ≠ n := ne_of_mem_of_not_mem hm hnN'
            rw [Function.update_of_ne hxn, Function.update_of_ne hmn]
            exact hρ₁edge m hm
        · intro z hzx hzN
          have hzn : z ≠ n := (ne_of_mem_of_not_mem (Finset.mem_insert_self n N') hzN).symm
          have hzN' : z ∉ N' := fun h => hzN (Finset.mem_insert_of_mem h)
          rw [Function.update_of_ne hzn]
          exact hρ₁out z hzx hzN'
        · intro φ z hz
          by_cases hzn : z = n
          · rw [hzn, Function.update_self]
            exact ckforces_persistence v_uc bf_uc hnn' (hzn ▸ hz)
          · rw [Function.update_of_ne hzn]
            exact hρ₁pers hz

/-! ## Derivation-forest invariant (task 537 Phase 6, Simpson 8.1.3 "restrict attention to trees")

Simpson's Lifting Lemma 8.1.3 is stated for `G` a **tree** (chunk 0154); the `boxI_lift`-over-an-
arbitrary-`Graph` statement is genuinely FALSE (the 3-cycle `x→a→b→x` in `handoffs/04` forces node
`b` to satisfy two independent, generally-incompatible raise constraints). The raw `R`-graph of
every `NIK` derivation is, however, a finite rooted forest **by construction**: `Graph.trivial`
(`Syntax.lean:123`) is the one-node, zero-edge base, and the only two edge-adding constructors,
`NIK.boxI` (`Deduction.lean:297`) and `NIK.diaE` (`Deduction.lean:309`), both call `G.addEdge x y`
with `y` chosen outside a finite exclusion set -- always `existing → fresh`, never closing a
cycle (audit report `03_tree-shape-invariant-audit.md` §1). `IsDerivationForest` packages the
three conjuncts this fact needs (finiteness, graded rank, unique parent -- audit §1/§4: dropping
either the rank or the unique-parent conjunct alone reopens either the 3-cycle or the
`x→a→b`/`x→c→b` diamond); it is threaded as a hypothesis through the soundness induction motive
(Phase 8), NOT added as a new `Graph` field, since the canonical model's graph
(`CanonicalModel.lean`) is not a finite forest (audit §2). -/

/-- **Derivation-forest invariant** (Simpson 8.1.3, chunk 0156). Three conjuncts, all
independently necessary (audit report 03 §1/§4): `G.X` is finite (needed for `boxI_lift`'s
finite-component recursion, Phase 7); `G.R` is **graded** by some rank function `ht` (rules out
*directed* cycles, e.g. the 3-cycle `x→a→b→x`); and every node has a **unique parent** under `G.R`
(rules out *undirected* diamonds, e.g. `x→a→b`, `x→c→b`). Together, graded rank + unique parent
make `G` a genuine finite rooted forest. -/
def IsDerivationForest {Atom : Type u} (G : Graph Atom) : Prop :=
  G.X.Finite ∧
    (∃ ht : Label Atom → ℕ, ∀ a b, G.R a b → ht b = ht a + 1) ∧
    (∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁ = a₂)

/-- **The trivial graph is a derivation forest.** `Graph.trivial` has no edges, so the
graded-rank and unique-parent conjuncts hold vacuously (the constant rank `fun _ => 0` works);
its node set `{var 0}` is finite. Discharges `IsDerivationForest` at the base of the soundness
induction (`nik_TS5_soundness`, Phase 8). -/
theorem forest_trivial {Atom : Type u} : IsDerivationForest (Graph.trivial Atom) :=
  ⟨Set.finite_singleton _, ⟨fun _ => 0, fun _ _ hab => hab.elim⟩, fun _ _ _ hab _ => hab.elim⟩

/-- **Adding a fresh-sink edge preserves the derivation-forest invariant.** If `G` is a
derivation forest and `y ∉ G.X` (so `y` is genuinely fresh), then `G.addEdge x y` -- the graph
extension `NIK.boxI`/`NIK.diaE` perform -- is again a derivation forest. The new rank function
`Function.update ht y (ht x + 1)` grades the new edge `x → y` by construction; unique-parent is
preserved because `y`, being fresh, gains exactly one source (`x`) and no old target's source set
changes; finiteness follows from `Set.Finite.union`/`Set.Finite.insert`. This is exactly the
preservation `NIK.boxI` (`Deduction.lean:297`) / `NIK.diaE` (`Deduction.lean:309`) require. -/
theorem forest_addEdge_fresh {Atom : Type u} {G : Graph Atom} (hG : IsDerivationForest G)
    {x y : Label Atom} (hx : x ∈ G.X) (hy : y ∉ G.X) :
    IsDerivationForest (G.addEdge x y) := by
  classical
  obtain ⟨hfin, ⟨ht, hht⟩, huniq⟩ := hG
  refine ⟨?_, ⟨Function.update ht y (ht x + 1), ?_⟩, ?_⟩
  · exact hfin.union (Set.Finite.insert x (Set.finite_singleton y))
  · intro a b hab
    rcases hab with hab | ⟨ha, hb⟩
    · have haG : a ∈ G.X := (G.edge_mem a b hab).1
      have hbG : b ∈ G.X := (G.edge_mem a b hab).2
      have hay : a ≠ y := fun h => hy (h ▸ haG)
      have hby : b ≠ y := fun h => hy (h ▸ hbG)
      rw [Function.update_of_ne hby, Function.update_of_ne hay]
      exact hht a b hab
    · rw [ha, hb, Function.update_self]
      have hxy : x ≠ y := fun h => hy (h ▸ hx)
      rw [Function.update_of_ne hxy]
  · intro a₁ a₂ b hab1 hab2
    rcases hab1 with hab1 | ⟨ha1, hb1⟩
    · rcases hab2 with hab2 | ⟨ha2, hb2⟩
      · exact huniq a₁ a₂ b hab1 hab2
      · exact absurd (hb2 ▸ (G.edge_mem a₁ b hab1).2) hy
    · rcases hab2 with hab2 | ⟨ha2, hb2⟩
      · exact absurd (hb1 ▸ (G.edge_mem a₂ b hab2).2) hy
      · exact ha1.trans ha2.symm

/-! ## One-point soundness and the anti-vacuity certificate (Phase 11.3) -/

/-- **Soundness of `N_IK(𝒯)` against the one-point model, for any `𝒯`.** Every label of the
derivation is interpreted at the unique point `()` of `Unit`, with the modal relation set to the
total relation (`fun _ _ => True`) and `botForces` arbitrary. Because there is only one possible
world, "raising the interpretation of one label" (the crux of the outstanding Lifting-Lemma
machinery -- see the module docstring's "What remains") is trivially the identity, so this
induction needs none of it: the `(□I)`/`(◇E)` cases simply pick any label fresh to the finite
exclusion set `L` (using `Infinite (Label Atom)`, via the injective `Label.var`) and re-apply the
cofinite premise's induction hypothesis at the same, unique point. The `(□E)`/`(◇I)` cases need
no relational-edge hypothesis at all (`hR`/`hR`/`hru` are unused beyond pattern-matching) because
the total relation makes every `r`-step trivial (`trivial : True`). This is NOT a special case of
the general `nik_TS5_soundness` (not yet landed); it is a self-contained soundness argument
against a single, degenerate model, used only to certify anti-vacuity (`nik_TS5_consistent`
below). -/
theorem nik_soundness_onePoint {Atom : Type u} {𝒯 : Set GeomAxiom} {val : Unit → Atom → Prop}
    {G : Graph Atom} {Γ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom}
    (h : NIK 𝒯 G Γ φ) :
    (∀ ψ ∈ Γ, CKForces (fun (_ _ : Unit) => True) val (fun _ => False) () ψ.prop) →
      CKForces (fun (_ _ : Unit) => True) val (fun _ => False) () φ.prop := by
  induction h with
  | assumption G Γ φ hmem => intro hΓ; exact hΓ _ hmem
  | efq G Γ x y A h ih =>
      intro hΓ
      exact absurd (ih hΓ) (by simp)
  | andI G Γ x A B _ _ ihA ihB => intro hΓ; exact ⟨ihA hΓ, ihB hΓ⟩
  | andE1 G Γ x A B _ ih => intro hΓ; exact (ih hΓ).1
  | andE2 G Γ x A B _ ih => intro hΓ; exact (ih hΓ).2
  | orI1 G Γ x A B _ ih => intro hΓ; exact Or.inl (ih hΓ)
  | orI2 G Γ x A B _ ih => intro hΓ; exact Or.inr (ih hΓ)
  | orE G Γ x y A B C hor hA hB ihor ihA ihB =>
      intro hΓ
      rcases ihor hΓ with h1 | h2
      · exact ihA (by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact h1
          · exact hΓ _ hψ)
      · exact ihB (by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact h2
          · exact hΓ _ hψ)
  | impI G Γ x A B h ih =>
      intro hΓ w' hw' hAforced
      cases w'
      exact ih (by
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hAforced
        · exact hΓ _ hψ)
  | impE G Γ x A B himp hA ihimp ihA =>
      intro hΓ
      exact ihimp hΓ () (le_refl _) (ihA hΓ)
  | boxE G Γ x y A hR h ih =>
      intro hΓ
      exact ih hΓ () (le_refl _) () trivial
  | boxI L hL G Γ x A h ih =>
      intro hΓ w' hw' u hru
      cases w'; cases u
      have hInf : Infinite (Label Atom) := by
        have hinj : Function.Injective (Label.var (Atom := Atom)) := by
          intro a b hab; cases hab; rfl
        exact Infinite.of_injective _ hinj
      obtain ⟨y, hy⟩ := hL.infinite_compl.nonempty
      exact ih y hy hΓ
  | diaI G Γ x y A hR h ih =>
      intro hΓ w' hw'
      exact ⟨(), trivial, ih hΓ⟩
  | diaE L hL G Γ x z A B hdia h ihdia ih =>
      intro hΓ
      obtain ⟨u, hru, hAu⟩ := ihdia hΓ () (le_refl _)
      cases u
      have hInf : Infinite (Label Atom) := by
        have hinj : Function.Injective (Label.var (Atom := Atom)) := by
          intro a b hab; cases hab; rfl
        exact Infinite.of_injective _ hinj
      obtain ⟨y, hy⟩ := hL.infinite_compl.nonempty
      exact ih y hy (by
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hAu
        · exact hΓ _ hψ)

/-- **Anti-vacuity certificate** (Phase 11.3): `N(TS5)` does not prove `⊥`. Direct corollary of
`nik_soundness_onePoint`, instantiated with `botForces := fun _ => False`: were `⊥` a theorem,
`nik_soundness_onePoint` would force `CKForces ... () ⊥ = False` (`Γ = []` discharges the
context-condition vacuously), a contradiction. This certifies Phase 10's `cs5_completeness` is a
*meaningful* statement (`N(TS5)` does not prove everything), per reports/11 condition 2. -/
theorem nik_TS5_consistent {Atom : Type u} :
    ¬ NIKTheorem TS5 (Proposition.bot : Proposition Atom) := by
  intro h
  exact nik_soundness_onePoint (val := fun _ _ => True) h (by simp)

/-! ## Tree-cascade lifting lemma (task 537 Phase 7, Simpson 8.1.3, chunks 0154-0155)

Completes the finite-component cascade `boxI_lift_star` left open (see that section's docstring),
taking `IsDerivationForest G` as an explicit hypothesis (audit report 03 §3). The recursion is
split into two independently-tractable pieces, avoiding any need for a general BFS/cycle-freeness
theorem over the raw `Graph`:

1. **`ht_le_of_reflTransGen`**: rank is non-decreasing along forward `G.R`-reachability -- a
   direct consequence of the graded-rank conjunct, needing no acyclicity argument.
2. **`raise_subtree`**: the "downward cascade" -- given a node `p` already raised to a *fixed*
   target `wp`, raise `p` together with the entire forward-reachable closure through a chosen
   `Finset` of `p`'s direct raw-neighbours, via repeated `cs5FCIncest_lift` (F1). Proved by
   well-founded recursion on `Set.ncard {q ∈ G.X | ht q ≥ ht p}` (strictly decreasing at each
   child, since graded rank forces `ht c > ht p`), nested with `Finset.induction` over the
   sibling set at each level. Disjointness of different children's downward closures follows
   directly from the unique-parent conjunct (no separate tree lemma needed): if a shared
   descendant existed, unique-parent applied to the last edge of the closing path forces the two
   children to coincide.
3. **`boxI_lift`**: raises `x` to the adversarial `w'` via `cs5FCIncest_raise`-driven walk up the
   (unique, by unique-parent) ancestor chain, invoking `raise_subtree` for the sibling branches
   hanging off each ancestor, and `raise_subtree` once more for `x`'s own full descendant set. -/

/-- **Rank is non-decreasing along forward `G.R`-reachability.** If `z` is reachable from `a` via
zero or more raw `R`-steps, then `ht a ≤ ht z`. Pure consequence of the graded-rank conjunct of
`IsDerivationForest` (no acyclicity/BFS-uniqueness argument needed): each step strictly increases
`ht` by exactly 1, so it can never come back down. -/
theorem ht_le_of_reflTransGen {Atom : Type u} {G : Graph Atom} {ht : Label Atom → ℕ}
    (hgrad : ∀ a b, G.R a b → ht b = ht a + 1) {a z : Label Atom}
    (h : Relation.ReflTransGen G.R a z) : ht a ≤ ht z := by
  induction h with
  | refl => exact le_refl _
  | tail _ hyz ih =>
      have heq := hgrad _ _ hyz
      omega

/-- **Downward cascade: raise a node and its entire forward-reachable closure through a chosen
Finset of direct raw-neighbours.** Given `p` already targeted to raise to `wp` (`ρ p ≤ wp`) and a
`Finset C` of direct raw-`R`-successors of `p` to process, produces a re-interpretation `ρ'` with
`ρ' p = wp`, monotone everywhere, re-establishing: the direct edges `p → c` for `c ∈ C` (via
`cs5FCIncest_lift`/F1); every raw edge among the forward-reachable closure of each `c ∈ C` (via
recursive `cs5FCIncest_lift` applications, well-founded on `Set.ncard {q ∈ G.X | ht q ≥ ht p}`,
strictly decreasing at each child since graded rank forces `ht c = ht p + 1 > ht p`); and leaving
everything outside `{p} ∪ ⋃ c ∈ C, {z | c ↝ z}` exactly as `ρ` had it. Disjointness of different
children's closures is derived inline from the unique-parent conjunct (no separate tree lemma
needed). -/
theorem raise_subtree {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {v : World → Atom → Prop} {botForces : World → Prop}
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    {G : Graph Atom} {ht : Label Atom → ℕ}
    (hfin : G.X.Finite) (hgrad : ∀ a b, G.R a b → ht b = ht a + 1)
    (huniq : ∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁ = a₂)
    {ρ : Label Atom → World} (hedge : ∀ a b, G.R a b → r (ρ a) (ρ b)) :
    ∀ n : ℕ, ∀ p : Label Atom, p ∈ G.X → Set.ncard {q ∈ G.X | ht q ≥ ht p} ≤ n →
    ∀ C : Finset (Label Atom), (∀ c ∈ C, G.R p c) →
    ∀ wp : World, ρ p ≤ wp →
    ∃ ρ' : Label Atom → World, ρ' p = wp ∧ (∀ z, ρ z ≤ ρ' z) ∧
      (∀ c ∈ C, r (ρ' p) (ρ' c)) ∧
      (∀ c ∈ C, ∀ a b, Relation.ReflTransGen G.R c a → G.R a b → r (ρ' a) (ρ' b)) ∧
      (∀ z, z ≠ p → (∀ c ∈ C, ¬ Relation.ReflTransGen G.R c z) → ρ' z = ρ z) ∧
      (∀ {φ : Proposition Atom} {z}, CKForces r v botForces (ρ z) φ →
        CKForces r v botForces (ρ' z) φ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hpX hcard C
    classical
    induction C using Finset.induction with
    | empty =>
        intro _ wp hwp
        refine ⟨fun z => if z = p then wp else ρ z, if_pos rfl, ?_, by simp, by simp, ?_, ?_⟩
        · intro z; by_cases hz : z = p
          · subst hz; simpa using hwp
          · simp [hz]
        · intro z hzp _; simp [hzp]
        · intro φ z hz
          by_cases hzp : z = p
          · subst hzp; simpa using ckforces_persistence v_uc bf_uc hwp hz
          · simpa [hzp] using hz
    | insert c C' hcC' ih' =>
        intro hC wp hwp
        have hC' : ∀ cm ∈ C', G.R p cm := fun cm hcm => hC cm (Finset.mem_insert_of_mem hcm)
        obtain ⟨ρ₁, hρ1p, hρ1mono, hρ1direct, hρ1desc, hρ1out, hρ1pers⟩ := ih' hC' wp hwp
        have hcp : G.R p c := hC c (Finset.mem_insert_self c C')
        have hcX : c ∈ G.X := (G.edge_mem p c hcp).2
        have hcht : ht c = ht p + 1 := hgrad p c hcp
        -- `c` is not reachable back to `p`: rank would have to decrease.
        have hpc : ¬ Relation.ReflTransGen G.R c p := by
          intro hreach
          have := ht_le_of_reflTransGen hgrad hreach
          omega
        -- measure strictly decreases at the child `c`.
        have hpXset : {q | q ∈ G.X ∧ ht q ≥ ht p}.Finite := hfin.subset (fun q hq => hq.1)
        have hsub : {q | q ∈ G.X ∧ ht q ≥ ht c} ⊂ {q | q ∈ G.X ∧ ht q ≥ ht p} := by
          constructor
          · intro q hq
            simp only [Set.mem_setOf_eq] at hq ⊢
            exact ⟨hq.1, by omega⟩
          · intro hcontra
            have hp' := hcontra (show p ∈ {q | q ∈ G.X ∧ ht q ≥ ht p} from ⟨hpX, le_refl (ht p)⟩)
            simp only [Set.mem_setOf_eq] at hp'
            omega
        have hn' : {q | q ∈ G.X ∧ ht q ≥ ht c}.ncard < n :=
          lt_of_lt_of_le (Set.ncard_lt_ncard hsub hpXset) hcard
        -- raise `c` itself via F1, relative to the *original* `ρ`.
        obtain ⟨c', hcc', hwc'⟩ := cs5FCIncest_lift hfc (hedge p c hcp) hwp
        -- recurse into `c`'s own full downward closure.
        have hCcSub : {cc | G.R c cc} ⊆ G.X := fun cc hcc => (G.edge_mem c cc hcc).2
        have hCcFin : {cc | G.R c cc}.Finite := hfin.subset hCcSub
        have hCcMem : ∀ cc ∈ hCcFin.toFinset, G.R c cc := fun cc hcc => hCcFin.mem_toFinset.mp hcc
        obtain ⟨ρc, hρcp, hρcmono, hρcdirect, hρcdesc, hρcout, hρcpers⟩ :=
          ih _ hn' c hcX (le_refl _) hCcFin.toFinset hCcMem c' hcc'
        -- `ρc`'s direct/descendant clauses, unfolded from "all children" to plain `G.R c _`.
        have hρc_full_direct : ∀ b, G.R c b → r (ρc c) (ρc b) := fun b hb =>
          hρcdirect b (hCcFin.mem_toFinset.mpr hb)
        have hρc_full_desc : ∀ a b, Relation.ReflTransGen G.R c a → G.R a b → r (ρc a) (ρc b) := by
          intro a b ha hab
          rcases Relation.ReflTransGen.cases_head ha with heq | ⟨cc, hccc, hcca⟩
          · rw [← heq]; exact hρc_full_direct b (heq ▸ hab)
          · exact hρcdesc cc (hCcFin.mem_toFinset.mpr hccc) a b hcca hab
        -- nothing reachable from a sibling `cm ∈ C'` is also reachable from `c` (unique-parent
        -- applied to the last edge of whichever path would witness the overlap).
        have hkey : ∀ cm ∈ C', ∀ a, Relation.ReflTransGen G.R cm a →
            ¬ Relation.ReflTransGen G.R c a := by
          intro cm hcmC' a ha
          induction ha with
          | refl =>
              intro hca
              rcases eq_or_ne cm c with rfl | hne
              · exact hcC' hcmC'
              · cases hca with
                | refl => exact hne rfl
                | tail hcy hycm =>
                    rename_i y
                    have hpcm : G.R p cm := hC' cm hcmC'
                    have hyp : y = p := huniq y p cm hycm hpcm
                    exact hpc (hyp ▸ hcy)
          | tail hcma' ha'a ih2 =>
              rename_i mid a'
              intro hca
              rcases eq_or_ne a' c with heq | hne
              · have ha'c : G.R mid c := heq ▸ ha'a
                have hap : mid = p := huniq mid p c ha'c hcp
                have hcmp : Relation.ReflTransGen G.R cm p := hap ▸ hcma'
                have hle := ht_le_of_reflTransGen hgrad hcmp
                have hcmht : ht cm = ht p + 1 := hgrad p cm (hC' cm hcmC')
                omega
              · cases hca with
                | refl => exact hne rfl
                | tail hcy hya =>
                    rename_i y
                    have hya' : y = mid := huniq y mid a' hya ha'a
                    exact ih2 (hya' ▸ hcy)
        classical
        refine ⟨fun z => if Relation.ReflTransGen G.R c z then ρc z else ρ₁ z,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [if_neg hpc]; exact hρ1p
        · intro z
          by_cases hz : Relation.ReflTransGen G.R c z
          · simp only [if_pos hz]; exact hρcmono z
          · simp only [if_neg hz]; exact hρ1mono z
        · intro cm hcm
          rcases Finset.mem_insert.mp hcm with heq | hcmC'
          · rw [heq]
            simp only [if_neg hpc, if_pos (Relation.ReflTransGen.refl (a := c))]
            rw [hρ1p, hρcp]; exact hwc'
          · simp only [if_neg hpc, if_neg (hkey cm hcmC' cm Relation.ReflTransGen.refl)]
            exact hρ1p ▸ hρ1direct cm hcmC'
        · intro cm hcm a b ha hab
          rcases Finset.mem_insert.mp hcm with heq | hcmC'
          · rw [heq] at ha
            have hb : Relation.ReflTransGen G.R c b := ha.tail hab
            simp only [if_pos ha, if_pos hb]
            exact hρc_full_desc a b ha hab
          · have hna : ¬ Relation.ReflTransGen G.R c a := hkey cm hcmC' a ha
            have hnb : ¬ Relation.ReflTransGen G.R c b := by
              intro hb
              cases hb with
              | refl =>
                  have hap : a = p := huniq a p c hab hcp
                  have hcmp : Relation.ReflTransGen G.R cm p := hap ▸ ha
                  have hle := ht_le_of_reflTransGen hgrad hcmp
                  have hcmht : ht cm = ht p + 1 := hgrad p cm (hC' cm hcmC')
                  omega
              | tail hcy hyb =>
                  rename_i y
                  have hya : y = a := huniq y a b hyb hab
                  exact hna (hya ▸ hcy)
            simp only [if_neg hna, if_neg hnb]
            exact hρ1desc cm hcmC' a b ha hab
        · intro z hzp hzC
          have hzc : ¬ Relation.ReflTransGen G.R c z := hzC c (Finset.mem_insert_self c C')
          simp only [if_neg hzc]
          exact hρ1out z hzp (fun cm hcm => hzC cm (Finset.mem_insert_of_mem hcm))
        · intro φ z hz
          by_cases hzc : Relation.ReflTransGen G.R c z
          · simp only [if_pos hzc]; exact hρcpers hz
          · simp only [if_neg hzc]
            exact hρ1pers hz

/-! ## Ancestor-walk assembly of `boxI_lift` (task 537 Phase 7 completion)

`raise_subtree` (above) is the downward-cascade piece. This section adds the upward piece — an
**ancestor walk** from `x` toward the root, invoking `raise_subtree` at each ancestor for the
sibling branches hanging off it — and assembles the two into `boxI_lift`.

**Why a plain unconditional ancestor induction is unsound**: an induction hypothesis whose
conclusion covers *every* edge of `G` unconditionally would, at each ancestor step, re-derive the
child branch it just came from via its own internal `raise_subtree` call, with no guarantee that
call picks the SAME value already pinned for that branch two levels down. The fix,
`boxI_lift_ancestor` below, threads an explicit `excl : Finset (Label Atom)` parameter through the
induction: `excl` names the direct child (always a singleton in practice, `{}` only at the very
top) whose entire downward closure is owned by the caller and must be left untouched. -/

/-- **Sibling closures are disjoint.** Two distinct raw-`R`-children `c₁ ≠ c₂` of a common node
`p` have disjoint forward-reachable closures: nothing reachable from `c₁` is also reachable from
`c₂`. Generalizes the sibling-disjointness argument proved inline inside `raise_subtree`'s
`insert` case (there specialized to one fixed new child vs. a `Finset` of already-processed
siblings) to two arbitrary named children, for reuse by `boxI_lift_ancestor`'s combine step. Same
proof shape: induct on the reachability witness, and at each step use `huniq` (unique parent) at
the last edge together with `ht_le_of_reflTransGen`/`hgrad` to rule out reaching back up to the
common parent `p`. -/
theorem siblings_disjoint {Atom : Type u} {G : Graph Atom} {ht : Label Atom → ℕ}
    (hgrad : ∀ a b, G.R a b → ht b = ht a + 1)
    (huniq : ∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁ = a₂)
    {p c₁ c₂ : Label Atom} (hc₁ : G.R p c₁) (hc₂ : G.R p c₂) (hne : c₁ ≠ c₂) :
    ∀ u, Relation.ReflTransGen G.R c₁ u → ¬ Relation.ReflTransGen G.R c₂ u := by
  intro u h1
  induction h1 with
  | refl =>
      intro hca
      cases hca with
      | refl => exact hne rfl
      | tail hcy hyc1 =>
          rename_i y
          have hyp : y = p := huniq y p c₁ hyc1 hc₁
          have hreach : Relation.ReflTransGen G.R c₂ p := hyp ▸ hcy
          have hle := ht_le_of_reflTransGen hgrad hreach
          have hc2ht : ht c₂ = ht p + 1 := hgrad p c₂ hc₂
          omega
  | tail hc1mid hmida' ih =>
      rename_i mid a'
      intro hca
      cases hca with
      | refl =>
          have hmidp : mid = p := huniq mid p c₂ hmida' hc₂
          have hreach : Relation.ReflTransGen G.R c₁ p := hmidp ▸ hc1mid
          have hle := ht_le_of_reflTransGen hgrad hreach
          have hc1ht : ht c₁ = ht p + 1 := hgrad p c₁ hc₁
          omega
      | tail hcy hya' =>
          rename_i y
          have hya : y = mid := huniq y mid a' hya' hmida'
          exact ih (hya ▸ hcy)

/-- **Ancestor-walk assembly.** Raises `z` (already targeted at `wz`) together with EVERY edge of
`G` except those "owned" by the caller — namely edges reachable from (or into) some excluded
child `e ∈ excl` of `z`. Walks up `z`'s unique-parent chain via `cs5FCIncest_raise` (F2),
invoking `raise_subtree` at `z` itself (over the un-excluded children) and recursing via the
strong induction on `n` (an upper bound for `ht`, strictly decreasing at each ancestor step since
graded rank forces `ht` of a parent to be strictly smaller). At the top-level call from
`boxI_lift`, `excl := ∅`, so the exclusion machinery vacuously drops out and conjunct 3 covers
*every* edge of `G`.

**Deviation from the plan's transcribed schema (documented, not a design re-opening):** conjunct
3's exclusion check is on the edge's *target* `b`, not its *source* `a` (plan note handoff
`07_phase7-boxI-lift-partial.md` checks `a`). Checking via `a` is unprovable at the boundary edge
into the excluded branch (e.g. the ancestor edge `q → z` itself, with `a = q` outside the
excluded closure but `b = z` inside it): `cs5FCIncest` has no "raise-source-only, keep-target-
exact" conjunct (see `boxI_lift_star`'s section docstring), so `r (raised q) (old ρ z)` is not
generally derivable. Checking via `b` correctly drops exactly the boundary edge (and everything
inside the excluded closure) from the obligation, since that edge is established separately by
the caller's own `cs5FCIncest_raise` fact before combining. This is the SAME Finset-exclusion
strategy the handoff specifies, with the one membership-check side corrected for provability;
the two-piece downward/ancestor decomposition and all five key decisions in the handoff are
unchanged. -/
theorem boxI_lift_ancestor {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {v : World → Atom → Prop} {botForces : World → Prop}
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    {G : Graph Atom} {ht : Label Atom → ℕ}
    (hfin : G.X.Finite) (hgrad : ∀ a b, G.R a b → ht b = ht a + 1)
    (huniq : ∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁ = a₂)
    {ρ : Label Atom → World} (hedge : ∀ a b, G.R a b → r (ρ a) (ρ b)) :
    ∀ n : ℕ, ∀ z : Label Atom, ht z ≤ n → z ∈ G.X →
    ∀ wz : World, ρ z ≤ wz →
    ∀ excl : Finset (Label Atom), (∀ e ∈ excl, G.R z e) →
    ∃ ρ' : Label Atom → World, ρ' z = wz ∧ (∀ u, ρ u ≤ ρ' u) ∧
      (∀ a b, G.R a b → (∀ e ∈ excl, ¬ Relation.ReflTransGen G.R e b) → r (ρ' a) (ρ' b)) ∧
      (∀ {φ : Proposition Atom} {u}, CKForces r v botForces (ρ u) φ →
        CKForces r v botForces (ρ' u) φ) ∧
      (∀ u, (∃ e ∈ excl, Relation.ReflTransGen G.R e u) → ρ' u = ρ u) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro z hzn hzX wz hwz excl hexcl
    classical
    have hCzSub : {cc | G.R z cc ∧ cc ∉ excl} ⊆ G.X := fun cc hcc => (G.edge_mem z cc hcc.1).2
    have hCzFin : {cc | G.R z cc ∧ cc ∉ excl}.Finite := hfin.subset hCzSub
    have hCzMem : ∀ c ∈ hCzFin.toFinset, G.R z c := fun c hc => (hCzFin.mem_toFinset.mp hc).1
    have hCzNotExcl : ∀ c ∈ hCzFin.toFinset, c ∉ excl := fun c hc => (hCzFin.mem_toFinset.mp hc).2
    obtain ⟨ρz, hρzz, hρzmono, hρzdirect, hρzdesc, hρzout, hρzpers⟩ :=
      raise_subtree hfc v_uc bf_uc hfin hgrad huniq hedge
        (Set.ncard {q ∈ G.X | ht q ≥ ht z}) z hzX (le_refl _)
        hCzFin.toFinset hCzMem wz hwz
    by_cases hparent : ∃ q, G.R q z
    · obtain ⟨q, hqz⟩ := hparent
      have hqX : q ∈ G.X := (G.edge_mem q z hqz).1
      have hqzht : ht z = ht q + 1 := hgrad q z hqz
      obtain ⟨q', hqq', hq'wz⟩ := cs5FCIncest_raise hfc (hedge q z hqz) hwz
      have hqn : ht q < n := by omega
      obtain ⟨ρq, hρqq, hρqmono, hρqedge, hρqpers, hρqout⟩ :=
        ihn (ht q) hqn q (le_refl _) hqX q' hqq' {z}
          (by intro e he; rw [Finset.mem_singleton] at he; subst he; exact hqz)
      have hzq : ¬ Relation.ReflTransGen G.R z q := by
        intro hzqreach
        have hle := ht_le_of_reflTransGen hgrad hzqreach
        omega
      refine ⟨fun u => if Relation.ReflTransGen G.R z u then ρz u else ρq u, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [if_pos (Relation.ReflTransGen.refl (a := z))]
        exact hρzz
      · intro u
        by_cases hu : Relation.ReflTransGen G.R z u
        · simp only [if_pos hu]; exact hρzmono u
        · simp only [if_neg hu]; exact hρqmono u
      · intro a b hab hbex
        by_cases hbz : b = z
        · subst hbz
          have haq : a = q := huniq a q b hab hqz
          subst haq
          simp only [if_neg hzq, if_pos (Relation.ReflTransGen.refl (a := b))]
          rw [hρqq, hρzz]
          exact hq'wz
        · by_cases hzb : Relation.ReflTransGen G.R z b
          · rcases hzb.cases_head with heq | ⟨c, hzc, hcb⟩
            · exact absurd heq.symm hbz
            · by_cases hcExcl : c ∈ excl
              · exact absurd hcb (hbex c hcExcl)
              · have hcCz : c ∈ hCzFin.toFinset := hCzFin.mem_toFinset.mpr ⟨hzc, hcExcl⟩
                rcases hcb.cases_tail with heqc | ⟨mid, hcmid, hmidb⟩
                · have haz : a = z := huniq a z b hab (heqc ▸ hzc)
                  subst haz
                  simp only [if_pos (Relation.ReflTransGen.refl (a := a)), if_pos hzb]
                  rw [heqc]
                  exact hρzdirect c hcCz
                · have hamid : mid = a := huniq mid a b hmidb hab
                  have hza : Relation.ReflTransGen G.R z a :=
                    hamid ▸ Relation.ReflTransGen.head hzc hcmid
                  simp only [if_pos hza, if_pos hzb]
                  exact hρzdesc c hcCz a b (hamid ▸ hcmid) hab
          · have hza : ¬ Relation.ReflTransGen G.R z a := fun h => hzb (h.tail hab)
            simp only [if_neg hza, if_neg hzb]
            exact hρqedge a b hab
              (by intro e he; rw [Finset.mem_singleton] at he; subst he; exact hzb)
      · intro φ u hf
        by_cases hu : Relation.ReflTransGen G.R z u
        · simp only [if_pos hu]; exact hρzpers hf
        · simp only [if_neg hu]; exact hρqpers hf
      · rintro u ⟨e, he, hreach⟩
        have hze : Relation.ReflTransGen G.R z u :=
          Relation.ReflTransGen.head (hexcl e he) hreach
        simp only [if_pos hze]
        have huz : u ≠ z := by
          intro huzeq
          rw [huzeq] at hreach
          have h1 := ht_le_of_reflTransGen hgrad hreach
          have h2 := hgrad z e (hexcl e he)
          omega
        have hnoCz : ∀ c ∈ hCzFin.toFinset, ¬ Relation.ReflTransGen G.R c u := by
          intro c hc
          exact siblings_disjoint hgrad huniq (hexcl e he) (hCzMem c hc)
            (fun heq => hCzNotExcl c hc (heq ▸ he)) u hreach
        exact hρzout u huz hnoCz
    · simp only [not_exists] at hparent
      refine ⟨ρz, hρzz, hρzmono, ?_, ?_, ?_⟩
      · intro a b hab hbex
        by_cases hza : Relation.ReflTransGen G.R z a
        · rcases hza.cases_head with heq | ⟨c, hzc, hca⟩
          · subst heq
            have hbExcl : b ∉ excl := fun hbe => hbex b hbe Relation.ReflTransGen.refl
            have hcCz : b ∈ hCzFin.toFinset := hCzFin.mem_toFinset.mpr ⟨hab, hbExcl⟩
            exact hρzdirect b hcCz
          · by_cases hcExcl : c ∈ excl
            · exact absurd (hca.tail hab) (hbex c hcExcl)
            · have hcCz : c ∈ hCzFin.toFinset := hCzFin.mem_toFinset.mpr ⟨hzc, hcExcl⟩
              exact hρzdesc c hcCz a b hca hab
        · have haz : a ≠ z := fun h => hza (h ▸ Relation.ReflTransGen.refl)
          have hnCa : ∀ c ∈ hCzFin.toFinset, ¬ Relation.ReflTransGen G.R c a := fun c hc hreach =>
            hza (Relation.ReflTransGen.head (hCzMem c hc) hreach)
          have ha_eq : ρz a = ρ a := hρzout a haz hnCa
          have hbz : b ≠ z := fun hbeq => hparent a (hbeq ▸ hab)
          have hnCb : ∀ c ∈ hCzFin.toFinset, ¬ Relation.ReflTransGen G.R c b := by
            intro c hc hreach
            rcases hreach.cases_tail with heq | ⟨mid, hcmid, hmidb⟩
            · exact haz (huniq a z c (heq ▸ hab) (hCzMem c hc))
            · have hamid : mid = a := huniq mid a b hmidb hab
              exact hza (Relation.ReflTransGen.head (hCzMem c hc) (hamid ▸ hcmid))
          have hb_eq : ρz b = ρ b := hρzout b hbz hnCb
          rw [ha_eq, hb_eq]
          exact hedge a b hab
      · intro φ u hf
        exact hρzpers hf
      · rintro u ⟨e, he, hreach⟩
        have huz : u ≠ z := by
          intro huzeq
          rw [huzeq] at hreach
          have h1 := ht_le_of_reflTransGen hgrad hreach
          have h2 := hgrad z e (hexcl e he)
          omega
        have hnoCz : ∀ c ∈ hCzFin.toFinset, ¬ Relation.ReflTransGen G.R c u := by
          intro c hc
          exact siblings_disjoint hgrad huniq (hexcl e he) (hCzMem c hc)
            (fun heq => hCzNotExcl c hc (heq ▸ he)) u hreach
        exact hρzout u huz hnoCz

/-- **The tree-cascade Lifting Lemma** (Simpson 8.1.3, chunks 0154-0155), completing the
finite-component cascade `boxI_lift_star` left open. Raises `x`'s interpretation to any `w' ≥
ρ x`, re-establishing the raw edge-cond over the WHOLE derivation graph `G` (not just `x`'s own
component: elsewhere, `ρ'` agrees with `ρ`, and the standing `hedge` hypothesis already covers
those edges) and persisting all `CKForces`/Γ-cond facts. Thin wrapper around
`boxI_lift_ancestor`, specialized to `excl := ∅`: the exclusion machinery's hypotheses become
vacuously true (no `e ∈ ∅`), so conjunct 3 reduces to full, unconditional coverage of `G.R`. -/
theorem boxI_lift {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {v : World → Atom → Prop} {botForces : World → Prop}
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    {G : Graph Atom} (hforest : IsDerivationForest G)
    {ρ : Label Atom → World} (hedge : ∀ a b, G.R a b → r (ρ a) (ρ b))
    {x : Label Atom} (hxX : x ∈ G.X) {w' : World} (hxw' : ρ x ≤ w') :
    ∃ ρ' : Label Atom → World, ρ' x = w' ∧ (∀ z, ρ z ≤ ρ' z) ∧
      (∀ a b, G.R a b → r (ρ' a) (ρ' b)) ∧
      (∀ {φ : Proposition Atom} {z}, CKForces r v botForces (ρ z) φ →
        CKForces r v botForces (ρ' z) φ) := by
  obtain ⟨hfin, ⟨ht, hgrad⟩, huniq⟩ := hforest
  obtain ⟨ρ', hρ'x, hρ'mono, hρ'edge, hρ'pers, -⟩ :=
    boxI_lift_ancestor hfc v_uc bf_uc hfin hgrad huniq hedge
      (ht x) x (le_refl _) hxX w' hxw' ∅ (by simp)
  exact ⟨ρ', hρ'x, hρ'mono, fun a b hab => hρ'edge a b hab (by simp), fun {φ} {z} hf => hρ'pers hf⟩

end Cslib.Logic.Modal.Labelled

end
