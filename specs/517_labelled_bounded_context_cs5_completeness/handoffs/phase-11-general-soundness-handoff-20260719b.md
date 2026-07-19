# Task 517 Continuation Handoff — Phase 11.1/11.2 (General Soundness), 2026-07-19 (second dispatch)

## Status Summary

- **Phase 10** (`cs5_completeness`): unchanged, **[COMPLETED]**, landed, sorry-free, axiom-clean.
- **Phase 11.3** (`nik_TS5_consistent`): **[COMPLETED] this dispatch**, landed via the plan's
  own pre-authorized direct route (one-point model), sorry-free, axiom-clean
  (`[propext, Classical.choice, Quot.sound]`), no `sorryAx`. New lemma `nik_soundness_onePoint`
  (a full 12-constructor `NIK` soundness induction against `World := Unit`, `r := fun _ _ => True`)
  is also landed and reusable. Both in `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/
  Soundness.lean`. Committed at `bb24a4b1`.
- **Phase 11.1/11.2** (general `nik_TS5_soundness`): **still not landed**. This dispatch did NOT
  add new proved lemmas toward the general theorem, but DID surface a materially sharper
  understanding of the obstruction than the prior dispatch's handoff had — recorded in
  `Soundness.lean`'s module docstring ("Refined analysis of items 1-4") and summarized below.
  **Not blocked** — this is a scope/budget continuation, matching the plan's own multi-dispatch
  estimate (1-2 dispatches for 11.1 alone, before this refinement).
- **Phase 12**: correctly **not started**, per the plan's own sequencing (depends on 11 completing
  first, so its `state.json` blockers-rewrite reflects the *final* state). Do not attempt Phase 12
  until `nik_TS5_soundness` lands.

**Next dispatch should set `next_phase: 11` (sub-phase 11.1, general-soundness continuation)**.

## The sharper obstruction found this dispatch

The prior dispatch's handoff (`phase-11-lifting-lemma-handoff-20260719.md`) framed the missing
graph-lifting lemma as a **tree-path propagation**: raise one label `x`, then propagate the raise
down `x`'s descendants via `cs5FCIncest_lift` + `ckforces_persistence`, keeping everything *not*
descended from `x` (including `x`'s own ancestors) unchanged.

This dispatch attempted an actual Lean encoding of the `(□I)` case against that framing and found
it does not close, for a reason neither this module's nor the prior handoff's docstring had yet
identified:

1. **`TS5 = {T, B, Four}` makes `TClosure TS5 G.R` an equivalence relation**, and `G` is *always
   connected* as an undirected graph (`Graph.addEdge` always attaches a new label to an
   already-present one, starting from `Graph.trivial`'s single node — `G` is a tree). An
   equivalence closure of a connected graph is the **total relation on the vertex set**:
   `TClosure TS5 G.R a b` holds for **every** `a, b ∈ G.X`, not just tree-adjacent pairs.
   Consequently edge-cond (`∀ a b, TClosure TS5 G.R a b → r (ρ a) (ρ b)`) requires `r` to hold
   between `ρ` of **every pair of labels used so far**, not just parent-child pairs — the
   interpreted image of `G.X` under `ρ` must be an `r`-*clique*. A fresh label introduced by
   `(□I)`/`(◇E)` must therefore be related to **every** existing label's image, not merely to its
   immediate parent — a materially larger obligation than the tree-path framing assumed.

2. **`cs5FCIncest_lift`'s raised witness is not exact, and edge-cond needs exactness.** Trying
   `ρ' y := u` (the semantically-required successor, from `hru : r w' u`, `w' ≥ ρ x`) to satisfy
   clique-membership against some *other* already-present label `a` needs `r (ρ a) u`, derivable
   from `r (ρ a) (ρ x)` (known, old edge-cond) and `r w' u`, `ρ x ≤ w'` via `hfour`'s shape
   (`r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t`, instantiated `w := ρ a`, `u := ρ x`,
   `u' := w'`, `t := u`) — but `hfour` only delivers `r v u` for **some** `v ≥ ρ a`, not
   `r (ρ a) u` exactly. Satisfying `a`'s clique membership therefore forces **also raising `a`'s**
   interpreted value to `v`, which then cascades to `a`'s own clique-neighbours in turn.

3. **The fix is asymmetric between edge-cond and Γ-cond.** Γ-cond (`∀ ψ ∈ Γ, CKForces (ρ ψ.lbl)
   ψ.prop`) survives raising `ρ` pointwise **for free**, via `ckforces_persistence` (`CKForces` is
   upward-closed: if `ψ` was forced at the old value and the new value is `≥` the old, it is still
   forced). Edge-cond (`r (ρ a) (ρ b)`) has **no such slack** — it is a flat, non-monotone fact
   about `r`, not about `CKForces`, so it cannot be "topped up" after the fact.

## The corrected target for items 1-2 (not yet attempted in Lean)

Not a tree-depth recursion (the prior framing), but a **finite-set clique-lifting lemma**:

> Given a *finite* set `S` of labels already `r`-clique-related under `ρ` (i.e. `∀ a b ∈ S,
> r (ρ a) (ρ b)`), and one member `x ∈ S` raised to `w' ≥ ρ x`, produce `ρ' ≥ ρ` pointwise on `S`
> (every member's value may need to rise, not just `x`'s) such that `S` is *again* an `r`-clique
> under `ρ'`, with `ρ' x = w'` (or `ρ' x ≥ w'`, whichever composes more cleanly with the box/dia
> clause).

This is plausibly provable by finite induction over `S` (e.g. `Finset`/`List` induction, since
only finitely many labels ever appear in one derivation), applying `hfour`/`hsymbox`/`hincest`
pairwise and taking each newly-forced raise as input to the next pairwise step — but this has
**not** been attempted in Lean yet; it is the concrete next step. `cs5FCIncest_lift` (already
landed, sorry-free) is very likely still an ingredient (the "raise one edge's source, get *some*
raised target" primitive), just composed differently than the tree-path framing envisioned.

**A live open question for the next dispatch to resolve early**: does this lemma actually need
"every member of `S` raised", or is there a smarter invariant (e.g. always keeping `ρ`'s image a
single `≤`-directed/confluent set, or picking `ρ`'s values from a canonically-maximal witness at
each step) that avoids re-raising the *whole* clique on every new label? Given `TS5`'s clique
structure this is worth 15-30 minutes of scoping before diving into the induction, since the
finite-clique-relift lemma could be genuinely substantial (100-250 lines) if done the "obvious"
way, and it recurs at **every** `(□I)`/`(◇E)` step of the main induction, so its statement shape
matters a lot for how painful the main 12-constructor induction (item 3) will be to close.

## What is NOT affected by this finding

- `cs5FCIncest_lift` itself: unaffected, still sorry-free, still a plausible ingredient.
- Phase 11.3 (`nik_TS5_consistent`, `nik_soundness_onePoint`): unaffected — the one-point model
  sidesteps this entirely (a one-point clique is trivially always satisfied).
- Phase 10 (`cs5_completeness`): completely independent, unaffected, still landed.
- Phase 11.2's own task ("validate each `cs5FCIncest` conjunct soundly interprets the matching
  `TClosure` edge rule") is *subsumed* by the corrected edge-cond framing above — once the
  clique-lifting lemma exists, edge-cond quantified over `TClosure` (not raw `G.R`) is the natural
  statement to carry through the main induction directly, rather than a separate validation pass.
  Re-scope 11.2 as "prove the clique-lifting lemma handles all of `TClosure TS5`'s cases (not just
  raw edges)" rather than a separate TClosure-induction pass over an already-fixed edge-cond.

## Files touched this dispatch

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`: added
  `nik_soundness_onePoint`, `nik_TS5_consistent` (Phase 11.3, landed), and the "Refined analysis
  of items 1-4" docstring section (this handoff's summary, in-file).
- `specs/517_labelled_bounded_context_cs5_completeness/plans/13_labelled-completeness-full-soundness.md`:
  Phase 11.3 marked `[COMPLETED]` with deviation annotations (direct route, not via
  `nik_TS5_soundness`).
- This handoff.

## Verification (this dispatch)

- `nik_soundness_onePoint`: `lean_verify` → `["propext","Classical.choice","Quot.sound"]`, no
  `sorryAx`.
- `nik_TS5_consistent`: `lean_verify` → `["propext","Classical.choice","Quot.sound"]`, no
  `sorryAx`.
- Full `lake build`: 3247/3247 green (unregressed).
- `lake exe checkInitImports`: pass.
- `lake lint`: 0 warnings (full-project run).
- `lake exe lint-style`: 0 warnings for `Soundness.lean`.
- `lake shake`: no suggestions for `Soundness.lean` (pre-existing suggestions for other,
  untouched files unrelated to this dispatch).
- `lake exe mk_all --module`: `Soundness.lean` already registered in `Cslib.lean`; reverted two
  unrelated import lines (`SchemaSoundness`, `SchemaBridges`/`SchemaUnion`) that `mk_all` picked
  up from a concurrent task's untracked files, to keep this commit scoped to task 517.
- `lake test`: 9241/9242 green; pre-existing sorries in unrelated Propositional Tableau files
  unregressed.
- Sorry inventory (new/modified files): **empty**.
- New axiom count: **zero**.
