# Summary: Phase 7 (`boxI_lift`) — Complete

## Status

**COMPLETED.** Continuation of the partial dispatch recorded in
`07_phase7-boxI-lift-partial-summary.md`. `boxI_lift` — the tree-cascade Lifting Lemma (Simpson
8.1.3, chunks 0154-0155) — is now landed in
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, sorry-free and
axiom-clean, closing the `boxI` producer side.

## What was landed this dispatch

Three new declarations, appended after `raise_subtree`, before `end Cslib.Logic.Modal.Labelled`:

1. **`siblings_disjoint`** — distinct raw-`R`-children `c₁ ≠ c₂` of a common node `p` have
   disjoint forward-reachable closures. Generalizes the disjointness argument already proved
   inline inside `raise_subtree`'s `insert` case (there specialized to one fixed new child vs.
   a `Finset` of already-processed siblings) to two arbitrary named children. Proved by induction
   on the reachability witness, using `huniq` (unique parent) at the last edge together with
   `ht_le_of_reflTransGen`/`hgrad` to rule out reaching back up to the common parent.

2. **`boxI_lift_ancestor`** — the Finset-exclusion-parametrized ancestor-walk induction specified
   in the plan's Phase 7 partial-progress note. Strong induction on an upper bound for `ht z`;
   at each step, calls `raise_subtree` to raise `z`'s own un-excluded downward closure, then
   either (base case, `z` has no parent) is done, or (succ case) F2-raises `z`'s unique parent
   `q` via `cs5FCIncest_raise` and recurses via the induction hypothesis at `q` with `{z}` as the
   new exclusion set, combining the two resulting interpretations via an if-then-else on
   `Relation.ReflTransGen G.R z ·`.

3. **`boxI_lift`** — thin wrapper specializing `boxI_lift_ancestor` to `excl := ∅`, so the
   exclusion machinery's hypotheses become vacuously true and the edge conjunct reduces to full,
   unconditional coverage of `G.R`. Matches the plan's audit §3 signature exactly.

## Documented deviation (not a design re-opening)

The dispatch-1 handoff's transcribed induction schema checked the `Finset`-exclusion antecedent
via the edge's **source** (`a`). This dispatch found (via `lean_goal` inspection before writing
the combine step) that checking via the source is unprovable at the boundary edge into the
excluded branch: e.g. for the ancestor edge `q → z` (with `q` outside the excluded closure and
`z` inside it), the source-based check makes the obligation active, requiring
`r (raised q) (old ρ z)` — but `cs5FCIncest` has no "raise-source-only, keep-target-exact"
conjunct (see `boxI_lift_star`'s own section docstring), so this is not generally derivable.
Checking via the edge's **target** (`b`) instead correctly drops exactly the boundary edge (and
everything inside the excluded closure) from the internal obligation, since that edge is
established separately by the caller's own `cs5FCIncest_raise` fact before the final combine.
This is a one-side correction to the membership check inside a single conjunct; the overall
two-piece downward/ancestor decomposition and all five key decisions recorded in the dispatch-1
handoff (`handoffs/07_phase7-boxI-lift-partial.md`) are unchanged and were followed verbatim.
Documented in `boxI_lift_ancestor`'s docstring.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` — green.
- `lake exe checkInitImports` — passes.
- `lake lint` — passes.
- `lake exe lint-style Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` — passes.
- `grep -n '\bsorry\b'` on the file — no tactic `sorry` (docstring prose mentions only).
- `lean_verify` on all three new declarations:
  - `siblings_disjoint`: `{propext, Quot.sound}`
  - `boxI_lift_ancestor`: `{propext, Classical.choice, Quot.sound}`
  - `boxI_lift`: `{propext, Classical.choice, Quot.sound}`
- No new axioms, no vacuous definitions, no `Graph`/`cs5FCIncest` modification, no Preserved
  Asset regressed.
- `lake shake`/`lake test` deferred to Phase 9 (the plan's dedicated regression-gate phase).

## Plan Deviations

- Phase 7's task checklist mentioned a `raise_component_by_distance` single-helper sketch in the
  original plan text; the actual landed decomposition (from dispatch 1, preserved here) is
  `raise_subtree` (downward cascade) + `boxI_lift_ancestor` (ancestor walk), which the plan's own
  Phase 7 partial-progress note already superseded the original sketch with. No further deviation
  beyond what dispatch 1 already recorded, plus the target-vs-source correction documented above.

## Next

Phase 8: main NIK induction (motive amended to carry `IsDerivationForest G`), close the `boxI`
case using `boxI_lift`, assemble `nik_TS5_soundness`. Not started this dispatch (mission scope:
Phase 7 only).
