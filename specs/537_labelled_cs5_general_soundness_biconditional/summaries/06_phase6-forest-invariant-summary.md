# Implementation Summary: Phase 6 — Derivation-forest invariant `IsDerivationForest` + preservation lemmas

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm
  8.1.4's biconditional
- **Plan**: plans/03_direct-route-forest.md (v3), Phase 6
- **Status**: [COMPLETED]

## What Landed

File: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, inserted immediately
after the landed `boxI_lift_star` (Phase 5) and before the "One-point soundness" section.

1. **`IsDerivationForest (G : Graph Atom) : Prop`**: the three conjuncts specified by report
   `03_tree-shape-invariant-audit.md` §1, verbatim:
   - `G.X.Finite`
   - graded rank: `∃ ht : Label Atom → ℕ, ∀ a b, G.R a b → ht b = ht a + 1` (rules out directed
     cycles)
   - unique parent: `∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁ = a₂` (rules out undirected diamonds)
2. **`forest_trivial : IsDerivationForest (Graph.trivial Atom)`** — 2-line term-mode proof:
   `⟨Set.finite_singleton _, ⟨fun _ => 0, fun _ _ hab => hab.elim⟩, fun _ _ _ hab _ => hab.elim⟩`.
   `Graph.trivial`'s edge relation is `fun _ _ => False`, so both the rank and unique-parent
   conjuncts are discharged by `hab.elim` on the (definitionally `False`) edge hypothesis.
3. **`forest_addEdge_fresh : IsDerivationForest G → x ∈ G.X → y ∉ G.X → IsDerivationForest (G.addEdge x y)`**
   — tactic-mode, ~30 lines. Extends the rank via `Function.update ht y (ht x + 1)`; the old-edge
   case rewrites both endpoints away from `y` using `G.edge_mem` (both endpoints of an old edge lie
   in `G.X`, hence differ from the fresh `y`); the new-edge case (`x → y`) closes by
   `Function.update_self`/`Function.update_of_ne`. Finiteness via `Set.Finite.union`/
   `Set.Finite.insert`. Unique-parent is a four-way case split on which of the two incoming edges
   (old vs. new `x → y`) each hypothesis is; the old/new-mixed cases derive a contradiction from
   `y ∉ G.X` via `G.edge_mem`, the old/old case reuses the inherited `huniq`, and the new/new case
   is `ha1.trans ha2.symm`.

Both are sorry-free and axiom-clean (`lean_verify`: `{"axioms":["propext","Classical.choice",
"Quot.sound"],"warnings":[]}` for each — the three standard axioms, no new axiom).
`lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` is green;
`lake exe checkInitImports` passes; `grep -n '\bsorry\b'` finds no tactic `sorry` (only prose
mentions of "sorry" inside docstrings/comments, all pre-existing). Spot-re-verified
`boxI_lift_star` (the Phase 5 Preserved Asset immediately preceding this insertion) is
unregressed: same three standard axioms.

## Plan Deviations

- **Tactic-level fix, not a scope or statement change.** The graded-rank case's new-edge branch
  was originally written as `rcases hab with hab | ⟨rfl, rfl⟩` (destructuring `a = x ∧ b = y` via
  `rfl`). Lean's `subst` eliminated the *outer* binders `x`/`y` (substituting them away in favor
  of the freshly-`intro`'d `a`/`b`) rather than the reverse, which orphaned the subsequent bare
  references to `x`/`y` in the proof (`error: Unknown identifier 'x'/'y'` at build time). Fixed by
  keeping the equalities as named hypotheses `ha : a = x`, `hb : b = y` and rewriting the goal
  with them (`rw [ha, hb, Function.update_self]` then `Function.update_of_ne`) instead of
  destructive `subst`/`rfl`-pattern matching. No change to `IsDerivationForest`'s statement, to
  either lemma's signature, or to the plan's task sequence — caught and fixed via
  `lake build` (machine-checked), per the postmortem's "machine-check before escalating" rule.
  No other deviation from the plan's exact task sequence.

## Preserved Assets

All fourteen Preserved Assets (Phases 1-5 plus prior task-517 lemmas) are unmodified. This phase
only inserted new declarations; nothing upstream or downstream was touched.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`: green.
- `lake exe checkInitImports`: clean.
- `grep -rn '\bsorry\b' Cslib/`: only pre-existing prose mentions in docstrings (lines 237, 241,
  292, 552 of `Soundness.lean`), no NEW tactic `sorry`.
- `lean_verify` on `forest_trivial` and `forest_addEdge_fresh`: `{"axioms":["propext",
  "Classical.choice","Quot.sound"]}` each — no new axiom, no `sorryAx`.
- `lean_verify` on `boxI_lift_star` (Preserved Asset spot-check): same three standard axioms,
  unregressed.

## Next Phase

Phase 7 (`boxI_lift`, the plan's sole concentrated-risk phase): state and prove the
tree-restricted Lifting Lemma taking `IsDerivationForest G` as a hypothesis, completing the
finite-component cascade `boxI_lift_star` left open. Recommended internal decomposition (per the
plan's Risk mitigation): land a `raise_component_by_distance` helper as its own green sub-step
before assembling `boxI_lift`.
