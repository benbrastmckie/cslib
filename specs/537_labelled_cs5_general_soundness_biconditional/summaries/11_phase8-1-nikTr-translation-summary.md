# Implementation Summary: Phase 8.1 -- `nikTr` Tree-Depth Translation (Plan v5)

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994
  Thm 8.1.4's biconditional
- **Plan**: plans/05_tree-recursive-hilbert-bridge.md (plan version 5)
- **Status of this dispatch**: Phase 8 remains `[IN PROGRESS]`; sub-step 8.1 (of 8.1-8.4) landed
  green and committed. Sub-steps 8.2-8.4 and Phases 9-10 remain `[NOT STARTED]`.
- **Commit**: `task 537 phase 8.1: land nikTr tree-depth translation + sanity examples`

## What landed

In `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (new section, appended
after the landed `boxI_lift`):

- `bigAndL`: a local finite-conjunction helper (`⊤`-surrogate base case `⊥ ⊃ ⊥`), since
  `Cslib.Logic.Modal.bigAnd` (`SegmentLindenbaum.lean`) is not transitively visible from this
  file's import chain.
- `factsAt`: the list of `Γ`-facts attached to a label `y` (`{B | y:B ∈ Γ}` as a `List`).
- `sigAtFuel` / `sigAt`: Simpson's subtree translation `Γ@U` (Fig. 6-1/6-2), fuel-bounded
  structural recursion (fuel = `G.X`'s finite cardinality, a safe upper bound on any node's
  descent depth in a finite graded-rank forest).
- `nikTrFuel` / `nikTr`: the ancestor-walk assembly of the full spine-wrap
  `Γ@T₀ ⊃ □(Γ@T₁ ⊃ □(… ⊃ □(Γ@T_m ⊃ A)…))`, i.e. `nikTr : Simpson's (Γ ⊢_G x:A)^T`.
- Two sanity `example`s pinning the definition: `Graph.trivial` adds zero ancestor-wraps
  (reduces to a `⊤`-padded identity on `A`); a one-edge extension of `Graph.trivial` adds exactly
  one `⊃ □(...)` wrap.

Sorry-free, axiom-clean (`grep` confirmed no `sorry`/`axiom` in the file). Scoped
`lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green;
`lake exe checkInitImports` clean. No Preserved Asset (Phases 1-7, PD.1) touched or regressed.

## Deviations from the plan (documented inline in the plan file too)

1. **Source corruption (H3).** The reflowed OCR of Simpson Ch. 6 chunks 943-975 is severely
   corrupted at the formula level (box/diamond glyphs conflated with digits/letters,
   sub/superscripts scrambled); the one worked example in the source could not be reproduced
   consistently from the OCR'd formula alone. The `Γ@U` recursion and spine-threading shape were
   reconstructed from the surrounding PROSE (legible and internally consistent), not from the
   corrupted formula rendering. Flagged in the new section's docstring rather than silently
   guessed, per the literature-fidelity policy.
2. **Fuel-bounded recursion instead of `ht`-indexed recursion.** `nikTr`/`sigAt` use a global
   fuel bound (`G.X`'s cardinality) rather than directly indexing by `IsDerivationForest`'s `ht`
   function. This is provably sufficient (any ascending/descending chain in a finite graded-rank
   forest has length `< |G.X|`) but that sufficiency lemma is NOT yet proved -- it will be needed
   in Phase 8.2/8.3 when relating `nikTr` across an `addEdge`-extended graph to the smaller graph.
   `IsDerivationForest` itself is untouched and available for that purpose.
3. **`⊤`-padded sanity examples, not byte-identical to Simpson's shape.** `bigAndL`'s empty case
   is a `⊤`-surrogate tautology (`⊥ ⊃ ⊥`), so the two sanity `example`s reduce to `⊤`-padded forms
   rather than a literal bare `A`. This is a documented, sound (`CS5ModalAxiom`-equivalent)
   restructuring, not a mathematical change -- but it means Phase 9's assembly step will need a
   short `⊤`-stripping lemma, not a direct `rfl`, when specialising to `Graph.trivial`.

## What remains (unchanged scope from the plan, now with one concrete new sub-task)

- **Sub-step 8.2**: state `nik_adequacy : NIK TS5 G Γ (x∶A) → IsDerivationForest G →
  Derivable CS5ModalAxiom (nikTr G Γ hfin x A)` and discharge the 8 label-local propositional
  constructors plus the two cross-label constructors `efq`/`orE` -- the cases that killed the v4
  flattened-shortcut attempts. A genuinely new prerequisite surfaced by this dispatch: a
  **fuel-sufficiency lemma** relating `nikTrFuel`/`sigAtFuel` at a smaller fuel value to the same
  at a larger one (needed once the induction crosses an `addEdge`, which increases `G.X`'s
  cardinality by one), since `nikTr`'s own definition does not yet establish this.
- **Sub-step 8.3**: the 4 modal cases (`boxI`, `boxE`, `diaI`, `diaE`), reusing `boxI_lift`,
  `box_iff_TClosure`/`dia_iff_TClosure`.
- **Sub-step 8.4**: specialise to `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable
  CS5ModalAxiom φ` over `Graph.trivial` (needs the `⊤`-stripping lemma noted above).
- **Phase 9**: assemble `nik_TS5_soundness` and retire the stale module-docstring notes.
- **Phase 10**: full regression gate.

No concrete machine-checked obstruction was hit in this dispatch -- this is scope, matching the
plan's own sizing of Phase 8 as "four to (worst-case) six agent runs." Sub-step 8.1 is the
foundational piece; 8.2 is the next, and per report 04's own risk assessment, the hardest
(`efq`/`orE`).

## Plan Deviations

See the two "*(deviation: ...)*" annotations added inline to Sub-step 8.1's checklist in
`plans/05_tree-recursive-hilbert-bridge.md`, and item 2 above (the new fuel-sufficiency
prerequisite for 8.2, not itself a deviation but a concrete addition to that sub-step's task list
worth flagging for the next dispatch).

## AI Tools Used

This work was prepared with the assistance of Claude Code (Anthropic) acting as the
`cslib-implementation-agent`. The tool was used for reading the existing landed lemmas and
`NIK`/`Graph` definitions, reconstructing Simpson's translation from OCR-degraded source prose,
drafting and iterating the Lean definitions/proofs via `lake build` feedback, and drafting this
summary. All Lean code was verified to compile via `lake build` on this branch.
