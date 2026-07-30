# Handoff: Phase 9 COLLAPSED, Continuation Notes for Phase 10

- **Task**: prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: `plans/06_gate-b2-then-origin-tracing-export.md`
- **Status**: PARTIAL (not BLOCKED) — Phases 1-9 complete and committed, full `lake build` green
  (3311 jobs), identical 4-sorry set as Phase 8 (no regression, no new sorries, zero `Cslib/`
  writes this dispatch). Phases 10-14 remain. Phase 10 is the plan's own declared **largest
  phase** ("comparable in scope to building `IWorldHist` itself"), pre-budgeted at 1-2
  dispatches — do not compress it into the tail of another dispatch.

## What happened this dispatch (Phase 9)

Read `handoffs/07_post-reuse-closure-verdict.md` first — it is the full technical record. Do
**not** re-derive its analysis; the summary below is only an index into it.

**Verdict: COLLAPSED.** Attempting the cheap route (saturation + copy-completeness, no fresh
provenance tracking) found:
- The `y ≤ x` ("descendant") sub-case closes cleanly using only already-landed exports
  (`IPosPersistRaw` (Phase 7) + `IBranchSaturation.sat_timp` + `no_contradiction`). Nothing new
  needs to be written for this half — treat it as available, not as work remaining.
- The `x ≤ y ≤ w` ("ancestor") sub-case is genuinely open: content flows forward-only
  (ancestor → descendant) via the copy channel, so `χ` present at an intermediate world `y`
  (a descendant of `x`) says nothing about `χ` at `x`. Closing it needs `χ`'s true point of
  origin traced back to `x` — this is precisely what Phase 10 is for. This was independently
  confirmed by Gate B's own Phase 2 prototype finding the identical gap
  (`handoffs/02_gate-b-verdict.md`), reached via a different route (a scratch prototype with an
  assumed `ForestComparable` hypothesis) — two independent passes landed on the same conclusion.
- Even the case split itself needs a `ForestComparable`/`par`-linearity fact that **does not yet
  exist** anywhere in `Scheme.lean` — grep-confirmed (only ever an assumed hypothesis in the
  Phase 2 scratch prototype, never a real corollary). Building it requires threading a fifth
  existential through `intExpandBranches_openBranch_sat`'s conclusion (the same kind of
  signature change Phases 7/8 each made as their own dispatch) — this is Phase 10's own first
  construction step, not a Phase 9 export.

**Zero `Cslib/` writes this dispatch** — confirmed via `git status --short Cslib/ CslibTests/`
(empty). Landing anything short of the full lemma would have required either a prohibited
`sorry`/weakened statement, or a signature change duplicated immediately by Phase 10.

**Verification (regression check only, nothing changed)**: `lake build` (full project, 3311
jobs) green, identical warning set to Phase 8's recorded state
(`Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1252` — unrelated, pre-existing;
`Scheme.lean:671` DP-5; `Scheme.lean:7617`'s internal deferred conjunct surfacing at
`Intuitionistic/Completeness.lean:137` DP-3 and `Minimal/Completeness.lean:133` DP-4).
`lake exe checkInitImports` clean. `lake exe lint-style` clean. `lean_verify` on `truthLemma`,
`tableau_complete`, `openBranch_countermodel`, `intuitionisticTableau_complete`,
`minimalTableau_complete`: all report only `["propext", "sorryAx", "Classical.choice",
"Quot.sound"]`, unchanged from Phase 8.

## Concrete next steps for Phase 10

Per the plan's own task list (Phase 10 section), plus what this dispatch's analysis adds:

1. **First construction step (new, identified this dispatch, not explicit in the plan's own
   task list)**: build the `ForestComparable` export. Thread `IWorldHist φ0 b e nw edges` (or a
   derived comparability corollary) through `intExpandBranches_openBranch_sat`'s conclusion as a
   fifth existential component, alongside `edges`, `rawEdges`, `lbEdges`. Watch the
   **direction gap**: `IWorldHist`'s (H1-acc) clause gives `parAncestor par c' c → isAccessible
   edges c' c`, not the converse. The reuse witness (`intFImpReuseWitnessAnc?_spec`,
   `Expansion.lean:321`) supplies a raw `isAccessible edges x l = true` fact directly — prefer
   stating whatever comparability corollary Phase 10 needs **directly in terms of
   `isAccessible`**, never routing through `parAncestor` membership, if that avoids needing the
   unestablished converse direction at all.
2. Extend `IWorldHist`'s witness functions — or thread a sibling invariant alongside them,
   mirroring `IAllAccessConsistent`'s companion-not-merged pattern (exactly how Phase 8 handled
   `IReuseContain` as a separate parallel list `lbSets`, not folded into `augSets`) — to record a
   traceable origin world for every positive formula's presence on the branch.
3. Generalize (H3)'s planted-positive-content shape (`Scheme.lean:3230-3232`: `∀ χ ∈ sfor c, χ ∈
   posFormulasAt b c`) from "the mint-time `Sfor` set" to "every positive formula's point of
   origin".
4. Prove the recorded origin is raw-accessible to any `x` a loop-back edge points from, using
   (H1-acc) and `par`-linearity.
5. Reuse `IWorldHist_mono` (`Scheme.lean:3263`ff) for the transfer in every non-minting arm and
   `IWorldHist_entry` (`Scheme.lean:3251`) for the vacuous entry discharge. Do not re-derive
   either.
6. Reuse `IAllWorldHist_append`/`_map_const` and the `IAllWorldHistCounter` family
   (`Scheme.lean:3280-3328`) for the list-level plumbing.
7. Once origin-tracing lands, **re-attempt Phase 9's residual lemma** using it: the `y ≤ x`
   closing argument from handoff 07 is reusable verbatim; only the `x ≤ y ≤ w` case needs the new
   origin fact (trace `χ`'s origin `z`; if `z ≤ x`, the copy channel delivers directly; `z` cannot
   sit strictly between `x` and `w` by construction of "origin" — confirm this last step
   concretely rather than assuming it).
8. Do **not** reach for `intWorldHist_chain_le`, `pathOf`, `pathOf_injOn`, or
   `intWorldHist_nw_le` — world-**bound** machinery, not persistence-relevant (unchanged
   exclusion from every earlier phase).
9. If this phase itself cannot complete within its dispatch, record a `[PARTIAL]` handoff with
   the same discipline this dispatch used: zero `Cslib/` writes left in a red state, no `sorry`,
   no weakened statement.

## Do not re-derive

- Handoff 07's full sub-case analysis (the `y ≤ x` closing argument, the `x ≤ y ≤ w` gap
  characterization, the `ForestComparable` non-existence finding) — already established.
- Gate B's Phase 2 prototype finding (`handoffs/02_gate-b-verdict.md`) — independently confirms
  the same gap; both analyses are now on record and agree.
- Phase 7's `IPosPersistRaw` and Phase 8's `IReuseContain`/`IAllReuseContain` — landed,
  sorry-free, reusable as-is.
- The exclusion list (quotient/blocking-frame route, Route C, `≤`-on-ℕ, budgeting
  `pathOf`/`intWorldHist_nw_le` as reuse wins) — still prohibited, unchanged.

## Files touched this dispatch

- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/plans/06_gate-b2-then-origin-tracing-export.md`
  (Phase 9 marked `[COMPLETED]` with COLLAPSED outcome; checklist ticked with deviation notes;
  Phase 10's entry criterion annotated as met)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/handoffs/07_post-reuse-closure-verdict.md`
  (new — the verdict record)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/handoffs/08_phase9-collapsed-phase10-handoff.md`
  (this file)

`git status --short Cslib/ CslibTests/` at the end of this dispatch is empty — no Lean source
changed.
