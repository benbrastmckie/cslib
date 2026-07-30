# Handoff: Phase 8 Complete, Continuation Notes for Phase 9

- **Task**: prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: `plans/06_gate-b2-then-origin-tracing-export.md`
- **Status**: PARTIAL (not BLOCKED) — Phases 1-8 complete, committed, full `lake build` green
  (3311 jobs). Phases 9-14 remain. This is a natural checkpoint: Phase 9 is described in the
  plan itself as "the genuinely large piece" and is budgeted as its own dispatch.

## What landed this dispatch

- **Phase 8**: `IReuseContain`/`IAllReuseContain` (existential-snapshot encoding, candidate 2
  from handoff 05) landed as a companion invariant, threaded through a NEW parallel list
  (`lbSets`/`pendingLB`/`doneLB`), separate from the existing `augSets`/`pendingAug`/`doneAug`.
  `intExpandBranches_openBranch_sat`'s conclusion gained a third existential `lbEdges` plus
  `IReuseContain lbEdges b`. The reuse arm (`case6` of the `key` induction) plants the new fact
  via a new `hcontGen` lemma (generalizing the existing `houtPhi` derivation from the single
  formula `φ` to every `χ` with `T(χ)@l ∈ bPers`) composed with `IReuseContain_snoc`. Every other
  arm that touches the new hypothesis (`case2`, `case4`, `case5`, `case7`, `case8`) performs only
  a monotone lift via `IReuseContain_mono`. `openBranch_countermodel`'s call site updated to
  supply `lbSets := [[]]` and `hARC := (by simp [IAllReuseContain, IReuseContain])`, destructuring
  the new tuple component as `_lbEdges`/`_hrc` (not yet consumed — that is Phase 9-12's job).

**Verification state**: `lake build` (full project, 3311 jobs) green. Exactly 4 sorries in this
task's scope, unchanged from Phase 7: DP-5 (`Scheme.lean:727` truthLemma T-imp case), the
Phase-6-introduced `openBranch_countermodel` conjunct (`Scheme.lean:7683` at time of writing),
DP-3 (`Intuitionistic/Completeness.lean:146`), DP-4 (`Minimal/Completeness.lean:141`). DP-2
(`intFreshMint_preserves_nw`) confirmed untouched by content and by `git diff --stat`. Only
`Scheme.lean` touched (`git status --short Cslib/ CslibTests/` shows this single file).
`lean_verify openBranch_countermodel` reports `["propext", "sorryAx", "Classical.choice",
"Quot.sound"]` — the `sorryAx` is transitive via the Phase-6 conjunct, unchanged from before this
dispatch. `checkInitImports` and `lint-style` clean. `TableauConformance` still green (build
succeeds — its assertions are `#guard_msgs in #eval` directives checked at build time, so a
clean build IS the conformance pass).

## New declarations available to Phase 9 (export, do not re-derive)

| Declaration | Location (Scheme.lean, line numbers approximate at time of writing) | Role |
|---|---|---|
| `IReuseContain (lbH : IEdges) (b : IBranch Atom) : Prop` | `~6483` | `∀ x l, (x,l) ∈ lbH → ∃ bSnap ⊆ b, ∀ χ, T(χ)@l ∈ bSnap → T(χ)@x ∈ bSnap`. The exported per-branch fact. |
| `IReuseContain_mono` | `~6503` | Monotone lift under branch growth — the ONLY lemma every non-planting arm needs. |
| `IReuseContain_snoc` | `~6513` | Extends by a newly recorded `(x, l)` pair, using the CURRENT branch as its own snapshot witness. This is how `case6` plants the fact. |
| `IAllReuseContain`, `IAllReuseContain_append`, `IAllReuseContain_map_const` | `~6528-6570` | List-level plumbing, structural mirrors of `IAllAccessConsistent`'s own three declarations. |
| `intExpandBranches_openBranch_sat`'s conclusion | `~6610` (top) | Now `∃ (edges rawEdges lbEdges : IEdges), IBranchSaturation Atom b ∧ IFimpAccess edges b ∧ IPosPersistRaw rawEdges b ∧ IReuseContain lbEdges b`. `openBranch_countermodel` currently discards `lbEdges`/the new conjunct via `_lbEdges`/`_hrc` — Phase 9-12 is what will actually consume it. |

## Concrete next steps for Phase 9

Phase 9's goal (per the plan, unchanged by this dispatch): prove the residual obligation — no
positive formula arrives at `w` after the reuse event without also being at `x` — attempting the
**cheap route** (saturation + copy-completeness) before falling back to Phase 10 (full origin
tracing).

1. State the residual lemma precisely: given `IReuseContain lbEdges b` (Phase 8, now landed),
   `IBranchSaturation Atom b` (already in the conclusion), and `IPosPersistRaw rawEdges b`
   (Phase 7, landed), show the FULL augmented-edge persistence fact — i.e., that
   `IReuseContain`'s existential-snapshot form can be strengthened to a bare "every χ present at
   `l` (at ANY later point) is present at `x`" fact, for the specific `x`/`l` pair recorded by
   each loop-back edge.
2. Two sources of post-reuse arrival at `w` (the plan's own enumeration — confirm it still holds
   by re-enumerating every site that appends a positive formula at an EXISTING label in
   `intStepBranch`/`applyAllTImpRules`/`applyPersistenceFixpoint`, per the plan's own Scope
   Hypothesis for Phase 9):
   - Decomposition at `w` of a premise already present at reuse time (present at `x` too, by
     Phase 8's `IReuseContain`; the final branch is saturated, so the same decomposition fires at
     `x`).
   - A copy from a raw ancestor `y` of `w` (via the V4 copy channel and Phase 4's
     `applyPersistenceFixpoint_copy_complete`). `par`-linearity (export from `IWorldHist`, NOT a
     new construction) makes `y` and `x` comparable; if `y ≤ x`, done; if `x ≤ y ≤ w`, recurse —
     this is the declared potential collapse point.
3. Record the verdict — **CLOSED** or **COLLAPSED** — in
   `handoffs/07_post-reuse-closure-verdict.md` (the plan's own file name is
   `handoffs/05_post-reuse-closure-verdict.md`; use the next free handoff number instead, i.e.
   `07_`, to avoid collision with this task's own handoff sequence — `05` and `06` are already
   taken by this task's handoffs, not the plan's placeholder numbering).
4. **Prohibited workarounds**: no `sorry`, no vacuous placeholder, no weakened statement. If the
   route collapses at `x ≤ y ≤ w`, stop and hand off with that recorded — Phase 10 is the
   pre-declared, budgeted fallback, not an improvisation.

## Do not re-derive

- Handoff 05's design-subtlety analysis (why a bare current-branch containment invariant is NOT
  preserved and why the existential-snapshot shape is needed) — Phase 8 already resolved and
  consumed it.
- Handoff 04's Gate B2 verdict (PASS, residual risk carried forward) — still not reopened.
- The exclusion list (quotient/blocking-frame route, Route C, `≤`-on-ℕ, budgeting
  `pathOf`/`intWorldHist_nw_le` as reuse wins) — still prohibited, unchanged.
- Phase 7's `IPosPersistRaw` and its derivation from `applyPersistenceFixpoint_copy_complete` —
  already landed, reusable as-is for the raw-edge half of Phase 9's argument.

## Files touched this dispatch

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (Phase 8 only)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/plans/06_gate-b2-then-origin-tracing-export.md`
  (Phase 8 marked `[COMPLETED]`, checklist ticked, outcome recorded)

`git status --short Cslib/ CslibTests/` at the end of this dispatch shows only `Scheme.lean` —
no stray writes.
