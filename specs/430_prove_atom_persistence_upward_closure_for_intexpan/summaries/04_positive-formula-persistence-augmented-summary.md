# Implementation Summary (Partial): Task 430 — Positive-Formula Persistence Along the Augmented Relation

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: plans/04_positive-formula-persistence-augmented.md
- **Status of this dispatch**: Phases 1-2 (the two gates) COMPLETED. Phases 3-8 NOT STARTED.
  No `Cslib/`/`CslibTests/` files modified; no sorries touched; DP-2 (`Scheme.lean:2605`)
  untouched.

## What was done

### Phase 2 (Gate B, done first per the plan's "if only one dispatch" guidance)

Prototyped, in `scratch/PersistPrototype.lean` (imports the real `IEdges`/`isAccessible`/
`ISF`/`Proposition`/`IBranch` types, `lake env lean`-verified, one documented `sorry`), the
single loop-back hop persistence question: does the `Sfor`-containment established at a
reuse-blocking event survive to the final branch?

**Verdict: PASS (conditional).** Not refuted (contrast the quotient route, which has a
concrete, proven counterexample). The descendant sub-case closes cleanly from a documented
`SelfCopyReach` hypothesis (Phase 3/4's deliverable) plus chain comparability
(`ForestComparable`, already available in substance from `Scheme.lean`'s private `IWorldHist`/
`parAncestor` machinery, landed by task 585 for DP-2). The ancestor sub-case needs
origin-tracing — not a fresh problem, but a repurposing of `IWorldHist`'s existing `par`/`obl`/
`fire`/`sfor` provenance witnesses. Full detail: `handoffs/02_gate-b-verdict.md`.

### Phase 1 (Gate A)

Re-ran task 574's variant-selection methodology in `scratch/VariantProbe.lean` against the
CURRENT (post-574, post-585) tree. Both **V1** (self-copy reinstated verbatim) and **V4**
(generalized to copy every positive formula) saturate identically to the control
(`len=219, maxLabel=21`, matching 574's own recorded measurement) at fuel≥120, stable through
fuel=200. All 20 rows of the propositional conformance corpus match for both variants.

**Decision: V4 selected** (both pass; V4 is the higher-value target per the plan's tie-break
rule, and this run empirically retires the "V4 might diverge" risk). Full detail:
`handoffs/01_gate-a-variant-selection.md`.

## What was NOT done (remaining work, Phases 3-8)

- **Phase 3**: Revert `a70187dd`'s three hunks (`Expansion.lean`, `Scheme.lean`,
  `Soundness.lean`), reinstating the copy channel in V4's generalized form (not V1's literal
  form — the plan's Phase 3 task list will need the "generalized filter for V4" variant
  wording it already anticipates). Atomic-batch commit; full CI verification required.
- **Phase 4**: Prove copy-completeness at a genuine `applyAllTImpRules` fixpoint over raw
  edges (`Scheme.lean:508-513` sketch).
- **Phase 5**: Thread and export the persistence invariant through
  `intExpandBranches_openBranch_sat`'s induction. Per the Gate B finding, this needs to extend
  `IWorldHist`'s existing provenance witnesses (or a sibling invariant), not invent new
  machinery from scratch — but it IS a substantial, comparable-scope engineering task, not a
  quick corollary.
- **Phase 6**: Discharge DP-5 (`Scheme.lean:633`, the T-imp case).
- **Phase 7**: Instantiate at atoms for DP-3 (`Intuitionistic/Completeness.lean:140`) and DP-4
  (`Minimal/Completeness.lean:128`).
- **Phase 8**: Full CI and final verification.

## Plan Deviations

None. Both gates were executed exactly as the plan specifies (Phase 2 before Phase 1, per the
plan's own explicit "if only one dispatch is available" instruction). No task was skipped,
altered, or silently deferred.

## Artifacts

- `scratch/VariantProbe.lean` (Gate A probe, builds/evaluates clean)
- `scratch/PersistPrototype.lean` (Gate B prototype, one documented `sorry`)
- `handoffs/01_gate-a-variant-selection.md`
- `handoffs/02_gate-b-verdict.md`
- This summary

## Continuation

The next dispatch should start at Phase 3, using the V4-generalized self-copy channel and the
Gate B verdict's guidance on what Phase 5's invariant actually needs to carry (provenance, not
just pairwise containment).
