# Task 317 Phase 2 Summary: Implement the Sfor-Containment Loop-Check

## Plan

`specs/317_propositional_tableau_completeness/plans/04_sfor-dedup-fuel-sufficiency.md`, Phase 2.

## What was done

Replaced the Phase-1 `none`-returning design stub `intFImpReuseWitness?` in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` with a real implementation,
and wired it into `go` (the `intExpandBranches` inner loop).

### `intFImpReuseWitness?`

Signature (unchanged from the Phase 1 stub, per the "do not redesign" instruction):

```lean
def intFImpReuseWitness? (bPers : IBranch Atom) (edges : IEdges)
    (newForms : List (ISF Atom)) (newEdge : Nat × Nat) : Option Nat
```

Implementation:
1. Reads `w := newEdge.2` (the source world).
2. Reads the obligation `ψ` as `newForms`'s sole `sign = .neg` entry (`List.findSome?`); returns
   `none` if absent (should not happen for this rule).
3. Reads `Sfor(w') = {φ} ∪ posFormulasAt bPers w` as `newForms`'s `sign = .pos` sublist
   (`List.filterMap`).
4. Searches `(bPers.map (·.label)).eraseDups` (the distinct world labels on the branch, in branch
   order) via `List.findSome?` for the first label `x` satisfying:
   - `isAccessible edges w x`
   - `sfor.all (forcedAtX.contains ·)` (containment)
   - `!(forcedAtX.contains ψ)` (obligation still open)
5. Returns `some x` for the first such label, or `none`.

### Wiring into `go`

The `some (.linearResult newForms nw' newEdge, newExp)` branch now matches on `newEdge`:
- `none` (alpha-rule): unchanged — extend branch, edges unchanged.
- `some e` (world-creating `F(φ → ψ)` rule): calls `intFImpReuseWitness? bPers edges newForms e`.
  - `some _x` (reuse): no new world, no new edge; continues `intExpandBranches` on `bPers`
    unchanged, `edges` unchanged, and the *original* `nw` (not `nw'`) since the fresh world was
    never created and its label should not be consumed. `F(φ → ψ)@w` is still marked expanded via
    `newExp` (already computed by `intStepBranch` regardless of which path is taken).
  - `none`: creates `w'` exactly as before (`Branch.extendMany bPers newForms`, `nw'`,
    `edges ++ [e]`).

## Signature-change question

**Answer: NO.** `intFImpRule`, `intApplyRuleFull`, and `intStepBranch` are all unchanged. The
entire check and its dispatch live inside `go`, exactly as the Phase 1 GO verdict predicted.

## Preserved-Asset check

A scoped build of the downstream `Soundness` module (read-only check, not touched) surfaced
exactly one broken lemma:

- **`intExpandBranches_closed_unsat`** in `Soundness.lean` (starts line 1083; unification
  failures at lines ~1396 and ~1461). Its induction assumed every world-creating step strictly
  grows the branch and edge set. The reuse (`some x`) path breaks that assumption.

This is the **expected** fallout flagged by this phase's own instructions ("if a preservation
lemma breaks because the branch no longer grows on a reused F(→), that is expected — record it
for Phase 3, do NOT patch by weakening"). It was recorded, not patched, per territory rules
(`Soundness.lean` is out of scope for this phase). See `.orchestrator-handoff.json` for the
suggested resolution direction.

`Expansion.lean`'s own Preserved Assets (`IExpandedConsistent_sat`,
`intStepBranch_linear_preserves`, `intStepBranch_result_ne_notApplicable`, etc.) were not
affected — none of them reason about `go`'s internal branch-growth pattern.

## Verification

- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion`: GREEN, 0 errors.
- Sorry count: unchanged (`Scheme.lean:330`, `Scheme.lean:985`, `Completeness.lean:113`,
  `Minimal/Completeness.lean:110` — none touched this phase).
- No new axioms, no vacuous definitions.

## Plan Deviations

None. Implementation matches the Phase 1 settled design exactly (signature, search order,
reuse condition, wiring point). The mission prompt's suggested signature
`intFImpReuseWitness? (φ ψ) (w) (edges) (b)` was NOT used — the actual Phase-1-committed stub
signature `(bPers) (edges) (newForms) (newEdge)` is authoritative and was preserved unchanged,
per the "do NOT redesign" instruction in both the Phase 1 GO verdict and this dispatch's mission.

## Files touched

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (only file committed)

## Next steps

Phase 3 (re-verify countermodel/Hintikka conditions for reused worlds, `Scheme.lean` side) can
run in parallel with Phase 4 (soundness audit, fixing `intExpandBranches_closed_unsat` in
`Soundness.lean` per the fallout recorded above).
