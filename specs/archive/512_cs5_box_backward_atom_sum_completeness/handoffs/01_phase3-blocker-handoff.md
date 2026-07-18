# Handoff: Task 512 — Resume at Phase 3 (Seed Consistency Gate)

## State

- Phases 1-2 landed, committed, CI-green, sorry-free, no new axiom:
  - `Cslib/Logics/Modal/Basic.lean` — `Proposition.map` + commutation + injectivity.
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (new) — `CS5Combined`,
    `cs5_axiom_relabel`, `τL`/`τR`, `DerivationTree`/`Deriv` transport corollaries.
- Phase 3 (`cs5Combined_seed_excludes`) is `[BLOCKED]` in the plan file, with a full analysis
  of what was tried and why it did not close, recorded inline at
  `specs/512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md` (search for
  "BLOCKER (Phase 3").
- Phases 4-5 not started (both consume Phase 3's output directly).

## What To Do Next

1. Read the Phase 3 blocker annotation in the plan file in full.
2. This dispatch's semantic/proof-theoretic analysis (documented there) rules out the two naive
   constructions the report sketched (toy 2-point frame; naive collapse-projection) as
   insufficient, and gives reasons to believe the seed-exclusion claim is likely TRUE (not a
   collapse) — so the recommended next move is a genuine attempt at either:
   - (a) a canonical-model-scale separating model (likely needs to build on the *existing*
     `CS5Segment`/`cs5Mreach` apparatus for the L-side, plus a second witness for the R-side that
     does not presuppose the very thing Phase 4 is trying to construct), or
   - (b) a derivation-height/structure induction proving a sharp logical-relation invariant over
     `CS5Combined`-derivations from the pure-`τL`-tagged seed.
3. `box_mem_of_boxed_context` (used by the sorry-free `cs5_pair_seed_mem`,
   `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-primeness.lean:98`) is the
   key existing ingredient for the "pure-L" half of route (b); it does not cover the cross-tagged
   cases on its own.
4. Do NOT retry the exact 2-point discrete frame or the naive "identify both copies"/naive
   collapse-projection ideas as originally sketched in the report — both are confirmed
   insufficient (see the blocker annotation for the specific counterexample-style reasoning).
5. Zero-debt constraint holds throughout: no `sorry`, no new `axiom`, no vacuous placeholder in
   `Cslib/`. If this genuinely cannot be closed constructively, the *acceptable* fallback is a
   PROVED mechanized obstruction theorem (not a `sorry`) — but per this dispatch's analysis, the
   claim more likely holds, so a proof attempt should be exhausted first.

## Verification Commands

```bash
cd ~/Projects/cslib
lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
lake exe checkInitImports
lake exe lint-style
lake shake --add-public --keep-implied --keep-prefix Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
grep -n "sorry" Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean Cslib/Logics/Modal/Basic.lean
```
