# Phase 2 Handoff — Create Support/Accessibility.lean

**Status**: [COMPLETED]

## What happened

- Created `Cslib/Logics/Modal/Tableau/Support/Accessibility.lean`, importing only
  `Cslib.Logics.Modal.Tableau.Branch`. Publishes `hasEdge_addEdge_cases`,
  `mem_successorsOf_hasEdge`, `hasEdge_mem_successorsOf` verbatim from their originals
  (`Soundness.lean` and `FmpMeasure.lean`/relocated `LoopChecking.lean` respectively).
- No `variable {Atom...}` section declared — all three facts are Atom-independent, so omitting
  the variable entirely (rather than declaring + `omit`-ing per lemma) is the minimal-footprint
  choice.
- Registered in `Cslib.lean` between `SoundnessStep` and `TDriver` (alphabetical).
- Full invariants table green: build 3312 jobs (+1 for the new module); checkInitImports 0;
  lint-style 0; shake 0 Modal/Tableau findings, 9 total; sorry census still exactly 1
  (`branchSatisfiableIn_s4FC_ancestor_redirect`); axiom count 0; do-not-edit files untouched.
- **Deviation discovered**: `FrameSoundness.lean` has a FOURTH `mem_successorsOf_hasEdge` copy
  named with a trailing prime (`mem_successorsOf_hasEdge'`), not an underscore suffix — not named
  anywhere in the plan text, and not caught by `census.py`'s suffix-only matching. Confirmed
  genuine via its docstring. **Deferred to Phase 3** — flagged explicitly so it isn't missed.
- `census.py` refined further: suffix-stripped families now require cross-file spread before
  merging (eliminates a same-file false-positive class found while auditing this family, e.g.
  `mem_modalUniverseS4_of`/`_of'`, which are legitimate distinct lemmas within one file, not
  duplicates). Current measured baseline on the post-Phase-2 tree (unchanged from Phase 1's close
  since Phase 2 was purely additive): **71 duplicates / 41 families** by the mechanical script;
  the known gap is that prime-named duplicates (like the one just found) are NOT included in that
  count and must be found by manual grep per family.

## Continuation pointer

Resume at **Phase 3**: migrate Accessibility consumers, delete duplicates. Before editing, ALSO
grep every family name plus `'` for its 41-family Accessibility trio, e.g.
`grep -rn "hasEdge_addEdge_cases'\|mem_successorsOf_hasEdge'\|hasEdge_mem_successorsOf'" *.lean`
in addition to the standard underscore-suffix census, given the prime-variant gap just found.
Known Phase 3 targets (from the plan plus this phase's addendum):
- `hasEdge_addEdge_cases`: BDriver.lean(_B), FmpMeasure.lean(_local), FrameCompleteness.lean(_Five,
  _C), FrameSoundness.lean(_anc, _FS), LoopChecking.lean(_S4), Soundness.lean (origin, to be
  de-privatized-then-deleted or fully removed and redirected to Support). No S5Simplification.lean
  copy actually exists despite the plan's text claiming one — confirmed by direct grep; record as
  another minor Scope Hypothesis discrepancy when Phase 3 executes.
- `mem_successorsOf_hasEdge`: FmpMeasure.lean (origin), LoopChecking.lean(_S4),
  S5Simplification.lean(_S5), FrameSoundness.lean (prime variant, `mem_successorsOf_hasEdge'`).
- `hasEdge_mem_successorsOf`: sole copy now lives in LoopChecking.lean (already consolidated in
  Phase 1) — route its call sites to `Support.Accessibility`'s published copy and delete the
  private LoopChecking.lean one.
