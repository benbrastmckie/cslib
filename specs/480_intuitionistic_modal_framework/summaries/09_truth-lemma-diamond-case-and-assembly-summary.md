# Phase 3c Summary: TruthLemma.lean — .diamond Case Helper + canonical_truth_lemma Assembly

**Task**: 480 (intuitionistic modal framework) | **Plan**: v4 | **Phase**: 3c | **Status**: COMPLETED

## What Was Proved

`Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` gains two new theorems:

### `truth_diamond_case`

The `.diamond` constructor case of the (to-be-assembled) `canonical_truth_lemma`:

```
BForces canonicalR canonicalVal botForces w (◇φ) ↔ (◇φ) ∈ w.val
```

taking the induction hypothesis for `φ` as an explicit parameter universally quantified over all
canonical worlds (same 3a/3b design note). Unlike `truth_box_case`, `canonicalR w v` is a
**single witness**, not a pair `⟨w', u⟩` — `BForces_diamond` is a bare existential over
successors of `w` itself, so the proof is simpler:

- **Forward direction**: given `u` with `canonicalR w u` and `φ` forced at `u`, `ih u` transports
  forcing to `φ ∈ u.val`; `canonicalR w u`'s diamond clause (`.2`) then gives `◇φ ∈ w.val`
  directly. **No modal axiom is needed for this direction.**
- **Backward direction**: given `◇φ ∈ w.val`, `canonical_diamond_witness` (Phase 2c) produces a
  single prime `v` with `canonicalR w v` and `φ ∈ v.val`; `ih v` transports this to forcing,
  witnessing the existential.

`truth_diamond_case` threads `h_Kdia`, `h_Cd` (and `h_K`, `h_dbot` transitively) solely via the
call to `canonical_diamond_witness` — no new axiom introduced. `h_Idb` is confirmed **not**
consumed (per Phase 2c's completion note).

### `canonical_truth_lemma`

The assembled truth lemma over all seven `Proposition` constructors, by `induction φ generalizing
w`, dispatching each constructor to its Phase 3a/3b/3c helper:

```
BForces canonicalR canonicalVal botForces w φ ↔ φ ∈ w.val
```

carrying the full four-axiom union `{h_K, h_Kdia, h_Idb, h_Cd}` (plus `h_dbot`, needed
transitively by the diamond case) as parametric hypotheses, with `botForces` kept a loose
parameter throughout (bridged via `h_bot`).

## Reference Grounding

- [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3, clause 3.5 (`.diamond` birelational forcing clause) and the assembled truth lemma.
- ianshil/CK `general_th_completeness.v`, diamond case — the construction consumed here is
  `canonical_diamond_witness`, already proved and frozen in Phase 2c.
- Report 03 §4 row 7 (diamond axiom requirement) and row 8 (assembled union).

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.TruthLemma` — succeeded (596 jobs), no
  warnings.
- `lake build` (full project) — succeeded (3190 jobs); only pre-existing, unrelated warnings/
  sorries (`Cslib/Logics/Propositional/Tableau/Intuitionistic/{Scheme,Completeness}.lean`,
  `Tableau/Minimal/Completeness.lean`), outside this task's scope.
- `lake exe checkInitImports` — passed (no output).
- `lake lint` / `lake exe lint-style` (scoped to `TruthLemma.lean`) — passed (no output).
- `lean_verify` on `truth_diamond_case` and `canonical_truth_lemma`: both
  `{propext, Classical.choice, Quot.sound}` only — no new axiom.
- `grep -rn "\bsorry\b"` on `TruthLemma.lean`: no real matches (only the substring inside
  "sorry-free" in docstrings).
- `canonical_truth_lemma` covers all seven constructors (no missing-case warning from
  `induction ... with`).
- `git status --porcelain`: only `TruthLemma.lean` modified under `Cslib/`; `CanonicalModel.lean`
  and the 3a/3b helpers untouched.

## Plan Deviations

None. The diamond forward direction turned out to need **no modal axiom at all** (a pleasant
simplification over the box case), closing purely via `canonicalR`'s diamond clause and the IH —
this is consistent with, not a deviation from, the plan's threaded-hypothesis table (which
attributes the axiom need to the *witness construction*, i.e. the backward direction). The
assembly was mechanical once all seven helpers typechecked, exactly as the plan's Phase 3a design
note anticipated. No STOP contingency was triggered.

## Next Steps

Phase 4 (`Completeness.lean`): package the canonical `BModel` from `CanonicalPrimeWorld`, the
`Preorder`, `canonicalR`, `canonicalVal`, `canonical_f1`/`canonical_f2`; state parametric
`ivalid_completeness`/`mvalid_completeness` from `canonical_truth_lemma` + `modal_prime_exclusion`;
expose the consistency hook. This is the final phase of the core framework (task 480); tasks
492-495 consume `Completeness.lean`'s parametric exports downstream.
