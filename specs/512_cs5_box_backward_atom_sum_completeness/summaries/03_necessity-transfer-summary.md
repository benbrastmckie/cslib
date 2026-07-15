# Summary 03: Necessity-Transfer Conjecture Attempted (Task 512, Phase 3 continuation)

## Outcome

`[PARTIAL]` — no full closure of `cs5Combined_seed_excludes`, no proved obstruction either. Real,
sorry-free, axiom-clean progress landed; the search space for a "cheap" discharge has now been
substantially narrowed by rigorous elimination.

## What landed

`cs5Combined_necTransfer` (`Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`):
`⊢CS5Combined τLΨ → τRA` implies `⊢CS5 □Ψ → □A`, via necessitation + `K`-distribution + the
already-landed box-equivalence lemmas + atom-collapse. Sorry-free; `#print axioms` shows only
`propext`/`Classical.choice`/`Quot.sound`.

## What this dispatch determined (the main deliverable, beyond the one lemma)

1. **The necessity-transfer conjecture's natural proof-algebra route is exhausted.** The landed
   lemma is the strongest reachable consequence via necessitation/K/cross-axioms/box-equivalence,
   and it is PROVABLY INSUFFICIENT (vacuous at `Ψ := A`, the hardest case, since `□A → □A` is a
   trivial tautology). No further chaining through this algebra can reach the needed
   unboxed-antecedent form `Ψ → □A`.
2. **Both of report 02's proposed discharge routes reduce to the same canonical-scale
   obstacle.** Route 1 (semantic) was already shown circular by report 02 (needs canonical-scale
   models). This dispatch's feasibility analysis of route 2's derivation-height induction shows
   it is not actually a distinct, cheaper alternative: any invariant closed under `ax`/
   `modus_ponens` for arbitrary `Γ` is a semantic truth-predicate in disguise, and a concrete toy
   valuation attempt fails because `H` is only quasi-prime (disjunction property), not
   negation-complete — so it cannot faithfully represent `w ⊨ τL '' H` for compound formulas.
   Only the full canonical model (all quasi-prime theories, mirroring `CS5Segment`/`cs5Mreach`)
   can do this, which is essentially the same machinery Phase 5 needs for `cs5_truth_lemma`
   itself.

## Recommendation for the next dispatch

Reframe Phase 3 as inseparable from Phases 4-5's canonical-model construction: build the
`CS5Combined` canonical model and a genuine truth lemma for it directly, and read off
`cs5Combined_seed_excludes` as a corollary, rather than continuing to search for a standalone
"cheap gate" proof. Full detail, including the precise chain of eliminations across three
dispatches, is in `handoffs/03_necessity-transfer-attempted.md`.

## Plan Deviations

- Task 3's "Tasks (route 2 — proof-theoretic projection, FALLBACK)" checklist item ("any combined
  derivation ... projects to a CS5 derivation forcing `□A ∈ H`") is *(deviation: altered —
  attempted via the necessity-transfer conjecture as directed by the prior continuation handoff;
  found the natural algebraic route yields only a strictly weaker, insufficient consequence;
  documented precisely rather than forcing a false completion)*.
- The Phase 3 "Tasks (route 1 — semantic, RECOMMENDED first)" checklist remains *(deviation:
  skipped — three dispatches now confirm this needs canonical-scale structure, not a toy
  2-world frame; re-attempting the toy-frame sketch as written in the plan would not converge,
  per this dispatch's negation-completeness argument)*.

## Verification

```
lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical   -- green
lake build                                                          -- full project green
lake test                                                           -- green
lake exe checkInitImports                                           -- clean
lake exe lint-style Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean  -- clean
grep -rn "\bsorry\b" Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean  -- none (prose only)
grep -n "^axiom " Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean     -- none
```

`#print axioms Cslib.Logic.Modal.cs5Combined_necTransfer` → `propext`, `Classical.choice`,
`Quot.sound` only.
