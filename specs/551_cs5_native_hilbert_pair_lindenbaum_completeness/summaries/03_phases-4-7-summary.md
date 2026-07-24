# Implementation Summary: CS5 Pair-Lindenbaum Incremental Assets — Phases 4-7

- **Task**: 551 - cs5_native_hilbert_pair_lindenbaum_completeness
- **Plan**: `plans/02_incremental-assets-deferred-route.md`
- **Dispatch scope**: Phases 4-7 ONLY. Phases 1-3 were landed in a prior dispatch (see
  `summaries/02_incremental-assets-phases-1-3-summary.md`) and consumed unchanged here. Phase 8
  (documentation/CI gate) is not attempted in this dispatch and remains open.
- **File modified**: `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Plan file also updated**: Phase 4 marked `[BLOCKED]` with the blocker record; Phases 5-6
  marked `[SKIPPED — Phase 4 blocked]`; Phase 7 marked `[COMPLETED]`.

## What landed

### Phase 4 [BLOCKED] — Cross-Inertness Support Lemma (the hard gate)

Attempted the structural induction on `DerivationTree` the plan's task list sketches, keyed on a
"necessitation-only-from-`[]`" invariant for bare-`□` conclusions:

```
∀ {Γ ψ}, DerivationTree CS5PairAxiom Γ (□ψ) → (□ψ ∈ Γ) ∨ Derivable CS5PairAxiom ψ
```

Tested via `lean_run_code` (not landed in the tracked file). The `assumption`/`necessitation`/
`weakening` cases close cleanly. The `modus_ponens` case does **not**: `exfalso` is not
justified there, because it is not vacuous. Counterexample: `CS5ModalAxiom.bBox : φ →
□(◇φ)` (`CS5.lean:216`) has a **bare box** as the consequent of an implication; `modus_ponens`
against a `bBox`-derived (or `k`/K-chained) hypothesis in `Γ` legitimately produces a bare-box
conclusion that is neither an assumption nor a necessitation witness. The naive invariant the
plan sketches is therefore **false** as stated, and the intended proof route does not go through.

A correct cross-inertness argument would need a strictly stronger inductive invariant (tracking
exactly which bare-box formulas over `cs5PairSeed H` content are K-reachable from seed-drawn
assumptions vs. reachable only via a `cross1`/`cross2` bridge) — assessed to be the same order of
difficulty as the Phase 7 disjunction-property obligation itself, matching the plan's own R-B
risk ("Phase 4 turns out to be as hard as obligation 3"). No semantic/soundness workaround
exists either (ruled out per the plan's Non-Goals: the cross-axioms are sound only under a
common valuation collapsing the two copies).

**Per the plan's own sanctioned fallback (R-B mitigation)**: marked `[BLOCKED]`, no `sorry`, no
vacuous placeholder inserted. Phases 5-6 skipped rather than substituted with an alternative
strategy (`.claude/rules/plan-compliance.md`).

### Phase 5 [SKIPPED — Phase 4 blocked]

Depends on Phase 4's cross-inertness lemma to reduce `τ_R A ∉ cl(cs5PairSeed H)` to the two
single-copy facts the plan names. Not attempted, per the plan's fallback.

### Phase 6 [SKIPPED — Phase 4 blocked]

Depends on Phase 4 symmetrically for `τ_L (□A) ∉ cl(cs5PairSeed H)`. Not attempted.

### Phase 7 [COMPLETED] — Formally Isolate the Research-Grade Obligation as a Named Open Lemma

Landed, sorry-free:

- **`CS5PairSeedDisjunctionProperty (H : Set (Proposition Atom)) (A : Proposition Atom) : Prop`**
  — the constructive disjunction property `τ_L (□A) ⊔ τ_R A ∉ cl_{CS5PairAxiom}(cs5PairSeed H)`,
  stated with **real content** (never `True`/`Unit`/`trivial`). Docstring records provenance
  ([Pacheco2024] Lemma 16, unsound as published — the negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈
  Θ` is invalid for a poset-maximal quasi-prime theory), the "no semantic witness" fact (report
  02 §2: the cross-axioms are sound only under a common valuation, collapsing the two copies),
  and status (open; expected to need a cut-free/nested-sequent argument, [Marin2021], not a
  direct Hilbert derivation). Never asserted as a theorem.

- **`cs5Pair_bigOr_imp_or`** — helper: for a list `l` all of whose elements are `a` or `b`,
  `⊢ bigOr l → (a ⊔ b)`, by induction on `l` using `cs5Pair_hOrI1`/`hOrI2`/`hOrE`/`hEFQ`.

- **`cs5Pair_orBot_imp_self`** — helper: `⊢ (x ⊔ ⊥) → x`, via `orE` composed with
  `Metalogic.empty_imp_id` and `cs5Pair_hEFQ`.

- **`cs5Pair_derivExcludes_of_disjunctionProperty`** — the conditional reduction theorem,
  consuming `hL`, `hR`, `hOpen` as **explicit hypotheses** (per the plan's "if Phase 4 blocked"
  contingency — `hL`/`hR` are not theorems here either, since Phases 5-6 were skipped):

  ```lean
  theorem cs5Pair_derivExcludes_of_disjunctionProperty {H A}
      (hL : cs5PairTauL (Proposition.box A) ∉ modalDeductiveClosure CS5PairAxiom (cs5PairSeed H))
      (hR : cs5PairTauR A ∉ modalDeductiveClosure CS5PairAxiom (cs5PairSeed H))
      (hOpen : CS5PairSeedDisjunctionProperty H A) :
      Metalogic.DerivExcludes (modalDerivationSystem CS5PairAxiom)
        {cs5PairTauL (Proposition.box A), cs5PairTauR A}
        (modalDeductiveClosure CS5PairAxiom (cs5PairSeed H))
  ```

  Proved by case analysis on the `List` argument of `DerivExcludes`: the `[]` case derives a
  contradiction with `hL` via `EFQ` (consistency of the closure); the singleton cases reduce to
  `hL`/`hR` via `cs5Pair_orBot_imp_self`; the `x :: y :: rest` (length ≥ 2) case reduces to
  `hOpen` via `cs5Pair_bigOr_imp_or`.

- **`## Open Obligations`** module section: what is proved, what is not (cross-inertness, the
  two individual exclusions, the named open obligation itself), and what a future discharge
  would unlock (instantiating `Metalogic.prime_set_exclusion`, projecting the prime superset back
  to a candidate box-backward pair — explicitly not attempted here, per the plan's Non-Goals).

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness`: green, 730 jobs.
- `grep -rn '\bsorry\b\|\badmit\b'`: zero tactic/term occurrences (two docstring-prose mentions
  of the word "sorry" only).
- `lake exe checkInitImports`: exit 0.
- `lake exe lint-style` on the file: clean.
- `lake lint` (full project): one pre-existing `docBlame` finding on `cs5PairSeed` (line 285) —
  a `/-! -/` section-header comment sits where the linter expects a `/-- -/` declaration
  docstring. This predates this dispatch (landed in Phase 3) and is out of scope for Phases 4-7;
  flagged for Phase 8's documentation pass. No lint findings on any Phase 4-7 declaration.
- `lean_verify` on `cs5Pair_derivExcludes_of_disjunctionProperty` and `cs5Pair_bigOr_imp_or`:
  axioms limited to `propext`/`Classical.choice`/`Quot.sound` (the latter has none at all).
- No task-number citations were introduced by this dispatch's new content (the pre-existing
  `specs/551_.../probes/...` path citations at lines 36/59/108 predate this dispatch, from
  Phase 1-3; Phase 8's task list already schedules their cleanup).

## Plan Deviations

- Phase 4 marked `[BLOCKED]` rather than completed — see blocker record above and
  `.orchestrator-handoff.json`. Sanctioned by the plan's own R-B risk mitigation; not a
  deviation from the plan's contract.
- Phases 5-6 marked `[SKIPPED — Phase 4 blocked]` rather than attempted — sanctioned by the same
  fallback (both explicitly `Depends on: 4`).
- No other deviations. Phase 7's definition and theorem match the plan's template statement
  (modulo `hL`/`hR` being explicit hypotheses rather than theorem citations, which is exactly
  the plan's own stated contingency for a Phase-4-blocked outcome).

## Next Steps

- A future dispatch (or the plan's spawned research subtask) targeting cross-inertness would
  need the stronger K-reachability invariant identified above before Phase 4 can be revisited;
  Phases 5-6 would follow directly once Phase 4 lands.
- The named open obligation `CS5PairSeedDisjunctionProperty` is the carrier for the spawned
  research subtask (cut-free/nested-sequent method, [Marin2021]) per the plan's "Spawned"
  section.
- Phase 8 (module docstring update, task-number citation audit, full CI pipeline) remains open
  and does not depend on Phase 4 landing.
