# Implementation Summary: Native Hilbert CS5 Completeness via Atom-Sum Pair Lindenbaum

- **Task**: 551 - cs5_native_hilbert_pair_lindenbaum_completeness
- **Status**: [PARTIAL]
- **Plan**: `plans/01_native-hilbert-cs5-completeness-plan.md`
- **Phases completed**: 3 of 8 (Phase 4 [BLOCKED]; Phases 5-8 not attempted)

## What Was Delivered

### Phase 1 (COMPLETED): R1 de-risking probe

`specs/551_.../probes/cs5-pair-combined-atomsum.lean` proves, sorry-free, that the combined
`CS5PairAxiom` construction over `Atom ⊕ Atom` (`CS5ModalAxiom` on each tagged copy plus two
cross-condition axioms `□(τ_L B) → τ_R B` / `□(τ_R B) → τ_L B`) is simultaneously:

- **Sound**: for any fallible-world model satisfying `cs5FC`, the cross-condition axioms are
  validated purely by reflexivity of the modal relation, using a valuation transport lemma
  (`ckforces_map`) that identifies forcing `τ_L B` with forcing `τ_R B` when both tags share the
  same underlying valuation.
- **`cl`-stable by construction**: any set deductively closed under `CS5PairAxiom` satisfies both
  cross-conditions automatically, via a single `modus_ponens` step against the internalised
  axioms — no external, non-`cl`-stable `Cons` predicate is needed at all.

This is the R1 hard gate the plan specifies; both properties closed sorry-free, with all
declarations depending only on `[propext]` (or `[propext, Classical.choice, Quot.sound]`),
confirmed via `lake env lean` output — no `sorryAx`.

### Phase 2 (COMPLETED): Atom-relabeling derivability functoriality

`Cslib/Logics/Modal/Metalogic/DerivationTree.lean` gains `DerivationTree.map`/`Deriv.map`/
`Derivable.map`: fully generic infrastructure showing derivability lifts along any atom
relabeling `f : Atom → Atom'`, given a schema-compatibility hypothesis relating the source and
target axiom systems. Not tied to `CS5PairAxiom` specifically (which did not yet exist when this
phase ran); reusable well beyond this task.

### Phase 3 (COMPLETED): `CS5PairAxiom` library promotion

New file `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` (added to `Cslib.lean`
via `lake exe mk_all --module`) promotes the probe's `CS5PairAxiom`, the `τ_L`/`τ_R` tag maps, the
easy transport direction (`Derivable CS5ModalAxiom φ → Derivable CS5PairAxiom (τ_L/τ_R φ)`, via
`Derivable.map`), and the `cl`-stability lemmas (`crossCond_left_stable`/`crossCond_right_stable`)
to the library. Deliberately kept separate from `CS5Canonical.lean`, which pursues the unrelated
(and separately dead-ended) birelational completeness route.

## Phase 4: BLOCKED — the genuine crux surfaces early

Phase 4 (instantiate `prime_maximal_is_prime`/`prime_set_exclusion` at `CS5PairAxiom`, excluding
`E := {τ_L(□A), τ_R A}`, to obtain a prime combined theory) could not be completed. Two distinct
findings, in order of discovery:

1. **A real gap in Phase 3's `CS5PairAxiom`**: `prime_exclusion`/`prime_maximal_is_prime` require
   the `orE` (and `implyK`/`implyS`/`efq`/etc.) schema to hold for **arbitrary**, including
   genuinely mixed (`inl`/`inr`-mixing), formulas over `Atom ⊕ Atom` — not just pure-tagged
   copies. Phase 3's `left`/`right`/`cross1`/`cross2` constructors only ever produce pure-tagged
   or cross-bridging conclusions, never a general mixed-formula propositional schema instance.
   This is mechanically fixable (add ~9 propositional-core constructors quantified over the full
   combined type).
2. **The deeper obstruction**: even with that fix, showing the specific exclusion set stays
   excluded from the natural seed `S₀ := τ_L''H ∪ τ_R''(cl(boxInv H))` requires a
   conservativity/projection-faithfulness theorem (`CS5PairAxiom`-derivability from a two-sided
   context reduces to `CS5ModalAxiom`-derivability on each side) — the plan's own "R2" risk, but
   it turns out to already be load-bearing at Phase 4's seed step, not deferrable to Phase 5. This
   claim is plausible (a sketch via `tBox`/`□B → B` and derivation-height induction is recorded in
   the plan's Phase 4 blocker section) but is a substantial, unproven metatheoretic result — not a
   mechanical continuation. Semantic (soundness-based) and signature-collapse routes were both
   tried and explicitly ruled out (documented in the plan with the exact reasoning for each).

Full details, including the exact routes tried and why each fails, are recorded in the plan
file's Phase 4 "BLOCKER" section (`plans/01_native-hilbert-cs5-completeness-plan.md`).

## Plan Deviations

- **Phase 2**: the per-side `Sum.inl`/`Sum.inr` specialisation into `CS5PairAxiom` (part of
  Phase 2's task list) was deferred to Phase 3, since `CS5PairAxiom` itself is defined in Phase 3
  per that phase's own title. Phase 2 delivered the fully generic `Derivable.map` instead; Phase 3
  instantiated it. No substance lost.
- **Phase 3**: `CS5Canonical.lean` was not used as the target file; a new file
  `CS5Completeness.lean` was created instead (an explicitly offered alternative in the plan),
  since `CS5Canonical.lean` is dedicated to the unrelated birelational route.
- **Phase 4**: marked `[BLOCKED]` per the Escalation Protocol, with the full analysis recorded
  inline in the plan file. No workaround, `sorry`, or vacuous placeholder was used.

## Zero-Debt Verification

- `sorry` count in all new/modified files: 0 (confirmed via `grep -rn '\bsorry\b'`, only prose
  mentions of "sorry-free" in docstrings match).
- New `axiom` declarations: 0 (confirmed via `grep -c '^axiom '`, only a docstring prose match).
- Vacuous definitions: none introduced.
- `lake build` on all touched modules (`Cslib.Logics.Modal.Metalogic.DerivationTree`,
  `Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness`): green.
- `lake exe mk_all --module`: run, `Cslib.lean` updated.
- `lake exe checkInitImports`/full-project `lake build`/`lake lint`/`lake test`: **not run** —
  at time of this dispatch, a concurrent session's in-progress edit to
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (entirely outside this task's file scope) left
  the full-project build graph transiently broken (a missing `.olean` for that module), so
  project-wide tools could not execute. This task's own new/modified files were independently
  scope-built and verified clean.

## Artifacts

- `specs/551_.../plans/01_native-hilbert-cs5-completeness-plan.md` (phase statuses + Phase 4
  blocker updated in place)
- `specs/551_.../probes/cs5-pair-combined-atomsum.lean` (Phase 1 probe)
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (Phase 2 functoriality infrastructure)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` (Phase 3 library promotion,
  new file)
- `Cslib.lean` (barrel import addition)
- `specs/551_.../summaries/01_native-hilbert-cs5-completeness-summary.md` (this file)

## Recommended Next Steps

1. Spawn a dedicated research pass on the context-relative conservativity lemma sketched in the
   Phase 4 blocker (candidate anchor: Pacheco's Lemma 16/17 area, since his defect is the unsound
   version of the same disjunction-under-mutual-constraint problem) before any further
   implementation dispatch.
2. If conservativity is confirmed provable, resume at Phase 4 with the `CS5PairAxiom`
   propositional-core fix applied first.
3. If conservativity is refuted or judged infeasible in reasonable effort, consider Route A
   (`CS5 ≡ IS5` collapse-then-reuse via `is5_completeness`) as the pragmatic alternative the
   research report already scoped as an explicit non-goal here but flagged as "mostly done."
