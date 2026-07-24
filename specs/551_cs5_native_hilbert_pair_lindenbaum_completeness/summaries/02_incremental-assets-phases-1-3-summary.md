# Implementation Summary: CS5 Pair-Lindenbaum Incremental Assets — Phases 1-3

- **Task**: 551 - cs5_native_hilbert_pair_lindenbaum_completeness
- **Plan**: `plans/02_incremental-assets-deferred-route.md`
- **Dispatch scope**: Phases 1-3 ONLY (of the plan's 8 phases). Phases 4-8 are **not** attempted
  in this dispatch and remain open.
- **File modified**: `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`

## What landed

### Phase 1 [COMPLETED] — Propositional-Core Extension of `CS5PairAxiom`

Extended the `CS5PairAxiom` inductive (`CS5Completeness.lean:92`) with nine propositional-core
constructors — `implyK`, `implyS`, `efq`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE` — each
quantified over the **entire** `Proposition (Atom ⊕ Atom)` type (not routed through
`cs5PairTauL`/`cs5PairTauR`), mirroring `CS5ModalAxiom`'s corresponding constructors
(`CS5.lean:170-195`). Reused `Cslib.Logic.Axioms.{AndI, AndE1, AndE2, OrI1, OrI2, OrE}` formers.
`left`/`right`/`cross1`/`cross2` are unchanged; no modal schema was added at mixed formulas.
The inductive's docstring now records the two-tier design and the reason whole-type
quantification is forced (the generic primeness engine's `hOrE`/`hEFQ`/`hCut` hypotheses in
`Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` range over the ambient formula type, not
just tagged formulas).

The four previously-landed lemmas (`cs5PairAxiom_left_derivable`, `cs5PairAxiom_right_derivable`,
`crossCond_left_stable`, `crossCond_right_stable`) compiled unchanged after the extension —
confirming risk R-A did not materialize.

### Phase 2 [COMPLETED] — Discharge the Primeness-Engine Preconditions at `CS5PairAxiom`

Landed the hypothesis bundle the generic engine needs, all sorry-free, one-line term proofs:

- `cs5Pair_hImplyK`, `cs5Pair_hImplyS` — raw `CS5PairAxiom` membership, via `.implyK`/`.implyS`.
- `cs5Pair_hEFQ`, `cs5Pair_hOrI1`, `cs5Pair_hOrI2`, `cs5Pair_hOrE` — `Deriv CS5PairAxiom []`
  instances, via `⟨.ax [] _ (.efq/.orI1/.orI2/.orE …)⟩`.
- `cs5Pair_hCut` — supplied by instantiating the existing generic supplier
  `modal_deriv_imp_of_union` (`Intuitionistic/PrimeTheory.lean`) at `Axioms := CS5PairAxiom`
  with `cs5Pair_hImplyK`/`cs5Pair_hImplyS`; the `insert a U` → `U ∪ {a}` shape conversion mirrors
  the precedent in `quasi_prime_set_exclusion` (`CS5.lean:864-870`) and `modal_prime_exclusion`
  (`Intuitionistic/PrimeTheory.lean:348-353`).

**Sanity check** (performed via `lean_run_code`, not left in the tracked file): partially
applying `Metalogic.prime_set_exclusion (modalDerivationSystem CS5PairAxiom) (fun _ => True)`
positionally with `cs5Pair_hOrI1`/`hOrI2`/`hOrE`/`hEFQ`/`hCut` plus the trivial-`Cons` closure
bundle (`modalDeductiveClosure CS5PairAxiom`, `modal_subset_deductive_closure`,
`modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS`) elaborated with **zero errors
and zero sorries**, leaving only `S`, `E`, `hS : Admissible … S`, `h_excl : DerivExcludes … E S`,
and the (vacuous under `Cons := fun _ => True`) chain-consistency hypothesis as remaining
arguments. This confirms the bundle discharges every schema/cut precondition, leaving
`DerivExcludes` (via `h_excl`) as the sole substantive remaining hole — exactly as the plan
anticipated.

### Phase 3 [COMPLETED] — The Two-Sided Seed `cs5PairSeed`

Defined:

```lean
def cs5PairSeed (H : Set (Proposition Atom)) : Set (Proposition (Atom ⊕ Atom)) :=
  cs5PairTauL '' H ∪ cs5PairTauR '' (modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H))
```

using `boxInv` (`Segment.lean:103`) and `modalDeductiveClosure` (`Intuitionistic/PrimeTheory.lean:78`).
Landed alongside it:

- `cs5PairTauL_injective` / `cs5PairTauR_injective` — corollaries of `Proposition.map_injective`
  (`Basic.lean:199`) applied to `Sum.inl_injective`/`Sum.inr_injective`, ruling out tag collision
  within each branch (each tagging map is a genuine embedding, so a witnessing `φ`/`ψ` recovered
  from an element of the seed is uniquely determined).
- `cs5PairSeed_mem_left : φ ∈ H → cs5PairTauL φ ∈ cs5PairSeed H`
- `cs5PairSeed_mem_right : φ ∈ modalDeductiveClosure CS5ModalAxiom (boxInv H) → cs5PairTauR φ ∈ cs5PairSeed H`
- `cs5PairSeed_mem_iff` — the membership-inversion lemma: every element of `cs5PairSeed H` is
  either `cs5PairTauL φ` for some `φ ∈ H`, or `cs5PairTauR ψ` for some `ψ` in the `CS5`-deductive
  closure of `boxInv H`. Proved directly by `simp only [cs5PairSeed, Set.mem_union, Set.mem_image]`.
  This is the case-split later phases (not in this dispatch) induct against.

## Verification performed

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness` — green after every
  phase (730 jobs, exit 0). Final re-run after Phase 3 also green.
- `grep -n '\bsorry\b\|\badmit\b'` over the file — only one hit, docstring prose (line 37,
  "close sorry-free"). Zero tactic/term `sorry`/`admit`.
- `#print axioms`-equivalent (`lean_verify`) on `cs5PairSeed_mem_iff` — only `propext`, no
  `sorryAx`.
- `lake exe checkInitImports` — passes silently (no violations); the file already imports
  `Cslib.Init` transitively via its existing `import Cslib.Init` line.
- All four previously-landed Phase-3-of-plan-01 lemmas re-verified to compile unchanged after
  the `CS5PairAxiom` extension (Phase 1's R-A discharge).

No `.claude`-scoped lint-style/CI pipeline run (Phase 8, out of scope for this dispatch, is the
plan's single designated point for the full CI pipeline).

## Plan Deviations

None. All three phases were implemented exactly as specified in
`plans/02_incremental-assets-deferred-route.md`, including exact declaration names, docstring
content, and citation of the plan's mandated file/line anchors. No `.lean` step required
substitution, and no phase was blocked.

## Out of scope (not attempted)

Per the dispatch instructions, Phases 4-8 of the plan were **not** attempted:

- Phase 4: Cross-Inertness Support Lemma (hard gate)
- Phase 5: Individual Exclusion `τ_R A ∉ cl(cs5PairSeed H)`
- Phase 6: Individual Exclusion `τ_L (□A) ∉ cl(cs5PairSeed H)`
- Phase 7: Formally Isolate the Research-Grade Obligation as a Named Open Lemma
  (`CS5PairSeedDisjunctionProperty`)
- Phase 8: Documentation, Frontier Record, and CI Gate

These remain `[NOT STARTED]` in the plan file. No `cs5_completeness''`, `cs5_box_backward`, or
any other Non-Goals-listed declaration was attempted, per the plan's explicit exclusions.

## Commits

- `task 551 phase 1: propositional-core extension of CS5PairAxiom`
- `task 551 phase 2: discharge primeness-engine preconditions at CS5PairAxiom`
- `task 551 phase 3: define the two-sided seed cs5PairSeed`

Each commit is scoped to `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` plus
the plan file's phase-marker/checklist updates only.
