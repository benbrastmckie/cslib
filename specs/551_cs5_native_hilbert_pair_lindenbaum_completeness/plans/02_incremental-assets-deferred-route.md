# Implementation Plan: CS5 Pair-Lindenbaum Incremental Assets, Deferred Route Decision

- **Task**: 551 - cs5_native_hilbert_pair_lindenbaum_completeness
- **Status**: [IMPLEMENTING]
- **Effort**: 14 hours
- **Dependencies**: None (517, 509, 508 are archived/completed and no longer gate this task; see
  Research Integration below)
- **Research Inputs**:
  - reports/01_route-b-native-hilbert-cs5-research.md
  - reports/02_conservativity-blocker-route-decision.md
  - reports/03_remaining-obligations-and-path.md
- **Artifacts**: plans/02_incremental-assets-deferred-route.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-compliance.md
  - .claude/rules/lean4.md
  - .claude/rules/cslib.md
  - .claude/rules/no-task-references-in-deliverables.md
- **Type**: cslib

## Overview

This plan supersedes `plans/01_native-hilbert-cs5-completeness-plan.md`, which drove toward a
native `cs5_completeness''` and terminated at a [BLOCKED] Phase 4. Reports 02 and 03 established
that the residual obstruction is a single, precisely-located, **research-grade** proof-theoretic
lemma with no semantic witness, and that the native completeness theorem is therefore not
reachable within this task. The user decision governing this revision is **"Both: assets now,
decide later."**

Accordingly this plan does three things and nothing else: (1) it lands the obligations that are
**useful under either eventual route** (the propositional-core extension of `CS5PairAxiom` and the
two individual seed exclusions), so no work here is wasted whichever route is later chosen;
(2) it **formally isolates** the research-grade obligation as a single **named open lemma** — a
stated, precisely-typed Lean `Prop`-valued definition with a docstring recording its provenance
(Pacheco 2024 Lemma 16, unsound as published, open here), consumed downstream as an **explicit
hypothesis**, never as a `sorry`; and (3) it **defers** the Route A vs. Route Native decision
until the spawned research subtask reports.

**Definition of done**: the four scope files plus `CS5Completeness.lean` build green under
scoped `lake build`, the sorry/admit census stays at **zero**, the named open obligation is
stated and documented but never asserted as a theorem, and the `DerivExcludes` precondition of
`prime_set_exclusion` is reduced to exactly that one named hypothesis by a sorry-free conditional
theorem.

### Research Integration

Newly integrated in this revision:

| Report | What it contributes |
|---|---|
| `reports/03_remaining-obligations-and-path.md` | Blocker re-assessment (deps 517/509/508 stale and archived); verified build census (scoped `lake build` of the four scope files + `CS5Completeness` = **731 jobs, exit 0**, **zero** sorry/admit — grep hits are docstring prose only); the landed-asset inventory with live line numbers; the finding that **`cs5_completeness''` does not exist as a declaration anywhere** and `cs5_box_backward` is prose-only; the three-obligation decomposition (mechanical / tractable / research-grade) this plan's phase structure implements; and the concrete Route-A lemma list with `CS5 ⊢ idb` as its unproven first gate |
| `reports/02_conservativity-blocker-route-decision.md` | The decisive structural reason the seed-exclusion has **no semantic witness** (§2: cross-axiom soundness forces a common valuation, collapsing the two copies, so no sound model separates `S₀` from `E`); identification of the obligation as Pacheco 2024 Lemma 16 (published proof unsound here); the adversarial confirmation that the discarded `CS5Combined` scaffold hit this identical wall (`cs5Combined_seed_excludes`, never closed); the four-route evaluation |

Carried forward from the prior round: `reports/01_route-b-native-hilbert-cs5-research.md` (route
selection, `cl`-stability gap, the `Atom ⊕ Atom` repair sketch, R1/R2 risk register).

### Prior Plan Reference

`plans/01_native-hilbert-cs5-completeness-plan.md`. Its Phases 1-3 are **[COMPLETED] and landed
sorry-free** and are consumed, not rebuilt, by this plan:

| Landed asset | Location | Reused by |
|---|---|---|
| `cs5PairTauL` / `cs5PairTauR` | `CS5Completeness.lean:80,84` | all phases |
| `CS5PairAxiom` (`left`/`right`/`cross1`/`cross2`) | `CS5Completeness.lean:92` | extended in Phase 1 |
| `cs5PairAxiom_left_derivable` / `_right_derivable` | `CS5Completeness.lean:112,117` | Phases 4-6 |
| `crossCond_left_stable` / `crossCond_right_stable` | `CS5Completeness.lean:136,148` | Phase 7 |
| `DerivationTree.map` / `Deriv.map` / `Derivable.map` | `DerivationTree.lean` | Phases 1, 4 |
| `cs5_axiom_sound''` | `CS5.lean:352` | route-agnostic asset |
| `cs5_dia_or` (k3) / `cs5_dia_bot_imp_bot` (k5) | `CS5.lean:539,712` | Route-A asset if chosen |
| `cs5_symmetric_tail_box_gap` | `CS5.lean:686` | motivates the pair; cited in docs |
| `ckvalidFC_completeness` (parametric driver) | `CKExtension.lean:246` | future assembly, either route |
| `is5_completeness` | `IS5.lean:364` | Route-A asset if chosen |

Prior plan Phases 4-8 are **retired by this revision**: Phase 4 as written is unexecutable (its
seed-exclusion step is the research-grade obligation), and Phases 5-8 all sit downstream of it.
Their intent is preserved — Phase 4's tractable fragments become this plan's Phases 1-6, and the
untractable fragment becomes this plan's Phase 7 named open obligation.

### Deferred Decision (Route A vs. Route Native)

**No route is chosen by this plan.** Both remain live; the decision is deferred until the spawned
research subtask (below) reports.

**Route A (collapse to IS5) remains available and is mostly wired.** Its full obligation chain,
in order:

1. `cs5_derives_idb : Derivable (@CS5ModalAxiom Atom) (idb …)` — **the unproven Route-A premise.**
   Report 03 §2 verified by grep over `Cslib/Logics/Modal/` that `idb` (and `k4`) are **absent
   from every `Constructive/CS5*` file**; `idb` occurs only in the intuitionistic/minimal systems
   (`IS5.lean`, `IS4.lean`, `MS5.lean`). So `CS5 ⊢ idb` is currently **unproven**, not merely
   unstated. It is a bounded, self-contained Hilbert derivation — but it has never been done, and
   Route A must not be adopted before it is discharged.
2. `cs5_iff_is5_derivable : Derivable CS5ModalAxiom φ ↔ Derivable IS5ModalAxiom φ` — forward via
   the landed collapse axioms `cs5_dia_or` (k3) + `cs5_dia_bot_imp_bot` (k5) + step 1; reverse by
   checking each `IS5ModalAxiom` constructor is CS5-derivable (the K/T/4/B modal core is shared).
3. `cs5FC_iff_is5FC_valid : CKValidFC cs5FC'' φ ↔ IValidFC is5FC φ` — the validity-coincidence
   bridge. Not circular: it draws on the **independently landed** `is5_completeness`, not on CS5
   completeness.
4. `cs5_completeness''` := compose 2 + 3 + `is5_completeness`; then state
   `cs5_soundness_completeness''` against `cs5_axiom_sound''`.

**Cost of Route A**: it abandons the native-Hilbert method-uniformity mandate — it re-bases the
semantics onto IS5's birelational frame class. Adopting it is a genuine mandate change that only
the user can authorize (report 02 §4). Nothing in this plan forecloses it, and nothing in this
plan performs it. Every asset this plan lands (the propositional core, the seed exclusions, the
named open obligation, the conditional `DerivExcludes`) is inert under Route A rather than wasted:
it stays in the library as the documented native-route frontier.

**Route Native** remains available and is what this plan advances toward, minus its one open
lemma.

### Spawned

A dedicated **research subtask** carries obligation 3 (Phase 7's named open lemma). Its scope:

- **Target**: a correct proof of the constructive **disjunction property of `CS5PairAxiom` under
  the `boxInv` cross-constraint**, from the two-sided seed — equivalently the statement named in
  Phase 7.
- **Method mandate**: a **cut-free / nested-sequent** route, not a direct Hilbert argument.
  Primary literature: **Marin–Morales–Straßburger 2021** (nested sequents for constructive S5);
  secondary: **Pacheco 2024**, Lemmas 16/17, treated as the *defective* version to **repair**
  (its published proof uses the negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, invalid for a
  poset-maximal quasi-prime theory).
- **Explicitly out of scope for the subtask**: the dead ends listed under Non-Goals below.
- **Reporting contract**: the subtask reports either (a) a proof strategy concrete enough to plan
  against, or (b) a verdict that the lemma is open, in which case the deferred route decision
  resolves to Route A or to task closure at [PARTIAL].

### Roadmap Alignment

No `specs/ROADMAP.md` present. The uniformity thesis (CK/CT/CS4/CS5 all complete by the same
fallible-world canonical-model method) is unchanged as a long-term goal; this plan's contribution
to it is a precisely-bounded, documented frontier rather than a closed theorem.

## Goals & Non-Goals

**Goals**:
- Extend `CS5PairAxiom` with a **full propositional core** quantified over the entire
  `Proposition (Atom ⊕ Atom)` type (~9 constructors), keeping the modal schemata pure-tagged, so
  the generic `prime_exclusion`/`prime_set_exclusion` engine's schema hypotheses become
  dischargeable at genuinely mixed formulas.
- Discharge the engine's `hImplyK`/`hImplyS`/`hOrI1`/`hOrI2`/`hOrE`/`hEFQ`/`hCut` preconditions at
  `CS5PairAxiom` as named, reusable library lemmas.
- Define the two-sided seed `cs5PairSeed` and prove the **two individual exclusions**
  `τ_R A ∉ cl(S₀)` and `τ_L (□A) ∉ cl(S₀)`, together with the cross-inertness support lemma they
  both rest on.
- **Formally isolate** the research-grade obligation as a single named, precisely-stated,
  thoroughly documented **open** definition — never a `sorry`, never a vacuous placeholder, never
  asserted as a theorem — and reduce `DerivExcludes` to exactly that one hypothesis by a
  sorry-free conditional theorem.
- Keep the scoped build green and the sorry/admit count at **zero** at every phase boundary.

**Non-Goals** (each explicitly out of scope; do not re-propose):
- **The native `cs5_completeness''` theorem is NOT a deliverable of this task under this
  revision.** It does not currently exist as a declaration anywhere in `Cslib/`, and it is not
  reachable without obligation 3. Neither is `cs5_box_backward`, `cs5_box_backward_onesided`, nor
  `cs5_soundness_completeness''`. This plan does not attempt any of them.
- **Committing to Route A.** No `cs5_derives_idb`, no `cs5_iff_is5_derivable`, no
  `cs5FC_iff_is5FC_valid` is attempted here. The decision is deferred (see Deferred Decision).
- **A direct Hilbert proof of obligation 3.** Research-grade, no semantic witness,
  multi-day-to-open. Not scheduled as a phase in this plan; carried by the spawned subtask.
- **The semantic `cs5PairAxiom_sound` route to seed-exclusion.** Ruled out and *not to be
  retried*: the cross-axioms are only sound under a **common** valuation for both copies, which
  identifies `τ_L X` with `τ_R X`, collapsing `cross1` to `□B → B`; hence every sound model
  forces the excluded `τ_R A` whenever `A ∈ H`, and **no sound model separates `S₀` from `E`**
  (report 02 §2). The route is additionally circular: it presupposes the truth lemma being built.
- **Signature-collapse via a `Sum.elim id id` retraction.** Ruled out and *not to be retried*:
  `cross1`'s image `□B → B` is not a `CS5ModalAxiom` instance, so the retraction is not
  schema-compatible with `CS5PairAxiom` and `Derivable.map` cannot be applied along it.
- **Route C (labelled/Simpson adequacy bridge)** as a deliverable of this task. The labelled
  `cs5_completeness` at `Labelled/Completeness.lean:130` already exists and is a different result;
  it is not renamed, moved, wrapped, or presented as this task's target.
- **The `cs5FCIncest` labelled-parity variant** (prior plan Phase 8). Retired.
- Re-proving anything already landed sorry-free.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R-A: Extending `CS5PairAxiom` with a mixed-formula propositional core breaks the landed Phase-3 lemmas (`cs5PairAxiom_left/right_derivable`, `crossCond_*_stable`) | H | L | Adding constructors only *enlarges* derivability; the `Derivable.map` schema-compat witnesses (`.left`/`.right`) are unaffected. Phase 1 re-runs the scoped build and explicitly re-verifies all four landed lemmas before the phase is declared green |
| R-B: The cross-inertness support lemma (Phase 4) turns out to be as hard as obligation 3 | H | M | Phase 4 is a **hard gate with an isolating fallback**: on failure, mark Phase 4 [BLOCKED], skip Phases 5-6 and 8's assembly clause, and still land Phases 1-3 and 7 (the isolation phase depends only on Phases 1 and 3, never on 4-6). The plan's headline deliverable — a documented, sorry-free open frontier — survives a Phase-4 failure intact |
| R-C: An implementer treats the Phase-7 named obligation as a proof target and reaches for `sorry` or a vacuous `:= True` placeholder to "close" it | H | M | Phase 7 states the obligation as a `Prop`-valued **definition** with real content (never `True`/`Unit`/`trivial`), consumed downstream only as an explicit hypothesis. `.claude/rules/lean4.md`'s vacuous-definition prohibition and the zero-sorry gate in every phase's verification criteria are the enforcement. A `sorry` anywhere in the scope files fails the phase |
| R-D: Scope creep back toward `cs5_completeness''` / `cs5_box_backward` mid-implementation | M | M | Non-Goals states the exclusion explicitly. `.claude/rules/plan-compliance.md` applies unconditionally to `.lean` files: a would-be deviation is a [BLOCKED] escalation, never a silent substitution |
| R-E: The individual exclusions (Phases 5-6) need a *stronger* fact than report 02 §2's sketch supplies from the mixed seed | M | M | Phase 4 factors the shared content out as one named support lemma so Phases 5 and 6 each reduce to a short application; if Phase 4's statement proves insufficient, that surfaces in Phase 4, not scattered across two later phases |
| R-F: Docstrings citing ephemeral task numbers land in `Cslib/` | L | M | `.claude/rules/no-task-references-in-deliverables.md`: Lean docstrings are deliverables. Cite durable anchors (file + declaration names, `[Pacheco2024]`, `[Marin2021]`), never "task N". Phase 8 audits this |
| R-G: Full-project `lake build` blocked by unrelated concurrent edits (as happened in prior Phase 3) | L | M | Phase gates use **scoped** `lake build Module.Name` on the four scope files + `CS5Completeness`; the full-project pipeline runs once, in Phase 8, and a transient unrelated breakage there is reported, not worked around |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 3 |
| 4 | 5, 6 | 4 |
| 5 | 7 | 3 |
| 6 | 8 | 2, 5, 6, 7 |

Phases within the same wave can execute in parallel. Note the deliberate structure: **Phase 7
(the isolation phase) depends only on Phase 3**, never on Phases 4-6. If Phase 4 blocks, Phase 7
still executes and the plan still delivers its headline artifact.

### Phase 1: Propositional-Core Extension of `CS5PairAxiom` [COMPLETED]

- **Goal:** Extend `CS5PairAxiom` with a full propositional core quantified over the **entire**
  `Proposition (Atom ⊕ Atom)` type, so the generic primeness engine's schema hypotheses become
  dischargeable at genuinely mixed formulas such as `(atom (inl p)).or (atom (inr q))`. Keep the
  **modal** schemata pure-tagged, so the only place left/right content mixes modally remains the
  two designated `cross1`/`cross2` bridges.
- **Tasks:**
  - [x] In `CS5Completeness.lean`, add to the `CS5PairAxiom` inductive the nine propositional-core
    constructors, each quantified over arbitrary `Proposition (Atom ⊕ Atom)` (NOT routed through
    `τ_L`/`τ_R`): `implyK`, `implyS`, `efq`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE` —
    mirroring `CS5ModalAxiom`'s corresponding constructors (`CS5.lean:170-195`) but at the
    combined type. Reuse `Cslib.Logic.Axioms.{AndI, AndE1, AndE2, OrI1, OrI2, OrE}` formers, as
    `CS5ModalAxiom` does.
  - [x] Leave `left`/`right`/`cross1`/`cross2` unchanged; do NOT add any modal schema at mixed
    formulas.
  - [x] Update the `CS5PairAxiom` docstring to record the two-tier design (propositional core at
    the whole type, modal schemata pure-tagged plus the two bridges) and *why* the whole-type
    quantification is forced (the generic engine's `hOrE`/`hEFQ`/`hCut` hypotheses range over the
    ambient formula type — `PrimeExclusion.lean:229,237,346-351,435-448`).
  - [x] Re-verify the four landed Phase-3 lemmas still compile unchanged:
    `cs5PairAxiom_left_derivable`, `cs5PairAxiom_right_derivable`, `crossCond_left_stable`,
    `crossCond_right_stable`.
- **Timing:** 2 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Verification:**
  - `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness` green, no errors.
  - All four landed lemmas compile without edits (R-A discharged).
  - `grep -n '\bsorry\b\|\badmit\b' ` over the file returns docstring prose only — **zero** tactic
    or term `sorry`.
  - `lake exe lint-style` clean on the modified file.

### Phase 2: Discharge the Primeness-Engine Preconditions at `CS5PairAxiom` [NOT STARTED]

- **Goal:** Land, as named reusable library lemmas, the hypothesis bundle that
  `prime_exclusion`/`prime_set_exclusion` require at `CS5PairAxiom`. This is the payoff of
  Phase 1 and is useful under either eventual route: it makes the generic engine applicable to the
  combined system at all.
- **Tasks:**
  - [ ] Prove `cs5Pair_hImplyK`, `cs5Pair_hImplyS` (needed by `deductionTheorem`,
    `PrimeTheory.lean`), `cs5Pair_hEFQ`, `cs5Pair_hOrI1`, `cs5Pair_hOrI2`, `cs5Pair_hOrE` — each
    a one-line `.ax`/constructor application given Phase 1's new constructors, at arbitrary
    `Proposition (Atom ⊕ Atom)`.
  - [ ] Supply `cs5Pair_hCut` by instantiating the existing generic supplier
    `modal_deriv_imp_of_union` (`PrimeTheory.lean`; `SegmentLindenbaum.lean:286-288` confirms it
    already has the singleton `S ∪ {a}` shape `prime_set_exclusion` expects, so **no new cut
    machinery is needed** — only instantiation) at `Axioms := CS5PairAxiom` with
    `cs5Pair_hImplyK`/`cs5Pair_hImplyS`.
  - [ ] Add a section docstring stating that these lemmas make the generic engine applicable, and
    that the one precondition they do **not** supply is `DerivExcludes` at the two-sided seed
    (forward-referencing Phase 7's named obligation).
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Verification:**
  - Every hypothesis lemma compiles sorry-free; scoped `lake build` green.
  - Sanity check: the full hypothesis bundle type-checks when passed positionally to
    `prime_set_exclusion` in a `#check`-level elaboration (the remaining hole is `DerivExcludes`
    and nothing else). Record the resulting goal in the phase notes.
  - Zero sorry/admit in the file.

### Phase 3: The Two-Sided Seed `cs5PairSeed` [NOT STARTED]

- **Goal:** Define, once and canonically, the two-sided seed that every downstream exclusion
  statement refers to, plus its basic membership lemmas. Small phase by design: Phases 4-6 and
  Phase 7 all depend on this definition being fixed, and Phase 7 must be able to proceed even if
  Phase 4 blocks.
- **Tasks:**
  - [ ] Define
    `cs5PairSeed (H : Set (Proposition Atom)) : Set (Proposition (Atom ⊕ Atom)) :=
    cs5PairTauL '' H ∪ cs5PairTauR '' (modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H))`,
    using `boxInv` from `Segment.lean:103` and `modalDeductiveClosure` from `PrimeTheory.lean:78`.
  - [ ] Prove the two injection lemmas: `φ ∈ H → cs5PairTauL φ ∈ cs5PairSeed H` and
    `φ ∈ modalDeductiveClosure CS5ModalAxiom (boxInv H) → cs5PairTauR φ ∈ cs5PairSeed H`.
  - [ ] Prove the membership-inversion lemma: every element of `cs5PairSeed H` is either
    `τ_L φ` with `φ ∈ H` or `τ_R ψ` with `ψ ∈ cl_{CS5}(boxInv H)` — the case-split Phases 4-6
    induct against. Use `Proposition.map_injective` (`Basic.lean:199`) to rule out tag collision.
  - [ ] Docstring the seed's role and its two components' provenance.
- **Timing:** 1.5 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Verification:**
  - Definition and three lemmas compile sorry-free; scoped `lake build` green.
  - Zero sorry/admit in the file.

### Phase 4: Cross-Inertness Support Lemma (Hard Gate) [NOT STARTED]

- **Goal:** Land the single support lemma both individual exclusions rest on: from the seed
  `cs5PairSeed H`, the cross-axioms `cross1`/`cross2` contribute nothing new, because their
  antecedents are boxed and `□` is introduced only by necessitation from the empty context
  (report 02 §2). Formally: any `CS5PairAxiom`-derivation from a context drawn from
  `cs5PairSeed H` whose conclusion is a pure-tagged formula factors through the corresponding
  single-copy `CS5ModalAxiom`-derivation.
- **Tasks:**
  - [ ] State the lemma precisely — the necessitation-only-from-`[]` invariant for `□` in
    `modalDerivationSystem`, plus the consequence that a `cross1`/`cross2` instance can only fire
    on a `CS5PairAxiom`-*theorem* antecedent, never on seed content.
  - [ ] Prove it by induction on the `DerivationTree` (`DerivationTree.lean`), tracking the
    side + boxed-ness invariant; reuse `Derivable.map` where the pure-tagged sub-derivations
    transport.
  - [ ] Record in the docstring exactly which facts about `cs5PairSeed` the argument consumes,
    so Phases 5-6 cite the lemma rather than re-deriving it.
- **Timing:** 2.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Verification:**
  - Lemma compiles sorry-free; scoped `lake build` green; zero sorry/admit.
  - **Gate (R-B):** if the lemma cannot be closed, mark this phase **[BLOCKED]**, record what was
    tried and the exact goal state reached, **skip Phases 5 and 6**, and proceed directly to
    Phase 7 (which does not depend on this phase) and then Phase 8. Do NOT insert a `sorry`, do
    NOT weaken the statement to something vacuous, and do NOT retry either dead end listed under
    Non-Goals.

### Phase 5: Individual Exclusion `τ_R A ∉ cl(cs5PairSeed H)` [NOT STARTED]

- **Goal:** Prove the first of the two individual seed exclusions: given deductively closed
  quasi-prime `H` with `□A ∉ H`, the right-tagged `τ_R A` is not in the `CS5PairAxiom`-closure of
  the seed.
- **Tasks:**
  - [ ] Reduce, via Phase 4's cross-inertness lemma and Phase 3's membership-inversion lemma, to
    the two single-copy facts: (a) `A ∉ modalDeductiveClosure CS5ModalAxiom (boxInv H)` — because
    for a normal modal logic with deductively closed `H`, `boxInv H ⊢ A` implies `□A ∈ H` by
    K-distribution over the boxed context, contradicting `□A ∉ H`; (b) `A` is not a `CS5` theorem
    — else `□A` is a theorem by necessitation, so `□A ∈ H`, same contradiction.
  - [ ] Prove (a) and (b) as named auxiliary lemmas, then compose.
  - [ ] Docstring the reduction, citing `cs5_boxInv_subset_iff` (`CS5.lean:575`) and the `T`-box
    fact `boxInv H ⊆ H` (`CS5.lean:599`) where used.
- **Timing:** 2 hours
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Verification:**
  - Exclusion lemma and both auxiliaries compile sorry-free; scoped `lake build` green.
  - Zero sorry/admit in the file.

### Phase 6: Individual Exclusion `τ_L (□A) ∉ cl(cs5PairSeed H)` [NOT STARTED]

- **Goal:** Prove the second individual seed exclusion, the left-tagged `□A`.
- **Tasks:**
  - [ ] Reduce, via Phase 4's cross-inertness lemma and Phase 3's membership-inversion lemma, to
    `□A ∉ modalDeductiveClosure CS5ModalAxiom H`, which is immediate from `H` deductively closed
    plus the hypothesis `□A ∉ H`.
  - [ ] Handle the right-component contribution: show the `τ_R`-side seed content cannot yield a
    left-tagged conclusion except through the cross-axioms, already neutralised by Phase 4.
  - [ ] Docstring the reduction.
- **Timing:** 2 hours
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Verification:**
  - Exclusion lemma compiles sorry-free; scoped `lake build` green.
  - Zero sorry/admit in the file.

### Phase 7: Formally Isolate the Research-Grade Obligation as a Named Open Lemma [NOT STARTED]

- **Goal:** State the one remaining obligation precisely, as a **named `Prop`-valued definition**
  with a docstring recording its provenance and status — **never** as a `sorry`, never as a
  claimed theorem, never as a vacuous placeholder — so the build stays sorry-free and honest and
  the open frontier is exactly one named object a reader can find and a future proof can target.
- **Tasks:**
  - [ ] Define the named open obligation, e.g.

    ```lean
    /-- **OPEN OBLIGATION (unproven, deliberately not a theorem).**  The constructive
    disjunction property of `CS5PairAxiom` under the `boxInv` cross-constraint, at the
    two-sided seed: for deductively closed quasi-prime `H` with `□A ∉ H`,

        τ_L (□A) ⊔ τ_R A ∉ cl_{CS5PairAxiom} (cs5PairSeed H).

    At the *seed* the theory is **not** prime, so "neither disjunct is derivable" does not
    give "the disjunction is not derivable" — constructively the disjunction is strictly
    weaker.  Both individual exclusions ARE proved (`…`, `…` above); only the
    disjunction-level negative is open.

    **Provenance.**  This is [Pacheco2024]'s Lemma 16.  Its published proof is **unsound**
    in this setting: it uses the negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, which is
    invalid for a poset-maximal quasi-prime theory.  The identical obligation defeated the
    earlier `CS5Combined` atom-sum scaffold (`cs5Combined_seed_excludes`, never closed, since
    removed — see `CS5Canonical.lean`'s module docstring).

    **No semantic witness exists.**  `CS5PairAxiom`'s cross-axioms are sound only under a
    *common* valuation for both copies, which identifies `τ_L X` with `τ_R X` and collapses
    `cross1` to `□B → B`; in every such model `τ_R A` is forced whenever `A ∈ H`.  So no
    sound model separates the seed from the excluded set, and a soundness/countermodel
    argument cannot discharge this — it is a purely syntactic separation fact.

    **Status.**  Open here.  A correct proof is expected to require a cut-free/nested-sequent
    argument ([Marin2021]) rather than a direct Hilbert derivation.  Stated as a definition,
    not asserted: this module contains no `sorry`. -/
    def CS5PairSeedDisjunctionProperty
        (H : Set (Proposition Atom)) (A : Proposition Atom) : Prop := …
    ```

    The definition must have **real content** (the actual non-membership statement) — the
    `def X := True` / `:= Unit` / `:= trivial` family is prohibited by `.claude/rules/lean4.md`
    and is semantically equivalent to `sorry`.
  - [ ] Prove the **conditional** reduction theorem, sorry-free, consuming the open obligation as
    an **explicit hypothesis**:

    `theorem cs5Pair_derivExcludes_of_disjunctionProperty … (hL : τ_L (□A) ∉ cl …) (hR : τ_R A ∉ cl …) (hOpen : CS5PairSeedDisjunctionProperty H A) : DerivExcludes (modalDerivationSystem (@CS5PairAxiom Atom)) {cs5PairTauL (Proposition.box A), cs5PairTauR A} (modalDeductiveClosure CS5PairAxiom (cs5PairSeed H))`

    proved by case analysis on the `List` argument of `DerivExcludes`
    (`PrimeExclusion.lean:332`): the `[]` case is `bigOr [] = ⊥` (consistency of the closure);
    the singleton cases are `hL`/`hR`; the two-element and longer cases reduce to `hOpen` via
    `bigOr`-monotonicity (`or_right_mono`, `bigOr_append_left`, `bigOr_append_right`,
    `PrimeExclusion.lean:329-390`) using Phase 2's `cs5Pair_hOrI1`/`hOrI2`/`hOrE`/`hEFQ`/`hCut`.
  - [ ] **If Phase 4 blocked** (so `hL`/`hR` are not available as theorems): state the conditional
    theorem with `hL` and `hR` as explicit hypotheses too, and document in the docstring that all
    three are open pending Phases 5-6 and the spawned subtask. The theorem itself remains
    sorry-free either way.
  - [ ] Add a module-level `## Open Obligations` section listing exactly what is open, what is
    proved, and what a discharge would unlock (the `prime_set_exclusion` application, then the
    projection to the pair `⟨H', T⟩`, then box-backward, then a native `cs5_completeness''`).
- **Timing:** 2.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Verification:**
  - The definition elaborates and the conditional theorem compiles **sorry-free**; scoped
    `lake build` green.
  - `grep` confirms **zero** tactic/term `sorry` or `admit` in the file.
  - The named definition is not `True`, `Unit`, `trivial`, or any vacuous form (R-C).
  - `#print axioms` on the conditional theorem shows no `sorryAx`.
  - No task-number citations appear in any new docstring (R-F).

### Phase 8: Documentation, Frontier Record, and CI Gate [NOT STARTED]

- **Goal:** Leave the module honest and navigable for the next reader — whichever route is later
  chosen — and run the CSLib CI pipeline once.
- **Tasks:**
  - [ ] Update `CS5Completeness.lean`'s module docstring: what is landed here, the single named
    open obligation, the two ruled-out dead ends (semantic seed-exclusion — circular and with no
    separating model; `Sum.elim id id` retraction — not schema-compatible, `cross1`'s image
    `□B → B` is not a `CS5ModalAxiom` instance) with the reason each is closed off, and an
    explicit statement that a native `cs5_completeness''` is **not** provided by this module.
  - [ ] Record the deferred route decision in the docstring at a durable-anchor level: the IS5
    collapse route remains available via `is5_completeness` (`IS5.lean:364`) and the landed
    collapse axioms `cs5_dia_or`/`cs5_dia_bot_imp_bot` (`CS5.lean:539,712`), gated on the
    currently-unproven `CS5 ⊢ idb` (`idb` is absent from every `Constructive/CS5*` file). Frame
    this as a documented alternative, not as a commitment.
  - [ ] Verify no docstring anywhere in the modified files cites a task number
    (`.claude/rules/no-task-references-in-deliverables.md`); cite `[Pacheco2024]`, `[Marin2021]`,
    and file/declaration anchors instead.
  - [ ] Run the CSLib CI pipeline in order: `lake build`; `lake exe checkInitImports`; `lake lint`;
    `lake exe lint-style`; `lake test`. No new file is added by this plan, so `mk_all` is not
    required — confirm that.
  - [ ] Final zero-debt census: `grep -rn '\bsorry\b\|\badmit\b\|\bsorryAx\b'` over the four scope
    files + `CS5Completeness.lean`; every hit must be docstring prose.
- **Timing:** 1.5 hours
- **Depends on:** 2, 5, 6, 7
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`
- **Verification:**
  - Full `lake build` green (no regression in the CK/CT/CS4 column or existing CS5 assets). A
    transient breakage caused by unrelated concurrent edits is **reported**, not worked around
    (R-G).
  - `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test` all pass on the
    modified file.
  - Sorry/admit census: **zero** tactic/term occurrences.
  - No task-number citations in `Cslib/`.

## Testing & Validation

- [ ] Every phase: scoped `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness`
      green before the phase is declared complete, and committed per the commit-per-green-substep
      mandate.
- [ ] Every phase: sorry/admit census over the scope files returns docstring prose only —
      **zero** tactic or term occurrences. This is a hard gate, not a preference.
- [ ] Phase 1: all four previously-landed Phase-3 lemmas compile unchanged after the inductive is
      extended.
- [ ] Phase 2: the full hypothesis bundle type-checks against `prime_set_exclusion`, leaving
      `DerivExcludes` as the sole remaining hole.
- [ ] Phase 4 gate: cross-inertness closes, or the phase is marked [BLOCKED] and Phases 5-6 are
      skipped while Phases 7-8 still run.
- [ ] Phase 7: `#print axioms` on the conditional `DerivExcludes` theorem shows no `sorryAx`; the
      named open definition is non-vacuous.
- [ ] Phase 8: full `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`,
      `lake test` all pass.
- [ ] Phase 8: no docstring in `Cslib/` cites a task number.

## Artifacts & Outputs

- `specs/551_cs5_native_hilbert_pair_lindenbaum_completeness/plans/02_incremental-assets-deferred-route.md`
  (this plan)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` — extended `CS5PairAxiom`
  (propositional core), the primeness-engine hypothesis bundle, `cs5PairSeed` and its membership
  lemmas, the cross-inertness support lemma, the two individual seed exclusions, the named open
  obligation `CS5PairSeedDisjunctionProperty`, and the conditional `DerivExcludes` theorem
- `specs/551_cs5_native_hilbert_pair_lindenbaum_completeness/summaries/02_incremental-assets-summary.md`
  (on completion) — must record which phases landed, whether Phase 4 gated, and the exact
  statement of the remaining open obligation
- A spawned research subtask (see Spawned above) carrying the open obligation

**Not produced by this plan** (restating, because the prior plan promised them):
`cs5_completeness''`, `cs5_box_backward`, `cs5_box_backward_onesided`,
`cs5_soundness_completeness''`, `cs5_derives_idb`, `cs5_iff_is5_derivable`,
`cs5FC_iff_is5FC_valid`, the `cs5FCIncest` variant.

## Rollback/Contingency

- Every phase commits its own green sub-step; a failed phase leaves prior phases intact and the
  build green. Prior commits are the rollback points.
- **Phase 4 gate failure (R-B):** mark [BLOCKED] with what was tried and the goal state reached;
  skip Phases 5-6; run Phases 7 and 8 anyway. The headline deliverable (a documented, sorry-free,
  precisely-named open frontier) does not depend on Phase 4.
- **Phase 7 is the floor.** If everything else blocks, the task must still leave behind the named
  open obligation and the module docstring recording the frontier and the deferred route
  decision. A task outcome with the frontier undocumented is worse than one with no new lemmas.
- Per `.claude/rules/plan-compliance.md`, any `.lean` step that cannot be executed as written is
  raised as a [BLOCKED] escalation — never silently substituted, never papered over with `sorry`
  or a vacuous definition (`.claude/rules/lean4.md`).
- Full revert: all edits are confined to `CS5Completeness.lean`. `git revert` of the phase commits
  restores the pre-revision state without touching the CK/CT/CS4 column, `CS5.lean`,
  `CS5Canonical.lean`, or `DerivationTree.lean`.
