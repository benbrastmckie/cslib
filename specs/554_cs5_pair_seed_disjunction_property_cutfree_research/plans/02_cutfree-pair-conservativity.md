# Implementation Plan: Task #554 (Round 2)

- **Task**: 554 - CS5 pair-seed obligation: cut-free route to two-label conservativity
- **Status**: [IMPLEMENTING]
- **Effort**: 86 hours (Stage A 9.5, B 7.5, C 5.5, D 8, E 5, F 28, G 22; the Stage F and G
  estimates carry wide error bars)
- **Dependencies**: None
- **Research Inputs**:
  - `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/reports/01_pair-seed-disjunction-collapse.md`
  - `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/reports/02_cutfree-literature-grounded.md` (supersedes 01 where they differ)
- **Artifacts**: plans/02_cutfree-pair-conservativity.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md, plan-compliance.md, no-task-references-in-deliverables.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The pair-seed obligation in `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` is
the last open sub-problem of the native-Hilbert `CS5` completeness route. Round 2 established,
machine-checked, that the obligation as literally stated is **false for every `H`**, and that once
repaired it is a **two-label, mixed-signature conservativity statement about Hilbert
derivability**. This plan repairs the statement first, then builds the only instrument that can
discharge the repaired statement: a cut-free nested-sequent system, following Arisaka–Das–
Straßburger, first for single-signature `CS5` and then extended to the two-label `CS5Pair`
signature.

**Definition of done**: `CS5PairSeedRightExclusion H A` is a sorry-free theorem, the caller-side
side condition is discharged from `□A ∉ H`, `Metalogic.prime_set_exclusion` is instantiated at
`CS5PairAxiom`, and the repo-wide bare-`sorry` count in `Cslib/` is still exactly 5.

### Route Recommendation (explicit, as required)

**Primary route: cut-free nested sequents (Stages B–G). The product-model-over-`IS5` route is
not adopted, and not because it is cheaper — because it is not viable.**

Round 2 §5 proposed a product model over `IS5` with two residuals, R-a (the base `is5FC` model's
accessibility must be total) and R-b (`H` `CS5`-closed, `□A ∉ H` ⟹ `□A ∉ cl_IS5(H)`), and flagged
R-b as "adjacent to the forbidden collapse route". Plan-time analysis sharpens *adjacent* to
*identical*:

> Instantiate R-b at `H := cl_CS5(∅)`. It then reads `CS5 ⊬ □A ⟹ IS5 ⊬ □A`. In both systems
> necessitation gives `⊢ A ⟹ ⊢ □A` and `tBox` gives `⊢ □A ⟹ ⊢ A`, so `⊢ □A` and `⊢ A` are
> interderivable in each. Contraposing therefore yields `IS5 ⊢ A ⟹ CS5 ⊢ A`, i.e. `IS5 ⊆ CS5`.
> Composed with the landed `cs5_closure_subset_is5_closure` direction this is exactly the
> `CS5 = IS5` collapse.

So R-b is not a residual gap of the product-model route — it *is* the collapse route, whose only
published basis is Pacheco's Lemma 16/18, the same unsound argument this task exists to repair,
and whose adoption the mandate reserves for explicit user authorisation. Phase 5 machine-checks
this reduction so the closure is a theorem in the repository, not a plan-time assertion. R-a is
independently unverified and belongs to the frame-condition family that already produced
`cs5Incest` being "mechanically false on every world type tried" in `CS5Canonical.lean`; it is not
separately probed because R-b already closes the route.

The cut-free route additionally **dominates**: it is the prerequisite for the collapse route too
(Arisaka–Das–Straßburger's derivations of `k3`/`k5` from `b` are *nested-sequent* derivations, so
transferring them to Hilbert derivability requires their soundness theorem anyway, and the status
of `k4` in `CS5` is unsettled without it), and a cut-free proof system for `CS5` is a library-grade
asset well beyond this one lemma.

### The Central Gap, Stated Head-On

**Cut-elimination for single-signature `CS5` does not close the obligation.** Arisaka–Das–
Straßburger's Theorem 5.2 covers `HCK + t + 4 + b` — CSLib's exact `CS5ModalAxiom` set, as the
safe pair `X = {t,4}`, `Y = {b}` — but over **one** signature. The obligation is about
`CS5PairAxiom`: `CS5` on two tagged copies of `Atom ⊕ Atom`, **plus** the two signature-mixing
cross schemas `□(τ_L B) → τ_R B` and `□(τ_R B) → τ_L B`, **plus** a propositional core quantified
over the whole `Proposition (Atom ⊕ Atom)` type including genuinely mixed formulas. Nothing in the
paper covers this.

The bridge (Stage G) is therefore required, and **it is the larger risk of the two**. Stages B–F
transcribe an 18-page published argument: long, but the argument exists and is known correct.
Stage G is unpublished mathematics. Its crux is Phase 28: Arisaka–Das–Straßburger's cut-elimination
is parametric over *structural* rules that manipulate only the nested tree, whereas the cross rules
move a formula between tag-copies — a formula-level operation their safe-pair scheme does not
cover. If Phase 28 fails, Stages B–F still stand as a complete, independently valuable deliverable,
and the task is marked `[BLOCKED]` with a precise diagnosis (see Rollback/Contingency).

### Research Integration

Established facts taken as given (machine-checked in round 2; not re-derived and not contradicted
anywhere in this plan):

- `CS5PairSeedDisjunctionProperty` (`CS5Completeness.lean:373`) is **false as literally stated**
  for every `H`. Minimal witness `A := ⊥ → ⊥`. The statement must gain a hypothesis relating `A`
  to `H`; the correct one is `A ∉ modalDeductiveClosure CS5ModalAxiom (boxInv H)` (round 2 §1.1
  candidate (i)). Phase 1 is a prerequisite for everything else.
- Round 1's reduction survives the repair: the obligation is equivalent to the single right
  exclusion `τ_R A ∉ cl(seed)`, and `hL` follows from it (round 1 R2–R4).
- Non-Goal 2's stated rationale is refuted: `Sum.elim id id` *is* schema-compatible, both cross
  axioms landing on `CS5ModalAxiom.tBox`. The Non-Goal's conclusion stands; only its reason was
  wrong (round 1 R5).
- Arisaka–Das–Straßburger covers CSLib's exact `CS5` axiom set (safe pair `X={t,4}`, `Y={b}`;
  Theorems 5.2, 6.3). Their Kripke-semantics disclaimer does not undercut this: their
  soundness/completeness is Hilbert-relative, which is precisely the currency the obligation
  needs. It is also the reason cut-elimination must be done **syntactically** here — there is no
  standard Kripke semantics for the constructive cube to run a semantic cut-admissibility argument
  against.
- Marin–Morales–Straßburger does **not** apply: `labIK≤`'s base is `IK`, not `CK` (it derives
  `k3`, `k4`, `k5`), so it settles `IS5`, not `CS5`.
- Arisaka–Das–Straßburger §4.3 (`b ⊢ k3, k5`) does **not** bear on the obstruction. `k3` is
  *diamond* over disjunction; the obstruction `□(A∨B) → (□A ∨ □B)` is not a theorem of even
  classical `S5`. No phase of this plan attempts it, and no phase depends on it.

Round-2 probes reused as regression material: `probes/seed_refutation.lean` (Phase 1),
`probes/cs5_subset_is5.lean` (Phase 5). Round-1 probes reused: `probes/cross1_collapse.lean`
(Phase 2), `probes/retraction_bound.lean` (Phase 4).

Precise source structure used for phase design (Arisaka–Das–Straßburger, `doc_id:
arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`, read via
`literature-search.sh --include-unverified`):

- **§2, eq. (2.1)**: `Φ ::= ∅ | A• | [Φ] | Φ, Φ` (LHS), `Ψ ::= A◦ | [Φ, Ψ]` (RHS); a full sequent
  is `Φ, Ψ`, containing exactly one output formula. `fm` translation as given there.
- **Observation 2.2**: every *output* context has the shape `Γ•₁, [Γ•₂, [… , [Γ•ₙ, { }] …]]`;
  every *input* context has the shape `Γ'{Λ{ }, Π◦}` with `Γ'{ }`, `Λ{ }` output contexts, all
  uniquely determined. This is used as the **definitional encoding** in Phase 7, not as a proved
  lemma — encoding output contexts as a `List` of LHS layers makes Observation 2.2 hold by
  construction and removes the zipper-style well-formedness burden.
- **Definition 2.3**: output pruning `Γ⇓{ } := Γ'{Λ{ }}`.
- **Theorem 5.2** side conditions and the covered-logic list (which names `CS5` explicitly).
- **§6**: super-rules `s4•/s4◦/s4□/s4♦/sb[]`; Proposition 6.4 (super-rules and base rules are
  mutually derivable); Lemma 6.5 (`s4•`/`s4◦` permute over any `r ∈ Ys[]`); eq. (6.2) auxiliary
  cuts `♦cut`/`□cut` with Fact 6.6; the `∗cut` convention (output cut formula in the left premise).

**In-repo precedent that shapes the Lean architecture** (a materially better starting position
than round 2's cost table assumed): `Cslib/Logics/Propositional/SequentCalculus/LJ/` already
contains a complete, sorry-free cut-elimination (`CutElimination.lean`, 711 lines) and subformula
property (`SubformulaProperty.lean`, 285 lines) for single-succedent LJ, with exactly the
decomposition Stage F needs — a `height` measure, a `CutFree` predicate, a `.mono` weakening
transport, separate principal-case lemmas for `andR/andL`, `orR/orL`, `impR/impL`, then left-side
and right-side structural recursions, then the Hauptsatz. It is over
`Cslib.Logic.PL.Proposition` (no modalities), so it is not a reusable *component*, but it is a
proven in-repo **template** of the right shape and size, and Phases 21–23 mirror its structure
deliberately.

### Prior Plan Reference

No prior plan exists for this task (`plans/` was empty). Round 1's §4.1 and round 2's §8.1
"land now" recommendations are folded into Stage A.

### Roadmap Alignment

No `roadmap_path` was supplied in this delegation context and no roadmap phases are included.

### What the Second Consumer Gains

The labelled `CS5` general-soundness task asked: *is a context-fold that splits compound context
facts derivable without the box-over-disjunction bridge?*

**No — and not "not yet", but never.** The missing bridge `□(A∨B) → (□A ∨ □B)` fails in classical
`S5` (two-world universal frame, `A` at one world, `B` at the other). It is therefore not a
constructive-versus-intuitionistic gap, and no strengthening of the base logic — `k3`, `k4`, `k5`,
the `IS5` collapse, or any intuitionistic Scott–Lemmon axiom — supplies it. Splitting the fold
also *relocates* rather than discharges the obligation: `Θ` sits in the antecedent, so a split
`□P₀ ∨ □P₁` is a strictly stronger hypothesis than the flat `□(P₀ ∨ P₁)`, pushing the same
non-theorem onto the caller. The `sigAt` freeze (`Labelled/Soundness.lean:1414`) is not the binding
constraint.

**What that consumer does gain from this plan** is the removal of the fold, not its repair. The
fold exists only to reduce a multi-label derivation to a single unlabelled `CS5` formula. In the
nested setting the analogous device is `fm` (Phase 6) together with the context-compositionality
lemmas (Phase 8) and the soundness auxiliaries (Phase 11): adequacy is stated **node-wise against
a context**, so no multi-node context is ever folded into one boxed `CS5` formula and the bridge
is never needed. Phases 6, 8, and 11 are the directly reusable deliverables for that consumer;
they land at Waves 1, 3, and 5 respectively — i.e. well before the high-risk Stage G — so that
consumer's payoff does not depend on Stage G succeeding.

## Goals & Non-Goals

**Goals**:

- Correct the refutable obligation statement and land the refutation as a permanent regression, so
  the unconditioned form can never be reintroduced.
- Collapse the module's three open obligations plus one blocked lemma to a single named obligation,
  with the caller-side side condition discharged rather than pushed onto the caller.
- Close the product-model route with a machine-checked reduction to `CS5 = IS5`.
- Formalise a cut-free nested-sequent system for `CS5` (`HCK + t + 4 + b`), sorry-free, with
  soundness, completeness, cut elimination, cut-free completeness, and the subformula property.
- Extend it to the two-label mixed-signature `CS5Pair` system and discharge
  `CS5PairSeedRightExclusion`.
- Instantiate `Metalogic.prime_set_exclusion` at `CS5PairAxiom`, delivering the box-backward pair
  the native `cs5_completeness''` route needs.

**Non-Goals**:

- **No `sorry`, no `axiom`, no vacuous definition, no weakened or restated obligation.** The
  repo-wide bare-`sorry` count in `Cslib/` is exactly 5 (`TemporalConservativity.lean:269`,
  `Tableau/Minimal/Completeness.lean:125`, `Tableau/Intuitionistic/Completeness.lean:133`,
  `Tableau/Intuitionistic/Scheme.lean:592` and `:1498`) and must stay there.
- **Not adopting the `CS5 = IS5` collapse route.** Phase 5 shows the product-model route requires
  it; adopting either remains a mandate change requiring explicit user authorisation.
- **No phase attempts `□(A∨B) → (□A ∨ □B)`** or any route requiring it.
- Not formalising Marin–Morales–Straßburger's `labIK≤` (wrong base logic).
- Not repairing `sigAt`'s context-fold in `Labelled/Soundness.lean`, and not modifying that file.
- Not attempting the full constructive cube — only the safe pair `X = {t,4}`, `Y = {b}` needed for
  `CS5`. The rule sets are defined so a later cube generalisation is additive, not a rewrite.
- Not creating a PR or pushing (see `.claude/rules/pr-prohibition.md`).

**Flagged: does any phase weaken or restate a landed theorem?**

One item, disclosed rather than hidden. `cs5Pair_derivExcludes_of_disjunctionProperty`
(`CS5Completeness.lean:415`) is landed, true, and sorry-free, but its hypotheses `hL`/`hR` are
jointly unsatisfiable at `CS5`-provable `A` (round 2 §1), so it is unusable at those instances.
**It is left textually unchanged.** Phase 2 adds a *new* entry point
`cs5Pair_derivExcludes_of_rightExclusion` which carries an extra side condition
`hA : A ∉ cl_CS5(boxInv H)` that the old theorem did not have. Taken in isolation that is a
weaker statement, so it is flagged here. It is not a net weakening in practice: Phase 3 discharges
`hA` from the caller's actual hypothesis `□A ∉ H` whenever `H` is `CS5`-deductively closed, which
the caller always is. No other phase restates, weakens, or deletes a landed theorem.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Phase 28 (cross-rule permutation in the cut-elimination induction) fails — the cross rules are formula-level, outside Arisaka–Das–Straßburger's structural safe-pair scheme | H | M | Design the cross rules in Phase 26 using the axioms-as-rules technique (Negri), which is the standard way to preserve cut-elimination when adding axioms; CSLib precedent exists in `SeqProof`'s `Theory`-parameterisation. If it still fails, Stages B–F stand alone; mark `[BLOCKED]` with the exact failing permutation case rather than weakening the target |
| Cut-elimination (Phases 21–23) is a long, delicate transcription with wide effort error bars | H | H | Mirror `LJ/CutElimination.lean`'s proven decomposition (principal cases as separate lemmas, then two structural recursions, then assembly); every phase ends at a green committable checkpoint; Phase 24 is a standalone milestone even if Stage G never starts |
| Nested-sequent well-formedness ("exactly one output formula") makes the Lean encoding fight the elaborator | M | M | Encode LHS and RHS sequents as separate mutual inductives per eq. (2.1) rather than as one type with a well-formedness predicate; encode output contexts in Observation 2.2 normal form so context well-formedness is definitional |
| Literature chunks are marked `unverified_summary` and may garble rule figures | M | M | Recovered source PDFs are available under `~/Projects/Literature/.sources-recovered/`; every phase that transcribes a rule figure must check the figure against the PDF before writing, per `lean4.md` Literature Fidelity |
| Phase 30's seed-relative bridge (infinite `cl(seed)` vs finite nested contexts) is under-specified in the sources | M | M | The `Deriv` system is already finitary (`Deriv Axioms L φ` with `L : List`), so the bridge is a compactness-style restatement over the existing finite-list derivability, not new analysis; probe it at the start of Phase 30 before committing to the encoding |
| Effort overruns the orchestrator's dispatch budget | M | H | 32 phases, each independently green and committable; stage boundaries (after Phases 5, 15, 24, 25) are natural split points for follow-up tasks |
| Docstring corrections reintroduce task-number citations in `Cslib/` | L | M | Phase 4 explicitly replaces existing `specs/NNN_.../probes/...` citations with durable anchors, per `.claude/rules/no-task-references-in-deliverables.md` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 5, 6 | -- |
| 2 | 2, 3, 4, 7 | 1, 6 |
| 3 | 8, 9 | 7 |
| 4 | 10 | 9 |
| 5 | 11, 14, 16, 19 | 8, 10 |
| 6 | 12, 17, 18 | 11, 16 |
| 7 | 13, 20 | 12, 18 |
| 8 | 15, 21 | 13, 14, 19, 20 |
| 9 | 22 | 17, 21 |
| 10 | 23 | 22 |
| 11 | 24 | 15, 23 |
| 12 | 25, 26 | 13, 24 |
| 13 | 27 | 15, 26 |
| 14 | 28 | 23, 27 |
| 15 | 29 | 28 |
| 16 | 30 | 29 |
| 17 | 31 | 25, 30 |
| 18 | 32 | 2, 3, 31 |

Phases within the same wave can execute in parallel.

---

## Stage A — Statement Repair and Route Closure

### Phase 1: Correct the obligation statement and land the refutation [COMPLETED]

**Goal**: Replace the refutable obligation with the corrected one and make the refutation a
permanent regression theorem.

**Tasks**:
- [x] Add `CS5PairSeedRightExclusion (H : Set (Proposition Atom)) (A : Proposition Atom) : Prop :=
      A ∉ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H) →
        cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)`
- [x] Promote `probes/seed_refutation.lean`'s `probe_refute_disjunctionProperty` as
      `cs5PairSeedDisjunctionProperty_false : ∀ H, ¬ CS5PairSeedDisjunctionProperty H
      (Proposition.bot.imp Proposition.bot)`, with a docstring stating the mechanism (every `CS5`
      theorem lies in `modalDeductiveClosure CS5ModalAxiom S` for every `S`, so `τ_R A` is
      literally in `cs5PairSeed H`)
- [x] Promote `probe_refute_hR_of_boxMem` as the `H`-driven companion refutation *(landed as
      `cs5PairSeed_tauR_mem_closure_of_boxMem` plus a disjunction-property corollary
      `cs5PairSeedDisjunctionProperty_false_of_boxMem`, mirroring the ⊤-witness refutation's
      structure but seeded from `□A ∈ H` instead of `A` being a theorem)*
- [x] Mark `CS5PairSeedDisjunctionProperty` deprecated in its docstring, pointing at
      `CS5PairSeedRightExclusion`; leave the definition and
      `cs5Pair_derivExcludes_of_disjunctionProperty` textually unchanged
- [x] `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` — new definition, two
  refutation theorems, deprecation docstring

**Verification**:
- Module builds; `lean_verify` reports no `sorryAx` on both refutation theorems
- `CS5PairSeedDisjunctionProperty` and `cs5Pair_derivExcludes_of_disjunctionProperty` are
  byte-identical to their pre-phase form apart from the added docstring paragraph

---

### Phase 2: Reduction lemmas under the corrected statement [COMPLETED]

**Goal**: Collapse three open obligations plus one blocked lemma to the single corrected
obligation.

**Tasks**:
- [x] Land `cs5Pair_or_imp_right : Deriv CS5PairAxiom [] (((cs5PairTauL (Proposition.box A)).or
      (cs5PairTauR A)).imp (cs5PairTauR A))` from `probes/cross1_collapse.lean`, using
      `Proposition.map_box` definitional equality (`Modal/Basic.lean:164`) so that
      `cs5PairTauL (□A)` is literally the antecedent of `CS5PairAxiom.cross1 A`
- [x] Land the equivalence: right exclusion ↔ the disjunction form, at fixed `H`, `A`
      *(landed as the two directions `cs5Pair_disjunctionProperty_of_rightExclusion` and
      `cs5Pair_rightExclusion_of_disjunctionProperty`)*
- [x] Land `cs5Pair_leftExclusion_of_rightExclusion` (round 1 R3, via `modus_ponens` against
      `cross1`)
- [x] Land `cs5Pair_derivExcludes_of_rightExclusion (hA : A ∉ modalDeductiveClosure CS5ModalAxiom
      (boxInv H)) (hExcl : CS5PairSeedRightExclusion H A) : Metalogic.DerivExcludes …`, composing
      the above into the existing `cs5Pair_derivExcludes_of_disjunctionProperty`
- [x] Docstring: record that the new entry point carries the `hA` side condition the old one
      lacked, and forward-reference Phase 3's bridge as its discharge
- [x] `lake build` the module

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`

**Verification**:
- Module builds; all four new theorems sorry-free under `lean_verify`
- The new entry point discharges all three hypotheses of the landed
  `cs5Pair_derivExcludes_of_disjunctionProperty` from `hA` and `hExcl` alone

---

### Phase 3: Caller-side bridge from `□A ∉ H` to the side condition [NOT STARTED]

**Goal**: Discharge Phase 2's `hA` from the hypothesis the caller actually has, so the repair adds
no residual burden downstream.

**Tasks**:
- [ ] Land box-over-finite-conjunction in `CS5`: from `□B₁, …, □Bₙ ∈ H` infer
      `□(B₁ ∧ … ∧ Bₙ) ∈ H` for `H` `CS5`-deductively closed (necessitate `andI`, then `k` twice;
      induct on the list)
- [ ] Land `cs5_box_mem_of_mem_boxInv_closure : Metalogic.DeductivelyClosed
      (modalDerivationSystem (@CS5ModalAxiom Atom)) H → A ∈ modalDeductiveClosure CS5ModalAxiom
      (boxInv H) → Proposition.box A ∈ H` — the finite witness list lies in `boxInv H`, the
      conjunction of its boxes lies in `H` by the previous step, and necessitation plus `k`
      transports the derivation
- [ ] Land the contrapositive as the named caller-side discharge: `H` deductively closed and
      `□A ∉ H` gives `A ∉ modalDeductiveClosure CS5ModalAxiom (boxInv H)`
- [ ] Docstring: state explicitly that round 2 §1.1's counterexample shape (`□(B → A), □B ∈ H`
      with `□A ∉ H`) cannot occur once `H` is deductively closed, since `k` puts `□A ∈ H`
- [ ] `lake build` the module

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` (or `Constructive/Segment.lean`
  if the box/`boxInv` lemmas fit better beside `boxInv`; decide at implementation time and record
  the choice)

**Verification**:
- Module builds; all three results sorry-free
- Composing Phase 2's entry point with this bridge yields a `DerivExcludes` statement whose only
  remaining hypotheses are `H` deductively closed, `□A ∉ H`, and `CS5PairSeedRightExclusion H A`

---

### Phase 4: Retraction functoriality and docstring corrections [NOT STARTED]

**Goal**: Land the sharpest bound obtainable by relabeling, and correct two mis-argued docstring
claims.

**Tasks**:
- [ ] Land `cs5PairRetract`, `cs5PairRetract_schema_compatible` (`Sum.elim id id` maps every
      `CS5PairAxiom` constructor to a genuine `CS5ModalAxiom` instance, both cross axioms landing
      on `tBox`), and `cs5PairRetract_bound` from `probes/retraction_bound.lean`
- [ ] Correct Non-Goal 2's stated reason: the retraction *is* schema-compatible; the route fails
      because the bound it yields (`τ_R A ∈ Θ → A ∈ H`) is compatible with `□A ∉ H`, and because
      every relabeling retraction is forced to identify the two copies (the atom instance forces
      `⊢ □q → q'`, a theorem only when `q = q'`)
- [ ] Correct the "No semantic witness exists" claim to "any semantic witness is equivalent to the
      pair's joint satisfiability, hence circular", and record the product-model reading as a
      genuine candidate that Phase 5 closes
- [ ] Correct the "expected to require a cut-free/nested-sequent argument ([Marin2021])" pointer:
      `labIK≤`'s base is `IK`, not `CK`; the applicable cut-free system is Arisaka–Das–Straßburger
- [ ] Replace `specs/NNN_.../probes/...` citations in the module docstring with durable anchors
      (declaration names, section titles), per `.claude/rules/no-task-references-in-deliverables.md`
- [ ] `lake build` the module

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`

**Verification**:
- Module builds; the three retraction results sorry-free
- `grep -n "specs/" Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` returns nothing

---

### Phase 5: Close the product-model route (machine-checked) [NOT STARTED]

**Goal**: Turn the plan-time argument that the product-model residual R-b is the `CS5 = IS5`
collapse into a repository theorem, and land the `CS5 → IS5` transport lemmas.

**Tasks**:
- [ ] Land `cs5Axiom_to_is5Axiom`, `cs5_deriv_to_is5`, `cs5_closure_subset_is5_closure` from
      `probes/cs5_subset_is5.lean` (`CS5ModalAxiom`'s constructors are a literal subset of
      `IS5ModalAxiom`'s; `IS5ModalAxiom` adds `kdisj`, `kfs`, `kbot`)
- [ ] Land the route-closure theorem: from the hypothesis
      `∀ S A, Proposition.box A ∉ modalDeductiveClosure CS5ModalAxiom S →
        Proposition.box A ∉ modalDeductiveClosure IS5ModalAxiom S`
      derive `∀ φ, Derivable IS5ModalAxiom φ → Derivable CS5ModalAxiom φ`, using necessitation and
      `tBox` in both systems to interderive `⊢ A` and `⊢ □A`
- [ ] Corollary: that hypothesis together with `cs5_closure_subset_is5_closure` gives
      `Derivable IS5ModalAxiom φ ↔ Derivable CS5ModalAxiom φ`
- [ ] Docstring: state that this is why the product-model-over-`IS5` route is not adopted — its
      residual is the collapse, not a weaker statement — and that the collapse's only published
      basis (Pacheco's `CKB = IKB`, §4) rests on the same unsound Lemma 16 this module repairs
- [ ] `lake build` the new/host module

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/` (new file, e.g. `CS5ToIS5.lean`) — placement chosen
  so the `Constructive → Intuitionistic` import direction stays clean; confirm against
  `Cslib.lean` barrel conventions and run `lake exe mk_all --module`

**Verification**:
- New module builds and is added to the barrel; `lake exe checkInitImports` passes
- Route-closure theorem sorry-free under `lean_verify`
- `lake exe lint-style` and `lake lint` clean on the new file

---

## Stage B — Nested Sequent Syntax

### Phase 6: Nested sequent structures and the `fm` translation [NOT STARTED]

**Goal**: Encode Arisaka–Das–Straßburger §2 eq. (2.1) and the corresponding-formula translation.

**Tasks**:
- [ ] Verify eq. (2.1) and the `fm` clauses against the recovered PDF before writing
- [ ] Define mutual inductives `NestedLhs (Atom)` (`∅ | A• | [Φ] | Φ, Φ`) and `NestedRhs (Atom)`
      (`A◦ | [Φ, Ψ]`) over `Cslib.Logic.Modal.Proposition Atom`, and `NestedFull := NestedLhs ×
      NestedRhs`. Two separate types, not one type with a well-formedness predicate: the
      "exactly one output formula" invariant then holds by construction
- [ ] Define `fm` on each: `fm(A•) = fm(A◦) = A`, `fm([Φ]) = ◇ fm(Φ)`, `fm([Φ, Ψ]) = □ (fm(Φ, Ψ))`,
      `fm(∅) = ⊤`, `fm(Φ₁, Φ₂) = fm(Φ₁) ∧ fm(Φ₂)`, `fm(Φ, Ψ) = fm(Φ) → fm(Ψ)`
- [ ] Land the Example 2.1 / Example 2.2 computations as `example`s, as executable documentation
      that the encoding matches the source
- [ ] Decide and document the comma treatment: `Φ, Φ` is a syntactic constructor, with
      associativity/commutativity/unit handled by explicit permutation lemmas rather than a
      quotient (matching how `Deriv`'s `List` contexts are handled elsewhere in the modal library)
- [ ] `lake build` the new module

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Syntax.lean` (new)

**Verification**:
- Module builds, no `sorry`; the Example 2.1 `example`s close by `rfl` or `decide`
- The ill-formed combinations of Example 2.1 are not expressible (type error), confirmed by a
  commented-out snippet plus a note

---

### Phase 7: Contexts, hole filling, and output pruning [NOT STARTED]

**Goal**: Encode contexts in Observation 2.2 normal form so well-formedness is definitional, and
define `Γ{∆}`, `Γ{∅}`, and `Γ⇓`.

**Tasks**:
- [ ] Define `OutputCtx := List NestedLhs` with the reading `Γ•₁, [Γ•₂, [… , [Γ•ₙ, { }] …]]`
      (Observation 2.2, eq. (2.2))
- [ ] Define `InputCtx` as the triple `⟨Γ' : OutputCtx, Λ : OutputCtx, Π : Proposition⟩` per
      eq. (2.3) `Γ'{Λ{ }, Π◦}`
- [ ] Define hole filling for both context kinds at each admissible filler type (RHS, full, LHS,
      and `∅`), with the result type determined statically per Observation 2.2's typing statement
- [ ] Define output pruning `Γ⇓ { } := Γ'{Λ{ }}` (Definition 2.3) on `InputCtx`, returning an
      `OutputCtx`
- [ ] Land the basic equational lemmas: filling with `∅`, nesting/associativity of filling,
      and `(Γ⇓){∆}` versus `Γ{∆}` relationships used later
- [ ] `lake build`

**Timing**: 2.5 hours

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Syntax.lean` (extend) or a sibling
  `Nested/Context.lean` if the file exceeds ~350 lines

**Verification**:
- Module builds, no `sorry`
- Observation 2.2's uniqueness claim holds by construction (documented, not proved as a lemma)
- Example 2.1's `Γ₁{ }`, `Γ₂{ }` are expressible and their `Γ{∅}` computations match the paper

---

### Phase 8: `fm` compositionality over contexts [NOT STARTED]

**Goal**: The workhorse lemmas relating `fm (Γ{∆})` to `fm ∆`, which every soundness case consumes.

**Tasks**:
- [ ] For each context kind, prove by induction on the `OutputCtx` list (the Lean form of
      "induction on the structure of `Γ{ }` (see Observation 2.2)") that `CS5`-derivability of
      `fm ∆ → fm ∆'` lifts to `fm (Γ{∆}) → fm (Γ{∆'})`, in the appropriate variance
- [ ] Prove the pruning relation: how `fm (Γ⇓{∆})` relates to `fm (Γ{∆})`
- [ ] Prove the monotonicity/anti-monotonicity direction facts each context kind needs (output
      contexts are covariant in the hole, input contexts contravariant)
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 7

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Translation.lean` (new)

**Verification**:
- Module builds, no `sorry`; every lemma stated against `Derivable (@CS5ModalAxiom Atom)`, so the
  Hilbert-relative currency is fixed from the start
- These are the reusable deliverables for the labelled-soundness consumer; docstring each with the
  node-wise adequacy reading

---

## Stage C — The Rule Systems

### Phase 9: `NCK′` rules [NOT STARTED]

**Goal**: The base nested-sequent system as an inductive proof-tree type.

**Tasks**:
- [ ] Verify the `NCK′` rule figure against the recovered PDF before writing
- [ ] Define `NestedProof : NestedFull Atom → Type` with the `NCK′` rules (identity/axiom, the
      propositional input/output rules, `⊥•`, the modal `□•`/`□◦`/`♦•`/`♦◦` rules, `k`, and the
      explicit contraction rule the paper flags as necessary in the constructive setting)
- [ ] Define `NestedProof.height`
- [ ] Land the smoke-test derivations the paper gives in §3
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 7

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Rules.lean` (new)

**Verification**:
- Module builds, no `sorry`; the §3 example derivations typecheck

---

### Phase 10: `NCS5 = NCK′ + {t,4}#_G + {b}[]` [NOT STARTED]

**Goal**: The `CS5` instance of the safe-pair scheme, plus the structural transport lemmas the
later inductions need.

**Tasks**:
- [ ] Verify the `t•`, `t◦`, `4•`, `4◦` (logical) and `b[]` (structural) rule figures against the
      PDF
- [ ] Extend the rule inductive to `NCS5`, with the axiom-set parameterisation kept explicit so a
      later cube generalisation is additive
- [ ] Record in a docstring why this is the right instance: safe pair `X = {t,4}`, `Y = {b}` —
      `5 ∉ Y` makes the first side condition vacuous, and `b ∈ Y` with `4 ∈ X` satisfies the
      second (Theorem 5.2, which names `CS5` in its covered list)
- [ ] Land weakening/`.mono` transport and the height bounds it preserves
- [ ] `lake build`

**Timing**: 2.5 hours

**Depends on**: 9

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Rules.lean`

**Verification**:
- Module builds, no `sorry`; `.mono` is height-non-increasing (stated and proved)

---

## Stage D — Soundness (Theorem 4.1)

### Phase 11: Soundness auxiliary lemmas [NOT STARTED]

**Goal**: The Lemma 4.2–4.9 family, as Hilbert-derivability facts about contexts.

**Tasks**:
- [ ] Verify Lemmas 4.2–4.9 against the PDF
- [ ] Land each as a statement about `Derivable (@CS5ModalAxiom Atom)`, proved by induction on the
      `OutputCtx` list using Phase 8's compositionality lemmas
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 8, 10

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` (new)

**Verification**: Module builds, no `sorry`; each lemma's statement is cross-referenced to its
source number in its docstring

---

### Phase 12: Theorem 4.1, propositional and `k` cases [NOT STARTED]

**Goal**: First half of soundness.

**Tasks**:
- [ ] State `nested_sound : NestedProof Γ → Derivable (@CS5ModalAxiom Atom) (fm Γ)`
- [ ] Discharge the identity, propositional, `⊥•`, contraction, and `k` cases
- [ ] Leave the modal/structural cases as explicit named holes closed in Phase 13 — no `sorry`:
      structure the proof as a case-analysis whose remaining branches are supplied by Phase 13's
      lemmas, so the file never contains an incomplete term
- [ ] `lake build`

**Timing**: 2.5 hours

**Depends on**: 11

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`

**Verification**: Module builds, no `sorry`; the phase lands the per-case lemmas, with the
top-level theorem assembled in Phase 13

---

### Phase 13: Theorem 4.1, modal and structural cases [NOT STARTED]

**Goal**: Complete soundness.

**Tasks**:
- [ ] Discharge `□•`, `□◦`, `♦•`, `♦◦`, `t•`, `t◦`, `4•`, `4◦`, `b[]`
- [ ] Assemble `nested_sound`
- [ ] Corollary: `NestedProof (A◦) → Derivable (@CS5ModalAxiom Atom) A`
- [ ] `lake build`

**Timing**: 2.5 hours

**Depends on**: 12

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`

**Verification**: `nested_sound` sorry-free under `lean_verify`; module builds

---

## Stage E — Completeness with Cut (Theorem 5.1)

### Phase 14: Nested derivations of the `CS5` axioms [NOT STARTED]

**Goal**: Every `CS5ModalAxiom` constructor is `NCS5 + cut`-provable.

**Tasks**:
- [ ] Add the `cut` rule (eq. (3.1)) to the proof-tree inductive, gated so `CutFree` can exclude it
      (mirror `LJ/Basic.lean`'s `SeqProof.CutFree` treatment of `.cut`)
- [ ] Derive each of the nine propositional constructors, `k`, `kdia`, `tBox`, `tDia`, `fourBox`,
      `fourDia`, `bBox`, `bDia` as `NestedProof (ψ◦)`
- [ ] Cross-check against §5's "Proofs of the axioms d, t, b, 4, and 5 in our system"
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 10

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Completeness.lean` (new),
  `Nested/Rules.lean` (add `cut`, `CutFree`)

**Verification**: Module builds, no `sorry`; one named theorem per axiom constructor

---

### Phase 15: Theorem 5.1 — completeness with cut [NOT STARTED]

**Goal**: `Derivable CS5ModalAxiom A → NestedProof (A◦)`.

**Tasks**:
- [ ] Simulate `modus_ponens` by `cut`
- [ ] Simulate necessitation by the `□◦` rule
- [ ] Simulate weakening/assumption handling to match `modalDerivationSystem`'s `Deriv` shape
- [ ] Assemble `nested_complete_with_cut`
- [ ] Sanity corollary with Phase 13: `Derivable CS5ModalAxiom A ↔ NestedProof (A◦)` (with cut)
- [ ] `lake build`

**Timing**: 2 hours

**Depends on**: 13, 14

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Completeness.lean`

**Verification**: The biconditional is sorry-free — a self-contained, independently valuable
milestone (a nested-sequent presentation of `CS5`, verified equivalent to the Hilbert system)

---

## Stage F — Cut Elimination (§6)

### Phase 16: Super-rules and Proposition 6.4 [NOT STARTED]

**Goal**: `s4•`, `s4◦`, `s4□`, `s4♦`, `sb[]` and their mutual derivability with the base rules.

**Tasks**:
- [ ] Verify Figure 6 against the PDF
- [ ] Define the super-rules; define `Xs#_G` and `Ys[]` for the safe pair `⟨{t,4}, {b}⟩` (which
      selects the `b ∈ Y, 5 ∉ Y` branch: `Ys[] = (Y[] \ {b[]}) ∪ {sb[]}`)
- [ ] Prove Proposition 6.4 both directions: `4•`/`4◦` are special cases of `s4•`/`s4◦` and `b[]`
      of `sb[]`; conversely `s4•`/`s4◦` are sequences of `4•`/`4◦`, `s4□`/`s4♦` are those composed
      with `□•`/`♦◦`, and `sb[]` is a sequence of `b[]`
- [ ] `lake build`

**Timing**: 2.5 hours

**Depends on**: 10

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/SuperRules.lean` (new)

**Verification**: Module builds, no `sorry`; both directions of Proposition 6.4 landed

---

### Phase 17: Lemma 6.5 — permutation of `s4•`/`s4◦` over `Ys[]` [NOT STARTED]

**Goal**: The permutation lemma the cut-elimination induction rests on.

**Tasks**:
- [ ] Verify the two nontrivial `s4◦`-over-`sb[]` interactions against the PDF
- [ ] Prove both, then the remaining "similar" cases explicitly (they are not similar to Lean)
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 16

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/SuperRules.lean`

**Verification**: Module builds, no `sorry`; each interaction is its own named lemma so a failure
localises

---

### Phase 18: Auxiliary cuts `♦cut`, `□cut`, and Fact 6.6 [NOT STARTED]

**Goal**: The strengthened cut forms eq. (6.2) needed because plain `cut` is too weak once `4•`
and `4◦` are present.

**Tasks**:
- [ ] Verify eq. (6.2) against the PDF
- [ ] Define `♦cut` (premises `Γ⇓{Θ•{♦A◦}}` and `Γ{♦A•, Θ•{∅}}`, conclusion `Γ{Θ•{∅}}`) and `□cut`
      (premises `Γ⇓{A◦, (Θ{∅})⇓}` and `Γ{Θ{A•}}`, conclusion `Γ{Θ{∅}}`)
- [ ] Prove Fact 6.6: `♦cut` derivable in `{cut, s4◦}` and in `{cut, 4◦}`; `□cut` derivable in
      `{cut, s4•}` and in `{cut, 4•}`
- [ ] Define `Cut := {cut, ♦cut, □cut}` and the `∗cut` abbreviation, fixing the convention that
      the output cut formula occurs in the left premise
- [ ] `lake build`

**Timing**: 2.5 hours

**Depends on**: 16

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/CutRules.lean` (new)

**Verification**: Module builds, no `sorry`; the premise-side convention is stated in a docstring
and used uniformly downstream

---

### Phase 19: Height-preserving admissibility of the structural rules [NOT STARTED]

**Goal**: Weakening and contraction admissible without increasing proof height — the precondition
for the cut induction to terminate.

**Tasks**:
- [ ] Height-preserving weakening (extend Phase 10's `.mono` to the height-preserving statement)
- [ ] Height-preserving contraction
- [ ] Any additional invertibility facts the principal cases will consume, identified by reading
      §6 ahead
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 10

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Admissibility.lean` (new)

**Verification**: Module builds, no `sorry`; each admissibility result carries an explicit height
bound in its statement

---

### Phase 20: The cut-value well-ordering [NOT STARTED]

**Goal**: The measure `≪` on cut-values, and its well-foundedness.

**Tasks**:
- [ ] Verify the definition of the cut-value and `≪` against the PDF
- [ ] Define the cut-value of a `∗cut` step (cut formula plus the relevant height/rank components)
- [ ] Prove `≪` well-founded, preferably by exhibiting a measure into a Mathlib well-founded order
      (lexicographic on `Nat`s) rather than constructing an `IsWellFounded` instance by hand
- [ ] `lake build`

**Timing**: 2.5 hours

**Depends on**: 18

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/CutMeasure.lean` (new)

**Verification**: Module builds, no `sorry`; well-foundedness available as a `WellFoundedRelation`
usable by `termination_by`

---

### Phase 21: Anchored-cut analysis — principal propositional cases [NOT STARTED]

**Goal**: `∧`, `∨`, `⊃` principal cases, one named lemma each.

**Tasks**:
- [ ] Mirror `LJ/CutElimination.lean`'s decomposition: a separate lemma per principal connective,
      each doing structural recursion on the right premise given a sub-proof of the left
- [ ] `∧` principal case
- [ ] `∨` principal case
- [ ] `⊃` principal case
- [ ] `lake build`

**Timing**: 3.5 hours

**Depends on**: 19, 20

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/CutElimination.lean` (new)

**Verification**: Module builds, no `sorry`; each case is independently green and committable

---

### Phase 22: Anchored-cut analysis — principal modal cases [NOT STARTED]

**Goal**: `□`, `♦` principal cases and the `t`/`4`/`b` interactions.

**Tasks**:
- [ ] `□` principal case, using `□cut`
- [ ] `♦` principal case, using `♦cut`
- [ ] `t•`/`t◦` interactions
- [ ] `4•`/`4◦` interactions via the super-rules and Phase 17's permutation lemma
- [ ] `b[]` interactions via `sb[]`
- [ ] `lake build`

**Timing**: 3.5 hours

**Depends on**: 17, 21

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/CutElimination.lean`

**Verification**: Module builds, no `sorry`

---

### Phase 23: Commutative cases and Theorem 6.3 [NOT STARTED]

**Goal**: Cut elimination for `NCS5`.

**Tasks**:
- [ ] Commutative (non-principal) cases on both premises
- [ ] Assemble the induction over `≪`, applying it to the leftmost-topmost `∗cut` step
- [ ] State and prove `nested_cutElim : NestedProof Γ → CutFreeNestedProof Γ` (Theorem 6.3)
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 22

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/CutElimination.lean`

**Verification**: `nested_cutElim` sorry-free under `lean_verify`

---

### Phase 24: Theorem 5.2 — cut-free completeness for `CS5` [NOT STARTED]

**Goal**: **Milestone.** A sorry-free cut-free proof system for `CS5`, verified equivalent to
CSLib's Hilbert system.

**Tasks**:
- [ ] Compose Phase 15 (completeness with cut) with Phase 23 (cut elimination) into
      `Derivable (@CS5ModalAxiom Atom) A → CutFreeNestedProof (A◦)`
- [ ] Compose with Phase 13 for the biconditional `Derivable CS5ModalAxiom A ↔ CutFreeNestedProof
      (A◦)`
- [ ] Module docstring recording the safe-pair justification, the Hilbert-relative currency, and
      the fact that Arisaka–Das–Straßburger's Kripke-semantics disclaimer does not affect this
      result
- [ ] Full `lake build`, `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`,
      `lake exe mk_all --module`, `lake test`

**Timing**: 2 hours

**Depends on**: 15, 23

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/CutFreeCompleteness.lean` (new), `Cslib.lean`

**Verification**:
- Whole-project build green; bare-`sorry` count in `Cslib/` still exactly 5
- This is the natural stage boundary: everything up to here is deliverable independently of
  Stage G's success

---

### Phase 25: Subformula property for cut-free proofs [NOT STARTED]

**Goal**: The instrument the exclusion argument consumes.

**Tasks**:
- [ ] Mirror `LJ/SubformulaProperty.lean`'s statement shape, adapted to nested sequents (every
      formula occurring in a cut-free proof is a subformula of a formula in the end-sequent,
      modulo the `t`/`4`/`b` rules' effect on modal depth — state the precise closure the modal
      rules force and prove that, not a false stronger claim)
- [ ] `lake build`

**Timing**: 2.5 hours

**Depends on**: 24

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/SubformulaProperty.lean` (new)

**Verification**: Module builds, no `sorry`; the statement is checked to be strong enough for
Phase 31's needs *before* Phase 26 begins (recorded as a note in the phase's commit)

---

## Stage G — The Two-Label Bridge (highest risk)

### Phase 26: The pair nested system and cross rules [NOT STARTED]

**Goal**: Instantiate the base system at `Atom ⊕ Atom` and add the cross rules, with soundness.

**Tasks**:
- [ ] Instantiate `NCS5` at `Atom ⊕ Atom` (the base system is already parametric in the atom type,
      so this is free)
- [ ] Add cross rules for `□(τ_L B) → τ_R B` and `□(τ_R B) → τ_L B` using the **axioms-as-rules**
      technique (Negri), i.e. as rules acting on the nested structure rather than as formulas
      introduced by `cut` — this is the design choice that gives Phase 28 its best chance
- [ ] Record the shape explicitly: the cross rules are restricted to *purely tagged* `B`, matching
      `CS5PairAxiom.cross1`/`.cross2`, and are the only place left/right content mixes modally
- [ ] Prove soundness of the cross rules against `CS5PairAxiom`: `NCS5Pair ⊢ Γ → Derivable
      (@CS5PairAxiom Atom) (fm Γ)`, extending Phase 13
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 13, 24

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Pair.lean` (new)

**Verification**: Module builds, no `sorry`; pair soundness landed

---

### Phase 27: Completeness with cut for `CS5PairAxiom` [NOT STARTED]

**Goal**: `Derivable CS5PairAxiom φ → NCS5PairProof (φ◦)`.

**Tasks**:
- [ ] Derive every `CS5PairAxiom` constructor: `left`/`right` (via the Phase 14 derivations
      transported along the tagging maps), `cross1`/`cross2` (via the new rules), and the nine
      whole-type propositional constructors — note these are at *arbitrary* formulas of
      `Proposition (Atom ⊕ Atom)`, mixed formulas included, which is exactly what the primeness
      engine forces and what the relabeling retraction could never handle
- [ ] Simulate `modus_ponens` and necessitation as in Phase 15
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 15, 26

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Pair.lean`

**Verification**: Module builds, no `sorry`

---

### Phase 28: Cross-rule permutation — the crux [NOT STARTED]

**Goal**: Show the cross rules permute in the cut-elimination induction. **This is the highest-risk
phase in the plan.**

**Tasks**:
- [ ] Enumerate every interaction of a cross rule with each `∗cut` variant and with each of
      `s4•`, `s4◦`, `s4□`, `s4♦`, `sb[]` — write the list out first, as an explicit checklist, so
      partial progress is measurable and a failure localises to a named interaction
- [ ] Prove each permutation, or identify precisely the first one that fails
- [ ] Confirm or refute that the cut-value measure of Phase 20 still decreases across cross-rule
      steps; if not, extend the measure and re-verify Phase 20's well-foundedness
- [ ] If an interaction genuinely fails: stop, mark this phase `[BLOCKED]`, record the exact
      interaction, the goal state, and what was tried. **Do not** weaken the target, insert a
      `sorry`, or substitute a different obligation
- [ ] `lake build`

**Timing**: 4 hours

**Depends on**: 23, 27

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Pair.lean`, possibly
  `Nested/CutMeasure.lean`

**Verification**: Module builds, no `sorry`; the interaction checklist is fully discharged, or the
phase is `[BLOCKED]` with the failing case named. Per `.claude/rules/plan-compliance.md`, a
would-be deviation on this phase is escalated as a blocker, not silently annotated

---

### Phase 29: Cut elimination and cut-free completeness for the pair system [NOT STARTED]

**Goal**: The pair analogue of Phases 23–24.

**Tasks**:
- [ ] Extend the commutative-case analysis to the cross rules
- [ ] Assemble pair cut elimination
- [ ] Compose into pair cut-free completeness: `Derivable CS5PairAxiom φ ↔ CutFreeNCS5PairProof
      (φ◦)`
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 28

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Pair.lean` (split into
  `Nested/PairCutElimination.lean` if it exceeds ~400 lines)

**Verification**: Module builds, no `sorry`

---

### Phase 30: The seed-relative derivability bridge [NOT STARTED]

**Goal**: Relate `modalDeductiveClosure CS5PairAxiom (cs5PairSeed H)` to nested derivability from a
finite seed context.

**Tasks**:
- [ ] Probe first: confirm that `modalDeductiveClosure` unfolds to finite-list `Deriv`
      derivability (`PrimeTheory.lean:78`), so the bridge is a finite-context restatement rather
      than a compactness argument
- [ ] Define the nested encoding of a finite list of seed formulas as an input context
- [ ] Prove: `φ ∈ modalDeductiveClosure CS5PairAxiom (cs5PairSeed H)` iff there is a finite
      `L ⊆ cs5PairSeed H` with a `NCS5Pair + cut` proof of the corresponding full sequent; then
      apply Phase 29 to get a cut-free one
- [ ] `lake build`

**Timing**: 3 hours

**Depends on**: 29

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/PairSeed.lean` (new)

**Verification**: Module builds, no `sorry`; the biconditional is stated at the exact
`modalDeductiveClosure` shape `CS5Completeness.lean` uses

---

### Phase 31: The exclusion argument [NOT STARTED]

**Goal**: From a cut-free pair derivation of `τ_R A` from the seed, conclude `A ∈ cl_CS5(boxInv H)`.

**Tasks**:
- [ ] Formalise the tag-inertness invariant round 1 §2.1 identified: `Θ ∩ τ_L''Prop = τ_L''H` and
      `Θ ∩ τ_R''Prop = τ_R''K` — no `CS5PairAxiom` constructor consumes `□φ` for genuinely mixed
      `φ`, so necessitation can produce mixed boxes but nothing can use them
- [ ] Use Phase 25's subformula property to bound which formulas can appear in a cut-free
      derivation from the seed, and hence rule out mixed intermediates short-circuiting the fixed
      point — this is precisely the step that was unavailable without cut elimination
- [ ] Prove the transfer facts round 1 §2.1 lists: `boxInv H ⊆ K`, `K ⊆ H`, the `B`-axiom transfers
      `τ_L B → τ_R ◇B` and `τ_R C → τ_L ◇C`
- [ ] Conclude the conservativity statement
- [ ] `lake build`

**Timing**: 3.5 hours

**Depends on**: 25, 30

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/PairSeed.lean`

**Verification**: Module builds, no `sorry`

---

### Phase 32: Discharge and downstream instantiation [NOT STARTED]

**Goal**: Land `CS5PairSeedRightExclusion` as a theorem and instantiate the primeness engine.

**Tasks**:
- [ ] Land `cs5PairSeedRightExclusion_holds : ∀ H A, CS5PairSeedRightExclusion H A` from Phase 31
- [ ] Compose with Phase 2's entry point and Phase 3's caller-side bridge to get an unconditional
      `DerivExcludes` for a `CS5`-deductively-closed `H` with `□A ∉ H`
- [ ] Instantiate `Metalogic.prime_set_exclusion` (`PrimeExclusion.lean:562`) at `CS5PairAxiom`
      using the landed hypothesis bundle (`cs5Pair_hImplyK` … `cs5Pair_hCut`), yielding the prime
      admissible `T ⊇ cl(cs5PairSeed H)` excluding `{τ_L (□A), τ_R A}`
- [ ] Rewrite the "Open Obligations" section of `CS5Completeness.lean` to record what is now
      proved, and what remains for the native `cs5_completeness''` (projecting `T`'s components —
      out of scope here, and stated as such)
- [ ] Full CI: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`,
      `lake test`, `lake exe mk_all --module`, `lake shake --add-public --keep-implied
      --keep-prefix`

**Timing**: 2.5 hours

**Depends on**: 2, 3, 31

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`,
  `Cslib/Logics/Modal/Metalogic/Constructive/Nested/PairSeed.lean`, `Cslib.lean`

**Verification**:
- Whole-project CI green
- `lean_verify` on `cs5PairSeedRightExclusion_holds` reports only `[propext, Classical.choice,
  Quot.sound]` and no `sorryAx`
- Bare-`sorry` count in `Cslib/` is exactly 5

---

## Testing & Validation

- [ ] After every phase: `lake build <scoped module>` green
- [ ] After every phase: `lean_verify` on each new theorem shows no `sorryAx`
- [ ] After every phase: bare-`sorry` count in `Cslib/` is exactly 5 (the five sites listed under
      Non-Goals). Check with a grep for bare `sorry` lines, not for the substring `sorry`, which
      also matches docstring prose
- [ ] No `def X := True` / `theorem X := trivial` / vacuous placeholder anywhere
      (`.claude/rules/cslib.md`, Vacuous Definitions)
- [ ] No task-number or `specs/` path citations in any file under `Cslib/`
- [ ] At Phase 24 (milestone) and Phase 32 (completion): full CI in the order given in
      `.claude/rules/cslib.md` — `lake exe cache get`, `lake build`, `lake exe checkInitImports`,
      `lake lint`, `lake exe lint-style`, `lake test`, `lake exe mk_all --module`, `lake shake`
- [ ] Every rule figure transcribed from Arisaka–Das–Straßburger is checked against the recovered
      PDF at `~/Projects/Literature/.sources-recovered/` before it is written, and the check is
      noted in the phase commit message (literature chunks carry `provenance_fidelity:
      unverified_summary` and must not be treated as authoritative)
- [ ] Regression: `cs5PairSeedDisjunctionProperty_false` remains a theorem, so the unconditioned
      obligation can never be reintroduced

## Artifacts & Outputs

- `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md` (this file)
- `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/summaries/02_*-summary.md`
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` (corrected statement, reduction
  lemmas, caller-side bridge, retraction assets, docstring corrections, final discharge)
- `Cslib/Logics/Modal/Metalogic/InterSystem/CS5ToIS5.lean` (transport lemmas + route-closure
  theorem)
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/` — new module tree: `Syntax.lean`,
  `Translation.lean`, `Rules.lean`, `Soundness.lean`, `Completeness.lean`, `SuperRules.lean`,
  `CutRules.lean`, `Admissibility.lean`, `CutMeasure.lean`, `CutElimination.lean`,
  `CutFreeCompleteness.lean`, `SubformulaProperty.lean`, `Pair.lean`, `PairSeed.lean`
- `Cslib.lean` (barrel updates via `lake exe mk_all --module`)

## Rollback/Contingency

**Per phase**: every phase ends at a green committable checkpoint with its own scoped commit
(`task 554 phase {P}: {name}`). Reverting a phase is a single-commit revert; no phase leaves the
build red.

**If Phase 28 fails** (the identified crux): mark Phase 28 `[BLOCKED]` and the task `[BLOCKED]`,
with the failing cross-rule/`∗cut` interaction named precisely. **Preserved assets** in that case
are substantial and stand on their own:

- Stage A: the corrected obligation, the refutation regression, the reduction to a single
  obligation, the caller-side bridge, the retraction functoriality, and the machine-checked
  closure of the product-model route.
- Stages B–F: a complete, sorry-free cut-free nested-sequent system for `CS5` with soundness,
  completeness, cut elimination, cut-free completeness, and the subformula property — a
  library-grade asset independent of this obligation, and the instrument needed to settle the
  `CS5 = IS5` question rigorously should that ever be authorised.
- The labelled-soundness consumer's deliverables (Phases 6, 8, 11) land at Waves 1, 3, and 5 and
  are unaffected.

This is why round 2's characterisation of the route as having "no partial payoff" is not carried
forward: the payoff is staged, and the two largest stage boundaries (Phase 24 and Phase 25) both
precede the crux.

**If an earlier phase fails**: the stage boundaries after Phases 5, 15, 24, and 25 are natural
split points. The orchestrator may convert any remaining stage into a follow-up task without
rework, since each stage's outputs are named modules with stated interfaces.

**Never**: discharge any obligation with `sorry`, an `axiom`, or a weakened, vacuous, or restated
target. A blocked phase is reported as blocked.
