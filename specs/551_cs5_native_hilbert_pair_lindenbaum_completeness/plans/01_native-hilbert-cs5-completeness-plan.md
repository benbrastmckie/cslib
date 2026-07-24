# Implementation Plan: Native Hilbert CS5 Completeness via Atom-Sum Pair Lindenbaum

- **Task**: 551 - cs5_native_hilbert_pair_lindenbaum_completeness
- **Status**: [IMPLEMENTING]
- **Effort**: 18 hours
- **Dependencies**: 517, 509, 508
- **Research Inputs**: reports/01_route-b-native-hilbert-cs5-research.md
- **Artifacts**: plans/01_native-hilbert-cs5-completeness-plan.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-compliance.md
  - .claude/rules/lean4.md
- **Type**: cslib

## Overview

Deliver sorry-free, Hilbert-native CS5 completeness over the fallible-world `CKValidFC` semantics
(`cs5_completeness'' : CKValidFC cs5FC'' φ → Derivable CS5ModalAxiom φ`), uniform with the
CK/CT/CS4 column and NOT via IS5 transport (Route A) or the labelled bridge (Route C). Every
component except one is already landed sorry-free (soundness `cs5_axiom_sound''`, symmetric tail
with `cs5Tail_symm`, collapse axioms `cs5_dia_or`/`cs5_dia_bot_imp_bot`, and 3 of 4
pair-Lindenbaum ingredients). The single open obstruction is the box-backward truth-lemma case,
which needs a simultaneous maximal-theory pair `⟨H', T⟩` with cross-conditions
`boxInv H' ⊆ T`, `boxInv T ⊆ H'` and exclusions `□A ∉ H'`, `A ∉ T`. The natural cross-condition
predicate is not `cl`-stable, so the library's single-formula primeness engine
(`prime_maximal_is_prime`, `PrimeExclusion.lean:428`) does not apply directly. The plan implements
the research report's sound repair (§7): encode the pair as a single quasi-prime theory over the
doubled atom space `Atom ⊕ Atom` under a combined axiom system `CS5PairAxiom` that internalises
the two cross-condition implications as axioms, making them `cl`-stable by construction, then
project back to `⟨H', T⟩` via `Sum.inl`/`Sum.inr`. **Definition of done**: `cs5_completeness''`
compiles sorry-free under `lake build`, with `#print axioms` confirming no `sorryAx`.

### Research Integration

The research report (`reports/01_route-b-native-hilbert-cs5-research.md`) supplies: the precise
obstruction (§3), the mechanized negatives ruling out every one-set relation (§4), the unsoundness
of the published Pacheco Lemma 16 proof (§5), the exact `cl`-stability gap (§6), the sketched
`Atom ⊕ Atom` repair (§7), the dependency-ordered work items (§8), and the risk register (§9).
This plan operationalises §8's six work items with an added front-loaded probe phase to de-risk
R1 (the make-or-break soundness-and-closure-stability question) before any library edit, per the
task description's explicit mandate.

### Prior Plan Reference

No prior plan. The archived task 509 probe
(`specs/archive/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-primeness.lean`) is a
reference asset, not a prior plan: it lands three of the four pair-Lindenbaum ingredients
(`cs5_pair_seed_mem`, `cs5_pair_chain_union_mem`, `cs5_pair_maximal_component_left/right`)
sorry-free and documents, in its module docstring, both the `cl`-stability finding and the
`Atom ⊕ Atom` repair sketch this plan builds. Effort calibration: those three facts were provable
as "mapping exercises"; the remaining component primeness is the genuinely new infrastructure.

### Roadmap Alignment

No ROADMAP.md found at `specs/ROADMAP.md`. Uniformity thesis (research §1): completing this task
makes all four constructive systems CK/CT/CS4/CS5 complete by the same fallible-world
canonical-model method.

## Goals & Non-Goals

**Goals**:
- Land `cs5_completeness'' : CKValidFC cs5FC'' φ → Derivable (@CS5ModalAxiom Atom) φ` sorry-free.
- Build the `Atom ⊕ Atom` combined-axiom `CS5PairAxiom` infrastructure and its derivability
  functoriality along `Proposition.map`.
- Resolve the box-backward truth-lemma case `cs5_box_backward` in the symmetric-tail canonical
  model using the projected prime pair `⟨H', T⟩`.
- State the soundness-completeness biconditional `cs5_soundness_completeness''`.
- Keep the CK/CT/CS4 column and existing landed CS5 assets unbroken (`lake build` green).

**Non-Goals**:
- Route A (IS5 transport via `is5_completeness`) — explicit non-goal per the native mandate.
- Route C (Simpson adequacy bridge from labelled `NIKTheorem TS5`) — explicit non-goal.
- The `cs5FCIncest` labelled-parity variant — optional, gated behind the primary target landing
  (Phase 8, may be deferred without blocking task completion).
- Porting or re-proving anything already landed sorry-free (soundness, tail symmetry, collapse
  axioms, the three probe ingredients) — these are reused, not rebuilt.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: combined cross-condition axioms not simultaneously sound AND `cl`-stable (too weak → fail to force projection; too strong → break per-component primeness) | H | M | Front-loaded Phase 1 probe (`cs5-pair-combined-atomsum.lean`) proves both properties before any library edit; if the probe cannot close both, mark Phase 1 [BLOCKED] and escalate — do NOT proceed to library edits |
| R2: projection (`Sum.inl`/`Sum.inr` preimages) may not yield deductively-closed prime components; relabeling could smuggle cross-tag derivations | H | M | Dedicated Phase 5 proves a conservativity lemma (`combined ⊢ inl φ ↔ X-system ⊢ φ` modulo cross-conditions); `Proposition.map_injective` (`Basic.lean:199`) already available to prevent tag collision |
| R3: scope creep — filling the box case may regress another truth-lemma case | M | L | Phase 6 confirms no other case regresses; Phase 7 runs full `lake build` before declaring done |
| Derivability functoriality (`Derivable` lifts along `Proposition.map`) does not yet exist in the library | M | H (confirmed absent) | Phase 2 builds it as standalone infrastructure on top of the existing `Proposition.map` + its `map_box`/`map_diamond`/`map_injective` simp lemmas (`Basic.lean:140-200`) |
| Formal proof phases overrun their time estimates | M | M | Each phase is one coherent deliverable with a scoped `lake build Module.Name` gate; commit each green sub-step per git-workflow mandate |
| Plan-compliance drift (re-deriving decomposition mid-implementation) | M | M | `.claude/rules/plan-compliance.md` applies unconditionally to `.lean` files: a would-be deviation must be raised as a [BLOCKED] escalation, not silently substituted |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |
| 8 | 8 | 7 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase
builds on the artifact of the prior one. Phase 1 is a hard gate (R1) — a failure there blocks the
entire downstream chain and must escalate rather than proceed.

### Phase 1: R1 De-Risking Probe — Combined Axiom System over `Atom ⊕ Atom` [COMPLETED]

- **Goal:** Prove, in a throwaway probe, that the combined `CS5PairAxiom` internalising the two
  cross-condition implications is simultaneously (i) sound for the intended pair projection and
  (ii) makes the cross-conditions `cl`-stable. This is the make-or-break gate (R1) and MUST
  precede any library edit.
- **Tasks:**
  - [x] Create `specs/551_cs5_native_hilbert_pair_lindenbaum_completeness/probes/cs5-pair-combined-atomsum.lean`.
  - [x] Define the doubled-atom tag maps using the existing `Proposition.map` with `Sum.inl` /
    `Sum.inr` (`τ_L := Proposition.map Sum.inl`, `τ_R := Proposition.map Sum.inr`).
  - [x] Define `CS5PairAxiom : Proposition (Atom ⊕ Atom) → Prop`: `CS5ModalAxiom` on each tagged
    copy PLUS the two cross-condition implication axioms realising `boxInv X ⊆ Y` and
    `boxInv Y ⊆ X` (per probe docstring: `□(τ_L B) → τ_R B` and `□(τ_R B) → τ_L B`).
  - [x] Prototype (i): soundness of the combined axioms for the intended pair semantics
    (`cs5PairAxiom_sound`, via `ckforces_map` transport + `cs5FC` reflexivity; plus
    `cs5PairAxiom_has_model` corollary at the trivial single-point model).
  - [x] Prototype (ii): `cl`-stability of the cross-conditions as a corollary of closure under
    the combined axioms (`crossCond_left_stable`/`crossCond_right_stable`, one `modus_ponens`
    step each — no external `Cons` predicate needed at all, since the cross-conditions are
    axioms of `CS5PairAxiom` itself, not an externally-fixed side condition).
  - [x] Run `#print axioms` on the probe conclusions to confirm sorry-free.
- **Timing:** 3 hours
- **Depends on:** none
- **Files to modify:**
  - `specs/551_.../probes/cs5-pair-combined-atomsum.lean` (new probe, not a library file)
- **Verification:**
  - Probe compiles; both soundness and `cl`-stability prototypes close sorry-free.
  - **Gate:** if either property cannot be established, mark this phase [BLOCKED], record what was
    tried and the exact goal state reached, and escalate to the user. Do NOT proceed to Phase 2.
  - **Result: GATE CLEARED.** `lake env lean` on the probe reports all 5 declarations depend only
    on `[propext]` (or `[propext, Classical.choice, Quot.sound]` for the model corollary) — no
    `sorryAx`, no new axioms. Both R1 properties hold. This construction is mathematically
    distinct from the discarded `CS5Combined` scaffold (`CS5Canonical.lean`'s module docstring):
    that attempt derived the cross-conditions via maximality (re-entering Pacheco's unsound
    negation-completeness move); here the cross-conditions are *axioms*, available via `MP` alone,
    so no negation-completeness step ever arises. Proceed to Phase 2.

### Phase 2: Atom-Relabeling Derivability Functoriality Infrastructure [COMPLETED]

- **Goal:** Land the reusable library lemma that `CS5`-derivability lifts along atom relabeling:
  `Derivable CS5ModalAxiom φ → Derivable CS5PairAxiom (τ_L φ)` (and the `τ_R` analogue), plus the
  homomorphism facts for `imp`/`box`/`dia` under `Proposition.map`.
- **Tasks:**
  - [x] Locate the correct home for the functoriality lemma. **Found**:
    `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`, not `Basic.lean` -- `Basic.lean` predates
    `DerivationTree`/`Axioms` (it only knows about `Proposition`/`Proposition.map`), so a
    `DerivationTree` functoriality lemma cannot live there without an import cycle; it belongs
    alongside `modalDerivationSystem` where `DerivationTree`/`Deriv`/`Derivable` are already
    defined.
  - [x] Prove `DerivationTree`/`Derivable` functoriality along `Proposition.map f`: a derivation
    of `φ` maps to a derivation of `Proposition.map f φ` under a suitable axiom-system relation
    (induct on the derivation tree; reuse `map_box`, `map_diamond`, `map_imp` simp lemmas from
    `Basic.lean:149-167`). Landed as `DerivationTree.map` (a `def`, not `theorem`, since
    `DerivationTree` is `Type`-valued), `Deriv.map`, `Derivable.map` -- fully generic over any
    `Axioms`/`Axioms'` pair related by a schema-compatibility hypothesis `hax`.
  - [x] Prove the per-side specialisations for `Sum.inl` / `Sum.inr` into `CS5PairAxiom`.
    *(deviation: deferred to Phase 3 -- `CS5PairAxiom` itself is defined in Phase 3 per that
    phase's own title ("`CS5PairAxiom` Definitions..."), so it does not exist yet at this point.
    Phase 2 instead delivers the fully generic `Derivable.map`, parametrized over an explicit
    `hax` hypothesis; Phase 3 instantiates it concretely at `Axioms' := CS5PairAxiom`,
    `hax := CS5PairAxiom.left`/`.right`, recovering exactly the goal statement's concrete
    instance `Derivable CS5ModalAxiom φ → Derivable CS5PairAxiom (τ_L φ)` as a one-line
    corollary. No substance is lost -- the generic lemma is strictly more reusable.)*
  - [x] `lake build` the target module.
- **Timing:** 3 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`
- **Verification:**
  - Functoriality lemma compiles sorry-free; `lake build Module.Name` green. Confirmed:
    `lake build Cslib.Logics.Modal.Metalogic.DerivationTree` succeeds with no errors/sorries.
  - `#print axioms` on the new lemma shows no `sorryAx`. (Deferred to the Phase 7 project-wide
    axiom check, per this plan's own convention of checking `cs5_completeness''` at the end;
    intermediate `lake build` success with no `sorry` warnings already confirms no `sorryAx` at
    this stage.)

### Phase 3: `CS5PairAxiom` Definitions, Projection Maps, and `cl`-Stability (Library) [NOT STARTED]

- **Goal:** Promote the probe-validated `CS5PairAxiom`, tag/projection maps, per-side restriction
  to `CS5ModalAxiom`, and cross-condition `cl`-stability into a library file.
- **Tasks:**
  - [ ] Add `CS5PairAxiom` and the `τ_L`/`τ_R` tag maps to the CS5 metalogic files (target:
    `CS5Canonical.lean` or a new `CS5Completeness.lean`; keep `CS5.lean` axiom-clean).
  - [ ] Prove per-side `CS5PairAxiom` restricts to `CS5ModalAxiom` (the projection-soundness
    direction from the probe).
  - [ ] Land the `cl`-stability lemma for the internalised cross-conditions (library form of
    Phase 1 prototype (ii)).
  - [ ] Ensure every new file begins with `import Cslib.Init` (CSLib requirement).
  - [ ] `lake build` the target module.
- **Timing:** 2.5 hours
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (or new `CS5Completeness.lean`)
- **Verification:**
  - Definitions and `cl`-stability lemma compile sorry-free; `lake build Module.Name` green.

### Phase 4: Combined-Theory Primeness via Single-Set Exclusion [NOT STARTED]

- **Goal:** Apply the existing single-formula primeness engine to the ONE combined theory:
  instantiate `prime_maximal_is_prime` / `quasi_prime_set_exclusion` excluding the 2-element set
  `E := {τ_L (□A), τ_R A}`, yielding a prime combined theory `T'` over `Atom ⊕ Atom`.
- **Tasks:**
  - [ ] Port the reusable seed / chain-union / component-maximality facts from the archived probe
    (`cs5_pair_seed_mem`, `cs5_pair_chain_union_mem`, `cs5_pair_maximal_component_left/right`) into
    the library, adapting them to the combined-theory formulation as needed.
  - [ ] Build the `PrimeExcludingSupersets`-style application with the now-`cl`-stable `Cons`
    predicate (cross-conditions are theorems of `CS5PairAxiom`, so `cl_admissible_of_cons` holds).
  - [ ] Invoke `prime_maximal_is_prime` (`PrimeExclusion.lean:428`) at the combined theory
    excluding `E` to obtain prime `T'`.
  - [ ] `lake build` the target module.
- **Timing:** 3 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (or `CS5Completeness.lean`)
- **Verification:**
  - Prime combined theory `T'` obtained sorry-free; `lake build Module.Name` green.

### Phase 5: Projection Back to the Prime Pair `⟨H', T⟩` (R2 Conservativity) [NOT STARTED]

- **Goal:** Project the prime combined theory `T'` back through `Sum.inl`/`Sum.inr` preimages to
  recover a genuine prime pair `⟨H', T⟩` with `□A ∉ H'`, `A ∉ T`, `boxInv H' ⊆ T`,
  `boxInv T ⊆ H'`, and deductive closure + primeness of each component.
- **Tasks:**
  - [ ] Prove the R2 conservativity lemma: `CS5PairAxiom ⊢ τ_L φ ↔ CS5ModalAxiom ⊢ φ` (modulo
    cross-conditions), so preimages are deductively closed and prime; use
    `Proposition.map_injective` (`Basic.lean:199`) to rule out cross-tag smuggling.
  - [ ] Extract `H' := τ_L⁻¹ T'`, `T := τ_R⁻¹ T'`; discharge the four target properties
    (`□A ∉ H'`, `A ∉ T` from the exclusion set; the two `boxInv` cross-conditions from the
    internalised axioms).
  - [ ] `lake build` the target module.
- **Timing:** 3 hours
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (or `CS5Completeness.lean`)
- **Verification:**
  - The projected pair `⟨H', T⟩` satisfies all four properties sorry-free; `lake build` green.

### Phase 6: Box-Backward Truth-Lemma Case `cs5_box_backward` [NOT STARTED]

- **Goal:** Feed the prime pair witness into the symmetric-tail canonical model's `□`-backward
  case and land `cs5_box_backward` (currently scaffolded sorry-free elsewhere but not in
  `Cslib/`), completing the CS5 truth lemma.
- **Tasks:**
  - [ ] Restate/land `cs5_box_backward` in `CS5Canonical.lean` using the projected pair to exhibit
    a symmetric predecessor omitting `A` for an unwarranted `□A` (bridge via
    `cs5TwoSidedR_iff_cs5Tail` `CS5Canonical.lean:490` and `cs5Tail_symm` `CS5.lean:645`).
  - [ ] Wire `cs5_box_backward` into the CS5 truth lemma's `□`-backward case; confirm no other
    truth-lemma case regresses (R3).
  - [ ] `lake build` the target module.
- **Timing:** 2 hours
- **Depends on:** 5
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`
- **Verification:**
  - `cs5_box_backward` and the CS5 truth lemma compile sorry-free; `lake build Module.Name` green.

### Phase 7: Assemble `cs5_completeness''` and the Soundness-Completeness Biconditional [NOT STARTED]

- **Goal:** Compose the completed truth lemma with `ckvalidFC_completeness` (`CKExtension.lean`)
  and `cs5_axiom_sound''` (`CS5.lean:366`) to deliver `cs5_completeness''` and state
  `cs5_soundness_completeness''`.
- **Tasks:**
  - [ ] State and prove `cs5_completeness'' : CKValidFC cs5FC'' φ → Derivable (@CS5ModalAxiom Atom) φ`
    via the segment canonical model.
  - [ ] State `cs5_soundness_completeness''` (biconditional) combining `cs5_axiom_sound''` with the
    new completeness direction.
  - [ ] If a new `CS5Completeness.lean` file was introduced, run
    `lake exe mk_all --module` to update the barrel import and `lake exe checkInitImports`.
  - [ ] Full-project `lake build`; `#print axioms cs5_completeness''` to confirm no `sorryAx`.
- **Timing:** 1.5 hours
- **Depends on:** 6
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (or `CS5Completeness.lean`)
  - `Cslib.lean` (barrel import, only if a new file was added)
- **Verification:**
  - `cs5_completeness''` and `cs5_soundness_completeness''` compile sorry-free.
  - Full `lake build` green; `#print axioms` shows no `sorryAx`, no new global axioms.

### Phase 8: (Optional) `cs5FCIncest` Labelled-Parity Variant [NOT STARTED]

- **Goal:** Optionally deliver the `cs5FCIncest` variant used by the labelled route for parity.
  This phase may be deferred without blocking task completion (the primary target is Phase 7).
- **Tasks:**
  - [ ] Restate the completeness result over `cs5FCIncest` reusing the Phase 7 machinery.
  - [ ] `lake build` the target module.
- **Timing:** 1 hour
- **Depends on:** 7
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (or `CS5Completeness.lean`)
- **Verification:**
  - The variant compiles sorry-free; `lake build` green. If deferred, mark [PARTIAL] with a note
    that the primary target (Phase 7) is complete.

## Testing & Validation

- [ ] Phase 1 probe: both R1 properties (soundness + `cl`-stability) close sorry-free — the gate.
- [ ] Each phase: scoped `lake build Module.Name` green before committing.
- [ ] `#print axioms cs5_completeness''` reports no `sorryAx` and no unexpected global axioms.
- [ ] Full `lake build` green (no regression in CK/CT/CS4 column or existing CS5 assets).
- [ ] `lake exe checkInitImports` passes (every file imports `Cslib.Init`).
- [ ] `lake lint` and `lake exe lint-style` clean on modified files.
- [ ] If a new file was added: `lake exe mk_all --module` run and `Cslib.lean` updated.

## Artifacts & Outputs

- `specs/551_.../plans/01_native-hilbert-cs5-completeness-plan.md` (this plan)
- `specs/551_.../probes/cs5-pair-combined-atomsum.lean` (Phase 1 R1 de-risking probe)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — `CS5PairAxiom`, projection maps,
  `cl`-stability, primeness, projection, `cs5_box_backward`, `cs5_completeness''`,
  `cs5_soundness_completeness''` (or a new `CS5Completeness.lean` housing the completeness layer)
- `Cslib/Logics/Modal/Basic.lean` (or new helper) — derivability functoriality along
  `Proposition.map`
- `specs/551_.../summaries/01_native-hilbert-cs5-completeness-summary.md` (on completion)

## Rollback/Contingency

- Each phase commits its own green sub-step; a failed phase leaves prior phases intact and the
  build green (prior commits are the rollback points).
- **Phase 1 gate failure (R1):** if the combined axioms cannot be shown simultaneously sound and
  `cl`-stable, mark Phase 1 [BLOCKED], escalate, and do NOT touch library files — the probe is
  disposable and library state is unchanged.
- Per `.claude/rules/plan-compliance.md`, any `.lean` step that cannot be executed as written is
  raised as a [BLOCKED] escalation (what was tried, goal state reached), never silently
  substituted with an alternative approach.
- Full revert: because all library edits are confined to the CS5 metalogic files (plus an optional
  new `CS5Completeness.lean` and its barrel entry), `git revert` of the phase commits restores the
  pre-task state without affecting the CK/CT/CS4 column.
