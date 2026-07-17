# Implementation Plan: Schema-Union Axiom Combinator for Modal ProofSystem Instances

- **Task**: 523 - Replace the 15 hand-written per-system axiom inductives with a compositional schema-union combinator
- **Status**: [BLOCKED]
- **Effort**: ~28-35 hours (Representation A, staged) / ~8-12 hours (Representation B fallback, single PR)
- **Dependencies**: Mandatory Zulip design decision (CONTRIBUTING.md:147); sequence AFTER tasks 520 and 521 (shared InterSystem / minimal-base surface)
- **Research Inputs**: reports/01_schema-union-combinator-blast-radius.md
- **Artifacts**: plans/01_schema-union-staged-rollout.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

> **THIS IS A DESIGN + STAGING DOCUMENT, NOT AN AUTONOMOUSLY-IMPLEMENTABLE PLAN.**
> Per `CONTRIBUTING.md:147`, this task hits BOTH "New cross-cutting abstractions / typeclasses"
> AND "Major refactorings", each of which independently mandates a Zulip design discussion
> *before any implementation*. The FIRST gate (Phase 1) is a Zulip design decision. Every
> implementation phase (Phases 3-7) is `[BLOCKED]` pending that decision AND pending the choice
> between Representation A (schema-union `def`) and Representation B (macro-generated inductives).
> No implementation phase may be dispatched — by `/implement`, `/orchestrate`, or otherwise —
> until Phase 1 resolves on-thread. Do not treat the presence of phases below as license to start.

## Overview

The 15 per-system modal axiom predicates in `Cslib/Logics/Modal/ProofSystem/Instances/*.lean`
(`KAxiom`, `TAxiom`, ..., plus S5's `ModalAxiom` at `Metalogic/DerivationTree.lean:64`) each
re-list a byte-identical 13-constructor propositional + K + diamond-duality core and differ only
in a subset of 5 modal-strength schemata (`modalT/D/B/Four/Five`), forming a clean 18-tag
lattice. The task replaces this duplication with a compositional schema-union combinator so each
system becomes a one-line tag-set declaration. Research establishes the refactor is *tractable
but high-cost and net line-negative* under Representation A: soundness (15 files) and the 524-line
`AxiomSubsumption.lean` are DELETED via generic combinators, not rewritten; completeness,
conservative-extension, Lifting, Modularity, and Conservativity are INSULATED by the already-
uniform `HasAxiom*` typeclass layer; the only irreducible hand cost is `IntToClassical.lean`
(36 sites, genuine intuitionistic->classical derivation work with cross-family coupling) plus the
15 instance files. Definition of done for *this planning artifact*: a Zulip-ready design proposal
plus a validated staged, additive, zero-debt rollout that a follow-up `/plan --hard` can expand
into per-file sub-phases once the design decision lands.

### Research Integration

Integrated from `reports/01_schema-union-combinator-blast-radius.md`:
- **Inventory (§1)**: 13-constructor shared core identical across all 15; 5 differentiator
  schemata; full 18-tag alphabet; S5's `ModalAxiom` = T+4+B (carries `modalB`, NOT `modalFive`).
- **Consumption layer (§2)**: `Foundations/Logic/ProofSystem.lean`'s `HasAxiom*` typeclasses are
  representation-agnostic — the decisive feasibility fact. `DerivationTree` is already
  predicate-parametric, so each `<Sys>Axiom` can become a plain `def : Proposition Atom -> Prop`.
- **Design (§3)**: Representation A = `ModalSchemaTag` enum + `SchemaUnion (S : Finset
  ModalSchemaTag)` combinator; Representation B = macro-generated flat inductives (lower risk,
  preserves elimination form).
- **Blast radius (§4)**: ~32-35 files touched but NET LINE-NEGATIVE under Rep A; the scary "329
  destructuring sites" mostly live in soundness + subsumption and are DELETED, not rewritten.
- **Compositional soundness (§5)**: 13 of 18 tag-validity atoms already exist frame-unconditional
  in `Metalogic/Soundness.lean`; a generic `unionSound` reduces each per-system soundness proof to
  a 3-5 line tag->validity table.
- **Sequencing (§6)**: staged additive rollout (A: introduce alongside + bridges; B: migrate
  soundness; C: replace subsumption; D: IntToClassical + instances, delete inductives last), each
  stage CI-green and zero-debt, sequenced AFTER 520/521.
- **Coordination (§7)**: Zulip design discussion is mandatory before implementation; draft message
  reproduced verbatim in Appendix A.

### Prior Plan Reference

No prior plan. This is plan version 1 for task 523.

### Roadmap Alignment

No `roadmap_path` provided and no `roadmap_flag` set for this dispatch; ROADMAP.md not consulted.
No roadmap phases added.

## Goals & Non-Goals

**Goals**:
- Produce a Zulip-ready design proposal presenting Representation A vs Representation B with the
  honest cost/risk breakdown, and obtain a maintainer design decision before any code changes.
- Define a staged, additive, zero-debt rollout in which every intermediate commit is CI-green and
  no stage requires `sorry` or a new axiom.
- Preserve every public theorem name (`k_soundness`, `KAxiom_implies_TAxiom`, the `HasAxiom*`
  instances) stable or behind deprecated aliases across all intermediate states.
- Collapse the 24 boilerplate `XAxiom_implies_YAxiom` subsumption lemmas to `Finset.subset` facts
  and the 15 per-system soundness case-splits to a generic `unionSound` (Representation A).
- Keep the sequencing constraint explicit: land AFTER tasks 520 and 521.

**Non-Goals**:
- Autonomous implementation. This plan is NOT to be executed by `/implement` or `/orchestrate`
  until the Zulip gate (Phase 1) resolves.
- Touching the out-of-scope intuitionistic/minimal modal axiom families (`IKModalAxiom`,
  `MKModalAxiom`, `CKModalAxiom`, `IS5ModalAxiom`, `MTModalAxiom`, ...) beyond keeping their
  existing witness-construction call sites into the classical `KAxiom`/`ModalAxiom` valid.
- Changing the `HasAxiom*` typeclass hierarchy in `Foundations/Logic/ProofSystem.lean` (it is the
  insulation layer; changing it would defeat the entire feasibility argument).
- Deciding the design unilaterally: Representation A vs B and the S5 `ModalAxiom` unification
  question are for the Zulip thread, not this document.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Zulip declines the abstraction or prefers Rep B | H | M | Present BOTH representations on-thread; Rep B (macro inductives) delivers the literal DRY goal with near-zero blast radius as a documented fallback (Phase 1 outcome branch). |
| Merge churn against tasks 520/521 (shared `Modularity.lean` / minimal-base surface) | H | H | Hard sequencing gate (Phase 2): do not start Stage A until 520 and 521 have landed; re-verify the InterSystem surface before Stage A. |
| Cross-family coupling breaks: intuitionistic/minimal families construct/consume classical `KAxiom`/`ModalAxiom` witnesses (`⟨.ax _ _ h⟩`) | H | M | Keep the bridge lemmas from Stage A (`SchemaUnion sysTags φ ↔ <Sys>Axiom φ`) live until Stage D; migrate `IntToClassical.lean` by hand (Phase 6) BEFORE deleting inductives (Phase 7); never delete an inductive while any witness-construction site still targets it. |
| Elimination-form change (`cases ... with | implyK` -> `obtain ⟨t, ht, hφ⟩; fin_cases t`) ripples further than mapped | M | M | Additive rollout: introduce combinator ALONGSIDE inductives with bridge equivalences (Stage A) so old and new coexist; migrate one file at a time, each independently CI-green. |
| A stage cannot close sorry-free | M | L | Zero-debt discipline: if any phase cannot close sorry-free, mark THAT phase `[BLOCKED]` with the open goal state recorded, rather than committing a `sorry` or deferring silently. |
| `unionSound` frame-condition plumbing for the 5 differentiator tags is harder than the 3-5 line estimate | M | L | 13 of 18 tags reuse existing frame-unconditional atoms from `Metalogic/Soundness.lean`; only 5 carry a frame condition, each already proved inline in the current per-system soundness files — port those proofs into the tag->validity table. |
| Deleting S5's `ModalAxiom` breaks `MCS.lean` / `Metalogic/Soundness.lean` / `Bimodal/.../ModalConservativity.lean` | M | M | Treat S5 unification as an explicit Zulip question (Appendix A, question 2); if kept separate, leave `ModalAxiom` in place and only bridge it; delete only if fully superseded and all 3 referencing files re-routed. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5, 6 | 3 |
| 5 | 7 | 4, 5, 6 |

Phases within the same wave can execute in parallel. NOTE: Phases 2-7 are `[BLOCKED]` pending the
Phase 1 Zulip design decision; the wave table describes the intended post-decision execution
order, not an authorization to run.

---

### Phase 1: Zulip design decision gate [NOT STARTED]

**Goal**: Obtain an explicit maintainer design decision on Zulip before any implementation, per
the mandatory `CONTRIBUTING.md:147` coordination requirement (this task hits both "cross-cutting
abstraction" and "major refactoring").

**Tasks**:
- [ ] Post the Zulip proposal (Appendix A) to the CSLib channel: suggest topic "Proposal —
      schema-union combinator for the 15 modal axiom predicates".
- [ ] Solicit a steer on the three explicit questions: (1) `def SchemaUnion` (Rep A) vs
      macro-generated inductives (Rep B); (2) whether S5's `ModalAxiom` should be unified into the
      same scheme or kept separate; (3) preferred landing order relative to the in-flight
      InterSystem / minimal-base work (tasks 520/521).
- [ ] Record the design decision (chosen representation + S5 disposition + sequencing) as an
      appendix or follow-up note before unblocking downstream phases.
- [ ] If maintainers prefer minimal churn -> select Representation B; the downstream Stage A-D
      phases below are Representation-A-shaped and would be replaced by a single macro-generation
      phase (see Contingency).

**Timing**: Human-coordination-bound (asynchronous; not agent-executable). Allow days for thread
response, not hours.

**Depends on**: none

**Files to modify**: none (coordination only; may append a decision record to this plan or a new
`plans/02_*.md` once the thread resolves).

**Verification**:
- A maintainer response on-thread selecting a representation and sequencing exists and is recorded.
- Until then, this phase stays `[NOT STARTED]` and all downstream phases stay `[BLOCKED]`.

---

### Phase 2: Sequencing prerequisite verification (after 520 & 521) [BLOCKED]

**Goal**: Confirm tasks 520 and 521 have landed and re-baseline the InterSystem / minimal-base
surface before introducing the combinator, avoiding rework the research explicitly warns against.

**Tasks**:
- [ ] Confirm task 521 (minimal-canonical trio deletion; MK routed through generic
      `mkvalidFC_completeness`) has landed and shrunk the minimal/InterSystem surface.
- [ ] Confirm task 520 (composite conservativity bridges in `Modularity.lean`) has landed.
- [ ] Re-grep the current constructor-construction and destructuring site counts under
      `Cslib/Logics/Modal/Metalogic/` to re-baseline the blast radius against the post-520/521 tree
      (research baseline: ~354 construction sites, ~329 destructuring sites).
- [ ] Re-confirm `IntToClassical.lean` cross-family witness-construction sites and the S5
      `ModalAxiom` referencing files (`MCS.lean`, `Metalogic/Soundness.lean`,
      `Bimodal/.../ModalConservativity.lean`) are unchanged or note deltas.

**Timing**: ~1-2 hours (verification + re-baseline).

**Depends on**: 1

**Files to modify**: none (verification only; may update this plan's blast-radius numbers).

**Verification**:
- 520 and 521 are in terminal/landed state.
- Re-baselined site counts recorded; no unexpected new coupling introduced by 520/521.

---

### Phase 3: Stage A — introduce combinator alongside inductives + bridge lemmas [BLOCKED]

**Goal**: Add `ModalSchemaTag`, `.Holds`, `SchemaUnion`, the generic `subsumption` lemma, and the
generic `unionSound` combinator ALONGSIDE the existing 15 inductives, with per-system bridge
equivalences — zero downstream blast, CI stays green. (Representation A.)

**Tasks**:
- [ ] Define `inductive ModalSchemaTag` (18 tags) with `deriving DecidableEq`.
- [ ] Define `ModalSchemaTag.Holds : ModalSchemaTag -> Proposition Atom -> Prop` (per-tag
      formula-level meaning, existential over metavariables).
- [ ] Define `SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom -> Prop :=
      fun χ => ∃ t ∈ S, t.Holds χ`.
- [ ] Prove the generic subsumption lemma: `Sᴬ ⊆ Sᴮ -> SchemaUnion Sᴬ φ -> SchemaUnion Sᴮ φ`.
- [ ] State and prove `unionSound` (per §5): `unionSound (S) (m) (hfc : ∀ t ∈ S,
      FrameValidatesTag m t) {φ} (h : SchemaUnion S φ) (w) : Satisfies m w φ`, reusing the 13
      frame-unconditional atoms in `Metalogic/Soundness.lean` and porting the 5 frame-conditioned
      proofs.
- [ ] Define the per-system tag sets (`kCore`, and one `Finset` per system) and prove bridge
      equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` for each of the 15 systems.

**Timing**: ~4-6 hours (definitions + generic lemmas + 15 bridge equivalences). During
post-Zulip `/plan --hard`, split the 15 bridge equivalences into per-file sub-phases (~100-500
lines/run each).

**Depends on**: 2

**Files to modify**:
- New file under `Cslib/Logics/Modal/ProofSystem/` (or `Metalogic/`) - `ModalSchemaTag`,
  `SchemaUnion`, `subsumption`, `unionSound`, per-system tag sets, bridge equivalences.
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` - reuse existing atoms (read-only or minor
  `FrameValidatesTag` glue).

**Verification**:
- `lake build` green with the combinator present and all 15 bridge lemmas proved sorry-free.
- No existing inductive or downstream file modified yet (additive-only).

---

### Phase 4: Stage B — migrate per-system soundness to `unionSound` [BLOCKED]

**Goal**: Replace each `Systems/*/Soundness.lean` case-split with a `unionSound` call fed by that
system's tag->validity table (net deletion), one file at a time.

**Tasks**:
- [ ] For each of the 15 systems, rewrite `<sys>_axiom_sound` to route through `unionSound` +
      the per-system tag->validity table (13 frame-unconditional atoms reused; up to 5
      frame-conditioned obligations ported from the existing inline proofs).
- [ ] Keep public soundness theorem names (`k_soundness`, ...) stable; use the Stage A bridge
      lemma where a caller still expects the inductive form.
- [ ] Commit each file green individually (per commit-per-green-substep mandate).

**Timing**: ~6-8 hours (15 files). Split into per-file sub-phases in the post-Zulip `/plan --hard`.

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean` (15 files) - case-splits replaced by
  `unionSound` (net deletion).

**Verification**:
- `lake build` green after each file migration.
- Per-system soundness theorems still discharge with identical public names; no `sorry`.

---

### Phase 5: Stage C — replace `AxiomSubsumption.lean` with `Finset.subset` facts [BLOCKED]

**Goal**: Collapse the 24 hand-written `XAxiom_implies_YAxiom` lemmas (~524 lines) to
`Finset.subset`-backed facts via the generic Stage A subsumption lemma; update the few call sites.

**Tasks**:
- [ ] Replace each of the 24 subsumption lemmas with a `Finset.subset` fact fed to the generic
      `subsumption` lemma (preserve public lemma names or provide deprecated aliases).
- [ ] Update the (few) call sites in `Lifting.lean` / `Modularity.lean` that reference subsumption
      lemma names (insulated: only call-site NAMES may change, not structure).
- [ ] Verify the deliberately-omitted `KB5 -> S5` edge stays omitted (S5 = T+4+B, not
      `modalFive`).

**Timing**: ~3-4 hours.

**Depends on**: 3 (independent of Phase 4; runs parallel in Wave 4)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` - 24 lemmas -> `Finset.subset`
  facts (net deletion).
- `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean`, `Modularity.lean` - call-site name
  updates only.

**Verification**:
- `lake build` green; all 24 subsumption facts proved via the generic lemma; no `sorry`.
- No spurious `KB5 -> S5` edge introduced.

---

### Phase 6: Stage D-1 — hand-migrate `IntToClassical.lean` witness constructions [BLOCKED]

**Goal**: Perform the irreducible hand-migration of the 36 constructor-destructuring sites in
`IntToClassical.lean` (genuine intuitionistic->classical derivation work + cross-family witness
construction), keeping every classical `KAxiom`/`ModalAxiom` witness-construction site valid.

**Tasks**:
- [ ] Migrate each of the ~36 sites that destructure or construct classical axiom witnesses to the
      `SchemaUnion` form (or via the Stage A bridge lemma where a witness is constructed as
      `⟨.ax _ _ h⟩`).
- [ ] Preserve cross-family coupling: intuitionistic/minimal families (`IKModalAxiom`, etc.) that
      construct in-scope classical witnesses must still typecheck.
- [ ] Do NOT delete any inductive in this phase (deletion is Phase 7, after all migrations green).

**Timing**: ~6-8 hours (genuine derivation work, not renaming). Split into sub-phases post-Zulip.

**Depends on**: 3 (independent of Phases 4/5; runs parallel in Wave 4)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean` (~36 sites).

**Verification**:
- `lake build` green; no `sorry`; cross-family witness-construction sites still valid.

---

### Phase 7: Stage D-2 — swap 15 instance registrations, delete inductives [BLOCKED]

**Goal**: Rewrite the 15 `HasAxiom*` instance registrations in `Instances/*.lean` to build their
fields from `SchemaUnion`, then delete the 15 inductives (and S5's `ModalAxiom` if the Zulip
decision unified it) — the terminal, once-everything-else-is-green step.

**Tasks**:
- [ ] For each of the 15 instance files, discharge each `HasAxiom*` field from `SchemaUnion` (via
      the Stage A bridge where convenient), replacing witness constructions like `KAxiom.implyK _`.
- [ ] Delete the 15 `<Sys>Axiom` inductives once no construction/destructuring site targets them.
- [ ] Delete or retain S5's `ModalAxiom` (`Metalogic/DerivationTree.lean:64`) per the Phase 1
      decision; if deleted, re-route `MCS.lean`, `Metalogic/Soundness.lean`,
      `Bimodal/.../ModalConservativity.lean`.
- [ ] Remove now-dead bridge lemmas that were only scaffolding (keep any that remain public API).
- [ ] Final full `lake build`; confirm the refactor is net line-negative as predicted.

**Timing**: ~4-6 hours.

**Depends on**: 4, 5, 6

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}.lean`
  (15 files) - instance registrations rewritten; inductives deleted.
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` - `ModalAxiom` disposition (conditional).
- `MCS.lean`, `Metalogic/Soundness.lean`, `Bimodal/.../ModalConservativity.lean` - conditional
  re-route if S5 unified.

**Verification**:
- Full `lake build` green; no `sorry`; no new axiom (`lean_verify` on key theorems).
- All 15 inductives removed; net line count negative vs baseline.
- All previously-public theorem/instance names resolve (directly or via retained aliases).

---

## Testing & Validation

- [ ] `lake build` green after EACH phase (additive/staged discipline — every intermediate commit
      CI-green).
- [ ] No `sorry` and no new `axiom` at any intermediate state (`lean_verify` spot-checks on
      `k_soundness`, `s5` soundness, representative `XAxiom_implies_YAxiom` facts).
- [ ] Public API surface unchanged: `k_soundness`, `KAxiom_implies_TAxiom`, the `HasAxiom*`
      instances resolve at every stage (stable names or deprecated aliases).
- [ ] The deliberately-absent `KB5 -> S5` subsumption edge remains absent.
- [ ] Final tree is net line-negative vs the pre-refactor baseline (Rep A success criterion).
- [ ] CSLib CI pipeline / `/vet` clean before any PR.

## Artifacts & Outputs

- plans/01_schema-union-staged-rollout.md (this design + staging document)
- A recorded Zulip design decision (appended here or as plans/02_*.md) — produced by Phase 1
- Post-decision, a `/plan --hard` expansion splitting Stages A-D into per-file sub-phases
- summaries/NN_{short-slug}-summary.md (only after implementation, post-Zulip)

## Rollback/Contingency

- **If Zulip declines or prefers minimal risk -> Representation B.** Replace Phases 3-7 with a
  single macro-generation phase: a `macro`/elaborator (`derive_modal_axiom KAxiom [implyK, ...,
  modalK, ...]`) that emits the flat inductives with constructor names AND elimination form
  preserved (near-zero downstream blast radius, landable in one PR). Forgoes the set-theoretic
  subsumption elegance; the macro can optionally also generate the O(edges) subsumption lemmas.
- **If a stage cannot close sorry-free**: mark that phase `[BLOCKED]` with the open goal state
  recorded; do NOT commit a `sorry` or a new axiom (zero-debt mandate).
- **Additive-rollout revert**: because the combinator is introduced alongside the inductives with
  bridge lemmas, any stage can be reverted independently by dropping its commit — the prior stage
  remains CI-green. Deletion of inductives (Phase 7) is deliberately last and reversible until
  merged.
- **Sequencing revert**: if 520/521 have not landed at Phase 2, hold at `[BLOCKED]`; do not start
  Stage A against a soon-to-change InterSystem surface.

## Appendix A: Zulip Coordination Message (draft, from research report §7)

> **Topic (suggest #CSLib channel):** Proposal — schema-union combinator for the 15 modal axiom
> predicates
>
> Hi all. The 15 per-system modal axiom predicates in
> `Cslib/Logics/Modal/ProofSystem/Instances/*.lean` (`KAxiom`, `TAxiom`, …, plus S5's
> `ModalAxiom`) each re-list an identical 13-constructor propositional+K+diamond-duality core and
> differ only in a subset of 5 modal-strength schemata (`modalT/D/B/Four/Five`). I'd like to
> replace the hand-written inductives with a compositional **schema-union combinator**
> `SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop`, so each system is a
> one-line tag-set declaration.
>
> **Motivation.** `DerivationTree` is already predicate-parametric and the `HasAxiom*`
> consumption layer in `Foundations/Logic/ProofSystem.lean` is already uniform, so the abstract
> layer is feasible today. Two immediate payoffs: the 24 boilerplate `XAxiom_implies_YAxiom`
> subsumption lemmas in `AxiomSubsumption.lean` (~524 lines) collapse to `Finset.subset` facts,
> and the 15 per-system soundness case-splits collapse to a generic `unionSound` fed by a
> per-tag validity table (13 of 18 tags are already frame-unconditional atoms in
> `Metalogic/Soundness.lean`).
>
> **Cost/risk I want input on.** It changes the *elimination form* of the axiom predicates. The
> soundness + subsumption sites are net-deleted, and completeness/conservativity go through the
> typeclass layer (insulated), but `InterSystem/IntToClassical.lean` (~36 sites, genuine
> intuitionistic→classical derivation work) needs hand migration, and there's cross-family
> coupling with the intuitionistic/minimal axiom families. I'm proposing a **staged, additive**
> rollout (introduce combinator alongside the inductives with bridge lemmas, migrate soundness,
> then subsumption, then instances, deleting the inductives last) so every intermediate commit is
> CI-green and zero-debt, sequenced **after** the in-flight minimal-base dedup and composite
> conservativity work touching the same files.
>
> **Alternative** if you'd prefer minimal churn: a `macro`-generated flat-inductive form that
> keeps constructor names and elimination form (near-zero downstream blast radius) at the price
> of the set-theoretic subsumption elegance.
>
> Would appreciate a steer on (1) `def SchemaUnion` vs macro-generated inductives, (2) whether
> the S5 `ModalAxiom` should be unified into the same scheme or kept, and (3) preferred landing
> order relative to the ongoing InterSystem/minimal-base work. Happy to write up a short design
> note / issue if useful.
