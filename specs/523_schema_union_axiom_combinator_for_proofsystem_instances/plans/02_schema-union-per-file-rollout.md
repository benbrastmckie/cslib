# Implementation Plan: Schema-Union Axiom Combinator for Modal ProofSystem Instances (v2)

- **Task**: 523 - Replace the 15 hand-written per-system axiom inductives with a compositional schema-union combinator
- **Status**: [PLANNED]
- **Effort**: ~24-32 hours (Representation A, staged additive rollout across ~20 agent runs)
- **Dependencies**: Tasks 520 and 521 (both COMPLETED — sequencing prerequisite satisfied)
- **Research Inputs**: reports/01_schema-union-combinator-blast-radius.md
- **Artifacts**: plans/02_schema-union-per-file-rollout.md (this file); plans/01_schema-union-staged-rollout.md (superseded design + staging doc, retained for history)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The design decision for this task is **RESOLVED** (user, 2026-07-18). Representation **A**
(schema-tag union) is selected; the mandatory Zulip design gate that blocked plan v1 is
**lifted**. This plan (v2) expands the v1 staging document's Stages A-D into concrete,
per-file / per-small-group sub-phases, each sized to one agent run (~100-500 lines of output,
per hard-mode H8 phase sizing).

The 15 per-system modal axiom predicates in `Cslib/Logics/Modal/ProofSystem/Instances/*.lean`
(`KAxiom`, `TAxiom`, ..., plus S5's `ModalAxiom` at `Metalogic/DerivationTree.lean:64`) each
re-list a byte-identical 13-constructor propositional + K + diamond-duality core and differ only
in a subset of 5 modal-strength schemata (`modalT/D/B/Four/Five`), forming a clean 18-tag
alphabet. The refactor introduces:

- `inductive ModalSchemaTag` (18 tags, `deriving DecidableEq`)
- `ModalSchemaTag.Holds : ModalSchemaTag → Proposition Atom → Prop` (per-tag formula meaning)
- `def SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop := fun χ => ∃ t ∈ S, t.Holds χ`

so each of the 14 `<Sys>Axiom` predicates plus S5 becomes a one-line `SchemaUnion` over its tag
set. The 24 `XAxiom_implies_YAxiom` subsumption lemmas collapse to one generic subsumption lemma
+ `Finset.subset` facts; the 15 per-system soundness case-splits collapse to a per-tag validity
table + one generic `unionSound` combinator.

**Resolved design parameters** (from the 2026-07-18 decision, binding on all phases):

- Representation = **A** (schema-tag union). S5 generalizes toward `Modal.ModalAxiom` as the
  existing pattern (S5 = T+4+B; carries `modalB`, NOT `modalFive`).
- ACCEPT the elimination-form change downstream: `cases … with | ctor` / `match` becomes
  `obtain ⟨t, ht, hφ⟩ := h; fin_cases t <;> …`.
- ACCEPT the ~36 genuine intuitionistic→classical hand-rewrites in
  `InterSystem/IntToClassical.lean`.
- Keep the intuitionistic/minimal families (`IKModalAxiom`, `MKModalAxiom`, `CKModalAxiom`,
  `IS5ModalAxiom`, `MTModalAxiom`) OUT of scope — but keep their witness-construction sites into
  classical `KAxiom`/`ModalAxiom` valid.
- Additive, zero-debt staging: every intermediate commit CI-green, no `sorry`, no new axiom.
  Every public theorem name stays stable or lives behind a deprecated alias across all
  intermediate states.

### Preserved Assets

The following work is complete and must not regress:

| Component | Reference | Status | Verified |
|-----------|-----------|--------|----------|
| Task 520 — composite conservativity bridges in `Modularity.lean` | `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean` | [COMPLETED] | 2026-07-18 (sequencing prereq) |
| Task 521 — minimal-canonical trio deletion; MK routed through generic `mkvalidFC_completeness` | InterSystem / minimal-base surface | [COMPLETED] | 2026-07-18 (sequencing prereq) |
| 15 per-system axiom inductives (live until Phase 8) | `Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}.lean` | live | must stay live until all consumers migrated |
| S5 `ModalAxiom` inductive (live until Phase 8) | `Cslib/Logics/Modal/Metalogic/DerivationTree.lean:64` | live | referenced by MCS/Soundness/ModalConservativity |
| Public API names (`k_soundness`, `s5_*` soundness, `KAxiom_implies_TAxiom`, the 24 subsumption lemmas, the `HasAxiom*` instances) | across Metalogic/InterSystem | stable | must resolve at every intermediate stage (stable or deprecated alias) |
| 13 frame-unconditional schema-validity atoms | `Cslib/Logics/Modal/Metalogic/Soundness.lean` (`Satisfies.implyK_axiom`, …, `diaDualityBack`) | reused | not modified — read-only reuse by `unionSound` |
| `HasAxiom*` typeclass hierarchy (the insulation layer) | `Cslib/Foundations/Logic/ProofSystem.lean` | untouched | representation-agnostic; changing it defeats feasibility |

### Source-to-Implementation Mapping (Tier: code — the existing tree is ground truth)

| Load-bearing decision | Source citation |
|-----------------------|-----------------|
| `DerivationTree` is predicate-parametric, so each `<Sys>Axiom` may become a `def : Proposition Atom → Prop` | report §3; `Lifting.lean` `liftDerivation`/`Derivable_mono` (`h_sub : ∀ φ, Axioms1 φ → Axioms2 φ`) |
| `HasAxiom*` layer is representation-agnostic — the load-bearing feasibility fact | report §2; `Cslib/Foundations/Logic/ProofSystem.lean` |
| 13 of 18 tags reuse existing frame-unconditional validity atoms; only 5 carry a frame condition | report §5; `Cslib/Logics/Modal/Metalogic/Soundness.lean` |
| S5 = T+4+B (carries `modalB`, not `modalFive`) → the `KB5 → S5` subsumption edge stays omitted | report §1.2, §1.3; `AxiomSubsumption.lean` (edge deliberately absent) |
| `IntToClassical.lean` is the irreducible hand cost (36 sites, genuine derivation work + cross-family witness construction `⟨.ax _ _ h⟩`) | report §4, §4.1; `InterSystem/IntToClassical.lean` (774 lines) |

### Research Integration

Integrated from `reports/01_schema-union-combinator-blast-radius.md`: inventory (§1), the
representation-agnostic consumption layer (§2), Representation A design (§3), the net-line-negative
blast radius (§4), compositional soundness via `unionSound` (§5), and the staged additive
sequencing (§6). §7's Zulip coordination is now a pre-PR courtesy heads-up (design already
decided), not a gate.

### Prior Plan Reference

Supersedes plans/01_schema-union-staged-rollout.md. That document was a design + staging artifact
whose Phase 1 was a mandatory Zulip design gate with Phases 2-7 `[BLOCKED]`. The gate resolved to
Representation A; this v2 lifts the block and expands Stages A-D into per-file sub-phases. v1 is
retained for history only.

### Roadmap Alignment

No `roadmap_path` provided for this dispatch; ROADMAP.md not consulted. No roadmap phases added.

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the v1 risk table, the research
blast-radius findings, and the resolved design decision.

**Do NOT**:
- Delete ANY `<Sys>Axiom` inductive (or S5's `ModalAxiom`) before Phase 8. Every deletion waits
  until no construction/destructuring site targets it. Deleting an inductive while a
  witness-construction site (`⟨.ax _ _ h⟩` producing a `KAxiom`) still targets it breaks the
  build. Inductive deletion is strictly the LAST step (Phase 8).
- Commit any `sorry` or introduce any new `axiom` at any intermediate state. If a phase cannot
  close sorry-free, mark THAT phase `[BLOCKED]` with the open goal state recorded — do not defer
  silently or commit debt.
- Modify the `HasAxiom*` typeclass hierarchy in `Cslib/Foundations/Logic/ProofSystem.lean`. It is
  the insulation layer; changing it defeats the entire feasibility argument.
- Rename or drop any public theorem/instance name without leaving a `@[deprecated]` alias.
  `k_soundness`, the S5 soundness lemmas, `KAxiom_implies_TAxiom` (and the 23 sibling subsumption
  lemmas), and the `HasAxiom*` instances must resolve at every intermediate stage.
- Introduce a `KB5 → S5` subsumption edge. S5 = T+4+B, not `modalFive`; the omission is
  deliberate and correct.
- Touch the intuitionistic/minimal axiom families (`IKModalAxiom`, `MKModalAxiom`, `CKModalAxiom`,
  `IS5ModalAxiom`, `MTModalAxiom`) beyond keeping their existing witness-construction call sites
  into the classical `KAxiom`/`ModalAxiom` valid.
- Batch multiple files into a single un-verified commit. Each per-file / per-group sub-phase
  builds green and commits on its own (commit-per-green-substep mandate).

**MUST preserve**:
- Every public theorem/instance name (stable or deprecated alias) at every stage.
- CI-green build after every sub-phase.
- The 13 frame-unconditional validity atoms in `Metalogic/Soundness.lean` (read-only reuse).
- Cross-family witness-construction validity in `IntToClassical.lean` throughout.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- Representation A (schema-tag `def` + `Finset` union) — Representation B (macro-generated
  inductives) is rejected and lives only in Rollback/Contingency as a break-glass fallback.
- S5 generalizes toward `Modal.ModalAxiom`; its disposition (unify vs. keep + bridge) is decided
  at Phase 8 per the migration state, not re-litigated mid-flight.
- The elimination-form change and the ~36 `IntToClassical.lean` hand-rewrites are ACCEPTED costs,
  not risks to be avoided.

## Goals & Non-Goals

**Goals**:
- Introduce `ModalSchemaTag`, `.Holds`, `SchemaUnion`, a generic subsumption lemma, and a generic
  `unionSound` combinator alongside the existing inductives (zero downstream blast).
- Prove the 15 bridge equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` (per-group sub-phases).
- Migrate the 15 per-system soundness proofs to `unionSound` (per-group sub-phases).
- Collapse `AxiomSubsumption.lean`'s 24 lemmas to `Finset.subset` facts.
- Hand-migrate `IntToClassical.lean`'s ~36 sites (per-cluster sub-phases).
- Swap the 15 instance registrations to build `HasAxiom*` fields from `SchemaUnion`, then delete
  the 15 inductives (+ `ModalAxiom` if fully superseded) strictly last.
- Every intermediate commit CI-green, zero-debt; net line-negative final tree.

**Non-Goals**:
- Representation B (macro inductives) — rejected by the design decision (break-glass only).
- Touching the intuitionistic/minimal modal axiom families beyond keeping their in-scope
  classical witness sites valid.
- Changing the `HasAxiom*` typeclass hierarchy in `Foundations/Logic/ProofSystem.lean`.
- Re-opening the S5 unification or elimination-form questions.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cross-family coupling breaks: intuitionistic/minimal families construct classical `KAxiom`/`ModalAxiom` witnesses (`⟨.ax _ _ h⟩`) | H | M | Keep Stage-A bridge lemmas live until Phase 8; migrate `IntToClassical.lean` (Phase 6) BEFORE swapping instances (Phase 7) and deleting inductives (Phase 8); never delete an inductive while a witness-construction site targets it. |
| Elimination-form change ripples beyond the mapped sites | M | M | Additive rollout: combinator lands ALONGSIDE inductives with bridge equivalences (Phases 1-3); migrate one file/group at a time, each independently CI-green; the bridge lets old and new coexist. |
| A sub-phase cannot close sorry-free | M | L | Zero-debt discipline: mark that sub-phase `[BLOCKED]` with the open goal recorded; never commit a `sorry` or new axiom. |
| `unionSound` frame-condition plumbing for the 5 differentiator tags harder than estimated | M | L | 13 of 18 tags reuse existing frame-unconditional atoms; only 5 carry a frame condition, each already proved inline in the current per-system soundness files — port those proofs into the tag→validity table (Phase 2). |
| Deleting S5's `ModalAxiom` breaks `MCS.lean` / `Metalogic/Soundness.lean` / `Bimodal/…/ModalConservativity.lean` | M | M | Phase 8 decides disposition from the migration state: if not fully superseded, leave `ModalAxiom` in place and only bridge it; delete only after all 3 referencing files are re-routed and green. |
| Large blast-radius PR surprises maintainers | L | L | Non-blocking pre-PR Zulip heads-up (courtesy, see below) before the user runs `/pr`; design is already decided, so this is a notice, not a gate. |

## Implementation Phases

**Dependency Analysis (wave map)**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5, 6 | 2 & 3 (Phase 4); 1 & 3 (Phase 5); 3 (Phase 6) |
| 4 | 7 | 3, 6 |
| 5 | 8 | 4, 5, 6, 7 |

Phases within the same wave may execute in parallel (distinct file territories). Sub-phases
(N.M) within a phase are sequential unless noted. New files proposed below (`SchemaUnion.lean`,
`SchemaSoundness.lean`, `SchemaBridges.lean`) are recommended locations; the implementer confirms
exact placement/imports at Phase 1 and keeps them consistent thereafter.

---

### Phase 1: Core scaffolding — `ModalSchemaTag` + `SchemaUnion` + generic subsumption [NOT STARTED]

**Goal**: Land the tag alphabet, per-tag `Holds`, the `SchemaUnion` combinator, and the single
generic subsumption lemma in a new file — purely additive, no existing file altered.

**Tasks**:
- [ ] Define `inductive ModalSchemaTag` (18 tags: `implyK implyS efq peirce modalK modalT modalD
      modalB modalFour modalFive andI andE1 andE2 orI1 orI2 orE diaDualityFwd diaDualityBack`) with
      `deriving DecidableEq`.
- [ ] Define `ModalSchemaTag.Holds : ModalSchemaTag → Proposition Atom → Prop` — one existential
      clause per tag (formula-level meaning; cite report §3 code block for the shapes).
- [ ] Define `SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop := fun χ => ∃ t ∈ S, t.Holds χ`.
- [ ] Prove the generic subsumption lemma: `Sᴬ ⊆ Sᴮ → SchemaUnion Sᴬ φ → SchemaUnion Sᴮ φ`.

**Estimated output**: ~150-250 lines. **Depends on**: none.

**Files to modify**:
- NEW `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` (proposed location).

**Verification**:
- Scoped `lake build Cslib.Logics.Modal.ProofSystem.SchemaUnion` green.
- Zero-`sorry` check on the new file (`grep -n sorry` empty; `lean_verify` on `SchemaUnion`,
  the subsumption lemma).
- No existing file modified.
- **Done when**: `SchemaUnion`, `ModalSchemaTag.Holds`, and the generic subsumption lemma compile
  sorry-free and no downstream file changed.

---

### Phase 2: `unionSound` combinator + per-tag validity table [NOT STARTED]

**Goal**: Provide the generic soundness combinator and the 18-entry tag→validity table (13
frame-unconditional atoms reused; 5 frame-conditioned proofs ported), so Phase 4 can delete the
per-system case-splits.

**Tasks**:
- [ ] Define `FrameValidatesTag m t` (per-tag semantic obligation) relating a `ModalSchemaTag` to
      the relevant frame condition (reflexive/serial/symmetric/transitive/Euclidean for the 5
      differentiators; unconditional for the other 13).
- [ ] State and prove `unionSound (S) (m) (hfc : ∀ t ∈ S, FrameValidatesTag m t) {φ}
      (h : SchemaUnion S φ) (w) : Satisfies m w φ` (report §5 signature).
- [ ] Populate the 13 frame-unconditional entries by reusing the existing atoms in
      `Metalogic/Soundness.lean` (`Satisfies.implyK_axiom`, …, `diaDualityBack`) — read-only reuse.
- [ ] Port the 5 frame-conditioned validity proofs (`modalT/D/B/Four/Five`) from the current
      inline per-system soundness proofs into the table.

**Estimated output**: ~200-350 lines. **Depends on**: 1.

**Files to modify**:
- NEW `Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean` (proposed location).
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` — read-only reuse (no edits, or minimal
  `FrameValidatesTag` glue only if unavoidable).

**Verification**:
- Scoped `lake build Cslib.Logics.Modal.Metalogic.SchemaSoundness` green.
- Zero-`sorry`; `lean_verify` on `unionSound`.
- **Done when**: `unionSound` compiles sorry-free and every one of the 18 tag-validity obligations
  is discharged.

---

### Phase 3: Per-system tag sets + 15 bridge equivalences [NOT STARTED]

**Goal**: Define `kCore` and the 15 per-system `Finset ModalSchemaTag` tag sets, and prove the
bridge equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` — additive; the inductives stay live.
Split into per-group sub-phases (~4 systems each, one agent run per group).

Per-system tag sets (report §1.3):
`K:{modalK} T:{modalK,modalT} D:{modalK,modalD} B:{modalK,modalB} K4:{modalK,modalFour}
K5:{modalK,modalFive} K45:{modalK,modalFour,modalFive} S4:{modalK,modalT,modalFour}
S5:{modalK,modalT,modalFour,modalB} TB:{modalK,modalT,modalB} KB5:{modalK,modalB,modalFive}
D4:{modalK,modalD,modalFour} D5:{modalK,modalD,modalFive} D45:{modalK,modalD,modalFour,modalFive}
DB:{modalK,modalD,modalB}` — each unioned with the 13-tag `kCore` (propositional + and/or + diaDuality).

**Sub-phase 3.1 — `kCore` + K, T, D, B** [NOT STARTED]
- [ ] Define `kCore` (the 13 shared tags) and the K/T/D/B tag sets.
- [ ] Prove bridges `SchemaUnion kTags φ ↔ KAxiom φ`, and the T/D/B analogues.
- Estimated output: ~150-250 lines.

**Sub-phase 3.2 — K4, K5, K45, S4** [NOT STARTED]
- [ ] Define the four tag sets; prove the four bridge equivalences.
- Estimated output: ~150-250 lines.

**Sub-phase 3.3 — S5, TB, KB5** [NOT STARTED]
- [ ] Define the three tag sets; prove bridges. For S5, bridge `SchemaUnion s5Tags φ ↔ ModalAxiom φ`
      (S5 = T+4+B; generalize toward `Modal.ModalAxiom` per the decision).
- Estimated output: ~120-200 lines.

**Sub-phase 3.4 — D4, D5, D45, DB** [NOT STARTED]
- [ ] Define the four tag sets; prove the four bridge equivalences.
- Estimated output: ~150-250 lines.

**Depends on**: 1 (needs `SchemaUnion`; independent of Phase 2).

**Files to modify**:
- NEW `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean` (proposed location) — imports the 15
  instance files + `SchemaUnion.lean`; holds tag sets + bridges. Existing instance files unchanged.

**Verification (each sub-phase)**:
- Scoped `lake build Cslib.Logics.Modal.ProofSystem.SchemaBridges` green after each group.
- Zero-`sorry`; each bridge proved as a genuine `↔` (no `sorry`, no `admit`).
- No instance file modified.
- **Done when**: all 15 bridge equivalences compile sorry-free; commit per group.

---

### Phase 4: Migrate 15 per-system soundness proofs to `unionSound` [NOT STARTED]

**Goal**: Replace each `Systems/*/Soundness.lean` case-split with a `unionSound` call fed by that
system's tag→validity table (net deletion), one small group per agent run. Public soundness
theorem names stay stable; use the Phase 3 bridge where a caller still expects the inductive form.

**Sub-phase 4.1 — K, T, D, B** [NOT STARTED]
- [ ] Rewrite `<sys>_axiom_sound` (K/T/D/B) through `unionSound` + the per-system tag→validity table.
- Files: `Systems/{K,T,D,B}/Soundness.lean`. Estimated output: ~120-220 lines net (deletion-heavy).

**Sub-phase 4.2 — K4, K5, K45, S4** [NOT STARTED]
- [ ] Rewrite the four soundness proofs through `unionSound`.
- Files: `Systems/{K4,K5,K45,S4}/Soundness.lean`. Estimated output: ~120-220 lines.

**Sub-phase 4.3 — S5, TB, KB5** [NOT STARTED]
- [ ] Rewrite the three soundness proofs; keep the S5 public soundness names stable.
- Files: `Systems/{S5,TB,KB5}/Soundness.lean`. Estimated output: ~100-200 lines.

**Sub-phase 4.4 — D4, D5, D45, DB** [NOT STARTED]
- [ ] Rewrite the four soundness proofs through `unionSound`.
- Files: `Systems/{D4,D5,D45,DB}/Soundness.lean`. Estimated output: ~120-220 lines.

**Depends on**: 2 (needs `unionSound`) and 3 (needs bridges + tag sets).

**Verification (each sub-phase)**:
- Scoped `lake build` of each touched `Systems/*/Soundness.lean` module green after the group.
- Public soundness theorem names unchanged (or deprecated alias); zero-`sorry`.
- **Done when**: every migrated soundness theorem discharges via `unionSound` with its original
  public name and no `sorry`; commit per group.

---

### Phase 5: Replace `AxiomSubsumption.lean` with `Finset.subset` facts [NOT STARTED]

**Goal**: Collapse the 24 hand-written `XAxiom_implies_YAxiom` lemmas (~524 lines) to
`Finset.subset`-backed facts via the Phase 1 generic subsumption lemma, then update the few call
sites. Net deletion.

**Sub-phase 5.1 — 24 subsumption facts** [NOT STARTED]
- [ ] Replace each of the 24 subsumption lemmas with a `Finset.subset` fact fed to the generic
      `subsumption` lemma; preserve each public lemma name (or provide a `@[deprecated]` alias).
- [ ] Verify the deliberately-omitted `KB5 → S5` edge stays omitted (S5 = T+4+B, not `modalFive`).
- File: `InterSystem/AxiomSubsumption.lean`. Estimated output: ~120-220 lines net (deletion-heavy).

**Sub-phase 5.2 — call-site name updates** [NOT STARTED]
- [ ] Update the (few) call sites in `Lifting.lean` / `Modularity.lean` that reference subsumption
      lemma names — call-site NAMES only, no structural change (these files are insulated).
- Files: `InterSystem/Lifting.lean`, `InterSystem/Modularity.lean`. Estimated output: ~30-80 lines.

**Depends on**: 1 (generic subsumption) and 3 (tag sets). Independent of Phase 4.

**Verification**:
- Scoped `lake build` of `AxiomSubsumption`, `Lifting`, `Modularity` green.
- All 24 subsumption facts proved via the generic lemma; zero-`sorry`; no `KB5 → S5` edge.
- **Done when**: `AxiomSubsumption.lean` contains no hand-written per-edge `match`, all 24 names
  resolve, and dependent files build; commit per sub-phase.

---

### Phase 6: Hand-migrate `IntToClassical.lean` (~36 sites) [NOT STARTED]

**Goal**: Perform the irreducible hand-migration of the ~36 constructor/destructuring sites in
`IntToClassical.lean` (774 lines) — genuine intuitionistic→classical derivation work plus
cross-family witness construction. NO inductive is deleted here. Split into per-cluster sub-phases;
the implementer partitions the ~36 sites into three balanced clusters at the start of 6.1 and
records the partition so 6.2/6.3 have fixed, non-overlapping scope.

**Sub-phase 6.1 — cluster 1 (destructuring sites, ~first third)** [NOT STARTED]
- [ ] Migrate the first ~12 sites: `cases … with | ctor` → `obtain ⟨t, ht, hφ⟩ := h; fin_cases t <;> …`
      (or via the Phase 3 bridge where cleaner).
- Estimated output: ~120-260 lines.

**Sub-phase 6.2 — cluster 2 (destructuring sites, ~second third)** [NOT STARTED]
- [ ] Migrate the next ~12 sites.
- Estimated output: ~120-260 lines.

**Sub-phase 6.3 — cluster 3 (witness-construction sites, `⟨.ax _ _ h⟩`)** [NOT STARTED]
- [ ] Migrate the remaining ~12 sites, prioritizing the cross-family witness constructions that
      build classical `KAxiom`/`ModalAxiom` witnesses; keep every out-of-scope intuitionistic/minimal
      call site typechecking (via the Phase 3 bridge).
- Estimated output: ~120-260 lines.

**Depends on**: 3 (needs bridges). Independent of Phases 4/5.

**Files to modify**: `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`.

**Verification (each sub-phase)**:
- Scoped `lake build Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical` green after each cluster.
- Zero-`sorry`; cross-family witness-construction sites still valid; no inductive deleted.
- **Done when**: all ~36 sites migrated across the three clusters, file builds sorry-free, and no
  `<Sys>Axiom`/`ModalAxiom` inductive has been removed; commit per cluster.

---

### Phase 7: Swap 15 instance registrations to `SchemaUnion` [NOT STARTED]

**Goal**: Rewrite each `HasAxiom*` instance registration in `Instances/*.lean` to discharge its
fields from `SchemaUnion` (via the Phase 3 bridge where convenient), replacing witness
constructions like `KAxiom.implyK _`. Inductives are NOT deleted here (that is Phase 8). Split into
per-cluster sub-phases (~4 files each).

**Sub-phase 7.1 — K, T, D, B** [NOT STARTED]
- [ ] Rewrite the `HasAxiom*` instance fields in `Instances/{K,T,D,B}.lean` to build from `SchemaUnion`.
- Estimated output: ~150-260 lines.

**Sub-phase 7.2 — K4, K5, K45, S4** [NOT STARTED]
- [ ] Rewrite `Instances/{K4,K5,K45,S4}.lean`.
- Estimated output: ~150-260 lines.

**Sub-phase 7.3 — S5, TB, KB5** [NOT STARTED]
- [ ] Rewrite `Instances/{S5,TB,KB5}.lean` (S5 discharges via the `ModalAxiom` bridge).
- Estimated output: ~120-220 lines.

**Sub-phase 7.4 — D4, D5, D45, DB** [NOT STARTED]
- [ ] Rewrite `Instances/{D4,D5,D45,DB}.lean`.
- Estimated output: ~150-260 lines.

**Depends on**: 3 (bridges) and 6 (IntToClassical migrated first, so instance-side changes never
strand a live cross-family witness site).

**Files to modify**: `Cslib/Logics/Modal/ProofSystem/Instances/{15 files}.lean` (registrations
only; inductive definitions untouched until Phase 8).

**Verification (each sub-phase)**:
- Scoped `lake build` of each touched `Instances/*.lean` module green after the group.
- Every `HasAxiom*` instance still resolves under its original name; zero-`sorry`; inductives still present.
- **Done when**: all 15 instances discharge their fields from `SchemaUnion` and build sorry-free,
  with the inductives still defined; commit per group.

---

### Phase 8: Delete the 15 inductives (+ `ModalAxiom` disposition), finalize [NOT STARTED]

**Goal**: The terminal, once-everything-else-is-green step: remove the now-unused inductives,
resolve S5's `ModalAxiom`, drop dead scaffolding bridges, and confirm the net-line-negative result.

**Tasks**:
- [ ] Confirm (grep) that no construction/destructuring site targets any `<Sys>Axiom` inductive.
- [ ] Delete the 14 `<Sys>Axiom` inductives from `Instances/*.lean`.
- [ ] Resolve S5's `ModalAxiom` (`Metalogic/DerivationTree.lean:64`): if fully superseded by
      `s5Tags`/`SchemaUnion`, re-route `MCS.lean`, `Metalogic/Soundness.lean`,
      `Bimodal/…/ModalConservativity.lean` and delete it; otherwise keep it and retain only its
      bridge (record which branch was taken and why).
- [ ] Remove now-dead bridge lemmas that were pure scaffolding; keep any that remain public API
      (with `@[deprecated]` alias if a name was public).
- [ ] Final full `lake build`; `lean_verify` on `k_soundness`, an S5 soundness lemma, and a
      representative subsumption fact to confirm no `sorry` and no new axiom.
- [ ] Confirm net line count is negative vs. the pre-refactor baseline.

**Estimated output**: ~150-300 lines of net deletion + re-route edits. **Depends on**: 4, 5, 6, 7.

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}.lean`
  (inductive definitions removed).
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` — `ModalAxiom` disposition (conditional).
- `MCS.lean`, `Metalogic/Soundness.lean`, `Bimodal/…/ModalConservativity.lean` — conditional
  re-route if S5 unified.

**Verification**:
- Full `lake build` green; zero-`sorry`; no new axiom (`lean_verify`).
- All 15 inductives removed (or `ModalAxiom` retained per the recorded branch); every prior public
  theorem/instance name resolves (direct or via alias).
- Net line count negative vs. baseline.
- **Done when**: the whole library builds sorry-free with the inductives gone and public API intact.

---

### Pre-PR user step (non-blocking courtesy — NOT a phase, NOT a gate)

Before the user runs `/pr` on the completed branch, post a brief Zulip heads-up to the #CSLib
channel noting the large-blast-radius (but net-line-negative) landing of the schema-union
combinator, so maintainers are not surprised by the diff. **The design decision has already
landed** — this is a courtesy notice, not a design gate, and it does not block any implementation
phase. A ready-to-post draft is in plans/01 Appendix A (trim to a "landing shortly" note). This
step is the user's to perform; agents do not post to Zulip or create the PR.

## Testing & Validation

- [ ] Scoped `lake build` green after EVERY sub-phase (additive/staged discipline — every
      intermediate commit CI-green).
- [ ] No `sorry` and no new `axiom` at any intermediate state (`grep -n sorry` on touched files;
      `lean_verify` spot-checks on `k_soundness`, an S5 soundness lemma, a representative
      `XAxiom_implies_YAxiom` fact, and `unionSound`).
- [ ] Public API surface unchanged: `k_soundness`, the S5 soundness lemmas, `KAxiom_implies_TAxiom`
      (+ 23 siblings), the `HasAxiom*` instances resolve at every stage (stable or deprecated alias).
- [ ] The deliberately-absent `KB5 → S5` subsumption edge remains absent.
- [ ] Final full `lake build` green and net line-negative vs. the pre-refactor baseline.
- [ ] CSLib CI pipeline / `/vet` clean before the user runs `/pr`.

## Artifacts & Outputs

- plans/02_schema-union-per-file-rollout.md (this per-file execution plan)
- plans/01_schema-union-staged-rollout.md (superseded design + staging doc; Appendix A Zulip draft)
- NEW Lean files (proposed): `ProofSystem/SchemaUnion.lean`, `Metalogic/SchemaSoundness.lean`,
  `ProofSystem/SchemaBridges.lean`
- summaries/NN_{short-slug}-summary.md (after implementation completes)

## Rollback/Contingency

- **Additive-rollout revert**: because the combinator is introduced alongside the inductives with
  bridge lemmas (Phases 1-3), any later sub-phase can be reverted independently by dropping its
  commit — the prior green state is preserved. Inductive deletion (Phase 8) is deliberately last
  and reversible until the PR merges.
- **If a sub-phase cannot close sorry-free**: mark that sub-phase `[BLOCKED]` with the open goal
  state recorded; never commit a `sorry` or new axiom (zero-debt mandate).
- **S5 disposition branch**: if deleting `ModalAxiom` at Phase 8 proves to strand a consumer, take
  the "keep + bridge" branch instead of forcing the deletion — the refactor still succeeds with
  `ModalAxiom` retained behind its bridge.
- **Break-glass (Representation B)**: only if Representation A hits an unforeseen hard blocker
  (e.g. `fin_cases`/`Finset` elaboration cost proves intractable at scale), fall back to
  macro-generated flat inductives (v1 Contingency). This reverses the settled design decision and
  therefore requires explicit user sign-off — it is NOT an in-flight option.
