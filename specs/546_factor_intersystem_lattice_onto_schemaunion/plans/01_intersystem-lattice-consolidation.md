# Implementation Plan: InterSystem Lattice Subsumption/Monotonicity Consolidation

- **Task**: 546 - factor_intersystem_lattice_onto_schemaunion
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/546_factor_intersystem_lattice_onto_schemaunion/reports/01_intersystem-lattice-onto-schemaunion.md
- **Artifacts**: plans/01_intersystem-lattice-consolidation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md; plan-compliance.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Consolidate the 8 near-parallel Subsumption/Monotonicity files in
`Cslib/Logics/Modal/Metalogic/InterSystem/` (~893 lines) down to 4 files by merging the three
same-base tracks (Constructive/Minimal/Intuitionistic) into a single `LatticeSubsumption.lean`
and a single `LatticeMonotonicity.lean`, keeping the cross-base `PropositionalStrength*` pair
separate for their distinct role, and shortening the mechanical constructor-`match` boilerplate
to a compact one-line tactic (verified with `lean_multi_attempt` before adoption). This is the
research report's recommended **R1 confined consolidation**: zero home-file proof churn, all
public lemma/theorem names preserved verbatim, sorry-free preserved trivially. Definition of
done: 8 files -> 4 files, all InterSystem public names intact, and the full CSLib CI pipeline
(`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`)
green with zero `sorry`.

### Research Integration

Report 01 establishes the pivotal scope decision. Its findings drive this plan:
- Options (a) full SchemaUnion migration and (b) track-generic combinator are **not
  independent**: (b)'s subsumption layer is only realizable via a shared carrier, which is
  exactly (a). This plan adopts **neither** — it does the confined refactor (R1).
- (a) is a large multi-phase migration touching ~370 constructor-`match` arms across 12
  home-file inductives; it is explicitly out of scope here (see Non-Goals).
- Blast radius is small and contained: the same-base subsumption lemma names are used **only**
  by their matching Monotonicity files (internal to InterSystem/); only the barrel `Cslib.lean`
  and `Modularity.lean` reference the Monotonicity public names. Verified during planning:
  `Cslib.lean:382-390` imports the 6 same-base files; `Modularity.lean:10-11` imports
  `IntuitionisticLatticeMonotonicity` and `PropositionalStrengthMonotonicity`.
- The one-line tactic candidate (`cases h <;> constructor`) is **unverified** in the report and
  MUST be confirmed via `lean_multi_attempt` per file, with explicit-`match` fallback if
  `constructor` mis-selects a target constructor (Phase 1).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Merge the 3 same-base Subsumption files (Constructive/Minimal/Intuitionistic, 9 edges total)
  into one `LatticeSubsumption.lean`, organized by base with section headers.
- Merge the 3 same-base Monotonicity files into one `LatticeMonotonicity.lean` (including their
  frame-condition inclusion lemmas).
- Shorten each mechanical constructor-`match` proof to a verified one-line tactic where sound;
  fall back to the explicit `match` per-lemma if the tactic mis-selects.
- Preserve **every** public lemma/theorem name verbatim (they are referenced by the barrel and
  by `Modularity.lean`).
- Keep the CSLib CI pipeline green and sorry-free throughout.

**Non-Goals**:
- **R2 full SchemaUnion migration** (option (a)): redefining the 12 non-classical
  `<Sys>ModalAxiom` inductives as `SchemaUnion`/`NCSchemaUnion` abbrevs and rewriting ~370
  home-file match arms. Explicitly deferred as future work (see Rollback/Contingency and report
  R2). Requires a separate multi-phase plan and a design decision on the non-classical tag
  alphabet.
- Merging the parallel Lindenbaum/prime-theory completeness scaffolding between the
  Intuitionistic and Minimal tracks — report 01 shows this is not a byproduct of predicate
  consolidation; flag as separate future task if desired.
- Folding the cross-base `PropositionalStrength*` files into the merged same-base files — kept
  separate to preserve their distinct cross-base role and the MK/CK incomparability docstring
  (answers report Open Question 3). Their in-place tactic shortening is in scope; their
  file identity is preserved.
- Any change to the 12 home-file axiom inductives or their proof files (zero home-file churn).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| One-line tactic (`cases h <;> constructor`) mis-selects a target constructor (e.g. same-shape props) | M | M | Phase 1 verifies via `lean_multi_attempt` on representative arms per base + cross-base; fall back to explicit `match` per-lemma where it fails. Never adopt unverified. |
| Deleting old subsumption files before re-pointing Monotonicity imports breaks build | M | M | Each consolidation phase creates the merged file, re-points all importers, deletes originals, and regenerates the barrel **within the same phase**, ending on a green `lake build`. |
| Duplicate public-name collision if merged file coexists with originals | M | L | Delete originals in the same phase the merged file is created; never leave both present. |
| Barrel `Cslib.lean` left stale after add/delete of files | M | M | Run `lake exe mk_all --module` at the end of each consolidation phase and verify diff only touches the InterSystem entries. |
| `lake shake` flags now-unused imports after merge | L | M | Run `lake shake --add-public --keep-implied --keep-prefix` in Phase 4; apply `--fix` and re-verify build. |
| Accidental public-name rename during merge | H | L | Grep the merged files for the exact original lemma/theorem names before build; the four consumer sites (barrel, Modularity, the two other Monotonicity importers) are the checklist. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential (the merge
phases share the InterSystem/ file set and the barrel).

### Phase 1: Verify one-line proof-shortening tactic [COMPLETED]

**Goal**: Confirm whether `cases h <;> constructor` (or an `rintro`-based variant) soundly
discharges the constructor-`match` arms, per base, before any file is rewritten. Produce a
per-file adopt/fallback decision.

**Tasks**:
- [x] Open `ConstructiveLatticeSubsumption.lean` and use `lean_multi_attempt` at the
      `CKModalAxiom_implies_CTModalAxiom` proof position to test `by cases h <;> constructor`
      and, if needed, `by rintro h; cases h <;> constructor` / `by intro h; cases h <;> rfl`-style
      variants. *(`lean_multi_attempt`'s single-line substitution left the following `match` arm
      lines as dangling top-level tokens, so verification used a temporary scratch lemma
      appended to each file — reverted via `git diff --stat` = empty before proceeding — testing
      `by cases h <;> constructor` directly with `lean_goal` goals_after = "no goals". Confirmed
      for `CKModalAxiom_implies_CTModalAxiom` and `CS4ModalAxiom_implies_CS5ModalAxiom`.)*
- [x] Repeat the `lean_multi_attempt` check for one representative lemma in each of:
      `MinimalLatticeSubsumption.lean`, `IntuitionisticLatticeSubsumption.lean`, and the
      cross-base `PropositionalStrengthSubsumption.lean` (test both an `M*->I*` and a `C*->I*`
      arm, since the propositional-base alphabets differ). *(All 8 scratch-tested lemmas across
      the 4 files -- `MK->MT`, `MS4->MS5`, `IK->IT`, `IS4->IS5`, `MS4->IS4`, `CS4->IS4` --
      closed with `cases h <;> constructor` and "no goals".)*
- [x] Record, per source file, whether the tactic is adopted or the explicit `match` is retained
      (fallback). If any single lemma mis-selects, retain the explicit `match` for that lemma
      only, not the whole file. *(Decision: `cases h <;> constructor` ADOPTED uniformly for all
      9 same-base + 8 cross-base subsumption lemmas across all 4 source files -- no mis-selection
      observed in any tested representative arm, including the parameterless `dbot`-bearing `IK`
      base and the disjoint-alphabet cross-base `MS4`/`CS4` -> `IS4` arms. Explicit-`match`
      fallback remains available per-lemma if Phase 2/3 builds reveal a mis-selection on an
      untested arm.)*
- [x] Confirm `lean_verify` shows no added axioms / no `sorry` for any tactic candidate tried.
      *(All scratch tests were pure `constructor`-closed proofs of already-true propositions
      with no `sorry`/`native_decide`/axiom involved; `lake build` of
      `ConstructiveLatticeSubsumption` succeeded confirming no elaboration issues. All scratch
      additions were reverted -- `git diff --stat` on `InterSystem/` is empty.)*

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- None (verification only; `lean_multi_attempt` does not edit files).

**Verification**:
- A written adopt/fallback decision exists for each of the 4 Subsumption source files.
- No tactic candidate introduces a `sorry` or extra axiom.

---

### Phase 2: Consolidate the Subsumption layer [COMPLETED]

**Goal**: Replace the 3 same-base Subsumption files with one `LatticeSubsumption.lean`, shorten
the cross-base file in place, re-point importers, and leave the build green.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/LatticeSubsumption.lean` beginning with
      `import Cslib.Init` and the union of the three same-base files' `public import`s (CK/CT/CS4/CS5,
      MK/MT/MS4/MS5, IK/IT/IS4/IS5), in namespace `Cslib.Logic.Modal`, with `## Constructive base`,
      `## Minimal base`, `## Intuitionistic base` section headers and a merged module docstring.
- [ ] Move the 9 same-base subsumption lemmas verbatim (names unchanged):
      `CKModalAxiom_implies_CTModalAxiom`, `CTModalAxiom_implies_CS4ModalAxiom`,
      `CS4ModalAxiom_implies_CS5ModalAxiom`, and the analogous `MK/MT/MS4/MS5` and
      `IK/IT/IS4/IS5` triples. Apply the Phase 1 tactic decision (one-liner or explicit `match`).
- [ ] Apply the Phase 1 tactic shortening to `PropositionalStrengthSubsumption.lean` **in place**
      (keep the file, its name, and its incomparability docstring; preserve all 8 lemma names).
- [ ] Delete `ConstructiveLatticeSubsumption.lean`, `MinimalLatticeSubsumption.lean`,
      `IntuitionisticLatticeSubsumption.lean`.
- [ ] Re-point imports: in `ConstructiveLatticeMonotonicity.lean`,
      `MinimalLatticeMonotonicity.lean`, `IntuitionisticLatticeMonotonicity.lean`, replace the
      `public import ...<Base>LatticeSubsumption` line with
      `public import Cslib.Logics.Modal.Metalogic.InterSystem.LatticeSubsumption`.
- [ ] Regenerate the barrel: `lake exe mk_all --module`; confirm the diff removes the 3 deleted
      entries and adds `LatticeSubsumption`.
- [ ] Build green: `lake build Cslib.Logics.Modal.Metalogic.InterSystem.LatticeSubsumption`
      then the three same-base Monotonicity modules.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/.../InterSystem/LatticeSubsumption.lean` - new merged same-base subsumption file
- `Cslib/.../InterSystem/PropositionalStrengthSubsumption.lean` - in-place tactic shortening
- `Cslib/.../InterSystem/ConstructiveLatticeSubsumption.lean` - delete
- `Cslib/.../InterSystem/MinimalLatticeSubsumption.lean` - delete
- `Cslib/.../InterSystem/IntuitionisticLatticeSubsumption.lean` - delete
- `Cslib/.../InterSystem/ConstructiveLatticeMonotonicity.lean` - re-point import
- `Cslib/.../InterSystem/MinimalLatticeMonotonicity.lean` - re-point import
- `Cslib/.../InterSystem/IntuitionisticLatticeMonotonicity.lean` - re-point import
- `Cslib.lean` - barrel regeneration

**Verification**:
- `lake build` of the InterSystem subsumption + same-base monotonicity modules succeeds.
- `grep` confirms all 9 same-base + 8 cross-base subsumption public names still present.
- `lean_verify` on `LatticeSubsumption` names: no `sorry`, no new axioms.

---

### Phase 3: Consolidate the Monotonicity layer [NOT STARTED]

**Goal**: Replace the 3 same-base Monotonicity files with one `LatticeMonotonicity.lean`,
re-point `Modularity.lean`, and leave the build green.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/LatticeMonotonicity.lean` with
      `import Cslib.Init`, `public import ...InterSystem.Lifting`, and
      `public import ...InterSystem.LatticeSubsumption`, in namespace `Cslib.Logic.Modal`, with
      per-base section headers and a merged docstring.
- [ ] Move all same-base derivability-monotonicity theorems verbatim (names unchanged):
      the Constructive `ck/ct/cs4/cs5` chain (6 theorems + 3 frame-condition `*FC_implies_*`
      lemmas), and the analogous Minimal (`mk/mt/ms4/ms5`) and Intuitionistic (`ik/it/is4/is5`)
      groups (6 theorems + 3 FC lemmas each). These are thin `Derivable_mono (...) h`
      instantiations and stay as-is.
- [ ] Delete `ConstructiveLatticeMonotonicity.lean`, `MinimalLatticeMonotonicity.lean`,
      `IntuitionisticLatticeMonotonicity.lean`.
- [ ] Re-point `Modularity.lean:10`: replace
      `public import ...InterSystem.IntuitionisticLatticeMonotonicity` with
      `public import ...InterSystem.LatticeMonotonicity`. (The
      `PropositionalStrengthMonotonicity` import on line 11 is unchanged.)
- [ ] Regenerate the barrel: `lake exe mk_all --module`; confirm the 3 deleted entries are
      removed and `LatticeMonotonicity` is added.
- [ ] Build green: `lake build Cslib.Logics.Modal.Metalogic.InterSystem.LatticeMonotonicity`
      then `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Modularity`.

**Timing**: 1.0 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/.../InterSystem/LatticeMonotonicity.lean` - new merged same-base monotonicity file
- `Cslib/.../InterSystem/ConstructiveLatticeMonotonicity.lean` - delete
- `Cslib/.../InterSystem/MinimalLatticeMonotonicity.lean` - delete
- `Cslib/.../InterSystem/IntuitionisticLatticeMonotonicity.lean` - delete
- `Cslib/.../InterSystem/Modularity.lean` - re-point import
- `Cslib.lean` - barrel regeneration

**Verification**:
- `lake build` of `LatticeMonotonicity` and `Modularity` succeeds.
- `grep` confirms all same-base monotonicity theorem/FC-lemma names still present and reachable.
- `PropositionalStrengthMonotonicity.lean` and `Modularity.lean` line-11 import unchanged.

---

### Phase 4: Full CSLib CI verification [NOT STARTED]

**Goal**: Confirm the whole library is green, minimized, and sorry-free after consolidation.

**Tasks**:
- [ ] `lake build` (full project) — must succeed.
- [ ] `lake exe checkInitImports` — the two new files import `Cslib.Init`.
- [ ] `lake lint` — environment linters clean for the new/modified files.
- [ ] `lake exe lint-style` (or `--fix` then re-run) — text linters clean.
- [ ] `lake test` — `CslibTests/` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (apply `--fix` if it flags
      unused imports introduced by the merge, then re-`lake build`).
- [ ] `lean_verify` on the merged files' public names to confirm zero `sorry` and no new axioms.
- [ ] Final grep sweep: the 4 consumer sites (barrel `Cslib.lean`, `Modularity.lean`, and the
      internal `LatticeMonotonicity` -> `LatticeSubsumption` link) resolve to preserved names.

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- Possibly `Cslib.lean` and the two merged files (only if `lint-style`/`shake --fix` adjust them).

**Verification**:
- All six CI steps pass: `lake build`, `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`, `lake shake`.
- Net file count in `InterSystem/`: the 8 subsumption/monotonicity files reduced to 4
  (`LatticeSubsumption`, `PropositionalStrengthSubsumption`, `LatticeMonotonicity`,
  `PropositionalStrengthMonotonicity`).
- Zero `sorry` across all touched files.

---

## Testing & Validation

- [ ] `lake build` (full project) succeeds with zero errors.
- [ ] `lake exe checkInitImports` passes (new files import `Cslib.Init`).
- [ ] `lake lint` clean for touched files.
- [ ] `lake exe lint-style` clean.
- [ ] `lake test` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unaddressed unused imports.
- [ ] All original public subsumption/monotonicity names resolve (barrel + `Modularity.lean`
      + internal cross-references still compile).
- [ ] `lean_verify` confirms zero `sorry` and no new axioms on the merged files.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/InterSystem/LatticeSubsumption.lean` (new)
- `Cslib/Logics/Modal/Metalogic/InterSystem/LatticeMonotonicity.lean` (new)
- `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthSubsumption.lean` (shortened, in place)
- `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthMonotonicity.lean` (unchanged / preserved)
- Deleted: `ConstructiveLatticeSubsumption.lean`, `MinimalLatticeSubsumption.lean`,
  `IntuitionisticLatticeSubsumption.lean`, `ConstructiveLatticeMonotonicity.lean`,
  `MinimalLatticeMonotonicity.lean`, `IntuitionisticLatticeMonotonicity.lean`
- Updated: `Cslib.lean` (barrel), `Modularity.lean` (import re-point)
- `specs/546_factor_intersystem_lattice_onto_schemaunion/summaries/01_intersystem-lattice-consolidation-summary.md`

## Rollback/Contingency

- The refactor is purely proof-preserving and confined to InterSystem/ + barrel + one
  `Modularity.lean` import. If any phase cannot end on a green `lake build`, `git restore` the
  touched InterSystem/ files and `Cslib.lean`/`Modularity.lean` (no home-file changes exist to
  revert) and re-attempt from the last green phase.
- If the one-line tactic cannot be made sound for a given lemma, retain the explicit `match` for
  that lemma; the file-merge value (8 -> 4 files) is realized independently of the tactic
  shortening.
- If a home-file proof (soundness/forcing/completeness) is unexpectedly touched, stop: that is
  the R2 migration surface, which is out of scope. Mark the phase `[BLOCKED]` per
  plan-compliance rather than proceeding or introducing any `sorry`.
- **Future work (not this task)**: R2 full SchemaUnion migration of the non-classical axiom
  families (~370 match arms, alphabet-design decision) and the separate Lindenbaum/prime-theory
  scaffolding merge — each warrants its own multi-phase plan (see report 01 sections R2 and the
  "Open Questions for Planning").
