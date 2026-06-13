# Research Report: Task 182 — Classical-Only Simplification (Team Synthesis)

- **Task**: 182 - Revert Modal/, Temporal/, and Bimodal/ to classical-only with minimal formula constructors
- **Started**: 2026-06-13T00:00:00Z
- **Completed**: 2026-06-13T00:00:00Z
- **Effort**: Team research synthesis (3 teammates)
- **Dependencies**: Tasks 173, 174, 175, 176, 177, 178 (source of and/or propagation)
- **Sources/Inputs**:
  - `specs/182_evaluate_classical_only_simplification/reports/02_teammate-a-findings.md` (git revert strategy)
  - `specs/182_evaluate_classical_only_simplification/reports/02_teammate-b-findings.md` (axiom inheritance and gap analysis)
  - `specs/182_evaluate_classical_only_simplification/reports/02_teammate-c-findings.md` (conservative extension proof strategy)
- **Artifacts**: `specs/182_evaluate_classical_only_simplification/reports/02_team-research.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

- The revert from primitive `and`/`or` constructors to Lukasiewicz abbreviations is feasible and the correct strategy. Commit-level revert is ruled out; a per-file selective restore from named baseline commits is the only safe approach, touching approximately 126 files across 6 phases.
- The Foundations layer is already 100% Lukasiewicz-encoded: every propositional reasoning pattern used in the upper layers (`pairing`, `lce_imp`, `rce_imp`, De Morgan, etc.) is derivable from `ClassicalHilbert` alone, with zero proof gaps requiring new theorems.
- After the revert, helper files (PropositionalHelpers, Perpetuity/Helpers) simplify by roughly 40%: and/or-specific helpers that duplicate Foundations theorems are removed, and wrap/unwrap bridges remain unchanged.
- The three task-182 deliverables have a clear dependency order: the syntactic embedding (FromPropositional) and axiom inheritance cleanup must be completed before conservative extension proofs; the Modal conservative extension can start immediately since all infrastructure exists.
- Total new proof code is small (115-215 lines) concentrated in the Temporal semantic bridge and Bimodal conservative extension; the bulk of the ~126-file change set is pure subtraction (removing and/or arms, axiom constructors, and soundness cases).

---

## Project Context

- **Upstream Dependencies**: Tasks 173 (phase 7 added and/or to FromPropositional), 175/176/177 (propagated primitive constructors into Modal/Temporal/Bimodal), commit `6450ad3e` (orchestration bundled 62 Bimodal/Temporal/Foundations files)
- **Downstream Dependents**: Task 182 deliverables (syntactic embedding, axiom inheritance, conservative extension) block no current tasks beyond themselves
- **Alternative Paths**: Keeping primitive constructors and adding `HasAnd`/`HasOr` to Foundations is the status quo; the revert is the chosen direction
- **Potential Extensions**: Conservative extension proofs could generalize to show CPL decidability inherited through the upper layers

---

## Findings

### 1. Git Revert Strategy (Teammate A)

**Commit-level revert is not viable** due to three compounding factors:

- Tasks 174-178 are interleaved in commit history with overlapping files. Individual task reverts (175, 176, 177) apply cleanly in isolation but leave the codebase broken because the bulk of downstream changes (metalogic, soundness, completeness) arrived in the orchestration commit.
- The orchestration commit `6450ad3e` bundles 62 exclusively-new files (47 Bimodal, 12 Temporal, 3 Foundations) and cannot be reverted cleanly without also destroying task metadata and research reports.
- Task 173 phase 7 (`db2a83bc`) added and/or cases to all three FromPropositional files using the Lukasiewicz encoding; these were later overwritten by tasks 175/176/177 with native constructor mapping. A simple revert would leave those files in an inconsistent state rather than restoring the Lukasiewicz versions.

**Recommended strategy**: Per-file selective restore using `git show <baseline>:<path>`, organized into 6 sequential phases:

| Phase | Scope | Files | Baseline |
|-------|-------|-------|---------|
| A | Formula types (Modal/Temporal/Bimodal) | 3 | `8b2a470d`, `abd1aa15^`, `c38fe3d6^` |
| B | Foundations (Axioms, ProofSystem, TemporalDerived) | 3 | `1852de3a` |
| C | Embeddings (FromPropositional x3, ModalEmbedding, TemporalEmbedding) | 5 | new + `1852de3a` |
| D | Modal layer (Denotation, LogicalEquivalence, ProofSystem, Metalogic) | ~51 | `8b2a470d` |
| E | Temporal layer (Syntax, Metalogic, ProofSystem, Semantics) | ~14 | mixed |
| F | Bimodal layer (Syntax, ProofSystem, Semantics, Metalogic, Theorems) | ~50+ | `1852de3a` |
| **Total** | | **~126** | |

**Critical nuance**: The FromPropositional files (Phase C) cannot simply revert to the pre-173-ph7 baseline because Propositional still has native `and`/`or` constructors. The embeddings must handle 5 PL constructors but map `and`/`or` to upper-layer Lukasiewicz abbreviations (not native constructors). New proofs of semantic coherence are needed for these 3 files; they are straightforward via Peirce's law and classical axioms.

**Key baseline commits**:
- `8b2a470d` — pre-Modal-propagation (last clean baseline for Modal)
- `de59f56b` — parent of task 176 phase 1 (last clean baseline for Temporal syntax)
- `c4e75ad4` — parent of task 177 phase 1 (last clean baseline for Bimodal syntax)
- `1852de3a` — pre-orchestration (last clean baseline for metalogic, Foundations, embeddings)

---

### 2. Axiom Inheritance and Gap Analysis (Teammate B)

**The Foundations layer is already Lukasiewicz-pure.** Every and/or-related theorem (`pairing`, `lce_imp`, `rce_imp`, `combine_imp_conj`, all De Morgan theorems) produces terms using only `HasImp.imp` and `HasBot.bot`. None reference `HasAnd.and` or `HasOr.or`. This means:

- After the revert, when `Formula.and`/`Formula.or` become abbreviations unfolding to `imp (imp phi (imp psi bot)) bot` and `imp (imp phi bot) psi` respectively, the Foundations theorems apply to upper-layer derivations **by definitional equality** — no translation or new bridge code is required.
- The wrap/unwrap bridge pattern (converting between concrete `DerivationTree` types and abstract `InferenceSystem.DerivableIn`) continues to work unchanged.

**Typeclass instances removed per system** (all three systems):
- `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE` — 6 instances removed
- `TemporalBXHilbert` and `BimodalTMHilbert` class declarations drop the `[HasAnd F] [HasOr F]` constraints

**Helper file simplification**:
- `PropositionalHelpers.lean` (Temporal): remove `pairing`, `lceImp`, `rceImp`, `demorganDisjNegBackward` — all delegate to Foundations directly
- `Perpetuity/Helpers.lean` (Bimodal): remove `combineImpConj`, `lceImp`, `rceImp` — same delegation pattern
- `Theorems/Propositional/Core.lean` (Bimodal): `ldi`, `rdi` (use `Axiom.orI1/orI2`) and `lem` (uses `orI1/orI2/Peirce`) must be re-proved using Lukasiewicz encoding

**Identified gaps (all resolvable, no new theorems required)**:

- `mcs_or_resolve` (Bimodal, `MCSProperties.lean:496`) and `temporal_or_resolve_left` (Temporal, `MCS.lean:493`): currently use `OrE` axiom directly. After revert, `or phi psi = imp (neg phi) psi`, so having `neg phi in Omega` and `(neg phi -> psi) in Omega` gives `psi in Omega` via `implication_property`. The re-proof is simpler than the original.
- `provEquiv_or_congr` (Bimodal `LindenbaumQuotient.lean:181-200`): uses `Axiom.orI1/orI2/orE` directly. After revert: `orI1` becomes `raa`, `orI2` becomes `ImplyK`, `orE` derives from `classical_merge` + contraposition — all from `ClassicalHilbert`.
- `lem` (Bimodal `Theorems/Propositional/Core.lean`): after revert, `or A (neg A) = imp (neg A) (neg A)` = `identity (neg A)` — trivially derivable.

**Summary**: The revert is purely subtractive for the axiom and typeclass layer. The handful of helper re-proofs are simpler after the revert, not harder.

---

### 3. Conservative Extension Proof Strategy (Teammate C)

The three conservative extension deliverables have fundamentally different proof complexity:

**Modal K (trivial — all infrastructure exists)**

The proof chain is a 3-line composition of already-proven results:
1. `k_soundness_derivable`: Modal derivability → universal semantic validity
2. `toModal_valid_implies_tautology` (in `FromPropositional.lean`): semantic validity → propositional tautology via single-world model
3. `prop_completeness` (in `Propositional/Metalogic/Completeness.lean`): tautology → CPL derivability

Estimated scope: 5-15 lines. One universe compatibility check needed (`Type*` vs `Type`), but straightforward to resolve by instantiating at universe 0.

**Temporal BX (easy — one new semantic bridge lemma)**

The proof chain is the same Soundness → Bridge → Completeness pattern, but the semantic bridge lemma does not yet exist:

- `temporal_satisfies_toTemporal_iff_evaluate`: structural induction on phi; toTemporal never introduces `untl`/`snce`, so each case is direct (atom, bot, imp, and, or all align). Estimated 15-20 lines.
- `toTemporal_valid_implies_tautology`: single-point temporal model using `Int` (a `LinearOrder` with `NoMaxOrder`/`NoMinOrder` in Mathlib) with constant valuation. Estimated 10-15 lines.
- `temporal_conservative_extension`: 3-line composition. Estimated 5-10 lines.

Total: 30-50 lines.

**Bimodal F (moderate — two competing approaches)**

Bimodal semantics uses `truthAt` with task models, world histories, and domains — significantly more complex than Modal or Temporal. Two approaches:

- **Approach A (recommended)**: Syntactic projection. Show that any Bimodal derivation of a propositional formula (no `box`/`untl`/`snce`) can be projected to a Modal derivation, then use the Modal conservative extension. Structurally similar to the existing `lift_derivation_qfree` in `Bimodal/Metalogic/ConservativeExtension/`. Estimated 80-150 lines.
- **Approach B**: Direct semantic bridge via single-point task model construction. More overhead (constructing a valid TaskFrame, WorldHistory, etc.) but avoids syntactic projection machinery.

The Approach A recommendation holds: it reuses existing infrastructure and avoids duplicating the complexity of the bimodal semantic layer.

**Post-revert simplification for conservative extension**: After the revert, the `toModal` embedding maps `PL.and`/`PL.or` to abbreviations that unfold via `imp`/`bot`. The semantic bridge lemma no longer needs explicit `and`/`or` constructor cases — they reduce through the `imp` case automatically. This slightly simplifies Teammate C's work.

---

## Synthesis

### Conflicts Resolved

**1. FromPropositional handling (A vs C): Apparent conflict, resolved.**

Teammate A says FromPropositional files cannot simply revert to the pre-173-ph7 baseline (since PL keeps native `and`/`or`). Teammate C says the semantic bridge lemma for conservative extension will need to handle `PL.and`/`PL.or` mapping to abbreviations in the upper layers.

Resolution: These are complementary constraints, not contradictory. The Phase C embedding files (FromPropositional) map PL's 5 constructors to upper-layer primitives-plus-abbreviations; the conservative extension semantic bridge then shows the abbreviations preserve semantic meaning. The correct order is: complete Phase C first (Teammate A's work), then write conservative extension proofs (Teammate C's work). Teammate C explicitly confirms this ordering in Section 8 of their findings.

**2. Helper file scope (A vs B): Apparent conflict, resolved.**

Teammate A includes `PropositionalHelpers.lean` and `Perpetuity/Helpers.lean` as files needing update (Phase C / Phase E / Phase F). Teammate B provides precise detail on what those files lose (the and/or-specific helpers) and what the simplified versions look like. No conflict exists — Teammate B's gap analysis provides the detailed content of Teammate A's phase-level file list.

**No genuine contradictions were found** across the three teammates' findings. All three investigated orthogonal angles that interlock cleanly.

### Coverage Gaps

**Gap 1: Bimodal Approach A vs B decision not finalized.**

Teammate C recommends syntactic projection (Approach A) for the Bimodal conservative extension but notes the project-internal `lift_derivation_qfree` as the reference model without fully working out the Bimodal-to-Modal projection lemma. The implementation phase will need to choose an approach early and commit to it. Recommend confirming Approach A is viable by checking whether `lift_derivation_qfree` covers the propositional fragment case, before committing to it.

**Gap 2: Subformulas.lean new content.**

Teammate A notes that `Subformulas.lean` may have new content (added by tasks 176/177) that requires adjustment beyond a simple baseline restore, and flags this as a low-severity risk. Neither Teammate B nor Teammate C addresses Subformulas specifically. This file should be read before Phase E/F execution to confirm whether it needs targeted editing vs. clean baseline restore.

**Gap 3: lake build verification cadence not specified.**

Teammate A's risk assessment identifies "post-revert build failures" as the highest-severity risk and says "must verify full `lake build` after each phase." Neither Teammate B nor Teammate C discusses build verification. The implementation plan should explicitly schedule `lake build` checkpoints after each of the 6 phases, not only at the end.

**Gap 4: `Cslib.Init` import chain after and/or axiom removal.**

After removing `HasAxiomAndI` etc. from the Modal/Temporal/Bimodal proof system instance files, the `Cslib.Init` barrel file must not reference removed symbols. Neither teammate audited the Init barrel explicitly. The CI pipeline's `lake exe checkInitImports` will catch this, but it should be flagged for Phase B/D/E/F verification.

### Recommendations

**R1 (Priority: High)**: Implement in the 6-phase order Teammate A specifies. Do not attempt to reorder or parallelize phases; build integrity depends on bottom-up restoration (formula types first, then foundations, then embeddings, then upper layers).

**R2 (Priority: High)**: Write the Modal conservative extension theorem (Teammate C's Phase 1) concurrently with Phase A (formula type revert). It is the simplest deliverable, validates the overall proof architecture, and is entirely independent of the revert.

**R3 (Priority: High)**: Run `lake build` after completing each of Phases A through F. Do not defer build verification to the end of the 6-phase sequence. The orchestration commit's 62-file scope means incremental verification is the only safe path.

**R4 (Priority: Medium)**: Before starting Phase F (Bimodal), audit `Bimodal/Metalogic/ConservativeExtension/` to confirm whether `lift_derivation_qfree` can be adapted for the propositional-fragment projection (Approach A). If not, fall back to Approach B (direct semantic bridge). Do not defer this decision to the middle of Phase F.

**R5 (Priority: Medium)**: Read `Cslib/Logics/Temporal/Syntax/Subformulas.lean` and the Bimodal equivalent before executing Phases E and F. If they contain task-176/177-introduced content beyond baseline, treat them as Phase C-style files needing targeted editing rather than clean restoration.

**R6 (Priority: Low)**: After all 6 phases and conservative extension proofs are complete, run the full CSLib CI pipeline: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`. The and/or axiom removals may affect the shake dependency graph.

---

## Unified Implementation Roadmap

### Phase Dependencies

```
Phase A (formula types)
    -> Phase B (foundations, parallel-safe after A)
    -> Phase C (embeddings, depends on A+B: PL still has and/or, upper layers now use abbrevs)
        -> Phase D (Modal layer, depends on A+C)
        -> Phase E (Temporal layer, depends on A+C)
        -> Phase F (Bimodal layer, depends on A+C+D+E for cross-embedding correctness)

Modal conservative extension (independent, starts after Phase A+C)
Temporal conservative extension (depends on Phase E completion)
Bimodal conservative extension (depends on Phase F completion + approach decision)
```

### Phase Sizing Estimates

| Phase | Scope | Estimated Effort |
|-------|-------|-----------------|
| A: Formula types | 3 files, direct restore | 0.5 hours |
| B: Foundations | 3 files, direct restore | 0.5 hours |
| C: Embeddings | 5 files; 3 need new proofs | 3-5 hours |
| D: Modal layer | ~51 files, bulk restore + match-case removal | 3-4 hours |
| E: Temporal layer | ~14 files, mixed restore + helper re-proof | 2-3 hours |
| F: Bimodal layer | ~50+ files, largest and most complex | 5-8 hours |
| Modal CE theorem | 5-15 lines, composition | 0.5 hours |
| Temporal CE theorem | 30-50 lines, new bridge | 2-3 hours |
| Bimodal CE theorem | 80-150 lines, projection or semantic | 4-8 hours |
| **Total** | **~126 files, ~115-215 new proof lines** | **~21-33 hours** |

### Critical Path

The critical path runs through Phase F (Bimodal) and then the Bimodal conservative extension. These two items together account for roughly half the total effort. The Bimodal layer's 50+ files and the non-trivial proof of its conservative extension over CPL are the highest-risk items.

---

## Risks and Mitigations

| Risk | Severity | Source | Mitigation |
|------|----------|--------|------------|
| Orchestration commit `6450ad3e` scope means Phase F is by far the largest phase | High | Teammate A | Execute Phase F incrementally; commit after each sub-directory group |
| FromPropositional semantic coherence proofs (Phase C) | Medium | Teammates A+C | Use Peirce's law + `classical_merge`; Foundations Core theorems cover the cases |
| Bimodal conservative extension approach selection | Medium | Teammate C | Audit `lift_derivation_qfree` before starting Phase F; fall back to Approach B if projection fails |
| Post-revert build failures from incomplete phase sequences | High | Teammate A | `lake build` checkpoint after every phase; never attempt next phase on a broken build |
| `mcs_or_resolve` re-proofs in MCS helpers | Low | Teammate B | Re-proof is simpler than original (implication_property replaces orE); low risk |
| Universe mismatch in Modal conservative extension | Low | Teammate C | Instantiate `k_soundness_derivable` at universe 0 explicitly if needed |
| Subformulas.lean new content scope | Low | Teammate A | Read before Phase E/F; may need targeted editing rather than clean restore |

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Git revert strategy — commit archaeology, baseline identification, per-file selective restore plan | Completed | High |
| B | Foundations axiom catalog, Lukasiewicz encoding verification, helper simplification analysis, gap analysis | Completed | High |
| C | Conservative extension proof strategy — Modal/Temporal/Bimodal proof chains, complexity estimates, approach recommendation | Completed | High |

All three teammates completed their assigned angles. No files were missing or malformed.

---

## Appendix

### Key Commit Hashes

| Purpose | Hash |
|---------|------|
| Pre-Modal propagation (last clean Modal baseline) | `8b2a470d` |
| Pre-Temporal propagation (syntax) | parent of `abd1aa15` (= `de59f56b`) |
| Pre-Bimodal propagation (syntax) | parent of `c38fe3d6` (= `c4e75ad4`) |
| Pre-orchestration (metalogic, Foundations, embeddings) | `1852de3a` |
| Pre-all-propagation (FromPropositional original) | `9e83b68b` |
| Orchestration bundled commit | `6450ad3e` (62 files, do not revert wholesale) |
| Task 173 phase 7 (added and/or to embeddings) | `db2a83bc` |

### Lukasiewicz Encoding Reference

```
neg phi      := imp phi bot
and phi psi  := imp (imp phi (imp psi bot)) bot    -- neg(phi -> neg psi)
or phi psi   := imp (imp phi bot) psi              -- neg phi -> psi
iff phi psi  := and (imp phi psi) (imp psi phi)
```

### Foundations Theorems Enabling Upper-Layer Re-Proofs

| Theorem | Location | Replaces |
|---------|----------|---------|
| `pairing` | Combinators.lean | `HasAxiomAndI.andI` |
| `lce_imp` | Core.lean | `HasAxiomAndE1.andE1` |
| `rce_imp` | Core.lean | `HasAxiomAndE2.andE2` |
| `combine_imp_conj` | Combinators.lean | and-intro under implication |
| `classical_merge` | Connectives.lean | `HasAxiomOrE.orE` |
| `demorgan_conj_neg` | Connectives.lean | De Morgan for conjunction |
| `demorgan_disj_neg` | Connectives.lean | De Morgan for disjunction |

### Existing Conservative Extension Infrastructure

- `Propositional/Metalogic/Soundness.lean`: `soundness_tautology` (complete)
- `Propositional/Metalogic/Completeness.lean`: `prop_completeness` + `completeness_iff_tautology` (complete)
- `Modal/Metalogic/Systems/K/Soundness.lean`: `k_soundness_derivable` (complete)
- `Modal/FromPropositional.lean`: `toModal_valid_implies_tautology`, `modal_satisfies_toModal_iff_evaluate` (complete)
- `Temporal/Metalogic/Soundness.lean`: `soundness_thderivable` (complete)
- `Temporal/FromPropositional.lean`: `PL.Proposition.toTemporal` + simp lemmas (complete); semantic bridge **missing**
- `Bimodal/Metalogic/ConservativeExtension/`: F+ over F proof (complete, but different scope — not CPL)
