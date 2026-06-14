# Research Report: Task #179

**Task**: modal_primitive_diamond — Add diamond (dia) as a primitive constructor to Modal.Proposition
**Date**: 2026-06-14
**Mode**: Team Research (4 teammates, standard mode)
**Completed**: 2026-06-14

---

## Summary

- The task description contains a factual error: the current `Modal.Proposition` type has only `{atom, bot, imp, box}` as primitives, not `{atom, bot, imp, and, or, box}`. All four teammates independently confirmed this. `neg`, `and`, `or`, and `diamond` are all `abbrev`-derived using the Lukasiewicz convention.
- Adding primitive `dia` is architecturally justified now: it is the consistent application of the same primitive-first design philosophy already applied to `and`/`or` in propositional logic, and it is required to unblock task 181 (bimodal layer).
- The timing conflict between teammates is resolved: there is no file conflict with task 188, which operates on propositional logic in a separate upstream branch. Task 179 can proceed immediately.
- Scope estimate converges at 35–42 files with the Critic's corrected count being more reliable than the prior report's ~55 estimate or Teammate A's 6–10 estimate. The critical new proof obligation is a `mcs_dia_witness` lemma for the completeness direction of the truth lemma.
- Recommended implementation: add `.dia` as a primitive constructor with `diamond` kept as a backward-compatible abbreviation pointing to `.dia`, add `HasDia` to `Connectives.lean`, and extend `ModalConnectives` to include `HasDia`.

---

## Key Findings

### Primary Approach (from Teammate A)

Teammate A investigated the current codebase state and implementation options in detail.

**Current state confirmed**: `Modal.Proposition` uses `{atom, bot, imp, box}` as the only primitive constructors. `diamond φ` is an `abbrev` for `.neg (.box (.neg φ))`. This means axioms involving `◇` (D, B, 5) are all spelled out as deeply nested term-level expansions — non-idiomatic and cognitively expensive.

**Recommended implementation strategy** (Option A): Add `.dia` constructor to the `Proposition` inductive and keep `diamond` as a backward-compatible `abbrev` pointing to `.dia`. This yields zero breaking changes — all existing code using `Proposition.diamond` continues to work, because the `abbrev` now routes to the primitive constructor instead of the negation expansion.

**Revised scope estimate**: 6–10 files with substantive changes. The key insight is that `ProofSystem/Instances/*.lean` and system-level `Soundness.lean`/`Completeness.lean` files do not induct on `Proposition`, so they need no changes if the `diamond` abbreviation is maintained.

**Truth lemma obligation identified**: The `.dia` case in the classical truth lemma is not trivial. The "forward" direction (from `∃ w', r w w' ∧ Satisfies w' φ` to `dia φ ∈ S`) requires reasoning through classical MCS infrastructure. The "backward" direction (from `dia φ ∈ S` to `∃ T accessible, φ ∈ T`) requires a new `mcs_dia_exists` lemma connecting primitive `.dia` membership to box-centric canonical accessibility.

**Timing**: Teammate A recommends deferring until after the first upstream PR (task 188). However, this recommendation is based on a mistaken belief about task 188's scope (see Conflicts Resolved below).

**Confidence level**: High on implementation approach; medium-high on timing recommendation.

### Alternative Approaches (from Teammate B)

Teammate B analyzed four alternative approaches to avoiding or restructuring the diamond change:

**Alternative A — `HasDia` typeclass alone without primitive constructor**: Assessed as insufficient. A `HasDia` typeclass with a classical default instance `dia φ := neg (box (neg φ))` does not fix the underlying problem. The axioms in `Axioms.lean` would still expand diamond inline; intuitionistic logics cannot override the classical default for a single inductive type.

**Alternative B — Parameterized proposition type**: Assessed as architecturally incompatible. The `Connectives.lean` file explicitly documents that CSLib uses separate concrete inductive types registered as typeclass instances, not parameterized inductives. Lean 4 cannot extend inductives, and dependent type parameterization creates universe friction.

**Alternative C — Separate `Intuitionistic.Modal.Proposition` type**: Correct long-term direction for IK/IS4 formalization but out of scope for task 179. Would require separate `Satisfies`, `DerivationTree`, `CanonicalModel`, and `truth_lemma` infrastructure.

**Alternative D — Defer until intuitionistic logics are needed**: The point-of-no-return concern is real and immediate. The refactoring cost grows linearly with file count. The modal Metalogic directory already has ~40 files. Every new completeness theorem added under derived-diamond is another file requiring a `.dia` case later.

**Key evidence for proceeding now**: The `Bimodal.ModalEmbedding.lean` currently proves `diamond` preservation by `rfl` — a proof that holds only because diamond unfolds identically in both types. Any future `Bimodal.Formula` changes (task 181) would break this `rfl` if not coordinated with a modal `dia` change.

**Recommended scope additions**: Add `HasDia` to `Connectives.lean`, update `Axioms.lean` to use `HasDia.dia` in `AxiomB`, `Axiom5`, and `AxiomD`, and provide the classical equivalence `◇φ ↔ ¬□¬φ` as a theorem (not a definition) for systems with Peirce's law.

**Confidence level**: High on alternatives analysis; medium on the estimate that classical equivalence proof is non-trivial inside CSLib's Hilbert system.

### Gaps and Shortcomings (from Teammate C — Critic)

The Critic identified five substantive issues with the prior research and Teammate A's findings:

**1. False premise in task description**: The task description lists `{atom, bot, imp, and, or, box}` as current primitives. This is wrong. The Critic confirmed from `Basic.lean` lines 52–61 that only `{atom, bot, imp, box}` are constructors. All four teammates independently verified this.

**2. Near-term motivation is concrete, not speculative**: The "enables intuitionistic modal logic" motivation is not supported by any active task. However, task 181 (Bimodal) explicitly depends on task 179 in `state.json`. The concrete near-term motivation is structural consistency with the temporal layer and unblocking task 181 — not intuitionistic expressibility.

**3. Scope estimate correction**: The prior research report estimated ~55 files; Teammate A estimated 6–10; the Critic's enumeration yields 35–42. The prior report double-counted (15 soundness + 15 completeness counted separately when most share a truth lemma family). Teammate A's 6–10 estimate is too low because it assumes zero changes to soundness files — but files using `unfold Proposition.diamond Proposition.neg` will require proof repair.

**4. Truth lemma witness gap is critical**: The `truth_lemma` in `Completeness.lean` currently has no `.dia` case. Adding `.dia` as a constructor triggers a compile error immediately — making the required changes visible. The existential-direction proof of the `.dia` truth lemma case requires a `mcs_dia_witness` lemma that is genuinely new work.

**5. No file conflict with task 188**: Task 188 targets upstream CSLib's propositional logic (`Cslib/Foundations/Logic/Defs.lean`) on a separate branch. Task 179 targets `Cslib/Logics/Modal/`. These are entirely disjoint directories and branches. The timing concern raised by Teammate A is based on a false premise about task 188's scope.

**Confidence level**: High on all findings.

### Strategic Horizons (from Teammate D)

Teammate D assessed the long-term architectural and upstream alignment implications.

**Architectural consistency**: The `Connectives.lean` file justifies making `and`/`or` primitive for propositional logic using exactly the same argument that task 179 uses for diamond: classical equivalences collapse the distinction only in classical logic. Primitive diamond is the consistent application of an already-committed architectural principle.

**Upstream convergence**: Upstream CSLib already uses primitive diamond in `{atom, not, and, diamond}`. The fork's `{atom, bot, imp, box}` creates a design divergence that would need resolution in any future modal PR to upstream. Task 179 closes this gap. When modal PRs eventually arrive (later in the 6-PR propositional-first sequence documented in `pr-description.md`), having primitive diamond in the fork makes the modal PR design clean.

**Task sequencing**: Tasks 179 and 180 are parallel foundation refactors with no mutual dependency. Both unblock task 181. Running them in parallel (with `--team` if resources allow) is the recommended sequencing.

**`HasDia` typeclass**: `ModalConnectives` currently extends `PropositionalConnectives F, HasBox F` with no `HasDia`. The docstring in `Connectives.lean` notes "diamond (possibility) are derived connectives" — this comment should become obsolete after task 179. Adding `HasDia` and extending `ModalConnectives` to include it is a natural companion step that keeps the connective abstraction complete.

**Case for "not now" is weak**: None of the conditions that would justify deferral hold: task 179 is not high-risk (scope is well-understood from task 177 playbook), nothing in the roadmap says to keep diamond derived, and upstream already has primitive diamond.

**Confidence level**: High on strategic assessment.

---

## Synthesis

### Conflicts Resolved

**Conflict 1 — Timing: "after task 188" (A) vs. "now" (B, C, D)**

The conflict is resolved in favor of proceeding now. Teammate A's deferral recommendation was based on the concern that adding `dia` would complicate the first upstream PR. The Critic confirmed that task 188 and task 179 operate in completely disjoint directories and branches with no file overlap. There is no timing conflict. The concrete dependency path (task 181 depends on task 179) provides a near-term concrete motivation for proceeding now.

**Resolution**: Proceed with task 179 now, independent of task 188's timeline.

**Conflict 2 — Scope: 6-10 files (A) vs. 35-42 files (C) vs. 55 files (prior report)**

The three estimates reflect different assumptions about backward compatibility and proof repair scope.

- The prior report's ~55 estimate double-counted system files and assumed full restructuring.
- Teammate A's 6–10 estimate assumes the `diamond` abbreviation is fully preserved and no proof repair is needed — but this undersells the impact. Proofs using `unfold Proposition.diamond Proposition.neg` (which exist in `Completeness.lean`) will need repair because you cannot `unfold` a constructor.
- The Critic's 35–42 estimate accounts for the proof repair cost but may overcount soundness files that are unaffected.

**Resolution**: Expect 15–30 files requiring meaningful changes, with proof repair concentrated in the 3 truth lemma families and the few files using `unfold` on diamond. The Critic's top-end estimate (42 files) includes mechanical match-arm additions that are low-risk. The planning phase should enumerate actual files requiring non-trivial proof changes.

**Conflict 3 — Primary motivation: intuitionistic logic (A, B, prior) vs. bimodal consistency (C)**

This is not a direct conflict but a framing difference. All teammates agree that making diamond primitive is correct; they differ on the primary motivation. The Critic's evidence (task 181 dependency in `state.json`, no IK tasks in TODO.md) supports framing the primary motivation as architectural consistency and unblocking task 181, with intuitionistic modal logic as a secondary long-term benefit.

**Resolution**: Both motivations are valid. The plan should document the concrete near-term motivation (task 181, `ModalConnectives` completeness, upstream alignment) as primary, and intuitionistic modal logic support as a future strategic benefit.

### Gaps Identified

**Gap 1 — `mcs_dia_witness` lemma**: No teammate provided the proof sketch for the diamond witness lemma in the existential direction of the truth lemma. The implementation plan must explicitly identify this as the central new proof obligation and prototype the proof in MCS.lean before propagating the constructor change.

**Gap 2 — Proof repair scope for `unfold` patterns**: Teammate B identified that `Completeness.lean` contains `unfold Proposition.diamond Proposition.neg` patterns that will require repair. The full extent of these patterns across all completeness files was not enumerated. The planning phase should grep for all `unfold.*diamond` occurrences.

**Gap 3 — `mcs_box_diamond` lemma interaction**: The Critic noted that `mcs_box_diamond` (MCS.lean, lines 163–173) currently treats `diamond` as a defined abbreviation. After making `dia` primitive, this lemma's proof may need adjustment. This was flagged but not fully analyzed.

**Gap 4 — `ModalEmbedding.lean` rfl proof**: Teammate B identified that `Bimodal.ModalEmbedding.lean` uses a `rfl` proof for diamond preservation that will break when `Modal.Proposition.diamond` becomes a constructor rather than an abbreviation expanding identically to `Bimodal.Formula.diamond`. Repair is required in task 181 (or possibly task 179 if the embedding file is in scope).

### Recommendations

1. **Proceed with task 179 now.** There is no file conflict with task 188. The concrete dependencies (task 181) and architectural consistency arguments are strong. Deferring increases refactoring cost monotonically.

2. **Use Option A: `.dia` primitive constructor with `diamond` backward-compatible abbreviation.** Add `.dia` constructor to `Proposition`, change `diamond` from `abbrev Proposition.diamond := .neg (.box (.neg φ))` to `abbrev Proposition.diamond := .dia`. This preserves existing notation and avoids breaking changes to axiom files.

3. **Add `HasDia` to `Connectives.lean` in the same task.** Extend `ModalConnectives` to include `HasDia`. Update `Axioms.lean` to use `HasDia.dia` in `AxiomB`, `Axiom5`, and `AxiomD` instead of the manually expanded negation terms.

4. **Prioritize the truth lemma `.dia` case as the critical path item.** The `mcs_dia_witness` lemma (or equivalent) must be prototyped first. It is the only genuinely new proof obligation. All other changes are either mechanical (new match arms) or proof repair (replacing `unfold diamond` with `simp [Satisfies]` or `rw [Satisfies.diamond_iff]`).

5. **Phase the implementation as follows** (recommended plan structure):
   - Phase 1: Core constructor (`Basic.lean`, `Denotation.lean`, `LogicalEquivalence.lean`, `Connectives.lean`)
   - Phase 2: MCS infrastructure (`MCS.lean` — add `mcs_dia_witness`; verify `mcs_box_diamond` proof still compiles)
   - Phase 3: Truth lemma extension (`Completeness.lean`, `K/Completeness.lean`, `D/Completeness.lean` — add `.dia` cases)
   - Phase 4: Axiom cleanup (`Axioms.lean`, `ProofSystem/Instances/*.lean` — update to use `HasDia.dia` or `dia` notation)
   - Phase 5: Verification (`lake build`, check `Bimodal/ModalEmbedding.lean` for `rfl` breakage)

6. **Do not include task 181 (bimodal) in task 179's scope.** The bimodal embedding will need updating but that is task 181's responsibility after both 179 and 180 complete.

7. **Correct the task description**: Update to reflect that current primitives are `{atom, bot, imp, box}` and the target is `{atom, bot, imp, box, dia}`.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|-----------------|
| A | Primary approach | completed | high | Backward-compatible implementation strategy; truth lemma analysis; timing recommendation (overridden by Critic) |
| B | Alternative approaches | completed | high | Systematic elimination of alternatives; `HasDia` typeclass scope; proof repair identification |
| C | Critic / Gap analysis | completed | high | Scope correction (35–42 files); timing conflict debunked; `mcs_dia_witness` gap; task 181 dependency as concrete motivation |
| D | Strategic horizons | completed | high | Upstream alignment; `HasDia` in `ModalConnectives`; parallel 179+180 sequencing; architectural consistency argument |

---

## References

- Fischer Servi, G. (1984). Axiomatisations for some intuitionistic modal logics. *Rendiconti del Seminario Matematico*, 42, 179–194.
- Simpson, A. (1994). *The Proof Theory and Semantics of Intuitionistic Modal Logic*. PhD thesis, University of Edinburgh.
- Bierman, G. & de Paiva, V. (2000). On an intuitionistic modal logic. *Studia Logica*, 65, 383–416.
- Prior research report: `specs/179_modal_primitive_diamond/reports/01_primitive-diamond-research.md`
- Task 177 playbook (bimodal and/or, ~127 files): referenced as scope comparator by Teammate D
- Task 181 dependency: confirmed in `specs/state.json` (`"dependencies": [179, 180]`)
- `Cslib/Logics/Modal/Basic.lean` lines 52–61: current `Proposition` constructors
- `Cslib/Logics/Modal/Metalogic/MCS.lean` lines 163–173: `mcs_box_diamond` lemma
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` lines 337–422: `truth_lemma` (no `.dia` case)
- `Cslib/Foundations/Logic/Connectives.lean`: `ModalConnectives` (missing `HasDia`)
- `Cslib/Foundations/Logic/Axioms.lean`: `AxiomB`, `Axiom5`, `AxiomD` with expanded diamond
