# Implementation Plan: Task #261 -- Propositional Logic Zulip Response

- **Task**: 261 - Review Zulip thread on propositional logic setup in CSLib, study all desiderata and conflicts, and craft a balanced response that satisfies all parties
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md, reports/02_nd-vs-hilbert-analysis.md, reports/03_typeclass-split-analysis.md
- **Artifacts**: plans/03_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This task produces a comprehensive Zulip response to the propositional logic thread (CSLib > Propositional Logic, MSG 602336739--605341190) and fills documentation gaps in the codebase. Two rounds of research identified that the codebase already resolves all substantive technical disputes (bridge lemmas exist, theory parameter handles MPL/IPL/CPL, AlgEvaluate with bot_val is implemented). The remaining work is: (1) rewrite the `NaturalDeduction/Basic.lean` docstring with a neutral framing that states the efq trade-off factually and restores Thomas's references, (2) add classically-scoped warnings to `FromPropositional.lean`, and (3) craft the Zulip response acknowledging the docstring rewrite and the neutral replacement. Done when the response file is written and all documentation edits compile.

### Research Integration

Round 1 (01_team-research.md) mapped all 23 thread messages, identified 4 participants and 3 design disputes, and found that all disputes are resolved in code. Key finding: the research flagged a missing `Evaluate`-to-`AlgEvaluate` bridge lemma, but codebase examination reveals this already exists as `propEvaluateEq` in `Semantics/Algebra/Bridge.lean`, along with `boolEvaluateEq`. The gaps that remain are documentation-only.

Round 2 (02_nd-vs-hilbert-analysis.md) retrieved Thomas's full final message (MSG 605341190, not truncated), performed deep ND-vs-Hilbert paradigm analysis, assessed Thomas's `IProposition`/`IDerivation` compromise proposal, and confirmed via adversarial verification that CSLib's design is defensible while acknowledging Thomas's ND symmetry point is a genuine trade-off.

Round 3 (03_typeclass-split-analysis.md) investigated whether a typeclass split can avoid the hybrid ND. Conclusion: **no** — Lean 4's inductive type system does not support conditionally-available constructors. Three approaches were analyzed (split at formula level, split at Derivation level, typeclass on connectives); all either collapse back to the current design or require Thomas's full dual-type duplication. The hybrid reflects a genuine logical asymmetry (`⊥` has no introduction rule). The duplication cost of the dual-type approach compounds across the entire downstream API (monad, substitution, evaluation, bridge lemmas, FromPropositional embeddings). Matthew Doty (MSG 605712144) endorses class-based approaches but flags conservative extension proof difficulty.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly advance any ROADMAP.md remaining items. It supports the overall Propositional module quality by improving documentation and maintaining contributor relations.

## Goals & Non-Goals

**Goals**:
- Rewrite `NaturalDeduction/Basic.lean` docstring with a neutral framing: state the efq trade-off factually, restore Thomas's references, link to the Zulip thread — without characterizing the design as settled or ongoing
- Add classically-scoped limitation warning to `FromPropositional.lean` module-level documentation
- Write a Zulip response that addresses each participant's concerns, follows a natural narrative arc, and invites continued collaboration
- Acknowledge Thomas's contributions (GHA idea, `v models T` pattern, original ND system) explicitly

**Non-Goals**:
- Implementing Thomas's `IProposition`/`IDerivation` compromise (decided against per round 3 analysis — duplication cost prohibitive for multi-logic architecture)
- Writing new bridge lemmas (already exist in `Semantics/Algebra/Bridge.lean`)
- Changing the `bot`-as-primitive-constructor design (architecturally settled)
- Adding sequent calculus formalization
- Splitting PR #648 (mentioned as a possibility in the response but not implemented here)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Restored docstring wording doesn't match Thomas's expectations | M | L | Restore his original framing verbatim where possible; the Zulip response explains the restoration and invites further edits |
| Response tone perceived as dismissive of Thomas's position | H | L | Explicitly acknowledge ND symmetry as a genuine trade-off, credit Thomas's contributions, and frame CSLib's choice as a design decision rather than a correctness claim |
| Documentation additions fail lake build | L | L | Run scoped `lake build` after each edit to verify |
| Zulip response too long for thread format | M | M | Keep response under 2000 words; use headers for scanability |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Restore Thomas's Docstring and Enhance ND Documentation [NOT STARTED]

**Goal**: Replace the current docstring with a neutral framing that states the efq trade-off factually without taking sides, restores Thomas's references, and links to the Zulip thread.

**Investigation Result** (completed pre-plan): Thomas's original docstring from PR #91 contained a paragraph explaining that the efq-as-axiom design "differs from many on-paper presentations" and framed the choice as **ongoing discussion**, with a link to the Zulip thread. Commit `7cc09612` (Jun 16, "five-primitive formula type with primitive bot") replaced this with the current text that presents the design as settled, removing the discussion framing, the Zulip link, and Thomas's original references (Prawitz prose citation, Sorensen & Urzyczyn).

**Tasks**:
- [ ] Read current docstring in `NaturalDeduction/Basic.lean`
- [ ] Replace the "Implementation notes" section with a neutral framing that: (a) states that efq is not among the 10 primitive rules and enters as a theory axiom via `[IsIntuitionistic T]`, (b) notes factually that this differs from standard on-paper ND presentations which include bottom elimination as a primitive rule, (c) names the specific trade-off: API uniformity and zero duplication across the multi-logic hierarchy (Modal, Temporal, Bimodal) vs. constructor-rule correspondence characteristic of Gentzen-style ND, (d) notes that `⊥` is genuinely asymmetric — it has no introduction rule in any proof system, so the "broken symmetry" reflects logical reality, (e) links to the Zulip Propositional Logic thread for further context — without characterizing the discussion as "ongoing" or "settled"
- [ ] Restore Thomas's reference citations (Prawitz, Sorensen & Urzyczyn) alongside the current BibKey references
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` to verify

**Timing**: 40 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- restore + enhance docstring

**Verification**:
- Docstring states the efq design choice and trade-off factually without taking sides
- Docstring notes it differs from standard on-paper ND presentations
- Docstring includes link to the Zulip Propositional Logic thread
- Docstring includes Thomas's references (Prawitz, Sorensen & Urzyczyn) alongside current BibKeys
- `lake build` passes for the module

---

### Phase 2: Add Classically-Scoped Warning to FromPropositional.lean [NOT STARTED]

**Goal**: Add a prominent module-level documentation note in `FromPropositional.lean` (both Modal and Temporal versions) warning that the Lukasiewicz encoding of `and`/`or` is valid only for classical modal logic.

**Tasks**:
- [ ] Review `Cslib/Logics/Modal/FromPropositional.lean` existing documentation
- [ ] If the warning is not already prominent enough, enhance it with a `## Limitations` section or a `@[simp]`-level note
- [ ] Review `Cslib/Logics/Temporal/FromPropositional.lean` for the same issue
- [ ] Run scoped `lake build` for both modules

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` -- enhanced limitation warning
- `Cslib/Logics/Temporal/FromPropositional.lean` -- enhanced limitation warning (if applicable)

**Verification**:
- Both files contain a prominent warning about the classical scope of the Lukasiewicz encoding
- `lake build` passes for both modules

---

### Phase 3: Document Completeness.lean and Add Bridge.lean References [NOT STARTED]

**Goal**: Add docstrings to all 12 definitions in `Semantics/Algebra/Completeness.lean` (currently zero docstrings on the most important file in the module) and add a References section to `Semantics/Algebra/Bridge.lean`.

**Tasks**:
- [ ] Read `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` and add docstrings to all key definitions: `canonicalV`, `canonicalBotVal`, `canonicalV_spec`, `tValid_canonicalV`, `nd_alg_sound`, `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical`, and any others
- [ ] Read `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` and add a References section citing `Rasiowa1974` and/or `RasiowaSikorski1963` for consistency with `Algebra.lean`
- [ ] Run scoped `lake build` for both modules

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` -- add docstrings to all definitions
- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` -- add References section

**Verification**:
- Every public definition in `Completeness.lean` has a docstring
- `Bridge.lean` module docstring includes a References section with BibKeys
- `lake build` passes for both modules

---

### Phase 4: Draft and Write Zulip Response [NOT STARTED]

**Goal**: Write a carefully crafted Zulip response that addresses each participant's concerns, presents the synthesis from both research rounds, follows a natural narrative arc, and invites continued collaboration.

**Tasks**:
- [ ] Draft the response incorporating findings from Phases 1-3
- [ ] Structure the response with the following narrative arc:
  1. Opening: gratitude for the discussion, acknowledgment of time elapsed
  2. Core design decision: bot-as-primitive, substitution invariance argument, free-monad structure
  3. Acknowledgment of Thomas's ND symmetry concern, then the counter-argument: `⊥` is the only connective with no introduction rule in any proof system — every other connective has symmetric intro/elim, but `⊥` has only elimination. This means the "broken symmetry" reflects a genuine logical asymmetry, not a design flaw. Making efq a theory axiom is the natural way to express that `⊥`-elimination is the only logic-dependent rule (absent in MPL, present in IPL/CPL).
  4. bot_val reframing: Johansson designated constant, not a patch
  5. Parametric completeness: Thomas's `v models T` pattern adopted as `AlgTValid` (credit Thomas)
  6. Prop vs. Bool: resolved by dual evaluator + bridge lemmas (all exist)
  7. Thomas's IProposition compromise and the typeclass question: thank for proof-of-concept, explain the duplication cost table (monad, substitution, evaluation, bridge lemmas, FromPropositional all doubled), note that typeclass splits were investigated and cannot avoid duplication due to Lean 4 inductive constraints, acknowledge Matthew's conservative extension concern (MSG 605712144), explain that `⊥`'s asymmetry (no intro rule) means the hybrid reflects logical reality
  8. Answer Thomas's docstring question: acknowledge the rewrite was hasty, explain the new neutral framing that states the trade-off factually and restores his references
  9. PR strategy: offer to split PR #648 for easier review
  10. Closing: credit Thomas's contributions, invite continued collaboration
- [ ] Review tone for balance: firm on technical decisions, gracious on contributions, honest about trade-offs
- [ ] Write the response to `specs/261_review_propositional_logic_zulip_thread/zulip-response.md`

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3

**Files to modify**:
- `specs/261_review_propositional_logic_zulip_thread/zulip-response.md` -- new file, the Zulip response draft

**Verification**:
- Response addresses all four of Thomas's paragraphs from MSG 605341190
- Response answers the docstring deletion question
- Response credits Thomas's contributions (GHA idea, `v models T` pattern, original ND system)
- Response length is under 2000 words
- Response follows a natural narrative arc (not a bullet-point dump)

## Testing & Validation

- [ ] All modified Lean files pass `lake build` (scoped to affected modules)
- [ ] Zulip response addresses all 4 paragraphs of Thomas's final message (MSG 605341190)
- [ ] Zulip response answers the docstring deletion question from Phase 1
- [ ] Zulip response credits Thomas's contributions explicitly
- [ ] Response tone is balanced: firm on technical decisions, generous on contributions
- [ ] Documentation enhancements do not change any definitions or proofs (docstring-only)

## Artifacts & Outputs

- `specs/261_review_propositional_logic_zulip_thread/plans/03_implementation-plan.md` -- this plan
- `specs/261_review_propositional_logic_zulip_thread/zulip-response.md` -- the Zulip response draft
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- neutral docstring with trade-off framing (Phase 1)
- `Cslib/Logics/Modal/FromPropositional.lean` -- verify/enhance limitation warning (Phase 2)
- `Cslib/Logics/Temporal/FromPropositional.lean` -- verify/enhance limitation warning (Phase 2)
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` -- docstrings for all definitions (Phase 3)
- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` -- References section (Phase 3)

## Rollback/Contingency

All changes are documentation-only (Lean docstrings) plus one new markdown file. Rollback is straightforward:
- Revert any docstring changes via `git checkout -- <file>` for the affected Lean files
- Delete `specs/261_review_propositional_logic_zulip_thread/zulip-response.md`
- No proofs or definitions are modified, so there is zero risk to compilation
