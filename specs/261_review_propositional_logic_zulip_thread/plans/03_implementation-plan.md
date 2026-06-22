# Implementation Plan: Task #261 -- Propositional Logic Zulip Response

- **Task**: 261 - Review Zulip thread on propositional logic setup in CSLib, study all desiderata and conflicts, and craft a balanced response that satisfies all parties
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md, reports/02_nd-vs-hilbert-analysis.md
- **Artifacts**: plans/03_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This task produces a comprehensive Zulip response to the propositional logic thread (CSLib > Propositional Logic, MSG 602336739--605341190) and fills documentation gaps in the codebase. Two rounds of research identified that the codebase already resolves all substantive technical disputes (bridge lemmas exist, theory parameter handles MPL/IPL/CPL, AlgEvaluate with bot_val is implemented). The remaining work is: (1) enhance documentation at three specific locations to pre-empt future design re-litigation, (2) investigate and answer Thomas's docstring question, and (3) craft the Zulip response. Done when the response file is written and all documentation edits compile.

### Research Integration

Round 1 (01_team-research.md) mapped all 23 thread messages, identified 4 participants and 3 design disputes, and found that all disputes are resolved in code. Key finding: the research flagged a missing `Evaluate`-to-`AlgEvaluate` bridge lemma, but codebase examination reveals this already exists as `propEvaluateEq` in `Semantics/Algebra/Bridge.lean`, along with `boolEvaluateEq`. The gaps that remain are documentation-only.

Round 2 (02_nd-vs-hilbert-analysis.md) retrieved Thomas's full final message (MSG 605341190, not truncated), performed deep ND-vs-Hilbert paradigm analysis, assessed Thomas's `IProposition`/`IDerivation` compromise proposal, and confirmed via adversarial verification that CSLib's design is defensible while acknowledging Thomas's ND symmetry point is a genuine trade-off.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly advance any ROADMAP.md remaining items. It supports the overall Propositional module quality by improving documentation and maintaining contributor relations.

## Goals & Non-Goals

**Goals**:
- Investigate Thomas's docstring question via git history and document findings
- Add classically-scoped limitation warning to `FromPropositional.lean` module-level documentation
- Add design rationale documentation to `NaturalDeduction/Basic.lean` explaining the efq-as-derived-rule choice
- Write a Zulip response that addresses each participant's concerns, follows a natural narrative arc, and invites continued collaboration
- Acknowledge Thomas's contributions (GHA idea, `v models T` pattern, original ND system) explicitly

**Non-Goals**:
- Implementing Thomas's `IProposition`/`IDerivation` compromise (decided against per research)
- Writing new bridge lemmas (already exist in `Semantics/Algebra/Bridge.lean`)
- Changing the `bot`-as-primitive-constructor design (architecturally settled)
- Adding sequent calculus formalization
- Splitting PR #648 (mentioned as a possibility in the response but not implemented here)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Thomas's docstring question refers to content not recoverable from git | M | L | Check git log with --follow; if content is not found, acknowledge uncertainty in the response |
| Response tone perceived as dismissive of Thomas's position | H | L | Explicitly acknowledge ND symmetry as a genuine trade-off, credit Thomas's contributions, and frame CSLib's choice as a design decision rather than a correctness claim |
| Documentation additions fail lake build | L | L | Run scoped `lake build` after each edit to verify |
| Zulip response too long for thread format | M | M | Keep response under 2000 words; use headers for scanability |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Investigate Docstring Deletion [NOT STARTED]

**Goal**: Determine what docstring content Thomas is asking about in MSG 605341190 ("btw Benjamin, why did you delete that part of the docstring in `NaturalDeduction/Basic`?") by examining git history.

**Tasks**:
- [ ] Run `git log --follow -p -- Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` to find docstring changes
- [ ] Identify what was removed or modified and when
- [ ] Record the finding for use in the Zulip response (Phase 4)

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**: None (read-only investigation)

**Verification**:
- The specific deletion is identified, or it is confirmed that no deletion occurred (in which case the response will ask Thomas for clarification)

---

### Phase 2: Enhance NaturalDeduction/Basic.lean Documentation [NOT STARTED]

**Goal**: Add or enhance documentation in `NaturalDeduction/Basic.lean` making the efq-as-derived-rule design choice explicit, addressing Thomas's ND symmetry concern proactively.

**Tasks**:
- [ ] Review the existing docstring (lines 14-64) to determine what is already documented
- [ ] If not already present, add a "Design Decisions" subsection explaining: (a) why efq is theory-dependent rather than a primitive constructor, (b) that this breaks the constructor-rule correspondence (acknowledging Thomas's point), (c) that this is a deliberate trade-off enabling MPL-first design with theory parameter
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` to verify

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- docstring enhancement

**Verification**:
- Documentation includes explicit mention of the efq design choice and its trade-offs
- `lake build` passes for the module

---

### Phase 3: Add Classically-Scoped Warning to FromPropositional.lean [NOT STARTED]

**Goal**: Add a prominent module-level documentation note in `FromPropositional.lean` (both Modal and Temporal versions) warning that the Lukasiewicz encoding of `and`/`or` is valid only for classical modal logic.

**Tasks**:
- [ ] Review `Cslib/Logics/Modal/FromPropositional.lean` existing documentation
- [ ] If the warning is not already prominent enough, enhance it with a `## Limitations` section or a `@[simp]`-level note
- [ ] Review `Cslib/Logics/Temporal/FromPropositional.lean` for the same issue
- [ ] Run scoped `lake build` for both modules

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` -- enhanced limitation warning
- `Cslib/Logics/Temporal/FromPropositional.lean` -- enhanced limitation warning (if applicable)

**Verification**:
- Both files contain a prominent warning about the classical scope of the Lukasiewicz encoding
- `lake build` passes for both modules

---

### Phase 4: Draft and Write Zulip Response [NOT STARTED]

**Goal**: Write a carefully crafted Zulip response that addresses each participant's concerns, presents the synthesis from both research rounds, follows a natural narrative arc, and invites continued collaboration.

**Tasks**:
- [ ] Draft the response incorporating findings from Phases 1-3
- [ ] Structure the response with the following narrative arc:
  1. Opening: gratitude for the discussion, acknowledgment of time elapsed
  2. Core design decision: bot-as-primitive, substitution invariance argument, free-monad structure
  3. Acknowledgment of Thomas's ND symmetry concern: genuine trade-off, not an oversight, documented
  4. bot_val reframing: Johansson designated constant, not a patch
  5. Parametric completeness: Thomas's `v models T` pattern adopted as `AlgTValid` (credit Thomas)
  6. Prop vs. Bool: resolved by dual evaluator + bridge lemmas (all exist)
  7. Thomas's IProposition compromise: thank for proof-of-concept, explain why dual types are impractical for multi-logic architecture
  8. Answer Thomas's docstring question (using findings from Phase 1)
  9. PR strategy: offer to split PR #648 for easier review
  10. Closing: credit Thomas's contributions, invite continued collaboration
- [ ] Review tone for balance: firm on technical decisions, gracious on contributions, honest about trade-offs
- [ ] Write the response to `specs/261_review_propositional_logic_zulip_thread/zulip-response.md`

**Timing**: 1.5 hours

**Depends on**: 2, 3

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
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- enhanced docstring (Phase 2)
- `Cslib/Logics/Modal/FromPropositional.lean` -- enhanced warning (Phase 3)
- `Cslib/Logics/Temporal/FromPropositional.lean` -- enhanced warning if needed (Phase 3)

## Rollback/Contingency

All changes are documentation-only (Lean docstrings) plus one new markdown file. Rollback is straightforward:
- Revert any docstring changes via `git checkout -- <file>` for the affected Lean files
- Delete `specs/261_review_propositional_logic_zulip_thread/zulip-response.md`
- No proofs or definitions are modified, so there is zero risk to compilation
