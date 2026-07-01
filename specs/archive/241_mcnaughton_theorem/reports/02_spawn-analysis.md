# Blocker Analysis: Task #241

**Parent Task**: #241 - mcnaughton_theorem
**Generated**: 2026-06-30
**Blocker**: Phase 4 of the plan requires proving `buchiCongr_DMA_language_eq` (the language equality between the assembled DMA and the original NBA), whose forward inclusion direction demands recurrent-class/idempotent infrastructure that the `BuchiCongruence` API does not currently expose. Two consecutive monolithic dispatches both hit context overflow with zero commits.

## Root Cause

The forward inclusion `language na ⊆ language (buchiCongr_DMA na)` is the research-grade core of McNaughton's theorem. Concretely, the proof must show that for any `xs ∈ language na`, the DMA's run visits a "good" recurrent congruence class infinitely often. This requires:

1. **A well-defined monoid structure on congruence classes**: The Büchi congruence quotient `Quotient BuchiCongruence.eq` has a multiplication `⟦u⟧ · ⟦v⟧ = ⟦u ++ v⟧`, but this multiplication and its basic algebraic laws (especially idempotent-power collapse: `b^k = b` when `b · b = b`) are not currently exposed as named lemmas in `Cslib/Computability/Languages/Congruences/RightCongruence.lean` or `BuchiCongruence.lean`. Without these, the prefix-class sequence `n ↦ ⟦xs.extract 0 n⟧` cannot be manipulated algebraically.

2. **A Ramsey-style recurrent-class lemma**: Fixing `[Finite State]`, for any input sequence `xs`, the infinite prefix-class run must frequently return to some idempotent class `b` that was preceded by a stabilising prefix class `a` (with `a · b = a`). This is the Choueka/Ramsey argument that `buchiFamily_cover` already invokes via `infinite_graph_ramsey`, but it needs to be recast at the level of the prefix-class run to produce a witness `b ∈ (buchiCongr_DMA na).run xs |>.infOcc`. The current `buchiFamily_cover` and `buchiFamily_saturation` lemmas exist, but the bridge from "cover exists" to "recurrent class in the run" requires the idempotent-structure already established in INFRA-1.

The orchestrator handoff (commit 44280434, `specs/241_mcnaughton_theorem/.orchestrator-handoff.json`) confirms: `buchiCongr_DMA_run_eq` is proved and green (`(buchiCongr_DMA na).run xs n = ⟦xs.extract 0 n⟧`), so the run is fully characterised as the prefix-class sequence. The missing piece is purely the algebraic/combinatorial infrastructure above.

## Proposed New Tasks

### New Task 1: Expose BuchiCongruence eqvCls monoid and idempotent lemmas
- **Effort**: 2-3 hours
- **Task Type**: cslib
- **Rationale**: The forward inclusion of `buchiCongr_DMA_language_eq` is expressed in terms of multiplication of congruence classes. Before any Ramsey argument can be written in Lean, the implementation must establish: (a) that `Quotient.mk BuchiCongruence.eq` is a well-defined multiplicative map (i.e., `⟦u ++ v⟧ = ⟦u⟧ · ⟦v⟧`), and (b) the idempotent-power collapse lemma: if `b · b = b` then `b ^ k = b` for all `k ≥ 1`. Additionally, any relevant companion fact such as `a · b = a` being preserved under iterated multiplication. These are purely algebraic facts about `RightCongruence`/`BuchiCongruence` monoid structure. Adding them as named lemmas in `Cslib/Computability/Languages/Congruences/RightCongruence.lean` (or `BuchiCongruence.lean`) is a single-dispatch-sized proof-engineering task with no research-grade difficulty.
- **Depends on**: None

### New Task 2: Prove Ramsey recurrent-class lemma for BuchiCongruence prefix runs
- **Effort**: 3-4 hours
- **Task Type**: cslib
- **Rationale**: With the monoid/idempotent lemmas in place, it becomes possible to state and prove the recurrent-class lemma: for `[Finite State]` and any `xs : ωSequence Alphabet`, there exist classes `a b : Quotient BuchiCongruence.eq` such that `b · b = b`, `a · b = a`, and `∃ᶠ k in atTop, (buchiCongr_DMA na).run xs k = a` (i.e., `a ∈ (buchiCongr_DMA na).run xs |>.infOcc`). The proof mirrors `buchiFamily_cover` — invoking `infinite_graph_ramsey` on the finite state space — but produces the explicit idempotent witness at the run level rather than the language-cover level. This is the direct bridge that lets Phase 4 close `b ∈ infOcc` and feed `buchiFamily_saturation` + `buchiFamily_cover` to complete the forward direction of `buchiCongr_DMA_language_eq`. The lemma can live in `BuchiCongruence.lean` alongside `buchiFamily_cover`.
- **Depends on**: New Task 1, because the statement uses `a · b = a` and `b · b = b` (multiplication on quotient classes from INFRA-1), the proof uses the idempotent-power collapse to show prefix classes stabilise, and the Lean elaborator needs the `Mul` instance on `Quotient BuchiCongruence.eq` to be recognised as the same operation throughout the proof.

## Dependency Reasoning

- **Task 1 (INFRA-1) has no dependencies**: All facts are purely algebraic about the `RightCongruence` quotient monoid. They can be proved in isolation, reading only `RightCongruence.lean` and `BuchiCongruence.lean`.

- **Task 2 (INFRA-2) depends on Task 1 (INFRA-1)**: The dependency is about implementation details, not just sequencing. Specifically:
  - The statement of INFRA-2 refers to `b · b = b` and `a · b = a`; these require the multiplication on `Quotient BuchiCongruence.eq` to be surfaced as a usable `Mul` instance with the `⟦u⟧ · ⟦v⟧ = ⟦u ++ v⟧` rewrite lemma (from INFRA-1) so Lean can elaborate the conditions and the proof can unfold them.
  - The core proof step reduces prefix-class arithmetic to idempotent-power collapse (`a · b^k = a · b = a`), which is the named lemma produced by INFRA-1. Without that lemma, INFRA-2's proof would need to re-derive it inline, making it a non-single-dispatch task.
  - The Lean `infOcc` conclusion requires matching `(buchiCongr_DMA na).run xs k = a` against the quotient structure, which is only ergonomic once INFRA-1 has established the canonical rewrite form.

- **Task 1 and Task 2 are NOT independent**: Task 2's statement and proof both depend on the specific names and types of lemmas produced by Task 1. The order is strictly sequential.

## After Completion

Once both spawned tasks are complete, resume the parent task #241 with `/implement 241`.

The blocker will be resolved because: INFRA-1 provides the algebraic rewrite lemmas needed to state the forward direction cleanly, and INFRA-2 provides the recurrent-class witness that `buchiFamily_saturation` + `buchiCongr_DMA_run_eq` need to conclude `b ∈ infOcc` of the DMA run. With these two lemmas in hand, the remaining Phase 4 work (forward inclusion, backward inclusion via accept-set unfolding, combine into `buchiCongr_DMA_language_eq`) and Phases 5-6 (close `IsRegular.iff_da_muller`) each become single-dispatch-sized proof tasks.
