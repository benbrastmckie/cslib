# Research Report: Zulip Thread Benefit/Cost Analysis for Conservative Extension

**Task**: 265 -- track_conservative_lean_sorry
**Session**: sess_1782157692_280fc8
**Date**: 2026-06-22
**Artifact**: 02 (second research round)

## 1. Zulip Thread Context

The Zulip thread on `#CSLib > Propositional Logic` includes four participants
(Benjamin Brast-McKie, Thomas Waring, Matthew Doty, Chris Henson) and spans a substantive
technical discussion about the algebraic semantics of propositional logic in CSLib. The
conservative extension result (`ipl_conservative_over_mpl`) appears as a recurrent topic
across multiple messages, revealing that it is not merely a cleanup item but a result that
multiple contributors have been thinking about.

### 1.1 Thomas Waring's Explicit Request

Thomas Waring directly stated: "I'd actually been looking for a semantic way to show that
IPL is conservative over MPL, and that was one of the reasons I wanted to allow substitutions
which don't preserve bot." This establishes that the conservative extension theorem is not
just an internal code hygiene matter -- it is a result that an active contributor was
specifically seeking. The fact that Thomas had been pursuing this through a different
approach (substitutions that do not preserve bot) and had not yet found a satisfactory
semantic proof increases the value of delivering one through the WithBot embedding.

### 1.2 Matthew Doty's Attempt and Assessment

Matthew Doty proposed using Dedekind-MacNeille completion to prove the result, then
cautioned: "Normally, this would establish that IPL is a conservative extension of MPL,
although I'm not sure we can prove it given how we are handling bot." Thomas confirmed
that the Dedekind-MacNeille approach does not solve the fundamental issue because "that
result requires allowing valuations v where v bot != bot." The thread thus documents
both an attempted approach and its explicit rejection -- providing additional validation
that the WithBot embedding (which the plan proposes) is the correct alternative.

### 1.3 The bot_val Design Controversy

The thread contains a sustained debate about whether `bot_val : H` (the explicit bottom
parameter in `AlgEvaluate`) is the right design. Thomas called it "unnatural" and argued
for a pure GHA approach without a primitive bot symbol. Benjamin defended the design on
substitution invariance and universal algebra grounds. The conservative extension theorem
has a special role in this debate: it is precisely the result that validates the `bot_val`
design by showing that the extra parameter (needed for MPL completeness over GHA) does not
break the relationship with IPL. Without this theorem, the `bot_val` parameter looks like
an ad hoc workaround rather than a principled design choice.

## 2. Benefit Analysis

### 2.1 Resolves the Only Sorry in Propositional Logic

The `sorry` at Conservative.lean:99 is the sole remaining sorry in the entire
`Cslib/Logics/Propositional/` directory. All other propositional logic results --
soundness, completeness (MPL, IPL, CPL), Lindenbaum algebra construction, canonical
model theory -- are fully proved. Filling this sorry achieves a clean sorry-free
propositional logic module, which is a strong signal of library maturity.

### 2.2 Validates a Contested Design Decision

The `bot_val : H` parameter in `AlgEvaluate` was debated in the Zulip thread. The
conservative extension theorem is the mathematical justification for this design:

- `AlgEvaluate` takes an explicit `bot_val` because `GeneralizedHeytingAlgebra` lacks
  a canonical bottom element (needed for MPL semantics).
- `IPL.alg_complete` fixes `bot_val = bot` because `HeytingAlgebra` provides one.
- The conservative extension shows these two evaluation regimes agree on bot-free
  formulas -- the `bot_val` parameter is harmless for the fragment that both logics share.

Without the proof, the design looks ad hoc. With it, the design is shown to be both
necessary (for MPL completeness) and harmless (for conservativity).

### 2.3 Fulfills an Explicit Community Request

Thomas Waring's message establishes direct community demand for a semantic conservativity
proof. Delivering this result demonstrates that CSLib's framework can answer questions
that contributors are actively pursuing. This is qualitatively different from filling a
sorry that nobody has asked about.

### 2.4 Demonstrates Framework Capability

The proof chains three independently valuable results:

1. `MPL.alg_complete` (GHA completeness for MPL)
2. `IPL.alg_complete` (HA completeness for IPL)
3. `AlgEvaluate_botFree_independent` (bot-free evaluation independence)

The conservative extension is the theorem that ties these together into a coherent
story about the relationship between logics. It demonstrates that CSLib's algebraic
semantics framework is not just a collection of isolated results but a system capable
of proving inter-logic relationships.

### 2.5 Validates the Rejection of Dedekind-MacNeille

The Zulip thread explicitly considered and rejected the Dedekind-MacNeille approach.
The plan's WithBot embedding succeeds where that approach failed. Completing the proof
retroactively validates the thread's analysis: the `bot_val` parameter, combined with
WithBot, is the correct way to bridge GHA and HA evaluation.

### 2.6 First Known Lean 4 Formalization

The first research report (01) found no existing Lean 4 formalization of this result
in Mathlib, FormalizedFormalLogic, or other known repositories. Completing this would
be a novel contribution to the Lean 4 formalization landscape.

## 3. Cost Analysis

### 3.1 Implementation Size

The plan estimates 55-70 lines of new Lean 4 code, confined to a single file
(`Conservative.lean`). This is small by any measure -- comparable to adding a
utility lemma rather than developing a new module.

### 3.2 Time Estimate

The plan estimates 1 hour across three sequential phases:
- Phase 1 (25 min): WithBot HeytingAlgebra instance
- Phase 2 (20 min): Embedding lemma
- Phase 3 (15 min): Main theorem and cleanup

This is a conservative estimate that accounts for potential Lean 4 tactic debugging.

### 3.3 Prerequisites

All mathematical prerequisites already exist in the codebase:

| Prerequisite | Location | Status |
|-------------|----------|--------|
| `AlgEvaluate` (evaluator) | `Algebra.lean:82` | Complete |
| `AlgEvaluate_botFree_independent` | `Conservative.lean:48` | Complete |
| `MPL.alg_complete` | `Completeness.lean:237` | Complete |
| `IPL.alg_complete` | `Completeness.lean:252` | Complete |
| `Proposition.IsBotFree` | `Conservative.lean:38` | Complete |
| `WithBot` (Mathlib) | `Mathlib.Order.WithBot` | Available |

No new imports, no new files, no new module structure changes. The proof is purely
additive within an existing file.

### 3.4 Risk Profile

The plan's risk analysis identifies four risks, all rated low likelihood:
- `HeytingAlgebra.ofHImp` case splits (mitigated by research verification)
- Universe level mismatch (mitigated by type universe analysis)
- Missing simp lemmas (mitigated by `lean_loogle` fallback)
- Simp interference (mitigated by `simp only` discipline)

The research report confirmed that the WithBot approach compiles in standalone tests.
The risk of failure is genuinely low.

### 3.5 Rollback Cost

All changes are confined to `Conservative.lean`. Rollback is a single
`git checkout -- Conservative.lean`. No other files are affected.

## 4. Design Validation

The conservative extension theorem has a unique role in validating CSLib's algebraic
semantics architecture. The design involves a deliberate tradeoff:

**The tradeoff**: `AlgEvaluate` uses `GeneralizedHeytingAlgebra` with an explicit
`bot_val : H` parameter instead of `HeytingAlgebra` with a fixed `bot`. This is
necessary because GHA is the natural algebra for MPL (Johansson's minimal logic),
which does not require `bot` to be the least element. But it introduces a question:
does the extra parameter create a gap between MPL and IPL semantics?

**The answer**: The conservative extension theorem says no -- for bot-free formulas,
the two evaluation regimes agree. The `bot_val` parameter is invisible to the
fragment that both logics share.

**What this validates**:
1. The `bot_val` parameter is not an artifact of lazy design but a mathematically
   necessary feature for GHA evaluation
2. The parameter does not introduce spurious non-conservativity
3. The three-tier algebra hierarchy (GHA -> HA -> BA) is properly stratified:
   each extension is conservative over the previous one for the shared fragment

This is precisely what Thomas Waring was seeking when he said he wanted a "semantic
way to show that IPL is conservative over MPL." The proof shows the design works.

## 5. Recommendation

**Strongly recommended to implement.** The benefit/cost ratio is exceptionally favorable:

| Dimension | Assessment |
|-----------|------------|
| Lines of code | 55-70 (small) |
| Time estimate | 1 hour (small) |
| Files affected | 1 (minimal) |
| Risk of failure | Low (prerequisites verified) |
| Resolves sorry | Yes -- the only one in Propositional/ |
| Community demand | Explicit (Thomas Waring's request) |
| Design validation | High (justifies `bot_val` parameter) |
| Framework demonstration | High (chains completeness + independence) |
| Novelty | First known Lean 4 formalization |
| Rollback cost | Trivial (single file) |

The implementation should proceed as planned. No modifications to the existing plan
are needed based on the Zulip thread analysis -- the thread confirms rather than
complicates the approach. The WithBot embedding addresses precisely the gap that
Thomas identified (evaluations where `v bot != bot`) and that the Dedekind-MacNeille
approach failed to solve.
