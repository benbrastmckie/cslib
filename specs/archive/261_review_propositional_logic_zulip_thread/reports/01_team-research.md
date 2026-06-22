# Research Report: Task #261

**Task**: Review Zulip thread on propositional logic setup in CSLib, study all desiderata and conflicts, and craft a balanced response that satisfies all parties
**Date**: 2026-06-21
**Mode**: Team Research (4 teammates)

## Summary

The Zulip thread (22-23 messages, 2026-06-07 to 2026-06-16) involves three CSLib contributors — Benjamin Brast-McKie, Thomas Waring, and Matthew Doty — plus PR comments from Ching-Tsun Chou, debating the propositional logic design for CSLib (PR #648). The thread reveals **convergence, not fundamental conflict**: the current codebase already implements solutions addressing all parties' core concerns, though this has not been explicitly communicated back to the thread. The one genuinely unresolved question is whether `⊥` should be a primitive constructor (Benjamin/Matthew/Chou) or an atom (Thomas), with the substitution invariance argument decisively favoring the primitive approach already implemented. Thomas's final message (MSG 605341190) is truncated and contains an unanswered question about a deletion.

## Key Findings

### 1. Thread Participants and Their Core Concerns

| Participant | Core Concern | Position on `⊥` | Position on `Prop`/`Bool` | Status in Codebase |
|---|---|---|---|---|
| Benjamin Brast-McKie | Kripke uniformity, substitution invariance | Primitive constructor (strong) | `Prop` primary, `Bool` secondary | Implemented in PR #648 |
| Thomas Waring | GHA naturality, ND symmetry, MPL primacy | Atom (to avoid `bot_val`) | GHA-polymorphic | Implemented via `AlgEvaluate` |
| Matthew Doty | DPLL/SAT computability | Primitive (agrees with Benjamin) | `Bool` preferred | Implemented via `BoolEvaluate` |
| Ching-Tsun Chou | (via PR comment) | Primitive (agrees with Benjamin) | `Bool.lean` alone may suffice | Bridge lemma exists |

### 2. The Three Design Disputes

**Dispute 1: `⊥` as primitive constructor vs. atom (PRIMARY, architecturally decided)**

- **Benjamin's argument**: `⊥` is a nullary operation symbol, not a variable. As a primitive constructor, `| .bot => .bot` makes substitution a free monad, and all substitution theorems (`subst_preserves_axiom`, `hilbertSubstitution`, monad laws) work without `σ(⊥) = ⊥` side conditions. The `bot_val : H` parameter in `AlgEvaluate` cleanly separates syntactic status from semantic freedom.
- **Thomas's argument**: `GeneralizedHeytingAlgebra` has no bottom element, so `bot_val` is an "unnatural" patch. With `⊥`-as-atom, the GHA evaluator needs no extra parameter, ND symmetry is preserved (each constructor has intro/elim rules), and MPL is literally the logic with no axioms.
- **Matthew's argument**: `⊥`-as-atom complicates DPLL (must handle `pos ⊥` removal from clauses, enforce `v ⊥ = ⊥` in outputs).
- **Cross-team consensus**: All 4 teammates agree the primitive `⊥` design is correct. Prior art (FormalizedFormalLogic, arXiv:2410.23765, standard Coq practice) uniformly uses `⊥` as a primitive constructor. The `bot_val` parameter is not a "patch" — it is the designated constant of Johansson algebras, with a precise algebraic meaning. The decision is also architecturally irreversible: hundreds of pattern matches on `.bot` exist across PL, Modal, Temporal, and Bimodal logic.

**Dispute 2: `Prop` vs. `Bool` semantics (SECONDARY, resolved in code)**

The codebase provides three evaluation layers:
- `Evaluate : (Atom → Prop) → Proposition Atom → Prop` — for canonical model construction (MCS membership is non-computable)
- `BoolEvaluate : (Atom → Bool) → Proposition Atom → Bool` — for DPLL/SAT computation
- `AlgEvaluate : (Atom → H) → H → Proposition Atom → H` — GHA-polymorphic, subsumes both

Bridge lemma `BoolEvaluate_eq_iff` connects `Bool` and `Prop` layers. This satisfies all parties.

**Dispute 3: MPL vs. IPL as base logic (STRUCTURAL, resolved by theory parameter)**

The `Theory` parameter design handles this: `Theory.MPL = ∅`, `Theory.IPL = Set.range (⊥ → ·)`, `Theory.CPL` adds DNE. Both positions coexist cleanly. Thomas's `v ⊨ T` parametric completeness style is compatible with this design and already partially implemented as `AlgTValid`.

### 3. What the Thread Is Actually About

The thread is less about fundamental design disagreements and more about:
- **Validation seeking**: Benjamin wants community buy-in for PR #648 choices
- **Coordination**: Thomas has competing implementations in branches; both want to avoid duplication
- **Feature requests**: Matthew needs specific DPLL capabilities
- **An unanswered question**: Thomas's final message asks about a deletion and was never addressed

## Synthesis

### Conflicts Resolved

| Conflict | Resolution | Evidence |
|---|---|---|
| `⊥` primitive vs. atom | Primitive is correct; substitution invariance is decisive | All 4 teammates agree; prior art confirms; codebase demonstrates |
| `Prop` vs. `Bool` semantics | Dual evaluator + bridge lemma | Already implemented; all parties have their use case covered |
| GHA vs. HA polymorphism | GHA with `bot_val` parameter | `AlgEvaluate` already does this; HA hardcoding would make MPL completeness false |
| MPL vs. IPL as base | Theory parameter captures both | `Theory.MPL = ∅` coexists with `Theory.IPL` and `Theory.CPL` |

### Gaps Identified

1. **Missing `Evaluate`↔`AlgEvaluate` bridge**: No lemma connecting `Evaluate v φ ↔ AlgEvaluate (· ∘ v) False φ = True`, even though `Prop` with `False` is a `BooleanAlgebra`. This is a documentation/API gap that should be addressed.

2. **Thomas's truncated message unanswered**: MSG 605341190 ends "btw Benjamin, why did you delete..." — this is an open question that any thread response must address.

3. **Four-semantics proliferation risk**: `Evaluate`, `BoolEvaluate`, `IForces`, and `AlgEvaluate` all coexist. The GHA approach was supposed to unify them but added a fourth layer alongside the others. Risk of a fifth when DPLL work begins.

4. **Modal embedding is classically scoped**: `FromPropositional.lean` uses Lukasiewicz encodings for `∧`/`∨` that break intuitionistically. If CSLib ever adds intuitionistic modal logic, this embedding needs revision. Should carry a more prominent warning.

5. **`DecidableEq Atom` constraint**: Required throughout but never discussed in the thread. Rules out certain atom types.

6. **Universe polymorphism**: GHA completeness quantifying over `H : Type*` may encounter universe limitations when `H` is the Lindenbaum algebra. Not discussed in thread.

7. **Dual proof systems**: Both ND and Hilbert systems exist with an equivalence proof. The thread doesn't discuss whether one should be canonical with the other derived, or whether both are first-class.

### Recommendations

1. **Affirm primitive `⊥`** with clear reasoning: substitution invariance, free-algebra structure, uniformity with modal/temporal embeddings, DPLL friendliness. Document `bot_val` as the "Johansson designated constant" rather than a patch.

2. **Adopt Thomas's `v ⊨ T` parametric completeness style** as the canonical public API for completeness statements. This is already endorsed by Benjamin and implemented as `AlgTValid`.

3. **Acknowledge Thomas's ND symmetry concern**: Document in `NaturalDeduction/Basic.lean` that efq being a derived rule (requiring `[IsIntuitionistic T]`) rather than a primitive rule is a deliberate design choice, not an oversight.

4. **Add the missing `Evaluate`↔`AlgEvaluate` bridge lemma**: `Evaluate v φ ↔ AlgEvaluate (· ∘ v) False φ = True`. This closes a gap all teammates identified.

5. **Consider modular PR strategy**: Split PR #648 into Defs, ProofSystem, ND, Semantics, Metalogic pieces. This lets Thomas review specific parts without blocking the whole effort.

6. **Frame DPLL as a stackable extension**: Matthew's DPLL work builds on the `BoolEvaluate` layer without requiring base changes. This should be explicitly encouraged.

7. **Address Thomas's truncated message directly**: The response must answer whatever deletion Thomas is asking about.

## Draft Response for Zulip Thread

Below is a recommended response to post to the thread. It acknowledges all positions, presents the synthesis, and invites further discussion on remaining gaps.

---

Thanks for the rich discussion, Thomas and Matthew. I've taken time to work through all the points carefully and study the interactions between the different approaches. Here's where I think things stand.

**On `⊥` as a primitive constructor vs. atom**: I remain convinced that primitive `⊥` is the right choice, and I think the thread has substantially converged on this. The substitution invariance argument is the decisive one: `⊥` is a nullary operation symbol (like `→`, `∧`), not a generator. With `⊥`-as-atom, every substitution theorem would acquire a `σ(⊥) = ⊥` side condition, breaking the free-monad structure that makes `subst_preserves_axiom` and `hilbertSubstitution` work cleanly. The `FromPropositional` embedding to modal logic also benefits — `| .bot => .bot` is direct, whereas `⊥`-as-atom would require a special-case check.

I do want to acknowledge Thomas's ND symmetry point directly: it's a genuine design consideration that each constructor should have corresponding intro/elim rules. In our current design, `⊥` doesn't have an introduction rule — instead, `efq` (`⊥ → A`) is a derived rule that appears when the theory includes it (via `[IsIntuitionistic T]`). This is a deliberate choice: it lets MPL exist as the logic with `Theory.MPL = ∅` (no axioms), while IPL adds `efq` via the theory parameter. I'll add documentation to `NaturalDeduction/Basic.lean` making this explicit.

Regarding the `bot_val` parameter in `AlgEvaluate`: I'd like to reframe this. The `bot_val : H` parameter is not a patch — it is the *Johansson designated constant*. In Johansson's original formulation of minimal logic, models are algebraic structures that may or may not have a bottom element; when they do, its interpretation is a free parameter. The `bot_val` in `AlgEvaluate` captures exactly this degree of freedom. For IPL/CPL, we fix `bot_val = ⊥` (recovering a `HeytingAlgebra`/`BooleanAlgebra`); for MPL, we quantify over all `bot_val` values. This parallels the `botForces` field in `KripkeModel`.

**On the parametric completeness style**: I completely agree with Thomas's `v ⊨ T` framing — it's elegant and general. The current `AlgTValid` definition and the algebraic completeness theorem already implement this pattern. I think this should be the canonical statement of completeness, with IPL/CPL corollaries specializing the algebra.

**On `Prop` vs. `Bool` semantics**: The current dual-evaluator approach resolves this. `Evaluate` (Prop-valued) is needed for canonical model construction (MCS membership via `fun p => atom p ∈ S` is irreducibly `Prop`-valued). `BoolEvaluate` (Bool-valued) is there for DPLL and SAT work. The bridge lemma `BoolEvaluate_eq_iff` connects them. The `AlgEvaluate` over GHA provides the unifying abstraction. Matthew, your DPLL work can build entirely on the `BoolEvaluate` layer without needing to touch the metatheory.

One gap I've noticed: we should add an explicit bridge lemma between `Evaluate` and `AlgEvaluate` (since `Prop` with `False` as bottom is a `BooleanAlgebra`). I'll add that.

**On PR strategy**: I'm open to splitting PR #648 into smaller pieces (Defs, ProofSystem, ND, Semantics, Metalogic) if that makes review easier. Thomas, would reviewing the `Defs.lean` + `Theory` definitions first be a good starting point? That's where the `⊥`-as-primitive choice lives, and settling that unblocks everything else.

Thomas — I also noticed your last message got cut off. You were asking about something I deleted? Could you clarify what you're referring to so I can address it properly?

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|---|---|---|---|---|
| A | Primary Analysis | completed | high | Full thread mapping, desiderata table, substitution invariance analysis |
| B | Alternative Approaches | completed | high | Prior art survey (FormalizedFormalLogic, arXiv:2410.23765, Coq), 4 design patterns compared |
| C | Critic | completed | high | Four-semantics proliferation risk, missing `Evaluate`↔`AlgEvaluate` bridge, truncated message gap |
| D | Horizons | completed | high | Strategic alignment with `FromPropositional` embedding, modular PR strategy, long-term modal logic concerns |

## References

- Zulip thread: CSLib > Propositional Logic (messages 602336739–605341190)
- CSLib codebase: `Cslib/Logics/Propositional/` (Defs, Semantics, ProofSystem, NaturalDeduction, Metalogic)
- FormalizedFormalLogic (Lean 4): https://formalizedformallogic.github.io/Book/
- arXiv:2410.23765 — Intuitionistic Propositional Logic in Lean
- Thomas Waring's branches: `cslib_SKI/hilbert`, `cslib_SKI/kripke`, `cslib_SKI/intuitionistic`
