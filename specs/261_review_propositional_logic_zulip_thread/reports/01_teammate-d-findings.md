# Teammate D: Strategic Horizons and Long-term Alignment
## Task 261 — Review Propositional Logic Zulip Thread

---

## Key Findings

### Thread Participants and Positions

**Benjamin Brast-McKie** (primary contributor, PR #648):
- Implemented Hilbert systems for MPL/IPL/CPL with soundness and completeness.
- Established ND equivalence and deduction theorem.
- Advocates for `⊥` as a **primitive constructor** (not an atom).
- Added dual-layer semantics: `Evaluate` (Prop-valued) + `BoolEvaluate` (Bool-valued) with a bridge lemma.
- Argues uniformity with Kripke semantics (modal/temporal) requires Prop-valued evaluation.

**Thomas Waring** (drafts in branches `cslib_SKI/hilbert` and `cslib_SKI/kripke`):
- Wrote the existing ND system in CSLib; has held off PRing due to existing open PRs.
- Proposes `GeneralizedHeytingAlgebra` (GHA) as the canonical semantic target, capturing MPL.
- Prefers MPL as the base (most minimal, encodes others via theory construction).
- Advocates for a parametric completeness theorem: `DerivableIn T A ↔ ∀ H [GHA] v, (v ⊨ T) → v ⊨ A`.
- Critical of `bot_val` as an extra parameter; prefers `⊥`-as-atom for GHA compatibility.

**Matthew Doty** (working on DPLL/SAT, Tseitin transformation):
- Needs `Atom → Bool` semantics for computable decision procedures.
- Questioned whether dual semantics (Prop + Bool) is necessary; suggested unified `Bool` approach.
- Agrees on explicit `⊥` constructor (sides with Benjamin on this).
- Interested in porting Harrison's *Handbook of Practical Logic* (DPLL, SAT solving).
- Raises concern about `⊥`-as-atom complexity for DPLL clause manipulation.

**Ching-Tsun Chou** (mentioned via PR comment):
- Suggested `Bool.lean` alone might suffice (noted by Benjamin as alternative to dual-file approach).
- Supports separate `bot` constructor.

### Core Technical Disagreements

1. **`⊥` as primitive vs. `⊥` as atom**:
   - Benjamin + Matthew + Chou: `⊥` should be a primitive constructor in the inductive type.
   - Thomas (original position): `⊥`-as-atom works for GHA-based development; `⊥`-as-primitive forces efq into the derivation type.
   - **Resolution emerging**: Benjamin's PR #648 already has primitive `⊥` and Thomas's compromise branch (`intuitionistic/`) accepts translations between frameworks.

2. **Prop-valued vs. Bool-valued semantics**:
   - Benjamin: Prop-valued is primary (Kripke uniformity), Bool as secondary with bridge.
   - Matthew: Bool-valued is more natural for decision procedures; proposed unified approach.
   - Thomas: GHA-polymorphic evaluation covers both; `Bool` is a Heyting algebra.
   - **Status**: PR #648 already implements dual-layer approach with `Algebra.lean` adding GHA-polymorphic `AlgEvaluate` with `bot_val` parameter.

3. **MPL vs. IPL as base**:
   - Thomas: MPL is most general; IPL/CPL are encoded via theory construction (`Theory.IPL`, `Theory.CPL`).
   - Benjamin: Works from IPL/CPL for bimodal compatibility; MPL is included.
   - **Current CSLib state**: `Defs.lean` has `Proposition` with primitive `{atom, bot, imp, and, or}` and theories `MPL/IPL/CPL` as `Theory Atom` values—Benjamin's approach.

4. **Single formula type vs. multiple formula types**:
   - Thomas: Different applications may want different base types (fragment-specific inductives).
   - Benjamin: Single `Proposition` type with uniform substitution theory.
   - Matthew: Sides implicitly with Benjamin for DPLL compatibility.

---

## Strategic Alignment Assessment

### CSLib's Established Hierarchy

From `ROADMAP.md` and the existing codebase, the architecture is:

```
Foundations/Logic  →  Propositional  →  Modal  →  Bimodal
                                      ↘  Temporal  ↗
```

This design was committed to *before* the Zulip thread. Key consequences:

1. **`FromPropositional.lean`** (both Modal and Temporal) depends on `Propositional.Defs` having a unified `Proposition` type with `{atom, bot, imp, and, or}` as primitives.
2. **`AlgEvaluate`** in `Semantics/Algebra.lean` already implements the GHA-polymorphic evaluator with `bot_val` — Thomas's approach is already partially incorporated.
3. **`BoolEvaluate`** in `Semantics/Bool.lean` is already available for Matthew's use case.
4. The `PropositionalConnectives` typeclass in `Foundations/Logic/Connectives.lean` ties everything together.

### What the Thread is Actually About

The thread is less about fundamental design choices (most are already made) and more about:
- **Validation seeking**: Benjamin wants community buy-in for PR #648 design decisions.
- **Coordination**: Thomas has competing implementations in branches; both want to avoid duplication.
- **Feature requests**: Matthew needs specific capabilities for SAT/DPLL work.
- **Converging perspectives**: All three are moving toward compatible designs.

---

## Long-term Architecture Considerations

### The Logic Hierarchy

CSLib's current and planned hierarchy (from ROADMAP.md):

```
Propositional → Modal (K, T, S4, S5, B, D, ...) → Temporal (BX) → Bimodal
                                                                   ↗
                                              (Temporal embeds in Bimodal)
```

**Future extensions** that the design must accommodate:
1. **Epistemic logic** (multi-agent modal): requires multi-modal box operators.
2. **Dynamic logic** (PDL, CTL): adds program modalities.
3. **Linear/substructural logics**: may need separate formula types (Thomas's point is valid here).
4. **Model checking** (already present via `LTL/ModelChecking.lean`): needs computable semantics.
5. **HML** (Hennessy-Milner Logic): already in CSLib, uses its own formula type.

### Critical Architecture Constraint

The `FromPropositional.lean` embedding pattern is the load-bearing architectural commitment. It means:
- `PL.Proposition` must have native `and`/`or` (the Lukasiewicz encoding would break intuitionistic soundness at the propositional level).
- `Modal.Proposition` uses Lukasiewicz for `and`/`or` (since it lacks native constructors) — this is acceptable for classical modal logic.
- The embedding `PL.Proposition.toModal` encodes PL `and`/`or` via Lukasiewicz, which is semantically coherent only classically.

**Long-term implication**: If CSLib ever adds non-classical modal logic (intuitionistic modal logic), the current `Modal.Proposition` will need revision or a parallel type. Thomas's point about fragment-specific types has merit here.

### The `bot_val` Design Choice

Benjamin's `AlgEvaluate` with explicit `bot_val` parameter is the right design for *this library's scope*:
- It correctly captures MPL semantics without forcing efq.
- It does not contradict Thomas's GHA-completeness theorem — the parametric `(v, bot_val)` pair is exactly Thomas's `v ⊨ T` setup.
- It preserves uniformity with Kripke semantics (where `Satisfies m w .bot = False` is a fixed semantic clause, not a model parameter).

The remaining semantic gap between approaches is narrower than the thread suggests: both Thomas and Benjamin have now implemented GHA-polymorphic evaluation. The `bot_val` vs. `⊥`-as-atom debate is resolved in favor of primitive `⊥` given the DPLL use case and substitution theory.

---

## Community and Adoption Perspective

### Positioning Relative to Mathlib

Mathlib already has:
- `Propositional` logic formalization in `Mathlib.Logic.Propositional` (rudimentary).
- `PropositionalLogic` interface in some form.
- No comprehensive Hilbert + ND + algebraic semantics combo.

CSLib's propositional logic can carve a distinctive niche by offering:
1. **Multi-system coverage**: MPL, IPL, CPL — all in one formalization with equivalence proofs.
2. **Metalogical depth**: Strong completeness, deduction theorem, MCS theory.
3. **Computable semantics**: BoolEvaluate + DPLL (Matthew's contribution) makes it practically useful.
4. **Algebraic lift**: GHA/HA/BA semantics covering all three logic strengths uniformly.
5. **Upward compatibility**: The `FromPropositional` embedding guarantees PL results lift to modal/temporal logics.

### What Would Make Adoption Easier

1. **A clear entry point**: The `Defs.lean` module header is well-documented. Need similar quality for `Semantics/` and `ProofSystem/` modules.
2. **The `v ⊨ T` notation**: Thomas's pattern is more readable and should be surfaced in the public API.
3. **Decide instances**: The `Decidable` instance for `Tautology` (via `BoolEvaluate`) enables `decide` tactics and native_decide.
4. **Documentation of the architecture**: A clear explanation of why dual semantics exist (Prop for theory, Bool for computation) would reduce confusion for new contributors.

---

## Creative Alternatives

### A Layered Compromise Design

Rather than forcing an either/or choice, the current codebase (as of PR #648) already implements a layered design:

```
Layer 0: PL.Proposition (inductive with {atom, bot, imp, and, or})
          ↓
Layer 1a: Evaluate (Atom → Prop) — for classical completeness
Layer 1b: AlgEvaluate (Atom → GHA, bot_val) — for MPL/IPL/CPL algebraic completeness
Layer 1c: BoolEvaluate (Atom → Bool) — for DPLL/SAT computation
          ↓
Bridge lemmas connecting all three layers
```

This satisfies all parties:
- **Thomas's GHA-completeness**: Already implemented in `Semantics/Algebra.lean`.
- **Matthew's Bool-semantics**: Already in `Semantics/Bool.lean`.
- **Benjamin's Kripke-uniform Prop semantics**: In `Semantics/SemanticConsequence.lean` and `Semantics/Kripke.lean`.

### The Missing Link: Explicit `v ⊨ T` Notation

Thomas's parametric completeness theorem:
```lean
theorem Theory.alg_complete [Inhabited Atom] {T : Theory Atom} {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Atom → H} {bot_val : H},
      AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤
```
...should become the *canonical statement* because it is:
1. **Most general** (quantifies over all GHAs).
2. **Satisfies all three-level specializations** by fixing the algebra class.
3. **Adopts Thomas's `v ⊨ T` framing** (via `AlgTValid`).

This already appears in `Semantics/Algebra.lean`. The synthesis response should highlight that this design is already implemented and needs PR review, not redesign.

### The PR Strategy

Rather than one large PR (#648), the optimal path given the converging positions:

1. **PR A**: `Logics/Propositional/Defs.lean` — the `Proposition` type, `Theory`, and `MPL/IPL/CPL` definitions. Small and uncontroversial.
2. **PR B**: `ProofSystem/` — Hilbert system for MPL/IPL/CPL. Builds on PR A.
3. **PR C**: `NaturalDeduction/` — ND system. Builds on PR A. Can be merged independently of PR B.
4. **PR D**: `Semantics/` — All semantic layers (Evaluate, AlgEvaluate, BoolEvaluate, Kripke). Builds on PR A.
5. **PR E**: `Metalogic/` — Completeness theorems. Builds on B, C, D.
6. **PR F**: Matthew's DPLL/SAT work. Builds on D.

This modular approach avoids the "one big PR" coordination problem and lets Thomas review the specific pieces he has opinions on without blocking the whole effort.

---

## Confidence Level

**High** on:
- The technical facts about the existing codebase (read directly from source).
- The thread content (fetched via Zulip API with full message text).
- The strategic alignment assessment (the design in PR #648 already synthesizes all three positions).
- The modular PR strategy being viable.

**Medium** on:
- Whether the CSLib maintainers (beyond the three thread participants) have additional constraints or preferences not reflected in the thread.
- The timeline for Thomas's competing branches being merged or abandoned.
- Whether future non-classical modal logic additions will require architectural revision to `Modal.Proposition`.

**Low** on:
- Probability logic (Matthew's speculative suggestion) — this is a much larger research area and not a near-term CSLib goal.
- Whether a separate `CslibStructural` namespace (Matthew's pedantic suggestion) would be adopted.

---

## Summary for Synthesis

The Zulip thread reveals **convergence, not fundamental conflict**. The three positions are:

| Contributor | Core Concern | Status in PR #648 |
|-------------|-------------|-------------------|
| Thomas Waring | GHA-polymorphic semantics; MPL primacy; modular PRs | Implemented via `AlgEvaluate` + `AlgTValid` |
| Matthew Doty | Bool semantics for DPLL; explicit `⊥` constructor | Implemented via `BoolEvaluate`; `⊥` is primitive |
| Benjamin Brast-McKie | Kripke uniformity; Hilbert + ND + algebraic all-in-one | Base architecture of PR #648 |

The balanced response should:
1. **Acknowledge that the design already satisfies all stated requirements** — GHA completeness, Bool evaluation, Prop semantics, and primitive `⊥`.
2. **Recommend the modular PR strategy** to unblock review and avoid coordination overhead.
3. **Elevate Thomas's `v ⊨ T` notation** as the canonical public API for completeness statements.
4. **Frame the DPLL work** as a natural extension that stacks on the semantic layer, not requiring base changes.
5. **Note the architectural commitment** to `FromPropositional` embeddings as a long-term constraint that validates the current single-type design over Thomas's fragment-type alternative.
