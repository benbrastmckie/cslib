# Teammate A Findings: Propositional Logic Zulip Thread Analysis

**Task**: Review Zulip thread on propositional logic setup in CSLib and craft a balanced response

**Thread URL**: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/with/604219492

**Date Analyzed**: 2026-06-21

---

## Key Findings

The Zulip thread (22 messages, spanning 2026-06-07 to 2026-06-16) involves three CSLib contributors debating the design of propositional logic foundations in CSLib. The thread originated when Benjamin Brast-McKie shared his propositional logic Hilbert system implementation and Matthew Doty asked about assignment semantics for a DPLL project. The discussion quickly revealed two separable but intertwined design disputes:

1. **Whether `⊥` should be a primitive constructor or an atom** — the core architectural dispute
2. **Whether valuations should be `Atom → Prop` or `Atom → Bool`** — a secondary but real dispute about computability

The thread ends with Benjamin making his most developed argument for primitive `⊥` with an explicit `bot_val` parameter. Thomas responds with a compromise branch and restates his case for minimal logic as the base. The thread is unresolved at the time of writing.

The current codebase (in `main`) reflects Benjamin's design: `⊥` is a primitive constructor, `AlgEvaluate` takes an explicit `bot_val : H` parameter, and both `Prop` and `Bool` evaluators coexist with a bridge lemma.

---

## Participants and Positions

### Benjamin Brast-McKie (6 messages)

**Role**: Primary implementer, working backwards from bimodal/modal logic toward propositional foundations.

**Core position**: `⊥` must be a primitive constructor, and the `bot_val` parameter cleanly handles the MPL need to let `⊥` be interpreted freely. Advocates for dual `Prop`/`Bool` semantics with a bridge lemma, motivated by uniformity with modal/temporal Kripke semantics (which are irreducibly `Prop`-valued).

**Key arguments**:
- Substitution invariance: `⊥` is a nullary operation symbol (like `→`, `∧`), fixed under every substitution. With `⊥`-as-atom, all substitution theorems (`subst_preserves_axiom`, `hilbertSubstitution`, etc.) acquire side conditions `σ(⊥) = ⊥`, breaking the free-algebra / Kleisli-category structure.
- Universal algebra ontology: atoms are generators, connectives (including nullary ones) are operations. `⊥` belongs with the connectives.
- The `bot_val` parameter is cheap: one extra argument to `AlgEvaluate`, one field (`botForces`) in `KripkeModel`. The `⊥`-as-atom alternative pushes the constraint `v ⊥ = ⊥` into every theorem statement and every model construction.
- The `v ⊨ T` style completeness theorem (Thomas's elegant parametric framing) is compatible with primitive `⊥` + `bot_val`: quantifying over `(v, bot_val)` pairs is orthogonal to the proposition type design.
- The `Prop`-valued canonical model is forced by `fun p => atom p ∈ S` (MCS membership is not decidable), so `Prop` stays primary; `Bool` is a computable companion layer.

### Thomas Waring (7 messages)

**Role**: Natural deduction expert, earlier CSLib contributor with existing ND system. Working on algebraic semantics from the GHA side.

**Core position**: Minimal logic should be the base theory, with `⊥` treated as an atom so that it can be absent. The natural deduction system was designed so that `MPL` (Johansson 1937) has no axioms — it is the logic of the ND rules themselves. IPL and CPL are theory extensions. With `⊥` as primitive constructor, efq would need to be a rule, not a theory parameter.

**Key arguments**:
- Natural deduction symmetry: each formula constructor should correspond to introduction and elimination rules. Adding `⊥` as a constructor without its corresponding efq rule breaks the symmetry.
- Algebraic: a `GeneralizedHeytingAlgebra` has no bottom element — that is precisely the right algebra for minimal logic. Adding `⊥` to the signature forces interpretation into a `HeytingAlgebra`.
- IPL can be encoded in MPL via the theory construction (`WithBot`-extended atom type) — no need to change the syntax.
- The `bot_val` field is "unnatural" from the GHA perspective: it exists to patch the mismatch between the signature (which includes `⊥`) and the algebra (which does not).
- The general completeness theorem with `v ⊨ T` style is elegant and avoids this issue entirely.
- Acknowledges that there is a pragmatic community question: if the community wants IPL as the base, Thomas will defer.
- Shares a compromise branch (`thomaskwaring/cslib_SKI/intuitionistic`) with a separate intuitionistic type that translates into the existing MPL framework.

### Matthew Doty (9 messages)

**Role**: Applied/computational user, working on DPLL/SAT, CNF, and probability logic formalization. Most messages in the thread.

**Core position**: Pragmatically endorses primitive `⊥` (with Ching-Tsun Chou), would prefer `Bool` semantics, and is willing to settle for the `Prop`-based approach if it is uniform. Raises the concern that `⊥`-as-atom adds DPLL complexity.

**Key arguments**:
- `Atom → Bool` is more portable for decision procedures (DPLL needs computable model construction).
- However, the thread reveals that all of CSLib uses `Prop`-based semantics (`ωAcceptor`, Thomas's draft PR), so Bool-only would be architecturally inconsistent.
- Agrees with `HasInterp` typeclass abstraction as a way to support both `Prop` and `Bool` via typeclass inference.
- Proposes using `decide` + `Classical.propDecidable` to unify the two evaluators into one, though acknowledges this makes the truth lemma "clumsy."
- With `⊥`-as-atom, DPLL would need to handle `pos ⊥` removal from every clause and ensure `v ⊥ = ⊥` in output valuations — agrees this is awkward.
- Interested in Dedekind-MacNeille completion to strengthen completeness from GHA to HA.

### Ching-Tsun Chou (mentioned, not directly quoted)

- Mentioned by Benjamin as agreeing that `Bool.lean` alone would suffice (for the `Prop`/`Bool` issue).
- Also mentioned as endorsing a separate `bot` constructor.

---

## Desiderata Mapping

| Desideratum | Benjamin | Thomas | Matthew |
|---|---|---|---|
| Primitive `⊥` constructor | Strong yes | No | Weak yes |
| `⊥` as atom (for MPL) | No | Strong yes | Neutral |
| `bot_val` parameter on evaluator | Yes | No (uses GHA without bottom) | Neutral |
| `Prop`-based primary semantics | Yes | Yes (in draft PR) | Weak no |
| `Bool`-based computable evaluator | Yes (as layer) | Yes (via HasInterp) | Strong yes |
| Unified polymorphic evaluator (GHA) | Yes (done: `AlgEvaluate`) | Yes (prefers no bot_val) | Yes (for HeytingAlgebra) |
| v ⊨ T parametric completeness style | Yes | Yes (originated this) | Neutral |
| Separate IPL type (Thomas's branch) | Neutral | Yes | Neutral |
| MPL as base, IPL as extension | Partial (via Theory param) | Strong yes | Neutral |
| Uniformity with modal/temporal logics | Strong yes | Neutral | Neutral |
| DPLL-friendly design | Partial | Neutral | Strong yes |

---

## Conflicts Identified

### Conflict 1: `⊥` as primitive constructor vs. atom (PRIMARY)

This is the fundamental unresolved disagreement.

**Thomas's view**: With `⊥` as a primitive constructor, you need `bot_val` to interpret it in GHA (which has no `⊥`), and this is architecturally "unnatural." The ND system was designed around the fact that minimal logic has no axioms about `⊥` — the theory parameter (`MPL = ∅`) does the work. Making `⊥` an atom lets substitutions freely remap it, enabling conservative extension results (IPL conservative over MPL) via unrestricted valuations.

**Benjamin's view**: `⊥` is a logical constant, not a variable. Its syntactic status as a nullary operation means it must be fixed by substitution homomorphisms. Every substitution theorem would need a `σ(⊥) = ⊥` side condition with `⊥`-as-atom. The free algebra structure is broken. `bot_val` is a small price that gives a clean semantic parameter.

**Resolution difficulty**: High. Both positions have genuine merit. Benjamin's argument from universal algebra / free-algebra theory is strong on principle. Thomas's argument from ND symmetry and GHA naturality is strong on design elegance. The key empirical question is: how much does the `σ(⊥) = ⊥` side condition actually propagate in practice?

**Current codebase choice**: Benjamin's design (primitive `⊥`, `bot_val` parameter). The existing code has `subst_preserves_axiom`, `hilbertSubstitution`, etc., all working without side conditions.

### Conflict 2: `Prop` vs. `Bool` semantics (SECONDARY, largely resolved)

**Matthew's original request**: `Atom → Bool` for DPLL.

**Resolution**: Largely resolved in the codebase. The current `Semantics/Bool.lean` provides `BoolEvaluate` alongside `Evaluate`, with bridge lemma `BoolEvaluate_eq_iff`. The `AlgEvaluate` over GHA provides the polymorphic foundation. Thomas's `HasInterp` typeclass approach would also support this. The community consensus (including Thomas and Ching-Tsun Chou) is that the algebraic evaluator over a typeclass is the right abstraction.

**Open question**: Whether two separate evaluation functions (`Evaluate` + `BoolEvaluate`) or a single polymorphic `AlgEvaluate` (specialized via typeclass inference) is the better API. Matthew proposed collapsing to `decide`-based canonical valuation; Benjamin rejected this on uniformity grounds with modal semantics.

### Conflict 3: Where to start — MPL vs. IPL (STRUCTURAL)

**Thomas**: MPL is the right base; IPL and CPL are theory extensions. The current ND system reflects this cleanly.

**Benjamin**: IPL (or at minimum, primitive `⊥`) is needed for the chain of logics (propositional → modal → temporal → bimodal). The Hilbert systems and completeness proofs are designed around the `⊥`-primitive paradigm.

**Current codebase**: Both coexist — `Theory.MPL = ∅`, `Theory.IPL`, `Theory.CPL` are all defined, and the `NaturalDeduction/Basic.lean` uses the theory parameter to control logic strength.

---

## Recommended Approach

Based on full analysis of the thread and the current codebase, the following synthesis is recommended:

### 1. Affirm the current `⊥`-as-primitive design (primary recommendation)

Benjamin's argument from substitution invariance is decisive. The existing codebase with `subst_preserves_axiom`, `hilbertSubstitution`, and monad structure already demonstrates the benefit: all substitution theorems work uniformly without `σ(⊥) = ⊥` side conditions. The `bot_val` parameter is a modest cost that cleanly separates two degrees of freedom:

- **Syntactic degree of freedom**: the formula type itself (which connectives are primitive)
- **Semantic degree of freedom**: what `⊥` evaluates to in a model

These are genuinely distinct, and conflating them (by making `⊥` an atom to get "free" semantic freedom) trades a small API simplification for a fundamental logical category error.

Thomas's concern about GHA naturality is valid but addressable: `AlgEvaluate` with `bot_val` is the right interface for GHA, and the current code already adopts this. The `bot_val` parameter is not "unnatural" — it is precisely the "designated constant" of Johansson algebras.

### 2. Adopt Thomas's `v ⊨ T` completeness style (secondary recommendation)

Benjamin already endorses this in his final message. This is not in conflict with primitive `⊥`. The parametric completeness theorem `DerivableIn T A ↔ ∀ v bot_val, (v, bot_val) ⊨ T → AlgEvaluate v bot_val A = ⊤` is both elegant and general.

This should be the primary statement of algebraic completeness, with IPL/CPL corollaries specializing to `bot_val = ⊥`.

### 3. Provide `Bool`/`Prop` bridge as the current code already does

The dual-evaluator approach (`Evaluate` + `BoolEvaluate` + bridge lemma) is the right solution. The `AlgEvaluate` over GHA subsumes both. DPLL code can use `BoolEvaluate` directly without needing to change the core metatheory.

### 4. Acknowledge Thomas's ND symmetry concern and offer a docstring explanation

The one valid gap in the current design: the `NaturalDeduction` system uses `⊥` as a constructor but has no efq as a primitive rule (it is a derived rule requiring `[IsIntuitionistic T]`). This means the ND symmetry is partially broken. This should be documented in `NaturalDeduction/Basic.lean` as a deliberate design choice, not an oversight.

### 5. On MPL-as-base vs. IPL-as-base: maintain the current theory-parameter design

The `Theory` parameter is the right abstraction. `MPL = ∅` as the minimal base, with IPL and CPL as extensions, is both elegant and flexible. Thomas's point that one can encode IPL in MPL via `WithBot`-extended atoms is correct but more complex than the current theory-extension approach. The current design should be maintained.

---

## Evidence / Examples

### Evidence for primitive `⊥` (current design)

From `Cslib/Logics/Propositional/Defs.lean` (line 128-133):
```lean
def Proposition.subst {Atom Atom' : Type u} (f : Atom → Proposition Atom') :
    Proposition Atom → Proposition Atom'
  | atom x => f x
  | bot => .bot        -- ⊥ is fixed by every substitution
  | imp A B => .imp (A.subst f) (B.subst f)
  ...
```

From `Cslib/Logics/Propositional/Semantics/Algebra.lean` (line 82-88):
```lean
def AlgEvaluate {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => bot_val    -- explicit free parameter; GHA has no ⊥
  | .imp a b => AlgEvaluate v bot_val a ⇨ AlgEvaluate v bot_val b
  ...
```

### Evidence for Thomas's concern

With the current primitive `⊥` design, one needs `bot_val` in GHA context because `GeneralizedHeytingAlgebra` has no `⊥`. The canonical completeness construction in `Semantics/Algebra/Completeness.lean` (lines 51-52) needs:
```lean
def Theory.canonicalBotVal (T : Theory Atom) : LindenbaumAlgebra T :=
  lindenbaumMk T .bot
```

This is an extra field compared to Thomas's approach (where `⊥`-as-atom would let the Lindenbaum algebra's own bottom serve).

### Evidence for Matthew's DPLL concern

With `⊥`-as-atom in DPLL, every clause processing step needs:
- Remove literal `pos ⊥` from every clause
- Remove every clause containing `neg ⊥`
- Ensure output valuations satisfy `v ⊥ = ⊥`

This is extra bookkeeping that is transparent with primitive `⊥` (where `BoolEvaluate` just maps `.bot => false`).

### Key cross-concern: `FromPropositional` embedding

`Cslib/Logics/Modal/FromPropositional.lean` already demonstrates that the PL-to-modal embedding works cleanly with primitive `⊥`:
```lean
def PL.Proposition.toModal : PL.Proposition Atom → Modal.Proposition Atom
  | .atom p => .atom p
  | .bot => .bot        -- direct mapping, no special case needed
  | .imp φ₁ φ₂ => .imp ...
```

With `⊥`-as-atom this would require a special check `if p == bot_atom then .bot else .atom p`.

---

## Confidence Level

**High** on:
- The full content of the thread (22 messages, all read in full)
- The current state of the codebase reflecting Benjamin's design choices
- The three participants' positions and their core arguments
- That the primary conflict (`⊥` primitive vs. atom) is genuinely unresolved in the thread

**Medium** on:
- The resolution recommendation (favoring current design). This reflects genuine evaluation of the arguments rather than deference to whoever wrote the most code.
- Thomas's branch content (referenced but not directly examined — available at `thomaskwaring/cslib_SKI/intuitionistic`)
- The extent to which `σ(⊥) = ⊥` side conditions would actually proliferate in Thomas's preferred design

**Low** on:
- What Ching-Tsun Chou's full position is (only mentioned indirectly by Benjamin)
- Whether the community has any implicit preference not expressed in this thread

---

## Summary for Response Drafting

The thread converges on most issues but diverges on one: whether `⊥` should be a primitive constructor (Benjamin/Matthew/Chou) or an atom (Thomas). The current codebase implements Benjamin's design. The most balanced response should:

1. Acknowledge Thomas's ND symmetry concern as a valid design principle
2. Make the case for why the current design is preferred (substitution invariance, free-algebra structure, uniformity with modal/temporal logics)
3. Explicitly adopt Thomas's `v ⊨ T` completeness style as the primary statement
4. Affirm the dual `Prop`/`Bool` evaluator approach for Matthew's DPLL use case
5. Invite Thomas to share his concern about the `bot_val` field's awkwardness, and whether documenting it as the "Johansson designated constant" helps
6. Note that the `Theory.WithBot` / `WithBot`-extended-atom approach Thomas mentions for conservative extension is worth exploring as a separate development, independent of the core design decision
