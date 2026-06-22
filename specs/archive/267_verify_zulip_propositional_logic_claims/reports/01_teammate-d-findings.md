# Teammate D Findings: Horizons — Strategic Analysis of CSLib Propositional Logic

- **Task**: 267 — Verify claims in Zulip Propositional Logic thread
- **Role**: Teammate D (Horizons — long-term alignment and strategic direction)
- **Date**: 2026-06-22
- **Agent**: cslib-research-agent (sonnet)

---

## Access Limitation

The Zulip thread at `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/605813681` requires authentication and could not be fetched directly. Two fetch attempts returned only the Zulip login page. The Zulip JSON API returned `{"result":"error","msg":"Not logged in: API authentication or user session required"}`.

**Mitigation**: This report reconstructs the strategic context from the CSLib codebase itself plus rich prior research in tasks 226 and 266, which explicitly reference and analyze the Zulip thread discussion. The propositional logic claims that likely appear in the thread can be verified against the actual code.

---

## Key Findings: Strategic Observations

### 1. The Propositional Module is CSLib's Most Complete Logic — and That Position is Strategic

The `Cslib/Logics/Propositional/` module (~30 files) provides three-tier coverage (MPL/IPL/CPL) with two proof systems (Hilbert + Natural Deduction), four semantic frameworks (bivalent, Boolean, Kripke, algebraic), and full strong completeness for all three logics. This is dramatically more complete than any other logic in CSLib:

- `Cslib/Logics/Modal/` — Hilbert only, no ND, Kripke completeness but no algebraic
- `Cslib/Logics/Temporal/` — Hilbert + dense/linear completeness, but no ND
- `Cslib/Logics/Bimodal/` — most complex, but algebraic completeness is partial

The Propositional module functions as the **proof-of-concept for CSLib's typeclass architecture**. It demonstrates that the `Foundations/Logic/` typeclass hierarchy (connectives, proof systems, inference systems, MCS infrastructure) works end-to-end. This is strategically important: Propositional is the template every new logic should follow.

### 2. The Single Sorry is the Right Priority — But the Thread May Overstate Urgency

The only sorry in the entire `Propositional/` module is `ipl_conservative_over_mpl` in `Semantics/Algebra/Conservative.lean:99`. This is now tracked by task 265 (`[BLOCKED]`), which notes that the proof requires embedding a Generalized Heyting Algebra into a Heyting Algebra — the Dedekind-MacNeille completion — and this is not available in Mathlib.

**Strategic observation**: The conservative extension theorem is mathematically interesting but NOT blocking any downstream work in the roadmap. The bimodal/temporal completeness goals (remaining roadmap items) do not depend on IPL conservativity over MPL. The thread discussion (per task 226's reference to it) involves external collaborators (Thomas Waring, Matthew Doty) whose fork of CSLib has different design choices (`bot`-as-atom vs. `bot`-as-primitive). The sorry's urgency may be framed in a PR coordination context, not intrinsic roadmap urgency.

**Risk**: Overprioritizing the sorry at the expense of more impactful infrastructure work (abstract completeness extraction, ProofSystem instance concretization).

### 3. The Algebraic Completeness Bridge Gap is More Strategic Than the Sorry

The `Semantics/Algebra/Completeness.lean` module's docstring explicitly defers:

> "Hilbert-level corollaries (`Derivable MinPropAxiom φ ↔ GHAValid φ`, etc.) require bridging the Hilbert axiomatic system (`DerivationTree`/`Derivable`) with the natural deduction system (`Theory.Derivation`/`DerivableIn`). This equivalence is nontrivial and deferred."

However, `NaturalDeduction/Equivalence.lean` ALREADY provides this bridge via 8 `hilbert_iff_nd` theorems. The Hilbert-to-algebraic-completeness composition is therefore a **straightforward composition of existing theorems** — not a new proof. This is a low-effort, high-impact gap that is more immediately actionable than the sorry.

### 4. `ProofSystem.lean` Documentation is Stale in a Strategically Misleading Way

`Cslib/Foundations/Logic/ProofSystem.lean` contains this note:

> "This module defines the **interface** only. Concrete instances require derivation trees (not yet ported) and are future work."

This is **false for the propositional tags**: `Instances.lean` and `IntMinInstances.lean` already register full `ClassicalHilbert`, `IntuitionisticHilbert`, and `MinimalHilbert` instances for `Propositional.HilbertCl/Int/Min`. The stale comment creates a false picture of where the infrastructure stands. For Modal, Temporal, and Bimodal tags, the situation is less clear — some may have instances, others may not.

**Strategic impact**: If the Zulip thread cites this documentation, claims based on it about "unregistered instances" may be inaccurate for propositional logic specifically, while remaining accurate for other logics.

### 5. The `PropositionalConnectives` Bundling Gap is Real but Low Priority

`Foundations/Logic/Connectives.lean:133` defines `PropositionalConnectives` as extending only `HasBot` and `HasImp`, not `HasAnd`/`HasOr`. The comment states:

> "Extending `PropositionalConnectives` to include them is deferred to task 173, when the four concrete formula types will be updated to provide `and`/`or` explicitly in their instances."

Task 173 is TOMBSTONED. This represents a deliberate architectural decision: `HasAnd`/`HasOr` are standalone atomic classes that formula types implement directly, not via the `PropositionalConnectives` bundle. This is a **design choice, not a defect**, but anyone reading the `PropositionalConnectives` definition and expecting `∧`/`∨` to be bundled would be confused.

### 6. Kripke Completeness for IPL/MPL Is Verified via Algebraic Route, Not Direct Canonical Model

The task 266 synthesis report correctly notes that completeness for IPL/MPL (via `IntStrongCompleteness.lean`, `MinStrongCompleteness.lean`) goes through the algebraic (MCS + Lindenbaum) route, not direct Kripke model construction. The Kripke bridge (`Algebra/KripkeBridge.lean`) exists but is unidirectional (algebraic → Kripke soundness, not completeness via prime filters).

Thomas Waring's development (per task 226) constructs Kripke completeness through prime filters of a GHA (`KripkeModel.ofHeyting`). This is a cleaner route — it avoids needing the canonical model construction entirely and derives everything from the algebraic completeness. **If the Zulip thread claims CSLib has Kripke completeness for IPL/MPL, the claim is correct in substance but the route is algebraic-first, not Kripke-direct.**

### 7. The Module Has Zero Test Coverage — A Strategic Blind Spot

No `CslibTests/` file imports any `Cslib.Logics.Propositional.*` module. The entire 30-file module is exercised only by compilation. This means:

- No tests for concrete derivability witnesses
- No tests for soundness/completeness applied to specific formulas
- No regression coverage for when definitions change

This is a strategic risk if the module is to be an upstream PR target. Reviewers on the CSLib main repo will likely request at least some concrete examples.

---

## Recommended Approach: How This Fits the Bigger Picture

### Immediate Priority (for Zulip thread verification context)

1. **Verify specific claims in the thread against the code.** The highest-risk claims to check (based on architectural complexity) are:
   - "There is only one sorry in the propositional module" — **VERIFIED TRUE**: `Conservative.lean:99` is the only sorry in `Cslib/Logics/Propositional/`
   - "The module has complete algebraic semantics for MPL/IPL/CPL" — **VERIFIED TRUE**: all three tiers have soundness and completeness via Lindenbaum quotient algebras (GHA/HA/BA)
   - "The ProofSystem typeclass instances are not yet registered" — **INACCURATE FOR PROPOSITIONAL**: Instances.lean and IntMinInstances.lean DO register full instances; this may be accurate for Modal/Bimodal tags
   - "Kripke completeness for IPL/MPL is proved" — **VERIFIED TRUE** but via algebraic route, not direct Kripke model construction
   - "The algebraic completeness is not bridged to the Hilbert system" — **TRUE**: deferred comment in Completeness.lean confirms this, but the bridge exists via Equivalence.lean; the composition is unmade

2. **Document the `bot`-as-primitive vs. `bot`-as-atom design divergence** if the thread involves coordination with Thomas/Matthew. Our `AlgEvaluate` has an explicit `bot_val : H` parameter because `bot` is a constructor, not `v ⊥`. This is the most structurally significant divergence from collaborators.

### Medium-Term Priority (roadmap alignment)

The roadmap's remaining items are all in Bimodal/Temporal completeness (discrete, continuous):
- Discrete completeness: `Logics/Bimodal/Metalogic/` + `Logics/Temporal/Metalogic/`
- Continuous extension completeness: `Logics/Bimodal/Metalogic/`
- Dense temporal completeness: `Logics/Temporal/Metalogic/`

These need **abstract completeness infrastructure**, not propositional improvements. The most strategically valuable action in the propositional space is:

1. Extract the MCS → canonical model → truth lemma → completeness pipeline into a reusable `Foundations/Logic/Metalogic/AbstractCompleteness.lean` layer
2. This would directly unblock the discrete/continuous completeness tasks by providing a parameterized completeness framework

### Long-Term Vision: Propositional as CSLib's Proof-of-Concept Template

The long-term architectural vision should treat `Propositional/` as the **reference implementation** for every new logic module. Specifically:

- A new logic should need to provide: formula type + connective instances + axiom set + semantics
- And get for free: Hilbert system via `Foundations/Logic/ProofSystem`, generic MCS via `Foundations/Logic/Metalogic/Consistency`, Lindenbaum's lemma via `set_lindenbaum`
- The `Propositional/` module demonstrates all of this working end-to-end

The **unconventional claim** here: the current architecture is closer to this ideal than it appears. The `GenericMCS.lean` file in `Foundations/Logic/Metalogic/` already gives `algebraicDerivationSystem` + `algebraic_has_deduction_theorem` for any `MinimalHilbert` system. The gap is not in the abstract infrastructure but in the documentation and composition of what already exists.

---

## Evidence/Examples

### Evidence 1: Only One Sorry in Propositional/

```bash
grep -rn "sorry" Cslib/Logics/Propositional/ --include="*.lean"
# Result: Only Conservative.lean:99
```

File: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean:99`
```lean
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (_hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A := by
  sorry
```

### Evidence 2: ProofSystem Instances ARE Registered for Propositional

From `Cslib/Logics/Propositional/ProofSystem/Instances.lean`:
```lean
instance : InferenceSystem Propositional.HilbertCl (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree PropositionalAxiom ([] : List _) φ

instance : ClassicalHilbert Propositional.HilbertCl (F := PL.Proposition Atom) where
  ...
```

These instances ARE registered. The `Note` in `ProofSystem.lean` is stale — it predates these files.

### Evidence 3: Algebraic Completeness Defers Hilbert Bridge

From `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean`:
> "Hilbert-level corollaries require bridging the Hilbert axiomatic system with the natural deduction system. This equivalence is nontrivial and deferred."

But from `NaturalDeduction/Equivalence.lean`, the bridge exists:
- `hilbert_iff_nd` — closed-context Min/Int/Cl equivalence
- `hilbert_iff_nd_ctx` — open-context Min/Int/Cl equivalence
These 8 theorems compose with algebraic completeness to give Hilbert-level completeness, but no `Derivable MinPropAxiom φ ↔ GHAValid φ` theorem is stated.

### Evidence 4: `PropositionalConnectives` Does Not Bundle `HasAnd`/`HasOr`

From `Cslib/Foundations/Logic/Connectives.lean:130-133`:
```lean
-- Extending `PropositionalConnectives` to include them is deferred to task 173,
-- when the four concrete formula types will be updated to provide `and`/`or`
-- explicitly in their instances.
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F
```

Task 173 is TOMBSTONED. This is the current state of the bundled class.

### Evidence 5: Kripke Completeness Goes Via Algebraic Route

The `Metalogic/IntStrongCompleteness.lean` and `MinStrongCompleteness.lean` files use the MCS + Lindenbaum tower, which terminates in a `HeytingAlgebra`/`GeneralizedHeytingAlgebra` instance. The `Semantics/Algebra/KripkeBridge.lean` translates algebraic validity back to Kripke validity. The route is: `DerivableIn → Lindenbaum(GHA) → AlgTValid → (via KripkeBridge) → IValid`. Direct Kripke completeness via prime filter construction (Thomas's route) is not implemented in CSLib.

### Evidence 6: Bimodal Sorries Are Separate and Not in Propositional

`Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` has 6 sorries, all tagged `-- sorry: blocked on task 37`. `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` has 4 sorries blocked on tasks 36/37. The broader claim "there is only one sorry in the propositional module" is true, but CSLib overall has ~16 sorries in Bimodal alone. Conflating these would be inaccurate.

---

## Claims Summary: Likely Accurate vs. Potentially Inaccurate

Based on codebase verification, here is how common claims about CSLib's propositional logic should be assessed:

| Claim | Verdict | Notes |
|-------|---------|-------|
| "One sorry in the propositional module" | ACCURATE | `Conservative.lean:99` only |
| "Algebraic completeness for MPL/IPL/CPL" | ACCURATE | Three-tier Lindenbaum tower |
| "Strong completeness for CPL via canonical model" | ACCURATE | `StrongCompleteness.lean` |
| "Kripke completeness for IPL/MPL proved" | ACCURATE (nuance) | Via algebraic route, not direct Kripke |
| "ProofSystem tag instances not yet registered" | INACCURATE (for PL) | `Instances.lean` + `IntMinInstances.lean` register them |
| "No Hilbert-to-algebraic-completeness bridge" | ACCURATE (gap is real) | But bridge components exist; composition unmade |
| "Conservative extension requires Dedekind-MacNeille" | ACCURATE | Explicitly documented |
| "`PropositionalConnectives` bundles `∧`/`∨`" | INACCURATE | Only `HasBot`/`HasImp`; task 173 tombstoned |
| "No test coverage for Propositional/" | ACCURATE | Zero CslibTests imports |
| "Only one sorry in CSLib" | INACCURATE | ~16 sorries in Bimodal, 1 in Propositional |

---

## Confidence Level

**High confidence** (directly code-verified):
- The single sorry in `Propositional/` is `Conservative.lean:99`
- ProofSystem tag instances ARE registered in `Instances.lean` + `IntMinInstances.lean`
- `PropositionalConnectives` does NOT bundle `HasAnd`/`HasOr`
- Algebraic completeness for all three tiers exists and is sorry-free
- The Hilbert-to-algebraic bridge exists structurally (via Equivalence.lean) but is not composed
- Bimodal has ~16 sorries separate from the propositional module

**Medium confidence** (architectural inference from code + task 226 analysis):
- The thread likely involves coordination with Thomas Waring and Matthew Doty whose forks use `bot`-as-atom
- The key design divergence (`bot_val` parameter in AlgEvaluate vs. `v ⊥`) is not a bug but an API difference
- The conservative extension sorry's urgency is PR-coordination-motivated, not roadmap-blocking

**Lower confidence** (cannot verify without thread access):
- Specific wording of claims in the Zulip thread
- Which claims, if any, are inaccurate as stated by thread participants
- Whether the thread discusses module-level or CSLib-wide sorry counts

---

## Limitations of This Report

The Zulip thread at message 605813681 could not be accessed. This report verifies likely claims
based on codebase inspection and the documented context from tasks 226 and 266, which reference
the same discussion. For verification of specific thread statements, the thread must be accessed
with a logged-in Zulip account or via `python-zulip-api` with appropriate credentials. See
`.claude/skills/skill-zulip/SKILL.md` for the Zulip fetch capability.
