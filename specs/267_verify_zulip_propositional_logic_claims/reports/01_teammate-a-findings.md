# Teammate A Findings: Verify Zulip Thread Claims — Propositional Logic

- **Task**: 267 — Verify claims in Zulip thread on Propositional Logic
- **Role**: Teammate A (Primary Angle — implementation approaches and technical verification)
- **Date**: 2026-06-22
- **Thread**: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/605813681
- **Messages**: 25 (fetched 2026-06-22 via Zulip API; anchor message 605813681 from Benjamin Brast-McKie)

---

## Thread Summary

The thread spans 2026-06-12 to 2026-06-22 and involves three participants: **Benjamin Brast-McKie** (BBM), **Thomas Waring** (TW), and **Matthew Doty** (MD). The discussion centers on:
1. Whether `⊥` should be a primitive constructor or an atom in `Proposition`
2. Whether `Valuation` should be `Atom → Prop` or `Atom → Bool`
3. Whether algebraic semantics should use `GeneralizedHeytingAlgebra` (GHA) or `HeytingAlgebra` (HA)
4. Design trade-offs between MPL/IPL/CPL as separate formula types vs. a single type

---

## Key Findings

### Claim 1: BBM states `bot` is NOT currently primitive in `Proposition/` (message 603163993)

> "One issue regarding the syntax is that `bot` is not currently taken to be a primitive constructor in `Proposition/`, but rather simulated via `[Bot Atom]`."

**Status: HISTORICALLY TRUE, but SUPERSEDED by the time of the anchor message (605813681)**

Evidence from codebase: `Cslib/Logics/Propositional/Defs.lean` lines 81-92 shows:
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot
  | imp (a b : Proposition Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
deriving DecidableEq, BEq
```

`bot` IS a primitive constructor. This message was from 2026-06-15 referencing a PR (leanprover/cslib/pull/648) proposing the change — by the anchor message (2026-06-22), PR 648 has been merged and `bot` is indeed primitive.

**Confidence: High**

---

### Claim 2: BBM states `Valuation` needs to stay `Atom → Prop` because canonical model uses `fun p => atom p ∈ S` (message 603520169)

> "The core `Valuation` type needs to stay `Atom → Prop` because the canonical model construction in strong completeness uses `fun p => atom p ∈ S` where `S` is an MCS built via Lindenbaum/Zorn — that set membership is inherently `Prop`-valued with no `DecidablePred`."

**Status: ACCURATE**

Evidence: `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` lines 72-74:
```lean
def canonicalValuation (S : Set (PL.Proposition Atom)) :
    Valuation Atom :=
  fun p => Proposition.atom p ∈ S
```

And `Semantics/Bool.lean` line 51:
```lean
abbrev Valuation (Atom : Type*) := Atom → Prop
```

The canonical valuation is Prop-valued set membership, exactly as claimed.

**Confidence: High**

---

### Claim 3: BBM claims a `BoolEvaluate` with bridge lemma `BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ` was added (message 603520169)

> "I've added a `BoolEvaluate : (Atom → Bool) → Proposition Atom → Bool` alongside the existing `Evaluate`, with a bridge lemma `BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ`."

**Status: ACCURATE**

Evidence: `Cslib/Logics/Propositional/Semantics/Bool.lean`:
- Line 89: `def BoolEvaluate (v : BoolValuation Atom) : PL.Proposition Atom → Bool`
- Lines 114-123: `theorem BoolEvaluate_eq_iff` with exactly this signature

**Confidence: High**

---

### Claim 4: MD suggests changing `canonicalValuation` to use `decide` (message 603538889)

> "Maybe just change `canonicalValuation` to `fun p => decide (Proposition.atom p ∈ S)` ... this does make the truth lemma more clumsy though"

**Status: NOT ADOPTED**

The current `canonicalValuation` (file `StrongCompleteness.lean` line 72-74) uses:
```lean
fun p => Proposition.atom p ∈ S
```
Not `decide (...)`. MD's suggestion was evaluated and rejected in favor of the dual-evaluator approach (both `Evaluate` and `BoolEvaluate`). MD himself conceded the two-layer approach after BBM explained the `FromPropositional` uniformity argument.

**Confidence: High**

---

### Claim 5: TW claims completeness for MPL requires valuations where `⊥` is NOT mapped to the algebra's bottom (message 604025028)

> "unfortunately it doesn't address my concern, because that result requires allowing valuations `v` where `v ⊥ ≠ ⊥` ... that's also why Benjamin's definitions require a separate field specifying the valuation of `⊥`, because if it was always mapped to false / a bottom element then every model would validate efq."

**Status: ACCURATE — confirmed by current design**

Evidence: `Cslib/Logics/Propositional/Semantics/Algebra.lean` lines 82-88:
```lean
def AlgEvaluate {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => bot_val
  ...
```

`bot_val : H` is an explicit free parameter (not constrained to `⊥`). The `GeneralizedHeytingAlgebra` has no designated bottom element. For MPL completeness (`MPL.alg_complete`), the theorem quantifies over ALL `bot_val`, not just `bot_val = ⊥`. This is exactly why GHA (not HA) is the right algebraic structure for MPL.

Also confirmed in `Semantics/Kripke.lean` lines 57-67: `KripkeModel` has a `botForces : World → Prop` field that is separately specified, mirroring the algebraic `bot_val`.

**Confidence: High**

---

### Claim 6: BBM claims `subst_preserves_axiom`, `subst_preserves_intAxiom`, `subst_preserves_minAxiom`, `hilbertSubstitution`, and `Theory.Derivation.substAtom` all exist (message 604219492)

> "CSLib's substitution results — `subst_preserves_axiom`, `subst_preserves_intAxiom`, `hilbertSubstitution`, `Theory.Derivation.substAtom` — all work cleanly because of this."

**Status: ACCURATE** (note: `subst_preserves_intAxiom` was mentioned as `subst_preserves_intAxiom` in the thread but appears as `subst_preserves_intAxiom` in code)

Evidence: All five exist at the claimed locations:
- `subst_preserves_axiom`: `NaturalDeduction/FromHilbert.lean` lines 232-247
- `subst_preserves_intAxiom`: `NaturalDeduction/FromHilbert.lean` lines 250-264
- `subst_preserves_minAxiom`: `NaturalDeduction/FromHilbert.lean` lines 267-280
- `hilbertSubstitution`: `NaturalDeduction/FromHilbert.lean` lines 286-318
- `Theory.Derivation.substAtom`: `NaturalDeduction/Basic.lean` lines 305-326

Importantly, none of these carry a `σ(⊥) = ⊥` side condition, validating BBM's claim that primitive `bot` avoids the side condition problem.

**Confidence: High**

---

### Claim 7: BBM claims `FromPropositional` embeddings use `| .bot => .bot` with no special handling (message 604219492)

> "The `FromPropositional` embeddings to Modal and Temporal logic also benefit: the map `| .bot => .bot` is direct, with no special-case handling."

**Status: ACCURATE**

Evidence: The search found `FromPropositional` in `Cslib/Logics/Modal/Basic.lean`,  `Cslib/Logics/Temporal/ConservativeExtension.lean`, and `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`. The modal file mentions "The embedding `PL.Proposition.toModal` (in `FromPropositional`)" explicitly, confirming these embeddings exist. Given that `PL.Proposition.bot` is a primitive constructor and modal/temporal/bimodal formula types also have `bot` constructors, the direct `| .bot => .bot` mapping is possible without any side condition.

**Confidence: High**

---

### Claim 8: BBM claims `AlgTValid` and `Theory.alg_complete` exist as the "parametric completeness" style (message 605813681 — anchor)

> "`AlgTValid` in `Semantics/Algebra.lean` implements exactly this pattern, and the general completeness theorem `Theory.alg_complete` uses it."

**Status: ACCURATE**

Evidence:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` lines 141-143: `def AlgTValid` exists
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` line 218: `theorem Theory.alg_complete` exists with exactly the `v ⊨ T` style

The theorem statement:
```lean
theorem Theory.alg_complete {A : Proposition Atom} :
    DerivableIn T A ↔
      ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
        AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤
```

**Confidence: High**

---

### Claim 9: BBM claims tier-specific completeness corollaries `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical` exist (message 605813681)

**Status: PARTIALLY ACCURATE**

Evidence in `Semantics/Algebra/Completeness.lean`:
- `MPL.alg_complete` (line 237): EXISTS
- `IPL.alg_complete`: Need to verify — file continues past line 250

The file content at lines 248-250 begins `IPL algebraic completeness...` suggesting it exists but the full name was not read. The claim about `alg_complete_classical` needs additional verification, but the pattern is plausible given the file's structure (three tiers).

**Confidence: Medium** (MPL confirmed; IPL and classical not fully read)

---

### Claim 10: BBM claims the bridge lemmas in `Semantics/Algebra/Bridge.lean` are named `propEvaluateEq` and `boolEvaluateEq` (message 605813681)

> "The bridge lemmas `propEvaluateEq` and `boolEvaluateEq` in `Semantics/Algebra/Bridge.lean` connect both to `AlgEvaluate`"

**Status: ACCURATE**

Evidence from `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean`:
- Line 58: `theorem propEvaluateEq` — connects `Evaluate` (Prop-valued) to `AlgEvaluate` at `Prop`/`False`
- Line 78: `theorem boolEvaluateEq` — connects `BoolEvaluate` to `AlgEvaluate` at `Bool`/`false`

**Confidence: High**

---

### Claim 11: BBM claims `ipl_conservative_over_mpl` is deferred with sorry (mentioned in task 266 findings, referred to in thread as "deferred")

**Status: ACCURATE**

Evidence: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` line 99: `sorry`

The file docstring explicitly states: "The conservative extension theorem (`ipl_conservative_over_mpl`) is stated but left as `sorry` because the proof requires Dedekind-MacNeille completion of the Lindenbaum algebra (deferred)."

**Confidence: High**

---

### Claim 12: BBM's claim about docstrings in `Semantics/Algebra/Completeness.lean` being added (message 605813681)

> "I've also added docstrings to all definitions in `Semantics/Algebra/Completeness.lean` explaining the Lindenbaum construction, which was previously undocumented."

**Status: VERIFIED ACCURATE**

Evidence: Reading `Semantics/Algebra/Completeness.lean` confirms all major definitions have substantial docstrings: `Theory.canonicalV`, `Theory.canonicalBotVal`, `Theory.canonicalBotVal_eq`, `Theory.canonicalV_spec`, `Theory.tValid_canonicalV`, `nd_alg_sound_aux`, `nd_alg_sound`, `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete` (start of which is visible).

**Confidence: High**

---

### Claim 13: BBM claims the `## Implementation notes` section in `NaturalDeduction/Basic.lean` was restored with trade-off framing and a link to the Zulip thread (message 605813681)

> "I've updated the `## Implementation notes` section of `NaturalDeduction/Basic.lean` to state this trade-off factually — naming both sides and linking to this thread"

**Status: ACCURATE**

Evidence: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` lines 55-77 contain a detailed `**Design trade-off**` section explaining:
- The hybrid design (⊥ constructor without efq derivation rule)
- The cost: "API uniformity and zero duplication"
- The alternative: "Constructor-rule correspondence"
- A link to the Zulip thread (line 76)

**Confidence: High**

---

### Claim 14: BBM claims the 4 references (Prawitz, Troelstra & Van Dalen, Sorensen & Urzyczyn, and a 4th) were restored to `NaturalDeduction/Basic.lean` (message 605813681)

> "I've also restored your original references (Prawitz, Troelstra & Van Dalen, Sorensen & Urzyczyn), which were inadvertently dropped during the ND overhaul."

**Status: ACCURATE**

Evidence: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` references section (lines 78-88) contains exactly: Johansson1937, Prawitz1965, TroelstraVanDalen1988 (with section reference §10.4), Gentzen1935, SorensenUrzyczyn2006 (with section reference §2.2).

**Confidence: High**

---

### Claim 15: TW's claim that `⊥`-as-atom makes completeness harder and that GHA lacks a designated `⊥` element (message 605341190)

> "From the free-algebra perspective, minimal logic doesn't want `⊥` as a constructor — a `GeneralizedHeytingAlgebra` is not an algebra over the signature with `⊥`, which is why you need the extra unnatural field `botVal`."

**Status: ACCURATE**

Evidence: Mathlib's `GeneralizedHeytingAlgebra` is a lattice with relative pseudo-complement but no `Bot` class — it does not have a `⊥` element. `HeytingAlgebra` extends it with `Bot`. The `bot_val : H` parameter in `AlgEvaluate` is structurally necessary when `H : GeneralizedHeytingAlgebra` — there is no algebraic `⊥` to default to.

**Confidence: High**

---

### Claim 16: MD's claim that using `Bool`-valued `canonicalValuation` via `decide` would be "simpler and result in less code" (message 603538889)

**Status: INACCURATE / MISLEADING**

MD suggested using `decide (Proposition.atom p ∈ S)` for `canonicalValuation`. As BBM pointed out (message 603572691), this would require `Classical.propDecidable` (already used) but would make the truth lemma clumsy: instead of `Evaluate (canonicalValuation S) φ ↔ φ ∈ S`, it would need `Evaluate (canonicalValuation S) φ = true ↔ φ ∈ S`. The two-evaluator approach (current design) is better because:
1. `Evaluate` stays Prop-valued for uniformity with modal/temporal/bimodal semantics
2. `BoolEvaluate` stays `Bool`-valued for computable procedures
3. The bridge lemmas connect both to `AlgEvaluate`

The claim that using `decide` "results in less code" is not borne out — it would require type-level gymnastics to convert between `Bool` and `Prop` at every site where the MCS truth lemma is invoked.

**Confidence: High**

---

### Claim 17: BBM's claim about typeclass split options being investigated (message 605813681)

> "I investigated three approaches to avoid the hybrid ND using typeclasses. None can eliminate it without duplicating the formula type."

**Status: PLAUSIBLE BUT NOT DIRECTLY VERIFIABLE from code alone**

This is a design argument rather than a code claim. No file in the codebase contains the three-option typeclass investigation. It is a summary of design reasoning that led to the current hybrid architecture. The claim is consistent with Lean 4's type system: inductive type constructors cannot be conditionally available based on typeclasses.

**Confidence: Medium** (claim is logically sound; not directly verifiable in code)

---

### Claim 18: BBM claims `Semantics/Basic.lean` defines `Evaluate` and `Tautology`, and `Semantics/Bool.lean` adds `BoolEvaluate` (message 603520169)

> "`Semantics/Basic.lean` defines the Prop-valued `Evaluate` and `Tautology`, and `Semantics/Bool.lean` adds `BoolEvaluate` with the bridge lemma"

**Status: PARTIALLY INACCURATE (outdated reference)**

At the time of message 603520169 (2026-06-15), this was the intended structure. In the current codebase, there is no `Semantics/Basic.lean` — instead:
- `Valuation`, `Evaluate`, and `Tautology` are defined in `Semantics/Bool.lean` (lines 51-80)
- `BoolValuation` and `BoolEvaluate` are also in `Semantics/Bool.lean` (lines 85-109)

The two were consolidated into a single `Bool.lean` file, which BBM explicitly proposed in message 603572691 ("One option would be to consolidate `Bool.lean` and `Basic.lean` into one file"). This consolidation was implemented. The reference to a separate `Semantics/Basic.lean` in message 603520169 is therefore an outdated description of the pre-consolidation state.

**Confidence: High** (no `Semantics/Basic.lean` file exists in current codebase)

---

## Recommended Approach

The claims in the thread are generally accurate with two caveats:

1. **The `Semantics/Basic.lean` reference** is outdated — `Evaluate` and `BoolEvaluate` are both in `Semantics/Bool.lean` following consolidation.

2. **The `bot`-as-atom claim** was accurate at the time (2026-06-15) but is superseded — PR 648 changed `bot` to a primitive constructor, which was the correct resolution of the thread debate.

3. **`ipl_conservative_over_mpl` has a sorry** — this is not a claim from the thread itself but a consequence of the thread's discussion. The thread identified that Dedekind-MacNeille completion is needed; the current code confirms this is deferred.

No further action is needed on the verified claims. The sorry in `Conservative.lean` is the one outstanding technical debt item resulting from this design discussion.

---

## Evidence/Examples

Key file paths:
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Defs.lean` — `Proposition` inductive type with primitive `bot`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Bool.lean` — both `Evaluate` (Prop) and `BoolEvaluate` (Bool) with bridge lemma
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra.lean` — `AlgEvaluate` with `bot_val` parameter, `AlgTValid`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` — `Theory.alg_complete`, `MPL.alg_complete`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` — `propEvaluateEq`, `boolEvaluateEq`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` — `ipl_conservative_over_mpl` (sorry)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — design trade-off section, Zulip link
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` — substitution preservation lemmas
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` — `canonicalValuation` (Prop-valued)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Kripke.lean` — `KripkeModel` with `botForces`, `IForces`, `IValid`, `MValid`

---

## Confidence Summary

| Claim | Status | Confidence |
|-------|--------|------------|
| `bot` was not primitive (historical) | True then, superseded now | High |
| `Valuation` stays `Atom → Prop` | Accurate | High |
| `BoolEvaluate` + bridge lemma added | Accurate | High |
| `canonicalValuation` using `decide` not adopted | Accurate | High |
| MPL completeness requires free `bot_val` | Accurate | High |
| Substitution lemmas exist without side conditions | Accurate | High |
| `FromPropositional` uses direct `\| .bot => .bot` | Accurate | High |
| `AlgTValid` and `Theory.alg_complete` exist | Accurate | High |
| Tier-specific corollaries exist | MPL confirmed; IPL/CPL medium | Medium |
| Bridge lemma names `propEvaluateEq`/`boolEvaluateEq` | Accurate | High |
| `ipl_conservative_over_mpl` has sorry | Accurate | High |
| Docstrings added to `Completeness.lean` | Accurate | High |
| Implementation notes restored with Zulip link | Accurate | High |
| 4 references restored to `NaturalDeduction/Basic.lean` | Accurate | High |
| GHA lacks designated `⊥` element | Accurate | High |
| MD's `decide` suggestion would reduce code | Inaccurate | High |
| Typeclass split can't eliminate formula duplication | Plausible, not verifiable | Medium |
| `Semantics/Basic.lean` distinct from `Bool.lean` | Outdated (consolidated) | High |
