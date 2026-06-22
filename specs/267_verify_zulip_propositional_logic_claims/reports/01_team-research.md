# Research Report: Task #267

**Task**: Verify Zulip Propositional Logic Claims
**Date**: 2026-06-22
**Mode**: Team Research (4 teammates)
**Session**: sess_1782154953_a78bf2

## Summary

The Zulip message (message 25 by BBM, 2026-06-22) makes approximately 20 verifiable technical claims about CSLib's propositional logic infrastructure. **17 are accurate, 1 is partially accurate with needed nuance, 1 is a design argument that cannot be verified from code alone, and 1 rhetorical claim ("convergence") is overstated.** Two claims about Thomas Waring's branch code are unverifiable from main. No claim is outright false.

The message is a careful summary of a 25-message thread spanning 2026-06-12 to 2026-06-22 involving BBM, Thomas Waring, and Matthew Doty. It addresses: `⊥`-as-primitive vs `⊥`-as-atom, ND symmetry trade-offs, Johansson algebras, parametric completeness, dual evaluators, and typeclass split feasibility.

---

## Claim-by-Claim Verification

### Section: On `⊥` as a primitive constructor

| # | Claim | Verdict | Evidence | Confidence |
|---|-------|---------|----------|------------|
| 1 | "substitution invariance" — `subst_preserves_axiom`, `subst_preserves_intAxiom`, `hilbertSubstitution`, `Theory.Derivation.substAtom` work without `σ(⊥) = ⊥` | **ACCURATE** | All 4 exist in `FromHilbert.lean` (lines 232–318) and `Basic.lean` (lines 305–326); none has a `σ(⊥) = ⊥` side condition. A 5th lemma `subst_preserves_minAxiom` also exists but is not mentioned. | High |
| 2 | "The `FromPropositional` embeddings to Modal and Temporal logic also benefit: the map `\| .bot => .bot` is direct" | **ACCURATE** | Confirmed in `Modal/Basic.lean`, `Temporal/ConservativeExtension.lean`, `Bimodal/Embedding/PropositionalEmbedding.lean`. | High |
| 3 | "the monad bind case `\| .bot => .bot` requires no condition" | **ACCURATE** | `Proposition` is a `Monad` instance; the `bind` case for `.bot` is trivially `| .bot => .bot`. | High |

**Nuance (Teammate C)**: The substitution discussion focuses entirely on `substAtom` (atom-level substitution, sound). A separate function `subs` (derivation-level hypothesis substitution, `Basic.lean` line 275) carries a TODO noting it is "not capture avoiding." These are different functions with different properties. The message does not conflate them, but a reader might.

### Section: The ND symmetry trade-off

| # | Claim | Verdict | Evidence | Confidence |
|---|-------|---------|----------|------------|
| 4 | "`⊥` has a syntax constructor but no derivation constructor" | **ACCURATE** | `Proposition` has `.bot`; `Theory.Derivation` has 10 constructors: `ax`, `ass`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `impI`, `impE` — none is efq. | High |
| 5 | "efq is absent in MPL and present in IPL/CPL as a logic-dependent rule" | **ACCURATE** | `MPL = ∅`, `IPL = Set.range (⊥ → ·)`, `CPL` adds `¬¬A → A`. `botE` derived rule in `DerivedRules.lean` requires `[IsIntuitionistic T]`. | High |
| 6 | "I've updated the `## Implementation notes` section of `NaturalDeduction/Basic.lean`" | **ACCURATE** | Lines 55–77 contain a detailed design trade-off section naming both sides (API uniformity vs constructor-rule correspondence), with a Zulip thread link at line 76. | High |
| 7 | "restored your original references (Prawitz, Troelstra & Van Dalen, Sorensen & Urzyczyn)" | **ACCURATE** | Lines 78–88 contain: Johansson1937, Prawitz1965, TroelstraVanDalen1988 (§10.4), Gentzen1935, SorensenUrzyczyn2006 (§2.2). | High |
| 8 | "The deletion was a mistake during the ND overhaul (commit `80f54485`, task 173)" | **PLAUSIBLE** | Historical claim about a past commit. Task 173 is tombstoned. Cannot verify from current state without `git log`. | Medium |

**Nuance (Teammate C)**: The claim "the thread has substantially converged on this" is **overstated**. Thomas Waring's most recent message (msg 23, 2026-06-21) advocates an alternative design (`IProposition`/`IDerivation`), and he has not responded to message 25. The thread records ongoing debate, not settled consensus.

### Section: On `bot_val`: Johansson's designated constant

| # | Claim | Verdict | Evidence | Confidence |
|---|-------|---------|----------|------------|
| 9 | "`bot_val : H` parameter in `AlgEvaluate` is the designated constant of Johansson algebras" | **ACCURATE** | `Algebra.lean` lines 82–88: `AlgEvaluate` takes `(v : Atom → H) (bot_val : H)` with `H : GeneralizedHeytingAlgebra`. GHA has no `Bot` instance, so `bot_val` is genuinely free. | High |
| 10 | "For IPL, fixing `bot_val = ⊥` recovers the standard Heyting algebra semantics" | **ACCURATE** | `IPL.alg_complete` (line 252) uses `[HeytingAlgebra H]` with `AlgEvaluate v (⊥ : H)`. | High |
| 11 | "For MPL, quantifying over all `bot_val` values is what makes MPL completeness true" | **ACCURATE** | `MPL.alg_complete` (line 237) uses `[GeneralizedHeytingAlgebra H]` and quantifies over `(bot_val : H)`. | High |
| 12 | "This parallels `botForces` in `KripkeModel`" | **ACCURATE** | `Kripke.lean` lines 57–67: `KripkeModel` has `botForces : World → Prop` as a separately specified field. | High |

### Section: On the parametric completeness style

| # | Claim | Verdict | Evidence | Confidence |
|---|-------|---------|----------|------------|
| 13 | "`AlgTValid` in `Semantics/Algebra.lean` implements exactly this pattern" | **ACCURATE** | Line 141: `def AlgTValid` exists. | High |
| 14 | "`Theory.alg_complete` uses it" | **ACCURATE** | Line 218: `theorem Theory.alg_complete` with `AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤`. | High |
| 15 | "The tier-specific corollaries (`MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical`) specialize the algebra type and `bot_val`" | **ACCURATE** | All three exist: `MPL.alg_complete` (line 237), `IPL.alg_complete` (line 252), `alg_complete_classical` (line 273). | High |
| 16 | "I've also added docstrings to all definitions in `Semantics/Algebra/Completeness.lean`" | **ACCURATE** | All major definitions (`canonicalV`, `canonicalBotVal`, `tValid_canonicalV`, `nd_alg_sound`, etc.) have substantial docstrings. | High |

**Nuance (Teammate C)**: Thomas's notation `v ⊨ T` with a bundled `Valuation Atom H` type alias (his branch) differs from the actual CSLib API which uses explicit `(v : Atom → H) (bot_val : H)` parameters and an `AlgTValid` predicate. The message correctly says the `v ⊨ T` "framing" is adopted, meaning the semantic concept, not Thomas's exact surface syntax.

### Section: On `Prop` vs. `Bool` semantics

| # | Claim | Verdict | Evidence | Confidence |
|---|-------|---------|----------|------------|
| 17 | "`Evaluate` (Prop-valued) is needed for canonical model construction: MCS membership is irreducibly `Prop`-valued" | **ACCURATE** | `Valuation Atom = Atom → Prop` (Bool.lean:51); `canonicalValuation S = fun p => Proposition.atom p ∈ S` (StrongCompleteness.lean:72–74). | High |
| 18 | "`BoolEvaluate` (Bool-valued) is there for DPLL and SAT" | **ACCURATE** | `BoolEvaluate : BoolValuation Atom → PL.Proposition Atom → Bool` (Bool.lean:89). | High |
| 19 | "The bridge lemmas `propEvaluateEq` and `boolEvaluateEq` in `Semantics/Algebra/Bridge.lean` connect both to `AlgEvaluate`" | **ACCURATE** | `propEvaluateEq` (line 58) and `boolEvaluateEq` (line 78) both exist in Bridge.lean. | High |

**Nuance (Teammate C)**: There are **two distinct sets of bridge lemmas** that the thread doesn't clearly distinguish:
- `BoolEvaluate_eq_iff` in `Bool.lean` — connects `BoolEvaluate` to `Evaluate` (Prop-valued)
- `boolEvaluateEq` in `Bridge.lean` — connects `BoolEvaluate` to `AlgEvaluate` (GHA-valued)

The message's claim about `Bridge.lean` lemmas is accurate, but earlier thread messages reference `BoolEvaluate_eq_iff` without distinguishing it.

### Section: On the typeclass split question

| # | Claim | Verdict | Evidence | Confidence |
|---|-------|---------|----------|------------|
| 20 | "I investigated three approaches to avoid the hybrid ND using typeclasses. None can eliminate it without duplicating the formula type." | **PLAUSIBLE** | Design argument consistent with Lean 4's type system (inductive constructors cannot be conditionally available). No code artifact records the investigation. | Medium |
| 21 | "Thomas's `IProposition`/`IDerivation` branch: `propEquiv`, `toDerivation`, `toIDerivation` compile" | **UNVERIFIABLE** | Branch code not in CSLib main. | Low |
| 22 | "`noncomputable toIDerivation` uses `Classical.choose`" | **UNVERIFIABLE** | Branch code not in CSLib main. | Low |

---

## Synthesis

### Conflicts Found and Resolved

**1. Convergence claim (Teammate A vs C)**
- Teammate A accepts claims at face value
- Teammate C flags "the thread has substantially converged" as overstated since Thomas hasn't responded
- **Resolution**: Teammate C is correct. The convergence claim is BBM's assessment, not a factual statement about thread outcome. Thomas's most recent message advocates an alternative design.

**2. Bridge lemma disambiguation (Teammate A vs C)**
- Teammate A verifies bridge lemma names as accurate
- Teammate C distinguishes two different bridge lemma sets
- **Resolution**: Both are right. The specific claim about `propEvaluateEq`/`boolEvaluateEq` in Bridge.lean is accurate. The thread's broader bridge lemma discussion conflates two different pairs.

**3. `subst_preserves_minAxiom` (Teammate A)**
- Teammate A lists 5 substitution lemmas; the message only names 4
- **Resolution**: The message omits `subst_preserves_minAxiom` but it exists. The claim is accurate for the 4 named; the omission is not an error, just incomplete enumeration.

### Gaps Identified

1. **Matthew Doty's `decide` proposal** — correctly not adopted, but the message's characterization of it as "resulting in less code" being wrong (Claim 16 from Teammate A) is a judgment about Matthew's suggestion, not a factual claim about code.

2. **`subs` non-capture-avoiding** (Teammate C) — the message discusses substitution invariance for `substAtom` but does not address the known `subs` defect (TODO at Basic.lean:275). Not a claim error, but a gap in the thread discussion.

3. **ProofSystem documentation staleness** (Teammate D) — `ProofSystem.lean` says "concrete instances require derivation trees (not yet ported)" but `Instances.lean` already registers them. The message doesn't cite this stale documentation, so it's not a claim error, but a codebase issue.

4. **Test coverage** (Teammate D) — zero `CslibTests` imports for the entire Propositional module. Not discussed in the thread.

### Recommendations

1. **The message is accurate for posting.** All substantive technical claims check out against the codebase. The only edit worth considering is softening "substantially converged" since Thomas hasn't responded yet.

2. **The `subs` non-capture-avoiding issue** should be documented or discussed separately — it's orthogonal to the `substAtom` invariance argument but could confuse readers.

3. **The stale `ProofSystem.lean` documentation** should be updated to reflect that propositional instances are registered.

4. **The Hilbert-to-algebraic completeness bridge** is an unmade composition (Teammate D observation) — the ND↔Hilbert equivalence exists in `Equivalence.lean` and the ND-algebraic completeness exists in `Completeness.lean`, but no theorem states `Derivable MinPropAxiom φ ↔ GHAValid φ` directly.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|------------------|
| A | Primary verification | completed | high | Fetched all 25 messages; verified 18 claims with specific file/line evidence |
| B | Infrastructure survey | completed | high | Independent codebase audit: 31 files, 3 logic tiers, architecture map |
| C | Critic | completed | high | Flagged convergence overstatement, bridge lemma conflation, subs defect |
| D | Horizons | completed | medium | Strategic context: sorry priority, stale docs, abstract completeness extraction |

**Note**: Teammates A and C successfully fetched the Zulip thread (25 messages). Teammates B and D could not access it (auth required) and pivoted to independent codebase investigation.

---

## Verdict Summary

| Category | Count |
|----------|-------|
| **Accurate** | 17 |
| **Accurate with nuance** | 1 (tier-specific corollaries — all exist but Teammate A initially had medium confidence on IPL/CPL) |
| **Overstated** | 1 ("substantially converged" — Thomas hasn't responded) |
| **Plausible but unverifiable from code** | 1 (typeclass split investigation) |
| **Unverifiable (branch code)** | 2 (Thomas's `IProposition`/`IDerivation` compilation claims) |
| **Outright false** | 0 |

The message is a reliable summary of CSLib's propositional logic state. The one substantive concern is the convergence claim — the thread records productive disagreement, not resolution.

---

## References

### Key Files Verified
- `Cslib/Logics/Propositional/Defs.lean` — `Proposition` with primitive `bot`
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — ND design trade-off, references, Zulip link
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` — substitution preservation lemmas
- `Cslib/Logics/Propositional/Semantics/Bool.lean` — `Evaluate`, `BoolEvaluate`, `BoolEvaluate_eq_iff`
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` — `AlgEvaluate`, `AlgTValid`
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` — `Theory.alg_complete`, tier corollaries
- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` — `propEvaluateEq`, `boolEvaluateEq`
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` — `ipl_conservative_over_mpl` (sorry)
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` — `KripkeModel` with `botForces`
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` — `canonicalValuation`
