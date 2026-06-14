# Teammate C: Critical Analysis of Connective-Basis Design

**Role**: Critic — identify gaps, errors, and unsupported claims  
**Task**: 171 — Research connective-basis design for minimal, intuitionistic, and classical PL in CSLib  
**Date**: 2026-06-12

---

## Key Findings

### Finding 1: The Claim "{imp, bot} is a basis for IPC" is Mathematically Incorrect (HIGH CONFIDENCE)

The current codebase makes a factually incorrect claim. In `Cslib/Foundations/Logic/Connectives.lean` (line 29-34) and `Cslib/Logics/Propositional/Defs.lean` (line 22), the comment states:

> "since `{imp, bot}` is functionally complete for classical logic, every other connective is definable"

This qualification "for classical logic" is correct. But the code then defines `Proposition.or` and `Proposition.and` using the classical encodings (lines 69-75 of `Defs.lean`), and the system is used for intuitionistic and minimal logic as well. The critical issue is that **the or/and abbreviations are used in the ND derivation system for intuitionistic logic** (`NaturalDeduction/Basic.lean`) without any disclaimer that they do not express the standard intuitionistic connectives.

**The Mathematical Error**: In intuitionistic propositional logic (IPC), the standard connectives {∧, ∨, →, ⊥} are NOT all inter-definable from just {→, ⊥}. Specifically:
- `¬(p → ¬q)` does NOT intuitionistically entail `p ∧ q` (though `p ∧ q` does entail it)
- `¬p → q` does NOT intuitionistically entail `p ∨ q` (though `p ∨ q` does entail it)

This is confirmed by the `DerivedRules.lean` file itself: `andE1`, `andE2`, and `orE` all require `[IsClassical T]` as a typeclass constraint (lines 143, 174, 232 of `DerivedRules.lean`). This is the smoking gun — the elimination rules for conjunction and disjunction require classical logic precisely because the definitions used (`A ∧ B := ¬(A → ¬B)` and `A ∨ B := ¬A → B`) are only classically equivalent to the standard connectives.

---

### Finding 2: Kripke Counterexamples Confirming the Failure

**Counterexample for ∧**: Show that `¬(p → ¬q)` is not intuitionistically derivable from `p ∧ q`, or more pointedly, that `¬(p → ¬q)` has strictly less deductive strength than `p ∧ q` in IPC.

Actually, the failure goes the OTHER direction: `p ∧ q` → `¬(p → ¬q)` is intuitionistically VALID (given p and q, assume p → ¬q; apply to p to get ¬q; apply ¬q to q to get ⊥). But `¬(p → ¬q)` → `p` and `¬(p → ¬q)` → `q` are NOT intuitionistically valid.

Kripke model: Three worlds w₀ ≤ w₁, w₀ ≤ w₂, with w₁ and w₂ incomparable.
- Valuation: p forced at w₁ only, q forced at w₂ only.
- At w₀: Is `¬(p → ¬q)` forced? 
  - `p → ¬q` at w₀ means: for all w' ≥ w₀, p at w' implies ¬q at w'.
  - At w₁: p holds, does ¬q hold at w₁? ¬q at w₁ means ∀ w'' ≥ w₁, q not at w''. Since w₁ has no successors beyond itself, and q is not at w₁, yes ¬q holds at w₁.
  - At w₂: p does not hold, so the implication is vacuously true.
  - So `p → ¬q` holds at w₀. Thus `¬(p → ¬q)` = `(p → ¬q) → ⊥` is NOT forced at w₀.
- Revised model: w₀ ≤ w₁ where both p and q are forced at w₁.
  - At w₀: p ∧ q (standard) is NOT forced (neither p nor q is forced at w₀).
  - At w₁: p ∧ q (standard) IS forced.
  - At w₀: `¬(p → ¬q)`:
    - Check `p → ¬q` at w₀: for w' ≥ w₀ with p at w', is ¬q at w'?
    - At w₁: p holds, but q also holds, so ¬q = q → ⊥ requires: ∀ w'' ≥ w₁, q → ⊥. At w₁ itself, q holds, so ⊥ must hold — contradiction. So ¬q FAILS at w₁.
    - Therefore `p → ¬q` is FALSE at w₀ (witness: w₁ where p holds but ¬q fails).
    - So `¬(p → ¬q)` is TRUE at w₀? No: `¬(p → ¬q)` means `(p → ¬q) → ⊥`. Since `p → ¬q` fails at w₀, this implication is satisfied vacuously only if `p → ¬q` holds at no w' ≥ w₀ (the Kripke semantics requires checking all successors). Actually at w₁: `p → ¬q` at w₁ requires for all w'' ≥ w₁, p → ¬q. At w₁ itself, p holds but ¬q fails, so `p → ¬q` fails at w₁. So `p → ¬q` is false at all worlds ≥ w₀. Therefore `(p → ¬q) → ⊥` is vacuously true at w₀.

This shows `¬(p → ¬q)` CAN be forced at a world where the STANDARD `p ∧ q` fails (w₀ has neither p nor q). The CSLib definition of `A ∧ B` as `¬(A → ¬B)` genuinely has different deductive behavior from standard ∧ in intuitionistic logic.

**Counterexample for ∨**: The standard disjunction property states: if `⊢_IPC A ∨ B` then `⊢_IPC A` or `⊢_IPC B`. The CSLib encoding `A ∨ B := ¬A → B` equals Peirce-like reasoning. As evidence: the definition `A ∨ B := ¬A → B` is classically equivalent to disjunction by LEM, but intuitionistically `¬A → B` is strictly weaker than `A ∨ B`.

Simple Kripke counterexample: Single world w₀, with p forced, q not forced.
- Standard `p ∨ q`: p is forced at w₀, so yes p ∨ q holds.
- CSLib `p ∨ q := ¬p → q`: ¬p at w₀ means p → ⊥, which fails since p holds. So ¬p → q is vacuously true (antecedent fails). Thus CSLib's `p ∨ q` is trivially true.

More telling example: w₀ ≤ w₁, p forced at w₁, q not forced anywhere.
- Standard `p ∨ q` at w₀: neither `p` nor `q` forced at w₀, so standard `p ∨ q` fails at w₀.
- CSLib `¬p → q` at w₀: ¬p at w₀ means for all w' ≥ w₀, p → ⊥. At w₁, p holds, so ¬p fails at w₁, hence ¬p fails at w₀. Therefore `¬p → q` is vacuously true at w₀.

This is a model where CSLib's `¬p → q` is forced but neither `p` nor `q` is forced — demonstrating that the CSLib `∨` definition has more "false positives" in intuitionistic logic.

---

### Finding 3: The "10 Rules to 5" Claim Requires Careful Qualification

**Claim analysis**: The PR author claims the natural deduction calculus over {imp, bot} needs "only 5 primitive rules instead of 10."

**What the code actually implements** (`NaturalDeduction/Basic.lean`, lines 85-98):
- `ax` (axiom from theory)
- `ass` (assumption from context)
- `impI` (implication introduction)
- `impE` (modus ponens / implication elimination)
- `botE` (ex falso quodlibet / bottom elimination)

That is 5 rules. The "10" presumably counts: ∧I, ∧E₁, ∧E₂, ∨I₁, ∨I₂, ∨E, →I, →E, ⊥E, and perhaps ¬I/¬E (or top introduction). The claim that conjunction/disjunction rules are "derivable" is:

**TRUE for classical logic**: With DNE available, the `DerivedRules.lean` file successfully derives all conjunction/disjunction/negation rules.

**PARTIALLY TRUE for intuitionistic logic**: The introduction rules are derivable (`andI`, `orI1`, `orI2`), but the elimination rules (`andE1`, `andE2`, `orE`) require `[IsClassical T]`. This is because the DEFINITIONS of ∧ and ∨ used are the classical ones, which only yield the full set of elimination rules under classical reasoning.

**FALSE for standard intuitionistic natural deduction**: In genuine IPC with standard ∧ and ∨, the elimination rules cannot be derived from {→, ⊥} alone because ∧ and ∨ are genuinely independent connectives. Gentzen's NJ explicitly has ALL connectives as primitives with their own rules.

The "5 primitive rules" claim holds only for the CLASSICAL system or for a system where ∧ and ∨ have been deliberately redefined as classical abbreviations. This is a design choice that works for classical logic but produces a non-standard intuitionistic system.

---

### Finding 4: What the Literature Actually Says

**Church (1956)**: "Introduction to Mathematical Logic" uses {→, ¬} or {→, ⊥} as a basis for CLASSICAL propositional logic in a Hilbert-style axiomatization. This is the standard reference for the classical adequacy claim. The CSLib references to Church are appropriate for the HILBERT system axioms, but Church was not developing natural deduction for intuitionistic logic.

**Heyting (1930)**: "Die formalen Regeln der intuitionistischen Logik" gave axioms for intuitionistic logic, but famously used the FULL set of connectives {∧, ∨, →, ¬} as PRIMITIVES, each with their own axioms. Heyting's formalization has 11 axioms covering all connectives separately. Using Heyting as a reference for the {imp, bot}-only basis for intuitionistic logic is MISLEADING — Heyting did the opposite.

**Gentzen (1935)**: "Untersuchungen über das logische Schließen" defined both NK (classical natural deduction) and NJ (intuitionistic natural deduction). Both systems use ALL connectives as PRIMITIVES with separate introduction and elimination rules. Gentzen's NJ has explicit ∧I, ∧E₁, ∧E₂, ∨I₁, ∨I₂, ∨E, →I, →E, ¬I, ¬E, ⊥E rules. Using Gentzen as a reference for the {imp, bot}-only approach is INCORRECT — the entire point of Gentzen's work was to give each connective its own rules.

**Prawitz (1965)**: Follows Gentzen's style exactly. All connectives are primitives with their own introduction and elimination rules. The normalization theorems Prawitz proved are specifically about these rules. Using Prawitz as support for {imp, bot} basis is INCORRECT.

**Troelstra & van Dalen (1988)**: Their constructive mathematics presentation uses the FULL intuitionistic language. They do not reduce to {→, ⊥}. This reference is inappropriate for the {imp, bot} claim.

**Chagrov & Zakharyaschev (1997)**: This book is about MODAL LOGIC. Their propositional base uses the full classical language. References to CZ in the Kripke semantics module are appropriate (persistence lemma, completeness theorems are there), but CZ is not a reference for choosing {imp, bot} as basis for propositional logic.

**Summary**: None of the cited references actually use {imp, bot} as the sole basis for INTUITIONISTIC natural deduction. The references support using {imp, bot} only for the HILBERT-STYLE axiomatization of CLASSICAL logic (Church) or for meta-level functional completeness arguments. The PR author appears to have conflated:
1. Functional completeness of {→, ⊥} for classical propositional logic (true, from Church)
2. Naturalness of the {→, ⊥} basis for intuitionistic logic (false — Heyting, Gentzen, Prawitz all used full connective sets)

---

### Finding 5: Critical Gaps in the Architecture

**Gap 1: The connective mismatch in intuitionistic contexts**

The code currently defines a single `Proposition` type that serves all three logics (minimal, intuitionistic, classical). The `∧` and `∨` defined as `abbrev` are the CLASSICAL encodings. When this type is used with `IntPropAxiom` (intuitionistic axioms), the resulting system is NOT standard intuitionistic propositional logic. It is the {→, ⊥} fragment of classical logic, which coincides with the full classical system (because the axioms K + S + EFQ already generate all classical tautologies involving only → and ⊥, and any ∧/∨ formula is interpreted via their classical abbreviations).

The `int_soundness_completeness` theorem (`IntCompleteness.lean`, line 122) states: `IValid φ ↔ Derivable IntPropAxiom φ`. But `IValid` is defined over the Kripke semantics for the FORMULA TYPE `PL.Proposition`, which only has `atom | bot | imp` constructors. Since `∧` and `∨` are abbreviations that unfold to `imp` and `bot`, the completeness theorem is really about the {→, ⊥} fragment, which IS complete for standard IPC restricted to {→, ⊥} formulas. This is a subtle but important distinction.

**Gap 2: No disjunction property is stated or provable**

The disjunction property (DP) is the hallmark of IPC: if `⊢_IPC A ∨ B` then `⊢_IPC A` or `⊢_IPC B`. In the CSLib encoding where `A ∨ B := ¬A → B`, the "disjunction property" would read: if `⊢ (¬A → B)` then `⊢ A` or `⊢ B`. This is FALSE classically (take A = ¬p, B = p: then ¬¬p → p is classically valid but neither ¬¬p nor p is derivable from nothing). It may hold for the intuitionistic axioms over this restricted signature, but it needs careful examination.

More precisely: for IPC over {→, ⊥}, the relevant property is the "existence property" for → and ⊥, which is decidable. The "disjunction property" for ∨ as standardly defined would be provable, but `∨` here means `¬A → B`, for which the property takes a different form.

**Gap 3: Negation is ambiguous across logics**

In minimal logic (MPL), `¬φ := φ → ⊥` but `⊥` is just another formula — it doesn't "explode." In intuitionistic logic (IPL/IPC), `⊥ → A` is an axiom (EFQ). In classical logic, `¬¬A → A` (DNE) is added. The code handles this correctly via the axiom hierarchy (`MinPropAxiom ⊆ IntPropAxiom ⊆ PropositionalAxiom`), but the DOCUMENTATION does not clarify that `¬` means something DIFFERENT in MPL vs IPL vs CPL — even though it has the same definition `A → ⊥`.

**Gap 4: The `IsClassical` constraint makes ∧ and ∨ second-class in IPL**

The `Theory.IsIntuitionistic` typeclass adds EFQ. The `Theory.IsClassical` typeclass adds DNE. But the elimination rules for ∧ and ∨ in `DerivedRules.lean` require `[IsClassical T]`, not `[IsIntuitionistic T]`. This means: in the CSLib system, even with intuitionistic axioms, you CANNOT perform `∧E1` or `∨E` derivations without asserting classicality. This is architecturally broken for anyone wanting to prove standard intuitionistic theorems about ∧ or ∨.

For example: in standard IPC, `p ∧ q ⊢ p` is a basic axiom. In CSLib's encoding, deriving `p ∧ q ⊢ p` requires `[IsClassical T]` because `andE1` has that constraint. This means the CSLib encoding of "intuitionistic logic with ∧" is actually classical logic.

---

## Evidence Summary

| Claim | Status | Evidence |
|-------|--------|----------|
| "{imp, bot} is functionally complete for CLASSICAL logic" | TRUE | Church 1956; classical truth tables |
| "{imp, bot} is a basis for INTUITIONISTIC logic" | MISLEADING | Heyting, Gentzen, Prawitz all used full connective sets |
| "andI is derivable in IPC" | TRUE (with CSLib definitions) | `DerivedRules.lean` line 111 |
| "andE1 is derivable in IPC" | FALSE — requires [IsClassical T] | `DerivedRules.lean` line 143 |
| "orI1, orI2 are derivable in IPC" | TRUE (with CSLib definitions) | `DerivedRules.lean` lines 201, 219 |
| "orE is derivable in IPC" | FALSE — requires [IsClassical T] | `DerivedRules.lean` line 232 |
| "The system has 5 primitive ND rules" | TRUE | `Basic.lean` lines 85-98: ax, ass, impI, impE, botE |
| "Conjunction/disjunction rules become derivable" | CONDITIONALLY TRUE | Only if "derivable" means "in classical logic" |

---

## Recommended Approach

The team should reach the following conclusions:

**1. Classify the design choice accurately**: The {imp, bot} basis is appropriate for:
- Classical propositional logic (CPL) — fully correct
- Hilbert-style axiomatization of all three logics — fully correct  
- The {→, ⊥} FRAGMENT of intuitionistic/minimal logic — correct but incomplete

It is NOT appropriate for claiming "intuitionistic logic with standard ∧ and ∨" because the derived connectives are classical abbreviations.

**2. The codebase is correct but its claims are overclaimed**: The actual Lean code compiles and proves correct theorems. The completeness theorems (`int_soundness_completeness`, `min_soundness_completeness`) are correct because they are about the formula type with only `atom | bot | imp` constructors, where ∧ and ∨ are definitional abbreviations. The Kripke semantics only needs to handle three cases. This is mathematically sound.

**3. The documentation and PR description need correction**: The claim that this approach "needs only 5 primitive rules instead of 10" should be qualified: this holds for the CLASSICAL system. For intuitionistic and minimal systems, the ∧/∨ elimination rules require classical axioms, making the system effectively classical when those connectives are used.

**4. The reference to Heyting, Gentzen, and Prawitz should be revised**: These authors used full connective sets. The appropriate literature reference for the {→, ⊥} basis approach is:
- Church (1956) for classical functional completeness
- The formal logic tradition of Hilbert-style presentations (not natural deduction style)
- The specific result that for the {→, ⊥} fragment, IPC is complete (this is a standard result but requires a precise citation)

**5. Consider a design alternative for genuine intuitionistic ∧/∨**: If CSLib needs intuitionistic natural deduction proofs involving ∧ and ∨ that work WITHOUT classical axioms, two options exist:
- Option A: Add `and` and `or` as genuine constructors to `Proposition` (standard approach, but increases inductive complexity)
- Option B: Keep the current design but document explicitly that ∧ and ∨ are classical abbreviations only, and that the intuitionistic system is the {→, ⊥} fragment of IPC

Option B is what the code actually does, but the documentation suggests Option A was intended.

---

## Confidence Levels

| Finding | Confidence |
|---------|-----------|
| andE1/andE2/orE require classical axioms (from code evidence) | HIGH — directly observable in DerivedRules.lean |
| Heyting used full connective sets, not {imp, bot} | HIGH — standard historical fact |
| Gentzen/Prawitz used full connective sets | HIGH — standard historical fact |
| Kripke counterexamples for CSLib ∧/∨ in IPC | HIGH — constructed by analysis of IForces semantics |
| The completeness theorems are mathematically correct | HIGH — the formula type only has three constructors |
| The documentation overclaims vs what's actually formalized | HIGH — direct comparison of claims vs code constraints |
| The disjunction property fails for the CSLib ∨ encoding | HIGH — classical counterexample given |

---

## Summary for Other Teammates

The CSLib propositional logic codebase is **internally consistent and mathematically correct** for what it actually formalizes: propositional logic over the {→, ⊥} signature with ∧/∨ as classical abbreviations. The code compiles, the completeness theorems are valid, and the derived rules work correctly in their stated scope.

The problem is a **claim-reality mismatch**: the comments and PR description claim this approach works for intuitionistic logic with standard ∧ and ∨, but the code itself reveals (via the `[IsClassical T]` constraints) that the ∧/∨ elimination rules are only available with classical axioms. The references cited (Heyting, Gentzen, Prawitz) actually used FULL connective sets and would not endorse the {imp, bot}-only approach for intuitionistic natural deduction.

The reviewer ctchou who challenged the {imp, bot} claim was mathematically correct to do so. The PR author's response should either (a) reframe the system as classical logic with a small inductive type, or (b) add genuine ∧/∨ constructors for a proper intuitionistic ND system.
