# Teammate A Findings: Literature Verification and Connective-Basis Truth

**Task**: Research connective-basis design for minimal, intuitionistic, and classical propositional
logic in CSLib (PR #635 context).

**Focus**: Determine the truth of specific claims and counter-claims about {imp, bot} as a
primitive basis.

---

## Key Findings

### Finding 1: Claim 1 is TRUE for classical logic, but the PR description is MISLEADING

**Claim**: "{imp, bot} is functionally complete for classical propositional logic."

**Verdict**: TRUE for classical (two-valued) propositional logic.

{→, ⊥} is a minimal functionally complete set of classical connectives. In classical logic, the
following definitions hold truth-functionally:

- ¬A := A → ⊥
- A ∨ B := ¬A → B (equivalently: (A → ⊥) → B)
- A ∧ B := ¬(A → ¬B) := (A → (B → ⊥)) → ⊥
- ⊤ := ⊥ → ⊥

Wikipedia (Functional Completeness) confirms: "{→, ⊥}" is listed among the minimal functionally
complete sets of logical connectives. The equivalences A ∧ B ≡ (A → (B → ⊥)) → ⊥ and
A ∨ B ≡ (A → ⊥) → B are classically valid.

**Why it is misleading**: The PR description does not acknowledge that this functional completeness
is a *classical* result only. The formula A ∨ B := ¬A → B holds classically (because it is
equivalent to excluded middle via classical double-negation), but this definitional equality fails
intuitionistically. See Finding 2.

---

### Finding 2: Counter-claim 1 is CORRECT — {imp, bot} is NOT adequate for intuitionistic logic

**Counter-claim**: "Can all logical connectives be reducible to implication and falsum in
INTUITIONISTIC propositional logic? I don't think so."

**Verdict**: The counter-claim is mathematically correct.

The connectives of intuitionistic propositional logic are NOT interdefinable. Multiple authoritative
sources confirm this:

1. **Stanford Encyclopedia of Philosophy (Intuitionistic Logic)** explicitly states:
   "the intuitionistic connectives ∧, ∨, →, ¬ are logically independent over IPC" and
   "none of the basic connectives can be dispensed with." The standard presentation uses
   "→, ∧, ∨, ⊥ as the basic connectives, treating ¬A as an abbreviation for (A → ⊥)."
   (SEP entry on Intuitionistic Logic, consulted June 2026)

2. **PlanetMath (Intuitionistic Logic)** states: "Although in classical logic the set of
   propositional functions can be reduced to one of the pairs (¬,∨), (¬,∧), (¬,→), the four
   intuitionistic connectives are not inter-definable."

3. **HandWiki (Intuitionistic Logic)**: "none of the basic connectives can be dispensed with"
   in intuitionistic logic, and "most of the classical identities between connectives and
   quantifiers are only theorems of intuitionistic logic in one direction."

**Why disjunction fails**: In intuitionistic logic, A ∨ B carries a constructive meaning: a proof
of A ∨ B must be either a proof of A or a proof of B (BHK interpretation). The classical
definition A ∨ B := ¬A → B fails intuitionistically because ¬A → B does NOT imply we have a
proof of A or a proof of B — it only says that if A is false then B holds, which classically
collapses to A ∨ B but intuitionistically does not.

The disjunction property (if ⊢ A ∨ B then ⊢ A or ⊢ B) is a key metalogical property of
intuitionistic logic that would be destroyed if A ∨ B were definitionally equal to ¬A → B,
because ¬A → B does not satisfy this property.

**Why conjunction also fails**: A ∧ B := (A → (B → ⊥)) → ⊥ holds classically but not
intuitionistically. From A ∧ B (classically rewritten) we can extract A by double-negation
elimination (DNE). But DNE is not available intuitionistically. Indeed, as confirmed by the
CSLib code itself (DerivedRules.lean, lines 129-193), andE1 and andE2 require [IsClassical T]
precisely because this extraction requires DNE.

**Concrete evidence from the CSLib implementation**: DerivedRules.lean shows:
- `andI` (conjunction introduction): no classical constraint required — works in minimal logic
- `andE1`, `andE2` (conjunction elimination): `[IsClassical T]` REQUIRED
- `orI1`, `orI2` (disjunction introduction): no classical constraint required
- `orE` (disjunction elimination): `[IsClassical T]` REQUIRED

This is direct proof that the Lukasiewicz encoding of ∧ and ∨ via {imp, bot} is only classically
adequate. The current CSLib code is therefore internally consistent, but the PR description
claiming this is "the standard basis" for intuitionistic logic is incorrect.

---

### Finding 3: Counter-claim 2 is CORRECT — the cited literature does not use {imp, bot} as sole primitives

**Counter-claim**: "Gentzen was not using the implication+falsum basis you are proposing."
Also: "the presentations in Prawitz and Troelstra & van Dalen do not do this kind of reduction."

**Verdict for Heyting 1930**: The counter-claim is correct. Multiple sources confirm:
- Heyting 1930 uses all of →, ∧, ∨, ¬ as primitives (or close to it).
- The Stanford Encyclopedia section on Heyting's 1930 work shows that both conjunction AND
  disjunction appear explicitly as separate axiom groups in his formalization.
- The non-interdefinability of these connectives was explicitly stated by Heyting 1930 (p.44):
  "none of →, ∧, ∨, ¬ can be defined in terms of the others." This is a theorem he proved
  (or stated without proof), not a design choice to avoid — it is a fundamental FACT that
  they cannot be reduced in the intuitionistic setting.

If Heyting 1930 were using {imp, bot} as sole primitives, it would contradict his own statement
that the four connectives are not interdefinable (since then ∧ and ∨ would be definable from
→ and ¬/⊥). Heyting cannot both assert non-interdefinability and use {imp, bot} as a complete
primitive basis.

**Verdict for Gentzen 1935 (NJ)**: The counter-claim is correct. Gentzen's NJ (natural deduction
for intuitionistic logic) treats conjunction, disjunction, implication, and falsum all as having
independent primitive introduction and elimination rules. Scholarly analysis confirms:
- NJ has ∧I, ∧E (two rules), ∨I (two rules), ∨E, →I, →E, ⊥E as primitive rules.
- This is a system with conjunction and disjunction as genuine primitives, not derived.
- ctchou attached the Gentzen 1935 paper to PR #635 as direct evidence.

**Verdict for Prawitz 1965**: The counter-claim is correct. As confirmed by multiple sources:
- "Prawitz's natural deduction calculus contains twelve rules, with one Introduction and one
  Elimination rule for each of the six logical connectives ∧, ∨, →, ∀, ∃, and ⊥."
  (Search result from Stanford Encyclopedia and secondary literature)
- Prawitz treats all connectives (∧, ∨, →, ¬/⊥) as having independent primitive intro/elim rules.
- The search result about Prawitz also notes: "Prawitz showed how the usual natural deduction
  inference rules for disjunction, conjunction and absurdity can be derived using those for
  implication and the second order quantifier in propositional intuitionistic SECOND ORDER logic"
  — this uses second-order quantification, not just {imp, bot}, and is not relevant to the
  first-order system.

**Verdict for Troelstra & van Dalen 1988**: The counter-claim is correct. Troelstra & van Dalen
use the standard intuitionistic connective set {→, ∧, ∨, ⊥} with negation as abbreviation
¬A := A → ⊥. They do NOT reduce ∧ and ∨ to {→, ⊥}.

**Verdict for Church 1956**: Church treats classical propositional logic. His basis would be
consistent with using {→, ⊥} for the classical logic fragment, but does not establish this
as a standard for intuitionistic or minimal logic.

**Verdict for Chagrov & Zakharyaschev 1997**: This book is about MODAL logic. Chapter 1 covers
classical propositional logic as background. They may well use a {→, ⊥} basis for classical
propositional logic (which is valid classically), but this does not establish the basis for IPL.

**Summary**: The PR description's claim that {imp, bot} is "the standard one in the literature"
conflates the classical adequacy of this basis with its inadequacy for the intuitionistic setting
that the cited authors (Heyting, Gentzen, Prawitz, Troelstra & van Dalen) were primarily concerned
with. None of these sources use {imp, bot} as the sole primitive set for intuitionistic logic.

---

### Finding 4: Counter-claim 3 is CORRECT — "5 rules instead of 10" is wrong for intuitionistic logic

**Counter-claim**: The conjunction and disjunction rules are NOT derivable from imp/bot rules alone
in intuitionistic logic.

**Verdict**: Correct. This follows directly from Finding 2.

**The true count for Gentzen NJ**: The intuitionistic natural deduction system NJ has approximately:
- ∧I: 1 rule (conjunction introduction)
- ∧E: 2 rules (left and right projection)
- ∨I: 2 rules (left and right injection)
- ∨E: 1 rule (case analysis)
- →I: 1 rule (implication introduction)
- →E: 1 rule (modus ponens)
- ⊥E: 1 rule (ex falso quodlibet)

Total: approximately 9-10 primitive rules (with negation sometimes treated as →⊥).

**The CSLib {imp, bot} system has**:
- ax: axiom from theory
- ass: assumption
- impI: implication introduction
- impE: implication elimination (modus ponens)
- botE: ex falso quodlibet

That is 5 inference rules CLASSICALLY adequate. The PR description is accurate that the current
CSLib system has 5 primitive rules in the natural deduction type, but incorrect to claim this is
adequate for intuitionistic logic. The "10 primitive rules → 5 primitive rules" framing is only
meaningful classically.

**The key issue**: In the CSLib implementation, andE1, andE2, and orE require [IsClassical T].
This means the rules governing ∧ and ∨ are NOT purely derivable from the 5 primitive rules —
they require an additional axiom schema (double negation elimination) to work. So the claim
"conjunction/disjunction rules become derivable rather than postulated" is only half-true:
the introduction rules (andI, orI1, orI2) are genuinely derivable, but the elimination rules
require classical reasoning.

---

### Finding 5: Johansson 1937 and Minimal Logic

**What minimal logic actually uses**: Minimal logic (Johansson 1937) is "usually formulated using
the same syntax as intuitionistic propositional logic, with implication →, conjunction ∧,
disjunction ∨, and falsum ⊥ as the basic connectives." Negation is derived: ¬A := A → ⊥.

The CSLib code in Axioms.lean correctly defines MinPropAxiom with only implyK and implyS
(over the {imp, bot}-based formula type), reflecting the minimal logic fragment that only uses
implication. The minimal logic in CSLib avoids ex falso quodlibet, which is correct.

However, the Johansson 1937 paper is NOT in references.bib and should be added. The Bibliographic
key would be "Johansson1937" (published in Compositio Mathematica, vol. 4, 1937, pp. 119-136,
titled "Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus").

---

## Evidence/Examples

### Direct textual evidence from the CSLib code

In DerivedRules.lean:
- Line 28-36: The module header explicitly states that elimination rules for conjunction,
  disjunction, and biconditional "require [IsClassical T]" because "the Lukasiewicz encoding
  of these connectives is only classically equivalent to their standard definitions."
- Lines 129, 143, 174, 232, 289, 294: All conjunction/disjunction elimination rules gated on
  [IsClassical T].

This is an internal admission within the CSLib code itself that the {imp, bot} encoding is only
classically adequate.

### From authoritative logic references

1. **SEP on Intuitionistic Logic**: "the intuitionistic connectives ∧, ∨, →, ¬ are logically
   independent over IPC" — meaning none can be defined in terms of the others.
   Standard primitives: →, ∧, ∨, ⊥ (with ¬A as abbreviation for A → ⊥).

2. **PlanetMath**: "the four intuitionistic connectives are not inter-definable" (directly from
   Heyting 1930's statement proved by Wajsberg 1938 and McKinsey 1939).

3. **SEP (Heyting 1930)**: Heyting's axiom groups explicitly include separate groups for
   conjunction and disjunction, confirming all four connectives are primitive in his system.

4. **Wikipedia (Functional Completeness)**: {→, ⊥} is functionally complete for CLASSICAL
   propositional logic. No mention of intuitionistic completeness.

5. **Prawitz 1965**: "twelve rules, with one Introduction and one Elimination rule for each of
   the six logical connectives ∧, ∨, →, ∀, ∃, and ⊥." — all connectives are primitive.

### The Lukasiewicz encodings used in CSLib

The encodings in Defs.lean are "Lukasiewicz convention" derivations:
- ¬A := A → ⊥ (standard and uncontroversial even intuitionistically)
- ⊤ := ⊥ → ⊥ (standard)
- A ∨ B := ¬A → B := (A → ⊥) → B (classical only: fails intuitionistically)
- A ∧ B := ¬(A → ¬B) := (A → (B → ⊥)) → ⊥ (classical only: requires DNE for elimination)

The negation and verum definitions are fine for all three logics. The disjunction and conjunction
definitions are CLASSICALLY correct but NOT intuitionistically adequate for proof extraction.

---

## Recommended Approach

### Option 1: Restrict the scope claim (minimal fix)

Revise the PR description and module documentation to accurately state that:
- The {imp, bot} basis is adequate for **classical** propositional logic.
- Conjunction and disjunction elimination require classical reasoning ([IsClassical T]).
- This is a design choice that optimizes the classical case at the cost of making
  intuitionistic proofs require explicit classical instantiation.
- The cited literature (Heyting, Gentzen, Prawitz) does NOT use this basis for IPL.

This keeps the implementation as-is but fixes the false claims in documentation.

**Assessment**: Honest and minimal. The Lean code works correctly (the IsClassical constraints
are correct), but the justification needs revision.

### Option 2: Use the full {→, ∧, ∨, ⊥} primitive set (correct for all three logics)

Add ∧ and ∨ back as primitive constructors (alongside bot and imp) to match the standard
intuitionistic connective set. This is what Heyting, Gentzen, Prawitz, and Troelstra & van Dalen
actually use. The Proposition type would have 5 constructors instead of 3:
```lean
inductive Proposition (Atom : Type u) where
  | atom (x : Atom)
  | bot
  | imp (a b : Proposition Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
```
Negation and top remain derived (¬A := A → ⊥, ⊤ := ⊥ → ⊥).
NJ would then have ~9 primitive rules instead of 5, but with genuinely intuitionistic proofs.

**Assessment**: Correct for all three logics but increases inductive case counts. The CSLib
design was explicitly seeking to minimize case counts. This tradeoff is a genuine design decision.

### Option 3: Two-layer approach (most accurate for CSLib's goals)

Keep the minimal {imp, bot} Proposition type but be explicit that:
1. The proof system is primarily designed for **classical** propositional logic.
2. For intuitionistic logic, the IsIntuitionistic constraint adds ex falso but does NOT
   make the Lukasiewicz encodings behave intuitionistically for ∧ and ∨.
3. If genuine intuitionistic proofs are needed, PR #607 (which ctchou referenced) may be
   more appropriate.

**Assessment**: This is the most honest framing. It acknowledges the limitation without
changing the design.

### Recommended: Option 1 (immediate) + clarification comment

The immediate recommendation is to fix the documentation claims:
1. Remove or qualify the claim that {imp, bot} is "the standard [basis] in the literature"
   for intuitionistic logic — it is standard for classical logic only.
2. Remove Heyting, Gentzen, Prawitz, and Troelstra & van Dalen from the list of citations
   supporting this basis — they do not use it.
3. Keep Church 1956 and Chagrov & Zakharyaschev 1997 as appropriate citations for the
   classical basis.
4. Explicitly document in DerivedRules.lean that the "5 rule" system is classically adequate
   only, and that the conjunction/disjunction elimination rules use classical reasoning.
5. Add `Johansson1937` to references.bib (citation for minimal logic).

---

## Confidence Level

| Finding | Claim | Verdict | Confidence |
|---------|-------|---------|------------|
| 1 | {imp, bot} functionally complete classically | TRUE | HIGH |
| 2 | {imp, bot} NOT adequate for intuitionistic logic | TRUE (counter-claim correct) | HIGH |
| 3a | Heyting 1930 uses {imp,bot} as sole primitives | FALSE | HIGH |
| 3b | Gentzen 1935 uses {imp,bot} as sole primitives | FALSE | HIGH |
| 3c | Prawitz 1965 does NOT reduce to {imp,bot} | CORRECT | HIGH |
| 3d | Troelstra & van Dalen do NOT reduce to {imp,bot} | CORRECT | HIGH |
| 4 | "5 rules instead of 10" claim wrong for IPL | TRUE | HIGH |
| 5 | Johansson 1937 not in references.bib | TRUE (confirmed) | HIGH |

The main finding with the highest certainty: **the non-interdefinability of intuitionistic
connectives is a proved theorem** (Wajsberg 1938, McKinsey 1939), originally stated by Heyting
1930. This is not ambiguous. The claim that {imp, bot} is adequate for intuitionistic logic is
mathematically false, not merely a matter of convention.

---

## Additional Notes on Current CSLib State

The current CSLib code is internally consistent but makes potentially misleading claims:

1. **Defs.lean line 21-22**: "Primitives are `atom`, `bot` (falsum), and `imp` (implication);
   since `{imp, bot}` is functionally complete for classical logic..." — this correctly hedges
   with "classical logic". This claim is accurate.

2. **Defs.lean line 24-26**: "IsIntuitionistic: a theory is intuitionistic if it contains the
   principle of explosion" — this is an Axiom-schema approach, not a formula-level primitive
   change. Adding ex falso as an axiom schema does NOT make the Lukasiewicz encoding of ∧ and ∨
   intuitionistically correct.

3. **Connectives.lean lines 28-34**: "Falsum and implication are taken as the only propositional
   primitives because `{imp, bot}` is functionally complete for classical logic" — this is accurate
   but should be more explicit that this creates a classical system with derived ∧/∨.

4. **NaturalDeduction/Basic.lean lines 45-49**: "Conjunction and disjunction rules are derivable
   from these primitives together with the definitions of `∧` and `∨` in terms of `→` and `⊥`"
   — this is only true if we also have classical reasoning available. The claim is imprecise.

The fundamental design issue: CSLib is using a {imp, bot} basis and calling the result a system
that supports "minimal, intuitionistic, and classical" propositional logic via axiom schemas.
But the Lukasiewicz encodings of ∧ and ∨ used in this system are not intuitionistically adequate
in the sense that the standard natural deduction rules for these connectives require classical
assumptions to hold. The "intuitionistic" and "minimal" theories in CSLib are really fragments:
they have minimal/intuitionistic behavior for implications, but their conjunction and disjunction
connectives behave classically (requiring [IsClassical T] for elimination).

This is a genuine design concern raised by ctchou that the PR description does not adequately address.
