# Teammate A Findings — Round 2: Primary Source Verification

**Task**: 192 — Verify literature claims in PR description at `specs/archive/188_first_propositional_upstream_pr/pr-description.md`
**Round**: 2 (full markdown conversions now available)
**Date**: 2026-06-14

---

## Claim Under Review (from PR description)

> "The choice of primitive connectives for propositional logic is discussed in [Church1956] §24; the five-primitive signature with `⊥` is the standard one for intuitionistic and minimal logic in [TroelstraVanDalen1988] Chapter 2. Primitive `⊥` is required for Johansson's minimal logic [Johansson1937], which defines negation `¬A := A → ⊥` using `⊥` as an undefined primitive symbol ('undefiniertes Grundzeichen')."

And separately:

> "The name `imp` is standard in Lean formalization practice (e.g., Lean's own `Prop` operations and modal logic formalizations). The previous `impl` was non-standard — no major proof theory reference uses this abbreviation for implication."

---

## 1. Church §24 — What Does It Actually Say?

**Source**: `specs/literature/church_1956.md`, lines 7724–8079

### What §24 is about

Church §24 is explicitly about **classical functional completeness** — which systems of connectives are expressively complete for classical propositional logic. The section header at line 7725 reads:

> `PRIMITIVE CONNECTIVES` (§24 header, page 141)

And the opening paragraph (lines 7753–7757):

> "In P₂ we used implication and negation as primitive connectives for the propositional calculus, and in P₁ we used implication and the constant f. We go on now to consider some other choices of primitive connectives (including, for convenience of expression, the constants as 0-ary connectives)."

### Does §24 mention intuitionistic logic?

**No.** Church §24 contains no mention of intuitionistic logic whatsoever. The entire section is devoted to classical completeness results for various connective bases (conditioned disjunction + t + f; implication + f; implication + negation; negation + disjunction; negation + conjunction; Sheffer stroke; etc.). Intuitionistic logic does not appear.

### Does §24 discuss the five-primitive {⊥, →, ∧, ∨} signature?

**No.** The five-primitive signature `{atom, bot, imp, and, or}` is not discussed anywhere in §24. Church §24 considers systems such as:
- Conditioned disjunction + t + f (lines 7860–7861)
- Implication and f (lines 7908–7928)  
- Implication and negation (lines 7916–7928)
- Negation and disjunction (lines 7933–7948)
- Negation and conjunction (lines 7933–7948)
- Single connectives: non-conjunction (Sheffer stroke) (lines 7996+)

None of these systems include ⊥ with →, ∧, ∨ simultaneously as the four connectives plus atoms.

### What connective bases does §24 actually discuss?

All bases discussed are for **classical** propositional calculus. The section establishes functional completeness (ability to express any Boolean function) for several binary/unary combinations, culminating in results about Sheffer stroke and conditioned disjunction.

### §26 — Intuitionistic Propositional Logic

The correct section for intuitionistic and minimal logic is **§26**, not §24. Church §26 (lines 8291–8429) is titled "Partial systems of propositional calculus" and is where IPL is discussed:

Lines 8374–8376:
> "The primitive connectives of Pg are implication, conjunction, disjunction, **equivalence**, and **negation**."

This is Church's formulation Pg of the intuitionistic propositional calculus. It uses **five primitives: implication, conjunction, disjunction, equivalence, and negation** — not the set {⊥, →, ∧, ∨}. Church does not use ⊥ as a primitive here; he treats negation as primitive.

Lines 8393–8398 describe the minimal calculus P" (Johansson):
> "The minimal propositional calculus of Kolmogoroff and Johansson makes a more drastic rejection of classical laws involving negation. A formulation of it, P", may be obtained from Pg by replacing the two foregoing axioms by the single axiom..."

Church's presentation of the minimal calculus also uses negation as a primitive (not ⊥ as primitive).

### Verdict on Church §24 Claim

The PR claim that "the choice of primitive connectives for propositional logic is discussed in [Church1956] §24" is **technically accurate but misleading**. §24 does discuss primitive connectives, but:
1. It is entirely about **classical** logic, not intuitionistic/minimal logic
2. The five-primitive `{atom, bot, imp, and, or}` signature is **not discussed in §24**
3. The correct section for intuitionistic logic is **§26**

The citation of §24 for the "five-primitive signature with ⊥" is therefore a **mismatch** — §24 simply does not contain this content.

---

## 2. Gentzen 1935 — What Notation Does He Use?

**Source**: `specs/literature/gentzen_1935.md`

### Connective symbols Gentzen uses

From lines 83–116 (Section I, terminology):

> "Logical symbols: & 'and', v 'or', ⊃ 'if... then', ⊃ t 'is equivalent to', 'not', V 'for all', ∃ 'there is'."

Gentzen uses:
- **&** for conjunction
- **v** for disjunction  
- **⊃** (the horseshoe/hook symbol) for implication — **not** → (arrow)
- **¬** for negation (written as `1` in the OCR rendering)
- **A** (capital lambda/fraktur A) for the false proposition (lines 89, 113): "Symbols for definite propositions: V ('the true proposition'), **A** ('the false proposition')"

### Does Gentzen use "imp" or "impl"?

**No.** Gentzen never uses the abbreviation "imp" or "impl" anywhere. He names his inference figures with symbols like:
- `⊃-I` and `⊃-E` for implication introduction/elimination (in NJ)
- `=-IS` and `=-IA` for implication introduction in succedent/antecedent (in LJ/LK)

The naming pattern uses the actual connective symbol (⊃), not an English abbreviation.

### What does NJ use as primitives?

NJ (natural deduction for intuitionistic logic) uses all standard connectives: &, v, ⊃ (implication), ¬ (negation), ∀, ∃. Gentzen notes at lines 601–612 that negation can be eliminated from NJ by treating ¬A as an abbreviation for A ⊃ A (where A is the propositional constant for "the false"):

> "5.2. It is possible to eliminate the negation from our calculus by regarding A. This is permissible, since by replacing every ¬A by A ⊃ A..."
> "5.2. It is possible to eliminate the negation from our calculus by regarding A as an abbreviation for A ⊃ A."

So Gentzen shows that ¬A := A ⊃ A (falsum) is definitionally equivalent in NJ, but he does not make ⊥ a **primitive** while abandoning ¬.

### Does Gentzen explicitly list his primitive connectives?

Gentzen does not frame NJ as having "primitive connectives" in the way an axiomatic system does. He defines which logical symbols occur (Section I), but the NJ system is presented via inference figure schemata for all connectives simultaneously. The symbol A (falsum) plays a special role (it has no I-rule, only an E-rule that makes any formula derivable from it), but it is a **propositional constant**, not described as one of the primitive connectives in Church's sense.

### Verdict on Gentzen claim

The PR says `imp` is standard per "Gentzen/Prawitz." Gentzen uses **⊃** (not "imp" as a word), and his inference figure names use the symbol itself (`⊃-I`, `⊃-E`). The claim that Gentzen uses "imp" as an abbreviation is **false** — Gentzen never uses this English abbreviation. However, the PR's broader point that `imp` is more standard than `impl` in Lean formalization may still be valid independently of the Gentzen citation.

---

## 3. Johansson 1937 — Verify Exact German Quotes

**Source**: `specs/literature/johansson_1937.md`

### "undefiniertes Grundzeichen"

**Found at line 71–72** (§1, Einleitung):

> "Die Auffassung von A. als undefiniertes Grundzeichen und die Definition von ¬ durch liegt dann sehr nahe."

Context (lines 68–77):
> "Die Möglichkeit ¬a durch a⊃A (wo A 'Widerspruch' oder 'etwas Falsches' bedeutet) zu ersetzen, ist wahrscheinlich recht allgemein bekannt; sie hängt ja mit dem Axiom 4.11 bei Heyting eng zusammen. **Die Auffassung von A als undefiniertes Grundzeichen und die Definition von ¬ durch** liegt dann sehr nahe."

Johansson uses **A** (not ⊥ or Λ) for falsum/contradiction. He writes that treating A as an "undefined primitive symbol" ("undefiniertes Grundzeichen") and defining negation via A is a natural choice.

### "undefinierte Grundaussage"

**Found at line 362** (§4, Die Aussage A):

> "Die Auffassung von A als eine undefinierte Grundaussage ist mit der von Kolmogoroff angegebenen 'aufgabentheoretischen' Deutung der intuitionistischen Logik verwandt."

Both phrases appear: "undefiniertes Grundzeichen" (§1) and "undefinierte Grundaussage" (§4). The PR description quotes "undefiniertes Grundzeichen" and this is confirmed present at lines 71–72.

### What symbol does Johansson use for falsum?

Johansson uses **A** (the letter A, apparently representing "Absurdum" or "Widerspruch"). The text at lines 68–69 explicitly states:

> "wo A 'Widerspruch' oder 'etwas Falsches' bedeutet"

He does **not** use ⊥ or Λ. The PR description translates Johansson's A as "⊥", which is a reasonable modern convention but is not Johansson's own notation.

### What is Johansson's exact definition of negation?

At lines 68–75, Johansson defines negation implicitly as:
- ¬a := a ⊃ A

This is stated in the natural language passage but also formalized at line 314–315:

> "Man kann aber auch umgekehrt A zu Grunde legen, und ¬ folgendermaßen definieren:"

And formula (22) (referenced at line 320) is the definition ¬a := a ⊃ A.

### What connectives does Johansson list as primitive?

Johansson's minimal calculus uses: **⊃** (implication), **A** (falsum, treated as an undefined primitive proposition), **v** (disjunction). He builds on Heyting's axioms for these three plus adds his own treatment of negation.

The key section §4 (lines 301–413) is titled "Die Aussage A ('Widerspruch') und deren Deutungen" and explains that A is treated "wie mit einer Aussagenvariablen" (like a propositional variable) — i.e., with no special axioms about it (line 319).

Conjunction (∧) appears implicitly through Heyting's axioms (§2 imports Heyting's §§2–3 unchanged), but Johansson does not explicitly list "primitive connectives" in the modern sense — he states which Heyting axioms he keeps vs. drops.

### Verdict on Johansson claim

The PR says Johansson defines "negation `¬A := A → ⊥` using `⊥` as an undefined primitive symbol ('undefiniertes Grundzeichen')."

This is **substantially correct** with a notation caveat:
- Johansson does define ¬a := a ⊃ A (not →, but ⊃, and not ⊥, but A)
- The phrase "undefiniertes Grundzeichen" does appear at line 71–72, exactly as quoted
- The PR substitutes ⊥ for Johansson's A and → for Johansson's ⊃, which are standard modern equivalents
- The quote is **confirmed present** in the text

However, the PR quote uses → (arrow) whereas Johansson uses ⊃ (horseshoe), and uses ⊥ whereas Johansson uses A. These are conventional modernizations, not fabrications.

---

## 4. Bentzen 2023 — What Constructor Names?

**Source**: `specs/literature/bentzen_2023.md`

### What constructor name does Bentzen use for implication?

**`impl`** — confirmed at lines 118–119:

```lean
| impl : form → form → form
```

The inductive type definition (lines 110–127) shows:
```lean
inductive form : Type
| atom : N → form
| bot  : form
| impl : form → form → form
| and  : form → form → form
| or   : form → form → form
```

Bentzen uses **`impl`**, not `imp`.

### What primitive connectives does the formula type have?

Five primitives: `atom`, `bot`, `impl`, `and`, `or` (lines 110–127). The PR description's five-primitive signature matches Bentzen's exactly: `{atom, bot, imp, and, or}` — except Bentzen calls the implication constructor **`impl`** not `imp`.

### Does Bentzen cite TroelstraVanDalen Chapter 2?

**Yes**, at reference [17] (lines 821–822):

> "[17] Troelstra, A.S., van Dalen, D.: Constructivism in mathematics. Vol. I, Studies in Logic and the Foundations of Mathematics, vol. 121. North-Holland, Amsterdam (1988)"

The paper's abstract (line 15) also states:

> "This paper presents a formalization of the classical proof of completeness in Henkin-style **developed by Troelstra and van Dalen** for intuitionistic logic with respect to Kripke models."

Bentzen cites TroelstraVanDalen [17] throughout the paper. The paper does not cite a specific chapter number "Chapter 2" in the body text — the citation is to the book as a whole.

### Verdict on Bentzen claim

The PR claim that Bentzen uses constructor name `impl` for implication is **correct** — confirmed at lines 118–119. This is directly relevant because the PR **renames** `impl` to `imp`, claiming `impl` is "non-standard." Yet Bentzen 2023 — cited in the same PR as a key reference — uses **`impl`** as the constructor name for implication. This **undermines** the PR's claim that `impl` is non-standard.

The PR description says:
> "The previous `impl` was non-standard — no major proof theory reference uses this abbreviation for implication."

But Bentzen 2023 — a paper explicitly about Lean formalization of IPL — uses precisely `impl`.

---

## Summary Table

| Claim | Source Section | Verdict |
|-------|---------------|---------|
| Church §24 discusses "primitive connectives" | §24 header (line 7725) | **TRUE** (but misleading — §24 is about *classical* completeness only) |
| Church §24 discusses intuitionistic/minimal logic | §24 (lines 7724–8079) | **FALSE** — intuitionistic logic is in §26, not §24 |
| Church §24 discusses five-primitive {⊥, →, ∧, ∨} signature | §24 entire | **FALSE** — this signature never appears in §24 |
| Church §26 lists IPL primitives as {⊥, →, ∧, ∨} | §26 (line 8375) | **FALSE** — Church lists {→, ∧, ∨, ↔, ¬}, i.e., negation not ⊥ |
| Johansson uses "undefiniertes Grundzeichen" for ⊥ | §1 (line 71–72) | **TRUE** — phrase confirmed, but symbol is A not ⊥ |
| Johansson's definition: ¬A := A → ⊥ | §1 (lines 68–75), §4 (line 314) | **SUBSTANTIALLY TRUE** — he writes ¬a := a ⊃ A (A = falsum, ⊃ = implication) |
| Gentzen uses "imp" as abbreviation for implication | Full text | **FALSE** — Gentzen uses ⊃ symbol; inference figures named ⊃-I, ⊃-E |
| Bentzen uses constructor name `impl` (not `imp`) | Lines 118–119 | **TRUE** — Bentzen uses `impl`, contradicting PR claim that `impl` is non-standard |
| Bentzen cites TroelstraVanDalen | Reference [17], line 821 | **TRUE** — cited throughout; "Chapter 2" not specifically mentioned |

---

## Key Finding for PR Review

The most significant issue is the **Church §24 citation**. The PR says "the choice of primitive connectives for propositional logic is discussed in [Church1956] §24" in the context of a five-primitive signature for intuitionistic/minimal logic. This is misleading because:

1. Church §24 discusses primitive connectives for **classical** propositional logic only
2. The five-primitive {atom, bot, imp, and, or} signature is **not in §24**
3. Intuitionistic propositional logic is in **§26**, where Church uses {→, ∧, ∨, ↔, ¬} — with negation primitive, not ⊥

The correct citation for a five-primitive signature with ⊥ for intuitionistic logic would be Bentzen 2023 itself (which uses exactly this signature), or TroelstraVanDalen Chapter 2 (cited but not verified here as that text is not in the literature directory).

The secondary finding is that the PR's naming claim — that `impl` is non-standard and should be `imp` — is **undermined by Bentzen 2023**, which uses `impl` as the Lean constructor name for implication in a directly comparable IPL formalization.
