# Teammate C Findings: Citation Accuracy Audit

**Task 192** — Round 2 Critic  
**Scope**: Audit literature citations in PR-scoped files against primary sources  
**Files audited**:
- `Cslib/Foundations/Logic/Connectives.lean`
- `Cslib/Logics/Propositional/Defs.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
- `Cslib/Foundations/Logic/Axioms.lean`

---

## 1. File-by-File Audit

### 1.1 `Cslib/Foundations/Logic/Connectives.lean`

**Claim (lines 29-34)**:
> Conjunction and disjunction are treated as primitives rather than Lukasiewicz-derived connectives. The classical encodings `and φ ψ := ¬(φ → ¬ψ)` and `or φ ψ := ¬φ → ψ` are only propositionally equivalent to `∧` and `∨` in classical logic ([Wajsberg1938], [McKinsey1939]); they fail in intuitionistic and minimal logic.

**Verdict: ACCURATE with minor over-attribution.**

The logical claim is correct: the Lukasiewicz encodings of conjunction/disjunction via implication and negation are classically but not intuitionistically equivalent to the primitive connectives. Wajsberg (1938) and McKinsey (1939) are appropriate supporting references — they investigated the independence of axioms in Heyting's calculus and exactly these kinds of classical-vs-intuitionistic equivalences. The encoding `and φ ψ := ¬(φ → ¬ψ)` is directly visible in Church (1956), §24, which proves completeness of `{negation, conjunction}` as well as the classical definability of all connectives from `{implication, negation}`. The [Church1956] citation listed in the references block is relevant background but not invoked inline here — this is fine.

**Note**: The claim does not assert that Wajsberg or McKinsey explicitly discuss "minimal logic" (which postdates them). What the sources establish is that the encodings work classically but not sub-classically. This is the correct reading.

---

**Claim (reference block, lines 43-53)**:
Lists [Johansson1937], [Wajsberg1938], [McKinsey1939], [Prawitz1965], [TroelstraVanDalen1988], [Church1956], [Heyting1930], [Gentzen1935], [ChagrovZakharyaschev1997].

**Verdict: PARTIAL CONCERN — [Prawitz1965] and [TroelstraVanDalen1988] are listed but not cited inline. The reference block is permissive (it lists references used anywhere in the module's context), so this is an editorial choice rather than a factual error. However, [Prawitz1965] is not cited in the module docstring body; it appears in other files. Reviewers may question why it appears here.**

**Recommendation**: Either add an inline citation justifying Prawitz's presence, or move it to files where it is directly cited.

---

### 1.2 `Cslib/Logics/Propositional/Defs.lean`

**Claim (lines 20-22)**:
> Primitives are `atom`, `bot` (falsum), `imp` (implication), `and` (conjunction), and `or` (disjunction), following the **standard Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition**.

**Verdict: PROBLEMATIC — "full-connective tradition" is an invented label. The grouping is defensible but the phrasing implies a single named tradition that does not exist as such in the literature.**

Breaking this down:

**Gentzen (1935)**: Gentzen's NJ/NK natural deduction calculus uses `{&, v, ⊃, ¬, ∀, ∃}` as distinct primitive symbols with introduction and elimination rules for each (Section II, §2.21). He explicitly notes in §5.2 that negation `¬A` can be regarded as an abbreviation for `A ⊃ A` (where `A` is the falsum constant), and that this replacement transforms a valid derivation into another valid derivation. So Gentzen himself shows that negation need not be primitive — his natural deduction system treats it as an abbreviation at the meta-level. Gentzen does not treat falsum `⊥` as a standalone primitive in the same way CSLib does; rather, he introduces a propositional constant `A` (the false proposition). The situation is more nuanced than "all connectives as primitive."

**Johansson (1937)**: Johansson's minimal calculus builds directly on Heyting's formalization. Its signature is `{⊃, A (falsum), v}` — where `¬` is defined as `¬a := a ⊃ A` (see §4 of the paper). Conjunction is handled via Heyting's §§2–3, which Johansson explicitly adopts unchanged (§2, first paragraph). The Johansson paper does treat `{⊃, A, v, ∧}` as the connective vocabulary, with negation derived, but he is specifically not adding to this tradition — he is reducing it by removing ex falso.

**Prawitz (1965)**: Prawitz's book treats `{∧, ∨, ⊃, ⊥}` as primitives with `¬A := A ⊃ ⊥` as a defined abbreviation (Ch. I, §1.2, the reference cited in Equivalence.lean). This is essentially the signature CSLib uses. This is the most direct source for the CSLib design.

**Troelstra and van Dalen (1988)**: Also use `{∧, ∨, ⊃, ⊥, ∀, ∃}` with `¬` derived, following Heyting's tradition.

**Bentzen (2023)**: Uses `{bot, impl, and, or}` as primitives with negation defined (Section 2.1, the `form` inductive type) — exactly the CSLib signature.

**Assessment of "Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition"**:

The description is historiographically imprecise for two reasons:
1. Gentzen himself does NOT strictly treat negation as derived (he includes `¬`-I and `¬`-E rules and merely notes that negation is eliminable). The true source of treating `¬` as *derived* in the sense CSLib uses (as a notation `A ⊃ ⊥`) is more traceable to Prawitz (1965) and the subsequent intuitionist tradition following from Heyting.
2. The phrase "full-connective tradition" implies a contrast with some "reduced-connective tradition," but the actual tradition being contrasted here is the classical Hilbert-style approach where `{⊃, ¬}` or `{⊃, ⊥}` suffice (because `∧` and `∨` are classically definable from them). Calling the multi-connective approach a named "tradition" attributed to these three authors is an editorial construction, not a historiographic fact.

**What is accurate**: These three bodies of work do all use `{∧, ∨, ⊃, ⊥}` (or the equivalent) as the primary logical vocabulary, with `¬` derived. So the underlying claim (that CSLib's connective signature follows these authors) is true. The label "full-connective tradition" is author-invented but not factually wrong.

**Recommendation**: Replace the phrasing. Two alternatives:
- **Minimal fix**: "following Prawitz (1965) and the constructive logic tradition in treating `¬` as derived from `⊥` (see [Prawitz1965], Ch. I §1.2; [TroelstraVanDalen1988])"
- **More precise fix**: "following the natural deduction tradition ([Gentzen1935], [Prawitz1965]) and constructive mathematics ([TroelstraVanDalen1988]) in treating `{bot, imp, and, or}` as primitive and negation as derived via `¬A := A → ⊥`"

---

### 1.3 `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

**Claim (lines 51-54)**:
> `MPL` (minimal propositional logic, Johansson 1937 [Johansson1937]): no axioms beyond the 10 primitive rules; bottom has no special status.

**Verdict: ACCURATE.**

This is confirmed by the Johansson (1937) text. Johansson's minimal calculus differs from Heyting's intuitionistic calculus precisely by removing the axiom `4.1: ¬a ⊃ (a ⊃ b)` (ex falso quodlibet), meaning bottom has no special elimination rule (§1). Johansson confirms in §2 that all theorems of Heyting's §§2–3 (concerning `⊃, A, v`) carry over unchanged, and §5 establishes the natural deduction version (NM calculus). The description "bottom has no special status" accurately captures that `⊥ → A` is not derivable.

---

**Reference cite (line 61)**:
> `[TroelstraVanDalen1988], Section 10.4`

**Verdict: PLAUSIBLE but unverifiable from available sources.** The available `bentzen_2023.md` literature file cites TroelstraVanDalen1988 as reference [17] but does not reproduce their section numbering. The Bentzen (2023) paper refers to "Troelstra and van Dalen's method" for completeness, and the Bentzen 2023 paper makes clear TvD treat intuitionistic logic with `{impl, conj, disj, falsity}` as primitives. The Section 10.4 citation in Basic.lean is specific enough to be credible (TvD's Constructivism in Mathematics, Vol. I, Ch. 10 covers natural deduction and the relationship between Hilbert and ND systems for intuitionistic logic). Without the TvD text directly available, this cannot be confirmed as precisely accurate, but it is not obviously wrong.

**Recommendation**: Flag for secondary verification against the TvD text itself.

---

**Claim (line 62-64)**:
> `[Gentzen1935]`

**Verdict: APPROPRIATE.** Gentzen (1935) is the foundational source for natural deduction (`NJ` calculus), and its citation here is entirely correct.

---

### 1.4 `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`

**Claim (line 65-66)**:
> `[Prawitz1965], Ch. I, §1.2 — primary reference for the Hilbert/ND equivalence`

**Verdict: PLAUSIBLE.** Prawitz (1965) Chapter I establishes natural deduction systems and their relationship to axiomatic systems. §1.2 in particular is where the equivalence between natural deduction and axiomatic systems is treated. This is a standard reference for this result and the citation is appropriate.

---

**Claim (lines 67-68)**:
> `[TroelstraVanDalen1988], Vol. I, §10.4 — intuitionistic case`

**Verdict: PLAUSIBLE but unverifiable (same caveat as above).** The intuitionistic case of the Hilbert/ND equivalence is covered in TvD's Constructivism in Mathematics, and §10.4 is a plausible section reference for this. Cannot confirm exact section numbering without the text.

---

### 1.5 `Cslib/Foundations/Logic/Axioms.lean`

**Claims (lines 54 and 64)**:
> `The Lukasiewicz encoding is classically equivalent to ∧, but not intuitionistically ([Wajsberg1938], [McKinsey1939]).`

**Verdict: ACCURATE.** This is the same claim as in Connectives.lean and is correct. Wajsberg (1938) and McKinsey (1939) investigated independence in Heyting's calculus, establishing what holds and fails sub-classically. The encodings `¬(φ → ¬ψ)` for conjunction and `¬φ → ψ` for disjunction are indeed classical-only.

---

## 2. The "Full-Connective Tradition" Claim — Detailed Assessment

The phrase "standard Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition" (Defs.lean, line 21) is the most significant citation-accuracy concern in the PR.

**Primary source evidence**:

1. **Gentzen (1935)**: Section I.1.1 lists `{&, v, ⊃, ≡, ¬}` as the logical symbols (along with quantifiers). Negation is listed as a primitive symbol, not derived. However, §5.2 shows that `¬A` can be treated as `A ⊃ A` (falsum), making negation eliminable. Gentzen's system does NOT define connectives from each other by default — all are present. So calling Gentzen a representative of treating "all connectives as primitive" is misleading: he shows they can be reduced but keeps them explicit for presentational reasons.

2. **Johansson (1937)**: The minimal calculus uses `{⊃, A (falsum), v, ∧}` with `¬a := a ⊃ A` (§4). Johansson explicitly derives negation rather than taking it as primitive. This matches CSLib's design. Johansson cites Heyting's §§2–3 and Gentzen's NJ. Johansson IS a clear precedent for the CSLib connective signature.

3. **Bentzen (2023)**: Uses `{bot, impl, and, or}` as the four primitive constructors in the `form` inductive type, with `¬p := p ⊃ ⊥` as notation. This is the most direct match to CSLib's `Proposition` type, and confirms this is a standard formalization choice in the Lean-based literature.

**Conclusion**: The underlying design choice (four primitives: `{⊥, →, ∧, ∨}`, negation derived) is sound and supported by Prawitz, Johansson, TvD, and Bentzen. The phrase "full-connective tradition" attributed to "Gentzen/Prawitz/Troelstra-van Dalen" is a label that:
- Is not a recognized term in the logic literature
- Slightly misrepresents Gentzen (who keeps `¬` as an explicit primitive symbol, even if he notes it is eliminable)
- Omits Johansson, who is arguably the most direct predecessor for the CSLib minimal logic framing

---

## 3. Church 1956 Citation Assessment

**Church (1956)** appears in the References blocks of Connectives.lean and Defs.lean but is not cited inline in the module docstrings of those files. Based on reading §24 of Church (1956), the text:
- Proves that `{implication, negation}` and `{negation, disjunction}` and `{negation, conjunction}` are each complete systems of primitive connectives for the propositional calculus
- Shows classical interdefinability of `∧`, `∨`, `⊃`, `¬`
- Does NOT discuss minimal logic or the failure of Lukasiewicz encodings in sub-classical settings

**Assessment**: Church (1956) is a legitimate background reference for classical propositional logic and connective systems, but it does not directly support the specific claims in Connectives.lean (which are about failures in intuitionistic/minimal logic). The errata note on page 5 of Church even mentions Wajsberg's paper and Curry's correction, showing Church was aware of these results. However, invoking Church as a reference for the Lukasiewicz encoding *failing* intuitionistically is tangential — Church's treatment is entirely classical. 

**Verdict**: The [Church1956] citation adds marginal value to these docstrings. It is not wrong to list it, but it may mislead a reader into thinking Church discusses the intuitionistic failure. The more precise citations are [Wajsberg1938] and [McKinsey1939] for the independence results, and [Johansson1937] for the minimal logic context.

**Recommendation**: Either annotate Church's role more clearly (e.g., "for classical connective systems") or drop it from modules where the claims are specifically about the sub-classical failure of Lukasiewicz encodings.

---

## 4. Summary of Findings

| File | Claim | Verdict | Severity |
|------|-------|---------|----------|
| Connectives.lean | Lukasiewicz encodings fail intuitionistically [Wajsberg1938], [McKinsey1939] | Accurate | None |
| Connectives.lean | [Prawitz1965] in reference block but not cited inline | Over-inclusion | Low |
| Defs.lean | "Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition" | Invented label; Gentzen mischaracterized | **Medium** |
| Defs.lean | MPL = Johansson 1937 | Accurate | None |
| Basic.lean | MPL: bottom has no special status [Johansson1937] | Accurate | None |
| Basic.lean | [TroelstraVanDalen1988] Section 10.4 | Plausible, unverifiable | Low |
| Equivalence.lean | [Prawitz1965] Ch. I §1.2 for Hilbert/ND equivalence | Appropriate | None |
| Axioms.lean | Lukasiewicz encodings classically only [Wajsberg1938], [McKinsey1939] | Accurate | None |
| Multiple files | [Church1956] — marginal relevance for intuitionistic claims | Tangential | Low |

---

## 5. Priority Recommendations

**Priority 1 (Medium severity)**: Fix the "full-connective tradition" claim in Defs.lean line 21.

Suggested replacement for lines 20-22:
```
Primitives are `atom`, `bot` (falsum), `imp` (implication), `and` (conjunction), and
`or` (disjunction). Negation (`neg`), verum (`top`), and biconditional (`iff`) are
derived connectives (`abbrev`s). This follows natural deduction style
([Gentzen1935], [Prawitz1965], Ch. I §1.2) and the constructive mathematics
tradition ([Johansson1937], [TroelstraVanDalen1988]) in which `¬A` abbreviates
`A → ⊥` rather than being taken as primitive.
```

**Priority 2 (Low severity)**: Clarify or remove [Church1956] from modules where the claim is specifically about intuitionistic/sub-classical failures.

**Priority 3 (Low)**: Verify [TroelstraVanDalen1988] §10.4 against the actual text before final PR submission.

**No action needed**: All claims about Johansson (1937), Wajsberg (1938), McKinsey (1939), and Gentzen (1935) as sources for natural deduction are factually accurate.
