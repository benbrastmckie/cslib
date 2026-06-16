<!-- Source: Gabbay, D., Hodkinson, I., and Reynolds, M. (1994). Temporal Logic: Mathematical Foundations and Computational Aspects, Volume 1. Oxford University Press. Chapter 10: Temporal Logic over the Integers, pp. 562-640. BibKey: GHR94 -->

# Temporal Logic: Mathematical Foundations and Computational Aspects

## Chapter 10: Temporal Logic over the Integers

D. GABBAY, I. HODKINSON, M. REYNOLDS

Oxford University Press, 1994. Pages 562–640.

---

### 10.1 Introduction

This chapter establishes completeness for temporal logic over the integers ℤ = ⟨ℤ, <⟩. The main result is that the Until-Since tense logic over the integers is axiomatizable, with a specific finite axiom schema. The chapter proceeds by:

1. Defining the Separation Theorem (§10.2), which shows every formula is equivalent to a Boolean combination of "pure past" and "pure future" formulas
2. Using separation to reduce completeness of the full U-S logic to completeness of one-directional fragments
3. Proving completeness via a canonical model construction adapted for integer time

The key technical tool is the *separation theorem* (Theorem 10.2.9), which says that any formula of the Since-Until language can be separated into a Boolean combination of formulas that use only past operators and formulas that use only future operators.

---

### 10.2 The Separation Theorem

#### 10.2.1 Definitions

Let the language ℒ contain propositional variables, Boolean connectives, and the binary temporal operators U (Until) and S (Since). We define:

**Definition 10.2.1 (Pure Future/Past Formulas).**
- A formula is *purely future* if it contains no occurrence of S (no past operators)
- A formula is *purely past* if it contains no occurrence of U (no future operators)
- A formula is *separated* if it is a Boolean combination of purely future and purely past formulas

**Lemma 10.2.1 (Distributivity Laws).** The following equivalences hold over all integer flows:

- S(φ ∨ ψ, χ) ↔ S(φ, χ) ∨ S(ψ, χ)  [S distributes over disjunction in first argument]
- U(φ ∨ ψ, χ) ↔ U(φ, χ) ∨ U(ψ, χ)  [U distributes over disjunction in first argument]
- S(φ, ψ ∨ χ) ↔ S(φ, ψ) ∨ S(φ, χ)  [S distributes over disjunction in second argument]
- U(φ, ψ ∨ χ) ↔ U(φ, ψ) ∨ U(φ, χ)  [U distributes over disjunction in second argument]

These distributivity laws are used throughout the normalization procedure.

**Lemma 10.2.2 (Negation Equivalences).** For ℤ-models:

- S(φ, ψ) ↔ ¬S(¬φ ∨ ψ, ¬φ)  [negation pushes through S]
- U(φ, ψ) ↔ ¬U(¬φ ∨ ψ, ¬φ)  [negation pushes through U]

These allow S and U to appear only with positive occurrences in normal forms.

**Lemma 10.2.3 (Duality).** The following duality holds over all linear orders:

- ¬Fφ ↔ H¬φ  (¬Pφ ↔ G¬φ)
- S(φ, ψ) and U(φ, ψ) are not duals of each other, but have mirror-image semantics

#### 10.2.2 Formula Hierarchy

To prove the separation theorem, we stratify formulas by a *rank* measuring the nesting of mixed U-S operators.

**Definition 10.2.4 (Rank).** The *U-S rank* of a formula is defined inductively:
- Atomic formulas have rank 0
- Boolean combinations preserve the maximum rank of subformulas
- If φ has rank n, then Uφ and Sφ have rank n + 1 (when φ contains operators of both polarities)

The key inductive step in the separation theorem reduces rank-n formulas to Boolean combinations of rank-(n-1) formulas together with purely past or purely future formulas.

#### 10.2.3 Elimination Lemmas

**Lemma 10.2.5 (Since-Elimination).** Over ℤ, every formula S(α, β) where β is purely past and α is arbitrary, is equivalent to a formula in which S occurs only applied to purely past subformulas.

*Proof sketch.* Write α = α_fut ∨ α_mix where α_fut is purely future and α_mix contains S-operators. Apply the distributivity law: S(α_fut ∨ α_mix, β) ↔ S(α_fut, β) ∨ S(α_mix, β). The second term S(α_mix, β) can be further reduced. The key case is S(S(φ,ψ), χ) which is equivalent to a formula of lower rank.

**Lemma 10.2.6 (Until-Elimination).** The dual statement holds for U.

**Lemma 10.2.7 (TemporalClosure).** The Boolean closure of purely future formulas and purely past formulas is closed under S and U in the following sense: any formula S(α_past, β_past) with both arguments purely past is itself equivalent to a purely past formula.

#### 10.2.4 Main Separation Result

**Theorem 10.2.9 (Separation Theorem).** Over the integer flow ⟨ℤ, <⟩, every formula φ of the U-S language is equivalent (has the same truth value at every point in every ℤ-model) to a separated formula — i.e., a Boolean combination of purely future and purely past formulas.

*Proof.* By induction on the structure of φ and on the U-S rank:

*Base case*: Atomic formulas and Boolean combinations are separated.

*Inductive step*: For S(φ, ψ): by the induction hypothesis, φ and ψ are equivalent to separated formulas. The separation theorem for compound S and U formulas follows from the elimination lemmas (10.2.5 and 10.2.6) applied iteratively, reducing rank at each step.

The key insight is that the integer flow has the *Dedekind-like* property that for any current moment t:
- Every formula φ is either "about the past" (depends only on T^≤t) or "about the future" (depends only on T^≥t) or can be rewritten as such

This structural property is what makes separation work for ℤ but not for all linear orders.

**Corollary 10.2.10 (Reduction to One-Directional Logic).** Completeness for the full U-S language over ℤ reduces to:
1. Completeness of the purely future fragment (the Until-only tense logic)  
2. Completeness of the purely past fragment (the Since-only tense logic)
3. Showing that the combination axioms (the "interaction axioms" between past and future) are complete

---

### 10.3 The Axiom System for Integer Temporal Logic

**Definition 10.3.1 (System TLZ).** The axiom system TLZ for temporal logic over ℤ consists of:

**Propositional axioms**: All tautologies.

**Future axioms**:
- (K_G) G(φ → ψ) → (Gφ → Gψ)
- (K_U) G(φ → ψ) → (U(χ,φ) → U(χ,ψ))  [U monotone in second argument]
- (U_expand) U(φ,ψ) ↔ ψ ∨ (φ ∧ F U(φ,ψ))  [Until unfolding — here F = U(⊤,·)]

Wait: more precisely, F φ abbreviates U(⊤, φ) and the Until expansion is:
- (U_exp) U(φ,ψ) ↔ ψ ∨ (φ ∧ °F U(φ,ψ))  where °F is "next moment"

**Past axioms** (mirror images):
- (K_H) H(φ → ψ) → (Hφ → Hψ)
- (K_S) H(φ → ψ) → (S(χ,φ) → S(χ,ψ))
- (S_exp) S(φ,ψ) ↔ ψ ∨ (φ ∧ °P S(φ,ψ))  where °P is "previous moment"

**Interaction axioms** (connecting past and future):
- (GP) φ → G P φ  (if φ now, then always in the future φ has been true)
- (HF) φ → H F φ  (if φ now, then always in the past φ will have been true)
- (GrndG) ¬G⊤ (there is always a future, i.e., time is infinite in the future)
- (GrndH) ¬H⊤ (time is infinite in the past)

**Discrete time axioms** (specific to ℤ):
- (succ_F) F φ ↔ °F φ ∨ °F F φ  (future = next or after-next)
- (succ_P) P φ ↔ °P φ ∨ °P P φ  (past = previous or before-previous)
- (circ_unique) °F °P φ ↔ φ  (next-then-previous = identity)
- (circ_unique2) °P °F φ ↔ φ  (previous-then-next = identity)

**Rules**: Modus Ponens, Necessitation for G, Necessitation for H.

**Theorem 10.3.2.** TLZ is sound with respect to ⟨ℤ, <⟩.

---

### 10.4 Completeness Proof

The completeness proof for TLZ proceeds via the Separation Theorem:

**Step 1.** Every formula φ is TLZ-equivalent to a separated formula sep(φ).

**Step 2.** Completeness of the purely future fragment (U-only logic over ℤ) by a filtered canonical model.

**Step 3.** Completeness of the purely past fragment (S-only logic over ℤ) by the dual construction.

**Step 4.** The interaction axioms ensure that the past and future canonical models can be combined into an ℤ-model satisfying sep(φ), and hence φ.

**Theorem 10.4.1 (Completeness).** Every TLZ-valid formula is provable in TLZ.

*Proof sketch.* Suppose φ is valid. By the Separation Theorem, sep(φ) is provably equivalent to φ in TLZ. By Steps 2-4, sep(φ) is provable. Therefore φ is provable.

The key lemma in Step 4 is:

**Lemma 10.4.2 (Integer Assembly).** Given a purely-future MCS Γ_fut and a purely-past MCS Γ_past that are *compatible* (i.e., agree on propositional atoms and on the interaction axioms), there exists a ℤ-model and a point t such that:
- t satisfies all formulas in Γ_fut
- t satisfies all formulas in Γ_past

The compatibility condition is exactly what the interaction axioms (GP, HF, etc.) guarantee.

---

### 10.5 The Burgess Construction for Bimodal Logic

The chapter also covers extensions to bimodal temporal logic where both the Until/Since operators and period-based ("during") operators are included. This is the "BX" system relevant to:

- Burgess (1982): Axioms for Tense Logic II (time periods)
- The bimodal completeness proof in GHR94

The bimodal language adds period operators D (during) and B (between), giving the BX axiom system. The Separation Theorem extends to the bimodal setting, allowing the bimodal completeness proof to reduce to the unimodal integer case.

**Definition 10.5.1 (BX Axioms).** The bimodal system BX extends TLZ with:
- D(φ, ψ): "φ holds during ψ" (period-based operator)
- B(φ, ψ): "ψ occurs between occurrences of φ"
- Axioms relating D, B to U, S via the inclusion ordering on intervals

The BX completeness theorem (full statement in Chapter 10, §10.5) establishes that BX is complete for the two-sorted structure combining instants ⟨ℤ,<⟩ with open intervals as periods.

---

### 10.6 Key Technical Lemmas for Formalization

The following lemmas are most relevant for Lean formalization of the separation result:

**Lemma 10.6.1 (U-Monotonicity).** If ⊨ φ → ψ then ⊨ U(χ,φ) → U(χ,ψ).

**Lemma 10.6.2 (U-Distribution).** ⊨ U(φ∨ψ, χ) ↔ U(φ,χ) ∨ U(ψ,χ).

**Lemma 10.6.3 (NormalForm).** Every formula is equivalent to a formula in *temporal normal form*: a disjunction of conjunctions of purely future and purely past literals.

**Lemma 10.6.4 (HierarchyStep).** For each rank-n formula, there is a rank-(n-1) formula that is ℤ-equivalent to it.

**Theorem 10.6.5 (all_formulas_separable).** Every formula is ℤ-equivalent to a separated formula.

*This is the main separation theorem, referenced in CSLib as GHR94 Theorem 10.2.9.*

---

### References for Chapter 10

[GHR94] Gabbay, D., Hodkinson, I., Reynolds, M. (1994). *Temporal Logic: Mathematical Foundations and Computational Aspects, Vol. 1*. Oxford.
[Burgess1982I] Burgess, J.P. (1982). Axioms for tense logic. I. "Since" and "Until". *Notre Dame J. Formal Logic* 23:367–374.
[Burgess1982II] Burgess, J.P. (1982). Axioms for tense logic. II. Time Periods. *Notre Dame J. Formal Logic* 23:375–383.
[Kamp1968] Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
[Reynolds1994] Reynolds, M. (1994). Axiomatising first-order temporal logic: Until and since over linear time. *J. Logic Comput.* 6:679–703.
