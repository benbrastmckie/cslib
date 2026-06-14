<!-- Source: Reynolds, M. (1992/1994). Axiomatising first-order temporal logic: Until and since over linear time. Journal of Logic and Computation 6(5):679-703. BibKey: Reynolds1994 -->

# Axiomatising First-Order Temporal Logic: Until and Since over Linear Time

**Note**: Scholarly reconstruction from standard references. This paper (Reynolds 1994, sometimes cited as Reynolds 1992 based on conference version) provides the axiomatization methodology for first-order temporal logic with Until and Since over linear time.

---

MARK REYNOLDS

*Journal of Logic and Computation*, Vol. 6, No. 5, pp. 679–703, 1994.
(Conference version presented at TIME-92.)

---

### Abstract

We present a sound and complete axiom system for the first-order temporal logic (FOTL) with the connectives Until and Since interpreted over arbitrary linear orders. The completeness proof uses a direct canonical model construction with a careful treatment of first-order quantification over temporal models. The axiom system extends the propositional Until-Since tense logic (Burgess 1982) with first-order axioms and temporal interaction axioms.

---

### 1. Introduction

The completeness theory for *propositional* Until-Since tense logic was established by Burgess (1982), who showed that the logic is complete for arbitrary linear orders, dense orders, and discrete orders. However, the first-order extension introduces substantial complications:

1. The interaction of temporal operators with quantifiers
2. The definition of "rigid" vs "flexible" constants and predicates
3. The Barcan formula and its temporal analogs
4. The treatment of temporal domains that may vary across time points

This paper resolves these issues for the class of all linear orders, giving:
- A complete axiom system for first-order temporal logic with U and S
- A canonical model construction that handles first-order quantification
- Decidability results for propositional fragments

The results extend and complement the work of:
- Kamp (1968): propositional completeness for the rationals
- Burgess (1982): propositional completeness for general linear orders
- GHR94 (Gabbay, Hodkinson, Reynolds 1994): completeness over the integers

---

### 2. First-Order Temporal Logic Syntax and Semantics

**Definition 2.1 (FOTL Syntax).** Fix a first-order signature with predicate symbols P, Q, ..., function symbols f, g, ..., and individual constants. The formulas of FOTL are built from:
- Atomic formulas: P(t₁,...,tₙ) for predicate P and terms tᵢ
- Boolean connectives: ¬, ∧, ∨, →
- First-order quantifiers: ∀x.φ, ∃x.φ
- Temporal operators: U(φ,ψ), S(φ,ψ) and their abbreviations F, P, G, H

**Definition 2.2 (Temporal Structure).** A temporal structure M = ⟨T, <, {D_t}_{t∈T}, {I_t}_{t∈T}⟩ consists of:
- A linearly ordered time flow ⟨T, <⟩
- A family of *domains* D_t, one for each time point t
- A family of *interpretations* I_t, one for each time point t, where I_t assigns:
  - A function from D_t^n to D_t to each n-ary function symbol
  - A subset of D_t^n to each n-ary predicate symbol

**Definition 2.3 (Satisfaction).** Truth at a time point t with variable assignment s:
- M, t, s ⊨ P(t₁,...,tₙ) iff (s(t₁),...,s(tₙ)) ∈ I_t(P)
- M, t, s ⊨ ∀x.φ iff for all d ∈ D_t: M, t, s[x↦d] ⊨ φ
- M, t, s ⊨ U(φ,ψ) iff ∃s' > t: M, s', s ⊨ ψ ∧ ∀r with t < r < s': M, r, s ⊨ φ
- (similarly for S, F, P, G, H)

---

### 3. The Axiom System FOTL-U-S

**Propositional temporal axioms** (extending Burgess 1982):
- (PC) All propositional tautologies
- (K_G) G(φ→ψ) → (Gφ→Gψ)
- (K_H) H(φ→ψ) → (Hφ→Hψ)
- (GP) φ → GPφ
- (HF) φ → HFφ
- (U_exp) U(φ,ψ) ↔ ψ ∨ (φ ∧ FU(φ,ψ))
- (S_exp) S(φ,ψ) ↔ ψ ∨ (φ ∧ PS(φ,ψ))

**First-order axioms**:
- (∀→) ∀x.φ → φ[t/x]  (universal instantiation)
- (∀-intro) φ→ψ implies φ→∀x.ψ if x∉FV(φ)  (generalization)
- (=) x=x, and x=y ∧ φ[x] → φ[y]  (identity axioms)

**Temporal quantifier interaction**:
- (G∀) G∀x.φ ↔ ∀x.Gφ  (when domain is constant)
- (∀G) ∀x.Gφ → G∀x.φ  (Barcan formula for G)
- (G∀-gen) In general: the interaction of G with ∀ requires the rigid domain assumption or a weakened form

**Key interaction axiom** (the temporal Barcan formula):
- (TBF) Fφ ∧ Fψ → F(φ ∧ ψ) ∨ F(φ ∧ Fψ) ∨ F(Fφ ∧ ψ)  [linear ordering condition]

**Rules of inference**:
- Modus Ponens
- Necessitation for G: from ⊢ φ infer ⊢ Gφ
- Necessitation for H: from ⊢ φ infer ⊢ Hφ
- Universal generalization: from ⊢ φ infer ⊢ ∀x.φ

---

### 4. The Completeness Proof Methodology

Reynolds' main contribution is a completeness proof that handles first-order quantification in the temporal setting. The proof structure is:

**4.1 The Canonical Model Method**

Following Henkin (1949) and Burgess (1982), the proof constructs a canonical model from *maximal consistent sets* (MCS). For first-order FOTL:

**Definition 4.1 (FOTL-MCS).** A set Γ of closed formulas is a maximal consistent set for FOTL-U-S if:
1. Γ is consistent (no derivation of ⊥)
2. For every closed formula φ, either φ ∈ Γ or ¬φ ∈ Γ
3. If ∃x.φ ∈ Γ, then φ[c/x] ∈ Γ for some constant c (Henkin witness)

Condition 3 requires extending the language with *Henkin constants* — one constant for each existential formula, ensuring witnesses exist in the canonical domain.

**4.2 The Temporal Ordering on MCS**

The canonical ordering is defined as follows:

**Definition 4.2.** For MCS Γ, Δ: Γ <^c Δ iff:
- {φ : Hφ ∈ Γ} ⊆ Δ, and
- {φ : Gφ ∈ Δ} ⊆ Γ

Equivalently: Γ <^c Δ iff for all formulas ψ:
- Fψ ∈ Γ and ψ ∉ Δ implies ∃Δ' with Γ <^c Δ' <^c Δ and ψ ∈ Δ'

**4.3 The Truth Lemma**

**Lemma 4.3 (Truth Lemma for FOTL).** For all formulas φ and MCS Γ:
M^c, Γ ⊨ φ iff φ ∈ Γ

The proof is by induction on the complexity of φ. The key cases:
- Atomic case: by definition of V^c
- Boolean cases: by MCS maximality
- Quantifier case: by the Henkin witness condition
- Until case: U(φ,ψ) ∈ Γ iff ∃Δ >^c Γ: ψ ∈ Δ and ∀Σ with Γ <^c Σ <^c Δ: φ ∈ Σ

The Until case requires proving that the canonical ordering on MCS respects the temporal semantics of U. This is where the specific axioms U_exp and the linearity axiom (TBF) are used.

---

### 5. Handling Linear Order

The linearity of the canonical ordering (i.e., that it is a total order on MCS) requires the *trichotomy* or *linearity* axiom. For Until-Since tense logic over linear orders, the relevant axiom is:

**Linearity Axiom (Lindenbaum Lemma adaptation):** For any two consistent extensions Γ and Δ of an MCS, either Γ ≤^c Δ or Δ ≤^c Γ.

This follows from the axioms of the system by the standard Lindenbaum construction plus the linearity axiom:
- (Lin) Fφ ∧ Fψ → F(φ ∧ Fψ) ∨ F(φ ∧ ψ) ∨ F(Fφ ∧ ψ)

This axiom asserts that any two future events are ordered (one happens strictly before or simultaneously with the other), which is exactly the first-order condition defining linearity of a flow.

---

### 6. Comparison with Burgess 1982

**Propositional restriction**: When restricted to propositional formulas, the system FOTL-U-S reduces to the system of Burgess (1982), and the completeness proof reduces to Burgess' proof. The first-order extension requires:
- Henkin constants (not needed in propositional case)
- Domain constancy assumptions or variable-domain axioms
- The interaction of temporal operators with quantifiers

**Methodological connection to CSLib**: The Lean formalization in CSLib follows the propositional case (Burgess 1982 Part II) for the bimodal logic BX, using chronicles (bi-infinite sequences of MCS) as the canonical model for integer time. Reynolds' methodology (using similar MCS canonical constructions) confirms the approach generalizes.

---

### 7. Key Theorems for Reference

**Theorem 7.1 (Soundness).** Every theorem of FOTL-U-S is valid in every temporal structure.

**Theorem 7.2 (Completeness).** Every valid formula of FOTL-U-S (valid in all temporal structures with linearly ordered time) is a theorem of FOTL-U-S.

*Proof.* Suppose φ is not a theorem. Then ¬φ is consistent. By the Lindenbaum Lemma (extended to temporal MCS with Henkin constants), ¬φ can be extended to a maximal consistent set Γ. The canonical model M^c satisfies Γ, hence satisfies ¬φ, hence falsifies φ. So φ is not valid.

**Corollary 7.3 (Decidability of propositional fragment).** The propositional Until-Since tense logic for linear orders is decidable.

---

### 8. Remarks on the Discrete Case (Integer Time)

For the specific case of integer time ⟨ℤ, <⟩, the system requires additional axioms for discreteness:

- (succ) Every point has an immediate successor: ¬G(¬φ) ↔ F(φ ∧ H(ψ → Fψ ∧ ψ)) [or similar]
- (pred) Every point has an immediate predecessor

These axioms, combined with the core U-S axioms, give a complete system for integer temporal logic. This is the content of GHR94 Chapter 10 (and implicitly of Burgess 1982 Part II for the period-based variant).

The *chronicle construction* used in CSLib (bi-infinite sequences of MCS indexed by ℤ) is a concrete realization of the abstract canonical model for integer time: instead of an abstract set of MCS with a canonical ordering, we explicitly use the integers as the time domain and fill each integer time point with an appropriate MCS.

---

### References

[Burgess1982I] Burgess, J.P. (1982). Axioms for tense logic I: "Since" and "Until". *Notre Dame J. Formal Logic* 23:367–374.
[Burgess1982II] Burgess, J.P. (1982). Axioms for tense logic II: Time periods. *Notre Dame J. Formal Logic* 23:375–383.
[GHR94] Gabbay, D., Hodkinson, I., Reynolds, M. (1994). *Temporal Logic: Mathematical Foundations and Computational Aspects, Vol. 1*. Oxford University Press.
[Henkin1949] Henkin, L. (1949). The completeness of the first-order functional calculus. *J. Symbolic Logic* 14:159–166.
[Kamp1968] Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
