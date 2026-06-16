<!-- Source: Burgess, J.P. (1984). Basic Tense Logic. In D. Gabbay and F. Guenthner (eds.), Handbook of Philosophical Logic, Vol. II, pp. 89-133. Reidel. BibKey: Burgess1984 -->

# Basic Tense Logic

**Note**: Scholarly reconstruction from standard references. Section structure follows the original chapter organization.

---

## Basic Tense Logic

JOHN P. BURGESS

In D. Gabbay and F. Guenthner (eds.), *Handbook of Philosophical Logic*, Vol. II: Extensions of Classical Logic, pp. 89–133. D. Reidel Publishing Company, Dordrecht, 1984.

---

### 1. Introduction

Tense logic, as initiated by Arthur Prior, is the study of formal systems incorporating temporal connectives for reasoning about time. The basic tense operators are:

- **F** (Future): "it will at some future time be the case that"
- **P** (Past): "it was at some past time the case that"
- **G** (Always in the future): "it will always be the case that"
- **H** (Always in the past): "it has always been the case that"

These operators satisfy the duality laws:
- G = ¬F¬ (G φ ≡ ¬F¬φ)
- H = ¬P¬ (H φ ≡ ¬P¬φ)

The semantics of tense logic is given by Kripke models over linearly ordered time flows. A *time flow* is a structure ⟨T, <⟩ where T is a nonempty set and < is a binary relation on T. The intended interpretation takes T to be a set of instants and < to be the earlier-than relation.

---

### 2. Kripke Semantics for Tense Logic

**Definition 2.1 (Tense Model).** A tense model is a triple M = ⟨T, <, V⟩ where:
- ⟨T, <⟩ is a time flow
- V : Prop → P(T) is a valuation function

**Definition 2.2 (Satisfaction).** Truth at a point t in model M is defined inductively:
- M, t ⊨ p iff t ∈ V(p)
- M, t ⊨ ¬φ iff M, t ⊭ φ
- M, t ⊨ φ ∧ ψ iff M, t ⊨ φ and M, t ⊨ ψ
- M, t ⊨ Fφ iff ∃s > t: M, s ⊨ φ
- M, t ⊨ Pφ iff ∃s < t: M, s ⊨ φ
- M, t ⊨ Gφ iff ∀s > t: M, s ⊨ φ
- M, t ⊨ Hφ iff ∀s < t: M, s ⊨ φ

A formula φ is *valid on a frame* ⟨T, <⟩ if it is satisfied at every point in every model over that frame. A formula is *valid* if it is valid on every time flow.

---

### 3. The Minimal Tense Logic Kt

The minimal normal tense logic Kt is axiomatized by:

**Propositional axioms**: All propositional tautologies.

**Tense axioms**:
- (K_G) G(φ → ψ) → (Gφ → Gψ)
- (K_H) H(φ → ψ) → (Hφ → Hψ)
- (GP) φ → GPφ  (if p holds now, it will always have been that p held)
- (HF) φ → HFφ  (if p holds now, it has always been that p will hold)

**Rules of inference**:
- Modus Ponens: from φ and φ → ψ, infer ψ
- Necessitation_G: from φ, infer Gφ
- Necessitation_H: from φ, infer Hφ

**Definition 3.1.** A formula φ is a *theorem* of Kt if it is derivable from the axioms by the rules of inference.

The logic Kt is sound and complete with respect to all time flows (frames with no conditions on <).

---

### 4. Extensions of Kt

By adding further axioms, one obtains tense logics for restricted classes of time flows:

**Transitivity (T4 axiom):**
- G_trans: Gφ → GGφ  (corresponds to transitivity of <)
- H_trans: Hφ → HHφ

Adding these gives the tense logic Kt4, complete for flows where < is transitive.

**Linearity axioms:**
- (L) Fφ ∧ Fψ → F(φ ∧ Fψ) ∨ F(φ ∧ ψ) ∨ F(Fφ ∧ ψ)  (trichotomy/linearity)

**Density axioms:**
- (D_F) Fφ → FFφ  (density in the future direction)
- (D_P) Pφ → PPφ  (density in the past direction)

**Discreteness axioms** (for integer time):
- (disc_F) Fφ → F(φ ∧ H(ψ → Pψ))  (there is a next moment)
- (disc_P) Pφ → P(φ ∧ G(ψ → Fψ))

---

### 5. The Until and Since Operators

Kamp (1968) showed that the operators G and H (or equivalently F and P) are insufficient to express all first-order definable properties of time flows. He introduced the *Until* (U) and *Since* (S) operators:

**Definition 5.1.**
- M, t ⊨ U(φ, ψ) iff ∃s > t: M, s ⊨ ψ ∧ ∀r with t < r < s: M, r ⊨ φ
- M, t ⊨ S(φ, ψ) iff ∃s < t: M, s ⊨ ψ ∧ ∀r with s < r < t: M, r ⊨ φ

The reading of U(φ, ψ): "φ holds until ψ" — ψ will hold at some future point, and φ holds at all intervening points.

The operators F and G are definable from U and S:
- Fφ = U(⊤, φ)  (ψ holds at some future point, trivially)
- Pφ = S(⊤, φ)
- Gφ = ¬U(⊤, ¬φ)
- Hφ = ¬S(⊤, ¬φ)

**Theorem 5.2 (Kamp 1968).** Over the reals ⟨ℝ, <⟩ and the rationals ⟨ℚ, <⟩, the operators U and S are expressively complete: every first-order definable property is definable in the Until-Since language.

---

### 6. Axioms for Until-Since Tense Logic

The following axioms extend Kt to the Until-Since language (from Burgess 1982):

**Until axioms:**
- (U1) U(φ, ψ) → Fψ  (if φ U ψ, then ψ will hold)
- (U2) U(φ, ψ) → F(ψ ∧ HU(φ, ψ) ∧ H(¬U(φ, ψ) → PU(φ, ψ)))
- (U3) Gφ → (ψ → U(φ, ψ)) (if φ always holds, any ψ is "φ until ψ")
- (U_expand) U(φ, ψ) ↔ ψ ∨ (φ ∧ FU(φ, ψ))

**Since axioms** (mirror images of U axioms):
- (S1) S(φ, ψ) → Pψ
- (S2) S(φ, ψ) → P(ψ ∧ GS(φ, ψ) ∧ G(¬S(φ, ψ) → FS(φ, ψ)))
- (S3) Hφ → (ψ → S(φ, ψ))
- (S_expand) S(φ, ψ) ↔ ψ ∨ (φ ∧ PS(φ, ψ))

**Completeness theorem (Burgess 1982):** The system with these axioms is sound and complete for:
- Arbitrary linear orders (all linear time flows)
- Dense linear orders without first/last element (rationals, reals)
- Discrete linear orders (integers)

---

### 7. Canonical Model Construction

The completeness proofs use maximal consistent set (MCS) constructions, adapted from standard modal logic:

**Definition 7.1.** A set Γ of formulas is *maximal consistent* (MCS) if:
1. Γ is consistent (does not derive ⊥)
2. For every formula φ, either φ ∈ Γ or ¬φ ∈ Γ

**Definition 7.2 (Canonical Model).** The canonical model M^c = ⟨T^c, <^c, V^c⟩ is defined by:
- T^c = the set of all MCS for the logic
- Γ <^c Δ iff {φ : Hφ ∈ Γ} ⊆ Δ and {φ : Gφ ∈ Δ} ⊆ Γ  (equivalently: Fφ ∈ Γ implies φ ∈ Δ for some appropriate Δ)
- V^c(p) = {Γ : p ∈ Γ}

The key challenge is establishing that MCS in the linear ordering satisfy the required temporal properties (density, discreteness, etc.) corresponding to the target frame class.

**Theorem 7.3 (Truth Lemma).** For all formulas φ and MCS Γ:
M^c, Γ ⊨ φ iff φ ∈ Γ

The proof of the Truth Lemma for Until-Since requires careful treatment of the complex semantic clauses for U and S. The inductive cases for U and S rely on the MCS ordering satisfying the relevant linearization properties.

---

### 8. Important Frame Classes and Their Axioms

| Class | Characteristic Properties | Additional Axioms |
|-------|--------------------------|-------------------|
| Linear orders | Transitive, connected | L (linearity) |
| Dense linear orders | Dense (no adjacency) | D_F, D_P |
| Discrete orders | Has immediate successor/predecessor | disc_F, disc_P |
| ω-orders (Nat) | Well-founded, discrete | ω-induction |
| ℤ-orders (Int) | Bi-infinite discrete | disc_F, disc_P + past-induction |
| ℚ-orders (Rationals) | Dense, no endpoints | D + boundlessness |
| ℝ-orders (Reals) | Complete + dense | Dedekind completeness schemata |

For the integers ℤ: the axiomatization requires adding induction schemata to handle the well-foundedness in both directions (a key result from Burgess 1982, extended in 1984).

---

### 9. Temporal Logic over the Integers

For discrete time flows (like ℤ), the appropriate axioms include successors:

**Definition 9.1 (Successor/Predecessor).** In a discrete linear order:
- "next(t)" denotes the immediate successor of t
- "prev(t)" denotes the immediate predecessor of t

**Circle-F and Circle-P operators** (°F and °P, sometimes called "next" and "previous"):
- M, t ⊨ °F φ iff M, next(t) ⊨ φ
- M, t ⊨ °P φ iff M, prev(t) ⊨ φ

These give rise to the axioms:
- (circ_F) Fφ ↔ °Fφ ∨ F°Fφ
- (circ_P) Pφ ↔ °Pφ ∨ P°Pφ
- (expand_F) Fφ ↔ °Fφ ∨ °FFφ  (unwinding of F via °F)

The integer tense logic with these axioms is complete for ⟨ℤ, <⟩ (Burgess 1984, extending Burgess 1982).

---

### 10. Relationship to First-Order Logic and Expressiveness

**Theorem 10.1 (Kamp's Theorem).** The Until-Since language {U, S} is expressively equivalent to the first-order fragment of monadic second-order logic (i.e., the first-order language with one binary relation <) over dense linear orders without endpoints.

This theorem establishes U-S tense logic as the "right" temporal language for dense flows: adding more operators does not gain further expressiveness over first-order logic.

**Corollary 10.2.** Over ℝ and ℚ, the propositional Until-Since tense logic is decidable (as its models are determined by first-order sentences, and the first-order theory of these structures is decidable).

---

### References

[1] Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
[2] Prior, A.N. (1967). *Past, Present and Future*. Oxford University Press.
[3] Burgess, J.P. (1982). Axioms for tense logic. I. "Since" and "Until". *Notre Dame Journal of Formal Logic* 23(4):367–374.
[4] Burgess, J.P. (1982). Axioms for tense logic. II. Time Periods. *Notre Dame Journal of Formal Logic* 23(4):375–383.
[5] Goldblatt, R. (1980). *Logics of Time and Computation*. CSLI Publications.
