# Teammate B Findings: Weak Completeness + Compactness Route to Strong Completeness

## Investigation Angle

Can strong completeness (`Gamma |= phi -> Gamma |- phi`) be derived from weak completeness (`|= phi -> |- phi`) combined with a compactness theorem, rather than proving it directly via the canonical model / MCS approach?

---

## 1. Current CSLib Infrastructure

### 1.1 What Exists (Weak Completeness)

CSLib already has weak completeness for all three logics:

| Logic | Theorem | File | Semantics |
|-------|---------|------|-----------|
| Classical | `prop_completeness` | `Metalogic/Completeness.lean` | Bivalent valuations (`Tautology phi -> Derivable PropositionalAxiom phi`) |
| Intuitionistic | `int_completeness` | `Metalogic/IntCompleteness.lean` | Kripke (`IValid phi -> Derivable IntPropAxiom phi`) |
| Minimal | `min_completeness` | `Metalogic/MinCompleteness.lean` | Kripke (`MValid phi -> Derivable MinPropAxiom phi`) |

### 1.2 What Does NOT Exist

- **No semantic consequence relation** for propositional logics. There is no `SemanticConsequence` definition analogous to `Cslib.Logic.Temporal.SemanticConsequence`.
- **No set-level derivability** (`Gamma |- phi` where `Gamma` is a set). The existing `Deriv` takes a `List` context; `Derivable` is `Deriv [] phi`.
- **No compactness theorem** anywhere in CSLib.
- **No strong completeness statement** for any propositional logic.

### 1.3 What Would Need to Be Built for the Compactness Route

1. Semantic consequence definitions for all three logics:
   - Classical: `Gamma |=_CL phi` := for all valuations v, if all of Gamma is true under v, then phi is true
   - Intuitionistic: `Gamma |=_IPC phi` := for all Kripke models, for all worlds w, if all of Gamma is forced at w, then phi is forced at w
   - Minimal: `Gamma |=_MPC phi` := same as intuitionistic but with arbitrary upward-closed bot_forces
2. Set-level derivability: `SetDeriv Axioms Gamma phi` := there exists a finite Gamma_0 subset of Gamma such that `Deriv Axioms (Gamma_0.toList) phi`
3. Compactness theorem for each logic
4. The derivation: weak completeness + compactness => strong completeness

---

## 2. The Compactness Route: Theoretical Analysis

### 2.1 Classical Propositional Logic

**Compactness statement**: A set Gamma of formulas is satisfiable (there exists a valuation making all formulas in Gamma true) if and only if every finite subset of Gamma is satisfiable.

**Proof sketch**:
- (=>) Trivial: if v satisfies Gamma, v satisfies every subset.
- (<=) This is the hard direction. Standard proof: Use Lindenbaum's lemma to extend any finitely satisfiable set to an MCS, then construct a satisfying valuation from the MCS via the truth lemma.

**Strong completeness from weak completeness + compactness**:
1. Assume `Gamma |= phi` (semantic consequence).
2. By contrapositive, assume `Gamma |- phi` fails, i.e., no finite `Gamma_0 subset Gamma` has `Gamma_0 |- phi`.
3. Then `Gamma |- not-phi` also fails. But this means `Gamma union {not-phi}` is consistent (every finite subset is consistent).
4. By compactness, `Gamma union {not-phi}` is satisfiable; let v be a model.
5. Then v satisfies all of Gamma but v does not satisfy phi.
6. This contradicts `Gamma |= phi`.

**CRITICAL ISSUE**: Step 3 above requires that for classical logic, consistency (not deriving bot) implies satisfiability. But this is essentially the content of the completeness theorem itself applied to finite contexts. So the "compactness" proof actually requires:
- **Weak completeness** to establish that each finite consistent subset has a model
- **Lindenbaum's lemma** to extend to the infinite case
- **Truth lemma** to construct the model from the MCS

In other words, the compactness proof for propositional logic essentially re-proves completeness.

### 2.2 Intuitionistic Propositional Logic

**Does IPC have the compactness property?** YES, intuitionistic propositional logic is compact with respect to Kripke semantics.

**Proof**: The standard proof uses essentially the same canonical model construction that proves completeness. Given a finitely satisfiable set Gamma:
1. Show Gamma is consistent (each finite subset is consistent, using soundness)
2. Extend to a prime DCCS via Lindenbaum/prime extension
3. Build the canonical Kripke model
4. Apply the truth lemma

**Important subtlety**: The compactness theorem for IPC is equivalent in logical strength to the completeness theorem. One cannot prove compactness independently of completeness without essentially duplicating the same infrastructure.

### 2.3 Minimal Propositional Logic

**Does minimal logic have the compactness property?** YES, minimal logic is compact with respect to minimal Kripke semantics.

The same canonical model construction works. The key difference is that MinTheory (deductively closed sets without consistency) plays the role of worlds instead of DCCS.

---

## 3. Direct (MCS/Canonical Model) Route vs. Compactness Route

### 3.1 The Direct Route

**Proof of strong completeness directly**:
1. Assume `Gamma |= phi`.
2. By contrapositive, assume `Gamma |- phi` fails.
3. Then `Gamma union {neg phi}` is consistent (for classical) or `Gamma` extended by appropriate closure properties (for intuitionistic/minimal) can be extended to appropriate maximal/prime sets.
4. Build canonical model from these sets.
5. Apply truth lemma to get a countermodel.
6. Contradiction with `Gamma |= phi`.

The key insight: **this is almost identical to the weak completeness proof**, except:
- Instead of starting with `{neg phi}` (weak case), we start with `Gamma union {neg phi}` (strong case)
- For Kripke semantics (int/min), canonical worlds come from theories extending `Gamma union {neg phi}` rather than just `{neg phi}`

### 3.2 Comparison Table

| Aspect | Direct (MCS) Route | Compactness Route |
|--------|-------------------|-------------------|
| **New definitions needed** | `SemanticConsequence`, `SetDeriv` | `SemanticConsequence`, `SetDeriv`, `Satisfiable`, `FinitelySatisfiable`, `Compactness` |
| **Proof complexity** | Single proof, directly extends existing weak completeness | Two separate theorems (compactness + derivation), but each reuses existing infrastructure |
| **Reuse of existing code** | Heavy reuse of existing truth lemma, Lindenbaum, MCS infrastructure; proof structure nearly identical to existing weak completeness | Same infrastructure reused, but in two separate theorems |
| **Additional theorems** | None beyond the strong completeness statement | Compactness theorem is independently useful |
| **Modularity** | Less modular -- strong completeness is monolithic | More modular -- compactness and weak completeness are independently useful results |
| **Standard in literature** | The standard approach in CZ (Chagrov-Zakharyaschev), which CSLib follows | More common in model theory textbooks (Chang-Keisler, Enderton) |
| **Lines of code estimate** | ~50-100 lines per logic (adapt existing proof) | ~150-200 lines per logic (compactness + derivation + definitions) |

### 3.3 Critical Observation: They Are Not Independent

The fundamental issue with the compactness route is that **compactness and completeness are equivalent** for propositional logics:

- **Completeness => Compactness**: If every consistent finite set has a model, and consistency is preserved under union of chains (Lindenbaum), then every finitely satisfiable set is satisfiable.
- **Compactness => Completeness**: If every finitely satisfiable set is satisfiable, then any tautology must be derivable (the set of its negation would be unsatisfiable, hence some finite subset is unsatisfiable, hence the formula is a finite consequence of the axioms, hence derivable).

The proof of compactness requires essentially the same infrastructure (Lindenbaum's lemma, truth lemma, canonical model) as the proof of completeness. There is no shortcut.

---

## 4. Feasibility Assessment for Each Logic

### 4.1 Classical (Bivalent Semantics)

**Direct route feasibility**: HIGH. The existing `prop_completeness` proof starting from `{neg phi}` can be generalized to start from `Gamma union {neg phi}`. The key modifications:
1. Define `SemanticConsequence_CL Gamma phi` := `forall v, (forall psi in Gamma, Evaluate v psi) -> Evaluate v phi`
2. Define `SetDeriv PropositionalAxiom Gamma phi` := `exists L : Finset, L.val.toList subset Gamma, Deriv Axioms L.val.toList phi`
3. Prove: if `not (SetDeriv PropositionalAxiom Gamma phi)`, then `Gamma union {neg phi}` is PropSetConsistent
4. Apply existing `prop_lindenbaum` to get MCS M containing `Gamma union {neg phi}`
5. Apply existing `prop_truth_lemma` with M
6. Derive contradiction

This requires about 50-80 lines of new proof beyond definitions.

**Compactness route feasibility**: MEDIUM. Would require defining satisfiability, proving compactness (using the same infrastructure), then deriving strong completeness. About 150-200 lines total.

### 4.2 Intuitionistic (Kripke Semantics)

**Direct route feasibility**: HIGH. The existing `int_completeness` proof can be adapted:
1. Define `SemanticConsequence_IPC Gamma phi` := `forall World [Preorder World] val (v_uc) w, (forall psi in Gamma, IForces val (fun _ => False) w psi) -> IForces val (fun _ => False) w phi`
2. Prove: if `not (SetDeriv IntPropAxiom Gamma phi)`, then `Gamma union {neg phi}` can be extended to a prime IntDCCS
3. Build canonical model using these worlds
4. Apply existing `int_truth_lemma`

**Complication for Kripke semantics**: Strong semantic consequence for Kripke semantics is:
`Gamma |= phi` iff for all models M, for all worlds w, if all of Gamma is forced at w, then phi is forced at w.

The canonical model argument requires that Gamma's elements are all in the "starting" world. This works because the Lindenbaum/prime extension preserves set membership.

**Compactness route feasibility**: MEDIUM-LOW. Kripke compactness is harder to state cleanly and the proof duplicates completeness infrastructure. No efficiency gain.

### 4.3 Minimal (Kripke Semantics with arbitrary bot_forces)

**Direct route feasibility**: HIGH. Same analysis as intuitionistic. The existing `min_completeness` proof extends straightforwardly because:
1. MinTheory closure properties already handle arbitrary context sets
2. Prime extension (`min_prime_exclusion`) already takes arbitrary starting sets
3. Truth lemma is already proven for `MinCanonicalWorld`

**Compactness route feasibility**: MEDIUM-LOW. Same issues as intuitionistic case.

---

## 5. Prior Art in Formalizations

### 5.1 Lean Formalizations

- **Bentzen (2023)**: "Verified completeness in Henkin-style for intuitionistic propositional logic" (arXiv:2310.01916). Proves weak completeness only. Uses canonical model construction with prime theories. Does NOT prove strong completeness or compactness. Source: https://github.com/bbentzen/ipl

- **Borges, Carvalho, Veloso (2024)**: "Intuitionistic Propositional Logic in Lean" (arXiv:2410.23765). Proves completeness for IPL with respect to both Kripke and Heyting algebra semantics. The completeness proof uses canonical models.

### 5.2 Isabelle/HOL Formalizations

- **From and Jacobsen (2025)**: "Isabelle/HOL Locales for Completeness a la Fitting" (ITP 2025, LIPIcs Vol. 352). Proves strong completeness for first-order logic using model existence lemma -> compactness -> strong completeness. Uses about 200 lines for the compactness step. Source: https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.8/LIPIcs.ITP.2025.8.pdf

  **Key insight from this paper**: They use the compactness route for first-order logic where it is natural because the Lowenheim-Skolem theorem and ultraproduct construction provide independent proofs of compactness. For propositional logic, this independence does not exist.

### 5.3 Coq Formalizations

- **Guo & Yu**: "A Comprehensive Formalization of Propositional Logic in Coq". Includes compactness theorem as a corollary of completeness, proving that a set is consistent iff all finite subsets are consistent. This confirms that in propositional logic, compactness follows from completeness rather than being an independent stepping stone.

### 5.4 Mathlib

- Mathlib has `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable` -- the compactness theorem for first-order logic. This uses ultraproducts and is not directly applicable to propositional logic. The propositional case would need its own construction.

---

## 6. Recommendations

### 6.1 Primary Recommendation: Direct (MCS) Route

The direct MCS/canonical model approach is strongly recommended over the compactness route for the following reasons:

1. **Less infrastructure**: No need to define satisfiability, finite satisfiability, or prove compactness as a separate theorem.
2. **Maximal code reuse**: The existing weak completeness proofs already contain 90% of the needed infrastructure. Strong completeness is a straightforward generalization.
3. **Consistency with CSLib style**: The existing modal completeness in CSLib also uses the direct canonical model approach (no compactness detour).
4. **Follows CZ reference**: CSLib's reference text (Chagrov-Zakharyaschev) uses the direct approach.
5. **Equivalent effort**: The compactness proof requires the same Lindenbaum/truth lemma infrastructure, providing no savings.

### 6.2 If Compactness Is Desired Independently

If compactness is desired as a standalone result (for its own mathematical interest), it can be proved as a **corollary** of strong completeness + strong soundness, rather than as a stepping stone to strong completeness:

```
strong_completeness + strong_soundness
=> consistency <-> satisfiability
=> finite consistency <-> finite satisfiability (by definition of consistency)
=> compactness
```

This gives compactness for free once strong completeness is established.

### 6.3 Concrete Steps for Strong Completeness (Direct Route)

For each logic (classical, intuitionistic, minimal):

**Step 1**: Define semantic consequence and set-level derivability (shared definitions):
```lean
-- Semantic consequence for classical logic
def PropSemanticConsequence (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  forall v : Valuation Atom, (forall psi, psi in Gamma -> Evaluate v psi) -> Evaluate v phi

-- Semantic consequence for intuitionistic logic (Kripke)
def ISemanticConsequence (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  forall (World : Type) [Preorder World] (val : World -> Atom -> Prop),
    (forall {w w'} (p : Atom), w <= w' -> val w p -> val w' p) ->
    forall w, (forall psi, psi in Gamma -> IForces val (fun _ => False) w psi) ->
    IForces val (fun _ => False) w phi

-- Set-level derivability
def SetDeriv (Axioms : PL.Proposition Atom -> Prop) (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  exists L : List (PL.Proposition Atom), (forall x, x in L -> x in Gamma) /\ Deriv Axioms L phi
```

**Step 2**: Prove strong completeness for each logic by adapting the existing weak completeness proof. The core modification is:
- Weak: start Lindenbaum from `{neg phi}` (or `{theorems}`)
- Strong: start Lindenbaum from `Gamma union {neg phi}` (or `closure(Gamma)`)

**Step 3**: Prove strong soundness (dual of strong completeness):
```lean
-- If Gamma |- phi, then Gamma |= phi
```
This follows from the existing per-formula soundness by noting that derivations use only finitely many premises.

---

## 7. Specific Theorem Statements

### 7.1 Classical Strong Completeness
```lean
theorem prop_strong_completeness
    {Gamma : Set (PL.Proposition Atom)} {phi : PL.Proposition Atom}
    (h : PropSemanticConsequence Gamma phi) :
    SetDeriv PropositionalAxiom Gamma phi
```

### 7.2 Intuitionistic Strong Completeness
```lean
theorem int_strong_completeness
    {Gamma : Set (PL.Proposition Atom)} {phi : PL.Proposition Atom}
    (h : ISemanticConsequence Gamma phi) :
    SetDeriv IntPropAxiom Gamma phi
```

### 7.3 Minimal Strong Completeness
```lean
theorem min_strong_completeness
    {Gamma : Set (PL.Proposition Atom)} {phi : PL.Proposition Atom}
    (h : MSemanticConsequence Gamma phi) :
    SetDeriv MinPropAxiom Gamma phi
```

### 7.4 Optional: Compactness as Corollary
```lean
theorem prop_compactness
    {Gamma : Set (PL.Proposition Atom)}
    (h : forall L : List (PL.Proposition Atom), (forall x, x in L -> x in Gamma) ->
         exists v, forall x, x in L -> Evaluate v x) :
    exists v, forall x, x in Gamma -> Evaluate v x
```

---

## 8. Key Risks and Blockers

### 8.1 Universe Level Issues
The Kripke semantics definitions (`IValid`, `MValid`) quantify over `Type v` for the world type. Strong completeness proofs that build canonical models at specific universe levels need careful universe management. The existing proofs use `{u, u}` universe constraints (worlds at same level as atoms). This should extend to strong completeness without issues.

### 8.2 Kripke Semantic Consequence and Persistence
For intuitionistic/minimal strong completeness, the semantic consequence must be carefully stated. The standard definition says "for all worlds w where all of Gamma is forced, phi is forced at w." Persistence ensures this is well-behaved, but the proof needs to thread persistence through the canonical model construction.

### 8.3 Set vs. List Context
CSLib's `Deriv` uses `List` contexts while strong completeness involves `Set` contexts. The bridge (`SetDeriv`) must handle the translation. This is standard: "there exists a finite list L drawn from Gamma such that L |- phi."

### 8.4 No New Infrastructure Needed for Compactness Route
If the compactness route were chosen, the proof of compactness itself would require all the same lemmas (Lindenbaum, truth lemma, canonical model) that the direct route uses. There is no independent proof of propositional compactness that avoids this machinery.

---

## Sources

- [Verified completeness in Henkin-style for intuitionistic propositional logic](https://arxiv.org/abs/2310.01916)
- [Intuitionistic Propositional Logic in Lean](https://arxiv.org/abs/2410.23765)
- [Isabelle/HOL Locales for Completeness a la Fitting (ITP 2025)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.8/LIPIcs.ITP.2025.8.pdf)
- [Compactness and Completeness of Propositional Logic (BU CS512)](https://www.cs.bu.edu/faculty/kfoury/UNI-Teaching/CS512/AK_Documents_Past_Semesters/compactness.pdf)
- [A Comprehensive Formalization of Propositional Logic in Coq](https://scispace.com/pdf/a-comprehensive-formalization-of-propositional-logic-in-coq-1nk9t6ea.pdf)
- [Compactness Theorem (IEP)](https://iep.utm.edu/compactness/)
- [Compactness Theorem (Wikipedia)](https://en.wikipedia.org/wiki/Compactness_theorem)
- [Strong Completeness and Limited Canonicity for PDL](https://www.researchgate.net/publication/30498427_Strong_Completeness_and_Limited_Canonicity_for_PDL)
- [Completeness Theory for Propositional Logics (Springer)](https://link.springer.com/book/10.1007/978-3-7643-8518-7)
- [Kripke Semantics (Wikipedia)](https://en.wikipedia.org/wiki/Kripke_semantics)
- [Intuitionistic Logic (SEP)](https://plato.stanford.edu/entries/logic-intuitionistic/)
- [Hypercanonicity, Extensive Canonicity, Canonicity and Strong Completeness of Intermediate Propositional Logics](https://www.researchgate.net/publication/220284319_Hypercanonicity_Extensive_Canonicity_Canonicity_and_Strong_Completeness_of_Intermediate_Propositional_Logics)
