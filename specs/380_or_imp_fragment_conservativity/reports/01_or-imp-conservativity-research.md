# Research Report — Task 380: Conservativity of IPL over IPL⟨∨,→,⊤⟩

## Bottom line

The task-372 Phase-6 NO-GO blocked only the *algebraic* (free-meet-completion) route. It did **not** survey the proof-theoretic infrastructure already in CSLib. That infrastructure changes everything: **CSLib already has a fully cut-eliminated LJ sequent calculus that is provably equivalent to the IntPropAxiom Hilbert system.** This makes a **proof-theoretic conservativity proof (route 1) the clearly most tractable, sorry-free, zero-new-axiom path**, requiring essentially **one new induction lemma** and standard context plumbing — no novel algebra, no free-meet completion, no MacNeille analysis.

The four routes from the handoff rank: **(1) cut-elimination — RECOMMENDED**; (Kripke canonical model — viable backup); (4) Gödel–Tait translation — unnecessary/subsumed; (2) MacNeille — high-risk, likely not sorry-free; (3) Rieger–Nishimura — inapplicable.

---

## What already exists (verified, with exact decls)

**The decisive discovery — LJ with cut elimination (all sorry-free, already in the tree):**
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean`
  - `inductive LJProof : @Sequent Atom → Type u` (11 ctors: `ax botL andL andR orL orR1 orR2 impL impR weakL cut`), lines 86–135.
  - `Sequent` = `Ctx Atom × Proposition Atom`, `Ctx Atom = Finset (Proposition Atom)`, notation `Γ ⊢ C`; requires `[DecidableEq Atom]`.
  - `def LJCutFree : LJProof seq → Prop` (line 193); `def CutFreeLJProof (seq) := { d : LJProof seq // LJCutFree d }` (lines 207–208).
- `Cslib/.../LJ/CutElimination.lean`
  - `theorem LJProof.cutElim (d : LJProof seq) : Nonempty (CutFreeLJProof seq)` (lines 674–709). **Cut elimination is done.**
  - `def CutFreeLJProof.mono (hL : seq.1 ⊆ Γ') ... : CutFreeLJProof (Γ', seq.2)` (line 88) — cut-free weakening.
- `Cslib/.../LJ/Completeness.lean`
  - `theorem hilbert_iff_lj : Deriv IntPropAxiom Γ.toList φ ↔ Nonempty (LJProof (Γ ⊢ φ))` (lines 273–275). **The Hilbert↔LJ bridge.**
  - `theorem lj_iff_ivalid : IValid φ ↔ Nonempty (LJProof (∅ ⊢ φ))` (lines 284–305).
- `Cslib/.../ProofSystemEquivalence.lean`: `iplProofSystemsTfae` (Deriv / ND / LJProof all equivalent).

**OrImp fragment core (shipped by task 372, verified present):**
- `FragmentAxioms.lean:257` `inductive OrImpAxiom` (`implyK implyS orI1 orI2 orE`); `OrImpAxiom.toMinPropAxiom` (284); `mem_implyK/mem_implyS` (295–309); `orImpAxiom_hasDeductionTheorem` (376).
- `FragmentPredicates.lean:73` `Proposition.IsAndBotFree` (atom=true, bot=false, imp=both, and=false, or=both); `imp_isAndBotFree` (189), `or_isAndBotFree` (195).
- `FragmentInstances.lean:120` `HilbertOrImp` instances (InferenceSystem/ModusPonens/HasAxiom*/MinimalHilbert).

**OrImp-applicable derived Hilbert rules** (all parametric in `Axioms` via explicit witnesses, so they accept `OrImpAxiom` constructors), `NaturalDeduction/HilbertDerivedRules.lean`:
- `hilbertOrI1Deriv (h_orI1) : Deriv A Γ A → Deriv A Γ (A∨B)` (389)
- `hilbertOrI2Deriv (h_orI2) : Deriv A Γ B → Deriv A Γ (A∨B)` (398)
- `hilbertOrEDeriv (h_K h_S h_orE) : Deriv Γ (A∨B) → Deriv (A::Γ) C → Deriv (B::Γ) C → Deriv Γ C` (407)
- `hilbertImpIDeriv (h_K h_S) : Deriv (A::Γ) B → Deriv Γ (A→B)` (501) — deduction theorem
- `hilbertImpEDeriv : Deriv Γ (A→B) → Deriv Γ A → Deriv Γ B` (514) — MP
- plus `hilbertCutListDeriv (h_K h_S)` and `hilbertWeakeningDeriv`/`assumption_deriv` (`HilbertLindenbaum.lean`, `FromHilbert.lean:220`).

Note: OrImp supplies every witness these rules need (K, S, orI1, orI2, orE) — and **nothing else is required**, because the fragment has no ∧/⊥ rules.

**Subsumption + bridges to reuse verbatim (from `ConjImpConservative.lean`):** `liftDerivationTree`/`derivable_mono` (59–84), and the `derivableConjImpOfDerivableInt` / `_iff` / `ipl_conservative_over_conjImp` template (104–146).

---

## Recommended route 1 — proof-theoretic (cut elimination)

### Why it works mathematically
IPL is conservative over the {∨,→,⊤} fragment by the **separation property**, which is the subformula property of cut-free LJ. A cut-free LJ proof of an and-bot-free endsequent contains only subformulas of and-bot-free formulas — hence no `∧` or `⊥` ever appears — so it uses only the `ax, orL, orR1, orR2, impL, impR, weakL` rules, each of which is simulated by an OrImp Hilbert step. The proof is *self-validating*: building the translation IS the conservativity proof.

### The single new core lemma (everything else is glue)
```lean
theorem cutFreeLJ_toOrImp {Atom : Type u} [DecidableEq Atom]
    {Γ : Ctx Atom} {C : Proposition Atom}
    (hΓ : ∀ x ∈ Γ, x.IsAndBotFree = true) (hC : C.IsAndBotFree = true)
    (d : CutFreeLJProof (Γ ⊢ C))
    {L : List (Proposition Atom)} (hL : ∀ x ∈ Γ, x ∈ L) :
    Deriv (@OrImpAxiom Atom) L C
```
Generalizing over *any* list `L ⊇ Γ` makes the `insert`/`weakL` cases trivial (just extend `L`) and dissolves the Finset-vs-List friction. Induct on `d.1 : LJProof` carrying `d.2 : LJCutFree d.1`:

- `ax A Γ (A∈Γ)` → `assumption_deriv` (A ∈ L via `hL`).
- `botL` → **vacuous**: `⊥ ∈ Γ` contradicts `hΓ` (`⊥.IsAndBotFree = false`).
- `andL`/`andR` → **vacuous**: `andL` needs `A∧B ∈ Γ` (contra `hΓ`); `andR` has `C = A∧B` (contra `hC`).
- `orR1`/`orR2` → `hC` gives the disjunct and-bot-free; IH then `hilbertOrI1Deriv`/`hilbertOrI2Deriv` (OrImp `orI1`/`orI2`).
- `orL A B (A∨B∈Γ) ...` → `hΓ` gives A,B and-bot-free; `assumption_deriv` for `A∨B`, two IHs (with `L`:=`A::L`, `B::L`), then `hilbertOrEDeriv` (OrImp `orE`,`implyK`,`implyS`).
- `impL A B (A→B∈Γ) (Γ⊢A) (B,Γ⊢C)` → `hΓ` gives A,B and-bot-free; `hilbertImpEDeriv` on the assumption `A→B` + IH(A) yields `Deriv L B`; combine with IH(C, `L:=B::L`) via `hilbertCutListDeriv`.
- `impR A B (A,Γ⊢B)` → `hC` gives A,B and-bot-free; IH (`L:=A::L`) then `hilbertImpIDeriv` (deduction theorem).
- `weakL A (Γ⊢C)` → IH with same `L` (membership monotone).
- `cut` → **vacuous**: discharged by `d.2 : LJCutFree` (cut case is `False`).

### Assembling the public theorem
```lean
theorem hilbertIplConservativeOverOrImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hABF : φ.IsAndBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@OrImpAxiom Atom) φ := by
  classical                                  -- letI : DecidableEq Atom := Classical.decEq _
  obtain ⟨d⟩ := hilbert_iff_lj.mp h          -- Derivable = Deriv [] φ = Deriv (∅:Ctx).toList φ
  obtain ⟨dcf⟩ := d.cutElim
  exact ⟨ (cutFreeLJ_toOrImp (by simp) hABF dcf (L:=[]) (by simp)) ⟩
```
(`Derivable A φ` is `Deriv A [] φ`; `(∅ : Ctx).toList = []`. Final call: `Γ = ∅`, `L = []`, `hΓ` vacuous.) Then mirror `ConjImpConservative.lean` for the rest:
- `derivableOrImpOfDerivableInt := derivable_mono (fun _ h => h.toMinPropAxiom.toIntPropAxiom)`
- `hilbertIplConservativeOverOrImp_iff` (⟨forward, subsumption⟩)
- ND corollary `ipl_conservative_over_orImp` via `derivableInIplIffDerivableInt.mp`.

### Critical caveat — and its clean fix
LJ requires `[DecidableEq Atom]`; the conjunctive analogue `hilbertIplConservativeOverConjImp` has **no** such hypothesis. To keep the OrImp signature parallel, open `classical`/`letI := Classical.decEq Atom` *inside the proof body* — legitimate because `Derivable` is a `Prop`, and the file is already `noncomputable`. This yields a public statement with **no `DecidableEq` hypothesis**, matching the chain's style. Flag this for the planner as the one deliberate technique.

### Files
- **New**: `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` (or under `Metalogic/` — it is proof-theoretic, not algebraic) holding `cutFreeLJ_toOrImp`, `hilbertIplConservativeOverOrImp`, subsumption, `_iff`, ND corollary. Imports: the LJ `CutElimination`/`Completeness` modules + `FragmentAxioms` + `HilbertDerivedRules` + `liftDerivationTree`'s home.
- **Modify**: `ConservativeChain.lean` — add the new vertex `IPL⟨∨,→,⊤⟩ ⊂ IPL` (condition `IsAndBotFree`), plus `orImpAxiom_iff_chain`, mirroring the existing `conjImpAxiom_iff_chain` block.
- **Modify**: `Cslib.lean` (`lake exe mk_all --module`).

### Risks (all bookkeeping, none mathematical)
1. **Finset `Ctx` ↔ List `Deriv` plumbing** — the only real cost. Mitigated by the `L ⊇ Γ` generalization above; `insert A Γ ⊆`-handling reduces to `A :: L`. Recommend a couple of tiny `Ctx.toList`/membership helper lemmas.
2. **Import layering** — confirm the LJ modules don't (transitively) import `ConservativeChain`/`Semantics.Algebra` (they shouldn't; they sit on ProofSystem + Kripke). If a cycle appears, place `OrImpConservative.lean` under `Metalogic/` and have `ConservativeChain` import *it*.
3. **`Derivable`/`Deriv [] φ` defeq + `(∅:Ctx).toList = []`** — verify with one `simp`/`rfl` probe before committing.

---

## Routes assessed and not recommended

- **Route 4 (Gödel–Tait OrImp→ConjImp translation):** there is no faithful definitional translation of ∨ into {∧,→,⊤} in IPL (the fragments are genuinely distinct), so a literal syntactic translation cannot exist. Any honest "translation" reduces to a proof-theoretic argument — which route 1 already is, far more directly. **Subsumed; do not pursue separately.**
- **Route 2 (MacNeille completion):** Mathlib has `Mathlib/Order/Completion.lean`, but the Dedekind–MacNeille completion of a Heyting algebra need not be Heyting (Bezhanishvili–Harding), and `⇨`-preservation on a {∨,→,⊤}-subreduct is precisely the open/false point. **High risk of an unbridgeable gap; reject.**
- **Route 3 (Rieger–Nishimura):** describes only the *one-generator* free Heyting algebra; gives nothing for general multi-variable conservativity. **Inapplicable; reject.**
- **Algebraic free-meet completion (the 372 NO-GO):** confirmed dead via `UpperSet.Ici` not preserving `⇨`. Note `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` exists but builds the *meet* completion of a {→,⊤} Hilbert algebra (adds ∧, preserves `⇨` — used for ImpConservative); it is **not** a join-completion and does not help here.

## Backup route K (Kripke canonical model)
Fully viable and also obstruction-free: CSLib has IPL Kripke soundness (`int_soundness_derivable : Derivable IntPropAxiom φ → IValid φ`), forcing `IForces`, and a canonical-model template (`IntCanonicalWorld`/`int_truth_lemma` over prime down-closed sets; `MinCanonicalWorld`/`MinPrimeTheory`). Conservativity = IPL soundness → and-bot-free forcing → membership in every prime OrImp-theory → `Derivable OrImpAxiom`. **Why it loses to route 1:** the existing prime-theory machinery is hard-coded to `IntPropAxiom`/`MinPropAxiom` (not parametric over fragment axiom sets), so route K must rebuild a fragment Lindenbaum/disjunction-property construction from scratch — substantially more new code than route 1's single induction lemma, which instead reuses the already-proven `cutElim`.

---

## Key reference files
- `Cslib/Logics/Propositional/SequentCalculus/LJ/{Basic,CutElimination,Completeness}.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/{ConjImpConservative,ImpConservative,ConservativeChain,HilbertLindenbaum}.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`, `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean`
- 372 artifacts: `specs/372_or_imp_disjunctive_implicational_fragment/{plans/01,reports/01,.orchestrator-handoff.json}`

## Recommendation for the planner
Turn route 1 into a short phased plan (≈3 phases): (P1) context-plumbing helpers (`Ctx.toList`/membership) + import-layering check + `Derivable`/`Deriv [] φ` defeq probe; (P2) the `cutFreeLJ_toOrImp` induction lemma; (P3) public theorem `hilbertIplConservativeOverOrImp` + subsumption + `_iff` + ND corollary + `ConservativeChain.lean` wiring + `Cslib.lean` + full CI. Call out the `classical`/`Classical.decEq` DecidableEq-elimination technique and the import-layering decision as the two things to validate early.
