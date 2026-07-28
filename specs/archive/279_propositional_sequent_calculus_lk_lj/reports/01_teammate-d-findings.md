# Task 279: Horizons Research — Strategic Alignment and Long-Term Direction

**Teammate**: D (HORIZONS — long-term alignment and strategic direction)
**Date**: 2026-06-23
**Task**: Propositional sequent calculus LK/LJ with cut elimination

---

## Executive Summary

Task 279 is a strategic linchpin in CSLib's logic library. It sits at the intersection of three
ongoing development threads — the proof-system triad (Hilbert + ND + SC), the decidability
pipeline, and the eventual extension of proof theory beyond propositional logic. The task has
four direct dependents (291, 292, 293, and modal tableau work), and its sequent calculus pattern
is the most natural substrate for lifting proof theory to modal, temporal, and bimodal logics.
Delivering LK/LJ with cut elimination would position CSLib as the first Lean 4 library with a
complete propositional sequent calculus formalization.

---

## 1. Roadmap Alignment

### 1.1 Immediate Position in the Task Graph

The task roadmap (`specs/ROADMAP.md`) describes porting BimodalLogic to CSLib across five levels:
Foundations, Propositional, Modal, Temporal, Bimodal. Task 279 lives at the Propositional level
and has two roles:

**Completing the proof-system triad.** CSLib already has:
- Hilbert-style derivation trees (`Cslib.Logics.Propositional.ProofSystem.Derivation`)
- Natural deduction (`Cslib.Logics.Propositional.NaturalDeduction.Basic`)
- An existing ND-Hilbert equivalence (`hilbert_iff_nd_*` from task 266, now complete)

Task 279 delivers the third pillar: sequent calculus. Task 291 (three-way equivalence) becomes a
one-line composition once 279 is done. This is the clearest near-term payoff.

**Enabling decidability via proof search.** Task 292 (IPL decidability via cut-free LJ) is a
direct dependent. Cut-free LJ proof search terminates because all formulas in a cut-free derivation
are subformulas of the root sequent. This subformula property is the standard Gentzen route to
propositional decidability — distinct from and complementary to the tableau route (task 298) and
the algebraic route (task 289, already completed).

### 1.2 Relation to the Tableau Pipeline (Tasks 296–301)

Task 296 (tableau architecture, now EXPANDED into 297–301) explicitly asks how tableau completeness
relates to the planned sequent calculus. Task 297 (foundations tableau infrastructure) is now
COMPLETED, and task 298 (propositional tableau decidability) is IMPLEMENTING. The two pipelines
— sequent calculus (279) and tableau (297–298) — are parallel routes to the same decidability
result, and both are currently in flight. 

**Key architectural relationship.** Sequent calculus completeness (LK/LJ) can be proved via
cut elimination + the subformula property, which independently verifies what the tableau approach
achieves via branch closure. The existence of both formalizations would give CSLib a rare dual
certification of propositional decidability: the `Decidable` instance from task 289 (algebraic),
the tableau decision procedure from task 298, and the cut-free proof search from task 292.

**Important cross-reference:** Task 296's description explicitly asked how SC completeness
(task 279) and MCS-based completeness relate. CSLib's existing completeness proofs are all
MCS-based (canonical model construction). A sequent calculus completeness proof can either:
(a) pass through MCS completeness as a corollary, or (b) give an independent cut-elimination
proof that implies completeness directly. Option (b) is strategically more valuable as an
independent verification.

### 1.3 What Is Still in the Roadmap

The roadmap `## Remaining` section lists completeness tasks for Bimodal and Temporal logics
at the semantic/MCS level. Task 279 does not directly unlock these, but its pattern does:
once a sequent calculus framework is in place for propositional logic, the question of "can
we lift this to modal/temporal?" becomes tractable.

---

## 2. Future Opportunities — Lifting to Modal and Beyond

### 2.1 Modal Sequent Calculi (G3K, G3S4, G3S5)

The most natural generalization of LK to modal logic is the Gentzen-Schütte family of display
calculi or the Fitting-style sequent calculi for modal logics. For the modal logics already
in CSLib (K, S4, S5), the standard labeled sequent calculus G3K adds two rules for box:

```
   Γ ⊢ Δ, A
────────────────── (□R)         A, Γ ⊢ Δ
   Γ ⊢ Δ, □A                ────────────── (□L)
                              □A, Γ ⊢ Δ
```

with additional conditions encoding the frame axioms for S4/S5. This is a direct extension of
LK. If the propositional LK definition uses typeclass parameters over `HasImp`, `HasAnd`, `HasOr`,
`HasBot`, then the modal extension only needs `HasBox` additional rules, and the structural lemmas
(weakening, contraction, exchange) lift without change.

**CSLib feasibility:** The `Cslib.Logic.Modal.Proposition` type already has `HasBox` and
`HasImp` instances. Modal formulas have DecidableEq (needed for Finset-based contexts). The
existing `InferenceSystem` typeclass and `DerivableIn` infrastructure would serve as the
derivability wrapper for a modal sequent calculus just as it does for ND and Hilbert.

### 2.2 Temporal and Bimodal Sequent Calculi

Temporal logic sequent calculi are substantially harder than modal ones because temporal
operators (Until, Since) require cyclic or loop rules. Standard finite sequent calculi do
not terminate for LTL; the fixed-point unfolding of Until generates infinite branches.
Options include:

- **Display calculi** (Belnap 1982): general but complex, not standard in Lean proofs
- **Hypersequent calculi** (Avron 1996): for some temporal logics
- **Cyclic proofs** (Brotherston 2006): handle recursive fixed-point operators

For CSLib's Temporal and Bimodal logics, the MCS-based completeness approach (already
in `Logics/Temporal/Metalogic/` and `Logics/Bimodal/Metalogic/`) is better suited than
sequent calculi. The tableau approach (tasks 299–301) is the more natural extension for
temporal logics.

**Recommendation:** Do not plan temporal/bimodal sequent calculi at this stage. The
temporal tableau (task 301) and MCS completeness are the right tools. Sequent calculi
for temporal/bimodal would require cyclic proof infrastructure that is far out of scope.

### 2.3 Intuitionistic Modal Logic (Possibility)

One strategically valuable extension: once LJ (intuitionistic sequent calculus) exists,
CSLib could support intuitionistic modal logics (IK, IS4) via a sequent calculus extension.
The `Basic.lean` for Modal notes that "non-classical modal logics require a separate `HasDia`
typeclass." Task 279 delivering LJ lays the foundation for this — LJ gives the underlying
intuitionistic logic, and adding modal rules on top gives IK.

---

## 3. Reuse Opportunities — Shared Infrastructure

### 3.1 What Should Live in Foundations/Logic/

**Sequent type.** A `Sequent F` type (left context × right formula, or left Finset × right Finset
for two-sided calculi) parameterized over a formula type `F` could live in
`Cslib.Foundations.Logic.SequentCalculus`. This parallels how CLL defines `abbrev Sequent Atom`
as a multiset — but for LK the right sequent structure is `Finset F × Finset F`.

**Structural rule lemmas.** Weakening, contraction, and exchange lemmas proved for a generic
`Sequent F` under generic connectivity assumptions could be reused by all sequent calculi.
These depend only on `DecidableEq F` and the Finset structure, not on the specific logic.

**Cut elimination theorem template.** The Hauptsatz argument follows a standard pattern:
induction on cut-rank and derivation height. A typeclass-parameterized version could express
this generically if the formula type carries a `cutRank` function. However, the proof of
cut elimination for modal logics is substantially different from propositional logic, so
extracting a generic version is premature at the propositional stage.

**Recommendation:** For task 279, define `SequentCalculus` infrastructure in
`Cslib/Logics/Propositional/SequentCalculus/` using the existing Foundations/ typeclasses
(`HasImp`, `HasAnd`, `HasOr`, `HasBot`). Extract shared definitions to Foundations only in
a follow-up task once the modal version is being built and shared patterns emerge.

### 3.2 Relation to the CLL Template

CLL (`Cslib/Logics/LinearLogic/CLL/Basic.lean`) uses `Multiset`-based sequents (one-sided:
a single list of propositions representing all conclusions). LK uses two-sided Finset-based
sequents (`Γ ⊢ Δ` as `Finset × Finset`). These are different data structures:

- CLL: `abbrev Sequent Atom := Multiset (Proposition Atom)` — one-sided, multiset
- LK: should be `Finset (Proposition Atom) × Finset (Proposition Atom)` — two-sided, Finset

The `InferenceSystem` typeclass can accommodate both: CLL uses `HasInferenceSystem (Sequent Atom)`,
and LK can use a new tag type `LKDerivation` or similar. The key reuse from CLL is the
structural pattern: use `InferenceSystem` as the derivability wrapper, define the sequent
rules as an inductive type, and provide a `DerivableIn` abbreviation.

**Note:** The task description says to follow the CLL template for structure, not data types.
Use Finset-based contexts as specified — the CLL multiset approach is specific to the linear
logic regime (structural rules are restricted, so multiplicities matter).

### 3.3 Relation to the NaturalDeduction Module

The existing `Theory.Derivation` type (ND) uses `Finset`-based contexts. This is an asset for
the bridge proofs (`nd_iff_lk`): context conversion between the two systems is straightforward
when both use Finset. The Hilbert-ND bridge in `NaturalDeduction/Equivalence.lean` uses
`List.toFinset` / `Finset.toList` for context conversion — the LK-ND bridge should reuse the
same approach.

---

## 4. Decidability Connection

### 4.1 Cut Elimination as a Decidability Engine

The standard proof-theoretic route to propositional decidability is:

1. **Cut elimination**: Every LK/LJ derivation has a cut-free proof (Hauptsatz).
2. **Subformula property**: All formulas in a cut-free proof are subformulas of the root sequent.
3. **Proof search terminates**: The search space is bounded by the finite set of subformulas.
4. **Decision procedure**: A backward-search algorithm over cut-free LJ is a decision procedure.

This is exactly what task 292 formalizes after task 279. The chain `279 -> 292 -> Decidable (LJDerivable)` is a complete proof-theoretic decidability argument, independent of the
algebraic argument (task 289) and the tableau argument (task 298).

**CSLib positioning:** Having three independent decidability proofs (algebraic, tableau,
cut-free proof search) for IPL would be exceptional — most Lean 4 libraries have one. This
triple redundancy is not wasteful; it demonstrates the robustness of CSLib's infrastructure
and provides verification that the three approaches agree.

### 4.2 First LK/LJ in Lean 4

The task description notes this would be "the first LK/LJ formalization in Lean 4." This is
a significant positioning claim. Checking what exists:
- Mathlib has natural deduction (`Propositional.Derivation`-type structures) but not LK/LJ
- Lean 4 ecosystem: some course materials exist, but no library-quality LK/LJ with cut elimination

If the claim is accurate, task 279 would be a showcase CSLib contribution suitable for
announcement at a Lean/Mathlib conference or workshop. The key deliverables to highlight would
be: cut elimination (Hauptsatz), the three-way equivalence (task 291), and the decidability
instance (task 292).

---

## 5. Creative Approaches — Alternative Architectures

### 5.1 Parameterized Calculus Over Structural Rules

Instead of defining LK and LJ as separate inductive types, consider a single parameterized
sequent calculus type with a typeclass parameter controlling which structural rules are present:

```lean
class SequentSystem (S : Type*) (F : Type*) extends InferenceSystem S (Finset F × Finset F) where
  hasContraction : Bool  -- absent in linear logic
  hasWeakening : Bool    -- absent in linear logic
  hasRightMulticonclusion : Bool  -- absent in LJ (single right formula)
```

This could unify LK (classical, multi-conclusion right), LJ (intuitionistic, single right
formula), and CLL (linear, multiset, no structural rules). **However**, this is premature
abstraction: the exact interface needed will only be clear after implementing both LK and LJ.

**Recommendation for task 279:** Implement LK and LJ as separate inductive types. If they
share many rules, factor the shared rules into a common base inductive type and let LK/LJ
extend via an embedding. Abstract the structural rule typeclass only after both are complete.

### 5.2 Two-Sided vs. One-Sided LK

Classical LK can be presented one-sided (all formulas on right, with duals for left formulas)
or two-sided (explicit left/right contexts). The CLL template is one-sided; the standard
Gentzen LK is two-sided. For propositional logic, the two presentations are equivalent, but:

- **Two-sided** is easier to understand and closer to the Gentzen 1935 source
- **One-sided** aligns with CLL and would make the LK-CLL relationship more direct
- **Two-sided with Finset** is what the task description specifies

The task description is explicit: "Finset-based contexts on both sides." Follow this. The
two-sided presentation is also more natural for the LJ restriction (single right formula).

### 5.3 Finset vs. List for Contexts

The ND system uses `Finset` (implicit exchange and contraction). LK also uses `Finset` per
the task description. The CLL uses `Multiset` (exchange only, no contraction). Using `Finset`
on both sides of LK:

- Eliminates the need to prove exchange and contraction separately (they are definitionally
  trivial: `{φ, ψ} = {ψ, φ}`)
- Makes the connection to ND (also Finset-based) direct
- Requires `DecidableEq Atom` for Finset membership, which `Proposition Atom` already has

**Confirmed choice:** Use `Finset (Proposition Atom)` for both left and right contexts in LK.
For LJ, the right context is a single formula (or `Option (Proposition Atom)`), not a Finset.

### 5.4 Cut Elimination Proof Strategy

There are two main strategies for cut elimination in Lean:

**Strategy A: Syntactic cut elimination (Gentzen's original).**
Induction on `(cutRank, leftHeight + rightHeight)` with the sub-case analysis on the structure
of the cut formula and the last rules applied. This is faithful to the literature but has
many cases (10 right rules × 10 left rules for propositional LK = up to 100 sub-cases).

**Strategy B: Semantic completeness shortcut.**
Prove soundness (LK ↔ tautology) and completeness independently (e.g., via Hilbert completeness
already in CSLib), then conclude that cut-free LK is complete without giving a constructive
cut-elimination transform. This is less informative but may be feasible with CSLib's existing
algebraic completeness.

**Recommendation:** Use Strategy A. The Hauptsatz as a constructive transform is the main
point of the task and what enables the subformula property and decidability downstream (task 292).
A semantic shortcut would not give the subformula property. The case analysis is large but
mechanical — `decide` or `omega` may close many arithmetic sub-goals once the induction is set up.

---

## 6. Adjacent Opportunities Unlocked by LK/LJ

Once task 279 delivers a working LK/LJ with cut elimination, the following become tractable:

### 6.1 Immediate (Tasks Already in the Task Graph)

| Task | Description | Dependency |
|------|-------------|------------|
| 291 | Three-way equivalence (Hilbert + ND + SC) | Composition of existing bridges |
| 292 | IPL decidability via cut-free proof search | Subformula property from cut elimination |
| 293 | Curry-Howard (depends on ND normalization, 290) | Independent but benefits from SC infrastructure |

### 6.2 Near-Term (Should Be Added to Task List)

**Herbrand's theorem.** For classical propositional logic, Herbrand's theorem is essentially
the subformula property of cut-free LK restricted to the quantifier-free fragment. While
CSLib currently focuses on propositional logic (no quantifiers), the pattern of Herbrand's
theorem is worth noting as the natural extension when first-order logic is added.

**Craig interpolation.** For propositional logic, Craig interpolation has a standard proof
via cut elimination: given a proof of `A ∧ B → C`, the cut-free proof gives an interpolant
by analyzing the formulas occurring in the proof. This would be a high-value result for
CSLib's propositional logic module.

**Glivenko's theorem (intuitionistic route).** Glivenko's theorem states that `⊢_IPL ¬¬φ`
iff `⊢_CPL φ`. CSLib's `Semantics/Algebra` module already mentions `hilbertGlivenko`. With
LK and LJ in place, this can also be proved via the sequent calculus translation.

**Subformula property as a lemma.** The subformula property (every formula in a cut-free
proof is a subformula of the conclusion) should be formalized as an explicit lemma, not
just used implicitly in the proof of decidability. This would be a standalone contribution.

### 6.3 Longer-Term (Future Tasks)

**Modal sequent calculus (G3K, G3S4, G3S5).** See Section 2.1. This would be task 302+ and
would depend on LK as a template. The structural rule lemmas from task 279 would reuse directly.

**Linear logic connections.** Since CLL (`Cslib/Logics/LinearLogic/CLL/Basic.lean`) is
already in CSLib, a formalized embedding of LK into CLL (classical logic = CLL + structural
rules) would be a natural bridge task. This is a known result in structural proof theory.

---

## 7. Recommendations

### 7.1 Implementation Priority

1. **Implement both LK and LJ** as separate but parallel inductive types sharing notation
   and structural lemmas. Do not attempt a single parameterized definition at this stage.

2. **Start with the two-sided Finset design.** Left: `Finset (Proposition Atom)`. Right:
   `Finset (Proposition Atom)` for LK; single `Proposition Atom` for LJ.

3. **Prove cut elimination syntactically** (Strategy A). Target Hauptsatz as the central
   deliverable because it enables the subformula property and task 292.

4. **Deliver `hilbert_iff_lk` and `nd_iff_lk` as explicit lemmas** at the module boundary.
   These are the entry points for tasks 291 and 292.

5. **File layout suggestion:**
   ```
   Cslib/Logics/Propositional/SequentCalculus/
   ├── Basic.lean          -- LK definition, structural rules
   ├── LJ.lean             -- LJ definition, restriction to single right formula
   ├── CutElimination.lean -- Hauptsatz, subformula property
   ├── Soundness.lean      -- LK/LJ soundness wrt semantics
   ├── Completeness.lean   -- LK/LJ completeness
   └── Equivalence.lean    -- hilbert_iff_lk, nd_iff_lk, bridges
   ```

### 7.2 Architectural Decisions for Task 279

- Use `InferenceSystem` + `DerivableIn` pattern (same as ND, Hilbert, CLL) for the
  derivability wrapper.
- Do NOT introduce new axioms. Cut elimination must be proved constructively from the
  rule structure.
- Reuse `Proposition.complexity` (defined in `Tableau/Defs.lean`) as the measure for
  cut-rank induction. Check if it is already exported or needs re-exposure.
- The `Theory.Derivation` ND type uses `Finset`. Ensure LK sequents use `Finset` for
  a straightforward `nd_iff_lk` proof.

### 7.3 Strategic Flag for Follow-Up Tasks

After task 279 is complete, propose:
- A new task for Craig interpolation (propositional level, medium complexity)
- A new task for modal sequent calculus G3K (requires modal formulas + box rules)
- These should be added to `specs/TODO.md` with task 279 as dependency

---

## 8. Summary of Key Findings

1. **Task 279 is the critical path item** for four downstream tasks (291, 292, 291, 293)
   and for CSLib's claim to the first Lean 4 LK/LJ formalization.

2. **Sequent calculus generalizes to modal logic (G3K/G3S4/G3S5)** via additional box
   rules on top of the propositional LK skeleton. The typeclass-parameterized formula
   infrastructure in Foundations/ is already designed to support this.

3. **Temporal and bimodal logics are NOT good candidates** for sequent calculi — cyclic
   proofs would be required. The tableau route (tasks 297–301) is the right approach there.

4. **Cut elimination (Hauptsatz) is the central deliverable.** It implies the subformula
   property, which is the engine for task 292's decidability proof. A semantic shortcut
   would not achieve this.

5. **Three parallel decidability proofs** (algebraic from task 289, tableau from tasks
   297–298, cut-free proof search from tasks 279+292) would be a unique CSLib achievement
   worth highlighting externally.

6. **Adjacent opportunities after task 279:** Craig interpolation and the modal sequent
   calculus (G3K) are the highest-value follow-up tasks once 279 is complete.

7. **Shared infrastructure belongs in Propositional/SequentCalculus/ first**, with extraction
   to Foundations/ only after the modal version reveals shared patterns.
