# Teammate C Findings: Critic — Gaps, Risks, and Problems

**Task**: 279 — Propositional Sequent Calculus LK/LJ
**Role**: Critic
**Date**: 2026-06-23

---

## Summary

Task 279 is extremely ambitious: it bundles two distinct sequent calculi (LK classical and LJ
intuitionistic), cut elimination (Hauptsatz) for both, soundness, completeness, and two bridge
proofs (hilbert_iff_lk, nd_iff_lk). Realistic scope is 1,500–3,000+ lines of Lean 4 across
5–8 files. Several of the listed deliverables have subtle circularity risks, and the CLL template
transfers less than one might expect. The dependency on task 280 is benign (task 280 is
archived/completed and records exactly the gap analysis that motivates task 279). The main
blocking risk is cut elimination: Lean 4's termination checker requires substantial scaffolding
for the classic double-induction on cut rank and proof height.

---

## 1. Critical Issues

### 1.1 Dependency on Task 280 — Benign but Invisible

Task 279 lists task 280 as a dependency, but task 280 does not appear in `state.json` and is not
in any active task list. Investigation reveals it is in `specs/archive/280_proof_system_triad_gap_analysis/`.
Task 280 was a research/gap-analysis task that has been completed and archived. Its output (the
archived reports) provides exactly the comprehensive audit that justifies task 279.

**Consequence**: There is no blocking dependency. Task 279 can proceed. The state.json entry for
task 279 should eventually have its dependency on 280 cleared (since 280 is gone from active
projects), but this does not block implementation.

### 1.2 Completeness Circularity Risk

The task asks for both:
- Soundness and completeness for LK/LJ, AND
- Bridge proofs `hilbert_iff_lk` and `nd_iff_lk`

These interact in a potential circularity:

**Path A (direct)**: Prove completeness of LK/LJ independently, then derive bridges.
- LK completeness via direct cut-free proof search (subformula property). This is technically
  correct but requires a complete proof-search algorithm in Lean, which is its own significant
  project.
- LJ completeness is harder: requires either (a) proof-search over the subformula property for
  LJ, or (b) reduction to existing IPL completeness.

**Path B (via bridge)**: Prove `hilbert_iff_lk` first (structural embedding), then transfer
completeness from the existing Hilbert completeness result (`prop_completeness_iff_tautology`,
`int_soundness_completeness`).
- This avoids circularity IF the bridge directions are carefully ordered:
  1. Prove LK/LJ → Hilbert direction (soundness of translation)
  2. Invoke existing Hilbert completeness to get "semantics → Hilbert → LK/LJ"
  3. Result: LK/LJ completeness without a direct proof
- **Risk**: If `hilbert_iff_lk` proof itself requires LK completeness in some direction, the
  argument becomes circular. The implementer must choose one direction as definitionally prior.

**Recommendation**: The only safe non-circular approach is:
1. Define LK/LJ inductively
2. Prove soundness of LK/LJ (directly, by induction on derivation)
3. Prove Hilbert → LK/LJ (simulation: every Hilbert axiom is LK/LJ-provable, MP is cut)
4. Extract completeness as a corollary of (2) + existing Hilbert completeness + (3)
5. State `hilbert_iff_lk` as the conjunction of (3) and the reverse obtained from cut elim + (2)

This must be spelled out explicitly in the implementation plan to prevent a circular argument.

### 1.3 Two Logics is Double Scope

The task asks for LK (classical) and LJ (intuitionistic). These are distinct systems with
different sequent shapes:
- LK: `Γ ⊢ Δ` with `Finset` on both sides
- LJ: `Γ ⊢ A` with `Finset` on the left but at most ONE formula on the right

The distinction is not cosmetic — LJ and LK have different rule sets for disjunction (right),
implication (right), and negation. Cut elimination, while similar in structure, must be proved
for each separately. There is no shared "generic" inductive that handles both.

**Consequence**: The task is effectively two separate sequent calculus projects sharing only the
formula type and some utility lemmas. It should be broken into at least two phases.

---

## 2. Scope Concerns

### 2.1 Estimated Size

| Component | Estimated Lines |
|-----------|----------------|
| LK inductive definition + notation | 80–120 |
| LK structural rules (weakening, exchange, contraction as admissible) | 150–250 |
| LK cut elimination | 400–800 |
| LK soundness | 100–150 |
| LK completeness (via bridge) | 50–80 |
| LJ inductive definition + notation | 80–120 |
| LJ structural rules | 150–250 |
| LJ cut elimination | 400–800 |
| LJ soundness | 100–150 |
| LJ completeness (via bridge) | 50–80 |
| `hilbert_iff_lk` (both directions) | 200–350 |
| `nd_iff_lk` (both directions) | 200–350 |
| File headers, docstrings, notation | 100–150 |
| **Total** | **2,060–3,600 lines** |

This is a large task. Compare: the full ND system (`NaturalDeduction/Basic.lean` + equivalence)
is ~900 lines; the Hilbert system with full metalogic is ~1,600 lines. A complete sequent
calculus with cut elimination will likely exceed either of those individually.

### 2.2 Recommended Phasing

The task should be implemented across at least 4 phases, likely 5–6:

1. **Phase 1**: LK definition, structural admissibility lemmas
2. **Phase 2**: LK soundness + LK→Hilbert bridge
3. **Phase 3**: LK cut elimination (Hauptsatz)
4. **Phase 4**: LJ definition, structural admissibility, soundness
5. **Phase 5**: LJ cut elimination
6. **Phase 6**: Bridge proofs `hilbert_iff_lk`, `nd_iff_lk`, completeness corollaries

Attempting to do this in fewer dispatches risks analysis-paralysis and incomplete phases.

### 2.3 Should the Task be Split?

**Yes, at minimum.** The dependency graph already anticipates downstream tasks 291
(three-way equivalence) and 292 (LJ decidability). Both depend on task 279's deliverables.
If task 279 over-scopes and stalls, both downstreams stall.

**Recommended minimal split**:
- Task 279A: LK definition + soundness + `hilbert_iff_lk` (no cut elim required for bridges)
- Task 279B: LK cut elimination
- Task 279C: LJ definition + soundness + `nd_iff_lk`
- Task 279D: LJ cut elimination

The bridges (279A, 279C) are independently valuable and can be completed without cut elimination.

---

## 3. Technical Risks

### 3.1 CLL Template Fitness — Limited Transfer

The CLL template (`Cslib/Logics/LinearLogic/CLL/Basic.lean`) contributes:

**What transfers**:
- One-sided sequent style using `Multiset` as context type (CLL uses `Multiset`)
- `HasInferenceSystem` instance pattern
- `cutFree` predicate on proofs
- `Proof.rwConclusion` utility

**What does NOT transfer and is actively harmful to follow**:

1. **One-sided vs. two-sided**: CLL is fundamentally one-sided (Γ ⊢ nothing; everything is on
   the left via duality). LK/LJ are two-sided (Γ ⊢ Δ). The CLL `Sequent` is a `Multiset` of
   propositions. For LK you need `Finset × Finset`. For LJ you need `Finset × Proposition`.
   CLL's `Proof : Sequent Atom → Type u` cannot be reused; you need `Proof : Ctx × Ctx → Type u`.

2. **Structural rules**: CLL has NO free weakening or contraction (they are restricted to `!`/`ʔ`
   contexts). LK/LJ have free weakening and contraction. If you copy CLL rules naively, you omit
   the structural rules that make classical/intuitionistic logic work. The CLL template would lead
   you to define rules that accidentally omit weakening.

3. **Cut formula duality**: CLL's cut uses `a` and `a⫠` (dual). LK/LJ cut uses the same formula
   `A` on both sides: `Γ ⊢ A, Δ` and `Γ', A ⊢ Δ'` combine to `Γ, Γ' ⊢ Δ, Δ'`. There is no
   notion of formula duality in classical/intuitionistic logic.

4. **CLL cut elimination is a TODO stub**: `CutElimination.lean` is 34 lines and the entire
   content is two commented-out skeletons with `-- TODO` annotations. There is no actual cut
   elimination in CLL to learn from.

5. **Multiset vs. Finset**: CLL uses `Multiset` contexts (which naturally handle linear
   resources). The existing ND system uses `Finset` (which absorbs contraction and exchange).
   Task 279 specifies "Finset-based contexts." This is a reasonable choice for classical/
   intuitionistic logic (contraction/exchange are free) but is a departure from CLL's Multiset.
   Finset introduces `DecidableEq` requirements everywhere and complicates membership proofs,
   though it matches the existing ND system's `Ctx Atom = Finset (Proposition Atom)`.

**Bottom line**: The CLL file is a useful reference for notation patterns and `HasInferenceSystem`
integration, but the actual rule structure, cut formulation, and context type must be redesigned
for LK/LJ from scratch.

### 3.2 Cut Elimination — Lean 4 Termination Challenge

Gentzen's cut elimination is typically proved by a double induction:
- Outer induction on **cut rank** (complexity of the cut formula)
- Inner induction on **proof height** (sum of heights of the two premises)

This creates a well-founded measure over pairs `(rank, height)`. Lean 4's termination checker
handles `termination_by` with lexicographic pairs, but the proof structure requires that:

1. The **grade** (rank, height) of the recursive call is strictly smaller
2. Every case in the case-split reduces the grade
3. The inductive hypothesis for cut on smaller rank is available globally

In Lean 4, this typically requires either:
- A `Nat`-valued measure function and `termination_by` annotation
- Or mutual recursion if the standard structural recursion fails

**Specific difficulties**:

a) **Key inductive cases**: The `cut` on `A ∧ B` requires cuts on `A` and `B` separately (lower
   rank). Lean 4 needs explicit rank-decreasing witnesses for each sub-call. The proof of
   rank-decrease requires that `sizeOf A < sizeOf (A ∧ B)`, which holds by the `Proposition`
   inductive definition but must be established explicitly as simp/omega lemmas.

b) **Principal cuts**: When both premises end with a rule for the cut formula (e.g., both end
   with `andR`/`andL`), the cut on height is: the sub-proof heights are strictly less. The
   `sizeOf`-based measure for `Proof` objects may not be syntactically clear to Lean's
   termination checker, requiring a manual height function.

c) **Non-principal cuts**: When the last rule does not involve the cut formula, the resulting
   recursive cut has smaller height on the left or right branch. This is the easier case but
   requires case-splitting over every rule.

d) **Number of cases**: LK has ~20 inference rules. Cut elimination requires case analysis over
   all combinations (cut formula in principal position vs. non-principal, left vs. right). This
   is O(20²) = ~400 potential cases, though most are symmetric and short.

**Lean 4 recommendation**: Define a `Proof.height : ⇓Γ → ℕ` function explicitly, prove
`sizeOf (cut_formula)` lemmas using `omega`, and use `termination_by (sizeOf A, p.height + q.height)`
or similar lexicographic measure with `decreasing_by omega` or `decreasing_by simp; omega`.

### 3.3 Finset Decidability Requirements

`Finset (Proposition Atom)` requires `DecidableEq (Proposition Atom)`. This is already provided
by `deriving DecidableEq` on the `Proposition` inductive in `Defs.lean`. However:

- Every lemma about Finset membership, `Finset.insert`, `Finset.union`, etc. requires the
  `DecidableEq` instance to be in scope.
- The variable section already uses `variable {Atom : Type u} [DecidableEq Atom]`.
- The `Proposition` DecidableEq instance depends on `DecidableEq Atom`.

This means every theorem in the sequent calculus needs `[DecidableEq Atom]` in scope. This is
already the pattern in `NaturalDeduction/Basic.lean` and should carry over without issue.

**Minor risk**: If Finset operations on propositions trigger excessive `decide` goals that slow
elaboration. The mitigant is `simp` with `Finset.mem_insert`, `Finset.mem_union` etc.

### 3.4 Admissibility of Structural Rules vs. Built-in Rules

There are two design choices for weakening/contraction in LK/LJ:

**Option A (built-in)**: Include weakening and contraction as primitive inference rules
```lean
| weakL : Proof (Γ ⊢ Δ) → Proof (insert A Γ ⊢ Δ)
| contrL : Proof (insert A (insert A Γ) ⊢ Δ) → Proof (insert A Γ ⊢ Δ)
```

**Option B (admissible)**: Use Finsets on both sides, which absorbs exchange and contraction
automatically (since `insert A (insert A S) = insert A S` for Finset). Only weakening remains
as an explicit structural rule or as a derived lemma.

The existing ND system uses Option B (Finset contexts). This is the recommended approach for
LK/LJ as well: with Finset on both sides, exchange and contraction are definitionally free.
Weakening (monotonicity) becomes a derived lemma.

**Risk with Option B**: Some cut elimination proofs in the literature assume explicit exchange
rules. If following a textbook proof step-by-step, the exchange steps may need to be replaced
by Finset commutativity rewrites (`Finset.insert_comm`, `Finset.union_comm`). These are
available in Mathlib but may require annotation.

### 3.5 LJ Right Side: Singleton or Option?

LJ has the constraint that the right-hand side of a sequent contains at most one formula.
Two common representations:
- `Option (Proposition Atom)` — `none` for empty succedent, `some A` for single formula
- `Proposition Atom` with a special `⊥` or `False` for empty

With `Finset`-based contexts (as specified), there is a mismatch: `Finset (Proposition Atom)`
on the right side can hold zero or more formulas. To encode the LJ constraint, you either:
1. Use a separate type for LJ (e.g., `type LJSequent := Ctx × Option (Proposition Atom)`)
2. Use `Finset` but constrain by a predicate (`h : Δ.card ≤ 1` in every rule)
3. Define LJ entirely separately with right-side as `Proposition Atom` (not `Finset`)

Option 3 is the standard academic approach and the cleanest in Lean 4. The task description says
"Finset-based contexts on both sides" which suggests Option 2, but this makes every rule carry
an extra hypothesis about Finset cardinality. This is awkward and non-standard.

**Recommendation**: For LJ, use `Ctx × Proposition Atom` (left Finset, right single formula).
This matches the shape of the existing ND system (`Sequent = Finset × Proposition`). The task
description should be interpreted as "Finset on the left" for LJ.

---

## 4. Integration Risks

### 4.1 Existing Sequent Notation Conflict

The existing ND system defines:
```lean
scoped notation Γ:60 " ⊢ " A => (⟨Γ, A⟩ : Sequent)
```
where `Sequent = Ctx × Proposition`. This notation is scoped to the `Cslib.Logic.PL` namespace.

A two-sided LK sequent `Γ ⊢ Δ` would conflict with this notation if both are open in the same
scope. The LK type would need either:
- A distinct notation (e.g., `Γ ⊢ᵥ Δ` or `Γ ⊢LK Δ`)
- Its own scoped namespace (`namespace Cslib.Logic.PL.LK`)

The CLL pattern suggests using a separate namespace (`Cslib.Logic.CLL`) with local scoping,
which avoids conflict. This is the right approach here.

### 4.2 Import Cycles

The planned bridge `hilbert_iff_lk` requires importing both:
- `Cslib.Logics.Propositional.ProofSystem.Derivation` (Hilbert system)
- The new `Cslib.Logics.Propositional.SequentCalculus.LK.Basic` (LK system)

This is safe as long as the LK file does NOT import the ProofSystem (i.e., the arrow goes one
way). The bridge file sits at a higher level and imports both. This matches the existing
`NaturalDeduction/Equivalence.lean` pattern which imports both the ND and Hilbert systems.

**Risk**: If the LK definition imports `Defs.lean` + `InferenceSystem` (only), and the Hilbert
system imports only `Defs.lean`, there is no cycle. Care must be taken not to accidentally
import Hilbert machinery from inside the LK definition file.

### 4.3 Directory Structure

The task requires deciding on a directory layout. Options:
```
Cslib/Logics/Propositional/
├── SequentCalculus/
│   ├── LK/
│   │   ├── Basic.lean       (rules)
│   │   ├── Soundness.lean
│   │   ├── CutElimination.lean
│   │   └── Completeness.lean
│   ├── LJ/
│   │   ├── Basic.lean
│   │   ├── Soundness.lean
│   │   ├── CutElimination.lean
│   │   └── Completeness.lean
│   └── Bridge.lean          (hilbert_iff_lk, nd_iff_lk)
```

This mirrors the `NaturalDeduction/` structure. The `ProofSystemEquivalence.lean` (task 291)
would then import from both `SequentCalculus/` and `NaturalDeduction/`.

### 4.4 `lake exe mk_all` Barrel Import

Adding new files requires running `lake exe mk_all --module` to update `Cslib.lean`. This is
a CI step listed in the CSLib CI verification order. The task must include this step, which is
often forgotten in multi-file implementations.

---

## 5. Recommendations

### R1 — Reduce scope to LK-only for the initial task delivery

Ship `hilbert_iff_lk` (without `nd_iff_lk`) as the first milestone, with LK soundness and the
Hilbert bridge. LJ can be a follow-up task. This unblocks tasks 291 and 292 for the pieces that
only require the Hilbert bridge.

### R2 — Cut elimination as a separate file with stub first

Implement LK fully (definition + soundness + bridge) in one file. Open a `LK/CutElimination.lean`
with the theorem statement and `sorry` as a clear marker — then fill the sorry as a subsequent
phase. This avoids the risk of getting stuck on termination-proof details before the structurally
simpler parts are done.

**Note**: A sorry stub is a temporary implementation placeholder for the purposes of getting
neighboring functionality (the bridges) verified. The sorry must not ship in the final PR; this
is a phasing strategy only.

### R3 — Use `Finset` on left, single formula on right for LJ

Do not try to use `Finset × Finset` for LJ with cardinality constraints. Use
`Ctx × Proposition Atom` directly, matching the existing ND system's `Sequent` type.

### R4 — Define explicit `Proof.height` function before cut elimination

Before attempting the cut elimination proof, define:
```lean
def Proof.height : ⇓Γ → ℕ
  | ax => 0
  | cut p q => p.height + q.height + 1
  ...
```
and prove the key size lemmas needed for the termination argument explicitly using `omega`.

### R5 — Check Mathlib for admissibility infrastructure

Before building cut elimination from scratch, use `lean_leansearch` to check if Mathlib has
any general cut elimination infrastructure or well-founded recursion patterns on proof trees
that could be instantiated. Mathlib has `Gentzen`-related content in some areas.

### R6 — Avoid the ND bridge until LK is stable

The `nd_iff_lk` bridge additionally requires translating ND derivations (with their 10
constructors, Finset contexts, and `Theory` parameter) into LK proofs. The LJ bridge is
similarly complex. These are two separate 200–350 line proofs each. Defer them to a follow-up
phase or task to avoid scope overload.

### R7 — The plan must explicitly order proofs to avoid completeness circularity

The implementation plan must state clearly:
1. LK soundness is proved by induction on `Proof`, with no reference to completeness
2. The Hilbert → LK direction is proved by exhibiting LK proofs of all Hilbert axioms
3. LK completeness is defined as "if semantically valid, then there is a Hilbert proof (existing
   completeness), and Hilbert → LK gives an LK proof" — this is circular-free

---

## 6. Summary Assessment

| Deliverable | Risk Level | Estimated Effort |
|-------------|------------|-----------------|
| LK definition + Finset infrastructure | Low | 1 phase (80–120 lines) |
| LK structural admissibility | Medium | 1 phase (150–250 lines) |
| LK soundness | Low-Medium | 1 phase (100–150 lines) |
| `hilbert_iff_lk` both directions | Medium | 1 phase (200–350 lines) |
| LK cut elimination | HIGH | 1–2 phases (400–800 lines) |
| LJ definition | Low-Medium | 1 phase (80–120 lines) |
| LJ structural admissibility | Medium | 1 phase (150–250 lines) |
| LJ soundness | Low-Medium | 1 phase (100–150 lines) |
| `nd_iff_lk` both directions | Medium | 1 phase (200–350 lines) |
| LJ cut elimination | HIGH | 1–2 phases (400–800 lines) |

**Overall assessment**: The task as stated is feasible but significantly underestimates the
implementation scope. Cut elimination alone is a multi-week Lean 4 formalization project.
The safe path is to split the task, ship LK + bridges first, then LJ + cut elimination in
follow-ups. The CLL template provides minimal guidance for the actual proof content. The
existing Propositional ND system is the better template to follow.
