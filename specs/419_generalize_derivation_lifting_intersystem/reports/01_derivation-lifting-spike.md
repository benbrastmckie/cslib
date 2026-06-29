# Task 419 — SPIKE: Generalize Derivation Lifting to a Cross-Logic Layer

**Task type**: cslib (SPIKE — investigation, read-only, no Lean edits)
**Status**: research / spike — no Lean source modified; this report is the only artifact.
**Date**: 2026-06-29
**Source**: specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md §6, Rank 4.

---

## 1. VERDICT

**(b) NOT CLEANLY ABSTRACTABLE — recommend mark BLOCKED (never sorry).**

The stated target — "ONE axiom-subsumption derivation-lifting result reusable by Modal,
Bimodal, and PL, hosted on the shared `InferenceSystem`/`algebraicDerivationSystem`
abstraction" — does not hold up under inspection of the actual constructor signatures. Three
independent obstacles each block it; any one is sufficient for BLOCKED:

1. **Parameterization-axis mismatch**: Modal and PL lift over an *axiom predicate*
   (`Axioms : Proposition Atom → Prop`); Bimodal's `DerivationTree fc` lifts over a *frame
   class* (`fc : FrameClass`) with a fixed, concrete `Axiom` inductive — there is no axiom
   predicate to subsume. Bimodal has **no axiom-subsumption lift to unify**.
2. **The shared substrate cannot host the lift**: `algebraicDerivationSystem` is built on
   `ListDeriv`, which by design omits `necessitation`; axiom-subsumption lifting must recurse
   *through* `necessitation`/`temporal_*`. Axiom subsumption at the seam level is a *morphism
   between two tag types*, which the `InferenceSystem` class does not model.
3. **Constructor + formula-type variance**: the three derivation trees live over three
   different formula algebras (PL.Proposition, Modal.Proposition, Bimodal.Formula) with three
   different constructor sets (4 / 5 / 7). The `necessitation` and `temporal_duality` arms are
   the specific variance points the task names, and they resist a single generic recursion.

A narrow 2-way unification (PL + Modal only) is *technically* possible but has near-zero or
negative ROI (see §5). It is **not** what the task asks for and does not justify the task's
Effort-L cost. Recommendation: **BLOCKED**, with the precise blocker recorded for the
orchestrator.

---

## 2. What the three "lifts" actually are (verified from source)

The task description treats Modal `liftDerivation`, PL's lift, and Bimodal `liftDerivationWith`
as three instances of one concept. They are not. They are **three different operations**:

| Operation | File:line | Signature shape | What it varies | Side conditions |
|---|---|---|---|---|
| Modal `liftDerivation` | `Modal/Metalogic/InterSystem/Lifting.lean:47` | `(∀ φ, A1 φ → A2 φ) → DerivationTree A1 Γ φ → DerivationTree A2 Γ φ` | **axiom predicate** A1⊆A2 | none |
| PL `liftDerivationTree` | `Propositional/Semantics/Algebra/ConjImpConservative.lean:59` | `(∀ ψ, A1 ψ → A2 ψ) → DerivationTree A1 Γ φ → DerivationTree A2 Γ φ` | **axiom predicate** A1⊆A2 | none |
| Bimodal `DerivationTree.lift` | `Bimodal/ProofSystem/Derivation.lean:~92` | `fc₁ ≤ fc₂ → DerivationTree fc₁ Γ φ → DerivationTree fc₂ Γ φ` | **frame class** fc₁≤fc₂ | none |
| Bimodal `liftDerivationWith` | `Bimodal/Metalogic/ConservativeExtension/Lifting.lean:636` | `(a : Atom) → ExtDerivationTree fc Γ φ → a ∉ collectDerivInl d → DerivationTree fc (Γ.map (liftFormula a)) (liftFormula a φ)` | **syntax** (unembed fresh atom) | freshness `a ∉ …`; per-node formula rewrites |

Key facts:

- **Modal and PL are genuine axiom-subsumption lifts.** Their bodies are *identical up to the
  formula type and the one extra `necessitation` arm*: remap `.ax` leaves via `h_sub`, recurse
  structurally on every other constructor.
- **Bimodal `liftDerivationWith` is conservative-extension unembedding, not axiom subsumption.**
  It substitutes a fresh atom for the extension atom `Sum.inr ()`, threads a freshness side
  condition through every node, and rewrites the *formula* at each node (`liftFormula a …`,
  and for the duality arm `liftFormula_swapTemporal a φ ▸ …`). It is `noncomputable` and shaped
  nothing like `liftDerivation`. The audit's "Bimodal's analogous `liftDerivationWith`" framing
  (§6) is the source of the conflation; it is analogous in *spirit* (structural recursion over a
  derivation tree) but not in *interface* (it varies syntax, not axioms).
- **Bimodal's actual axiom-monotone lift is `DerivationTree.lift` over `fc`**, a *different axis*
  from PL/Modal's axiom-predicate axis.

---

## 3. The three constructor sets (verified)

```
PL.DerivationTree (Axioms : PL.Proposition Atom → Prop)        -- 4 constructors
  ax · assumption · modus_ponens · weakening

Modal.DerivationTree (Axioms : Modal.Proposition Atom → Prop)  -- 5 constructors
  ax · assumption · modus_ponens · necessitation · weakening
                                   ^^^^^^^^^^^^^ empty-ctx → box φ

Bimodal.DerivationTree (fc : FrameClass)                       -- 7 constructors, NO axiom pred
  axiom(h : Axiom φ)(h_fc : h.minFrameClass ≤ fc)
  · assumption · modus_ponens
  · necessitation            empty-ctx → box φ
  · temporal_necessitation   empty-ctx → φ.allFuture
  · temporal_duality         empty-ctx → φ.swapTemporal     ← variance point
  · weakening
```

- PL has **no box** in its `Proposition`, so it has no `necessitation` arm and never could.
- Modal's `necessitation` is axiom-blind (passes through under any `h_sub`), so it does not
  obstruct a PL↔Modal unification *per se* — the obstruction is that PL and Modal use
  **different formula types** (`PL.Proposition Atom` vs `Modal.Proposition Atom`), so one
  recursion cannot range over both without abstracting the formula algebra too.
- Bimodal's `temporal_duality` is the named "variance" risk. In an axiom-subsumption setting it
  *would* pass through cleanly (it is axiom-blind), **but Bimodal has no axiom predicate** to
  subsume in the first place, so the question is moot — the unification fails one level earlier
  (axis mismatch, §4), before constructor variance even matters.

---

## 4. Why the shared `InferenceSystem`/`algebraicDerivationSystem` cannot host this

Read from `Cslib/Foundations/Logic/InferenceSystem.lean` and
`Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`:

- `class InferenceSystem (S α) where derivation (a : α) : Sort v` — a tag `S` mapping a value to
  a derivation Sort. **No axiom-predicate parameter exists at this level.** Different axiom sets
  become different tag types (`HilbertOf Axioms1` vs `HilbertOf Axioms2` in
  `Modal/Metalogic/GenericMCSBridge.lean`). Axiom subsumption is therefore a *morphism between
  two `InferenceSystem` instances*, a notion the class does not provide.
- `def algebraicDerivationSystem : DerivationSystem F` is built from
  `ListDeriv Γ φ := DerivableIn S (listImp Γ φ)` — pure implication-chaining with
  `mp`/`weakening`/`assumption` only. Its own docstring (GenericMCS.lean:103–109) states:
  *"`ListDeriv` does not include necessitation … the modal-specific `modalDerivationSystem` must
  still be used"* for necessitation-dependent reasoning.
- Axiom-subsumption lifting **must recurse through `necessitation`** (Modal) and would need
  `temporal_*` (Bimodal). The seam abstraction is precisely the layer that *erases* those
  constructors. So the lift cannot be expressed where the task wants it: it must live on the
  per-logic `DerivationTree`, which is exactly where it already lives (three times).

Conclusion: the shared substrate is the right home for the **MCS / deduction-theorem
machinery** (which is already shared and axiom-blind), but it is structurally the **wrong home
for the derivation lift**, which is inherently a statement about the rule-bearing inductive.

---

## 5. The only clean unification, and why it is not worth it

A genuine 2-way unification of **PL + Modal** (the two real axiom-subsumption lifts) is possible
in principle, but every realization has poor ROI:

- **Option A — shared typeclass `LiftableDerivation`** with method
  `liftDeriv : (∀ φ, A1 φ → A2 φ) → D A1 Γ φ → D A2 Γ φ` and a `derivable_mono` corollary proved
  once over the class. Cost: +1 class, +1 generic corollary, +2 instances whose bodies are the
  *existing* `liftDerivation`/`liftDerivationTree` recursions verbatim. Net: removes **zero**
  recursion bodies (each logic still supplies its own), unifies only the `_mono` corollary
  statement (~4 trivial lines each). Negative-to-neutral LOC, added indirection. Bimodal cannot
  instantiate it (no axiom predicate), so it is at best a PL+Modal cosmetic.
- **Option B — one shared generic inductive** reused as every logic's `DerivationTree`. Requires
  unifying `PL.Proposition` / `Modal.Proposition` / `Bimodal.Formula` into one syntax-with-holes
  and rewriting every proof system + all downstream files. XL+ refactor; Bimodal still does not
  fit (fc-parameterized, extra temporal rules, concrete `Axiom`). Out of scope by orders of
  magnitude; high regression risk across 16+ Modal files and the entire Bimodal/Temporal stack.

Neither delivers the task's promised payload ("ONE result reusable by Modal, **Bimodal**, and
PL"). Bimodal is excluded by construction in both.

---

## 6. Recommendation to the orchestrator

**Mark task 419 BLOCKED.** The blocker is structural and precisely characterized (§4 axis
mismatch + §2 operation conflation), not a proof-effort gap, so it will not be resolved by more
implementation time and must **never** be papered over with `sorry` or a vacuous definition.

Concrete blocker statement (for escalation):

> The task presupposes that Modal `liftDerivation`, PL `liftDerivationTree`, and Bimodal
> `liftDerivationWith` are three instances of one *axiom-subsumption* lift unifiable on
> `InferenceSystem`/`algebraicDerivationSystem`. Source inspection refutes this:
> (1) Bimodal's `DerivationTree` is frame-class-parameterized over a concrete `Axiom` inductive
> and has **no axiom predicate**; its `liftDerivationWith` is conservative-extension atom
> unembedding (freshness side-conditions + per-node formula rewrites), a different operation.
> (2) `algebraicDerivationSystem` is built on `ListDeriv`, which omits `necessitation` by
> design (GenericMCS.lean:103–109), whereas the lift must recurse through it; axiom subsumption
> at that level is a tag-to-tag morphism the `InferenceSystem` class does not express.
> (3) The three lifts range over three distinct formula types and constructor sets (4/5/7),
> so no single recursion ranges over all three without first unifying the syntaxes (XL+).
> The only clean unification (PL+Modal typeclass) removes zero recursion bodies and excludes
> Bimodal, failing the stated payload.

If the project still wants *some* consolidation, the supportable follow-on (separate, smaller
task — do **not** fold into 419) would be: a PL+Modal-only `derivable_mono` statement-level
typeclass, explicitly scoped to the two axiom-predicate logics and explicitly excluding Bimodal.
That is a cosmetic XS, not the cross-logic Foundations layer task 419 envisions, and should be
user-approved before spawning.

---

## 7. Reuse-check trail (CSLib reuse-first)

- `Cslib/Foundations/Logic/InferenceSystem.lean` — `InferenceSystem` class (no axiom param).
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — `algebraicDerivationSystem` (ListDeriv;
  no necessitation), `HasMinimalAxioms`, `algebraic_has_deduction_theorem`.
- `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean:47` — `ListDeriv` (implication-chain).
- `Cslib/Foundations/Logic/ProofSystem.lean:342` — `MinimalHilbert`.
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean:56` — `DerivationSystem` structure
  (fields: `Deriv`, `weakening`, `assumption`, `mp` — note: **no axiom-leaf, no necessitation**;
  confirms the seam is rule-fixed/axiom-blind).
- Existing lifts: `Modal/Metalogic/InterSystem/Lifting.lean:47`,
  `Propositional/Semantics/Algebra/ConjImpConservative.lean:59`,
  `Bimodal/ProofSystem/Derivation.lean:~92` (`lift`),
  `Bimodal/Metalogic/ConservativeExtension/Lifting.lean:636` (`liftDerivationWith`).
- `Foundations/Logic/Metalogic/ConservativityLift.lean` (task 417 placement) exists but hosts
  conservativity-lift scaffolding, not an axiom-subsumption derivation functor; it does not
  change the verdict.

No existing Foundations abstraction already provides the target; and none *can* without the
syntax unification ruled out above. Reuse-first is satisfied: the right reuse is to **keep the
three per-logic lifts** and not introduce a leaky cross-logic layer.
