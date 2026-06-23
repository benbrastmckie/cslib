# Research Report: Task #266 — Teammate A (Primary Approach)

**Task**: 266 - Research Propositional and Foundations Improvements
**Date**: 2026-06-23
**Artifact**: 04_teammate-a-findings.md
**Role**: Teammate A — Post-Hilbert-Primary Audit

---

## Key Findings

### Items Completed by Tasks 281-285

The following plan items from `03_propositional-foundations-plan.md` are DONE based on direct codebase audit:

**Phase 1 (Bridge Algebraic Completeness to Hilbert) — COMPLETE**

`Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` exists and contains:
- `MPL.hilbert_alg_complete : Derivable MinPropAxiom φ ↔ GHAValid φ`
- `IPL.hilbert_alg_complete : Derivable IntPropAxiom φ ↔ HAValid φ`
- `CPL.hilbert_alg_complete : Derivable PropositionalAxiom φ ↔ BAValid φ`

`Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` exists and uses
`hilbert_alg_complete` at lines 84, 86, 96, 98, 105, 109, 119, 120, 125, 131, 137, 138, 143, 149, 156, 159, 164.

Evidence: `grep -rn "hilbert_alg_complete" Cslib/Logics/Propositional/` returns 20+ hits
confirming the bridge is in active use.

**Modal/Temporal/Bimodal ProofSystem Tag Instances — COMPLETE**

All 15 modal systems have full `InferenceSystem` + bundled Hilbert class instances:
- `Modal/ProofSystem/Instances/` contains separate files for K, T, D, B, K4, K5, K45, S4, S5, TB,
  KB5, D4, D5, D45, DB — each with `InferenceSystem`, inference rule, axiom, and bundled instances
- `Temporal/ProofSystem/Instances.lean` provides the complete `TemporalBXHilbert` instance for
  `Temporal.HilbertBX`, including all 22 `HasAxiom*` instances
- `Bimodal/ProofSystem/Instances.lean` provides the `BimodalTMHilbert` instance for
  `Bimodal.HilbertTM` (confirmed in file header: "all 22 HasAxiom*, HasAxiomMF, and BimodalTMHilbert instances")

All tag types declared in `ProofSystem.lean` (lines 471-528) are now fully instantiated.

**ProofSystem.lean Documentation — COMPLETE**

`Cslib/Foundations/Logic/ProofSystem.lean` lines 41-57 now contain accurate documentation
describing the Hilbert-primary architecture, including metalogic results at the Hilbert level
and the complete list of `hilbert_alg_complete`, `hilbertIplConservativeOverMpl`, and
`hilbertGlivenko` theorems. No stale "not yet ported" comment was found. The plan's Phase 2
target (fix line 49-50) is already done.

---

### Items Remaining — CONFIRMED NOT DONE

**Phase 2 (Fix subs TODO) — PARTIAL**

`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:275` still contains:
```
/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
```
The `ProofSystem.lean` stale comment is gone, but the `subs` capture-avoidance TODO remains.
Since PL has no binding operators, this comment is misleading and should be clarified or removed.

**Phase 3 (HasDia Primitive) — NOT DONE**

`Cslib/Foundations/Logic/Connectives.lean` does not contain `class HasDia`. The file currently
defines: `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`, `HasNext`, `HasAnd`, `HasOr`,
plus bundled classes. Comments at lines 96, 142 still say "require a separate `HasDia` typeclass,
since `□` and `◇` become independent operators" — acknowledging the gap but not implementing it.

`Cslib/Foundations/Logic/Axioms.lean` comments at lines 152, 163, 175 still say "since `HasDia`
is not yet a primitive in `ModalConnectives`" — confirming this work is undone.

**Phase 4 (Decidable Tautology Instance) — NOT DONE**

`Cslib/Logics/Propositional/Semantics/Bool.lean` has:
- `BoolEvaluate` and `BoolEvaluate_eq_iff` (bridge between Bool and Prop evaluation)
- `instDecidableBoolEvaluate` (decidability of `Evaluate` under Boolean valuations)
- `Tautology φ` definition (line 79)

But no `instance : Decidable (Tautology φ)` exists. No file in `Cslib/` contains
"instDecidableTautology" or "Decidable (Tautology". The infrastructure is 90% assembled; only
the `Fintype Atom` enumeration step is missing.

**Phase 5 (GenericMCS Bridge for Modal Logic) — NOT DONE**

No `GenericMCSBridge.lean` exists in `Cslib/Logics/Modal/Metalogic/`. The modal, temporal, and
bimodal logics each use their own custom derivation systems (`modalDerivationSystem`,
`temporalDerivationSystem`, `bimodalDerivationSystem`) rather than the generic
`algebraicDerivationSystem` from `Foundations/Logic/Metalogic/GenericMCS.lean`. The Phase 5
scoping work (prove equivalence, or document the gap) is undone.

**Phase 6 (Extract Propositional Tableau to Foundations/) — NOT DONE**

`Cslib/Foundations/Logic/` has no `PropositionalTableau.lean`. The 8 propositional tableau rules
(`andPos`, `andNeg`, `orPos`, `orNeg`, `impPos`, `impNeg`, `negPos`, `negNeg`) are still
embedded inside `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` (lines 87-101).
No extraction has occurred.

**Phase 7 (Add Propositional Test Coverage) — NOT DONE**

`CslibTests/` contains 13 test files (Bisimulation, CCS, CLL, DFA, FreeMonad, GrindLint,
HasFresh, HML, ImportWithMathlib, LambdaCalculus, LTS, MLL, Reduction). None cover
`Cslib.Logics.Propositional.*`. `CslibTests.lean` has 13 imports, none for Propositional.
Zero test coverage for `BoolEvaluate`, `Tautology`, or any propositional derivability.

---

## Recommended Approach

Given that tasks 281-285 completed Phases 1 and most of Phase 2, the remaining work consists of
Phases 2 (partial), 3, 4, 5, 6, and 7 from the plan.

**Priority ordering for remaining work (effort × value):**

1. **Phase 2 partial** — Remove/clarify the `subs` capture-avoidance TODO in Basic.lean:275.
   Trivial edit (< 5 min). No implementation skill needed.

2. **Phase 4** — `Decidable (Tautology φ)` instance. The infrastructure is already in
   Bool.lean. The required steps are:
   - Prove `Tautology φ ↔ ∀ v : BoolValuation Atom, BoolEvaluate v φ = true`
     using `BoolEvaluate_eq_iff`
   - Use `Fintype.decidableForallFintype` or similar Mathlib instance for
     `[Fintype Atom] [DecidableEq Atom]` to close `Decidable (∀ v : Atom → Bool, ...)`
   - ~20-30 lines in `Bool.lean`

3. **Phase 7** — Test coverage. Depends on Phase 4 for the `decide` tests.
   `CslibTests/Propositional.lean` with `#eval BoolEvaluate` examples and basic derivability
   smoke tests. ~30-50 lines.

4. **Phase 3** — `HasDia` primitive. Additive change to `Connectives.lean`:
   `class HasDia (F : Type*) where dia : F → F` with scoped notation `◇`.
   Update 3 comment lines in `Axioms.lean`. ~15 lines.

5. **Phase 5** — GenericMCS bridge. Higher effort. All three downstream logics
   (modal, temporal, bimodal) use custom derivation systems. The bridge proof requires
   showing `algebraicDerivationSystem (S := Modal.HilbertK)` and
   `modalDerivationSystem ModalAxiom` agree on consistency/MCS properties.
   If feasible, eliminates ~200-300 lines of duplicated MCS code per logic.

6. **Phase 6** — Propositional tableau extraction. The 8 propositional rules in
   `Bimodal/Decidability/Tableau.lean` are specialized to `SignedFormula (Formula Atom)`.
   Generalizing to a polymorphic `[HasImp F] [HasAnd F] [HasOr F]` requires either rewriting
   them generically or parameterizing the signed formula type. Medium effort (~200 lines).

---

## Evidence / Examples

### Phase 1 Complete — HilbertCompleteness.lean exists

```
/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean
```
Header: "Hilbert-Level Algebraic Completeness for Propositional Logic ... proves Hilbert-level
algebraic completeness for all three propositional logic tiers using the Hilbert Lindenbaum
algebra directly."

### Phase 2 Partial — subs TODO still present

```
/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:275
/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
```

### Phase 3 Not Done — HasDia mentioned but not implemented

```
/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Axioms.lean:152
"Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `HasDia` is not yet
a primitive in `ModalConnectives`."
```

### Phase 4 Not Done — Tautology is Prop-only

```
/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Bool.lean:79
def Tautology (φ : PL.Proposition Atom) : Prop :=
  ∀ (v : Valuation Atom), Evaluate v φ
```
No `Decidable (Tautology φ)` instance in any file.

### Phase 5 Not Done — custom derivation systems persist

```
/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/DerivationTree.lean:198
def modalDerivationSystem (Axioms : Proposition Atom → Prop) : ...
```
`algebraicDerivationSystem` is defined in `Foundations/Logic/Metalogic/GenericMCS.lean:46`
but not referenced by any modal/temporal/bimodal file.

### Phase 6 Not Done — propositional rules embedded in bimodal tableau

```
/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean:85-101
inductive TableauRule : Type where
  | andPos  -- T(A AND B) -> T(A), T(B)
  | andNeg  -- F(A AND B) -> F(A) | F(B)
  | orPos   -- T(A OR B) -> T(A) | T(B)
  | orNeg   -- F(A OR B) -> F(A), F(B)
  | impPos  -- T(A -> B) -> F(A) | T(B)
  | impNeg  -- F(A -> B) -> T(A), F(B)
  | negPos  -- T(neg A) -> F(A)
  | negNeg  -- F(neg A) -> T(A)
  ...
```
No `Cslib/Foundations/Logic/PropositionalTableau.lean` exists.

### Phase 7 Not Done — CslibTests.lean has no Propositional import

```
/home/benjamin/Projects/cslib/CslibTests.lean (13 imports, none for Propositional)
```

---

## Confidence Level

**High** for all six "NOT DONE" findings: each was verified by direct file listing, grep, and
file content inspection. The "COMPLETE" findings for Phase 1 and Modal/Temporal/Bimodal instances
are confirmed by both file existence and content.

**Medium** for the effort estimates in the Recommended Approach section. Phases 4 and 3 are
straightforward; Phase 5 (GenericMCS bridge) involves a non-trivial compatibility proof whose
complexity depends on how closely `algebraicDerivationSystem` matches the custom systems.
