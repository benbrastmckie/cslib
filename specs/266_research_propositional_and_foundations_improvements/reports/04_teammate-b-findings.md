# Research Report: Task #266 — Teammate B Findings

**Task**: 266 - Research improvements to Propositional/ and Foundations/Logic/
**Role**: Teammate B — Alternative Approaches (focus on what the task description might be MISSING)
**Started**: 2026-06-23
**Completed**: 2026-06-23
**Task Type**: cslib
**Domains**: logic, formal

---

## Executive Summary

- Zero sorries remain in Propositional/ and Foundations/Logic/
- `lake lint` passes cleanly for all of Cslib (no issues to fix)
- `lake exe lint-style` produces no warnings in either directory
- One in-docstring TODO tag remains in `NaturalDeduction/Basic.lean` (line 275) identifying a known non-capture-avoiding substitution
- The And/Or axiom typeclasses (`HasAxiomAndI`, `HasAxiomOrE`, etc.) are **not bundled** into `MinimalHilbert`/`IntuitionisticHilbert`/`ClassicalHilbert` — they are registered separately for each of the three concrete tags; no bundled `PropAndOrHilbert` class exists
- `InferenceSystem.lean` has an empty module docstring (`/-! -/`) that should be filled in
- `FUntilEquiv` and `PSinceEquiv` (BX12/BX12') are definitional identities (`φ → φ`) per the Burgess 1982 convention, which is acknowledged in the docstring; they are included in `TemporalBXHilbert` for structural uniformity but may merit a documented design note
- `DNE` is defined as an axiom formula in `Axioms.lean` but there is no `HasAxiomDNE` typeclass in `ProofSystem.lean`; DNE is instead derived as a theorem `double_negation` from Peirce + EFQ; this is intentional but the gap is implicit

---

## Findings

### Finding 1: Zero Sorries (Confirmed)

`grep -rn sorry` over both directories returns nothing. All proofs are complete.

**Confidence**: High (direct grep result)

---

### Finding 2: Linter Clean (Both Linters)

- `lake lint` (environment linter): passes with `-- Linting passed for Cslib.`
- `lake exe lint-style` (text linter): produces no output for either directory

**Confidence**: High (direct execution)

---

### Finding 3: In-Docstring TODO Tag

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`, line 275

```
/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
def Theory.Derivation.subs {Γ Γ' Δ : Ctx Atom} {B : Proposition Atom}
```

The `TODO:` tag is embedded inside the docstring, not a standalone comment, so `/fix-it` scans would not catch it as a tag. The note documents a known limitation: `subs` is not capture-avoiding (substitution may clash with bound variables). This is a semantic limitation, not merely cosmetic.

**Recommendation**: Extract the TODO into a standalone NOTE/FIX comment below the docstring, or create a task for a capture-avoiding rewrite. At minimum, move it out of the docstring so `/fix-it` can track it.

**Confidence**: High (found directly in source)

---

### Finding 4: Empty Module Docstring in `InferenceSystem.lean`

**File**: `Cslib/Foundations/Logic/InferenceSystem.lean`, line 11

```lean
/-! -/
```

The module-level docstring section header exists but is empty. All other files in `Foundations/Logic/` have substantive module docstrings. `InferenceSystem.lean` defines the core `InferenceSystem` typeclass, `Default` tag, `DerivableIn`, and `Derivable` — these merit a module-level explanation.

**Recommendation**: Add a proper `/-! # Inference System ... -/` module docstring explaining:
- The `InferenceSystem S α` typeclass and `S⇓a` notation
- The `Default` tag for canonical inference systems
- `DerivableIn` vs `Derivable` distinction
- The coercions between derivation trees and derivability propositions

**Confidence**: High (direct inspection)

---

### Finding 5: And/Or Axiom Typeclasses Are Not Bundled Into `*Hilbert` Classes

**Files**: `Cslib/Foundations/Logic/ProofSystem.lean`, `Cslib/Logics/Propositional/ProofSystem/Instances.lean`

`MinimalHilbert`, `IntuitionisticHilbert`, and `ClassicalHilbert` bundle only the implication/bot axioms and MP. The and/or axiom typeclasses (`HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE`) are defined as a separate section with the `[HasAnd F] [HasOr F]` constraint, and each concrete propositional tag (`HilbertCl`, `HilbertInt`, `HilbertMin`) registers them separately.

This means any code working generically over `[ClassicalHilbert S]` cannot use and/or axioms without also importing the separate instances. There is no `PropAndOrHilbert` bundled class.

The docstring for `PropositionalConnectives` in `Connectives.lean` (line 128) explicitly acknowledges this: `"Extending PropositionalConnectives to include [HasAnd/HasOr] is deferred to task 173"`.

**Recommendation**: Once task 173 is resolved (or as part of task 266), consider adding:
```lean
/-- Classical propositional Hilbert system with and/or axioms. -/
class ClassicalAndOrHilbert (S : Type*) [HasBot F] [HasImp F] [HasAnd F] [HasOr F]
    [InferenceSystem S F]
    extends ClassicalHilbert S (F := F),
            HasAxiomAndI S (F := F), HasAxiomAndE1 S (F := F),
            HasAxiomAndE2 S (F := F), HasAxiomOrI1 S (F := F),
            HasAxiomOrI2 S (F := F), HasAxiomOrE S (F := F)
```

This would allow generic theorems about `∧`/`∨` to be stated cleanly.

**Confidence**: High (confirmed by reading ProofSystem.lean and Instances.lean)

---

### Finding 6: `DNE` Axiom Defined but No `HasAxiomDNE` Typeclass

**File**: `Cslib/Foundations/Logic/Axioms.lean`, line 94

```lean
/-- Double negation elimination: ¬¬φ → φ -/
protected abbrev DNE (φ : F) : F :=
  HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot) φ
```

`DNE` exists as an axiom formula in `Axioms.lean` (alongside the other propositional axioms), but `ProofSystem.lean` does not have a corresponding `HasAxiomDNE` typeclass. Instead, DNE is recovered as a derived theorem `double_negation` from `[ClassicalHilbert S]` via `Peirce + EFQ + B-combinator`.

This is internally consistent: Peirce's law is classically equivalent to DNE, and the current design uses Peirce as the axiom and derives DNE. However, the asymmetry (axiom formula defined, no corresponding typeclass) may confuse future contributors.

**Recommendation**: Either:
1. Add a docstring note to `Axioms.DNE` explaining it is defined for completeness but not instantiated as a separate typeclass (DNE is derived from `ClassicalHilbert`), or
2. Add `HasAxiomDNE` as an alternative to `HasAxiomPeirce` with a bridge instance showing equivalence (useful for systems that axiomatize DNE directly rather than Peirce).

**Confidence**: High (confirmed by reading both files)

---

### Finding 7: `FUntilEquiv` / `PSinceEquiv` Are Definitional Identities

**File**: `Cslib/Foundations/Logic/Axioms.lean`, lines 334–341

```lean
/-- F-Until equivalence (BX12): ... trivially F(φ) → F(φ). -/
protected abbrev FUntilEquiv (φ : F) : F :=
  HasImp.imp (HasUntil.untl top' φ) (HasUntil.untl top' φ)

/-- P-Since equivalence (BX12'): ... trivially P(φ) → P(φ). -/
protected abbrev PSinceEquiv (φ : F) : F :=
  HasImp.imp (HasSince.snce top' φ) (HasSince.snce top' φ)
```

Both BX12 and BX12' degenerate to `φ → φ` under the Burgess 1982 convention used in CSLib (where `F φ = ⊤ U φ` and `P φ = ⊤ S φ`). The docstrings acknowledge this ("trivially F(φ) → F(φ)"). The corresponding `HasAxiomFUntilEquiv` and `HasAxiomPSinceEquiv` typeclasses and their instances are trivially satisfied.

This is not a bug; it is a deliberate representation choice. The issue is that these add two typeclasses and four instance registrations (one each in Temporal and Bimodal instances files) for axioms that are tautologies. A design note in the `TemporalBXHilbert` class docstring (currently absent) would help future contributors understand why these are included.

**Recommendation**: Add a note to `TemporalBXHilbert`'s docstring (in `ProofSystem.lean`) explaining that BX12/BX12' are included for source-level fidelity with the Burgess axiom system even though they are trivially provable under the Burgess 1982 `F`/`P` convention used in CSLib.

**Confidence**: High (confirmed by reading Axioms.lean lines 330–341)

---

### Finding 8: `deductionHelpers.lean` Uses `noncomputable` Broadly

**File**: `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean`, lines 83–118

All four generic deduction helpers (`deductionAxiom`, `deductionImpSelf`, `deductionAssumptionOther`, `deductionMpUnderImp`) are marked `noncomputable`. This is expected since they use `Classical.choice` transitively (through `DerivableIn.toDerivation`). However, the module docstring does not note this constraint.

These functions are used across all four proof system levels (PL, Modal, Temporal, Bimodal) to prove concrete deduction theorems.

**Recommendation**: This is acceptable as-is. The `noncomputable` markers are correct. The only improvement would be adding a note in the module docstring that these helpers are noncomputable due to the `Classical.choice` path in `DerivableIn.toDerivation`.

**Confidence**: Medium (noncomputable is correct, not a defect)

---

### Finding 9: `SetDeduction.lean` Imports Mathlib Tactics Not Clearly Needed

**File**: `Cslib/Foundations/Logic/Metalogic/SetDeduction.lean`, lines 10–11

```lean
public import Mathlib.Tactic.SetLike
public import Mathlib.Data.Set.Insert
```

These two Mathlib imports are present. `Mathlib.Data.Set.Insert` provides `Set.mem_insert_iff` and related lemmas which are genuinely used. `Mathlib.Tactic.SetLike` provides the `SetLike` typeclass. Scanning `SetDeduction.lean`, there is no `SetLike` usage; the file only uses plain `Set F` operations. This import may be unnecessary.

**Recommendation**: Run `lake shake` to verify whether `Mathlib.Tactic.SetLike` is actually needed in `SetDeduction.lean`. If not, remove it.

**Confidence**: Medium (SetLike usage not found in the file by grep, but may be transitively required)

---

## Recommended Approach

Prioritized by impact and ease:

1. **(Quick Win)** Fill the empty module docstring in `InferenceSystem.lean` (Finding 4) — 10 lines of documentation.
2. **(Quick Win)** Move the in-docstring TODO in `Basic.lean` line 275 to a standalone tag (Finding 3).
3. **(Documentation)** Add design notes for `DNE` asymmetry (Finding 6) and `FUntilEquiv`/`PSinceEquiv` tautology inclusion (Finding 7).
4. **(Design)** Consider a `ClassicalAndOrHilbert` bundled class (Finding 5) — this would benefit any future generic and/or theorems in Foundations/Logic/.
5. **(Maintenance)** Run `lake shake --fix` to verify the `SetLike` import is needed (Finding 9).

---

## Confidence Level

**High confidence** on all findings (Findings 1–7): directly confirmed by reading source files and running tools.

**Medium confidence** on Findings 8–9: `noncomputable` is clearly correct; the `SetLike` import question requires `lake shake` to confirm.

---

## Evidence

- No sorry output: `grep -rn sorry Cslib/Logics/Propositional/ Cslib/Foundations/Logic/` returns empty
- Lint output: `lake lint` returns `-- Linting passed for Cslib.`
- Style lint: `lake exe lint-style` returns nothing for these directories
- TODO tag: `grep -rn "FIX:\|TODO:\|NOTE:\|QUESTION:"` finds exactly one hit: `Basic.lean:275`
- Empty docstring: `grep -n "^/-\! -\/"` finds `InferenceSystem.lean:11:/-! -/`
- DNE gap: `grep -rn "HasAxiomDNE"` returns empty; `Axioms.DNE` exists at line 94
- And/Or not bundled: `MinimalHilbert`/`IntuitionisticHilbert`/`ClassicalHilbert` `extends` clauses do not include `HasAxiomAndI` etc.; confirmed in `ProofSystem.lean` lines 321–338
