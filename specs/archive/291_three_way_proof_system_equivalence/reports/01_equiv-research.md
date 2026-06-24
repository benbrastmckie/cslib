# Research Report: Three-Way Proof System Equivalence (Task 291)

## Summary

Task 291 asks for a unifying module that states three-way equivalence (Hilbert, ND, SC) as
`List.TFAE` theorems for MPL, IPL, and CPL. Research confirms that all required bridge
theorems exist for CPL (classical) and IPL (intuitionistic), making those two TFAE
statements purely compositional. MPL (minimal) lacks a sequent calculus entirely — no
minimal SC system exists in CSLib — so the MPL three-way equivalence is blocked. A two-way
MPL equivalence (Hilbert ↔ ND) can still be included.

## 1. Existing Bridge Theorems

### 1.1 Classical Logic (CPL)

All three pairwise bridges exist in the codebase:

| Bridge | Theorem | File | Type |
|--------|---------|------|------|
| Hilbert ↔ ND | `hilbert_iff_nd_ctx_cl` | NaturalDeduction/Equivalence.lean:364 | `Deriv PropositionalAxiom Γ.toList φ ↔ DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ φ)` |
| ND ↔ LK | `nd_iff_lk` | SequentCalculus/LK/Completeness.lean:332 | `DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ A) ↔ Nonempty (LKProof (Γ ⊢ₛ {A}))` |
| Hilbert ↔ LK | `hilbert_iff_lk` | SequentCalculus/LK/Completeness.lean:361 | `Deriv PropositionalAxiom Γ.toList φ ↔ Nonempty (LKProof (Γ ⊢ₛ {φ}))` |

Closed-context forms also exist: `hilbert_iff_nd_cl`, `lk_iff_tautology`.

### 1.2 Intuitionistic Logic (IPL)

All three pairwise bridges exist:

| Bridge | Theorem | File | Type |
|--------|---------|------|------|
| Hilbert ↔ ND | `hilbert_iff_nd_ctx_int` | NaturalDeduction/Equivalence.lean:356 | `Deriv IntPropAxiom Γ.toList φ ↔ DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ φ)` |
| ND ↔ LJ | `nd_iff_lj` | SequentCalculus/LJ/Completeness.lean:248 | `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A) ↔ Nonempty (LJProof (Γ ⊢ A))` |
| Hilbert ↔ LJ | `hilbert_iff_lj` | SequentCalculus/LJ/Completeness.lean:273 | `Deriv IntPropAxiom Γ.toList φ ↔ Nonempty (LJProof (Γ ⊢ φ))` |

Closed-context forms: `hilbert_iff_nd_int`, `lj_iff_ivalid`.

### 1.3 Minimal Logic (MPL)

Only the Hilbert–ND bridge exists:

| Bridge | Theorem | File | Type |
|--------|---------|------|------|
| Hilbert ↔ ND | `hilbert_iff_nd_ctx_min` | NaturalDeduction/Equivalence.lean:348 | `Deriv MinPropAxiom Γ.toList φ ↔ DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ φ)` |

**No minimal sequent calculus (LM) exists in CSLib.** The SequentCalculus directory contains
only LK (classical) and LJ (intuitionistic). There is no `LM` or equivalent for minimal logic.
Consequently, the MPL three-way TFAE is blocked.

## 2. Type Signature Analysis

### 2.1 Context Representations

The three proof systems use different context representations:

- **Hilbert** (`Deriv`): `List (PL.Proposition Atom)` contexts
- **ND** (`DerivableIn`): `Ctx Atom` = `Finset (PL.Proposition Atom)` contexts
- **LK**: `Finset (Proposition Atom)` antecedent, `Finset (Proposition Atom)` succedent
- **LJ**: `Ctx Atom` = `Finset (PL.Proposition Atom)` antecedent, single `Proposition Atom` conclusion

The bridge theorems already handle these conversions:
- Hilbert–ND bridges take `Γ : Ctx Atom` and use `Γ.toList` for the Hilbert side
- LK uses a separate `LKSequent` with `⊢ₛ` notation; the bridge restricts succedent to `{φ}`
- LJ reuses the ND `Sequent` type (`Γ ⊢ A`)

### 2.2 TFAE Propositions

For a TFAE statement over `Γ : Ctx Atom` and `φ : Proposition Atom`:

**CPL TFAE**:
```lean
[Deriv PropositionalAxiom Γ.toList φ,
 DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ φ),
 Nonempty (LKProof (Γ ⊢ₛ {φ}))]
```

**IPL TFAE**:
```lean
[Deriv IntPropAxiom Γ.toList φ,
 DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ φ),
 Nonempty (LJProof (Γ ⊢ φ))]
```

**MPL** (two-way only):
```lean
Deriv MinPropAxiom Γ.toList φ ↔ DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ φ)
```

## 3. Mathlib TFAE Infrastructure

### 3.1 Core API

- `List.TFAE : List Prop → Prop` — states that all propositions in a list are pairwise equivalent
- `tfae_have` tactic — establishes individual implications between numbered items
- `tfae_finish` tactic — closes the TFAE goal once enough implications form a cycle
- `List.TFAE.out : l.TFAE → (n₁ n₂ : ℕ) → a ↔ b` — extracts individual equivalences

### 3.2 Usage Pattern

```lean
theorem foo_tfae : [P, Q, R].TFAE := by
  tfae_have 1 ↔ 2 := iff_theorem_1_2
  tfae_have 2 ↔ 3 := iff_theorem_2_3
  tfae_finish
```

For three items, two pairwise equivalences suffice (1 ↔ 2 and 2 ↔ 3 form a chain).

### 3.3 Required Import

```lean
import Mathlib.Tactic.TFAE
```

This brings in `Mathlib.Data.List.TFAE` and the `tfae_have`/`tfae_finish` tactics.

## 4. Recommended Design

### 4.1 File Location

`Cslib/Logics/Propositional/ProofSystemEquivalence.lean` as specified in the task.

### 4.2 Module Structure

```lean
import Cslib.Init
import Cslib.Logics.Propositional.SequentCalculus.LK.Completeness
import Cslib.Logics.Propositional.SequentCalculus.LJ.Completeness
import Mathlib.Tactic.TFAE

namespace Cslib.Logic.PL

/-! ## Classical Three-Way Equivalence -/

-- Context-based TFAE
theorem cpl_proof_systems_tfae (Γ : Ctx Atom) (φ : Proposition Atom) :
    [Deriv PropositionalAxiom Γ.toList φ,
     DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ φ),
     Nonempty (LKProof (Γ ⊢ₛ ({φ} : Finset _)))].TFAE := by
  tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_cl
  tfae_have 2 ↔ 3 := nd_iff_lk
  tfae_finish

-- Closed-context corollary
theorem cpl_proof_systems_tfae_closed (φ : Proposition Atom) :
    [Derivable PropositionalAxiom φ,
     DerivableIn (AxiomTheory PropositionalAxiom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LKProof (∅ ⊢ₛ ({φ} : Finset _)))].TFAE := by
  -- instantiate cpl_proof_systems_tfae at Γ = ∅ or prove directly
  ...

/-! ## Intuitionistic Three-Way Equivalence -/

theorem ipl_proof_systems_tfae (Γ : Ctx Atom) (φ : Proposition Atom) :
    [Deriv IntPropAxiom Γ.toList φ,
     DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ φ),
     Nonempty (LJProof (Γ ⊢ φ))].TFAE := by
  tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_int
  tfae_have 2 ↔ 3 := nd_iff_lj
  tfae_finish

-- Closed-context corollary
theorem ipl_proof_systems_tfae_closed (φ : Proposition Atom) :
    [Derivable IntPropAxiom φ,
     DerivableIn (AxiomTheory IntPropAxiom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LJProof (∅ ⊢ φ))].TFAE := by
  ...

/-! ## Minimal Two-Way Equivalence -/

-- No TFAE for MPL (no minimal SC exists); include 2-way iff as documentation
theorem mpl_hilbert_iff_nd (Γ : Ctx Atom) (φ : Proposition Atom) :
    Deriv MinPropAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx_min

end Cslib.Logic.PL
```

### 4.3 Key Design Decisions

1. **Parametrize over `Γ : Ctx Atom`** (context-based) as the primary form. This is the
   strongest statement and matches the existing bridge theorem signatures. Closed-context
   corollaries at `Γ = ∅` can be derived.

2. **Use `Deriv`/`Derivable` for Hilbert** (not `SetDerivable`), matching the existing bridge
   theorem types exactly.

3. **Use `DerivableIn` for ND**, which is `Nonempty (Theory.Derivation ...)` via the
   `InferenceSystem` instance.

4. **Use `Nonempty (LKProof ...)` / `Nonempty (LJProof ...)` for SC**, matching the existing
   bridge theorem types.

5. **MPL gets a two-way iff only**, re-exported from `hilbert_iff_nd_ctx_min`. This is a
   design choice to document the gap while still providing value.

6. **Consider adding convenience `TFAE.out` corollaries** for extracting individual
   equivalences, e.g., `cpl_hilbert_iff_lk_from_tfae`, though the existing standalone
   theorems (`hilbert_iff_lk`, etc.) already serve this purpose.

### 4.4 Naming Convention

Following CSLib patterns:
- `cpl_proof_systems_tfae` — classical, context-based
- `ipl_proof_systems_tfae` — intuitionistic, context-based
- `cpl_proof_systems_tfae_closed` — classical, closed context
- `ipl_proof_systems_tfae_closed` — intuitionistic, closed context
- `mpl_hilbert_iff_nd` — minimal, two-way (re-export)

### 4.5 Closed-Context Forms

For the closed-context TFAE, there's a subtlety: `Derivable Axioms φ = Deriv Axioms [] φ`,
but the context-based TFAE uses `Γ.toList` where `Γ : Ctx Atom`. At `Γ = ∅`:
- `(∅ : Ctx Atom).toList = []` — needs `Finset.toList_empty`
- `Derivable Axioms φ = Deriv Axioms [] φ` — definitional

So the closed-context form can be obtained by:
```lean
theorem cpl_proof_systems_tfae_closed ... := by
  have h := cpl_proof_systems_tfae (∅ : Ctx Atom) φ
  simp only [Finset.toList_empty] at h
  exact h
```

## 5. Proof Complexity Assessment

**Difficulty: Very low (purely compositional)**

Each TFAE proof is 3 lines: two `tfae_have` lines establishing pairwise equivalences from
existing theorems, and one `tfae_finish`. The bridges are already proven and have matching
type signatures.

The only potential complication is the `Finset.toList_empty` rewrite for closed-context forms,
which is straightforward.

**Estimated total implementation: ~50-80 lines including module header and docstrings.**

## 6. Blockers and Dependencies

### 6.1 Dependency Status

| Dependency | Status | Impact |
|------------|--------|--------|
| Task 314 (LK) | Implementing | LK code exists and builds; task status may be stale |
| Task 315 (LJ) | Completed | No issues |

The LK code (`Completeness.lean`, `Soundness.lean`, `Basic.lean`, `CutElimination.lean`) all
build with 0 sorries. The task 314 status of "implementing" appears stale — the code is
functionally complete.

### 6.2 MPL Blocker

The MPL three-way TFAE requires a minimal sequent calculus (LM) that does not exist.
Specifically, LJ without `botL` (the ex falso quodlibet rule) would constitute LM, but
this has not been formalized. This is a separate, significant task (new inductive type,
soundness, completeness against Kripke semantics for minimal logic, and bridge theorems).

**Recommendation**: Proceed with CPL and IPL three-way TFAE now. Include MPL as a two-way
iff (Hilbert ↔ ND). Document the LM gap. A future task can add LM and extend the MPL
equivalence to three-way.

### 6.3 No Other Blockers

All required imports build. The TFAE tactic is available from Mathlib. No new definitions
or abstractions are needed — this is pure composition.

## 7. Reuse Check

### 7.1 CSLib Foundations

No existing TFAE or proof-system equivalence infrastructure in `Cslib.Foundations.*`.

### 7.2 Existing Abstractions

All needed abstractions already exist:
- `Deriv` / `Derivable` (Hilbert)
- `DerivableIn` / `AxiomTheory` (ND)
- `LKProof` / `LKSequent` (LK)
- `LJProof` (LJ)
- `Ctx` / `Sequent` (shared)

No new definitions or typeclasses are needed.

### 7.3 Mathlib

`List.TFAE`, `tfae_have`, `tfae_finish` from `Mathlib.Tactic.TFAE` — already available.

## 8. Lint Compliance Notes

- All new theorems need docstrings (`docBlame`)
- Theorem names use `lowerCamelCase` — `cpl_proof_systems_tfae` uses underscores which
  will trigger `defsWithUnderscore`. Consider `cplProofSystemsTfae` instead
- The file must begin with `import Cslib.Init`
- All declarations are `Prop`-valued, so they should use `theorem` not `def` (`defLemma`)

## 9. Tactic Survey

For the TFAE proofs, the only tactics needed are:
- `tfae_have` — establishes pairwise implications
- `tfae_finish` — closes TFAE goal from established implications
- `simp only [Finset.toList_empty]` — for closed-context corollaries
- `exact` — for the MPL re-export

No complex tactic automation (aesop, omega, decide) is needed.
