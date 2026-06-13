# Research Report: Task #186

**Task**: hilbert_nd_equivalence_refactor
**Date**: 2026-06-13
**Mode**: Team Research (4 teammates)

- **Started**: 2026-06-13T00:00:00Z
- **Completed**: 2026-06-13T00:00:00Z
- **Effort**: Team research (4 teammates, standard mode)
- **Dependencies**: Task 185 (propositional foundations quality audit)
- **Sources/Inputs**:
  - `specs/186_hilbert_nd_equivalence_refactor/reports/01_teammate-a-findings.md` (Primary approach: context-based equivalence architecture)
  - `specs/186_hilbert_nd_equivalence_refactor/reports/01_teammate-b-findings.md` (Alternative approaches: EFQ-free ndToHilbert, structure bundling)
  - `specs/186_hilbert_nd_equivalence_refactor/reports/01_teammate-c-findings.md` (Critic: List/Finset round-trip, AxiomTheory vs MPL, semantic issues)
  - `specs/186_hilbert_nd_equivalence_refactor/reports/01_teammate-d-findings.md` (Horizons: historical precedent, verified citations)
  - `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (current implementation)
  - `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (ND system)
  - `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` (Hilbert system)
  - `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` (MinPropAxiom/IntPropAxiom/PropositionalAxiom)
  - `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` (deduction theorem)
- **Artifacts**: `specs/186_hilbert_nd_equivalence_refactor/reports/01_team-research.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

---

## Summary

The refactoring is well-scoped and achievable with minimal code changes. The two key findings are: (1) `h_EFQ` is provably unused in `ndToHilbert` — all four teammates independently confirmed this via complete case analysis — so removing it unblocks the minimal logic corollary; (2) both directions of the context-based bridge (`hilbert_to_nd_deriv` and `nd_to_hilbert_deriv`) already exist with full context support, so the context-based `hilbert_iff_nd_ctx` theorem is a one-liner composition of existing lemmas using `Finset.toList_toFinset` as the bridge. The final architecture has one generic context-based theorem with three instantiated corollaries (min/int/cl), subsisting the current closed-context theorems as special cases.

---

## Key Findings

### 1. `h_EFQ` Is Provably Unused in `ndToHilbert` (Unanimous, HIGH Confidence)

All four teammates independently confirmed: `h_EFQ` is passed through recursive calls in `ndToHilbert` but never consumed in any match arm. The structural reason is definitive:

- `Theory.Derivation` has 10 primitive constructors: `ax`, `ass`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `impI`, `impE`.
- `botE` (bottom elimination) is NOT a constructor — it is a derived rule in `DerivedRules.lean` requiring `[IsIntuitionistic T]`.
- Since `botE` is not a constructor, `ndToHilbert`'s pattern match never encounters it.
- When an ND derivation over `AxiomTheory IntPropAxiom` uses `botE`, it expands to `impE (ax (IsIntuitionistic.efq A)) d`, which is handled by the `ax` and `impE` arms — neither of which uses `h_EFQ`.

Complete match arm analysis:

| Arm | Axiom Witnesses Consumed |
|-----|--------------------------|
| `.ax h_mem` | none (constructs `.ax ... (mem_axiomTheory.mp h_mem)`) |
| `.ass h_mem` | none |
| `.andI` | `h_andI` via `hilbertAndI` |
| `.andE1` | `h_andE1` via `hilbertAndE1` |
| `.andE2` | `h_andE2` via `hilbertAndE2` |
| `.orI1` | `h_orI1` via `hilbertOrI1` |
| `.orI2` | `h_orI2` via `hilbertOrI2` |
| `.orE` | `h_K`, `h_S`, `h_orE` via `hilbertOrE` |
| `.impE` | none (direct `modus_ponens`) |
| `.impI` | `h_K`, `h_S` via `deductionTheorem` |

The helper functions called (`hilbertAndI`, `hilbertOrE`, `deductionTheorem`, etc.) also do not use EFQ. Removing `h_EFQ` is a pure deletion with no proof strategy changes.

### 2. Context-Based Equivalence Is a One-Liner (HIGH Confidence)

The canonical statement with Finset as primary context type:

```lean
theorem hilbert_iff_nd_ctx
    {Axioms : PL.Proposition Atom → Prop}
    (h_K ...) (h_S ...) (h_andI ...) (h_andE1 ...) (h_andE2 ...)
    (h_orI1 ...) (h_orI2 ...) (h_orE ...)
    {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv Axioms Γ.toList φ ↔
    DerivableIn (AxiomTheory Axioms : Theory Atom) ((Γ : Ctx Atom) ⊢ φ)
```

**Forward direction**: `hilbert_to_nd_deriv h` produces `DerivableIn ... (Γ.toList.toFinset ⊢ φ)`. The key bridge lemma `Finset.toList_toFinset : s.toList.toFinset = s` rewrites `Γ.toList.toFinset` back to `Γ`. So: `rwa [Finset.toList_toFinset] at this`.

**Backward direction**: `nd_to_hilbert_deriv h_K h_S h_andI ... h` produces `Deriv Axioms Γ.toList φ` directly. No conversion needed.

**Why Finset-as-primary**: Using `Γ : Ctx Atom` (Finset) avoids the `List.toFinset.toList ≠ id` pitfall (duplicates removed, order changed). The round-trip `Finset.toList.toFinset = id` always holds, making the forward direction clean.

The existing closed-context `hilbert_iff_nd` becomes a corollary at `Γ = ∅` since `(∅ : Ctx Atom).toList = []` and `Deriv Axioms [] φ = Derivable Axioms φ`.

### 3. Minimal Logic Corollary (`hilbert_iff_nd_min`) Now Possible (HIGH Confidence)

After removing `h_EFQ`, the simplified `ndToHilbert` requires exactly 8 axiom witnesses: K, S, andI, andE1, andE2, orI1, orI2, orE. These are precisely the constructors of `MinPropAxiom`. Therefore:

```lean
theorem hilbert_iff_nd_ctx_min {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv MinPropAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
```

This was previously blocked because `MinPropAxiom` has no `efq` constructor.

### 4. `AxiomTheory MinPropAxiom` vs `MPL` — Design Clarification (RESOLVED)

Teammate C raised a critical semantic distinction:
- `MPL : Theory Atom := ∅` (empty theory — pure ND with no theory axioms)
- `AxiomTheory MinPropAxiom = {φ | MinPropAxiom φ}` (K, S, and/or axioms as theory members)

These are NOT the same ND theory. However, the task's framework is correct:

**The `AxiomTheory` approach is the right bridge.** The result `Deriv MinPropAxiom Γ.toList φ ↔ DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ φ)` says: "the Hilbert system with MinPropAxiom axioms derives the same formulas as ND augmented with those same axioms as theory axioms." This is exactly what the generic `hilbert_iff_nd` framework provides — a correspondence between two proof systems with the same axiom base.

The deeper result `Derivable MinPropAxiom φ ↔ DerivableIn MPL (∅ ⊢ φ)` (showing the Hilbert axioms are ND-derivable from the primitive rules alone, and vice versa) is a separate, harder theorem that requires additional proofs:
- Forward: K and S axiom schemata are derivable using only the 10 primitive ND rules (no theory axioms)
- Backward: Each primitive ND rule is derivable in the MinPropAxiom Hilbert system (already done in `HilbertDerivedRules.lean`)

This deeper result is OUT OF SCOPE for the current task but could be a follow-up. The `AxiomTheory`-based equivalence is the correct and natural result for the generic framework.

**Recommendation**: Document this distinction in the module docstring. The `AxiomTheory` equivalence is a bridge between two parameterized proof systems sharing the same axiom predicate, not a statement about pure minimal/intuitionistic/classical logic strength.

### 5. Historical Precedent (HIGH Confidence)

**Who proved the equivalence?**
- **Gentzen (1935)**: Introduced both ND (NJ/NK) and sequent calculus. The Hilbert ↔ ND equivalence was implicit, not formally stated as a theorem.
- **Prawitz (1965)**, Chapter I, §1.2: Primary reference. Establishes mutual derivability between Hilbert and ND for classical and intuitionistic logic. Covers closed derivability.
- **Troelstra & van Dalen (1988)**, §10.4: Formally proves N-IPC ≡ H-IPC (intuitionistic case). Most precise reference for the intuitionistic equivalence.
- **van Dalen (2013)**, §2.4: Accessible treatment of the deduction theorem and Hilbert ↔ ND equivalence for classical logic.

**The context-based version** (`Γ ⊢_H φ ↔ Γ ⊢_ND φ`) is NOT explicitly stated in any standard reference. It follows immediately from the closed version plus the deduction theorem. CSLib's formalization should cite it as "a standard consequence of the deduction theorem" rather than claiming novelty.

**Minimal logic**: Johansson (1937) defined minimal logic in Hilbert-style only. The ND formulation is due to Prawitz (1965). No standard reference explicitly states the Hilbert ↔ ND equivalence for minimal logic, but it follows from the same argument.

### 6. Citation Verification and Gaps

**Verified in `references.bib`**: All 6 existing BibKeys confirmed present and correctly formatted: `Johansson1937`, `Prawitz1965`, `TroelstraVanDalen1988`, `Gentzen1935`, `Church1956`, `ChagrovZakharyaschev1997`.

**Missing entries to add**:

| Priority | Reference | BibKey | Purpose |
|----------|-----------|--------|---------|
| HIGH | van Dalen, *Logic and Structure*, 5th ed. (2013) | `vanDalen2013` | Deduction theorem + Hilbert ↔ ND for CPC, §2.4 |
| HIGH | Herbrand, *Recherches sur la théorie de la démonstration* (1930) | `Herbrand1930` | Historical origin of the deduction theorem |
| MEDIUM | Fitting, *Intuitionistic Logic, Model Theory and Forcing* (1969) | `Fitting1969` | Alternative reference for intuitionistic ND |

**`Equivalence.lean` currently cites no external literature** — only internal CSLib files. This must be fixed.

### 7. No Downstream Consumers — Refactoring Is Safe (HIGH Confidence)

Teammate D verified by codebase grep: no file outside `NaturalDeduction/` imports or references `hilbert_iff_nd`, `AxiomTheory`, or `ndToHilbert`. The equivalence module is self-contained. Refactoring (including removing `h_EFQ` from public API signatures) has zero breakage risk.

---

## Synthesis

### Conflicts Resolved

**Conflict 1: Statement form — List-primary vs Finset-primary**
- Teammate A proposed `Γ : Ctx Atom` (Finset) as primary
- Teammate C noted both Option A (List-primary) and Option B (Finset-primary)
- **Resolution**: Finset-primary (`Deriv Axioms Γ.toList φ ↔ DerivableIn ... (Γ ⊢ φ)`) is correct. It avoids the `List.toFinset.toList ≠ id` problem. The round-trip `Finset.toList.toFinset = Finset` always holds via `Finset.toList_toFinset`.

**Conflict 2: Structure bundling vs explicit parameters**
- Teammate B recommended a `HasMinimalConnectiveAxioms` structure bundling 8 witnesses
- Teammate A used explicit parameters throughout
- **Resolution**: Keep explicit parameters for consistency with the existing codebase (`deductionTheorem`, `hilbertOrE`, etc. all use explicit parameters). A structure bundling would be a follow-up ergonomic improvement, not part of this task.

**Conflict 3: AxiomTheory MinPropAxiom vs MPL for minimal logic**
- Teammate C flagged this as a critical semantic mismatch
- **Resolution**: The `AxiomTheory` approach is the correct one for the generic framework. The `Derivable MinPropAxiom φ ↔ DerivableIn MPL (∅ ⊢ φ)` result is a separate, deeper theorem (out of scope). Document the distinction in the module docstring.

### Gaps Identified

1. **`Finset.toList_toFinset` availability**: Need to verify this lemma exists in the current Mathlib version used by CSLib. All teammates assume it exists (it's a standard Mathlib lemma), but it should be confirmed during implementation.

2. **`noncomputable` on `ndToHilbert`**: The function remains `noncomputable` because the `impI` case uses `deductionTheorem`, which uses `Classical.propDecidable`. This is philosophically odd for minimal logic but mathematically correct. Teammate C noted a potentially constructive version exists (since `DecidableEq Atom` is in scope), but this is a deep refactor out of scope.

3. **The `list_cons_mem_finset_insert_toList` bridge lemma**: Currently defined in `Equivalence.lean` but may be unused after refactoring. Check during implementation.

4. **DeductionTheorem.lean has no literature citations**: Task 185 flagged this. Should be addressed as part of this task if touching citation infrastructure.

### Recommendations

**The refactoring decomposes into 3 phases:**

**Phase 1: Remove `h_EFQ` from `ndToHilbert` (mechanical deletion)**
- Remove `h_EFQ` parameter from: `ndToHilbert`, `nd_to_hilbert_deriv`, `hilbert_iff_nd`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`
- Remove `h_EFQ` from all 10 recursive calls within `ndToHilbert`
- Zero proof strategy changes — pure parameter deletion
- Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` to verify

**Phase 2: Add context-based equivalence + minimal logic corollary**
- Add `hilbert_iff_nd_ctx` (generic, 8 axiom witnesses, `Γ : Ctx Atom`)
- Add `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`
- Refactor existing `hilbert_iff_nd`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl` as corollaries of the context versions at `Γ = ∅`
- Update module docstring: context-based versions as primary, closed-context as corollaries

**Phase 3: Literature references and docstring updates**
- Add `vanDalen2013`, `Herbrand1930`, `Fitting1969` to `references.bib`
- Add external literature citations to `Equivalence.lean` module docstring (Prawitz 1965 Ch. I, Troelstra & van Dalen 1988 §10.4)
- Update `Defs.lean` bridge description to mention context-based equivalence
- Document the `AxiomTheory Axioms` vs `MPL`/`IPL`/`CPL` distinction

**Estimated complexity**: LOW. Phase 1 is pure deletion. Phase 2 is ~30 lines of new Lean code. Phase 3 is documentation. Total: ~80 lines changed, ~50 lines added.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary approach: context architecture | completed | high |
| B | Alternatives: EFQ removal, bundling | completed | high |
| C | Critic: round-trip, semantic mismatch | completed | high |
| D | Horizons: citations, strategic direction | completed | high |

## References

- [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965], Chapter I, §1.2
- [A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*][TroelstraVanDalen1988], §10.4
- [G. Gentzen, *Untersuchungen uber das logische Schliessen*][Gentzen1935]
- [I. Johansson, *Der Minimalkalkul*][Johansson1937]
- D. van Dalen, *Logic and Structure*, 5th ed. (2013), §2.4 — **to add to references.bib**
- J. Herbrand, *Recherches sur la theorie de la demonstration* (1930) — **to add to references.bib**
