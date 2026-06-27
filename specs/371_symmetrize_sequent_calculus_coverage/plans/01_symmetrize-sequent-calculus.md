# Implementation Plan: Task #371

- **Task**: 371 - symmetrize_sequent_calculus_coverage
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/371_symmetrize_sequent_calculus_coverage/reports/01_symmetrize-sequent-calculus.md
- **Artifacts**: plans/01_symmetrize-sequent-calculus.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Close three asymmetries between the classical (LK) and intuitionistic (LJ) propositional
sequent-calculus developments under `Cslib/Logics/Propositional/SequentCalculus/`. Each item is
a new self-contained file that derives its result as a corollary of already-proved theorems
(cut elimination, the completeness bridges, and the existing tableau decision procedure): no new
axioms, no `sorry`. The three items are mutually independent — they touch distinct new files and
only share read access to the two barrel files — so phases 1-3 may be implemented in any order
(or in parallel under a territory contract on `LK.lean`/`LJ.lean`). A final integration phase
wires barrels, regenerates `Cslib.lean`, minimizes imports, and drives the full CI pipeline green.

### Research Integration

The plan transcribes the concrete file directions in the research report verbatim where the
report gives Lean signatures (Item 1 `LJProof.formulas` + `ljCutFreeSubformulaProp`; Item 2
`lkListDeduction{Fwd,Bwd}` + `instDecidableLKDerivable`; Item 3 `lk_cut_free_completeness`).
Source facts re-verified during planning:
- `LKProof.subformula_property` template lives at `LK/SubformulaProperty.lean:255-276`; the
  cut-free core is `cutFreeSubformulaProp` (private, structural induction, vacuous `cut` case).
- `lk_iff_tautology : Tautology φ ↔ Nonempty (LKProof (∅ ⊢ₛ {φ}))` at `LK/Completeness.lean:383`.
- `LKProof.cutElim : Nonempty (CutFreeLKProof seq)` at `LK/CutElimination.lean:839`.
- `instDecidableLJDerivable` (Item-2 template) uses `decidable_of_iff (IValid (ctxToImp Γ A))`
  with `ljProofDeduction{Fwd,Bwd}`; `noncomputable` because `ctxToImp` uses `Finset.toList`.
- All files in this tree use the new module syntax: first line `module`, then `import Cslib.Init`,
  then `public import ...`. Namespace is `Cslib.Logic.PL`. Both barrels are hand-maintained.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Add `LJ/SubformulaProperty.lean` (single-conclusion mirror of the LK subformula property).
- Add `LK/Decidability.lean` (LK derivability decidable via reduction to the classical tautology
  checker, single-succedent `Γ ⊢ₛ {A}`).
- Add `LK/CutFreeCompleteness.lean` with `lk_cut_free_completeness`.
- Register the three files in their barrels; regenerate `Cslib.lean`; full CI green
  (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`). Zero new axioms, no `sorry`.

**Non-Goals**:
- Multi-conclusion (`Γ ⊢ₛ Δ`) LK decidability via `⋁Δ` encoding — explicitly deferred/optional
  per the research report (requires succedent-disjunction inversion; not needed to match LJ).
- Any change to existing LK/LJ proof files, cut-elimination, or completeness theorems.
- New subformula machinery, new implication-encoding, or a new decision procedure (all reused).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Item 2 backward deduction lemma (`lkListDeductionBwd`: `cut`+`impL`+`Finset` set-arithmetic) does not transcribe cleanly | M | M | Copy `ljListDeductionBwd` (`LJ/Decidability.lean:129-161`) and adapt succedent to `{A}`. If blocked, ship the empty-context one-liner fallback `decidable_of_iff (Tautology φ) lk_iff_tautology` (a genuine, correct LK decision instance) and mark the general-context lemma optional. **Never introduce `sorry`.** |
| `noncomputable` propagation in Item 2 | L | M | Mark both LK decision instances `noncomputable` (matches `instDecidableLJDerivable`); do not expect `decide`-style reduction downstream. |
| `Sequent` is a `Prod` abbrev in Item 1 (no named fields) | L | M | Use `seq.1`/`seq.2`; conclusion target is `insert seq.2 seq.1`; `induction d` rebinds `Γ`/`C` per constructor as in LK. |
| Barrel/import drift (new files not in `Cslib.lean`; over-broad imports) | L | M | Add each file to the matching barrel; run `lake exe mk_all --module`, then `lake shake`, `checkInitImports`, `lint-style` in Phase 4. |
| Import collision: `lk_iff_tautology` lives in `Completeness`, not `CutElimination` | L | L | Item 3 file imports **both** `LK.CutElimination` and `LK.Completeness` (kept in its own file to avoid adding a `Completeness` import to `SubformulaProperty.lean`). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |

Phases 1, 2, and 3 are independent (distinct new files; the only shared resources are the two
barrel files, edited in Phase 4) and can execute in parallel under a territory contract. Phase 4
integrates and runs CI, so it depends on all three.

---

### Phase 1: Item 1 — LJ Subformula Property [COMPLETED]

**Goal**: Add the single-conclusion subformula property for LJ as a corollary of
`LJProof.cutElim`, mirroring `LK/SubformulaProperty.lean`.

**Template mirrored**: `Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean`
(`LKProof.formulas:51-62`, `cutFreeSubformulaProp:90-243`, public results `:255-276`).

**Target file**: `Cslib/Logics/Propositional/SequentCalculus/LJ/SubformulaProperty.lean` (new,
~150-200 lines).

**Header** (new module syntax):
```lean
module
import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination
public import Cslib.Logics.Propositional.Subformula
```
`namespace Cslib.Logic.PL`, `open Proposition`, `variable {Atom} [DecidableEq Atom]`.

**Tasks**:
- [ ] Define `LJProof.formulas {seq : @Sequent Atom} : LJProof seq → Finset (Proposition Atom)`
      over the 11 LJ constructors (`ax, botL, andL, andR, orL, orR1, orR2, impL, impR, weakL, cut`):
      leaves `ax`/`botL` give `insert _ Γ`; unary rules pass `d.formulas` through; binary rules
      (`andR, orL, impL, cut`) union the children.
- [ ] `private lemma ljLiftSub {B C tgt} (hmem : C ∈ tgt) (hsub : B.IsSubformula C) :`
      `∃ D ∈ tgt, B.IsSubformula D := ⟨C, hmem, hsub⟩` (one-sided replacement of LK's Left/Right pair).
- [ ] `private lemma ljCutFreeSubformulaProp (d : LJProof seq) (hcf : LJCutFree d) :`
      `∀ B ∈ d.formulas, ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C` by `induction d with`,
      one `rcases` per rule on the conclusion-membership of the IH witness; `cut` case
      `exact absurd hcf id`. Per-case subformula routing (target of conclusion `(Γ,C)` is
      `insert C Γ`): `andL`→`and_left/and_right` into `A∧B ∈ Γ`; `andR`→`A,B` subformulas of
      conclusion `A∧B`; `orR1/orR2`→`or_left/or_right`; `orL`→`A∨B ∈ Γ`; `impL`→`imp_left` (left
      premise), `imp_right` (right premise); `impR`→`imp_left`/`imp_right` on conclusion `A→B`;
      `weakL`→pass through with extra `mem_insert_of_mem`.
- [ ] Public `lemma CutFreeLJProof.subformula_property {Γ : Ctx Atom} {C : Proposition Atom}`
      `(d : CutFreeLJProof (Γ ⊢ C)) : ∀ B ∈ d.val.formulas, ∃ D ∈ insert C Γ, B.IsSubformula D`
      `:= ljCutFreeSubformulaProp d.val d.property`.
- [ ] Public `theorem LJProof.subformula_property (d : LJProof seq) :`
      `∃ d' : CutFreeLJProof seq, ∀ B ∈ d'.val.formulas, ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C`
      via `obtain ⟨d'⟩ := d.cutElim; exact ⟨d', ljCutFreeSubformulaProp d'.val d'.property⟩`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/SubformulaProperty.lean` - create (new file).

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.SubformulaProperty` succeeds, no
  `sorry`/`admit`, no new axioms (spot-check `#print axioms LJProof.subformula_property` →
  only standard axioms).

---

### Phase 2: Item 2 — LK Decidability [IN PROGRESS]

**Goal**: Make LK derivability of `Γ ⊢ₛ {A}` decidable by reduction to the existing classical
tautology checker, mirroring `LJ/Decidability.lean`. Stay single-succedent throughout (no `orR`/
`weakR` inversion).

**Template mirrored**: `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean`
(`ljListDeductionFwd:90`, `ljListDeductionBwd:129`, `ljProofDeduction{Fwd,Bwd}:111,169`,
`instDecidableLJDerivable:189`).

**Target file**: `Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean` (new,
~120-180 lines).

**Header**:
```lean
module
import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LK.Completeness
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability        -- reuse listToImp/ctxToImp
public import Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure     -- instDecidableTautologyTableau
```
`variable {Atom} [DecidableEq Atom] [Hashable Atom]`.

**Tasks**:
- [ ] `def lkListDeductionFwd : ∀ L Γ A, LKProof ((L.toFinset ∪ Γ) ⊢ₛ {A}) →`
      `LKProof (Γ ⊢ₛ {listToImp L A})` — `[]`: `simpa`; `A::As`: `LKProof.impR` + recurse +
      `LKProof.mono` (mirror `ljListDeductionFwd`).
- [ ] `def lkListDeductionBwd : ∀ L Γ A, LKProof (Γ ⊢ₛ {listToImp L A}) →`
      `LKProof ((L.toFinset ∪ Γ) ⊢ₛ {A})` — `A::As`: `LKProof.cut` on `(A → rest)` using
      `LKProof.impL` + `LKProof.ax` (mirror `ljListDeductionBwd:129-161`; result need not be
      cut-free — only `Nonempty` is asserted). **This is the medium-risk lemma — see fallback.**
- [ ] `noncomputable def lkProofDeductionFwd {Γ A} (d : LKProof (Γ ⊢ₛ {A})) :`
      `LKProof (∅ ⊢ₛ {ctxToImp Γ A})` — unfold `ctxToImp`; apply `lkListDeductionFwd`.
- [ ] `noncomputable def lkProofDeductionBwd {Γ A} (d : LKProof (∅ ⊢ₛ {ctxToImp Γ A})) :`
      `LKProof (Γ ⊢ₛ {A})` — symmetric via `lkListDeductionBwd`.
- [ ] `noncomputable instance instDecidableLKDerivable {Γ A} :`
      `Decidable (Nonempty (LKProof (Γ ⊢ₛ {A})))` via
      `decidable_of_iff (Tautology (ctxToImp Γ A))` with the two-direction bridge:
      `mp` uses `lk_iff_tautology.mp` then `lkProofDeductionBwd`; `mpr` uses `lkProofDeductionFwd`
      then `lk_iff_tautology.mpr`.
- [ ] (Optional, low-risk) `noncomputable instance instDecidableDerivableInCPL {Γ A} :`
      `Decidable (DerivableIn (AxiomTheory (@PropositionalAxiom Atom)) (Γ ⊢ A))` via
      `decidable_of_iff (Nonempty (LKProof (Γ ⊢ₛ {A}))) nd_iff_lk.symm`.

**Fallback (if `lkListDeductionBwd` is blocked)**: descope to the empty-context instance — a
guaranteed one-liner that is still a genuine, correct LK decision procedure:
```lean
noncomputable instance {φ : Proposition Atom} :
    Decidable (Nonempty (LKProof (∅ ⊢ₛ {φ}))) :=
  decidable_of_iff (Tautology φ) lk_iff_tautology
```
Ship this and mark the general-context lemma optional. Do **not** introduce `sorry`.

**Timing**: 2 hours (includes the deduction-lemma transcription risk buffer).

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean` - create (new file).

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Decidability` succeeds; no `sorry`,
  no new axioms. If fallback used, the empty-context instance type-checks and the descope is
  noted in the implementation summary.

---

### Phase 3: Item 3 — LK Cut-Free Completeness [COMPLETED]

**Goal**: Add the named corollary `lk_cut_free_completeness` (composition of `lk_iff_tautology.mp`
and `LKProof.cutElim`).

**Template mirrored**: direct 2-line composition; references `CutFreeLKProof` +
`LKProof.cutElim` (`LK/CutElimination.lean:839`) and `lk_iff_tautology` (`LK/Completeness.lean:383`).

**Target file**: `Cslib/Logics/Propositional/SequentCalculus/LK/CutFreeCompleteness.lean` (new,
~15-25 lines). Kept separate so `SubformulaProperty.lean` need not import `Completeness`.

**Header**:
```lean
module
import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination
public import Cslib.Logics.Propositional.SequentCalculus.LK.Completeness
```
`namespace Cslib.Logic.PL`, `variable {Atom} [DecidableEq Atom] [Hashable Atom]` (match the
instance assumptions used by `lk_iff_tautology`).

**Tasks**:
- [ ] `theorem lk_cut_free_completeness {φ : Proposition Atom} (h : Tautology φ) :`
      `Nonempty (CutFreeLKProof (∅ ⊢ₛ ({φ} : Finset _)))` via
      `obtain ⟨d⟩ := lk_iff_tautology.mp h; exact d.cutElim`.
- [ ] (Optional) state the iff `Tautology φ ↔ Nonempty (CutFreeLKProof (∅ ⊢ₛ {φ}))`; backward
      direction `fun ⟨d⟩ => lk_iff_tautology.mpr ⟨d.val⟩`.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutFreeCompleteness.lean` - create (new file).

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutFreeCompleteness` succeeds;
  `#print axioms lk_cut_free_completeness` shows only standard axioms; no `sorry`.

---

### Phase 4: Integration & CI [COMPLETED]

**Goal**: Register the three new files in their barrels, regenerate the top-level import barrel,
minimize imports, and pass the full CSLib CI pipeline.

**Depends on**: 1, 2, 3

**Tasks**:
- [ ] Add to `Cslib/Logics/Propositional/SequentCalculus/LJ.lean`:
      `public import Cslib.Logics.Propositional.SequentCalculus.LJ.SubformulaProperty`.
- [ ] Add to `Cslib/Logics/Propositional/SequentCalculus/LK.lean`:
      `public import Cslib.Logics.Propositional.SequentCalculus.LK.Decidability` and
      `public import Cslib.Logics.Propositional.SequentCalculus.LK.CutFreeCompleteness`
      (note: `LK.lean` already gets `CutElimination` transitively via `SubformulaProperty`).
- [ ] Run `lake exe mk_all --module` to refresh `Cslib.lean`.
- [ ] Run `lake build` (whole-library) — green.
- [ ] Run `lake exe checkInitImports` (every new file begins `import Cslib.Init`).
- [ ] Run `lake exe lint-style`.
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix`; remove any flagged unused
      imports from the three new files and re-build.
- [ ] Run `lake test` (CslibTests suite) — green.

**Timing**: 1 hour

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ.lean` - add SubformulaProperty import.
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` - add Decidability + CutFreeCompleteness imports.
- `Cslib.lean` - regenerated by `mk_all`.

**Verification**:
- All CI commands exit 0. No `sorry`/`admit` across the three new files. No new axioms beyond the
  Lean/Mathlib standard set.

## Testing & Validation

- [ ] `lake build` of each new module individually succeeds (Phases 1-3 checkpoints).
- [ ] Whole-library `lake build` green after barrel + `mk_all` updates (Phase 4).
- [ ] `lake test` green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused imports in new files.
- [ ] No `sorry`/`admit`; `#print axioms` on the three headline results shows only standard axioms.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/LJ/SubformulaProperty.lean` (new)
- `Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean` (new)
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutFreeCompleteness.lean` (new)
- Updated barrels: `LJ.lean`, `LK.lean`; regenerated `Cslib.lean`.
- Implementation summary noting whether Item 2 shipped general-context or empty-context fallback.

## Rollback/Contingency

- Each new file is additive and independent; if any single item fails to build, drop its barrel
  line (and its `mk_all` entry) and ship the remaining items — the three are decoupled.
- Item 2 has a defined descope path (empty-context instance) that keeps the deliverable
  `sorry`-free; prefer descope over any incomplete proof.
- No existing files are modified except the two barrels and the generated `Cslib.lean`, so revert
  is a clean `git checkout` of those plus deletion of the new files.
