# Implementation Plan: Task #377

- **Task**: 377 - classical_conjunction_fragment_axioms
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: Task 352 (ClassicalImpAxiom plumbing, completed)
- **Research Inputs**: None (no research report; grounded directly in `FragmentAxioms.lean` sibling blocks)
- **Artifacts**: plans/01_classical-conjimp-axioms.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add the classical conjunction-implication fragment axiom systems to
`Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`, filling the missing classical
middle (CL-A) of the propositional conservativity chain. This is a pure mechanical mirror of the
existing `ConjImpAxiom`, `ConjImpBotAxiom`, and `ClassicalImpAxiom` blocks already in that file:
two new axiom inductives (`ClassicalConjImpAxiom` for CPL⟨∧,→,⊤⟩, `ClassicalConjImpBotAxiom` for
CPL⟨∧,→,⊥,⊤⟩), their subsumption maps, implication witnesses, substitution closure, deduction
theorem instances, and fragment-predicate compatibility lemmas. No new semantics are introduced;
every declaration is a structural reconstruction proof (`cases`-and-rebuild or definitional
witness). Definition of done: the file builds clean with zero debt (no `sorry`, `axiom`, or
vacuous defs) and passes the CSLib CI gate.

### Research Integration

No research report was produced for this task. The implementation is grounded entirely in the
sibling blocks of the target file:
- `ConjImpAxiom` block (lines 48-237) — 5-constructor inductive + `mem_*` + `subst_preserves_*` +
  `isOrBotFree` compat + deduction-theorem instance. Template for `ClassicalConjImpAxiom`.
- `ConjImpBotAxiom` block (lines 246-394) — adds `efq` constructor + `isOrFree` compat. Template
  for `ClassicalConjImpBotAxiom`.
- `ClassicalImpAxiom` block (lines 539-645) — supplies the `peirce` constructor and the
  `peirce_isImpTopOnly` compat shape (to be adapted to `isOrBotFree` / `isOrFree`).
- `Axioms.lean` — `PropositionalAxiom` (the classical target with `peirce`, `efq`, and all and/or
  axioms) and the `*.toPropAxiom` / `MinPropAxiom.toIntPropAxiom` proof shapes.

### Prior Plan Reference

No prior plan for this task. Task 352's plan
(`specs/352_cpl_conservative_over_classical_implicational_fragment/plans/03_classical-imp-conservativity-v3.md`)
established the `ClassicalImpAxiom` plumbing pattern; its Phase 1/2 confirm that the
inductive → witnesses → subst → deduction-theorem sequence builds cleanly and is the validated
ordering reused here.

### Roadmap Alignment

No ROADMAP.md consulted (no `roadmap_path` provided). This task is the SYNTAX layer (CL-A) of the
propositional conservativity chain and **unblocks tasks 378 and 379** (the downstream
conservativity proofs that consume these axiom systems).

## Goals & Non-Goals

**Goals**:
- Define `ClassicalConjImpAxiom` (6 constructors: `implyK, implyS, peirce, andI, andE1, andE2`).
- Define `ClassicalConjImpBotAxiom` (the above + `efq`, 7 constructors).
- Provide subsumption maps: `ConjImpAxiom.toClassicalConjImpAxiom`,
  `ClassicalImpAxiom.toClassicalConjImpAxiom`, `ClassicalConjImpAxiom.toClassicalConjImpBotAxiom`,
  `ClassicalConjImpAxiom.toPropAxiom`, `ClassicalConjImpBotAxiom.toPropAxiom`.
- Provide `mem_implyK` / `mem_implyS` witnesses, `subst_preserves_*` closure lemmas, and
  `*_hasDeductionTheorem` instances for both systems.
- Provide `IsOrBotFree` compat lemmas for `ClassicalConjImpAxiom` and `IsOrFree` compat lemmas for
  `ClassicalConjImpBotAxiom` (one per constructor, including `peirce` and `efq`).
- Build clean with zero proof debt; pass the full CSLib CI gate.

**Non-Goals**:
- No new semantics, no new fragment predicates, no soundness/completeness/conservativity proofs.
- No edits to `Axioms.lean`, `FragmentPredicates.lean`, or downstream task 378/379 files.
- No refactoring of the existing sibling blocks.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `peirce` compat for `IsOrBotFree`/`IsOrFree` has no exact sibling (only `isImpTopOnly` exists) | L | M | Adapt the `classicalImpAxiom_peirce_isImpTopOnly` structure (lines 633-638) swapping `imp_isImpTopOnly` → `imp_isOrBotFree`/`imp_isOrFree`; verify with `lean_goal` before committing |
| `efq` compat uses `Proposition.bot` simp form | L | L | Reuse exact `conjImpBotAxiom_efq_isOrFree` proof (line 384-387): `imp_isOrFree (by simp [Proposition.IsOrFree]) hφ` |
| Namespace placement / `mem_*` resolution in deduction-theorem instances | L | L | Place `mem_*` inside `namespace ClassicalConjImpAxiom`/`ClassicalConjImpBotAxiom` exactly as siblings do; reference as `ClassicalConjImpAxiom.mem_implyK` etc. |
| New declarations break import minimization or style lint | L | L | Run full CI gate in final phase; append blocks after the existing `ClassicalImp` block before the final `end Cslib.Logic.PL` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1 |
| 4 | 4 | 2 |
| 5 | 5 | 1 |
| 6 | 6 | 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Phases 2, 3, and 5 all depend only on the
inductives (Phase 1) and edit disjoint declaration groups in the same file, so they may be
batched into a single agent run if preferred; they are listed separately for clarity of scope.

### Phase 1: Axiom Inductives [NOT STARTED]

**Goal**: Define the two axiom inductive predicates, mirroring `ConjImpAxiom` (+ `peirce` from
`ClassicalImpAxiom`) and `ConjImpBotAxiom` (+ `peirce`).

**Tasks**:
- [ ] Add a `/-! ## ClassicalConjImp Axiom System -/` section after the existing `ClassicalImp`
      block (before `end Cslib.Logic.PL`).
- [ ] Define `inductive ClassicalConjImpAxiom : PL.Proposition Atom → Prop` with constructors
      `implyK`, `implyS`, `peirce`, `andI`, `andE1`, `andE2` (copy constructor signatures verbatim
      from `ConjImpAxiom` lines 60-74 and `ClassicalImpAxiom.peirce` lines 558-560).
- [ ] Define `inductive ClassicalConjImpBotAxiom : PL.Proposition Atom → Prop` with the same six
      constructors plus `efq (φ) : ClassicalConjImpBotAxiom (Proposition.bot.imp φ)` (copy from
      `ConjImpBotAxiom.efq` lines 275-277).
- [ ] Add module-level docstrings on each inductive listing the constructors (mirror existing
      docstring style).

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` - append two `inductive` blocks.

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds with the two new
  inductives present (no proofs yet, so no errors expected).
- `lean_goal` / `lean_hover_info` confirm each inductive has the expected constructor count
  (6 and 7).

---

### Phase 2: Implication Witnesses and Substitution Closure [NOT STARTED]

**Goal**: Add `mem_implyK` / `mem_implyS` witnesses (inside each namespace) and the
`subst_preserves_*` closure lemmas for both systems.

**Tasks**:
- [ ] Add `namespace ClassicalConjImpAxiom` with `mem_implyK` and `mem_implyS` (mirror lines
      113-127); close namespace.
- [ ] Add `namespace ClassicalConjImpBotAxiom` with `mem_implyK` and `mem_implyS` (mirror lines
      305-319); close namespace.
- [ ] Add `subst_preserves_classicalConjImpAxiom` — `cases h` over 6 constructors, rebuilding with
      `.subst f` (mirror `subst_preserves_conjImpAxiom` lines 148-158 plus a `peirce` arm from
      `subst_preserves_classicalImpAxiom` line 608).
- [ ] Add `subst_preserves_classicalConjImpBotAxiom` — 7-constructor version including the `efq`
      arm `| efq a => exact .efq (a.subst f)` (mirror line 335).

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` - add witness namespaces and two
  substitution theorems.

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds.
- `lean_verify` on `subst_preserves_classicalConjImpAxiom` and
  `subst_preserves_classicalConjImpBotAxiom` shows no `sorry`/extra axioms.

---

### Phase 3: Subsumption Maps (toX) [NOT STARTED]

**Goal**: Add the five `toX` subsumption theorems, each a `cases`-and-reconstruct proof.

**Tasks**:
- [ ] `ConjImpAxiom.toClassicalConjImpAxiom` — 5 constructor arms (mirror
      `ConjImpAxiom.toConjImpBotAxiom` lines 282-289).
- [ ] `ClassicalImpAxiom.toClassicalConjImpAxiom` — 3 arms `implyK/implyS/peirce` (mirror
      `ImpAxiom.toClassicalImpAxiom` lines 565-569 with a `peirce` arm).
- [ ] `ClassicalConjImpAxiom.toClassicalConjImpBotAxiom` — 6 arms (5 mirror + `peirce`).
- [ ] `ClassicalConjImpAxiom.toPropAxiom` — 6 arms targeting `PropositionalAxiom` (mirror
      `ClassicalImpAxiom.toPropAxiom` lines 572-577 with the three `and*` arms added).
- [ ] `ClassicalConjImpBotAxiom.toPropAxiom` — 7 arms including `| efq a => exact .efq a`.

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` - add five subsumption theorems
  under `/-! ## ... Subsumption -/` sub-sections.

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds.
- Each `toX` resolves all `cases` arms (no "missing cases" or "unsolved goals").

---

### Phase 4: Deduction Theorem Instances [NOT STARTED]

**Goal**: Add the `hasDeductionTheorem` instances for both systems using the Phase 2 witnesses.

**Tasks**:
- [ ] `classicalConjImpAxiom_hasDeductionTheorem :
      Metalogic.HasDeductionTheorem (propDerivationSystem (@ClassicalConjImpAxiom Atom))` :=
      `hasDeductionTheorem ClassicalConjImpAxiom.mem_implyK ClassicalConjImpAxiom.mem_implyS`
      (mirror lines 235-237).
- [ ] `classicalConjImpBotAxiom_hasDeductionTheorem` — analogous, using the `ClassicalConjImpBotAxiom`
      witnesses (mirror lines 392-394).

**Timing**: 10 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` - add two deduction-theorem
  theorems under `/-! ## ... Deduction Theorem Instance -/` sub-sections.

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds.
- `lean_hover_info` confirms both instances elaborate to the expected `HasDeductionTheorem` type.

---

### Phase 5: Fragment-Predicate Compatibility Lemmas [NOT STARTED]

**Goal**: Add per-constructor fragment-predicate compatibility lemmas — `IsOrBotFree` for
`ClassicalConjImpAxiom`, `IsOrFree` for `ClassicalConjImpBotAxiom`.

**Tasks**:
- [ ] `ClassicalConjImpAxiom` IsOrBotFree compat (mirror `conjImpAxiom_*_isOrBotFree` lines
      175-212): `classicalConjImpAxiom_implyK_isOrBotFree`, `_implyS_`, `_andI_`, `_andE1_`,
      `_andE2_`.
- [ ] `classicalConjImpAxiom_peirce_isOrBotFree {φ ψ} (hφ hψ) :
      (((φ.imp ψ).imp φ).imp φ).IsOrBotFree = true` — adapt `classicalImpAxiom_peirce_isImpTopOnly`
      (lines 633-638) swapping `imp_isImpTopOnly` → `imp_isOrBotFree`.
- [ ] `ClassicalConjImpBotAxiom` IsOrFree compat (mirror `conjImpBotAxiom_*_isOrFree` lines
      342-387): `_implyK_`, `_implyS_`, `_andI_`, `_andE1_`, `_andE2_`, and `_efq_` (reuse the
      `imp_isOrFree (by simp [Proposition.IsOrFree]) hφ` form from line 387).
- [ ] `classicalConjImpBotAxiom_peirce_isOrFree` — `peirce` arm adapted with `imp_isOrFree`.

**Timing**: 25 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` - add compat lemma groups under
  `/-! ## ... Fragment Predicate Compatibility -/` sub-sections.

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds.
- Use `lean_multi_attempt` / `lean_goal` to confirm the `peirce` and `efq` proof terms close their
  goals before finalizing (these two have no exact sibling).

---

### Phase 6: CI Gate [NOT STARTED]

**Goal**: Run the full CSLib CI pipeline and confirm zero proof debt across the new declarations.

**Tasks**:
- [ ] `lake exe cache get` (if needed) then `lake build` — full project compiles.
- [ ] `lake exe checkInitImports` — file still imports `Cslib.Init` (unchanged; existing import).
- [ ] `lake lint` — no new environment-linter warnings (docBlame on all new decls satisfied by
      docstrings).
- [ ] `lake exe lint-style` — text linters pass (or `--fix`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no new unused imports introduced.
- [ ] `lean_verify` on all new top-level declarations — confirm no `sorry`, no added axioms, no
      vacuous defs.

**Timing**: 25 minutes

**Depends on**: 2, 3, 4, 5

**Files to modify**:
- None (verification only); apply lint auto-fixes to `FragmentAxioms.lean` if flagged.

**Verification**:
- Full CI gate green: `lake build`, `checkInitImports`, `lake lint`, `lint-style`, `shake` all
  pass.
- Zero-debt confirmed via `lean_verify` and a `grep` for `sorry`/`admit` in the new blocks.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` after each phase.
- [ ] `lake build` (full project) green at Phase 6.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake lint` reports no new warnings (all new decls have docstrings).
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` introduces no unused-import findings.
- [ ] `lean_verify` shows no `sorry`/`axiom`/vacuous defs on every new declaration.
- [ ] Constructor counts: `ClassicalConjImpAxiom` = 6, `ClassicalConjImpBotAxiom` = 7.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — two new axiom systems with:
  - `inductive ClassicalConjImpAxiom`, `inductive ClassicalConjImpBotAxiom`
  - `ConjImpAxiom.toClassicalConjImpAxiom`, `ClassicalImpAxiom.toClassicalConjImpAxiom`,
    `ClassicalConjImpAxiom.toClassicalConjImpBotAxiom`, `ClassicalConjImpAxiom.toPropAxiom`,
    `ClassicalConjImpBotAxiom.toPropAxiom`
  - `mem_implyK` / `mem_implyS` witnesses (both namespaces)
  - `subst_preserves_classicalConjImpAxiom`, `subst_preserves_classicalConjImpBotAxiom`
  - `classicalConjImpAxiom_hasDeductionTheorem`, `classicalConjImpBotAxiom_hasDeductionTheorem`
  - `classicalConjImpAxiom_*_isOrBotFree` (6 lemmas incl. `peirce`)
  - `classicalConjImpBotAxiom_*_isOrFree` (7 lemmas incl. `peirce`, `efq`)
- plans/01_classical-conjimp-axioms.md (this file)

## Rollback/Contingency

All changes are additive to a single file (`FragmentAxioms.lean`). To revert, delete the appended
`ClassicalConjImp` / `ClassicalConjImpBot` sections (everything after the existing `ClassicalImp`
deduction-theorem instance and before `end Cslib.Logic.PL`), restoring the file to its current
state. No other files are touched, so a single `git checkout -- FragmentAxioms.lean` fully rolls
back the task. If the `peirce`/`efq` compat lemmas resist (Phase 5 risk), mark Phase 5
[BLOCKED] and document the goal state; the inductives, subsumption maps, and deduction-theorem
instances (Phases 1-4) remain independently valid and buildable.
