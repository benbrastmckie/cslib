# Teammate A Findings: Git Revert Feasibility for Task 182

## Summary

A commit-level `git revert` strategy is **not recommended**. The commits are too interleaved across tasks and the orchestration commit (6450ad3e) bundles unrelated changes. A **per-file selective revert** using `git show <pre-commit>:<path>` is the recommended strategy.

---

## 1. Commit Map

### Commit Timeline (chronological order)

| Order | Hash | Task | Description |
|-------|------|------|-------------|
| 1 | `8b2a470d` | 173 | Complete implementation (last clean baseline) |
| 2 | `2bb099dc` | 175 | Phase 1: add and/or constructors to Modal.Proposition |
| 3 | `f8852499` | 175 | Phase 2: semantic infrastructure (Denotation, LogicalEquivalence) |
| 4 | `79fdbaeb` | 178 | Complete implementation (references only, no Modal/Temporal/Bimodal) |
| 5 | `de59f56b` | 175 | Phase 3: FromPropositional resolve 2 sorry entries |
| 6 | `abd1aa15` | 176 | Phase 1: Temporal syntax foundation |
| 7 | `2301547b` | 174 | Phase 3: prime theories (Propositional only) |
| 8 | `fa02f2aa` | 175 | Phase 4: proof system axiom constructors |
| 9 | `195dedb2` | 174 | Complete implementation (Propositional only) |
| 10 | `c4e75ad4` | 175 | Phases 5-6: soundness/completeness truth lemmas |
| 11 | `c38fe3d6` | 177 | Phase 1: core syntax layer |
| 12 | `1852de3a` | 177 | Phase 2: proof system layer |
| 13 | `6450ad3e` | orchestration | Massive bundled commit (62 files exclusive to this commit) |
| 14-19 | various | 179-182 | Metadata only, no Lean source changes |

### Pre-Propagation Baseline Commits

| Layer | Last clean commit (no and/or) | Hash |
|-------|-------------------------------|------|
| Modal | Before task 175 phase 1 | `8b2a470d` (parent of `2bb099dc`) |
| Temporal | Before task 176 phase 1 | Parent of `abd1aa15` (which is `de59f56b`) |
| Bimodal | Before task 177 phase 1 | Parent of `c38fe3d6` (which is `c4e75ad4`) |
| Foundations | Before orchestration | `1852de3a` |
| Embeddings | Before orchestration + task 173 phase 7 | `9e83b68b` |

---

## 2. Why Commit-Level Revert Fails

### Problem 1: Interleaving

Tasks 174, 175, 176, 177, 178 are interleaved in the commit history. They were executed in parallel with overlapping files:

- Task 175 (5 commits) modified Propositional/ files that task 174 (2 commits) also modified
- Task 178 sits between task 175 phases 2 and 3
- Task 174 sits between task 175 phases 3 and 4

### Problem 2: The Orchestration Commit (6450ad3e)

This is the critical obstacle. Commit `6450ad3e` contains **62 source files** that were NOT touched by any individual task 175/176/177 commit. It bundles:

- 47 Bimodal files (metalogic, semantics, theorems, decidability, separation)
- 12 Temporal files (metalogic, proof system, semantics)
- 3 Foundations files (Axioms.lean, ProofSystem.lean, TemporalDerived.lean)

Reverting `6450ad3e` as a single commit:
- Conflicts on `specs/TODO.md` and `specs/state.json`
- Would also revert Foundations changes (which should be reverted but need care)
- Would delete research reports and metadata for tasks 174/176/177 (undesirable side effect)

### Problem 3: Task 173 Phase 7

Commit `db2a83bc` (task 173 phase 7) added and/or cases to ALL THREE FromPropositional files:
- `Cslib/Logics/Modal/FromPropositional.lean`
- `Cslib/Logics/Temporal/FromPropositional.lean`
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`

This commit also modified task 173's other files (CI verification). Reverting it wholesale would break task 173's work. The FromPropositional changes were then OVERWRITTEN by tasks 175/176/177 (which switched from Lukasiewicz encoding to native constructor mapping). So reverting just task 175/176/177 without also fixing the task 173 phase 7 changes would leave the FromPropositional files in an inconsistent state.

### Dry-Run Revert Results

| Revert target | Conflicts? | Notes |
|---------------|------------|-------|
| Task 175 (5 commits) | No conflicts | Clean revert of Modal changes only |
| Task 176 (1 commit) | Conflict on specs/plan | Minor, resolvable |
| Task 177 (2 commits) | No conflicts | Clean revert of Bimodal syntax/proof system |
| Orchestration (6450ad3e) | Conflicts on specs/ | Massive scope, would delete research metadata |

Even though individual reverts apply cleanly, they leave the codebase in a broken state because the orchestration commit contains the bulk of the downstream changes (metalogic, soundness, etc.) that depend on the and/or constructors.

---

## 3. Pre-Propagation Formula Types

### Modal.Proposition (pre-task 175, at `8b2a470d`)

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Proposition Atom)
  | box (φ : Proposition Atom)
  deriving DecidableEq, BEq

abbrev Proposition.neg (φ : Proposition Atom) := .imp φ .bot
abbrev Proposition.top : Proposition Atom := .imp .bot .bot
abbrev Proposition.or (φ₁ φ₂ : Proposition Atom) := .imp (.imp φ₁ .bot) φ₂
abbrev Proposition.and (φ₁ φ₂ : Proposition Atom) := .imp (.imp φ₁ (.imp φ₂ .bot)) .bot
```

### Temporal.Formula (pre-task 176, parent of `abd1aa15`)

```lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Formula Atom)
  | untl (φ₁ φ₂ : Formula Atom)
  | snce (φ₁ φ₂ : Formula Atom)
deriving DecidableEq, BEq

abbrev Formula.neg (φ : Formula Atom) := .imp φ .bot
abbrev Formula.top : Formula Atom := .imp .bot .bot
abbrev Formula.or (φ₁ φ₂ : Formula Atom) := .imp (.imp φ₁ .bot) φ₂
abbrev Formula.and (φ₁ φ₂ : Formula Atom) := .imp (.imp φ₁ (.imp φ₂ .bot)) .bot
```

### Bimodal.Formula (pre-task 177, parent of `c38fe3d6`)

```lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Formula Atom)
  | box (φ : Formula Atom)
  | untl (φ₁ φ₂ : Formula Atom)
  | snce (φ₁ φ₂ : Formula Atom)
deriving DecidableEq, BEq

abbrev Formula.neg (φ : Formula Atom) := .imp φ .bot
abbrev Formula.top : Formula Atom := .imp .bot .bot
abbrev Formula.or (φ₁ φ₂ : Formula Atom) := .imp (.imp φ₁ .bot) φ₂
abbrev Formula.and (φ₁ φ₂ : Formula Atom) := .imp (.imp φ₁ (.imp φ₂ .bot)) .bot
```

---

## 4. Cross-Task File Overlap Analysis

### Task 174 (Propositional Metalogic)

- Files: Only `Cslib/Logics/Propositional/Metalogic/` (4 files)
- **Zero overlap** with Modal/, Temporal/, or Bimodal/ directories
- **Safe to ignore** for task 182

### Task 178 (Documentation/References)

- Files: `Cslib/Foundations/Logic/Connectives.lean`, `Cslib/Logics/Propositional/Defs.lean`, `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`, `references.bib`
- **Zero overlap** with Modal/, Temporal/, or Bimodal/ directories
- **Safe to ignore** for task 182

### Task 173 Phase 7 (`db2a83bc`)

- DOES overlap: Modified `FromPropositional.lean` in Modal, Temporal, and Bimodal
- Added and/or cases using Lukasiewicz encoding (`.and` mapped to `imp/bot` pattern)
- Later overwritten by tasks 175/176/177 which mapped `.and` to native `.and`
- **Must be addressed**: After reverting the native constructors, the FromPropositional files need to return to Lukasiewicz-encoding versions

---

## 5. Orchestration Commit (6450ad3e) Breakdown

This commit is the linchpin. It bundles 62 exclusively-new file changes not present in any prior task commit:

### By Directory

| Directory | Files | Nature of Changes |
|-----------|-------|-------------------|
| Bimodal/Metalogic/ | 34 | Soundness cases, completeness truth lemmas, MCS properties, separation theorem, decidability, conservative extension |
| Bimodal/Theorems/ | 5 | Propositional connective theorems, temporal derived, perpetuity |
| Bimodal/Semantics/ | 1 | Truth.lean (and/or satisfaction clauses) |
| Bimodal/Embedding/ | 3 | ModalEmbedding, TemporalEmbedding, PropositionalEmbedding |
| Temporal/Metalogic/ | 7 | Chronicle, completeness helpers, MCS, soundness |
| Temporal/ProofSystem/ | 2 | Axioms, Instances |
| Temporal/Semantics/ | 1 | Satisfies.lean |
| Temporal/FromPropositional | 1 | Embedding with native constructors |
| Foundations/Logic/ | 3 | Axioms (HasAnd/HasOr in temporal section), ProofSystem (TemporalBXHilbert), TemporalDerived |

### Foundations Changes (Must Revert)

The orchestration commit changed Foundations in two ways:

1. **Axioms.lean**: Added `[HasAnd F] [HasOr F]` to the Temporal section variable block. Changed `conj'`/`disj'` (Lukasiewicz helpers) to `HasAnd.and`/`HasOr.or` in BX5, BX5', BX6, BX6', BX7, BX7', BX11, BX11', BX13, BX13' axiom definitions.

2. **ProofSystem.lean**: Added `[HasAnd F] [HasOr F]` to `TemporalBXHilbert` and `BimodalTMHilbert` class declarations.

3. **TemporalDerived.lean**: Minor temporal derived theorem changes.

These Foundations changes are **tightly coupled** to the and/or propagation and must be reverted along with the upper layer changes.

---

## 6. FromPropositional Evolution

### Modal/FromPropositional.lean

| State | `toModal` definition | and/or proof |
|-------|---------------------|--------------|
| Pre-173-ph7 (`9e83b68b`) | 3 cases: atom, bot, imp | No and/or cases (PL had no and/or) |
| Post-173-ph7 (`db2a83bc`) | 5 cases: +and/or using `.and`/`.or` abbrevs | Lukasiewicz encoding; `sorry` in semantic coherence |
| Post-175-ph3 (`de59f56b`) | 5 cases: and/or using native `.and`/`.or` | Direct constructor mapping; full proofs |
| Current | 5 cases: `(.and ...) => .and ...` | Trivial, both types have native constructors |

**Revert target**: Back to Lukasiewicz encoding. The `and` case maps `(.and φ ψ)` to `φ.toModal.and φ.toModal` where `and` is `abbrev ... := .imp (.imp φ (.imp ψ .bot)) .bot`. The semantic coherence proof is straightforward with Peirce's law.

### Temporal/FromPropositional.lean

| State | `toTemporal` definition |
|-------|------------------------|
| Pre-173-ph7 | 3 cases: atom, bot, imp |
| Post-173-ph7 | 5 cases: and/or via explicit `imp/bot` encoding |
| Post-orchestration | 5 cases: and/or via native constructors |

### Bimodal/Embedding/PropositionalEmbedding.lean

Same evolution as Temporal; currently maps PL's `.and` to Bimodal's native `.and`.

---

## 7. Recommended Revert Strategy

### RECOMMENDED: Per-File Selective Revert

**Strategy**: For each file, use `git show <baseline>:<path>` to extract the pre-propagation version, then selectively apply it.

### Concrete Steps

#### Phase A: Formula Type Revert (3 files)

Restore the pre-propagation inductive types from these baseline commits:

| File | Baseline | Method |
|------|----------|--------|
| `Cslib/Logics/Modal/Basic.lean` | `8b2a470d` | `git show 8b2a470d:Cslib/Logics/Modal/Basic.lean` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | Parent of `abd1aa15` | `git show abd1aa15^:Cslib/Logics/Temporal/Syntax/Formula.lean` |
| `Cslib/Logics/Bimodal/Syntax/Formula.lean` | Parent of `c38fe3d6` | `git show c38fe3d6^:Cslib/Logics/Bimodal/Syntax/Formula.lean` |

#### Phase B: Foundations Revert (3 files)

| File | Baseline | Notes |
|------|----------|-------|
| `Cslib/Foundations/Logic/Axioms.lean` | `1852de3a` | Remove `[HasAnd F] [HasOr F]` from Temporal section; restore `conj'`/`disj'` |
| `Cslib/Foundations/Logic/ProofSystem.lean` | `1852de3a` | Remove `[HasAnd F] [HasOr F]` from class declarations |
| `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` | `1852de3a` | Restore pre-orchestration version |

#### Phase C: Embedding Revert (3 files)

| File | Baseline | Notes |
|------|----------|-------|
| `Cslib/Logics/Modal/FromPropositional.lean` | Needs new version | Map PL `.and`/`.or` to Modal abbrevs; prove semantic coherence |
| `Cslib/Logics/Temporal/FromPropositional.lean` | Needs new version | Map PL `.and`/`.or` to Temporal abbrevs |
| `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` | Needs new version | Map PL `.and`/`.or` to Bimodal abbrevs |
| `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` | `1852de3a` | Remove and/or cases from Modal->Bimodal embedding |
| `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` | `1852de3a` | Remove and/or cases from Temporal->Bimodal embedding |

**Note**: FromPropositional files cannot simply revert to pre-173-ph7 baseline because Propositional STILL has native and/or constructors. The embedding must handle 5 PL constructors but map to 3/5/6 upper-layer primitives plus abbreviations.

#### Phase D: Modal Layer Revert (~51 files)

| Directory | Files | Baseline |
|-----------|-------|----------|
| Modal/Denotation.lean | 1 | `8b2a470d` |
| Modal/LogicalEquivalence.lean | 1 | `8b2a470d` |
| Modal/ProofSystem/Instances/*.lean | 15 | `8b2a470d` |
| Modal/Metalogic/DerivationTree.lean | 1 | `8b2a470d` |
| Modal/Metalogic/Completeness.lean | 1 | `8b2a470d` |
| Modal/Metalogic/Systems/*/Soundness.lean | 15 | `8b2a470d` |
| Modal/Metalogic/Systems/*/Completeness.lean | 15 | `8b2a470d` |

All reverted from baseline `8b2a470d`.

#### Phase E: Temporal Layer Revert (~14 files)

All files from parent of `abd1aa15` or `1852de3a` (for orchestration-only files):

| Category | Files | Baseline |
|----------|-------|----------|
| Syntax (Formula, Subformulas) | 2 | Parent of `abd1aa15` |
| Metalogic (7 files) | 7 | `1852de3a` |
| ProofSystem (Axioms, Instances) | 2 | `1852de3a` |
| Semantics/Satisfies | 1 | `1852de3a` |

#### Phase F: Bimodal Layer Revert (~50+ files)

Largest layer. All from parent of `c38fe3d6` or `1852de3a`:

| Category | Files | Baseline |
|----------|-------|----------|
| Syntax (4 files) | 4 | Parent of `c38fe3d6` |
| ProofSystem (3 files) | 3 | Parent of `c38fe3d6` |
| Semantics/Truth | 1 | `1852de3a` |
| Metalogic (34 files) | 34 | `1852de3a` |
| Theorems (5 files) | 5 | `1852de3a` |

---

## 8. Key Baseline Commit Hashes

| Purpose | Hash | Description |
|---------|------|-------------|
| Pre-Modal-propagation | `8b2a470d` | Last commit before any and/or added to Modal |
| Pre-Temporal-propagation (syntax) | `de59f56b` | Parent of task 176 phase 1 |
| Pre-Bimodal-propagation (syntax) | `c4e75ad4` | Parent of task 177 phase 1 |
| Pre-orchestration (metalogic/foundations) | `1852de3a` | Last commit before orchestration bundled changes |
| Pre-all-propagation (FromPropositional original) | `9e83b68b` | Task 173 phase 6, before phase 7 added embedding cases |

---

## 9. Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| FromPropositional semantic coherence proofs | Medium | Straightforward with classical axioms (Peirce's law) |
| Bimodal layer size (50+ files) | Medium | Most files just need match-case removal |
| Foundations Axioms.lean `conj'`/`disj'` restoration | Low | Clean revert from `1852de3a` baseline |
| Subformulas.lean new content | Low | New content (added by 176/177) may need adjustment |
| Post-revert build failures | High | Must verify full `lake build` after each phase |

---

## 10. Estimated Scope

| Phase | Files | Complexity |
|-------|-------|-----------|
| A: Formula types | 3 | Low - direct restore |
| B: Foundations | 3 | Low - direct restore |
| C: Embeddings | 5 | Medium - FromPropositional needs new proofs |
| D: Modal | ~51 | Medium - bulk restore from `8b2a470d` |
| E: Temporal | ~14 | Medium - mixed baselines |
| F: Bimodal | ~50+ | High - largest layer, most complex metalogic |
| **Total** | **~126 files** | |
