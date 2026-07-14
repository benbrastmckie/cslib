# Research Report: Update ORGANISATION.md Propositional Section

- **Task**: 390
- **Session**: sess_1782893182_f5e27d_390
- **Date**: 2026-07-01
- **Agent**: cslib-research-agent
- **Status**: RESEARCHED — implementation is a mechanical documentation edit

## TL;DR

`ORGANISATION.md` has two relevant sections:

1. **Propositional Logic section** (`ORGANISATION.md:97-106`) is a 4-item stub listing only
   `Defs.lean`, `NaturalDeduction/Basic.lean`, `ProofSystem/`, `Metalogic/`. The on-disk tree
   under `Cslib/Logics/Propositional/` has **115 `.lean` files** across 7 major subdirectories.
   This section MUST be rewritten. Exact before/after is in §3.

2. **Namespace Convention section** (`ORGANISATION.md:254-264`) is **already correct**. It was
   fixed by archived task 387 (commit `1845ede5`, "keep Cslib.Logic.PL, fix local
   ORGANISATION.md"). Line 259 already reads `Cslib.Logic.PL -- from Logics/Propositional/
   (the namespace leaf is PL, matching upstream leanprover/cslib)`. No content change is
   required here; an optional one-line clarification is proposed in §4. See §5 for why.

## 1. Current State (verified, file:line)

### 1.1 Propositional Logic section — `ORGANISATION.md:97-106` (verbatim)

```
### Propositional Logic (`Logics/Propositional/`)

​```
Propositional/
├── Defs.lean                  -- Formula type, proof system instances
├── NaturalDeduction/          -- Natural deduction proof system
│   └── Basic.lean
├── ProofSystem/               -- Hilbert-style proof system
└── Metalogic/                 -- Completeness, soundness
​```
```

(The fenced code block occupies lines 99-106. The section header is line 97.)

### 1.2 Namespace Convention section — `ORGANISATION.md:254-264` (verbatim)

```
## Namespace Convention

The `Cslib.Logic` namespace spans both `Foundations/Logic/` and `Logics/`:
- `Cslib.Logic.Axioms` -- from `Foundations/Logic/Axioms.lean`
- `Cslib.Logic.Automation` -- from `Foundations/Logic/Automation/`
- `Cslib.Logic.PL` -- from `Logics/Propositional/` (the namespace leaf is `PL`, matching upstream `leanprover/cslib`)
- `Cslib.Logic.Modal` -- from `Logics/Modal/`
- `Cslib.Logic.Temporal` -- from `Logics/Temporal/`
- `Cslib.Logic.Bimodal` -- from `Logics/Bimodal/`

Infrastructure lives in `Foundations/`, specific logics live in `Logics/`, and both share the `Cslib.Logic` namespace prefix.
```

## 2. On-Disk File Tree (verified via `find Cslib/Logics/Propositional -name '*.lean'`)

Total: **115 files**. Per-subdirectory counts:

| Subdirectory | Files | Notes |
|--------------|-------|-------|
| `SequentCalculus/` | 18 | `Defs.lean` + `LJ/` (8) + `LK/` (9), plus `SequentCalculus.lean`, `LJ.lean`, `LK.lean` aggregators |
| `CurryHoward/` | 3 | `Defs.lean`, `Isomorphism.lean`, `Reduction.lean` |
| `Semantics/` | 36 | 4 top-level + `Algebra/` (32 files) + `Algebra.lean` aggregator |
| `Tableau/` | 17 | `Defs.lean` + `Classical/` + `Intuitionistic/` + `Minimal/` + aggregators |
| `NaturalDeduction/` | 11 | `Basic` + derived-rules + `Normalization/` (4) |
| `Metalogic/` | 18 | Soundness/Completeness/Lindenbaum/MCS + Int/Min/Classical variants |
| `ProofSystem/` | 6 | `Axioms`, `Derivation`, `Instances`, `IntMinInstances`, `Fragment{Axioms,Instances}` |
| top-level `*.lean` | 6 | `Defs.lean`, `Subformula.lean`, `Embedding.lean`, `ProofSystemEquivalence.lean`, `SequentCalculus.lean`, `Tableau.lean` |

Key files called out by the task description, all confirmed present:
- `SequentCalculus/LJ/{Interpolation,CutElimination,SubformulaProperty,Decidability}.lean` ✓
- `SequentCalculus/LK/{Interpolation,CutElimination,SubformulaProperty,Decidability,CutFreeCompleteness}.lean` ✓
- `CurryHoward/{Defs,Isomorphism,Reduction}.lean` ✓
- `Semantics/Algebra/` (32 files): `Brouwerian*.lean`, `Hilbert*.lean`, `Glivenko.lean`,
  `KripkeBridge.lean`, `Conservative*.lean`, `*Conservative*.lean` variants ✓
- `Tableau/{Classical,Intuitionistic,Minimal}/{Completeness,Soundness,DecisionProcedure}.lean` ✓
- `Subformula.lean`, `ProofSystemEquivalence.lean` (top-level) ✓

## 3. Proposed Edit — Propositional Logic section (`ORGANISATION.md:99-106`)

**BEFORE** (replace the fenced block at lines 99-106):

```
Propositional/
├── Defs.lean                  -- Formula type, proof system instances
├── NaturalDeduction/          -- Natural deduction proof system
│   └── Basic.lean
├── ProofSystem/               -- Hilbert-style proof system
└── Metalogic/                 -- Completeness, soundness
```

**AFTER**:

```
Propositional/
├── Defs.lean                   -- Proposition (formula) type, HasImp/HasBot/HasAnd/HasOr instances
├── Subformula.lean             -- Subformula relation
├── Embedding.lean              -- Fragment embeddings (MPL/IPL/CPL)
├── ProofSystemEquivalence.lean -- Equivalence between the proof systems below
├── ProofSystem/                -- Hilbert-style proof system
│   ├── Axioms.lean
│   ├── Derivation.lean
│   ├── Instances.lean          -- Typeclass instances (MinimalHilbert, etc.)
│   ├── IntMinInstances.lean    -- Intuitionistic / minimal instances
│   └── Fragment{Axioms,Instances}.lean
├── NaturalDeduction/           -- Natural deduction proof system
│   ├── Basic.lean
│   ├── DerivedRules.lean, HilbertDerivedRules.lean
│   ├── AxiomAdmissibility.lean, Equivalence.lean, FromHilbert.lean
│   └── Normalization/          -- Normalization + subformula property
│       └── Basic.lean, Reduction.lean, Termination.lean, SubformulaProperty.lean
├── SequentCalculus/            -- Gentzen sequent calculi
│   ├── Defs.lean
│   ├── LJ/                      -- Intuitionistic sequent calculus
│   │   └── Basic, Soundness, Completeness, CutElimination,
│   │       SubformulaProperty, Interpolation, Decidability
│   └── LK/                      -- Classical sequent calculus
│       └── Basic, Soundness, Completeness, CutFreeCompleteness,
│           CutElimination, SubformulaProperty, Interpolation, Decidability
├── Tableau/                    -- Tableau decision procedures
│   ├── Defs.lean
│   ├── Classical/              -- Expansion, Soundness, Completeness, DecisionProcedure
│   ├── Intuitionistic/         -- Rules, Scheme, Expansion, Soundness, Completeness, DecisionProcedure
│   └── Minimal/                -- Soundness, Completeness, DecisionProcedure
├── Semantics/                  -- Semantics
│   ├── Bool.lean               -- Boolean (classical) valuations
│   ├── Kripke.lean             -- Kripke semantics (intuitionistic)
│   ├── SemanticConsequence.lean
│   └── Algebra/                -- Algebraic semantics (Brouwerian/Heyting + Hilbert
│                                  algebras, Glivenko, Kripke bridge, conservativity — 32 files)
└── Metalogic/                  -- Soundness, completeness, decidability
    ├── Soundness.lean, StrongCompleteness.lean, DeductionTheorem.lean, MCS.lean
    ├── Int*.lean, Min*.lean    -- intuitionistic / minimal variants
    ├── Classical*Completeness.lean -- fragment completeness (Imp, ConjImp, ConjImpBot)
    └── Generic{Lindenbaum,MCSBridge}.lean, ConservativityLift.lean
```

Notes for the implementer:
- This mirrors the abbreviated style already used for the Modal/Temporal trees below it
  (representative filenames, brace-grouping for families, not an exhaustive listing).
- Do NOT list all 32 `Semantics/Algebra/` files individually — the parenthetical summary
  matches the density of the surrounding sections. If a fuller listing is wanted, the
  headline families are: `Brouwerian*`, `Hilbert*`, `Glivenko`, `Conservative*` /
  `*Conservative*`, `KripkeBridge`, `Pointed*`, `Fragment*`.
- Preserve the surrounding blank line before `### Modal Logic (Logics/Modal/)` (currently
  line 108).

## 4. Proposed Edit — Namespace Convention section (OPTIONAL)

The section is **already accurate** (line 259 documents `Cslib.Logic.PL`). No change is
strictly required by the current on-disk reality (verified: 105 files declare
`namespace Cslib.Logic.PL`; **zero** files declare or reference `Cslib.Logic.Propositional`).

If the implementer wants to make the directory-vs-leaf distinction more explicit (task 390's
"PL vs Propositional" note), append a single clarifying sentence after line 264:

**Insert after line 264**:

```
Note: the directory is `Logics/Propositional/` but the namespace leaf is `PL` (not
`Propositional`); this matches upstream `leanprover/cslib` and is intentional (see task 387).
Renaming the leaf would be a breaking public-API change.
```

This is optional. If omitted, the section still passes as correct.

## 5. Task 387 Resolution (evidence)

Task 387 ("rename namespace PL -> Propositional") is **archived** at
`specs/archive/387_rename_namespace_pl_to_propositional/`. Its report
(`reports/01_rename-pl-to-propositional.md`) concluded the rename is a breaking public-API
change requiring maintainer Zulip consensus (AI contribution policy forbids an agent from
driving that). Commit `1845ede5` ("task 387: redirect after upstream check — keep
Cslib.Logic.PL, fix local ORGANISATION.md") resolved it by KEEPING `PL` and correcting
`ORGANISATION.md:259` from `Cslib.Logic.Propositional` to `Cslib.Logic.PL`. Therefore the
"PL vs Propositional" divergence flagged in task 390's description is **already resolved** —
task 390 only needs to (a) rewrite the Propositional tree stub, and (b) optionally add the
clarifying note in §4.

## 6. Out of Scope / Do NOT touch

- The Module Dependency Hierarchy diagram (`ORGANISATION.md:80-95`) is accurate; no change.
- The Modal/Temporal/Bimodal tree sections (lines 108-153); no change.
- The "Propositional Embeddings and the Classical-Scope Boundary" section (lines 213-244);
  its file:line references (`Propositional/Defs.lean:89,91`, `Semantics/Kripke.lean:58-130`)
  are unrelated to this task and were not re-verified.
- No Lean source files change. This is a `.md`-only edit. No `lake build` needed.

## 7. Reuse-First / Zero-Debt Compliance

- No new Lean definitions, abstractions, or axioms are introduced (doc-only task) — reuse-first
  and zero-debt gates are trivially satisfied.
- No `sorry`, no CI impact. `lake` pipeline unaffected.

## 8. Definition of Done (for implementation phase)

1. `ORGANISATION.md:99-106` fenced block replaced with the §3 AFTER tree.
2. (Optional) §4 clarifying note appended after line 264.
3. `grep -n "NaturalDeduction/" ORGANISATION.md` shows the expanded subtree; the "4-item
   stub" no longer present.
4. Markdown fences balanced; the `### Modal Logic` header still immediately follows the
   Propositional block with one blank line.
5. No Lean/CI changes.
