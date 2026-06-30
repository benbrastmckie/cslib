# Research Report: Rename namespace `Cslib.Logic.PL` -> `Cslib.Logic.Propositional`

- **Task**: 387
- **Session**: sess_1782817543_eee5ae_387
- **Date**: 2026-06-30
- **Agent**: cslib-research-agent
- **Status**: RESEARCHED — task is **HUMAN-GATED / BLOCKED** pending maintainer consensus

## TL;DR

The codebase uses the short namespace `Cslib.Logic.PL` (106 files declare
`namespace Cslib.Logic.PL`), while `ORGANISATION.md:259` specifies the canonical
namespace as `Cslib.Logic.Propositional`. This is a real, confirmed divergence.

Renaming it is a **breaking public API change**: PR #648 cherry-picks the propositional
foundation slice and exposes `Cslib.Logic.PL` publicly (`Defs.lean:78`,
`NaturalDeduction/Basic.lean:121`). Per the AI contribution policy, an agent **MUST NOT**
open the upstream Zulip thread, secure maintainer consensus, or unilaterally perform the
breaking public rename. **A human must drive the Zulip consensus step first.**

This task does **NOT** block the PR #648 foundation cherry-pick. The divergence should be
noted as "pending" in the PR #648 description and the rename executed mechanically only
after a human secures agreement.

## 1. Confirmed Namespace Usage

### 1.1 Declaration form

All declarations use the fully-qualified form `namespace Cslib.Logic.PL`. There are **zero**
occurrences of a short `namespace PL` (verified: `grep -c "^namespace PL"` = 0). The leaf
segment is `PL`, nested under `Cslib.Logic`.

- **Files declaring `namespace Cslib.Logic.PL`**: **106**
- **Files referencing `Cslib.Logic.PL` (qualified string)**: 105 (`.lean` files)
- **Files referencing the `PL` token at all (code + docstrings)**: 135

### 1.2 PR #648 public exposure points (confirmed)

| File | Line | Content |
|------|------|---------|
| `Cslib/Logics/Propositional/Defs.lean` | 78 | `namespace Cslib.Logic.PL` (wraps `inductive Proposition`) |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | 121 | `namespace Cslib.Logic.PL` |

`Defs.lean:78` is the root: `Proposition`, `Proposition.neg`, and the `HasImp`/`HasBot`/
`HasAnd`/`HasOr` instances all live under `Cslib.Logic.PL`. Once PR #648 lands these on
upstream `main`, the `PL` leaf name becomes part of the public API and any rename is breaking
for downstream consumers (internal and any external users).

## 2. ORGANISATION.md Specification (verified)

`ORGANISATION.md`, section **"Namespace Convention"** (lines 254-264), quoted verbatim:

> ## Namespace Convention
>
> The `Cslib.Logic` namespace spans both `Foundations/Logic/` and `Logics/`:
> - `Cslib.Logic.Axioms` -- from `Foundations/Logic/Axioms.lean`
> - `Cslib.Logic.Automation` -- from `Foundations/Logic/Automation/`
> - **`Cslib.Logic.Propositional` -- from `Logics/Propositional/`**
> - `Cslib.Logic.Modal` -- from `Logics/Modal/`
> - `Cslib.Logic.Temporal` -- from `Logics/Temporal/`
> - `Cslib.Logic.Bimodal` -- from `Logics/Bimodal/`
>
> Infrastructure lives in `Foundations/`, specific logics live in `Logics/`, and both share
> the `Cslib.Logic` namespace prefix.

**Conclusion**: ORGANISATION.md unambiguously specifies `Cslib.Logic.Propositional` for
`Logics/Propositional/`. The codebase's actual `Cslib.Logic.PL` leaf is non-conforming. The
rename direction is `PL` -> `Propositional` (leaf segment only; the `Cslib.Logic` prefix is
unchanged).

## 3. Mechanical-Rename Impact Map

The rename is purely the leaf segment `PL` -> `Propositional` inside the `Cslib.Logic`
namespace. Two classes of edits are required.

### 3.1 Class A — Namespace owners (declarations)

**106 files** declaring `namespace Cslib.Logic.PL` need:
`namespace Cslib.Logic.PL` -> `namespace Cslib.Logic.Propositional`
(and the matching `end Cslib.Logic.PL` -> `end Cslib.Logic.Propositional` where present).

These are almost entirely under `Cslib/Logics/Propositional/**` — the full list of 106 is
enumerated in the grep appendix below. Two notable non-Propositional declarers:

| File | Line | Note |
|------|------|------|
| `Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean` | 385 | Opens `namespace Cslib.Logic.PL` to add the `principal_le_algEvaluate` embedding lemma — a Foundations file that contributes into the PL namespace. Must be renamed in lockstep. |
| `Cslib/Logics/Propositional/Defs.lean` | 78 | Root declaration (PR #648 exposure point). |

### 3.2 Class B — Downstream consumers (references)

Files **outside** `Logics/Propositional/` that reference the `PL` leaf in **code** (not just
docstrings). These break if the namespace renames and are not updated together.

#### B.1 Embedding definitions (define `PL.Proposition.to*` members)

| File | Identifiers to update |
|------|----------------------|
| `Cslib/Logics/Modal/FromPropositional.lean` | `PL.Proposition.toModal`, `instCoePLToModal`, `PL.Proposition.toModal_{atom,bot,imp,and,or,neg}`, `PL.Proposition`, `PL.Evaluate`, `PL.Tautology` (~30 refs) |
| `Cslib/Logics/Temporal/FromPropositional.lean` | `PL.Proposition.toTemporal`, `instCoePLToTemporal`, `PL.Proposition.toTemporal_{atom,bot,imp,and,or,neg}`, `PL.Proposition` |
| `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` | `PL.Proposition.toBimodal`, `instCoePLToBimodal`, `PL.Proposition.toBimodal_*`, `PL.Proposition.toModal_toBimodal`, `PL.Proposition.toTemporal_toBimodal`, `PL.Proposition.embedding_commutes`, `PL.Proposition` |

Note: these files *define* members **into** the `PL` namespace (e.g.
`def PL.Proposition.toModal`). After the rename the qualifier becomes
`Propositional.Proposition.toModal` (or they continue via `open Propositional`). All `to*`
member names are unaffected; only the `PL` prefix changes.

#### B.2 Conservative-extension consumers (use `open PL`, `PL.Proposition`, `PL.Derivable`)

| File | Pattern |
|------|---------|
| `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean` | `open PL Cslib.Logic.Modal`; `PL.Proposition`, `PL.Derivable` |
| `Cslib/Logics/Modal/Metalogic/Systems/{K,K4,K5,K45,KB5,B,T,TB,D,D4,D5,D45,DB,S4,S5}/ConservativeExtension.lean` (15 files) | `open PL Cslib.Logic.Modal`; `PL.Proposition`, `PL.Derivable` |
| `Cslib/Logics/Temporal/ConservativeExtension.lean` | `open Temporal Cslib.Logic.Temporal PL`; `PL.Proposition`, `PL.Evaluate` |
| `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` | `open Bimodal ... PL`; `PL.Proposition`, `PL.Evaluate`, `PL.Derivable` |

For every `open PL` / `open ... PL`, replace `PL` with `Propositional`. For every `PL.Foo`
qualified reference, replace `PL.` with `Propositional.`.

#### B.3 Docstring-only references (non-breaking, but should be updated for accuracy)

These reference `PL.*` only in comments/docstrings; they will still compile if missed, but
should be swept for documentation consistency:

- `Cslib/Foundations/Logic/Axioms.lean` (`PL.Proposition` in doc text, lines 52, 62)
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` (`PL.HilbertOf`, `PL/Metalogic/...`)
- `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` (`PL liftDerivationTree`)
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` (`PL.Proposition` in doc text)
- `Cslib/Logics/Modal/Basic.lean` (`PL.Proposition`, `PL.Proposition.toModal` in doc text)

### 3.3 Rename mechanics (once unblocked)

Because the leaf segment `PL` is short and could collide with unrelated tokens, the rename
must be **token-aware**, not a blind `s/PL/Propositional/`:

1. `namespace Cslib.Logic.PL` -> `namespace Cslib.Logic.Propositional` (and matching `end`).
2. `Cslib.Logic.PL` (qualified) -> `Cslib.Logic.Propositional`.
3. `open PL` and `open ... PL ...` -> substitute `PL` token with `Propositional`.
4. `PL.` qualified-identifier prefix -> `Propositional.` (word-boundary anchored on `\bPL\.`).
5. Docstring sweep for `PL.*` and `PL/` path references (B.3).
6. Verify no `instCoePL*` instance *names* are altered (those are identifier names, not
   namespace segments — leave them, or rename to `instCoeProp*` only if desired, but that is
   a separate cosmetic decision, not required by the namespace rename).
7. Full `lake build` + CI pipeline (`lake test`, `lake exe checkInitImports`,
   `lake exe lint-style`, `lake shake`).

Estimated scope: ~106 declarer files + ~21 downstream code consumers + ~5 docstring files
= **~132 files touched**.

## 4. CRITICAL: Human-Gated Blocker

Per the task description and CSLib's AI contribution policy, this rename **requires upstream
maintainer agreement secured via a human-authored Zulip thread BEFORE any mechanical rename**.

The following actions are **OUT OF SCOPE for any AI agent** and must be performed by a human:

1. **Opening / authoring the upstream Zulip thread** proposing `PL` -> `Propositional`.
2. **Securing maintainer consensus** on the breaking public rename.
3. **Deciding the timing** relative to PR #648 landing.

An agent **MUST NOT**:
- Open the Zulip thread or post to upstream channels.
- Perform the mechanical rename before consensus is recorded.
- Land the rename inside PR #648 (it is a separate, breaking, post-consensus change).

**Recommendation**: Mark task 387 **[BLOCKED]** pending the human-driven Zulip consensus.
This report fully documents the rename plan so that, once a human confirms agreement, the
mechanical rename can be executed in a single deterministic pass (Section 3.3) by a
follow-up `/implement`.

## 5. Relationship to PR #648 (non-blocking)

This rename does **NOT** block the PR #648 foundation cherry-pick. PR #648 should:
- Land with the current `Cslib.Logic.PL` namespace as-is.
- **Note the divergence as "pending"** in the PR description: ORGANISATION.md specifies
  `Cslib.Logic.Propositional`; the `PL` leaf is a known non-conformance whose breaking rename
  is deferred to a separate, maintainer-agreed change (task 387).

This avoids coupling a routine foundation slice to a repo-wide breaking rename that needs its
own consensus.

## 6. Reuse / Standards Notes

- This is a rename, not a new abstraction, so the reuse-first protocol is satisfied vacuously
  (no new definitions). The canonical name `Cslib.Logic.Propositional` already exists as the
  documented standard in ORGANISATION.md.
- Zero-debt: the mechanical rename introduces no `sorry`/axioms; it is a pure refactor
  verified by `lake build`. No sorry-deferral patterns apply.
- Lint: renaming a namespace leaf does not introduce new declarations, so docBlame/defLemma
  are not triggered; `dupNamespace` should be re-checked after rename (ensure no declaration
  is named `Propositional.Propositional...`).

## Appendix A: Full list of 106 `namespace Cslib.Logic.PL` declarers

All under `Cslib/Logics/Propositional/**` except
`Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean:385`. Representative roots:
`Defs.lean:78`, `Subformula.lean:43`, `ProofSystem/{Axioms,Derivation,Instances,FragmentAxioms,
FragmentInstances,IntMinInstances}.lean`, `NaturalDeduction/**` (Basic:121, DerivedRules,
HilbertDerivedRules, FromHilbert, Equivalence, AxiomAdmissibility, Normalization/**),
`SequentCalculus/**` (Defs, LJ/**, LK/**), `Tableau/**` (Defs, Classical/**, Intuitionistic/**,
Minimal/**), `Semantics/**` (Bool, Kripke, SemanticConsequence, Algebra + Algebra/** ~35 files),
`Metalogic/**` (MCS, Soundness, *Completeness, *Lindenbaum, Decidability, DeductionTheorem,
GenericMCSBridge, etc.). The exact file:line set is recoverable via:
`grep -rn "namespace Cslib\.Logic\.PL" --include="*.lean" Cslib`.
