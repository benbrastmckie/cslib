# Research Report: Drop the Connectives.lean typeclass layer from PR #662 in favor of #607 Operators

- **Task**: 469 — drop_connectives_typeclass_layer_pr_662
- **Type**: cslib
- **Session**: sess_1783022251_1a3cf2
- **Date**: 2026-07-02
- **Status**: researched
- **Agent**: cslib-research-agent

## Executive Summary

The task premise — that `Cslib/Foundations/Logic/Connectives.lean` (introduced by PR #662) is
"unused" and can be dropped in favor of PR #607's `Operators/` hierarchy — **does not hold in the
current working tree**, and a naive deletion would break a large fraction of the CSLib logic stack.
Grep evidence (below) shows the Connectives typeclasses (`HasBot`, `HasImp`, `HasBox`,
`PropositionalConnectives`, `ModalConnectives`) are load-bearing infrastructure consumed by the
entire polymorphic modal/temporal metalogic (`Foundations/Logic/Axioms.lean`,
`ProofSystem.lean`, `Theorems/Modal/*`) and by `Bimodal`, `LTL`, `Temporal`, `Modal`, and
`Propositional`.

The "unused" characterization is **only defensible in the narrow scope of PR #662 as a standalone
diff against `upstream/main`**, where the polymorphic *consumers* were added by later fork commits
(tasks 229/254/260/266/340) and are therefore not part of the #662 changeset.

Critically, **PR #607's Operators hierarchy is NOT a drop-in replacement** and is **not merged**:
- Neither `Connectives.lean` nor `Operators/` exists on `upstream/main` — #607 and #662 are two
  competing, unmerged PRs touching the same area.
- #607 provides **no falsum/`HasBot` class**, **no bundle classes** (`PropositionalConnectives` /
  `ModalConnectives`), uses the name `HasImpl.impl` (not `HasImp.imp`), makes **negation
  primitive** (`HasNot`) rather than `⊥`-derived, and refactors Modal with the **opposite
  primitive set** (`{atom, not, and, diamond}`, diamond primitive) versus #662's
  `{atom, bot, imp, box}`.

**Recommendation**: Do **not** delete `Connectives.lean` in the working tree as a standalone
operation — it would require sorry-free re-proving of the entire modal metalogic against a
hierarchy that does not yet provide the needed abstractions. Mark the deletion interpretation
**[BLOCKED]** pending the prerequisite chain in §6, or **rescope** the task to the PR-coordination
action in §5 (Interpretation A). A concrete migration sketch for both interpretations is provided.

## 1. The Connectives.lean typeclass layer (PR #662)

**File**: `Cslib/Foundations/Logic/Connectives.lean` (working tree, 10,375 bytes; git history:
tasks 340, 266, 260, 254, 229). In the #662 diff it appears as a *new file*
(`pr662.diff` hunk `@@ -0,0 +1,91 @@`, path `Cslib/Foundations/Logic/Connectives.lean`).

**Namespace**: `Cslib.Logic`.

**Contents** (from `pr662.diff` and working tree):
- Atomic classes: `HasBot` (`bot : F`), `HasImp` (`imp : F → F → F`), `HasBox` (`box : F → F`),
  `HasAnd` (`and : F → F → F`), `HasOr` (`or : F → F → F`).
- Bundle classes:
  - `class PropositionalConnectives (F) extends HasBot F, HasImp F` — carries defaulted
    `neg`/`top` fields (task 340).
  - `class ModalConnectives (F) extends PropositionalConnectives F, HasBox F`.
- Design rationale in the module docstring: `⊥` primitive (substitution-invariance argument),
  `neg`/`top` derived; `HasAnd`/`HasOr` independent primitives to support minimal/intuitionistic
  logic.

**Instances registered by #662**:
- `Modal/Basic.lean`: `instance : ModalConnectives (Proposition Atom)` with `bot/imp/box` =
  `.bot/.imp/.box` (working tree lines ~86-89). `Proposition.neg`/`.top` are `abbrev`s delegating
  to `PropositionalConnectives.neg`/`.top` (working tree lines ~90-100).
- `Propositional/Defs.lean` (pr662.diff hunk near line 1032): `instance : PropositionalConnectives
  (Proposition Atom)`, `instance : HasAnd (Proposition Atom)`, `instance : HasOr (Proposition
  Atom)`.

### Is it "unused"? — Evidence says NO (in the working tree)

Grep of the working tree (`grep -rn "HasBox\|ModalConnectives\|..." Cslib/`, excluding
`Connectives.lean`) shows heavy consumption:

| Consumer | Evidence |
|----------|----------|
| `Foundations/Logic/Axioms.lean` | `variable [HasBot F] [HasImp F] [HasBox F]`; axioms K/T/4/5/B/G built from `HasImp.imp`, `HasBox.box`, `HasBot.bot` (lines 140-216, 383-390); also `[HasDia F]`, `[HasUntil F]`. |
| `Foundations/Logic/ProofSystem.lean` | `class Necessitation [HasBox F]` (l.80); ~20 Hilbert-system classes `ModalHilbert`, `ModalS4Hilbert`, `ModalS5Hilbert`, `BimodalTMHilbert`, … all `[HasBot F] [HasImp F] [HasBox F]` (l.361-482). |
| `Foundations/Logic/Theorems/Modal/S5.lean` | ~200 references to `HasBox.box`/`HasImp.imp`/`HasBot.bot` in polymorphic proofs (`variable [HasBot F] [HasImp F] [HasBox F]`, l.61). |
| `Foundations/Logic/Theorems/Modal/Basic.lean` | Polymorphic modal K-theorems over `[HasBox F]` (l.49-188). |
| `Foundations/Logic/Automation/HilbertSearch.lean` | `HasBox.box`/`HasImp.imp` (l.54). |
| `Modal/Basic.lean` | `ModalConnectives` instance + `neg`/`top` abbrevs over `PropositionalConnectives`. |
| `Bimodal/Syntax/Formula.lean` + Metalogic (Soundness, Separation/*, ProofSystem) | `Formula.neg`/`.top` delegate to `PropositionalConnectives.neg`/`.top`; hundreds of `simp only [… PropositionalConnectives.neg, PropositionalConnectives.top …]` calls. |
| `LTL/Semantics/Satisfies.lean`, `Temporal/Syntax/Formula.lean` | import + `PropositionalConnectives.neg/.top`. |
| Module imports | `Bimodal`, `LTL`, `Temporal`, `Modal`, `Propositional/Defs`, `Axioms`, `Metalogic/*`, `Tableau/Branch` all `public import Cslib.Foundations.Logic.Connectives`. |

**Conclusion**: In the working tree, `Connectives.lean` is NOT unused. It is the polymorphic
substrate of the modal Hilbert systems and the shared `neg`/`top` defaults across four logics.
"Unused" is true only if PR #662 is viewed in isolation against `upstream/main`, where the
consumers listed above are not part of the PR.

## 2. The #607 Operators hierarchy

**PR #607** (fmontesi, "feat(Logic): logical operators", state **OPEN**, `mergeStateStatus:
BLOCKED`). Adds `Cslib/Foundations/Logic/Operators/{And,Box,Diamond,Iff,Impl,Not,Or,Tensor}.lean`
plus a `LogicalEquivalence` refactor and Modal/Propositional/CLL instance registration.

**Design** (from `pr607.diff`), all in namespace `Cslib.Logic`, one class per file with
class-attached scoped notation:

| Class | Method | Notation |
|-------|--------|----------|
| `HasAnd` | `and (a b : α) : α` | `infixr:36 " ∧ "` |
| `HasOr` | `or` | `infixr:30 " ∨ "` |
| `HasImpl` | `impl (a b : α) : α` | `infixr:25 " → "` |
| `HasNot` | `not (a : α) : α` | `notation:max "¬" p:40` |
| `HasBox` | `box (a : α) : α` | `prefix:40 "□"` |
| `HasDiamond` | `diamond` | `prefix:40 "◇"` |
| `HasIff` | `iff` | `infixr:20 " ↔ "` |
| `HasTensor` | `tensor` | `infixr:35 " ⊗ "` |

**Key structural gaps vs. Connectives.lean**:
1. **No `HasBot`/falsum class** and no `HasTop`. #607 instead offers `instance [Bot Atom] :
   HasNot (Proposition Atom) := {not := Proposition.neg}` — negation is primitive at the class
   level; `⊥` handling relies on Mathlib `Bot`/`Top` on `Atom`, not a logical-falsum typeclass.
2. **No bundle classes** — no `PropositionalConnectives`/`ModalConnectives`. Each formula type
   registers individual `HasX` instances.
3. **Naming**: `HasImpl.impl`, not `HasImp.imp`. (#662's description explicitly notes this
   `imp` vs `impl` divergence and the `impE` elimination-rule alignment argument.)
4. **Notation lives on the class** (polymorphic across all instances), whereas Connectives keeps
   notation per formula type.
5. **Opposite Modal primitives**: #607 keeps `Modal.Proposition = {atom, not, and, diamond}`
   (diamond primitive; `or/impl/iff/box` derived — `box φ := ¬◇¬φ`). #662 uses
   `{atom, bot, imp, box}` (box primitive; diamond derived). PR #662's own description states the
   constructor refactor is "structurally incompatible with #607's current instances."

**Does #607 subsume Connectives?** No. It covers the *notation-class* role for
`∧ ∨ → ¬ □ ◇ ↔ ⊗`, but it does not provide (a) a falsum typeclass, (b) bundles, (c) the `imp`
naming used by `impE` across Bimodal/Temporal, (d) `HasUntil`/`HasDia` as consumed by
`Axioms.lean`/`ProofSystem.lean`, or (e) the `neg`/`top` class defaults relied on by four logics.

## 3. Migration path

Two coherent interpretations, with opposite feasibility.

### Interpretation A — PR-coordination (rescope; viable)
Goal: let PR #662 merge upstream without introducing a foundations typeclass file that competes
with #607. On a **rebased #662 branch** (not the fork main):
1. Remove `Cslib/Foundations/Logic/Connectives.lean` from the #662 changeset and its `Cslib.lean`
   entry.
2. In `Modal/Basic.lean` and `Propositional/Defs.lean`, replace the
   `ModalConnectives`/`PropositionalConnectives`/`HasAnd`/`HasOr` instance registrations and the
   `PropositionalConnectives.neg`/`.top` delegations with **direct** `def`/`abbrev` definitions +
   per-type scoped notation (the pre-#648 style), OR make them depend on #607's Operators once
   #607 lands.
3. Coordinate `imp` vs `impl` naming and box-vs-diamond primitive with reviewers (open item on
   both PRs).
This is a **PR-branch** action; it does not touch the fork's downstream metalogic because that
metalogic is not in PR #662.

### Interpretation B — delete from the working tree (NOT viable as deletion)
To actually remove `Connectives.lean` from the fork main you must **migrate every consumer** in §1
to #607's Operators. This requires, at minimum:
1. #607 merged (or vendored) — currently absent from `upstream/main`.
2. #607 extended with a falsum/`HasBot` class (or a redesign of `Axioms.lean`/`ProofSystem.lean`
   to avoid `HasBot.bot`), plus `HasUntil`/`HasDia` equivalents.
3. Bundle replacements or rewrite of `PropositionalConnectives.neg`/`.top` defaults consumed by
   `Bimodal`/`LTL`/`Temporal` (hundreds of `simp only [PropositionalConnectives.neg/.top]` sites).
4. Rename reconciliation `HasImp.imp` → `HasImpl.impl` across `Axioms.lean`, `ProofSystem.lean`,
   `Theorems/Modal/*`, `HilbertSearch.lean` (~hundreds of call sites).
5. Sorry-free re-verification of the entire modal Hilbert/S5 theorem stack under the new classes.
This is a multi-file, multi-logic refactor, not a deletion, and cannot be completed while #607 is
unmerged and lacks the needed abstractions.

## 4. Reuse check (CSLib reuse-first)

- `Foundations/Logic/Connectives.lean` already IS the reused abstraction — it is the shared
  connective layer across Propositional/Modal/Bimodal/Temporal/LTL. Removing it removes reuse.
- `#607/Operators` is the *proposed* replacement abstraction but is incomplete (no `HasBot`, no
  bundles) and unmerged. It cannot yet be reused as a substitute.
- No third existing abstraction in `Foundations/` covers falsum-as-primitive + bundles. New
  definitions are therefore NOT recommended; the correct move is coordination between #607 and
  #662, not new code.

## 5. Risks / blockers

1. **[BLOCKER] Connectives is load-bearing** — deletion from the working tree breaks
   `Axioms.lean`, `ProofSystem.lean`, `Theorems/Modal/*`, `HilbertSearch.lean`, and the
   `neg`/`top` defaults used by Bimodal/LTL/Temporal. (Evidence: §1 table.)
2. **[BLOCKER] #607 not merged** — `Operators/` is absent from `upstream/main`
   (`git cat-file -e upstream/main:…/Operators/Box.lean` → ABSENT); #607 state OPEN, BLOCKED.
3. **[BLOCKER] #607 lacks required abstractions** — no `HasBot`, no bundles, no `HasUntil`/`HasDia`
   as consumed by the fork metalogic.
4. **[CONFLICT] Naming** — `HasImp.imp` (fork/#648/#662) vs `HasImpl.impl` (#607); unresolved on
   both PRs. Affects `impE` elimination-rule naming across Bimodal/Temporal.
5. **[CONFLICT] Primitive choice** — #662 `{bot, imp, box}` vs #607 `{not, and, diamond}` for
   `Modal.Proposition`; structurally incompatible per #662's own description.
6. **[PROCESS] Both PRs unmerged and overlapping** — coordination decision (which hierarchy wins)
   is a maintainer/reviewer call, not a mechanical edit.

## 6. Recommendation

- **Do not** perform a standalone deletion of `Connectives.lean` in the working tree. Under the
  zero-debt policy this cannot be completed sorry-free without the prerequisite chain below, so the
  literal "drop" interpretation should be marked **[BLOCKED]** for user review.
- **Prerequisite chain to unblock Interpretation B**: (1) #607 merged; (2) #607 gains `HasBot` +
  bundle equivalents + `HasUntil`/`HasDia`; (3) `imp`/`impl` and bot/not-primitive decisions
  settled; (4) planned migration of the five foundation files + Bimodal/LTL/Temporal with full
  re-verification.
- **Preferred near-term action (Interpretation A)**: rescope task 469 to *decouple PR #662 from the
  foundations typeclass file on its PR branch* (define Modal notation directly, defer the
  typeclass-layer decision to a joint #607/#662 coordination PR). This unblocks #662's upstream
  review without destabilizing the fork's downstream metalogic.
- Escalate the imp/impl and box/diamond primitive decisions to the #607/#662 reviewers before any
  code change.

### Zero-debt / lint notes
No `sorry`/axiom shortcuts are proposed. The report explicitly declines the deletion because it
cannot be done sorry-free today. Any Interpretation-A edits must preserve docstrings on new/changed
declarations (docBlame), keep lowerCamelCase names, and re-verify `@[simp]` LHS for any relocated
reduction lemmas.

## References
- `pr662.diff` (`gh pr diff 662 --repo leanprover/cslib`): `Connectives.lean` new-file hunk;
  `Modal/Basic.lean` `ModalConnectives` instance; `Propositional/Defs.lean` `PropositionalConnectives`/`HasAnd`/`HasOr` instances.
- `pr607.diff` (`gh pr diff 607 --repo leanprover/cslib`): `Operators/{And,Box,Diamond,Iff,Impl,Not,Or,Tensor}.lean`; Modal `{atom,not,and,diamond}` refactor; `HasNot`/`HasImpl` naming; no `HasBot`.
- Working tree: `Cslib/Foundations/Logic/{Connectives,Axioms,ProofSystem}.lean`,
  `Cslib/Foundations/Logic/Theorems/Modal/{Basic,S5}.lean`, `Cslib/Logics/Modal/Basic.lean`,
  `Cslib/Logics/{Bimodal,LTL,Temporal}/…`.
- Merge state: `upstream/main` lacks both `Connectives.lean` and `Operators/` (git cat-file).
