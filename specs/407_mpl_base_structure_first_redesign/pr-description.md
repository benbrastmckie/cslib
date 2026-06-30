<!-- ============================================================
HUMAN-AUTHOR-REQUIRED

This file is AI-assisted scaffolding for a new PR body for task 407.
The HUMAN (benbrastmckie) must review, reword, and finalize before
pasting it into the GitHub PR body.

OPEN QUESTIONS — See "## Open questions (resolve before submitting)" below.
These are blocking decisions the AI cannot make. Resolve them before running /pr 407.

Zulip AI policy (msg #605827029, Chris Henson): AI-drafted Zulip prose may not
be posted to Zulip. This document is an internal scaffold; any maintainer
coordination (Zulip thread replies, PR review comments, @-mentions) must be
human-authored.
============================================================ -->

# PR Description — task 407: MPL base structure-first redesign (Waves 1–4)

## Suggested title

`feat(Logics/Propositional): establish MPL as structure-first base with ⊥ as a primitive nullary connective`

---

## Summary

This PR establishes **minimal propositional logic (MPL) as the genuine base** of CSLib's
propositional logic hierarchy, reversing the narrative (but not the machinery) of task-398's
IPL-base framing. The key architectural principle — borrowed from Johansson (1937) — is that
`⊥` is a **primitive nullary connective** in the one fixed language `⟨Atom, ⊥, ∧, ∨, →⟩`
whose meaning is *intentionally underdetermined* in the base logic: it receives a designated
interpretation `bot_val` in each model, with no constitutive proof rule. The IPL explosion
module (`efq`) is an *independently additive* property, not part of the base relation.

**Key changes:**

- Re-frames the ND inductive: the existing task-398 typeclass-gated constructor
  `efq [IsIntuitionistic T]` is now documented and understood as the **explosion property
  module**; MPL is the base relation (option C). Adds `MinimalDerivation` as a theory
  abbreviation and `IsBotRuleFree` as an additive `Prop` predicate on derivations. Zero
  proof churn to existing theorems.
- Introduces a **named semantic bottom-property hierarchy** (`HasLeastBot` mixin over
  Mathlib `OrderBot`): `BrouwerianBot` (free `bot_val`, MPL semantics) and
  `PointedBrouwerian` (leastness constraint, IPL semantics) are wired through this hierarchy.
  Explosion soundness `algEvaluate_imp_bot_eq_top` and IPL-validity lift `algTValid_ipl_of_hasLeastBot`
  are proved relative to `HasLeastBot`, not baked into `OrderBot`.
- Introduces a **generic explosion-parameterized Lindenbaum substrate** (`GenericDCCS`,
  `GenericLindenbaumAlg`, `GenericLindenbaum`) from which `MinLindenbaum` and `IntLindenbaum`
  are re-derived as instances, eliminating approximately 50% of duplicated Min*/Int* closure
  and witness code. `MinStrongCompleteness` and `IntStrongCompleteness` remain sorry-free.
- Delivers a **fragment-genericity spike**: `AlgEvalIndependent P` (abstract
  evaluation-independence property), `isBotFree_eval_independent` and `isOrBotFree_eval_independent`
  as concrete instances, `generic_gha_implies_ha` (generic `GHAValid → HAValid`), and
  `ghaValid_iff_haValid_of_botFree` as one worked conservativity corollary. The fully generic
  `HAValid → Derivable P-logic` requires per-fragment algebraic completeness and is deferred to
  task 410.
- Unifies the **tableau expansion loop** behind a `closurePred : IBranch Atom → Bool`
  parameter: `intuitionisticTableau` and `minimalTableau` are now instances of a single
  `intExpandBranches`/`propExpandBranches` function rather than duplicated code.

The algebraic semantics, Hilbert axiom, conservativity, and completeness layers (MPL/IPL/CPL)
were already structure-first; this PR reifies and documents the implicit structure as
first-class artifacts and eliminates duplication in the metalogic.

**Zero sorries introduced. Zero new axioms. All MPL/IPL/CPL/Modal/Temporal/Bimodal/SequentCalculus completeness chains remain green.**

---

## Modified files

### New files

- `Cslib/Logics/Propositional/Semantics/Algebra/BotProperties.lean`
  — `HasLeastBot` mixin, `instHasLeastBotOrderBot`, explosion soundness and IPL-validity
  corollaries relative to leastness.

- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentGeneric.lean`
  — `AlgEvalIndependent`, concrete instances for `IsBotFree`/`IsOrBotFree`, generic
  `GHAValid → HAValid` and the `ghaValid_iff_haValid_of_botFree` equivalence.

- `Cslib/Logics/Propositional/Metalogic/GenericLindenbaum.lean`
  — `GenericDCCS`, `GenericLindenbaumAlg`, `GenericLindenbaum` explosion-parameterized substrate.

### Modified files

- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
  — Module docstring rewritten (MPL base + gated explosion module; Design A vs B argument;
  Zulip thread reference); `MinimalDerivation` abbreviation and `IsBotRuleFree` predicate added.

- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianBot.lean`
  — `BrouwerianBot` and `PointedBrouwerian` wired through `HasLeastBot`;
  `instHasLeastBotPointedBrouwerian` instance added.

- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`
  — Deductive-closure, consistency, saturation, and Lindenbaum fields derived from
  `GenericLindenbaum`; duplicated Int* code removed.

- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`
  — Same: Min* derivation from generic substrate; duplicated code removed.

- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean`,
  `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean`
  — Threaded through generic substrate; both remain sorry-free.

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
  — `intExpandBranches` parameterized by `closurePred`; `propExpandBranches` alias added;
  `intuitionisticTableau` and `minimalTableau` as instances.

- `Cslib.lean`
  — Three new modules added to the barrel: `BotProperties`, `FragmentGeneric`,
  `GenericLindenbaum`.

**Net diff: 830 insertions, 200 deletions across 11 files.**

---

## Design rationale

### Why `⊥` is primitive (Design A over Design B)

Two alternatives to a primitive nullary `⊥` were considered and rejected:

- **B1 (language-extension)**: a `⊥`-free base type extended with `⊥` for IPL. Rejected
  because it would duplicate the entire formula API (monad/bind, `DecidableEq`, `subst`,
  three evaluators, `FromPropositional` embeddings across Modal/Temporal/Bimodal), and strand
  the existing `MinPropAxiom`/`MPL.hilbert_alg_complete`/conservativity assets which are
  stated with `⊥`.

- **B2 (atom encoding)**: `⊥` as a distinguished atom `⊥ : Atom`. Rejected because every
  substitution theorem would acquire a `σ(⊥) = ⊥` side condition (breaking the free-algebra
  universal property of `Proposition Atom` as the free monad on `{⊥, →, ∧, ∨}`), and would
  strand the existing conservativity results proved via `WithBot`.

The decisive argument for Design A is **substitution invariance**: with `⊥` as a nullary
operation symbol (same kind as `→`, `∧`, `∨`), it is fixed by every substitution and every
scheme is automatically substitution-closed. See Zulip thread #604219492 for the full
free-algebra argument. Design B is documented in the in-source design note
(`NaturalDeduction/Basic.lean` lines 51–114) and in
`specs/407_mpl_base_structure_first_redesign/mpl-base-design-note.md`.

### Why option C for ND reconciliation (not option B)

The task-398 ND inductive carries `efq [IsIntuitionistic T]` as a typeclass-gated constructor.
Three reconciliation options were evaluated:

- **Option A**: keep the gate; re-document as MPL-base. Zero proof churn.
- **Option B**: split ND into a `⊥`-rule-free `MinDerivation` base plus an explosion extension.
  Exact match to the structure-first ideal, but requires re-cutting Curry–Howard and Prawitz
  normalization against the split (the single hard point from task 398). Deferred to task 409.
- **Option C** (adopted): typeclass-property framing as the destination. The `IsIntuitionistic`
  gate *is* the explosion property module; MPL-as-base is *already operationally true* because
  `min_consistent : ¬ Derivable MinPropAxiom ⊥` ensures no `IsIntuitionistic` instance exists
  at minimal strength, making `efq` unconstructible. Only the documentation and abbreviation
  were missing.

Option C was adopted because the design's stated principle — *modularity organized around
properties rather than connectives* — is already satisfied by the `IsIntuitionistic` gate.
The literal `⊥`-rule-free inductive (option B) is the only thing the gate cannot provide;
that is a separable, independently-justifiable engineering cost (task 409).

### `HasLeastBot` over `HasExplosion`

A new `HasExplosion` proof-theoretic class was considered and rejected on the grounds that
`IsIntuitionistic` already is it (Zulip #606970606 discussion). `HasLeastBot` was chosen
as a thin `Prop`-mixin asserting `∀ a, bot_val ≤ a` over an existing Mathlib `OrderBot`
instance, rather than a new structure competing with `OrderBot`. This keeps the semantic
property hierarchy additive and avoids duplicating Mathlib structure.

### Fragment-genericity spike (S3 gate triggered)

The fragment-genericity headline (`AlgEvalIndependent` / generic `GHAValid ↔ HAValid`) was
delivered as a bounded spike with an explicit research-or-defer gate. The gate was triggered:
the mechanism is delivered and one worked instance is proved, but the remaining step —
`HAValid φ → Derivable X-logic φ` for a specific sub-logic `X` — requires per-fragment
algebraic completeness. This is open research, and no `sorry` was introduced. Task 410
is spawned to address it.

---

## Deferred

- **Literal `⊥`-rule-free ND inductive (option B)**: `MinDerivation` base + explosion
  extension, with Curry–Howard/normalization re-cut. Deferred to task 409 (spawned).
- **Minimal sequent calculus (`LM` base)**: define `LM` (no `botL`), prove cut/subformula
  once, route `LJ = LM + botL`. Deferred to task 408 (spawned; high cost).
- **Per-fragment algebraic completeness**: `HAValid φ → Derivable P-logic φ` for a
  parameterized fragment predicate `P`. Deferred to task 410 (spawned).
- **Categorical/initiality layer**: the explicit universal-property witness `0 → A`
  (initial-object semantics for `⊥`). Deferred; only `bot_le` via `OrderBot` is currently
  provided.
- **Connective typeclasses**: any reconciliation with PR #607's `HasNot`/`HasBot` typeclass
  design. Kept independent per Zulip #606970606.

---

## Coordination

**PR #648 (`feat/propositional-v2`)**: This PR builds directly on the propositional
foundation established by #648 (primitive `bot` constructor, `efq`-gated ND). The
`MinimalDerivation` abbreviation and `IsBotRuleFree` predicate added here complement the
`IsIntuitionistic`-gated `efq` constructor shipped in #648. This PR should not be merged
before #648.

**PR #607 (fmontesi, connective typeclasses)**: Connective typeclasses are kept as a
separate development per Zulip #606970606. This PR does not introduce any connective
typeclass or modify `Connectives.lean`. Coordination with #607 is a separate task (task 400).

**Spawned follow-on tasks** (not part of this PR):
- Task 408: Minimal sequent calculus `LM` (high-cost structural item; own task).
- Task 409: Literal `⊥`-rule-free ND inductive (option B); Curry–Howard re-cut.
- Task 410: Per-fragment algebraic completeness for the `AlgEvalIndependent` framework.

**Zulip**: any Zulip replies coordinating this PR with maintainers (Waring, Doty, Henson)
must be human-authored per the AI policy established in msg #605827029. This PR
description was AI-scaffolded and requires human review before posting.

---

## CI verification

All checks run on this branch before PR preparation:

- `lake build`: PASS (3151 jobs, zero errors)
- `lake exe checkInitImports`: PASS
- `lake lint`: PASS for all task-407 modified and new files (pre-existing issues in
  unmodified files: `Rules.lean`, `Saturation.lean`, `Subformula.lean`,
  `DeductionTheorem.lean`, `Termination.lean`, `Soundness.lean`, `DenseMCS.lean`,
  `GenericMCSBridge.lean`)
- `lake exe lint-style`: PASS
- `lake shake --add-public --keep-implied --keep-prefix`: no findings in task-407 files
  (pre-existing findings in unmodified SequentCalculus/Temporal files)
- `lake exe mk_all --module`: PASS for task-407 new files (pre-existing `IntFMPSpike`
  stub issue tracked in task 385)
- `lake test`: PASS (9142/9142 jobs)
- Sorries introduced: **0** (4 pre-existing in `Intuitionistic/Scheme.lean` and
  `Completeness.lean`; many in Bimodal/BXCanonical tracked by tasks 36/37)
- New axioms introduced: **0**

---

## References

- [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
- [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
- [A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*][TroelstraVanDalen1988]
- [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935]
- [M. H. B. Sørensen, P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*][SorensenUrzyczyn2006]
- CSLib Zulip thread on Propositional Logic (topic): substitution-invariance argument (#604219492),
  ND symmetry (#605341190, #606970606), fragment-genericity as the real ask (#606970606),
  AI policy (#605827029)

---

## Open questions (resolve before submitting)

These questions were identified in research report 01 §9 and carry forward to the PR.
**None can be resolved by the agent; each requires a human decision.** Running `/pr 407`
is blocked until these are settled.

1. **ND reconciliation: confirm option C vs. pursue option B now.**
   This PR adopts option C (re-frame the task-398 typeclass gate as the explosion property
   module; zero proof churn). Option B (a literal `⊥`-rule-free `MinDerivation` inductive,
   with Curry–Howard/normalization re-cut) is deferred to task 409 and is *not* included
   here. Confirm this is the intended scope. If option B is wanted now, a different implementation
   branch is required and the summary above must be rewritten substantially.

2. **Scope: is this PR meant to land Waves 1–4 only, or should Waves 5–6 be included?**
   This PR ships Waves 1–4 only. Tasks 408 (LM base, Wave 5) and 409 (option B ND, Wave 6)
   are spawned as separate tasks. Confirm that waves 5–6 remain separate PRs.

3. **Categorical/initiality: include or defer?**
   The explicit initial-object witness (`0 → A` universal-property categorical semantics) is
   not included — only `bot_le` via `OrderBot`. If the broader categorical-semantics programme
   requires this now rather than as a follow-on, the PR scope needs expanding (and task 410
   may need a companion).

4. **Property naming: `HasLeastBot` as shipped — does it match the preferred vocabulary?**
   The PR ships `HasLeastBot` (thin `Prop`-mixin over `OrderBot`) but no `HasDesignatedBot`
   structure (the existing `bot_val` parameter plays that role). `HasExplosion` was not coined
   (`IsIntuitionistic` plays that role). Confirm whether these naming choices align with the
   evolving NOTATION.md / typeclass naming conventions, especially in light of PR #607's
   `HasNot`/`HasBot` design.

5. **Relationship to task 400 / PR #607: is coordination adequate?**
   This PR keeps connective typeclasses entirely out of scope and does not modify
   `Connectives.lean`. Confirm that this stance — deferring to task 400 — is correct, and
   that no in-scope Lean code here conflicts with the connective-typeclass design in #607.

---

## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and extracting files from a development branch to create a clean PR branch
- Running CI verification commands
- Drafting this PR description

All Lean code was written by the author (Benjamin Brast-McKie) and verified to compile
cleanly on the PR branch.
