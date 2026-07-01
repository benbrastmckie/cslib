# Task 415 — Spawn Manifest (Retrospective)

**Task type**: cslib (task-tracking artifact; internal, not upstream-facing)
**Status**: retrospective — see §0 for why this manifest documents completed work rather than
proposing new tasks.
**Date**: 2026-07-01
**Source**: `reports/01_lifting-audit.md` §8 (Ranks 1-5), §9 (errata), §10 (post-audit update)

---

## 0. Why This Manifest Is Retrospective, Not Prospective

The implementation plan for task 415 (`plans/01_lifting-audit-spawn.md`, Phase 3) originally
called for this manifest to specify five **new** follow-on tasks for the multi-task-creation
standard's interactive-selection-plus-confirmation flow (Phase 4). During Phase 1's evidence
re-verification (2026-07-01), it was discovered that **all five candidates were already spawned**
as child tasks 416-420 (`parent_task: 415`) by a prior orchestration pass (`git` commit
`ce9e3ef8`, "orchestrate tasks 416-420: complete orchestration (4/5 succeeded)"), and **all five
are now `status: completed`** in `specs/archive/state.json` / `specs/state.json`.

This manifest therefore documents the **rank -> task -> outcome** mapping as executed, records
what each child task actually delivered (which in one case — Rank 1/task 416 — differs
substantially from what the report originally scoped), and confirms there is **no residual item
from the original five** requiring new task creation. The task-393 cross-reference (§4 below)
remains the one live, still-`not_started` sibling task that this audit's findings touch but that
415 does not own or need to spawn (393 already exists independently).

**Consequence for Phase 4**: no new tasks are created by this manifest. Nothing requires user
confirmation under the multi-task-creation standard, because nothing new is proposed.

---

## 1. Rank -> Task -> Outcome Table

| Rank | Candidate (report §8) | Child task | Effort (est. -> actual) | Status | Deps / cross-refs |
|---|---|---|---|---|---|
| 1 | Instantiate GenericLindenbaum (closes Finding 3) | **416** `instantiate_generic_lindenbaum_phase6` | M -> **S** (trivial doc fix; code debt pre-closed by task 407 phase 6) | completed | none hard; residual micro-duplication (~40 lines, definitionally-equal closure scaffolding) explicitly left to task 393 |
| 2 | Foundations-level parametric conservativity lift (closes Finding 2) | **417** `parametric_conservativity_lift_foundations` | M -> M | completed | synergistic with 416 (shared `prop_completeness`); none hard |
| 3 | Shared `PropositionalEmbedding` typeclass (supports Finding 1) | **418** `shared_propositional_embedding_typeclass` | S-M -> S-M | completed | none |
| 4 | Cross-logic derivation-lifting spike | **419** `generalize_derivation_lifting_intersystem` | L -> L | completed (forward direction landed; backward/Equiv direction explicitly deferred) | benefited from 417's `Foundations` placement; spun off study task **448** `study_deriv_shared_metatheory_substrate` (also completed, verdict NO-GO on the backward-map extension) |
| 5 | Documentation-only structure-preserving-embedding note | **420** `native_embedding_prerequisites_doc` | S -> S | completed | none |

All five landed at or below their estimated effort. No task in this set is `[BLOCKED]`, contains
a `sorry`, or introduces a new axiom (per each task's own completion record).

---

## 2. Per-Rank Detail

### Rank 1 -> Task 416 (Finding 3)

**What was scoped**: re-derive `MinTheory`/`IntDCCS` as instances of `GenericTheory`, deleting
~270 net duplicated lines and activating a "dormant" 295-line substrate.

**What actually happened**: task 416's own investigation (its report,
`specs/archive/416_instantiate_generic_lindenbaum_phase6/reports/01_generic-lindenbaum-phase6.md`)
established that the re-derivation was **already done** by task 407 phase 6 (commit `9242d243`,
predating this audit's 2026-06-29 verification pass). `MinLindenbaum.lean`/`IntLindenbaum.lean`
already delegate to `generic_deriv_from_closure_to_S`/`generic_deriv_imp_of_union`/
`generic_imp_witness`. The only actionable, in-scope, zero-risk deliverable was fixing a stale
docstring in `GenericLindenbaum.lean:43-52` that still claimed the substrate was "additive...
deferred to Phase 6" — task 416 did exactly this and nothing else, correctly declining to
manufacture unnecessary rework. A residual ~40-line micro-duplication (definitionally-equal
closure-scaffolding defs: `minDeductiveClosure`/`intDeductiveClosure` and friends) was identified
and explicitly left to task 393's umbrella, since those defs are public downstream API consumed
by `MinStrongCompleteness.lean`, `IntStrongCompleteness.lean`, and `IntDecidability.lean` — files
in 393's declared scope.

**Lesson for future audits**: line-count-based duplication estimates (the report's "~565 dup
lines") should be corroborated against whether cited files actually contain duplicated *bodies*
versus thin delegating wrappers of similar total length. This audit's Finding 3 conflated the two.

### Rank 2 -> Task 417 (Finding 2)

Delivered exactly as scoped: `Cslib/Logics/Propositional/Metalogic/ConservativityLift.lean`
(later relocated per a follow-up placement report to its current path) with
`conservative_over_cpl` and `evaluate_iff_of_classicalBridge`; `temporal_conservative_extension`
and `bimodal_conservative_extension` re-expressed as thin instances (files now 74 and 121 lines
respectively, down from their pre-refactor sizes). This directly upgrades report §7's
conservativity-uniformity row from PARTIAL to MET (see report §11).

### Rank 3 -> Task 418 (Finding 1, partial)

Delivered exactly as scoped: `Cslib/Logics/Propositional/Embedding.lean` with the
`PropositionalEmbedding` typeclass and the generic `embed` function (structural on
`atom`/`bot`/`imp`, Łukasiewicz on `and`/`or`), a single limitation note, and an uninstantiated
`NativePropositionalEmbedding` extension point for a future intuitionistic-faithful embedding.
Does **not** itself close Finding 1's open native-embedding gap (by design — see report §3 and
task 420 below).

### Rank 4 -> Task 419 (spike, InterSystem)

Delivered the forward direction: `Foundations/Logic/Metalogic/ProofSystemMorphism.lean`
(`ProofSig`/`Deriv`/`ProofSigHom`/`Deriv.map` + functor laws), with Modal and PL as full `Equiv`s
and Bimodal as a forward map + `HEq` intertwining (`DerivationTree.lift`). The backward-map /
full-`Equiv` extension for multi-closure Bimodal was correctly identified as out of scope for the
spike (representation-change risk) and spun off to study task 448, which concluded **NO-GO**:
`GenericMCS` already provides the load-bearing shared-metatheory substrate at the `Prop` level;
the `Deriv` sigma "Vision B" substrate has no identified proof-theoretic consumer, so the ROI gate
fails. 448's roadmap redirects any future shared-metatheory effort to existing tasks 41 and 415 —
this task (415) has no further action item from that redirect beyond noting it here.

### Rank 5 -> Task 420 (doc-only)

Delivered exactly as scoped: an in-repo design note recording the four prerequisites for a
native, intuitionistic-faithful embedding. No Lean change, as required.

---

## 3. What Remains Genuinely Open (Not Spawned, Not Recommended For Spawning Now)

- **Native intuitionistic-faithful embedding** (report §3, "XL, multi-task, weeks") — correctly
  gated on a future intuitionistic modal/temporal/bimodal logic existing first. Task 420 recorded
  the prerequisites; no further spawn is warranted until that logic exists.
- **Full ND/LJ/LK structural-metatheory unification** (report §6) — explicitly assessed and
  deprioritized in the original report as XL with low value-to-effort; nothing changed this
  verdict during re-verification. Not recommended for spawning.
- **Task 393's own scope** ((a) quotient-Lindenbaum consolidation, (b) `litCtx_congr`
  parameterization, (c) Soundness/conservativity/LJ-LK assessment) — this is a **pre-existing,
  independent task** (`not_started`, depends on task 391), not something 415 spawns. 415's
  contribution is confirming the sibling relationship still holds: task 416 closed the
  deductive-closure Min/Int Lindenbaum axis (with the ~40-line residual left for 393), and task
  417 folds 393's "(c)" conservativity-assessment item into the now-uniform
  `conservative_over_cpl` lift. **No change to 393's dependencies or scope is proposed here** —
  393's owner should simply be aware, when 393 is eventually picked up, that 416/417 already
  narrowed its (a)/(c)-adjacent territory.

---

## 4. Task-393 Cross-Reference (Confirmed Still Valid)

Task 393 (`reuse_consolidation_lindenbaum_classical`, `not_started`, depends on 391,
Zulip-first per CONTRIBUTING) remains the correct home for:
- The residual ~40-line Min/Int closure-scaffolding duplication (identified by task 416, left
  unaddressed by design — see §2 Rank 1 above).
- Its own (a) HilbertLindenbaum/HilbertLindenbaumRel/HilbertAlgCompleteness quotient-Lindenbaum
  consolidation (~2100 lines) — untouched by any of 416-420.
- Its own (b) `litCtx_congr` public-ification and Classical-completeness parameterization
  (~700 lines) — untouched by any of 416-420.
- Its own (c) Soundness/conservativity/LJ-LK assessment — narrowed in scope by task 417's
  `conservative_over_cpl` (the conservativity leg of (c) is now unified rather than needing
  separate assessment across Modal/Temporal/Bimodal).

No dependency edges or description changes to task 393 are made by this task (415); this section
is informational only, for whoever picks up 393 next.

---

## 5. Internal/Upstream Classification

This manifest is an **internal** task-tracking artifact (rank -> task -> outcome mapping,
AI-authored, acceptable for internal use). It contains no upstream-facing (Zulip) prose and
makes no claims requiring human authorship review beyond what is already flagged in
`reports/01_lifting-audit.md` §8's `[SCAFFOLD]` block.
