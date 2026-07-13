# Implementation Plan: Task #299 (Revised, v6 — native-constructor refactor)

- **Task**: 299 - Modal K Tableau Decision Procedure
- **Status**: [NOT STARTED]
- **Effort**: ~12 hours (full datatype refactor + tableau rebuild; supersedes the encoding-based v5)
- **Dependencies**: None
- **Research Inputs**: reports/01_modal-k-tableau-research.md; reports/03_completeness-decomposition.md; reports/04_truth-lemma-architecture.md
- **Artifacts**: plans/06_modal-k-tableau-plan.md (this file); supersedes plans/05_modal-k-tableau-plan.md
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - CSLib CONTRIBUTING.md (zero-sorry / zero-admit / zero-new-axiom)
  - CSLib ORGANISATION.md (barrel / module layout)
- **Type**: cslib

## Overview

Rebuild the modal K tableau decision procedure under `Cslib/Logics/Modal/Tableau/` on a
**native-constructor `Modal.Proposition` datatype**. The prior approach (v5 and earlier) kept
`Modal.Proposition` Łukasiewicz-minimal (`atom, bot, imp, box` only) and *encoded* `and/or/neg/
diamond` as nested `imp`/`bot`/`box` trees. That encoding is the root cause of the completeness
blocker: the uniform `imp` bridge lemmas (`hintikka_imp_pos`/`hintikka_imp_neg`) are **false** for
encoded connectives, the tableau rules had to pattern-match deeply nested shapes like
`.imp (.box (.imp φ .bot)) .bot`, and the truth lemma needed strong-induction-on-complexity gymnastics
to recover IHs at grandchildren of the encoding.

This v6 revision is a **foundational datatype change, not a patch** (user-confirmed). We redefine
`Modal.Proposition` with primitive constructors `atom, bot, imp, and, or, box, diamond` — mirroring
the propositional layer's Gentzen/Prawitz house style (`PL.Proposition` is primitive in
`atom, bot, imp, and, or`; see `Cslib/Logics/Propositional/Defs.lean:81`). With native constructors:

- The tableau rules collapse to **one decomposer/rule per connective** (`andPos/andNeg`, `orPos/orNeg`,
  `impPos/impNeg`, `boxPos/boxNeg`, `diamondPos/diamondNeg`) that match constructors directly — no
  nested-`imp` matching.
- The completeness truth lemma uses **plain structural induction** on the constructor: native `and`/`or`
  give the correct IHs at their own children directly. No strong induction, no size measure, no
  view/classifier — the constructor *is* the classifier.
- The two false uniform-`imp` bridge lemmas are **deleted entirely** (not repaired).

Definition of done: `Modal.Proposition` is native; all of `Modal/Basic.lean`, `Modal/
LogicalEquivalence.lean`, `Modal/Tableau/*`, and the `Bimodal/Embedding/ModalEmbedding.lean` consumer
build green; `modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides` and a `Decidable`
instance are proved with ZERO `sorry`, ZERO `admit`, ZERO new `axiom`; full CSLib CI green.

### Research Integration

This v6 plan integrates the prior reports and the user-confirmed architecture decision recorded in the
revision request:

- **reports/04_truth-lemma-architecture.md** — diagnosed the root cause (encoded connectives make the
  uniform `imp` bridge unsound; `induction φ` cannot supply IHs at the grandchildren of an encoding).
  v5 resolved this *within* the encoding via strong-induction-on-`sizeOf`. v6 instead **removes the
  encoding**, which dissolves the blocker at its source: structural induction over native `and/or`
  yields the needed IHs directly (report 04 §2's "deep IH" requirement vanishes when the connective is
  primitive). The size-bounded `modalTruthLemma_aux` and the four-shape `imp`-dispatch table from v5
  Phase 5c are therefore **retired** — replaced by one structural case per native constructor, mirroring
  `Propositional/Tableau/Classical/Completeness.lean`'s `classicalTruthLemma` (report 04 §3 notes the
  propositional truth lemma already does exactly this because *its* `Proposition` has native and/or).
- **reports/01_modal-k-tableau-research.md** — reuse the label-generic CSLib Foundations tableau layer,
  the Classical/Bimodal templates, and K-vs-S5 box-rule correctness. All carry over; only the per-rule
  encodings change.
- **reports/03_completeness-decomposition.md** — per-rule bridge isolation and the `forall₂_*` worklist
  hoist for the loop invariant carry over structurally (signatures change with the datatype).

Reports integrated: see `reports_integrated` in `.return-meta.json`.

### Relationship to v5 (what carries over vs. what is rebuilt)

The v5 *proof strategy* survives; every v5 *signature* changes because the datatype changes. Concretely:

- **Strategy preserved** (carried as design intent, re-expressed on native constructors): the soundness
  architecture (`modalStepBranch_preserves_sat` → `modalExpandBranches_closed_unsat` → `modalTableau_
  sound`); the completeness skeleton (`extractModel` → Hintikka set → truth lemma → countermodel
  wrapper); the `LoopInduction` `forall₂_*` worklist plumbing and `accFreshInv` freshness invariant; the
  fuel-based saturation loop; the final `decides` iff + `Decidable` instance.
- **Deleted, not repaired**: `hintikka_imp_pos` / `hintikka_imp_neg` (false for encoded connectives);
  the v5 `modalTruthLemma_aux` strong-induction-on-`sizeOf` scaffold and its four-shape `imp` dispatch;
  every nested-`imp` match in `Rules.lean` (`.imp (.box (.imp φ .bot)) .bot` etc.).
- **Status reset**: because the datatype changes underneath them, the v5 [COMPLETED] phases (soundness
  green at `3660ac0c`; completeness pieces 5a/5b/5d) do **not** carry their green status into v6 — their
  *content* is preserved as the template each v6 phase re-establishes on native constructors. No v6 phase
  is pre-marked [COMPLETED]; each must re-build to green.

### Roadmap Alignment

`specs/ROADMAP.md` exists but no roadmap-update flag was provided; this plan does not modify ROADMAP.md.
Task 299 is part of the modal/temporal tableau series (299-301); completing it advances the Modal Logic
decidability line and makes the native `Modal.Proposition` the stable substrate for tasks 300-301.

## Goals & Non-Goals

**Goals**:
- `Modal.Proposition` redefined with **native** constructors `atom, bot, imp, and, or, box, diamond`
  (diamond primitive); `neg`, `top`, `iff` kept as derived `abbrev`s; `ModalConnectives`/`Bot`/notation
  instances and `@[simp]` reduction lemmas (`neg_def`, `top_def`) preserved.
- `Satisfies` and its `@[grind]`/`@[simp]` companion lemmas updated to the native constructors; the
  K/T/4/5 modal-axiom theorems in `Basic.lean` re-proved green.
- `Modal.LogicalEquivalence.Context` extended with the new recursive positions; `congruence` re-proved.
- `Bimodal/Embedding/ModalEmbedding.lean` updated to the native API and green.
- A `modalComplexity` (one case per constructor, `@[simp]` reduction lemmas) mirroring
  `Propositional/Subformula.lean:193`.
- Tableau rebuilt on native constructors: per-connective decomposers/rules, K successor propagation
  (boxPos persistent, boxNeg linear, diamondPos linear/existential, diamondNeg persistent).
- `modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides` + a `Decidable` instance (no
  `Fintype Atom` requirement), all ZERO `sorry`/`admit`/new-`axiom`; full CSLib CI green.

**Non-Goals**:
- Any modal system beyond K (no T/D/4/5/B/S4/S5 frame conditions in the *tableau*; the existing
  `Basic.lean` axiom theorems are kept building but not extended).
- Optimised/performant saturation; fuel-based correctness suffices.
- A canonical-model / Lindenbaum completeness proof (countermodel extraction is the route).
- Reviving the encoded datatype or the `imp` bridge-lemma factoring.
- Changing `PL.Proposition` (propositional layer) — it is the *template*, untouched.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Datatype change cascades to unforeseen consumers | H | M | Phase A starts with a repo-wide grep for `Modal`-scoped `.and`/`.or`/`.diamond`/`Proposition.Context`/`Satisfies`; confirmed consumers: `Modal/Basic.lean`, `Modal/LogicalEquivalence.lean`, all `Modal/Tableau/*`, `Bimodal/Embedding/ModalEmbedding.lean`. Re-grep before each phase. |
| `diamond_iff`/`and_iff`/`or_iff` (25 uses in `Basic.lean`) break when constructors go native | M | H | These reduction lemmas become `Iff.rfl`/`by simp [Satisfies]` once `Satisfies` has native cases; the 25 `rw [diamond_iff]` call sites in the K/T/4/5 theorems keep working because the lemma name/statement is preserved (only its proof body changes). Re-prove the lemmas first, then build the theorems. |
| `Satisfies` `@[grind]` set changes alter downstream `grind` proofs | M | M | Add native cases to `Satisfies` and the `@[grind =]` companion lemmas (`and_iff_and`, `or_iff_or`, `diamond_iff_exists`) so `grind` sees the same iff-rewrites; rebuild `Basic.lean` green before touching tableau. |
| `ModalEmbedding.lean` uses the OLD encoding shape | H | M | Inspect with `lean_file_outline`; update to native `.and`/`.or`/`.diamond`; rebuild that file green as part of Phase A's gate (it imports `Modal/Basic.lean`). |
| Tableau rules mis-handle the now-primitive `diamond` (was derived) | M | M | `diamondPos` creates a fresh successor + edge + `T(φ)@w'` matching `.pos, .diamond φ` directly; `diamondNeg` is `.persistent` over recorded successors matching `.neg, .diamond φ`. No `.imp (.box (.imp φ .bot)) .bot` matching remains. |
| `mk_all`/barrel omits new module or `LoopInduction.lean` | L | M | Phase F runs `lake exe mk_all --module` and `lake exe checkInitImports`; verify every `Modal/Tableau/*.lean` is reachable from the Cslib barrel. |
| Concurrent sessions clobber WIP (shared checkout) | M | M | Serialize sessions or use a git worktree; commit each green, zero-sorry milestone immediately. |
| `complexity`/termination obligations in saturation reappear | L | L | `modalComplexity` is one-case-per-constructor with `@[simp]` reductions; the fuel bound `modalFuel φ` is structural and unaffected by the constructor count. |

**Environment hazard**: multiple concurrent Claude sessions share this checkout; a sibling `git add -A`
previously swept WIP into an unrelated commit. Serialize sessions or use separate git worktrees. This
refactor touches shared foundational files (`Modal/Basic.lean`), so it is **not** import-isolated like
the v5 completeness work — run it as a single serialized track, committing each phase at green.

## Context-Budget Protocol (MANDATORY for every phase)

The reference files are large. Implementation agents MUST navigate, not bulk-read:

1. **Navigate with lean-lsp**: `lean_file_outline` to locate declarations; `lean_diagnostic_messages`
   for the authoritative current error set; `lean_goal` + `lean_hover_info` at a target line for proof
   state; `lean_multi_attempt` to test a tactic without editing. Use `Read` with `offset`/`limit` for
   only ±40 lines around a target.
2. **Build truncated, single-module** while iterating:
   `lake build Cslib.Logics.Modal.Tableau.<Module> 2>&1 | tail -60`. Reserve the whole-library
   `lake build` for Phase F (CI).
3. **Per-phase gate**: targeted declarations report NO errors via `lean_diagnostic_messages`; NO `sorry`,
   NO `admit`, NO new `axiom`; `grep -rn 'sorry\|admit\|^axiom ' Cslib/Logics/Modal/` empty for touched
   files; commit `task 299 phase {X}: …`.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | A (datatype + Satisfies + complexity + LogicalEquivalence + ModalEmbedding) | -- |
| 2 | B (tableau Defs/Rules/Closure/Branch on native constructors) | A |
| 3 | C (Soundness + SoundnessStep) | B |
| 4 | D (Saturation + LoopInduction) | B, C |
| 5 | E (Completeness truth lemma, native structural induction) | C, D |
| 6 | F (decides + Decidable + barrel + CI) | E |

Each phase is sized to one agent run (~100-500 lines of output, builds to green). Phase A is the
foundational gate: nothing in `Tableau/` can compile until `Modal/Basic.lean` is green on the native
datatype. Confirm the file/consumer set by grep at the start of each phase (the architecture request
established the set; re-verify against the working tree).

---

### Phase A: Native datatype + Satisfies + complexity + downstream foundation [BLOCKED]

**BLOCKER** (discovered during implementation attempt, see
`handoffs/01_scope-discovery-blocker.md` for full detail):
- **What failed**: Making `Proposition.diamond` a primitive constructor (required by this
  plan's design) breaks a definitional identity (`diamond φ` used to be defeq to the raw
  Łukasiewicz shape `(□(φ → ⊥)) → ⊥`) that `Cslib/Logics/Modal/Metalogic/**` (MCS.lean,
  Completeness.lean, DerivationTree.lean) and `Cslib/Logics/Modal/ProofSystem/Instances/
  {B,TB,KB5,S5,DB}.lean` (and their `Systems/*/{Soundness,Completeness,
  ConservativeExtension}.lean` counterparts) rely on structurally, not just by notation.
  None of these files are in this plan's stated consumer set.
- **What was tried**: Implemented and individually verified (green `lake build`) the full
  Phase A patch for `Basic.lean`, `LogicalEquivalence.lean`, `ModalEmbedding.lean`,
  `Denotation.lean` (not in original file list -- real gap), `FromPropositional.lean`.
  Mechanically fixed 5 axiom-schema sites (`DerivationTree.lean`, `B/TB/KB5/DB.lean`) by
  substituting the canonical `Axioms.AxiomB` abbrev for the manual `Proposition.diamond`
  expansion -- this part worked and rebuilt green. Attempted the same for
  `Metalogic/Completeness.lean`'s canonical-model proofs (`canonical_symm`,
  `canonical_eucl`, `canonical_eucl_from_5`) and found they do syntactic surgery on the
  diamond term's structure (expecting it to unify with an `.imp` pattern), which no
  longer works once diamond is primitive -- this is NOT mechanical, it requires either
  restating the canonical-model proofs around the raw encoding explicitly, or adding new
  `HasDia`/`AxiomDiaDualityFwd`/`AxiomDiaDualityBack` infrastructure across ~9 modal
  systems (B, TB, KB5, S5, DB, D45, D5, K45, K5).
- **Why it's stuck**: Fixing the canonical-model layer requires either genuine new
  proof content (a native-diamond "existence lemma" for the canonical model) or new
  axiom-schema design, neither of which this plan discusses or scopes. This is a design
  decision, not an implementation detail, and the blast radius (~9 systems × 3 files) is
  large enough to warrant its own phase/task rather than folding into Phase A.
- **What is needed**: Re-plan (new plan version) that (1) explicitly scopes the
  Metalogic/ProofSystem consumer set and picks a resolution strategy (raw-encoding
  restatement vs. new HasDia axiomatic infrastructure), (2) adds `FmpMeasure.lean`
  (3011 lines) and `CompletenessLoop.lean` (1096 lines) to the Phase E/F file lists --
  these were added by tasks 442/462 after this plan was written and are not currently
  scoped anywhere in this plan despite depending pervasively on the Łukasiewicz
  decomposers. Consider splitting into task 441 (datatype + Basic-layer consumers,
  self-contained and verified buildable) + a follow-on task for the Metalogic/Hilbert
  layer + the original Tableau-focused phases B-F.
- **Prohibited workarounds**: Did NOT use `sorry`, `def X := True`, or any vacuous
  placeholder. Did NOT invent new axiom schemata unilaterally. All working-tree changes
  were reverted; `git status --short -- Cslib/` is clean at HEAD `ebd6bb1d`.

**Goal**: Redefine `Modal.Proposition` with native constructors and bring every direct consumer of the
datatype (`Basic.lean`, `LogicalEquivalence.lean`, `Bimodal/Embedding/ModalEmbedding.lean`) back to
green. No tableau work in this phase.

**Tasks**:
- [ ] **Redefine the inductive** in `Cslib/Logics/Modal/Basic.lean:70` from `atom, bot, imp, box` to
  primitive `atom, bot, imp, and, or, box, diamond`. Keep `Proposition.neg := .imp · .bot`,
  `Proposition.top := .imp .bot .bot`, `Proposition.iff` as derived `abbrev`s (mirror
  `Propositional/Defs.lean:21-28` house style). **Delete** the old derived `abbrev`s for `and`
  (`:113`), `or` (`:109`), `diamond` (`:124`) — they are now constructors.
- [ ] Preserve the `ModalConnectives` instance (`:86`), the `Bot` instance (`:132`), and all scoped
  notation (`∧`, `∨`, `→`, `¬`, `□`, `◇`, `:139`). Keep the `@[simp]` reduction lemmas `neg_def`
  (`:103`) and `top_def` (`:106`). Ensure `ModalConnectives.and/or` resolve to the new constructors.
- [ ] **Extend `Satisfies`** (`:145-149`) with native cases:
  `| .and φ₁ φ₂ => Satisfies … φ₁ ∧ Satisfies … φ₂`; `| .or φ₁ φ₂ => Satisfies … φ₁ ∨ Satisfies … φ₂`;
  `| .diamond φ => ∃ w', m.r w w' ∧ Satisfies m w' φ`. Keep `imp`/`box`/`atom`/`bot` cases.
- [ ] **Re-prove the reduction lemmas** as `Iff.rfl`/`by simp only [Satisfies]`:
  `Satisfies.and_iff` (`:168`), `Satisfies.or_iff` (`:178`) — now trivial from the native cases (drop
  the `change … → … → False` encoding gymnastics); `Satisfies.diamond_iff` (`:156`) — now
  `Iff.rfl`-style (drop the `change Satisfies … (.imp (.box (.imp φ .bot)) .bot)` line). `Satisfies.
  neg_iff` (`:152`) stays (neg still derived). Keep the `@[grind =]` Bundled companions
  (`and_iff_and`, `or_iff_or`, `diamond_iff_exists`, `:224-247`) — bodies unchanged, they delegate to
  the re-proved lemmas.
- [ ] **Verify the 25 `diamond_iff`/`and_iff`/`or_iff` call sites** in `Basic.lean` (the K/T/4/5 modal
  axiom theorems, `~:290-440`) still build: the lemma *names and statements* are preserved, so the
  `rw [diamond_iff]` etc. proofs are untouched. Fix any that relied on the encoding's definitional shape
  (e.g. a `change` to the old encoding) by replacing with the iff-rewrite.
- [ ] **`modalComplexity`** (new, mirror `Propositional/Subformula.lean:193`): one case per constructor
  (`atom`/`bot` → 0; `imp`/`and`/`or` → `1 + …`; `box`/`diamond` → `1 + …`) with `@[simp]` reduction
  lemmas per binary/unary constructor. Place in `Modal/Basic.lean` or a `Modal/Subformula.lean` mirror
  per ORGANISATION.md (prefer matching the propositional layout).
- [ ] **`LogicalEquivalence.Context`** (`Modal/LogicalEquivalence.lean:39`): add the new recursive
  positions `andL/andR`, `orL/orR`, `diamond` (alongside existing `impL/impR/box`). Extend
  `Context.fill` (`:50`) and re-prove `LogicallyEquivalent.congruence` (`:63`, currently
  `simp only [Proposition.Context.fill, Satisfies]`) to cover the new cases.
- [ ] **`Bimodal/Embedding/ModalEmbedding.lean`**: inspect with `lean_file_outline`; update any use of
  the old encoded `.and`/`.or`/`.diamond` shapes to the native constructors; rebuild green.

**Timing**: ~3.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` (datatype, Satisfies, reduction lemmas, axiom theorems, complexity)
- `Cslib/Logics/Modal/LogicalEquivalence.lean` (Context + fill + congruence)
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` (consumer update)
- possibly new `Cslib/Logics/Modal/Subformula.lean` (complexity, mirroring propositional)

**Verification**:
- `lake build Cslib.Logics.Modal.Basic`, `Cslib.Logics.Modal.LogicalEquivalence`,
  `Cslib.Logics.Bimodal.Embedding.ModalEmbedding` all green; ZERO sorry/admit/new-axiom.
- `lean_verify` on the touched modal-axiom theorems shows no new axioms.
- Commit `task 299 phase A: native Modal.Proposition (and/or/diamond primitive) + consumers green`.

---

### Phase B: Tableau Defs / Rules / Closure / Branch on native constructors [NOT STARTED]

**Goal**: Rebuild the tableau front-end on the native datatype. Decomposers match constructors directly;
no nested-`imp` matching anywhere.

**Tasks**:
- [ ] **`Defs.lean`**: replace the Łukasiewicz classifiers (`modalNegOf?`/`modalOrOf?`/`modalAndOf?`/
  `modalImpOf?`/`boxOf?`/`diaOf?`) with **constructor-matching** decomposers — one per connective,
  matching exactly the corresponding constructor (mirror `Propositional/Tableau/Defs.lean`'s
  `propAndOf?`/`propOrOf?` "decompose EXACTLY the conjunction/disjunction"). Keep the `WorldIndex`,
  `Hashable (Proposition Atom)` instance, and `complexity` re-export. Provide `@[simp]` reduction
  lemmas for each decomposer.
- [ ] **`Rules.lean` `modalApplyOne`**: replace the encoded matches (`.imp (.box (.imp φ .bot)) .bot`
  at `:91/:109/:134/:142`) with native per-connective rules:
  - `andPos`: `.pos, .and φ₁ φ₂` → `.linear [T φ₁ @w, T φ₂ @w]`;
    `andNeg`: `.neg, .and φ₁ φ₂` → `.branching [[F φ₁ @w],[F φ₂ @w]]`.
  - `orPos`: `.pos, .or φ₁ φ₂` → `.branching [[T φ₁ @w],[T φ₂ @w]]`;
    `orNeg`: `.neg, .or φ₁ φ₂` → `.linear [F φ₁ @w, F φ₂ @w]`.
  - `impPos`: `.pos, .imp φ₁ φ₂` → `.branching [[F φ₁ @w],[T φ₂ @w]]`;
    `impNeg`: `.neg, .imp φ₁ φ₂` → `.linear [T φ₁ @w, F φ₂ @w]`.
  - `boxPos`: `.pos, .box φ` → `.persistent`, propagate `T φ @w'` to each recorded successor `w'`
    (scoped to `acc` edges only — K-sound, not S5);
    `boxNeg`: `.neg, .box φ` → `.linear`, create fresh `w'`, edge `w→w'`, `F φ @w'`.
  - `diamondPos`: `.pos, .diamond φ` → `.linear`, create fresh `w'`, edge `w→w'`, `T φ @w'`
    (existential);
    `diamondNeg`: `.neg, .diamond φ` → `.persistent`, propagate `F φ @w'` to each recorded successor.
  (Dispatch order: propositional rules then the four K modal rules, as in the current docstring
  `Rules.lean:61-66`; the rule table in the docstring already describes this design.)
- [ ] **`Branch.lean`**: keep `Accessibility`, `empty`/`addEdge`/`successorsOf`/`allWorlds`/`hasEdge`,
  `boxPositivesOf`, `boxPropagation`. Update `boxPositivesOf`/propagation helpers to match
  `.box`/`.diamond` constructors directly (drop encoded-shape `filterMap` matches at `:98-109/:124-134`).
- [ ] **`Closure.lean`**: `isModalClosed` — update any connective-shape references to native
  constructors (contradiction detection on signed atoms/⊥ is unchanged).

**Timing**: ~2.5 hours

**Depends on**: A

**Files to modify**: `Cslib/Logics/Modal/Tableau/{Defs,Rules,Branch,Closure}.lean`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Closure` (transitively builds Defs/Rules/Branch) green; ZERO
  sorry/admit/new-axiom.
- `grep -n '\.imp (\.box' Cslib/Logics/Modal/Tableau/Rules.lean` empty (no encoded matching remains).
- Commit `task 299 phase B: tableau Defs/Rules/Branch/Closure on native constructors`.

---

### Phase C: Soundness + SoundnessStep on native constructors [NOT STARTED]

**Goal**: Re-establish `modalTableau_sound` against Kripke semantics over all models, on the native
datatype. Re-express the v5 soundness architecture (its strategy carries over; signatures change).

**Tasks**:
- [ ] **`SoundnessStep.lean`**: re-prove `modalStepBranch_preserves_sat` (each rule preserves
  satisfiability of the branch) using the native `Satisfies` cases and the `@[grind =]` companions from
  Phase A. Keep `accFreshInv`/`accFreshInv_empty` (freshness invariant for fresh-world creation in
  `boxNeg`/`diamondPos`).
- [ ] **`Soundness.lean`**: re-prove `modalExpandBranches_closed_unsat` (closed result ⇒ unsatisfiable)
  and the `forall₂_*` worklist helpers (these are label-generic and largely unchanged, but verify they
  compile against the new signatures). Discharge `modalTableau_sound`.
- [ ] Per-rule soundness obligations now use native `Satisfies.and_iff`/`or_iff`/`diamond_iff` directly
  (no encoding unfolds). The `boxPos`/`diamondNeg` persistence and `boxNeg`/`diamondPos` existential
  cases mirror the v5 proofs with the constructor match in place of the encoded shape.

**Timing**: ~3 hours (may need a small second dispatch for the step lemma)

**Depends on**: B

**Files to modify**: `Cslib/Logics/Modal/Tableau/{SoundnessStep,Soundness}.lean`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Soundness` green; ZERO sorry/admit/new-axiom.
- `#print axioms modalTableau_sound` shows only standard axioms.
- Commit `task 299 phase C: modalTableau_sound on native constructors`.

---

### Phase D: Saturation + LoopInduction [NOT STARTED]

**Goal**: Re-establish the fuel-based saturation loop, the `modalTableau φ` entry point, the Hintikka
predicate, and the hoisted `forall₂_*` loop-induction plumbing.

**Tasks**:
- [ ] **`Saturation.lean`**: `ModalTableauResult`, `modalStepBranch`, `modalExpandBranches` +
  `processNext` worklist, `modalFuel φ` with `termination_by`, entry point `modalTableau φ`,
  `modalHintikkaSet b acc`. Update the Hintikka clause to range over native-constructor rule outputs
  (the `match (modalApplyOne sf b acc).1 with .linear/.branching/.persistent/.notApplicable` shape is
  unchanged; only the per-rule outputs differ). Confirm the fuel bound still type-checks with
  `modalComplexity`.
- [ ] **`LoopInduction.lean`**: keep the de-`private`'d, re-exported `forall₂_*` helpers
  (`forall₂_of_zip_mem`, `forall₂_replicate_right`, `forall₂_append_aux`, `forall₂_drop_aux`,
  `forall₂_take_aux`) so `Completeness.lean` reuses them without importing `Soundness.lean`. Verify
  they compile unchanged (label-generic) and that `Soundness.lean` imports them.

**Timing**: ~1.5 hours

**Depends on**: B, C

**Files to modify**: `Cslib/Logics/Modal/Tableau/{Saturation,LoopInduction}.lean`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Saturation` and `…LoopInduction` green; ZERO sorry/admit.
- Commit `task 299 phase D: saturation loop + LoopInduction on native constructors`.

---

### Phase E: Completeness — native structural-induction truth lemma [NOT STARTED]

**Goal**: Prove `modalTableau_complete` via `extractModel` + Hintikka set + a **structural-induction
truth lemma** over native constructors. This is where the native refactor pays off: no strong induction,
no size measure, no `imp` bridge lemmas.

**Tasks**:
- [ ] **`extractModel` + helpers** (re-establish v5 Phase 5a content on native datatype): `extractModel b
  acc` (`r w w' := acc.hasEdge w w' = true`; `v w p := b.any (sign=.pos ∧ formula=.atom p ∧ label=w)`);
  `extractModel_atom_sat_iff`, `extractModel_bot_false`; `openBranch_noTBot`,
  `openBranch_noContradiction`.
- [ ] **`modalTruthLemma`** via **plain `induction φ`** (mirror `Propositional/Tableau/Classical/
  Completeness.lean:84` `classicalTruthLemma`), proving the `pos ∧ neg` conjunction with one case per
  constructor:
  - `atom`/`bot`: as the propositional template (atom-reflection / ⊥-absence).
  - `and φ₁ φ₂`: `andPos` `.linear [T φ₁, T φ₂]` gives both members; close `Satisfies (and φ₁ φ₂)` via
    `Satisfies.and_iff` and the **child IHs** `(ih φ₁).1`, `(ih φ₂).1` — supplied directly by
    `induction φ` (no deep IH needed; the connective is primitive). `andNeg` `.branching` dually with
    `(ih …).2`.
  - `or φ₁ φ₂`: `orPos` `.branching`, `orNeg` `.linear`, child IHs, `Satisfies.or_iff`.
  - `imp φ₁ φ₂`: `impPos` `.branching [[F φ₁],[T φ₂]]` → `(ih φ₁).2` / `(ih φ₂).1`; `impNeg` `.linear
    [T φ₁, F φ₂]` → `(ih φ₁).1` / `(ih φ₂).2`.
  - `box φ`: re-establish `hintikka_box_pos`/`hintikka_box_neg` content (box is still primitive) — the
    only rules touching the accessibility relation; `(ih φ)` at successor worlds.
  - `diamond φ`: now **primitive** — `diamondPos` `.linear` (fresh successor witness) → `Satisfies.
    diamond_iff` with `(ih φ).1` at `w'`; `diamondNeg` `.persistent` over recorded successors →
    `(ih φ).2`. No `¬□¬` unfolding.
  Public statement: `modalTruthLemma (b) (acc) (hH) : ∀ φ w, (T φ @w ∈ b → Satisfies (extractModel b
  acc) w φ) ∧ (F φ @w ∈ b → ¬ Satisfies …)`. **Do not** reintroduce `modalTruthLemma_aux` or any
  `sizeOf` scaffold — structural induction suffices.
- [ ] **`modalOpenBranch_countermodel`** (v5 Phase 5d content): a `modalHintikkaSet b acc` branch yields
  `extractModel b acc` refuting `φ` (apply `modalTruthLemma … .2` to the initial `F φ @0` membership).
- [ ] **Loop invariant** `modalExpandBranches_hintikka`: the returned open branch is a Hintikka set.
  Mirror `modalExpandBranches_closed_unsat` (Phase C) for acc-threading + the classical
  `classicalExpandBranches_hintikka` / `classicalStepBranch_none_saturated` /
  `classicalStepBranch_hintikka_inv` for the open/Hintikka logic. Reuse the hoisted `forall₂_*` helpers
  and `accFreshInv`. Handle world-creation interleaving (boxNeg/diamondPos re-firing as successors
  appear); the fuel bound `modalFuel φ` should suffice.
- [ ] Discharge `modalTableau_complete` (contrapositive: open ⇒ Hintikka ⇒ countermodel).

**Timing**: ~3 hours (may need 1-2 dispatches for the loop invariant; truth lemma itself is much smaller
than v5's strong-induction version)

**Depends on**: C, D

**Files to modify**: `Cslib/Logics/Modal/Tableau/Completeness.lean`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Completeness` green; ZERO sorry/admit/new-axiom.
- `grep -rn 'sorry\|admit\|^axiom ' Cslib/Logics/Modal/Tableau/Completeness.lean` empty.
- `#print axioms modalTableau_complete` shows only standard axioms.
- Commit `task 299 phase E: completeness truth lemma (native structural induction) + modalTableau_complete`.

**Contingency (zero-debt fallback)**: if world-creation interleaving cannot close in one genuine
attempt, keep Phases A-E-through-truth-lemma committed sorry-free, mark the loop-invariant piece
[BLOCKED] with the precise residual obligation, `/spawn` a follow-up. Never ship `sorry`/`admit`/axioms.

---

### Phase F: Decision procedure, barrel, and CI [NOT STARTED]

**Goal**: Package the iff + `Decidable` instance, add the module barrel, confirm no new axioms, pass the
full CSLib CI pipeline with zero sorry/admit.

**Tasks**:
- [ ] Prove `modalTableau_decides : modalTableau φ = .closed ↔ <φ valid over all models>` from
  `modalTableau_sound` + `modalTableau_complete`; provide a `Decidable` instance via `isTrue`/`isFalse`
  (requires only `DecidableEq + Hashable`, no `Fintype Atom`).
- [ ] Confirm NO `sorry`/`admit`/new-`axiom` anywhere under `Cslib/Logics/Modal/` (grep clean) and
  `#print axioms` on `modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides` shows only
  standard axioms.
- [ ] Add module doc comments + barrel via `lake exe mk_all --module` so every `Modal/Tableau/*.lean`
  (including `LoopInduction.lean`) and any new `Modal/Subformula.lean` are reachable from the Cslib
  barrel (per ORGANISATION.md).
- [ ] Run the full CI pipeline: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`, `lake test`.

**Timing**: ~1.5 hours

**Depends on**: E

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (decision procedure iff + `Decidable` instance)
- barrel/import file under `Cslib/` per ORGANISATION.md

**Verification**:
- All CI commands exit 0; `#print axioms modalTableau_decides` shows only standard axioms; no
  `sorry`/`admit` (grep clean).
- Commit `task 299 phase F: decision procedure + barrel + CI green`.

---

## Testing & Validation

- [ ] `lake build` of all `Cslib/Logics/Modal/**.lean` (Basic, LogicalEquivalence, Subformula if added,
  and Tableau Defs/Branch/Rules/Closure/Saturation/SoundnessStep/Soundness/LoopInduction/Completeness)
  succeeds, plus `Bimodal/Embedding/ModalEmbedding.lean`.
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no issues.
- [ ] Zero `sorry`, zero `admit`, zero new axioms across `Cslib/Logics/Modal/` (grep + `#print axioms`
  on `modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides`).
- [ ] Smoke `#eval`: K-valid `□(p ⟶ q) ⟶ (□p ⟶ □q)` returns `closed`; K-invalid `□p ⟶ p` returns an
  open branch with a refuting countermodel; native `◇`/`∧`/`∨` formulas decide correctly.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Basic.lean` (Phase A — native datatype, Satisfies, complexity, axiom theorems)
- `Cslib/Logics/Modal/LogicalEquivalence.lean` (Phase A — Context + fill + congruence)
- `Cslib/Logics/Modal/Subformula.lean` (Phase A — `modalComplexity`, if split out per ORGANISATION.md)
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` (Phase A — consumer update)
- `Cslib/Logics/Modal/Tableau/Defs.lean` (Phase B)
- `Cslib/Logics/Modal/Tableau/Branch.lean` (Phase B)
- `Cslib/Logics/Modal/Tableau/Rules.lean` (Phase B)
- `Cslib/Logics/Modal/Tableau/Closure.lean` (Phase B)
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` (Phase C)
- `Cslib/Logics/Modal/Tableau/Soundness.lean` (Phase C)
- `Cslib/Logics/Modal/Tableau/Saturation.lean` (Phase D)
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean` (Phase D)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (Phase E)
- barrel/import file per ORGANISATION.md (Phase F)
- `modalTableau`, `modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides`, and a
  `Decidable` instance.

## Rollback/Contingency

- The datatype change is foundational and touches shared files; the rollback unit is the whole v6 track.
  Each phase commits at a green, zero-sorry milestone, so `git checkout` of the last green commit always
  recovers a building tree.
- If Phase A cannot bring `ModalEmbedding.lean` green, do not proceed — the datatype change must leave
  the whole library building. Revert the inductive change and re-scope.
- If Phase E's loop invariant stalls, apply its zero-debt fallback: spawn a follow-up for the invariant,
  keep the sorry-free truth lemma + soundness committed, mark task 299 `[BLOCKED]`/`[PARTIAL]`. Never
  commit `sorry`, `admit`, or new axioms.
- The v5 plan (`plans/05_modal-k-tableau-plan.md`) and the encoding-based git history remain as
  reference; this plan supersedes it but does not delete it.
