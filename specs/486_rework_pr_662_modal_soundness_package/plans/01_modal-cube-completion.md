# Implementation Plan: Task #486 — Modal-Cube Completion on #607 (PR #662, Option A)

- **Task**: 486 - Rework PR #662 into a modal-soundness/canonicity completion package on #607
- **Status**: [PR READY]
- **Effort**: 4 hours
- **Dependencies**: None (research complete; base branch live)
- **Research Inputs**: specs/486_rework_pr_662_modal_soundness_package/reports/01_modal-soundness-package.md
- **Artifacts**: plans/01_modal-cube-completion.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Scope is **LOCKED to Option A** (user-chosen 2026-07-12); do not re-open. Deliver a self-contained,
non-duplicative modal-cube **completion** on top of #607, reusing task 477's both-primitive refactor
that is already **LIVE and intact** on the live PR head `origin/feat/modal-formula-primitives`
(=`70b7ec4d`). This plan does **not** reconstruct task 477 (the research report §2/§3.1 assumed the
477 branch was deleted; that assumption is superseded by the verified corrected premise below) and
does **not** re-port #607's Basic.lean soundness/canonicity lemmas (they already ship on #607).

The genuinely new, non-duplicative work is confined to **`Cube.lean`** and **`references.bib`**:
(1) complete the existing `Validity` section with `B.b_valid`, `Four.four_valid`, `Five.five_valid`,
`D.d_valid` (mirroring the existing `K.k_valid`/`T.t_valid`); (2) add a new `Canonicity` section with
Cube-level frame-determination wrappers (T↔reflexive, B↔symmetric, 4↔transitive, 5↔euclidean,
D↔serial) over Basic.lean's already-green `Satisfies.*_refl/_symm/_trans/_rightEuclidean/_serial`
lemmas; (3) add the `ChagrovZakharyaschev1997` bib entry. **Definition of done**: all four new
validity wrappers + five canonicity wrappers compile with **zero sorry / zero new axioms**, module-
scoped `lake build Cslib.Logics.Modal.*` is green, the bib entry is present, and the diff is prepared
as a clean single commit on the live PR-head lineage.

### Research Integration

Integrated report: `reports/01_modal-soundness-package.md`. Key findings carried into this plan:
- #607 already owns the full Basic.lean modal-cube soundness/canonicity; re-porting would duplicate
  (reuse-first violation). The new content is thin Cube-level `∈ logic` / frame-class wrappers only.
- Relation infrastructure is verified real on the base: `Relation.Serial`
  (`Cslib/Foundations/Relation/Defs.lean:74`), `Relation.RightEuclidean` (`Defs.lean:49`),
  `Std.Refl`/`Std.Symm`, `IsTrans`, the `Euclidean.lean` bridges, and the `Classical.arbitrary`
  spy-valuation gadget. No Mathlib discovery is required.
- Every hard proof direction (`dual`, `five`/euclidean, `b`/symmetric) has a green precedent already
  compiled on the base — cited per phase below. Zero-sorry is achievable and mandatory.

### Corrected Premise (verified 2026-07-12, supersedes report §2/§3.1 "reconstruct 477")

Verified against `origin/feat/modal-formula-primitives`=`70b7ec4d`:
- `Cslib/Logics/Modal/Basic.lean` already has `| box (φ)` as the 5th `Proposition` constructor
  (line 50), the genuine both-primitive `Satisfies.dual` proof (line 209), and its companion
  `Satisfies.box_iff_not_diamond_not` (line 220). Task 477's both-primitive refactor is **live and
  intact — not lost**.
- `Cslib/Logics/Modal/Denotation.lean` (+1) and `Cslib/Logics/Modal/LogicalEquivalence.lean` (+9)
  already carry their `box` constructor cases from the same live 477 refactor. **No further work on
  those two files** — this plan touches only `Cube.lean` and `references.bib`.
- `Cube.lean` on the PR head has `K.k_valid` (line 130) and `T.t_valid` (line 134) **only** — no
  B/4/5/D validity, no `Canonicity` section. This is precisely the gap Option A fills.
- `references.bib` on the PR head has `Blackburn2001` only — `ChagrovZakharyaschev1997` absent,
  `Avigad2022` correctly absent (and must stay absent).

### Prior Plan Reference

No prior plan for task 486. This is plan version 1.

### Roadmap Alignment

No `roadmap_path` supplied and no ROADMAP.md consulted for this task. Task 486 is a follow-up from
task 477 (parent_task) and supersedes abandoned tasks 468/469/475; it advances the #662 PR toward a
reviewable, non-duplicative modal-cube contribution on #607.

### Honest LOC Accounting (no padding)

- **New work atop the live PR head** (this plan's deliverable): Cube.lean validity wrappers ~35 LOC
  + Cube.lean canonicity section ~70–110 LOC + references.bib ~14 LOC + docstrings ~10 LOC ≈
  **~130–170 net new LOC**.
- **Total #662 diff vs the #607 base** (including the already-live 477 refactor, ~80 LOC of modal
  changes): ≈ **~210–250 LOC**, landing inside the ~180–290 honest target.
- The 477 refactor is **reused, not re-counted as this task's authorship** — reporting both numbers
  transparently per the locked-scope instruction.

## Goals & Non-Goals

**Goals**:
- Complete `Cube.lean`'s `Validity` section: add `B.b_valid`, `Four.four_valid`, `Five.five_valid`,
  `D.d_valid`, each a thin wrapper over the existing `Satisfies.b/.four/.five/.d`.
- Add a new `Cube.lean` `Canonicity` section: `T.t_canonical` (Std.Refl), `B.b_canonical` (Std.Symm),
  `Four.four_canonical` (IsTrans), `Five.five_canonical` (Relation.RightEuclidean), `D.d_canonical`
  (Relation.Serial), each wrapping the existing `Satisfies.*_refl/_symm/_trans/_rightEuclidean/_serial`.
- Add `ChagrovZakharyaschev1997` to `references.bib`.
- Zero `sorry` / zero new axioms across all added theorems (hard requirement).
- Module-scoped green build (`lake build Cslib.Logics.Modal.*`) at every phase gate.
- A clean single-commit diff on the live PR-head lineage, ready for `/pr`.

**Non-Goals**:
- Reconstructing task 477's both-primitive refactor (already live on the PR head — reuse it).
- Editing `Basic.lean`, `Denotation.lean`, or `LogicalEquivalence.lean` beyond what is already live
  (their box cases and soundness/canonicity lemmas are done and green).
- Re-porting or re-stating any #607-owned Basic.lean soundness/canonicity lemma (duplication).
- Any work on: `FromPropositional.lean` (#648-entangled); `Metalogic/**` (MCS, canonical-model
  Completeness, DeductionTheorem, DerivationTree, proof-theoretic Soundness, Systems/*);
  `Metalogic/InterSystem/**`; `ProofSystem/`; `Tableau/`; fork-local `Connectives.lean` /
  `ModalConnectives` (dropped — reuse #607 split `Operators/*`); `HML/LogicalEquivalence.lean`
  (pre-existing #607 blocker).
- Adding `Avigad2022` (the Łukasiewicz-encoding note does not apply to the both-primitive base).
- Working on `main`, or on the stale local fork `feat/modal-formula-primitives`=`8d7a061e`.
- Full-library CI (blocked by out-of-scope #607 HML defect — see Risks).
- Deciding the PR-boundary/ownership question (Option B "re-own the whole cube") — deferred to
  fmontesi/Waring; out of scope here.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Full-library `lake build`/`checkInitImports`/`shake`/`test` blocked by pre-existing #607 `HML/LogicalEquivalence.lean` defect (3-arg vs 4-arg `LogicalEquivalence`) | M | H (certain) | Gate every phase on **module-scoped** `lake build Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Cube Cslib.Logics.Modal.Denotation Cslib.Logics.Modal.LogicalEquivalence`. Document that full CI must wait on fmontesi fixing HML; it is not #662's bug. Do NOT touch HML. |
| A validity/canonicity wrapper's `grind`/instance-synthesis invocation regresses under the both-primitive box | M | M | Every proof has a green precedent on the base (K.k_valid/T.t_valid for validity; Satisfies.*_refl/_symm/… for canonicity). Test each wrapper with `lean_multi_attempt` before committing; fall back to the explicit `box_iff_forall.mp`/`diamond_iff_exists.mp` chains from report §5.2–§5.3 if `grind` regresses. |
| Accidental `sorry`/axiom slips into a wrapper | H | L | Phase 4 runs a mandatory zero-sorry/axiom audit: `grep -rn "sorry\|admit" Cslib/Logics/Modal/Cube.lean` returns nothing, and `#print axioms` / `lean_verify` on each new theorem shows only the standard classical axioms already used by Basic.lean (no new axioms). |
| Wrong base branch → dirty PR diff or lost 477 work | H | L | Branch **directly from `origin/feat/modal-formula-primitives`=`70b7ec4d`** (its ancestor is `pr607`; base is current fmontesi/connectives). Never branch from `main` or the stale local fork `8d7a061e`. Phase 1 verifies the both-primitive markers are present before any edit. |
| Phase 2 and Phase 3 both edit `Cube.lean` → merge/territory conflict if parallelised | M | L | Keep them strictly sequential (Phase 3 depends on Phase 2). Single file, single owner per phase. |
| `ChagrovZakharyaschev1997` BibKey/format mismatch with CSLib `references.bib` conventions | L | L | Mirror the existing `Blackburn2001` `@book` entry structure; the fork already carries a compatible entry to copy verbatim. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: every phase
edits shared `Cube.lean` state and/or gates on the prior phase's green build.

### Phase 1: Worktree setup, establish PR-head base state, verify green [COMPLETED]

- **Goal:** Create an isolated worktree on the live PR-head lineage with task 477's both-primitive
  refactor intact, and confirm the Modal module builds green before any new work.
- **Base-branch decision (branch directly from the live PR head — justified):**
  Branch from `origin/feat/modal-formula-primitives`=`70b7ec4d`, **not** by cherry-picking 477's
  commit onto a fresh `pr607` branch. Justification (verified):
  - `pr607`=`c2ec2962` is a **direct ancestor** of `origin/feat/modal-formula-primitives`
    (`git merge-base --is-ancestor` confirms), so branching from the PR head still satisfies the
    "#607-lineage, never main, never the `8d7a061e` fork" intent.
  - The PR head already carries task 477's both-primitive refactor **guaranteed intact** — zero
    reconstruction and zero cherry-pick-conflict risk (Basic.lean differs between the two bases, so
    a cherry-pick onto stale `pr607` would likely conflict).
  - The PR head's base is the **current** fmontesi/connectives (newer than `pr607`; the pr607↔head
    diff spans 62 files incl. `lean-toolchain`/`lake-manifest` drift). Building here means the
    eventual `/pr` rebase onto fmontesi/connectives is trivial; cherry-picking onto stale `pr607`
    would instead strand the work on an outdated base and force a connectives catch-up later.
- **Tasks:**
  - [ ] `git branch task-486-pr662-modal-package origin/feat/modal-formula-primitives`
  - [ ] `git worktree add /home/benjamin/Projects/cslib-task-486-pr662-modal-package task-486-pr662-modal-package`
  - [ ] Verify the both-primitive refactor is present in the worktree: `Cslib/Logics/Modal/Basic.lean`
        has `| box (φ` constructor, `Satisfies.dual` genuine proof, and `Satisfies.box_iff_not_diamond_not`;
        `Denotation.lean` and `LogicalEquivalence.lean` carry their `box` cases.
  - [ ] Confirm `Cube.lean` currently has `K.k_valid` and `T.t_valid` only (no B/4/5/D validity, no
        `Canonicity` section) — the target gap.
  - [ ] Module-scoped green gate: `lake build Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Cube Cslib.Logics.Modal.Denotation Cslib.Logics.Modal.LogicalEquivalence` (fetch cache if needed).
  - [ ] Record that full-library CI is blocked by the out-of-scope HML defect (do not attempt to fix).
- **Timing:** ~1 hour (dominated by the first module build / cache fetch).
- **Depends on:** none
- **Files to modify:** none (setup + verification only).
- **Verification:** Worktree exists; both-primitive markers confirmed; `lake build Cslib.Logics.Modal.*`
  exits 0 with no errors.

### Phase 2: Cube.lean Validity wrappers (B / 4 / 5 / D) [COMPLETED]

- **Goal:** Complete the existing `section Validity` in `Cube.lean` with the four missing axiom-
  validity wrappers, mirroring `K.k_valid`/`T.t_valid`.
- **Green precedent (zero-sorry, cited):** `K.k_valid` (Cube.lean:130) and `T.t_valid` (Cube.lean:134)
  are the exact template; `Satisfies.b/.four/.five/.d` are already green in `Basic.lean` on the base.
  `T.t_valid`'s `grind [Satisfies.t (instRefl := (by assumption))]` is the instance-passing pattern.
- **Tasks:**
  - [x] Add `B.b_valid : (φ → □◇φ : Proposition Atom) ∈ B World Atom` — wrapper over `Satisfies.b`
        *(deviation: altered -- `Satisfies.b`'s `[Std.Symm m.r]` instance arg is anonymous in the
        actual Basic.lean signature, unlike `Satisfies.t`'s named `instRefl`, so the
        `(instSymm := (by assumption))` named-argument style does not apply; used
        `intro m h; haveI : Std.Symm m.r := h; intro w; exact Satisfies.b φ` instead — confirmed
        zero-goals via `lean_goal`)*.
  - [x] Add `Four.four_valid : (◇◇φ → ◇φ : Proposition Atom) ∈ Four World Atom` — wrapper over
        `Satisfies.four` *(deviation: altered -- same anonymous-instance pattern:
        `intro m h; haveI : IsTrans World m.r := h; intro w; exact Satisfies.four φ`)*.
  - [x] Add `Five.five_valid : (◇φ → □◇φ : Proposition Atom) ∈ Five World Atom` — wrapper over
        `Satisfies.five` *(deviation: altered -- `intro m h; haveI : Relation.RightEuclidean m.r := h;
        intro w; exact Satisfies.five φ`)*.
  - [x] Add `D.d_valid : (□φ → ◇φ : Proposition Atom) ∈ D World Atom` — wrapper over `Satisfies.d`
        *(deviation: altered -- `intro m h; haveI : Relation.Serial m.r := h; intro w;
        exact Satisfies.d φ`)*.
  - [x] Test each wrapper's tactic with `lean_multi_attempt` before finalizing; fall back to explicit
        intro + `Satisfies.*` application if `grind` regresses. *(grind regressed on all four
        non-T wrappers per the anonymous-instance issue above; used the explicit fallback for all
        four, confirmed sorry-free via `lean_goal` showing "no goals" at each proof's end)*.
  - [x] Confirm exact axiom shapes (`φ → □◇φ` for B, `◇φ → □◇φ` for 5, etc.) against the `Satisfies.*`
        signatures in `Basic.lean` via `lean_hover_info`. *(confirmed via direct Read of Basic.lean
        lines 248, 264, 281, 298 -- shapes match the plan exactly)*.
- **Timing:** ~1 hour.
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Cube.lean` — extend `section Validity` (~35 LOC added).
- **Verification:** `lake build Cslib.Logics.Modal.Cube` green; the four new theorems type-check with
  no `sorry`; `#print axioms` on each shows no new axioms beyond those Basic.lean already uses.

### Phase 3: Cube.lean Canonicity section (T / B / 4 / 5 / D frame determination) [COMPLETED]

- **Goal:** Add a new `section Canonicity` to `Cube.lean` giving Cube-level frame-determination
  wrappers over Basic.lean's already-green converse lemmas.
- **Green precedent (zero-sorry, cited):** `Satisfies.t_refl`, `.b_symm`, `.four_trans`,
  `.five_rightEuclidean`, `.d_serial` are already green on the base. The harder directions have
  worked precedents documented in report §5.2 (`five`/RightEuclidean via
  `Relation.RightEuclidean.rightEuclidean`) and §5.3 (`b_symm` via the `Classical.arbitrary`
  spy-valuation `let v := fun w' _ => w' = w₁`). Relation infra verified real: `Relation.Serial`
  (`Defs.lean:74`), `Relation.RightEuclidean` (`Defs.lean:49`), `Std.Refl`/`Std.Symm`, `IsTrans`,
  `Euclidean.lean` bridges.
- **Tasks:**
  - [x] Open `section Canonicity` with a `/-! ... -/` module note explaining the frame-determination
        direction (axiom global validity forces the frame condition).
        *(deviation: altered -- also required adding `open scoped InferenceSystem` immediately
        after `section Canonicity`: the `⇓` notation is `scoped` under the `Cslib.Logic.InferenceSystem`
        namespace and Basic.lean opens it file-locally at its line 123 -- that `open scoped` does
        NOT propagate to importing files, so Cube.lean needed its own `open scoped InferenceSystem`
        to parse `⇓Modal[...]` in the canonicity hypothesis types. Diagnosed via the "expected token"
        parse errors at the `⇓` position on first build attempt.)*
  - [x] `T.t_canonical` → `Std.Refl r`, wrapping `Satisfies.t_refl`.
  - [x] `B.b_canonical` → `Std.Symm r`, wrapping `Satisfies.b_symm` (spy-valuation gadget).
  - [x] `Four.four_canonical` → `IsTrans`, wrapping `Satisfies.four_trans`.
  - [x] `Five.five_canonical` → `Relation.RightEuclidean`, wrapping `Satisfies.five_rightEuclidean`.
  - [x] `D.d_canonical` → `Relation.Serial`, wrapping `Satisfies.d_serial`.
  - [x] Match each wrapper's hypothesis shape (global validity of the axiom, e.g.
        `∀ {v} {w} {φ}, ⇓Modal[⟨r,v⟩,w ⊨ φ → ◇φ]`) to the Basic.lean converse signature via
        `lean_hover_info`; test with `lean_multi_attempt`. *(matched exactly per the report's §3.4
        sketch and Basic.lean's `Satisfies.t_refl`/`.b_symm`/`.four_trans`/`.five_rightEuclidean`/
        `.d_serial` signatures (Read directly, lines 234-310); each Cube-level wrapper is a
        one-line `:= Satisfies.*_refl/... h` term-mode proof, confirmed sorry-free by `lean_goal`
        and the module build.)*
  - [x] Add `[Nonempty Atom]` where the spy-valuation requires an atom witness (B, and any using
        `Classical.arbitrary Atom`), matching the Basic.lean lemma constraints. *(added
        `[Nonempty Atom]` uniformly to all five canonicity wrappers, matching each underlying
        `Satisfies.*_refl/_symm/_trans/_rightEuclidean/_serial` constraint.)*
- **Timing:** ~1.5 hours (canonicity wrappers are the substantive new content).
- **Depends on:** 2 (same file; sequential to avoid `Cube.lean` territory conflict).
- **Files to modify:**
  - `Cslib/Logics/Modal/Cube.lean` — new `section Canonicity` (~70–110 LOC added).
- **Verification:** `lake build Cslib.Logics.Modal.Cube` green; all five canonicity theorems
  type-check with no `sorry`; no new axioms introduced.

### Phase 4: references.bib, docstrings, zero-sorry/axiom audit, single-commit prep [COMPLETED]

- **Goal:** Add the bibliography entry, document the new sections, prove zero-debt, and prepare a
  clean single-commit diff.
- **Tasks:**
  - [x] Add `ChagrovZakharyaschev1997` (box-first Chagrov & Zakharyaschev, *Modal Logic*) to
        `references.bib`, mirroring the existing `Blackburn2001` `@book` structure. Do **NOT** add
        `Avigad2022`. *(added as `@book{ChagrovZakharyaschev1997, ...}` right after `Blackburn2001`;
        confirmed `Avigad2022` absent via grep.)*
  - [x] Add/verify docstrings on the four new validity wrappers and five new canonicity wrappers, and
        a short module-level note for the `Canonicity` section; cite `ChagrovZakharyaschev1997` where a
        BibKey reference is expected by CSLib convention. *(all 9 new theorems have `/-- ... -/`
        docstrings; module-level `/-! ## Canonicity ... -/` note added citing
        `[ChagrovZakharyaschev1997]`; also added it to the file's top `## References` list alongside
        `Blackburn2001`.)*
  - [x] **Zero-sorry/axiom audit (hard gate):** `grep -rn "sorry\|admit" Cslib/Logics/Modal/Cube.lean`
        returns nothing; run `#print axioms` (or `lean_verify`) on every new theorem
        (`B.b_valid`, `Four.four_valid`, `Five.five_valid`, `D.d_valid`, `T.t_canonical`,
        `B.b_canonical`, `Four.four_canonical`, `Five.five_canonical`, `D.d_canonical`) and confirm
        only the standard classical axioms already relied on by Basic.lean appear — no new axioms.
        *(confirmed: grep returns nothing; `lean_verify` on all 9 theorems reports only
        `["propext", "Classical.choice", "Quot.sound"]` — no new axioms.)*
  - [x] Final module-scoped green build:
        `lake build Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Cube Cslib.Logics.Modal.Denotation Cslib.Logics.Modal.LogicalEquivalence`.
        *(green, 645/645 jobs.)*
  - [x] Prepare the clean single commit (message `task 486: complete modal cube validity + canonicity on #607`),
        confining the diff to `Cube.lean` + `references.bib` (plus the already-live 477 refactor carried
        by the base branch). Squash any intermediate WIP commits so the deliverable is one logical commit
        ready for `/pr` rebase onto fmontesi/connectives. *(squashed phase 2/3/4 WIP commits via
        `git reset --soft 70b7ec4d` + single recommit `4ebdba5`; diff confined to exactly the two
        intended files, 80 insertions, 0 deletions.)*
  - [x] **Unplanned bonus discovery (deviation: altered scope of "deferred" full-CI risk):** the plan's
        Risk table asserted full-library `lake build`/`checkInitImports`/`lint`/`lint-style`/`shake`/
        `test` was **certainly** (H likelihood) blocked by a pre-existing #607 `HML/LogicalEquivalence.lean`
        3-arg-vs-4-arg defect. This did **not** materialize on `origin/feat/modal-formula-primitives`=
        `70b7ec4d`: `lake build Cslib` (2759/2759), `lake exe checkInitImports` (exit 0), `lake lint`
        ("Linting passed for Cslib"), `lake exe lint-style` (exit 0), and `lake test` (8790/8790) **all
        passed cleanly**, full-library, no HML defect present on this base. `lake shake` surfaced only
        pre-existing suggestions unrelated to this diff (confirmed via `git show 70b7ec4d:...` that the
        one Cube.lean-related shake suggestion — an implicit `Relation.Euclidean` import — predates this
        task's edits, inherited from the existing `Five`/`D` defs). `lake exe mk_all --module` regenerated
        `CslibTests.lean` with unrelated syntax drift (pre-existing repo/toolchain skew, not part of this
        task's scope) — reverted via `git checkout -- CslibTests.lean` to keep the diff confined to
        `Cube.lean` + `references.bib` per the plan's Non-Goals. Full-library CI is therefore reported as
        **passing**, not deferred, in the final summary — a stronger result than the plan anticipated.
- **Timing:** ~0.5 hour.
- **Depends on:** 3
- **Files to modify:**
  - `references.bib` — add `ChagrovZakharyaschev1997` (~14 LOC).
  - `Cslib/Logics/Modal/Cube.lean` — docstrings only (~10 LOC).
- **Verification:** bib entry present and `Avigad2022` absent; audit shows zero sorry and no new
  axioms; module build green; git log shows a single clean task-486 commit on the PR-head lineage.

## Testing & Validation

- [x] Module-scoped build green at every phase gate: `lake build Cslib.Logics.Modal.Basic
      Cslib.Logics.Modal.Cube Cslib.Logics.Modal.Denotation Cslib.Logics.Modal.LogicalEquivalence`.
      Confirmed green at Phase 1 (pre-work), Phase 2, Phase 3, and Phase 4 (645/645 jobs each time).
- [x] All four validity wrappers (`B.b_valid`, `Four.four_valid`, `Five.five_valid`, `D.d_valid`)
      compile with no `sorry`. Confirmed via `lean_goal` ("no goals") and `lean_verify`.
- [x] All five canonicity wrappers (`T/B/Four/Five/D.*_canonical`) compile with no `sorry`. Confirmed
      via `lean_verify` (standard classical axioms only) and the module build.
- [x] `grep -rn "sorry\|admit" Cslib/Logics/Modal/Cube.lean` returns nothing. Confirmed (exit 1 / no
      matches).
- [x] `#print axioms` / `lean_verify` on each new theorem introduces no new axioms beyond Basic.lean's.
      All 9 report exactly `["propext", "Classical.choice", "Quot.sound"]`.
- [x] `references.bib` contains `ChagrovZakharyaschev1997` and does NOT contain `Avigad2022`. Confirmed
      via grep.
- [x] Diff confined to `Cube.lean` + `references.bib` (atop the already-live 477 refactor). Confirmed:
      `git diff 70b7ec4d --stat` shows exactly these two files, 80 insertions, 0 deletions.
- [x] Full-library CI (`checkInitImports`/`shake`/`test`) — **deviation: upgraded from "deferred" to
      "passing".** The plan's Risk table asserted this was certainly blocked by a pre-existing #607
      `HML/LogicalEquivalence.lean` defect; that defect did **not** reproduce on this base
      (`70b7ec4d`). `lake build Cslib` (2759/2759), `lake exe checkInitImports` (exit 0), `lake lint`
      ("Linting passed for Cslib"), `lake exe lint-style` (exit 0), and `lake test` (8790/8790) all
      pass full-library, with a clean `git status` (no incidental file drift left staged). `lake shake`
      surfaced only pre-existing suggestions unrelated to this diff.

## Artifacts & Outputs

- `plans/01_modal-cube-completion.md` (this plan)
- Worktree: `/home/benjamin/Projects/cslib-task-486-pr662-modal-package` on branch
  `task-486-pr662-modal-package` (off `origin/feat/modal-formula-primitives`)
- Modified `Cslib/Logics/Modal/Cube.lean` (validity + canonicity sections completed)
- Modified `references.bib` (`ChagrovZakharyaschev1997` added)
- Single clean commit `task 486: complete modal cube validity + canonicity on #607`
- `summaries/01_modal-cube-completion-summary.md` (produced at /implement)

## Rollback/Contingency

- All work is isolated in the `cslib-task-486-pr662-modal-package` worktree; the main checkout and
  `pr607`/`origin` refs are untouched. To abandon: `git worktree remove
  /home/benjamin/Projects/cslib-task-486-pr662-modal-package` and `git branch -D
  task-486-pr662-modal-package`.
- Because Phases 2–4 only **add** theorems and a bib entry (no edits to existing #607-owned lemmas),
  reverting any single phase is a localized deletion of the added `Cube.lean` section / bib entry with
  no impact on the live 477 refactor.
- If a canonicity direction cannot be discharged sorry-free within Phase 3 despite the green
  precedents, do NOT introduce a `sorry` or axiom (hard requirement). Instead mark Phase 3 [PARTIAL],
  commit the green validity work from Phase 2, and escalate with the exact failing goal state for a
  targeted follow-up — never ship debt.
