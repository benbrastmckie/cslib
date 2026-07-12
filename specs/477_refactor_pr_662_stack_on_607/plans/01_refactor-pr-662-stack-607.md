# Implementation Plan: Refactor PR #662 to Stack on PR #607 (box + diamond both primitive)

- **Task**: 477 - Refactor PR #662 (leanprover/cslib) to stack on PR #607 so both □ (box) and ◇ (dia) are primitive modal connectives
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: PR #607 (`fmontesi/connectives`) as the stacking base — present locally as branch `pr607`
- **Research Inputs**: specs/477_refactor_pr_662_stack_on_607/reports/01_refactor-pr-662-stack-607.md
- **Artifacts**: plans/01_refactor-pr-662-stack-607.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Rework PR #662's modal-logic contribution so it stacks on PR #607 instead of duplicating an
operator-typeclass layer. Per the task-476 Zulip settlement, the target is **both □ and ◇
primitive**. Following the research report's recommended Path 1, we keep #607's `{not, and}`
propositional base and its diamond-primitive `Proposition`, then **add `box` as a fifth primitive
constructor** — yielding `Proposition (Atom) = {atom, not, and, diamond, box}`. The
interdefinability law `◇φ ↔ ¬□¬φ` (`Satisfies.dual`) becomes a **derived theorem** proved from the
two now-primitive semantic clauses. #662's duplicate `Connectives.lean` is deleted in favor of
#607's `Operators.lean`, and `Modal/LogicalEquivalence.lean` is migrated to #607's new
`HasLogicalEquivalence` API. **Definition of done**: all touched modules `lake build` green, `lake
test` + `lake exe checkInitImports` + `lake exe lint-style` + `lake shake` pass, zero debt (no
`sorry`, no new axioms), and the stacked diff stays well under 500 LOC.

### Research Integration

Integrates report `01_refactor-pr-662-stack-607.md` in full:
- §2 reuse check (delete `Connectives.lean`; reuse #607 `Operators.lean` typeclasses).
- §4 file-by-file Path 1 refactor (the backbone of Phases 2–5).
- §5 design decision (propositional base stays `not/and`; `bot/imp` deferred to a follow-up).
- §6 LOC budget (~80–100, worst-case ~140) — enforced here with a per-phase running tally.
- §7 stacking mechanics — captured as Phase 6 (documentation only; no branch/PR work).
- §8 risks — carried into Risks & Mitigations below, including the **task-premise correction**:
  #607 is still diamond-primitive at its tip; making box primitive is precisely #662's contribution.

### Prior Plan Reference

No prior plan. This is the first plan for task 477.

### Roadmap Alignment

No ROADMAP.md consulted for this task (none provided in delegation context).

## Goals & Non-Goals

**Goals**:
- Make `Proposition` box-and-diamond both primitive: `{atom, not, and, diamond, box}`.
- Delete #662's `Connectives.lean`; reuse #607's `Operators.lean` typeclasses and notation.
- Derive `Satisfies.dual : ◇φ ↔ ¬□¬φ` (and optionally its companion) as honest semantic theorems.
- Migrate `Modal/LogicalEquivalence.lean` to #607's `HasLogicalEquivalence` API.
- Keep the stacked diff < 500 LOC (target ~80–140) with zero proof debt.
- Reach local build-green + full CI pipeline pass against #607's base.

**Non-Goals**:
- Converging the propositional base to `{bot, imp}` (Path 2) — deferred to a separate follow-up PR.
- Creating git branches, rebasing for GitHub, or submitting/retargeting the PR — handled later by
  `/pr`. Implementation stops at source-refactor + local build-green.
- Modifying downstream consumers beyond what the both-primitive change requires (e.g. #649/LTL).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task premise says "#607 makes both primitive" but #607's tip is still diamond-primitive | H | H | Treat "make box primitive" as #662's contribution ON TOP of #607; Phase 1 verifies #607's tip (`Operators.lean` present, `Proposition = {atom,not,and,diamond}`) before editing |
| Working tree currently on `main` (has `Connectives.lean`, no `Operators.lean`) — wrong base | H | H | Phase 1 establishes a local working state derived from `pr607` (the #607 head, exists locally) so the refactor compiles against the correct base; PR-level base targeting deferred to `/pr` |
| `grind` proofs (`k/t/b/four/five/d`, `dual`) fail after clauses change | M | M | Characterization lemmas become `rfl`; re-run `lake build Cslib.Logics.Modal.Basic`, adjust grind hints; keep zero-debt (no `sorry`) |
| `LogicalEquivalence` arity migration in Modal instance | M | M | Mirror #607's HML `HasLogicalEquivalence` instance exactly; ensure `HasInferenceSystem` instance present |
| Notation-precedence drift (#607 `Operators.lean` vs old #662 precedences) | M | L | Inherit all notation from `Operators.lean`; re-check parenthesization-sensitive proofs |
| Name drift `imp_iff_imp` (#607) vs `impl_iff_impl` (#662) | L | M | Standardize on #607's `imp_iff_imp`; do not reintroduce `impl_iff_impl` |
| LOC budget creep past 500 | M | L | Per-phase running LOC tally (below); STOP and reassess if cumulative Δ exceeds 250 |
| #607 not yet merged (moving target) | M | M | Rework now against local `pr607`; keep `backup/662-pre-rebase*` untouched; final rebase deferred to `/pr` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel. Phases 3 and 4 are independent (Denotation vs.
LogicalEquivalence) once the `box` constructor exists.

**Running LOC tally (net stacked Δ, relative to #607's branch)** — enforce < 500:
| After phase | Phase Δ (net) | Cumulative | Budget headroom |
|-------------|---------------|------------|-----------------|
| 1 | 0 (deletes 91 from #662 footprint) | 0 | 500 |
| 2 | +35 to +50 | 35–50 | ≥ 450 |
| 3 | +10 | 45–60 | ≥ 440 |
| 4 | +25 | 70–85 | ≥ 415 |
| 5 | +10 to +18 | 80–103 (worst ~140) | ≥ 360 |
| 6 | 0 (docs only) | 80–103 | ≥ 360 |

Each phase MUST record its actual `git diff --stat` net addition against the #607 base and update
this tally in the execution summary. **Hard stop**: if cumulative net Δ exceeds 250 LOC, halt and
reassess scope before continuing.

---

### Phase 1: Establish #607 base, delete Connectives.lean, fix imports [COMPLETED]

- **Goal:** Put the working tree on #607's base and remove the duplicate operator-typeclass file,
  reverting its import — a net-zero-LOC cleanup that unblocks every later phase.
- **Tasks:**
  - [ ] Confirm the working state is derived from `pr607` (the #607 head). Verify #607's tip:
    `Cslib/Foundations/Logic/Operators.lean` exists, and `Cslib/Logics/Modal/Basic.lean` has
    `Proposition = {atom, not, and, diamond}` (diamond primitive, `box := ¬◇¬φ` derived). Do NOT
    create GitHub branches or retarget any PR — local working state only.
  - [x] Delete `Cslib/Foundations/Logic/Connectives.lean` entirely (all its typeclasses —
    `HasBot/HasImp/HasAnd/HasOr/HasBox`, `PropositionalConnectives`, `ModalConnectives` — are
    provided by #607's `Operators.lean`). *(deviation: skipped -- the local `pr607` base branch
    never contains `Connectives.lean` in the first place; it is unique to the `feat/modal-formula-primitives`
    (#662) branch. Confirmed via `git show pr607:Cslib/Foundations/Logic/Connectives.lean` -> not
    found, and `git ls-tree -r pr607` listing only the split `Operators/*.lean` files. No deletion
    needed.)*
  - [x] In `Cslib.lean`, drop `public import Cslib.Foundations.Logic.Connectives`; ensure
    `Operators.lean` remains imported (already imported by #607). No net line addition.
    *(deviation: skipped -- `pr607`'s `Cslib.lean` never imports `Logic.Connectives`; it already
    imports each `Operators/{And,Box,Diamond,Iff,Impl,Not,Or,Tensor}.lean` split file.)*
  - [x] Confirm no other module imports `...Logic.Connectives` (grep); if any do, repoint to
    `Operators`. Verified: `grep -rn "Logic.Connectives" Cslib CslibTests Cslib.lean` on the
    `task-477-pr662-stack-607` branch (checked out from `pr607` at `/home/benjamin/Projects/cslib-task-477-pr662-stack-607`)
    returns no matches.

  **Base-establishment note**: Working state was NOT built by switching the main checkout to
  `pr607` (that would discard `specs/` task tracking and ~2,860 files of unrelated local-only
  CSLib development that has diverged far past both `pr607` and `feat/modal-formula-primitives`
  on `main` -- e.g. `main`'s `Connectives.lean` is now a 4-module shared foundation used by 34+
  files across Propositional/Modal/Temporal/Bimodal/LTL, built by many *other* local tasks after
  #662 was originally drafted; deleting it there would be a massive, out-of-scope blocker).
  Instead: `git branch task-477-pr662-stack-607 pr607`, then
  `git worktree add /home/benjamin/Projects/cslib-task-477-pr662-stack-607 task-477-pr662-stack-607`.
  All Phase 1-5 source edits happen in that worktree; `specs/` bookkeeping (this plan, metadata,
  handoff) stays on `main` in the primary checkout. Confirmed `Operators/*.lean` (split files, not
  a single `Operators.lean`) present and `Modal/Basic.lean` is `{atom, not, and, diamond}`
  (diamond primitive, `box := ¬◇¬φ` derived) -- matches the plan's Phase-1 verification intent.
  Baseline `lake build Cslib.Logics.Modal.{Basic,Denotation,LogicalEquivalence,Cube}` is green
  before any edits (648/648 jobs).
- **Files to modify:**
  - `Cslib/Foundations/Logic/Connectives.lean` — DELETE
  - `Cslib.lean` — remove Connectives import line
- **Timing:** ~45 min
- **Depends on:** none
- **Verification:**
  - `grep -r "Logic.Connectives" Cslib` returns nothing.
  - `lake build Cslib.Foundations.Logic.Operators` green.
  - Full `lake build` still green (nothing references the deleted file).
  - Record `git diff --stat` net Δ (expect ~0) in the running tally.

---

### Phase 2: Add `box` primitive to Basic.lean and derive `dual` [COMPLETED]

**Result**: `git diff --stat pr607 -- Cslib/Logics/Modal/Basic.lean` = 35 insertions(+), 17
deletions(-), net **+18 LOC** (under the planned +35 to +50 estimate -- removing the old derived
`Proposition.box`/`box_def` block offset most of the new box-clause additions). `lake build
Cslib.Logics.Modal.Basic` green, zero `sorry`, zero new `axiom` declarations. `Satisfies.dual` is
now proved via `simp only [iff_iff_iff, diamond_iff_exists, not_iff_not, box_iff_forall]` followed
by an explicit `constructor` with `by_contra`/`push Not` for the classical backward direction
(mirrors the plan's fallback path since a bare `by grind` did not close the quantifier-duality
goal on the first attempt -- `rintro`/`constructor` directly on the un-simplified `⇓Modal[...]`
goal also failed because the object-level `Proposition.iff`/`.imp`/`.and` do not unfold to a
meta `Iff`/`Function` without first rewriting via `Satisfies.iff_iff_iff`). Added the optional
companion `Satisfies.box_iff_not_diamond_not : □φ ↔ ¬◇¬φ` per the plan's "optionally add" note.
`Satisfies.box_iff_forall` reduced to `Iff.rfl` as expected.

- **Goal:** Make `box` a primitive constructor alongside #607's primitive `diamond`, giving both
  modalities primitive status, and turn interdefinability into a derived theorem.
- **Tasks:**
  - [ ] Ensure `Cslib/Logics/Modal/Basic.lean` imports `Cslib.Foundations.Logic.Operators` (as
    #607 does); do not re-import/define `Connectives`.
  - [ ] Add constructor `| box (φ : Proposition Atom)` to the `Proposition` inductive → primitives
    become `{atom, not, and, diamond, box}`.
  - [ ] Remove #607's derived `def Proposition.box := ¬◇¬φ` and its `box_def` grind lemma.
  - [ ] Point the `HasBox` instance at the new constructor:
    `instance : HasBox (Proposition Atom) := ⟨Proposition.box⟩`; add
    `@[scoped grind =] lemma Proposition.box_def : φ.box = □φ := rfl`.
  - [ ] Add the primitive `Satisfies` clause: `| .box φ => ∀ w', m.r w w' → Satisfies m w' φ`.
  - [ ] Reduce `Satisfies.box_iff_forall` to `Iff.rfl` (was `grind [Proposition.box]` in #607).
  - [ ] **Convert interdefinability to a derived theorem**: keep `Satisfies.dual : ◇φ ↔ ¬□¬φ` but
    prove it from the two primitive semantic clauses (`by grind`, or an explicit
    `constructor <;> ...` with `Classical.em` if grind needs a decidability nudge — mirror #662's
    existing `Satisfies.or_iff` pattern). Optionally add companion
    `Satisfies.box_iff_not_diamond_not : □φ ↔ ¬◇¬φ`.
  - [ ] Do NOT redefine `∧/∨/→/↔/¬/□/◇` notation — inherit from `Operators.lean`. Keep #607's
    rename `imp_iff_imp` (do not reintroduce `impl_iff_impl`).
  - [ ] Decide on `deriving DecidableEq, BEq` for the new inductive: retain only if a downstream
    consumer (e.g. Tableau) needs it; otherwise omit to shrink the diff.
- **Files to modify:**
  - `Cslib/Logics/Modal/Basic.lean` — add box constructor + clause + derived `dual`
- **Timing:** ~75 min
- **Depends on:** 1
- **Verification:**
  - `lake build Cslib.Logics.Modal.Basic` green; no `sorry`, no new axioms
    (`lean_verify Satisfies.dual` shows no added axioms).
  - `Satisfies.box_iff_forall` and `Satisfies.diamond_iff_exists` reduce to `rfl`.
  - Record net Δ (expect +35 to +50) in the running tally.

---

### Phase 3: Add `box` denotation clause to Denotation.lean [COMPLETED]

**Result**: `git diff --stat pr607 -- Cslib/Logics/Modal/Denotation.lean` = **+1 LOC** (under the
planned ~+10 estimate; no characterisation lemma was needed -- `satisfies_mem_denotation`'s
`induction φ generalizing w <;> grind` closed the new `box` case automatically, as did
`not_denotation` and `theoryEq_denotation_eq`, all unchanged). `lake build
Cslib.Logics.Modal.Denotation` green, zero `sorry`.

- **Goal:** Give the primitive `box` its set-theoretic denotation, keeping existing
  `not/and/diamond` denotation proofs intact.
- **Tasks:**
  - [ ] Add `| .box φ => {w | ∀ w', m.r w w' → w' ∈ φ.denotation m}` to `Proposition.denotation`
    (diamond clause stays as-is from main).
  - [ ] Verify existing `satisfies_mem_denotation` / `theoryEq_*` proofs still close; add a
    `box_denotation` characterization lemma only if `grind` needs it.
- **Files to modify:**
  - `Cslib/Logics/Modal/Denotation.lean` — add box denotation clause (+ optional lemma)
- **Timing:** ~30 min
- **Depends on:** 2
- **Verification:**
  - `lake build Cslib.Logics.Modal.Denotation` green; no `sorry`.
  - Record net Δ (expect ~+10) in the running tally.

---

### Phase 4: Add `box` context + migrate to HasLogicalEquivalence in Modal/LogicalEquivalence.lean [COMPLETED]

**Result**: `git diff --stat pr607 -- Cslib/Logics/Modal/LogicalEquivalence.lean` = **+9 LOC**
(well under the planned ~+25 estimate). *(deviation: the "migrate the framework instance from the
old 3-arg `LogicalEquivalence` to #607's `HasLogicalEquivalence`" sub-task was already satisfied
on the `pr607` base -- ground-truth read via `git show pr607:Cslib/Logics/Modal/LogicalEquivalence.lean`
shows `instance : HasLogicalEquivalence (Proposition Atom) (Judgement World Atom)` already present,
contradicting the research report's §3 claim that "#607 does not touch
`Modal/LogicalEquivalence.lean`" -- #607 has evidently been updated since the report was written.
Only the `box` `Context` constructor + `fill` clause + one `Congruence` induction arm (mirroring
`diamond`'s, using `∀ w'`/`intro` instead of `∃ w'`/`rintro`) were added.)* `lake build
Cslib.Logics.Modal.LogicalEquivalence` green, zero `sorry`.

- **Goal:** Extend congruence machinery to the `box` constructor and migrate the framework instance
  from the old 3-arg `LogicalEquivalence` to #607's `HasLogicalEquivalence`.
- **Tasks:**
  - [ ] Keep main's `Context = {hole, not, andL, andR, diamond}`; add `| box (c : Context Atom)`
    and its `fill` clause `| box c => □(c.fill φ)` (no `impL/impR` rewrite — `not/and` base kept).
  - [ ] Add the `box` case to the `Congruence` proof (one `induction` arm, analogous to `diamond`).
  - [ ] Migrate the framework instance from the old 3-arg
    `LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled` to #607's
    `HasLogicalEquivalence (Proposition Atom) (Judgement World Atom)`, mirroring #607's HML
    migration. Ensure `instance : HasInferenceSystem (Judgement World Atom) := ⟨Satisfies.Bundled⟩`
    is present (as #662 already adds).
- **Files to modify:**
  - `Cslib/Logics/Modal/LogicalEquivalence.lean` — box context + `HasLogicalEquivalence` migration
- **Timing:** ~60 min
- **Depends on:** 2
- **Verification:**
  - `lake build Cslib.Logics.Modal.LogicalEquivalence` green; no `sorry`.
  - Instance resolves under `≡[S]` notation as #607's HML instance does.
  - Record net Δ (expect ~+25) in the running tally.

---

### Phase 5: Cube.lean, GrindLint, references.bib, and full CI green [PARTIAL]

**BLOCKER** (Phase 5, full-library CI gate only):
- **What failed**: `lake exe checkInitImports`, `lake shake --add-public --keep-implied --keep-prefix`,
  and `lake test` all fail because `Cslib.lean` (the library aggregator both they and `CslibTests/*`
  transitively depend on) fails to build: `Cslib/Logics/HML/LogicalEquivalence.lean:105-106` has a
  type error (`Application type mismatch: ... Satisfies.Bundled ... expected ... Type ?u.8` /
  `failed to synthesize instance HasContext (Satisfies.Judgement State Label)`).
- **What was tried**: (1) Confirmed the failure is 100% pre-existing on the unmodified `pr607` tip
  and NOT introduced by this task -- `git stash`'d all task-477 edits, rebuilt
  `Cslib.Logics.HML.LogicalEquivalence` in isolation, got the identical error; `git diff pr607 --
  Cslib/Logics/HML/LogicalEquivalence.lean` is empty (file untouched). (2) Confirmed root cause:
  `Foundations/Logic/LogicalEquivalence.lean` on `pr607` already has the new 4-arg signature
  `class LogicalEquivalence S Proposition [HasContext Proposition] Judgement [HasHContext ...] [InferenceSystem S Judgement]`,
  but `Logics/HML/LogicalEquivalence.lean:105-106` still instantiates the *old* 3-arg form
  (`instance : LogicalEquivalence (Proposition Label) (Satisfies.Judgement State Label) (Satisfies.Bundled) where ...`)
  -- i.e. #607's own HML migration (claimed complete in the task-477 research report, §3) is
  incomplete/broken on this snapshot of `pr607`. (3) Confirmed the failure is isolated: no other
  file imports `Logics.Modal.*` besides `Cslib.lean` (`grep -rl "Logics.Modal" Cslib/ CslibTests/ Cslib.lean`),
  so this is unrelated to any Modal/box-primitive change made in Phases 2-4.
- **Why it's stuck**: This is a genuine, pre-existing defect in PR #607's own commit tree (HML is
  a separate logic module from Modal, and fixing its `LogicalEquivalence` instance requires
  understanding fmontesi's intended `HasContext (Satisfies.Judgement State Label)` design for
  HML specifically -- not researched or scoped for task 477, which is `Non-Goals`-scoped to
  "Modifying downstream consumers beyond what the both-primitive [Modal] change requires."
  Fixing it here would be uncontrolled scope creep into another PR's defect.
- **What is needed**: Either (a) fmontesi fixes HML's `LogicalEquivalence` instantiation upstream
  in #607 before it lands (recommended -- flag via the Zulip coordination channel, since this
  blocks #607's own `lake test`/CI on its current tip, independent of #662/task-477), or (b) a
  narrowly-scoped follow-up task explicitly chartered to migrate `HML/LogicalEquivalence.lean` to
  the new 4-arg `LogicalEquivalence`/`HasLogicalEquivalence` API (mirroring what #607 already did
  correctly for `Modal/LogicalEquivalence.lean` and CLL).
- **Prohibited workarounds**: Did NOT touch `Cslib/Logics/HML/LogicalEquivalence.lean`, did NOT
  add `sorry`, did NOT stub/skip the failing instance, did NOT weaken any Modal-side proof to
  route around it.

**What DID complete for Phase 5** (scoped, unaffected by the HML blocker):
- `Cube.lean`: confirmed **zero changes needed** -- `lake build Cslib.Logics.Modal.Cube` green;
  no `Relation.Euclidean` import addition required (unlike #662's original branch, `Basic.lean`
  on `pr607` already imports it), matching the plan's "expect no change" prediction exactly.
  `k_valid`/`t_valid`/order lemmas (`k_subset_d`, etc.) are untouched and unaffected by the
  primitive-set change since they only reference `Satisfies.k`/`Satisfies.t`/`logic`/`K`/`T` by
  name, not `box_iff_forall`'s proof term.
- `CslibTests/GrindLint.lean`: **zero skip entries added** -- the only new `@[scoped grind]`-tagged
  declaration introduced is `Proposition.box_def`, which mirrors the existing, already-unskipped
  `Proposition.{not,and,diamond}_def` pattern (none of those three appear in `pr607`'s
  `GrindLint.lean` skip list, confirmed via `grep -n "Modal" CslibTests/GrindLint.lean` -> no
  matches). By the same pattern, `box_def` should not require a skip either. **This could not be
  empirically verified** by actually running `#grind_lint check` because `CslibTests/GrindLint.lean`
  does `import Cslib` (the whole aggregator), which is blocked by the HML defect above -- flagged
  as an open item for whoever resolves the HML blocker to re-run.
- `references.bib`: added `ChagrovZakharyaschev1997` (+10 lines; did NOT add `Avigad2022`, per
  plan). Also added a short module-docstring paragraph to `Modal/Basic.lean` motivating
  both-primitive design and citing both `[Blackburn2001]` (diamond-first) and
  `[ChagrovZakharyaschev1997]` (box-first) so the new bib entry is actually referenced, not orphaned.
  `lake build Cslib.Logics.Modal.Basic` confirms the citation resolves.

**Verification actually run and green** (scoped, not blocked by HML):
- `lake build Cslib.Logics.Modal.{Basic,Denotation,LogicalEquivalence,Cube}` -- green.
- `lake exe lint-style Cslib.Logics.Modal.{Basic,Denotation,LogicalEquivalence}` -- exits 0, no
  style errors reported (text-based linter does not require full-library elaboration).
- Zero `sorry` in all 3 touched Modal files (`grep -n "\bsorry\b"` on each -- no matches).
- Zero new `axiom` declarations introduced (no `axiom` keyword appears in any diff hunk).

**Verification blocked by the pre-existing HML defect (NOT run to completion)**:
- `lake exe checkInitImports` -- fails: `Cslib.olean` does not exist (whole-aggregator build
  failure via HML).
- `lake shake --add-public --keep-implied --keep-prefix` -- fails: same root cause.
- `lake test` -- fails: same root cause (confirmed via full run; `CslibTests.{CCS,CLL,Bisimulation,
  DFA,HML,FreeMonad,HasFresh,Reduction,LTS,LambdaCalculus,MLL}` all build fine up to the point
  `Cslib.Logics.HML.LogicalEquivalence` is reached, which fails and halts further aggregator-
  dependent targets including `CslibTests.GrindLint`).

**LOC tally (net stacked Δ vs `pr607`, actual)**:
| File | Net Δ |
|------|-------|
| `Cslib/Logics/Modal/Basic.lean` | +46 (63 ins / 17 del) |
| `Cslib/Logics/Modal/Denotation.lean` | +1 |
| `Cslib/Logics/Modal/LogicalEquivalence.lean` | +9 |
| `references.bib` | +10 |
| **Total** | **+66 / -17 = net +49 LOC** |

Well under the 500-LOC target and under the 250-LOC hard-stop; smaller than the plan's ~80-140
estimate because Phase 1 needed 0 LOC on this base (no `Connectives.lean` to delete) and Phase 4's
`HasLogicalEquivalence` migration was already done upstream in #607.

- **Goal:** Close out the remaining touch points and prove the whole stack green end-to-end.
- **Tasks:**
  - [x] `Cslib/Logics/Modal/Cube.lean`: expect no change beyond the `import ...Relation.Euclidean`
    line #662 already adds. Verify `four/b/five/d` still close under both-primitive
    characterizations (now `rfl`); adjust grind hints only if needed. *(deviation: altered --
    zero changes needed at all, not even the import: `pr607`'s `Modal/Basic.lean` already imports
    `Cslib.Foundations.Relation.Euclidean` directly, so `Cube.lean` needed no edit. `lake build
    Cslib.Logics.Modal.Cube` confirmed green unchanged.)*
  - [x] `CslibTests/GrindLint.lean`: register `#grind_lint skip` entries only for the NEW
    `@[scoped grind]` modal lemmas that remain (e.g. new `box_denotation` / derived `dual` if
    tagged). Drop skips for lemmas that no longer exist. Keep the list minimal. *(deviation:
    altered -- reasoned by analogy (no skip needed, matching unskipped `not_def`/`and_def`/
    `diamond_def`) rather than empirically verified, since `#grind_lint check` requires `import
    Cslib`, which is blocked by the pre-existing HML defect documented above. File left unchanged.)*
  - [x] `references.bib`: add `ChagrovZakharyaschev1997` (box-first presentation, cited in
    Basic.lean docstring). Do NOT add `Avigad2022` (only cited by the deleted `Connectives.lean`).
    `Blackburn2001` already exists on main. Done -- also added a short docstring paragraph to
    `Modal/Basic.lean` citing both `[Blackburn2001]` and `[ChagrovZakharyaschev1997]` so the new
    entry is not orphaned.
  - [~] Run the full CI pipeline and fix any fallout. *(deviation: altered -- scoped
    `lake build`/`lake exe lint-style` on the 3 touched Modal files ran clean; whole-library
    `lake exe checkInitImports`/`lake shake`/`lake test` are blocked by a pre-existing, out-of-scope
    defect in `Cslib/Logics/HML/LogicalEquivalence.lean` on the `pr607` base -- see BLOCKER above.
    No fallout from task-477's own changes was found; the blocking fallout is #607's own.)*
- **Files to modify:**
  - `Cslib/Logics/Modal/Cube.lean` — import / verification (0–5 LOC) *(actual: 0 LOC)*
  - `CslibTests/GrindLint.lean` — trim skip list (1–3 LOC) *(actual: 0 LOC, unverifiable -- see above)*
  - `references.bib` — `+ChagrovZakharyaschev1997` (~8 LOC) *(actual: +10 LOC)*
- **Timing:** ~60 min
- **Depends on:** 3, 4
- **Verification:**
  - `lake build` (whole library) green. **BLOCKED** by pre-existing HML defect (not task-477's).
  - `lake test` green. **BLOCKED** by pre-existing HML defect (not task-477's).
  - `lake exe checkInitImports` passes. **BLOCKED** by pre-existing HML defect (not task-477's).
  - `lake exe lint-style` passes. **PASSED** (scoped to the 3 touched Modal files).
  - `lake shake --add-public --keep-implied --keep-prefix` clean. **BLOCKED** by pre-existing HML
    defect (not task-477's).
  - Zero `sorry` across touched modules; no new axioms. **PASSED** (verified via grep on all 3
    touched files).
  - Record final cumulative net Δ and confirm < 500 (target ≤ ~140) in the running tally.
    **PASSED**: net +49 LOC (see tally above), under target.

---

### Phase 6: Stacking-mechanics coordination note (documentation only) [COMPLETED]

**Coordination note** (captured here per plan instructions; no branch/PR operations performed):

(a) **Stacking base**: The reworked #662 modal-primitives commit was built as local branch
`task-477-pr662-stack-607`, created from local branch `pr607` (`git branch
task-477-pr662-stack-607 pr607`) and checked out in a dedicated worktree at
`/home/benjamin/Projects/cslib-task-477-pr662-stack-607` (kept separate from the primary
`/home/benjamin/Projects/cslib` checkout on `main`, which carries `specs/` task-tracking plus
~2,860 files of unrelated local-only CSLib development that has diverged far past both `pr607` and
`feat/modal-formula-primitives`). When `/pr` later prepares the real submission, it should rebase
`feat/modal-formula-primitives` (#662) onto `fmontesi/connectives` (#607's actual head) rather than
onto `main`, and can use `task-477-pr662-stack-607`'s 3-file diff (Basic/Denotation/
LogicalEquivalence + references.bib) as the reference patch.

(b) **LogicalEquivalence migration status -- correction to the research report**: the report's §3
claim that "#607 does not touch `Modal/LogicalEquivalence.lean`" is **out of date**: on the current
`pr607` tip, `Modal/LogicalEquivalence.lean` already uses the new `HasLogicalEquivalence` API
(`instance : HasLogicalEquivalence (Proposition Atom) (Judgement World Atom) where ...`). So #662
no longer needs to *complete* that migration for Modal -- only add the `box` `Context`
constructor/case. **However**, a *different*, previously unflagged problem was found during Phase
5 verification: `Logics/HML/LogicalEquivalence.lean` (also part of #607, a different logic module
entirely) still instantiates the *old* 3-arg `LogicalEquivalence` class signature and fails to
build against #607's own updated `Foundations/Logic/LogicalEquivalence.lean`. This is pre-existing
on `pr607` (verified via `git stash` + isolated rebuild) and blocks `lake exe checkInitImports`,
`lake shake`, and `lake test` for the *entire* library, independent of anything task 477 changed.
**This should be flagged to fmontesi as a blocker for #607 landing in a green state**, separate
from and prior to any #662 stacking concern.

(c) **Downstream #649 (LTL)**: per the existing Zulip draft
(`specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md`), #649 rebases onto
whichever of {#607, #662} lands first; nothing in this task's findings changes that guidance.

(d) **Backups**: `backup/662-pre-rebase`, `backup/662-pre-rebase-jul11`, and other
`backup/*-pre-rebase*` branches (pre-existing, untouched by this task) continue to preserve the
pre-rework #662 tip. `task-477-pr662-stack-607` is an additional, separate new branch/worktree; it
does not overwrite or rebase any existing branch.

(e) **Explicitly out of scope here (deferred to `/pr`)**: no GitHub branch was pushed, no PR base
was retargeted, and no PR was created or updated. All work is local-only per the task instructions.

- **Goal:** Record the stacking/rebasing coordination facts for the later `/pr` step WITHOUT
  executing any branch or PR operation.
- **Tasks:**
  - [x] Write a short coordination note (in the execution summary) capturing: (a) #662's reworked
    commit stacks on `fmontesi/connectives` (#607 head), rebasing `feat/modal-formula-primitives`
    onto `pr607` rather than `main`; (b) the reworked #662 *completes* the `LogicalEquivalence`
    migration for the Modal layer (parallel to #607's HML/CLL changes) — flag this to fmontesi;
    (c) downstream #649 (LTL) rebases onto whichever of {#607, #662} lands first; (d) backups
    `backup/662-pre-rebase*` preserve the pre-rework tip. *(deviation: altered -- point (b) is
    corrected in the note above: #607's Modal `LogicalEquivalence` migration was ALREADY complete
    on the verified `pr607` tip, so #662 does not need to complete it; instead a DIFFERENT
    pre-existing #607 defect was found in `HML/LogicalEquivalence.lean`, which is what actually
    needs flagging to fmontesi.)*
  - [x] Explicitly note that branch creation, GitHub base retargeting, and PR submission are
    OUT of scope here and are handled by `/pr`. Confirmed: no branch was pushed, no PR touched.
- **Files to modify:**
  - none (documentation captured in the execution summary)
- **Timing:** ~20 min
- **Depends on:** 5
- **Verification:**
  - Coordination note present in the summary; no git branch/PR side effects performed. **PASSED**.

---

## Testing & Validation

- [~] `lake build` (full library) green after Phase 5. Scoped Modal build green; whole-library
  build blocked by pre-existing `pr607`/HML defect (see Phase 5 BLOCKER).
- [~] `lake test` (CslibTests suite) green. Blocked by the same pre-existing HML defect.
- [~] `lake exe checkInitImports` passes. Blocked by the same pre-existing HML defect.
- [x] `lake exe lint-style` passes. Passed for all 3 touched Modal files.
- [~] `lake shake --add-public --keep-implied --keep-prefix` clean. Blocked by the same
  pre-existing HML defect.
- [x] No `sorry` and no new axioms in any touched module. Verified via `grep -n "\bsorry\b"` (no
  matches in any of the 3 touched files) and manual diff review (no `axiom` keyword added).
- [x] `grep -r "Logic.Connectives" Cslib` returns nothing. Confirmed on the `task-477-pr662-stack-607`
  branch (the file never existed on the `pr607` base to begin with).
- [x] Cumulative net stacked Δ < 500 LOC (target ≤ ~140), recorded in the running tally. **+49 LOC
  net**, well under target.
- [x] `Proposition` primitives are exactly `{atom, not, and, diamond, box}` (both modalities
  primitive); `Satisfies.dual` is a derived theorem, not `Iff.rfl` by definition. Confirmed: the
  `Proposition` inductive now has exactly 5 constructors, and `Satisfies.dual`'s proof is a
  multi-step classical argument (`simp only [...]` + `constructor` + `by_contra`/`push Not`), not
  `:= Iff.rfl` or `iff_iff_iff.mpr Iff.rfl`.

## Artifacts & Outputs

- `specs/477_refactor_pr_662_stack_on_607/plans/01_refactor-pr-662-stack-607.md` (this plan)
- `specs/477_refactor_pr_662_stack_on_607/summaries/01_refactor-pr-662-stack-607-summary.md`
  (execution summary — includes the final LOC tally and the Phase 6 coordination note)
- Reworked source, actual (local branch `task-477-pr662-stack-607`, based on `pr607`, checked out
  in worktree `/home/benjamin/Projects/cslib-task-477-pr662-stack-607` -- NOT the primary
  `/home/benjamin/Projects/cslib` checkout, which stays on `main` for `specs/` tracking):
  - `Cslib/Foundations/Logic/Connectives.lean` — N/A, never existed on `pr607`
  - modified `Cslib/Logics/Modal/Basic.lean` (+63/-17), `Cslib/Logics/Modal/Denotation.lean` (+1),
    `Cslib/Logics/Modal/LogicalEquivalence.lean` (+9), `references.bib` (+10)
  - `Cslib.lean`, `Cslib/Logics/Modal/Cube.lean`, `CslibTests/GrindLint.lean` — unchanged (no edit
    needed on this base; see Phase 1/5 deviation notes)

## Rollback/Contingency

- All work is local against a `pr607`-derived working state; `backup/662-pre-rebase*` branches
  preserve the pre-rework #662 tip for full recovery.
- Per-phase builds are independent checkpoints: if a phase's `lake build` fails and cannot be made
  green without debt, revert that phase's edits (`git checkout -- <file>`) and reassess — never
  introduce `sorry` or a new axiom to force green.
- If the cumulative net Δ approaches the 250-LOC hard stop, halt and reconsider scope (e.g. drop the
  optional `deriving`/companion lemma) before proceeding.
- No branch/PR side effects are performed here, so rollback never requires undoing remote state;
  `/pr` handles all branch and submission operations later.
