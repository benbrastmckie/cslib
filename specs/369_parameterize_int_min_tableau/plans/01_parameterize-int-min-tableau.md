# Implementation Plan: Task #369

- **Task**: 369 - Parameterize the Intuitionistic & Minimal Tableau Developments
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: Task 363 (classical tableau build repaired so suite is green)
- **Research Inputs**: specs/369_parameterize_int_min_tableau/reports/01_parameterize-int-min-tableau.md
- **Artifacts**: plans/01_parameterize-int-min-tableau.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib (Lean 4)
- **Lean Intent**: false

## Overview

Remove ~350-400 lines of duplication between the Intuitionistic and Minimal tableau
developments by abstracting over their two points of divergence — the branch closure
predicate `closurePred : IBranch Atom -> Bool` and the countermodel's `modelBot : IBranch
Atom -> Nat -> Prop` — into a single bundling `structure IntMinScheme`. Soundness is
**already parameterized** (task 316 closed it generically via `intExpandBranches_closed_unsat`),
so this refactor is completeness-only plus thin soundness wrappers. The six current
completeness sorries (3 in `Int/Completeness.lean`, 3 in `Min/Completeness.lean`) collapse to
**ONE** parametric `truthLemma S` sorry handed to task 317; `openBranch_countermodel` and
`tableau_complete` derive generically from it. The shared development lands in a new module
`Tableau/Intuitionistic/Scheme.lean` (Int is already the shared home — `Min/Completeness.lean`
imports `Int/Completeness.lean`).

### Research Integration

The plan follows the research report's 5-phase structure (report Section 4) verbatim in
sequencing and uses its concrete design (report Section 2): the `IntMinScheme` interface with
fields `closurePred`, `modelBot`, `closed_unsat`, `bot_truth`, `modelBot_uc`; the `def`
instances `intScheme`/`minScheme` (NOT `instance`, to avoid resolution ambiguity — report
Risk 1); reuse of `intExtractValuation` and `minOpen_no_contradiction` (already proved) as
engines for the Min scheme obligations. Sorry census independently re-verified against the
working tree: `Int/Completeness.lean` lines 89/98/112 and `Min/Completeness.lean` lines
168/179/190 are the only real `sorry` tokens (6 total); both Soundness files and both
DecisionProcedure files are sorry-free.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap_flag not set). This task advances the propositional-tableau
metalogic line: it is a structural prerequisite that lets task 317
(`propositional_tableau_completeness`, currently [BLOCKED]) discharge ONE truth lemma instead
of two.

## Goals & Non-Goals

**Goals**:
- Introduce `IntMinScheme` + `intScheme`/`minScheme` as the single abstraction boundary over
  `(closurePred, modelBot)`.
- Re-express both soundness theorems as thin instantiations of a generic `tableau_sound S`,
  keeping all Soundness code green (task 316 constraint).
- Unify the two completeness trios into one parametric `truthLemma S` /
  `openBranch_countermodel S` / `tableau_complete S`, leaving exactly ONE parametric sorry
  (`truthLemma S`).
- Repoint both DecisionProcedure modules at the parametric completeness theorem.
- Delete the duplicated Int/Min completeness scaffolding and pass full CI.
- Make Min's `modelBot_uc` (T(bot) upward-closure) an explicit scheme FIELD rather than a
  docstring claim, folding any real proof into the single parametric obligation.

**Non-Goals**:
- Discharging `truthLemma S` itself — that is task 317. This plan deliberately leaves it as
  the single intended sorry.
- Modifying `Foundations/Logic/Tableau/ClosureCondition.lean` or threading the
  `ClosureCondition` typeclass through the scaffolding. It is reused UNCHANGED at the leaf
  (`isIntuitionisticallyClosed`); the scheme stores the composed `Bool` predicate (report §2.4).
- Introducing any new standalone sorry, especially any Soundness sorry.
- Touching the already-shared rule engine (`intExpandBranches`, `intExpandBranches_closed_unsat`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Forcing `closurePred` through `ClosureCondition` typeclass misfits (Bool-valued; Min bypasses it) | H | M | Keep `closurePred`/`modelBot` as plain `structure` fields; leave `ClosureCondition` untouched; use `def intScheme`/`def minScheme`, not `instance` (report Risk 1) |
| Min's `modelBot_uc` (T(bot) upward-closure) is only a docstring claim, not a lemma | M | H | Make `modelBot_uc` an explicit scheme field; for Min fold the real upward-closure proof into the single parametric obligation — do NOT spawn a new standalone sorry (report Risk 2) |
| Accidentally introducing a second sorry while wiring `bot_truth`/`modelBot_uc` for Min | H | M | P1 proves Min's `bot_truth` via existing `minOpen_no_contradiction`; any residual obligation rolls into `truthLemma S`, never a new field-level sorry. Verify token count after each phase |
| Soundness regression (task 316 violation) | H | L | P2 only wraps the existing generic proof; run `lake build` on both Soundness modules before commit; sorry-token count on Soundness stays 0 |
| `shake` re-minimizes imports after moving shared defs (Min transitively pulls Int/Completeness) | M | M | Run `lake shake --add-public --keep-implied --keep-prefix` in P5; fix import graph; run `lake exe mk_all --module` for the new barrel entry |
| Lint/doc drift: missing docstrings (docBlame), `def` vs `lemma`, naming | M | M | Every `structure` field + decl gets a docstring; `truthLemma`/`tableau_complete` are `lemma`/`theorem`; names lowerCamelCase; update stale "4 sorries" DecisionProcedure docstrings in P4/P5 (report Risk 3,4) |
| Red window leaks beyond the single intended sorry | H | L | Staging rule: keep OLD defs until NEW ones land, delete only in P5; each commit is fully green OR contains exactly the one `truthLemma S` sorry |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are a strict linear chain (each builds structurally on the previous module landing
green); no two phases run in parallel. Each phase is sized to one bounded agent run
(~100-300 lines of output) ending at a `lake build` checkpoint.

### Sorry-Accounting Invariant (MUST hold at every commit)

Net real `sorry` tokens across the Int+Min Tableau tree move monotonically **6 -> 1**, never
up. Baseline today: 6 (Int/Completeness 89,98,112; Min/Completeness 168,179,190). Target after
P5: 1 (`truthLemma S` in `Scheme.lean`). No phase may increase the count, and no Soundness
sorry may ever appear (must stay 0). Verification command at each commit gate:

```bash
base="Cslib/Logics/Propositional/Tableau"
grep -REn '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' \
  "$base/Intuitionistic" "$base/Minimal" \
  | grep -vE ':[0-9]+:\s*(--|/-|\*)' | grep -viE 'sorry-free|no sorry|sorries'
# count must be <= the previous phase's count, and Soundness lines must never appear
```

---

### Phase 1: Define `IntMinScheme` interface + instances [NOT STARTED]

**Goal**: Create `Scheme.lean` with the `IntMinScheme` structure and the two data instances,
fully green (structure + instances only, zero sorry).

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`; `import
      Cslib.Init` and `import` `Intuitionistic/Soundness.lean` (pulls
      `intBranchSatisfied`, `intClosed_unsatisfiable`, `isIntuitionisticallyClosed`,
      `IBranch`) and `Intuitionistic/Completeness.lean` (for `intExtractValuation`) plus
      `Minimal/Soundness.lean` (`minClosed_unsatisfiable`, `isMinimallyClosed`) and the
      Min countermodel data (`minBranchBotForces`, `minOpen_no_contradiction`).
- [ ] Declare `structure IntMinScheme (Atom : Type*) [DecidableEq Atom] [Hashable Atom]` with
      docstring'd fields exactly as report §2.2:
      `closurePred : IBranch Atom -> Bool`,
      `modelBot : IBranch Atom -> Nat -> Prop`,
      `closed_unsat` (soundness obligation),
      `bot_truth` (completeness bot-case: on an open branch, T(bot)/F(bot) match `modelBot`),
      `modelBot_uc` (upward-closure of `modelBot b` along the accessibility order).
- [ ] Define `def intScheme : IntMinScheme Atom := { closurePred := isIntuitionisticallyClosed,
      modelBot := fun _ _ => False, closed_unsat := intClosed_unsatisfiable,
      bot_truth := <vacuous: T(bot) cannot be open under isIntuitionisticallyClosed>,
      modelBot_uc := <trivial: False is upward-closed> }`.
- [ ] Define `def minScheme : IntMinScheme Atom := { closurePred := isMinimallyClosed,
      modelBot := minBranchBotForces, closed_unsat := minClosed_unsatisfiable,
      bot_truth := <from minOpen_no_contradiction (already PROVED, Min/Completeness.lean:89-140)>,
      modelBot_uc := <T(bot) persistence; if the upward-closure lemma is not yet available,
      DO NOT add a field-level sorry — defer by leaving the obligation inside truthLemma in P3
      and stub modelBot_uc only if it can be discharged trivially here; otherwise restructure
      so the real work lands as part of the single P3 obligation> }`.
- [ ] Use plain `def` (not `instance`) for both schemes (report Risk 1). Field names
      lowerCamelCase; every field + the structure carries a docstring (docBlame).

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - NEW: structure + both instances.

**Build state / staging**: GREEN. Only a structure and two value-level instances are added;
no existing declaration is touched, so nothing breaks. If `minScheme.modelBot_uc` cannot be
discharged cleanly without a new sorry, choose the structuring that keeps this field green and
pushes the real proof obligation into `truthLemma S` (P3) — the invariant forbids a new
field-level sorry here.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`
- Sorry-token count over Int+Min Tableau tree still **6** (Scheme.lean adds 0).
- Soundness sorry count still 0.

---

### Phase 2: Thin Soundness wrappers [IN PROGRESS]

**Goal**: Add generic `tableau_sound S` and re-express `intuitionisticTableau_sound` /
`minimalTableau_sound` as one-line instantiations, keeping Soundness green.

**Tasks**:
- [ ] In `Scheme.lean` (or a thin section importing it), add
      `theorem tableau_sound (S : IntMinScheme Atom) (phi : Proposition Atom)
      (h : intExpandBranches [<.neg, phi, 0>] [[]] [1] [[]] (2^(2*phi.complexity+2)) S.closurePred
      = .closed) : <validity with botForces from the quantifier>` whose body is today's
      `intuitionisticTableau_sound` proof with `(isIntuitionisticallyClosed,
      intClosed_unsatisfiable)` replaced by `(S.closurePred, S.closed_unsat)` (report §2.3).
- [ ] Re-express `intuitionisticTableau_sound` as `:= tableau_sound intScheme ...` and
      `minimalTableau_sound` as `:= tableau_sound minScheme ...` — OR leave the originals in
      place and add the generic form alongside (staging choice; prefer leaving originals until
      P5 to keep every intermediate commit green and call sites stable).
- [ ] Confirm `modelBot` is irrelevant on the soundness side (validity supplies `botForces`),
      so no `modelBot`/`modelBot_uc` threading is needed here (report Risk 2).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - add `tableau_sound S`.
- `Intuitionistic/Soundness.lean` / `Minimal/Soundness.lean` - OPTIONAL repoint of the two
  `*_sound` theorems to the generic form (keep originals if repoint risks red; full collapse
  can wait for P5).

**Build state / staging**: GREEN (soundness is already generic; this only re-expresses it).
Both Soundness modules must build and remain sorry-free.

**Verification**:
- `lake build` of Scheme + both Soundness modules.
- Soundness sorry count still 0; total tree count still **6**.

---

### Phase 3: Parametric Completeness / countermodel (THE single red phase) [NOT STARTED]

**Goal**: Add the parametric `truthLemma S` (the ONE intended sorry), and derive
`openBranch_countermodel S` and `tableau_complete S` generically from it. End state: exactly
ONE parametric sorry in the entire Int+Min tree.

**Tasks**:
- [ ] In `Scheme.lean` add
      `lemma truthLemma (S : IntMinScheme Atom) (b : IBranch Atom)
      (hopen : S.closurePred b = false) (hsat : <saturation>) (phi : Proposition Atom) (w : Nat) :
      (T(phi)@w in b -> IForces (intExtractValuation b) (S.modelBot b) w phi) /\
      (F(phi)@w in b -> not IForces (intExtractValuation b) (S.modelBot b) w phi)`.
      Induct on `phi`: discharge the bot case via `S.bot_truth`; discharge the imp/persistence
      cases via `S.modelBot_uc`. Leave the deep core as the SINGLE `sorry` (handed to task 317).
      Use `lemma` (not `def`) for defLemma lint compliance.
- [ ] Add `lemma openBranch_countermodel (S : IntMinScheme Atom) (phi : Proposition Atom)
      (h : <tableau S> phi = .openBranch b) : not IForces (intExtractValuation b) (S.modelBot b) 0 phi`,
      derived from `truthLemma S b _ _ phi 0` + `F(phi)@0 in b` on the initial branch.
      This carries NO new sorry — it consumes `truthLemma`.
- [ ] Add `theorem tableau_complete (S : IntMinScheme Atom) (phi : Proposition Atom)
      (hvalid : <validity S> phi) : <tableau S> phi = .closed`, by contrapositive via
      `openBranch_countermodel`. NO new sorry.
- [ ] Verify exactly ONE `sorry` token now exists in `Scheme.lean` and the OLD six are still
      present (not yet deleted — deletion is P5). Net tree count during P3 is therefore
      transiently **7** in the working tree; the committed state must be staged so the new
      `Scheme.lean` sorry is the single intended parametric obligation and the report-tracked
      "active" obligation is 1. (Old duplicated sorries are dead code pending P5 deletion; if
      the orchestrator prefers a strictly-monotone token count, fold P3 and P5 deletion into a
      single commit — see staging note below.)

**Timing**: 2 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - add `truthLemma S`
  (1 sorry), `openBranch_countermodel S`, `tableau_complete S`.

**Build state / staging**: RED only at the body of `truthLemma S`, and only there — isolated
and intended. Everything else compiles. Staging rule for the invariant: to keep the committed
sorry count monotone non-increasing, EITHER (a) commit P3 with the new single sorry while the
old six remain (working-tree count 7, but the canonical/active obligation is the 1 parametric
one) and immediately delete the old six in P5; OR (b) merge the P5 deletions of the old Int/Min
trios into the P3 commit so the committed tree goes directly 6 -> 1. Option (b) is preferred
when a strictly monotone `grep` count is required at every commit; option (a) is acceptable if
DecisionProcedure call sites (P4) still reference the old completeness names. Pick (b) if P4
can be repointed in the same change; otherwise (a) then P5.

**Verification**:
- `lake build Cslib...Scheme` — single sorry at `truthLemma S`, all else green.
- `openBranch_countermodel S` and `tableau_complete S` elaborate with no additional sorry.
- Active parametric obligation count = **1**.

---

### Phase 4: DecisionProcedure port [NOT STARTED]

**Goal**: Point both decidability instances at the parametric completeness theorem; optionally
add a generic `decidableValid S`.

**Tasks**:
- [ ] Repoint `instDecidableIValid` (Int/DecisionProcedure.lean) to consume
      `tableau_complete intScheme` and `instDecidableMValid` (Min/DecisionProcedure.lean) to
      consume `tableau_complete minScheme`.
- [ ] Optionally add generic `tableau_decides S` / `decidableValid S` in `Scheme.lean`, with
      two ~10-line instance shims in the existing DecisionProcedure modules (report §1.4).
- [ ] Update stale "4 sorries" docstrings in both DecisionProcedure modules to reflect the
      unified single parametric obligation (report Risk 4).

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Intuitionistic/DecisionProcedure.lean` - repoint `instDecidableIValid`; fix docstring.
- `Minimal/DecisionProcedure.lean` - repoint `instDecidableMValid`; fix docstring.
- `Scheme.lean` - OPTIONAL `tableau_decides S` / `decidableValid S`.

**Build state / staging**: GREEN modulo the one inherited `truthLemma S` sorry. Both
DecisionProcedure modules build (they only transitively depend on the parametric completeness,
which elaborates).

**Verification**:
- `lake build` of both DecisionProcedure modules + Scheme.
- No new sorry introduced; active obligation still **1**.

---

### Phase 5: Delete duplicated Int/Min code + full CI [NOT STARTED]

**Goal**: Remove the duplicated completeness scaffolding, repoint or delete call sites, and
pass the full CI pipeline. End state: net tree sorry count = **1**.

**Tasks**:
- [ ] Delete (or replace with 1-line corollaries `:= truthLemma intScheme ...` /
      `:= tableau_complete minScheme ...`) the duplicated trio in both files:
      `intTruthLemma`, `intuitionisticOpenBranch_countermodel`, `intuitionisticTableau_complete`
      (Int/Completeness.lean) and `minTruthLemma`, `minOpenBranch_countermodel`,
      `minimalTableau_complete` (Min/Completeness.lean). This removes the OLD six sorries.
- [ ] If P2 left the original `*_sound` theorems in place, collapse them now to the generic
      `tableau_sound` form (or leave as thin corollaries).
- [ ] Update the "Notes on sorry" docstring blocks in both Completeness files to point at the
      single `Scheme.truthLemma` obligation.
- [ ] Add the new module to the barrel: `lake exe mk_all --module` (or hand-edit the relevant
      `.lean` aggregator) so `Scheme.lean` is imported.
- [ ] Run full CI: `lake build` -> `lake test` -> `lake exe checkInitImports` ->
      `lake exe lint-style` -> `lake shake --add-public --keep-implied --keep-prefix`. Fix
      import-graph re-minimization from `shake` (Min transitively pulled Int/Completeness;
      after moving shared defs to Scheme.lean the graph changes — report Risk 5).

**Timing**: 1.5 hours

**Depends on**: 4

**Files to modify**:
- `Intuitionistic/Completeness.lean` - delete/replace duplicated trio; update docstrings.
- `Minimal/Completeness.lean` - delete/replace duplicated trio; update docstrings.
- `Intuitionistic/Soundness.lean` / `Minimal/Soundness.lean` - finalize `*_sound` collapse if deferred.
- Barrel/aggregator module - add `Scheme.lean` import (via `mk_all --module`).

**Build state / staging**: GREEN save the single `truthLemma S` sorry. After deletion the OLD
six sorries are gone; the only remaining sorry is the parametric `truthLemma S`. Net tree
count: **6 -> 1**.

**Verification**:
- Full CI green: `lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`,
  `lake exe mk_all --module`.
- Final sorry-token sweep over Int+Min Tableau tree returns exactly **1** line (the
  `truthLemma S` body); Soundness lines absent.

---

## Testing & Validation

- [ ] `lake build` succeeds for the whole `Cslib.Logics.Propositional.Tableau` tree.
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes (Scheme.lean imports `Cslib.Init`).
- [ ] `lake exe lint-style` passes (docstrings on structure + every field; lowerCamelCase
      names; `lemma`/`theorem` for `truthLemma`/`tableau_complete`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (import graph re-minimized).
- [ ] Sorry-token sweep: exactly **1** real sorry (`Scheme.truthLemma`) across Int+Min Tableau;
      both Soundness modules remain at **0**.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (NEW): `IntMinScheme`
  structure, `intScheme`/`minScheme` instances, `tableau_sound S`, `truthLemma S` (the single
  sorry), `openBranch_countermodel S`, `tableau_complete S`, optional `decidableValid S`.
- Reduced `Int/Completeness.lean` and `Min/Completeness.lean` (duplicated trios removed).
- Repointed `Int/DecisionProcedure.lean` and `Min/DecisionProcedure.lean`.
- ~350-400 lines of duplication removed; 6 completeness sorries unified into 1 parametric
  obligation for task 317.

## Rollback/Contingency

- The shared development is additive in P1-P4 (new `Scheme.lean`; originals untouched until
  P5). If any phase fails, revert that phase's commit; earlier commits remain green and the
  old Int/Min trios continue to function unchanged.
- If `shake`/import re-minimization in P5 proves intractable, keep the duplicated trios as
  thin 1-line corollaries (`:= truthLemma intScheme ...`) rather than deleting them — this
  preserves the import graph while still collapsing the sorries to 1.
- If `minScheme.modelBot_uc` cannot be discharged without new proof work, restructure so the
  obligation lives inside the single `truthLemma S` sorry (P3); never add a standalone field
  sorry. Worst case, the parametric trio carries at most the obligations of one logic — never
  more, and never any Soundness sorry (report §3).
