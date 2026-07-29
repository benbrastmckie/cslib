# Implementation Plan: Task #317

- **Task**: 317 - Fill sorry instances in propositional tableau completeness proofs
- **Status**: [IN PROGRESS] — classical phase partially attempted; `Classical/Completeness.lean` is build-RED (see "Current State")
- **Effort**: 11 hours (classical phase largely consumed; ~8h remaining incl. fixing the red build)
- **Dependencies**: None (task 316 soundness is independent for completeness direction). M1 (`minimalTableau_sound`) is DEFERRED to task 316 — it lives in `Minimal/Soundness.lean`, which is 316's territory (see Phase 4).
- **Research Inputs**: specs/317_propositional_tableau_completeness/reports/01_tableau-completeness-research.md
- **Artifacts**: plans/01_tableau-completeness-plan.md (this file); classical-easy-attempt.patch (saved attempt, see below)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Current State (updated 2026-06-24)

**`Classical/Completeness.lean` does NOT build** — it carries **~54 build errors** (≈51 of which are
**pre-existing at the committed HEAD**, in the `classicalTruthLemma` / Hintikka-helper region around
lines 110–229: unknown constants like `List.findSome?_of_mem`/`List.find?_of_mem`, unsolved goals,
failed rewrites, "function expected"). This longstanding red state — not the sorry count — is the real
blocker for the classical phase. **Restoring a green build must precede any further sorry work.**

Sorry progress (misleading without the build context): the file is at **1 live sorry**,
`classicalExpandBranches_hintikka` (~L462) — the **deep loop-invariant induction** (induction on fuel +
inner induction on the pending list proving the open branch is a Hintikka set). This is the classical
analog of task 316's intuitionistic induction crux and will likely need the same focused, possibly
research-informed treatment rather than a single broad dispatch.

An agent attempted the two *easy* classical sorries (the `classicalTableau_hintikka` bridge ~L470 and
the F(φ)-membership in `classicalOpenBranch_countermodel` ~L486), reducing 3→1 sorry, but introduced
broken helper lemmas and left the file red. That attempt is preserved in
`specs/317_propositional_tableau_completeness/classical-easy-attempt.patch` (NOT yet build-clean; treat
as a starting point, not a finished proof).

**Other files (untouched, still at baseline)**: `Intuitionistic/Completeness.lean` (7 sorries, B1/B2
unresolved), `Minimal/Completeness.lean` (8 sorries), the `DecisionProcedure.lean` files. The
intuitionistic and minimal completeness phases have NOT been started.

## Overview

Fill 8 sorry instances across 3 files to prove completeness of propositional tableau systems
for classical, intuitionistic, and minimal logic. The core technique is the Hintikka-set
argument: extract a countermodel from any open saturated branch, prove a truth lemma by
formula induction, then derive completeness by contrapositive. Classical completeness (3 sorries)
is self-contained and serves as the pattern for the harder intuitionistic (3 sorries) and
minimal (2 sorries) cases. Two potential blockers require resolution: (B1) the intuitionistic
truth lemma's F-atom case under `IntuitionisticClosure`, and (B2) the saturation hypothesis
mismatch between truth lemma signatures and expansion loop output.

### Research Integration

Key findings from the research report:
- 8 sorry sites decompose into truth lemmas (3), countermodel extraction (3), and main
  completeness theorems (2). Dependency chain within each logic: truth lemma -> countermodel -> completeness.
- Classical case is fully self-contained; all needed infrastructure exists.
- Blocker B1: `IntuitionisticClosure` only closes on T(bot), NOT on complementary atoms.
  The F-atom case of the intuitionistic truth lemma requires T(p)/F(p) at the same world
  to be impossible on open branches. Research identifies three resolution options: (1) strengthen
  closure, (2) prove structural invariant, (3) restructure countermodel.
- Blocker B2: Truth lemma hypotheses use `classicalStepBranch b [] = none` (empty expanded list),
  but the expansion loop produces branches saturated w.r.t. a non-empty expanded list. Need
  Hintikka bridge or hypothesis adjustment.
- M1 (`minimalTableau_sound`) is soundness, not completeness -- but needed for `Decidable`
  instance. Task 316 is [PLANNED] and may address M1; include M1 in this plan as contingency.
- `extractValuation`, `intExtractValuation`, `intBotForces`, `BoolEvaluate` simp lemmas,
  `IForces` simp lemmas, `tautology_iff_boolEvaluate_true`, and `iforces_persistence` are all
  available infrastructure.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Fill all 8 sorry instances in the 3 completeness files
- Prove classical completeness (C1, C2, C3) with no sorry
- Prove intuitionistic completeness (I1, I2, I3) with no sorry, resolving B1 and B2
- Prove minimal soundness (M1) and completeness (M2) with no sorry
- Ensure `Decidable (MValid phi)` and `Decidable (Derivable MinPropAxiom phi)` are sorry-free
- All modified files pass `lake build`

**Non-Goals**:
- Refactoring the expansion loop or tableau infrastructure
- Proving strong completeness (only weak completeness: validity implies closure)
- Modifying the soundness proofs (task 316 scope)
- Adding new files or new top-level declarations beyond helper lemmas within existing files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| B1: F-atom case under IntuitionisticClosure (T(p)/F(p) coexistence) | H | M | Try structural invariant proof first; fall back to strengthening closure to include atomic contradictions; worst case mark I1-I3 BLOCKED |
| B2: Saturation hypothesis mismatch (empty vs non-empty expanded) | M | H | Define explicit Hintikka predicates as intermediate layer; prove saturation-implies-Hintikka bridge lemma; or weaken truth lemma hypothesis to match expansion output |
| Expansion loop invariant extraction difficulty | M | M | Focus truth lemma on Hintikka conditions directly rather than trying to prove complex loop invariants about fuel-based recursion |
| M1 overlap with task 316 | L | M | Include M1 in Phase 4; if task 316 fills it first, skip and use their proof |
| Lean tactic difficulties with induction on formula structure | M | L | Use `Proposition.rec` or explicit match if tactic-mode induction is awkward; lean_multi_attempt to test approaches |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Classical Truth Lemma and Helpers [IN PROGRESS] *(deviation: the implemented file uses a `classicalHintikkaSet` decomposition — `classicalExpandBranches_hintikka` + `classicalTableau_hintikka` — not present in the original C1/C2/C3 framing)*

**STATUS NOTE (2026-06-24)**: ~54 build errors remain (≈51 pre-existing at HEAD) in the helper region
(~L110–229). **Priority 0 for this phase: get `Classical/Completeness.lean` to a green build** before
any sorry work — fix the unknown-constant references (`List.findSome?_of_mem`, `List.find?_of_mem` are
not real Mathlib lemmas; find the correct `List.find?`/`List.findSome?` membership lemmas via
`lean_loogle`/`lean_leansearch`), the unsolved goals, and the failed rewrites. Only then is the file's
sorry count meaningful. The single remaining sorry, `classicalExpandBranches_hintikka` (~L462), is the
**deep loop-invariant induction** and should be treated as its own focused sub-task (see Phase 2 note).

**Goal**: Prove `classicalTruthLemma` (C1) and the Hintikka-bridge lemmas needed for the classical
Hintikka-set argument; restore a green build for the module.

**Tasks**:
- [ ] Inspect `classicalApplyOne` and `classicalStepBranch` behavior via lean_goal to understand
  what `classicalStepBranch b [] = none` actually guarantees about formulas on `b`
- [ ] Determine whether the current hypothesis `classicalStepBranch b [] = none` is usable
  as-is (it means every formula on `b` yields `.notApplicable`, i.e., only atoms and bot remain)
  or needs a Hintikka bridge lemma
- [ ] If a bridge is needed: define a helper predicate `classicalHintikka` capturing the
  Hintikka conditions (if T(and) then T(both conjuncts), if F(and) then F(one disjunct), etc.)
  and prove `classicalStepBranch b [] = none -> classicalHintikka b`
- [ ] Prove `classicalTruthLemma` by induction on `phi`:
  - atom p: T-direction uses `extractValuation` definition directly; F-direction uses
    `isClassicallyClosed b = false` to rule out T(p)/F(p) coexistence
  - bot: T-direction vacuous (T(bot) contradicts `hopen` since ClassicalClosure detects T(bot));
    F-direction trivial (`BoolEvaluate v bot = false`)
  - imp/and/or: Use saturation (or Hintikka conditions) + induction hypothesis
- [ ] Verify C1 with `lean_verify` (no sorry, no axiom beyond standard)

**Timing**: 3 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - Fill `classicalTruthLemma`, add helper lemmas if needed

**Verification**:
- `lean_goal` shows no sorry in `classicalTruthLemma`
- `lean_verify Cslib.Logic.PL.classicalTruthLemma` returns clean

---

### Phase 2: Classical Countermodel and Completeness [IN PROGRESS]

**STATUS NOTE (2026-06-24)**: The bridge `classicalTableau_hintikka` (~L470) and the F(φ)-membership
sorry in `classicalOpenBranch_countermodel` (~L486) were ATTEMPTED (reduced 3→1 sorry) but the
supporting helper lemmas are build-red — see `classical-easy-attempt.patch`. The remaining structural
piece is `classicalExpandBranches_hintikka` (~L462), the **deep loop-invariant induction** (induction
on fuel + inner induction on the pending list). Recommended approach (mirroring the successful 316
intuitionistic path): a dedicated research/decomposition pass to break this induction into a stated
loop invariant + small helper lemmas, then a tightly-scoped, commit-after-each-step implementation —
do NOT attempt it in a single broad dispatch (such attempts overflowed repeatedly on the analogous 316
proof). Once `classicalExpandBranches_hintikka` is proved and the helper region builds green, the
bridge and `classicalTableau_complete` follow mechanically.

**Goal**: Prove `classicalOpenBranch_countermodel` (C2), `classicalTableau_complete` (C3), and the
underlying `classicalExpandBranches_hintikka` loop invariant; reach a green, sorry-free
`Classical/Completeness.lean`.

**Tasks**:
- [ ] Prove `classicalOpenBranch_countermodel`:
  - Unfold `classicalTableau` to understand how `classicalExpandBranches` returns `.openBranch b`
  - Extract from the expansion result that: (a) `isClassicallyClosed b = false`, (b) the
    branch is saturated, (c) the initial formula `F(phi)` persists on `b`
  - Property (a): The expansion only returns `.openBranch b` for branches where `isClassicallyClosed`
    is false (line 137 of Expansion.lean checks this before the saturation match)
  - Property (b): At the `.openBranch b` return site (line 137), `classicalStepBranch b e = none`
    for some expanded set `e`
  - Property (c): `Branch.extendMany` prepends new formulas, preserving existing ones
  - May need auxiliary lemma about expansion monotonicity; alternatively restructure proof
    to use properties directly from the match structure
  - Apply `classicalTruthLemma` with the F-direction for `phi` to get
    `BoolEvaluate (extractValuation b) phi = false`
- [ ] Prove `classicalTableau_complete`:
  - Cases on `classicalTableau phi` result
  - If `.closed`, done
  - If `.openBranch b`, apply `classicalOpenBranch_countermodel` to get
    `BoolEvaluate (extractValuation b) phi = false`
  - From `Tautology phi`, use `tautology_iff_boolEvaluate_true` to get
    `BoolEvaluate (extractValuation b) phi = true`
  - Derive contradiction
- [ ] Verify both with `lean_verify`, run `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - Fill `classicalOpenBranch_countermodel` and `classicalTableau_complete`

**Verification**:
- `lean_verify` clean for both declarations
- `lake build` succeeds for the Classical/Completeness module

---

### Phase 3: Intuitionistic Completeness [NOT STARTED]

**Goal**: Resolve blockers B1 and B2, then prove `intTruthLemma` (I1),
`intuitionisticOpenBranch_countermodel` (I2), and `intuitionisticTableau_complete` (I3).

**Tasks**:
- [ ] **Resolve B1 (atomic contradiction under IntuitionisticClosure)**:
  - First attempt: prove a structural invariant that the intuitionistic expansion loop never
    produces T(atom p) and F(atom p) at the same world label on an open branch. Trace through
    `intApplyRuleFull` to verify that T(p) at w and F(p) at w cannot coexist after expansion:
    - F(p) at w arises only from initial formula or F-connective decomposition at w
    - T(p) at w arises from T-connective decomposition or persistence propagation from w' <= w
    - Check whether persistence can propagate T(p) to a world that also has F(p)
  - If structural invariant is infeasible: modify `isIntuitionisticallyClosed` to also close
    on atomic complementary pairs (same as `MinimalClosure` for atoms). This is sound because
    no intuitionistic Kripke model can have `val w p` and `not (val w p)` simultaneously.
    Update the closure check and verify soundness still holds.
  - If neither works: mark I1-I3 as [BLOCKED] and document the specific obstacle
- [ ] **Resolve B2 (saturation hypothesis mismatch)**:
  - Adjust `intTruthLemma` hypothesis from `intStepBranch b [] 0 = none` to a form matching
    what the expansion loop actually provides. Options:
    (a) Use `intStepBranch b expanded nw = none` with existentially quantified expanded/nw
    (b) Define `intHintikka b` predicate and use that as hypothesis
    (c) Prove that every formula on the saturated branch with applicable rules is in the
        expanded set, which gives the Hintikka conditions
  - Implement chosen approach
- [ ] **Prove `intTruthLemma` (I1)** by induction on `phi` and cases on world `w`:
  - atom p: T-direction by definition of `intExtractValuation`; F-direction by B1 resolution
  - bot: T-direction vacuous (contradicts `hopen`); F-direction trivial (`intBotForces w = False`)
  - imp phi psi: T-direction uses persistence saturation (for all w' >= w with T(phi), T(psi));
    F-direction uses world-creating rule (exists w' with T(phi) and F(psi))
  - and phi psi: Standard alpha/beta decomposition + IH
  - or phi psi: Standard alpha/beta decomposition + IH
- [ ] **Prove `intuitionisticOpenBranch_countermodel` (I2)**:
  - Extract from `intuitionisticTableau phi = .openBranch b` that b is open and satisfies
    truth lemma hypotheses
  - Apply truth lemma F-direction to get `not (IForces ... 0 phi)` from `F(phi)` at world 0
- [ ] **Prove `intuitionisticTableau_complete` (I3)**:
  - Contrapositive: assume `not closed`, get `openBranch b`, apply I2, contradict `IValid phi`
  - Instantiate `IValid phi` with the extracted model to get `IForces ... 0 phi`
  - Need to verify `intExtractValuation b` is upward-closed (persistence propagation ensures this)
- [ ] Verify all three with `lean_verify`, run `lake build` for the module

**Timing**: 4 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - Fill `intTruthLemma`, `intuitionisticOpenBranch_countermodel`, `intuitionisticTableau_complete`; modify hypothesis signatures if B2 resolution requires it
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - Only if B1 resolution requires changing `isIntuitionisticallyClosed`

**Verification**:
- `lean_verify` clean for all three declarations
- `lake build` succeeds for Intuitionistic/Completeness module
- If Expansion.lean was modified, also verify Soundness.lean still builds

---

### Phase 4: Minimal Completeness [NOT STARTED]

**STATUS NOTE (2026-06-24) — territory correction**: `minimalTableau_sound` (M1) lives in
`Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`, which is **task 316's territory** (all
`*/Soundness.lean` files belong to 316). Under the active 316/317 territory contract, **317 does NOT
fill M1** — it uses `minimalTableau_sound` as-is (a lemma with an internal `sorry` still type-checks, so
M2 and the `Decidable` instances can be made sorry-free independently; M1's residual sorry is 316's to
discharge). The original file mapping below (M1+M2 in `Minimal/DecisionProcedure.lean`) is STALE: M2
(`minimalTableau_complete`) is in `Minimal/Completeness.lean`; the `Decidable` instances are in
`Minimal/DecisionProcedure.lean`. This phase's scope is **M2 + the minimal `Decidable` instances only**.

**Goal**: Prove `minimalTableau_complete` (M2) and make the minimal `Decidable` instances sorry-free,
using `minimalTableau_sound` (M1) as a black box owned by task 316.

**Tasks**:
- [ ] **Do NOT edit `Minimal/Soundness.lean`** (M1 / `minimalTableau_sound` is 316's). If M2 or a
  `Decidable` instance genuinely cannot be made sorry-free without M1 being sorry-free, record it as a
  dependency-on-316 blocker rather than crossing territory.
- [ ] **Prove `minimalTableau_sound` (M1)** (if not already filled by task 316):
  - Follows same pattern as intuitionistic soundness but with `MinimalClosure`
  - Closure unsatisfiability: if T(atom p) and F(atom p) at same world w, then
    `val w p` and `not (val w p)` is a contradiction in any model
  - Loop invariant: each expansion step preserves satisfiability
  - Main argument: if tableau is closed, every branch is closed, initial branch was satisfiable
    (from `MValid phi` and any model), so the initial branch must close -- contradiction shows
    phi is MValid
  - Actually for soundness direction: closed -> MValid. Contrapositive: not MValid -> open.
    Direct: show closed branch is unsatisfiable, expansion preserves satisfiability,
    initial branch is satisfiable from any model satisfying phi -> contradiction -> all closed
- [ ] **Prove `minimalTableau_complete` (M2)**:
  - Adapt Phase 3 pattern with modifications:
  - `botForces w = b.any (fun sf => sf.sign == .pos && sf.formula == .bot && sf.label == w)`
    instead of `fun _ => False`
  - Truth lemma bot case: T(bot) at w means `botForces w = true` by definition of extracted
    botForces (a concrete membership check), so `IForces v bf w bot = bf w = True`
  - F(bot) at w: need `not (botForces w)`. Since `MinimalClosure` closes on T(p)/F(p) for
    atomic p but NOT on T(bot), F(bot) can be on an open branch. But bot is not atomic, so
    `isMinimallyClosed` does not check F(bot) against T(bot). This means F(bot) at w and
    T(bot) at w could coexist on an open branch under MinimalClosure.
  - Resolution: F(bot) at world w should mean `not (botForces w)` i.e., T(bot) at w is not
    on the branch. Need to verify this is maintained by expansion, or handle the case where
    both exist.
  - The truth lemma for minimal uses the same Hintikka approach as intuitionistic but with
    the modified botForces and MinimalClosure
  - F-atom case is guaranteed by MinimalClosure (closes on T(p)/F(p) for atomic p)
  - Upward-closure of extracted botForces follows from persistence propagation of T(bot)
  - Prove countermodel and completeness analogously to I2, I3
- [ ] Verify both with `lean_verify`, run `lake build` for the module
- [ ] Run full CI: `lake build`, `lake test`, `lake exe checkInitImports`

**Timing**: 2 hours

**Depends on**: 3

**Files to modify** (corrected 2026-06-24):
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - Fill `minimalTableau_complete` (M2) + helper lemmas (minimal truth lemma, minimal countermodel extraction)
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - Make the minimal `Decidable` instances sorry-free
- **NOT** `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` — M1 (`minimalTableau_sound`) is task 316's territory; use it as-is

**Verification**:
- `lean_verify` clean for both declarations
- `lake build` succeeds for the full project
- `lake test` passes
- `lake exe checkInitImports` passes
- All `Decidable` instances in DecisionProcedure.lean are sorry-free

## Testing & Validation

- [ ] Each declaration passes `lean_verify` with no sorry and no non-standard axioms
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` succeeds
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` succeeds
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` succeeds
- [ ] `lake build` (full project) succeeds
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `Decidable (MValid phi)` instance is sorry-free (downstream of M1+M2)
- [ ] `Decidable (Derivable MinPropAxiom phi)` instance is sorry-free

## Artifacts & Outputs

- `specs/317_propositional_tableau_completeness/plans/01_tableau-completeness-plan.md` (this file)
- Modified: `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
- Possibly modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (if B1 requires closure change)

## Rollback/Contingency

- Each phase modifies one file (except Phase 3 which may touch Expansion.lean). Git revert
  per-phase commits if a phase introduces regressions.
- If B1 is unresolvable without major refactoring: mark I1-I3 and M2 as [BLOCKED], complete
  classical proofs (C1-C3) and M1 as partial success. Create a follow-up task for the
  infrastructure changes needed.
- If B2 requires changing lemma signatures: this is acceptable since all proofs are currently
  `sorry` -- the signatures have not been relied upon downstream except by the sorry-bearing
  `Decidable` instances.
