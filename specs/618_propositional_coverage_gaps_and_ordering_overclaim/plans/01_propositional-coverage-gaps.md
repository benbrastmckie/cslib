# Implementation Plan: Propositional Coverage Gaps and the Ordering Overclaim

- **Task**: 618 - Close remaining coverage gaps in the propositional metatheory; correct the docstring that overclaims a result the tree does not prove
- **Status**: [COMPLETED]
- **Effort**: 11 hours
- **Dependencies**: None blocking. Task 614 (`computable_ctxtoimp_context_decidability`, status `planning`) is *coordinated with* but explicitly NOT blocking -- see Phase 4.
- **Research Inputs**: `specs/618_propositional_coverage_gaps_and_ordering_overclaim/reports/01_propositional-coverage-gaps.md`
- **Artifacts**: plans/01_propositional-coverage-gaps.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Two distinct bodies of work. First, correct six docstrings that assert results the tree does not
prove (Part A, extended by research from five defects to six) plus one deliberate-absence note --
this is correctness of the record and ships first, independently of everything else. Second, close
the measured coverage gaps: two cheap compositions on the LJ/LK side (B1, B2), one small
composition on the fragment side (D1-relative), and LM parity (B3, C1-C3), which requires
generalising LJ's concretely-written structural metatheory from `IPL` to an arbitrary `Theory T`
and then instantiating at `MPL`. Definition of done: all ten phases green, the full CI gate
passes, zero `sorry` and zero new axioms introduced.

### Research Integration

The research report materially corrected four premises the task description asserted. All four are
built into this plan rather than discovered at implementation time:

1. **A4 is only half true.** `intuitionisticTableau_complete` exists; `temporalTableau_complete`
   genuinely does not (it appears only as a blocked obligation at
   `Temporal/Tableau/Completeness.lean:122`). Phase 1 does a **split** re-tensing, not a blanket
   one, or it replaces one false statement with another.
2. **A1 has three defects, not one** -- unproved "strictly", a "five" contradicted by its own
   three-node display block, and a chain-identity conflation between the Imp/Int/Prop chain the
   theorem proves and the Min/Int/Prop theorems immediately above it.
3. **A6 is a sixth overclaim the task did not list.** `LJ/Basic.lean:78-79` claims cut elimination
   and the subformula property are "proved once generically over `T`"; both are written concretely
   at `IPL`. Phase 6 makes that claim true; Phase 1 corrects it in the interim.
4. **C1's stated premise is false but its conclusion survives.** `ljCutAdmissibility` is NOT
   already generic -- no `{T : Theory Atom}` binder occurs anywhere in `LJ/CutElimination.lean`.
   The generalisation route is nonetheless right and mechanical, because `SeqProof.mono`
   (`LJ/Basic.lean:184-186`) already solves the only hard part (reconstructing the
   `[IsIntuitionistic T]`-gated `botL` via a `letI` instance rebind) and `Basic.lean:178-179`
   documents that idiom.

Also integrated: the report's correction that the four `lj*Deduction*` helpers are LJ-specific
(not generic as the task assumed) but touch no gated constructor, so generalising them is
mechanical; and the report's finding that D2's difficulty is materially overstated.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` line 88: "Minimal / Intuitionistic / Classical propositional: Hilbert, ND
(+ normalization), LJ/LK sequent calculus (cut-elim, interpolation), soundness, strong
completeness, Lindenbaum". Phases 4 and 6-9 advance the **Minimal** column of that row from
three modules (Basic/Soundness/Completeness) toward LJ/LK parity by adding cut elimination,
subformula property, interpolation, and decidability. Phase 5 advances line 89 (fragment
conservativity chain). Phase 1 is record correctness and advances no roadmap item.

## Goals & Non-Goals

**Goals**:
- Correct every docstring in the propositional tree that asserts an unproved or non-existent
  result (A1-A6), and record the one deliberate architectural absence (G9) so it stops generating
  false coverage findings.
- Add `ljCutFreeCompleteness` / `ljCutFreeIffIValid` to close the LK/LJ asymmetry (B1).
- Expose the already-proved general split-interpolation lemma publicly, in the bundled
  `CutFreeXProof` shape (B2).
- Generalise LJ's cut elimination, subformula property, and interpolation from `IPL` to an
  arbitrary `Theory T`, preserving every current `LJProof.*` signature, and instantiate all three
  at `MPL` (C1, C2, C3).
- Add LM decidability (B3).
- Add `OrImpAxiom` completeness relative to IPL semantics on the and-bot-free sublanguage, with a
  docstring that states plainly what kind of completeness it is (D1-relative).
- Introduce zero `sorry` and zero new axioms.

**Non-Goals**:
- **D1-absolute** (fragment-matched algebraic completeness for the meet-free imp-disjunction
  signature). Needs a new algebra class chosen and defined, i.e. definitional infrastructure, not
  just a proof. Recorded as a recommended follow-up in Phase 10; not attempted here.
- **D2** (the two separation theorems establishing MPL != IPL != CPL). The research measured these
  as tractable (~15-25 lines and ~30-50 lines respectively, via hand-built semantic countermodels
  following the in-tree `CslibTests/ModalFrameSeparation.lean` precedent), NOT as an open research
  problem. They are still new mathematical content and are kept out of this otherwise
  cleanup-plus-mechanical-generalisation diff. Recommended as a follow-up in Phase 10.
- **G6** (a `Fintype`-free `Decidable (Derivable PropositionalAxiom φ)` via the tableau route).
  The task instructs A2 as a deletion; this plan follows that instruction. See "Resolved Open
  Decisions" below for the coupling the research flagged and why it is not taken here.
- Anything under the "DO NOT TOUCH" heading of the task description: the intuitionistic engine's
  internal "not proved"/"refuted" notes in `Expansion.lean` and `Scheme.lean`.

### Resolved Open Decisions

The research left three decisions for the planner. All three are decided here so implementation
does not stall on them.

| Decision | Resolution | Rationale |
|---|---|---|
| B2 public API shape | **Bundled `CutFreeLKProof`/`CutFreeLJProof` wrapper**; `maeharaCore`/`ljMaeharaCore` stay `private` | Consistent with `lkCutFreeCompleteness` and `CutFreeLJProof.subformula_property`; un-privatising the core would expose an internal induction shape as public API |
| A2: deletion vs. pairing with G6 | **Plain deletion**, of BOTH `:23` and the dangling `:33-34` description | The task instructs deletion. G6 is a separate judgment call whose cost is not carried by this task's scope; taking it would silently convert a cleanup task into a new-instance task |
| B3 vs. task 614 | **Do not block.** Build against `ctxToImp` as it stands and carry the `noncomputable` taint with an explicit docstring note | Task 614 is `planning`, not landed. Blocking would stall an independent wave-1 phase on an unlanded task. Phase 4 checks 614's status at implementation time and takes the computable route only if it has landed |

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Phase 6 (C1a): adding `{T : Theory Atom}` perturbs elaboration order and breaks termination checking on the nested well-founded recursions in the 715-line `LJ/CutElimination.lean`. The named hot spot is the `decreasing_by simp [SeqProof.height, LJProof.height]` at `:650`, whose `LJProof.height` is an `IPL`-only re-export | H | M | Phase 6 is dispatched alone with a scoped `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination` gate before anything downstream is touched. If it stalls, mark Phase 6 `[BLOCKED]` with the goal state recorded and do NOT attempt phases 7-9 around it; phases 1-5 are independent and still land |
| A4 re-tensed as a blanket past tense, replacing one false claim with another | M | M | Phase 1 task list mandates a split: intuitionistic clause to past tense, temporal clause stays present and cites the blocked obligation at `Temporal/Tableau/Completeness.lean:122` |
| A1 fixed for "strictly" only, leaving the false "five" numeral standing | M | M | Phase 1 lists all three A1 defects as separate checklist items |
| Phase 6's re-export inversion of `LJCutFree`/`CutFreeLJProof` breaks a downstream call site | H | L | `LJProof.cutElim`'s current signature is preserved by contract; Phase 6 tier is `full`, so the complete gate set runs before it closes |
| B3's `noncomputable` taint is carried silently and becomes the next overclaim | L | M | Phase 4 requires an explicit docstring note naming the `ctxToImp` `Finset.toList` cause |
| D1-relative's docstring overclaims "orImp completeness" without qualification, becoming the next A1 | M | M | Phase 5 verification requires the docstring to state "relative to IPL semantics on the and-bot-free sublanguage", not bare "completeness" |
| Phases 8 and 9 both edit `LM.lean`'s import list; parallel execution would conflict | L | M | Phase 9 depends on Phase 8, serialising the two `LM.lean` edits |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4, 5 | -- |
| 2 | 6 | 1 |
| 3 | 7 | 6 |
| 4 | 8 | 7 |
| 5 | 9 | 3, 7, 8 |
| 6 | 10 | 1, 2, 3, 4, 5, 6, 7, 8, 9 |

Phases within the same wave can execute in parallel. Wave 1's five phases have disjoint file
territories (verified: no file appears in two of them).

---

### Phase 1: Correct the record (A1-A6 + G9 note) [COMPLETED]

**Goal**: Every docstring in the propositional tree that asserts an unproved or non-existent
result is corrected, and the one deliberate architectural absence is documented.

**Tasks**:
- [ ] A1 (`Semantics/Algebra/ConservativeChain.lean:140`) -- fix all THREE defects: (a) drop
      "strictly", which nothing in the tree proves; (b) drop or correct "five", which the
      docstring's own three-node display block contradicts; (c) resolve the chain-identity
      conflation -- the docstring reads as covering both the Imp -> Int -> Prop chain the theorem
      proves and the Min -> Int -> Prop theorems at `:125`/`:135`, which it does not. Scope the
      replacement to what `derivability_subsumption_chain` (`:148`) actually proves: a single
      implication `Derivable ImpAxiom φ -> Derivable PropositionalAxiom φ`.
- [ ] A2 (`Tableau/Classical/DecisionProcedure.lean`) -- remove `instDecidableDerivable` from the
      Main Results list at `:23` AND remove/re-point the dangling description at `:33-34` that
      describes the same non-existent instance. Fixing only `:23` leaves a dangling description.
- [ ] A3 (`Tableau/Intuitionistic/DecisionProcedure.lean:62`) -- the "feeds the modal/temporal/
      bimodal extensions" claim has zero consumers outside `Cslib/Logics/Propositional/`. Restate
      as aspirational ("intended as the entry point for downstream extensions; no external
      consumers at present") or drop the sentence -- the "canonical registered instance" role is
      already stated on the preceding line.
- [ ] A4 (`CslibTests/TableauConformance.lean:34-35`) -- **SPLIT** re-tensing, not blanket. The
      intuitionistic clause goes to past tense and names `intuitionisticTableau_complete` /
      `intuitionisticTableau_decides` as now existing and sorry-free. The temporal clause STAYS in
      the present tense and cites `Temporal/Tableau/Completeness.lean:122`'s blocked obligation as
      the reason. Preserve the file's existing justification of the `#eval` mechanism -- the
      kernel-reduction stall is independent of theorem availability and applies to both rows.
- [ ] A5 (`Tableau/Minimal/DecisionProcedure.lean:119`) -- add the universe pin: the docstring says
      "`MValid φ` is decidable" where `instDecidableMValid` (`:123`) is stated at `MValid.{_, 0} φ`.
      Optionally cross-reference the file's own "Universe Invariance of `MValid`" section at
      `:131-139`.
- [ ] A6 (`SequentCalculus/LJ/Basic.lean:78-79`) -- the claim that cut elimination and the
      subformula property are "proved once generically over `T`" is false; both are at `IPL`.
      Correct it to name only what IS generic (`height`, `mono`, `CutFree`, `IsBotRuleFree`,
      `SeqProof.formulas`). Phase 6 makes the stronger claim true; this phase must not
      pre-emptively assert it.
- [ ] G9 (`NaturalDeduction/Equivalence.lean`) -- add a module-docstring note recording that the
      absence of direct ND soundness/completeness is deliberate, and that both directions are
      reached by composing `hilbert_iff_nd_*` (`:448`, `:456`, `:464`) with Hilbert-side results.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: seven files are asserted to need edits -- `ConservativeChain.lean`,
`Tableau/Classical/DecisionProcedure.lean`, `Tableau/Intuitionistic/DecisionProcedure.lean`,
`CslibTests/TableauConformance.lean`, `Tableau/Minimal/DecisionProcedure.lean`,
`SequentCalculus/LJ/Basic.lean`, `NaturalDeduction/Equivalence.lean`. Confirm at implementation
time by reading each cited line and reproducing the defect before editing. If a cited line no
longer reads as reported, record the discrepancy rather than editing blind.

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` - A1, three defects
- `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` - A2, two sites
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` - A3
- `CslibTests/TableauConformance.lean` - A4, split re-tensing
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - A5, universe pin
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` - A6
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - G9 note

**Verification**:
- Each edited module builds (`lake build` of the containing module).
- Diff read-through confirms every changed hunk lies inside a docstring or comment region --
  edits must not cross a `/--` ... `-/` boundary.
- Grep confirms no remaining occurrence of "strictly ordered" or "five Hilbert systems" in
  `ConservativeChain.lean`, and no remaining occurrence of `instDecidableDerivable` in
  `Tableau/Classical/DecisionProcedure.lean`'s header.
- A4's temporal clause still reads in the present tense (a blanket past-tense rewrite is a
  verification failure, not a pass).

---

### Phase 2: B1 -- LJ cut-free completeness [COMPLETED]

**Goal**: `SequentCalculus/LJ/CutFreeCompleteness.lean` exists with the LJ counterparts of
`lkCutFreeCompleteness` / `lkCutFreeIffTautology`, closing the LK/LJ asymmetry.

**Tasks**:
- [ ] Read `LK/CutFreeCompleteness.lean` (~50 lines, two theorems) as the template.
- [ ] Create `SequentCalculus/LJ/CutFreeCompleteness.lean` composing `lj_iff_ivalid`
      (`LJ/Completeness.lean:288`) with `LJProof.cutElim` (`LJ/CutElimination.lean:678`),
      producing `ljCutFreeCompleteness` and `ljCutFreeIffIValid`.
- [ ] Name the biconditional `ljCutFreeIffIValid`, NOT `...IffTautology` -- the LJ side is
      intuitionistic validity, not tautologyhood.
- [ ] Carry `lj_iff_ivalid`'s explicit `IValid.{u, u}` universe pin through the statements rather
      than attempting to erase it (this is the one difference from the LK template).
- [ ] Add the new module to `SequentCalculus/LJ.lean`'s import list.

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: estimated ~50 lines mirroring the LK file, and exactly two new public
theorems. Confirm by diffing the finished module's declaration count against
`LK/CutFreeCompleteness.lean`; a materially larger file means the composition was not as direct
as measured and should be re-examined before proceeding.

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutFreeCompleteness.lean` - NEW
- `Cslib/Logics/Propositional/SequentCalculus/LJ.lean` - add import

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutFreeCompleteness` succeeds.
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ` succeeds (import list intact).
- `lean_verify` on both new theorems reports no `sorryAx` and no axiom beyond
  `{propext, Classical.choice, Quot.sound}`.

---

### Phase 3: B2 -- public general split interpolation [COMPLETED]

**Goal**: The already-proved general split-interpolation lemma over arbitrary cover partitions is
publicly reachable for both LK and LJ, in the bundled `CutFreeXProof` shape, with no new proof.

**Tasks**:
- [ ] Add `LKProof.splitInterpolation` to `LK/Interpolation.lean` as a thin public wrapper taking
      the bundled `CutFreeLKProof seq` and delegating to `maeharaCore d.1 d.2 ...` (`:62`).
- [ ] Add the LJ counterpart `LJProof.splitInterpolation` to `LJ/Interpolation.lean` delegating to
      `ljMaeharaCore` (`:68`). Note the LJ core takes only `Γ₁ Γ₂` (single-succedent), not the
      four-way LK split -- do not force a uniform signature.
- [ ] Keep `maeharaCore` and `ljMaeharaCore` `private`. The decision (recorded above) is to wrap,
      not to un-privatise -- un-privatising would expose an internal induction shape as API.
- [ ] Docstring both wrappers stating that they are the general-partition form, and that the
      existing `LKProof.interpolation` (`:863`) / `LJProof.interpolation` (`:560`) remain the
      empty-context implication specialisations.

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: interface

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` - add public wrapper
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` - add public wrapper

**Verification**:
- Both modules build.
- Neither `private` marker was removed (grep confirms `private lemma maeharaCore` and
  `private lemma ljMaeharaCore` still present).
- Both wrappers elaborate with no new proof obligations -- the body is a delegation, so any
  tactic block beyond the delegation indicates the API shape was chosen wrong.

---

### Phase 4: B3 -- LM decidability [COMPLETED]

**Goal**: `Decidable (Nonempty (SeqProofMinimal (Γ ⊢ A)))` and `instDecidableDerivableInMPL`
exist, matching the LJ decidability surface.

**Tasks**:
- [ ] Check task 614's status at implementation time. If `ctxToImp` has become computable, build
      on the computable route. If not (its status at plan time is `planning`, i.e. not landed),
      proceed against `ctxToImp` as it stands and accept the `noncomputable` taint -- do NOT block.
- [ ] Generalise the four deduction-theorem helpers in `LJ/Decidability.lean` from `LJProof` to
      `SeqProof T`, renaming to `seqListDeductionFwd` / `seqProofDeductionFwd` /
      `seqListDeductionBwd` / `seqProofDeductionBwd` (currently `ljListDeductionFwd` `:91`,
      `ljProofDeductionFwd` `:112`, `ljListDeductionBwd` `:130`, `ljProofDeductionBwd` `:170`).
      This is a mechanical binder change with no proof obligations: every rule they use (`ax`,
      `impR`, `impL`, `weakL`, `mono`) is in the ungated ten-rule minimal base of `SeqProof`
      (`LJ/Basic.lean:93-144`); none touches the gated `botL`.
- [ ] Preserve the existing `instDecidableLJDerivable` (`:197`) signature by re-exporting at `IPL`.
- [ ] Create `SequentCalculus/LM/Decidability.lean` following `instDecidableLJDerivable` as the
      structural template, composing `lm_iff_mvalid` (`LM/Completeness.lean:304`) with
      `instDecidableMValid` (`Tableau/Minimal/DecisionProcedure.lean:123`), reusing
      `listToImp`/`ctxToImp` (`LJ/Decidability.lean:72,82`).
- [ ] If the `noncomputable` route was taken, add an explicit docstring note naming the cause
      (`ctxToImp` is `noncomputable` via `Finset.toList`) so the taint is recorded, not silent.
- [ ] Add the new module to `SequentCalculus/LM.lean`'s import list.

**Timing**: 1 hour 15 minutes

**Depends on**: none. The helper generalisation is confined to `LJ/Decidability.lean` and does
not overlap Phase 6's territory (`LJ/CutElimination.lean`, `LJ/Basic.lean`). LM decidability
routes through completeness, not cut elimination, so it does not need Phase 7.

**Verification Tier**: interface

**Scope Hypothesis**: exactly four helpers are asserted to need generalising. Confirm at
implementation time by grepping `LJ/Decidability.lean` for declarations mentioning `LJProof` in
their binders; if more than four are found, the extra ones are in scope for this phase and the
count is corrected in the summary rather than the extras being skipped.

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` - generalise four helpers,
  re-export at `IPL`
- `Cslib/Logics/Propositional/SequentCalculus/LM/Decidability.lean` - NEW
- `Cslib/Logics/Propositional/SequentCalculus/LM.lean` - add import

**Verification**:
- `lake build` of `LJ.Decidability`, `LM.Decidability`, and `LM` all succeed.
- `instDecidableLJDerivable`'s signature is unchanged (its existing call sites still elaborate).
- If `noncomputable`, the docstring note naming the cause is present.

---

### Phase 5: D1-relative -- orImp completeness against IPL semantics [COMPLETED]

**Goal**: `OrImpAxiom` stops being the only one of the eight fragment axiom systems with zero
completeness theorem, via a short composition -- and its docstring states exactly which kind of
completeness it is.

**Tasks**:
- [ ] Compose the `.mp` direction of `hilbertIplConservativeOverOrImp_iff`
      (`Semantics/Algebra/FragmentConservativityInstances.lean:197`) with an existing IPL
      completeness theorem (`IPL.hilbert_alg_completeness` in `Algebra/HilbertCompleteness.lean`,
      or the Kripke route via `lj_iff_ivalid`) to obtain
      `IValid φ → Derivable OrImpAxiom φ` for `φ.IsAndBotFree = true`.
- [ ] Place it in `Semantics/Algebra/OrImpConservative.lean` alongside the existing
      `hilbertIplConservativeOverOrImp` (`:200`).
- [ ] Docstring it as **completeness relative to IPL semantics on the and-bot-free sublanguage**,
      explicitly NOT the fragment-matched algebraic completeness the other four intuitionistic
      fragments have. This qualification is mandatory: an unqualified "orImp completeness"
      docstring would be exactly the class of overclaim Phase 1 is fixing.

**Timing**: 30 minutes

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: estimated under 10 lines, being a composition of two existing results. If
the composition requires more than a handful of lines or any new lemma, that indicates the
conservativity biconditional does not compose as measured -- stop and record rather than growing
the phase into a proof effort.

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` - add the relative
  completeness theorem

**Verification**:
- Module builds; `lean_verify` shows no `sorryAx`.
- The docstring contains the explicit "relative to IPL semantics / and-bot-free sublanguage"
  qualification.

---

### Phase 6: C1a -- generalise cut elimination from IPL to arbitrary T [COMPLETED]

**Goal**: `LJ/CutElimination.lean`'s seven `ljCutAdm*` declarations plus `LJCutIH` carry a
`{T : Theory Atom}` binder, with `LJProof.cutElim`'s current signature preserved by an `IPL`
re-export so no downstream call site breaks.

**Tasks**:
- [ ] Invert the `LJCutFree` / `CutFreeLJProof` re-export: `LJCutFree` is already just a
      `@[reducible]` re-export of the generic `SeqProof.CutFree` at `IPL` (`LJ/Basic.lean:252`),
      so introduce `CutFreeSeqProof T` generically and re-export `CutFreeLJProof` at `IPL`. This
      is a re-export inversion, not a redefinition.
- [ ] Add `{T : Theory Atom}` to `LJCutIH` (`:99`), `ljCutAdmPrincipalAndR` (`:119`),
      `ljCutAdmPrincipalOrR` (`:230`), `ljCutAdmPrincipalImpR` (`:354`), `ljCutAdmLeft` (`:467`),
      `ljCutAdmRight` (`:549`), `ljCutAdmissibility` (`:659`).
- [ ] Convert the five `.botL` match arms (`:136-137`, `:248-249`, `:369-370`, `:477-478`,
      `:561-567`) to the `@SeqProof.botL ... inst ...` + `letI := inst` form. Follow
      `SeqProof.mono` (`LJ/Basic.lean:184-186`) verbatim as the in-tree precedent; the idiom is
      documented at `Basic.lean:178-179`. These arms must be RECONSTRUCTED, not merely read.
- [ ] Fix the `decreasing_by simp [SeqProof.height, LJProof.height]` at `:650`. `LJProof.height`
      is an `IPL`-only re-export and will likely need dropping under generalisation. **This is the
      single most likely place the mechanical port breaks** -- expect to spend disproportionate
      time here and do not treat a termination failure as a sign the whole route is wrong.
- [ ] Re-export `LJProof.cutElim` (`:678`) at `IPL` with its CURRENT signature unchanged.
- [ ] Update `LJ/Basic.lean:78-79`'s docstring (corrected in Phase 1 to claim less) to now
      truthfully include cut elimination as generic over `T`.

**Timing**: 2 hours

**Depends on**: 1

Phase 1 also edits `LJ/Basic.lean` (A6). Serialising avoids a territory conflict on that file and
means this phase updates an already-honest docstring rather than racing one.

**Verification Tier**: full

**Commit Mode**: atomic-batch

The binder change spans `LJ/Basic.lean` and `LJ/CutElimination.lean` and the tree is expected to
be red between them; the declared file set is exactly those two files. This batch is declared here
in advance and must not be widened at implementation time.

**Scope Hypothesis**: seven `ljCutAdm*` declarations plus `LJCutIH` need the binder, and exactly
five `.botL` match arms need the `letI` reconstruction. Confirm at implementation time by grepping
`LJ/CutElimination.lean` for `botL` occurrences and for top-level declarations; if the counts
differ from 8 and 5, the plan's measurement was stale and the actual counts govern.

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` - `CutFreeSeqProof` re-export
  inversion; A6 docstring now truthful for cut elimination
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - the generalisation

**Verification**:
- Scoped gate first: `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination`
  succeeds, INCLUDING termination checking, before anything downstream is touched.
- `LJProof.cutElim`'s signature is unchanged -- every existing call site still elaborates
  (`LJ/Interpolation.lean`, `LJ/Decidability.lean`, and Phase 2's new `LJ/CutFreeCompleteness.lean`
  all build).
- Full CI gate set runs before the phase closes.
- `lean_verify` on `ljCutAdmissibility` shows no `sorryAx` and no new axiom.

**On failure**: mark this phase `[BLOCKED]`, record the exact goal state and the failing
`decreasing_by` obligation, and do NOT attempt phases 7-9 around it. Phases 1-5 are independent
and still land.

---

### Phase 7: C1b -- LM cut elimination [COMPLETED]

**Goal**: `SequentCalculus/LM/CutElimination.lean` exists, instantiating Phase 6's generic
machinery at `MPL`.

**Tasks**:
- [ ] Create `SequentCalculus/LM/CutElimination.lean` instantiating the now-generic
      `ljCutAdmissibility` at `MPL` (recall `SeqProofMinimal = SeqProof MPL`).
- [ ] Expose `SeqProofMinimal.cutElim` with the LM-facing signature, mirroring
      `LJProof.cutElim`'s shape.
- [ ] Add the new module to `SequentCalculus/LM.lean`'s import list.

**Timing**: 1 hour

**Depends on**: 6

**Verification Tier**: interface

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LM/CutElimination.lean` - NEW
- `Cslib/Logics/Propositional/SequentCalculus/LM.lean` - add import

**Verification**:
- `lake build` of `LM.CutElimination` and `LM` succeed.
- `lean_verify Cslib...SeqProofMinimal.cutElim` shows no `sorryAx`.
- The instantiation requires no `IsIntuitionistic MPL` instance (if it does, the generalisation in
  Phase 6 was incomplete and Phase 6 must be reopened, not worked around here).

---

### Phase 8: C2 -- LM subformula property [COMPLETED]

**Goal**: `SequentCalculus/LM/SubformulaProperty.lean` exists; the subformula PROPERTY theorems
are generic over `T` and instantiated at `MPL`.

**Tasks**:
- [ ] Confirm `SeqProof.formulas` (`LJ/SubformulaProperty.lean:50`) is already generic including
      its `@SeqProof.botL _ _ _ Γ C _ _` arm -- the collection function needs no work.
- [ ] Generalise the property theorems to `{T}`: `ljCutFreeSubformulaProp` (`:82`),
      `CutFreeLJProof.subformula_property` (`:259`), `LJProof.subformula_property` (`:274`). Same
      generalise-then-re-export-at-`IPL` route as Phase 6; these consume `CutFreeLJProof`, which
      Phase 6 made a re-export of the generic `CutFreeSeqProof T`.
- [ ] Preserve all three current `IPL`-level signatures via re-exports.
- [ ] Create `SequentCalculus/LM/SubformulaProperty.lean` instantiating at `MPL`, and add it to
      `SequentCalculus/LM.lean`'s import list.

**Timing**: 1 hour

**Depends on**: 7

**Verification Tier**: interface

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/SubformulaProperty.lean` - generalise the three
  property theorems, re-export at `IPL`
- `Cslib/Logics/Propositional/SequentCalculus/LM/SubformulaProperty.lean` - NEW
- `Cslib/Logics/Propositional/SequentCalculus/LM.lean` - add import

**Verification**:
- `lake build` of `LJ.SubformulaProperty`, `LM.SubformulaProperty`, and `LM` succeed.
- All three original `IPL`-level names still resolve with unchanged signatures.
- `LJ/Basic.lean:78-79`'s docstring can now truthfully include the subformula property as generic
  over `T`; update it in this phase (Phase 6 covered cut elimination only).

---

### Phase 9: C3 -- LM Craig interpolation [COMPLETED]

**Goal**: `SequentCalculus/LM/Interpolation.lean` exists, reusing the Phase 3 public wrapper shape
rather than introducing a second one.

**Tasks**:
- [ ] Generalise `ljMaeharaCore` (`LJ/Interpolation.lean:68`) and `ljCraigInterpolation` (`:521`)
      from `IPL` to `{T}`, re-exporting at `IPL` so `LJProof.interpolation` (`:560`) and Phase 3's
      `LJProof.splitInterpolation` keep their signatures.
- [ ] Generalise the Phase 3 wrapper alongside the core -- do NOT introduce a second public shape
      for the LM side. This is the reason Phase 3 sequences before this phase.
- [ ] Create `SequentCalculus/LM/Interpolation.lean` instantiating at `MPL`, exposing the LM
      analogues of `LJProof.interpolation` and `LJProof.splitInterpolation`.
- [ ] Add the new module to `SequentCalculus/LM.lean`'s import list.

**Timing**: 1 hour 30 minutes

**Depends on**: 3, 7, 8

Phase 8 is a dependency for territory as well as content: both phases edit `LM.lean`'s import
list, and serialising them avoids a conflicting edit.

**Verification Tier**: interface

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` - generalise core + wrapper,
  re-export at `IPL`
- `Cslib/Logics/Propositional/SequentCalculus/LM/Interpolation.lean` - NEW
- `Cslib/Logics/Propositional/SequentCalculus/LM.lean` - add import

**Verification**:
- `lake build` of `LJ.Interpolation`, `LM.Interpolation`, and `LM` succeed.
- Exactly one public split-interpolation shape exists across LJ and LM (grep for
  `splitInterpolation` returns the generic declaration plus re-exports, not two independent
  definitions).
- `lean_verify` on the LM interpolation theorem shows no `sorryAx`.

---

### Phase 10: Full-gate verification and follow-up recommendations [COMPLETED WITH EXCLUSIONS]

**Goal**: The whole tree is green under the complete gate set, the zero-debt claim is verified
rather than asserted, and the two out-of-scope items are recorded as recommendations with the
research's measurements attached.

**Tasks**:
- [x] Run the full build across `Cslib/Logics/Propositional/` and `CslibTests/`. *(deviation:
      the whole-repo `lake build`/`lake lint`/`lake exe checkInitImports`/`lake shake`/
      `lake test` gate cannot complete -- see Reasoned Exclusions below. Every module in the
      entire project, including every file this task touched, built successfully; only the
      final top-level `Cslib.lean` barrel target failed, for a pre-existing, unrelated reason.
      `Cslib.Logics.Propositional.SequentCalculus` (the whole subtree) and the specific test
      file Phase 1 edited, `CslibTests.TableauConformance`, both build scoped.)*
- [x] Verify zero `sorry` was introduced: scan `Cslib/Logics/Propositional/` and confirm every hit
      is docstring prose, matching the pre-change baseline the research established.
- [x] Verify no new axioms: `lean_verify` each new headline theorem and confirm the axiom set does
      not exceed `{propext, Classical.choice, Quot.sound}`.
- [x] Re-read every Phase 1 docstring correction against what the tree now proves -- Phases 6 and
      8 changed what is true about `LJ/Basic.lean:78-79`, and A1's correction must NOT have been
      reinstated as "strictly" on the strength of anything landed here (nothing here proves
      strictness; even the D2 separations would establish MPL ⊊ IPL ⊊ CPL, which is not the
      Imp -> Int -> Prop chain A1's docstring displays).
- [x] Record in the implementation summary the two recommended follow-up tasks, with the
      research's measurements so they can be scheduled rather than re-researched:
      (a) **D1-absolute** -- fragment-matched algebraic completeness for the ⟨∨,→,⊤⟩ signature;
      needs an algebra class chosen and defined first, because the meet-free signature gives `→`
      nothing to residuate against; warrants its own research pass.
      (b) **D2** -- the two separation theorems; measured as roughly one phase, NOT an open
      research problem: `⊥ → p` separates MPL from IPL (~15-25 lines, via the one-point model
      `World := Unit`, `v _ _ := False`, `bf _ := True`, cheap precisely because
      `LM/Soundness.lean:61` quantifies over arbitrary upward-closed `bot_forces`), and `p ∨ ¬p`
      separates IPL from CPL (~30-50 lines, via the two-point Kripke chain). The `decide` /
      `WellFounded.fix` kernel-stall concern is a red herring:
      `CslibTests/ModalFrameSeparation.lean` already routes around the same stall with hand-built
      semantic countermodels ported as named theorems.
- [x] Record G6 as a considered-and-not-taken decision, noting its coupling to A2.

**Timing**: 1 hour

**Depends on**: 1, 2, 3, 4, 5, 6, 7, 8, 9

**Verification Tier**: full

**Files to modify**:
- `specs/618_propositional_coverage_gaps_and_ordering_overclaim/summaries/01_propositional-coverage-gaps-summary.md` - NEW

**Verification**:
- Full CI gate passes. *(deviation: see Reasoned Exclusions -- blocked by an unrelated,
  pre-existing, out-of-territory conflict, not by anything this task changed.)*
- Zero `sorry`, zero new axioms, confirmed by command output quoted in the summary.
- The summary names both follow-up recommendations with their measured scope.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|---|---|---|
| Whole-repo `lake build` (and everything gated on it: `lake exe checkInitImports`, `lake lint`, `lake shake --add-public --keep-implied --keep-prefix`, `lake test`) | Fails at the single remaining target, the top-level `Cslib.lean` barrel, on a pre-existing conflict between two files both defining `HasDiamond` (`Cslib/Foundations/Logic/Operators.lean` vs `Cslib/Foundations/Logic/Connectives.lean`) from task 619's in-flight, already-committed migration (`b81f7e48`, `8d13fdba`), which per this dispatch's delegation instructions is explicitly out of territory ("task 619 has preserved (stashed) work targeting `Cslib/Foundations/Logic/Connectives.lean` and ~17 downstream files"). Not caused by, and not fixable within, this task's scope. | `lake build` output: `error: Cslib.lean:1:0: import Cslib.Foundations.Logic.Operators failed, environment already contains 'Cslib.Logic.HasDiamond.casesOn' from Cslib.Foundations.Logic.Connectives`. The build otherwise reaches `[3330/3331]` -- every module in the project, including every file this task touched -- before failing only on `Cslib.lean` itself. `git diff Cslib.lean` (before this task's own `mk_all` run) shows zero changes to `Cslib.lean` from this task's phases 1-9, confirming the conflict predates and is independent of this task's edits. |
| `lake exe lint-style` and `lake exe mk_all --module` | Not excluded -- both ran to completion successfully, since neither depends on the broken `Cslib.olean`. `mk_all` correctly added this task's six new modules (`LJ.CutFreeCompleteness`, `LM.CutElimination`, `LM.Decidability`, `LM.Interpolation`, `LM.SubformulaProperty`, plus the pre-existing `LM.CutElimination`/`Decidability` entries) to `Cslib.lean`'s import list, touching no line outside this task's own new files. | `lake exe lint-style` exit code `0`; `git diff Cslib.lean` after `mk_all` shows only additions, all naming this task's own new files, no deletions. |

---

## Testing & Validation

- [ ] `lake build` succeeds for the whole `Cslib/Logics/Propositional/` subtree.
- [ ] `lake build` succeeds for `CslibTests/` (Phase 1 edits `TableauConformance.lean`).
- [ ] No `sorry` occurs anywhere under `Cslib/Logics/Propositional/` outside docstring prose.
- [ ] `lean_verify` on each new headline theorem (`ljCutFreeCompleteness`, `ljCutFreeIffIValid`,
      `LKProof.splitInterpolation`, `LJProof.splitInterpolation`, `SeqProofMinimal.cutElim`, the
      LM subformula property, the LM interpolation theorem, `instDecidableDerivableInMPL`, the
      orImp relative completeness theorem) reports no axiom beyond
      `{propext, Classical.choice, Quot.sound}`.
- [ ] Every pre-existing `LJProof.*` and `instDecidableLJDerivable` signature is unchanged after
      the generalisations (Phases 6, 8, 9, and the helper rename in Phase 4).
- [ ] Grep confirms no docstring in the touched files asserts strictness, a five-node chain, a
      non-existent `instDecidableDerivable`, external consumers that do not exist, an unpinned
      `MValid`, or generic-over-`T` status for anything that is not.
- [ ] `SequentCalculus/LM.lean` imports seven modules if all phases land (Basic, Soundness,
      Completeness, CutElimination, SubformulaProperty, Interpolation, Decidability), against
      three at plan time. If Phase 6 blocks, the reachable count is four (the three originals plus
      Decidability from Phase 4).

## Artifacts & Outputs

- `specs/618_propositional_coverage_gaps_and_ordering_overclaim/plans/01_propositional-coverage-gaps.md` (this file)
- `specs/618_propositional_coverage_gaps_and_ordering_overclaim/summaries/01_propositional-coverage-gaps-summary.md`
- New Lean modules:
  - `Cslib/Logics/Propositional/SequentCalculus/LJ/CutFreeCompleteness.lean`
  - `Cslib/Logics/Propositional/SequentCalculus/LM/CutElimination.lean`
  - `Cslib/Logics/Propositional/SequentCalculus/LM/SubformulaProperty.lean`
  - `Cslib/Logics/Propositional/SequentCalculus/LM/Interpolation.lean`
  - `Cslib/Logics/Propositional/SequentCalculus/LM/Decidability.lean`
- Modified Lean modules: `ConservativeChain.lean`, three `DecisionProcedure.lean` files,
  `CslibTests/TableauConformance.lean`, `NaturalDeduction/Equivalence.lean`,
  `OrImpConservative.lean`, `LJ/Basic.lean`, `LJ/CutElimination.lean`,
  `LJ/SubformulaProperty.lean`, `LJ/Interpolation.lean`, `LJ/Decidability.lean`,
  `LK/Interpolation.lean`, `LJ.lean`, `LM.lean`

## Rollback/Contingency

- Each phase commits separately, so any phase can be reverted independently. Phase 1 in particular
  is a standalone commit that must land regardless of what happens to Phases 2-9, per the task's
  instruction that the A1 correction not wait on future work.
- Phase 6 is the only phase with real risk of not completing as written, and the risk is
  mechanical (termination checking under a new binder), not mathematical. Its contingency is
  explicit: mark `[BLOCKED]`, record the goal state and the failing obligation, revert only that
  phase's two-file atomic batch, and leave Phases 7-9 unattempted. Phases 1-5 remain landed.
- No phase requires a `sorry` or a new axiom. If any phase appears to need one, that is a signal
  the route was mismeasured -- stop and record rather than introducing debt.
- Signature preservation is the rollback safety net for the generalisation phases: because every
  `IPL`-level name is re-exported with its current signature, reverting a generalisation phase
  cannot strand a downstream call site.
