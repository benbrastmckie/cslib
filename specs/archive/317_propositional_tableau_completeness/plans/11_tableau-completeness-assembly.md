# Implementation Plan: Propositional/Intuitionistic Tableau Completeness — Invariant Threading and Bridge Assembly

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Status**: [PARTIAL] (Phases 0-1 complete and committed; Phase 2 blocked, see
  `handoffs/11_phase2-blocker-findings.md`; Phases 3-7 not started, transitively blocked)
- **Effort**: 18 hours
- **Dependencies**: 552 (completed — landed the `.pos, .imp` branching arm)
- **Research Inputs**:
  - reports/11_team-research.md (synthesis, primary input)
  - reports/11_teammate-a-findings.md (primary route, exact Lean signatures)
  - reports/11_teammate-b-findings.md (bridging-lemma idiom, prior art, Mathlib absence)
  - reports/11_teammate-c-findings.md (claim audit, territory risk, conformance gap)
  - reports/11_teammate-d-findings.md (downstream consumers, task disposition)
  - reports/10_wave-a-atomic-derisk.md (reference only)
- **Artifacts**: plans/11_tableau-completeness-assembly.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-compliance.md
  - .claude/rules/lean4.md
- **Type**: cslib

## Overview

Four bare tactic-level `sorry`s remain under `Cslib/Logics/Propositional/Tableau/`
(`Intuitionistic/Scheme.lean:592`, `Intuitionistic/Scheme.lean:1498`,
`Intuitionistic/Completeness.lean:133`, `Minimal/Completeness.lean:125`). This plan closes all
four. It supersedes plan v6 (`plans/06_route-a-frame-plumbing.md`) rather than resuming it: v6's
Phase 9 and Phase 10 are both `[BLOCKED]`, and the two blockers they recorded have since been
closed by landed code (the `.pos, .imp` branching arm from task 552; the sorry-free
`applyPersistenceFixpoint_genuine_of_count_le_fuel`). Everything v6 built before those phases is
preserved and load-bearing here.

**The task description's "REMAINING SCOPE IS ASSEMBLY ONLY" framing is refuted and must not be
carried into implementation.** Item (1) (`sat_timp`) genuinely is mechanical. Items (2) and (3)
share a prerequisite that does not exist: `intExpandBranches_openBranch_sat`
(`Scheme.lean:1480-1492`) carries `IAllConsistent`/`IAllAccessConsistent` but **no** measure
hypothesis and **no** `φ0` universe parameter, and the three measure lemmas that would feed it
(`intExpMeasure_step_lt` :2521, `intExpMeasure_step_lt_branch` :2589, `intExpMeasure_init_le_fuel`
:2723) have **zero call sites**. `applyPersistenceFixpoint_genuine_of_count_le_fuel` (:2912) is
sorry-free but dead code — its `hb`/`hfuel` hypotheses cannot currently be supplied. Threading
that invariant is new plumbing and is the bulk of this plan (Phases 2-3). Item (4) needs a further
obligation the four-item list never names (Phases 6-7).

Equally, this is **not** open research. Three of the four obligations have verified, concrete
routes, the mandated parametric abstraction already exists and needs no refactor budget, and the
in-file STOP-gate that used to block the atom-persistence argument records its own recommended
route (`Scheme.lean:478-483`, recommendation (a)) which Phases 2-3 make available.

### Additional finding this plan is built on (not in the research reports)

`tableau_complete`'s premise (`Scheme.lean:1927-1930`) is

```lean
(hvalid : ∀ (edges : IEdges) (b : IBranch Atom),
  @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ)
```

quantified over **arbitrary** `edges` and `b`. Discharging it from `IValid φ` requires upward
closure of `intExtractValuation b` along `intAccessPreorder edges` for an arbitrary pair, which is
false (take `b = [T(p)@0]`, `edges = [(0,1)]`). The two bridge sorries as currently posed are
therefore **not provable at their current statement**, independent of any persistence machinery.
The premise must first be narrowed to carry the persistence witness for the pair that
`openBranch_countermodel` actually produces. This is Phase 7, and it is why item (4) is a
two-phase job. The narrowing makes `tableau_complete` strictly stronger, so the stable public
contract (`intuitionisticTableau_complete`, `minimalTableau_complete`, the `Decidable` instances)
stays byte-stable.

### Research Integration

| Research input | What this plan takes from it |
|---|---|
| `11_team-research.md` Recommendations | The Phase 0 spike, the six-step phase sequence, the "split the invariant-threading phase" instruction, the three plan-level risks |
| `11_teammate-a-findings.md` | Exact `sat_timp` field text, the `φ0`/universe-membership/measure-bound invariant shape, the zero-case measure argument, `openBranch_countermodel` (:1893) as the sole call site |
| `11_teammate-b-findings.md` | The copy-completeness bridging lemma and its proof idiom (`applyAllTImpRules_copy_notMem` :2777, `intTImpRule_output_notMem` :2806); forward-only disjunction elimination; "no Mathlib leverage" |
| `11_teammate-c-findings.md` | `git blame` docstring ordering; the pinned `Measure.lean` read dependency; the Minimal conformance blind spot; the sorry-measurement objection |
| `11_teammate-d-findings.md` | 430/456/375/413 disposition — all deferred, none folded in |

### Preserved Assets

The following work is complete and must not regress. All entries verified sorry-free at HEAD
during planning.

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| `IntMinScheme` structure + `intScheme`/`minScheme` instances (the mandated parametric abstraction — already built) | `Intuitionistic/Scheme.lean:118, :159, :208` | [COMPLETED] | 2026-07-26 |
| Parametric `truthLemma` over `S : IntMinScheme Atom` (5 of 6 connective cases closed) | `Intuitionistic/Scheme.lean:555-630` | [COMPLETED] | 2026-07-26 |
| `intAccessPreorder` + `intAccessPreorder_le_of_isAccessible` (edge-reachability `Preorder Nat`) — v6 Phase 1 | `Intuitionistic/Scheme.lean:309-323` | [COMPLETED] | commit `a1883c4e` |
| `IFimpAccess` companion predicate + `IExpandedAccessConsistent`/`IExpandedAccessConsistent_sat` extraction — v6 Phases 1-4 | `Intuitionistic/Scheme.lean:435, :835, :1442` | [COMPLETED] | 2026-07-26 |
| `IExpandedConsistent_sat` (sole `IBranchSaturation` construction site) + the 5 existing saturation fields | `Intuitionistic/Scheme.lean:74-101, :904` | [COMPLETED] | 2026-07-26 |
| `IAllConsistent`/`IExpandedConsistent`/`ILabelBound` invariant + monotonicity combinators; `none`-case closed | `Intuitionistic/Scheme.lean` | [COMPLETED] | plan 03 P1, commit `26508fe9` |
| Fuel raised to `intFuel φ` + downstream caller audit — v6 Phase 5 | `Expansion.lean` and callers | [COMPLETED] | v6 P5 |
| `intSubfmls`/`intUniverse`/`intWork` + `intUniverse_length_le`, `intSubfmls_impCount_le` (:2016) — v6 Phase 6 | `Intuitionistic/Scheme.lean` | [COMPLETED] | v6 P6 |
| Branch-universe containment infrastructure: `mem_intUniverse_of`, `intUniverse_mem_formula`/`_mem_label`, `intTImpRule_outputs_subset`, `intApplyRuleFull_outputs_subset` (:2272) — v6 Phase 6.2 | `Intuitionistic/Scheme.lean` | [COMPLETED] | commits `bb4ffa3c`, `015f81c1` |
| `intExpMeasure_step_lt` (:2521) + `intExpMeasure_step_lt_branch` (:2589) — v6 Phase 7 | `Intuitionistic/Scheme.lean` | [COMPLETED] | v6 P7 |
| `intExpMeasure_init_le_fuel` (:2723) — v6 Phase 8 | `Intuitionistic/Scheme.lean` | [COMPLETED] | v6 P8 |
| `applyPersistenceFixpoint_genuine_of_count_le_fuel` (:2912) + supports `applyAllTImpRules_copy_notMem` (:2777), `intTImpRule_output_notMem` (:2806), `applyAllTImpRules_count_drop` (:2831) | `Intuitionistic/Scheme.lean` | [COMPLETED] | v6 P10 dispatch |
| Option-A dedup `intFImpReuseWitness?` (sound) | `Intuitionistic/Expansion.lean` | [COMPLETED] | commit `4202d1df` |
| Calculus soundness (`intRule_preserves_sat` incl. the `.pos, .imp` case) | `Intuitionistic/Soundness.lean` | [COMPLETED] | task 316/552 — READ-ONLY territory |
| `.pos, .imp` branching arm `[[F(φ)@l],[T(ψ)@l]]` | `Intuitionistic/Rules.lean:274-275` | [COMPLETED] | task 552, commit `db48c4c2` |
| 43-row conformance guard (24 temporal + 19 `intuitionisticTableau` rows) | `CslibTests/TableauConformance.lean` | [COMPLETED] | 2026-07-26 |
| `NegriVonPlato2001` (:913), `Fitting1983` (:211), `Fitting1969` (:204) bib keys | `references.bib` | [COMPLETED] | 2026-07-26 — v6 Phase 11 needs no work |

**Superseded by this plan** (do not resume): v6 Phase 9 `[BLOCKED]` and v6 Phase 10 `[BLOCKED]`.
v6 Phase 9's stated blockers were (1) fuel entanglement and (2) `Sub(φ0)` determinacy. Blocker (2)
is closed by task 552's branching arm. Blocker (1) is now half-closed — the persistence-loop
termination lemma it said was missing exists (`applyPersistenceFixpoint_genuine_of_count_le_fuel`);
what remains is supplying its hypotheses, which is Phases 2-3 here. v6 Phase 11 (bib keys) is
unnecessary: the keys are already present.

## Goals & Non-Goals

**Goals**:
- Close all four bare sorries in `Cslib/Logics/Propositional/Tableau/`, reaching a sorry-free
  intuitionistic and minimal tableau completeness development.
- Add `sat_timp` to `IBranchSaturation` and discharge it at its sole construction site.
- Thread a `φ0`-universe-membership + measure-bound invariant through
  `intExpandBranches_openBranch_sat`, wiring the three currently-dead `intExpMeasure_*` lemmas and
  `applyPersistenceFixpoint_genuine_of_count_le_fuel` into live use.
- Deliver the two new companion predicates (`ITimpAccess`, `IAtomPersist`) from the same site that
  already delivers `IFimpAccess`, and consume them in `truthLemma` and in the two validity bridges.
- Narrow `tableau_complete`'s `hvalid` premise so the bridges are provable, keeping every public
  statement byte-stable.
- Repair the stale docstring block at `Scheme.lean:3001-3022`.
- Keep CI green: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`; the 43-row conformance guard stays green.

**Non-Goals**:
- Any parametric refactor of Int/Min. `IntMinScheme` already exists; both `Completeness.lean`
  files are already thin ~130-line corollaries. Zero budget.
- Any change to `Rules.lean` or `Expansion.lean` calculus rules. The stale block's "new calculus
  rule needed" recommendation is wrong.
- Any edit to `Cslib/Foundations/**` (read-only dependency) or `Intuitionistic/Soundness.lean` /
  `Minimal/Soundness.lean` (task 316 territory).
- Any Mathlib search for Kripke/persistence/fuel machinery — verified absent.
- Redefining `IForces`, `IValid`, `MValid`, or `iforces_persistence` (v6 Route (b), rejected).
- Tasks 430, 456, 375, 413. Task 430's disposition is decided **after** this task lands.
- Adding `minimalTableau` rows to the conformance guard (named as residual risk R2, not fixed here).

## Risks & Mitigations

| ID | Risk | Impact | Likelihood | Mitigation |
|----|------|--------|------------|------------|
| R1 | **Pinned read-only dependency breaks.** `Scheme.lean:10` imports `Cslib.Foundations.Logic.Tableau.Measure` and consumes `sum_map_le_length_mul` at :2058 and :2068. A concurrent session (task 557, modal-tableau refactor/Boneyard programme) holds a live lock (`sess_1785105096_50f3c7`, acquired 2026-07-26T22:31:36Z) and is restructuring exactly this class of shared abstraction. This task never writes there, but a move/rename/archive breaks its build. | H | M | **Pinned-SHA pre-phase check, not coordination hope.** Pinned SHA at plan time: `facba1f42469805b666d6eca78156ac4d7be5c71` (task 458 phase 1, 2026-07-01). At the start of every phase run `git log -1 --format=%H -- Cslib/Foundations/Logic/Tableau/Measure.lean` and compare. On mismatch: do not start the phase; re-verify `sum_map_le_length_mul` still exists with the same signature (`lean_hover_info`), record the new SHA in the phase's Started line, and only then proceed. If the lemma or file is gone, mark the phase `[BLOCKED]` and hand off — do not attempt an in-place substitute. |
| R2 | **Minimal calculus has zero executable regression protection.** `CslibTests/TableauConformance.lean` has 43 rows, of which **zero** are `minimalTableau` (verified: `grep -c minimalTableau` returns 0). This task closes `Minimal/Completeness.lean:125`, so a Minimal-side regression is invisible to the guard the acceptance criteria rely on. | M | M | Compensate inside this task rather than expanding scope: every phase touching the Minimal side must run `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness` **and** `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` scoped-green, and Phase 7 must `#print axioms Cslib.Logic.PL.minimalTableau_complete` and record the axiom set in the summary. Recommend (do not implement) a follow-up to add `minimalTableau` conformance rows; name it in the completion summary. |
| R3 | **Narrowing `tableau_complete`'s `hvalid` premise ripples into `DecisionProcedure.lean`.** | M | M | Adding a hypothesis to `hvalid`'s binder makes the premise weaker and `tableau_complete` stronger, so existing callers get easier goals, not harder ones. Phase 7 must nonetheless scoped-build both `DecisionProcedure` modules and confirm `intuitionisticTableau_complete` / `minimalTableau_complete` / `instDecidableIValid` statements are byte-identical (`git diff` shows only proof-body changes in those declarations). |
| R4 | **Phase 3's zero-case measure argument is the largest single unit** and is a genuinely new lemma (measure = 0 ⟹ `e ⊇ intUniverse φ0` ⟹ every compound formula on `b` already in `e`). | H | M | Bounded-attempt budget: Phase 3 is split from Phase 2 precisely so the zero case has a dispatch of its own. If the zero case does not close within the phase, commit the green succ-case maintenance from Phase 3's first half and mark the phase `[PARTIAL]` with the exact resisting goal — do **not** introduce a sorry and do **not** widen scope into Phase 4. |
| R5 | **Phase 6's atom-persistence induction may be genuinely open-ended.** The in-file STOP-gate author (`Scheme.lean:442-483`) states it is "not completable from completeness-side machinery alone" as of the pre-invariant design, and two research teammates independently flagged item (4) as under-scoped. | H | M | The STOP-gate's own recommendation (a) (`Scheme.lean:478-481`) is the route: state persistence as a predicate threaded alongside `sat_timp` and discharge it once `measure ≤ fuel` is available — which Phases 2-3 make available, removing the wave-ordering inversion the STOP-gate describes. Phase 6 gets an explicit stopping condition (below). If it stops, the phase is `[BLOCKED]` with the exact goal, this plan is re-planned, and task 430 (whose own falsification spike already identifies this same obligation) is the natural home. **No strategic sorry is planned for this division point** — see Rollback/Contingency for why. |
| R6 | **Context overflow on large recursive proofs.** Prior dispatches on this task overflowed (v6 R6, observed). | H | H | Scoped + grepped builds only; `offset`/`limit` windowed reads — never a whole-file read of `Scheme.lean` (3000+ lines); prefer `lean_multi_attempt` over repeated `lean_goal` dumps; commit at every green sub-step; stop and write a sharp handoff the instant context tightens. A committed green partial is success. |
| R7 | **Concurrent writers on `Scheme.lean`.** Multiple live orchestrator sessions exist in this repo (verified: uncommitted modifications to `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` and `LoopChecking.lean` at plan time). | M | H | SINGLE-WRITER-PER-FILE. Every phase runs `git log -1 -- <target file>` plus a scoped green build before its first edit. The wave table below is deliberately fully sequential for this reason. Never `git add -A`; commit only the files the phase touched. |
| R8 | **Adding a field to `IBranchSaturation` disturbs `Soundness.lean`.** Not confirmed read-only by research. | M | L | Phase 1 opens with `grep -rn "IBranchSaturation" Cslib/` to re-confirm the single construction site (`IExpandedConsistent_sat`, `Scheme.lean:904`) before adding the field. If a second construction site exists in `Soundness.lean`, mark `[BLOCKED]` and escalate — do not edit `Soundness.lean`. |
| R9 | **Spike answer (b) comes back "no extra obligation needed."** | L | L | Then Phases 6 and 7 collapse into a single phase and the plan is smaller than written. This is the good branch; record the decision in the Phase 0 output and mark Phase 6 `[COMPLETED]` as vacuous with the evidence, rather than silently skipping it. |

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from this task's actual history (plan v6
Phases 9/10 `[BLOCKED]` resolutions, the v5/v6 postmortem list, and the 2026-07-26 research), not
from generic guidance.

**Do NOT**:

1. **Do NOT treat "sorry-free" as "usable."** This task's central failure mode. Three
   `intExpMeasure_*` lemmas and `applyPersistenceFixpoint_genuine_of_count_le_fuel` are all
   sorry-free with **zero call sites**, because their hypotheses cannot be supplied where they are
   needed. Before claiming any lemma closes an obligation, check its call sites and confirm every
   hypothesis is derivable at the intended use point.
2. **Do NOT resolve contradictory in-file docstrings by judgment.** Use `git blame` ordering.
   `Scheme.lean:488` ("Gap 2 RESOLVED", commit `db48c4c2`, 2026-07-24 23:51) postdates
   `Scheme.lean:3001` ("determinacy remains BLOCKED", commit `a0a16c4b`, 2026-07-24 08:26) by
   fifteen hours, and is the commit that landed the branching arm the earlier block says is
   missing. The `~3000` block is the stale one.
3. **Do NOT budget for a parametric refactor.** `IntMinScheme` (`Scheme.lean:118`, instances :159
   and :208) already exists; `truthLemma`/`openBranch_countermodel`/`tableau_complete` are already
   stated once against it; both `Completeness.lean` files are already thin corollaries. Read the
   description's "rather than duplicating" as "keep it this way."
4. **Do NOT propose or implement a new calculus rule.** The stale block's recommendation of a
   `Rules.lean`/`Expansion.lean` calculus-level change is wrong both by staleness and technically:
   the T-imp case needs no converse IH.
5. **Do NOT search Mathlib for Kripke semantics, intuitionistic persistence, tableau calculi, or
   fuel/fixpoint-sufficiency machinery.** Verified absent by exhaustive rate-limited search.
   Heyting algebras exist and connect to nothing here. The reusable pieces
   (`Relation.ReflTransGen`, `intAccessPreorder`) are already in-repo and in use.
6. **Do NOT run a raw full `lake build`** during phase work. Scoped and grepped only, e.g.
   `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"`.
   A full `lake build` belongs only in the final CI gate. Another session is actively building in
   this repo.
7. **Do NOT read `Scheme.lean` whole.** Windowed `offset`/`limit` reads only (R6).
8. **Do NOT run two writers on the same file concurrently** (R7). `git log -1 -- <file>` before
   each phase. Never `git add -A` or `git commit -am`; stage only the files the phase touched.
9. **Do NOT introduce any `sorry`, `axiom`, or vacuous/placeholder definition** (`def X := True`,
   `theorem X := trivial`, etc.). A phase that cannot close is `[BLOCKED]` or `[PARTIAL]` with a
   handoff, never a forced closure.
10. **Do NOT edit `Intuitionistic/Soundness.lean`, `Minimal/Soundness.lean`, or anything under
    `Cslib/Foundations/`.** Read-only. Task 316 / task 557 territory.
11. **Do NOT change any public statement.** `intuitionisticTableau_complete`,
    `minimalTableau_complete`, `Decidable (IValid φ)`, `Decidable (Derivable IntPropAxiom φ)`,
    `instDecidableIValid`, and every `DecisionProcedure` consumer stay byte-stable. Thread new
    internal hypotheses through `private` `_aux`/`key` helpers.
12. **Do NOT fold in tasks 430, 456, 375, or 413.** 430's disposition is decided after this task
    lands, and only then.

**MUST preserve**:

- Every row of the Preserved Assets table above, unmodified and sorry-free.
- The full two-direction `truthLemma` (both the T- and F-directions of every connective case).
- The literal `sat_fimp` field (no reformulation).
- The Option-A dedup `intFImpReuseWitness?` (sound; do not revert).
- A green scoped build at every commit boundary. The four inventory sorries persist only until
  their owning phase closes them; no phase may add a new one.
- The 43-row conformance guard green.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):

- **`sat_timp` is the reflexive, same-label field** (teammate A's shape, adopted over teammate B's
  quantify-over-accessible-worlds shape). Rationale: the total lift work is identical; A's shape
  keeps the discharge at `IExpandedConsistent_sat` purely mechanical and isolates the
  copy-completeness fact as a separately verifiable unit. Exact statement fixed in Phase 1.
- **The accessible-world lift is delivered as a companion predicate `ITimpAccess edges b`**, not as
  a field, mirroring the already-landed `IFimpAccess edges b` (`Scheme.lean:435`) and delivered
  from the same site (`intExpandBranches_openBranch_sat`'s `∃ edges, ... ∧ IFimpAccess edges b`
  conclusion, `:1492`). Same for atom persistence (`IAtomPersist edges b`, Phase 6).
- **Frame = edge reachability** (`intAccessPreorder`), not numeric `≤`. Route (b) (redefining
  `IForces`) stays rejected.
- **Fuel stays raised** to `intFuel φ`; the measure is the counting-against-fixed-universe measure.
- **The two validity bridges are one parametric lemma** over `S : IntMinScheme Atom`, instantiated
  at `intScheme` (where the `modelBot` obligation is vacuous — `fun _ => False`) and `minScheme`
  (where it is real).

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2 | 0, 1 |
| 4 | 3 | 2 |
| 5 | 4 | 3 |
| 6 | 5 | 1, 4 |
| 7 | 6 | 3 |
| 8 | 7 | 5, 6 |

Phases within the same wave can execute in parallel.

**Parallelism declaration (explicit, per H7 territory contract)**: there is **no** exploitable
parallelism in this plan, and the fully-sequential wave table is a deliberate result rather than an
oversight. Phases 1-6 all write `Intuitionistic/Scheme.lean`, and R7 (concurrent writers, observed
live in this repo) forbids two writers on one file. Phase 7 is the only phase that writes elsewhere
(`Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`) but it depends on both 5 and 6, so
it cannot be lifted into an earlier wave. Phase 0 is read-only but must precede every writer,
because a spike agent reading `Scheme.lean` while another agent rewrites it is exactly the
territory hazard R7 names. Territory contract: **one `Scheme.lean` writer at a time, for the whole
plan.**

### Phase 0: Verification spike — record the two load-bearing decisions [COMPLETED]

- **Goal:** Answer two questions against live Lean goal state before any phase boundary downstream
  is treated as fixed, and record the answers as a durable decision record.
- **Tasks:**
  - [ ] Pinned-SHA check (R1): `git log -1 --format=%H -- Cslib/Foundations/Logic/Tableau/Measure.lean`;
        compare against `facba1f42469805b666d6eca78156ac4d7be5c71`.
  - [ ] Re-grep the four sorry locations (line numbers drift; v6 saw +50 shifts from doc inserts):
        `grep -rnE '(^[[:space:]]+sorry[[:space:]]*(--.*)?$)|((:=|by|<;>|;)[[:space:]]+sorry([[:space:]]|$))' Cslib/Logics/Propositional/Tableau/ --include=*.lean`
  - [ ] **Question (a)**: does forward-only disjunction elimination close the T-imp case at
        `Scheme.lean:592`? Use `lean_goal` at :592 to record the exact goal and context, then
        `lean_multi_attempt` a script that assumes `sat_timp` (reflexive, at `w'`) and
        `ITimpAccess` (copy at every edge-accessible `w'`) as named hypotheses and closes by:
        `F(φ')@w'` arm — contrapositive of `ih_φ'`'s F-direction against the given
        `IForces val w' φ'`; `T(ψ')@w'` arm — `ih_ψ'`'s T-direction directly. Teammates B and C
        both argue this works and that the stale docstring's "needs the converse IH" objection is
        wrong; neither verified it in Lean. Probe scratch files go under
        `specs/317_propositional_tableau_completeness/` — **never** under `Cslib/`, and nothing
        from this phase is committed to `Cslib/`.
  - [ ] **Question (b)**: do the two validity bridges need an atom-persistence obligation beyond
        `sat_timp`? Use `lean_goal` at `Intuitionistic/Completeness.lean:133` and
        `Minimal/Completeness.lean:125`, and read `tableau_complete`'s `hvalid` binder
        (`Scheme.lean:1927-1930`). Confirm or refute this plan's Overview finding that `hvalid`'s
        quantification over arbitrary `edges`/`b` makes the current bridge statement unprovable and
        forces the Phase 7 premise narrowing.
  - [ ] Confirm `IBranchSaturation` has exactly one construction site (R8):
        `grep -rn "IBranchSaturation" Cslib/`.
  - [ ] Write the decision record to
        `specs/317_propositional_tableau_completeness/handoffs/11_phase0-spike-decisions.md`:
        for each of (a) and (b), the exact goal text, what was attempted, the verdict, and whether
        the phase sequence below is CONFIRMED or requires RE-PLAN.
- **Expected output:** ~100-150 lines (decision record only; no `Cslib/` edits).
- **Done when:** the decision record exists and states, for both questions, a verdict backed by a
  recorded goal state — not by a static reading.
- **Branch point:** if (b) is **yes** (the expected answer), this is an eight-phase job as written.
  If (b) is **no**, Phases 6 and 7 collapse into one and the plan must be re-scoped downward before
  Phase 6 is dispatched. If (a) fails, STOP: the specific way it fails is exactly what a re-plan
  needs, and closing :592 becomes an open problem rather than an assembly step.
- **Timing:** 1 hour
- **Depends on:** none

### Phase 1: `sat_timp` field on `IBranchSaturation` + mechanical discharge [COMPLETED]

- **Goal:** Add the reflexive `sat_timp` field and discharge it at `IExpandedConsistent_sat`, the
  sole construction site, leaving the file scoped-green.
- **Tasks:**
  - [ ] Pinned-SHA check (R1) + `git log -1 -- Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (R7).
  - [ ] Add the field to `IBranchSaturation` (`Scheme.lean:74-101`), after `sat_fimp`, matching the
        surrounding docstring style:
        `sat_timp : ∀ (φ ψ : Proposition Atom) (w : Nat), b.any (fun sf => sf.sign == .pos && sf.formula == .imp φ ψ && sf.label == w) = true → b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) = true ∨ b.any (fun sf => sf.sign == .pos && sf.formula == ψ && sf.label == w) = true`
  - [ ] Discharge it in `IExpandedConsistent_sat` (`Scheme.lean:904`) by the same six-line pattern
        the five existing fields use, via `compound_sat` on `sfSatisfied`'s `.pos, .imp` clause
        (`Scheme.lean:765-771`, which already states exactly this disjunction). `intApplyRuleFull`'s
        `.pos, .imp` case is `.branchingResult`, hence `≠ .notApplicable`, so `compound_sat`
        applies unchanged.
  - [ ] Scoped build: `Intuitionistic.Scheme`, then `Intuitionistic.Completeness` and
        `Minimal.Completeness` (field addition ripples to every `IBranchSaturation` consumer).
  - [ ] Commit (scoped staging, task-scoped message).
- **Expected output:** ~60-100 lines.
- **Done when:** `sat_timp` is a field, `IExpandedConsistent_sat` is still sorry-free, all three
  scoped builds are green, and the sorry count in the tree is still exactly 4 (this phase closes
  none).
- **Timing:** 1.5 hours
- **Depends on:** 0

### Phase 2: Universe/measure invariant — definition and call-site threading [BLOCKED]

**Blocked 2026-07-26.** Full findings recorded at
`specs/317_propositional_tableau_completeness/handoffs/11_phase2-blocker-findings.md`. Summary:
(1) `intUniverse`/`intExpMeasure` are declared ~450-950 lines *after*
`intExpandBranches_openBranch_sat` in the file, so referencing them in its signature is a forward
reference — verified via a real build error, not a typo — requiring a large (but mechanical)
relocation of that block; (2) independent of (1), maintaining the universe-membership invariant
across the F-imp world-creating recursive step needs a `nextWorld ≤ φ0.complexity + 1` bound
(`intExpandBranches_world_bound`) that is explicitly documented in-file
(`Scheme.lean:2025-2038`, `:2052-2055`, `:2536-2538`) as a known, unbuilt "continuation, see
handoff" item — not a mechanical assembly step. No `sorry`/axiom/vacuous statement was
introduced; the broken in-progress attempt was reverted (`git checkout --`) back to the
Phase-1-committed green state. The handoff also records a genuine positive finding: Phase 3's
zero case is easy once the invariant exists (a short contradiction from `intExpMeasure ≤ 0`
forcing `branches = []`), so the *actual* remaining difficulty is narrower than Phase 3's own
text describes, but it sits earlier (Phase 2's succ-case threading prerequisite), not in the zero
case itself. **Recommendation: re-plan Phases 2-3 (and transitively 4-7) as a new round budgeting
explicitly for the relocation and the new world-bound lemma.**

- **Goal:** Give `intExpandBranches_openBranch_sat` the `φ0` parameter and the two invariant
  hypotheses it currently lacks, and establish them at its sole call site. No sorry closes here;
  this is the plumbing that makes Phases 3-6 possible.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks.
  - [ ] Add to `intExpandBranches_openBranch_sat` (`Scheme.lean:1480-1492`) a fixed formula
        parameter `φ0 : Proposition Atom`, a universe-membership invariant
        `∀ x ∈ bh, x ∈ intUniverse φ0` (mirroring
        `applyPersistenceFixpoint_genuine_of_count_le_fuel`'s own `hb`, `Scheme.lean:2912-2917`),
        and a measure bound
        `intExpMeasure (intUniverse φ0) (bh :: pending) (e :: pendingExp) ≤ fuel' + 1`.
        Propagate both through the internal `key`/`go` induction statement (`:1501-1520`).
  - [ ] Establish both at the sole call site, `openBranch_countermodel` (`:1871`, invocation at
        `:1893`), using `intExpMeasure_init_le_fuel φ` (`:2723`) and `intUniverse`'s membership
        constructors `intUniverse_mem_formula`/`intUniverse_mem_label` — all currently dead code,
        now given their first call sites.
  - [ ] Keep the new hypotheses internal: `openBranch_countermodel`'s and
        `tableau_complete`'s conclusions must not gain a premise (Postmortem 11).
  - [ ] Scoped builds; commit at green.
- **Expected output:** ~150-250 lines.
- **Done when:** `intExpandBranches_openBranch_sat` carries `φ0` plus both invariants, the call site
  discharges them, `intExpMeasure_init_le_fuel` has a call site, the tree still has exactly 4
  sorries, and the scoped builds are green.
- **Timing:** 3 hours
- **Depends on:** 0, 1

### Phase 3: Succ-case invariant maintenance + fuel=0 zero-case discharge [NOT STARTED]

- **Goal:** Maintain the Phase 2 invariant across the recursive calls, then use it to close the
  fuel=0 base case. Closes sorry 2 of 4 (`Scheme.lean:1498`).
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks.
  - [ ] Succ case (`Scheme.lean:1499` onward): re-establish the measure bound at each recursive call
        using `intExpMeasure_step_lt` (`:2521`) and `intExpMeasure_step_lt_branch` (`:2589`) — both
        sorry-free and currently uncalled — and re-establish universe membership using
        `intApplyRuleFull_outputs_subset` (`:2272`) and `intTImpRule_outputs_subset`.
  - [ ] **Commit here** if the succ case is green, before attempting the zero case (R4).
  - [ ] Zero case (`:1494-1498`): from `measure ≤ fuel = 0` derive `measure = 0`; since each
        summand `3 ^ intWork U b e ≥ 1`, a sum-of-zero argument forces `intWork U b e = 0` for the
        selected pair; `intWork`'s second summand is
        `(intUniverse φ0).countP (fun sf => !(e.any (· == sf)))`, so this gives
        `e ⊇ intUniverse φ0`. Combined with `∀ x ∈ b, x ∈ intUniverse φ0` and the closure property
        that every `intApplyRuleFull` output on `b` lies in `intUniverse φ0`, conclude that every
        compound formula on `b` is already in `e` — the same fact `intStepBranch_none_compound_mem`
        extracts from `intStepBranch b e nw = none`, derived here from the measure instead. Feed it
        to `IExpandedConsistent_sat`/`IExpandedAccessConsistent_sat` and replace the `sorry`.
  - [ ] Scoped builds; commit at green.
- **Expected output:** ~200-300 lines.
- **Done when:** `Scheme.lean:1498`'s `sorry` is gone, the tree has exactly 3 sorries, and the
  scoped builds are green.
- **Stopping condition (R4):** if the zero case does not close within this phase, commit the green
  succ-case work, mark the phase `[PARTIAL]`, and hand off the exact resisting goal. Do not
  introduce a sorry; do not widen into Phase 4.
- **Timing:** 4 hours
- **Depends on:** 2

### Phase 4: `ITimpAccess` copy-completeness bridge [NOT STARTED]

- **Goal:** Convert the genuine-fixpoint equality into membership at every edge-accessible world,
  and expose it from `intExpandBranches_openBranch_sat` alongside `IFimpAccess`.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks.
  - [ ] Define `ITimpAccess (edges : IEdges) (b : IBranch Atom) : Prop`, mirroring `IFimpAccess`
        (`Scheme.lean:435`):
        `∀ (φ ψ : Proposition Atom) (w w' : Nat), b.any (T(φ→ψ)@w) = true → isAccessible edges w w' = true → b.any (T(φ→ψ)@w') = true`.
  - [ ] Prove it at a genuine fixpoint by contradiction against the fixpoint equality, using the
        `if b.any (...) then none else some copy` guard idiom already established by
        `applyAllTImpRules_copy_notMem` (`:2777`) and `intTImpRule_output_notMem` (`:2806`): if the
        copy were absent, one more `applyAllTImpRules` round would add it, contradicting equality.
  - [ ] Supply `applyPersistenceFixpoint_genuine_of_count_le_fuel`'s `hb` and `hfuel` from the
        Phase 2/3 invariant at the point `bPers` is computed (`Scheme.lean:1548` region), giving
        that lemma its first call site.
  - [ ] Widen `intExpandBranches_openBranch_sat`'s conclusion (`:1492`) to
        `∃ edges, IBranchSaturation Atom b ∧ IFimpAccess edges b ∧ ITimpAccess edges b`, and update
        the `openBranch_countermodel` call site's `obtain`.
  - [ ] Scoped builds; commit at green.
- **Expected output:** ~120-200 lines.
- **Done when:** `ITimpAccess` is defined and delivered from the open-branch boundary,
  `applyPersistenceFixpoint_genuine_of_count_le_fuel` has a call site, the tree still has exactly 3
  sorries, and the scoped builds are green.
- **Timing:** 2 hours
- **Depends on:** 3

### Phase 5: Close `truthLemma`'s T-imp case and repair the stale docstring [NOT STARTED]

- **Goal:** Close sorry 1 of 4 (`Scheme.lean:592`) and, in the same phase, delete or rewrite the
  now-fully-obsolete blocked-determinacy block.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks; re-grep the sorry's current line number.
  - [ ] Add `(htimp : ITimpAccess edges b)` to `truthLemma`'s signature (`Scheme.lean:555-559`),
        alongside the existing `hfimp`, and thread it from `openBranch_countermodel`.
  - [ ] Close the T-imp case exactly as Phase 0(a) verified: `intro _`; obtain the copy at `w'` from
        `htimp`; apply `hsat.sat_timp` at `w'` to get the disjunction; in the `F(φ')@w'` arm derive
        a contradiction with the given `IForces val w' φ'` via the contrapositive of `ih_φ'`'s
        F-direction; in the `T(ψ')@w'` arm close with `ih_ψ'`'s T-direction. No converse IH.
  - [ ] Replace the stale comment block at `Scheme.lean:579-591` (inside the case) with a short
        note describing the landed proof.
  - [ ] **Docstring repair**: rewrite or delete the block at `Scheme.lean:3001-3022` ("GAP 2
        investigation ... determinacy remains BLOCKED"). It is both stale (written fifteen hours
        before the commit that landed the branching arm) and technically wrong (it claims a converse
        IH is required). Mirror the style of the "Gap 2 ... RESOLVED" block at `:485-500`, and point
        at the landed `sat_timp` field and T-imp proof.
  - [ ] Re-scan `Scheme.lean` for any other docstring rendered false by Phases 1-5, in particular
        the STOP-gate at `:442-483` and the `sat_timp` discharge note at `:485-533`, and update
        them.
  - [ ] Scoped builds; commit at green.
- **Expected output:** ~120-200 lines (proof plus docstring edits).
- **Done when:** `Scheme.lean:592`'s `sorry` is gone, the tree has exactly 2 sorries (both bridges),
  no docstring in `Scheme.lean` still asserts determinacy or the T-imp case is blocked, and the
  scoped builds are green.
- **Timing:** 2 hours
- **Depends on:** 1, 4

### Phase 6: `IAtomPersist` upward-closure predicate and its discharge [NOT STARTED]

- **Goal:** Supply the atom-persistence obligation the task's four-item list never names: upward
  closure of `intExtractValuation b` (and, for the Minimal side, `minBranchBotForces b`) along
  `intAccessPreorder edges`, for the branch the expansion actually returns.
- **Route (settled, from the in-file STOP-gate's own recommendation (a), `Scheme.lean:478-481`):**
  state persistence as a predicate threaded alongside `sat_timp`/`ITimpAccess` and discharge it
  once `measure ≤ fuel` is available. Phases 2-3 make it available, removing the wave-ordering
  inversion the STOP-gate describes as the reason it was previously not completable.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks. Re-read the Phase 0 decision record; if (b) came back
        "no", stop and re-scope (R9).
  - [ ] Define `IAtomPersist (edges : IEdges) (b : IBranch Atom) : Prop` as upward closure of the
        atom-membership test along `isAccessible edges`, mirroring `IFimpAccess`/`ITimpAccess`
        shape. State the `modelBot` analogue parametrically over `S : IntMinScheme Atom` so one
        predicate covers `intExtractValuation` and `minBranchBotForces` (`Minimal/Soundness.lean:169-171`).
  - [ ] Discharge it at the genuine persistence fixpoint by induction on formula complexity: the
        fixpoint (Phase 4's machinery) is the base fact for the atom case; the imp/and/or cases use
        the IH. The co-inductive dependency the STOP-gate describes at `:461-465` (a `T(atom p)`
        introduced by a `T(φ→atom p)`-triggered `intTImpRule` firing at a later persistence round
        needs the antecedent's own persistence to have already propagated) is exactly what the
        genuine fixpoint discharges — at a fixpoint there is no "later round."
  - [ ] Extend `intExpandBranches_openBranch_sat`'s conclusion with `IAtomPersist edges b` and
        update the `openBranch_countermodel` call site.
  - [ ] Scoped builds; commit at green.
- **Expected output:** ~200-300 lines.
- **Done when:** `IAtomPersist` is defined, discharged sorry-free, and delivered from the
  open-branch boundary; the tree still has exactly 2 sorries; scoped builds green.
- **Stopping condition (R5):** this phase has a hard stop. If the induction does not close within
  the dispatch, commit whatever is green, mark the phase `[BLOCKED]`, and record the exact
  resisting goal plus which case of the complexity induction failed. Do not introduce a sorry, do
  not weaken the statement to something vacuous, and do not proceed to Phase 7. A blocked Phase 6
  triggers a re-plan; task 430 (whose own falsification spike identifies this same obligation) is
  the natural home for the escalation, but that disposition is not made here.
- **Timing:** 3 hours
- **Depends on:** 3

### Phase 7: Narrow `tableau_complete`'s premise and close both validity bridges [NOT STARTED]

- **Goal:** Close sorries 3 and 4 of 4 (`Intuitionistic/Completeness.lean:133`,
  `Minimal/Completeness.lean:125`) as one parametric lemma, reaching a sorry-free tree.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks; re-grep both sorry line numbers.
  - [ ] **Premise narrowing (the Overview finding):** change `tableau_complete`'s `hvalid`
        (`Scheme.lean:1927-1930`) from `∀ edges b, IForces ...` to
        `∀ edges b, IAtomPersist edges b → (S.modelBot-persistence) → IForces ...`, and supply the
        two witnesses inside `tableau_complete`'s own proof from `openBranch_countermodel`'s
        Phase-6-widened conclusion (`:1937`). This makes `tableau_complete` strictly stronger; no
        public statement changes.
  - [ ] State one private parametric bridge over `S : IntMinScheme Atom` taking the upward-closure
        witnesses and producing the `hvalid` premise from validity, using `IValid`/`MValid`'s shape
        at `Cslib/Logics/Propositional/Semantics/Kripke.lean:145-168`.
  - [ ] Instantiate at `intScheme` in `Intuitionistic/Completeness.lean:124-133` — the `modelBot`
        obligation is vacuous, `fun _ => False` being trivially upward-closed (compare
        `mvalid_implies_ivalid`, `Kripke.lean:165-168`) — replacing the `sorry`.
  - [ ] Instantiate at `minScheme` in `Minimal/Completeness.lean:113-125` — here the `modelBot`
        obligation is real and is discharged by Phase 6's parametric `modelBot` clause — replacing
        the `sorry`.
  - [ ] Update the "Notes on sorry" docstring sections in `Intuitionistic/Completeness.lean:39-43`,
        `Minimal/Completeness.lean:43-47`, `Intuitionistic/DecisionProcedure.lean:34-59`, and
        `Minimal/DecisionProcedure.lean:20-66` — all four currently describe deferred completeness
        sorries and sorry-taint that will no longer exist.
  - [ ] **Byte-stability check (R3):** `git diff` must show only proof-body changes, never statement
        changes, in `intuitionisticTableau_complete`, `minimalTableau_complete`, and every
        `Decidable` instance. Scoped-build both `DecisionProcedure` modules.
  - [ ] Axiom gate: `lean_verify` / `#print axioms` on
        `Cslib.Logic.PL.intuitionisticTableau_complete` and
        `Cslib.Logic.PL.minimalTableau_complete`; expect `{propext, Classical.choice, Quot.sound}`
        with no `sorryAx`. Record both axiom sets in the summary (R2 compensation).
  - [ ] Full CI gate (see Testing & Validation); commit at green.
- **Expected output:** ~200-300 lines (proof plus four docstring sections).
- **Done when:** the strict sorry scan over `Cslib/Logics/Propositional/Tableau/` returns **zero**
  hits, both public theorems print sorry-free axiom sets, and the full CI pipeline is green.
- **Timing:** 2 hours
- **Depends on:** 5, 6

## Testing & Validation

**Sorry measurement (the acceptance criterion's operational definition).** The repo-wide `grep -rn
"sorry"` figure (169 hits across many files at plan time) conflates tactic uses with prose and is
**not** a usable baseline. Use this stricter scan instead:

```
grep -rnE '(^[[:space:]]+sorry[[:space:]]*(--.*)?$)|((:=|by|<;>|;)[[:space:]]+sorry([[:space:]]|$))' Cslib --include=*.lean
```

- **Baseline verified 2026-07-26 at plan time**: 29 hits across 10 files. Exactly 4 are in
  `Cslib/Logics/Propositional/Tableau/` — `Intuitionistic/Scheme.lean:592`,
  `Intuitionistic/Scheme.lean:1498`, `Intuitionistic/Completeness.lean:133`,
  `Minimal/Completeness.lean:125`. (A looser variant of this pattern also matches one prose line at
  `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean:323`; the pattern above excludes it.)
- **Authoritative task-scoped criterion**: the scan restricted to
  `Cslib/Logics/Propositional/Tableau/` goes from **4 to 0**.
- **Repo-wide figure is a moving target** and must be measured before and after **at the same
  commit**, never compared across sessions: a concurrent session had uncommitted modifications to
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` and `LoopChecking.lean` at plan time, and that
  file's sorry line number moved during the planning pass itself.
- **Axiom gate (stronger than any grep)**: `#print axioms` / `lean_verify` on
  `Cslib.Logic.PL.intuitionisticTableau_complete`, `Cslib.Logic.PL.minimalTableau_complete`,
  `Cslib.Logic.PL.truthLemma`, and `Cslib.Logic.PL.tableau_complete` must show no `sorryAx`.

**Per-phase**:
- [ ] Pinned-SHA check on `Cslib/Foundations/Logic/Tableau/Measure.lean` before every phase (R1).
- [ ] `git log -1 -- <target file>` before every phase's first edit (R7).
- [ ] Scoped grepped build of the edited module, e.g.
      `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"`.
- [ ] Scoped build of `Cslib.Logics.Propositional.Tableau.Minimal.Completeness` and
      `...Minimal.DecisionProcedure` for any phase touching shared machinery (R2 compensation —
      the conformance guard has zero `minimalTableau` rows).
- [ ] Strict sorry scan over the task tree; the count must match the phase's stated expectation.

**Final CI gate (Phase 7 only)**:
- [ ] `lake build`
- [ ] `lake exe checkInitImports`
- [ ] `lake lint`
- [ ] `lake exe lint-style`
- [ ] `lake test` — the 43-row `CslibTests/TableauConformance.lean` guard must stay green
- [ ] `lake shake --add-public --keep-implied --keep-prefix`
- [ ] Strict sorry scan: zero hits in `Cslib/Logics/Propositional/Tableau/`
- [ ] Axiom gate on the four declarations above

## Artifacts & Outputs

- `specs/317_propositional_tableau_completeness/plans/11_tableau-completeness-assembly.md` (this file)
- `specs/317_propositional_tableau_completeness/handoffs/11_phase0-spike-decisions.md` (Phase 0)
- `specs/317_propositional_tableau_completeness/summaries/11_tableau-completeness-assembly-summary.md` (on completion)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (Phases 1-7)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` (Phase 7)
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (Phase 7)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` (Phase 7, docstrings)
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (Phase 7, docstrings)

## Rollback/Contingency

- **Per-phase rollback**: every phase commits only at a scoped-green boundary with scoped staging,
  so any phase is revertible by a single `git revert` of its commit without disturbing earlier
  phases. Never `git add -A`.
- **Phase 0 says (a) fails**: closing `Scheme.lean:592` is an open problem, not an assembly step.
  Stop, record the failing goal, and re-plan. Do not dispatch Phases 1-5 on the assumption that the
  disjunction-elimination route works.
- **Phase 3 zero case resists**: commit the green succ-case half, mark `[PARTIAL]`, hand off. The
  three downstream phases are all blocked on it, so this is a genuine stop, not a detour.
- **Phase 6 blocks**: this is the plan's single most likely failure point (R5). Mark `[BLOCKED]`,
  record the failing induction case, and re-plan. Task 430 already tracks this same obligation and
  is the natural home; its disposition is decided at that point, not in advance.
- **Why no planned strategic sorry / skeleton plan**: the one candidate division point is Phase 6's
  atom-persistence obligation. It is not planned as a strategic sorry because (i) a concrete route
  exists — the in-file STOP-gate's own recommendation (a), whose stated blocker (the wave-ordering
  inversion) Phases 2-3 remove; (ii) a follow-up task for exactly this obligation already exists
  (430), so emitting a new one would duplicate live work the research explicitly warns against; and
  (iii) leaving a sorry at this point would leave both public completeness theorems `sorryAx`-tainted,
  which is the specific outcome this task exists to eliminate. A bounded attempt with a hard stop is
  the better trade.
- **R1 fires (`Measure.lean` moved or `sum_map_le_length_mul` renamed)**: do not adapt in place.
  Mark the current phase `[BLOCKED]`, record the new SHA and what changed, and escalate — the fix
  belongs with whoever moved it.
- **Full revert**: all `Cslib/` changes in this plan are confined to five files under
  `Cslib/Logics/Propositional/Tableau/`. Reverting the phase commits in reverse order restores the
  4-sorry baseline exactly; no other subsystem depends on the new predicates.
