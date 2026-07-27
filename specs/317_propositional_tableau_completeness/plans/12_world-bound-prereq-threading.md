# Implementation Plan: Propositional/Intuitionistic Tableau Completeness — World-Bound Prerequisite, Invariant Threading, and Bridge Assembly

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Status**: [NOT STARTED]
- **Effort**: 24 hours total (2.5 hours already landed in Phases 0-1; ~21.5 hours remaining)
- **Dependencies**: 552 (completed — landed the `.pos, .imp` branching arm)
- **Research Inputs**:
  - handoffs/11_phase0-spike-decisions.md (Phase 0 verification spike — both spike questions CONFIRMED)
  - handoffs/11_phase2-blocker-findings.md (Phase 2 blocker — the two obstacles this revision is built on)
  - summaries/11_tableau-completeness-assembly-summary.md (v11 dispatch outcome, CI baseline finding)
  - reports/11_team-research.md (synthesis, primary input to v11)
  - reports/11_teammate-a-findings.md (primary route, exact Lean signatures)
  - reports/11_teammate-b-findings.md (bridging-lemma idiom, prior art, Mathlib absence)
  - reports/11_teammate-c-findings.md (claim audit, territory risk, conformance gap)
  - reports/11_teammate-d-findings.md (downstream consumers, task disposition)
- **Artifacts**: plans/12_world-bound-prereq-threading.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-compliance.md
  - .claude/rules/lean4.md
- **Type**: cslib

## Overview

Four bare tactic-level `sorry`s remain under `Cslib/Logics/Propositional/Tableau/`. Verified at
revision time (2026-07-26, strict scan): `Intuitionistic/Scheme.lean:599`,
`Intuitionistic/Scheme.lean:1517`, `Intuitionistic/Completeness.lean:133`,
`Minimal/Completeness.lean:125`. Repo-wide strict scan: 29 hits. This plan closes all four.

This plan supersedes v11 (`plans/11_tableau-completeness-assembly.md`) rather than restarting it.
v11's Phases 0 and 1 completed green and are committed; they are carried here verbatim as
`[COMPLETED]` and must not be re-planned or re-executed. v11's Phase 2 is `[BLOCKED]`, and the
blocker is a genuine scope correction, not a dispatch failure.

**What v11 got wrong, concretely.** The hard-mode dispatch that executed v11 verified two
obstacles v11's sizing did not anticipate, plus one structural claim that turned out to be false:

1. **Forward reference (mechanical but large).** `intExpandBranches_openBranch_sat` is declared at
   `Scheme.lean:1499` (docstring from `:1478`), but its signature must reference `intUniverse`
   (`:2056`) and `intExpMeasure` (`:2382`). Adding them produces real
   `Function expected at intUniverse` / `Function expected at intExpMeasure` build errors — not a
   typo. The fix is relocating the self-contained universe/measure/persistence block (`:1959-3019`,
   ~1,060 lines of already-landed sorry-free Preserved-Assets code) to before `:1478`.

2. **A missing load-bearing lemma (the real blocker).** Maintaining the universe-membership
   invariant across the world-creating `F(φ→ψ)` step requires
   `intApplyRuleFull_outputs_subset`'s hypothesis `(hnw : nextWorld ≤ φ0.complexity + 1)`
   (`Scheme.lean:2291` region). Nothing in the file establishes that bound on the running
   `nextWorld` counter. The file documents this in **three** places as a known, unbuilt
   continuation named `intExpandBranches_world_bound`: `Scheme.lean:2025-2038` (docstring above
   `intSubfmls_impCount_le`), `:2052-2055` (above `intUniverse`), and `:2536-2538` (on
   `intExpMeasure_step_lt`, which explicitly contrasts its own weaker `hb` with "a distinct,
   harder distinct-label-count fact this lemma does not need"). Building it needs a genuinely new
   argument: an injection from "worlds created during expansion" into "distinct `.imp`-node
   positions of φ0's parse tree", with the already-proven `intSubfmls_impCount_le` (`:2035`) as the
   codomain-size ingredient, threaded as a fresh invariant through the same recursion.

3. **v11's Phase 2 / Phase 3 split is not realizable.**
   `induction fuel generalizing branches expandedSets nextWorlds edgeSets hAC hLen0 hACC`
   automatically reverts any context hypothesis mentioning a generalized variable. The moment
   `hUniv`/`hMeasure` enter the signature, every existing `ih`/`ih_inner` call site immediately
   demands their proofs. "Add the hypotheses" (v11 P2) and "maintain them" (v11 P3) are one
   indivisible unit at the Lean level. They are merged here.

**The positive finding, preserved.** v11 flagged its Phase 3 zero case as risk R4, "the largest
single unit". It is not. `intExpMeasure`'s summand is `3 ^ intWork ...`, which is `≥ 1`
unconditionally, so `intExpMeasure U branches expandedSets ≤ 0` (fuel = 0) forces `branches = []`
directly — a nonempty zipped list sums to ≥ 1. And `intExpandBranches [] ... 0 ...` is
`branches.findSome? (...)` on `[]` (`Expansion.lean:369-373`), which is `none`, i.e. `.closed`,
never `.openBranch`. So the zero case closes by short contradiction, **not** by the elaborate
"measure = 0 ⟹ `e ⊇ intUniverse φ0` ⟹ every compound formula on `b` already in `e`" argument v11's
Phase 3 text describes. R4 is downgraded accordingly, and the contradiction route is written into
the phase so the implementer does not rediscover it.

**Unchanged from v11, and still true.** The "REMAINING SCOPE IS ASSEMBLY ONLY" framing in the task
description is refuted and must not be carried into implementation. Item (1) (`sat_timp`) genuinely
was mechanical — it landed in Phase 1. Items (2) and (3) need the invariant plumbing that Phases
2-5 build. Item (4) needs a further obligation the four-item list never names (Phases 8-9).
Equally, this is not open research: three of the four obligations have verified concrete routes,
the mandated parametric abstraction (`IntMinScheme`) already exists and needs no refactor budget,
and both Phase 0 spike questions came back exactly as predicted.

### The `tableau_complete` premise finding (confirmed by the Phase 0 spike)

`tableau_complete`'s premise (`Scheme.lean:1946-1948`) is

```lean
(hvalid : ∀ (edges : IEdges) (b : IBranch Atom),
  @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ)
```

quantified over **arbitrary** `edges` and `b`. Discharging it from `IValid φ` requires upward
closure of `intExtractValuation b` along `intAccessPreorder edges` for an arbitrary pair, which is
false (take `b = [T(p)@0]`, `edges = [(0,1)]`). The two bridge sorries as currently posed are
therefore **not provable at their current statement**, independent of any persistence machinery.
The Phase 0 spike confirmed this against live goal state at both bridge sites. The premise must
first be narrowed to carry the persistence witness for the pair that `openBranch_countermodel`
actually produces. This is Phase 9, and it is why item (4) is a two-phase job. The narrowing makes
`tableau_complete` strictly stronger, so the stable public contract
(`intuitionisticTableau_complete`, `minimalTableau_complete`, the `Decidable` instances) stays
byte-stable.

### Research Integration

Reports newly integrated in this revision (v12):

| New input | What this plan takes from it |
|---|---|
| `handoffs/11_phase0-spike-decisions.md` | Both spike verdicts CONFIRMED: (a) forward-only disjunction elimination closes the T-imp case given `sat_timp` + `ITimpAccess`, no converse IH; (b) the `hvalid` premise narrowing is required, not optional. R1 pinned SHA matched; R8 retired (single `IBranchSaturation` construction site confirmed by grep). |
| `handoffs/11_phase2-blocker-findings.md` | The two new prerequisite phases (relocation, world bound); the Phase 2/3 non-separability finding; the confirmed-easy zero-case contradiction route; the three in-file citations documenting `intExpandBranches_world_bound` as a known continuation. |
| `summaries/11_tableau-completeness-assembly-summary.md` | Phase 0/1 completion evidence and commits; the pre-existing unrelated full-`lake build` breakage in `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` (task 554, commit `88b198bf`) that makes scoped verification the working criterion. |

Carried forward from v11 (integrated in plan version 11, unchanged here):
`reports/11_team-research.md`, `reports/11_teammate-{a,b,c,d}-findings.md`,
`reports/10_wave-a-atomic-derisk.md` (reference only).

### Preserved Assets

The following work is complete and must not regress. All entries verified sorry-free at HEAD
during planning. The last two rows are new in v12 — they are Phases 0 and 1 of this plan.

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| `IntMinScheme` structure + `intScheme`/`minScheme` instances (the mandated parametric abstraction — already built) | `Intuitionistic/Scheme.lean:118, :159, :208` | [COMPLETED] | 2026-07-26 |
| Parametric `truthLemma` over `S : IntMinScheme Atom` (5 of 6 connective cases closed) | `Intuitionistic/Scheme.lean:562-640` | [COMPLETED] | 2026-07-26 |
| `intAccessPreorder` + `intAccessPreorder_le_of_isAccessible` (edge-reachability `Preorder Nat`) — v6 Phase 1 | `Intuitionistic/Scheme.lean:309-340` | [COMPLETED] | commit `a1883c4e` |
| `IFimpAccess` companion predicate + `IExpandedAccessConsistent`/`IExpandedAccessConsistent_sat` extraction — v6 Phases 1-4 | `Intuitionistic/Scheme.lean:442, :1461` | [COMPLETED] | 2026-07-26 |
| `IExpandedConsistent_sat` (sole `IBranchSaturation` construction site) + the saturation fields | `Intuitionistic/Scheme.lean:74-115, :910` | [COMPLETED] | 2026-07-26 |
| `IAllConsistent`/`IExpandedConsistent`/`ILabelBound` invariant + monotonicity combinators; `none`-case closed | `Intuitionistic/Scheme.lean` | [COMPLETED] | plan 03 P1, commit `26508fe9` |
| Fuel raised to `intFuel φ` + downstream caller audit — v6 Phase 5 | `Expansion.lean` and callers | [COMPLETED] | v6 P5 |
| `intSubfmls`/`intUniverse`/`intWork` + `intUniverse_length_le` (:2065), `intSubfmls_impCount_le` (:2035) — v6 Phase 6 | `Intuitionistic/Scheme.lean` | [COMPLETED] | v6 P6 |
| Branch-universe containment infrastructure: `mem_intUniverse_of` (:2152), `intUniverse_mem_formula` (:2171)/`_mem_label` (:2180), `intTImpRule_outputs_subset` (:2195), `applyAllTImpRules_subset` (:2223), `intApplyRuleFull_outputs_subset` (:2291) — v6 Phase 6.2 | `Intuitionistic/Scheme.lean` | [COMPLETED] | commits `bb4ffa3c`, `015f81c1` |
| `intExpMeasure_step_lt` (:2540) + `intExpMeasure_step_lt_branch` (:2608) — v6 Phase 7 | `Intuitionistic/Scheme.lean` | [COMPLETED] | v6 P7 |
| `intExpMeasure_init_le_fuel` (:2742) — v6 Phase 8 | `Intuitionistic/Scheme.lean` | [COMPLETED] | v6 P8 |
| `applyPersistenceFixpoint_genuine_of_count_le_fuel` (:2931) + supports `applyAllTImpRules_copy_notMem` (:2796), `intTImpRule_output_notMem` (:2825), `applyAllTImpRules_count_drop` (:2850) | `Intuitionistic/Scheme.lean` | [COMPLETED] | v6 P10 dispatch |
| Option-A dedup `intFImpReuseWitness?` (sound) | `Intuitionistic/Expansion.lean` | [COMPLETED] | commit `4202d1df` |
| Calculus soundness (`intRule_preserves_sat` incl. the `.pos, .imp` case) | `Intuitionistic/Soundness.lean` | [COMPLETED] | task 316/552 — READ-ONLY territory |
| `.pos, .imp` branching arm `[[F(φ)@l],[T(ψ)@l]]` | `Intuitionistic/Rules.lean:274-275` | [COMPLETED] | task 552, commit `db48c4c2` |
| 43-row conformance guard (24 temporal + 19 `intuitionisticTableau` rows) | `CslibTests/TableauConformance.lean` | [COMPLETED] | 2026-07-26 |
| `NegriVonPlato2001` (:913), `Fitting1983` (:211), `Fitting1969` (:204) bib keys | `references.bib` | [COMPLETED] | 2026-07-26 — v6 Phase 11 needs no work |
| **Phase 0 verification spike decision record** (R1 SHA match, R8 single-site confirmation, spike verdicts (a) and (b) both CONFIRMED against live goal state) | `handoffs/11_phase0-spike-decisions.md` | [COMPLETED] | commit `82a578b2` |
| **`sat_timp` field on `IBranchSaturation` (:105) + mechanical discharge at `IExpandedConsistent_sat`** (six fields now; all consumers rebuild unchanged) | `Intuitionistic/Scheme.lean:105, :910` | [COMPLETED] | commit `774035dd` |

**Superseded (do not resume)**: v6 Phase 9 `[BLOCKED]`, v6 Phase 10 `[BLOCKED]`, v11 Phases 2-7.
v11 Phases 2 and 3 are replaced by Phases 2-5 here (relocation + world bound + merged threading);
v11 Phases 4-7 are carried forward substantively as Phases 6-9. v6 Phase 11 (bib keys) is
unnecessary: the keys are already present.

## Goals & Non-Goals

**Goals**:
- Close all four bare sorries in `Cslib/Logics/Propositional/Tableau/`, reaching a sorry-free
  intuitionistic and minimal tableau completeness development.
- Relocate the universe/measure/persistence block so the invariant can be *stated* on
  `intExpandBranches_openBranch_sat` at all (Phase 2).
- Build `intExpandBranches_world_bound` — the `nextWorld ≤ φ0.complexity + 1` bound the file
  documents in three places as an unbuilt continuation, and the load-bearing prerequisite for
  everything downstream (Phases 3-4).
- Thread a `φ0`-universe-membership + measure-bound invariant through
  `intExpandBranches_openBranch_sat` as one indivisible unit, wiring the three currently-dead
  `intExpMeasure_*` lemmas and `applyPersistenceFixpoint_genuine_of_count_le_fuel` into live use
  (Phases 5-6).
- Deliver the two new companion predicates (`ITimpAccess`, `IAtomPersist`) from the same site that
  already delivers `IFimpAccess`, and consume them in `truthLemma` and in the two validity bridges.
- Narrow `tableau_complete`'s `hvalid` premise so the bridges are provable, keeping every public
  statement byte-stable.
- Repair the stale docstring block near `Scheme.lean:3020` (and the now-falsified `sat_timp`
  STOP-gate notes at `:492-540`). **This is an explicit task requirement and was never reached in
  v11 — it is mandatory, not optional cleanup.**
- Keep CI green: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`; the 43-row conformance guard stays green. (See the CI baseline caveat under
  Testing & Validation.)

**Non-Goals**:
- Any parametric refactor of Int/Min. `IntMinScheme` already exists; both `Completeness.lean`
  files are already thin ~130-line corollaries. Zero budget.
- Any change to `Rules.lean` or `Expansion.lean` calculus rules. The stale block's "new calculus
  rule needed" recommendation is wrong.
- Any edit to `Cslib/Foundations/**` (read-only dependency) or `Intuitionistic/Soundness.lean` /
  `Minimal/Soundness.lean` (task 316 territory).
- Any Mathlib search for Kripke/persistence/fuel/fixpoint-sufficiency machinery — verified absent.
- Redefining `IForces`, `IValid`, `MValid`, or `iforces_persistence` (v6 Route (b), rejected).
- Fixing the unrelated pre-existing `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`
  breakage. Out of territory; owned by whoever owns task 554.
- Tasks 430, 456, 375, 413. Task 430's disposition is decided **after** this task lands.
- Adding `minimalTableau` rows to the conformance guard (residual risk R2, not fixed here).
- Any *semantic* change to code moved by Phase 2. That phase is pure code motion.

## Risks & Mitigations

| ID | Risk | Impact | Likelihood | Mitigation |
|----|------|--------|------------|------------|
| R1 | **Pinned read-only dependency breaks.** `Scheme.lean:10` imports `Cslib.Foundations.Logic.Tableau.Measure` and consumes `sum_map_le_length_mul`. A concurrent session (task 557, modal-tableau refactor/Boneyard programme) is restructuring exactly this class of shared abstraction. This task never writes there, but a move/rename/archive breaks its build. | H | M | **Pinned-SHA pre-phase check, not coordination hope.** Pinned SHA, re-verified at v12 revision time (2026-07-26): `facba1f42469805b666d6eca78156ac4d7be5c71`. At the start of every phase run `git log -1 --format=%H -- Cslib/Foundations/Logic/Tableau/Measure.lean` and compare. On mismatch: do not start the phase; re-verify `sum_map_le_length_mul` still exists with the same signature (`lean_hover_info`), record the new SHA in the phase's Started line, and only then proceed. If the lemma or file is gone, mark the phase `[BLOCKED]` and hand off — do not attempt an in-place substitute. |
| R2 | **Minimal calculus has zero executable regression protection.** `CslibTests/TableauConformance.lean` has 43 rows, of which **zero** are `minimalTableau`. This task closes `Minimal/Completeness.lean:125`, so a Minimal-side regression is invisible to the guard the acceptance criteria rely on. | M | M | Compensate inside this task rather than expanding scope: every phase touching the Minimal side must run `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness` **and** `... Minimal.DecisionProcedure` scoped-green, and Phase 9 must `#print axioms Cslib.Logic.PL.minimalTableau_complete` and record the axiom set in the summary. Recommend (do not implement) a follow-up adding `minimalTableau` conformance rows; name it in the completion summary. |
| R3 | **Narrowing `tableau_complete`'s `hvalid` premise ripples into `DecisionProcedure.lean`.** | M | M | Adding a hypothesis to `hvalid`'s binder makes the premise weaker and `tableau_complete` stronger, so existing callers get easier goals, not harder ones. Phase 9 must nonetheless scoped-build both `DecisionProcedure` modules and confirm `intuitionisticTableau_complete` / `minimalTableau_complete` / `instDecidableIValid` statements are byte-identical (`git diff` shows only proof-body changes in those declarations). |
| R4 | **~~Phase 3's zero-case measure argument is the largest single unit.~~ DOWNGRADED (v12).** The fuel=0 case is *easy*. Justification, verified during the v11 Phase 2 dispatch and recorded in `handoffs/11_phase2-blocker-findings.md`: `intExpMeasure`'s summand is `3 ^ intWork ...`, which is `≥ 1` unconditionally, so `intExpMeasure U branches expandedSets ≤ 0` forces `branches = []`; and `intExpandBranches [] ... 0 ...` (`Expansion.lean:369-373`) is `findSome?` on `[]`, hence `.closed`, never `.openBranch`. The case closes by short contradiction. The elaborate "measure = 0 ⟹ `e ⊇ intUniverse φ0`" route v11 described is **not** needed. | L | L | Write the contradiction route directly into Phase 5's task list (done) so the implementer does not re-derive it. No dedicated dispatch, no bounded-attempt budget, no phase split for the zero case. The real difficulty moved *earlier*, to R10/R11. |
| R10 | **NEW, HIGH: `intExpandBranches_world_bound` may be genuinely hard or open.** The file documents it in three places (`:2025-2038`, `:2052-2055`, `:2536-2538`) as an unbuilt continuation, and `intExpMeasure_step_lt`'s own docstring calls it "a distinct, **harder** distinct-label-count fact this lemma does not need" — i.e. the measure lemmas were deliberately engineered *around* it. It needs a new injection argument (worlds created ↪ distinct `.imp`-node positions of φ0), threaded as a fresh invariant through the same recursion. Everything from Phase 5 onward depends on it. | H | M | Split across Phases 3 and 4 with a hard commit boundary between them (accounting invariant + local step facts first; threading and the conclusion second), so a stall in the threading half does not lose the accounting half. Both phases have explicit stopping conditions. `intSubfmls_impCount_le` (`:2035`) is already proven and is the codomain-size ingredient — do not re-derive it. If Phase 3 or 4 stalls, mark `[BLOCKED]` with the exact resisting goal and re-plan; do **not** introduce a `sorry` and do **not** weaken the bound to something vacuous. Note there is a legitimate alternative worth 30 minutes of Phase 3's budget before committing to the injection: an invariant shape for Phase 5 that avoids needing `intApplyRuleFull_outputs_subset`'s `hnw` at all (e.g. carrying a per-branch label-set bound directly). If such a shape is found and verified against live goal state, Phases 3-4 collapse and Phase 5 absorbs the difference — record the decision in a handoff either way. |
| R11 | **NEW, MEDIUM-HIGH: the Phase 2 block relocation is ~1,060 lines of code motion in a 3,045-line file with live concurrent writers.** A botched move (dropped `omit` lines, split `section`/`variable` scope, reordered mutually-referencing private lemmas) breaks already-landed sorry-free Preserved-Assets code. | H | L | Pure code motion, no proof changes — so the exit criterion is exact: a scoped `lake build` of `Intuitionistic.Scheme` green, plus `git diff --stat` showing the *only* change is relocation (line counts added ≈ removed for the moved block). Before moving, verify the block is genuinely self-contained by grepping every identifier it references against the `:1478-1958` region; the v11 handoff asserts self-containment but that assertion must be re-checked, not assumed. Move the block **whole** (`:1959` through the end of `applyPersistenceFixpoint_genuine_of_count_le_fuel` at `:3019`), not piecewise — the persistence sub-block at `:2779-3019` is needed inside `intExpandBranches_openBranch_sat`'s proof by Phase 6, so leaving it behind only defers the same move. Commit immediately at green, before any other phase starts. |
| R12 | **NEW, LOW severity / certain: the full `lake build` baseline is already red for unrelated reasons.** `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` fails with a missing-cases error (`NestedProof.cut (InputCtx.mk _ _ _)`), committed by task 554 (`88b198bf`, 2026-07-26). Verified committed, not a concurrent-session working-tree artifact. This transitively fails `lake exe checkInitImports` too. | L | Certain | **State it, do not chase it.** A future implementer must not misattribute this failure to task 317. Until it clears, scoped-module verification is the working criterion (see Testing & Validation). Re-check with `git log -1 -- Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` at the start of Phase 9; if it is fixed, run the full gate as written. If it is still red at Phase 9, run every gate that *can* run scoped, record the unrelated failure explicitly in the summary, and do not mark the task complete on the strength of a full-build pass that never happened. |
| R5 | **Phase 8's atom-persistence induction may be genuinely open-ended.** The in-file STOP-gate author (`Scheme.lean:442-491`) states it is "not completable from completeness-side machinery alone" as of the pre-invariant design, and two research teammates independently flagged item (4) as under-scoped. | H | M | The STOP-gate's own recommendation (a) (`Scheme.lean:486-490`) is the route: state persistence as a predicate threaded alongside `sat_timp` and discharge it once `measure ≤ fuel` is available — which Phases 2-5 make available, removing the wave-ordering inversion the STOP-gate describes. Phase 8 gets an explicit stopping condition (below). If it stops, the phase is `[BLOCKED]` with the exact goal, this plan is re-planned, and task 430 (whose own falsification spike already identifies this same obligation) is the natural home. **No strategic sorry is planned for this division point** — see Rollback/Contingency for why. |
| R6 | **Context overflow on large recursive proofs.** Prior dispatches on this task overflowed (v6 R6, observed; v11 dispatch also ran tight). | H | H | Scoped + grepped builds only; `offset`/`limit` windowed reads — never a whole-file read of `Scheme.lean` (3,045 lines); prefer `lean_multi_attempt` over repeated `lean_goal` dumps; commit at every green sub-step; stop and write a sharp handoff the instant context tightens. A committed green partial is success. Phase 2's relocation is deliberately its own dispatch for exactly this reason. |
| R7 | **Concurrent writers on `Scheme.lean`.** Multiple live orchestrator sessions exist in this repo. | M | H | SINGLE-WRITER-PER-FILE. Every phase runs `git log -1 -- <target file>` plus a scoped green build before its first edit. The wave table below is deliberately fully sequential for this reason. Never `git add -A`; commit only the files the phase touched. |
| R8 | ~~Adding a field to `IBranchSaturation` disturbs `Soundness.lean`.~~ **RETIRED (v12).** Phase 0's grep confirmed exactly one construction site (`IExpandedConsistent_sat`, `Scheme.lean:910`); Phase 1 landed the field and all consumers rebuilt unchanged. | -- | -- | No action. Historical record only. |
| R9 | ~~Spike answer (b) comes back "no extra obligation needed."~~ **RETIRED (v12).** Phase 0 answered (b) **yes**, confirmed against live goal state at both bridge sites. Phases 8 and 9 stay separate. | -- | -- | No action. Historical record only. |

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from this task's actual history (v6 Phases
9/10 `[BLOCKED]`, the v11 Phase 2 blocker, the v5/v6 postmortem list, and the 2026-07-26 research),
not from generic guidance. **Carried forward from v11 and strengthened** — rules 13-15 are new.

**Do NOT**:

1. **Do NOT treat "sorry-free" as "usable."** This task's central failure mode. Three
   `intExpMeasure_*` lemmas and `applyPersistenceFixpoint_genuine_of_count_le_fuel` are all
   sorry-free with **zero call sites**, because their hypotheses cannot be supplied where they are
   needed. Before claiming any lemma closes an obligation, check its call sites and confirm every
   hypothesis is derivable at the intended use point.
2. **Do NOT resolve contradictory in-file docstrings by judgment.** Use `git blame` ordering.
   `Scheme.lean:495` ("Gap 2 RESOLVED", commit `db48c4c2`, 2026-07-24 23:51) postdates the
   `~:3020` block ("determinacy remains BLOCKED", commit `a0a16c4b`, 2026-07-24 08:26) by fifteen
   hours, and is the commit that landed the branching arm the earlier block says is missing. The
   `~:3020` block is the stale one.
3. **Do NOT budget for a parametric refactor.** `IntMinScheme` (`Scheme.lean:118`, instances :159
   and :208) already exists; `truthLemma`/`openBranch_countermodel`/`tableau_complete` are already
   stated once against it; both `Completeness.lean` files are already thin corollaries. Read the
   description's "rather than duplicating" as "keep it this way."
4. **Do NOT propose or implement a new calculus rule.** The stale block's recommendation of a
   `Rules.lean`/`Expansion.lean` calculus-level change is wrong both by staleness and technically:
   the T-imp case needs no converse IH (Phase 0 spike question (a), CONFIRMED).
5. **Do NOT search Mathlib for Kripke semantics, intuitionistic persistence, tableau calculi, or
   fuel/fixpoint-sufficiency machinery.** Verified absent by exhaustive rate-limited search.
   Heyting algebras exist and connect to nothing here. The reusable pieces
   (`Relation.ReflTransGen`, `intAccessPreorder`) are already in-repo and in use.
6. **Do NOT run a raw full `lake build`** during phase work. Scoped and grepped only, e.g.
   `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"`.
   A full `lake build` belongs only in the final CI gate. Another session is actively building in
   this repo, and the full build is red for unrelated reasons anyway (R12).
7. **Do NOT read `Scheme.lean` whole.** Windowed `offset`/`limit` reads only (R6). This applies
   to Phase 2's relocation as well: use `sed`/`awk` range extraction and `git diff --stat`
   verification, not a whole-file Read.
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
13. **NEW: Do NOT mix code motion with proof changes in Phase 2.** The relocation is pure motion.
    If a moved declaration needs *any* edit to compile, that is a signal the block was not
    self-contained — stop, record it, and re-scope. A relocation commit whose diff contains proof
    text changes is not verifiable as safe.
14. **NEW: Do NOT re-split the merged threading phase (Phase 5) back into "add hypotheses" and
    "maintain hypotheses."** The v11 dispatch verified they are not separable: `induction fuel
    generalizing ...` reverts any context hypothesis mentioning a generalized variable, so every
    `ih`/`ih_inner` call site demands the new proofs the moment the hypotheses exist. Attempting a
    partial landing here produces an uncompilable intermediate state, not a green commit.
15. **NEW: Do NOT report a task-level completion on the strength of a full `lake build` that did
    not run.** R12's unrelated breakage makes the full build red. Scoped verification is the
    working criterion, and the summary must say so explicitly rather than implying full CI passed.

**MUST preserve**:

- Every row of the Preserved Assets table above, unmodified and sorry-free — including the two new
  v12 rows (Phase 0 decision record, Phase 1 `sat_timp` field).
- The full two-direction `truthLemma` (both the T- and F-directions of every connective case).
- The literal `sat_fimp` field (no reformulation) and the landed `sat_timp` field (no
  reformulation — it is committed and discharged).
- The Option-A dedup `intFImpReuseWitness?` (sound; do not revert).
- A green scoped build at every commit boundary. The four inventory sorries persist only until
  their owning phase closes them; no phase may add a new one.
- The 43-row conformance guard green.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):

- **`sat_timp` is the reflexive, same-label field.** Landed in Phase 1 (`Scheme.lean:105`,
  commit `774035dd`). Not re-openable.
- **The accessible-world lift is delivered as a companion predicate `ITimpAccess edges b`**, not as
  a field, mirroring the already-landed `IFimpAccess edges b` (`Scheme.lean:442`) and delivered
  from the same site. Same for atom persistence (`IAtomPersist edges b`, Phase 8).
- **Frame = edge reachability** (`intAccessPreorder`), not numeric `≤`. Route (b) (redefining
  `IForces`) stays rejected.
- **Fuel stays raised** to `intFuel φ`; the measure is the counting-against-fixed-universe measure.
- **The two validity bridges are one parametric lemma** over `S : IntMinScheme Atom`, instantiated
  at `intScheme` (where the `modelBot` obligation is vacuous — `fun _ => False`) and `minScheme`
  (where it is real). Discharged ONCE, parametrically.
- **The T-imp case closes by forward-only disjunction elimination, no converse IH.** Phase 0 spike
  question (a), CONFIRMED against live goal state.
- **The `hvalid` premise narrowing is required.** Phase 0 spike question (b), CONFIRMED.
- **The fuel=0 zero case closes by the `3^n ≥ 1` contradiction** (R4), not the universe-containment
  route.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2 | 1 |
| 4 | 3 | 2 |
| 5 | 4 | 3 |
| 6 | 5 | 4 |
| 7 | 6 | 5 |
| 8 | 7 | 6 |
| 9 | 8 | 5 |
| 10 | 9 | 7, 8 |

Phases within the same wave can execute in parallel.

**Parallelism declaration (explicit, per H7 territory contract)**: there is **no** exploitable
parallelism in this plan, and the fully-sequential wave table is a deliberate result rather than an
oversight. Phases 1-8 all write `Intuitionistic/Scheme.lean`, and R7 (concurrent writers, observed
live in this repo) forbids two writers on one file. Phases 7 and 8 have *logically* disjoint
dependency sets (7 needs 6; 8 needs only 5) and could in principle run concurrently, but both write
`Scheme.lean`, so they are serialized into separate waves. Phase 9 is the only phase that writes
elsewhere (`Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`, both
`DecisionProcedure.lean` docstrings) but it depends on both 7 and 8, so it cannot be lifted
earlier. Territory contract: **one `Scheme.lean` writer at a time, for the whole plan.**

### Phase 0: Verification spike — record the two load-bearing decisions [COMPLETED]

- **Goal:** Answer two questions against live Lean goal state before any phase boundary downstream
  is treated as fixed, and record the answers as a durable decision record.
- **Outcome (do not re-execute):** Both questions came back CONFIRMED.
  - R1 pinned-SHA check: `facba1f42469805b666d6eca78156ac4d7be5c71`, matching. No mismatch.
  - Sorry re-grep: exactly 4 hits in the task tree; 29 repo-wide. Matched the baseline.
  - R8: `grep -rn "IBranchSaturation" Cslib/` — exactly one construction site
    (`IExpandedConsistent_sat`). R8 retired.
  - **Question (a) — CONFIRMED.** `lean_goal` at the T-imp case recorded
    `⊢ ∀ (w' : ℕ), w ≤ w' → IForces val w' φ' → IForces val w' ψ'`. Given `sat_timp` (reflexive, at
    `w'`) and `ITimpAccess`, the case closes by: obtain the copy at `w'` from `ITimpAccess`;
    `hsat.sat_timp` at `w'` gives `F(φ')@w' ∈ b ∨ T(ψ')@w' ∈ b`; the `F(φ')@w'` arm is the
    contrapositive of `ih_φ'`'s F-direction against the given `IForces val w' φ'`; the `T(ψ')@w'`
    arm is `ih_ψ'`'s T-direction directly. **No converse IH.**
  - **Question (b) — CONFIRMED.** `tableau_complete`'s `hvalid` is quantified over arbitrary
    `edges`/`b`; both bridges are `intro edges _b; sorry` against that premise, and `IValid φ` /
    `MValid φ` cannot supply it. The Phase 9 premise narrowing is required, not optional.
- **Evidence:** commit `82a578b2`; decision record at
  `specs/317_propositional_tableau_completeness/handoffs/11_phase0-spike-decisions.md`.
- **Timing:** 1 hour (actual)
- **Depends on:** none
- **Completed:** 2026-07-26

### Phase 1: `sat_timp` field on `IBranchSaturation` + mechanical discharge [COMPLETED]

- **Goal:** Add the reflexive `sat_timp` field and discharge it at `IExpandedConsistent_sat`, the
  sole construction site, leaving the file scoped-green.
- **Outcome (do not re-execute):** `sat_timp` landed at `Scheme.lean:105` (after `sat_fimp`), with
  the mechanical discharge at `IExpandedConsistent_sat` (`Scheme.lean:910`) using the same
  `compound_sat`/`intStepBranch_none_compound_mem` pattern the five existing fields use, against
  `sfSatisfied`'s already-landed `.pos, .imp` clause. `IBranchSaturation` now has six fields;
  every existing consumer rebuilt unchanged since the field is additive and discharged at the sole
  site. Scoped builds of `Intuitionistic.Scheme`, `Intuitionistic.Completeness`, and
  `Minimal.Completeness` all green. Sorry count unchanged at 4, as scoped — this phase closes none.
- **Evidence:** commit `774035dd` ("task 317 phase 1: add sat_timp field to IBranchSaturation and
  discharge mechanically").
- **Timing:** 1.5 hours (actual)
- **Depends on:** 0
- **Completed:** 2026-07-26

### Phase 2: Relocate the universe/measure/persistence block before `intExpandBranches_openBranch_sat` [NOT STARTED]

- **Goal:** Make the Phase 5 invariant *statable* at all. Pure code motion — no proof changes, no
  statement changes, no new declarations. This phase closes no sorry and adds no mathematics; its
  entire value is removing the forward reference verified in
  `handoffs/11_phase2-blocker-findings.md`.
- **The block to move** (line numbers verified at v12 revision time; re-grep before editing, they
  drift): `Scheme.lean:1959` (the `/-! ## Fixed Finite Universe and Counting Work` section header)
  through `:3019` (the last line of `applyPersistenceFixpoint_genuine_of_count_le_fuel`) — roughly
  1,060 lines. **Destination**: immediately before `:1478`, the start of
  `intExpandBranches_openBranch_sat`'s docstring. This places the whole block ahead of
  `intExpandBranches_openBranch_sat` (`:1499`), `openBranch_countermodel` (`:1890`), and
  `tableau_complete` (`:1946`), all three of which need it.
- **Tasks:**
  - [ ] Pinned-SHA check (R1) + `git log -1 -- Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (R7).
  - [ ] Re-grep the current line numbers of the four anchors: the section header, the end of
        `applyPersistenceFixpoint_genuine_of_count_le_fuel`, `intExpandBranches_openBranch_sat`'s
        docstring start, and the trailing `/-! ### GAP 2 investigation` block.
  - [ ] **Verify self-containment before moving** (R11 — the v11 handoff asserts it; re-check, do
        not assume). Extract the identifier set the block references and confirm none is declared
        in the `:1478-1958` region. Specifically confirm: no reference to
        `intExpandBranches_openBranch_sat`, `openBranch_countermodel`, `tableau_complete`,
        `IExpandedAccessConsistent_sat`, `IAllAccessConsistent_map`, or any `private` lemma in that
        window. If any reference exists, STOP and re-scope — the move is not a simple block move.
  - [ ] Move the block **whole**. Do not move the universe/measure part while leaving the
        persistence part (`:2779-3019`) behind: Phase 6 needs
        `applyPersistenceFixpoint_genuine_of_count_le_fuel` inside
        `intExpandBranches_openBranch_sat`'s proof, so a partial move only defers the same work.
  - [ ] Carry `omit [DecidableEq Atom] [Hashable Atom] in` / `omit [Hashable Atom] in` prefix lines
        and any `variable`/`section` scoping with their declarations. These are the most likely
        silent breakage in a block move.
  - [ ] Leave the trailing `/-! ### GAP 2 investigation ... determinacy remains BLOCKED` module-doc
        block (`~:3020-3041`) where it is, or carry it with the persistence block — either is fine;
        Phase 7 rewrites it regardless. Do not delete it here (that is Phase 7's mandatory task and
        must be a reviewable edit, not a side effect of code motion).
  - [ ] Scoped build: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"`.
  - [ ] `git diff --stat` sanity check: added ≈ removed for `Scheme.lean`; no other file touched.
        Spot-check `git diff` for any non-motion hunk (Postmortem 13).
  - [ ] Commit (scoped staging, task-scoped message) **immediately** at green — do not carry an
        uncommitted 1,000-line reorg into another phase (R7).
- **Expected output:** ~1,060 lines relocated; net new content ≈ 0.
- **Done when:** `Intuitionistic.Scheme` builds green, `intUniverse`/`intExpMeasure`/`intSubfmls`/
  `intWork` and the persistence lemmas all precede `intExpandBranches_openBranch_sat`, the strict
  sorry scan over the task tree still returns exactly 4, and `git diff` contains no proof-text
  change. **A green scoped `lake build` of the module is the whole verification** — because nothing
  but position changed, a green build is a complete correctness argument for this phase.
- **Stopping condition (R11):** if self-containment fails, or if any moved declaration needs an
  edit to compile, mark `[BLOCKED]`, record which declaration and why, and re-plan. Do not patch
  the declaration to make the move work.
- **Timing:** 2 hours
- **Depends on:** 1

### Phase 3: World-budget accounting invariant — definition and local step facts [NOT STARTED]

- **Goal:** Build the first half of `intExpandBranches_world_bound` (R10): the accounting invariant
  that makes "worlds created so far ≤ number of distinct `.imp` nodes of φ0" expressible, plus the
  per-step facts that each world-creating step consumes a fresh `.imp` position. No threading
  through the recursion yet — that is Phase 4.
- **Context (do not re-derive):** the target bound is `nextWorld ≤ φ0.complexity + 1`, needed as
  `intApplyRuleFull_outputs_subset`'s `hnw` hypothesis (`Scheme.lean:2291` region, post-relocation
  line will differ). The file documents the whole argument as a known unbuilt continuation in three
  places: `:2025-2038`, `:2052-2055`, `:2536-2538` (pre-relocation line numbers). The combinatorial
  ingredient `intSubfmls_impCount_le` (`:2035`) is **already proven** — it is the codomain-size
  bound. Do not re-prove it.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks; re-grep post-relocation line numbers.
  - [ ] **Timeboxed alternative check (30 minutes, R10):** before committing to the injection,
        check against live goal state whether a Phase 5 invariant shape exists that avoids needing
        `intApplyRuleFull_outputs_subset`'s `hnw` at all (e.g. carrying a per-branch label-set
        containment directly, rather than a numeric counter bound). If such a shape verifies,
        record the decision in a handoff and Phases 3-4 collapse into Phase 5. If not, record that
        it was checked and rejected, and proceed with the injection. Either way this decision is
        written down, not left implicit.
  - [ ] State the accounting invariant: relate the running `nextWorld` counter (and, in the list
        form, `nextWorlds`) to the `.imp`-node budget of φ0, in a shape that can be threaded
        alongside the existing `IAllConsistent`/`IAllAccessConsistent`/`ILabelBound` invariants
        through `intExpandBranches`'s recursion. Mirror `ILabelBound`'s shape — it is the closest
        already-threaded numeric invariant and its threading pattern is the one Phase 4 reuses.
  - [ ] Prove the local step facts: (i) the only rule that increments `nextWorld` is the
        world-creating `F(φ→ψ)` linear-result case in `intApplyRuleFull`; (ii) each such firing is
        associated with a distinct `.imp`-node position of φ0 (this is the injection); (iii) the
        non-world-creating cases leave the budget unchanged. Keep each as its own `private lemma`
        so Phase 4 consumes named facts rather than re-deriving them inline.
  - [ ] Connect the budget's codomain size to `intSubfmls_impCount_le`, yielding
        `(worlds created) ≤ φ0.complexity`, hence the `φ0.complexity + 1` target once the initial
        world is counted.
  - [ ] Scoped build; commit at green.
- **Expected output:** ~200-350 lines.
- **Done when:** the accounting invariant is defined, the local step facts are stated and proven
  sorry-free, the codomain connection to `intSubfmls_impCount_le` is in place, the tree still has
  exactly 4 sorries, and the scoped build is green.
- **Stopping condition (R10):** if the injection cannot be constructed within this dispatch, commit
  whatever is green, mark `[PARTIAL]`, and record the exact resisting goal plus which of the three
  local step facts failed. Do not introduce a `sorry`, do not weaken the bound to a vacuous
  statement, and do not proceed to Phase 4.
- **Timing:** 3 hours
- **Depends on:** 2

### Phase 4: Thread the world budget; conclude `intExpandBranches_world_bound` [NOT STARTED]

- **Goal:** Thread Phase 3's accounting invariant through `intExpandBranches`'s recursion and
  conclude `intExpandBranches_world_bound : nextWorld ≤ φ0.complexity + 1` at every point the
  recursion reaches. This is the load-bearing prerequisite for Phase 5 onward.
- **Note on merging:** if Phase 3's dispatch closes both the accounting and the threading in one
  run, mark this phase `[COMPLETED]` with Phase 3's evidence rather than dispatching it separately.
  The split exists to give R10 a commit boundary, not to force two runs.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks.
  - [ ] Add the budget invariant to the recursion's threaded state, following the same pattern
        `IAllConsistent`/`ILabelBound` already use. Expect the `induction fuel generalizing ...`
        revert behavior (Postmortem 14): the invariant must be re-established at *every* `ih` and
        `ih_inner` call site in the same dispatch.
  - [ ] Discharge the world-creating case using Phase 3's injection fact; discharge the
        non-world-creating cases using Phase 3's "budget unchanged" facts.
  - [ ] State and prove `intExpandBranches_world_bound` as the extractable consequence, in the form
        `intApplyRuleFull_outputs_subset`'s `hnw` hypothesis expects (`nextWorld ≤ φ0.complexity + 1`),
        so Phase 5 can apply it directly without adaptation.
  - [ ] Confirm the initial call site's budget (`nextWorlds = [1]` at `tableau_complete`) satisfies
        the invariant.
  - [ ] Scoped build; commit at green.
- **Expected output:** ~250-400 lines.
- **Done when:** `intExpandBranches_world_bound` exists sorry-free with the exact hypothesis shape
  `intApplyRuleFull_outputs_subset` needs, the tree still has exactly 4 sorries, and the scoped
  build is green.
- **Stopping condition (R10):** if the threading does not close, commit any green sub-step, mark
  `[BLOCKED]`, and record the exact resisting `ih` call site and goal. Phases 5-9 are all
  transitively blocked on this; a blocked Phase 4 triggers a re-plan, not a workaround.
- **Timing:** 3 hours
- **Depends on:** 3

### Phase 5: Universe/measure invariant — definition, threading, and fuel=0 discharge (one unit) [NOT STARTED]

- **Goal:** Give `intExpandBranches_openBranch_sat` the `φ0` parameter and the two invariant
  hypotheses it lacks, maintain them across every recursive call, establish them at the sole call
  site, and close the fuel=0 base case. Closes sorry 2 of 4 (`Scheme.lean:1517`).
- **Why this is one phase, not two (Postmortem 14):** v11 split "add the hypotheses" from "maintain
  them". The v11 dispatch verified that split is not realizable —
  `induction fuel generalizing branches expandedSets nextWorlds edgeSets hAC hLen0 hACC`
  automatically reverts any context hypothesis mentioning a generalized variable, so the moment
  `hUniv`/`hMeasure` exist in the signature, every `ih`/`ih_inner` call site immediately requires
  their proofs. There is no green intermediate state between the two halves. Do not re-split.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks; re-grep the sorry's current line number.
  - [ ] Add to `intExpandBranches_openBranch_sat` a fixed formula parameter `φ0 : Proposition Atom`,
        a universe-membership invariant `∀ b1 ∈ branches, ∀ x ∈ b1, x ∈ intUniverse φ0`, and a
        measure bound `intExpMeasure (intUniverse φ0) branches expandedSets ≤ fuel`. Propagate both
        through the internal `key`/`go` induction statement.
  - [ ] **Succ case — measure:** re-establish the bound at each recursive call using
        `intExpMeasure_step_lt` and `intExpMeasure_step_lt_branch` (both sorry-free, currently
        zero call sites — this gives them their first).
  - [ ] **Succ case — universe membership:** re-establish using `intApplyRuleFull_outputs_subset`
        and `intTImpRule_outputs_subset`. The world-creating `F(φ→ψ)` linear-result case supplies
        `intApplyRuleFull_outputs_subset`'s `hnw : nextWorld ≤ φ0.complexity + 1` from **Phase 4's
        `intExpandBranches_world_bound`** — this is the whole reason Phases 3-4 exist.
  - [ ] **Fuel=0 zero case — the confirmed-easy route (R4).** Do **not** attempt the
        "measure = 0 ⟹ `e ⊇ intUniverse φ0`" argument v11 described. Instead: `intExpMeasure`'s
        summand is `3 ^ intWork ...`, which is `≥ 1` for every branch unconditionally
        (`3 ^ n ≥ 1` for all `n`), so `intExpMeasure U branches expandedSets ≤ 0` forces
        `branches = []` — a nonempty zipped list sums to `≥ 1`. And `intExpandBranches` at fuel 0
        (`Expansion.lean:369-373`) is `branches.findSome? (...)`, which on `[]` is `none`, i.e.
        `.closed`, never `.openBranch b`. So the hypothesis `h : ... = .openBranch b` is absurd and
        the case closes by short contradiction.
  - [ ] Establish both invariants at the sole call site, `openBranch_countermodel` (invocation
        region `:1890-1944`), using `intExpMeasure_init_le_fuel` and `intUniverse`'s membership
        constructors `intUniverse_mem_formula`/`intUniverse_mem_label` — all currently dead code,
        now given their first call sites.
  - [ ] Keep the new hypotheses internal: `openBranch_countermodel`'s and `tableau_complete`'s
        conclusions must not gain a premise (Postmortem 11).
  - [ ] Scoped builds (`Intuitionistic.Scheme`, `Intuitionistic.Completeness`,
        `Minimal.Completeness`); commit at green.
- **Expected output:** ~350-500 lines.
- **Done when:** `Scheme.lean:1517`'s `sorry` is gone, the tree has exactly 3 sorries,
  `intExpMeasure_init_le_fuel`/`intExpMeasure_step_lt`/`intExpMeasure_step_lt_branch` all have call
  sites, and the scoped builds are green.
- **Stopping condition:** this phase is atomic by construction — there is no green partial between
  "hypotheses added" and "hypotheses maintained". If it does not close, `git checkout --` the
  in-progress edit back to the last green commit (as the v11 dispatch correctly did), mark
  `[BLOCKED]`, and hand off the exact resisting `ih` call site. Do not commit a broken tree and do
  not introduce a `sorry`.
- **Timing:** 5 hours
- **Depends on:** 4

### Phase 6: `ITimpAccess` copy-completeness bridge [NOT STARTED]

- **Goal:** Convert the genuine-fixpoint equality into membership at every edge-accessible world,
  and expose it from `intExpandBranches_openBranch_sat` alongside `IFimpAccess`.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks.
  - [ ] Define `ITimpAccess (edges : IEdges) (b : IBranch Atom) : Prop`, mirroring `IFimpAccess`
        (`Scheme.lean:442`):
        `∀ (φ ψ : Proposition Atom) (w w' : Nat), b.any (T(φ→ψ)@w) = true → isAccessible edges w w' = true → b.any (T(φ→ψ)@w') = true`.
  - [ ] Prove it at a genuine fixpoint by contradiction against the fixpoint equality, using the
        `if b.any (...) then none else some copy` guard idiom already established by
        `applyAllTImpRules_copy_notMem` and `intTImpRule_output_notMem`: if the copy were absent,
        one more `applyAllTImpRules` round would add it, contradicting equality.
  - [ ] Supply `applyPersistenceFixpoint_genuine_of_count_le_fuel`'s `hb` and `hfuel` from the
        Phase 5 invariant at the point `bPers` is computed, giving that lemma its first call site.
  - [ ] Widen `intExpandBranches_openBranch_sat`'s conclusion to
        `∃ edges, IBranchSaturation Atom b ∧ IFimpAccess edges b ∧ ITimpAccess edges b`, and update
        the `openBranch_countermodel` call site's `obtain`.
  - [ ] Scoped builds; commit at green.
- **Expected output:** ~120-200 lines.
- **Done when:** `ITimpAccess` is defined and delivered from the open-branch boundary,
  `applyPersistenceFixpoint_genuine_of_count_le_fuel` has a call site, the tree still has exactly 3
  sorries, and the scoped builds are green.
- **Timing:** 2 hours
- **Depends on:** 5

### Phase 7: Close `truthLemma`'s T-imp case and repair the stale docstrings [NOT STARTED]

- **Goal:** Close sorry 1 of 4 (`Scheme.lean:599`) and, in the same phase, repair every docstring
  the landed work has falsified. **The docstring repair is a MANDATORY task requirement, not
  optional cleanup** — it was scoped in v11's Phase 5 and never reached because Phase 2 blocked.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks; re-grep the sorry's current line number.
  - [ ] Add `(htimp : ITimpAccess edges b)` to `truthLemma`'s signature (`Scheme.lean:562-566`),
        alongside the existing `hfimp`, and thread it from `openBranch_countermodel`.
  - [ ] Close the T-imp case exactly as Phase 0(a) verified against live goal state: `intro _`;
        obtain the copy at `w'` from `htimp`; apply `hsat.sat_timp` at `w'` to get the disjunction;
        in the `F(φ')@w'` arm derive a contradiction with the given `IForces val w' φ'` via the
        contrapositive of `ih_φ'`'s F-direction; in the `T(ψ')@w'` arm close with `ih_ψ'`'s
        T-direction. **No converse IH.**
  - [ ] Replace the stale comment block inside the case (`Scheme.lean:585-598`) with a short note
        describing the landed proof.
  - [ ] **MANDATORY docstring repair 1**: rewrite or delete the block at `Scheme.lean:~3020-3041`
        ("GAP 2 investigation ... determinacy remains BLOCKED"; the line number moves if Phase 2
        carried it — re-grep for `GAP 2 investigation`). It is both stale (written fifteen hours
        before commit `db48c4c2` landed the branching arm) and technically wrong (it claims a
        converse IH is required, and recommends a new calculus rule). Mirror the style of the
        "Gap 2 ... RESOLVED" block at `:495`, and point at the landed `sat_timp` field and T-imp
        proof.
  - [ ] **MANDATORY docstring repair 2**: the `sat_timp` discharge STOP-gate note at
        `Scheme.lean:492-540` now asserts things Phase 1 falsified — in particular
        "`sat_timp` is NOT added as an `IBranchSaturation` field" (`:527-529`) and the deferral
        rationale at `:536-540`. Rewrite to describe what landed.
  - [ ] Re-scan `Scheme.lean` for any other docstring rendered false by Phases 1-7, in particular
        the STOP-gate at `:442-491`, the "fuel-0 base case still has a gap" note in
        `intExpandBranches_openBranch_sat`'s own docstring (`:1478-1498`, falsified by Phase 5),
        and the "`intExpMeasure` ... not yet defined" claim in the relocated section header
        (`:1959-1980`). Update them.
  - [ ] Scoped builds; commit at green.
- **Expected output:** ~150-250 lines (proof plus docstring edits).
- **Done when:** `Scheme.lean:599`'s `sorry` is gone, the tree has exactly 2 sorries (both bridges),
  no docstring in `Scheme.lean` still asserts determinacy is blocked / the T-imp case is blocked /
  `sat_timp` is not a field / the fuel-0 case has a gap, and the scoped builds are green.
- **Timing:** 2 hours
- **Depends on:** 6

### Phase 8: `IAtomPersist` upward-closure predicate and its discharge [NOT STARTED]

- **Goal:** Supply the atom-persistence obligation the task's four-item list never names: upward
  closure of `intExtractValuation b` (and, for the Minimal side, `minBranchBotForces b`) along
  `intAccessPreorder edges`, for the branch the expansion actually returns.
- **Route (settled, from the in-file STOP-gate's own recommendation (a), `Scheme.lean:486-490`):**
  state persistence as a predicate threaded alongside `sat_timp`/`ITimpAccess` and discharge it
  once `measure ≤ fuel` is available. Phases 2-5 make it available, removing the wave-ordering
  inversion the STOP-gate describes as the reason it was previously not completable.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks.
  - [ ] Define `IAtomPersist (edges : IEdges) (b : IBranch Atom) : Prop` as upward closure of the
        atom-membership test along `isAccessible edges`, mirroring `IFimpAccess`/`ITimpAccess`
        shape. State the `modelBot` analogue parametrically over `S : IntMinScheme Atom` so one
        predicate covers `intExtractValuation` and `minBranchBotForces`
        (`Minimal/Soundness.lean:169-171`, read-only).
  - [ ] Discharge it at the genuine persistence fixpoint by induction on formula complexity: the
        fixpoint (Phase 6's machinery) is the base fact for the atom case; the imp/and/or cases use
        the IH. The co-inductive dependency the STOP-gate describes (a `T(atom p)` introduced by a
        `T(φ→atom p)`-triggered `intTImpRule` firing at a later persistence round needs the
        antecedent's own persistence to have already propagated) is exactly what the genuine
        fixpoint discharges — at a fixpoint there is no "later round".
  - [ ] Extend `intExpandBranches_openBranch_sat`'s conclusion with `IAtomPersist edges b` and
        update the `openBranch_countermodel` call site.
  - [ ] Scoped builds; commit at green.
- **Expected output:** ~200-300 lines.
- **Done when:** `IAtomPersist` is defined, discharged sorry-free, and delivered from the
  open-branch boundary; the tree still has exactly 2 sorries; scoped builds green.
- **Stopping condition (R5):** this phase has a hard stop. If the induction does not close within
  the dispatch, commit whatever is green, mark `[BLOCKED]`, and record the exact resisting goal
  plus which case of the complexity induction failed. Do not introduce a sorry, do not weaken the
  statement to something vacuous, and do not proceed to Phase 9. A blocked Phase 8 triggers a
  re-plan; task 430 (whose own falsification spike identifies this same obligation) is the natural
  home for the escalation, but that disposition is not made here.
- **Timing:** 3 hours
- **Depends on:** 5

### Phase 9: Narrow `tableau_complete`'s premise and close both validity bridges [NOT STARTED]

- **Goal:** Close sorries 3 and 4 of 4 (`Intuitionistic/Completeness.lean:133`,
  `Minimal/Completeness.lean:125`) as **one parametric lemma over `S : IntMinScheme Atom`**,
  reaching a sorry-free tree. Discharging the truth-lemma/countermodel pair once, parametrically,
  is a standing task constraint — do not duplicate the argument across the Int and Min sides.
- **Tasks:**
  - [ ] Pinned-SHA + single-writer checks; re-grep both sorry line numbers.
  - [ ] R12 re-check: `git log -1 -- Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`
        and a scoped build of that module, to determine whether the full CI gate below can run
        honestly this dispatch.
  - [ ] **Premise narrowing (Phase 0 question (b), CONFIRMED required):** change
        `tableau_complete`'s `hvalid` (`Scheme.lean:1946-1948`) from `∀ edges b, IForces ...` to
        `∀ edges b, IAtomPersist edges b → (S.modelBot-persistence) → IForces ...`, and supply the
        two witnesses inside `tableau_complete`'s own proof from `openBranch_countermodel`'s
        Phase-8-widened conclusion. This makes `tableau_complete` strictly stronger; no public
        statement changes.
  - [ ] State one `private` parametric bridge over `S : IntMinScheme Atom` taking the upward-closure
        witnesses and producing the `hvalid` premise from validity, using `IValid`/`MValid`'s shape
        at `Cslib/Logics/Propositional/Semantics/Kripke.lean:145-168`.
  - [ ] Instantiate at `intScheme` in `Intuitionistic/Completeness.lean:124-133` — the `modelBot`
        obligation is vacuous, `fun _ => False` being trivially upward-closed (compare
        `mvalid_implies_ivalid`, `Kripke.lean:165-168`) — replacing the `sorry`.
  - [ ] Instantiate at `minScheme` in `Minimal/Completeness.lean:113-125` — here the `modelBot`
        obligation is real and is discharged by Phase 8's parametric `modelBot` clause — replacing
        the `sorry`.
  - [ ] Update the "Notes on sorry" docstring sections in `Intuitionistic/Completeness.lean:39-43`,
        `Minimal/Completeness.lean:43-47`, `Intuitionistic/DecisionProcedure.lean:34-59`, and
        `Minimal/DecisionProcedure.lean:20-66` — all four currently describe deferred completeness
        sorries and sorry-taint that will no longer exist.
  - [ ] **Byte-stability check (R3):** `git diff` must show only proof-body changes, never statement
        changes, in `intuitionisticTableau_complete`, `minimalTableau_complete`, and every
        `Decidable` instance. Scoped-build both `DecisionProcedure` modules.
  - [ ] **Axiom gate:** `lean_verify` / `#print axioms` on
        `Cslib.Logic.PL.intuitionisticTableau_complete` and `Cslib.Logic.PL.minimalTableau_complete`;
        expect `{propext, Classical.choice, Quot.sound}` with **no `sorryAx` and no new axiom**.
        Record both axiom sets in the summary (R2 compensation).
  - [ ] CI gate (see Testing & Validation, including the R12 caveat); commit at green.
- **Expected output:** ~200-300 lines (proof plus four docstring sections).
- **Done when:** the strict sorry scan over `Cslib/Logics/Propositional/Tableau/` returns **zero**
  hits, both public theorems print sorry-free axiom sets with no new axioms, and every CI step that
  can honestly run is green (with any R12-attributable failure explicitly recorded as unrelated).
- **Timing:** 2 hours
- **Depends on:** 7, 8

## Testing & Validation

**Standing task constraints** (apply to every phase, not just the final gate):

- [ ] **No new axioms.** `#print axioms` on any touched public declaration must show no addition
      beyond `{propext, Classical.choice, Quot.sound}`.
- [ ] **`Cslib/` bare-sorry count must go DOWN.** Measured with the strict scan below, at the same
      commit, before and after.
- [ ] **`Intuitionistic/Soundness.lean` is READ-ONLY.** So are `Minimal/Soundness.lean` and
      everything under `Cslib/Foundations/`.
- [ ] **The 43-row `CslibTests/TableauConformance.lean` guard stays green.**
- [ ] **The truth-lemma/countermodel pair is discharged ONCE, parametrically over `IntMinScheme`.**
      No Int/Min duplication of the argument.

**Sorry measurement (the acceptance criterion's operational definition).** The repo-wide
`grep -rn "sorry"` figure conflates tactic uses with prose and is **not** a usable baseline. Use
this stricter scan:

```
grep -rnE '(^[[:space:]]+sorry[[:space:]]*(--.*)?$)|((:=|by|<;>|;)[[:space:]]+sorry([[:space:]]|$))' Cslib --include=*.lean
```

- **Baseline re-verified 2026-07-26 at v12 revision time**: 29 hits repo-wide. Exactly 4 are in
  `Cslib/Logics/Propositional/Tableau/` — `Intuitionistic/Scheme.lean:599`,
  `Intuitionistic/Scheme.lean:1517`, `Intuitionistic/Completeness.lean:133`,
  `Minimal/Completeness.lean:125`. (Note these differ from v11's plan-time numbers `:592`/`:1498`;
  Phase 1's field addition shifted them. Re-grep at the start of every phase.)
- **Authoritative task-scoped criterion**: the scan restricted to
  `Cslib/Logics/Propositional/Tableau/` goes from **4 to 0**.
- **Repo-wide figure is a moving target** and must be measured before and after **at the same
  commit**, never compared across sessions.
- **Axiom gate (stronger than any grep)**: `#print axioms` / `lean_verify` on
  `Cslib.Logic.PL.intuitionisticTableau_complete`, `Cslib.Logic.PL.minimalTableau_complete`,
  `Cslib.Logic.PL.truthLemma`, and `Cslib.Logic.PL.tableau_complete` must show no `sorryAx`.

**CI baseline caveat (R12) — read before interpreting any full-build result.** The full `lake build`
currently **fails on a pre-existing, unrelated breakage**:
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` has a missing-cases error
(`NestedProof.cut (InputCtx.mk _ _ _)`), introduced by task 554 (commit `88b198bf`, 2026-07-26) and
verified committed rather than a concurrent-session working-tree artifact. This transitively fails
`lake exe checkInitImports`, which is not evaluable independently of the full build. **A future
implementer must not misattribute either failure to task 317.** Until that breakage clears,
**scoped-module verification is the working criterion**:

```
lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness
lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.DecisionProcedure
lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness
lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure
lake build CslibTests.TableauConformance
```
each piped through `2>&1 | grep -E "error|Build completed"`. All six green, plus the axiom gate, is
the honest completion criterion while R12 stands.

**Per-phase**:
- [ ] Pinned-SHA check on `Cslib/Foundations/Logic/Tableau/Measure.lean` before every phase (R1).
- [ ] `git log -1 -- <target file>` before every phase's first edit (R7).
- [ ] Scoped grepped build of the edited module.
- [ ] Scoped build of `Cslib.Logics.Propositional.Tableau.Minimal.Completeness` and
      `...Minimal.DecisionProcedure` for any phase touching shared machinery (R2 compensation —
      the conformance guard has zero `minimalTableau` rows).
- [ ] Strict sorry scan over the task tree; the count must match the phase's stated expectation.

**Final CI gate (Phase 9 only)**:
- [ ] `lake build` — subject to the R12 caveat above; record the unrelated failure explicitly if it
      is still present, and do not claim a pass that did not happen.
- [ ] `lake exe checkInitImports` — not evaluable while the full build is red (R12).
- [ ] `lake lint`
- [ ] `lake exe lint-style`
- [ ] `lake test` — the 43-row `CslibTests/TableauConformance.lean` guard must stay green
- [ ] `lake shake --add-public --keep-implied --keep-prefix`
- [ ] Strict sorry scan: zero hits in `Cslib/Logics/Propositional/Tableau/`; repo-wide count down
      from 29 to 25
- [ ] Axiom gate on the four declarations above; no new axioms

## Artifacts & Outputs

- `specs/317_propositional_tableau_completeness/plans/12_world-bound-prereq-threading.md` (this file)
- `specs/317_propositional_tableau_completeness/handoffs/11_phase0-spike-decisions.md` (Phase 0, landed)
- `specs/317_propositional_tableau_completeness/handoffs/11_phase2-blocker-findings.md` (v11 Phase 2 blocker, landed — the input to this revision)
- `specs/317_propositional_tableau_completeness/handoffs/12_world-bound-decision.md` (Phase 3, if the timeboxed alternative check produces a decision worth recording — expected)
- `specs/317_propositional_tableau_completeness/summaries/12_world-bound-prereq-threading-summary.md` (on completion)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (Phases 2-8, and Phase 9's premise narrowing)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` (Phase 9)
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (Phase 9)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` (Phase 9, docstrings)
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (Phase 9, docstrings)

## Rollback/Contingency

- **Per-phase rollback**: every phase commits only at a scoped-green boundary with scoped staging,
  so any phase is revertible by a single `git revert` of its commit without disturbing earlier
  phases. Never `git add -A`.
- **Phase 2 relocation goes wrong**: this is the cheapest phase to roll back — pure code motion, a
  single commit, and `git revert` restores the exact prior file. If self-containment fails, that is
  information (the block is not movable as a unit) and forces a re-plan of *how* to state the
  invariant, not a patch to the moved code.
- **Phase 3 or 4 (world bound) stalls**: this is the plan's new critical path (R10). Everything from
  Phase 5 on is transitively blocked. Mark `[BLOCKED]`/`[PARTIAL]`, record the exact resisting
  goal, and re-plan. The timeboxed alternative check in Phase 3 exists precisely so a stall arrives
  with a recorded answer to "is there a shape that avoids needing this at all?" rather than without
  one.
- **Phase 5 does not close**: it is atomic (Postmortem 14) — there is no green partial. Revert the
  in-progress edit to the last green commit, as the v11 dispatch correctly did, and hand off.
- **Phase 8 blocks**: still the plan's most likely *mathematical* failure point after the world
  bound (R5). Mark `[BLOCKED]`, record the failing induction case, and re-plan. Task 430 already
  tracks this same obligation and is the natural home; its disposition is decided at that point,
  not in advance.
- **Why no planned strategic sorry / skeleton plan**: the two candidate division points are the
  world bound (Phases 3-4) and Phase 8's atom-persistence obligation. Neither is planned as a
  strategic sorry because (i) both have concrete routes — the world bound has an explicit
  in-file-documented argument sketch plus a proven combinatorial ingredient
  (`intSubfmls_impCount_le`), and Phase 8 has the STOP-gate's own recommendation (a), whose stated
  blocker Phases 2-5 remove; (ii) a follow-up task for the persistence obligation already exists
  (430), so emitting a new one would duplicate live work the research explicitly warns against; and
  (iii) leaving a sorry at either point would leave both public completeness theorems
  `sorryAx`-tainted, which is the specific outcome this task exists to eliminate. A bounded attempt
  with a hard stop is the better trade.
- **R1 fires (`Measure.lean` moved or `sum_map_le_length_mul` renamed)**: do not adapt in place.
  Mark the current phase `[BLOCKED]`, record the new SHA and what changed, and escalate — the fix
  belongs with whoever moved it.
- **R12 (unrelated full-build breakage) never clears**: do not fix it (out of territory) and do not
  let it block task completion. Complete on the six scoped builds plus the axiom gate, and state
  the unrelated failure explicitly in the summary.
- **Full revert**: all `Cslib/` changes in this plan are confined to five files under
  `Cslib/Logics/Propositional/Tableau/`. Reverting the phase commits in reverse order restores the
  4-sorry baseline exactly; no other subsystem depends on the new predicates.
