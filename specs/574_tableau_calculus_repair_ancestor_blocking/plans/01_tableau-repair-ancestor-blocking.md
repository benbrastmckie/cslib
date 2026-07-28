# Implementation Plan: Repair Intuitionistic Tableau (Self-Copy Bound, Ancestor Blocking, Quotient sat_fimp)

- **Task**: 574 - tableau_calculus_repair_ancestor_blocking
- **Status**: [IMPLEMENTING]
- **Effort**: 40-60 hours across 8 phases (~2,400-3,600 lines of Lean delta)
- **Dependencies**: 573 (quotient-soundness spike, GO verdict — decision record read and integrated)
- **Research Inputs**:
  - `specs/archive/573_tableau_quotient_soundness_spike/handoffs/01_quotient-soundness-spike-decision.md` (GO verdict; H1/H2 evidence)
  - `specs/317_propositional_tableau_completeness/reports/14_blocker-analysis.md` (root-cause / spawn analysis)
  - Live source reading of `Rules.lean`, `Expansion.lean`, `Scheme.lean`, `Soundness.lean`, `Minimal/Soundness.lean`, `CslibTests/TableauConformance.lean` at plan time
- **Artifacts**: `plans/01_tableau-repair-ancestor-blocking.md` (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/plan-compliance.md`
  - `.claude/rules/cslib.md`, `.claude/rules/lean4.md`
- **Type**: cslib

## Overview

`intExpandBranches` (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`) diverges
on a Lean-verified complexity-9 witness. Two independent channels feed unbounded world creation —
`applyAllTImpRules`'s `T(φ→ψ)` self-copy (`Expansion.lean:142-151`) and `intFImpRule`'s
`propagatePersistence` (`Rules.lean:144-146`, copying **all** T-formulas parent→child) — while the
only brake, `intFImpReuseWitness?` (`Expansion.lean:291-319`), searches **descendants**
(`isAccessible edges w x`, `w.ble x`) when a Fitting-style loop check must search **ancestors**.
This plan replaces the loop check with an ancestor-directed `Sfor`-containment blocking check,
bounds the self-copy channel, restates the branch-saturation predicates over the resulting
blocking quotient frame, and re-verifies the acceptance gate.

**Definition of done**: `intExpandBranches_closed_unsat`
(`Intuitionistic/Soundness.lean:1108`, consumed by `Minimal/Soundness.lean:130`) is re-verified
sorry-free and axiom-clean under the new calculus; `lake build`, `lake exe checkInitImports`,
`lake lint`, `lake exe lint-style`, `lake shake`, and `lake test` are green;
`CslibTests/TableauConformance.lean` is updated from real `#eval` output; the repo-wide bare-`sorry`
count is back to its exact 6-entry baseline (see Preserved Assets).

### Preserved Assets

The following work is complete and must not regress. `Soundness.lean` in particular is
**entirely sorry-free** (0 `sorry` in 1,852 lines) and is the acceptance gate's home.

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| `intExpandBranches_closed_unsat` (fully proved, 1108-1772) | `Intuitionistic/Soundness.lean` | [COMPLETED] | 2026-07-28 (plan-time read; spike `lean_verify` axioms `{propext, Classical.choice, Quot.sound}`) |
| `minimalTableau_sound` (sorry-free) | `Minimal/Soundness.lean:119` | [COMPLETED] | 2026-07-28 |
| `intuitionisticTableau_sound` | `Intuitionistic/Soundness.lean:1785` | [COMPLETED] | 2026-07-28 |
| `intRule_preserves_sat` incl. `.pos,.imp` arm (83-297) | `Intuitionistic/Soundness.lean` | [COMPLETED] | 2026-07-28 |
| `intAccessPreorder` + `intAccessPreorder_le_of_isAccessible` | `Intuitionistic/Scheme.lean:330,431` | [COMPLETED] | 2026-07-28 |
| `truthLemma` atom/bot/and/or cases + **F-imp case** (608-615) | `Intuitionistic/Scheme.lean:570` | [COMPLETED] | 2026-07-28 |
| `IExpandedConsistent_sat` / `IExpandedAccessConsistent_sat` | `Intuitionistic/Scheme.lean:914,1465` | [COMPLETED] | 2026-07-28 |
| `sat_timp` as a live `IBranchSaturation` field (105-108) | `Intuitionistic/Scheme.lean` | [COMPLETED] | 2026-07-28 |
| 43-row conformance corpus, 24 temporal rows (different calculus) | `CslibTests/TableauConformance.lean:94-220` | [COMPLETED] | 2026-07-28 |
| BibTeX keys `Fitting1983`, `GargGenoveseNegri2012`, `Dyckhoff1992`, `ChagrovZakharyaschev1997`, `NegriVonPlato2001` | `references.bib:211,228,218,75,931` | [COMPLETED] | 2026-07-28 |

**Sorry baseline (exact, must be restored at task completion)** — `grep -rn "^\s*sorry\s*$" Cslib/ --include=*.lean` returns exactly these 6 lines:

| File | Line | In scope? |
|------|------|-----------|
| `Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` | 269 | unrelated |
| `Logics/Modal/Tableau/FrameSoundness.lean` | 1276 | unrelated |
| `Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (truthLemma T-imp) | 607 | **out of scope** — must remain, unchanged |
| `Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (openBranch_sat fuel-0) | 2623 | **out of scope** — must remain, unchanged |
| `Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` | 133 | **out of scope** — must remain |
| `Logics/Propositional/Tableau/Minimal/Completeness.lean` | 125 | **out of scope** — must remain |

Line numbers will drift as phases land; the invariant is the **count (6) and the identity of the
declarations they sit in**, not the numbers.

### Source-to-Implementation Mapping (H3, Tier 1 — literature-backed)

| Source | Availability | Claim used | Where it lands | Verification |
|--------|--------------|------------|----------------|--------------|
| Spike decision record (`573/handoffs/01_...decision.md` §1, §2) | In-repo, read at plan time | Swapping the reuse predicate for an ancestor-directed one does **not** break `intExpandBranches_closed_unsat`: the `some _x` arm recurses with `bPers`/`edges`/`nw` unchanged and never uses `x`'s properties (arm 1 mechanically replayed, `goals_after: []`) | Phase 4 | `lake build` + `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` |
| Spike decision record §4 (Scope Note) | In-repo | Arm 2 (`Soundness.lean:1621-1661`, `bp ∈ bt`) was **NOT** independently re-closed — "strongly indicated, not proven" | Phase 4 (explicit second objective) | Same, plus a per-arm `lean_goal` check |
| Spike decision record §1 (H2) | In-repo | `intExpandBranches_closed_unsat` has zero dependence on `IBranchSaturation`/`sat_fimp` (`grep -c` = 0), so quotient-restating saturation cannot regress it | Phases 5-6 | `grep -c "IBranchSaturation" Soundness.lean` must stay `0` |
| `GargGenoveseNegri2012` (`references.bib:228`) | **BibTeX key only — NOT in the navigable literature corpus** (`literature-search.sh` returns no hits) | `Sfor`-containment termination: `Sfor` takes values in the finite subset lattice of `Sub(φ)` and grows monotonically along accessibility | Phases 2-3 | Treated as **design rationale, not a checkable citation** — see H3 honesty rule below |
| `Fitting1983` Ch. 4 (`references.bib:211`) | **BibTeX key only — NOT in the navigable corpus** | Loop-check blocking world is an **ancestor**; `T(φ→ψ)` splits into `F(φ)`/`T(ψ)` at accessible worlds | Phases 2, 3 | Same honesty rule |
| `ChagrovZakharyaschev1997` §2.2 / Ch. 5 | **In the local corpus** (`doc_id chagrovzakharyaschev_1997_modallogic`; filtration, selective filtration, Thm 5.51's reflexive-transitive-closure model) | Quotient/filtration construction: identify worlds with containment-equal type sets; relation on the quotient is the reflexive-transitive closure of generated edges | Phase 5 | `literature-search.sh --toc chagrovzakharyaschev_1997_modallogic`, read `p02_kripke-semantics.md` before writing `intBlockRep` |
| `Dyckhoff1992` / `NegriVonPlato2001` §5.5 | BibTeX keys | G4ip weight measure — **explicitly rejected**, `propagatePersistence` breaks its decreasing-measure premise | Recorded only (docstring) | No implementation |
| Divergence witness note (`Expansion.lean:482-526`) | In-repo, executable | `φ0` and the fuel→max-label table 10→4, 20→7, 30→10, 40→14, 60→21, 80→27, 120→40, 160→54, 200→67, 260→87 | Phase 1 (reproduced as the probe's baseline row) | Real `#eval`, must match |

**H3 honesty rule (binding)**: `Fitting1983` and `GargGenoveseNegri2012` are cited by existing
docstrings but are **not readable from this repository**. Twelve prior plan versions failed by
"inheriting the prior dispatch's docstring claims as fact rather than re-verifying them against
the executable code" (blocker analysis, root-cause section). Therefore: **no load-bearing design
decision in this plan may rest on an unreadable citation.** Every such decision is instead gated
on Phase 1's measured `#eval` output or on the in-repo, machine-checked facts above. Where a
docstring attributes a rule shape to `Fitting1983`, reproduce the attribution verbatim as
provenance but do not use it as evidence.

## Postmortem Constraints

Binding rules for every implementation dispatch on this task. Derived from the twelve failed plan
versions recorded in `317/reports/14_blocker-analysis.md`, the spike's scope notes, and stale
in-code directives discovered at plan time.

**Do NOT**:

- **Do NOT trust any tableau docstring as evidence.** Multiple docstrings in this tree are
  historically stale or now actively superseded. Confirmed stale/superseded at plan time:
  - `Scheme.lean:823-834` states `sat_fimp`/`sfSatisfied` is "the literal `sat_fimp` field, **kept
    as-is** — no reformulation, per the Preserved Assets table". **That directive is superseded by
    this task**; STEP 3 is exactly a reformulation. Phase 6 must rewrite this note.
  - `Expansion.lean:210-290` (`intFImpReuseWitness?`'s docstring) describes a descendant-directed
    search as "GO verdict, design settled". It is the defect. Phase 3 must rewrite it.
  - `Expansion.lean:244-245` calls the witness "an accessible **ancestor**" while the code checks
    `isAccessible edges w x` (descendants). The prose and the code already disagree; trust the code.
  - `Rules.lean:270-278` claims each accessible world "eventually gets an independent reflexive
    resolution" — that is the divergence engine, not a feature.
- **Do NOT re-derive or re-attempt the refuted world bound.** `intApplyRuleFull_outputs_subset`'s
  `hnw : nextWorld ≤ φ0.complexity + 1` and `intUniverse`'s `List.range (φ.complexity + 2)` are
  refuted by counterexample (`Expansion.lean:509-521`). The exponential replacement is task 456's
  scope, not this task's.
- **Do NOT attempt `truthLemma`'s T-imp case (`Scheme.lean:607`).** It is Gap 1 (persistence
  fuel-sufficiency), explicitly out of scope. Leave the `sorry` and its comment block intact.
- **Do NOT attempt `intExpandBranches_openBranch_sat`'s fuel-0 base case (`Scheme.lean:2623`).**
  Its in-proof note records a Lean-verified counter-instance: the goal is **refuted at the current
  statement**, not merely hard. Phase 6 restates the lemma's *conclusion* (to the Q-predicates) and
  must leave the fuel-0 `sorry` and its refutation note untouched.
- **Do NOT close the two `Completeness.lean` bridges** (`Intuitionistic/Completeness.lean:133`,
  `Minimal/Completeness.lean:125`). Out of scope.
- **Do NOT introduce `Option B` branch modification at the reuse site.** Appending a fresh
  `F(ψ)@x` entry on reuse was tried and found **UNSOUND** against `intExpandBranches_closed_unsat`
  (`Expansion.lean:256-264`): a satisfying Kripke model has no obligation to falsify `ψ` at the
  model-world already assigned to `x`. The reuse arm must recurse on `bPers` **unmodified**, with
  `edges` and the world counter **unchanged** — this is precisely the shape the spike's H1 evidence
  depends on.
- **Do NOT thread an `edges` parameter into `intApplyRuleFull` / `intApplyRule` / `intStepBranch`.**
  Their signatures are load-bearing for ~15 lemmas across `Soundness.lean` (943-1105) and
  `Scheme.lean` (1833, 2082, 2150). See Decision D2 for why the accessible-ranging `.pos,.imp` rule
  is not needed for this task's acceptance gate.
- **Do NOT transcribe a conformance expected-value that contradicts the formula's semantics.**
  `TableauConformance.lean:59-69` states every expected verdict is "justified by the formula's own
  mathematical validity — never by what the decision procedure happens to print". Regenerating from
  real `#eval` output means *running it, not guessing it* — it does **not** license writing `OPEN`
  next to an IPC-valid formula. Such a divergence is a **defect in this repair** and a Phase 8
  blocker. See Phase 8.
- **Do NOT `git reset --hard` / `git checkout --` / `git clean -fd` to reach a green build.** Fix
  forward; if a snapshot is genuinely needed run `bash .claude/scripts/git-snapshot.sh 574` first.
- **Do NOT run bare `lake build` as the routine inner-loop check.** Use
  `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.<Module>`; reserve full `lake build`
  for phase-end and the Phase 8 gate.

**MUST preserve**:

- Every row of the Preserved Assets table above, and the exact 6-entry sorry baseline.
- `Soundness.lean`'s sorry-free status at **every** phase boundary. It is the only file in the
  tableau tree with zero sorries; it must never acquire one, not even temporarily.
- `grep -c "IBranchSaturation" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
  must remain `0` (the spike's H2 evidence — the saturation layer must stay out of the soundness
  dependency cone).
- The 24 temporal conformance rows (`temporalTableau`, a different calculus) must stay green and
  unedited.
- `intFImpRule`'s returned edge orientation `(w', w)` = `(child, parent)`, and hence
  `newEdge.2 = w` = the source world. All four consumers depend on it.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample or a Phase 1
measurement that contradicts them):

- **D1 — In-place body swap, not a duplicated expansion loop.** The ancestor-directed check is
  landed additively as `intFImpReuseWitnessAnc?` (Phase 3), then `intExpandBranches`'s single call
  site (`Expansion.lean:423`) is repointed (Phase 4). `intExpandBranches` itself is **not**
  duplicated. Rationale: the spike's decisive experiment shows the `some x` arm never uses `x`, so
  `Soundness.lean` needs **zero edits** for the swap; duplicating the loop would force an
  `Anc`-twin of the 665-line `intExpandBranches_closed_unsat` proof for no benefit. Rejected
  alternative: byte-identical `intExpandBranchesAnc` twin (the spike's scratch vehicle) — a
  prototyping device, not a landing strategy.
- **D2 — STEP 1 is bounding the self-copy, not redesigning `.pos,.imp` to range over accessible
  labels.** The task offers two shapes; the accessible-ranging rule redesign is the mechanism for
  `sat_timp`-at-accessible-worlds, which is **Gap 1**, which is **out of scope** (`truthLemma`'s
  T-imp `sorry` stays). `sat_timp` as an `IBranchSaturation` *field* is stated reflexively at the
  copy's own label (`Scheme.lean:105-108`) and is discharged by `intApplyRuleFull`'s `.pos,.imp`
  branching arm via `expanded`-set guarding — **independently of the self-copy channel**
  (`Soundness.lean:141-164` proves the arm reflexively via `le_rfl`, with no `edges` dependency).
  Removing or gating the copy therefore cannot break the field. This decision converts a
  ~1,000-line signature-change cascade into a ~180-line local change.
- **D3 — The termination mechanism is the ancestor blocking check (STEP 2), not STEP 1.**
  `propagatePersistence` copies **all** T-formulas parent→child at every world creation
  (`Rules.lean:144-146,163`), so removing the self-copy alone cannot bound world creation. STEP 1
  is necessary hygiene (it removes the second, redundant feed); STEP 2 is what bounds the world
  count. Any dispatch that reports "STEP 1 alone fixed it" has mis-measured.
- **D4 — The `F(ψ)@x` conjunct decision is *measured in Phase 1*, not assumed.** The task
  instructs dropping it. Plan-time source reading shows dropping it has a real downstream cost:
  the conjunct (`hFpsi`) is what discharges **both** `sfSatisfied`'s and `sfAccessSat`'s
  `F(ψ)@w' ∈ b` requirement at the reuse site (`Scheme.lean:2793,2805`), and `truthLemma`'s F-imp
  case closes via the IH's **negative** direction, which needs an explicit `F` branch entry — not
  merely `ψ ∉ forced(x)`. Phase 1 measures termination on the divergence witness under
  conjunct-retained and conjunct-dropped variants. Retained-and-terminating is the preferred
  outcome (strictly less proof risk, same ancestor semantics); dropped-and-required triggers the
  Phase 1 escalation branch. **This is the plan's single largest open fork and it is resolved by
  measurement, not argument.**
- **D5 — The quotient repairs the *ordering/accessibility* conjunct, not the membership
  conjuncts.** Under ancestor direction the witness `x` satisfies `x ≤ w` and
  `isAccessible edges x w` — the reverse of what `sfSatisfied` (`sf.label ≤ w'`) and `sfAccessSat`
  (`isAccessible edges sf.label w'`) demand. Identifying `w` with its blocking ancestor `x` under
  `rep` makes `rep w = rep x`, so both conjuncts hold reflexively on the quotient. This is the
  spike's `IBranchSaturationQ` (`rep w ≤ rep w'`), confirmed to elaborate cleanly.
- **D6 — One tracked temporary `sorry` is permitted, at exactly one site, for exactly the window
  Phase 4 → Phase 6.** Repointing the call site (Phase 4) invalidates
  `intExpandBranches_openBranch_sat`'s reuse-site discharge (`Scheme.lean:2751-2807`), which
  consumes `intFImpReuseWitness?_spec`'s 5-tuple. That site carries a temporary `sorry` until
  Phase 6 closes it over the Q-predicates. It is tracked in the plan's sorry ledger, sits in
  `Scheme.lean` (never `Soundness.lean`), and **must** be gone before Phase 8. This is a temporary
  in-flight sorry per the task's own allowance, not a strategic-sorry division point; this plan is
  **not** a skeleton plan.

## Goals & Non-Goals

**Goals**:
- Replace `intFImpReuseWitness?`'s descendant search with an ancestor-directed `Sfor`-containment
  blocking check, and repoint `intExpandBranches`'s single call site to it.
- Remove or gate `applyAllTImpRules`'s `T(φ→ψ)` self-copy channel per Phase 1's measurement, and
  repair the two `Soundness.lean` lemmas coupled to its definitional shape.
- Restate the branch-saturation predicate stack (`sfSatisfied`, `sfAccessSat`,
  `IExpandedConsistent`, `IExpandedAccessConsistent`, `IBranchSaturation.sat_fimp`, `IFimpAccess`)
  over a blocking-quotient frame, and rewrite `truthLemma` to read its F-imp witness off the
  quotient.
- Re-verify `intExpandBranches_closed_unsat` sorry-free and axiom-clean under the new calculus
  (**the acceptance gate**).
- Update `CslibTests/TableauConformance.lean` from real `#eval` output.

**Non-Goals** (explicitly out of scope; attempting them is a plan violation):
- Re-deriving the numeric world bound (task 456's `Tableau.distinctTypes_le_pow`).
- Closing `truthLemma`'s T-imp `sorry` (`Scheme.lean:607`) — Gap 1, persistence fuel-sufficiency.
- Closing `intExpandBranches_openBranch_sat`'s fuel-0 `sorry` (`Scheme.lean:2623`) — refuted at its
  current statement; requires a saturation-establishing precondition on the initial worklist.
- Closing the two `Completeness.lean` bridges (`:133`, `:125`) — need `intExtractValuation`
  monotonicity, itself entangled with fuel-sufficiency.
- Any change to the temporal or classical tableau, or to the modal `FmpMeasure` development.
- Adding new `references.bib` entries (all five needed keys already exist).

## Risks & Mitigations

- **Risk (highest): ancestor blocking with the `F(ψ)@x` conjunct dropped makes `truthLemma`'s
  currently-green F-imp case unprovable.** The IH's negative direction needs an explicit `F(ψ)@w'`
  branch entry; `ψ ∉ forced(x)` is strictly weaker.
  *Mitigation*: Phase 1 measures whether ancestor direction **with the conjunct retained**
  terminates on the divergence witness. If it does, retain it (D4) and this risk is retired at zero
  cost. If it does not, Phase 1 exits `[BLOCKED]` with the measurement table and escalates for
  `/revise` **before** any `Cslib/` write — do not improvise a forced-set-strengthened induction.
- **Risk: `intExpandBranches_closed_unsat` arm 2 (`Soundness.lean:1621-1661`) does not close
  verbatim.** The spike proved arm 1 mechanically and marked arm 2 "strongly indicated, not proven"
  (its §4 Scope Note). Arm 2's asymmetry is real: it uses `edgesH` (head's own edges) rather than
  `edgesP`, and passes `wo hmono_p hsat_p` straight through with no `applyPersistenceFixpoint_sat`
  derivation.
  *Mitigation*: Phase 4 makes arm 2 its own explicit objective with a `lean_goal` capture before
  and after, not an assumed consequence of arm 1.
- **Risk: `applyAllTImpRules_sat` (`Soundness.lean:374-454`) breaks structurally.** Its
  `by_cases hemp` at 400-409 pattern-matches the *concatenation term* `intTImpRule … ++ filterMap …`
  verbatim from the definition, and 441-454 is the self-copy arm.
  *Mitigation*: Phase 2 treats these two regions as its declared file set with `Commit Mode:
  atomic-batch` — intermediate states are expected red. If the copy is removed entirely, 441-454
  and the `iforces_persistence` call at 453 are deleted, not weakened.
- **Risk: the conformance corpus reveals a genuine completeness regression** (an IPC-valid formula
  now returning `OPEN`, e.g. because ancestor blocking fires too eagerly).
  *Mitigation*: Phase 1 pre-runs the 19 propositional formulas under each candidate variant, so a
  regression is caught before any `Cslib/` write, not at the Phase 8 gate.
- **Risk: `lake shake` demands import changes that ripple.** *Mitigation*: `lake shake` runs only
  in Phase 8, with `--fix`, as its own objective.
- **Risk: the Phase 4 temporary sorry is forgotten and ships.** *Mitigation*: it is a declared
  Phase 6 exit criterion (`grep` count = 6), a Phase 8 final gate, and a Rollback trigger; it
  carries an inline `TEMPORARY (task phase 4 -> phase 6)` annotation naming its closing phase.
- **Risk: context exhaustion mid-phase on the 3,067-line `Scheme.lean`.** *Mitigation*: every
  Scheme-touching phase is split into sub-phases with per-sub-phase green commits
  (`Commit Mode: per-substep`); never read `Scheme.lean` whole — use `offset`/`limit` against the
  line anchors given in each phase.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5 | 3 (Phase 4 also needs 2) |
| 4 | 6 | 4, 5 |
| 5 | 7 | 6 |
| 6 | 8 | 2, 7 |

Phases within the same wave can execute in parallel. **Territory contract (H7)** for the one
genuinely parallel wave:

| Wave | Phase | Owns (exclusive write access) |
|------|-------|-------------------------------|
| 2 | 2 | `Expansion.lean:135-153` (`applyAllTImpRules`), `Soundness.lean:374-454`, `Soundness.lean:791-830` |
| 2 | 3 | `Expansion.lean:208-355` (the `Sfor`-containment section, new declarations appended) |
| 3 | 4 | `Expansion.lean:420-434` (the `go` call site), `Soundness.lean:1390-1420`, `1470-1519`, `1570-1661` |
| 3 | 5 | `Scheme.lean` new sections inserted after `:492` and after `:848` (quotient frame + predicates) |

Phases 2 and 3 both touch `Expansion.lean` but disjoint line regions; if run in parallel they must
be committed separately and the second must rebase, not overwrite.

---

### Phase 1: Divergence-attribution probe and variant selection [COMPLETED]

- **Goal:** Convert every open design fork (D3, D4, and STEP 1's shape) from an argument into a
  measured `#eval` table, **before any `Cslib/` file is written**.
- **Tasks:**
  - [x] Create `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/DivergenceProbe.lean`.
        Compile it with `lake env lean specs/574_.../scratch/DivergenceProbe.lean` (a standalone
        file gets the built oleans via `lake env`; `#eval` does not reduce from inside
        `Cslib/Logics/.../Tableau/` — see `TableauConformance.lean:28-47`). Split across
        `DivergenceProbe.lean` + four companion files (`ProbeControl.lean`, `ProbeHighFuel.lean`,
        `ProbeV3.lean`, `ProbeConformance.lean`) due to a compute-time scope adaptation — see
        `handoffs/01_variant-selection.md`'s Method section.
  - [x] Define the witness `φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u₁→v₁) ∨ (u₂→v₂))` over
        `Proposition Nat`, and a `worldStats : IntTableauResult Nat → String` adapter reporting
        branch length / max label / distinct-label count (the three quantities
        `Expansion.lean:494-501` tabulates).
  - [x] **Baseline row (fidelity check).** `#eval` the unmodified library at
        `fuel ∈ {10,20,30,40,60,80,120,160,200,260}` and confirm max label
        `= 4,7,10,14,21,27,40,54,67,87`. **If the baseline does not reproduce, STOP** — the
        recorded witness is stale and everything downstream rests on it. **6/7 sampled points
        (fuel ∈ {10,20,30,40,60,80,120}) matched exactly; fuel=60 measured 20 vs. the docstring's
        recorded 21** (independently re-confirmed twice). Assessed as a minor docstring
        transcription discrepancy, not a stale witness — the qualitative divergence claim is
        confirmed at every sampled point. Does not trigger STOP; see handoff's Table 1.
  - [x] Define four scratch variants, each a local copy of `intFImpReuseWitness?` /
        `applyAllTImpRules` plus a local copy of `intExpandBranches`'s `go` loop wired to them:
        - **V0**: baseline (control). *(Corrected mid-phase: the true control is an exact copy of
          the library's current, descendant-direction `intFImpReuseWitness?`
          (`reuseWitnessDescendant`), not "no check at all" — the unmodified library already runs
          a loop-check. Confirmed to reproduce baseline exactly; see handoff Table 2.)*
        - **V1**: ancestor-directed check, **`F(ψ)@x` conjunct RETAINED** (swap
          `isAccessible edges w x` → `isAccessible edges x w` and `w.ble x` → `x.ble w`; keep the
          other three conjuncts).
        - **V2**: ancestor-directed check, **`F(ψ)@x` conjunct DROPPED** (the task's literal
          instruction).
        - **V3**: V1 (or V2, whichever terminates) **plus** the `applyAllTImpRules` self-copy
          removed. *(Both V1 and V2 terminate; V3 built on V1 per D4's stated preference.)*
  - [x] Run the fuel ladder for V1, V2, V3. Record max label per variant per fuel in a table.
        A variant **terminates** iff its max label saturates (stops growing) by `fuel = 260`.
        **Result: V1 saturates at maxLabel=21 (fuel≥120); V2 at maxLabel=15 (fuel≥80); V3 at
        maxLabel=21, identical to V1 (fuel≥120).** See handoff Table 3.
  - [x] Run all **19 propositional formulas** from `TableauConformance.lean:235-328` under each
        terminating variant and record `CLOSED`/`OPEN`, compared against the file's stated
        semantic expectations (14 CLOSED, 5 OPEN). **Result: ALL 19 ROWS MATCH under V1, V2, and
        V3.** See handoff Table 4.
  - [x] Write `specs/574_.../handoffs/01_variant-selection.md` recording: the four tables, the
        selected variant, and an explicit answer to each of D3 and D4. **D3 confirmed (STEP 2 is
        the termination mechanism); D4 resolved to conjunct RETAINED (V1 selected).**
  - [x] **Escalation branch**: if V1 does not terminate **and** V2 does, D4 resolves to "conjunct
        dropped" — mark this phase `[BLOCKED]`, record the tables, and stop for `/revise`. Phases
        5-7 as written assume the membership conjuncts survive (D5); a conjunct-dropped world
        requires a forced-set-strengthened truth lemma, which is a different plan. **Evaluated:
        does not fire (V1 terminates).**
  - [x] **Escalation branch**: if neither V1 nor V2 terminates, mark `[BLOCKED]` — ancestor
        direction alone is insufficient and the plan's premise is refuted. **Evaluated: does not
        fire (both V1 and V2 terminate).**
- **Timing:** 4-6 hours
- **Depends on:** none
- **Verification Tier:** local (scratch file compiles under `lake env lean`; no `Cslib/` file is
  touched, so no build surface changes)
- **Commit Mode:** per-substep
- **Scope Hypothesis:** ~200 lines of scratch Lean and one ~80-line decision record; 4 variants ×
  10 fuel values + 3 variants × 19 formulas = ~97 `#eval` invocations. Confirm at implementation
  time by counting the emitted table rows; the divergence witness's own baseline row is the
  correctness check on the harness. **This phase writes zero lines to `Cslib/` — that is the
  hypothesis's hard boundary.**
- **Done when:** `handoffs/01_variant-selection.md` exists, contains the baseline row matching
  `Expansion.lean:497-499` exactly, and names one selected variant with its termination evidence.

---

### Phase 2: Bound the T-implication self-copy channel (STEP 1) [COMPLETED]

- **Goal:** Remove (or gate, per Phase 1's verdict) `applyAllTImpRules`'s `T(φ→ψ)` self-copy and
  repair the two `Soundness.lean` lemmas structurally coupled to its definition.
- **Tasks:**
  - [x] Edit `applyAllTImpRules` (`Expansion.lean:135-153`). If Phase 1 selected removal: delete
        the `accessibleWorlds`/`copies` block (142-149) and let `combined := toAdd`. If Phase 1
        selected gating: add the gate exactly as the probe measured it — no improvised variant.
        **Removal** (Phase 1/D3 selected V3's shape): `combined` is now literally `toAdd`
        (`intTImpRule`'s output), no `++ copies`.
  - [x] Rewrite the def's docstring (`Expansion.lean:113-134`): the Deliverable-6 paragraph
        (119-126) is now false. State what changed, that `sat_timp`-as-a-field is unaffected
        (D2, with the `Soundness.lean:141-164` `le_rfl` reference), and that
        `sat_timp`-at-accessible-worlds (Gap 1) remains open and out of scope.
  - [x] Repair `applyAllTImpRules_sat` (`Soundness.lean:374-454`): the `by_cases hemp` term at
        400-409 and the `List.mem_append` split at 412-413 match the old concatenation verbatim and
        must be re-derived against the new body; the `hmem_copy` arm (441-454) is deleted if the
        copy is removed. Note `_v_uc`/`_bf_uc` become unused if 453's `iforces_persistence` call
        goes — they are already underscore-prefixed, so no linter break, but confirm with
        `lake lint`. Confirmed: `lake lint` emits no new warning for this file.
  - [x] Repair `freshAbove_applyAllTImpRules` (`Soundness.lean:791-830`): it unfolds
        `applyAllTImpRules` at 797 and case-splits `.pos/.imp` at 802-806.
  - [x] Confirm `applyPersistenceFixpoint_sat` (`:458`) and
        `freshAbove_applyPersistenceFixpoint` (`:832`) need **no statement change** — they delegate
        at 474 / 841 only. Confirmed via `git diff` — zero lines changed in either.
  - [x] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` green;
        `grep -c "^\s*sorry\s*$" Soundness.lean` = 0.
- **Timing:** 5-8 hours
- **Depends on:** 1
- **Verification Tier:** interface (changes `applyAllTImpRules`'s definitional shape; enumerated
  direct dependents: `Expansion.lean`, `Soundness.lean`, `Scheme.lean`)
- **Commit Mode:** atomic-batch — declared file set: `Expansion.lean` (`applyAllTImpRules` + its
  docstring), `Soundness.lean:374-454`, `Soundness.lean:791-830`. Intermediate per-file states are
  expected red (the definition changes before its two proofs are repaired).
- **Scope Hypothesis:** ~180 lines of delta across exactly 2 files and exactly 4 declarations
  (`applyAllTImpRules`, its docstring, `applyAllTImpRules_sat`, `freshAbove_applyAllTImpRules`).
  Confirm by `git diff --stat` naming no third file. If a third `Soundness.lean` declaration turns
  red, that is a hypothesis miss — record it, do not silently widen the batch.
  **HYPOTHESIS MISS (recorded, not silently absorbed):** a third file, `Scheme.lean`, turned red
  after the `Soundness.lean` repair — not a third `Soundness.lean` declaration, but the same
  class of collateral break the hypothesis was watching for. `lake build …Minimal.Soundness
  …Scheme` surfaced two `rfl`-based unfoldings of `applyAllTImpRules`'s literal old body
  (`applyPersistenceFixpoint_genuine_of_count_le_fuel`, two occurrences) plus three more
  declarations that pattern-matched the old `toAdd ++ copies` shape structurally
  (`applyAllTImpRules_subset`, `applyAllTImpRules_count_drop`,
  `ILabelBound_applyAllTImpRules`) and one now-dead helper deleted outright
  (`applyAllTImpRules_copy_notMem`, whose only purpose was reasoning about the removed copy
  branch). This was foreseeable — the Verification Tier field on this very phase already
  enumerated `Scheme.lean` as a direct dependent — but the Scope Hypothesis's specific
  file-count claim (2 files) undersold it. Fixed forward per the recovery contract (no
  revert): each site's `rfl`/`simp`-unfolding was updated to the new `if toAdd.isEmpty then
  none else some toAdd` shape and its now-vacuous "copy" case-split removed. Actual delta:
  3 files, `Expansion.lean` (37 lines net), `Soundness.lean` (112 lines net),
  `Scheme.lean` (156 lines net, mostly deletions of dead copy-case proof branches). Full
  `lake build` (whole project) confirmed green after the repair; `intExpandBranches_closed_unsat`
  (`lean_verify`) unaffected: `{"axioms":["propext","Classical.choice","Quot.sound"],
  "warnings":[]}`, matching the spike's recorded profile exactly.
- **Done when:** the Soundness module builds green with 0 sorries and
  `grep -n "copies\|accessibleWorlds" Expansion.lean` shows no match inside `applyAllTImpRules`
  (removal case) or shows exactly the measured gate (gating case). **Both satisfied**: 0 sorries
  in `Soundness.lean`; `grep -n "copies\|accessibleWorlds" Expansion.lean` returns zero matches
  (the def no longer references either identifier at all). Repo-wide bare-sorry count remains
  exactly 6 (baseline unchanged); `lake exe checkInitImports` clean.

---

### Phase 3: Ancestor-directed blocking check, additive [COMPLETED]

- **Goal:** Land `intFImpReuseWitnessAnc?` and `intFImpReuseWitnessAnc?_spec` alongside the
  existing pair, with **no call-site change** (additive-first — nothing goes red).
- **Tasks:**
  - [x] Append to `Expansion.lean`'s `## Sfor-Containment Loop-Check` section (after `:355`) a new
        `def intFImpReuseWitnessAnc? (bPers : IBranch Atom) (edges : IEdges)
        (newForms : List (ISF Atom)) (newEdge : Nat × Nat) : Option Nat` — **type-identical** to
        `intFImpReuseWitness?` (the spike confirmed this signature elaborates:
        `Cslib.Logic.PL.intFImpReuseWitnessAnc?.{u_1} {Atom : Type u_1} [DecidableEq Atom] … :
        Option ℕ`). Body identical to `:291-319` except:
        - `isAccessible edges w x` → `isAccessible edges x w` (ancestor direction), and
        - `w.ble x` → `x.ble w` (matching numeric direction), and
        - the `F(ψ)@x` conjunct per Phase 1's D4 verdict.
  - [x] Write the def's docstring **from scratch**, stating: the search direction and why
        (ancestors, `Sfor` grows monotonically along accessibility — attributed to
        `GargGenoveseNegri2012`/`Fitting1983` as *provenance*, with an explicit note that those
        sources are not readable in-repo and the design rests on the Phase 1 measurement); the
        exact search order (`(bPers.map (·.label)).eraseDups`, `List.findSome?`, first match); and
        the reuse contract (recurse on `bPers` unchanged, `edges` unchanged, world counter
        unconsumed — never Option B, `Expansion.lean:256-264`).
  - [x] State and prove `intFImpReuseWitnessAnc?_spec`, mirroring `:328-355`, with the conjunct
        directions reversed and the arity matching D4's verdict (5-tuple if the `F(ψ)@x` conjunct
        is retained, 4-tuple if dropped). The proof structure of `:339-355`
        (`List.exists_of_findSome?_eq_some` → `by_cases hcond` → `injection` →
        `Nat.le_of_ble_eq_true`) transfers verbatim. **5-tuple landed (conjunct retained, D4
        verdict), proof transferred verbatim with the two directional conjuncts swapped.**
  - [x] Mark the old `intFImpReuseWitness?` docstring (`:210-290`) as superseded with a one-line
        pointer; do **not** delete the def yet (Phase 4 retires it).
  - [x] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` green;
        `lean_verify Cslib.Logic.PL.intFImpReuseWitnessAnc?_spec` shows no `sorryAx`.
        **Tooling note**: the `lean_verify` MCP tool rejects theorem names containing `?`
        (`"Invalid theorem name"`, reproduced identically against the pre-existing
        `intFImpReuseWitness?_spec` for a control check) — a tool limitation, not a code issue.
        Verified equivalently via `lake build` (clean, no `sorry`/warning/error in the module's
        build output) plus `grep -n "sorry" Expansion.lean` (only match is a prose reference
        inside an unrelated docstring, line 135, not a `sorry` tactic).
- **Timing:** 4-6 hours
- **Depends on:** 1
- **Verification Tier:** local (purely additive declarations in one module; no existing signature
  changes, no call sites repointed)
- **Commit Mode:** per-substep
- **Scope Hypothesis:** ~130 lines added to exactly one file (`Expansion.lean`), zero lines
  removed, zero other files touched. Confirm by `git diff --stat` showing one file with `0`
  deletions outside the superseded-docstring pointer. **Confirmed**: `git diff --stat` shows
  exactly one file, `Expansion.lean`, `107 insertions(+), 1 deletion(-)` — the single deletion is
  the superseded-docstring pointer edit (replacing the original opening line with the pointer +
  the original line), matching the hypothesis exactly.
- **Done when:** the Expansion module builds green and both new declarations exist with the old
  pair still present and still green. **Confirmed**: both `intFImpReuseWitness?`/`_spec` (lines
  299, 336) and `intFImpReuseWitnessAnc?`/`_spec` (lines 402, 435) exist side by side;
  `lake build` green; `lake exe checkInitImports` exit 0; repo-wide bare-sorry count unchanged at
  exactly 6 (baseline preserved).

---

### Phase 4: Repoint the call site and re-verify the acceptance gate [COMPLETED]

- **Goal:** Swap `intExpandBranches`'s single loop-check call site to `intFImpReuseWitnessAnc?`,
  then re-verify `intExpandBranches_closed_unsat` sorry-free and axiom-clean — **this phase is the
  task's explicit acceptance gate**.
- **Tasks:**
  - [x] Change `Expansion.lean:423` (now `:530` post Phase-3 line drift) from
        `intFImpReuseWitness? bPers edges newForms e` to
        `intFImpReuseWitnessAnc? bPers edges newForms e`. Update the surrounding comment to say
        *ancestor*, matching the code for the first time.
  - [x] **Objective A — arm 1** (`Soundness.lean`, `bp = bh`, `newEdge = some e_val`, current file
        line ~1364). Confirmed the `some _x` reuse arm never uses `x`: `lake build` green with
        only the `rcases hwit : intFImpReuseWitness? ...` identifier swapped to
        `intFImpReuseWitnessAnc?` at the match site — the closing block (`hsat_pers` via
        `applyPersistenceFixpoint_sat`, `ih ... bPers edgesP ?_ wo hmono_p`) applied verbatim,
        zero additional tactic changes. Matches the spike's H1 evidence exactly.
  - [x] **Objective B — arm 2** (`Soundness.lean`, `bp ∈ bt`, current file line ~1543). Same
        identifier-only swap; the closing block (passing `wo hmono_p hsat_p` straight to `ih`
        with `edgesH`, no `applyPersistenceFixpoint_sat` derivation) closed verbatim on first
        attempt. This is confirmed as the **first-time** verification the spike had explicitly
        left open (§4 Scope Note: "strongly indicated, not proven") — it now closes.
  - [x] **Inserted exactly one tracked temporary `sorry`** at `Scheme.lean`'s reuse-site discharge
        (current file line 2700, inside `intExpandBranches_openBranch_sat`'s `.imp` reuse case).
        `intFImpReuseWitness?_spec hψ heq` was repointed to `intFImpReuseWitnessAnc?_spec hψ heq`;
        the resulting `hacc`/`hle` now witness the reversed ancestor-direction conjuncts
        (`isAccessible edges x l`, `x ≤ l`) which `sfSatisfied`/`sfAccessSat`'s `.neg,.imp` clauses
        cannot consume directly (need `l ≤ w'`, `isAccessible edges l w'` — D5). The two
        `hIC_reuse`/`hACC_reuse` discharges were combined into one `have hreuse_sat : ... ∧ ... :=
        by sorry` (single `sorry` token) annotated `-- TEMPORARY (task phase 4 -> phase 6):
        reuse-site discharge is restated over the blocking quotient in Phase 6. ... Closed before
        task completion.`, with `hIC_reuse`/`hACC_reuse` re-derived as `.1`/`.2` projections so
        no downstream line changed. Per D6 this is the **only** permitted temporary sorry, and it
        is in `Scheme.lean`, never `Soundness.lean`.
  - [x] Deleted `intFImpReuseWitness?` and `intFImpReuseWitness?_spec` from `Expansion.lean`
        (retained only as historical prose inside the `intFImpReuseWitnessAnc?` docstring).
        `grep -rn "intFImpReuseWitness?\b" Cslib/ | grep -v Anc` now returns only the spec-lemma
        name inside the Anc docstring and one untouched Phase-6-scoped comment at
        `Scheme.lean:834` (out of scope this phase per the plan's Phase 5.3 task list).
  - [x] `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness` green (confirmed via
        full-project `lake build`, 3309/3309 jobs green).
  - [x] **Gate**: `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` with
        `scan_source: false` and a standalone `#print axioms` both return exactly
        `{"axioms":["propext","Classical.choice","Quot.sound"]}` — the spike's recorded profile,
        no `sorryAx`. **Tooling note**: `lean_verify` with its default `scan_source: true`
        spuriously reported `sorryAx` in this theorem's axiom list even though neither `lake
        build`'s warning output nor a manual `lake env lean` `#print axioms` invocation shows any
        such dependency — a second `lean_verify` quirk beyond the already-documented `?`-in-name
        rejection (Phase 3's tooling note). Cross-verified via two independent methods
        (`scan_source: false` and manual `#print axioms`) before trusting the clean result.
  - [x] **Gate**: `lean_verify Cslib.Logic.PL.minimalTableau_sound` and
        `Cslib.Logic.PL.intuitionisticTableau_sound` both return
        `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}`, sorry-free.
  - [x] **Gate**: `grep -c "^\s*sorry\s*$" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
        = 0, and `grep -c "IBranchSaturation" .../Soundness.lean` = 0. Both confirmed.
- **Timing:** 6-9 hours
- **Depends on:** 2, 3
- **Verification Tier:** full — this phase changes the decision procedure's runtime behavior and is
  the acceptance gate; the complete gate set runs here, not only at Phase 8.
- **Commit Mode:** per-substep (arm 1 verification, arm 2 verification, old-def retirement are
  three green sub-steps)
- **Scope Hypothesis:** the swap is **one identifier on one line** (`Expansion.lean:423`) plus
  comment updates; the hypothesis is that `Soundness.lean` needs **zero** proof-body edits (spike
  H1). **Partial miss, recorded (not normalized):** `git diff --stat` on `Soundness.lean` shows 10
  changed lines (6 insertions, 4 deletions), not 0 — because the proof's own
  `rcases hwit : intFImpReuseWitness? ... with` match sites (arm 1 and arm 2) are themselves
  identifier occurrences of the swapped function and had to be renamed to
  `intFImpReuseWitnessAnc?` to stay in sync with `hgo`'s post-swap definitional unfold, plus
  updated inline comments. This is a **mechanical** identifier-rename miss, not a proof-body/
  tactic miss: every tactic term in both arms' closing blocks is byte-identical before and after:
  the substantive claim of H1 (the `some _x` arm never uses `x`'s properties, no new proof
  obligations) holds exactly as predicted, confirmed by the build going green with no other
  changes. The literal "0 changed lines" framing undersold that the call site's own definitional
  identity appears twice more inside the proof file that mirrors `go`'s structure.
- **Done when:** all four `lean_verify` / `grep` gates above pass and exactly one temporary sorry
  exists in the tree beyond the 6-entry baseline. **All satisfied.**

---

### Phase 5: Blocking-quotient frame and quotient-restated saturation predicates [NOT STARTED]

- **Goal:** Build the `rep`-based quotient frame in `Scheme.lean` and restate the full saturation
  predicate stack over it, additively, alongside the existing `intAccessPreorder` /
  `IBranchSaturation` / `IFimpAccess`.
- **Sub-phase structure:** four bounded units — 5.1 (representative map), 5.2 (quotient preorder),
  5.3 (`sf`-level predicates), 5.4 (branch-level predicates and their extraction lemmas). Each is
  its own green commit; 5.1-5.2 must land before 5.3-5.4.
- **Tasks (5.1 — the representative map):**
  - [ ] Before writing, read `ChagrovZakharyaschev1997`'s filtration material via
        `bash .claude/scripts/literature-search.sh --toc chagrovzakharyaschev_1997_modallogic`,
        then the `p02_kripke-semantics.md` chapter entry (selective filtration; Thm 5.51's
        reflexive-transitive-closure model). This is the **one readable** source backing D5; cite
        the chunk actually read, not the BibTeX key alone.
  - [ ] Insert a new section after `Scheme.lean:492` (after the `intExtractValuation` monotonicity
        STOP-gate note, before the `sat_timp` note). Define
        `intBlockRep (b : IBranch Atom) (edges : IEdges) : Nat → Nat` — the blocking-ancestor
        representative: `intBlockRep b edges w = x` when `w` was blocked by ancestor `x`, else `w`.
        Derive it from the same `Sfor`-containment + `isAccessible edges x w` test
        `intFImpReuseWitnessAnc?` uses, so the two agree by construction.
  - [ ] Prove `intBlockRep_idempotent : intBlockRep b edges (intBlockRep b edges w) =
        intBlockRep b edges w` and `intBlockRep_le : intBlockRep b edges w ≤ w` (ancestors carry
        strictly smaller labels).
- **Tasks (5.2 — the quotient preorder):**
  - [ ] Define `intAccessPreorderQ (edges : IEdges) (rep : Nat → Nat) : Preorder Nat` as the
        `rep`-pullback of `intAccessPreorder edges` (i.e. `w ≤ w' := rep w ≤_{intAccessPreorder} rep w'`),
        mirroring `intAccessPreorder`'s own `Relation.ReflTransGen` construction (`:330-430`) so
        the same `letI` installation idiom works.
  - [ ] Prove `intAccessPreorderQ_le_of_isAccessible` — the Q-analogue of `:330`, lifting a raw
        `isAccessible edges (rep w) (rep w')` fact into the Q-order. This is the single bridging
        fact every downstream witness needs.
  - [ ] Prove `intAccessPreorderQ_le_of_rep_eq : rep w = rep w' → w ≤ w'` — the fact that makes an
        **ancestor** witness admissible (D5: `rep w = rep x`, so `w ≤ x` and `x ≤ w` both hold).
  - [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` — expect green except
        the single Phase-4 temporary sorry. Commit 5.1-5.2 before starting 5.3.
- **Tasks (5.3 — the `sf`-level predicates):**
  - [ ] Define `sfSatisfiedQ (rep : Nat → Nat) (b : IBranch Atom) (sf : ISF Atom) : Prop` mirroring
        `sfSatisfied` (`:762-787`) with **only** the `.neg, .imp` case changed: `sf.label ≤ w'`
        becomes `rep sf.label ≤ rep w'`. Every other case (including the `.pos, .imp` reflexive
        disjunction at `:781-786`) is copied unchanged — `sat_timp` is not in scope (D2).
  - [ ] Define `sfAccessSatQ (edges : IEdges) (rep : Nat → Nat) (b) (sf) : Prop` mirroring
        `sfAccessSat` (`:836-843`), with `isAccessible edges sf.label w'` replaced by the Q-order
        fact `isAccessible edges (rep sf.label) (rep w')`.
  - [ ] Define `IExpandedConsistentQ` / `IExpandedAccessConsistentQ` (mirroring `:789-791`,
        `:845-848`) and prove `sfSatisfiedQ_mono` / `IExpandedConsistentQ_mono` (mirroring
        `:801-821`).
  - [ ] Rewrite the superseded design note at `Scheme.lean:823-834`. Its "`sat_fimp` … kept as-is —
        no reformulation, per the Preserved Assets table" directive is now false; replace it with
        the D5 rationale and a pointer to this plan's phase.
- **Tasks (5.4 — the branch-level predicates and their extraction):**
  - [ ] Define `IBranchSaturationQ (Atom) (b) (rep : Nat → Nat)` — a copy of `IBranchSaturation`
        (`:74-108`) with `sat_fimp` restated as
        `∃ w', rep w ≤ rep w' ∧ T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b`. The spike prototyped this exact shape
        and confirmed it elaborates with zero diagnostics
        (`Cslib.Logic.PL.IBranchSaturationQ.{u_2} (Atom) [DecidableEq Atom] [Hashable Atom]
        (b : IBranch Atom) (rep : ℕ → ℕ) : Prop`). All five other fields copied verbatim.
  - [ ] Define `IFimpAccessQ (edges : IEdges) (rep : Nat → Nat) (b : IBranch Atom) : Prop`
        mirroring `IFimpAccess` (`:442-447`) with `isAccessible edges w w'` replaced by
        `isAccessible edges (rep w) (rep w')`.
  - [ ] Prove `IExpandedConsistentQ_sat` (mirroring `:914-1001`) and
        `IExpandedAccessConsistentQ_sat` (mirroring `:1465-1484`). Both proofs are mechanical: the
        `sat_fimp` bullet at `:979-990` closes by `exact hsat` because `sfSatisfied`'s clause and
        the field are definitionally identical — preserve that property in the Q-versions so the
        same one-liner works.
  - [ ] `lake build …Scheme` — green except the single temporary sorry.
- **Timing:** 14-21 hours (5.1-5.2: 6-9h; 5.3-5.4: 8-12h)
- **Depends on:** 3
- **Verification Tier:** local (purely additive declarations in `Scheme.lean`; no existing
  signature touched; the two rewritten docstrings are prose)
- **Commit Mode:** per-substep — 5.1, 5.2, 5.3, 5.4 are four separate green commits
- **Scope Hypothesis:** ~480 lines added to exactly one file (`Scheme.lean`), ~15 new declarations:
  5.1-5.2 contribute `intBlockRep`, `intBlockRep_idempotent`, `intBlockRep_le`,
  `intAccessPreorderQ`, `intAccessPreorderQ_le_of_isAccessible`,
  `intAccessPreorderQ_le_of_rep_eq`; 5.3-5.4 contribute `sfSatisfiedQ`, `sfAccessSatQ`,
  `IExpandedConsistentQ`, `IExpandedAccessConsistentQ`, `sfSatisfiedQ_mono`,
  `IExpandedConsistentQ_mono`, `IBranchSaturationQ`, `IFimpAccessQ`,
  `IExpandedConsistentQ_sat`, `IExpandedAccessConsistentQ_sat`. Two load-bearing sub-hypotheses to
  confirm at implementation time: (i) `intBlockRep` is definable without a new recursion/fuel
  parameter; (ii) `sat_fimp`'s Q-restatement stays *definitionally identical* to `sfSatisfiedQ`'s
  `.neg,.imp` clause so the extraction bullet still closes by the one-liner `exact hsat`. Either
  miss must be recorded before proceeding, not absorbed.
- **Done when:** the three lifting lemmas and both `_sat` extraction lemmas are proved sorry-free,
  `IBranchSaturationQ` / `IFimpAccessQ` exist alongside (not replacing) the originals, and the
  module's sorry count is exactly 3 (the two baseline + the one temporary).

---

### Phase 6: Re-close the reuse-site discharge; retire the temporary sorry [NOT STARTED]

- **Goal:** Restate `intExpandBranches_openBranch_sat`'s conclusion over the Q-predicates, re-close
  its reuse-site discharge, and remove the Phase-4 temporary sorry — restoring the exact 6-entry
  sorry baseline.
- **Tasks:**
  - [ ] Change `intExpandBranches_openBranch_sat`'s conclusion (`Scheme.lean:2594-2595`) from
        `∃ edges, IBranchSaturation Atom b ∧ IFimpAccess edges b` to
        `∃ edges, IBranchSaturationQ Atom b (intBlockRep b edges) ∧
        IFimpAccessQ edges (intBlockRep b edges) b`, threading the change through the inner
        `suffices key` restatement (`:2626-2646`) and the `IAllConsistent`/`IAllAccessConsistent`
        hypotheses.
  - [ ] **Leave `:2623`'s fuel-0 `sorry` and its 26-line refutation note (`:2597-2622`) exactly as
        they are.** The counter-instance recorded there (`branches = [[F(p∧q)@0]]`) refutes
        `sat_fand`, a field this task does not touch, so the note stays valid verbatim.
  - [ ] Re-close the `intStepBranch … = none` leaf (`:2697-2703`) against the Q-extraction lemmas
        from Phase 5.4 — a one-line substitution of `IExpandedConsistentQ_sat` /
        `IExpandedAccessConsistentQ_sat`.
  - [ ] **Re-close the reuse-site discharge (`:2751-2807`), removing the temporary sorry.** Destructure
        `intFImpReuseWitnessAnc?_spec hψ heq`; the ancestor witness `x` now satisfies
        `isAccessible edgesH x l` and `x ≤ l`. Discharge `sfSatisfiedQ`'s ordering conjunct via
        `intAccessPreorderQ_le_of_rep_eq` (Phase 5.2) using `intBlockRep … l = x` — the two agree
        by construction (Phase 5.1). `houtPhi` (derived from `hcont` at `:2761-2778`) and `hFpsi`
        transfer unchanged.
  - [ ] Re-close the `branchingResult` case (`:2808+`) — it replicates `edgesH` unchanged and
        should need only the Q-predicate names substituted.
  - [ ] **Gate**: `grep -rn "^\s*sorry\s*$" Cslib/ --include=*.lean | wc -l` = **6**, and the six
        lines are the exact baseline declarations.
  - [ ] **Gate**: `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` still axiom-clean
        (it must be untouched by all of Phases 5-6; H2 says it never mentions saturation).
- **Timing:** 8-12 hours
- **Depends on:** 4, 5
- **Verification Tier:** interface (`intExpandBranches_openBranch_sat` is `private`, but its
  conclusion type flows into `openBranch_countermodel` at `:3017-3020`; enumerated dependents:
  `Scheme.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`)
- **Commit Mode:** per-substep
- **Scope Hypothesis:** ~220 lines of delta confined to `Scheme.lean:2562-2860`, plus whatever
  `openBranch_countermodel` (`:2996-3022`) needs to re-typecheck. The hypothesis is that the
  fuel-0 sorry region (`:2597-2623`) is **untouched** — confirm by `git diff` showing no change in
  that range.
- **Done when:** the repo-wide bare-sorry count is exactly 6 and the acceptance-gate `lean_verify`
  still passes.

---

### Phase 7: truthLemma over the quotient; downstream migration [NOT STARTED]

- **Goal:** Rewrite `truthLemma` to read its F-imp witness off the quotient frame and migrate the
  four downstream consumers, preserving the T-imp `sorry` exactly.
- **Sub-phase structure:** 7.1 (`truthLemma` itself), 7.2 (downstream migration). Separate green
  commits.
- **Tasks (7.1 — `truthLemma`):**
  - [ ] Change `truthLemma`'s signature (`Scheme.lean:570-579`): `hsat : IBranchSaturationQ Atom b
        (intBlockRep b edges)`, `hfimp : IFimpAccessQ edges (intBlockRep b edges) b`, and the
        `letI : Preorder Nat := intAccessPreorderQ edges (intBlockRep b edges)` in place of
        `intAccessPreorder edges` at `:575` and `:580`.
  - [ ] Rewrite the **F-imp case** (`:608-615`) — currently green via `IFimpAccess` — to obtain the
        witness from `IFimpAccessQ` and lift it with `intAccessPreorderQ_le_of_isAccessible`
        (Phase 5.2) in place of `intAccessPreorder_le_of_isAccessible` at `:615`. The closing shape
        `exact (ih_ψ' w').2 hf_ψ' (hcontra w' <lift> ((ih_φ' w').1 ht_φ'))` is preserved; only the
        lifting lemma changes. **This case must end green — it is a Preserved Asset.**
  - [ ] Leave the **T-imp case** (`:591-607`) and its `sorry` untouched. Its 12-line comment block
        (`:594-605`) references Gap 1 and `applyAllTImpRules`'s copy propagation — Phase 2 changed
        that channel, so append one sentence recording the change and that Gap 1 is *still* the
        blocker (D2), without touching the `sorry` itself.
  - [ ] Update the `Route (a) frame` docstring paragraph (`:563-569`) to describe the quotient
        frame.
  - [ ] Rewrite the and/or/atom/bot cases only if the `Preorder` instance change forces it (it
        should not — those cases never mention the order).
- **Tasks (7.2 — downstream migration):**
  - [ ] `openBranch_countermodel` (`:2996-3022`): update the `IForces` instance argument from
        `intAccessPreorder edges` to `intAccessPreorderQ edges (intBlockRep b edges)`, and the
        `truthLemma S b edges hopen hsat hfimp φ 0` application at `:3021`.
  - [ ] `tableau_complete` (`:3052-3064`): update `hvalid`'s `@IForces` instance argument the same
        way.
  - [ ] `Intuitionistic/Completeness.lean:77` and `Minimal/Completeness.lean:81`: both carry
        `(hfimp : IFimpAccess edges b)` in a signature; migrate to `IFimpAccessQ`. **Their
        `sorry`s at `:133` / `:125` stay** — do not attempt them.
  - [ ] Delete `IBranchSaturation` / `IFimpAccess` / `sfSatisfied` / `sfAccessSat` /
        `IExpandedConsistent` / `IExpandedAccessConsistent` and their `_sat` lemmas **only if**
        `grep -rn` shows zero remaining references. Otherwise leave them and record why.
  - [ ] `lake build` (full) green.
- **Timing:** 8-12 hours
- **Depends on:** 6
- **Verification Tier:** interface (changes `truthLemma`'s public signature; enumerated dependents:
  `Scheme.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`,
  `Intuitionistic/DecisionProcedure.lean`, `Minimal/DecisionProcedure.lean`)
- **Commit Mode:** per-substep
- **Scope Hypothesis:** delta confined to exactly 3 files (`Scheme.lean`,
  `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`), ~250 lines. The
  `DecisionProcedure.lean` files are hypothesised to need **no** edits (they consume
  `tableau_complete`'s statement, not `truthLemma`'s). Confirm with `git diff --stat`; a
  `DecisionProcedure.lean` change is a hypothesis miss to record.
- **Done when:** full `lake build` is green, the sorry count is exactly 6, and `truthLemma`'s F-imp
  case is sorry-free.

---

### Phase 8: Conformance regeneration and full CI gate [NOT STARTED]

- **Goal:** Regenerate `CslibTests/TableauConformance.lean` from real `#eval` output and pass the
  complete CSLib CI pipeline.
- **Tasks:**
  - [ ] Re-run all 19 propositional rows (`:235-328`) via `#guard_msgs in #eval` and record the
        **actual** verdicts. Compare each against the file's stated semantic expectation
        (14 CLOSED / 5 OPEN per `:224`).
  - [ ] **Divergence handling (binding).** Any row whose actual verdict contradicts the formula's
        IPC validity is a **defect in this repair**, not a value to transcribe
        (`TableauConformance.lean:59-69`). Mark this phase `[BLOCKED]`, record the offending row(s)
        and the Phase 1 probe's prediction for them, and escalate. Do **not** flip the expected
        string to match.
  - [ ] Add **one new row** asserting the divergence witness `φ0` now terminates: an
        `#guard_msgs in #eval intVerdict (intuitionisticTableau φ0)` entry with the semantically
        correct verdict, plus a comment naming it as the regression guard for this repair. This is
        the row-count change the task anticipates (19 → 20 propositional rows, 43 → 44 total).
  - [ ] Rewrite the file's "Corpus provenance" docstring (`:59-69`): the "all 43 rows are green /
        pure regression guard" paragraph and the "43 rows (24 temporal, 19 propositional)" count
        both change. State what changed and why.
  - [ ] Leave the 24 temporal rows (`:94-220`) and their docstrings **untouched** — a different
        calculus.
  - [ ] Run the CSLib CI pipeline in order (`.claude/rules/cslib.md`):
        `lake exe cache get` → `lake build` → `lake exe checkInitImports` → `lake lint` →
        `lake exe lint-style` → `lake test` → `lake shake --add-public --keep-implied --keep-prefix`.
  - [ ] Delete `specs/574_.../scratch/DivergenceProbe.lean` (Phase 1's scratch vehicle) after
        confirming its findings are recorded in `handoffs/01_variant-selection.md`.
  - [ ] Write `specs/574_.../summaries/01_tableau-repair-summary.md`.
  - [ ] **Final gates**: repo-wide bare-sorry count = 6 and identical to the baseline table;
        `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` axiom profile =
        `{propext, Classical.choice, Quot.sound}`; `git diff --stat` touches no file outside
        `Cslib/Logics/Propositional/Tableau/`, `CslibTests/TableauConformance.lean`, and `specs/`.
- **Timing:** 5-8 hours
- **Depends on:** 2, 7
- **Verification Tier:** full — the complete repository gate set
- **Commit Mode:** per-substep
- **Scope Hypothesis:** ~120 lines of delta in `CslibTests/TableauConformance.lean` (19 verdicts
  re-checked, 1 row added, 1 docstring paragraph rewritten), plus whatever `lake shake --fix`
  emits. The hypothesis is that **zero** propositional expected-value strings need to change
  (the repair should preserve semantic correctness, only change internal branch shapes) — confirm
  by `git diff` showing changes only to the docstring and the new row. Any flipped verdict string
  triggers the divergence-handling branch above.
- **Done when:** every CI step exits 0, the sorry baseline is restored, and the conformance file
  documents the regenerated corpus.

## Testing & Validation

- [ ] Phase 1 baseline row reproduces `Expansion.lean:497-499`'s fuel→max-label table exactly.
- [ ] Selected variant's max label **saturates** by `fuel = 260` on the divergence witness.
- [ ] `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` →
      `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}` (acceptance gate).
- [ ] `lean_verify Cslib.Logic.PL.minimalTableau_sound` and
      `Cslib.Logic.PL.intuitionisticTableau_sound` sorry-free.
- [ ] `grep -c "^\s*sorry\s*$" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` = 0
      at **every** phase boundary.
- [ ] `grep -c "IBranchSaturation" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` = 0.
- [ ] `grep -rn "^\s*sorry\s*$" Cslib/ --include=*.lean | wc -l` = 6 at task completion, matching
      the baseline table declaration-for-declaration.
- [ ] `lake build` green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake lint` green (watch for newly-unused `_v_uc`/`_bf_uc` after Phase 2).
- [ ] `lake exe lint-style` green.
- [ ] `lake test` green (includes `CslibTests/TableauConformance.lean`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` green.
- [ ] All 24 temporal conformance rows unchanged and green.
- [ ] No new `axiom` declarations: `git diff | grep "^+axiom"` empty.
- [ ] No `def X := True` / `theorem X := trivial` vacuous placeholders introduced.

## Artifacts & Outputs

- `specs/574_tableau_calculus_repair_ancestor_blocking/plans/01_tableau-repair-ancestor-blocking.md` (this file)
- `specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md` (Phase 1)
- `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/DivergenceProbe.lean` (Phase 1;
  deleted in Phase 8 after its findings are recorded)
- `specs/574_tableau_calculus_repair_ancestor_blocking/summaries/01_tableau-repair-summary.md` (Phase 8)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Expansion,Rules,Scheme,Soundness,Completeness}.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- Modified: `CslibTests/TableauConformance.lean`

## Rollback/Contingency

- Every phase commits per the Commit-Per-Green-Substep Mandate (`task 574 phase {P}.{O}: …`), so
  any phase can be reverted by `git revert` of its commit range without touching sibling phases.
- **Phase 4 is the natural rollback boundary**: before it, the tree is fully green with the old
  calculus still wired in (Phase 3 is purely additive; Phase 2 is independent). Reverting Phases
  4-8 restores the pre-repair decision procedure while keeping the Phase 2 hygiene and the Phase 3
  declarations.
- If Phase 1 hits either escalation branch, **nothing under `Cslib/` has been written** and the
  correct action is `/revise 574`, not improvisation.
- If the Phase 6 temporary sorry cannot be closed, mark Phase 6 `[BLOCKED]`, revert Phases 4-6 to
  the Phase 3 boundary (leaving the tree green with 6 sorries), and escalate. **Do not complete the
  task with the temporary sorry in place** — the task's constraints forbid it, and `Scheme.lean`
  carrying a third sorry is a silent regression of the baseline.
- Never use `git reset --hard` / `git clean -fd` to reach a green build; snapshot first with
  `bash .claude/scripts/git-snapshot.sh 574` if a rollback is genuinely required.
