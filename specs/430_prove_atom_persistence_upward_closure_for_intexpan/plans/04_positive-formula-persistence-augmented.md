# Implementation Plan: Task #430 — Positive-Formula Persistence Along the Augmented Relation

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Status**: [IMPLEMENTING]
- **Effort**: Gates (Phases 1-2): ~2 dispatches, gating. Phases 3-8: deliberately not given a firm
  budget — see "On cost estimates" in the Overview.
- **Dependencies**: None blocking at dispatch time. Task 317's Route (a) frame plumbing has
  **landed** (`truthLemma` installs `intAccessPreorder edges`, `Scheme.lean:582/587`; both
  `Completeness.lean` bridges already accept `edges` as an argument) — the coordination gate that
  was plan 03's Phase 1 is discharged. Task 585 (DP-2) is sequenced alongside, not ahead: see
  Planned Strategic Sorries. Task 574's landed work is touched by Phase 3 — see "Cross-task
  coordination with task 574".
- **Research Inputs**:
  - `specs/317_propositional_tableau_completeness/reports/17_timp-continuation-options.md`
    (**newly integrated — the decision record driving this revision**)
  - reports/01_atom-persistence-upward-closure.md (seed)
  - reports/02_team-research.md (team, 4 teammates)
  - reports/03_falsification-spike.md (empirical)
  - `specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md`
    (probe methodology and the V1/V3 measurement Gate A re-runs)
  - `specs/574_tableau_calculus_repair_ancestor_blocking/reports/01_phase6-blocker-resolution.md`
    (the in-repo quotient refutation)
- **Artifacts**: plans/04_positive-formula-persistence-augmented.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md;
  lean4.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This task's scope is **widened** from atom-persistence to **positive-formula persistence along the
augmented accessibility relation**. The statement to prove once and instantiate twice:

```
∀ φ w w', w ≤ w' → T(φ)@w ∈ b → T(φ)@w' ∈ b
```

where `≤` is `intAccessPreorder edges` over the **augmented** edge list returned by
`intExpandBranches_openBranch_sat` (`Scheme.lean:4875` conclusion, witness `augSets` threaded at
`:4863/4869/4905`) — **not** the algorithm's raw `edgeSets`.

**The structural hole.** `propagatePersistence` (`Rules.lean:144-146`, called from `intFImpRule`
at `:163`) copies every positive formula from `w` to a fresh child `w'` **at creation time**. The
hole is the opposite order: positive formulas arriving at `w` **after** `w'` was already minted
are never re-propagated. That single hole surfaces as sorries at two formula shapes:

| φ shape | Manifestation | Sorry |
|---|---|---|
| `φ = atom p` | late `T(atom p)@w` never reaches an older child → monotonicity bridge | DP-3 (`Intuitionistic/Completeness.lean:140`), DP-4 (`Minimal/Completeness.lean:128`) |
| `φ = φ'→ψ'` | copy never arrives at `w'`, so reflexive `sat_timp` cannot fire → Gap 1 | DP-5 (`Scheme.lean:633`) |

**Why one task, not two** (all from report 17):
- **F6**: closing either sorry alone has **zero public payoff**. Both public completeness theorems
  carry independent sorries and both delegate to `truthLemma`. Only the union yields a sorry-free
  public theorem. A T-imp-only or atom-only phase is therefore excluded (see Reasoned Exclusions).
- **F3**: `truthLemma`'s frame is `intAccessPreorder` over the **augmented** edge list, deliberately
  decoupled from the algorithm's raw `edges` (`Scheme.lean:544-546`, `:771-781`). Any copy channel
  filters on raw edges and is **strictly weaker**. No algorithm-level, shape-specific patch can
  close it; the fix must be at the **invariant** level, where a general statement costs no more than
  an atom-only one.
- The unification is **pre-recorded in-source**, not invented here: `Scheme.lean:431-434` already
  recommends stating monotonicity "as a NEW field/hypothesis threaded alongside `sat_timp`", and
  `:413-420` records the same co-inductive diagnosis. The two `Completeness.lean` bridge comments
  (`:137`, `:125-127`) already name DP-5 as the same fact at the other shape.

**Structure: two hard gates, then the build-out.** Gate B (Phase 2) is the option-killer and comes
before any calculus change; it is statable against the tree exactly as it stands. If Gate B fails,
**permanent deferral becomes the terminal answer for all three sorries at once**, and escalation to
Option 2 (quotient) is prohibited — see Rollback/Contingency.

**On cost estimates.** Report 17's own 600-1200 line figure is marked **low confidence** by its
author (anchored on the ~480-line quotient stack and a ~92-line prototype as reference class). It
is **not** presented here as a budget, and no phase below is sized against it. Phase-level sizing
uses per-phase Scope Hypotheses instead, confirmed at implementation time.

### Research Integration

Newly integrated in this revision:

- **`317/reports/17_timp-continuation-options.md`** — the decision record. Verdict: Option 1
  (bounded copy channel) **GO** in reshaped form, merged into this task; Option 2 (quotient)
  **NO-GO** with two independent refutations; Option 3 (deferral) is correct bookkeeping but
  decides nothing technical. Findings consumed: **F1** (the copy channel is termination-orthogonal
  under ancestor blocking — *measured*, 574 Table 3, V1 vs V3 reach the identical saturated branch
  at `len=219, maxLabel=21, distinctLabels=22`); **F2** (reinstatement is a mechanical revert of
  `a70187dd`'s three hunks, all green at the parent commit); **F3** (raw vs. augmented edges — the
  decisive, previously unrecorded finding, and the reason for Gate B); **F5** (exactly what
  `propagatePersistence` gives and what is missing); **F6** (no public payoff from closing either
  sorry alone).
- **`574/handoffs/01_variant-selection.md`** — the probe methodology Gate A re-runs (scratch-only
  `#eval` harness, fuel ladder, `worldStats` adapter, conformance-row check), plus the true-control
  fidelity discipline that validated it.

Confidence levels from report 17 are respected verbatim, including its `[UNVERIFIED]` markers —
see Risks. Report 17's own adversarial pass (H4) refuted its author's first conclusion (that a bare
revert closes Gap 1); Gate B exists because of that refutation, not in spite of it.

### Preserved from plan 03

- Team S2's finding that **one** generic lemma covers both bridges (atoms and `⊥` are the same
  `b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w)` shape) — carried into
  Phase 7 as the two-corollary packaging, now as an instantiation of the general persistence
  statement rather than a standalone fact.
- Placement guidance: standalone corollaries, **not** new `IntMinScheme` fields.
- The CI/verification phase, unchanged in substance (Phase 8).
- The Route C (containment preorder) and Approach B (`≤`-on-ℕ) exclusions, both empirically
  refuted by report 03 — restated in Reasoned Exclusions so they are not re-litigated.

**Discharged:** plan 03's Phase 1 coordination gate ("has 317 Wave A landed?") is now answered YES
by direct read of the tree, and does not reappear as a phase.

### Cross-task coordination with task 574

Phase 3 reverts `a70187dd`, which is **task 574's settled work**. This is stated, not assumed away.
Report 17's assessment: it does **not** re-open 574's design. Task 574 settled *termination*
(ancestor blocking is the mechanism) and *the reuse-witness admissibility route* (loop-back edges,
not quotient). 574's own D3 verdict records the copy channel as termination-**orthogonal**, and
`a70187dd`'s own commit message describes the removal as "orthogonal hygiene, not the termination
mechanism", explicitly scoped as not addressing Gap 1. This is therefore a **coordinated
follow-up** with 574 cross-referenced — and Gate A (Phase 1) is precisely what makes it
non-speculative rather than a bet. Phase 3 must not proceed on the strength of this paragraph
alone; it proceeds on Gate A's measurement.

## Goals & Non-Goals

**Goals**:
- Prove positive-formula persistence along `intAccessPreorder augEdges` **once**, as an invariant
  threaded through `intExpandBranches_openBranch_sat` and exported in its conclusion.
- Instantiate it at `φ = φ'→ψ'` to close DP-5 (`Scheme.lean:633`).
- Instantiate it at `φ = atom p` (and `φ = .bot`) to close DP-3
  (`Intuitionistic/Completeness.lean:140`) and DP-4 (`Minimal/Completeness.lean:128`).
- Net effect: both public completeness theorems (`intuitionisticTableau_complete`,
  `minimalTableau_complete`) become sorry-free, modulo DP-2 (task 585).
- No new `axiom`s; no statement weakened to dodge a gap; full CI green.

**Non-Goals**:
- Do **not** touch DP-2 (`intFreshMint_preserves_nw`, `Scheme.lean:2605`) — task 585 territory.
- Do **not** rebuild a quotient / blocking-frame reconstruction (Option 2) under any circumstance,
  including as an escalation after a Gate B failure. See Reasoned Exclusions.
- Do **not** re-open task 574's termination design (ancestor blocking, loop-back reuse witness).
  Phase 3 restores an orthogonal channel; it changes no blocking or reuse logic.
- Do **not** dispatch a T-imp-only or atom-only phase (F6: zero public payoff either way).
- Do **not** pursue Route C (containment preorder) or Approach B (`≤`-on-ℕ upward closure) — both
  empirically refuted by reports 02/03.
- Do **not** write to `Cslib/` or `CslibTests/` during Phases 1-2. Both gates are scratch-only.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **The `Sfor`-containment does not survive to the final branch.** Report 17 F3 flags this `[UNVERIFIED]`: containment is established against `bPers` (the branch at blocking time), not the final `b`, and is consumed locally at the discharge site rather than exported. **The single largest unretired risk; it can kill the approach.** | Critical | Medium | Gate B (Phase 2), run first, against the tree as it stands, before any calculus change. Prototype in `scratch/`, `lake build` green, then decide. Failure ⇒ terminal deferral (Rollback/Contingency), NOT escalation. |
| **V4 (copy every positive formula) diverges.** Report 17 H4 row 7 refuted its own author's "positives obviously terminate" reasoning: positives feed `intApplyRuleFull`'s `.pos,.imp` BETA arm, which yields a world-minting `F(antecedent)@w'` — the original divergence feed. V4 is **not** assumed safe. | High | Medium | Gate A (Phase 1) measures V1 and V4 side by side. V1 (self-copy reinstated verbatim) is the pre-measured fallback: 574 Table 3 recorded it terminating at `maxLabel=21` across fuel 120/160/200/260. |
| Reverting `a70187dd` breaks `Soundness.lean`'s acceptance gate | High | Low | The pre-removal versions were green at `a70187dd^`. Re-verify `intExpandBranches_closed_unsat` sorry-free and axiom-clean at each phase boundary, as 574 did. Phase 3 is `Commit Mode: atomic-batch` precisely because the three files must move together. |
| `TableauConformance.lean`'s propositional rows shift under V1/V4 | High | Low | Gate A checks every propositional row before any `Cslib/` write; 574 measured zero regression for V1. |
| DP-2 (task 585) still gates `applyPersistenceFixpoint_genuine_of_count_le_fuel`'s `hb` premise in practice | Medium | High | Sequence 585 alongside or ahead of Phase 6/7; the fixpoint lemma itself is already sorry-free. DP-2 is recorded as a planned strategic sorry owned elsewhere, not silently absorbed. |
| Territory collision on `Scheme.lean` with a concurrently live 317/574/585 phase | High | Medium | `file_scope` is populated in this task's metadata so the orchestrator's footprint gate can serialize. Phases 4-6 all write `Scheme.lean` and are declared strictly sequential for that reason. |
| Report 17's C&Z citation rests on visibly degraded OCR | Low | Medium | The Option 2 no-go does not depend on it alone (the in-repo refutation is independent). Re-check against a physical copy before the citation appears in any Lean docstring. |
| Report 13's "no world bound of any size exists" is read as still binding | Medium | Medium | It is **superseded, not contradicted**: it measured the *pre-repair* calculus. Post-repair `WBound φ0` (`Scheme.lean:1692`) / `intUniverseExt` (`:1721`) exist and `applyPersistenceFixpoint_genuine_of_count_le_fuel` is landed sorry-free. Do not let a stale reading shape any phase. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |
| 5 | 6, 7 | 5 |
| 6 | 8 | 6, 7 |

Phases within the same wave can execute in parallel.

**Territory note for wave 1**: Phases 1 and 2 write only to
`specs/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/` and own disjoint files
there (Phase 1: `VariantProbe*.lean`; Phase 2: `PersistPrototype.lean`). Neither writes `Cslib/` or
`CslibTests/`. **If only one dispatch is available, run Phase 2 first** — it is the option-killer,
and a Gate B failure makes Phase 1's compute spend worthless.

### Phase 1: Gate A — variant selection probe (V1 vs V4) [COMPLETED]

- **Goal:** Determine, by measurement, which copy-channel form to reinstate: **V1** (the self-copy
  reinstated verbatim, as removed by `a70187dd`) or **V4** (generalize the channel to copy *every*
  positive formula, not just `T(φ→ψ)`, to accessible worlds lacking it). V4 is the higher-value
  target — it makes the invariant hold at all formula shapes in one step — but is explicitly not
  assumed safe.
- **Tasks:**
  - [ ] Re-create task 574's probe harness in
        `specs/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/`, following
        `574/handoffs/01_variant-selection.md`'s methodology: local copies of
        `applyAllTImpRules` / `intFImpReuseWitness?` wired into a local copy of
        `intExpandBranches`'s `go` loop, called with an explicit fuel argument; `worldStats`
        adapter reporting `len` / `maxLabel` / `distinctLabels`.
  - [ ] Reproduce the **true control** first (exact copy of the library's current
        `intFImpReuseWitness?`) and confirm it matches the post-Phase-6 tree's own behaviour before
        trusting any variant's absolute numbers. 574's harness-fidelity correction is a required
        step, not an optional one.
  - [ ] Measure **V1** and **V4** against witness `φ0` on the fuel ladder, at minimum through
        `fuel = 120`, with spot checks at 160/200/260 for any variant whose termination status the
        trimmed ladder leaves ambiguous.
  - [ ] Check **every** `CslibTests/TableauConformance.lean` propositional row against both variants
        (read-only against that file — do not edit it).
  - [ ] Record the decision: V4 if it saturates and all conformance rows match; otherwise fall back
        to V1. If **neither** terminates, record the result and mark the phase `[BLOCKED]` — do not
        proceed to Phase 3 on an unmeasured channel.
- **Timing:** ~1 dispatch
- **Depends on:** none
- **Verification Tier:** local
- **Scope Hypothesis:** the probe reproduces 574's control exactly and V1 reproduces its recorded
  `maxLabel=21` saturation. Confirm by running the control before the variants and comparing
  against `574/handoffs/01` Tables 2-3. A control mismatch invalidates the variant numbers and must
  be resolved before the decision is recorded.
- **Files to modify:** `specs/.../430.../scratch/VariantProbe*.lean` (new). **Zero** writes to
  `Cslib/` or `CslibTests/` — confirm with `git status --short Cslib/ CslibTests/` (must be empty).

### Phase 2: Gate B — persistence prototype (GATING, no algorithm change) [COMPLETED]

- **Goal:** Decide whether positive-formula persistence is provable along the augmented relation
  **at all**, before any calculus change is made. This is the option-killer.
- **Tasks:**
  - [ ] Without changing any algorithm, prototype in `scratch/`:
        ```
        ∀ φ w w', isAccessible augEdges w w' = true → T(φ)@w ∈ b → T(φ)@w' ∈ b
        ```
        restricted to a **single loop-back hop** `(x, l)`, using the `Sfor`-containment available at
        the blocking site (`Scheme.lean:742-744`, `:771-781`).
  - [ ] Confront the recorded risk head-on: the containment is established against `bPers` (the
        branch at blocking time), **not** the final branch `b`, and is consumed locally at the
        discharge site rather than exported. Determine whether it survives to the final branch.
        This is the specific question the phase exists to answer.
  - [ ] Follow 574's own successful methodology: prototype in `scratch/`, `lake build` green, then
        decide. A prototype that does not build is not a result.
  - [ ] Record an explicit verdict: **PASS** (containment survives; proceed to Phase 3) or **FAIL**
        (it does not; see Rollback/Contingency — terminal deferral, no escalation).
- **Timing:** ~1 dispatch
- **Depends on:** none
- **Verification Tier:** local
- **Scope Hypothesis:** the single-hop restriction is sufficient to decide the general case, on the
  grounds that the augmented list differs from the raw list only by loop-back edges and multi-hop
  reachability is their reflexive-transitive closure. Confirm at implementation time by checking
  that the prototype's hop lemma composes under `Relation.ReflTransGen`; if it does not, the phase's
  verdict must say so rather than claiming a general result from a single-hop proof.
- **Files to modify:** `specs/.../430.../scratch/PersistPrototype.lean` (new). Zero writes to
  `Cslib/`.

### Phase 3: Reinstate the copy channel (revert `a70187dd`'s three hunks) [COMPLETED]

- **Goal:** Restore the copy channel in the form Gate A selected, returning the tree to a green
  build with the channel present.
- **Tasks:**
  - [x] `Expansion.lean`: restore the `accessibleWorlds` / `copies` / `combined` block (a literal
        restoration for V1; the generalized filter for V4) plus the docstring the removal rewrote.
        *(altered: implemented as V4's generalized `genCopies` channel — copies every positive
        formula, not just `T(φ→ψ)` — as a separate `let` appended alongside `newForms`, per Gate
        A's selection, rather than a literal `a70187dd^` restoration)*
  - [x] `Scheme.lean`: restore the `rfl`-level pattern-match repairs the removal made —
        `ILabelBound_applyAllTImpRules`, `applyAllTImpRules_subset`, `applyAllTImpRules_count_drop`,
        `applyPersistenceFixpoint_genuine_of_count_le_fuel` — and restore the helper
        `applyAllTImpRules_copy_notMem`, which the diff preserves in full. *(altered: also updated
        `ILabelBoundStrict_applyAllTImpRules` and `applyAllTImpRules_subset_ext`, two lemmas added
        after `a70187dd` that pattern-matched the same copy-free body and were not in the original
        diff's scope; generalized `applyAllTImpRules_copy_notMem` to an arbitrary formula `χ`
        rather than `φ → ψ` specifically; added a new shared helper
        `applyAllTImpRules_eq_self_of_length_eq` to avoid tripling the zero-both-channels
        argument across the three call sites)*
  - [x] `Soundness.lean`: restore `applyAllTImpRules_sat` and `freshAbove_applyAllTImpRules`.
        *(altered: both proofs restructured for the 3-way append (`b`, ψ-consequence
        `newForms.flatten`, generalized `genCopies.flatten`) and the new copy case is closed via
        `iforces_persistence` at the general formula, not the `imp`-specific `iforces_persistence`
        application the old removed code used)*
  - [x] Re-verify `intExpandBranches_closed_unsat` is sorry-free and axiom-clean; confirm
        `Soundness.lean` remains sorry-free. *(confirmed: `lean_verify` reports
        `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}`; `Soundness.lean`
        has zero bare sorries)*
  - [x] Re-run the `TableauConformance.lean` propositional rows against the real library (not the
        probe harness) and confirm they match Gate A's measurement. *(confirmed: `lake test`
        builds `CslibTests.TableauConformance` green with the reinstated channel live)*
- **Verification results:** `lake build` (full project) green; `lake exe checkInitImports` clean;
  `lake lint` shows zero new warnings in the three touched files (144 pre-existing repo-wide
  warnings, all outside this task's territory); `lake exe lint-style` clean; `lake shake` shows no
  new findings in the touched files; `lake test` green including `TableauConformance`. Repo-wide
  bare-sorry count is 5 (DP-3 `Completeness.lean:140`, DP-4 `Minimal/Completeness.lean:128`, DP-5
  `Scheme.lean:727`, plus two unrelated sorries in Bimodal/Modal files outside this task's scope).
  DP-2 does not appear — task 585 retired it before this dispatch, confirmed by direct grep, not
  touched here.
- **Timing:** ~1 dispatch
- **Depends on:** 1, 2
- **Verification Tier:** full
- **Commit Mode:** atomic-batch
- **Scope Hypothesis:** the revert is mechanical and confined to exactly the three files
  `a70187dd` touched, all of which were green at its parent commit. Confirm at implementation time
  with `git show --stat a70187dd` and by taking `git show a70187dd^:<path>` as the reference for
  each restored hunk. If the intervening tree has diverged such that a hunk no longer applies
  cleanly, record the divergence rather than hand-reconstructing it silently.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`,
  `.../Intuitionistic/Scheme.lean`, `.../Intuitionistic/Soundness.lean`. The three move together:
  intermediate per-file states are expected red and must not be committed.

### Phase 4: Copy-completeness at a genuine `applyAllTImpRules` fixpoint [NOT STARTED]

- **Goal:** Prove that at a genuine `applyAllTImpRules` fixpoint, the copy channel has in fact
  delivered every positive formula it owes along the **raw** edges.
- **Tasks:**
  - [ ] Follow the `filterMap` / `countP` argument the STOP-gate note already sketches at
        `Scheme.lean:508-513`, mirroring the landed `applyAllTImpRules_count_drop`.
  - [ ] State the fixpoint-level copy-completeness lemma over raw edges and prove it sorry-free.
  - [ ] Confirm the lemma composes with `applyPersistenceFixpoint_genuine_of_count_le_fuel`
        (`Scheme.lean`, landed sorry-free) — this phase supplies the copy side of the pairing whose
        fuel side is already retired.
- **Timing:** ~1 dispatch
- **Depends on:** 3
- **Verification Tier:** local
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 5: Thread and export the persistence invariant [NOT STARTED]

- **Goal:** Carry the containment/persistence fact through the forward induction and expose it in
  `intExpandBranches_openBranch_sat`'s conclusion, so `truthLemma` and both bridges can consume it.
- **Tasks:**
  - [ ] Define the invariant predicate (proposed name `IPosPersist edges b`; the implementer
        confirms or renames per CSLib conventions) capturing
        `∀ φ w w', isAccessible edges w w' = true → T(φ)@w ∈ b → T(φ)@w' ∈ b`.
  - [ ] Thread it alongside `IAllAccessConsistent` through `intExpandBranches_openBranch_sat`'s
        `key` induction (the parallel-list invariant pattern already in use — `Scheme.lean:1348`ff
        for `IAllAccessConsistent`, `:4863/4869/4905` for the `augSets` threading). Reuse that
        pattern; do not invent a parallel mechanism.
  - [ ] Extend the conclusion from `∃ edges, IBranchSaturation Atom b ∧ IFimpAccess edges b`
        (`Scheme.lean:4875`) to also carry the persistence conjunct, and update the two call sites
        (`Scheme.lean:5598`ff and any other `obtain ⟨edges, hsat, hfimp⟩` destructuring).
  - [ ] Provide the `Relation.ReflTransGen` lift from the one-step form to the
        `intAccessPreorder edges` order, reusing `intAccessPreorder_le_of_isAccessible`
        (`Scheme.lean:276`) rather than redefining it.
- **Timing:** ~1-2 dispatches
- **Depends on:** 4
- **Verification Tier:** interface
- **Scope Hypothesis:** the conclusion change breaks exactly the destructuring call sites of
  `intExpandBranches_openBranch_sat`, which is `private` and has a small, enumerable consumer set.
  Confirm at implementation time with `grep -n "intExpandBranches_openBranch_sat" Scheme.lean` and
  fix every hit; if the count exceeds the enumerated set, record it.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 6: Discharge the T-implication case (DP-5) [NOT STARTED]

- **Goal:** Close `Scheme.lean:633` sorry-free by instantiating the exported invariant at
  `φ = φ'→ψ'`, letting the reflexive `sat_timp` field (`Scheme.lean:115-121`) fire at `w'`.
- **Tasks:**
  - [ ] Consume the persistence conjunct in `truthLemma`'s `imp` case to obtain `T(φ'→ψ')@w'` from
        `T(φ'→ψ')@w` and `w ≤ w'` at the `intAccessPreorder edges` frame.
  - [ ] Fire `sat_timp` at `w'`; close the case via `ih_φ'` / `ih_ψ'`.
  - [ ] Replace the `sorry`; `lean_goal` at each step to confirm closure.
  - [ ] Update the surrounding STOP-gate docstrings (`Scheme.lean:395-436`, `:461-560`) to record
        that Gap 1 is closed, replacing the deferral text rather than leaving stale prose.
  - [ ] `lean_verify` `truthLemma`: axiom-clean, no `sorryAx`.
- **Timing:** ~1 dispatch
- **Depends on:** 5
- **Verification Tier:** interface
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 7: Instantiate at atoms — discharge DP-3 and DP-4 [NOT STARTED]

- **Goal:** Close `Intuitionistic/Completeness.lean:140` and `Minimal/Completeness.lean:128`
  sorry-free by instantiating the same exported invariant at `φ = atom p` (and `φ = .bot`).
- **Tasks:**
  - [ ] Package the upward-closure fact **once**, order-agnostically, as a standalone corollary
        parametric in the formula slot (team S2: atoms and `⊥` are the same
        `b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w)` shape). Do **not**
        add fields to `IntMinScheme`.
  - [ ] Derive `intExtractValuation_upward_closed` (φ := `.atom p`) and
        `minBranchBotForces_upward_closed` (φ := `.bot`) as one-line specializations.
  - [ ] `Intuitionistic/Completeness.lean`: instantiate `IValid φ` at `World = ℕ`,
        `Preorder := intAccessPreorder edges`, `val := intExtractValuation b`, supplying the
        upward-closure corollary; reconcile `modelBot b = fun _ => False`; replace the `sorry`.
  - [ ] `Minimal/Completeness.lean`: instantiate `MValid φ` with `botForces := minBranchBotForces b`,
        supplying both corollaries for `MValid`'s two upward-closure obligations; replace the
        `sorry`.
  - [ ] Update both files' "Notes on sorry" module sections (`:39-47` / `:43-47`) — they currently
        describe the deferral.
  - [ ] `lean_verify` both public theorems: axiom-clean, no `sorryAx`.
- **Timing:** ~1 dispatch
- **Depends on:** 5
- **Verification Tier:** interface
- **Scope Hypothesis:** the corollary can live in the `Completeness.lean` files or a small new
  module without needing private access to `Scheme.lean` internals. Confirm at implementation time;
  if privacy forces it into `Scheme.lean`, that edit must be serialized behind Phase 6 (same file,
  single writer) — which converts wave 5 from parallel to sequential. Record the conversion rather
  than editing concurrently.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`,
  `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (fallback:
  `.../Intuitionistic/Scheme.lean` for the shared corollary, serialized behind Phase 6).

### Phase 8: CI and final verification [NOT STARTED]

- **Goal:** Confirm all three sorries are gone with no regressions and full CI green.
- **Tasks:**
  - [ ] `grep -n sorry` on both `Completeness.lean` files returns no bare `sorry`.
  - [ ] `grep -n "^  sorry"` / bare-sorry census on `Scheme.lean`: DP-5 gone, DP-2 (`:2605`) is the
        only remaining bare sorry in this task's territory.
  - [ ] `lean_verify` on `intuitionisticTableau_complete`, `minimalTableau_complete`, `truthLemma`,
        and `intExpandBranches_closed_unsat`: no new axioms, no `sorryAx` beyond DP-2's reach.
  - [ ] Full CI pipeline: `lake build`; `lake exe checkInitImports`; `lake exe lint-style`;
        `lake shake --add-public --keep-implied --keep-prefix`; `lake test`.
  - [ ] `CslibTests/TableauConformance.lean` fully green.
  - [ ] Confirm no stray scratch modules under `Cslib/` (`Scratch430.lean` and equivalents absent).
- **Timing:** ~30-45 min
- **Depends on:** 6, 7
- **Verification Tier:** full
- **Files to modify:** none (verification only; lint/shake auto-fixes if flagged).

## Planned Strategic Sorries

| Division Point | File / Line / Statement | Assumption | Why Deferred | Follow-Up Task |
|-----------------|--------------------------|------------|---------------|----------------|
| DP-2 fresh-mint `hNW` preservation | `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:2605` — `intFreshMint_preserves_nw` (line current at `8a36eba9`; re-locate by content if shifted) | The creation-count invariant holds: a fresh mint preserves `nw + 1 ≤ WBound φ0` | Owned by task 585, not this task. It gates `applyPersistenceFixpoint_genuine_of_count_le_fuel`'s `hb` premise in practice but the fixpoint lemma itself is already sorry-free, so it does not block any phase above | 585 |
| Gate B failure ⇒ terminal deferral of DP-3/DP-4/DP-5 | `Scheme.lean:633`; `Intuitionistic/Completeness.lean:140`; `Minimal/Completeness.lean:128` | None — this row records the *absence* of a viable route, not an assumed fact | Conditional on Phase 2 returning FAIL. If the `Sfor`-containment does not survive to the final branch, no route to the invariant remains; permanent deferral becomes the terminal answer for all three at once. Escalation to Option 2 is explicitly prohibited | none (terminal — see Rollback/Contingency) |

**Note on follow-up tokens**: no `{{FOLLOWUP:i}}` placeholders appear above because this revision
creates no new follow-up tasks. Task 585 already exists and is the real, allocated owner of DP-2;
the second row is a terminal-deferral contingency with no follow-up by construction.

## Reasoned Exclusions

Recorded pre-emptively at plan time (permitted by plan-format.md's "Relationship to Scope
Hypothesis"). No phase above currently carries `[COMPLETED WITH EXCLUSIONS]`; this section exists so
these decisions are not re-litigated mid-implementation.

| Item | Reason | Evidence |
|------|--------|----------|
| **Option 2: quotient / blocking-frame reconstruction** | **NO-GO.** Two independent refutations. (1) In-repo: task 574 built the ~480-line `intBlockRep` / `intAccessPreorderQ` stack, then refuted and deleted it — `intBlockRep` is a function of the *final* branch and is not monotone under branch growth, so it cannot carry `intExpandBranches_openBranch_sat`'s **forward** induction. (2) Published: a filtration relation in the interval `S̲ ⊆ S ⊆ S̄` may be nontransitive even when `R` is transitive, and not all such `S` give rise to filtrations of intuitionistic models — exactly the assumption an `intAccessPreorderQ` pullback rests on. It also does not *sidestep* the `Force → T(_)@w' ∈ b` gap, it **relocates** it. | `574/reports/01_phase6-blocker-resolution.md` (§Executive Verdict, §Secondary Defect); 574 phase commits `b70eadc0`…`1ebf52ad` (built) and `175f7ea6` (deleted, grep-confirmed zero external references); `ChagrovZakharyaschev1997` §The Filtration Method, read verbatim in report 17 (`chunk_0246.md:63-65`) — OCR visibly degraded, but the in-repo refutation is independent of it. |
| **The objection "the quotient refutation was about `openBranch_sat`, so it may not bind `truthLemma`"** | **The objection fails.** `truthLemma` itself runs over the final branch, so a quotient *could* be defined there — but `truthLemma` consumes `IBranchSaturation` / `IFimpAccess`, both produced by the forward induction, which is precisely where `intBlockRep`'s non-monotonicity bites. | Report 17 adversarial pass (H4) row 3; `Scheme.lean:4875` (the conclusion `truthLemma` consumes). |
| **A T-imp-only phase** | Excluded per F6: zero public payoff. Both public completeness theorems carry independent sorries and both delegate to `truthLemma`; discharging Gap 1 alone moves no public theorem from sorry-carrying to sorry-free. | Report 17 F6; `Intuitionistic/Completeness.lean:140`, `Minimal/Completeness.lean:128` (both still `sorry` at `8a36eba9`). |
| **An atom-only phase (the task's original scope)** | Same reason, mirrored. Closing DP-3/DP-4 without DP-5 leaves `truthLemma` sorry-carrying, which both public theorems delegate to. F3 additionally shows the atom-only statement costs no less to prove than the general one, since the obstruction is at the invariant level, not the formula shape. | Report 17 F3, F6; `Scheme.lean:431-434` (in-source recommendation to state monotonicity generally, alongside `sat_timp`). |
| **Route C (containment preorder) and Approach B (`≤`-on-ℕ upward closure)** | Both empirically refuted before this revision. Raw edge upward-closure FAILS (phi4); Route C containment REFUTED at imp-F (phi4); the raw valuation is provably not upward-closed under `≤`-on-ℕ (sibling worlds). | reports/03_falsification-spike.md (EXPERIMENT 1a and the imp-F refutation); reports/02_team-research.md S1. |
| **Report 13's "no world bound of any size exists"** | **Superseded, not contradicted.** Report 13 measured the *pre-repair* calculus and is correct about it. Post-repair, `WBound φ0` and `intUniverseExt` exist and `applyPersistenceFixpoint_genuine_of_count_le_fuel` is landed sorry-free over them. Do not let a stale reading of report 13 shape any phase. | Report 17 F4 and H4 row 4; `Scheme.lean:1692` (`WBound`), `:1721` (`intUniverseExt`), `:3495`-region (the landed fixpoint lemma). |
| **Report 17's 600-1200 line cost estimate as a budget** | The author marks it **low confidence**, anchored on the ~480-line quotient stack and a ~92-line prototype as reference class. It is recorded as context, never as a firm budget, and no phase is sized against it. | Report 17 F8 and its Confidence Levels section ("*Low, flagged not asserted:* F8's 600-1200 line estimate"). |

## Testing & Validation

- [ ] Gate A: control reproduces the library's current behaviour exactly; V1 and/or V4 saturate on
      `φ0` at `fuel ≥ 120`; every `TableauConformance.lean` propositional row matches.
- [ ] Gate B: prototype builds green in `scratch/`; explicit PASS/FAIL verdict recorded.
- [ ] `git status --short Cslib/ CslibTests/` empty at the end of Phases 1 and 2.
- [ ] `grep -n sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` → no bare
      `sorry`.
- [ ] `grep -n sorry Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` → no bare `sorry`.
- [ ] `Scheme.lean:633` DP-5 closed; `Scheme.lean:2605` DP-2 remains, unchanged and untouched.
- [ ] `lean_verify` on `intuitionisticTableau_complete`, `minimalTableau_complete`, `truthLemma`,
      `intExpandBranches_closed_unsat`: no new axioms.
- [ ] `Soundness.lean` remains sorry-free; `intExpandBranches_closed_unsat` axiom-clean at every
      phase boundary from Phase 3 onward.
- [ ] Full CI: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`, `lake test`.
- [ ] Docstrings updated, not left stale: `Scheme.lean`'s STOP-gate note and both
      `Completeness.lean` "Notes on sorry" sections reflect the closed state.

## Artifacts & Outputs

- plans/04_positive-formula-persistence-augmented.md (this file)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/VariantProbe*.lean`
  (Gate A, scratch only)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/PersistPrototype.lean`
  (Gate B, scratch only)
- handoffs/01_gate-a-variant-selection.md and handoffs/02_gate-b-verdict.md (gate verdicts, so a
  later dispatch does not re-run the probes)
- Edited: `Intuitionistic/Expansion.lean`, `Intuitionistic/Scheme.lean`,
  `Intuitionistic/Soundness.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`
- summaries/04_positive-formula-persistence-augmented-summary.md (on implementation)

## Rollback/Contingency

- **Gate A returns "neither V1 nor V4 terminates"**: mark Phase 1 `[BLOCKED]`, record the
  measurement, do not proceed to Phase 3. No `Cslib/` writes have been made, so there is nothing to
  roll back.
- **Gate B returns FAIL (the containment does not survive to the final branch)**: **the whole
  approach collapses.** Permanent deferral becomes the terminal answer for DP-3, DP-4 and DP-5 at
  once. Record this verdict in `handoffs/02_gate-b-verdict.md`, re-annotate all three sorries as
  terminally deferred with the Gate B evidence, and mark the task `[BLOCKED]`. **Do NOT escalate to
  Option 2** — the quotient route is refuted twice over (see Reasoned Exclusions) and a Gate B
  failure is not new evidence in its favour. No `Cslib/` writes have been made at that point.
- **Phase 3 revert breaks the build and cannot be repaired within the dispatch**: the phase is
  `atomic-batch`; nothing is committed until the batch is green, so `git checkout` of the three
  files to HEAD restores the pre-phase state cleanly. Record which hunk failed to apply.
- **A later proof phase fails**: revert that file to the last green commit. Phases 4-6 are strictly
  sequential on `Scheme.lean`, so at most one file is in flight at a time.
- **Territory conflict detected mid-flight** (317, 574, or 585 writing `Scheme.lean`): stop, yield
  the file to the single writer, and re-synchronize at the next phase boundary. `file_scope` is
  populated in this task's metadata so the orchestrator can serialize this in advance.
