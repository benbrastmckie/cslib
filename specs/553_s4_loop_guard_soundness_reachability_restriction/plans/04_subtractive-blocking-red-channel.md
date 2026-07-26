# Implementation Plan: Massacci-Style Subtractive Blocking with a Completeness-Only Redirect Channel (v4)

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Status**: [IMPLEMENTING]
- **Effort**: 32-40 hours (12 phases; two of them are front-loaded decision gates that may
  terminate the route)
- **Dependencies**: 535 (completeness-line task; its landed keyed completeness results are inputs)
- **Research Inputs**:
  - `reports/04_massacci-subtractive-blocking-priced.md` (**primary**; route (3) priced and
    recommended, with the three new probes)
  - `reports/03_soundness-strength-necessity.md` (§2.3, §4.2, §7.2 — invariant-strength census;
    its route (2′) recommendation is *reversed* by report 04 and is not re-argued here)
  - `reports/02_redirect-inertness-divergence-audit.md` (§3.1 row 6, §5.1 — the two landed
    refutations that kill route (2′)'s proof strategies)
  - `reports/01_s4-keyed-guard-soundness-falsified.md` (the machine-checked `cex`; the
    reachability restriction's rejection)
  - `plans/03_ancestor-only-blocking.md` (`#### Phase 1 Measurements` — inherited;
    `#### Phase 2 Verdict` — the landed refutation of the ancestor route)
  - Literature: `Massacci2000`, BibKey verified at `references.bib:1010`; chunks
    `chunk_0029.md`-`chunk_0031.md`, `chunk_0065.md` (read in this planning run — see
    Source-to-Implementation Mapping)
- **Artifacts**: `plans/04_subtractive-blocking-red-channel.md` (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/plan-compliance.md`
  - `.claude/rules/cslib.md`
  - `.claude/rules/lean4.md`
- **Type**: cslib
- **Lean Intent**: true
- **Plan version**: 4 (supersedes v3 `03_ancestor-only-blocking.md`, stamped **[ABANDONED]** with a
  `Superseded by` pointer to this file, per the convention v1/v2 already use; v3's Phase 1
  `[COMPLETED]` status and its four measurements are preserved verbatim and inherited here)

---

## Overview

The keyed S4 loop guard `blockingWorldS4Keyed` (`LoopChecking.lean:506-511`) licenses a redirect
edge `src → wBlock` into the same `Accessibility` structure that `branchSatisfiableIn`'s edge
conjunct quantifies over (`FrameSoundness.lean:113`). That single design decision is the source of
every failure this task has recorded: it converts a completeness-side model-construction artifact
into a per-step soundness obligation against an existentially arbitrary witness model. This plan
executes **route (3)**: `Massacci2000` Technique 8.2 subtractive blocking — the blocked arm emits
`(.linear [], acc)`, **no edge** — plus a **separate, completeness-only redirect channel** `red`
threaded alongside `keys`, with the countermodel extracted over `ReflTransGen (acc ∪ red)`.

Soundness never sees `red`; completeness sees both. That asymmetry is the whole route, and it is
what makes the soundness side close at **full `branchSatisfiableIn s4FC` strength** rather than by
weakening to `branchPropAdequateIn`.

**Definition of done**: a subtractive, ordered, `red`-threading S4 keyed driver
(`modalTableauS4KeyedSub`) with *both* a machine-checked soundness theorem against `s4FC` **and** a
machine-checked completeness theorem, the decidability instance `instDecidableS4Valid` landed, a
permanent regression witness that `cex` no longer closes, every new declaration sorry-free and
axiom-clean, and full CI green at every commit. No landed driver is retired.

**Scope constraint**: file scope is `Cslib/Logics/Modal/Tableau/{LoopChecking,FrameCompleteness,
FrameSoundness}.lean` plus `CslibTests/S4LoopGuardRegression.lean` plus this task's `specs/`
directory. `Cslib/Logics/Modal/Tableau/Rules.lean`, `Cslib/Logics/Modal/Tableau/Saturation.lean`,
`Cslib/Logics/Modal/Tableau/SoundnessStep.lean` and `Cslib/Logics/Modal/Tableau/Branch.lean` are
**read-only in every phase** (see Postmortem Constraints for why each). The concurrent session's
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` and `Cslib.lean` are out of scope.

### Why this route, in one paragraph, without re-arguing settled ground

Route (3) does **not** eliminate the hard obligation; it **relocates** it from a per-step invariant
to a terminal-leaf obligation. Every landed counterexample in this task's record refutes the
obligation at a *transient intermediate* state — report 02 §2.2 refutes
`blockedRedirect_boxctx_mem` at step [6] of a 5-step trace, with report 02's own note that `b` is
"repaired one step later" — and a saturated open branch does not exhibit transient states. Measured
at terminal open leaves (`artifacts/s4subtractive3.lean`): **0 failures out of 24,314 recorded
blocking decisions, across 110,741 terminal open leaves of 80,681 formulas in 3 corpora**, including
the chain-closed forward-cone form with redirect chains up to 39 deep.

### The Single Load-Bearing Risk, Stated Up Front — and Why It Is Front-Loaded

**That is measurement, not proof, and this task has already been burned by exactly that gap.** v3's
Phase 1 measured the box-propagation obligation at **1374 pass / 0 fail** and v3's Phase 2 still
died at its gate, because empirical truth does not imply provability in a given framing. The
1374/1374 result is preserved as an inherited asset (see Preserved Assets P1) and is *not* treated
as evidence for anything in this plan.

Accordingly the route's two load-bearing obligations are separated and both are **standalone,
driver-independent, cheaply-falsifiable decision gates in waves 1-2**, before any driver surgery:

- **Gate A (Phase 2) — the CONSUMPTION side.** Does the forward-cone Hintikka statement actually
  feed a truth lemma over `ReflTransGen (acc ∪ red)`? This is report 04 §9's own mandatory
  condition: *"if the forward-cone form cannot be made to feed `modalTruthLemmaS4`, route (3) is
  **not** viable and the honest fallback is route (1), not (2′)."*
- **Gate B (Phase 3) — the ESTABLISHMENT side.** Can the forward-cone clauses be *proved* from
  branch-level facts at a blocked step? Two of the four transfers — the **unwrapped** box and
  diamond transfers, conditions (c)/(e), each 0 failures out of 24,314 — are provable by
  near-transcription of the landed `modalStepBranchS4Keyed_blocked_witness_mem`
  (`LoopChecking.lean:8806-8824`) from `S4LoopInv.keyLowerBd` plus the guard's own `some` contract;
  verified by reading `successorBirthContent` (`:384-391`) against `relevantSetFinset` (`:333-337`)
  in this planning run. The **cone extension beyond `wBlock` itself is the genuinely unproven
  part**, and Phase 3 exists to prove it or to name the exact missing fact.

Gates A and B are independent (A assumes the forward-cone clauses as hypotheses; B proves them), so
they run in parallel as wave 2. **Neither gate may be closed with a `sorry`** — see Postmortem
Constraints.

**What kills route (3)**, stated now so no dispatch has to decide it under pressure:

| Outcome | Verdict |
|---|---|
| Phase 2 cannot derive the box-positive or diamond-negative truth-lemma case from the forward-cone conjuncts | **Route (3) is dead.** Escalate to the user. The honest fallback is route (1) (full canonical/pinned-witness truth lemma), **not** route (2′). |
| Phase 3's cone extension needs a fact that no branch-level or threaded invariant can supply | **Route (3) is dead.** Escalate with the exact goal state. |
| Phase 3's cone extension needs a *nameable* additional threaded invariant | **Route (3) survives**, at the cost of one added phase (3b) carrying that invariant. Record the statement; do not proceed to Phase 4 until it is stated and its plausibility is checked against the probe. |
| Phase 3 succeeds only for the box half, not the diamond half | **Route (3) is dead as planned.** Do **not** fall back to the wrapped diamond form — it has 40 measured counterexamples (report 04 §6.4). Escalate. |

### Reconciliation with the recorded mandate

`specs/state.json`'s `mandate_change` entry records the user's post-v3 choice of *"driver-dependent
Hintikka/canonical-model truth lemma"* (route (1)). Route (3) **contains** that work rather than
replacing it: Phase 2 is a driver-dependent Hintikka/canonical-model truth lemma, over
`ReflTransGen (acc ∪ red)` instead of `ReflTransGen acc`. What route (3) additionally buys is that
the *soundness* side no longer needs a pinned witness model at all, because a blocked step is the
identity on `(b, acc)`. The mandate's substance is preserved; the route label is updated to (3) per
the user's decision in this dispatch, on the evidence in report 04.

### Design Decision Derived at Plan Time (and one cheap design REFUTED at plan time)

`Accessibility` is a bare `⟨edges : List (WorldIndex × WorldIndex)⟩` (`Branch.lean:55-57`), so `red`
can be **materialized into an `Accessibility`** at the point of use:

```lean
abbrev Reds := List (WorldIndex × WorldIndex × Sign × Proposition Atom)
def accWithReds (acc : Accessibility) (red : Reds) : Accessibility :=
  ⟨acc.edges ++ red.map (fun r => (r.1, r.2.1))⟩
```

This is the probe's `augEdges` (`artifacts/s4subtractive3.lean:222-224`) lifted into the library
type, and it means `extractModelS4` and all five `extractModelS4*` lemmas
(`FrameCompleteness.lean:143-189`) are reused **verbatim** at `acc := accWithReds acc red`; no
`extractModelS4Sub` is needed. That is a real saving against report 04's §7.2 phase 7 estimate.

**The tempting next step is REFUTED, and recording that refutation is the point of this
subsection.** It looks as though one could then reuse `modalHintikkaSetS4` (`:6543-6562`) itself
verbatim at `accWithReds acc red` and inherit `modalTruthLemmaS4`,
`modalOpenBranchS4_countermodel` and the whole `FrameCompleteness.lean` assembly for free. **That
design is exactly the (d)-shaped statement with 40 known counterexamples.** Reason, verified by
reading: `modalHintikkaSetS4`'s conjunct 2 evaluates `modalApplyOneS4 φ₀ sf b acc`, whose
box-positive and diamond-negative arms propagate *along every edge of the `acc` it is handed*
(`modalFourBoxProp b acc ψ w`). Handing it the union therefore demands `T(□χ)@wBlock ∈ b` **and**
`F(◇χ)@wBlock ∈ b` for every recorded redirect — the wrapped-at-target forms, conditions (b) and
(d). (d) fails **40 times out of 24,314** (report 04 §6.4). So the union must **not** be substituted
into conjunct 2.

**The design this plan adopts** is therefore a *bifurcated* predicate, and this is the statement
shape Phase 1 fixes:

| Conjunct | Relation it is stated over | Rationale |
|---|---|---|
| 1. `isModalClosed b = false` | — | unchanged |
| 2. saturation w.r.t. `modalApplyOneS4 φ₀` | **`acc` only** | avoids the (b)/(d) obligations entirely; and the subtractive driver *does* saturate over `acc`, since a blocked step adds no `acc` edge |
| 3. box-negative witness `∃ w', … ∧ F(χ)@w' ∈ b` | **`accWithReds acc red`** | the redirect supplies the witness; `modalStepBranchS4Keyed_blocked_witness_mem` (`:8806-8824`, zero `acc` mentions) supplies the branch-membership half free |
| 4. diamond-positive witness | **`accWithReds acc red`** | dual |
| 5. `redBoxForwardCone` (G\*) | cone in `accWithReds acc red` | **0 failures / 24,314** |
| 6. `redDiaForwardCone` (F\*) | cone in `accWithReds acc red` | **0 failures / 24,314**; the wrapped alternative (d) has **40** |

Consequence for Phase 2, also verified by reading: `hintikkaS4_box_pos_step` (`:6599`) destructures
its hypothesis as `⟨_, hrule, _⟩` — it consumes **only conjunct 2**. So generalizing
`hintikkaS4_box_pos_{self,step,reflTransGen}` and their diamond duals (`:6599`, `:6686`, `:6779`,
`:6863`, `:6985-6998`, `:7001-7013`) to take the bare saturation conjunct instead of the full
predicate is a **mechanical hypothesis-weakening**, and it is *mandatory*: conjuncts 3/4 over bare
`acc` are false for the subtractive driver, so the full-predicate form cannot be supplied.

### Preserved Assets

Sorry-free, axiom-clean landed work that **must not regress**. Each row carries an explicit
disposition. Nothing is deleted on an unverified premise; nothing in this table is retired by this
plan at all.

| Component | File | Status | Verified | Disposition under route (3) |
|---|---|---|---|---|
| **P1: v3 Phase 1 probe and its four measurements** | `specs/553_.../artifacts/s4ancestor.lean`; `plans/03_...md` `#### Phase 1 Measurements` | [COMPLETED] | 2026-07-26 | **INHERITED, not redone.** The `[COMPLETED]` heading and the measurement text are preserved verbatim when v3 is stamped `[ABANDONED]`. Measurement D(iv)'s 1374/1374 is explicitly **not** used as evidence for any obligation in this plan. |
| **P2: report 04's three probes** | `artifacts/s4subtractive.lean`, `s4subtractive2.lean`, `s4subtractive3.lean` | [COMPLETED] | 2026-07-26 | **EXTENDED, not replaced.** Phase 1 realigns `s4subtractive3.lean`'s decidable mirrors to the final Lean statement shapes; Phase 12 re-runs the differential sweep. The independent semantic oracle (self-calibrating to least-countermodel-size 3 for `cex`, matching `LoopChecking.lean:473-476`) is the adjudicator for every verdict disagreement. Do **not** write a new harness. |
| P3: counterexample regression corpus | `CslibTests/S4LoopGuardRegression.lean` (197 lines) | [COMPLETED] | 2026-07-26 | **KEEP unchanged; extended in Phase 12.** The shipped unordered driver's documented unsoundness is unaffected. |
| P4: guard + its three contract lemmas | `LoopChecking.lean:506-555` (`blockingWorldS4Keyed`, `_eq_birthContent`, `_none_fresh`) | [COMPLETED] | 2026-07-26 | **KEEP, BYTE-FOR-BYTE UNCHANGED, load-bearing.** Route (3) changes the guard's *effect*, never its *decision*. This is precisely why termination survives (§5.1 of report 04). |
| P5: guard docstring's defect record | `LoopChecking.lean:466-505` | [COMPLETED] | 2026-07-26 | **KEEP as historical record; APPEND in Phase 4** a pointer to the subtractive repair. Do not delete the `:478-492` staleness / no-reachability-restriction description. |
| P6: ordered stepper family | `modalNonMintCandidates`; `modalStepBranchS4KeyedOrdered` (`:1107`), `_cases` (`:1124`); `modalExpandBranchesS4KeyedOrdered` (`:7739`); `modalTableauS4KeyedOrdered` (`:7800`) | [COMPLETED] | 2026-07-26 | **KEEP as base, unchanged.** The subtractive driver lands *beside* it. The ordered stepper is **mandatory** for route (3) (see Postmortem Constraints). |
| P7: `S4LoopInv` (10 fields) + fuel-sufficiency chain | `S4LoopInv` (`:7047-7080`), `modalKnownWorlds_length_le_worldBoundS4` (`:6459`), `modalStepBranchS4_worldBound` (`:6501`), `modalExpMeasure_entry_le_fuelS4` (`:8486`), `modalExpMeasure_step_lt_S4Keyed` (`:9502-9520`) | [COMPLETED] | 2026-07-26 | **KEEP UNCHANGED.** A parallel 9-field `S4LoopInvSub` lands beside it (Phase 5). `modalStepBranchS4_preserves_outDegEq` (`:4917-5104`, 188 lines) stays where it is — it is still true for the landed drivers; it simply gets **no subtractive analogue**. |
| P8: landed keyed completeness line | `modalTableauS4Keyed_complete` (`FrameCompleteness.lean:4265-4301`) + its 43 S4-keyed dependencies (1,983 lines, 0 sorries) | [COMPLETED] | 2026-07-26 | **KEEP GREEN THROUGHOUT.** Enforced by the parallel-definition convention (`LoopChecking.lean:459-464`, `:990-996`). 1,188 of those lines survive untouched; the rest gain *parallel* `Sub` analogues, not edits. |
| P9: the load-bearing survivor | `modalStepBranchS4Keyed_blocked_witness_mem` (`:8806-8824`, 19 lines, zero `acc`/edge mentions) | [COMPLETED] | 2026-07-26 | **REUSE VERBATIM.** It yields `⟨s, φ, wBlock⟩ ∈ b` from `keyLowerBd` alone. Phase 3's two unwrapped-transfer lemmas are near-transcriptions of its 15-line proof. |
| P10: `extractModelS4` + 5 lemmas; the two `ReflTransGen` path bridges | `FrameCompleteness.lean:143-189`; `LoopChecking.lean:6985-6998`, `:7001-7013` | [COMPLETED] | 2026-07-26 | **REUSE.** `extractModelS4` is reused verbatim at `accWithReds acc red`. The path bridges are *generalized in place* by hypothesis-weakening (conjunct 2 only) — a strictly weaker hypothesis, so no existing caller breaks. |
| P11: the origin-edge / `keysOriginS4` family | `LoopChecking.lean:1279`, `:1294`, `:1306`, `:1327`, `:2009`, `:2015`, `:4558`, `:4775`, `:2406` | [COMPLETED] | 2026-07-26 | **KEEP, unused by route (3).** Route (3) needs no spine, so this family is not load-bearing here. It is sorry-free and true; **do not delete it** on the grounds that this route does not consume it. |
| P12: the `sorry` at `FrameSoundness.lean:1244` | `branchSatisfiableIn_s4FC_ancestor_redirect` (`:1220-1244`) | [COMPLETED] (documented marker) | 2026-07-26 | **STAYS, per explicit user decision. No phase in this plan touches it.** See "Flagged for User Decision" below. |

### Flagged for User Decision (not planned, not actioned)

**Determination requested by the dispatch**: does route (3) make the lemma holding the
`FrameSoundness.lean:1244` `sorry` obsolete? **Yes — determined by reading, stated here rather than
acted on.** `branchSatisfiableIn_s4FC_ancestor_redirect` exists to justify *adding* a redirect edge
to `acc`. Under route (3) no blocked step ever adds an edge to `acc`, so the subtractive soundness
capstone (Phase 8) never invokes an edge-justification lemma of any shape: the blocked arm's
preservation obligation is `branchSatisfiableIn s4FC b acc → branchSatisfiableIn s4FC b acc`,
discharged by `id`. The lemma therefore becomes **dead code with respect to every declaration this
plan lands**.

Per the user's explicit decision the `sorry` **stays**, and **no phase below removes, edits, or
retargets it**. The options are recorded for the user only:

1. **Keep as-is** (current default; requires no action, and no phase depends on the choice). The
   directory's sorry census stays at 1.
2. **Delete the lemma and its `sorry`** — would make `Cslib/Logics/Modal/Tableau/` sorry-free. Cheap
   (one declaration, one scoped `lake shake`), but discards a machine-checked record of *why* the
   ancestor route failed.
3. **Keep the lemma, retarget its docstring** to say the obligation is dissolved rather than open.

If the user later chooses (2) or (3), it is a one-dispatch follow-up, sequenced **after** Phase 8
has landed (so the obsolescence claim is verified by the absence of a consumer, not asserted).

### Source-to-Implementation Mapping (H3, Tier 1 literature + Tier 3 implementation)

BibKey verified: `Massacci2000` at **`references.bib:1010`** (read in this planning run). Every
literature claim below carries a proposition/definition number **and** a page number, per the lean4
H3 override. Chunks read in this planning run: `chunk_0029.md`, `chunk_0030.md`, `chunk_0031.md`,
`chunk_0065.md` under
`~/Projects/Literature/massacci_2000_single_step_tableaux_for_modal_logics/`.

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|---|---|---|---|---|
| Massacci 2000 | Technique 8.2, p. 337 (`chunk_0030.md`): *"Before reducing a π-formula, check whether the corresponding prefix is not a copy of a shorter prefix"* — blocking = **withholding a rule**, adding nothing | `modalApplyOneS4KeyedSub` | `Proposition Atom → List (WorldIndex × Finset (Sign × Proposition Atom)) → RuleApply Atom` | pending (Phase 4) |
| Massacci 2000 | Remark on proof confluence, p. 337 (`chunk_0030.md`): *"We do not need to backtrack once we find a loop; we leave the 'copies'"* | variant **S1 (consume)**: blocked arm emits `(.linear [], acc)` so `sf` enters `e` | — | pending (Phase 4) |
| Massacci 2000 | Def. 8.2 (modal copy: *"same ν formulae"*), p. 337 (`chunk_0030.md`) | `successorBirthContent` (**landed**, `LoopChecking.lean:384-391`) | `Proposition Atom → List (SignedFormula …) → Sign → Proposition Atom → WorldIndex → Finset (Sign × Proposition Atom)` | transcribed (landed) |
| Massacci 2000 | Thm 8.1, p. 337 (`chunk_0030.md`): a π-completed branch witnesses satisfiability — **completeness-side only**, which is why Massacci carries no soundness obligation from blocking | `modalTableauS4KeyedSub_complete` | `s4Valid φ₀ → modalTableauS4KeyedSub φ₀ = .closed` | pending (Phase 11) |
| Massacci 2000 | Prop. 8.1, Appendix B (`chunk_0065.md`): *"σ₀ : □A ∈ B implies σ : □A ∈ B"* for σ₀ an initial subsequence of σ — box monotonicity **ancestor → descendant** | `hintikkaS4_box_pos_reflTransGen` (**landed**, `LoopChecking.lean:6985-6998`), generalized to the bare saturation conjunct | `… → Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w' → ⟨.pos, ψ, w'⟩ ∈ b` | transcribed (landed); hypothesis-weakened in Phase 2 |
| Massacci 2000 | Def. 8.1 (copy), p. 336 (`chunk_0029.md`) — copy relation is on the **source** prefix's own content | **no CSLib analogue — DELIBERATE DIVERGENCE**, see below | — | n/a |
| Massacci 2000 | Pruning Lemma 8.2, p. 338 (`chunk_0031.md`): `B ∖ Ftree(σ.n)` stays π-completed — the literature's model *identifies* copies and records no redirect | **not ported** — replaced by the `red` channel, see below | — | n/a |
| Massacci 2000 | Prop. 8.2 and Prop. B.5, Appendix B (`chunk_0065.md`): the longest unreduced prefix has length `hbL − 1 = 1 + dp + p × n` (a **depth** bound resting on the Pruning Lemma) | **NOT NEEDED.** `modalWorldBoundS4 φ₀ = 2 ^ (2 * |modalSubfmls φ₀|)` (`LoopChecking.lean:229`), a pigeonhole *cardinality* bound, is retained verbatim | `Proposition Atom → Nat` | transcribed (landed), retained |
| Tier 3 (implementation) | `branchSatisfiableIn`'s edge conjunct quantifies over `acc.hasEdge` only (`FrameSoundness.lean:113`) — read in this planning run | `S4SubSoundSpec` blocked disjunct `apply sf b acc = (.linear [], acc)` | `RuleApply Atom → Prop` | pending (Phase 8) |
| Tier 3 (implementation) | `S5SoundSpec` (`FrameSoundness.lean:2256-2261`) + its docstring at `:2245-2250` — the `apply`-parametric reuse ladder, whose right disjunct still owes a *formula and an edge* | template for `S4SubSoundSpec`, whose blocked disjunct owes **neither** | — | pending (Phase 8) |
| Tier 3 (implementation) | `Accessibility` is `⟨edges : List (WorldIndex × WorldIndex)⟩` (`Branch.lean:55-57`) | `Reds`, `accWithReds` | `Accessibility → Reds → Accessibility` | pending (Phase 1) |
| Tier 3 (implementation) | `hintikka_congr_S4` (`:7821-7833`) closes because `modalHintikkaSetS4`'s conjunct 2 is `True` at exactly the two minting shapes (`:6549-6551`) | `hintikka_congr_S4Sub` | `modalHintikkaSetGen (modalApplyOneS4KeyedSub φ₀ keys) b acc ↔ modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc` | pending (Phase 4) — a 13-line transcription, since the subtractive rule also differs from `modalApplyOneS4` **only** at those two shapes |

**Deliberate divergence from `Massacci2000`, recorded rather than papered over** (report 04 §1.2,
§3.4): Massacci's copy relation (Def. 8.1, p. 336; Def. 8.2, p. 337) is on the **source** prefix's
ν-formulas, so he can fold σ onto a shorter σ₀ and *inherit σ₀'s successors* — a quotient, with no
edge anywhere. CSLib's guard (`blockingWorldS4Keyed`, `:506-511`) instead compares the
**prospective successor's** birth content (`successorBirthContent`, `:384-391`) against a recorded
key. These are different relations, so Massacci's copy-folding model construction does not transfer
verbatim, and a faithful Def. 8.2 port would replace the guard — which would forfeit CSLib's
pigeonhole world bound and drag in Massacci's depth bound (Prop. 8.2 / B.5) as a replacement.
Route (3) therefore keeps CSLib's guard and *moves the redirect out of the soundness-tracked
structure* instead of quotienting. **Route (3) is literature-guided, not literature-transcribed.**
No literature-acquisition phase is planned: the `Gore1999` gap (`references.bib:1023`) is settled
and is not the blocker.

---

## Postmortem Constraints

Binding on every implementation dispatch under this plan.

### What structural property of route (3) prevents a fourth recurrence — and what would falsify it

Three routes have now failed or been superseded: **Route P / settled-context scheduling** (v1),
**the origin-edge invariant** (v2, its two inertness lemmas machine-checked FALSE and removed at
commit `5ac7cbb7`), and **ancestor-only blocking** (v3, Phase 2 `[BLOCKED]`). A fourth — the
**reachability restriction** — was rejected in report 01 before it was ever planned (96.7% of
blocking decisions target non-reachable worlds, so the world bound fails).

All three failures have **one shape**: each tried to *justify an edge that had been added to
`acc`* against a witness model that `branchSatisfiableIn` leaves existentially arbitrary. v3's
Phase 2 Verdict states the obstruction in its most general form — `s4FC`'s `IsTrans` conjunct binds
the concrete relation `m.r`, so any extension of `m.r` must close transitively over *every* ambient
predecessor of `f src`, and no branch-level hypothesis can control those. Restricting *which* world
the edge targets (v3) does not touch this, because the obstruction is about the looseness of the
witness model, not about the target.

**Route (3)'s structural property**: the edge is never added to `acc`. The obligation is moved
**out of the soundness-tracked structure** entirely, into a channel (`red`) that only the
completeness direction reads. There is no edge to justify, so the obstruction has no premise. That
is the honest statement of why this route differs; it is not that the obligation got easier, but
that it left the structure the soundness invariant quantifies over.

**The claim is falsifiable, and Phase 8 must run the falsification test as an explicit step.** The
claim fails if any of the following turns out to be true:

1. Any conjunct of `branchSatisfiableIn` (`FrameSoundness.lean:110-118`), or any hypothesis of the
   subtractive soundness fuel induction, reads `red` or `accWithReds`.
2. `accFreshInv` / `accTargetsKnown` (`SoundnessStep.lean:392`; `FmpMeasure.lean:1891`) must be
   maintained over the union rather than over `acc`.
3. The termination/measure chain (`modalExpMeasure_step_lt_S4Keyed`, `:9502-9520`;
   `modalExpMeasure_entry_le_fuelS4`, `:8486`) reads the union.
4. The entry point must surface the union in a way the *soundness statement* observes.

**Test**: after Phase 8 lands, `grep -n 'red\|accWithReds\|Reds' ` over every declaration in the
soundness chain must return **zero hits**, and `S4SubSoundSpec`'s statement must mention only
`acc`. Record the grep output in the phase's handoff. A non-zero result means the obligation is back
inside the soundness structure and the route's central claim is false — escalate, do not patch.

### Do NOT

- **Do NOT add the redirect edge to `acc`, in any phase, for any reason.** This is the single
  defect all three failed routes share. If a proof appears to need it, that is the falsification
  test above firing — escalate.
- **Do NOT state the diamond-negative (or box-positive) Hintikka clause in the
  wrapped-formula-at-the-target form** `F(◇χ)@src ∈ b → F(◇χ)@wBlock ∈ b` (condition (d)). It has
  **40 measured counterexamples out of 24,314** (report 04 §6.4). Writing it is writing a lemma with
  40 known counterexamples. Use the forward-cone form (F\*)/(G\*).
- **Do NOT substitute `accWithReds acc red` into `modalHintikkaSetS4`'s conjunct 2** or into any
  `modalApplyOneS4` application. See "Design Decision Derived at Plan Time" — that is the (b)/(d)
  obligation in disguise.
- **Do NOT use the unordered subtractive stepper.** Measured: the unordered subtractive driver loses
  **2 closures** on the 1-atom size ≤ 8 corpus (`◇□□(p0→□◇p0)`, `◇□□(◇□p0→p0)`, neither falsifiable
  to model size 4); the ordered one loses none. `modalStepBranchS4KeyedSubOrdered` is mandatory.
- **Do NOT leave a `sorry` standing at a decision gate (Phases 2 and 3).** A `sorry` at a gate
  stands in for a possibly-false statement — the exact failure this task has suffered **twice**
  (v2's removed inertness lemmas; v3's `:1244`). A strategic-sorry skeleton remains a legitimate
  *mid-phase recovery* move inside a non-gate phase and must be discharged before that phase is
  marked `[COMPLETED]`. At a gate, if the proof does not close, **revert the attempt** and record
  the exact `lean_goal` state in this plan's verdict subsection. Do not commit the sorry.
- **Do NOT re-open the settled results** listed in "Design decisions are SETTLED" below, and in
  particular **do NOT re-argue `branchPropAdequateIn`**. Report 03 established that weakening would
  be safe for all consumers; the user has chosen full strength and report 04 shows route (3)
  delivers it without being more expensive. This is closed.
- **Do NOT re-propose** any of: the three removed false lemmas (`blockedRedirect_boxctx_mem`,
  `blockedRedirect_diaNeg_mem`, `blockedRedirect_propAdequate`); the §5.1 disjunctive-edge-conjunct
  repair (route (2′) — both disjuncts' proof strategies have landed refutations); the reachability
  restriction; ancestor-only blocking; redirect-inertness in any form.
- **Do NOT state a claim about driver behaviour, an "the invariant already gives us X" step, or a
  "Named difficulty", without checking it against the actual definitions in the same dispatch.**
  v1, v2 and v3 all blocked on this same shape. Every phase below carries its verification inside
  the phase.
- **Do NOT modify `Cslib/Logics/Modal/Tableau/Rules.lean`** — `modalApplyOne` is shared with
  K/T/B/S5 and with `FmpMeasure.lean`'s `_gen` lemmas. Any payload change belongs in the S4-keyed
  layer.
- **Do NOT modify `Cslib/Logics/Modal/Tableau/Saturation.lean`.** `ModalTableauResult`
  (`Saturation.lean:82`) is consumed by 8 files (`BDriver`, `TDriver`, `CompletenessLoop`,
  `FiveSimplification`, `S5Simplification`, `LoopChecking`, `FrameCompleteness`, `Saturation`
  itself). It carries only `(b, acc)`. `red` must be surfaced by a **new, S4-keyed-local** result
  type or by materializing the union at the return point — Phase 7 decides, and neither option
  edits this file.
- **Do NOT modify `Cslib/Logics/Modal/Tableau/Branch.lean` or `SoundnessStep.lean`.** Both are
  read-only inputs; `accWithReds` is defined in `LoopChecking.lean`, not beside `Accessibility`.
- **Do NOT edit any landed declaration in-place except by strict hypothesis-weakening.** The one
  sanctioned in-place change in this plan is Phase 2's weakening of the six
  `hintikkaS4_{box_pos,dia_neg}_{self,step,reflTransGen}` hypotheses from the full predicate to the
  bare saturation conjunct — strictly weaker, so no existing caller can break; verify by a clean
  project-wide `lake build`.
- **Do NOT touch `Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` or `Cslib.lean`** —
  concurrent session territory.
- **Do NOT weaken, vacuously restate, or `True`-stub any statement.** `def X := True`,
  `theorem X := trivial` and friends are prohibited (`.claude/rules/cslib.md`).
- **Do NOT compress Phases 2 and 3 into one dispatch**, and do not reorder them behind Phase 4.
  They are the route's two decision gates and they are deliberately in wave 2.
- **Do NOT treat a measurement as a proof.** v3's Measurement D(iv) was 1374/1374 and the route
  still died. Probe results in this plan are gates that can only ever *kill* a design, never
  license one.

### MUST preserve

- Every row of the Preserved Assets table, at its stated disposition. In particular:
  `blockingWorldS4Keyed` and its three contract lemmas **byte-for-byte unchanged**;
  `modalTableauS4Keyed_complete` green at every commit; the `sorry` at `FrameSoundness.lean:1244`
  untouched.
- **Sorry count in `Cslib/Logics/Modal/Tableau/` stays at exactly 1** (`FrameSoundness.lean:1244`)
  at every phase boundary. Verify with `grep -rn '\bsorry\b' Cslib/Logics/Modal/Tableau/*.lean`
  and discount docstring mentions.
- **Zero new axioms.** Do **not** hard-code a repo axiom count in a verification step: the
  raw `grep -rn '^axiom' Cslib/ | wc -l` census reads **47** across 37 files as measured in this
  planning run, which does **not** match the "26" asserted by v3, and this plan will not propagate
  an unverified number. **Instead**: capture the baseline with the exact command at the start of
  each phase, require byte-equality at the end, and additionally run `lean_verify` on every new
  top-level theorem, requiring only the standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`).
- Full CI green at every commit: `lake build`, `lake test`, `lake lint`, `lake exe
  checkInitImports`, `lake exe lint-style`, `lake exe mk_all --module` (must report no update
  necessary — `Cslib.lean` is concurrent-session territory), and scoped
  `lake shake --add-public --keep-implied --keep-prefix` on each touched file.
- The measured facts from report 04's probes. Any dispatch that changes a driver **re-runs** the
  differential sweep rather than reasoning about what it would produce.
- Commit at every green sub-step, per `.claude/rules/git-workflow.md`'s commit-per-green-substep
  mandate.

### Design decisions are SETTLED (do not re-open without a concrete, machine-checked counterexample)

1. **Keyed S4 soundness as originally stated is FALSE** — report 01, machine-checked `cex`, node
   size 19, with an explicit 3-world reflexive-transitive countermodel.
2. **The reachability restriction is REJECTED** — 96.7% of blocking decisions target non-reachable
   worlds (report 01).
3. **`blockedRedirect_boxctx_mem` / `_diaNeg_mem` / `_propAdequate` are FALSE at a reachable
   (transient) state** (report 02) and have been removed.
4. **Ancestor-only blocking does not close** (v3 `#### Phase 2 Verdict`).
5. **Weakening to `branchPropAdequateIn` would be SAFE for all consumers** (report 03) — but the
   user has chosen **full strength**, and report 04 finds route (3) both delivers it and is not more
   expensive. **Closed. Do not re-argue.**
6. **Route (3) dissolves the #548 reflexivity risk**: `modalApplyOne_boxPos_sound`
   (`SoundnessStep.lean:446-459`) has **no `FC` parameter at all** (verified by reading its
   signature in this planning run); `FrameSoundness.lean:1085-1100` and `:1106-1123` use
   `htrans.trans` with `hrefl` destructured and never used. Reflexivity is needed only for the
   T-rule itself (`:973`), which is intrinsic to T/S4 and simply absent from K4/D4's rule set.
7. **`Gore1999` is settled and is not a blocker.** No literature-acquisition phase.
8. **Variant S1 (consume, `(.linear [], acc)`) is the variant**, not S2 (`.notApplicable`). S1's
   blocked step still grows `e`, which is `modalExpMeasure_step_lt_S4Keyed`'s decrease witness;
   S2 would take no step at all. S1 makes `S4LoopInv.outDegEq` false, which is why it is dropped
   (below), not why S2 is preferred.
9. **`outDegEq` is droppable, not re-provable** — `grep` shows `.outDegEq` is *provided* at
   `LoopChecking.lean:7546`/`:7610` and **consumed nowhere** in the S4 line, and
   `modalExpMeasure_step_lt_S4Keyed` (`:9502-9520`) does not take it. **Mechanism (refinement, not
   a re-opening)**: the field is dropped by *never carrying it into the new `S4LoopInvSub`*, and
   the landed `S4LoopInv` and its 188-line `modalStepBranchS4_preserves_outDegEq` are left
   untouched. That realizes the same 188-line saving with zero regression risk to the landed
   completeness line, which is strictly better than deleting a field from a landed structure.
10. **The subtractive driver lands as a PARALLEL definition family** (`…Sub…`), per this file's own
    convention (`LoopChecking.lean:459-464`, `:990-996`). No landed driver is retired by this plan.
11. **Massacci's depth bound is NOT imported.** CSLib's pigeonhole `modalWorldBoundS4` is retained,
    because the guard is unchanged (report 04 §5.4).
12. **The `red` channel is THREADED, never RECOMPUTED.** `successorBirthContent` (`:384-391`) reads
    the *live* `b`, which has grown by the time an open leaf is reached — the documented staleness
    defect at `LoopChecking.lean:478-492`. Recomputing `red` at the leaf would reproduce that
    defect.

---

## Goals & Non-Goals

- **Goals**:
  - Settle, **before any driver surgery**, both halves of the route's load-bearing obligation:
    that the forward-cone Hintikka form feeds a truth lemma over `ReflTransGen (acc ∪ red)`
    (Phase 2), and that the forward-cone clauses are provable at a blocked step (Phase 3).
  - Land a subtractive, ordered, `red`-threading S4 keyed driver that is sorry-free.
  - Prove it **sound** against `s4FC` at **full `branchSatisfiableIn s4FC` strength**.
  - Prove it **complete**, over the augmented extraction relation.
  - Land `s4Valid_decides` / `instDecidableS4Valid` — the downstream consumer this task exists to
    unblock.
  - Gate the landed driver empirically with report 04's proven three-corpus harness and its
    independent semantic oracle.
- **Non-Goals**:
  - Retiring `modalTableauS4Keyed`, `modalTableauS4KeyedOrdered`, or any landed lemma.
  - Removing, editing, or retargeting the `sorry` at `FrameSoundness.lean:1244` (user decision;
    flagged above, not planned).
  - Any change to `Rules.lean`, `Saturation.lean`, `Branch.lean`, `SoundnessStep.lean`, to
    K/T/B/S5, or to the concurrent session's territory.
  - A faithful port of `Massacci2000` Def. 8.2 / the Pruning Lemma (strictly more expensive; see
    the divergence note).
  - Acquiring `Gore1999`.
  - Extending the mechanism to K4/K45/D4/D45 (#548). Route (3) *dissolves* the blocker for them;
    actually instantiating those corners is separate work.

## Risks & Mitigations

- **Risk (highest): Phase 3's cone extension is not provable.** The two unwrapped transfers
  ((c)/(e)) follow from `keyLowerBd` + the guard contract, but extending the payload to `wBlock`'s
  *forward cone* in `acc ∪ red` does not, and 0 failures out of 24,314 is measurement, not proof.
  *Mitigation*: Phase 3 is a standalone, driver-independent gate in wave 2 with an explicit
  three-way verdict (proved / needs a nameable extra invariant → Phase 3b / dead → escalate). No
  phase after 3 is scaffolded around a positive outcome.
- **Risk: Phase 2's truth lemma does not close from the forward-cone conjuncts.** The path
  decomposition over a union relation is new. *Mitigation*: Phase 2 is standalone (no driver) and
  runs in parallel with Phase 3, so the cheaper of the two failures is discovered in the same wave.
  Report 04 §9 already names route (1) as the honest fallback if this fails.
- **Risk: the S5 `apply`-parametric ladder is not the drop-in it appears to be.** Verified in this
  planning run: `modalTableauS5Gen_sound` (`FrameSoundness.lean:3317`) and
  `modalExpandBranchesGen_closed_unsatIn` (`:731`) are stated over `modalTableauGen` /
  `modalExpandBranchesGen`, which **do not thread `keys`** — whereas the keyed drivers do (and the
  subtractive one threads `red` as well). *Mitigation*: Phase 8 is scoped as *"write the fuel
  induction for `modalExpandBranchesS4KeyedSubOrdered`'s own shape, using the S5Gen ladder as a
  template"*, budgeted at ~400 lines with a declared 8.1/8.2 split, not as a free instantiation.
- **Risk: `red` cannot be surfaced at the open leaf without touching `ModalTableauResult`.**
  *Mitigation*: Phase 7 carries two pre-designed options (a new S4-keyed-local result type carrying
  `red` with a projecting entry point; or materializing `accWithReds` at the return point only,
  which leaves the *threaded* `acc` clean and so preserves soundness triviality). Both leave
  `Saturation.lean` untouched. The phase's first task is to pick one against a stated criterion.
- **Risk: the completeness cost overruns.** Counted, not estimated: 4 decls / 1,036 lines need new
  proofs, 10 decls / 186 lines need restatement, 1,188 lines survive; the entire semantic dependence
  on the redirect edge is **17 lines in 4 clauses** (`LoopChecking.lean:6557-6562`, `:8756-8759`,
  `:8763-8766`). *Mitigation*: Phases 9-11 are sized against those exact line ranges, and the
  plan-time discovery that `extractModelS4` is reused verbatim removes one of report 04's estimated
  phases' worth of work.
- **Risk: termination regresses.** *Mitigation*: none needed beyond transcription — the guard is
  unchanged, all four `keys` fields of `S4LoopInv` are `acc`-free (`:7063-7080`, read in this
  planning run), `keysDistinct`'s sole establisher is about the guard, and measured `keysDistinct`
  breakage is 0/8532 with fuel exhaustion 2 (shipped) vs 0 (subtractive). Phase 6 transcribes;
  Phase 12 re-measures.
- **Risk: context exhaustion mid-phase.** *Mitigation*: every phase is one bounded unit with a
  concrete stopping condition and a declared split rule where it approaches the ceiling.

---

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5, 7 | 4 |
| 5 | 6, 8, 9, 12 | 5, 7 |
| 6 | 10 | 6, 9 |
| 7 | 11 | 2, 10 |

Phases within the same wave can execute in parallel.

**Territory contracts for parallel dispatch** (H7). No two phases in the same wave write the same
file *section*:

| Wave | Phase | Owns (write) | Read-only |
|---|---|---|---|
| 2 | 2 | `FrameCompleteness.lean` (new `…Sub` truth-lemma section) **and** the six `hintikkaS4_*` hypothesis-weakenings in `LoopChecking.lean` | everything else |
| 2 | 3 | `LoopChecking.lean` new "redirect transfer" section (append after `:8824`) | `FrameCompleteness.lean` |
| 4 | 5 | `LoopChecking.lean` invariant section (`S4LoopInvSub`, append after `:7513`'s block) | — |
| 4 | 7 | `LoopChecking.lean` driver section (`…SubOrdered` expander + entry point, append after `:7810`) | — |
| 5 | 6 | `LoopChecking.lean` bounds/measure section | — |
| 5 | 8 | `FrameSoundness.lean` (new `…Sub` soundness section, append at end) | `SoundnessStep.lean` |
| 5 | 9 | `LoopChecking.lean` Hintikka-invariant section | — |
| 5 | 12 | `CslibTests/S4LoopGuardRegression.lean`, `specs/…/artifacts/` | `Cslib/**` |
| 6 | 10 | `LoopChecking.lean` top-loop Hintikka section | — |
| 7 | 11 | `FrameCompleteness.lean` S4Keyed assembly section | — |

**Wave-5 caveat**: Phases 6 and 9 both write `LoopChecking.lean`. They may be dispatched in
parallel **only** under the declared section ownership above, with each dispatch re-reading the file
immediately before its first `Edit`. If a dispatch finds the file changed under it, it serializes
(runs after the other) rather than merging.

**Note on phase count (H8 deviation, declared).** Twelve phases exceeds the 8-phase ceiling the
hard-mode planner applies to "complex" tasks, and exceeds report 04 §7.2's price of ~9. The excess
is three phases, each deliberate:

1. **Phase 1 (statement-shape design) is separated** because report 04 §9 makes it a mandatory
   condition that the clause shapes be fixed *before any proof is attempted*, and because the
   (b)/(d) trap is a statement-shape trap, not a proof difficulty.
2. **The single "load-bearing obligation" phase is split into two gates (2 and 3)** because
   consumption and establishment are independent obligations with different files, different kill
   criteria, and different fallbacks — and splitting them is precisely what lets both run in
   wave 2 instead of one hiding behind the other.
3. **Phase 12 (empirical regression gate) is separated** because it is a measurement in a different
   territory (`CslibTests/`) and must be re-runnable independently of any proof phase.

Every phase independently passes the bounded-unit test: one definition family, one lemma family, or
one measurement, each with a concrete stopping condition stated below, each estimated at ≤ ~400
lines with an explicit split rule where it approaches that.

**A skeleton plan with strategic-sorry division points was considered and REJECTED.** The two
riskiest obligations are Phases 2 and 3, so there is no long green prefix to skeletonise; and a
strategic sorry at either gate would be a sorry standing in for a possibly-false statement — the
exact failure this task has already suffered twice (v2's removed inertness lemmas; v3's `:1244`).
`plan_metadata.skeleton` is therefore `false` and there is no `## Planned Strategic Sorries`
section.

---

### Phase 1: The `red` channel type, `accWithReds`, and the bifurcated Hintikka predicate `modalHintikkaSetS4Sub` [COMPLETED]

- **Goal:** Fix the exact Lean statement shapes the whole route rests on, with **no proofs
  attempted**, and re-validate them against the probe in their *final* form.
- **Tasks:**
  - [x] `abbrev Reds := List (WorldIndex × WorldIndex × Sign × Proposition Atom)` in
        `LoopChecking.lean`, matching `artifacts/s4subtractive3.lean:43`'s working type
        (source, target, sign, formula). **Landed as `abbrev Reds (Atom : Type*) [DecidableEq
        Atom] [Hashable Atom] := List (...)`** rather than the plan's bare zero-argument form:
        unlike the probe's `P := Proposition Nat` (a concrete type), `LoopChecking.lean`'s
        `Atom` is an ambient section `variable`, and a zero-argument `abbrev` referencing it
        fails to elaborate at every use site (`don't know how to synthesize implicit argument
        Atom` -- confirmed by a minimal reproduction before landing). Every use site writes
        `Reds Atom` explicitly; this is a mechanical Lean-elaboration necessity, not a design
        change -- the type is byte-identical in content to the plan's spec.
  - [x] `def accWithReds (acc : Accessibility) (red : Reds) : Accessibility :=
        ⟨acc.edges ++ red.map (fun r => (r.1, r.2.1))⟩`, plus the single `simp` bridge
        `hasEdge_accWithReds_iff : (accWithReds acc red).hasEdge x y = (acc.hasEdge x y ||
        red.any (fun r => r.1 == x && r.2.1 == y))` (by `List.any_append`). Landed proof:
        `simp only [accWithReds, Accessibility.hasEdge, List.any_append, List.any_map,
        Function.comp_def]` (verified `List.any_map`'s stated form needs `Function.comp_def` to
        close the resulting `∘`-vs-`fun` goal; confirmed via `lean_run_code` before landing).
  - [x] `def modalHintikkaSetS4Sub (φ₀) (b) (acc : Accessibility) (red : Reds) : Prop` with the six
        conjuncts of the Overview's bifurcation table. Conjunct 2 is stated over **`acc`**;
        conjuncts 3/4 over **`accWithReds acc red`**; conjuncts 5/6 are:
        ```lean
        -- 5. redBoxForwardCone  (G*)
        ∀ (χ : Proposition Atom) (src wBlock : WorldIndex) (s : Sign) (φ : Proposition Atom),
          (src, wBlock, s, φ) ∈ red →
          (⟨.pos, .box χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
          ∀ u, Relation.ReflTransGen
                 (fun x y => (accWithReds acc red).hasEdge x y = true) wBlock u →
            (⟨.pos, χ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
        -- 6. redDiaForwardCone  (F*)
        ∀ (χ : Proposition Atom) (src wBlock : WorldIndex) (s : Sign) (φ : Proposition Atom),
          (src, wBlock, s, φ) ∈ red →
          (⟨.neg, .diamond χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
          ∀ u, Relation.ReflTransGen
                 (fun x y => (accWithReds acc red).hasEdge x y = true) wBlock u →
            (⟨.neg, χ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
        ```
  - [x] `structure S4KeyedSubHintikkaInv` — **field statements only, no preservation proof**: the
        `S4KeyedHintikkaInv` fields (`:8752-8766`) with `eBoxNegWitness`/`eDiamondPosWitness`
        restated over `accWithReds acc red`, plus two fields mirroring conjuncts 5/6.
  - [x] Extend `artifacts/s4subtractive3.lean` so `condGStar`/`condFStar` (`:226-239`) are
        **syntactically aligned** with the final conjunct 5/6 statements — same quantifier order,
        same `red`-membership premise, same cone relation — and re-run all three corpora.
  - [x] Record the re-run's verbatim `#eval` output in this plan under
        `#### Phase 1 Statement Validation`.
- **Estimated output:** ~120 lines of Lean plus a ~60-line probe delta plus a ~25-line measurement
  record.
- **Done when:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking` is clean with the new
  declarations, **no `sorry` and no proof beyond `rfl`/`simp`-level bridges** exists in the phase's
  output, and the realigned probe reports **0 failures** for conjuncts 5/6 on all three corpora. If
  the realigned probe reports a **non-zero** failure count, the phase ends `[BLOCKED]` — the final
  statement shape is falsified and the route must be escalated before any proof work.
- **Timing:** 2-3 hours
- **Depends on:** none

#### Phase 1 Statement Validation

Landed declarations (`Cslib/Logics/Modal/Tableau/LoopChecking.lean`, inserted after
`S4KeyedHintikkaInv_weaken`, before "## Phase 7: Single-Step Invariant Preservation"):
`Reds`, `accWithReds`, `hasEdge_accWithReds_iff`, `modalHintikkaSetS4Sub`,
`S4KeyedSubHintikkaInv`. `lake build Cslib.Logics.Modal.Tableau.LoopChecking` is clean (exit 0,
zero errors). `lake exe checkInitImports` clean. Sorry census over
`Cslib/Logics/Modal/Tableau/*.lean` unchanged at exactly 1 (`FrameSoundness.lean:1244`, untouched
per user decision) -- no new `sorry`, no proof beyond the single `simp only` bridge. No new
axioms (no `axiom` keyword used anywhere in this phase's output).

`condGStar`/`condFStar` (`specs/553_.../artifacts/s4subtractive3.lean`) carry a doc comment
cross-referencing `modalHintikkaSetS4Sub` conjuncts 5/6 field-by-field (red-membership premise,
box/diamond-shaped antecedent, `accWithReds`-cone-via-`reachEdges`/`augEdges`, conclusion) and
were re-run on all three corpora via `lake env lean
specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4subtractive3.lean`
(exit 0). Verbatim output for the three sweep corpora:

```
C6.2: formulas=8532 openLeavesVisited=11139 recordedRedirects=1652
C6.2: (a) witness present at wBlock      -- FAILURES = 0
C6.2: (b) T(□χ)@src -> T(□χ)@wBlock      -- FAILURES = 0   <-- LOAD-BEARING
C6.2: (c) T(□χ)@src -> T(χ)@wBlock       -- FAILURES = 0
C6.2: (d) F(◇χ)@src -> F(◇χ)@wBlock      -- FAILURES = 0
C6.2: (e) F(◇χ)@src -> F(χ)@wBlock       -- FAILURES = 0
C6.2: (g) T(□χ)@src -> T(χ)@u for ALL u acc-reachable from wBlock -- FAILURES = 0   <-- EXACT TRUTH-LEMMA OBLIGATION
C6.2: (f) F(◇χ)@src -> F(χ)@u for ALL u acc-reachable from wBlock -- FAILURES = 0   <-- EXACT TRUTH-LEMMA OBLIGATION
C6.2: (G*) box obligation over ALL u reachable in acc UNION red -- FAILURES = 0   <-- FULL OBLIGATION
C6.2: (F*) dia obligation over ALL u reachable in acc UNION red -- FAILURES = 0   <-- FULL OBLIGATION
C6.2: redirects whose source ALREADY had a genuine acc-successor witness = 24
C7.1: formulas=16850 openLeavesVisited=21750 recordedRedirects=6303
C7.1: (a) witness present at wBlock      -- FAILURES = 0
C7.1: (b) T(□χ)@src -> T(□χ)@wBlock      -- FAILURES = 0   <-- LOAD-BEARING
C7.1: (c) T(□χ)@src -> T(χ)@wBlock       -- FAILURES = 0
C7.1: (d) F(◇χ)@src -> F(◇χ)@wBlock      -- FAILURES = 16
C7.1: (e) F(◇χ)@src -> F(χ)@wBlock       -- FAILURES = 0
C7.1: (g) T(□χ)@src -> T(χ)@u for ALL u acc-reachable from wBlock -- FAILURES = 0   <-- EXACT TRUTH-LEMMA OBLIGATION
C7.1: (f) F(◇χ)@src -> F(χ)@u for ALL u acc-reachable from wBlock -- FAILURES = 0   <-- EXACT TRUTH-LEMMA OBLIGATION
C7.1: (G*) box obligation over ALL u reachable in acc UNION red -- FAILURES = 0   <-- FULL OBLIGATION
C7.1: (F*) dia obligation over ALL u reachable in acc UNION red -- FAILURES = 0   <-- FULL OBLIGATION
C7.1: redirects whose source ALREADY had a genuine acc-successor witness = 253
C7.2: formulas=55299 openLeavesVisited=77852 recordedRedirects=16359
C7.2: (a) witness present at wBlock      -- FAILURES = 0
C7.2: (b) T(□χ)@src -> T(□χ)@wBlock      -- FAILURES = 0   <-- LOAD-BEARING
C7.2: (c) T(□χ)@src -> T(χ)@wBlock       -- FAILURES = 0
C7.2: (d) F(◇χ)@src -> F(◇χ)@wBlock      -- FAILURES = 24
C7.2: (e) F(◇χ)@src -> F(χ)@wBlock       -- FAILURES = 0
C7.2: (g) T(□χ)@src -> T(χ)@u for ALL u acc-reachable from wBlock -- FAILURES = 0   <-- EXACT TRUTH-LEMMA OBLIGATION
C7.2: (f) F(◇χ)@src -> F(χ)@u for ALL u acc-reachable from wBlock -- FAILURES = 0   <-- EXACT TRUTH-LEMMA OBLIGATION
C7.2: (G*) box obligation over ALL u reachable in acc UNION red -- FAILURES = 0   <-- FULL OBLIGATION
C7.2: (F*) dia obligation over ALL u reachable in acc UNION red -- FAILURES = 0   <-- FULL OBLIGATION
C7.2: redirects whose source ALREADY had a genuine acc-successor witness = 490
```

**Verdict: PASS.** `failGStar = 0` and `failFStar = 0` on all three corpora
(1652 + 6303 + 16359 = **24,314** recorded redirects, matching report 04's baseline exactly).
The forward-cone conjuncts 5/6 -- the ones actually landed in `modalHintikkaSetS4Sub` and
`S4KeyedSubHintikkaInv` -- have **zero measured counterexamples** in their final statement form.
(d), the forbidden wrapped-at-target form, still fails (16 + 24 = 40 total, matching report 04's
previously-recorded count) -- expected and correctly NOT used anywhere in the landed statements,
confirming the bifurcation was necessary. Per the phase's done-when criterion, Phase 1 proceeds
to `[COMPLETED]`; Phases 2 and 3 (the two decision gates) are unblocked for wave 2.

---

### Phase 2: DECISION GATE A — `modalTruthLemmaS4Sub` over `ReflTransGen (acc ∪ red)` [COMPLETED]

- **Goal:** Prove, standalone and with **no driver dependency**, that the Phase 1 predicate feeds a
  truth lemma. This is report 04 §9's mandatory viability condition.
- **Tasks:**
  - [x] Weaken the hypotheses of the six landed bridges `hintikkaS4_box_pos_self` (`:6779`),
        `_step` (`:6599`), `_reflTransGen` (`:6985-6998`), `hintikkaS4_dia_neg_self` (`:6863`),
        `_step` (`:6686`), `_reflTransGen` (`:7001-7013`) from `modalHintikkaSetS4 φ₀ b acc` to the
        bare **saturation conjunct**. Verified prerequisite: `hintikkaS4_box_pos_step` destructures
        `hH` as `⟨_, hrule, _⟩`, so it uses conjunct 2 only. This is **mandatory**, not cosmetic:
        conjuncts 3/4 over bare `acc` are false for the subtractive driver. Strictly weaker
        hypotheses cannot break any existing caller — confirm with a clean project-wide
        `lake build`. **Landed as new `def modalS4Saturated` (the named bare saturation conjunct,
        shared verbatim by `modalHintikkaSetS4` and `modalHintikkaSetS4Sub`) plus two one-line
        projection bridges `modalHintikkaSetS4_saturated`/`modalHintikkaSetS4Sub_saturated`
        (`hH.2.1` off either predicate), rather than editing `modalHintikkaSetS4`'s own body** —
        this is a Plan Deviation from the literal "weaken the hypotheses" wording (see Plan
        Deviations in the Phase 2 summary): the six bridges' signatures were changed exactly as
        specified, but the two existing callers in `modalTruthLemmaS4`
        (`FrameCompleteness.lean`, box/diamond cases) needed their `hH` argument adjusted to
        `modalHintikkaSetS4_saturated φ₀ b acc hH` — a one-line, semantically-inert accommodation
        of the strictly-weaker parameter type, confirmed by a clean scoped rebuild of both files.
  - [x] `lemma reflTransGen_accWithReds_first_red` (the path decomposition): a
        `ReflTransGen (accWithReds acc red)`-path `w ⤳ u` either stays entirely inside
        `acc.hasEdge`, or splits as `w ⤳_acc x`, a `red` entry `(x, wB, s, φ)`, and a residual
        `ReflTransGen (accWithReds acc red)`-path `wB ⤳ u`. Prove by
        `Relation.ReflTransGen.head_induction_on` plus `hasEdge_accWithReds_iff`. **Landed
        verbatim to spec** in `LoopChecking.lean`.
  - [x] `lemma modalTruthLemmaS4Sub (φ₀) (b) (acc) (red) (hH : modalHintikkaSetS4Sub φ₀ b acc red) :
        ∀ φ w, (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS4 b (accWithReds acc red)) w φ) ∧
        (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS4 b (accWithReds acc red)) w φ)`. Transcribe
        `modalTruthLemmaS4`'s complexity induction (`FrameCompleteness.lean:232-394`), replacing
        exactly the box-positive and diamond-negative cases (`:375-394`) with: decompose the path;
        the `acc`-only case uses the weakened bridge; the first-`red`-hop case uses the weakened
        bridge to reach `x`, then conjunct 5 (resp. 6) on the residual cone. **Landed with one
        necessary refinement** (see Plan Deviations): the "weakened bridge" that carries the
        formula from `w` to the `red`-hop's source `x` must preserve the *wrapped* shape
        (`T(□ψ)@x`/`F(◇ψ)@x`), since conjuncts 5/6 require the wrapped antecedent at the source —
        `hintikkaS4_box_pos_reflTransGen`/`hintikkaS4_dia_neg_reflTransGen` instead *unwrap* at the
        endpoint (that is their entire purpose for the `acc`-only case), so two new box/diamond-
        **preserving** path bridges (`hintikkaS4_box_pos_reflTransGen_boxed`/
        `hintikkaS4_dia_neg_reflTransGen_boxed`, `LoopChecking.lean`) were added, mirroring the
        existing bridges' induction with the `refl` case returning `hmem` unchanged instead of
        invoking `_self`.
  - [x] `theorem modalOpenBranchS4Sub_countermodel` — a ~12-line transcription of
        `modalOpenBranchS4_countermodel` (`FrameCompleteness.lean:401-408`) at
        `accWithReds acc red`, reusing `extractModelS4_refl`/`_trans` (`FC:160-178`) **verbatim**.
        **Landed verbatim to spec.**
  - [x] Record the verdict under `#### Phase 2 Verdict`, whether positive or negative.
- **Estimated output:** ~300 lines. **Split rule:** if the path-decomposition lemma plus the two
  replaced truth-lemma cases exceed 300 lines, split into 2.1 (hypothesis-weakening + path
  decomposition) and 2.2 (truth lemma + countermodel) rather than growing the phase. **Not
  triggered**: total new/changed Lean is ~230 lines across the two files.
- **Done when:** `modalTruthLemmaS4Sub` and `modalOpenBranchS4Sub_countermodel` are **sorry-free**,
  `lake build` is clean project-wide, and `lean_verify` on both reports only standard axioms.
  **Met, with one documented scope caveat**: see `#### Phase 2 Verdict` for the full-project
  `lake build` caveat (a concurrent, explicitly out-of-scope failure in
  `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`).
- **Kill criterion:** if either the box-positive or the diamond-negative case cannot be derived from
  conjuncts 5/6, **revert the attempt (commit no `sorry`)**, mark the phase `[BLOCKED]`, record the
  exact `lean_goal` state and the tactics tried under `#### Phase 2 Verdict`, and **escalate to the
  user**. The honest fallback is route (1), **not** route (2′). Do not weaken conjuncts 5/6 towards
  the wrapped (b)/(d) forms to make the induction go through. **Not triggered — both cases derive
  cleanly from conjuncts 5/6 once the box/diamond-preserving path bridges supply the correctly
  wrapped antecedent at the `red`-hop's source.**
- **Timing:** 4-5 hours
- **Depends on:** 1

#### Phase 2 Verdict

**Verdict: PASS — route (3) survives Decision Gate A.** The Phase 1 bifurcated predicate
`modalHintikkaSetS4Sub` does feed a truth lemma over `ReflTransGen (accWithReds acc red)`, proved
without weakening conjuncts 5/6 toward the forbidden wrapped-at-target form and without any
`sorry`.

**What was landed** (`Cslib/Logics/Modal/Tableau/LoopChecking.lean` and
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`):

- `modalS4Saturated` (`LoopChecking.lean`): the bare saturation conjunct, named so it can be
  shared by `modalHintikkaSetS4` and `modalHintikkaSetS4Sub` alike.
- `modalHintikkaSetS4_saturated` / `modalHintikkaSetS4Sub_saturated` (`LoopChecking.lean`):
  one-line `.2.1` projection bridges from either full predicate to `modalS4Saturated`.
- The six bridges `hintikkaS4_{box_pos,dia_neg}_{self,step,reflTransGen}` (`LoopChecking.lean`):
  hypothesis re-stated from `modalHintikkaSetS4 φ₀ b acc` to `modalS4Saturated φ₀ b acc` —
  strictly weaker, confirmed by a clean scoped rebuild; the two existing callers in
  `modalTruthLemmaS4` (`FrameCompleteness.lean`) updated to project via
  `modalHintikkaSetS4_saturated`.
- `reflTransGen_accWithReds_first_red` (`LoopChecking.lean`): the path-decomposition lemma, to
  spec.
- `hintikkaS4_box_pos_reflTransGen_boxed` / `hintikkaS4_dia_neg_reflTransGen_boxed`
  (`LoopChecking.lean`, new — see Plan Deviations): box/diamond-*preserving* path bridges,
  needed because conjuncts 5/6 require the wrapped antecedent `T(□ψ)@x`/`F(◇ψ)@x` at the
  `red`-hop's source `x`, not the unwrapped `T(ψ)@x`/`F(ψ)@x` the existing (unwrapping) bridges
  produce.
- `modalTruthLemmaS4Sub` (`FrameCompleteness.lean`): the full complexity induction, to spec —
  every non-modal case transcribed verbatim (they depend only on conjunct 2, which is identical
  in shape between the two predicates and evaluated over `acc` in both); the box-positive and
  diamond-negative cases case-split on `reflTransGen_accWithReds_first_red`, using the ordinary
  (unwrapping) bridge on the `acc`-only disjunct and the new boxed bridge plus conjunct 5/6 on
  the `red`-hop disjunct.
- `modalOpenBranchS4Sub_countermodel` (`FrameCompleteness.lean`): to spec, verbatim transcription.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` — clean, zero errors.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` — clean, zero errors.
- `lean_verify` on `modalTruthLemmaS4Sub`: `{"axioms":["propext","Classical.choice","Quot.sound"]}`
  — standard axioms only (the one `"opaque"` source-scan hit is a pre-existing docstring mention
  at `FrameCompleteness.lean:2514`, unrelated to this phase's code, not a real `opaque`
  declaration).
- `lean_verify` on `modalOpenBranchS4Sub_countermodel`: identical result, standard axioms only.
- `grep -rn '\bsorry\b' Cslib/Logics/Modal/Tableau/*.lean` (discounting doc/comment mentions):
  exactly one hit, `FrameSoundness.lean:1244`, unchanged from before this phase (the
  user-retained marker; untouched, per the Postmortem Constraints and Preserved Assets P12).
- `lake exe lint-style Cslib/Logics/Modal/Tableau/{LoopChecking,FrameCompleteness}.lean` — clean.
- `grep -rln` for all six bridge names across `Cslib/` and `CslibTests/` confirms the only two
  files referencing them are `LoopChecking.lean` and `FrameCompleteness.lean` — no hidden caller
  elsewhere in the tree could have broken.

**Caveat — full-project `lake build` is currently blocked by a concurrent, explicitly
out-of-scope failure, not by this phase's work**: `lake build` (whole project) fails with exactly
one target error, `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1329:2:
Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)`. This file is explicitly
out-of-scope for this task (Overview: *"The concurrent session's
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` and `Cslib.lean` are out of scope"*), was
never touched by this phase, and is actively being repaired by a concurrent session (task 554,
phase 14, "general id / efq" blocker — same session's `task554-id-repair` dispatch). Because the
full-project `.olean` set is consequently incomplete, `lake exe checkInitImports` and
`lake shake` (both of which require a fully up-to-date project build) could not be run to
completion this dispatch; `lake exe lint-style`, scoped to the two touched files, was run
directly and is clean. This is recorded here rather than treated as a Phase 2 failure because
(a) the plan itself declares this file out of scope, (b) both files this phase actually wrote to
build cleanly in isolation, and (c) no caller anywhere in the tree references the six weakened
bridges outside those two files (verified above). Re-run `lake exe checkInitImports` and
`lake shake` once the concurrent Nested/Soundness fix lands.

**Consequence**: Gate A does not kill route (3). Phase 3 (Gate B, establishment) remains
independently gated and is unblocked for a separate wave-2 dispatch, per the plan's own
"Gates A and B are independent" statement. No phase after 2 was scaffolded around this positive
outcome, consistent with the plan's risk mitigation.

---

### Phase 3: DECISION GATE B — the standalone redirect forward-cone transfer lemma [BLOCKED]

- **Goal:** Prove, standalone and with **no driver dependency**, that conjuncts 5/6 hold at a
  blocked step; or name the exact missing fact.
- **Tasks:**
  - [x] Land the two **free** transfers first, as near-transcriptions of
        `modalStepBranchS4Keyed_blocked_witness_mem`'s 15-line proof (`:8806-8824`):
        - `blockedRedirect_unwrapped_boxPos_mem`: from `hkL : keyLowerBd`-shaped and
          `hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock`, for every `χ` with
          `(pos, χ) ∈ signedSubfmls φ₀` and `⟨.pos, .box χ, src⟩ ∈ b`, conclude
          `⟨.pos, χ, wBlock⟩ ∈ b`. **Verified derivation chain** (read in this planning run):
          `blockingWorldS4Keyed_eq_birthContent` (`:514`) gives `wBlock`'s recorded key
          `= successorBirthContent φ₀ b s φ src`; `successorBirthContent` (`:384-391`) puts
          `(pos, χ)` in that key exactly when `⟨.pos, .box χ, src⟩ ∈ b`; `keyLowerBd` sends it into
          `relevantSetFinset φ₀ b wBlock` (`:333-337`), whose membership *is* `⟨.pos, χ, wBlock⟩ ∈ b`.
          This is condition (c), measured **0 failures / 24,314**.
        - `blockedRedirect_unwrapped_diaNeg_mem`: the dual, condition (e), also **0 / 24,314**.
  - [x] State the cone extension as a standalone lemma over abstract hypotheses about
        `(b, acc, red, keys)` — the guard `some` contract, `keyLowerBd`, the saturation conjunct
        over `acc`, and whatever additional threaded content proves necessary — concluding
        conjuncts 5 and 6. Follow v3 Phase 2's pattern of a driver-independent statement: it is what
        made that gate return a decisive verdict in one dispatch.
  - [x] Attempt the proof. **Record explicitly** which of the following the cone extension needs,
        because this determines the verdict: (i) nothing beyond the free transfers plus
        `acc`-saturation → gate passes outright; (ii) a nameable additional invariant on recorded
        redirects → gate passes with a Phase 3b; (iii) a fact about the ambient branch that no
        threaded invariant can supply → gate fails. **Outcome (iii) — see verdict below.**
  - [x] Record the verdict, with the exact `lean_goal` state at any blocker, under
        `#### Phase 3 Verdict`.
- **Estimated output:** ~250 lines. **Split rule:** if the two free transfers plus the cone lemma
  exceed 300 lines, split into 3.1 (the two unwrapped transfers, which are the certain part) and
  3.2 (the cone extension, which is the gate) rather than growing the phase. **Not triggered**:
  the free transfers landed at 73 lines; the cone extension was refuted, not landed.
- **Done when:** the two unwrapped-transfer lemmas **and** the cone lemma are sorry-free and the
  scoped `lake build Cslib.Logics.Modal.Tableau.LoopChecking` is clean. **Partially met**: the two
  free transfers are landed sorry-free and the scoped build is clean; the cone lemma is refuted
  (outcome iii), so it is not landed at all — no `sorry` was committed for it.
- **Kill / branch criterion:** outcome (i) → proceed. Outcome (ii) → **do not proceed to Phase 4**;
  add Phase 3b with the named invariant's exact statement, and check that statement against the
  probe (extending `s4subtractive3.lean`) before dispatching it. Outcome (iii) → **revert the
  attempt (commit no `sorry`)**, mark `[BLOCKED]`, escalate. If only the box half closes and the
  diamond half does not, that is outcome (iii): **do not** fall back to the wrapped (d) form, which
  has 40 measured counterexamples. **Outcome (iii) obtains — attempt reverted, phase `[BLOCKED]`,
  escalating per this criterion.**
- **Timing:** 4-5 hours
- **Depends on:** 1

#### Phase 3 Verdict

**Verdict: FAIL — route (3) does not survive Decision Gate B as stated. The forward-cone
conjuncts (5/6) of `modalHintikkaSetS4Sub` cannot be established from `keyLowerBd` +
`modalS4Saturated` + the guard's `some` contract, nor from any nameable strengthening of
`red`'s bookkeeping invariant that stops short of adding the redirect edge to `acc` (which the
Postmortem Constraints forbid absolutely, as the shared defect of all three prior failed
routes).**

**What was landed (kept)**: the two free transfers, sorry-free, committed at `task 553 phase
3.1`:
- `blockedRedirect_unwrapped_boxPos_mem` (`LoopChecking.lean:9060-9090` in the post-edit file):
  from `hkL : keyLowerBd`-shaped, `hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some
  wBlock`, `(pos, χ) ∈ signedSubfmls φ₀`, `⟨.pos, .box χ, src⟩ ∈ b`, concludes the **unwrapped**
  `⟨.pos, χ, wBlock⟩ ∈ b`. This is exactly condition (c) (0/24,314), and it is the reflexive
  (`u = wBlock`) base case of conjunct 5 only.
- `blockedRedirect_unwrapped_diaNeg_mem`: the dual for condition (e) (0/24,314), the reflexive
  base case of conjunct 6.

**What was attempted and reverted**: a standalone cone-extension lemma
`blockedRedirect_boxPos_forwardCone_probe`, generalized over the induction's current point,
carrying `⟨.pos, .box χ, w⟩ ∈ b` (the **wrapped** shape) so it could be pushed across further
`acc`-edges via the existing bridge `hintikkaS4_box_pos_step`, and re-invoking the free transfer
at any further `red`-hop under the most generous plausible additional hypothesis available,
`hredValid : ∀ r ∈ red, blockingWorldS4Keyed φ₀ b keys r.2.2.1 r.2.2.2 r.1 = some r.2.1` (every
recorded `red` entry reflects a genuine guard decision — itself a nameable invariant the driver
could maintain). Proof by `Relation.ReflTransGen.head_induction_on`, splitting each edge via
`hasEdge_accWithReds_iff` into an `acc`-edge or a `red`-edge, mirroring
`reflTransGen_accWithReds_first_red`'s decomposition.

**Exact blocker, `lean_goal` at the stuck point** (case `head.inr`, the red-hop branch, after
the induction has advanced through zero-or-more `acc`-edges and hit a first further `red`-hop
`(a✝, c✝, rs, rphi) ∈ red` past the original `wBlock`):

```
ih : { sign := Sign.pos, formula := □χ, label := c✝ } ∈ b →
     { sign := Sign.pos, formula := χ, label := u } ∈ b
hunwrapped : { sign := Sign.pos, formula := χ, label := c✝ } ∈ b
⊢ { sign := Sign.pos, formula := χ, label := u } ∈ b
```

`ih` demands the **wrapped** fact `⟨.pos, .box χ, c✝⟩ ∈ b` to continue propagating (exactly
mirroring `hintikkaS4_box_pos_step`'s requirement — only wrapped `.box`-shaped formulas persist
across `acc`-edges in this Hintikka apparatus). `hunwrapped` — the strongest fact the free
transfer can produce at a redirect target, even granting `hredValid` — is only the **unwrapped**
`⟨.pos, χ, c✝⟩ ∈ b`. There is no bridge from unwrapped `χ`-membership back to wrapped
`.box χ`-membership: `exact hunwrapped` fails on a genuine type mismatch (not a search-tactic
gap), `assumption` fails, and `aesop`'s exhaustive search fails outright on the goal with every
available hypothesis in context. This is not a proof-search shortfall: asserting such a bridge
(`χ@w ∈ b → □χ@w ∈ b`, unconditionally) would be **unsound** — an ordinary formula being true at
a world does not make it necessary there in S4 (only `□χ → χ` and `□χ → □□χ` are valid; the
converse fails for arbitrary formulas), so no sound lemma of this shape can exist anywhere in
the library, threaded or not.

**Why no nameable invariant on `(keys, red)` can close this**, generalizing the specific
blocker: keyLowerBd (`k ⊆ relevantSetFinset φ₀ b w`, `relevantSetFinset` a `Finset (Sign ×
Proposition Atom)` of *unwrapped* signed-formula membership) is definitionally incapable of
producing a *wrapped* fact `⟨.pos, .box χ, wBlock⟩ ∈ b` — the Finset apparatus only ever
witnesses `⟨p.1, p.2, w⟩ ∈ b` for `p.2` literally equal to the recorded element, and the only
element the box-context-transfer branch of `successorBirthContent` ever records is the
*unwrapped* `(pos, χ)`, never `(pos, .box χ)` (that would need `T(□□χ)@src ∈ b`, a strictly
stronger hypothesis this lemma is not given, and nothing in `modalApplyOneS4`'s rules derives
`T(□□χ)` from `T(□χ)` at the same world without an actual `acc`-edge — which is precisely the
thing route (3) forbids adding). The only mechanism this codebase has for making a formula
persist forward at all is `acc`-edge propagation of an already-wrapped formula
(`hintikkaS4_box_pos_step`/`_dia_neg_step`); the redirect, by design, is never an `acc`-edge.
So establishing the forward cone beyond the immediate (reflexive) blocking target would require
either (a) adding the redirect to `acc` — the single defect shared by all three prior failed
routes, explicitly forbidden — or (b) a wholly new persistence mechanism with no basis in the
current guard/key/red bookkeeping. Neither is a "nameable additional invariant on recorded
redirects" in the sense outcome (ii) contemplates; both are re-openings of settled, forbidden
ground. This is outcome **(iii)**.

**Consistency with the measured 0/24,314**: the measurement is over conditions (c)/(e) only
(the reflexive base case established by the free transfers), not over the full forward cone for
arbitrary `u`. It is not in tension with this verdict — it is exactly the part of conjuncts 5/6
this dispatch confirms holds, and the plan's own caution ("a measurement can never license a
design, only kill it") is what this verdict acts on for the remaining, unmeasured part.

**Consequence**: per the Overview's kill table (row 2) and this phase's kill/branch criterion,
**route (3) is dead as planned.** The probe attempt was reverted before commit (no `sorry`
landed); only the two free transfers (the certain, already-true part, independently useful and
unaffected by this verdict) remain in the tree. Escalating to the user per the Kill Criterion
Note and outcome-(iii) protocol. Phases 4-12 are **not** dispatched, per the plan's explicit
"not scaffolded on a positive verdict" design.

#### Post-Gate-B Triage

Following the Phase 3 Verdict, the user authorized route (1) (canonical/pinned-witness truth
lemma) for a forthcoming plan v5, and separately authorized a bounded cleanup dispatch to
disposition the machinery route (3) left behind: keep what is route-independent, revert what
only serves the dead `red` channel. This explains why `LoopChecking.lean`/
`FrameCompleteness.lean` still contain `Reds`/`accWithReds` machinery with no driver using it —
it is retained infrastructure, not a loose end.

**Kept** (route-independent, moved to a "Route-Independent Remnant" doc comment in
`LoopChecking.lean`):
- `modalS4Saturated` and its projection bridges (`modalHintikkaSetS4_saturated`, and the six
  `hintikkaS4_{box_pos,dia_neg}_{self,step,reflTransGen}` bridges, whose hypotheses were
  already weakened from `modalHintikkaSetS4` to `modalS4Saturated` prior to this triage) —
  strictly weaker hypotheses, strictly better factoring.
- `Reds`/`accWithReds` (`LoopChecking.lean`) — general "accessibility plus a recorded
  extra-edge list" packaging with no route-specific content.
- `hasEdge_accWithReds_iff` and `reflTransGen_accWithReds_first_red` (`LoopChecking.lean`) —
  general `simp`/path-decomposition bridges over that packaging.
- `blockedRedirect_unwrapped_boxPos_mem`/`blockedRedirect_unwrapped_diaNeg_mem`
  (`LoopChecking.lean`) — the sorry-free, standard-axioms-only free transfers landed above;
  true statements about the guard, independent of any route.
- `FrameSoundness.lean:1244` and its `sorry` — retained by standing user decision; untouched,
  remains the only `sorry` in `Cslib/Logics/Modal/Tableau/`.

**Reverted** (served only the dead bifurcated Hintikka predicate / forward-cone obligation):
`modalHintikkaSetS4Sub`, `modalHintikkaSetS4Sub_saturated`, `S4KeyedSubHintikkaInv`
(`LoopChecking.lean`); `hintikkaS4_box_pos_reflTransGen_boxed`,
`hintikkaS4_dia_neg_reflTransGen_boxed` (`LoopChecking.lean`); `modalTruthLemmaS4Sub`,
`modalOpenBranchS4Sub_countermodel` (`FrameCompleteness.lean`).

**Judgement call on `Reds`/`accWithReds`**: both are consumed by the two KEPT general bridges
above (`hasEdge_accWithReds_iff`, `reflTransGen_accWithReds_first_red`), so they could not
simply be deleted. Chose to **keep both as minimal support** for those two bridges (option (a)
of the two offered) rather than restating the bridges over a plain `Accessibility` append and
dropping `Reds`/`accWithReds` (option (b)): `Reds`/`accWithReds` are themselves trivial type
packaging (a bare `abbrev`/one-line `def`) with no route-specific content, so keeping them costs
nothing, while restating both bridges' statements and proofs over an inlined append would be
non-trivial rework for a pure cleanup dispatch.

**Verification**: scoped `lake build Cslib.Logics.Modal.Tableau.LoopChecking` and
`...FrameCompleteness` both clean; `lake exe lint-style` clean on both touched files; sorry
census in `Cslib/Logics/Modal/Tableau/` is exactly 1 (`FrameSoundness.lean:1244`); `lean_verify`
on both `blockedRedirect_unwrapped_*_mem` lemmas reports only `propext`, `Classical.choice`,
`Quot.sound`.

---

### Phase 4: Parallel subtractive rule and ordered stepper threading `red` [IN PROGRESS]

- **Goal:** Land the subtractive rule and the ordered subtractive stepper **beside** the landed
  ones, with the landed drivers byte-for-byte unchanged.
- **Tasks:**
  - [ ] `def modalApplyOneS4KeyedSub` — `modalApplyOneS4Keyed` (`:747-759`) with both blocked arms
        emitting `(.linear [], acc)` instead of `(.linear [], acc.addEdge sf.label wBlock)`
        (variant **S1**, consume — settled). The guard call is unchanged.
  - [ ] The two blocked-`eq` spec lemmas, mirroring `modalApplyOneS4Keyed_boxNeg_blocked_eq` and its
        dia-positive twin (`:763-770`, `:785-793`).
  - [ ] `hintikka_congr_S4Sub` — a **13-line transcription** of `hintikka_congr_S4` (`:7821-7833`).
        Verified prerequisite: `modalHintikkaSetS4`'s conjunct 2 is definitionally `True` at exactly
        the two minting shapes (`:6549-6551`), and `modalApplyOneS4KeyedSub` differs from
        `modalApplyOneS4` **only** at those shapes, so the same `simp_all` closes it.
  - [ ] `def modalStepBranchS4KeyedSubBody` and `def modalStepBranchS4KeyedSubOrdered`, mirroring
        `:1107-1117`'s two-stage shape (`modalNonMintCandidates` scan, then fallback), with the
        return type extended by `Reds`:
        `Option (List (List (SignedFormula …)) × List (List (SignedFormula …)) × Accessibility ×
        List (WorldIndex × Finset (Sign × Proposition Atom)) × Reds)`. On a blocked arm append
        `(sf.label, wBlock, s, φ)` to `red`; on every other arm carry `red` unchanged. This is the
        threading shape `artifacts/s4subtractive3.lean:76-103` already runs.
  - [ ] `modalStepBranchS4KeyedSubOrdered_cases` — the structural split every later lemma factors
        through, transcribing `:1124-1135`.
  - [ ] Append to `blockingWorldS4Keyed`'s docstring (`:466-505`) a pointer to the subtractive
        repair. **Leave the existing defect description at `:478-492` intact** as historical record.
- **Estimated output:** ~220 lines.
- **Done when:** sorry-free; `lake build Cslib.Logics.Modal.Tableau.LoopChecking` clean;
  `modalApplyOneS4Keyed`, `modalStepBranchS4Keyed`, `modalStepBranchS4KeyedOrdered` and
  `blockingWorldS4Keyed` verified unchanged apart from the docstring append (`git diff` inspected).
- **Timing:** 2-3 hours
- **Depends on:** 2, 3

---

### Phase 5: `S4LoopInvSub` (nine fields, no `outDegEq`) and its per-step preservation [NOT STARTED]

- **Goal:** Land the subtractive loop invariant and prove the ordered subtractive stepper preserves
  it, carrying the `outDegEq` drop explicitly.
- **Tasks:**
  - [ ] **Zero-consumer verification step, run and recorded first** (this is its own deliverable,
        not a footnote): re-verify by `grep -n '\.outDegEq' Cslib/Logics/Modal/Tableau/*.lean` that
        the field is *provided* only at `:7546` and `:7610` and **consumed nowhere** in the S4 line;
        and re-read `modalExpMeasure_step_lt_S4Keyed`'s hypothesis list (`:9502-9520`) confirming it
        takes `hb`/`hknown`/`hWC`/`hKT`/`hKD`/`hKI` and **not** `outDegEq`. Record both outputs in a
        source comment beside `S4LoopInvSub` and in the phase handoff. If a consumer *is* found, do
        not proceed — the drop is unsound and the phase ends `[BLOCKED]`.
  - [ ] `structure S4LoopInvSub` — `S4LoopInv`'s (`:7047-7080`) nine fields other than `outDegEq`,
        with the two edge **upper** bounds `accFresh` / `accKnown` carried over unchanged (they get
        *strictly weaker* with fewer edges, so their proofs shrink), and `red` present as an index
        only where a field mentions it (none of the nine do — record that fact).
  - [ ] `modalStepBranchS4KeyedSubOrdered_preserves_S4LoopInvSub`, factoring through
        `…_cases`. The four `keys` fields transcribe unchanged, because the guard is unchanged and
        `blockingWorldS4Keyed_none_fresh` (`:538`) is a statement about the guard.
  - [ ] Do **not** touch `S4LoopInv` or `modalStepBranchS4_preserves_outDegEq` (`:4917-5104`).
- **Estimated output:** ~300 lines. **Split rule:** if preservation of the nine fields exceeds 300
  lines, split into 5.1 (structure + the four `keys` fields + `accFresh`/`accKnown`) and 5.2
  (`bClosure`/`eClosure`/`eNodup`-family) rather than growing the phase.
- **Done when:** sorry-free; scoped `lake build` clean; the zero-consumer check recorded; landed
  `S4LoopInv` and its preservation lemmas unchanged.
- **Timing:** 3-4 hours
- **Depends on:** 4

---

### Phase 6: World bound, `bClosure`, and the measure step for the subtractive driver [NOT STARTED]

- **Goal:** Re-derive fuel sufficiency for the subtractive ordered stepper, by transcription.
- **Tasks:**
  - [ ] Instantiate `modalKnownWorlds_length_le_worldBoundS4` (`:6459`) and
        `modalStepBranchS4_worldBound` (`:6501`) for the subtractive stepper. **Verified premise**:
        all four consumed `S4LoopInv` fields (`keysTotal` `:7063`, `keyLowerBd` `:7068`,
        `keysDistinct` `:7073`, `keysInUniverse` `:7076`) mention **no `acc`**, so the pigeonhole
        argument is edge-independent and `modalWorldBoundS4` (`:229`) is retained verbatim.
  - [ ] `modalExpMeasure_step_lt_S4KeyedSub` — instantiate `:9502-9520`'s hypothesis list from
        `S4LoopInvSub`. The blocked S1 step still grows `e` (`newExps = e ++ [sf]`, cf. `:978`),
        which is the decrease witness.
  - [ ] `modalExpMeasure_entry_le_fuelS4` (`:8486`) applies verbatim; confirm and record rather than
        re-derive.
  - [ ] Explicitly confirm in a source comment that no declaration in this phase mentions `red` or
        `accWithReds` — termination is edge-independent and must stay so.
- **Estimated output:** ~200 lines.
- **Done when:** sorry-free; scoped `lake build` clean; the `red`-free confirmation recorded.
- **Timing:** 2-3 hours
- **Depends on:** 5

---

### Phase 7: The subtractive expander, the leaf result carrying `red`, and the entry point [NOT STARTED]

- **Goal:** Land `modalExpandBranchesS4KeyedSubOrdered` threading `red` per branch, and an entry
  point whose type matches every other driver's, **without touching `Saturation.lean`**.
- **Tasks:**
  - [ ] **First task: pick the leaf-result design against a stated criterion.** `ModalTableauResult`
        (`Saturation.lean:82`) carries only `(b, acc)` and is consumed by 8 files — it is
        read-only.
        - **Option A (default): union-at-return.** Thread `red` alongside `keys`; the saturated arm
          returns `.openBranch b (accWithReds a red)` and the `fuel = 0` base case likewise. The
          *threaded* `acc` stays clean, so soundness triviality is preserved (the soundness
          statement never inspects the `.openBranch` payload). Zero new types.
        - **Option B: a new S4-keyed-local result type.** `inductive ModalTableauResultRed` carrying
          `(b, acc, red)`, used by the expander only, with
          `modalTableauS4KeyedSub : Proposition Atom → ModalTableauResult Atom` projecting it.
        - **Criterion**: choose A unless some Phase 10/11 obligation needs `acc` and `red`
          *separately* at the leaf. Verified starting point: `modalOpenBranchS4_countermodel`
          (`FrameCompleteness.lean:401-408`) consumes only the Hintikka predicate, and
          `modalExpandBranchesS4Keyed_openBranch_initial_mem` (`:10221-10348`) mentions no `acc`, so
          A looks sufficient. **Record the decision and its justification in a source comment**;
          switching later is a rework of Phases 10-11.
  - [ ] `def modalExpandBranchesS4KeyedSubOrdered`, mirroring `:7739-7789`'s `processNext` shape with
        a fifth threaded list `pendingReds`/`doneReds`, replicated across a `.branching` split's
        children exactly as `keys'` is.
  - [ ] `def modalTableauS4KeyedSub (φ : Proposition Atom) : ModalTableauResult Atom`, seeding
        `keys := [(0, ∅)]` (**not** `[]` — `S4LoopInv.keysTotal`, per the correction recorded at
        `:7800-7810`) and `red := []`, with fuel `modalFuelS4 φ`.
  - [ ] `modalExpandBranchesS4KeyedSubOrdered_openBranch_initial_mem` — the `F(φ₀)@0 ∈ b` fact,
        transcribing `:10221-10348` (128 lines, `acc`-free, so it transcribes cleanly).
- **Estimated output:** ~300 lines. **Split rule:** if the expander plus the initial-membership
  lemma exceed 300 lines, split into 7.1 (expander + entry point) and 7.2 (initial membership).
- **Done when:** sorry-free; `lake build` clean project-wide; `Saturation.lean` untouched (`git
  diff` empty for it); the landed expanders and entry points unchanged.
- **Timing:** 3-4 hours
- **Depends on:** 4

---

### Phase 8: Soundness capstone at full `branchSatisfiableIn s4FC` [NOT STARTED]

- **Goal:** `modalTableauS4KeyedSub_sound : modalTableauS4KeyedSub φ = .closed → s4Valid φ`, at
  **full** `branchSatisfiableIn s4FC` strength, with no weakening anywhere.
- **Tasks:**
  - [ ] `def S4SubSoundSpec (apply : RuleApply Atom) : Prop` — the analogue of `S5SoundSpec`
        (`FrameSoundness.lean:2256-2261`) whose second disjunct is
        `apply sf b acc = (RuleResult.linear [], acc)`: **no formula and no edge**. Prove
        `modalApplyOneS4KeyedSub_s4SubSoundSpec` by the same shape as
        `modalApplyOneS5w_s5SoundSpec` (`:2273-2287`).
  - [ ] Per-step preservation. The blocked arm's obligation is
        `branchSatisfiableIn s4FC b acc → branchSatisfiableIn s4FC b acc`, discharged by `id`
        (verified: neither `branchSatisfiableIn` `:110-118` nor the invariant mentions `e`). The
        remaining arms consume the landed, sorry-free, full-strength lemmas:
        `modalApplyOne_boxPos_sound` (`SoundnessStep.lean:446-459`, **no `FC` parameter**),
        `modalApplyOne_diaNeg_sound`, `branchSatisfiableIn_reflFC_boxPos_mem`
        (`FrameSoundness.lean:973`), `branchSatisfiableIn_s4FC_boxPos_trans_mem` (`:1085-1100`,
        `IsTrans` only), `branchSatisfiableIn_s4FC_diaNeg_trans_mem` (`:1106-1123`).
  - [ ] The fuel induction over `modalExpandBranchesS4KeyedSubOrdered`'s own shape. **Use the S5Gen
        ladder as a TEMPLATE, not a drop-in**: verified in this planning run that
        `modalExpandBranchesGen_closed_unsatIn` (`:731`) and `modalTableauS5Gen_sound` (`:3317`) are
        stated over `modalTableauGen`/`modalExpandBranchesGen`, which thread neither `keys` nor
        `red`.
  - [ ] `theorem modalTableauS4KeyedSub_sound`.
  - [ ] **Falsification test for the plan's central claim** (see Postmortem Constraints): `grep -n
        'red\|accWithReds\|Reds'` over every declaration this phase adds must return **zero hits**,
        and `S4SubSoundSpec`'s statement must mention only `acc`. Record the grep output verbatim in
        the phase handoff. A non-zero result means the obligation is back inside the
        soundness-tracked structure — escalate, do not patch.
  - [ ] Do **not** touch `branchSatisfiableIn_s4FC_ancestor_redirect` or its `sorry` at `:1244`.
- **Estimated output:** ~400 lines. **Split rule:** if the spec plus per-step preservation plus the
  fuel induction exceed 400 lines, split into 8.1 (`S4SubSoundSpec` + per-step preservation) and
  8.2 (fuel induction + capstone) rather than growing the phase.
- **Done when:** `modalTableauS4KeyedSub_sound` is sorry-free; `lake build` clean project-wide;
  `lean_verify` reports only standard axioms; the axiom-count baseline captured at phase start is
  byte-identical at phase end; the falsification grep returns zero hits; the sorry count in
  `Cslib/Logics/Modal/Tableau/` is still exactly 1.
- **Timing:** 5-6 hours
- **Depends on:** 5, 7

---

### Phase 9: `S4KeyedSubHintikkaInv` preservation across the subtractive ordered stepper [NOT STARTED]

- **Goal:** Prove the Phase 1 invariant is preserved by every arm of
  `modalStepBranchS4KeyedSubOrdered` — the analogue of
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` (`:9006-9340`, 335 lines).
- **Tasks:**
  - [ ] Transcribe the non-blocked arms from `:9006-9340`, replacing `acc` with
        `accWithReds acc red` in the witness fields only.
  - [ ] The two blocked arms (`:9074-9109` box-negative, `:9157-9192` dia-positive) are the new
        work: where the landed proof produces
        `have hedge : newAcc0.hasEdge sf.label wBlock = true` then `exact ⟨wBlock, hedge, hwitmem⟩`,
        the subtractive proof produces the *`red`* edge — `hasEdge_accWithReds_iff` plus the newly
        appended `red` entry — with `hwitmem` still supplied by the **verbatim reused**
        `modalStepBranchS4Keyed_blocked_witness_mem` (`:8806-8824`).
  - [ ] The two forward-cone fields (conjuncts 5/6) are discharged from **Phase 3's cone lemma**
        (plus Phase 3b's invariant if outcome (ii) fired). Monotonicity across branch/`acc`/`red`
        growth mirrors `S4KeyedHintikkaInv_weaken` (`:8770`-region).
- **Estimated output:** ~350 lines. **Split rule:** if the non-blocked transcription plus the two
  blocked arms plus the two cone fields exceed 350 lines, split into 9.1 (non-blocked arms +
  weakening) and 9.2 (blocked arms + cone fields).
- **Done when:** sorry-free; scoped `lake build` clean.
- **Timing:** 4-5 hours
- **Depends on:** 4, 5

---

### Phase 10: `modalExpandBranchesS4KeyedSubOrdered_hintikka` [NOT STARTED]

- **Goal:** Prove the open leaf of the subtractive driver satisfies `modalHintikkaSetS4Sub` — the
  analogue of `modalExpandBranchesS4Keyed_hintikka` (`:9860-10209`, 350 lines).
- **Tasks:**
  - [ ] Transcribe the fuel induction of `:9860-10209`, threading `red` alongside `keys` through
        every arm (closed branches carry theirs to `done`; a `.branching` split replicates the
        single returned `red'`).
  - [ ] At the saturated arm, discharge the six conjuncts: conjunct 1 from `isModalClosed b =
        false`; conjunct 2 over `acc` from the `none`-return saturation, bridged by
        `hintikka_congr_S4Sub` (Phase 4); conjuncts 3/4 from `S4KeyedSubHintikkaInv`'s witness
        fields (replacing `:10041-10050`'s `hHinv.eBoxNegWitness`/`eDiamondPosWitness` projections);
        conjuncts 5/6 from the invariant's cone fields.
  - [ ] Consume `modalExpMeasure_entry_le_fuelS4` and Phase 6's measure step exactly as `:9860`'s
        landed proof does.
- **Estimated output:** ~350 lines. **Split rule:** if the induction plus the six-conjunct discharge
  exceed 350 lines, split into 10.1 (induction skeleton + conjuncts 1/2) and 10.2 (conjuncts 3-6).
- **Done when:** sorry-free; scoped `lake build` clean.
- **Timing:** 4-5 hours
- **Depends on:** 6, 7, 9

---

### Phase 11: Completeness capstone and the decidability instance [NOT STARTED]

- **Goal:** Land `modalTableauS4KeyedSub_complete`, `s4Valid_decides`, and
  `instDecidableS4Valid` — the downstream consumer this task exists to unblock.
- **Tasks:**
  - [ ] `private lemma modalTableauS4KeyedSub_initial` — the entry invariant, transcribing
        `modalTableauS4Keyed_initial` (`FrameCompleteness.lean:4190-4210`-region) with `red := []`
        (all `red`-indexed fields vacuous at `red = []`).
  - [ ] `theorem modalTableauS4KeyedSub_complete (h : s4Valid φ₀) : modalTableauS4KeyedSub φ₀ =
        .closed`, assembling Phase 10's Hintikka lemma, Phase 7's initial-membership lemma, and
        Phase 2's `modalOpenBranchS4Sub_countermodel`, mirroring `:4265-4301`'s shape.
  - [ ] `theorem s4Valid_decides (φ₀) : s4Valid φ₀ ↔ modalTableauS4KeyedSub φ₀ = .closed` — from
        Phase 8's soundness and this phase's completeness. Mirror `s5Valid_decides`
        (`FrameCompleteness.lean:2407`).
  - [ ] `instance instDecidableS4Valid : Decidable (s4Valid φ₀)`, mirroring `:2412-2420`. No
        `Fintype Atom` assumption.
  - [ ] Update `FrameCompleteness.lean:4159-4177`'s module note: the decidability half is no longer
        out of scope. **Leave the record that `modalTableauS4Keyed_sound` is false as stated
        intact** — it remains true of the *landed* driver.
- **Estimated output:** ~200 lines.
- **Done when:** all four declarations sorry-free; `lake build` clean project-wide; `lean_verify`
  on `s4Valid_decides` reports only standard axioms; `modalTableauS4Keyed_complete` still green.
- **Timing:** 3 hours
- **Depends on:** 2, 10

---

### Phase 12: Empirical regression gate for the landed subtractive driver [NOT STARTED]

- **Goal:** Pin the measured behaviour of the *landed* driver in the repository's own test corpus,
  and re-run the differential sweep against the landed definitions rather than the probe's copies.
- **Tasks:**
  - [ ] Extend `CslibTests/S4LoopGuardRegression.lean` (do **not** rewrite it): `cex` is **OPEN**
        under `modalTableauS4KeyedSub` at fuel 400, while the shipped unordered keyed driver closes
        it; the T, 4 and K axiom instances all **CLOSE**.
  - [ ] Re-run the three-corpus differential sweep by pointing report 04's harness
        (`artifacts/s4subtractive.lean`, `s4subtractive2.lean`) at the **landed**
        `modalStepBranchS4KeyedSubOrdered` instead of the probe's local copy: 2 atoms size ≤ 6
        (8,532), 2 atoms size ≤ 7 (55,299), 1 atom size ≤ 8 (95,730), fuel 100.
  - [ ] **Gates**: `open → closed` must be **0** on every corpus (a soundness regression; fatal).
        `closed → open` must be **0** on every corpus for the *ordered* driver (report 04 measured
        0/0/0 ordered vs 0/0/2 unordered). The guard must be confirmed to **fire** (report 04:
        915 / 7,011 / 15,256 formulas) — verdict agreement on a corpus where the guard never
        triggers is worthless. `keysDistinct` breakage must be 0. Fuel exhaustion must be ≤ the
        shipped driver's (report 04 measured 0 vs 2).
  - [ ] Adjudicate any disagreement with report 04's **independent semantic oracle**
        (`s4subtractive.lean`, self-calibrating to least-countermodel-size 3 for `cex`, matching
        `LoopChecking.lean:473-476`), not by argument.
  - [ ] Record all counts verbatim under `#### Phase 12 Measurements`.
- **Estimated output:** ~120 lines of test Lean plus a ~50-line probe delta plus a ~30-line
  measurement record.
- **Done when:** `lake test` green including `CslibTests.S4LoopGuardRegression`; every gate above
  satisfied with numbers recorded, not prose. Any `open → closed` occurrence ends the phase
  `[BLOCKED]` and escalates immediately.
- **Timing:** 3 hours
- **Depends on:** 7

---

## Testing & Validation

- [ ] `lake build` clean project-wide at every phase boundary.
- [ ] `lake test` green, including `CslibTests.S4LoopGuardRegression`.
- [ ] `lake lint` shows exactly the known pre-existing baseline error in
      `Cslib/Logics/Temporal/Tableau/Saturation.lean` and no others.
- [ ] `lake exe checkInitImports` clean.
- [ ] `lake exe lint-style` clean.
- [ ] `lake exe mk_all --module` reports no update necessary (`Cslib.lean` must stay untouched —
      concurrent session territory).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` on each touched file: zero findings.
- [ ] Sorry count in `Cslib/Logics/Modal/Tableau/` is exactly **1**
      (`FrameSoundness.lean:1244`, user-retained) at every phase boundary.
- [ ] Axiom baseline captured at each phase start with `grep -rn '^axiom' Cslib/ | wc -l` is
      byte-identical at phase end; `lean_verify` on every new top-level theorem reports only
      `propext` / `Classical.choice` / `Quot.sound`.
- [ ] `git diff` confirms `Rules.lean`, `Saturation.lean`, `Branch.lean` and `SoundnessStep.lean`
      are untouched.
- [ ] `git diff` confirms `blockingWorldS4Keyed` and its three contract lemmas are unchanged apart
      from Phase 4's docstring append.
- [ ] `modalTableauS4Keyed_complete` compiles at every commit.
- [ ] Phase 8's falsification grep (`red` / `accWithReds` / `Reds` in the soundness chain) returns
      zero hits.
- [ ] Phase 1's realigned probe and Phase 12's landed-driver sweep both report **0** failures /
      **0** `open → closed`.

## Artifacts & Outputs

- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/04_subtractive-blocking-red-channel.md`
  (this file)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (Phases 1, 2 partial, 3, 4, 5, 6, 7, 9, 10)
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (Phases 2, 11)
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (Phase 8)
- `CslibTests/S4LoopGuardRegression.lean` (Phase 12)
- `specs/553_.../artifacts/s4subtractive3.lean` (extended in Phase 1)
- `specs/553_.../artifacts/s4subtractive.lean`, `s4subtractive2.lean` (re-pointed in Phase 12)
- `specs/553_.../summaries/04_subtractive-blocking-red-channel-summary.md` (on completion)
- `specs/553_.../.orchestrator-handoff.json` (per dispatch)

## Rollback/Contingency

- Every phase lands **beside** existing declarations rather than replacing them, so reverting any
  phase is a targeted deletion of new declarations plus a scoped `lake shake`. The only in-place
  edits in the whole plan are Phase 2's hypothesis-weakening of six landed bridges (strictly weaker,
  so revertible by restoring the original hypothesis) and Phase 4's / Phase 11's docstring appends.
- Phase 2 or Phase 3 `[BLOCKED]` is a **route-level stop, not a rollback**: Phase 1's statements and
  probe realignment remain valuable, no `sorry` is committed, and the escalation to the user carries
  the exact `lean_goal` state. Do not scaffold Phases 4-12 around an unresolved gate.
- Before Phase 7 (the only phase that could change what a downstream file observes at a driver's
  return type), take a snapshot with `bash .claude/scripts/git-snapshot.sh`.
- If Phase 7's Option A (union-at-return) is later found insufficient by Phase 10 or 11, switching
  to Option B is a rework of Phases 10-11 only — Phases 1-9 are unaffected, because none of them
  observes the leaf result.
- No phase deletes any landed declaration. If a phase appears to require one, that is out of scope
  and must be escalated.
