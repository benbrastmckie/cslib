# Implementation Plan: Task #317 (v4 — Sfor-containment dedup + fuel-sufficiency, HARD mode)

- **Task**: 317 - Close the B2 `fuel=0` sorry via the Garg–Genovese–Negri `Sfor`-containment loop-check
- **Status**: [IMPLEMENTING]
- **Effort**: 11 hours
- **Dependencies**: 316 (soundness, landed — TERRITORY HAZARD, see below), 323, 363, 369 (landed). B1 truthLemma (`Scheme.lean:330`) is a *separate* residual, NOT a dependency and NOT in scope. Downstream: 430 (atom-persistence bridge), then 375 (proof-system TFAE edges).
- **Research Inputs**:
  - `specs/317_propositional_tableau_completeness/reports/04_fuel-sufficiency-measure.md` (F-signed measure `P = Σ 3^complexity`; linear world bound `W ≤ complexity+1` = lemma F5; `WellFounded.prod_lex`; the `2^Θ(c²)` step-count crux)
  - `specs/317_propositional_tableau_completeness/reports/05_fuel-sufficiency-literature.md` (Garg–Genovese–Negri `Sfor`-containment technique; `2^|Sub(φ)|` world bound; FMP/mosaic `O(2²ⁿ)`; BibKeys)
- **Artifacts**: `plans/04_sfor-dedup-fuel-sufficiency.md` (this file). Supersedes the BLOCKED Phase 2a of `plans/03_b2-fuel-sufficiency.md`; carries its Phase 1 (B2 `none` case) forward as a Preserved Asset.
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md (CSLib zero-debt)
- **Type**: cslib
- **Lean Intent**: true

## Overview

The build is GREEN with two direct `sorry`s in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`:
line ~330 (B1 truthLemma T-imp, OUT OF SCOPE) and line ~985 (B2 `fuel=0` base case of
`intExpandBranches_openBranch_sat`, THE sorry this plan closes). The B2 `none`-case sorry was
already closed in Phase 1 of plan 03 (commit `26508fe9`) via the `IAllConsistent` invariant — a
Preserved Asset, do NOT recreate.

Two independent spikes (reports 04 code-level, 05 literature) **converged**: the existing fuel
`2^(2·complexity+2)` is INSUFFICIENT for the current loop-check-free `intExpandBranches`, because
`propagatePersistence` copies every T-signed compound to each fresh world under a fresh label, so
`T(∨)` compounds re-split at every world and β-branch out, giving a worst-case step count of
`2^Θ(complexity²)` > the `2^Θ(complexity)` fuel. A `Scheme.lean`-only measure under the current
fuel is provably impossible (report 04, F6).

**User decision (SETTLED, do NOT re-litigate)**: implement the field-standard **`Sfor`-containment
loop-check** (Garg, Genovese & Negri, LICS 2012 — `GargGenoveseNegri2012`). This is the
deduplication the standard procedures use to make step-count = deduplicated-model-size
`≤ 2^|Sub(φ)| = O(2²ⁿ)`, at which point the **existing** `2^(2·complexity+2)` fuel becomes
adequate (report 05, Q2/Q3; the fuel was sized for the *deduplicated* model all along). The fuel
formula stays unchanged, so downstream callers pinned to it are untouched.

**Definition of done**: `Scheme.lean` builds GREEN; sorry ~985 (B2 `fuel=0`) is closed
sorry-free; only sorry ~330 (B1) remains; no new axioms/sorries/placeholders; `Soundness.lean`
(task 316) unedited unless Phase 4 proves it unavoidable (and then only with prominent
coordination flagging); public signature `openBranch_countermodel` stable.

### Research Integration

- **Report 05 (literature, Tier 1)** supplies the design: the `Sfor`-containment termination
  condition — a new world is created only if its forced-formula set is NOT contained in an
  accessible ancestor's; since `Sfor` grows monotonically and has `≤ 2^|Sub(φ)|` values, worlds
  are bounded and re-expansion is cut. Load-bearing citation for the proof comment:
  `GargGenoveseNegri2012` (dedup rationale) + `DershowitzManna1979` (multiset ordering) +
  `ChagrovZakharyaschev1997`/`Fitting1983` (FMP `2^|subfmls|` bound, both PRESENT in
  `references.bib`). The 10 MISSING BibKeys (with ready entries) are in report 05 §Q4; adding the
  two load-bearing ones (`GargGenoveseNegri2012`, `DershowitzManna1979`) is a Phase 6 sub-task.
- **Report 04 (code-level)** supplies the reusable measure apparatus: the F-signed base-3
  potential `P = Σ 3^complexity` (persistence-invariant, F1–F3), the LINEAR world-count bound
  `W ≤ complexity+1` (lemma F5 — reuse where the sharper `2^|Sub(φ)|` is not needed), and
  `WellFounded.prod_lex` (`Mathlib.Order.RelClasses`) for the lexicographic termination object.

#### Source-to-Implementation Mapping (Tier 1 — MANDATORY for this literature-backed task)

| Source claim | BibKey / Report | Lean target | Translation notes |
|---|---|---|---|
| Termination via **containment of the forced-set `Sfor(x)` labelling each world**; new world created only if its `Sfor` is not `⊆` an accessible world's | `GargGenoveseNegri2012` (report 05 §Q1-B, §7) | new dedup helper in `Expansion.lean` (fires in `go`'s `.linearResult`+`newEdge` case, i.e. after `intFImpRule`) | `Sfor(w) := posFormulasAt bPers w` (`Rules.lean:126-128`); accessibility via `isAccessible edges w x`; the prospective new world's forced-set is `{φ} ∪ posFormulasAt bPers w`, obligation `F(ψ)`. Reuse ancestor `x` when `{φ} ∪ Sfor(w) ⊆ Sfor(x)` and `ψ ∉ forced(x)`. |
| `#Sfor values ≤ 2^\|Sub(φ)\|` ⇒ worlds bounded, backward `→R` cannot loop | `GargGenoveseNegri2012`; `ChagrovZakharyaschev1997` FMP (PRESENT) | Phase 5 `intExpandBranches_world_bound_dedup` | With dedup, each created world strictly grows `Sfor` beyond every accessible ancestor; distinct forced-sets over `Sub(φ)` number `≤ 2^\|Sub(φ)\|`. Fallback: report 04 F5 gives the weaker linear `W ≤ c+1` if the `2^\|Sub\|` chain argument proves too heavy in Lean. |
| Deduplicated model size `O(2²ⁿ)` = the fuel's intended magnitude `2^(2·complexity+2)` | `Caleiro2013` §4.3 (report 05); FMP | Phase 6 `intExpandBranches_fuel_sufficient` | Step count collapses to `#worlds × #forced-sets-per-world ≤ 2^\|Sub\| · 2^\|Sub\| = O(2²ⁿ)` once dedup cuts per-world re-splits. The existing fuel `2^(2·complexity+2)` then dominates. |
| Multiset / Dershowitz–Manna ordering for the termination measure | `DershowitzManna1979`; report 04 F4 (`WellFounded.prod_lex`) | Phase 5 measure | Lexicographic `(Sfor-antichain-remaining, intra-world unexpanded count)`; only needed if a flat Nat measure under the new bound will not close — prefer the flat bounded-counter argument (mirrors classical `fuel=0 ⟹ saturated`). |
| G4ip worlds-free weight is NOT used | `TroelstraSchwichtenberg2000` §4.3 (PRESENT) | proof comment only | Record in a code comment WHY the textbook G4ip weight does not transfer (it models no world creation), pre-empting reviewer confusion (report 05 §Q1-A). |

### Prior Plan Reference (plan 03)

Plan 03 closed the B2 `none` case (Phase 1, commit `26508fe9`) and then hit a hard wall at
Phase 2a: its R1 measure gate is BLOCKED because no `Scheme.lean`-only measure fits the current
fuel for the un-deduplicated procedure (confirmed by both spikes). This plan does NOT retry a
`Scheme.lean`-only measure. Instead it widens territory (per the user decision) to add the
`Sfor`-containment dedup that collapses the step count, then proves the existing fuel suffices.
Plan 03's Phases 2a–2d are SUPERSEDED. Plan 03's Postmortem Constraints (anti-overflow R4,
concurrent-edit R5, signature stability, phase sizing, zero-debt, scope fence) are carried forward
**verbatim** below and remain binding.

### Roadmap Alignment

No ROADMAP.md found. Downstream chain: closing B2 (this plan) unblocks **task 430**
(atom-persistence bridge — needs the B2 sorry gone), which unblocks **task 375** (proof-system
TFAE edges). **Coordination note for 430**: 430 reasons about `intExtractValuation`
upward-closure under the world order. The dedup REUSES ancestor worlds instead of creating fresh
ones, which changes the accessibility relation (`edges`) and hence the world structure 430's
atom-upward-closure argument depends on. Phase 3 MUST record precisely how the dedup alters the
countermodel's accessibility relation so 430 can be re-planned against the new structure. Do NOT
plan 430's work here; only flag the interaction.

## Preserved Assets (do NOT recreate — build on these)

The following work is COMPLETE and must not regress:

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| B2 `none` case closed via `IAllConsistent` invariant | `Scheme.lean` (was sorry ~713) | [COMPLETED] | commit `26508fe9`, 2026-07-01 |
| `IAllConsistent` / `IExpandedConsistent` / `ILabelBound` invariant + monotonicity combinators | `Scheme.lean` | [COMPLETED] | sorry-free (plan 03 Phase 1) |
| `IExpandedConsistent_sat` (the bridge: `intStepBranch = none` + invariant → `IBranchSaturation`) | `Scheme.lean` | [COMPLETED] | sorry-free |
| Per-step preservation lemmas (`ILabelBound_extendMany`, `intStepBranch_some_exists`, `intStepBranch_linear_preserves`, `intStepBranch_branch_preserves`, `ILabelBound_applyPersistenceFixpoint`) | `Scheme.lean` | [COMPLETED] | sorry-free |
| `intStepBranch`, `intExpandBranches` + inner `go`, `applyPersistenceFixpoint`, `Branch.extendMany` | `Expansion.lean` | [COMPLETED] | sorry-free scaffolding (pre-dedup shape) |
| `intFImpRule`, `propagatePersistence`, `posFormulasAt`, `intTImpRule`, `isAccessible` | `Rules.lean` | [COMPLETED] | sorry-free |
| Classical template `classicalExpMeasure` / `classicalExpMeasure_step_lt` / `classicalExpandBranches_hintikka` | `Classical/Completeness.lean` | [COMPLETED] | reference-only pattern for the `fuel=0 ⟹ saturated` closing |
| Calculus soundness | `Intuitionistic/Soundness.lean` (task 316) | [COMPLETED] | sorry-free — TERRITORY HAZARD, treat as read-only |

## Goals & Non-Goals

**Goals**:
- Design and implement the `Sfor`-containment loop-check in the intuitionistic tableau expansion
  so no two worlds on a branch have containment-equal forced-sets.
- Keep the existing fuel formula `2^(2·complexity+2)` unchanged; prove it now suffices.
- Close sorry ~985 (B2 `fuel=0` base case) via the dedup-bounded fuel-sufficiency argument.
- Keep the public signature `openBranch_countermodel` (and any other public lemma) stable.
- `Scheme.lean` builds GREEN; only sorry ~330 (B1) remains.

**Non-Goals**:
- **B1 truthLemma T-imp (`Scheme.lean:330`)** — explicitly OUT OF SCOPE; leave its sorry intact.
- Task 430 (atom-persistence bridge) and task 375 (TFAE) — flag the dedup's effect on 430's
  world structure (Phase 3), but do NOT implement them.
- Raising the fuel formula (Option B of the spikes) — the user chose dedup (Option A).
- Editing `Soundness.lean` (task 316) — permitted ONLY if Phase 4 proves it strictly unavoidable,
  and then only with prominent coordination flagging and a scoped commit.
- Re-proving or recreating any Preserved Asset.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **R1 (dominant): the `Sfor`-containment check cannot be stated cleanly against the existing edge-list/world/branch structures.** The check needs "forced-set at a world" and "accessible ancestor" — if these are not computable from `posFormulasAt` + `isAccessible edges` without a data-structure change, the whole design stalls. | H | M | Phase 1 is a dedicated design/spike phase with an explicit **STOP-and-escalate gate** (mirrors plan 03's R1 gate): state the check precisely against `posFormulasAt bPers w` (forced-set) and `isAccessible edges w x` (ancestry). If it cannot be expressed without a new field on `IBranch`/`IEdges`, STOP, mark Phase 1 [BLOCKED], escalate — do NOT invent a parallel data structure or add placeholders. |
| **R2 (second-highest): dedup breaks the countermodel/Hintikka conditions at a reused world.** A reused ancestor must still satisfy the saturation/Hintikka conditions the countermodel extraction (`openBranch_countermodel`, `IBranchSaturation`, `intExtractValuation`) relies on. | H | M | Phase 3 re-verifies the countermodel side: enumerate the lemmas that read the world/accessibility structure and re-prove each for the reused-world case. If a reused world violates a Hintikka condition, the dedup predicate is too aggressive — tighten the containment condition (require `ψ ∉ forced(x)` at the witness) and re-verify. STOP/[BLOCKED] before weakening any countermodel lemma. |
| **R3: dedup forces edits to `Soundness.lean` (task 316 territory).** If soundness lemmas quantify over the concrete expansion output, the dedup could disturb them. | M | L | Soundness is about *rule* soundness (satisfiable branch stays satisfiable), not the search strategy; the dedup adds no rule, it only skips an F(→) firing when subsumed. Phase 4 audits this read-only first; touch `Soundness.lean` ONLY if the audit proves a lemma genuinely breaks, and then flag as a coordination hazard and commit `Soundness.lean` separately. |
| **R4 (anti-overflow): context overflow on the large recursive proofs.** Four prior dispatches overflowed. | H | H | See Postmortem Constraints: scoped+grepped builds only, `offset`/`limit` reads, `lean_multi_attempt` over `lean_goal` dumps, commit at every green, stop-and-handoff the instant context tightens. |
| **R5 (concurrent-edit): multiple orchestrator sessions live in this tree; `Rules.lean`/`Expansion.lean`/`Scheme.lean` may be concurrently edited.** | M | M | `git log -1 -- <file>` + scoped rebuild GREEN before EACH phase; commit ONLY the touched files, never `git add -A`. |
| **R6: world-bound / fuel arithmetic off by a factor.** Relating `#worlds ≤ 2^\|Sub(φ)\|` and step-count to `2^(2·complexity+2)` may be loose. | M | M | Phase 5 proves boundedness with slack (`≤`, never `=`); reuse report 04 F5's linear `W ≤ c+1` as a fallback if the `2^\|Sub\|` chain argument is too heavy. Prove `measure(initial) ≤ fuel`, not equality. |

## Postmortem Constraints (HARD — every phase MUST obey)

Binding rules derived from plan 03's four overflow incidents, the two spikes, and the settled
user decision. Carried forward verbatim from plan 03 (items 1–6), extended for the widened
territory (items 7–9).

**Do NOT**:
1. **ANTI-OVERFLOW (R4).** Never run a raw full `lake build`. Build scoped + grepped ONLY:
   `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"`
   (swap the module for `Expansion` / `Rules` when those are the edited file). Read with
   `offset`/`limit` around the target line ONLY — never whole-file reads of
   `Scheme.lean`/`Expansion.lean`/`Rules.lean`. Prefer `lean_multi_attempt` over repeated
   `lean_goal` dumps. STOP and write a sharp handoff the instant context feels tight — a
   committed green partial IS success.
2. **Do NOT change the fuel formula** `2^(2·complexity+2)` in `Expansion.lean`. The user chose
   dedup precisely so the fuel stays fixed and downstream callers are untouched.
3. **Do NOT touch sorry ~330 (B1)** or any `*/Completeness.lean` bridge sorry that is out of scope.
4. **Do NOT edit `Soundness.lean` (task 316)** unless Phase 4 proves it strictly unavoidable;
   if so, flag prominently and commit it in a SEPARATE scoped commit.
5. **Do NOT introduce any `sorry`, `axiom`, or placeholder lemma.** If the design (Phase 1),
   countermodel re-proof (Phase 3), or bound proof (Phase 5) fails, mark the phase [BLOCKED] and
   hand off (zero-debt).
6. **Do NOT `git add -A`.** Commit only the files a phase actually touched.

**MUST preserve**:
- All Preserved Assets above (the `IAllConsistent` invariant machinery, `IExpandedConsistent_sat`,
  the closed B2 `none` case, the sorry-free scaffolding).
- The public signature of `openBranch_countermodel` (thread any new hypotheses through the
  existing `private` `_aux`/`suffices key` from plan 03 Phase 1, not through public types).
- Calculus soundness (task 316) — its green build must survive.
- The existing green build at every commit boundary.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **Dedup, not fuel-raise.** The `Sfor`-containment loop-check (Option A) is chosen over raising
  the fuel (Option B). Rationale: it keeps the fuel formula and downstream callers stable and is
  the literature-standard device (report 05).
- **`Sfor` = the forced (T-signed) formula set at a world**, computed via `posFormulasAt`;
  ancestry via `isAccessible edges`. No new persistent data structure unless Phase 1 proves the
  existing structures cannot express the check.
- **The G4ip worlds-free weight is not the measure** — worlds are the dominant component (report
  05 §Q1); do not attempt to port the textbook G4ip weight directly.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |

Phases 3 and 4 form the only declared parallel wave: Phase 3 edits `Scheme.lean`/completeness-side
lemmas while Phase 4 audits (and only if unavoidable, edits) `Soundness.lean` — DISJOINT file
territory, so they may run concurrently PROVIDED each observes R5 (single-writer per file,
`git log -1` + rebuild before starting). All other phases touch `Scheme.lean` and/or the shared
`Expansion.lean` and are serialized. Phase 4 is largely read-only (an audit); if it finds no
required edit it is a fast confirmation.

---

### Phase 1: Design the `Sfor`-containment loop-check [COMPLETED]

**Goal**: Produce a precise, code-grounded specification of the dedup — the highest-risk design
decision (R1). No proof obligations closed here; the deliverable is a settled design recorded as a
docstring/comment plus a written STOP-gate verdict.

**Tasks**:
- [x] `git log -1 -- Expansion.lean Rules.lean Scheme.lean`; scoped+grepped rebuild GREEN baseline.
      (Last touching commit: `26508fe9`. Scoped rebuild of `Expansion` module: GREEN.)
- [x] Read (windowed, `offset`/`limit`) `intExpandBranches`/`go` (`Expansion.lean:~210-258`),
      `intFImpRule`/`propagatePersistence`/`posFormulasAt` (`Rules.lean:126-159`), and
      `isAccessible`/`IEdges` — confirm `Sfor(w) := posFormulasAt bPers w` and ancestry via
      `isAccessible edges w x` are the right primitives. CONFIRMED: `go` already carries `bPers`
      and `edges` (pre-extension) in scope at the exact point the check must run; `intFImpRule`
      returns `newForms = [T(φ)@w', F(ψ)@w'] ++ propagatePersistence b w w'` and edge `(w', w)`,
      so `Sfor(w')`, `ψ`, and `w` are all extractable from `newForms`/`newEdge` without
      recomputing or threading anything new through the rule layer.
- [x] **State the check precisely**:
      - *Which set*: the prospective forced-set at the would-be new world `w'` =
        `{φ} ∪ posFormulasAt bPers w` (the `T(φ)` output plus the persistence copies), with
        obligation `F(ψ)`.
      - *Where it fires*: in `go`'s `.linearResult newForms nw' (some newEdge)` branch (the ONLY
        world-creating case, produced by `intFImpRule`), BEFORE `Branch.extendMany`/edge append.
      - *What it returns*: **reuse** an accessible ancestor `x` (via `isAccessible edges w x`) when
        `{φ} ∪ Sfor(w) ⊆ Sfor(x)` AND `ψ ∉ forced(x)` — in which case DO NOT create `w'`; mark
        `F(φ→ψ)@w` expanded and continue the same branch (no new world, no new edge). Otherwise
        create `w'` as today. This guarantees no two worlds on a branch have containment-equal
        forced-sets.
- [x] **STOP-and-escalate gate (R1)**: if the check CANNOT be stated against the existing
      `IBranch`/`IEdges`/`posFormulasAt`/`isAccessible` structures without adding a new persistent
      field, STOP, mark Phase 1 [BLOCKED], write a handoff naming exactly what structure is missing.
      Do NOT invent a parallel structure or add placeholders.
      **GO** — no new persistent field needed; the check is fully expressible with existing
      structures using values already in `go`'s own scope (see docstring below).
- [x] Record the settled design as a docstring on the (not-yet-implemented) helper name
      `intFImpReuseWitness?` (or similar) plus the `GargGenoveseNegri2012` citation and the
      "why not G4ip weight" note. No `.lean` proof code committed this phase (design comment only,
      or a `def` stub with the signature if it typechecks trivially).
      Recorded as a docstring + trivial `none`-returning stub `intFImpReuseWitness?` in
      `Expansion.lean` (between `intStepBranch_result_ne_notApplicable` and the `## Expansion
      Loop` section), citing `GargGenoveseNegri2012` (BibKey not yet in `references.bib` —
      deferred to Phase 6 per this plan). Scoped rebuild of `Expansion` module: GREEN, 0 new
      sorries, 0 new axioms, 0 vacuous definitions (`@[nolint unusedArguments]` used on the
      stub's placeholder-name parameters, matching existing CSLib convention).
- [x] Commit touched files only (likely plan + a design comment/stub): `task 317 phase 1: Sfor-containment dedup design`.

**Estimated output**: ~150 lines (design spec + docstring + gate verdict). **Done when**: the
check is stated against existing structures with a written GO verdict, OR Phase 1 is [BLOCKED]
with a precise missing-structure handoff.

**Phase 1 verdict: GO.** See `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`,
docstring on `intFImpReuseWitness?` (design stub, ~line 181-244), for the full settled design.
Summary: the check fires inside `go`'s existing `.linearResult newForms nw' (some newEdge)`
branch using `bPers`, `edges` (both already in `go`'s parameter scope), and `w = newEdge.2`;
`Sfor(w')` and `ψ` are read directly off `newForms` (no recomputation). **No signature change
to `intFImpRule`, `intApplyRuleFull`, or `intStepBranch` is required** — `edges` is available
one level up (in `go`) from where the world-creating rule fires, exactly where the reuse
decision needs to be made. Phase 2 implements the search (`isAccessible edges w x`, containment
`Sfor(w') ⊆ posFormulasAt bPers x`, `ψ ∉ posFormulasAt bPers x`) and wires the branch into `go`.

**Timing**: 2 hours. **Depends on**: none.

**Files to modify**: `Expansion.lean` (design comment / helper stub only) — no proof obligations.

---

### Phase 2: Implement the `Sfor`-containment loop-check [COMPLETED]

**Goal**: Implement the dedup helper and wire it into `go`, without breaking any Preserved Asset
or the public `openBranch_countermodel` signature.

**Tasks**:
- [x] `git log -1`; scoped+grepped rebuild GREEN.
- [x] Implement `intFImpReuseWitness? (bPers : IBranch Atom) (edges : IEdges)
      (newForms : List (ISF Atom)) (newEdge : Nat × Nat) : Option Nat` (returns the reusable
      ancestor label, or `none`) exactly per the Phase 1 spec, using `posFormulasAt` +
      `isAccessible` + list-containment (`List.contains`, `List.all`). (Signature matches the
      Phase-1-settled stub exactly — `bPers`/`edges`/`newForms`/`newEdge`, not the `φ ψ w edges b`
      form sketched in the Phase 2 header, per the "do not redesign" instruction.)
- [x] Wired into `go`'s `.linearResult`+`some newEdge` branch: witness `some x` takes the
      no-new-world path (mark expanded via `newExp`, continue same branch on `bPers`, `edges`,
      and `nw` unchanged — no edge append, world counter not consumed); `none` keeps the existing
      world-creating path verbatim (`Branch.extendMany bPers newForms`, `nw'`, `edges ++ [e]`).
- [x] **Signature-change answer: NO.** `intFImpRule`, `intApplyRuleFull`, and `intStepBranch` are
      unchanged. The reuse check and its wiring are confined entirely to `go` inside
      `intExpandBranches`, exactly as the Phase 1 GO verdict predicted.
- [x] Confirmed Preserved-Asset lemmas: scoped build of the downstream `Soundness` module surfaced
      exactly ONE broken lemma, `intExpandBranches_closed_unsat` (Soundness.lean, starts line 1083;
      failing unification sites at ~1396 and ~1461) — its induction assumed every world-creating
      step strictly grows the branch via `Branch.extendMany`/new edge, which the reuse path no
      longer does. This is EXPECTED per this phase's instructions (branch no longer always grows
      on a reused `F(→)`); NOT patched here — recorded verbatim for Phase 3/4. No other Preserved
      Asset (in `Expansion.lean` itself) regressed; `IExpandedConsistent_sat` and
      `intStepBranch_linear_preserves` were not touched by this diff (both live in `Expansion.lean`
      above the `go` recursion and do not reason about `go`'s internal branch-growth pattern).
- [x] Scoped+grepped build of `Expansion` GREEN; no new sorries (verified: `Scheme.lean` sorries
      at lines 330/985 unchanged; zero sorries in `Expansion.lean`).
- [x] Commit `Expansion.lean` only (no `Rules.lean` change needed):
      `task 317 phase 2: implement Sfor-containment loop-check`.

**Estimated output**: ~200-300 lines (helper + `go` wiring + fallout fixes). **Done when**:
`Expansion.lean` builds GREEN with the dedup live, the signature-change question is answered in
the handoff, and no Preserved Asset is deleted.

**Timing**: 2.5 hours. **Depends on**: 1.

**Phase 2 result**: `Expansion.lean` GREEN with the dedup live (no signature change to the rule
layer). One Preserved-Asset lemma, `intExpandBranches_closed_unsat` in `Soundness.lean`, now
fails to typecheck — this is the expected soundness-side fallout flagged for Phase 3/4 (the
induction must be revised to handle the no-new-world reuse case, likely by adding a case showing
that reusing an ancestor whose forced-set already contains `Sfor(w')` preserves satisfiability
without needing a fresh `worldOf'`). No sorry was introduced or removed; no vacuous definition;
no new axiom.

**Files to modify**: `Expansion.lean` (+ possibly `Rules.lean`).

---

### Phase 3: Re-verify countermodel / Hintikka conditions for reused worlds [BLOCKED]

**Goal**: Prove the dedup preserves the completeness-side countermodel: a reused ancestor world
still satisfies every saturation/Hintikka/countermodel condition that `openBranch_countermodel`,
`IBranchSaturation`, and `intExtractValuation` depend on. (Second-highest risk, R2.)

**Tasks**:
- [x] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN. Last touching commit: `26508fe9`
      (Phase 1, predates the Phase 2 dedup at `619acd3a`). Scoped build of
      `Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` currently CANNOT reach
      `Scheme.lean` itself: `Scheme.lean` transitively imports `Minimal.Soundness` →
      `Intuitionistic.Soundness`, and `Intuitionistic/Soundness.lean` is the file Phase 2's
      dedup already broke (`intExpandBranches_closed_unsat`, known/expected, Phase 4's job).
      `lake build` therefore fails at the `Soundness` target before ever attempting `Scheme`
      (confirmed: full build log shows only `Soundness.lean:1396/1399/1458/1461` errors, no
      `Scheme.lean` diagnostics at all — this is a pre-existing/expected cross-file build
      ordering artifact, not a Phase-3-caused regression). Per dispatch instructions this is
      IGNORED as a Phase-3 blocker (Phase 4's concurrent job); it does mean Phase 3's own
      "scoped+grepped build GREEN" gate cannot be exercised until Phase 4 lands.
      **NOTE for the orchestrator**: the `lean-lsp` MCP server in this session is pointed at
      a *different* project (`/home/benjamin/Projects/BimodalLogic`), not `cslib`
      (`lean_run_code` reports `unknown module prefix 'Cslib'`; `lean_goal` on cslib files
      returns null goals). All analysis below is by direct source inspection only — no live
      Lean feedback was available to double-check it in this session.
- [x] Enumerate (windowed reads) every lemma that reads the world/accessibility structure of the
      returned open branch: `IBranchSaturation` (`Scheme.lean:72-99`, esp. field `sat_fimp` —
      the F(φ→ψ) Hintikka condition), `sfSatisfied`/`IExpandedConsistent`
      (`Scheme.lean:478-503`), `IExpandedConsistent_sat` (`Scheme.lean:562-635`, not re-read in
      detail — subsumed by the blocker below, since it consumes exactly the invariant that
      fails to hold), `intExpandBranches_openBranch_sat` (`Scheme.lean:968-1095`, the lemma that
      actually threads `IAllConsistent`/`IExpandedConsistent` through `go`'s cases — this is
      where the break surfaces), `openBranch_countermodel` (`Scheme.lean:1245-1270`, not
      reached — blocked upstream).
- [x] **BLOCKER FOUND (R2 materialized) — the `Sfor`-containment predicate does not establish
      the Hintikka condition it is relied on to establish.**
      - `intExpandBranches_openBranch_sat`'s `succ` case (`Scheme.lean:1055-1074`, as committed
        at `26508fe9`) is *itself* now stale/broken independent of any semantic question: it was
        written against the PRE-dedup `go` (uniform `Branch.extendMany bPers newForms`/`nw'`
        for both `newEdge = none` and `newEdge = some e`), but the POST-dedup `go`
        (`Expansion.lean:320-355`) inserts a THIRD case inside `newEdge = some e`: a further
        match on `intFImpReuseWitness? bPers edges newForms e`, where the `some _x` (reuse)
        branch recurses on `bPers` UNCHANGED (not `Branch.extendMany bPers newForms`), with
        `nw` unchanged (not `nw'`) and `edges` unchanged (not `edges ++ [e]`)
        (`Expansion.lean:335-346`). The committed proof's `simp only at hgo` /
        `exact ih _ _ _ _ hAC' hLen0' hgo` at line 1074 no longer matches `hgo`'s actual shape
        once `go` unfolds — the case split must be extended to cover `newEdge`/witness
        separately, requiring a **new** invariant-preservation fact for the reuse branch:
        `IExpandedConsistent bPers newExp` (on the SAME `bPers`, just `newExp = eH ++ [sf]` per
        `intStepBranch`'s definition, `Expansion.lean:150-157` — `sf` is included in `newExp`
        unconditionally, regardless of what `go` later decides to do with it).
      - That new fact is exactly where the semantic gap lives. `IExpandedConsistent bPers newExp`
        requires `sfSatisfied bPers sf` for `sf = ⟨.neg, .imp φ ψ, w⟩` (`Scheme.lean:502-503`),
        which for the `.neg, .imp` case (`Scheme.lean:495-498`) demands
        `∃ w' ≥ w, T(φ)@w' ∈ bPers ∧ F(ψ)@w' ∈ bPers` — i.e. an *explicit* `.neg`-signed `ψ`
        entry at the witness world, matching `IBranchSaturation.sat_fimp`'s requirement
        verbatim (`Scheme.lean:91-95`: `F(φ→ψ)@w ∈ b → ∃ w' ≥ w, T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b`).
      - `intFImpReuseWitness?` (`Expansion.lean:248-267`) only checks, for the witness `x`:
        `isAccessible edges w x`, `Sfor(w') ⊆ posFormulasAt bPers x` (gives `T(φ)@x ∈ bPers`,
        fine), and `ψ ∉ posFormulasAt bPers x` (i.e. **not** `T(ψ)@x`). This last condition is
        NOT equivalent to "`F(ψ)@x ∈ bPers`" — a branch can (and generically does) simply have
        *no* signed entry for `ψ` at `x` at all (neither `.pos` nor `.neg`), since
        `propagatePersistence` only ever copies `.pos`-signed formulas
        (`Rules.lean:139-141`) and nothing else adds an unprompted `F(ψ)@x` to an *existing*
        ancestor world merely because it is chosen as a reuse witness.
      - **Concrete counterexample** (by direct construction/inspection, not run — see the
        MCP-misconfiguration note above): let `Atom := Nat`, `atomP := .atom 0`,
        `atomQ := .atom 1`, `atomR := .atom 2`. Let
        `bPers := [⟨.pos, atomQ, 1⟩, ⟨.neg, atomR, 1⟩]` (world `1 = x` was created earlier as
        a witness for some unrelated `F(atomQ → atomR)` discharge; it carries `T(atomQ)@1` and
        `F(atomR)@1` and says nothing whatsoever about `atomP`), `edges := [(1, 0)]` (`x = 1` is
        a child of `w = 0`, so `isAccessible edges 0 1 = true`). Now suppose `F(atomQ → atomP)@0`
        fires at `w = 0`, prospectively creating `w' = 2` with
        `newForms := [⟨.pos, atomQ, 2⟩, ⟨.neg, atomP, 2⟩]` (so `Sfor(w') = {atomQ}`, obligation
        `atomP`). Tracing `intFImpReuseWitness? bPers edges newForms (2, 0)` by hand: candidate
        `x = 1` passes all three conditions (`isAccessible edges 0 1`; `sfor = [atomQ]`,
        `forcedAtX = posFormulasAt bPers 1 = [atomQ]`, so `sfor.all (forcedAtX.contains ·)` is
        `true`; `forcedAtX.contains atomP` is `false`, so `!(...)` is `true`) — the function
        returns `some 1`. But `bPers.any (fun y => y.sign == .neg && y.formula == atomP &&
        y.label == 1)` is `false` by literal inspection of `bPers`'s two entries: **`x = 1` has
        no `F(atomP)@1` entry**, so `sat_fimp`/`sfSatisfied` genuinely fails at the reused
        world for this `sf`, and no *other* world `w'' ≥ 0` in this branch has both `T(atomQ)`
        and `F(atomP)` either. `IExpandedConsistent bPers newExp` is false; the invariant the
        rest of the completeness chain depends on breaks at exactly this step.
      - Per the plan's own contingency: **this predicate is too aggressive** — it establishes
        "no vacuous closure" (`ψ ∉ Sfor(x)`) but not "the Hintikka witness for `ψ` already
        exists at `x`". Recommended tightening for a Phase 1/2 revisit (NOT implemented here —
        out of Phase 3 territory and explicitly forbidden to patch around): strengthen the third
        conjunct in `intFImpReuseWitness?` from `!(forcedAtX.contains ψ)` to a check for an
        **explicit** `F(ψ)@x` entry, e.g.
        `bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) = true`, i.e.
        search only among worlds that already carry a live `F(ψ)` obligation matching the one
        `w'` would have received, not merely worlds that happen not to force `ψ` positively.
        (This is a strictly narrower — hence safe — search predicate; whether it still finds
        enough witnesses to keep the world-bound argument for Phase 5 is an open question for
        that Phase 1/2 revisit, not resolved here.)
- [x] **Record the accessibility-structure delta for task 430** (coordination note, informational
      only — not implemented): under the (currently broken) dedup design, a discharged
      `F(φ→ψ)@w` no longer always produces a fresh leaf world with a single incoming edge from
      `w`; instead it can be discharged by ANY already-accessible ancestor `x`, so a single
      world `x` can end up serving as the Hintikka witness for MANY unrelated `F(→)` obligations
      raised at different worlds/times, and `edges` stops growing on those steps entirely (no
      new `(w', w)` pair is appended). Task 430's `intExtractValuation` upward-closure argument,
      which presumably reasons "each obligation gets its own witness world reachable by one
      hop from where it was raised", will need to instead reason over a shared/converging witness
      structure where multiple obligations point at the same `x` and the tree is shallower and
      more heavily cross-referenced than the pre-dedup one-obligation-one-child shape.
- [x] Hintikka-condition verdict: **VIOLATED** for the world-creating case (see blocker above).
      Per plan instruction: do NOT weaken `sfSatisfied`/`IBranchSaturation`/any countermodel
      lemma to compensate. **STOPPING here, marking this phase [BLOCKED]**, and handing off the
      concrete counterexample above recommending a Phase 1/2 tightening of
      `intFImpReuseWitness?`.
- [ ] Scoped+grepped build GREEN; no new sorries. **NOT ATTEMPTED** — no `Scheme.lean` edit was
      made (correctly: any edit implementing the reuse case of
      `intExpandBranches_openBranch_sat` would require either a new `sorry` (forbidden) or
      weakening a countermodel lemma (forbidden)). `Scheme.lean` is byte-identical to the
      `26508fe9` baseline; zero new sorries, zero new axioms, zero vacuous definitions (nothing
      was written).
- [ ] Commit `Scheme.lean` only — **N/A, no `Scheme.lean` changes to commit.**

**Estimated output**: ~250-400 lines. **Done when**: the countermodel chain builds GREEN under
the dedup and the task-430 accessibility delta is documented. If >400 lines emerge, split into
3.1 (`IBranchSaturation`/`IExpandedConsistent_sat` re-proof) and 3.2 (`intExtractValuation`/
`openBranch_countermodel` re-proof).

**Phase 3 verdict: BLOCKED (R2).** The `Sfor`-containment predicate `intFImpReuseWitness?`
(Expansion.lean, Phase 2) guarantees `T(φ)@x` at the reuse witness but NOT the explicit
`F(ψ)@x` entry that `IBranchSaturation.sat_fimp`/`sfSatisfied`'s `.neg, .imp` case requires.
Concrete counterexample recorded above. Recommend Phase 1/2 revisit: tighten the predicate to
require an explicit `F(ψ)@x` branch entry (not merely `ψ ∉ posFormulasAt bPers x`), then
re-dispatch Phase 3 against the tightened predicate. No `Scheme.lean` edits were made; the
Preserved Assets and the `26508fe9` baseline are untouched.

**Timing**: 2 hours. **Depends on**: 2.

**Files to modify**: `Scheme.lean` (+ `Intuitionistic/Completeness.lean` only if a countermodel
lemma lives there — flag if so). **No files were modified this dispatch** (blocked before any
edit).

---

### Phase 4: Soundness + green-build regression audit (task 316 coordination) [COMPLETED]

**Goal**: Determine whether the calculus SOUNDNESS proof (task 316, `Intuitionistic/Soundness.lean`)
and the wider green build survive the dedup, and identify precisely any soundness/countermodel
lemma the dedup disturbs. Read-only first; edit `Soundness.lean` ONLY if strictly unavoidable.

**Verdict**: `Soundness.lean` MINIMALLY TOUCHED (task-316 coordination flag raised). Exactly one
lemma broke: `intExpandBranches_closed_unsat`'s induction over `intExpandBranches.go`'s
`linearResult ... (some e)` case assumed every world-creating step strictly grows the branch via
`Branch.extendMany` + a new edge; the dedup's reuse path (`intFImpReuseWitness? = some x`)
recurses on `bPers` unchanged instead. Fixed by hoisting an explicit case split on `newEdge` and
the reuse witness (mirroring `go`'s own structure) and adding the missing reuse sub-case, which
applies the fuel-induction hypothesis directly to `bPers` (no new world, no
`intRule_preserves_sat`, since `applyPersistenceFixpoint_sat` already gives satisfiability of
exactly the branch the recursive call receives). All other soundness lemmas are rule-level and
confirmed untouched (the dedup changes `go`'s control flow only, not `intApplyRuleFull`/
`intFImpRule`'s rule semantics). Scoped build GREEN (`lake build
Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`); `lean_verify` on
`intExpandBranches_closed_unsat` reports only the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); 0 sorries in the file. Commit `8a5c0250`. See
`specs/317_propositional_tableau_completeness/progress/phase-4-progress.json` for full detail.

**Tasks**:
- [x] `git log -1 -- Soundness.lean`; scoped+grepped rebuild of `Soundness` (and a scoped build of
      any module importing the changed `Expansion.lean`) GREEN or capture the exact errors.
- [x] Audit (windowed reads) which soundness lemmas quantify over the expansion output vs. over the
      abstract rules. Expected finding: soundness is rule-level (satisfiable branch stays
      satisfiable), the dedup adds no rule, so `Soundness.lean` is untouched. CONFIRM this rather
      than assume it. (Finding: confirmed rule-level for all lemmas EXCEPT
      `intExpandBranches_closed_unsat`, which quantifies over `go`'s output directly and did break.)
- [x] If a soundness lemma genuinely breaks: flag PROMINENTLY as a task-316 coordination hazard in
      the handoff, make the MINIMAL fix, and commit `Soundness.lean` in a SEPARATE scoped commit
      (`task 317 phase 4: minimal Soundness.lean fix for dedup (coordinates task 316)`). If the fix
      is non-trivial, STOP/[BLOCKED] and escalate for task-316 coordination rather than editing
      task-316 territory unilaterally. (Judged a localized case-addition, not a re-architecture;
      proceeded rather than escalating -- see progress file for the explicit escalation
      consideration.)
- [x] Record the verdict: `Soundness.lean` NOT touched (expected) / minimally touched / [BLOCKED].
- [x] Commit only if an edit was made (else this phase produces only a handoff verdict + plan
      check-off). (Committed: `8a5c0250`.)

**Estimated output**: ~50-150 lines (audit verdict; edits only if unavoidable). **Done when**: a
written verdict states whether `Soundness.lean` is untouched, and the build regression status is
captured. **Parallelizable with Phase 3** (disjoint files, subject to R5).

**Timing**: 1 hour. **Depends on**: 2.

**Files to modify**: none expected; `Soundness.lean` ONLY if unavoidable (separate commit).

---

### Phase 5: Prove the dedup-bounded world + step bounds fit the existing fuel [NOT STARTED]

**Goal**: State and prove the boundedness lemmas: with dedup, `#worlds ≤ 2^|Sub(φ)|` and total
steps `≤ 2^(2·complexity+2)`, i.e. the existing fuel dominates. This is the arithmetic crux the
dedup unlocks (impossible without it per report 04 F6).

**Tasks**:
- [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
- [ ] **5.1 — bounded-worlds lemma**: state `intExpandBranches_world_bound_dedup`: created worlds
      have pairwise non-containment-equal forced-sets over `Sub(φ)`, so `#worlds ≤ 2^|Sub(φ)|`.
      Reuse report 04 F5's linear `W ≤ complexity+1` as a FALLBACK if the `2^|Sub|` antichain
      argument is too heavy in Lean (the linear bound is stronger and also suffices, since
      `complexity+1 ≤ 2^(2·complexity+2)`).
- [ ] **5.2 — fuel-sufficiency lemma**: state `intExpandBranches_fuel_sufficient`: total expansion
      steps `≤ 2^(2·complexity+2)` because dedup makes step-count = deduplicated-model-size
      (`#worlds × per-world unexpanded compounds`, each bounded by `2^|Sub(φ)|`). Formalize via a
      strictly-decreasing bounded-counter / measure argument (mirror the classical
      `classicalExpMeasure_step_lt` → `fuel=0 ⟹ saturated` pattern; use `WellFounded.prod_lex`
      only if a flat Nat measure will not close). Cite `GargGenoveseNegri2012` +
      `DershowitzManna1979` + `ChagrovZakharyaschev1997` in the docstring.
- [ ] Prove bounds with SLACK (`≤`, never `=`); if 5.1+5.2 exceed ~450 lines together, they are
      already split into sub-phases 5.1 and 5.2 (commit each at green).
- [ ] Scoped+grepped build GREEN; no new sorries.
- [ ] Commit `Scheme.lean` only: `task 317 phase 5: dedup world-bound + fuel-sufficiency lemmas`
      (or two commits for 5.1 and 5.2).

**Estimated output**: ~400-500 lines total (split 5.1 / 5.2 if needed). **Done when**:
`intExpandBranches_world_bound_dedup` and `intExpandBranches_fuel_sufficient` are sorry-free and
stated in the form Phase 7 consumes.

**Timing**: 2.5 hours. **Depends on**: 3, 4.

**Files to modify**: `Scheme.lean`.

---

### Phase 6: Add the two load-bearing BibKeys [NOT STARTED]

**Goal**: Add the missing citations the Phase 5 proof comment relies on to `references.bib`.

**Tasks**:
- [ ] `git log -1 -- references.bib`; confirm `GargGenoveseNegri2012` and `DershowitzManna1979`
      are ABSENT (report 05 §Q4 confirms) and that `ChagrovZakharyaschev1997`/`Fitting1983`/
      `TroelstraSchwichtenberg2000` are PRESENT.
- [ ] Append the two ready BibTeX entries from report 05 §Q4 (`GargGenoveseNegri2012`,
      `DershowitzManna1979`) to `references.bib`. (Optionally the other 8 if the proof comment
      references them — but only the two load-bearing ones are required.)
- [ ] Confirm the Phase 5 proof-comment BibKeys now resolve.
- [ ] Commit `references.bib` only: `task 317 phase 6: add GargGenoveseNegri2012 + DershowitzManna1979 bibkeys`.

**Estimated output**: ~20-40 lines (bib entries). **Done when**: the two BibKeys are present and
the Phase 5 comment cites resolvable keys.

**Timing**: 0.5 hours. **Depends on**: 5.

**Files to modify**: `references.bib`.

---

### Phase 7: Close sorry ~985 (B2 `fuel=0` base case) [NOT STARTED]

**Goal**: Discharge the last B2 residual (sorry ~985) using the Phase 5 fuel-sufficiency lemma,
keeping `openBranch_countermodel` stable.

**Tasks**:
- [ ] `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN.
- [ ] Read (windowed) `Scheme.lean:~975-995`; identify the `fuel=0` base case of
      `intExpandBranches_openBranch_sat` and the fuel value threaded from `openBranch_countermodel`
      (`2^(2·complexity+2)`).
- [ ] Apply `intExpandBranches_fuel_sufficient` (Phase 5) to show the `fuel=0` open-return is
      unreachable for the initial call (or yields the saturation fact directly), closing sorry ~985.
      Thread via the existing `private` `_aux`/`key` (plan 03 Phase 1) — keep the public signature
      byte-stable.
- [ ] Scoped+grepped build GREEN; `grep -n sorry Scheme.lean` → only sorry ~330 (B1) remains.
- [ ] `lean_verify intExpandBranches_openBranch_sat` (and `openBranch_countermodel`) → no `sorryAx`,
      no new axioms.
- [ ] Commit `Scheme.lean` only: `task 317 phase 7: close B2 fuel=0 base case via dedup fuel-sufficiency`.

**Estimated output**: ~80-150 lines. **Done when**: sorry ~985 is gone, only B1 (~330) remains,
`lean_verify` reports no `sorryAx`/new axioms, and `openBranch_countermodel` signature is unchanged.

**Timing**: 1.5 hours. **Depends on**: 6.

**Files to modify**: `Scheme.lean`.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"` → Build completed.
- [ ] Scoped builds of `Expansion` and (if touched) `Rules` GREEN.
- [ ] `grep -n sorry Scheme.lean` → exactly one remaining sorry (line ~330, B1); ~985 gone.
- [ ] `openBranch_countermodel` public signature byte-identical to baseline.
- [ ] `lean_verify` on `intExpandBranches_openBranch_sat`, `openBranch_countermodel`,
      `intExpandBranches_fuel_sufficient`, `intExpandBranches_world_bound_dedup` → no `sorryAx`,
      no new axioms.
- [ ] `Soundness.lean` (task 316) unchanged in the diff (or, if unavoidably edited, in a separate
      scoped commit with a coordination note).
- [ ] Diff contains only `Expansion.lean`, `Scheme.lean`, `references.bib` (+ `Rules.lean` /
      `Completeness.lean` / `Soundness.lean` only if a phase explicitly required and flagged it) —
      never `git add -A`.
- [ ] Full CI smoke (only if context budget allows; else defer to /vet): `lake test`,
      `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`.

## Artifacts & Outputs

- `specs/317_propositional_tableau_completeness/plans/04_sfor-dedup-fuel-sufficiency.md` (this file)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (dedup helper
  `intFImpReuseWitness?` + `go` wiring)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (B2 sorry ~985 closed;
  new `intExpandBranches_world_bound_dedup`, `intExpandBranches_fuel_sufficient`; countermodel
  re-verification)
- Modified: `references.bib` (`GargGenoveseNegri2012`, `DershowitzManna1979`)
- Possibly modified (flag if so): `Rules.lean` (only if `intFImpRule` must consult the check),
  `Intuitionistic/Completeness.lean`, `Intuitionistic/Soundness.lean` (task 316 — separate commit)
- Downstream effect: task 430 (atom-persistence bridge) unblocked once B2 (~985) is closed;
  Phase 3 records the dedup's accessibility-structure delta for 430's re-plan.

## Rollback/Contingency

- Each phase commits at GREEN; `git revert` a phase commit if it regresses. The chain
  1→2→3/4→5→6→7 peels back cleanly to the `26508fe9` Preserved-Asset green state.
- **R1 escalation (Phase 1)**: if the `Sfor`-containment check cannot be stated against existing
  structures, mark Phase 1 [BLOCKED], leave sorry ~985 intact, hand off the missing-structure
  analysis. The closed B2 `none` case (`26508fe9`) remains a real committed deliverable.
- **R2 escalation (Phase 3)**: if a reused world breaks a Hintikka/countermodel condition and
  tightening the predicate does not recover it, mark Phase 3 [BLOCKED] and hand off — do NOT
  weaken any countermodel lemma or add a placeholder.
- **R3 escalation (Phase 4)**: if `Soundness.lean` (task 316) needs a non-trivial edit, STOP,
  mark [BLOCKED], and escalate for task-316 coordination rather than editing 316 territory.
- **Overflow contingency (R4)**: a committed green partial + a sharp handoff (which lemma is
  stated, its goal state, what remains) is the success criterion for an interrupted run.
- Never edit sorry ~330 (B1) or change the fuel formula under any contingency.
