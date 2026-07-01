# Implementation Plan: Task #454 — Consolidate Chronicle PointInsertion Since seed-consistency (Bimodal ↔ Temporal)

- **Task**: 454 - Consolidate Chronicle PointInsertion Since helpers into a shared `SinceSeedInterface`
- **Status**: [NOT STARTED]
- **Effort**: 12 hours
- **Dependencies**: None (recommend landing before 449-451; see Coordination Risk)
- **Research Inputs**: specs/454_consolidate_chronicle_pointinsertion_bimodal_temporal/reports/01_consolidate-chronicle-pointinsertion.md
- **Artifacts**: plans/01_consolidate-since-seed-interface.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Factor the duplicated, `fc`-diverged Chronicle point-insertion *Since* seed-consistency helpers
shared by `Logics/Bimodal/.../PointInsertion/Since.lean` (1019 L) and
`Logics/Temporal/.../PointInsertion/Since.lean` (704 L) into a common,
interface-parameterized module `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean`
(namespace `Cslib.Logic.Metalogic.Chronicle`). Divergence between the two files is ~100% mechanical
`fc : FrameClass` threading plus notation aliases, so an abstract `SinceSeedInterface` structure that
takes the tense-logic Burgess apparatus as statement-only fields lets both proof bodies collapse to
one generic proof; each logic supplies a thin instance (Temporal: one; Bimodal: an `fc`-indexed
family) and keeps its four public names as verbatim wrappers. **Definition of done**: both logics
reduced to thin instantiations, all four public names preserved at their current signatures, external
`CounterexampleElimination/*` consumers compile unchanged, full CI green, and **zero new
sorries/axioms** (the refactor only MOVES existing sorry-free proofs).

### Research Integration

Integrated from `reports/01_consolidate-chronicle-pointinsertion.md`:
- **§1.3** — the two big seed-consistency theorems diverge 100% mechanically (`fc`-threading + notation).
- **§2.2** — recommended `SinceSeedInterface (F : Type*)` structure (~25-35 fields, statements only);
  reuse Foundations `HasSince`/`HasUntil` (`Connectives.lean:117,122`) and `MCSProperties`
  (`SetConsistent`/`SetMaximalConsistent`) to shrink the interface (§2.3).
- **§2.4** — use a `structure` (not a `class`) because Bimodal needs an `fc`-indexed instance family.
- **§3.3** — public-API preservation table: `lemma_2_7_since`, `lemma_2_8_since`,
  `lemma24SinceWithGuard`, `lemma24WithGuard` are public with external consumers → keep name+sig, wrap;
  `lemma_2_7_since_seed_consistent`, `lemma_2_8_since_seed_consistent`, `lemma27SinceSeed`, `l27s*` are
  private with zero external consumers → relocate freely.
- **§5** — Phase-0 signature/defeq gate is blocking; §1.4/§5.5 — do NOT unify Burgess.lean/Seeds.lean
  bodies (they diverge non-mechanically); §5.4 — reconcile the one `simp only` set diff with the superset.
- **§6** — the research's 6-phase sketch is refined below into 7 one-agent-run phases (0-6), splitting
  the `lemma_2_8` port into a generic+Temporal phase and a Bimodal phase to mirror `lemma_2_7`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (not provided in delegation context).

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` with a
  `SinceSeedInterface` structure and generic `lemma_2_7_since_seed_consistent` /
  `lemma_2_8_since_seed_consistent` theorems plus the shared `lemma27SinceSeed` + `l27s*` helpers.
- Reduce both `Since.lean` files to thin instances + verbatim-signature public wrappers.
- Reuse Foundations `HasSince`/`HasUntil` and `MCSProperties` predicates where definitionally sound.
- Preserve all four public names (`lemma_2_7_since`, `lemma_2_8_since`, `lemma24SinceWithGuard`,
  `lemma24WithGuard`) so `CounterexampleElimination/*` in both logics compiles unchanged.
- Net eliminate ~200-300 duplicated lines; zero new sorries/axioms.

**Non-Goals**:
- Unifying `Burgess.lean` / `Seeds.lean` proof bodies (they diverge non-mechanically — out of scope;
  only their lemma *signatures* enter the interface as fields).
- Sharing the Bimodal-only `until_witness_enriched_seed_consistent` /
  `since_witness_enriched_seed_consistent` (no Temporal counterpart in this file — stay in Bimodal).
- Any change to external consumers' source (they must compile unmodified).
- Absorbing any new `FrameClass` case from tasks 449-451 (the `fc`-polymorphic interface absorbs
  those automatically; no proactive work here).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Interface-field signatures mismatch a logic's concrete lemma type (modulo `fc`) | H | M | Phase-0 gate: transcribe every field type from `lean_hover_info` on the concrete lemmas in BOTH trees before writing the structure; build the module in isolation before any deletion. |
| Deleting a local private body that still has a hidden consumer | H | L | §3.3 grep-verified zero external consumers for privates; delete only AFTER the wrapper + instance compile in the same phase; re-grep for each name before deletion. |
| Accidentally introducing a `sorry`/axiom during transcription | H | L | `lean_verify` the generic theorems (axiom check) each porting phase; `grep -rn "sorry\|admit\|axiom" ` on all touched files in Phase 6; refactor MOVES sorry-free proofs only. |
| `simp only [Formula.and, Formula.neg]` vs `[Formula.and]` divergence in `l27s_b5_β_mem` | M | M | Use the superset `[..., Formula.neg]`; verify both goals still close via `lean_multi_attempt` in Phase 1. |
| Reuse of Foundations `MCSProperties` predicates is not definitional per-logic | M | M | Phase 0: `lean_hover_info` on `Temporal.SetMaximalConsistent` and `SetMaximalConsistent fc` vs the Foundations predicate; if not defeq, keep them as interface fields (design already tolerates ~4 extra fields). |
| New Foundations `Chronicle` namespace triggers lint (docBlame, dupNamespace) | L | M | Add license header + module docstring; docstring every declaration; apply `@[nolint dupNamespace]` as `ChronicleTypes.lean` does; run `lake lint` in Phase 6. |
| Import cycle from the new Foundations module | L | L | Module imports only Foundations (`Connectives`, `MCSProperties`, list-deduction); no `Cslib/Logics/*` import. Both Since.lean files `public import` it (mirrors GenericMCS). |
| Latent churn from tasks 449-451 (extend `FrameClass`) | M | L | 449-451 are `not_started` (not in flight). Land 454 first; if 449 lands first, rebase is mechanical (interface gains no fields, only the `fc` domain grows). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2 | 0, 1 |
| 4 | 3, 4 | 2 |
| 5 | 5 | 3, 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel. Wave 4 parallelism is file-disjoint: Phase 3
edits only Bimodal `Since.lean`; Phase 4 edits the shared module + Temporal `Since.lean`.

---

### Phase 0: Signature/defeq gate + interface skeleton [COMPLETED]

**Goal**: Create the new Foundations module with the `SinceSeedInterface` structure whose field
signatures are verified against BOTH logics' concrete lemmas; compile the module in isolation. No
per-logic edits, no generic proof body, no deletions yet.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` with license
      header, module docstring, and namespace `Cslib.Logic.Metalogic.Chronicle`.
- [ ] Confirm reuse targets: `lean_hover_info` on `HasSince`/`HasUntil` (`Connectives.lean:117,122`)
      and on Foundations `SetConsistent`/`SetMaximalConsistent`/`closed_under_derivation`
      (`MCSProperties.lean`). Decide per §2.3 whether each becomes a `[HasSince F]`-style constraint /
      reused predicate or an interface field.
- [ ] For each apparatus lemma the Since proofs invoke (`BurgessR3Maximal_extension_fails`,
      `burgessRSince_implies_burgessR`, `dc_delta_B_controlled`, `untl_left_mono_thm`,
      `snce_left_mono_thm`, `self_accum_since_mcs`, `list_conj_mem_dcs`, `list_conj_mem_mcs`,
      `listConjImpliesElem`, negation-completeness, `deductiveClosure` closure, …), run
      `lean_hover_info` on the concrete declaration in BOTH the Bimodal and Temporal trees and record
      the `fc`-abstracted field signature.
- [ ] Write the `SinceSeedInterface (F : Type*)` structure: abstract `Deriv : List F → F → Type*`,
      consistency predicates (reused or field), Burgess-relation predicates, and the ~15 lemma fields
      (statements only). Declare the generic theorem *signatures* (`lemma_2_7_since_seed_consistent`,
      `lemma_2_8_since_seed_consistent`) with `sorry`-free stubs deferred (leave `:= by sorry`
      ONLY transiently within this phase's build check, then remove — see note).
- [ ] `lake build Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency` (module in
      isolation). Structure and field types must typecheck.

**Note on transient stubs**: to typecheck the structure and theorem *statements* before Phase 2/4
port the bodies, use `theorem … := trivial`-style only if it typechecks; otherwise keep the theorem
declarations commented out and uncomment in Phase 2/4. Do NOT commit a `sorry` — Phase 6 forbids it,
and each porting phase supplies the real body. If a temporary `sorry` is unavoidable for the isolated
build, it MUST be removed within the same wave before that phase is marked complete.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` (new) — structure + field
  signatures + theorem statements.

**Verification**:
- `lake build` of the new module in isolation succeeds; field types match both logics' lemmas
  (spot-check 3-4 via `lean_multi_attempt` supplying the concrete lemma as the field value).
- No `sorry`/`axiom` committed (transient build stubs removed).
- `lake exe lint-style` on the new file passes (header/docstrings present).

---

### Phase 1: Relocate small `l27s*` formula-operator helpers [COMPLETED]

**Deviation (beneficial, ahead of schedule)**: to retarget the `l27s*` helpers this phase
also had to define the *full* `temporalSinceInterface` / `bimodalSinceInterface (fc)`
instances (originally scheduled for Phases 2/3), since the relocated helpers need a
concrete `SinceSeedInterface` value to pass to the shared module's generic defs. Both
instances are now complete, verified, and committed in the two `Since.lean` files —
Phase 2/3/4/5 can wire the ported generic theorems directly against
`temporalSinceInterface`/`bimodalSinceInterface fc` with no further instance-construction
work required. Two interface fields not anticipated in the Phase-0 sketch were added
during this phase: `untlInjective`/`andInjective` (needed because `l27s_c5_γ_mem`/
`l27s_b5_β_mem` rely on injectivity of the concrete `Formula.untl`/`Formula.and`
constructors, which cannot be recovered generically over an abstract `F`). Both are
proved trivially by each logic (`Formula.untl.inj`; `Formula.and`'s Lukasiewicz-unfold +
`Formula.imp.inj` composed twice) and verified building in both trees. The
formula-operator-only `l27s*` helpers do not depend on `fc` at all, so Bimodal's relocated
wrappers use `bimodalSinceInterface FrameClass.Base` internally (arbitrary index) and keep
their original no-`fc` signatures verbatim -- zero call-site changes elsewhere in the file.

**Goal**: Move `lemma27SinceSeed` + the small `l27s*` helpers (near byte-identical, formula-operator
only, zero external consumers) into the shared module; retarget both `Since.lean` files to the shared
copies; both logics build.

**Tasks**:
- [ ] Move `lemma27SinceSeed`, `l27sC5EventList`, `l27s_c5_event_list_mem`, `l27sB5GuardList`,
      `l27s_b5_guard_list_mem`, `l27s_c5_γ_mem`, `l27s_b5_β_mem` into `SinceSeedConsistency.lean`
      over the `HasSince`/`HasUntil`/`HasAnd`/`HasNeg` formula interface.
- [ ] Reconcile the one proof-line diff (`simp only [Formula.and, Formula.neg]` vs `[Formula.and]`)
      using the superset lemma list; verify both original goals still close via `lean_multi_attempt`.
- [ ] Delete both local copies from Bimodal and Temporal `Since.lean`; add `public import` of the
      shared module to each.
- [ ] `lake build` Bimodal `Since.lean` and Temporal `Since.lean`.

**Timing**: 1.5 hours

**Depends on**: 0

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` — add small helpers.
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean` — delete local
  copies, add import.
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean` — delete local copies, add import.

**Verification**:
- Both `Since.lean` files build; no reference to the deleted local helper names remains
  (`grep -n "l27s"` shows only the shared-module references).
- Zero new sorries.

---

### Phase 2: Port `lemma_2_7_since_seed_consistent` (generic) + Temporal wiring [COMPLETED]

**Groundwork already done (Phase 1 spillover)**: `temporalSinceInterface`/`bimodalSinceInterface fc`
are ALREADY fully defined, verified, and committed (in the two `Since.lean` files) with every field of
`SinceSeedInterface` populated -- this phase does NOT need to construct either instance. Only the
generic proof body itself remains to be ported. `lemma24WithGuard`/`lemma24SinceWithGuard` do **not**
route through `lemma_2_7_since_seed_consistent`'s body mechanically (their proof strategies genuinely
diverge between logics -- Bimodal uses `until_witness_enriched_seed_consistent`/
`since_witness_enriched_seed_consistent` directly; Temporal uses `past_temporal_witness_seed_consistent`
+ a recursive call into `lemma_2_7_since`), so they are OUT of scope for this phase and need zero
edits -- they already compile unchanged as long as `lemma_2_7_since`'s public signature is preserved.

**Goal**: Port the `lemma_2_7_since_seed_consistent` proof body **and** the `lemma_2_7_since` wrapper
body (both diverge 100% mechanically per the research; both collapse into ONE generic theorem) into
the shared module as the generic `SinceSeedInterface`-consuming theorem(s); wire Temporal's public
`lemma_2_7_since` as a thin one-line delegation to the generic theorem via `temporalSinceInterface`;
delete Temporal's local private body; build Temporal + its `CounterexampleElimination`.

**Tasks**:
- [x] Transcribe the Temporal `lemma_2_7_since_seed_consistent` body (the `fc := .Base` reading, §1.3)
      into the generic theorem, replacing every concrete `f …` with `I.f …`.
- [x] Also transcribe the Temporal `lemma_2_7_since` wrapper body (lines 334-414 of
      `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean` as of the Phase-1 commit)
      into a second generic theorem (or fold both into one) -- it diverges 100% mechanically too (see
      research §1.3 wrapper row), so it should collapse the same way rather than staying a per-logic
      ~80-line body.
- [x] Keep public `lemma_2_7_since` (and `lemma24SinceWithGuard`/`lemma24WithGuard` if they route
      through 2_7) at current signatures as wrappers calling the generic theorem via the instance.
- [x] Re-grep to confirm `lemma_2_7_since_seed_consistent` (private) has no Temporal consumers; delete
      the local body. *(deviation: altered -- the local private theorem is now itself a one-line
      delegation to the generic theorem rather than deleted outright, since Temporal's `lemma_2_7_since`
      wrapper calls it by its private local name; this preserves zero call-site churn elsewhere in the
      file while still eliminating the ~185-line duplicated body.)*
- [x] `lean_verify` the generic `lemma_2_7_since_seed_consistent` (axiom check: no new axioms/sorries).
      *(build-clean verified via `lake build`; MCP `lean_verify` tool not loaded this session --
      grep-verified zero `sorry`/`axiom` in touched files instead, see Phase 6.)*
- [x] `lake build` Temporal `Since.lean` and `…/Temporal/…/CounterexampleElimination/{RecursiveWalks,
      MainElimination}.lean`.

**Deviation -- 3 additional interface fields required**: transcription required 3 fields not
anticipated in Phase 0/1: `untlLeftMonoThm`, `snceLeftMonoThm` (MCS-membership-level left
monotonicity for `untl`/`snce`, used by the seed-consistency proof; not derivable from the existing
`untlLeftMonoDeriv` field alone since they additionally thread `theoremInMcs`/necessitation), and
`lindenbaum` (flagged as a possible-need in the Phase-0/1 handoff; confirmed needed by the
`lemma_2_7_since` wrapper, which calls Temporal's `temporal_lindenbaum` / Bimodal's
`set_lindenbaum_fc`). All three were added to `SinceSeedInterface` AND supplied in both
`temporalSinceInterface` and `bimodalSinceInterface fc` in the same commit (keeping both logics
green at every checkpoint), even though Bimodal's *wiring* to the generic theorem is Phase 3's job.
Two module-level generic lemmas (`subsetDeductiveClosure`, `deductiveClosureClosedUnderDerivation`)
were added alongside the seed-consistency/wrapper theorems -- these are pure consequences of the
abstract `Deriv` family (matching both logics' own proofs verbatim) and needed no new fields.

**Timing**: 2 hours

**Depends on**: 2 requires 0, 1.

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` — generic 2_7 theorem body.
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean` — instance + wrapper, delete body.

**Verification**:
- Temporal `Since.lean` + `CounterexampleElimination/*` build.
- `lean_verify Cslib.Logic.Metalogic.Chronicle.lemma_2_7_since_seed_consistent` reports no sorry/new axiom.
- Public `lemma_2_7_since` signature unchanged (diff shows only body).

---

### Phase 3: Bimodal `lemma_2_7_since` wiring [NOT STARTED]

**Goal**: Wire the Bimodal `fc`-indexed `SinceSeedInterface` family and the `lemma_2_7_since` wrapper;
delete Bimodal's local `lemma_2_7_since_seed_consistent` body; build Bimodal.

**Tasks**:
- [ ] Define `bimodalSinceInterface (fc : FrameClass) : SinceSeedInterface (Formula Atom)` populating
      every field with Bimodal's `fc`-threaded lemmas.
- [ ] Keep public `lemma_2_7_since (fc : FrameClass) …` (and `lemma24*` if 2_7-routed) at current
      signatures as wrappers calling the generic theorem via `bimodalSinceInterface fc`.
- [ ] Re-grep to confirm the private body has no Bimodal consumers; delete it.
- [ ] `lake build` Bimodal `Since.lean` and Bimodal `CounterexampleElimination/Interface.lean`.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean` — `fc`-family
  instance + wrapper, delete local body.

**Verification**:
- Bimodal `Since.lean` + `CounterexampleElimination/Interface.lean` build.
- Public `lemma_2_7_since` (Bimodal) signature unchanged.
- Zero new sorries in Bimodal `Since.lean`.

---

### Phase 4: Port `lemma_2_8_since_seed_consistent` (generic) + Temporal wiring [NOT STARTED]

**Goal**: Repeat the Phase-2 pattern for `lemma_2_8_since_seed_consistent`: generic body + Temporal
instance field(s) + `lemma_2_8_since` wrapper; delete Temporal's local 2_8 body; build Temporal + CEE.

**Tasks**:
- [ ] Transcribe the Temporal `lemma_2_8_since_seed_consistent` body into a generic
      `SinceSeedInterface`-consuming theorem (add any additional interface fields it needs — extend the
      structure if 2_8 invokes apparatus not covered in Phase 0; re-verify field types via `lean_hover_info`).
- [ ] Extend `temporalSinceInterface` with any new fields; keep public `lemma_2_8_since` (and
      `lemma24*` if 2_8-routed) as thin wrappers.
- [ ] Re-grep zero consumers of the private 2_8 body; delete Temporal's local body.
- [ ] `lean_verify` the generic `lemma_2_8_since_seed_consistent`.
- [ ] `lake build` Temporal `Since.lean` + `CounterexampleElimination/*`.

**Timing**: 2 hours

**Depends on**: 4 requires 2 (generic-proof pattern + Temporal instance established). File-disjoint
from Phase 3, so 3 and 4 may run in parallel.

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` — generic 2_8 theorem +
  any new fields.
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean` — extend instance + wrapper,
  delete 2_8 body.

**Verification**:
- Temporal `Since.lean` + `CounterexampleElimination/*` build.
- `lean_verify` on generic 2_8 reports no sorry/new axiom.
- If the structure gained fields, Phase-2's generic 2_7 and Temporal instance still build.

---

### Phase 5: Bimodal `lemma_2_8_since` wiring [NOT STARTED]

**Goal**: Extend the Bimodal `fc`-family instance for 2_8 and wire the `lemma_2_8_since` wrapper;
delete Bimodal's local 2_8 body; build Bimodal.

**Tasks**:
- [ ] Extend `bimodalSinceInterface (fc)` with any 2_8 fields added in Phase 4.
- [ ] Keep public `lemma_2_8_since (fc) …` (and `lemma24*` if 2_8-routed) as thin wrappers via
      `bimodalSinceInterface fc`.
- [ ] Confirm all four public names (`lemma_2_7_since`, `lemma_2_8_since`, `lemma24SinceWithGuard`,
      `lemma24WithGuard`) are now wrappers on both sides with original signatures.
- [ ] Re-grep zero consumers; delete Bimodal's local 2_8 body.
- [ ] `lake build` Bimodal `Since.lean` + `CounterexampleElimination/Interface.lean`.

**Timing**: 2 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean` — extend instance
  + wrapper, delete 2_8 body.

**Verification**:
- Bimodal `Since.lean` + `CounterexampleElimination/Interface.lean` build.
- All four public names preserved verbatim (signature diff empty).
- Zero new sorries in Bimodal `Since.lean`.

---

### Phase 6: Full CI, barrel update, zero-debt verification [NOT STARTED]

**Goal**: Run the full CSLib CI pipeline, update the module barrel, and verify zero new
sorries/axioms across all touched files.

**Tasks**:
- [ ] Update the module index barrel (`lake exe mk_all --module`) to include the new
      `SinceSeedConsistency.lean`; ensure `Cslib.Init` / `checkInitImports` stays green.
- [ ] `lake build` (whole library).
- [ ] `lake test` (CslibTests suite).
- [ ] `lake exe checkInitImports`.
- [ ] `lake exe lint-style`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (import hygiene).
- [ ] `lake lint` (docBlame/dupNamespace on new Foundations declarations).
- [ ] `lean_verify` both generic seed-consistency theorems (axiom check).
- [ ] `grep -rn "sorry\|admit\|\baxiom\b"` on all touched files → zero new entries.

**Timing**: 1.5 hours

**Depends on**: 5

**Files to modify**:
- Module barrel / `Cslib/Init` as required by `mk_all`; no proof edits expected (repair only if CI flags).

**Verification**:
- Full pipeline green: `lake build`, `lake test`, `checkInitImports`, `lint-style`, `shake`, `lint`.
- Zero new sorries/axioms; both generic theorems verified clean.

---

## Testing & Validation

- [ ] `lake build` succeeds (whole library) after every phase that edits Lean files.
- [ ] `lake test` passes (Phase 6).
- [ ] `lake exe checkInitImports` green (Phase 6).
- [ ] `lake exe lint-style` green (Phases 0 and 6).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` clean (Phase 6).
- [ ] `lake lint` clean on new Foundations declarations (Phase 6).
- [ ] `lean_verify` on `lemma_2_7_since_seed_consistent` and `lemma_2_8_since_seed_consistent`
      generic theorems: no new axioms, no sorries.
- [ ] All four public names (`lemma_2_7_since`, `lemma_2_8_since`, `lemma24SinceWithGuard`,
      `lemma24WithGuard`) preserved at original signatures in both logics (signature diff empty).
- [ ] External consumers compile unmodified: Bimodal `CounterexampleElimination/Interface.lean`;
      Temporal `CounterexampleElimination/{RecursiveWalks,MainElimination}.lean`.

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` (new shared module:
  `SinceSeedInterface` structure, small `l27s*` helpers, generic `lemma_2_7_since_seed_consistent` /
  `lemma_2_8_since_seed_consistent`).
- Rewritten `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean`
  (thin: `fc`-family instance + four public wrappers).
- Rewritten `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean`
  (thin: single instance + four public wrappers).
- Updated module barrel / `Cslib.Init` import list.
- `specs/454_consolidate_chronicle_pointinsertion_bimodal_temporal/summaries/01_consolidate-since-seed-interface-summary.md`
  (produced by /implement).

## Rollback/Contingency

- The refactor is confined to three Lean files plus a barrel entry; each phase is independently
  buildable and committed at a green milestone. To revert, `git revert` the phase commits in reverse
  order — the deleted private bodies remain recoverable from history, and the four public names are
  never touched, so external consumers are unaffected by a rollback.
- If the Phase-0 gate reveals a field signature cannot be `fc`-abstracted cleanly, STOP before any
  deletion: the local copies remain intact, so no logic is broken; escalate the specific field as a
  blocker rather than forcing a `sorry`.
- If a porting phase cannot close the generic body without a new proof obligation (would introduce a
  sorry), abandon that phase's deletion, restore the local body, and mark the phase [BLOCKED] with the
  specific goal state — the prior green phases remain valid.
