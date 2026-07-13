# Implementation Plan: Task #441 (Revised, v2 — native constructors + HasDia duality infrastructure)

- **Task**: 441 - modal_proposition_native_refactor
- **Status**: [NOT STARTED]
- **Effort**: ~32 hours (native datatype + Hilbert duality infrastructure + Metalogic restatement + tableau port)
- **Dependencies**: None
- **Research Inputs**: plans/01_modal-proposition-native-refactor.md (superseded); handoffs/01_scope-discovery-blocker.md (blocker analysis, file:line grounded)
- **Artifacts**: plans/02_native-refactor-hasdia-duality.md (this file); supersedes plans/01_modal-proposition-native-refactor.md
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - CSLib CONTRIBUTING.md (zero-sorry / zero-admit; new axiom *schemata* sanctioned below, zero Lean `axiom` declarations)
  - CSLib ORGANISATION.md (barrel / module layout)
- **Type**: cslib

## Overview

Refactor `Modal.Proposition` (`Cslib/Logics/Modal/Basic.lean:70`) from Lukasiewicz-minimal
(`atom, bot, imp, box`) to **native constructors** `atom, bot, imp, and, or, box, diamond`, and
bring the entire Modal layer — Basic consumers, the Hilbert Metalogic/ProofSystem layer (15
systems), and the full Tableau directory including the post-plan-v1 files `FmpMeasure.lean`
(3011 lines) and `CompletenessLoop.lean` (1096 lines) — back to green with zero `sorry`, zero
`admit`, and zero Lean `axiom` declarations.

This v2 plan resolves the v1 Phase A blocker (see `handoffs/01_scope-discovery-blocker.md`):
making `diamond` a primitive constructor destroys the definitional identity `◇φ ≡ (□(φ → ⊥)) → ⊥`
that `Metalogic/MCS.lean`, `Metalogic/Completeness.lean`, and the ProofSystem instances relied on
structurally. The **user-selected resolution** is route (b) from the handoff: **HasDia /
duality-axiom infrastructure**. `Cslib/Foundations/Logic/` already anticipates this design
end-to-end — `HasDia` (`Connectives.lean:112`), `Axioms.AxiomDiaDualityFwd/Back`
(`Axioms.lean:206-217`), `HasAxiomDiaDualityFwd/Back` (`ProofSystem.lean:213-218`), and the
parallel and/or families `Axioms.AxiomAndI/AndE1/AndE2/OrI1/OrI2/OrE` (`Axioms.lean:107-133`)
with `HasAxiomAndI`..`HasAxiomOrE` (`ProofSystem.lean:142-162`) — all currently **uninstantiated**
for `Modal.Proposition`. This plan instantiates them.

**Scope correction over the revision request**: the request estimated "~9 modal systems" for the
duality deployment. Verified against HEAD (`a8eb1d8b`): the generic canonical-model
`truth_lemma` (`Metalogic/Completeness.lean:266`) quantifies over **all** propositions of the
enriched language for **every** system, so its new `.and`/`.or`/`.diamond` cases require the
new axiom schemata in **all 15** system axiom inductives (K, T, K4, S4, D, D4, D45, D5, DB, B,
TB, K45, K5, KB5, plus `ModalAxiom` in `Metalogic/DerivationTree.lean:58` used by S5) — not just
the 9 systems whose named axioms (B/5/D) mention diamond. The additions are textually uniform
per system; the schedule below sizes them into two mechanical phases.

Definition of done: `Modal.Proposition` is native; all of `Cslib/Logics/Modal/**` (Basic,
LogicalEquivalence, Denotation, FromPropositional, Cube, Metalogic/**, ProofSystem/**,
Tableau/** including FmpMeasure and CompletenessLoop) and
`Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` build green; full CSLib CI passes; ZERO
`sorry`, ZERO `admit`, ZERO Lean `axiom` declarations.

### Research Integration

This revision integrates:

- **handoffs/01_scope-discovery-blocker.md** — the authoritative account of what breaks and why.
  Its verified-green base patch (five files + five mechanical Hilbert sites) is preserved
  verbatim as Phase 1. Its route (b) recommendation is adopted as the design (user-confirmed).
  Its file inventory (FmpMeasure/CompletenessLoop gap, `Systems/*/Soundness.lean` diamond
  unfolds, `Completeness.lean` error sites at lines 139/170/217/240/282) drives Phases 4-9.
- **plans/01_modal-proposition-native-refactor.md** — the native-constructor design intent,
  context-budget protocol, and tableau porting strategy carry over. Its Phases B-F assumed a
  tableau *rebuild*; tasks 442/462 have since landed the tableau (including FMP machinery) green
  on the encoded datatype, so this plan re-frames tableau work as a *port* (Phases 10-14).
  No v1 phase carries [COMPLETED] status: the v1 Phase A patch was verified green but reverted
  (tree clean at HEAD), so Phase 1 re-derives it fresh, as the handoff recommends.

### Justification for New Axiom Schemata (sanctioned zero-debt exception)

The only "new axioms" are new **constructors of the per-system axiom-schema inductives**
(`Prop`-valued inductives such as `BAxiom`, `ModalAxiom`), each stated via the canonical
Foundations abbrevs. There are NO Lean `axiom` declarations. Justification:

1. **Conservativity over the encoded presentation**: before this refactor, `∧`/`∨`/`◇` were
   abbreviations, so every instance of `AxiomAndI/AndE1/AndE2/OrI1/OrI2/OrE/DiaDualityFwd/Back`
   was already a *theorem* of each classical system (derivable from implyK/implyS/efq/peirce
   (+K), with the duality pair holding definitionally). Adding them as schemata for the now-free
   primitives does not change the set of derivable encoded-fragment formulas.
2. **Necessity**: with `and`/`or`/`diamond` free constructors, the systems can derive nothing
   about them without characterizing axioms; the canonical-model truth lemma would be false.
3. **Soundness is proved, not assumed**: every new schema gets a semantic soundness case in
   Phase 4 (`Satisfies.and_iff`/`or_iff`/`dual`), so `#print axioms` stays clean.

This is exactly the extension path the Foundations docstrings prescribe ("For proof systems with
a primitive `HasDia`, the conjunction of `AxiomDiaDualityFwd` and `AxiomDiaDualityBack`
establishes the duality", `Axioms.lean:157-160`).

### Key Design Decisions

1. **Typeclass instances** (Phase 1, in `Basic.lean` next to the `ModalConnectives` instance):
   `instance : HasAnd (Proposition Atom) := ⟨.and⟩`, `instance : HasOr (Proposition Atom) :=
   ⟨.or⟩`, `instance : HasDia (Proposition Atom) := ⟨.diamond⟩`. `ModalConnectives` itself is
   untouched (it has no and/or/dia fields; `HasAnd`/`HasOr`/`HasDia` are standalone atomic
   classes per `Connectives.lean:132-137,112`).
2. **Axiom-schema shape** (Phases 2-3): each of the 15 axiom inductives gains 8 constructors —
   `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `diaDualityFwd`, `diaDualityBack` — with
   statements written as `(Axioms.AxiomAndI φ ψ)`, ..., `(Axioms.AxiomDiaDualityBack φ)` (the
   canonical abbrevs, never hand-expanded terms). The named modal axioms (B/5/D) stay stated via
   `Axioms.AxiomB`/`Axiom5`/`AxiomD` (raw encoded shape — the handoff's verified mechanical fix),
   NOT restated with native `◇`; native/raw mediation happens inside MCS via the duality
   schemata. Each `Instances/*.lean` file then discharges `HasAxiomAndI`..`HasAxiomOrE` and
   `HasAxiomDiaDualityFwd/Back` alongside its existing `HasAxiom*` discharges.
3. **MCS-level bridging instead of term surgery** (Phase 5): new lemmas `mcs_dia_to_raw`
   (`(◇φ) ∈ S → ((□(φ → ⊥)) → ⊥) ∈ S`, via `mcs_mp_axiom` + `h_dualFwd`) and `mcs_raw_to_dia`
   (converse, via `h_dualBack`) replace every point where `Completeness.lean` previously relied
   on `◇φ` *being* an `.imp` node. `mcs_box_diamond` (`MCS.lean:164`) keeps its hypothesis
   `h_B` in raw `Axioms.AxiomB` shape and gets its conclusion restated to the **raw boxed**
   shape `(□((□(φ → ⊥)) → ⊥)) ∈ S`; callers bridge to native `◇` only *after* unboxing through
   the canonical relation (this avoids needing boxed duality axioms or necessitation-closure
   arguments inside the parametric MCS framework).
4. **Truth-lemma extension** (Phases 7-8): the generic `truth_lemma` gains `.and`/`.or` cases
   (MCS closure via the and/or schemata + maximality) and a `.diamond` case whose `←` direction
   is a genuine canonical **existence lemma** (`(◇φ) ∈ S → ∃ T, canonical-R S T ∧ φ ∈ T`),
   proved by bridging to raw shape and reusing the Lindenbaum/consistency machinery already
   present in the box case. New hypothesis callbacks (`h_andI`.. `h_dualBack`) thread through
   `truth_lemma`, `strong_completeness` (:606), `strong_completeness_iff` (:645),
   `compactness` (:672), `weak_completeness` (:704).
5. **Tableau decomposer API preservation** (Phase 10): keep the decomposer *names*
   (`modalNegOf?`/`modalAndOf?`/`modalOrOf?`/`modalImpOf?`/`modalBoxOf?`/`modalDiaOf?`,
   `Tableau/Defs.lean`) and their `@[simp]` lemma names; redefine bodies to match native
   constructors. This minimizes churn across the 67 + 33 + 4 decomposer call sites in
   `Tableau/Completeness.lean`, `FmpMeasure.lean`, `CompletenessLoop.lean`. Breakage then
   localizes to (a) encoded-shape `rfl` lemmas (e.g. `modalDiaOf?_dia`, `Defs.lean:230`),
   (b) exhaustive matches/inductions needing `.and`/`.or`/`.diamond` cases, (c) sites that
   pattern-matched the encoded shapes directly (`Rules.lean:91/109/134/142`,
   `Branch.lean:98-134`).

### Roadmap Alignment

No roadmap-update flag was provided; this plan does not modify ROADMAP.md. Task 441 unblocks the
modal tableau/decidability line (299-301 series) and gives tasks 490-496 (intuitionistic/minimal
modal metalogic) the native substrate with an explicit `HasDia` — required for non-classical
modal logics where diamond cannot be derived (per `Connectives.lean:166-169`).

## Goals & Non-Goals

**Goals**:
- Native `Modal.Proposition` with constructors `atom, bot, imp, and, or, box, diamond`; `neg`,
  `top`, `iff` remain derived abbrevs; notation and `@[simp]`/`@[grind]` lemma names preserved.
- `HasAnd`/`HasOr`/`HasDia` instances for `Proposition Atom`.
- All 15 Hilbert system axiom inductives extended with the 8 canonical characterization
  schemata; `HasAxiomAndI`..`HasAxiomOrE`, `HasAxiomDiaDualityFwd/Back` discharged per system.
- All 15 `Systems/*/Soundness.lean` extended with semantic cases for the new schemata; the
  diamond-unfold breaks in B/DB/KB5/S5/TB soundness (`modalB`) and the D/5-family (`modalD`/
  `modalFive`) repaired via `Satisfies.dual`/`diamond_iff`.
- `Metalogic/MCS.lean` + `Metalogic/Completeness.lean` restated on duality bridging: canonical
  frame lemmas (`canonical_symm`/`canonical_eucl`/`canonical_eucl_from_5`) and the generic
  `truth_lemma` with `.and`/`.or`/`.diamond` cases; all 15 `Systems/*/Completeness.lean`
  re-instantiated; ConservativeExtension / InterSystem / GenericMCSBridge / DeductionTheorem /
  Cube swept green.
- Full `Tableau/**` port including `FmpMeasure.lean` and `CompletenessLoop.lean`.
- Full CSLib CI green; zero `sorry`/`admit`; zero Lean `axiom` declarations.

**Non-Goals**:
- Restating the named modal axioms (B/5/D) with native `◇` (they stay canonical-raw via
  `Axioms.AxiomB`/`Axiom5`/`AxiomD`; a native-◇ axiom presentation is future work).
- Changing `PL.Proposition`, `Bimodal.Formula`, or Temporal formula types (Bimodal stays
  Lukasiewicz-encoded; only its Modal-embedding consumer is updated).
- Intuitionistic/minimal modal systems (tasks 490-496 build on this).
- Tableau algorithm redesign or performance work; this is a port of green code.
- Deleting the v1 plan or the encoded-datatype git history.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Full `lake build` is red mid-track (foundational datatype change; Phases 1-14 form one contiguous refactor) | H | Certain | Run the whole track on branch `task-441-native-refactor`. Per-phase gates are *targeted* `lake build <owned modules>` green + `lean_diagnostic_messages` clean on owned files; whole-library green is Phase 15's gate. Commit at every phase (branch), merge only at Phase 15 green. |
| Truth-lemma `.diamond` existence lemma is genuinely new proof content and may exceed one dispatch | H | M | Phase 8 is dedicated solely to it; the box case (:282 onward) already contains the Lindenbaum/unboxing machinery to mirror. Fallback: if it stalls, commit the sorry-free partial file state (and/or cases from Phase 7), mark Phase 8 [BLOCKED] with the precise residual goal, `/spawn` a follow-up. Never `sorry`. |
| `FmpMeasure.lean` (3011 lines) exhaustive inductions explode with 3 new constructor cases each | H | M | Phase 13 is dedicated; decomposer-API preservation (Phase 10) limits breakage to induction cases + shape lemmas. Fallback: split Phase 13 into two dispatches at a module-internal seam (measure defs vs. measure-decrease proofs); mark [PARTIAL] between dispatches. |
| Hidden consumers outside the verified blast radius (e.g. exhaustive `induction φ` in InterSystem/, Cube.lean, DeductionTheorem.lean) | M | M | Handoff grep found no direct and/or/◇ use there (only `Cube.lean` 1 docstring hit), but Phase 9 includes a mandatory sweep: `grep -rn "induction φ\|match.*Proposition" ` over `Metalogic/ ProofSystem/ Cube.lean` + build. Re-grep at the start of every phase. |
| 15-system axiom/instance sweep is large (~40-60 lines x 15 files) and drifts from the canonical shapes | M | M | Phases 2-3 use ONLY the `Axioms.*` abbrevs (never hand-expanded terms) — the exact discipline that made the handoff's 5-site AxiomB fix build green. Copy the Phase 2 pattern file-by-file. |
| `Satisfies` `@[grind]` set changes break downstream `grind` proofs | M | M | Keep the `@[grind =]` companions (`and_iff_and`, `or_iff_or`, `diamond_iff_exists`, `Basic.lean:224-247`) with unchanged names/statements; re-prove bodies on native cases. Verified green in the handoff's Phase A run. |
| `FromPropositional.lean` `toModal_and/toModal_or` non-defeq trap (shared `PL.Proposition.embed` still emits raw shapes) | M | H (known) | Handoff already solved it: restate the lemmas' RHS as the raw nested-`imp` shape, leave `modal_satisfies_toModal_iff_evaluate` body unchanged. Phase 1 re-applies exactly that. |
| ConservativeExtension proofs break on new constructors asymmetrically | M | M | New constructors are added to *every* system uniformly, so subsystem-to-supersystem axiom maps extend constructor-to-constructor. Phase 9 owns all 15 ConservativeExtension files together. |
| Concurrent sessions share this checkout (active agents: main, t317-impl-1) | M | M | Feature branch + serialize: no other task may touch `Cslib/Logics/Modal/**` or `Cslib/Foundations/Logic/**` while waves 1-7 run. Commit every green milestone immediately. |

## Context-Budget Protocol (MANDATORY for every phase)

Reference files are large (FmpMeasure 3011, CompletenessLoop 1096, Tableau/Completeness 832,
Metalogic/Completeness 723 lines). Implementation agents MUST navigate, not bulk-read:

1. `lean_file_outline` to locate declarations; `lean_diagnostic_messages` for the authoritative
   error set; `lean_goal`/`lean_hover_info` at target lines; `lean_multi_attempt` before edits;
   `Read` with `offset`/`limit` (±40 lines around a target) only.
2. Build truncated and single-module while iterating:
   `lake build Cslib.Logics.Modal.<Module> 2>&1 | tail -60`. Whole-library builds are Phase 15
   only.
3. Per-phase gate: owned modules build green; `grep -rn 'sorry\|admit\|^axiom ' ` clean over
   touched files; commit `task 441 phase {N}: ...` on the feature branch.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 5, 10 | 1 |
| 3 | 4, 6, 11 | 2, 3, 5, 10 |
| 4 | 7, 12 | 6, 11 |
| 5 | 8, 13 | 7, 12 |
| 6 | 9, 14 | 4, 8, 13 |
| 7 | 15 | 9, 14 |

Phases within the same wave can execute in parallel — territory contracts: the **Metalogic
track** (Phases 2-9) owns `Cslib/Logics/Modal/Metalogic/**`, `Cslib/Logics/Modal/ProofSystem/**`,
and `Cslib/Logics/Modal/Cube.lean`; the **Tableau track** (Phases 10-14) owns
`Cslib/Logics/Modal/Tableau/**`; Phase 1 exclusively owns `Basic.lean`,
`LogicalEquivalence.lean`, `Denotation.lean`, `FromPropositional.lean`,
`Bimodal/Embedding/ModalEmbedding.lean` (frozen for all later phases except the one-line
instance additions listed in Phase 1 itself). Phases 2 and 3 split the Instances directory
disjointly. Phases 6, 7, 8 all touch `Metalogic/Completeness.lean` and are therefore strictly
serialized. Each phase is sized to a single agent run (~100-500 lines of output). Re-grep the
consumer set at the start of each phase.

---

### Phase 1: Native datatype base patch + typeclass instances + mechanical Hilbert sites [NOT STARTED]

- **Goal:** Re-derive and apply the handoff's individually-verified-green base patch, plus the
  `HasAnd`/`HasOr`/`HasDia` instances, plus the 5 mechanical axiom-schema fixes. After this
  phase the seven owned Basic-layer files build green in isolation (the wider library is
  expected red until later phases).
- **Tasks:**
  - [ ] `Cslib/Logics/Modal/Basic.lean`: redefine the inductive (`:70`) with primitive
    `atom, bot, imp, and, or, box, diamond` (delete the derived abbrevs for `or` (`:109`),
    `and` (`:113`), `diamond` (`:124`); keep `neg`/`top`/`iff` abbrevs and `neg_def`/`top_def`).
    Preserve the `ModalConnectives` instance (`:86`), `Bot` instance, and all scoped notation.
  - [ ] `Basic.lean`: add `instance : HasAnd (Proposition Atom) := ⟨.and⟩`,
    `instance : HasOr (Proposition Atom) := ⟨.or⟩`,
    `instance : HasDia (Proposition Atom) := ⟨.diamond⟩` adjacent to the `ModalConnectives`
    instance (import `Cslib.Foundations.Logic.Connectives` is already in scope via
    ModalConnectives).
  - [ ] `Basic.lean`: extend `Satisfies` (`:145-149`) with native `.and`/`.or`/`.diamond` cases;
    re-prove `Satisfies.and_iff`/`or_iff`/`diamond_iff` as `Iff.rfl`-style; rewrite
    `Satisfies.dual` (`:290`) as a genuine semantic proof (no longer definitional; handoff
    verified `rintro`/`push_neg` route); keep the `@[grind =]` companions (`:224-247`) with
    unchanged statements; verify the ~25 `rw [diamond_iff]`-style call sites in the K/T/4/5
    theorems still build.
  - [ ] `Cslib/Logics/Modal/LogicalEquivalence.lean`: extend `Proposition.Context` (`:39`) with
    `andL/andR/orL/orR/diamond`, extend `Context.fill` (`:50`), re-prove `congruence` (`:63`).
  - [ ] `Cslib/Logics/Modal/Denotation.lean`: extend `Proposition.denotation` and
    `satisfies_mem_denotation` with `.and`/`.or`/`.diamond` cases (handoff-identified gap).
  - [ ] `Cslib/Logics/Modal/FromPropositional.lean`: restate `toModal_and`/`toModal_or` with
    raw nested-`imp`/`bot` RHS (the shared `PL.Proposition.embed` skeleton in
    `Propositional/Embedding.lean` is NOT touched); `modal_satisfies_toModal_iff_evaluate`
    body unchanged.
  - [ ] `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean`: add `.and/.or/.diamond` cases to
    `toBimodal` (targets `Bimodal.Formula.and/or/diamond`, which remain encoded).
  - [ ] Mechanical axiom sites (handoff-verified): `Metalogic/DerivationTree.lean:81`
    (`ModalAxiom.modalB` restated as `ModalAxiom (Axioms.AxiomB φ)`; add
    `public import Cslib.Foundations.Logic.Axioms`) and `ProofSystem/Instances/{B,TB,KB5,DB}.lean`
    `*.modalB` likewise. ALSO restate the diamond-mentioning `modalD` sites
    (`Instances/{D,D4,D45,D5,DB}.lean`) via `Axioms.AxiomD` and `modalFive` sites
    (`Instances/{D45,D5,K45,K5,KB5}.lean`) via `Axioms.Axiom5` — same one-line substitution
    pattern (the handoff verified B; D/5 are structurally identical).
- **Timing:** ~3.5 hours
- **Depends on:** none
- **Files to modify:** `Cslib/Logics/Modal/Basic.lean`, `LogicalEquivalence.lean`,
  `Denotation.lean`, `FromPropositional.lean`, `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean`,
  `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`,
  `Cslib/Logics/Modal/ProofSystem/Instances/{B,TB,KB5,DB,D,D4,D45,D5,K45,K5}.lean` (schema
  statements only)
- **Verification:** `lake build` of `Cslib.Logics.Modal.Basic`, `...LogicalEquivalence`,
  `...Denotation`, `...FromPropositional`, `Cslib.Logics.Bimodal.Embedding.ModalEmbedding`,
  `...Metalogic.DerivationTree` all green in isolation; zero sorry/admit/axiom in touched files.
  Commit `task 441 phase 1: native Modal.Proposition + HasAnd/HasOr/HasDia + base consumers`.
- **Risk/Fallback:** biggest risk is a drifted `Satisfies.dual` proof; the handoff confirms a
  semantic proof exists — if the exact tactic script resists, `lean_multi_attempt` alternatives
  (`grind`, `tauto` with `Classical`) before hand-expansion. If `ModalEmbedding` resists, do NOT
  proceed to wave 2 (v1 rollback rule): revert and re-scope.

---

### Phase 2: Characterization schemata + HasAxiom discharges, group 1 (ModalAxiom, S5, S4, K, T, K4, B, TB) [NOT STARTED]

- **Goal:** Extend the group-1 axiom inductives with the 8 canonical schemata and discharge the
  corresponding `HasAxiom*` typeclass instances. This phase sets the copy-paste pattern for
  Phase 3.
- **Tasks:**
  - [ ] `Metalogic/DerivationTree.lean` `ModalAxiom` (`:58`): add constructors `andI φ ψ :
    ModalAxiom (Axioms.AxiomAndI φ ψ)`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`,
    `diaDualityFwd φ : ModalAxiom (Axioms.AxiomDiaDualityFwd φ)`, `diaDualityBack` — 8 total,
    all via `Axioms.*` abbrevs, with doc comments citing the encoded-derivability
    conservativity argument.
  - [ ] `ProofSystem/Instances/{S4,K,T,K4,B,TB}.lean`: same 8 constructors per axiom inductive.
    (S5's instance file discharges via `ModalAxiom` — update its `HasAxiom*` discharge block
    (`S5.lean:95` region) with the new instances.)
  - [ ] In each file's instance block (pattern: `(Modal.BAxiom.modalB _)⟩` at `B.lean:120`),
    discharge `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`,
    `HasAxiomOrE`, `HasAxiomDiaDualityFwd`, `HasAxiomDiaDualityBack` for the system.
  - [ ] Verify no `HasAnd F`/`HasOr F`/`HasDia F` instance gaps: the schemata abbrevs require
    them; Phase 1 provided them on `Proposition Atom`.
- **Timing:** ~2 hours
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`,
  `Cslib/Logics/Modal/ProofSystem/Instances/{S5,S4,K,T,K4,B,TB}.lean`
- **Verification:** each owned module builds green in isolation (their `Systems/` consumers may
  still be red — that is Phase 4/9 territory); zero sorry/admit. Commit
  `task 441 phase 2: and/or/dia characterization schemata (group 1)`.
- **Risk/Fallback:** instance-resolution ambiguity if `HasAxiom*` classes take the system `S` as
  an out-param — mirror exactly how the existing `HasAxiomB` discharges are written in the same
  file. Fallback: explicit `(F := Proposition Atom)` annotations.

---

### Phase 3: Characterization schemata + HasAxiom discharges, group 2 (D, D4, D45, D5, DB, K45, K5, KB5) [NOT STARTED]

- **Goal:** Apply the Phase 2 pattern to the remaining 8 system files.
- **Tasks:**
  - [ ] `ProofSystem/Instances/{D,D4,D45,D5,DB,K45,K5,KB5}.lean`: add the same 8 constructors
    per axiom inductive + `HasAxiom*` discharges, copying Phase 2's committed pattern verbatim.
- **Timing:** ~1.5 hours
- **Depends on:** 1 (pattern from 2; file-disjoint, may run in parallel with 2 if the pattern is
  agreed in the dispatch prompt)
- **Files to modify:** `Cslib/Logics/Modal/ProofSystem/Instances/{D,D4,D45,D5,DB,K45,K5,KB5}.lean`
- **Verification:** each owned module builds green in isolation; zero sorry/admit. Commit
  `task 441 phase 3: and/or/dia characterization schemata (group 2)`.
- **Risk/Fallback:** none beyond Phase 2's; if Phase 2 discovered pattern corrections, apply them
  here first.

---

### Phase 4: Systems soundness sweep (15 files, new schema cases + diamond-unfold repairs) [NOT STARTED]

- **Goal:** Every `Systems/*/Soundness.lean` proves the 8 new axiom cases semantically and the
  previously-defeq diamond unfolds are repaired.
- **Tasks:**
  - [ ] All 15 `Metalogic/Systems/{K,T,K4,S4,S5,D,D4,D45,D5,DB,B,TB,K45,K5,KB5}/Soundness.lean`:
    the soundness induction over the axiom inductive gains 8 uniform cases. Semantic content:
    `andI/andE1/andE2` via `Satisfies.and_iff`; `orI1/orI2/orE` via `Satisfies.or_iff`;
    `diaDualityFwd/diaDualityBack` via `Satisfies.dual` — each expected to close with
    `simp [Satisfies...] <;> tauto` or `grind` using the Phase 1 `@[grind =]` companions.
  - [ ] Repair the known diamond-unfold breaks: `Systems/S5/Soundness.lean:57` `modalB` case
    (`introN` failure per handoff) and the analogous `modalB` cases in
    `{B,DB,KB5,TB}/Soundness.lean` (`:48/:58/:60/:63`) and `modalD`/`modalFive` cases in the
    D/5-family — rewrite through `Satisfies.dual`/`diamond_iff` where the raw `Axioms.AxiomB/5/D`
    statement's semantics is proved directly against the encoded shape (no native ◇ appears in
    those axiom statements post-Phase 1, so these cases reason purely on imp/box/bot semantics).
- **Timing:** ~2.5 hours
- **Depends on:** 2, 3
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean` (15 files)
- **Verification:** `lake build` green for all 15 Soundness modules; zero sorry/admit. Commit
  `task 441 phase 4: soundness cases for characterization schemata (15 systems)`.
- **Risk/Fallback:** if a `modalB`-style case resists tactic repair, prove a shared helper lemma
  once in `Basic.lean`-adjacent scope (e.g. `satisfies_axiomB_of_symm`) and reuse — but prefer
  local repair to avoid re-opening Phase 1 territory; a helper goes in a NEW file
  `Metalogic/Systems/SoundnessHelpers.lean` if needed (do not edit Basic.lean).

---

### Phase 5: MCS duality bridges + and/or closure lemmas [NOT STARTED]

- **Goal:** `MCS.lean` provides the membership-level lemmas the canonical-model layer needs, so
  no proof ever again depends on `◇φ` unifying with an `.imp` node.
- **Tasks:**
  - [ ] `Metalogic/MCS.lean`: add `mcs_dia_to_raw` — from `h_dualFwd : ∀ φ, Axioms
    (Axioms.AxiomDiaDualityFwd φ)` and `(◇φ) ∈ S` conclude `((□(φ.imp .bot)).imp .bot) ∈ S`
    (one `mcs_mp_axiom` application); `mcs_raw_to_dia` — converse via `h_dualBack`.
  - [ ] Restate `mcs_box_diamond` (`:164-174`): hypothesis `h_B` stays raw
    (`∀ φ, Axioms (Axioms.AxiomB φ)`); conclusion becomes the raw boxed shape
    `(Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)) ∈ S`. Callers (Phase 6)
    unbox through canonical-R, then bridge with `mcs_raw_to_dia` where native `◇` membership is
    required. Keep a thin native-conclusion corollary ONLY if it can be derived without boxed
    duality (do not add boxed duality axioms).
  - [ ] Add and/or MCS closure lemmas for the truth lemma: `mcs_and_mem_iff`
    (`(φ.and ψ) ∈ S ↔ φ ∈ S ∧ ψ ∈ S`, via `h_andI/h_andE1/h_andE2` + `mcs_mp_axiom`) and
    `mcs_or_mem_iff` (`(φ.or ψ) ∈ S ↔ φ ∈ S ∨ ψ ∈ S`; `←` via `h_orI1/h_orI2`; `→` via
    maximality/`modal_negation_complete` + `h_orE`), following the file's existing
    hypothesis-callback parameterization style (`h_implyK`, `h_implyS`, ...).
- **Timing:** ~2.5 hours
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/MCS.lean`
- **Verification:** `lake build Cslib.Logics.Modal.Metalogic.MCS` green; zero sorry/admit.
  Commit `task 441 phase 5: MCS duality bridges + and/or closure lemmas`.
- **Risk/Fallback:** `mcs_or_mem_iff` forward direction needs a small propositional derivation
  (from `¬φ, ¬ψ ∈ S` and `h_orE` derive `¬(φ ∨ ψ) ∈ S`); if the DerivationTree plumbing gets
  long, mirror the existing `modal_dne_from_neg_neg` (`Completeness.lean:487`) construction
  style. Fallback: state the or-lemma in the exact weakest form the Phase 7 truth-lemma case
  needs (one direction per truth-lemma direction) rather than a full iff.

---

### Phase 6: Canonical frame lemmas restated on duality bridging [NOT STARTED]

- **Goal:** `canonical_symm` (:105), `canonical_eucl` (:142), `canonical_eucl_from_5` (:192) in
  `Metalogic/Completeness.lean` build green with no syntactic diamond surgery — the exact v1
  break points (error sites :139, :170, :217, :240 per the handoff).
- **Tasks:**
  - [ ] Thread `h_dualFwd`/`h_dualBack` hypotheses (canonical `Axioms.*` shapes) through the
    three frame lemmas' signatures.
  - [ ] Replace each site that applied `modal_implication_property` directly to a `(◇ψ) ∈ T`
    term (expecting an `.imp` membership) with `mcs_dia_to_raw` first, then the unchanged raw
    reasoning; where the proof produced a raw shape and needed native `◇` membership, insert
    `mcs_raw_to_dia`.
  - [ ] Adapt to the restated `mcs_box_diamond` (raw boxed conclusion): unbox via canonical-R
    membership, bridge after.
  - [ ] Update the three lemmas' call sites within the same file (frame-condition bundles for
    the per-system completeness instantiations) to supply the new hypotheses.
- **Timing:** ~3 hours
- **Depends on:** 5
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Completeness.lean` (frame-lemma section,
  ~lines 100-260, plus signatures of direct callers in-file)
- **Verification:** the three frame lemmas report no errors via `lean_diagnostic_messages`
  (whole-file build still red until Phases 7-8 fix the truth lemma — gate on
  per-declaration diagnostics, not module build); zero sorry/admit in the edited region.
  Commit `task 441 phase 6: canonical frame lemmas via duality bridging`.
- **Risk/Fallback:** this is proof-content core #1. If a bridging step exposes a missing MCS
  helper, add it to the Phase 5 section of `MCS.lean` (same track, no territory conflict).
  If `canonical_eucl_from_5`'s double-negation plumbing (:217-240) resists, restate its internal
  `have`s fully in raw shape (duality bridges only at entry/exit of the lemma).

---

### Phase 7: Generic truth lemma — and/or cases + callback threading [NOT STARTED]

- **Goal:** `truth_lemma` (:266) covers `.and` and `.or`; all downstream generic theorems accept
  the new callbacks. (`.diamond` case is Phase 8; until then the truth lemma may carry the
  diamond case as a structured stub ONLY in the sense of Phase 8 doing it next — no `sorry` is
  ever committed: Phases 7 and 8 land as a single commit if needed, see fallback.)
- **Tasks:**
  - [ ] Extend `truth_lemma`'s hypothesis list with `h_andI, h_andE1, h_andE2, h_orI1, h_orI2,
    h_orE, h_dualFwd, h_dualBack` (all `∀ ..., Axioms (Axioms.Axiom... ...)` shape).
  - [ ] Add the `.and φ ψ` case: both directions via `mcs_and_mem_iff` + IHs (structural
    recursion supplies IHs at φ, ψ directly — the native-constructor payoff).
  - [ ] Add the `.or φ ψ` case via `mcs_or_mem_iff` + IHs.
  - [ ] Thread the new callbacks through `strong_completeness` (:606),
    `strong_completeness_iff` (:645), `compactness` (:672), `weak_completeness` (:704), and the
    consistency helpers if their signatures constrain the axiom callbacks.
- **Timing:** ~2.5 hours
- **Depends on:** 6 (same file — strict serialization)
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Completeness.lean`
- **Verification:** `.and`/`.or` cases error-free by `lean_diagnostic_messages`; threading
  compiles. Commit combined with Phase 8 if the diamond case is required for the recursion to
  elaborate (Lean will demand exhaustiveness — see fallback). Zero sorry/admit at commit time.
- **Risk/Fallback:** the truth lemma is a recursive `def`-style match (`:278` on), so Lean
  requires ALL cases at once — Phases 7 and 8 are then one editing session with two review
  passes and a single commit `task 441 phases 7-8: truth lemma native cases`. They remain
  separate phases for effort accounting and dispatch focus; the Phase 7 dispatch prepares the
  and/or cases and all threading, the Phase 8 dispatch completes diamond and commits.

---

### Phase 8: Truth lemma — canonical diamond existence lemma + diamond case [NOT STARTED]

- **Goal:** The genuinely new proof content: `(◇φ) ∈ S → ∃ T, canonicalR S T ∧ φ ∈ T` and the
  `.diamond` truth-lemma case; the whole `Metalogic/Completeness.lean` module builds green.
- **Tasks:**
  - [ ] Prove the canonical existence lemma: from `(◇φ) ∈ S`, bridge to raw
    (`mcs_dia_to_raw`), i.e. `¬□¬φ ∈ S`; show `{ψ | (□ψ) ∈ S} ∪ {φ}` is consistent (standard
    argument: a finite refutation would derive `□¬φ ∈ S` contra maximal consistency — reuse the
    unboxing/Lindenbaum machinery already in the box case of the current truth lemma and
    `modal_lindenbaum`); extend to an MCS `T` with `canonicalR S T` and `φ ∈ T`.
  - [ ] `.diamond φ` case, `←` (membership to satisfaction): existence lemma + IH at `T` +
    native `Satisfies` diamond case.
  - [ ] `.diamond φ` case, `→` (satisfaction to membership): from a witness `T` with
    `canonicalR S T`, `φ ∈ T` (via IH), derive `(◇φ) ∈ S`: contrapositive — if `(◇φ) ∉ S` then
    `¬◇φ ∈ S`, bridge via `h_dualFwd`/`h_dualBack` to `□¬φ ∈ S`, hence `¬φ ∈ T`, contradiction.
  - [ ] Whole-module build of `Metalogic/Completeness.lean`; fix the remaining exhaustive
    `induction φ` sites in-module (handoff: :417, :640, :666 — expected to be consumers of the
    truth lemma / negation-completeness helpers needing only the new cases or the new
    callbacks).
- **Timing:** ~3.5 hours (may need a second dispatch; see fallback)
- **Depends on:** 7
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Completeness.lean`
- **Verification:** `lake build Cslib.Logics.Modal.Metalogic.Completeness` green; zero
  sorry/admit; `lean_verify` on `truth_lemma` and `strong_completeness` shows only standard
  axioms. Commit `task 441 phases 7-8: truth lemma native cases + diamond existence lemma`.
- **Risk/Fallback:** highest-risk phase in the plan. The consistency argument for the existence
  lemma requires deriving `□¬φ ∈ S` from a finite `L ⊆ {ψ | □ψ ∈ S}` refuting `φ` — this needs
  K-distribution + necessitation over the conjunction, machinery that exists for the box case;
  if the box case's exact form doesn't transfer, extract its core as a shared helper first
  (same-file refactor). Fallback: if not closable in two genuine dispatches, commit the green
  Phase 6 state, mark Phase 8 [BLOCKED] with the precise open goal, `/spawn` a dedicated
  existence-lemma task. Never `sorry`.

---

### Phase 9: Systems completeness instantiations + ConservativeExtension + Metalogic sweep [NOT STARTED]

- **Goal:** All 15 `Systems/*/Completeness.lean` supply the new callbacks; ConservativeExtension,
  InterSystem, GenericMCSBridge, DeductionTheorem, Cube all green — the entire
  Metalogic/ProofSystem subtree builds.
- **Tasks:**
  - [ ] 15 `Systems/*/Completeness.lean`: pass the new axiom callbacks
    (`fun φ ψ => .andI φ ψ` style, matching each system's constructor names) to
    `truth_lemma`/`strong_completeness_iff` instantiations; supply `h_dualFwd`/`h_dualBack` to
    the frame-lemma bundles for the B/5-family systems (canonical_symm/eucl users).
  - [ ] 15 `Systems/*/ConservativeExtension.lean`: extend the axiom-mapping proofs with the 8
    new constructor cases (uniform constructor-to-constructor mapping).
  - [ ] Sweep and repair: `Metalogic/InterSystem/{AxiomSubsumption,Conservativity,Lifting,
    LiftViaMorphism}.lean`, `Metalogic/GenericMCSBridge.lean`, `Metalogic/DeductionTheorem.lean`,
    `Metalogic/Soundness.lean`, `Cslib/Logics/Modal/Cube.lean` — grep confirmed no direct
    and/or/◇ dependence, but exhaustive matches and the new axiom constructors in subsumption
    proofs may surface; fix mechanically.
  - [ ] `lake build` of the full `Cslib.Logics.Modal.Metalogic` + `...ProofSystem` + `...Cube`
    subtree.
- **Timing:** ~3 hours
- **Depends on:** 4, 8
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Systems/*/{Completeness,
  ConservativeExtension}.lean` (30 files), `Cslib/Logics/Modal/Metalogic/InterSystem/*.lean`,
  `GenericMCSBridge.lean`, `DeductionTheorem.lean`, `Soundness.lean`, `Cslib/Logics/Modal/Cube.lean`
  (as needed)
- **Verification:** entire Metalogic/ProofSystem/Cube subtree builds green; zero sorry/admit.
  Commit `task 441 phase 9: systems completeness + conservative extensions on native datatype`.
- **Risk/Fallback:** InterSystem axiom-subsumption proofs enumerate axiom constructors — 8 new
  cases per subsumption pair; if a pair's new cases don't map constructor-to-constructor
  (differently-named constructors), map through the shared `Axioms.*` statement instead. If the
  file count exceeds one dispatch, split at Systems/ vs InterSystem+rest.

---

### Phase 10: Tableau core port — Defs, Rules, Branch, Closure [NOT STARTED]

- **Goal:** Tableau front-end green on native constructors with the decomposer API names
  preserved (minimal-churn contract for Phases 12-14).
- **Tasks:**
  - [ ] `Tableau/Defs.lean`: redefine `modalNegOf?`/`modalAndOf?`/`modalOrOf?`/`modalImpOf?`/
    `modalBoxOf?`/`modalDiaOf?` to match native constructors exactly (keep names); update their
    `@[simp]` reduction lemmas — `modalDiaOf?_dia` (`:230`) becomes
    `modalDiaOf? (.diamond a) = some a` (statement changes shape; keep the lemma name); add
    `.and/.or/.diamond` cases to `modalComplexity` and `modalPropHash` exhaustive matches; keep
    `WorldIndex` and the `Hashable` instance.
  - [ ] `Tableau/Rules.lean` `modalApplyOne`: replace the encoded matches
    (`.imp (.box (.imp φ .bot)) .bot` at `:91/:109/:134/:142`) with native per-connective rules —
    `andPos/andNeg`, `orPos/orNeg`, `impPos/impNeg`, `boxPos` (persistent), `boxNeg` (fresh
    successor), `diamondPos` (fresh successor, existential), `diamondNeg` (persistent) — per the
    v1 Phase B rule table (K-sound successor scoping).
  - [ ] `Tableau/Branch.lean`: update `boxPositivesOf`/propagation `filterMap` matches
    (`:98-134`) to native `.box`/`.diamond`.
  - [ ] `Tableau/Closure.lean`: update any connective-shape references (signed-atom/⊥
    contradiction detection unchanged).
- **Timing:** ~2.5 hours
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Modal/Tableau/{Defs,Rules,Branch,Closure}.lean`
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.Closure` (transitively Defs/Rules/
  Branch) green; `grep -n '\.imp (\.box' Cslib/Logics/Modal/Tableau/Rules.lean` empty; zero
  sorry/admit. Commit `task 441 phase 10: tableau core on native constructors`.
- **Risk/Fallback:** downstream files (Soundness.., FmpMeasure) may depend on the *statement*
  of `modalDiaOf?_dia`-style lemmas; keeping names but changing statements is intentional —
  downstream repairs belong to Phases 11-14, do not chase them here.

---

### Phase 11: Tableau soundness + saturation port [NOT STARTED]

- **Goal:** `SoundnessStep`, `Soundness`, `Saturation`, `LoopInduction` green on the native
  rules.
- **Tasks:**
  - [ ] `Tableau/SoundnessStep.lean`: re-establish `modalStepBranch_preserves_sat` per-rule
    obligations on native `Satisfies` cases (Phase 1 `@[grind =]` companions); keep
    `accFreshInv` freshness plumbing.
  - [ ] `Tableau/Soundness.lean`: port `modalExpandBranches_closed_unsat` + `modalTableau_sound`
    (worklist `forall₂_*` helpers are label-generic; verify signatures).
  - [ ] `Tableau/Saturation.lean`: port the fuel loop, `modalHintikkaSet`, entry point; confirm
    the fuel bound type-checks against the extended `modalComplexity`.
  - [ ] `Tableau/LoopInduction.lean`: verify the `forall₂_*` helpers compile unchanged.
- **Timing:** ~3 hours
- **Depends on:** 10
- **Files to modify:** `Cslib/Logics/Modal/Tableau/{SoundnessStep,Soundness,Saturation,LoopInduction}.lean`
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.Soundness` and `...Saturation` green;
  `#print axioms modalTableau_sound` standard-only; zero sorry/admit. Commit
  `task 441 phase 11: tableau soundness + saturation on native constructors`.
- **Risk/Fallback:** existing proofs were written against encoded rule outputs; where a proof
  case does not port mechanically, re-prove that case fresh on the native rule (the per-rule
  obligations are simpler natively — one constructor per connective). Do not preserve dead
  encoded-shape helper lemmas; delete them.

---

### Phase 12: Tableau completeness port (Completeness.lean) [NOT STARTED]

- **Goal:** `Tableau/Completeness.lean` (832 lines, 67 decomposer references) green.
- **Tasks:**
  - [ ] Port `extractModel` + Hintikka bridge lemmas to native constructors; where the file's
    truth-lemma/bridge structure did strong-induction or encoded-shape dispatch, simplify to
    structural cases when the port forces a rewrite (v1 Phase E payoff), otherwise port
    minimally.
  - [ ] Add `.and/.or/.diamond` cases to every exhaustive match/induction; repair uses of the
    reshaped `modalDiaOf?_dia`-family lemmas.
  - [ ] Discharge the file's public completeness theorems against the ported Saturation layer.
- **Timing:** ~3 hours
- **Depends on:** 11
- **Files to modify:** `Cslib/Logics/Modal/Tableau/Completeness.lean`
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.Completeness` green;
  `#print axioms` standard-only on the module's public theorems; zero sorry/admit. Commit
  `task 441 phase 12: tableau completeness port`.
- **Risk/Fallback:** if the encoded-era Hintikka bridge lemmas (the v1-era `imp`-bridge
  descendants) turn out false or unprovable natively, delete and replace with per-connective
  bridges (one lemma per native constructor) — the design v1 prescribed. Budget one extra
  dispatch if the bridge set needs redesign; mark [PARTIAL] between dispatches.

---

### Phase 13: FmpMeasure port (3011 lines) [NOT STARTED]

- **Goal:** `Tableau/FmpMeasure.lean` — added by tasks 442/462, absent from plan v1 — green on
  native constructors.
- **Tasks:**
  - [ ] Survey with `lean_file_outline` + `lake build ... | tail -60` FIRST; classify errors into
    (a) exhaustive matches/inductions needing `.and/.or/.diamond` cases, (b) decomposer shape
    lemmas, (c) measure-decrease proofs referencing encoded sizes.
  - [ ] Extend every exhaustive match/induction; new cases for the measure functions follow the
    binary (`imp`-like) and unary (`box`-like) templates already present.
  - [ ] Re-prove measure-decrease lemmas where `sizeOf`/complexity arithmetic changes (native
    `and/or/diamond` have direct subterm decrease — strictly simpler than the encoded nesting).
- **Timing:** ~3.5 hours (pre-authorized second dispatch if error count after triage exceeds ~40)
- **Depends on:** 12 (verify import direction at phase start; if FmpMeasure does not import
  Completeness, this phase may start after 11)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` green; zero sorry/admit.
  Commit `task 441 phase 13: FmpMeasure port`.
- **Risk/Fallback:** largest single file in the task. If the measure-decrease arithmetic for the
  new constructors breaks a downstream termination proof, adjust the measure weights (any
  strictly-monotone assignment works for the decrease lemmas) rather than restructuring proofs.
  Split-dispatch seam: measure definitions + shape lemmas first, decrease/termination proofs
  second.

---

### Phase 14: CompletenessLoop port (1096 lines) [NOT STARTED]

- **Goal:** `Tableau/CompletenessLoop.lean` — added by tasks 442/462, absent from plan v1 —
  green; the whole Tableau directory builds.
- **Tasks:**
  - [ ] Port the file's 4 decomposer references and any exhaustive inductions (expected light:
    grep found only 4 decomposer hits).
  - [ ] `lake build` the full `Cslib/Logics/Modal/Tableau/` directory.
- **Timing:** ~1.5 hours
- **Depends on:** 13
- **Files to modify:** `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
- **Verification:** full Tableau subtree builds green; zero sorry/admit. Commit
  `task 441 phase 14: CompletenessLoop port (tableau subtree green)`.
- **Risk/Fallback:** if CompletenessLoop consumes FmpMeasure lemmas whose statements changed in
  Phase 13, repair here (Phase 13 must log any statement changes in its commit message for this
  phase's dispatch).

---

### Phase 15: Full-library build, barrel, CI, zero-debt sweep [NOT STARTED]

- **Goal:** Whole repository green; merge-ready.
- **Tasks:**
  - [ ] Repo-wide consumer re-grep: `grep -rn "Modal.Proposition\|Logic.Modal" Cslib/ CslibTests/`
    outside `Logics/Modal/` — repair any straggler (tests included).
  - [ ] `lake exe mk_all --module` (barrel completeness for any file-set changes).
  - [ ] Full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
    `lake shake --add-public --keep-implied --keep-prefix`.
  - [ ] Zero-debt sweep: `grep -rn 'sorry\|admit\|^axiom \|^\s*axiom ' Cslib/Logics/Modal/
    Cslib/Foundations/Logic/` empty; `lean_verify`/`#print axioms` on `truth_lemma`,
    `strong_completeness`, `modalTableau_sound`, and the tableau completeness theorems —
    standard axioms only.
  - [ ] Merge `task-441-native-refactor` to main (fast-forward or merge commit per repo
    convention); final commit `task 441: complete implementation`.
- **Timing:** ~1.5 hours
- **Depends on:** 9, 14
- **Files to modify:** barrel files as flagged by `mk_all`; stragglers only
- **Verification:** all CI commands exit 0. Commit + merge.
- **Risk/Fallback:** `lake shake` may flag import churn from the new Foundations imports —
  apply its suggested fixes; if `lake test` smoke-tests decide formulas via the tableau,
  verify a native `◇/∧/∨` formula decides correctly (add a CslibTests case if none exists).

---

## Testing & Validation

- [ ] `lake build` (full library) green at Phase 15; per-phase targeted module builds green at
  each phase gate.
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public
  --keep-implied --keep-prefix` all pass.
- [ ] Zero `sorry`, zero `admit`, zero Lean `axiom` declarations across `Cslib/Logics/Modal/`
  and `Cslib/Foundations/Logic/` (grep + `#print axioms` on `truth_lemma`,
  `strong_completeness`, `modalTableau_sound`, tableau completeness theorems).
- [ ] The 8 new schemata appear in all 15 axiom inductives with soundness cases (spot-check via
  `lean_local_search andI` per system namespace).
- [ ] Semantic smoke checks: `Satisfies.dual` holds as a theorem (not `rfl`); a native
  `◇p ∧ ◇q`-style formula elaborates, satisfies, and (if the tableau decides it) decides
  correctly.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Basic.lean` (Phase 1 — native datatype, HasAnd/HasOr/HasDia, Satisfies)
- `Cslib/Logics/Modal/{LogicalEquivalence,Denotation,FromPropositional}.lean` (Phase 1)
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` (Phase 1)
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (Phases 1-2)
- `Cslib/Logics/Modal/ProofSystem/Instances/*.lean` (15 files, Phases 1-3)
- `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean` (15 files, Phase 4)
- `Cslib/Logics/Modal/Metalogic/MCS.lean` (Phase 5)
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` (Phases 6-8)
- `Cslib/Logics/Modal/Metalogic/Systems/*/{Completeness,ConservativeExtension}.lean` (Phase 9)
- `Cslib/Logics/Modal/Metalogic/{InterSystem/*,GenericMCSBridge,DeductionTheorem,Soundness}.lean`,
  `Cslib/Logics/Modal/Cube.lean` (Phase 9, as needed)
- `Cslib/Logics/Modal/Tableau/{Defs,Rules,Branch,Closure}.lean` (Phase 10)
- `Cslib/Logics/Modal/Tableau/{SoundnessStep,Soundness,Saturation,LoopInduction}.lean` (Phase 11)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (Phase 12)
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (Phase 13)
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (Phase 14)
- Barrel/import updates per `mk_all` (Phase 15)
- `summaries/02_native-refactor-hasdia-duality-summary.md` (on completion)

## Rollback/Contingency

- The whole track runs on branch `task-441-native-refactor`; main stays green throughout.
  Rollback unit = the branch; `git checkout` of the last per-phase commit always recovers the
  furthest green-gated state.
- If Phase 1 cannot bring `ModalEmbedding.lean` green, do not proceed (the datatype change must
  not strand the Bimodal layer): revert and re-scope.
- If Phase 8 (diamond existence lemma) stalls after two genuine dispatches: commit the Phase 6
  green state, mark Phase 8 [BLOCKED] with the precise open goal, `/spawn` a dedicated task.
  The Tableau track (10-14) is independent and may continue.
- If FmpMeasure (Phase 13) exceeds its split-dispatch budget: mark [PARTIAL] with the triaged
  error inventory; the phase resumes from the seam.
- Never commit `sorry`, `admit`, or Lean `axiom` declarations under any contingency. The new
  axiom *schemata* (inductive constructors) are the single sanctioned design exception,
  justified in the Overview.
- Plan v1 (`plans/01_modal-proposition-native-refactor.md`) and the blocker handoff remain as
  reference; this plan supersedes v1 but does not delete it.
