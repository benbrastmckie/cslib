# Implementation Plan: Task #370 — Sorry-Free Int/Min Decidability via FMP

- **Task**: 370 - int_min_metalogic_decidability
- **Status**: [IN PROGRESS] — Phase 1 spike GO (architecture validated); resume from Phase 1 cleanup
- **Effort**: ~10 hours remaining (est. 800-1400 Lean lines across Int+Min; spike de-risked)
- **Dependencies**: None
- **Research Inputs**: specs/370_int_min_metalogic_decidability/reports/01_int-min-decidability-fmp-vs-lj.md
- **Artifacts**: plans/01_int-min-fmp-decidability.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Establish genuinely **sorry-free** `Decidable (Derivable IntPropAxiom φ)` and
`Decidable (Derivable MinPropAxiom φ)` via the **finite model property (FMP)**, building a
**direct finite canonical Kripke model** (research strategy (b)) over `Σ`-bounded prime
saturated theories, where `Σ := subformulas φ`. The existing tableau-backed decidability
instances are sorry-tainted and the LJ-bridge route inherits that taint; both are rejected by
the research. The whole task reduces to a sorry-free decidable characterization of derivability,
assembled through the already-trusted, sorry-free metalogic completeness `Iff`s
(`int_soundness_completeness`, `min_soundness_completeness`) and the reusable sorry-free
canonical-model assets (`int_truth_lemma`/`min_truth_lemma` templates, the Lindenbaum toolkit).

The single HIGH-risk component is the **`Σ`-bounded finite Lindenbaum lemma**
(`int_fin_imp_witness`) together with the **`Fintype`/decidability of the bounded world type**
(R2). **Definition of done**: both `Decidable` instances type-check sorry-free (verified with
`lean_verify` / axiom audit) and the full CI pipeline is green; OR, if the Phase 1 de-risking
spike cannot discharge the finite Lindenbaum + Fintype obligations sorry-free within bounded
effort, the task is marked **[BLOCKED]** with an exact recorded goal state — never a `sorry`,
and never a fallback to the tableau instance.

### Current State (updated 2026-06-27 — supersedes the original [BLOCKED])

The original blocker ("FMP go/no-go did not cleanly resolve; 1 remaining sorry in the
finite-Lindenbaum/Fintype witness") is **stale**. Re-inspection of committed code shows the
HIGH-risk design questions are effectively **resolved**, and the remaining work is concrete:

- **Phase 1 spike result = GO.** `Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean` is
  committed (orchestration commit `1977f78b`) and contains **no `sorry`**. The two gating
  obligations are essentially in place:
  - `Fintype (IntFinWorld φ)` — **DONE** via `Fintype.ofInjective` on the carrier→`Σ.powerset`
    embedding (`instFintypeIntFinWorld`). This solves risk R2 *without* deciding `SetDerivable`.
  - `int_fin_imp_witness` — **architecture validated, ~95% complete.** The spike abandons the
    from-scratch *finite* Lindenbaum (original R1) for a cleaner route: lift `w` to the existing
    **infinite** canonical model, apply the already-proven sorry-free `int_imp_witness` +
    `int_prime_exclusion`, then **restrict the resulting prime DCCS back to Σ**
    (`carrier' := φ.subformulas.filter (· ∈ T'')`). This sidesteps Zorn-for-finite-models. The
    helper `intFinWorld_propConsistent` is also complete.
- **The committed spike does NOT compile.** A scoped `lake build` of the module reports two
  concrete, ordinary errors inside `int_fin_imp_witness` (no `sorry`, no feasibility wall):
  1. **Parse error** — a hypothesis is named `hψ'Σ`; `Σ` is a reserved Lean 4 token. Rename to
     ASCII (e.g. `hψ'mem`).
  2. **Unsolved goals in the `closed'` field proof** — the restriction-to-Σ deductive-closure
     argument (`SetDerivable IntPropAxiom ↑carrier' ψ' → ψ' ∈ carrier'`) does not close. The
     pieces are present (`SetDerivable_weakening` from `↑carrier' ⊆ ↑T''`, then T''’s DCCS
     closure field `IntDCCS.2 : ∀ L φ, (∀ x∈L, x∈T'') → Deriv L φ → φ ∈ T''`); the projection
     wiring via `h_sd_T''.choose`/`.choose_spec` mismatches the actual shape of `SetDerivable`
     and must be re-derived.
- **Trap:** the spike file is an **orphan — not in `Cslib.lean`** — so the full `lake build`
  never compiles it. That is why the orchestration reported success and CI looked green while
  leaving a broken committed file. Any resume MUST either fix-and-promote it into a barreled
  file or delete it; it must not be left as a committed non-compiling orphan.
- **Phase 2 already exists.** `Cslib/Logics/Propositional/Subformula.lean` (committed under task
  334, in the barrel) provides `subformulas`, `Proposition.IsSubformula`, and the closure lemmas
  (`imp_left/right`, `and_left/right`, `or_left/right`, `refl`, `trans`). Phase 2 is therefore
  a no-op beyond importing it — do **not** redefine these.

**Resume point:** Phase 1 cleanup (fix the two compile errors), then Phases 3→7 with Phase 2
collapsed to an import. Standard `/implement`/`/orchestrate` is appropriate (the risky design is
settled); only escalate to `--hard` or split Int/Min into separate dispatches if a re-dispatch
again overflows context on the `int_fmp` ↔ truth-lemma assembly.

### Research Integration

Key findings driving this plan (from report 01):
- **Both existing Int/Min decidability instances are sorry-tainted** via the tableau
  completeness witnesses (`intuitionisticTableau_complete` 4 sorries; `minimalTableau_complete`
  / `minTruthLemma` 3 sorries). Goal is a tableau-**independent** sorry-free instance.
- **LJ-bridge route REJECTED**: `instDecidableLJDerivable` is itself
  `decidable_of_iff (IValid …)` routed through the tableau; bridging to it re-imports the taint.
  No terminating syntactic LJ search (G4ip/LJT) exists in-tree, so LJ is not a clean source.
- **FMP route RECOMMENDED (strategy b)**: direct finite canonical model; worlds = `Σ`-bounded
  prime saturated theories, preorder = `⊆`, `val w p := .atom p ∈ w.carrier`; decision
  enumerates `(subformulas φ).powerset`.
- **Reusable sorry-free assets** (cite in implementation): `int_soundness`/`min_soundness`
  (→ direction), `int_truth_lemma` (IntStrongCompleteness.lean:97) / `min_truth_lemma` as
  line-for-line proof **templates**, `int_imp_witness`/`int_prime_exclusion`
  (IntLindenbaum.lean:234/319) and Min mirrors as **patterns** for the finite (Zorn-free)
  Lindenbaum, `SetDerivable` + deduction theorem (`DeductionTheorem.lean`),
  `Proposition` `DecidableEq` (Defs.lean:92), `Finset.powerset`,
  `Fintype.ofFinset`, `Fintype.decidableForallFintype`.
- **R2 crux**: the world `closed` field references `SetDerivable` (a `Prop` over unbounded
  derivations); to keep `Fintype`/membership-decidability we must **not** decide `SetDerivable`.
  Resolution: define worlds as `Σ.powerset.filter P` with a purely finitary `P`, proving
  separately that filtered sets are exactly restrictions of prime DCCS.
- **Min mirror** is structurally identical but drops the `consistent` field (⊥ may belong) and
  has a trivial bot case (`min_truth_lemma` bot case is `Iff.rfl`), so it is strictly easier.
- **`noncomputable` is acceptable** per the task (finite Lindenbaum extension uses classical
  choice over a finite domain); the decision `Prop` itself is `Decidable` via
  `Fintype.decidableForallFintype`. No new axioms, no `sorry`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; ROADMAP.md not consulted. No roadmap phases
added.

## Goals & Non-Goals

**Goals**:
- Sorry-free `Decidable (Derivable IntPropAxiom φ)` independent of the tableau.
- Sorry-free `Decidable (Derivable MinPropAxiom φ)` independent of the tableau.
- A reusable, sorry-free FMP layer: `subformulas` closure, `IntFinWorld`/`MinFinWorld`
  (+`Fintype`, `Preorder`), finite truth lemma, finite Lindenbaum witness, `int_fmp`/`min_fmp`.
- Full CSLib CI pipeline green on all new files.
- An **early go/no-go decision** (Phase 1 spike) that prevents sunk effort on the full build if
  the HIGH-risk core is infeasible.

**Non-Goals**:
- Discharging the 4 tableau completeness sorries (would clean the *existing* instances but the
  task mandates tableau independence — explicitly out of scope).
- Bridging to / repairing the LJ decidability instance.
- Deprecating or re-routing the existing tableau instances (a possible future follow-up noted
  only in R6; not in scope here).
- Requiring `[Fintype Atom]` to be dropped; matching the classical instance signature
  (`[Fintype Atom] [DecidableEq Atom]`) is acceptable (R5).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: `int_fin_imp_witness` finite (Zorn-free) Lindenbaum resists clean construction | H | M | **Phase 1 de-risking spike** isolates this before committing later phases; mirror `int_imp_witness`+`int_prime_exclusion` patterns with finite iteration over Σ |
| R2: `IntFinWorld` `Fintype`/membership-decidability blocked by `closed` field referencing `SetDerivable` (Prop over unbounded derivations) | H | M | Define worlds as `Σ.powerset.filter P` with finitary `P`; prove equivalence to "restriction of prime DCCS" separately; never decide `SetDerivable`. Validated in Phase 1 spike |
| R3: Intuitionistic `imp` truth-lemma case needs the witness world (Phase 4 ↔ finite Lindenbaum) | M | M | Land the finite Lindenbaum witness in Phase 1/3 first; Phase 4 imp case is then a direct call |
| R4: Universe polymorphism of `IValid` when instantiating the finite model in (→) | L | L | Pick `World := IntFinWorld φ : Type _`; `int_soundness`/`IValid` are polymorphic; for (←) target `Derivable` directly via `int_fmp`, bypassing `IValid` |
| R5: Whether `[Fintype Atom]` is required | L | L | Add `[Fintype Atom] [DecidableEq Atom]` to match classical instance signature; acceptable simplification |
| R6: Naming collision with existing `instDecidableDerivableIntPropAxiom` (tableau) | L | M | Place new instances in a new file/namespace or use a primed name |
| R7: `lake shake` / `checkInitImports` / import minimization on new files | L | M | `import Cslib.Init` first; run `lake exe mk_all --module`; standard CI hygiene in Phase 7 |
| R8: Effort overrun (1000-1800 lines) exceeds a single cycle | M | M | Staged phases, Int and Min separated, commit at each green `lake build` milestone |
| R9: Spike fails → temptation to `sorry` or fall back to tableau | H | L | **Hard constraint**: on spike failure mark [BLOCKED] with exact goal state; no sorry, no tableau fallback (see Phase 1 and Rollback) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |

Phases within the same wave can execute in parallel. This plan is fully sequential: every phase
after the Phase 1 spike gate is **conditional on the spike succeeding** (see Phase 1).

---

### Phase 1: Spike Cleanup — Make `IntFMPSpike.lean` Compile (GO already decided) [IN PROGRESS]

**Goal**: The go/no-go gate is **decided GO** — the spike `IntFMPSpike.lean` already contains a
sorry-free `Fintype (IntFinWorld φ)` and an ~95%-complete `int_fin_imp_witness` built via the
infinite-canonical-model-restricted-to-Σ route (NOT the original finite-iteration Lindenbaum).
The remaining Phase 1 work is to **make the file compile** by fixing the two concrete errors
surfaced by `lake build Cslib.Logics.Propositional.Metalogic.IntFMPSpike`, then proceed.

**Tasks**:
- [ ] **Fix the parse error**: the hypothesis named `hψ'Σ` (in the `closed'` field proof) uses
      the reserved Lean 4 token `Σ`. Rename to an ASCII identifier (e.g. `hψ'mem`) and update its
      use sites.
- [ ] **Close the `closed'` field goal** `SetDerivable IntPropAxiom (↑carrier') ψ' → ψ' ∈ carrier'`
      inside `int_fin_imp_witness`. The route is already scaffolded but the final projection
      fails:
      - `carrier' := φ.subformulas.filter (· ∈ T'')`, so `↑carrier' ⊆ ↑T''` as sets.
      - Weaken the derivation with `SetDerivable_weakening h_sub_set h_sd'` to get
        `SetDerivable IntPropAxiom ↑T'' ψ'`.
      - Apply T''’s DCCS closure field. `IntDCCS S = PropSetConsistent .. S ∧ (∀ L φ, (∀ x∈L, x∈S)
        → Deriv L φ → φ ∈ S)`, reached via `hT''_prime.1.2`. Re-derive the witness list/membership/
        derivation from `SetDerivable` directly (the current `h_sd_T''.choose`/`.choose_spec.1/.2`
        wiring mismatches the actual `SetDerivable` shape — use `obtain ⟨L, hLsub, hLderiv⟩ := h_sd_T''`
        or the correct accessor) so that `ψ' ∈ T''`, hence `ψ' ∈ carrier'`.
- [ ] Verify the whole spike module compiles: `lake build Cslib.Logics.Propositional.Metalogic.IntFMPSpike`.
- [ ] `lean_verify` axiom audit on `int_fin_imp_witness`, `instFintypeIntFinWorld`,
      `intFinWorld_propConsistent`: no `sorryAx`; only permitted axioms (`Classical.choice` etc.).
- [ ] Decide the orphan-file disposition (carried out in Phase 3): the validated defs/lemmas are
      **promoted** into the barreled `IntDecidability.lean`; the scratch `IntFMPSpike.lean` is then
      **deleted** (it must not remain as a committed, un-barreled, formerly-broken file).

**Timing**: 1-1.5 hours

**Depends on**: none (resume point)

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean` — fix the two compile errors; this is
  the scratch source that Phase 3 promotes then deletes.

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.IntFMPSpike` is green.
- `int_fin_imp_witness`, `instFintypeIntFinWorld`, `intFinWorld_propConsistent` type-check with no
  `sorry`/`admit` (`lean_verify` / `#print axioms` shows only permitted axioms).

---

### Phase 2: Subformula Closure Infrastructure [COMPLETED — pre-existing]

**Goal**: Provide the `subformulas` Finset closure and its closure lemmas. **Already satisfied
by committed code** — no new work.

**Status**: `Cslib/Logics/Propositional/Subformula.lean` (committed under task 334, present in
the `Cslib.lean` barrel) already provides:
- `Proposition.subformulas : Proposition Atom → Finset (Proposition Atom)` over all 5 constructors;
- `Proposition.IsSubformula` (`A.IsSubformula B ↔ A ∈ B.subformulas`);
- closure lemmas `IsSubformula.refl`, `.trans`, `.and_left/.and_right`, `.or_left/.or_right`,
  `.imp_left/.imp_right`.

**Tasks**:
- [ ] In `IntDecidability.lean`, `import Cslib.Logics.Propositional.Subformula` and use
      `φ.subformulas` / `Proposition.IsSubformula` directly. Do **NOT** redefine `subformulas`
      or the closure lemmas (the spike already depends on these names).
- [ ] If any specific finset-membership form is needed downstream (e.g. `self_mem_subformulas`),
      derive it from `IsSubformula.refl` rather than defining a new lemma.

**Timing**: 0 hours (verification only)

**Depends on**: 1

**Files to modify**: none (import only).

**Verification**:
- `Cslib/Logics/Propositional/Subformula.lean` builds (already in barrel); names resolve.

---

### Phase 3: Promote Spike Into Barreled `IntDecidability.lean` [NOT STARTED]

**Goal**: Move the now-compiling spike construction (`IntFinWorld`, `IntFinWorld.ext`,
`instPreorderIntFinWorld`, `instFintypeIntFinWorld`, `intFinWorld_propConsistent`,
`int_fin_imp_witness`) from the scratch `IntFMPSpike.lean` into a committed, barreled file, and
delete the orphan. The construction itself is already validated in Phase 1 — this phase is
relocation + barrel hygiene, not new proof work.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` with `import Cslib.Init`
      first line, plus `import Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness` and
      `import Cslib.Logics.Propositional.Subformula`.
- [ ] Move the validated definitions/instances/lemmas verbatim from `IntFMPSpike.lean`. Keep the
      `Fintype.ofInjective`-based `instFintypeIntFinWorld` and the infinite-canonical-restriction
      proof of `int_fin_imp_witness` (the route validated in Phase 1).
- [ ] `lake exe mk_all --module` to register the new file in the `Cslib.lean` barrel.
- [ ] **Delete `Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean`** (orphan removed).
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.IntDecidability` green; axiom audit clean.

**Timing**: 1-1.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` (new) — promoted world type +
  instances + `int_fin_imp_witness`.
- `Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean` (delete).
- `Cslib.lean` (barrel, via `mk_all`).

**Verification**:
- `lake build` (scoped) green; new file in barrel; `IntFMPSpike.lean` removed.
- `#print axioms` on the instances shows only permitted axioms.

---

### Phase 4: Valuation, Upward Closure, Finite Truth Lemma [NOT STARTED]

**Goal**: Define the finite valuation and prove `int_fin_truth_lemma` by mirroring
`int_truth_lemma` (IntStrongCompleteness.lean:97) case-for-case; the `imp` backward case calls
the Phase 1 `int_fin_imp_witness`.

**Tasks**:
- [ ] Define `intFinVal (w : IntFinWorld φ) (p : Atom) : Prop := .atom p ∈ w.carrier`.
- [ ] Prove `intFinVal_upward_closed` from the `⊆` order.
- [ ] Prove `int_fin_truth_lemma (w) {ψ} (hψ : ψ ∈ subformulas φ) :
      IForces intFinVal (fun _ => False) w ψ ↔ ψ ∈ w.carrier`. Mirror `int_truth_lemma` for
      `atom`/`bot`/`and`/`or`; the `imp` backward case uses `int_fin_imp_witness` (Phase 1),
      with subformula closure lemmas (Phase 2) supplying `ψ, χ ∈ Σ`.

**Timing**: 2-3 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` — valuation + truth lemma.

**Verification**:
- `lake build` green; `int_fin_truth_lemma` sorry-free (`lean_verify`).

---

### Phase 5: FMP Characterization + Decidable Instance (Int complete) [NOT STARTED]

**Goal**: Assemble `int_fmp` and derive the sorry-free `Decidable (Derivable IntPropAxiom φ)`.

**Tasks**:
- [ ] Prove `int_fmp (φ) : Derivable IntPropAxiom φ ↔ ∀ w : IntFinWorld φ, φ ∈ w.carrier`.
      (→) via sorry-free `int_soundness` → `IValid`, instantiated at `World := IntFinWorld φ`,
      using `int_fin_truth_lemma` with `self_mem_subformulas` (R4). (←) by contrapositive:
      finite-Lindenbaum-style extension of the Σ-closure of ∅ omitting φ to a world with
      `φ ∉ w.carrier` (built on Phase 1/4).
- [ ] Define `noncomputable instance instDecidableDerivableIntPropAxiom' (φ) :
      Decidable (Derivable IntPropAxiom φ) := decidable_of_iff _ (int_fmp φ).symm`, with
      `∀ w : IntFinWorld φ, φ ∈ w.carrier` decidable via `Fintype.decidableForallFintype` +
      `DecidableEq (Proposition Atom)`. Use a primed name / new namespace to avoid R6 collision.
- [ ] Axis-audit the instance: confirm transitively sorry-free and tableau-independent.

**Timing**: 2-3 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` — `int_fmp` + Decidable instance.

**Verification**:
- `lake build` green; `lean_verify` / `#print axioms instDecidableDerivableIntPropAxiom'` shows
  no `sorryAx` and no dependence on `intuitionisticTableau_complete`.

---

### Phase 6: Minimal Mirror (`MinFinWorld` → `min_fmp` → Decidable) [NOT STARTED]

**Goal**: Replicate Phases 2-5 for Minimal logic in `MinDecidability.lean`. Structurally
identical; drop the `consistent` field (⊥ may belong), add the `minBotForces`-style bot
predicate on worlds, and reuse `min_truth_lemma`/`min_imp_witness`/`min_prime_exclusion`
patterns. The bot case is `Iff.rfl`-trivial (MinStrongCompleteness.lean:41), so this is easier
than Int.

**Tasks**:
- [ ] New file `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` (`import Cslib.Init`).
- [ ] `subformulas` is shared (import from Int file) — do not redefine.
- [ ] Define `MinFinWorld φ` (no `consistent` field), `Fintype`, `Preorder`, decidable
      membership (mirror Phase 3).
- [ ] Define `minFinVal` + the bot-forces predicate; prove upward closure; prove
      `min_fin_truth_lemma` (mirror Phase 4; bot case `Iff.rfl`).
- [ ] Prove `min_fin_imp_witness` (mirror Phase 1; uses `min_soundness`/`min_imp_witness`
      patterns).
- [ ] Prove `min_fmp` and define
      `noncomputable instance instDecidableDerivableMinPropAxiom' (φ) :
      Decidable (Derivable MinPropAxiom φ) := decidable_of_iff _ (min_fmp φ).symm`.

**Timing**: 3-4 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` (new) — full Min mirror.

**Verification**:
- `lake build` green; `#print axioms instDecidableDerivableMinPropAxiom'` shows no `sorryAx`
  and no dependence on `minimalTableau_complete`/`minTruthLemma`.

---

### Phase 7: CI Verification + Import Hygiene [NOT STARTED]

**Goal**: Pass the full CSLib CI pipeline on all new files and finalize import hygiene.

**Tasks**:
- [ ] `lake build` (full).
- [ ] `lake test` (CslibTests suite).
- [ ] `lake exe checkInitImports` (verify `Cslib.Init` imports).
- [ ] `lake exe lint-style`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (dependency minimization).
- [ ] `lake exe mk_all --module` to register the two new files.
- [ ] Final axiom audit on both `Decidable` instances: sorry-free and tableau-independent.

**Timing**: 1-1.5 hours

**Depends on**: 6

**Files to modify**:
- Import index / `mk_all`-generated module list as required; fixes surfaced by lint/shake on the
  two new files.

**Verification**:
- All five CI commands exit 0; both instances pass the axiom audit (no `sorryAx`, no tableau
  completeness witnesses in the dependency closure).

## Testing & Validation

- [ ] `lake build` green across `IntDecidability.lean` and `MinDecidability.lean`.
- [ ] `lake test` passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (no unused imports).
- [ ] `#print axioms instDecidableDerivableIntPropAxiom'` — no `sorryAx`; no
      `intuitionisticTableau_complete` in closure.
- [ ] `#print axioms instDecidableDerivableMinPropAxiom'` — no `sorryAx`; no
      `minimalTableau_complete`/`minTruthLemma` in closure.
- [ ] Spike lemmas (`int_fin_imp_witness`, `Fintype (IntFinWorld φ)`) verified sorry-free at the
      Phase 1 gate.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` — `subformulas` + closure,
  `IntFinWorld` (+`Fintype`,`Preorder`), `intFinVal`, `int_fin_truth_lemma`,
  `int_fin_imp_witness`, `int_fmp`, `instDecidableDerivableIntPropAxiom'`.
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` — Min mirror through
  `instDecidableDerivableMinPropAxiom'`.
- (Phase 1 only) `IntFMPSpike.lean` scratch — discarded or promoted; never committed with `sorry`.
- `specs/370_int_min_metalogic_decidability/summaries/01_int-min-fmp-decidability-summary.md`
  (implementation summary, on completion).

## Rollback/Contingency

- **Spike NO-GO (Phase 1 fails)**: This is the planned contingency, not an error. Mark the task
  `[BLOCKED]` with the exact failing `lean_goal` state(s) and the obstruction recorded in the
  return metadata and summary. **Do not** introduce any `sorry` into committed code and **do
  not** fall back to the tableau-backed instance (that would re-import the taint the task
  forbids). Discharging the 4 tableau completeness sorries is an explicitly out-of-scope
  alternative path noted only for completeness.
- **Mid-build failure (Phases 2-6)**: each phase ends at a green `lake build` and is committed
  incrementally; revert the offending phase's file changes (git) to the last green commit and
  re-dispatch from that phase. No partial `sorry` is ever committed.
- **CI failure (Phase 7)**: fix import/lint/shake issues on the two new files; if a deeper
  soundness issue surfaces, revert to the last green per-phase commit and re-plan rather than
  patch with `sorry`.
- **Zero-debt invariant**: at no point is a `sorry`, `admit`, or new axiom (beyond the
  permitted `Classical.choice` on `noncomputable` defs) committed. Any inability to proceed
  sorry-free resolves to `[BLOCKED]`, never to debt.
