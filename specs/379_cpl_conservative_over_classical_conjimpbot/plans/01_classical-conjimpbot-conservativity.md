# Implementation Plan: Task #379 - CPL Conservative over Classical ⟨∧,→,⊥,⊤⟩ Fragment

- **Task**: 379 - Prove CPL is conservative over its classical conjunctive-implicational-falsum fragment CPL⟨∧,→,⊥,⊤⟩ (CL-C)
- **Status**: [COMPLETED]
- **Effort**: ~3.5 hours
- **Dependencies**: Task 378 (the ∧-extended Kalmár truth lemma `classicalConjImp_kalmar` + the derived-lemma / `litCtx` / collapse machinery in `Metalogic/ClassicalConjImpCompleteness.lean`); Task 377 (`ClassicalConjImpBotAxiom`, its `toPropAxiom`, the EFQ axiom, and `classicalConjImpBotAxiom_hasDeductionTheorem`). Both are currently `[PLANNING]` — see Risk R0.
- **Research Inputs**: None (no research report for this task). Grounding: task-352 landed proof `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` (the proven Kalmár/Tarski–Bernays template), task-378 plan/module (the ∧ extension this builds on), and the intuitionistic analogue `Semantics/Algebra/ConjImpBotConservative.lean` (the ⊥-case / conservativity-edge shape).
- **Artifacts**: plans/01_classical-conjimpbot-conservativity.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib

## Overview

This task completes the **classical conservativity column to 4-for-4** (CL-A `CPL⟨→,⊤⟩`, CL-B
`CPL⟨∧,→,⊤⟩`, **CL-C `CPL⟨∧,→,⊥,⊤⟩` = this task**, plus the full CPL apex). The deliverable is the
one genuinely new completeness theorem

```lean
classicalConjImpBot_completeness : φ.IsOrFree = true → Tautology φ → Derivable ClassicalConjImpBotAxiom φ
```

proved by the **truth-assignment (Kalmár / Tarski–Bernays) method** — *not* algebraically (classical
fragments are not Heyting-complete, so the Brouwerian/algebraic route used on the intuitionistic side
does not transfer; see Non-Goals). From it we derive the conservativity edge
`cpl_conservative_over_classicalConjImpBot` (CPL conservative over CPL⟨∧,→,⊥,⊤⟩ for or-free formulas),
the subsumption direction, and the biconditional `classicalConjImpBot_iff_chain`.

**The crux is small.** Task 378 already builds the ∧-extended Kalmár truth lemma over the
`IsOrBotFree` predicate (atom / imp / and). This task widens the predicate to `IsOrFree` (which
additionally admits `⊥`) and adds exactly **one new inductive case to the truth lemma: `bot`**. Under
any Boolean assignment `BoolEvaluate v ⊥ = false`, so the `bot` case is the *easy* increment over 378:

- **TRUE side** (`BoolEvaluate v ⊥ = true → …`): vacuous — the hypothesis `false = true` is
  discharged by `simp`/contradiction. There is **no real TRUE obligation** because `⊥` is never true.
- **FALSE side** (`BoolEvaluate v ⊥ = false → Γ ⊢ ⊥ → goal`): immediate — `⊥ → goal` is exactly the
  EFQ / ex-falso axiom instance of `ClassicalConjImpBotAxiom` (the fragment now contains a *real* `⊥`,
  whose elimination axiom discharges the surrogate-implication directly).

All other content (atom / imp / and case recipes, the in-context derived helpers, `litCtx`, atom
collapse, the `goal := φ` recovery step, and the conservativity capstone) is **transcribed from the
task-378 module retargeted to `ClassicalConjImpBotAxiom`**, with the axiom-independent definitions
(`Proposition.atoms`, `litCtx`, `litCtx_mem`) reused by import. The conservativity edge composes
`classicalConjImpBot_completeness` with CPL soundness through `ClassicalConjImpBotAxiom.toPropAxiom`,
mirroring `cpl_conservative_over_imp` (task 352, `ClassicalImpCompleteness.lean:381`) and the
intuitionistic `ipl_conservative_over_conjImpBot` (`ConjImpBotConservative.lean:134`).

**After this lands the classical column is complete and the three towers — MPL (minimal), IPL
(intuitionistic), CPL (classical) — are structurally symmetric**, each conservative over its
⟨∧,→,⊥,⊤⟩ rung by the route appropriate to it (algebraic/Brouwerian for MPL/IPL, truth-assignment for
CPL).

### Research Integration

No research report exists for task 379. The authoritative grounding sources are:

- **Task-352 landed module** `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean`
  (402 lines, CI-green) — the proven Kalmár/Tarski–Bernays template. Every structural element of this
  plan (soundness via `toPropAxiom`, in-context helpers `imp_trans_ctx`/`weaken_ctx`, the
  falsum-surrogate `litCtx`, `litCtx_mem`, `classicalImp_kalmar` double-negation truth lemma,
  `elim_atom`, `collapse`, the `goal := φ` recovery in `classicalImp_completeness`, and the
  conservativity/subsumption/biconditional triple) is reproduced one fragment up.
- **Task-378 module** `Metalogic/ClassicalConjImpCompleteness.lean` (the `∧` extension) — supplies the
  exact `and`-case recipe and the `ClassicalConjImpAxiom` derived lemmas to transcribe. **If 378 has
  not yet landed**, the `and`-case is reconstructed by mirroring the ∧-projection/pairing pattern of
  the intuitionistic `ConjImpConservative.lean` adapted to the truth-assignment context (see R0).
- **Intuitionistic analogue** `Semantics/Algebra/ConjImpBotConservative.lean` — the `IsOrFree`
  predicate boundary, the ⊥-enables-the-bot-case observation
  (`ConjImpBotConservative.lean:48,87-90`), and the conservativity-edge / `_iff` shape
  (`hilbertIplConservativeOverConjImpBot`, `derivableConjImpBotOfDerivableInt`,
  `hilbertIplConservativeOverConjImpBot_iff`).

### Prior Plan Reference

No prior plan for task 379. Effort and phase structure are **calibrated against the task-352 plan v3**
(which decomposed the identical proof one fragment down into landed phases) and its CI-green module:
the genuinely hard lemma there was the Peirce subcase of the truth lemma, already solved and inherited
through 378; here the only new proof obligation is the trivial `bot` case, so this plan is shorter and
lower-risk than 352's.

### Roadmap Alignment

No `specs/ROADMAP.md` found in repository root. Within the implicit "classical conservativity column"
program (tasks 352 → 377 → 378 → 379), this task is the terminal CL-C rung that closes the column.

## Goals & Non-Goals

**Goals**:
- Create the new module `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpBotCompleteness.lean`
  with soundness `classicalConjImpBot_soundness` (via `ClassicalConjImpBotAxiom.toPropAxiom`).
- Land the `IsOrFree` Kalmár truth lemma `classicalConjImpBot_kalmar` — atom/imp/and cases transcribed
  from task 378, **plus the new `bot` case** (the easy increment; EFQ on the FALSE side, vacuous TRUE
  side).
- Land the `ClassicalConjImpBotAxiom`-targeted derived helpers, `elim_atom`, `collapse`, and the new
  theorem `classicalConjImpBot_completeness` (recovery at `goal := φ`).
- Land the conservativity edge `cpl_conservative_over_classicalConjImpBot`, the subsumption
  `derivablePropOfDerivableClassicalConjImpBot`, and the biconditional `classicalConjImpBot_iff_chain`;
  extend the conservativity-chain doc edge `CPL⟨∧,→,⊥,⊤⟩ ⊂ CPL`.
- Pass the full CI gate (`lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake`, barrel registration).

**Non-Goals** (hard constraints):
- **Truth-assignment / Kalmár method ONLY.** No `ImplicationAlgebra`/`HeytingAlgebra`/`TarskiAlgebra`
  typeclass, no Lindenbaum–Tarski / Brouwerian / pointed-lower-set construction, no Abbott embedding.
  Classical fragments are not Heyting-complete, so the algebraic route used by the *intuitionistic*
  `ConjImpBotConservative` does **not** transfer — only the conservativity-edge *shape* is mirrored,
  not its algebraic engine.
- **ZERO-DEBT.** No `sorry`, no new `axiom`, no vacuous definitions (`def X := True`, `:= trivial`,
  `:= Unit`, etc., per `.claude/rules/cslib.md`). If any phase is intractable within budget, mark it
  `[BLOCKED]` with the exact `lean_goal` stuck state — never paper over with a placeholder.
- **Strictly propositional, strictly additive.** New work confined to
  `Logics/Propositional/{Metalogic,Semantics/Algebra}`. Do not edit existing chain theorems or the
  task-352/378 modules (only import them); do not touch `Foundations/`.
- New completeness work lives in `Metalogic/ClassicalConjImpBotCompleteness.lean` (NOT
  `Semantics/Algebra/`); only the chain doc-edge + subsumption re-export touches
  `Semantics/Algebra/ConservativeChain.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R0: Dependencies 377/378 are still `[PLANNING]` — `ClassicalConjImpBotAxiom`, its EFQ axiom, `toPropAxiom`, the DT instance, and the 378 ∧-Kalmár recipe may not yet exist | H | M | Implementation must not start until 377 (axioms) and 378 (∧-Kalmár) are landed and CI-green. Phase 0 is an explicit dependency-gate check. If 378 has landed, **transcribe its atom/imp/and recipes verbatim** (retargeting the axiom constructor); if only 377 has landed, reconstruct the and-case from 352's imp-case pattern + the ∧-projection/pairing axioms (mirror `ConjImpConservative`). If neither is landed, mark the whole plan `[BLOCKED]` — do not stub. |
| R1: the truth lemma is one induction — the `bot` case cannot be "bolted on" externally; `classicalConjImpBot_kalmar` must restate **all** of atom/imp/and/bot | M | H (certain) | Accepted by design. Atom/imp/and are mechanical transcriptions from 378 (zero new mathematics); only `bot` is new and it is trivial (vacuous TRUE side + one EFQ axiom on the FALSE side). Keep the lemma ≤ ~75–90 lines; factor the `imp`/`and` cases into private helpers if context budget is tight. |
| R2: EFQ axiom name/shape from 377 unknown at plan time (`.exfalso goal` vs `.botElim goal` vs `⊥ → φ` as `.efq φ`) | M | M | Phase 1 resolves the exact constructor by `lean_local_search`/`lean_hover_info` on the landed `ClassicalConjImpBotAxiom`. The FALSE-side discharge is a single `⟨.ax _ _ (<efq> goal)⟩`; only the constructor name varies. Cross-check against the intuitionistic `ConjImpBotAxiom` EFQ constructor. |
| R3: derived lemmas (`imp_self`, `imp_trans(_ctx)`, `weaken_ctx`, `peirce_mp`, ∧-helpers, `elim_atom`, `collapse`) are axiom-set-specific — they reference `ClassicalConjImpBotAxiom` constructors and the 377 DT instance, so they must be re-derived, not imported | M | H | Transcribe each from 352/378 retargeting `.ax _ _ (.implyK …)` etc. and `classicalConjImpBotAxiom_hasDeductionTheorem`. The axiom-**independent** defs `Proposition.atoms`, `litCtx`, `litCtx_mem`, `litCtx_congr` ARE reused by import from `ClassicalImpCompleteness` (they mention no axiom). Note this reuse/transcribe split explicitly in each phase. |
| R4: `goal := φ` recovery interacts with real `⊥` in the fragment | L | L | No interaction: `goal` stays an abstract surrogate throughout the induction exactly as in 352/378; the real `⊥` only matters in the `bot` case where EFQ supplies `⊥ → goal`. Recovery is the unchanged `mp_deriv hKalmarTrue (weakening_deriv (…_imp_self φ) …)` pattern (`ClassicalImpCompleteness.lean:370-372`). |
| R5: `decide`/`aesop`/flexible `simp` shortcut on `Tautology`/`BoolEvaluate` (`Atom` not `Fintype`) | M | M | FORBIDDEN per task-352 anti-overflow contract; `simp only [...]` with explicit lemma lists only. `bot` TRUE-side discharge uses `simp only [BoolEvaluate_bot]`/`exact absurd … (by decide)` on the closed `Bool` literal, never on `Tautology`. |
| R6: lint/CI failures (docBlame, naming, barrel, shake, `Cslib.Init`) | L | M | Docstring on every decl; `theorem`/`lemma` for Prop-valued; lowerCamelCase; `import Cslib.Init`; full CI gate in the final phase; register the new file via `lake exe mk_all --module Cslib`. |

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

The chain 0→1→2→3→4→5→6 is strictly sequential (each phase appends to the single new module and
consumes the previous). Dispatch one phase per agent run; commit after each green phase with
`task 379 phase {P}: {name}`.

---

### Phase 0: Dependency gate + reuse/transcribe inventory [COMPLETED]

- **Goal:** Confirm tasks 377 and 378 are landed and CI-green; record the exact landed signatures this
  plan transcribes/reuses, resolving the names left abstract here.
- **Tasks:**
  - [ ] Verify `ClassicalConjImpBotAxiom`, `ClassicalConjImpBotAxiom.toPropAxiom`, and
        `classicalConjImpBotAxiom_hasDeductionTheorem` exist in
        `ProofSystem/FragmentAxioms.lean` (task 377). Record the **EFQ constructor** name/shape
        (resolves R2) and the ∧-axiom constructors (projection/pairing).
  - [ ] Verify task-378 module `Metalogic/ClassicalConjImpCompleteness.lean` exists with
        `classicalConjImp_kalmar` (the ∧-extended truth lemma) and its derived lemmas; record the
        exact `and`-case recipe and derived-lemma signatures to transcribe.
  - [ ] Confirm the axiom-independent reusables `Proposition.atoms`, `litCtx`, `litCtx_mem`,
        `litCtx_congr` are importable from `ClassicalImpCompleteness` (task 352) and mention no axiom.
  - [ ] Confirm `IsOrFree` (`FragmentPredicates.lean:46`), `BoolEvaluate_bot`, `BoolEvaluate_imp`,
        `BoolEvaluate_atom`, `tautology_iff_boolEvaluate_true`, `prop_soundness_tautology`,
        `mp_deriv`, `weakening_deriv`, `assumption_deriv`, `liftDerivationTree` are available.
  - [ ] If 377 OR 378 is not landed: STOP, mark this plan `[BLOCKED]` with which dependency is missing.
- **Timing:** ~20 min
- **Depends on:** none

---

### Phase 1: New module skeleton + soundness [COMPLETED]

- **Goal:** Create `Metalogic/ClassicalConjImpBotCompleteness.lean` with header, imports, namespace,
  and `classicalConjImpBot_soundness`.
- **Tasks:**
  - [ ] License header + `module` + `import Cslib.Init` + `public import` of
        `ProofSystem.FragmentAxioms`, `Metalogic.Soundness`, and the task-378 module
        `Metalogic.ClassicalConjImpCompleteness` (which transitively re-exports the 352 reusables).
  - [ ] Module docstring `# Completeness of the Classical ⟨∧,→,⊥,⊤⟩ Fragment CPL⟨∧,→,⊥,⊤⟩` modelled on
        `ClassicalImpCompleteness.lean:14-48`, noting the Kalmár method, the EFQ-driven `bot` case, and
        the reference to the 352/378 modules.
  - [ ] `@[expose] public section`, `namespace Cslib.Logic.PL`, `variable {Atom : Type*}`.
  - [ ] `classicalConjImpBot_soundness {φ} (h : Derivable ClassicalConjImpBotAxiom φ) : Tautology φ`
        via `prop_soundness_tautology ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩`
        (mirror `classicalImp_soundness`, `ClassicalImpCompleteness.lean:60-63`).
  - [ ] Scoped build green; `lean_verify` shows no `sorryAx`.
- **Timing:** ~25 min
- **Depends on:** 0

---

### Phase 2: Derived lemmas for `ClassicalConjImpBotAxiom` (incl. EFQ helper) [COMPLETED]

- **Goal:** Re-derive the axiom-set-specific helpers the truth lemma consumes, retargeted to
  `ClassicalConjImpBotAxiom`, plus the **new EFQ helper**.
- **Tasks:**
  - [ ] Transcribe (retargeting axiom constructors): `classicalConjImpBot_imp_self`,
        `classicalConjImpBot_imp_trans` (empty ctx), `classicalConjImpBot_imp_trans_ctx` (in-context,
        via DT + `mp_deriv` + `assumption_deriv`; see `ClassicalImpCompleteness.lean:140-148`),
        `classicalConjImpBot_weaken_ctx` (K-axiom + `mp_deriv`; `:151-154`), and
        `classicalConjImpBot_peirce_mp` (`:94-97`).
  - [ ] Transcribe the ∧-helper lemmas the 378 `and`-case consumes (projection/pairing combinators),
        retargeted to the bot axiom's ∧-constructors (names recorded in Phase 0).
  - [ ] **NEW** EFQ helper: `classicalConjImpBot_exfalso {Γ goal} : Deriv ClassicalConjImpBotAxiom Γ
        (Proposition.bot.imp goal) := ⟨.ax _ _ (<efq> goal)⟩` (constructor from Phase 0). Docstring:
        "Ex falso: the falsum axiom gives `Γ ⊢ ⊥ → φ` for any `φ`; consumed by the `bot` FALSE side of
        the truth lemma."
  - [ ] Reuse `Proposition.atoms`, `litCtx`, `litCtx_mem`, `litCtx_congr` **by import** (do not
        redefine — they are axiom-independent).
  - [ ] Each lemma ≤ ~8 lines; scoped build green per lemma via `lean_goal`; no `sorryAx`.
- **Timing:** ~45 min
- **Depends on:** 1

---

### Phase 3: The `IsOrFree` Kalmár truth lemma — atom/imp/and (transcribe) [COMPLETED]

- **Goal:** State `classicalConjImpBot_kalmar` over `IsOrFree` and discharge the four reused branches
  (atom TRUE/FALSE, imp TRUE/FALSE, and TRUE/FALSE, or-excluded), transcribing from 378.
- **Tasks:**
  - [ ] Signature (double-negation falsum-surrogate form, fixed abstract `goal`):
        ```lean
        theorem classicalConjImpBot_kalmar {v : BoolValuation Atom} {goal : PL.Proposition Atom}
            (as : List Atom) {φ : PL.Proposition Atom} (hOF : φ.IsOrFree = true)
            (hcov : ∀ p, p ∈ φ.atoms → p ∈ as) :
            (BoolEvaluate v φ = true  →
                Deriv ClassicalConjImpBotAxiom (litCtx v goal as) ((φ.imp goal).imp goal)) ∧
            (BoolEvaluate v φ = false →
                Deriv ClassicalConjImpBotAxiom (litCtx v goal as) (φ.imp goal)) := by
          revert hOF hcov; induction φ with …
        ```
  - [ ] `atom p` case: transcribe `ClassicalImpCompleteness.lean:172-189` (retarget axiom; `hcov`
        unfolds via `Proposition.atoms`, membership via `litCtx_mem`).
  - [ ] `imp a b` case (TRUE-true-consequent / TRUE-false-antecedent-Peirce / FALSE): transcribe
        `:193-273`, retargeting axiom constructors and using the Phase-2 `_ctx`/`peirce_mp` helpers.
        `IsOrFree` splits via `simp only [Proposition.IsOrFree, Bool.and_eq_true]` (same shape as
        `IsImpTopOnly`).
  - [ ] `and a b` case: transcribe the task-378 `and`-case recipe verbatim (retarget axiom; consume
        the Phase-2 ∧-helpers). (If 378 unlanded — R0 — reconstruct from projection/pairing axioms.)
  - [ ] `or a b _ _` case: excluded — `intro hOF _; simp [Proposition.IsOrFree] at hOF` (or-free
        forbids `or`; mirror the bot/and exclusions in `ClassicalImpCompleteness.lean:190-192`).
  - [ ] Leave the `bot` case as the only open goal (filled in Phase 4). Verify all other branches green
        with `lean_goal`.
- **Timing:** ~60 min
- **Depends on:** 2

---

### Phase 4: Truth lemma — the new `bot` case (easy increment) [COMPLETED]

- **Goal:** Discharge the single genuinely new branch of `classicalConjImpBot_kalmar`.
- **Tasks:**
  - [ ] `bot` case scaffold: `| bot => intro _ _; simp only [BoolEvaluate_bot]; constructor`.
  - [ ] **TRUE side** (vacuous): hypothesis is `BoolEvaluate v ⊥ = true`, i.e. `false = true` after
        `simp only [BoolEvaluate_bot]`; discharge by `intro hv; exact absurd hv (by decide)` (or
        `simp at hv`) — `⊥` is never true, so there is no real obligation.
  - [ ] **FALSE side** (immediate EFQ): goal is `Deriv ClassicalConjImpBotAxiom (litCtx v goal as)
        (Proposition.bot.imp goal)`; discharge by `intro _; exact classicalConjImpBot_exfalso`
        (the Phase-2 EFQ helper) — `⊥ → goal` is the falsum axiom instance.
  - [ ] Whole `classicalConjImpBot_kalmar` now closed; `lean_goal` shows "no goals"; `lean_verify
        Cslib.Logic.PL.classicalConjImpBot_kalmar` shows no `sorryAx`/unexpected axioms.
  - [ ] **[BLOCKED] fallback:** if any non-bot branch (Peirce/∧) proves intractable, mark this phase
        `[BLOCKED]` with the exact `lean_goal` stuck state and which conjunct/subcase; leave NO `sorry`.
- **Timing:** ~20 min
- **Depends on:** 3

---

### Phase 5: Atom elimination + collapse + `classicalConjImpBot_completeness` [COMPLETED]

- **Goal:** Iterate atom elimination over the literal context and conclude completeness.
- **Tasks:**
  - [ ] Transcribe `classicalConjImpBot_elim_atom` (DT-peel each branch + one `mp_deriv`; retarget
        axiom + 377 DT instance; `ClassicalImpCompleteness.lean:281-288`).
  - [ ] Transcribe `classicalConjImpBot_collapse` (induction on `as`, `Classical.em (p ∈ ps)`,
        `Function.update`, `litCtx_congr`, `classicalConjImpBot_elim_atom`; `:315-354`).
  - [ ] `classicalConjImpBot_completeness {φ} (hOF : φ.IsOrFree = true) (h : Tautology φ) : Derivable
        ClassicalConjImpBotAxiom φ`: `rw [tautology_iff_boolEvaluate_true] at h`; apply
        `classicalConjImpBot_collapse φ.atoms`; for each `v`, take the TRUE conjunct of
        `classicalConjImpBot_kalmar` at `goal := φ`, `mp_deriv` with the weakened
        `classicalConjImpBot_imp_self φ` to recover `Deriv (litCtx v φ φ.atoms) φ`
        (mirror `:364-372`).
  - [ ] Scoped build green; `lean_verify` on `classicalConjImpBot_completeness` shows no `sorryAx`.
- **Timing:** ~40 min
- **Depends on:** 4

---

### Phase 6: Conservativity edge + chain biconditional + CI gate [COMPLETED]

- **Goal:** Land the conservativity triple, extend the chain doc-edge, pass the full CI gate.
- **Tasks:**
  - [ ] `cpl_conservative_over_classicalConjImpBot {φ} (hOF : φ.IsOrFree = true)
        (h : Derivable PropositionalAxiom φ) : Derivable ClassicalConjImpBotAxiom φ :=
        classicalConjImpBot_completeness hOF (prop_soundness_tautology h)`
        (mirror `cpl_conservative_over_imp`, `:381-384`).
  - [ ] `derivablePropOfDerivableClassicalConjImpBot` (subsumption via `liftDerivationTree` +
        `toPropAxiom`; `:389-392`).
  - [ ] `classicalConjImpBot_iff_chain {φ} (hOF : φ.IsOrFree = true) :
        Derivable ClassicalConjImpBotAxiom φ ↔ Derivable PropositionalAxiom φ` (`:397-399`).
  - [ ] Extend `Semantics/Algebra/ConservativeChain.lean` doc table with the edge
        `CPL⟨∧,→,⊥,⊤⟩ ⊂ CPL` and re-export the subsumption (additive; do not edit existing edges).
        Note in a comment that the classical column is now 4-for-4 and the MPL/IPL/CPL towers are
        structurally symmetric.
  - [ ] Register the new module: `lake exe mk_all --module Cslib`.
  - [ ] Full CI gate (see Testing & Validation); fix any lint/shake/import/barrel issues.
- **Timing:** ~30 min
- **Depends on:** 5

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Metalogic.ClassicalConjImpBotCompleteness` — scoped build
      green after each of Phases 1–6.
- [ ] `lake build` — whole library compiles; no `sorry`/`axiom` introduced.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — new module imports `Cslib.Init`.
- [ ] `lake exe lint-style` — style clean (docstring on every decl, naming, line length).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports.
- [ ] `lake exe mk_all --module Cslib` — new module registered in the barrel.
- [ ] `lean_verify` on `classicalConjImpBot_kalmar`, `classicalConjImpBot_completeness`,
      `cpl_conservative_over_classicalConjImpBot` — no `sorryAx`, no unexpected axioms.
- [ ] Existing intuitionistic and classical chain edges in `ConservativeChain.lean` unchanged and
      still compile.
- [ ] No edits outside `Logics/Propositional/{Metalogic,Semantics/Algebra}`; task-352/378 modules
      imported, not modified.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpBotCompleteness.lean` — NEW module:
  `classicalConjImpBot_soundness`; derived helpers (`…_imp_self`, `…_imp_trans`, `…_imp_trans_ctx`,
  `…_weaken_ctx`, `…_peirce_mp`, ∧-helpers, **`…_exfalso`**); `classicalConjImpBot_kalmar` (atom/imp/and
  transcribed + new `bot` case); `classicalConjImpBot_elim_atom`, `classicalConjImpBot_collapse`,
  `classicalConjImpBot_completeness`; `cpl_conservative_over_classicalConjImpBot`,
  `derivablePropOfDerivableClassicalConjImpBot`, `classicalConjImpBot_iff_chain`.
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` — additive doc-edge
  `CPL⟨∧,→,⊥,⊤⟩ ⊂ CPL` + subsumption re-export.
- Barrel `Cslib.lean` updated via `mk_all`.
- `specs/379_cpl_conservative_over_classical_conjimpbot/summaries/01_classical-conjimpbot-conservativity-summary.md`
  (at completion).

## Rollback/Contingency

- All changes additive: a single new module plus a doc-edge/subsumption in `ConservativeChain.lean`.
  To revert: delete `Metalogic/ClassicalConjImpBotCompleteness.lean`, revert the `ConservativeChain.lean`
  additions, re-run `lake exe mk_all --module Cslib`. Existing chain edges and the 352/378 modules are
  never edited, so rollback cannot regress them.
- **Dependency-gate fallback (R0):** if 377 or 378 is not landed, mark the plan `[BLOCKED]` at Phase 0
  with the missing dependency named; do not stub axioms or recipes.
- **Zero-debt fallback (R1/R4):** if any truth-lemma branch is intractable within budget, mark the
  relevant phase `[BLOCKED]` with the exact `lean_goal` stuck state; leave NO `sorry`, NO `axiom`, NO
  vacuous placeholder. Earlier green phases remain committed, additive value.
- **Per-phase commits** mean a failure in any later phase loses at most that phase's in-progress work.
</content>
</invoke>
