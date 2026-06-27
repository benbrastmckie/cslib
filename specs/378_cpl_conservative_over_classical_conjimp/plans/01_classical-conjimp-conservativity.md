# Implementation Plan: Task #378 - CPL Conservative over Classical Conjunction-Implication Fragment CPL⟨∧,→,⊤⟩

- **Task**: 378 - Prove CPL is conservative over its classical conjunction-implication fragment CPL⟨∧,→,⊤⟩ (CL-B rung)
- **Status**: [NOT STARTED]
- **Effort**: ~5 hours
- **Dependencies**: Task 377 (the `ClassicalConjImpAxiom` system: `implyK`, `implyS`, `peirce`, `andI`, `andE1`, `andE2`, plus `ClassicalConjImpAxiom.toPropAxiom`, `classicalConjImpAxiom_hasDeductionTheorem`, `mem_implyK`/`mem_implyS`, `subst_preserves_*`). Task 377 must be landed/CI-green before Phase 1.
- **Research Inputs**: None (no research report; grounded directly in the task-352 template and the source files listed under Standards).
- **Artifacts**: plans/01_classical-conjimp-conservativity.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prove that the full classical propositional calculus (CPL) is conservative over its classical
conjunction-implication fragment CPL⟨∧,→,⊤⟩ — axiomatized by K, S, Peirce, andI, andE1, andE2 —
for or-bot-free formulas. The deliverable theorem is

```lean
classicalConjImp_completeness : φ.IsOrBotFree = true → Tautology φ → Derivable ClassicalConjImpAxiom φ
```

together with the conservativity edge `cpl_conservative_over_classicalConjImp` and the chain
biconditional `classicalConjImp_iff_chain`.

Completeness is proved by the **Kalmár / Tarski–Bernays truth-assignment method**, EXTENDING the
landed `classicalImp_kalmar` truth lemma (in
`Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean`, task 352) with a new
**conjunction (`and`) case**. The falsum-surrogate / double-negation encoding carries over verbatim:
under a fixed abstract surrogate `goal`, "`φ` true" is the double negation `(φ → goal) → goal` and
"`φ` false" is `φ → goal`. The work is a structural mirror of task 352's now-complete module, plus
the genuinely new `and` truth-table subcases (the risk-concentrated content).

**Definition of done**: `classicalConjImp_completeness`, `cpl_conservative_over_classicalConjImp`,
`classicalConjImp_iff_chain` land in a new module `ClassicalConjImpCompleteness.lean` with zero debt
(no `sorry`, no new `axiom`, no vacuous definitions) and the full CSLib CI gate green.

### Research Integration

No research report exists. The plan is grounded in four read sources:
- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` (task 352, FULLY LANDED) —
  the direct line-by-line template: `classicalImp_soundness`, `classicalImp_imp_self`,
  `classicalImp_imp_trans`, `classicalImp_peirce_mp`, `Proposition.atoms`, `litCtx`, `litCtx_mem`,
  `classicalImp_imp_trans_ctx`, `classicalImp_weaken_ctx`, `classicalImp_kalmar`,
  `classicalImp_elim_atom`, `litCtx_congr`, `classicalImp_collapse`, `classicalImp_completeness`,
  `cpl_conservative_over_imp`, `derivablePropOfDerivableClassicalImp`, `classicalImpAxiom_iff_chain`.
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — the `ConjImpAxiom` block (lines
  59–74) supplies the exact `andI`/`andE1`/`andE2` shapes; task 377 mirrors these into
  `ClassicalConjImpAxiom` and adds `peirce`.
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` — `IsOrBotFree` (atom→true,
  bot→false, imp→both, and→both, or→false) and its closure/subsumption lemmas
  (`imp_isOrBotFree`, `and_isOrBotFree`, `subst_preserves_isOrBotFree`,
  `IsImpTopOnly_implies_IsOrBotFree`).
- `Cslib/Logics/Propositional/Semantics/Bool.lean` — `BoolEvaluate_and` (line 106):
  `BoolEvaluate v (a.and b) = (BoolEvaluate v a && BoolEvaluate v b)` (so `a∧b` is true iff both
  conjuncts are true). `BoolEvaluate_imp`, `BoolEvaluate_atom` likewise.

### Prior Plan Reference

No prior plan for task 378. The plan deliberately mirrors task 352's
`plans/03_classical-imp-conservativity-v3.md` phase structure (truth lemma → elimination → collapse
→ completeness → conservativity), which proved correct and CI-green, calibrating effort and risk from
that experience. The `and` case is the additive new content; everything else is mechanical
transcription with `ClassicalImpAxiom → ClassicalConjImpAxiom` and `IsImpTopOnly → IsOrBotFree`
substitutions.

### Roadmap Alignment

No `roadmap_flag` was set and no ROADMAP.md consultation was requested. This task is the CL-B rung
("classical column" middle) of the propositional conservativity chain — it sits directly above the
task-352 implicational result and below the Glivenko/CPL top. No ROADMAP.md edits are in scope.

## Goals & Non-Goals

**Goals**:
- Land `classicalConjImp_kalmar`: the `IsOrBotFree`-indexed double-negation truth lemma over the
  classical conjunction-implication fragment, with live `atom`, `imp`, and **`and`** cases (the
  `imp` case transcribed from the landed `classicalImp_kalmar`; the `and` case NEW).
- Land the supporting mirror: `classicalConjImp_soundness`, in-context derived helpers, a new atom
  collector covering `and`, `classicalConjImp_elim_atom`, `classicalConjImp_collapse`.
- Deliver `classicalConjImp_completeness : φ.IsOrBotFree = true → Tautology φ → Derivable ClassicalConjImpAxiom φ`.
- Deliver `cpl_conservative_over_classicalConjImp`, `derivablePropOfDerivableClassicalConjImp`, and
  the biconditional `classicalConjImp_iff_chain`.
- Keep CI green: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`, barrel registration, naming/docBlame.

**Non-Goals** (hard constraints):
- **Truth-assignment route ONLY.** Do NOT use an algebraic free-completion / Lindenbaum–Tarski /
  Heyting / Brouwerian-completion route. Classical fragments are NOT Heyting/Brouwerian-complete —
  **Peirce's law is invalid in free Heyting completions**, so a Diego/free-algebra approach cannot
  prove this. The proof MUST extend `classicalImp_kalmar` with an `and` case. (See R1.)
- **ZERO-DEBT**: no `sorry`, no new `axiom`, no vacuous definitions (`def X := True`, `:= trivial`,
  `:= Unit`, etc.). If the `and`-extended truth lemma is intractable within budget, mark the phase
  `[BLOCKED]` with the exact stuck goal state — never `sorry`.
- **Strictly propositional, additive scope.** New code lives in the new module
  `Metalogic/ClassicalConjImpCompleteness.lean`. Do NOT edit task-352's
  `ClassicalImpCompleteness.lean` (reuse its public decls by import). Do NOT edit existing chain
  theorems.
- No new semantics, no new typeclasses.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **R1: the `and`-case Kalmár induction is the genuine (medium-high) difficulty** | H | M | The `and` TRUE subcase needs a nested deduction-theorem construction (`H::Γ ⊢ a→(b→goal)` via `andI`, then discharge the two double-negation IHs) with deep `List.mem_cons` context-index bookkeeping; the `and` FALSE subcase composes `andE1`/`andE2` with an IH-FALSE. Both are worked out in the §`and`-case discharge table below. **HARD CONSTRAINT**: truth-assignment method only — NO algebraic free-completion (Peirce invalid in free Heyting completions). Build each subcase incrementally with `lean_goal`, factor the `and` case into a private helper if context budget is tight. **If still intractable within budget, mark Phase 2 `[BLOCKED]` with the precise `lean_goal` output (which conjunct/subcase, the intermediate goal); leave NO `sorry`, NO `axiom`.** |
| R2: existing `Proposition.atoms` returns `[]` for `and` (it only recurses `atom`/`imp`) — reusing it would under-cover conjunction atoms and break completeness | H | H (certain) | Define a NEW atom collector in the new module that recurses into `and` (e.g. `Proposition.atomsConjImp`, `and a b => a.atomsConjImp ++ b.atomsConjImp`). Use it (not `Proposition.atoms`) in `classicalConjImp_completeness` and as the `hcov` target in `classicalConjImp_kalmar`. `litCtx`/`litCtx_mem` are generic over `as : List Atom`, so they work unchanged with the new collector's output. |
| R3: `litCtx_congr` is `private` in task-352's module → not importable | M | M | Re-derive a local `private lemma litCtx_congr` in the new module (5-line copy; pure list/proposition induction, axiom-independent). `litCtx` and `litCtx_mem` ARE public — reuse by import. |
| R4: task 377 (`ClassicalConjImpAxiom`) not landed or missing a needed decl (e.g. `classicalConjImpAxiom_hasDeductionTheorem`, `toPropAxiom`, the `peirce`/`andI`/`andE1`/`andE2` constructors) | H | L | Phase 1 begins by confirming task 377's exports compile (a scoped `lake build` of `FragmentAxioms`). If any required decl is absent, STOP and surface as a dependency gap (do not work around with local axioms). Required decls: constructors `implyK`/`implyS`/`peirce`/`andI`/`andE1`/`andE2`; `ClassicalConjImpAxiom.toPropAxiom`; `classicalConjImpAxiom_hasDeductionTheorem : HasDeductionTheorem (propDerivationSystem ClassicalConjImpAxiom)`. |
| R5: context overflow in the verbose `imp`+`and` truth-lemma cases (the landed `imp` case alone is ~80 lines of nested `assumption_deriv (List.mem_cons...)`) | H | M | One phase = one dispatch = one commit. Transcribe the `imp` case verbatim from the landed `classicalImp_kalmar` (swap axiom name only); develop the `and` case separately and factor it into a private helper if needed. Verify one subcase at a time with `lean_goal`. Use scoped builds `lake build Cslib.Logics.Propositional.Metalogic.ClassicalConjImpCompleteness`. |
| R6: `decide`/`aesop`/flexible `simp` shortcut on `Tautology`/`BoolEvaluate` (`Atom` not `Fintype`) | M | M | FORBIDDEN. `simp only [...]` with explicit lemma lists (`BoolEvaluate_and`, `BoolEvaluate_imp`, `Bool.and_eq_true`, `Bool.not_*`) is fine, mirroring the landed proof. |
| R7: lint/CI failures (docBlame, naming, line length, barrel, shake) | L | M | Docstring every decl; `theorem`/`lemma` for Prop-valued; lowerCamelCase; `import Cslib.Init`; register in barrel via `mk_all`; full CI gate in Phase 5. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- (requires task 377 landed) |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

The work is strictly sequential (each phase consumes the previous phase's declarations). Dispatch one
phase per agent run; commit immediately on green with `task 378 phase {P}: {name}`.

---

### Phase 1: Module scaffolding, soundness, derived helpers, atom collector [NOT STARTED]

**Goal**: Stand up `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` with all
the non-truth-lemma scaffolding mirrored from task 352, plus the `and`-aware atom collector. This is
mechanical transcription (low risk) and must be solid before the truth lemma.

**Tasks**:
- [ ] Confirm task 377 exports compile: scoped `lake build` of `Cslib.Logics.Propositional.ProofSystem.FragmentAxioms`; verify constructors `implyK`/`implyS`/`peirce`/`andI`/`andE1`/`andE2`, `ClassicalConjImpAxiom.toPropAxiom`, and `classicalConjImpAxiom_hasDeductionTheorem` exist (R4). If any is missing, STOP and surface the dependency gap.
- [ ] Create the module: copyright header, `module`, `import Cslib.Init`, `public import` of `ProofSystem.FragmentAxioms`, `Metalogic.Soundness`, `Metalogic.ClassicalImpCompleteness` (to reuse `litCtx`, `litCtx_mem`), and `Semantics.Algebra.ConjImpConservative` if needed for soundness plumbing; `@[expose] public section`; `namespace Cslib.Logic.PL`; `variable {Atom : Type*}`. Module docstring describing the CL-B completeness strategy.
- [ ] `classicalConjImp_soundness {φ} (h : Derivable ClassicalConjImpAxiom φ) : Tautology φ` — mirror `classicalImp_soundness` exactly, routing through `ClassicalConjImpAxiom.toPropAxiom` and `prop_soundness_tautology`.
- [ ] Derived lemmas (mirror, swap axiom name): `classicalConjImp_imp_self`, `classicalConjImp_imp_trans`, `classicalConjImp_peirce_mp`.
- [ ] In-context helpers (mirror): `classicalConjImp_imp_trans_ctx`, `classicalConjImp_weaken_ctx`.
- [ ] NEW atom collector covering `and`: `Proposition.atomsConjImp : Proposition Atom → List Atom` with `atom p => [p]`, `imp a b => a.atomsConjImp ++ b.atomsConjImp`, `and a b => a.atomsConjImp ++ b.atomsConjImp`, `_ => []`. Docstring (R2).
- [ ] `private lemma litCtx_congr` — local copy from task 352 (axiom-independent; `litCtx` is reused by import) (R3).
- [ ] Verify: scoped build green; `lean_verify` shows no `sorryAx`/unexpected axioms on the new decls.

**Timing**: ~1 hour

**Depends on**: none (within this plan; gated by task 377 being landed)

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` (NEW) — all decls above.

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.ClassicalConjImpCompleteness` green.
- Every new decl has a docstring; no `sorry`/`axiom`.

---

### Phase 2: ∧-extended Kalmár truth lemma (RISK-CONCENTRATED) [NOT STARTED]

**Goal**: Land `classicalConjImp_kalmar`, the falsum-surrogate / double-negation truth lemma over
`IsOrBotFree` formulas, with live `atom`, `imp`, and **`and`** cases. The `atom` and `imp` cases are
transcribed verbatim from the landed `classicalImp_kalmar` (axiom-name swap only). The `and` case is
NEW and is the genuine difficulty of the task.

**Target signature** (note: `IsOrBotFree` replaces `IsImpTopOnly`; `atomsConjImp` replaces `atoms`):

```lean
theorem classicalConjImp_kalmar {v : BoolValuation Atom} {goal : PL.Proposition Atom}
    (as : List Atom) {φ : PL.Proposition Atom} (hOBF : φ.IsOrBotFree = true)
    (hcov : ∀ p, p ∈ φ.atomsConjImp → p ∈ as) :
    (BoolEvaluate v φ = true →
        Deriv ClassicalConjImpAxiom (litCtx v goal as) ((φ.imp goal).imp goal)) ∧
    (BoolEvaluate v φ = false →
        Deriv ClassicalConjImpAxiom (litCtx v goal as) (φ.imp goal)) := by
  revert hOBF hcov
  induction φ with
  | atom p => ...        -- verbatim from classicalImp_kalmar (axiom swap)
  | imp a b iha ihb => ...-- verbatim from classicalImp_kalmar (axiom swap); Peirce confined here
  | and a b iha ihb => ...-- NEW (see discharge table)
  | bot => intro hOBF _; simp [Proposition.IsOrBotFree] at hOBF
  | or a b _ _ => intro hOBF _; simp [Proposition.IsOrBotFree] at hOBF
```

`IsOrBotFree` excludes `bot` and `or` (both discharged by `simp [Proposition.IsOrBotFree] at hOBF`);
it admits `atom`, `imp`, AND `and`. `goal`, `v`, `as` are fixed across the induction; only
`hOBF`/`hcov` are reverted and reintroduced per case. `litCtx`/`litCtx_mem` reused by import.

**Tasks**:
- [ ] Transcribe the `atom` case verbatim from the landed `classicalImp_kalmar` (swap `Proposition.atoms`→`atomsConjImp` in the `hcov` simp; swap `classicalImpAxiom_hasDeductionTheorem`→`classicalConjImpAxiom_hasDeductionTheorem`). Verify with `lean_goal`.
- [ ] Transcribe the `imp` case verbatim (swap axiom name; the helpers `classicalConjImp_imp_trans_ctx`, `classicalConjImp_peirce_mp`, the `.implyK`/`.peirce` constructors are the Phase-1 ConjImp analogs). Peirce remains confined to the `imp` TRUE false-antecedent subcase. Verify with `lean_goal`.
- [ ] NEW `and` case, using `BoolEvaluate_and` (`a∧b` true iff both true). Split TRUE/FALSE, then split on `BoolEvaluate v a`. Implement per the discharge table below; verify each subcase with `lean_goal`. Factor into a `private` helper if context budget is tight.
- [ ] Discharge `bot` and `or` with `simp [Proposition.IsOrBotFree] at hOBF`.
- [ ] `lean_verify Cslib.Logic.PL.classicalConjImp_kalmar` — no `sorryAx`, no unexpected axioms.

**`and`-case discharge table** (analogous to task 352 §F4). Let `Γ := litCtx v goal as`; "DT" =
`classicalConjImpAxiom_hasDeductionTheorem` (peels head: `Deriv (φ::Γ) ψ → Deriv Γ (φ.imp ψ)`).
IHs: `iha`/`ihb` each split into TRUE conjunct (double negation `(x→goal)→goal`) and FALSE conjunct
(`x→goal`). **No Peirce is needed in either `and` subcase** — Peirce stays confined to the `imp`
case.

| Subcase | `v`-condition | Conclusion | Discharge recipe |
|---------|---------------|------------|------------------|
| `and a b` TRUE | `v a = true ∧ v b = true` (`BoolEvaluate v (a∧b) = true`) | `Γ ⊢ ((a∧b)→goal)→goal` | IHa-TRUE `Γ⊢(a→goal)→goal`, IHb-TRUE `Γ⊢(b→goal)→goal`. DT introduce `H := (a∧b)→goal`. (i) Build `H::Γ ⊢ a→(b→goal)`: from `andI a b : a→(b→(a∧b))` compose with `H` (under `a` then `b`: `andI` gives `a∧b`, `H` gives `goal`) — nested DT / `classicalConjImp_imp_trans_ctx`. (ii) Build `H::Γ ⊢ a→goal`: DT introduce `a`; from `a→(b→goal)` + assumption `a` get `b→goal`; apply IHb-TRUE (weakened) to get `goal`; DT peels `a`. (iii) Apply IHa-TRUE (weakened) to `a→goal` ⟹ `goal`. DT peels `H` ⟹ conclusion. |
| `and a b` FALSE, **left false** | `v a = false` (`BoolEvaluate v (a∧b) = false`) | `Γ ⊢ (a∧b)→goal` | IHa-FALSE `Γ⊢a→goal`. Compose `andE1 a b : (a∧b)→a` with `a→goal` via `classicalConjImp_imp_trans` (empty-ctx) or `classicalConjImp_imp_trans_ctx` ⟹ `(a∧b)→goal`. |
| `and a b` FALSE, **right false** | `v a = true ∧ v b = false` | `Γ ⊢ (a∧b)→goal` | IHb-FALSE `Γ⊢b→goal`. Compose `andE2 a b : (a∧b)→b` with `b→goal` via `classicalConjImp_imp_trans_ctx` ⟹ `(a∧b)→goal`. |

**Splitting guidance**: after `simp only [BoolEvaluate_and]`, the TRUE goal hypothesis is
`(BoolEvaluate v a && BoolEvaluate v b) = true` and the FALSE one is `... = false`. `cases hva :
BoolEvaluate v a`: in the TRUE branch, `hva = false` is impossible (`Bool.false_and` ⟹ `true = ...`
contradiction), and `hva = true` forces `v b = true` (`Bool.true_and`); in the FALSE branch,
`hva = false` uses the left-false recipe (andE1), `hva = true` forces `v b = false` (right-false,
andE2). `Bool.and_eq_true`/`Bool.and_eq_false_iff` (or explicit `Bool.true_and`/`Bool.false_and`)
drive the splits. `Proposition.IsOrBotFree (a.and b) = a.IsOrBotFree && b.IsOrBotFree` gives
`hOBFa`/`hOBFb` via `Bool.and_eq_true`; `hcova`/`hcovb` follow from
`(a.and b).atomsConjImp = a.atomsConjImp ++ b.atomsConjImp` and `List.mem_append`.

**Implementer order**: prove `atom` (verbatim), then the `and` FALSE subcases (andE1/andE2 — the
easiest), then `imp` (verbatim), then the `and` TRUE subcase (the nested-DT construction — hardest);
verify the TRUE subcase's intermediate `H::Γ ⊢ a→(b→goal)` and `H::Γ ⊢ a→goal` goals with `lean_goal`
before chaining. Estimated `and` case ≈ 40–60 lines; whole truth lemma ≈ 130–160 lines (the `imp`
case alone is ~80). Factor the `and` case into a private helper
`classicalConjImp_kalmar_and` if the combined proof strains context.

**[BLOCKED] fallback**: if the `and` TRUE nested-DT subcase is intractable within budget, mark this
phase `[BLOCKED]` with the precise stuck goal state recorded (exact `lean_goal` output, which
subcase, the intermediate goal). Leave NO `sorry`, NO `axiom`, NO vacuous placeholder. Phases 3–5
then also block; Phase 1 remains committed additive value.

**Timing**: ~2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` — add
  `classicalConjImp_kalmar` (and optional private `classicalConjImp_kalmar_and`).

**Verification**:
- Scoped build green; `lean_verify` on `classicalConjImp_kalmar` shows no `sorryAx`.

---

### Phase 3: Atom elimination and context collapse [NOT STARTED]

**Goal**: Mirror the task-352 atom-elimination and context-collapse lemmas for
`ClassicalConjImpAxiom`. Mechanical transcription (the proofs are axiom-name swaps of landed code;
they do not depend on the truth-lemma conclusion shape).

**Tasks**:
- [ ] `classicalConjImp_elim_atom {goal Γ p} (hT : Deriv … (atom p :: Γ) goal) (hF : Deriv … ((atom p).imp goal :: Γ) goal) : Deriv … Γ goal` — mirror `classicalImp_elim_atom` (two DT peels + one `mp_deriv`).
- [ ] `classicalConjImp_collapse (as) (h : ∀ v, Deriv … (litCtx v goal as) goal) : Derivable ClassicalConjImpAxiom goal` — mirror `classicalImp_collapse` (induction on `as`, `Classical.em (p ∈ ps)`, `Function.update`, the local `litCtx_congr`, `classicalConjImp_elim_atom`).
- [ ] Verify scoped build; `lean_verify` clean.

**Timing**: ~0.75 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` — add the two lemmas.

**Verification**:
- Scoped build green; no `sorryAx`.

---

### Phase 4: Completeness, conservativity edge, chain biconditional [NOT STARTED]

**Goal**: Assemble the deliverables from the truth lemma + collapse, then the conservativity edge and
chain biconditional. Mirror task 352's Phases 9–10 (recovery step + conservativity), using
`atomsConjImp` and `IsOrBotFree`.

**Tasks**:
- [ ] `classicalConjImp_completeness {φ} (hOBF : φ.IsOrBotFree = true) (h : Tautology φ) : Derivable ClassicalConjImpAxiom φ` — `rw [tautology_iff_boolEvaluate_true] at h`; `apply classicalConjImp_collapse φ.atomsConjImp`; `intro v`; take the TRUE conjunct of `classicalConjImp_kalmar` at `goal := φ` (coverage `fun p hp => hp`) to get `Deriv (litCtx v φ φ.atomsConjImp) ((φ→φ)→φ)`; recover `Deriv … φ` by `mp_deriv hkalT (weakening_deriv (classicalConjImp_imp_self φ) (… List.not_mem_nil))`.
- [ ] `cpl_conservative_over_classicalConjImp {φ} (hOBF : φ.IsOrBotFree = true) (h : Derivable PropositionalAxiom φ) : Derivable ClassicalConjImpAxiom φ` := `classicalConjImp_completeness hOBF (prop_soundness_tautology h)` — mirror `cpl_conservative_over_imp`.
- [ ] `derivablePropOfDerivableClassicalConjImp {φ} (h : Derivable ClassicalConjImpAxiom φ) : Derivable PropositionalAxiom φ` — `obtain ⟨d⟩ := h; exact ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩`.
- [ ] `classicalConjImp_iff_chain {φ} (hOBF : φ.IsOrBotFree = true) : Derivable ClassicalConjImpAxiom φ ↔ Derivable PropositionalAxiom φ` := `⟨derivablePropOfDerivableClassicalConjImp, cpl_conservative_over_classicalConjImp hOBF⟩`.
- [ ] Verify scoped build; `lean_verify` on `classicalConjImp_completeness` and `cpl_conservative_over_classicalConjImp` shows no `sorryAx`.

**Timing**: ~0.5 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` — add the four decls.

**Verification**:
- Scoped build green; target theorems `sorryAx`-free.

---

### Phase 5: CI gate [NOT STARTED]

**Goal**: Register the new module in the barrel and pass the full CSLib CI pipeline.

**Tasks**:
- [ ] `lake exe mk_all --module Cslib` — register `ClassicalConjImpCompleteness` in the `Cslib.lean` barrel.
- [ ] `lake build` — whole library compiles; no `sorry`/`axiom` introduced anywhere.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — new module imports `Cslib.Init`.
- [ ] `lake exe lint-style` — style clean (docstrings on every decl, lowerCamelCase, line length); `--fix` then re-check if needed.
- [ ] `lake lint` — environment linters (docBlame etc.) clean.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports (or `--fix`).
- [ ] Confirm no edits leaked outside the new module (task-352 `ClassicalImpCompleteness.lean` and existing chain theorems unchanged).

**Timing**: ~0.5 hour

**Depends on**: 4

**Files to modify**:
- `Cslib.lean` (barrel; via `mk_all`).

**Verification**:
- Full CI gate green; `git diff` confined to the new module + barrel.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Metalogic.ClassicalConjImpCompleteness` — scoped build green after each of Phases 1–4.
- [ ] `lake build` — whole library compiles; no `sorry`/`axiom` introduced.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — new module imports `Cslib.Init`.
- [ ] `lake exe lint-style` and `lake lint` — style/environment linters clean.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports.
- [ ] `lake exe mk_all --module Cslib` — new module registered in the barrel.
- [ ] `lean_verify` on `classicalConjImp_kalmar`, `classicalConjImp_completeness`, `cpl_conservative_over_classicalConjImp` — no `sorryAx`, no unexpected axioms.
- [ ] No edits outside `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` and the barrel.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` (NEW) — containing:
  `classicalConjImp_soundness`, `classicalConjImp_imp_self`, `classicalConjImp_imp_trans`,
  `classicalConjImp_peirce_mp`, `classicalConjImp_imp_trans_ctx`, `classicalConjImp_weaken_ctx`,
  `Proposition.atomsConjImp`, `private litCtx_congr`, `classicalConjImp_kalmar`
  (optional private `classicalConjImp_kalmar_and`), `classicalConjImp_elim_atom`,
  `classicalConjImp_collapse`, `classicalConjImp_completeness`,
  `cpl_conservative_over_classicalConjImp`, `derivablePropOfDerivableClassicalConjImp`,
  `classicalConjImp_iff_chain`. (`litCtx`/`litCtx_mem` reused by import from task 352.)
- `Cslib.lean` — barrel updated via `mk_all`.
- `specs/378_cpl_conservative_over_classical_conjimp/summaries/01_classical-conjimp-conservativity-summary.md` (at completion).

## Rollback/Contingency

- All changes are additive and confined to the new module + the barrel entry. To revert: delete
  `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` and re-run
  `lake exe mk_all --module Cslib`. Task-352's module and the existing chain are never edited, so
  rollback cannot regress them.
- **Zero-debt fallback (R1)**: if the `and`-extended truth lemma (specifically the `and` TRUE
  nested-DT subcase) is intractable within budget, mark Phase 2 `[BLOCKED]` with the exact stuck goal
  state recorded; leave NO `sorry` and NO `axiom`; surface for user review. Phase 1 remains
  self-contained, CI-green, additive value.
- **Per-phase commits** mean a context-overflow death in any later phase loses at most that phase's
  in-progress work; all prior phases are already committed.
- **Dependency gap (R4)**: if task 377 is not landed or missing a required decl, Phase 1 STOPs and
  the task surfaces as blocked-on-377 (no local-axiom workaround).
