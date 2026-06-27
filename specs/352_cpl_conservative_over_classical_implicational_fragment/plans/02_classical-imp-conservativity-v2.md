# Implementation Plan v2: Task #352 - CPL Conservative over Classical Implicational Fragment

- **Task**: 352 - Prove CPL is conservative over its classical implicational fragment CPL⟨→,⊤⟩
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours remaining (Phase 1 of ~7h already done)
- **Dependencies**: None (additive; coordinate footprint with running task 350)
- **Research Inputs**: specs/352_cpl_conservative_over_classical_implicational_fragment/reports/01_cpl-conservative-classical-implicational.md
- **Artifacts**: plans/02_classical-imp-conservativity-v2.md (this file); supersedes plans/01_classical-imp-conservativity.md (kept for history)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a **streamlining revision** of plan v1. The deliverable is unchanged: prove CPL is
conservative over its purely implicational fragment CPL⟨→,⊤⟩ (axiomatized K + S + Peirce) via the
**truth-assignment (Kalmár) route**, producing the one genuinely new theorem
`classicalImp_completeness` and the two-line conservativity corollary `cpl_conservative_over_imp`.

**Why v2 exists (concrete failure mode).** Two `cslib-implementation-agent` runs of v1 BOTH died on
token/context limits. Root causes, now designed out:
1. v1 concentrated risk in two large phases (truth lemma 2h, atom elimination 1.5h) executed in a
   single dispatch. Agents (a) *designed* the Kalmár proof live via repeated `lean_multi_attempt`
   proof-search storms, (b) re-read the growing module many times, (c) ballooned one file with heavy
   context bookkeeping.
2. v2 fixes this with **one lemma per phase**, **pre-stated exact Lean signatures** (transcribe, do
   not design), an explicit **List-context representation** that eliminates Finset bookkeeping, and
   an **anti-overflow tactics contract**.

**Already done — do NOT re-plan.** Phase 1 (the entire `ClassicalImpAxiom` fragment + plumbing in
`FragmentAxioms.lean`) is COMPLETED and committed (commit `14a7c447`). It is reproduced below for
reference only; it is marked `[COMPLETED]` and must not be touched.

### Research Integration

Report 01 is integrated in full (route decision, axiomatization, reuse map, proof structure §6).
This v2 additionally grounds **every** lemma signature against the real committed code, inspected
during revision:
- `ClassicalImpAxiom` block — `FragmentAxioms.lean:551-645` (committed): constructors `implyK`,
  `implyS`, `peirce`; `ImpAxiom.toClassicalImpAxiom`; `ClassicalImpAxiom.toPropAxiom`;
  `ClassicalImpAxiom.mem_implyK/mem_implyS`; `subst_preserves_classicalImpAxiom`;
  `classicalImpAxiom_{implyK,implyS,peirce}_isImpTopOnly`; `classicalImpAxiom_hasDeductionTheorem`.
- Proof context is a **`List`**, not a Finset — `DerivationTree`/`Deriv`/`Derivable` in
  `ProofSystem/Derivation.lean:68-129`; combinators `mp_deriv`, `weakening_deriv`,
  `assumption_deriv`. This is the single biggest simplification lever (directive #3).
- Deduction theorem interface — `HasDeductionTheorem D := ∀ {Γ φ ψ}, D.Deriv (φ :: Γ) ψ →
  D.Deriv Γ (φ.imp ψ)` (`Foundations/Logic/Metalogic/Consistency.lean:187-188`). The cons-peel
  direction is exactly what atom elimination needs.
- `Tautology`/`Evaluate`/`BoolEvaluate` — `Semantics/Bool.lean:57-90`; bridge
  `tautology_iff_boolEvaluate_true` (`Bool.lean:157`).
- `prop_soundness_tautology` — `Metalogic/Soundness.lean` (`Derivable PropositionalAxiom φ →
  Tautology φ`).
- `IsImpTopOnly` — `Semantics/Algebra/FragmentPredicates.lean:63-68`: `.atom ↦ true`, `.bot ↦
  false`, `.imp a b ↦ a.IsImpTopOnly && b.IsImpTopOnly`, `.and/.or ↦ false`. **Consequence: the
  Kalmár induction has only two live cases, `atom` and `imp`; `bot`, `and`, `or` are discharged by
  `simp [Proposition.IsImpTopOnly] at hITO`** (copy the idiom from `freeMeetEvaluateEq`,
  `ImpConservative.lean:77-85`).
- `liftDerivationTree` subsumption idiom — `ImpConservative.lean:135-140`
  (`derivableImpOfDerivableInt`), mirrored for the classical branch.
- `listToImp` exists (`SequentCalculus/LJ/Decidability.lean:71-73`) but is bound to `LJProof`
  (sequent calculus), NOT the Hilbert `Derivable`; it is a reusable *encoding pattern* only. We do
  NOT import it — the List context + cons-based deduction theorem make a separate encoding
  unnecessary (see Representation Decision).

### Prior Plan Reference

Supersedes plans/01_classical-imp-conservativity.md. v1's 5 coarse phases (1 done, 4 large) are
re-decomposed into 10 fine phases (1 done, 9 new), each independently committable.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path in delegation context). The task advances the propositional
conservativity chain to its classical branch.

## Goals & Non-Goals

**Goals**:
- Deliver `classicalImp_completeness : IsImpTopOnly φ → Tautology φ → Derivable ClassicalImpAxiom φ`
  (Kalmár / Tarski–Bernays) in a new `Metalogic/ClassicalImpCompleteness.lean`.
- Deliver `cpl_conservative_over_imp` (classical) + `classicalImpAxiom_iff_chain` biconditional.
- Extend `Semantics/Algebra/ConservativeChain.lean` with the classical-branch subsumption
  `derivablePropOfDerivableClassicalImp` and the doc-table edge `CPL⟨→,⊤⟩ ⊂ CPL`.
- Keep CI green: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`, `lake exe mk_all --module`.

**Non-Goals** (hard constraints preserved from v1):
- **Truth-assignment route only**: no `ImplicationAlgebra`/`TarskiAlgebra` typeclass, no
  Lindenbaum–Tarski construction, no Abbott embedding, no new Foundations math.
- **ZERO-DEBT**: no `sorry`, no new `axiom`, no vacuous definitions (`def X := True` etc.). If the
  Kalmár truth lemma (Phase 7) or Peirce case lemma (Phase 5) is intractable within budget, mark
  that phase `[BLOCKED]` with the exact stuck goal state — Phases 1–6 still land as CI-green
  additive value.
- **No edits outside** `Logics/Propositional/{ProofSystem,Metalogic,Semantics/Algebra}` (task 350
  owns Foundations/Logic/Metalogic and the deduction files — do not touch).
- New module placed at `Metalogic/ClassicalImpCompleteness.lean` (NOT `Semantics/Algebra/`, whose
  name presupposed the declined algebraic route).

## Dispatch Discipline (READ BEFORE IMPLEMENTING)

This section is the heart of the streamlining. **Every implementing agent MUST obey it.**

1. **One phase = one dispatch = one commit.** Each phase below adds exactly one declaration (or one
   small def + its helper). Implement only that phase's declaration, verify it green, commit
   immediately with `task 352 phase {P}: {name}`, and STOP. Do not start the next phase in the same
   dispatch.
2. **Append, do not re-read the whole file.** The new module grows by appending. Do NOT re-read the
   entire `ClassicalImpCompleteness.lean` on each dispatch. Read only: (a) this plan's signature for
   your phase, (b) the *last ~30 lines* of the module if you need the immediately-preceding lemma's
   exact name, and (c) the specific committed signatures cited in your phase. Trust the Edit tool's
   file-state tracking; do not re-read to verify after editing.
3. **Transcribe, do not design.** Every lemma's full Lean signature is pre-stated below. Type the
   signature verbatim, then prove it with the one-line recipe. Do NOT run `lean_multi_attempt`
   storms to *discover* the statement — the statement is given.
4. **Anti-overflow tactics contract (directive #4)**:
   - Prefer short structured/term-mode proofs. Keep each proof **≤ ~40 lines**.
   - Verify **one lemma at a time** with `lean_goal` at the proof's end; avoid blanket
     `lean_diagnostic_messages` (it hangs — see rules) and avoid `lake build` of the whole project
     mid-phase (use `lake build Cslib.Logics.Propositional.Metalogic.ClassicalImpCompleteness`).
   - **FORBIDDEN**: `decide`, `aesop`, or flexible `simp`-dumps on `Tautology`/`Evaluate` (`Atom` is
     not `Fintype`; the theorem is for arbitrary `Atom`). `simp only [...]` with explicit lemma
     lists is fine.
   - Cap `lean_multi_attempt` to a handful of *targeted* tactic probes per goal; if a goal resists
     after a few probes, fall back to the explicit `apply`/`exact` axiom-witness style.
5. **Reuse-first.** Before writing any helper, `lean_local_search` for it. The combinators
   `mp_deriv`, `weakening_deriv`, `assumption_deriv` and `classicalImpAxiom_hasDeductionTheorem`
   already exist — use them.

## Representation Decision (directive #3 — minimizes bookkeeping)

The Hilbert proof context is a `List (PL.Proposition Atom)` and the deduction theorem peels the
**head**: `D.Deriv (φ :: Γ) ψ → D.Deriv Γ (φ.imp ψ)`. We exploit this to avoid Finset membership
transport entirely.

**Chosen literal-context encoding** (define in Phase 6):

```lean
/-- The Kalmár literal context for a Boolean assignment `v` and falsum-surrogate `goal`,
keyed on a list of atoms `as`: atom `p` contributes `p` if `v p` else `p → goal`. -/
def litCtx (v : BoolValuation Atom) (goal : PL.Proposition Atom) :
    List Atom → List (PL.Proposition Atom)
  | [] => []
  | p :: ps => (if v p then PL.Proposition.atom p else (PL.Proposition.atom p).imp goal)
                :: litCtx v goal ps
```

Properties this buys us, all on `List` (no Finset):
- Membership of a literal is `List.Mem`, discharged by `assumption_deriv`/`List.Mem` simp.
- Atom elimination peels the **head** atom `p` via `classicalImpAxiom_hasDeductionTheorem` applied to
  the two branch derivations, then `mp_deriv` — see Phase 8/9. No `Finset.toList`, no `ctxToImp`,
  no `listToImp` import.
- The truth lemma carries `as` as an explicit list parameter; at the top level `as` is the atom list
  of `φ` (any list containing `φ`'s atoms works, by `weakening_deriv`).

Document this encoding once (Phase 6 docstring); downstream phases reference it rather than
re-deriving it.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: Kalmár truth lemma (Phase 7), specifically the `imp` case false-antecedent subcase, is the genuine difficulty | H | M | Isolated to ONE phase with the derived lemmas (Phases 3–5) and literal context (Phase 6) built and committed first; follow report §6 step-by-step; if intractable, mark Phase 7 `[BLOCKED]` with exact goal state — no sorry/axiom |
| R2: Peirce case lemma (Phase 5) is where classical strength enters; its exact statement may need adjustment | M | M | Pre-stated below as a guide; agent confirms the precise shape against the truth-lemma `imp` case it feeds; `[BLOCKED]` fallback if neither shape closes |
| R3: context overflow recurs | H (was the failure) | L (now) | Dispatch Discipline: one lemma/phase, append-only, pre-stated signatures, ≤40-line proofs, scoped builds |
| R4: Foundations Peirce lemmas assume ⊥/EFQ, not reusable | M | H (known) | Phases 3–5 build fresh negation-free derived lemmas; do NOT import ⊥-based Core/HilbertDerivedRules Peirce lemmas |
| R5: footprint conflict with task 350 | M | L | Strictly additive within Propositional/{ProofSystem,Metalogic,Semantics/Algebra} |
| R6: `decide`/`aesop` shortcut on `Tautology` | M | M | Forbidden (anti-overflow contract); `Tautology` only decidable for `Fintype Atom` |
| R7: lint/CI failures (docstrings, naming, barrel, shake) | L | M | Docstrings on every decl; `theorem`/`lemma` for Prop-valued; lowerCamelCase; `import Cslib.Init`; full CI gate in Phase 10 |

## Implementation Phases

**Dependency Analysis (revised wave table for the finer split)**:

| Wave | Phases | Blocked by | Parallelizable within wave |
|------|--------|------------|----------------------------|
| 0 | 1 | -- | done (committed) |
| 1 | 2, 3 | 1 | yes (soundness ⟂ identity; both depend only on the new module skeleton) |
| 2 | 4 | 3 | -- (imp_trans uses identity/K/S) |
| 3 | 5 | 4 | -- (Peirce case lemma) |
| 4 | 6 | 1 | (litCtx def; depends only on fragment, could run in wave 1, but kept here for module ordering) |
| 5 | 7 | 5, 6 | -- (truth lemma; risk-concentrated) |
| 6 | 8 | 7 | -- (single-atom elimination) |
| 7 | 9 | 8 | -- (iterate + completeness) |
| 8 | 10 | 9 | -- (conservativity + chain + CI gate) |

Practical guidance: dispatch one phase at a time in the order 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9 → 10.
Phases 2 and 3 are genuinely independent and may be dispatched in parallel if desired, but each is
small enough that serial dispatch is fine.

---

### Phase 1: Define ClassicalImpAxiom fragment and plumbing [COMPLETED]

**Committed in `14a7c447`** (`FragmentAxioms.lean:551-645`). Reproduced for reference; do NOT
modify. Provides:
- `inductive ClassicalImpAxiom` with `| implyK φ ψ`, `| implyS φ ψ χ`, `| peirce φ ψ`.
- `theorem ImpAxiom.toClassicalImpAxiom (h : ImpAxiom φ) : ClassicalImpAxiom φ`.
- `theorem ClassicalImpAxiom.toPropAxiom (h : ClassicalImpAxiom φ) : PropositionalAxiom φ`.
- `theorem ClassicalImpAxiom.mem_implyK : ∀ (φ ψ), ClassicalImpAxiom (φ.imp (ψ.imp φ))`.
- `theorem ClassicalImpAxiom.mem_implyS : ∀ (φ ψ χ), ClassicalImpAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))`.
- `theorem subst_preserves_classicalImpAxiom (h : ClassicalImpAxiom φ) (f) : ClassicalImpAxiom (φ.subst f)`.
- `classicalImpAxiom_{implyK,implyS,peirce}_isImpTopOnly`.
- `theorem classicalImpAxiom_hasDeductionTheorem : Metalogic.HasDeductionTheorem (propDerivationSystem (@ClassicalImpAxiom Atom))`.

**Status**: done. No work in this phase.

---

### Phase 2: New module skeleton + soundness [COMPLETED]

**Goal**: Create the module and prove the (easy) soundness direction.

**File (new)**: `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean`.
Header: `import Cslib.Init`, plus imports for `FragmentAxioms`, `Semantics/Bool`,
`Metalogic/Soundness`, `ProofSystem/Derivation`. Module docstring. `namespace Cslib.Logic.PL`,
`open Cslib.Logic`, `variable {Atom : Type*}`.

**Single declaration**:
```lean
/-- Soundness for the classical implicational fragment: every `ClassicalImpAxiom`-derivable
formula is a tautology. Routes through `ClassicalImpAxiom.toPropAxiom` and CPL soundness. -/
theorem classicalImp_soundness {φ : PL.Proposition Atom}
    (h : Derivable ClassicalImpAxiom φ) : Tautology φ := by
  obtain ⟨d⟩ := h
  exact prop_soundness_tautology ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩
```
**Recipe**: lift the `ClassicalImpAxiom` derivation tree to a `PropositionalAxiom` one via
`liftDerivationTree` + `ClassicalImpAxiom.toPropAxiom` (pattern: `ImpConservative.lean:135-140`),
then apply `prop_soundness_tautology`. **If** `liftDerivationTree` is not in scope from the imports,
prove directly by `induction d` mirroring `prop_soundness` — but try the lift first.
**Expected size**: ≤ 8 lines.

**Then**: register in barrel `lake exe mk_all --module Cslib`; scoped build green.

**Depends on**: 1. **Verification**: module builds; `lean_verify` shows no `sorryAx`.

---

### Phase 3: Derived lemma — identity `⊢ φ → φ` [NOT STARTED]

**Goal**: The implicational identity over `ClassicalImpAxiom`, the first Hilbert derived rule.

**Single declaration** (state the most convenient of the two forms; prefer the empty-context form):
```lean
/-- Identity: `⊢ φ → φ` in the classical implicational fragment (standard `S K K` derivation). -/
theorem classicalImp_imp_self (φ : PL.Proposition Atom) :
    Derivable ClassicalImpAxiom (φ.imp φ) := by
  sorry -- replace: S K K derivation
```
**Recipe**: classic `⊢ (φ → ((φ→φ) → φ)) → ((φ → (φ→φ)) → (φ → φ))` (S with ψ:=φ→φ, χ:=φ) applied to
K (`⊢ φ → ((φ→φ) → φ)`) and K (`⊢ φ → (φ→φ)`), via `mp_deriv`. Build the three axiom leaves with
`⟨.ax [] _ (.implyS ..)⟩`, `⟨.ax [] _ (.implyK ..)⟩` (constructors from Phase 1), then two
`mp_deriv`. **Expected size**: ~10–15 lines. Verify with `lean_goal`; remove the `sorry`.

**Depends on**: 2. **Verification**: green; no `sorryAx`.

---

### Phase 4: Derived lemma — composition / `imp_trans` [NOT STARTED]

**Goal**: Hypothetical-syllogism style composition, used by the truth lemma's `imp` case.

**Single declaration** (hypothetical form is easiest to consume under the deduction theorem):
```lean
/-- Composition: from `⊢ φ → ψ` and `⊢ ψ → χ` derive `⊢ φ → χ`. -/
theorem classicalImp_imp_trans {φ ψ χ : PL.Proposition Atom}
    (h₁ : Derivable ClassicalImpAxiom (φ.imp ψ))
    (h₂ : Derivable ClassicalImpAxiom (ψ.imp χ)) :
    Derivable ClassicalImpAxiom (φ.imp χ) := by
  sorry
```
**Recipe**: Use `classicalImpAxiom_hasDeductionTheorem`. Work in context `[φ]`: `assumption_deriv`
gives `[φ] ⊢ φ`; weaken `h₁, h₂` to context `[φ]` with `weakening_deriv`; two `mp_deriv` give
`[φ] ⊢ χ`; then `classicalImpAxiom_hasDeductionTheorem` (the `(φ :: Γ) → imp` peel) yields `⊢ φ → χ`.
Alternatively the pure `S`/`K` term proof; pick whichever is shorter. **Expected size**: ~12–20
lines. (Optional sibling, only if Phase 7 needs it: the "prefix-weakening" lemma
`⊢ ψ → (φ → ψ)`-driven `Derivable ... ψ → Derivable ... (φ.imp ψ)` via K + MP — add it here as a
second tiny lemma if and only if Phase 7's recipe references it.)

**Depends on**: 3. **Verification**: green; no `sorryAx`.

---

### Phase 5: Derived lemma — Peirce-driven classical case lemma [NOT STARTED]

**Goal**: The lemma where classical strength (Peirce) enters. This feeds the truth lemma's `imp`
case false-antecedent subcase and/or the atom-elimination collapse. **Risk-bearing**: confirm the
exact shape against the consumer in Phase 7/8 before finalizing.

**Candidate declaration** (guide — adjust the precise shape to match the consumer; keep it a single
lemma):
```lean
/-- Classical case lemma (Peirce): from `Γ ⊢ (φ → goal) → φ` derive `Γ ⊢ φ`. Direct use of the
`peirce` axiom + modus ponens; this is the only place Peirce's law is invoked. -/
theorem classicalImp_peirce_mp {Γ : List (PL.Proposition Atom)} {φ goal : PL.Proposition Atom}
    (h : Deriv ClassicalImpAxiom Γ (((φ.imp goal).imp φ).imp φ → φ)) -- shape TBD vs consumer
    : Deriv ClassicalImpAxiom Γ φ := by
  sorry
```
**Recipe**: the `peirce` axiom instance is `⟨.ax Γ _ (.peirce φ goal)⟩ : Deriv _ Γ (((φ.imp
goal).imp φ).imp φ)`; combine with the hypothesis via `mp_deriv`. **Before writing**: peek at the
Phase 7 `imp`/false-antecedent recipe and the Phase 8 elimination recipe and state THIS lemma in
exactly the form they consume (the report §6 step 2/4 "Peirce-driven case lemma"). Keep it ≤ ~25
lines.
**[BLOCKED] fallback**: if no clean single-lemma shape closes the consumer goals, record the exact
goal states and mark `[BLOCKED]` — do not sorry.

**Depends on**: 4. **Verification**: green; no `sorryAx`.

---

### Phase 6: Literal-context definition `litCtx` + membership helper [NOT STARTED]

**Goal**: Define the List-based Kalmár literal context (see Representation Decision) and the one
helper the truth lemma needs.

**Declarations**:
```lean
/-- (See Representation Decision in the plan.) -/
def litCtx (v : BoolValuation Atom) (goal : PL.Proposition Atom) :
    List Atom → List (PL.Proposition Atom)
  | [] => []
  | p :: ps => (if v p then PL.Proposition.atom p else (PL.Proposition.atom p).imp goal)
                :: litCtx v goal ps

/-- Each literal of `litCtx` is derivable-by-assumption from the context. (Membership helper:
the atom `p`'s literal sits in `litCtx v goal as` when `p ∈ as`.) -/
theorem litCtx_mem {v : BoolValuation Atom} {goal : PL.Proposition Atom} {as : List Atom}
    {p : Atom} (hp : p ∈ as) :
    (if v p then PL.Proposition.atom p else (PL.Proposition.atom p).imp goal)
      ∈ litCtx v goal as := by
  sorry
```
**Recipe**: `litCtx` is a plain structural `def` (no proof). `litCtx_mem` by `induction as` +
`simp [litCtx]` on the cons/`List.mem_cons` cases. **Expected size**: def ~5 lines, helper ~10
lines. State only the helper(s) the truth lemma actually consumes — if Phase 7's recipe uses a
direct `assumption_deriv` with an inline membership proof, this helper may be folded in; keep this
phase to the `def` plus at most one helper.

**Depends on**: 1 (only the fragment). **Verification**: green.

---

### Phase 7: Kalmár truth lemma [NOT STARTED] — RISK-CONCENTRATED

**Goal**: The core lemma, by induction on imp-top-only `φ`, relative to a Boolean assignment `v`,
an atom list `as` covering `φ`'s atoms, and a fixed falsum-surrogate `goal`.

**Single declaration**:
```lean
/-- Kalmár truth lemma (falsum-surrogate form). For imp-top-only `φ`, under the literal context
`litCtx v goal as` (with `as` covering the atoms of `φ`): if `v ⊨ φ` then the context derives `φ`;
otherwise it derives `φ → goal`. Proved by induction on `φ`; only `atom` and `imp` cases are live
(`bot`/`and`/`or` are excluded by `IsImpTopOnly`). Peirce enters via `classicalImp_peirce_mp`
(Phase 5). -/
theorem classicalImp_kalmar {v : BoolValuation Atom} {goal : PL.Proposition Atom}
    (as : List Atom) {φ : PL.Proposition Atom} (hITO : φ.IsImpTopOnly = true)
    (hcov : ∀ p, p ∈ φ.atoms → p ∈ as) :  -- `φ.atoms` : adjust to the actual atom-collector name; see note
    (BoolEvaluate v φ = true → Deriv ClassicalImpAxiom (litCtx v goal as) φ) ∧
    (BoolEvaluate v φ = false → Deriv ClassicalImpAxiom (litCtx v goal as) (φ.imp goal)) := by
  sorry
```
**Note on `φ.atoms`/`hcov`**: locate the existing atom-collector for `PL.Proposition` with
`lean_local_search` (candidates: `Proposition.atoms`, `Proposition.vars`). If none exists, the
cleanest alternative is to drop `as`/`hcov` and quantify the context over *all* atoms is impossible
(infinite); instead keep `as` and require `hcov` only for the atoms appearing in `φ`. If no
collector exists, define a tiny `Proposition.atoms : Proposition Atom → List Atom` as a sibling in
Phase 6 (add it there, not here). Confirm the exact form before transcribing.

**Per-case recipe** (follow report §6 step 3; FORBIDDEN to bypass with `decide`/`aesop`):
- `induction φ` with cases `atom/bot/imp/and/or`. Discharge `bot`, `and`, `or` immediately:
  `simp [Proposition.IsImpTopOnly] at hITO` (copy `freeMeetEvaluateEq`, `ImpConservative.lean:79,84,85`).
- **`atom p`**: split on `v p`. If `true`: `BoolEvaluate` is `true`; the literal is `atom p ∈
  litCtx` (`litCtx_mem` / `assumption_deriv`). If `false`: `BoolEvaluate` is `false`; the literal is
  `(atom p).imp goal`, giving the right conjunct by `assumption_deriv`. ~10–15 lines.
- **`imp a b`** (`hITO` gives `a.IsImpTopOnly ∧ b.IsImpTopOnly` via `Bool.and_eq_true`): split on
  `BoolEvaluate v a`, `BoolEvaluate v b`. Three combinations make `a→b` true (use `classicalImp_imp_trans`
  / K-weakening from Phase 4), one makes it false (`v⊨a`, `v⊭b`: combine IH `… ⊢ a` and IH `… ⊢ b→goal`
  to get `… ⊢ (a→b)→goal`). The subtle true-subcase `v⊭a` is where `classicalImp_peirce_mp` (Phase 5)
  is invoked. **This is the hard step**: if it stalls, re-read report §6 and the Phase-5 lemma shape
  before declaring blocked. ~25–35 lines.

**Anti-overflow**: keep the whole proof ≤ ~50 lines; verify each case branch with `lean_goal` once;
do NOT proof-search the whole lemma with `lean_multi_attempt`.

**[BLOCKED] fallback**: if the `imp` true/false-antecedent subcase is intractable within budget,
mark `[BLOCKED]` with the precise stuck goal state recorded in the plan + metadata; leave NO sorry,
NO axiom. Phases 8–10 then also block; Phases 1–6 remain committed value.

**Depends on**: 5, 6. **Verification**: `sorry`-free; `lean_verify` no unexpected axioms.

---

### Phase 8: Single-atom elimination step [NOT STARTED]

**Goal**: Eliminate one atom from the front of the literal context, collapsing the two Boolean
branches for that atom.

**Single declaration**:
```lean
/-- Atom elimination (one step): if the context with `p` true derives `goal` and the context with
`p` false (i.e. with `p → goal`) derives `goal`, then the shorter context derives `goal`. -/
theorem classicalImp_elim_atom {goal : PL.Proposition Atom}
    {Γ : List (PL.Proposition Atom)} {p : Atom}
    (hT : Deriv ClassicalImpAxiom (PL.Proposition.atom p :: Γ) goal)
    (hF : Deriv ClassicalImpAxiom ((PL.Proposition.atom p).imp goal :: Γ) goal) :
    Deriv ClassicalImpAxiom Γ goal := by
  sorry
```
**Recipe**: apply `classicalImpAxiom_hasDeductionTheorem` to `hT` (peel `atom p`) → `Γ ⊢ (atom p) →
goal`; apply it to `hF` (peel `(atom p).imp goal`) → `Γ ⊢ ((atom p) → goal) → goal`; then `mp_deriv`
gives `Γ ⊢ goal`. **Note**: `classicalImpAxiom_hasDeductionTheorem` has type
`HasDeductionTheorem (propDerivationSystem ClassicalImpAxiom)`, i.e. `∀ {Γ φ ψ}, (…).Deriv (φ::Γ) ψ
→ (…).Deriv Γ (φ.imp ψ)`; unfold `propDerivationSystem`/`Deriv` if needed (see
`DeductionTheorem.lean:205`). If this collapse turns out to need Peirce (it may, depending on the
truth-lemma form), route through `classicalImp_peirce_mp` (Phase 5) — confirm which. **Expected
size**: ~12–20 lines.

**Depends on**: 7. **Verification**: green; no `sorryAx`.

---

### Phase 9: Iterate elimination + `classicalImp_completeness` [NOT STARTED]

**Goal**: Iterate `classicalImp_elim_atom` over the atom list to discharge the whole context, then
conclude completeness.

**Declarations** (one helper by induction on `as` + the headline theorem):
```lean
/-- Collapse the full literal context: if for every Boolean assignment the context derives `goal`,
then the empty context derives `goal`. By induction on the atom list `as`, using
`classicalImp_elim_atom` at each step. -/
theorem classicalImp_collapse {goal : PL.Proposition Atom} (as : List Atom)
    (h : ∀ v : BoolValuation Atom, Deriv ClassicalImpAxiom (litCtx v goal as) goal) :
    Derivable ClassicalImpAxiom goal := by
  sorry

/-- **The new theorem.** K + S + Peirce is complete for classical implicational tautologies
(Tarski–Bernays). -/
theorem classicalImp_completeness {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) (h : Tautology φ) :
    Derivable ClassicalImpAxiom φ := by
  sorry
```
**Recipe (`classicalImp_collapse`)**: `induction as`. Base `[]`: `litCtx v goal [] = []`, so `h v`
is already `Deriv … [] goal = Derivable … goal` (pick any `v`). Cons `p :: ps`: instantiate `h` at
the two assignments that agree off `p` and differ on `p` (use `Function.update`), feed the two
branches to `classicalImp_elim_atom`, then to the IH. Watch the `if v p` reduction in `litCtx`
(`simp [litCtx]` with the updated valuation). ~20–30 lines.
**Recipe (`classicalImp_completeness`)**: take `as := φ.atoms` (or the collector from Phase 7); from
`h : Tautology φ` get `∀ v, BoolEvaluate v φ = true` via `tautology_iff_boolEvaluate_true`; for each
`v`, the left conjunct of `classicalImp_kalmar` (with `goal := φ`) gives `Deriv … (litCtx v φ as)
φ`; apply `classicalImp_collapse` with `goal := φ`. ~12–18 lines.

**Depends on**: 8. **Verification**: `sorry`-free; `lean_verify Cslib.Logic.PL.classicalImp_completeness`
shows no `sorryAx`.

---

### Phase 10: Conservativity, chain extension, CI gate [NOT STARTED]

**Goal**: The short conservativity corollary, the biconditional, the chain subsumption + doc edge,
and the full CI gate.

**Declarations (in the new module)**:
```lean
/-- **Classical conservativity**: CPL is conservative over CPL⟨→,⊤⟩ for imp-top-only formulas. -/
theorem cpl_conservative_over_imp {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) (h : Derivable PropositionalAxiom φ) :
    Derivable ClassicalImpAxiom φ :=
  classicalImp_completeness hITO (prop_soundness_tautology h)

/-- **Subsumption (easy direction)**: every `ClassicalImpAxiom`-derivable formula is
`PropositionalAxiom`-derivable. -/
theorem derivablePropOfDerivableClassicalImp {φ : PL.Proposition Atom}
    (h : Derivable ClassicalImpAxiom φ) : Derivable PropositionalAxiom φ := by
  obtain ⟨d⟩ := h
  exact ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩

/-- **Biconditional**: for imp-top-only formulas, classical-implicational and full CPL derivability
coincide. -/
theorem classicalImpAxiom_iff_chain {φ : PL.Proposition Atom} (hITO : φ.IsImpTopOnly = true) :
    Derivable ClassicalImpAxiom φ ↔ Derivable PropositionalAxiom φ :=
  ⟨derivablePropOfDerivableClassicalImp, cpl_conservative_over_imp hITO⟩
```
**Then** in `Semantics/Algebra/ConservativeChain.lean` (additive): place
`derivablePropOfDerivableClassicalImp` (or re-export it) and extend the chain doc table with the
classical-branch edge `CPL⟨→,⊤⟩ ⊂ CPL`. Mirror the existing `derivableImpOfDerivableInt` /
biconditional pattern (`ImpConservative.lean:135-149`). Keep additions minimal; do not edit existing
chain theorems.

**Then** run the full CI gate (Testing & Validation). Fix lint/shake/import/barrel issues.

**Expected size**: corollary 2 lines, subsumption ~4 lines, biconditional 2 lines, chain doc ~5
lines + 1 subsumption decl.

**Depends on**: 9. **Verification**: full CI gate green; existing chain unchanged.

---

## Testing & Validation

- [ ] `lake build` — whole library compiles; no `sorry`/`axiom` introduced.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — new module imports `Cslib.Init`.
- [ ] `lake exe lint-style` — style clean (docstrings, naming, line length).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports.
- [ ] `lake exe mk_all --module Cslib` — new module registered in barrel.
- [ ] Existing intuitionistic chain in `ConservativeChain.lean` unchanged and still compiles.
- [ ] `lean_verify` on `classicalImp_completeness` and `cpl_conservative_over_imp` — no `sorryAx`.
- [ ] No edits outside `Logics/Propositional/{ProofSystem,Metalogic,Semantics/Algebra}`.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` — new module:
  `classicalImp_soundness`, `classicalImp_imp_self`, `classicalImp_imp_trans`,
  `classicalImp_peirce_mp`, `litCtx` (+ `litCtx_mem`), `classicalImp_kalmar`,
  `classicalImp_elim_atom`, `classicalImp_collapse`, `classicalImp_completeness`,
  `cpl_conservative_over_imp`, `derivablePropOfDerivableClassicalImp`, `classicalImpAxiom_iff_chain`.
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` — classical-branch
  subsumption + doc-table edge `CPL⟨→,⊤⟩ ⊂ CPL`.
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — Phase 1 block (already committed).
- Barrel updated via `mk_all`.
- `specs/352_cpl_conservative_over_classical_implicational_fragment/summaries/02_classical-imp-conservativity-summary.md`
  (at completion).

## Rollback/Contingency

- All changes additive and confined to the new module + `ConservativeChain.lean` doc/subsumption +
  the already-committed `FragmentAxioms.lean` block. To revert post-Phase-1 work: delete
  `Metalogic/ClassicalImpCompleteness.lean`, revert the `ConservativeChain.lean` additions, re-run
  `lake exe mk_all --module Cslib`. The existing chain is never edited, so rollback cannot regress
  it.
- **Zero-debt fallback** (R1/R2): if Phase 5 (Peirce case lemma) or Phase 7 (Kalmár truth lemma) is
  intractable within budget, mark that phase `[BLOCKED]` with the exact stuck goal state recorded,
  leave NO `sorry` and NO `axiom`, and surface for user review. Phases 1–6 (fragment + soundness +
  identity + composition + literal context) still land as self-contained, CI-green, additive value.
- **Per-phase commits** mean a context-overflow death in any later phase loses at most that one
  phase's in-progress work; all prior phases are already committed.
</content>
</invoke>
