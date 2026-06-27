# Implementation Plan v3: Task #352 - CPL Conservative over Classical Implicational Fragment

- **Task**: 352 - Prove CPL is conservative over its classical implicational fragment CPL⟨→,⊤⟩
- **Status**: [IN PROGRESS]
- **Effort**: ~3.5 hours remaining (Phases 1–6 landed and committed; Phases 7–10 outstanding)
- **Dependencies**: None (additive; coordinate footprint with running task 350)
- **Research Inputs**:
  - specs/352_cpl_conservative_over_classical_implicational_fragment/reports/01_cpl-conservative-classical-implicational.md
  - specs/352_cpl_conservative_over_classical_implicational_fragment/reports/02_corrected-kalmar-truth-lemma.md
- **Artifacts**: plans/03_classical-imp-conservativity-v3.md (this file); supersedes plans/02_classical-imp-conservativity-v2.md and plans/01_classical-imp-conservativity.md (kept for history)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib

## Overview

This is a **correction revision** of plan v2. The deliverable is unchanged: prove CPL is
conservative over its purely implicational fragment CPL⟨→,⊤⟩ (axiomatized K + S + Peirce) via the
**truth-assignment (Kalmár / Tarski–Bernays) route**, producing the one genuinely new theorem
`classicalImp_completeness` and the conservativity corollary `cpl_conservative_over_imp`.

**Why v3 exists (the corrected Phase 7).** v2 executed Phases 1–6 successfully (all committed and
CI-green in `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean`, which currently
ends at `litCtx_mem`, line 132). v2 **Phase 7 (Kalmár truth lemma) reached [BLOCKED]**: the truth
lemma's TRUE-side conclusion `litCtx v goal as ⊢ φ` is **semantically invalid** (recorded
countermodel below), so it is underivable in any sound system.

**The correction is the SHAPE OF THE CONCLUSION, not the quantification of `goal`** (report 02,
§F1–F5). An earlier draft of this v3 proposed varying the surrogate (`goal := a.imp b`) plus a
`litCtx_goal_congr` context-equality helper; **research 02 proved that approach cannot work** — for
*every* choice of `goal`, `litCtx v goal as ⊨ φ` is invalid, so no goal-variation and no
context-equality lemma can rescue the `⊢ φ` conclusion. That entire approach (and the
`litCtx_goal_congr` helper, which neither exists nor is needed) is **dropped**.

The correct truth lemma uses the **double-negation / falsum-surrogate encoding** (Kuroda/Glivenko
negative translation specialised to the →-fragment): with `goal` playing the role of ⊥, "`φ` true"
is encoded as `¬¬φ = (φ → goal) → goal` and "`φ` false" as `¬φ = φ → goal`. The TRUE branch
concludes the **double negation `(φ → goal) → goal`** (not `φ`); the FALSE branch keeps `φ → goal`.
The surrogate `goal` is a **fixed abstract parameter, never varied**; both inductive hypotheses for
`a` and `b` use the **same context** `litCtx v goal as`. No context bridge, no generalized-`goal` IH.
Peirce's law is provably required and isolated to exactly one subcase (the `imp a b` TRUE-side with a
false antecedent).

### Recorded countermodel (why the v2 `⊢ φ` conclusion was false, and why the fix is valid)

> φ = `(atom p).imp (atom q)`, `v p = v q = false` (so `v ⊨ φ`), `goal = atom r`, `as = [p,q]`.
> Literal context `Γ = litCtx v r [p,q] = [(atom p).imp (atom r), (atom q).imp (atom r)]` = `[p→r, q→r]`.
> The v2 TRUE branch claimed `Γ ⊢ (atom p).imp (atom q)`, but the model `w = (p:T, q:F, r:T)`
> satisfies `Γ` (`p→r = T`, `q→r = T`) yet falsifies `p→q` — so `Γ ⊭ p→q` and the conclusion is
> underivable for ANY `goal`.
> Under the **corrected** TRUE conclusion, `Γ ⊢ ((p→q) → r) → r`, which IS a semantic consequence of
> `Γ` (report 02, §F2): the countermodel no longer applies because the conclusion is the double
> negation, valid for every surrogate.

### Research Integration

- Report 01 (`reports/01_…`) remains integrated in full (route decision §3, K+S+Peirce
  axiomatization §2, reuse map §4, proof structure §6).
- **Report 02 (`reports/02_corrected-kalmar-truth-lemma.md`) is the authoritative correction source
  for Phase 7.** It supplies: the proof that the `⊢ φ` conclusion is invalid for all `goal` (§F1);
  the corrected double-negation statement with semantic validity proven for every `goal` (§F2); the
  exact Lean signature (§F3); the per-case discharge table (§F4); the proof that Peirce is required
  and isolated to one subcase (§F5); downstream impact on Phases 8–9 (§F6); and the two in-context
  micro-helpers (§F7). The literature-fidelity constraint is reinforced — the double-negation form is
  the *standard* falsum-surrogate device (arXiv 2305.05035, 1512.00091, 1511.02953), not a deviation.

### Prior Plan Reference

Supersedes plans/02_classical-imp-conservativity-v2.md. v2's 10-phase decomposition is preserved:
Phases 1–6 are landed code (`[COMPLETED]`, reproduced for reference only — do NOT re-do), Phase 7 is
**corrected per report 02** (the substantive change in v3, plus two NEW in-context helper lemmas),
Phase 9 gains a one-line recovery step, and Phases 8 and 10 are carried forward `[NOT STARTED]`
unchanged.

## Goals & Non-Goals

**Goals**:
- Land the corrected `classicalImp_kalmar` with the **double-negation TRUE-side conclusion** and a
  fixed abstract surrogate `goal` (Phase 7) — the one genuinely hard lemma.
- Land two NEW in-context derived helpers (`classicalImp_imp_trans_ctx`, `classicalImp_weaken_ctx`)
  the truth lemma consumes (the landed empty-context `classicalImp_imp_trans` is unusable inside a
  `litCtx` context).
- Deliver `classicalImp_completeness : IsImpTopOnly φ → Tautology φ → Derivable ClassicalImpAxiom φ`
  via single-atom elimination + iteration (Phases 8–9).
- Deliver `cpl_conservative_over_imp` + the `classicalImpAxiom_iff_chain` biconditional + chain
  subsumption, and pass the full CI gate (Phase 10).
- Keep CI green: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`, naming/docBlame.

**Non-Goals** (hard constraints preserved from v1/v2):
- **Truth-assignment route only**: no `ImplicationAlgebra`/`TarskiAlgebra` typeclass, no
  Lindenbaum–Tarski construction, no Abbott embedding, no new Foundations math.
- **ZERO-DEBT**: no `sorry`, no new `axiom`, no vacuous definitions (`def X := True`, `:= trivial`,
  `:= Unit`, etc.). If the corrected Phase 7 is still intractable within budget, mark it `[BLOCKED]`
  with the exact stuck goal state — Phases 1–6 remain CI-green additive value.
- **Strictly propositional scope.** No edits outside
  `Logics/Propositional/{ProofSystem,Metalogic,Semantics/Algebra}` (task 350 owns
  `Foundations/Logic/Metalogic` and the deduction files — do not touch).
- New completeness work stays in `Metalogic/ClassicalImpCompleteness.lean` (NOT `Semantics/Algebra/`).

## Dispatch Discipline (READ BEFORE IMPLEMENTING)

Carried forward from v2 — every implementing agent MUST obey it.

1. **One phase = one dispatch = one commit.** Phases 7–10 each add their declarations, verify green,
   commit immediately with `task 352 phase {P}: {name}`, and STOP.
2. **Append, do not re-read the whole file.** The module grows by appending after `litCtx_mem`
   (current line 132). Read only: (a) this plan's signature for your phase, (b) the *last ~30 lines*
   of the module if you need the immediately-preceding lemma's exact name, (c) the specific committed
   signatures cited in your phase. Trust the Edit tool's file-state tracking; do not re-read to
   verify after editing.
3. **Transcribe, do not design.** Phase 7's corrected signature, helper signatures, and per-case
   recipe table are pre-stated (report 02 §F3, §F4, §F7). Type the signatures, then prove with the
   recipe. Do NOT run `lean_multi_attempt` storms to *rediscover* the statement.
4. **Anti-overflow tactics contract**:
   - Prefer short structured/term-mode proofs. Keep the Phase-7 truth lemma **≤ ~55–70 lines** (report
     02 §Recommendations notes ~55–70 lines is realistic; the two helpers are ≤6 lines each); all
     other proofs ≤ ~40 lines. If the `imp` case is tight on context budget, factor it into a private
     helper.
   - Verify **one lemma/case at a time** with `lean_goal` at the proof's end. Do NOT call
     `lean_diagnostic_messages` (hangs). Use scoped builds:
     `lake build Cslib.Logics.Propositional.Metalogic.ClassicalImpCompleteness`.
   - **FORBIDDEN**: `decide`, `aesop`, or flexible `simp`-dumps on `Tautology`/`Evaluate`/`BoolEvaluate`
     (`Atom` is not `Fintype`). `simp only [...]` with explicit lemma lists is fine.
   - Cap `lean_multi_attempt` to a handful of *targeted* probes per goal; otherwise fall back to
     explicit `apply`/`exact` axiom-witness style.
5. **Reuse-first.** The combinators `mp_deriv`, `weakening_deriv`, `assumption_deriv` and
   `classicalImpAxiom_hasDeductionTheorem` ("DT") already exist — use them. Phases 3–5 derived lemmas
   (`classicalImp_imp_self`, `classicalImp_imp_trans`, `classicalImp_peirce_mp`) are landed — call
   them. `litCtx`, `litCtx_mem`, and `classicalImp_peirce_mp` are **unchanged** (report 02 §D3).

## Representation Decision (the List literal context — landed in Phase 6, UNCHANGED)

The Hilbert proof context is a `List (PL.Proposition Atom)`; the deduction theorem peels the
**head**: `D.Deriv (φ :: Γ) ψ → D.Deriv Γ (φ.imp ψ)`. The landed `litCtx` (file lines 114–118) and
`litCtx_mem` (lines 121–132) are **correct and unchanged**:

```lean
def litCtx (v : BoolValuation Atom) (goal : PL.Proposition Atom) :
    List Atom → List (PL.Proposition Atom)
  | [] => []
  | p :: ps => (if v p then PL.Proposition.atom p else (PL.Proposition.atom p).imp goal)
                :: litCtx v goal ps
```

Under the falsum-surrogate reading, the false-atom literal `(atom p).imp goal` is exactly `¬p`
relative to the surrogate `goal`. **`litCtx_mem` is the only membership helper needed.** Because the
corrected truth lemma keeps `goal` fixed throughout the induction, the literal context never changes
between the `φ`, `a`, and `b` nodes — there is **no context bridge, no surrogate-swap, and no
`litCtx_goal_congr` helper** (the v2 blocker's "context-equality lemma" does not exist and is
dropped; report 02 §D2).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: Kalmár truth lemma (Phase 7) is the genuine difficulty — **now resolved by the double-negation conclusion shape** | H | M | The v2 block is RESOLVED by changing the TRUE-side conclusion to the double negation `(φ → goal) → goal` (Kuroda/Glivenko negative translation; report 02 §F2 proves BOTH branches semantically valid for EVERY `goal`). `goal` stays fixed/abstract; no goal-variation, no context bridge. The recorded countermodel (Γ entails `((p→q)→r)→r` but NOT `p→q`) is exactly why the old `⊢ φ` conclusion failed and the new one succeeds. If still intractable within budget, mark `[BLOCKED]` with exact goal state — no sorry/axiom |
| R2: Peirce subcase nests two DT introductions (`H := (a→b)→goal`, then `K' := goal→(a→b)`) | M | M | Build the intermediate `Γ,H ⊢ (goal→(a→b))→goal` as a `have`, check with `lean_goal`, then a single `classicalImp_peirce_mp` (φ := goal, goal-slot := a→b) + DT (report 02 §R2, §F4). Peirce is required and confined to this one subcase (report 02 §F5) — Phase 5's `classicalImp_peirce_mp` needs NO change |
| R3: omitting the in-context helpers forces verbose inlining / overflow | M | M | Land the two NEW micro-helpers (`classicalImp_imp_trans_ctx`, `classicalImp_weaken_ctx`, ≤6 lines each, report 02 §F7) FIRST, at the head of Phase 7 |
| R4: context overflow recurs | H (original failure) | L | Dispatch Discipline: one lemma/phase, append-only, pre-stated signatures, scoped builds, ≤55–70-line Phase-7 proof (factor `imp` case into a private helper if tight) |
| R5: footprint conflict with task 350 | M | L | Strictly additive within Propositional/{ProofSystem,Metalogic,Semantics/Algebra} |
| R6: `decide`/`aesop` shortcut on `Tautology` | M | M | Forbidden (anti-overflow contract); `Tautology` only decidable for `Fintype Atom` |
| R7: lint/CI failures (docstrings, naming, barrel, shake) | L | M | Docstrings on every decl; `theorem`/`lemma` for Prop-valued; lowerCamelCase; `import Cslib.Init`; full CI gate in Phase 10 |

## Implementation Phases

**Dependency Analysis (wave table)**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 0 | 1, 2, 3, 4, 5, 6 | -- (all landed/committed) |
| 1 | 7 | 6 (in-context helpers + corrected Kalmár truth lemma) |
| 2 | 8 | 7 (single-atom elimination) |
| 3 | 9 | 8 (iterate + completeness) |
| 4 | 10 | 9 (conservativity + chain + CI gate) |

The live work (7→8→9→10) is strictly sequential. Dispatch one phase at a time.

---

### Phase 1: Define ClassicalImpAxiom fragment and plumbing [COMPLETED]

**Committed in `14a7c447`** (`FragmentAxioms.lean:551-645`). Reproduced for reference; do NOT
modify. Provides: `inductive ClassicalImpAxiom` (`| implyK φ ψ`, `| implyS φ ψ χ`, `| peirce φ ψ`);
`ImpAxiom.toClassicalImpAxiom`; `ClassicalImpAxiom.toPropAxiom`; `ClassicalImpAxiom.mem_implyK`/
`mem_implyS`; `subst_preserves_classicalImpAxiom`; `classicalImpAxiom_{implyK,implyS,peirce}_isImpTopOnly`;
`classicalImpAxiom_hasDeductionTheorem : HasDeductionTheorem (propDerivationSystem ClassicalImpAxiom)`.

- **Depends on:** none. **Status**: done. No work in this phase.

---

### Phase 2: New module skeleton + soundness [COMPLETED]

**Landed** (lines 1–63): module header, `namespace Cslib.Logic.PL`, `variable {Atom : Type*}`, and:

```lean
theorem classicalImp_soundness {φ : PL.Proposition Atom}
    (h : Derivable ClassicalImpAxiom φ) : Tautology φ := by
  obtain ⟨d⟩ := h
  exact prop_soundness_tautology ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩
```

- **Depends on:** 1. **Status**: done; no `sorryAx`.

---

### Phase 3: Derived lemma — identity `⊢ φ → φ` [COMPLETED]

**Landed** (lines 67–74), term-mode S K K derivation. Consumed by Phase 9's recovery step.

```lean
theorem classicalImp_imp_self (φ : PL.Proposition Atom) :
    Derivable ClassicalImpAxiom (φ.imp φ) :=
  mp_deriv
    (mp_deriv ⟨.ax [] _ (.implyS φ (φ.imp φ) φ)⟩ ⟨.ax [] _ (.implyK φ (φ.imp φ))⟩)
    ⟨.ax [] _ (.implyK φ φ)⟩
```

- **Depends on:** 2. **Status**: done; no `sorryAx`.

---

### Phase 4: Derived lemma — composition / `imp_trans` (empty context) [COMPLETED]

**Landed** (lines 80–87), pure K + S term proof for the **empty (`Derivable`) context**:

```lean
theorem classicalImp_imp_trans {φ ψ χ : PL.Proposition Atom}
    (h₁ : Derivable ClassicalImpAxiom (φ.imp ψ))
    (h₂ : Derivable ClassicalImpAxiom (ψ.imp χ)) :
    Derivable ClassicalImpAxiom (φ.imp χ) :=
  mp_deriv (mp_deriv ⟨.ax [] _ (.implyS φ ψ χ)⟩
              (mp_deriv ⟨.ax [] _ (.implyK (ψ.imp χ) φ)⟩ h₂)) h₁
```

- **Depends on:** 3. **Status**: done; no `sorryAx`.
- **NOTE (report 02 §F7)**: this empty-context form is **not** usable inside the truth lemma, which
  composes derivations living in the context `litCtx v goal as`. Two in-context siblings are required
  and are added at the head of Phase 7 (Step 0) as NEW declarations — see Phase 7. Phase 4 itself
  remains landed and unchanged.

---

### Phase 5: Derived lemma — Peirce-driven classical case lemma [COMPLETED]

**Landed** (lines 94–97). Peirce's law is invoked here and only here. Its shape is **exactly** what
the corrected Phase 7 needs (report 02 §F4 Peirce-instantiation detail) — **no change required**:

```lean
theorem classicalImp_peirce_mp {Γ : List (PL.Proposition Atom)} {φ goal : PL.Proposition Atom}
    (h : Deriv ClassicalImpAxiom Γ ((φ.imp goal).imp φ)) :
    Deriv ClassicalImpAxiom Γ φ :=
  mp_deriv ⟨.ax Γ _ (.peirce φ goal)⟩ h
```

- **Depends on:** 4. **Status**: done; no `sorryAx`. Consumed by Phase 7's `imp` TRUE-side
  false-antecedent subcase, instantiated with `φ := goal` (the surrogate) and `goal`-slot `:= a.imp b`.

---

### Phase 6: Atom collector + literal-context `litCtx` + membership helper [COMPLETED]

**Landed** (lines 103–132): `Proposition.atoms` (the `as`-collector), `litCtx`, and `litCtx_mem`.
All unchanged and correct under the corrected truth lemma (report 02 §F3).

```lean
def Proposition.atoms : PL.Proposition Atom → List Atom
  | .atom p => [p]
  | .imp a b => a.atoms ++ b.atoms
  | _ => []
-- litCtx (114-118) and litCtx_mem (121-132) as committed; see Representation Decision.
```

- **Depends on:** 1. **Status**: done.

---

### Phase 7: In-context helpers + CORRECTED Kalmár truth lemma (double-negation form) [NOT STARTED]

**This is the substantive correction in v3 and the risk-concentrated phase.** Encodes report 02
§F3 (signature), §F4 (per-case table), §F7 (helpers).

#### Step 0 — two NEW in-context micro-helpers (report 02 §F7)

The committed `classicalImp_imp_trans` (Phase 4) is empty-context only. Add these two helpers (each
≤6 lines, pure DT + `mp_deriv` + `assumption_deriv`; no new mathematics). They are the only NEW
additions to the derived-lemmas area and are **`[NOT STARTED]`** (distinct from the landed
empty-context lemmas). Land them FIRST, verify green:

```lean
/-- In-context composition: from `Γ ⊢ φ → ψ` and `Γ ⊢ ψ → χ` derive `Γ ⊢ φ → χ`.
DT over `[φ]`: assumption `φ`, `mp_deriv` with (weakened) `h₁` then `h₂`, then peel. -/
theorem classicalImp_imp_trans_ctx {Γ : List (PL.Proposition Atom)} {φ ψ χ : PL.Proposition Atom}
    (h₁ : Deriv ClassicalImpAxiom Γ (φ.imp ψ)) (h₂ : Deriv ClassicalImpAxiom Γ (ψ.imp χ)) :
    Deriv ClassicalImpAxiom Γ (φ.imp χ) := by
  sorry

/-- In-context K-weakening: from `Γ ⊢ ψ` derive `Γ ⊢ φ → ψ` (K axiom + `mp_deriv`). -/
theorem classicalImp_weaken_ctx {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (h : Deriv ClassicalImpAxiom Γ ψ) : Deriv ClassicalImpAxiom Γ (φ.imp ψ) := by
  sorry
```

(Replace each `sorry` with the ≤6-line proof; verify with `lean_goal`. Commit Step 0 separately if
the dispatch budget is tight, then proceed to the truth lemma.)

#### Step 1 — the corrected Kalmár truth lemma (report 02 §F3)

**Goal**: induction on imp-top-only `φ`, relative to a Boolean assignment `v`, an atom list `as`
covering `φ`'s atoms, and a **fixed abstract surrogate `goal`**. TRUE branch concludes the **double
negation** `(φ → goal) → goal`; FALSE branch concludes `φ → goal`. Only `atom` and `imp` cases are
live (`bot`/`and`/`or` excluded by `IsImpTopOnly`).

**Do NOT re-implement the v2 `⊢ φ` conclusion** — it is semantically invalid for all `goal`
(countermodel in Overview; report 02 §F1). **Do NOT vary `goal` and do NOT introduce any
context-equality helper** — `goal` is fixed; both IHs use the same context `litCtx v goal as`.

```lean
/-- Kalmár truth lemma (falsum-surrogate / double-negation form). For imp-top-only `φ`, under the
literal context `litCtx v goal as` (with `as` covering the atoms of `φ`): if `v ⊨ φ` then the context
derives the double negation `(φ → goal) → goal`; otherwise it derives `φ → goal`. The surrogate
`goal` is fixed and arbitrary. Proved by induction on `φ`; only `atom` and `imp` cases are live.
Peirce's law enters only in the `imp` TRUE-side false-antecedent subcase. -/
theorem classicalImp_kalmar {v : BoolValuation Atom} {goal : PL.Proposition Atom}
    (as : List Atom) {φ : PL.Proposition Atom} (hITO : φ.IsImpTopOnly = true)
    (hcov : ∀ p, p ∈ φ.atoms → p ∈ as) :
    (BoolEvaluate v φ = true  →
        Deriv ClassicalImpAxiom (litCtx v goal as) ((φ.imp goal).imp goal)) ∧
    (BoolEvaluate v φ = false →
        Deriv ClassicalImpAxiom (litCtx v goal as) (φ.imp goal)) := by
  revert hITO hcov          -- φ-dependent; reintroduce per case
  induction φ with
  | atom p => intro hITO hcov; ...
  | imp a b iha ihb => intro hITO hcov; ...
  | bot => intro hITO _; simp [Proposition.IsImpTopOnly] at hITO
  | and a b _ _ => intro hITO _; simp [Proposition.IsImpTopOnly] at hITO
  | or a b _ _ => intro hITO _; simp [Proposition.IsImpTopOnly] at hITO
```

Notes (report 02 §F3): `goal`, `v`, `as` are **fixed** across the induction; only `hITO`/`hcov` are
reverted then reintroduced per case. `litCtx`/`litCtx_mem` unchanged. No helper beyond `litCtx_mem`
is needed for membership.

#### Per-case discharge table (report 02 §F4)

Let `Γ := litCtx v goal as`. "DT" = `classicalImpAxiom_hasDeductionTheorem` (peels head:
`Deriv (φ::Γ) ψ → Deriv Γ (φ.imp ψ)`). `K φ ψ := ⟨.ax _ _ (.implyK φ ψ)⟩ : Γ ⊢ φ→(ψ→φ)`.

| Case | `v`-condition | Conclusion | Discharge recipe | Peirce? |
|------|---------------|------------|------------------|---------|
| `atom p` TRUE | `v p = true` | `Γ ⊢ (p→goal)→goal` | literal `atom p ∈ Γ` (`litCtx_mem`); DT over `[p→goal]`: from `p→goal` and `p` get `goal` by `mp_deriv`; DT ⟹ conclusion | no |
| `atom p` FALSE | `v p = false` | `Γ ⊢ p→goal` | literal `(atom p).imp goal ∈ Γ` (`litCtx_mem`); `assumption_deriv` | no |
| `imp a b` FALSE | `v a=true, v b=false` (`v⊭a→b`) | `Γ ⊢ (a→b)→goal` | IHa-TRUE `Γ⊢(a→goal)→goal`, IHb-FALSE `Γ⊢b→goal`. DT over `[a→b]`: compose `a→b` (assumption) with `b→goal` to `a→goal` via `classicalImp_imp_trans_ctx`; `mp_deriv` IHa-TRUE ⟹ `goal`; DT | no |
| `imp a b` TRUE, **false antecedent** | `v a=false` (any `v b`) | `Γ ⊢ ((a→b)→goal)→goal` | IHa-FALSE `Γ⊢a→goal`. DT introduces `H:=(a→b)→goal`; build `Γ,H ⊢ (goal→(a→b))→goal` (inner DT introduces `K':=goal→(a→b)`; under `a`: `a→goal`⟹`goal`, `K'`⟹`a→b`, ⟹`b`; DT ⟹`a→b`; `H`⟹`goal`); apply `classicalImp_peirce_mp` (its `φ:=goal`, `goal`-slot`:=a→b`) ⟹ `goal`; DT ⟹ conclusion | **YES** |
| `imp a b` TRUE, **true consequent** | `v a=true, v b=true` | `Γ ⊢ ((a→b)→goal)→goal` | IHb-TRUE `Γ⊢(b→goal)→goal`. DT introduces `H:=(a→b)→goal`; from `K b a : b→(a→b)` compose with `H` to `b→goal` via `classicalImp_imp_trans_ctx`; `mp_deriv` IHb-TRUE ⟹ `goal`; DT | no |

Splitting guidance (report 02 §F4): the two TRUE subcases partition `v ⊨ (a→b)` — split on
`BoolEvaluate v a`; in the `true` branch the TRUE side forces `v b = true` (else it is the FALSE
case). `Bool.and_eq_true` on `hITO` supplies `a.IsImpTopOnly`/`b.IsImpTopOnly`; `hcov` for `a`/`b`
follows from `Proposition.atoms (a.imp b) = a.atoms ++ b.atoms` and `List.mem_append`. Discharge
`bot`/`and`/`or` with `simp [Proposition.IsImpTopOnly] at hITO` (copy `ImpConservative.lean:79,84,85`).

**Implementer order (report 02 §Recommendations)**: prove the `atom` case and the FALSE side first
(no Peirce), optionally commit; then the two TRUE subcases; verify the Peirce subcase with `lean_goal`
at the intermediate `Γ,H ⊢ goal`. Whole truth lemma ≈ 55–70 lines; factor the `imp` case into a
private helper if context budget is tight.

**[BLOCKED] fallback**: if the `imp` TRUE false-antecedent (Peirce) subcase is still intractable
within budget, mark this phase `[BLOCKED]` with the precise stuck goal state recorded (exact
`lean_goal` output, which conjunct/subcase, and the intermediate `Γ,H` goal). Leave NO `sorry`, NO
`axiom`, NO vacuous placeholder. Phases 8–10 then also block; Phases 1–6 remain committed value.

- **Depends on:** 6 (and consumes Phases 3, 5; uses the Step-0 helpers). **Verification**:
  `sorry`-free; `lean_verify Cslib.Logic.PL.classicalImp_kalmar` shows no unexpected axioms.

---

### Phase 8: Single-atom elimination step [NOT STARTED]

**UNCHANGED from v3 draft (report 02 §F6: independent of the truth-lemma conclusion shape).**

**Goal**: Eliminate one atom from the front of the literal context, collapsing the two Boolean
branches for that atom.

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
**Recipe**: DT on `hT` (peel `atom p`) → `Γ ⊢ (atom p) → goal`; DT on `hF` (peel `(atom p).imp goal`)
→ `Γ ⊢ ((atom p) → goal) → goal`; then one `mp_deriv` gives `Γ ⊢ goal`
(`classicalImpAxiom_hasDeductionTheorem` has type `HasDeductionTheorem (propDerivationSystem
ClassicalImpAxiom)`; unfold `propDerivationSystem`/`Deriv` if needed, `DeductionTheorem.lean:205`).
~12–20 lines. Replace the `sorry` before committing.

- **Depends on:** 7. **Verification**: green; no `sorryAx`.

---

### Phase 9: Iterate elimination + `classicalImp_completeness` [NOT STARTED]

**Goal**: Iterate `classicalImp_elim_atom` over the atom list to discharge the whole context, then
conclude completeness. **One-step patch over v3 draft** (report 02 §F6): recover `Γ ⊢ φ` from the
double-negation TRUE side at `goal := φ`.

```lean
/-- Collapse the full literal context: if for every Boolean assignment the context derives `goal`,
then the empty context derives `goal`. By induction on `as`, using `classicalImp_elim_atom`. -/
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
**Recipe (`classicalImp_collapse`)**: `induction as`. Base `[]`: `litCtx v goal [] = []`, so `h v` is
`Derivable … goal`. Cons `p :: ps`: instantiate `h` at the two assignments agreeing off `p` and
differing on `p` (`Function.update`), feed the two `litCtx` branches (the `if v p` reduces under the
updated valuation, `simp [litCtx]`) to `classicalImp_elim_atom`, then to the IH. ~20–30 lines.

**Recipe (`classicalImp_completeness`)** (report 02 §F6, the corrected recovery step): take
`as := φ.atoms`; from `h : Tautology φ` get `∀ v, BoolEvaluate v φ = true` via
`tautology_iff_boolEvaluate_true`; for each `v`, the **TRUE conjunct of `classicalImp_kalmar` at
`goal := φ`** gives `Deriv (litCtx v φ as) ((φ.imp φ).imp φ)`. **Recover `Deriv (litCtx v φ as) φ`**
by `mp_deriv hKalmarTrue hIdId`, where `hIdId : Deriv (litCtx v φ as) (φ.imp φ)` is
`classicalImp_imp_self φ` (empty-context `Derivable`) **weakened via `weakening_deriv`** (`[] ⊆ _`).
Then feed `∀ v, Deriv (litCtx v φ as) φ` to `classicalImp_collapse` with `goal := φ`. ~14–20 lines
(net addition over the draft: the single `mp_deriv … (weakening_deriv (classicalImp_imp_self φ) …)`).

- **Depends on:** 8. **Verification**: `sorry`-free;
  `lean_verify Cslib.Logic.PL.classicalImp_completeness` shows no `sorryAx`.

---

### Phase 10: Conservativity, chain extension, CI gate [NOT STARTED]

**UNCHANGED from v3 draft (report 02 §F6: conservativity capstone unaffected by the conclusion shape).**

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
classical-branch edge `CPL⟨→,⊤⟩ ⊂ CPL`. Mirror `derivableImpOfDerivableInt` / biconditional pattern
(`ImpConservative.lean:135-149`). Keep additions minimal; do not edit existing chain theorems.

**Then** run the full CI gate (Testing & Validation). Fix lint/shake/import/barrel issues.

- **Depends on:** 9. **Verification**: full CI gate green; existing chain unchanged.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Metalogic.ClassicalImpCompleteness` — scoped build green
      after each of Phases 7–10.
- [ ] `lake build` — whole library compiles; no `sorry`/`axiom` introduced.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — new/edited modules import `Cslib.Init`.
- [ ] `lake exe lint-style` — style clean (docstrings on every decl, naming, line length).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports.
- [ ] `lake exe mk_all --module Cslib` — module registered in barrel (already present; re-confirm).
- [ ] Existing intuitionistic chain in `ConservativeChain.lean` unchanged and still compiles.
- [ ] `lean_verify` on `classicalImp_kalmar`, `classicalImp_completeness`, `cpl_conservative_over_imp`
      — no `sorryAx`, no unexpected axioms.
- [ ] No edits outside `Logics/Propositional/{ProofSystem,Metalogic,Semantics/Algebra}`.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` — extended (Phase 7+) with:
  `classicalImp_imp_trans_ctx`, `classicalImp_weaken_ctx` (NEW in-context helpers),
  `classicalImp_kalmar` (corrected double-negation form), `classicalImp_elim_atom`,
  `classicalImp_collapse`, `classicalImp_completeness`, `cpl_conservative_over_imp`,
  `derivablePropOfDerivableClassicalImp`, `classicalImpAxiom_iff_chain`. (Phases 1–6 decls already
  landed; `litCtx`/`litCtx_mem`/`classicalImp_peirce_mp` unchanged. No `litCtx_goal_congr` — dropped.)
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` — classical-branch
  subsumption + doc-table edge `CPL⟨→,⊤⟩ ⊂ CPL`.
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — Phase 1 block (already committed).
- Barrel updated via `mk_all` (already present).
- `specs/352_cpl_conservative_over_classical_implicational_fragment/summaries/03_classical-imp-conservativity-summary.md`
  (at completion).

## Rollback/Contingency

- All changes additive and confined to the new module + `ConservativeChain.lean` doc/subsumption +
  the already-committed `FragmentAxioms.lean` block. To revert post-Phase-6 work: truncate
  `Metalogic/ClassicalImpCompleteness.lean` back to `litCtx_mem` (line 132), revert the
  `ConservativeChain.lean` additions, re-run `lake exe mk_all --module Cslib`. The existing chain is
  never edited, so rollback cannot regress it.
- **Zero-debt fallback (R1)**: if the corrected Phase 7 (specifically the Peirce subcase) is
  intractable within budget, mark it `[BLOCKED]` with the exact stuck goal state recorded, leave NO
  `sorry` and NO `axiom`, and surface for user review. Phases 1–6 remain self-contained, CI-green,
  additive value.
- **Per-phase commits** mean a context-overflow death in any later phase loses at most that one
  phase's in-progress work; all prior phases are already committed.
