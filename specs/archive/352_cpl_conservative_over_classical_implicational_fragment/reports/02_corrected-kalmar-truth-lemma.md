# Research Report: Corrected Kalmár Truth Lemma for CPL⟨→,⊤⟩ (Task 352 Phase 7)

- **Task**: 352 - Prove CPL is conservative over its classical implicational fragment CPL⟨→,⊤⟩
- **Started**: 2026-06-27T04:56:32Z
- **Completed**: 2026-06-27T05:30:00Z
- **Effort**: ~35 minutes
- **Dependencies**: Phases 1-6 committed (fragment + soundness + identity + imp_trans + peirce_mp + litCtx)
- **Sources/Inputs**:
  - `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` (litCtx, litCtx_mem, classicalImp_imp_self, classicalImp_imp_trans, classicalImp_peirce_mp)
  - `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` (ClassicalImpAxiom: implyK/implyS/peirce; classicalImpAxiom_hasDeductionTheorem)
  - `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` (Deriv, mp_deriv, weakening_deriv, assumption_deriv)
  - `Cslib/Logics/Propositional/Semantics/Bool.lean` (BoolEvaluate, Tautology, tautology_iff_boolEvaluate_true)
  - `Cslib/Foundations/Logic/Metalogic/Consistency.lean` (HasDeductionTheorem)
  - Plan v2 Phase 7 BLOCKER block; orchestrator handoff JSON
  - Literature: arXiv 2305.05035 (Kalmár-style constructive completeness for positive calculi with Peirce); arXiv 1512.00091; arXiv 1511.02953
- **Artifacts**: this report
- **Standards**: report-format.md; cslib.md; lean4.md (zero-debt)

## Executive Summary

- **VERDICT: the proposed fix (b) is WRONG and unnecessary.** Neither "vary `goal` to `a.imp b`
  in the recursive call" (b) nor "fix `goal` to the outer/top formula" (a) yields a true lemma.
  Both keep the TRUE-side conclusion equal to `φ`, and that conclusion is the actual bug: it is
  semantically invalid for the implicational fragment (the recorded countermodel refutes it).
- **The real correction is the TRUE-side conclusion.** The truth lemma must conclude the
  **double-negation relative to the surrogate**, `(φ → goal) → goal`, in the TRUE case (not `φ`),
  while the FALSE case keeps `φ → goal`. This is the standard Kalmár falsum-surrogate / Kuroda
  negative-translation encoding (`goal` plays ⊥; "`φ` true" = `¬¬φ`, "`φ` false" = `¬φ`).
- With that single change, **`goal` stays a fixed abstract parameter** (universally quantified,
  never varied per recursion). **No context-equality lemma and no generalized-`goal` IH are
  needed** — the contexts never change during the induction. Both branches are valid for *every*
  `goal`, so the countermodel disappears.
- **Peirce's law is required in exactly one subcase**: the `imp a b` TRUE-side with a *false
  antecedent* (`BoolEvaluate v a = false`). It is discharged by the existing `classicalImp_peirce_mp`
  with its `goal`-slot instantiated to `a.imp b` (so Phase 5's lemma shape is already correct).
- **Downstream is essentially unchanged.** Phase 8 (`classicalImp_elim_atom`) is untouched. Phase 9
  inserts one extra `mp_deriv` with the weakened identity `φ → φ` to recover
  `litCtx v φ as ⊢ φ` from `litCtx v φ as ⊢ (φ → φ) → φ` at `goal := φ`.
- One small implementation refinement: the truth lemma needs **context-level** composition and
  K-weakening; the committed `classicalImp_imp_trans` is empty-context only. Add tiny in-context
  helpers (or inline `deduction + mp`). No new mathematics.

## Context & Scope

The deliverable `classicalImp_completeness` proves K+S+Peirce complete for imp-top-only
tautologies via the Kalmár / Tarski–Bernays truth-assignment method. The fragment is negation-free
(no ⊥), so a designated formula `goal` plays the role of falsum (falsum surrogate). Phase 7 stalled
because the truth lemma as planned,

```
(BoolEvaluate v φ = true  → Deriv ClassicalImpAxiom (litCtx v goal as) φ) ∧
(BoolEvaluate v φ = false → Deriv ClassicalImpAxiom (litCtx v goal as) (φ.imp goal))
```

has a TRUE-side conclusion (`φ`) that is **false as a mathematical statement**. The question is
the precise correct statement, its exact Lean signature, the per-case discharge recipe, and the
downstream impact. The semantics in scope: `BoolEvaluate v (a.imp b) = (!BoolEvaluate v a || BoolEvaluate v b)`
(`Bool.lean:93`), `litCtx` maps a true atom `p` to `atom p` and a false atom to `(atom p).imp goal`
(`ClassicalImpCompleteness.lean:114-118`).

## Findings

### F1 — Why both (a) and (b) fail: the TRUE-side `φ` conclusion is invalid

Write `Γ = litCtx v g as` = `{ atom p : v p = true } ∪ { atom p → g : v p = false }`.

**Semantic test of the planned TRUE side `Γ ⊨ φ` when `v ⊨ φ`.** Take a model `w ⊨ Γ`. The
constraints are: `v p = true ⟹ w p = true`; `v p = false ⟹ (w p = false ∨ w ⊨ g)`. If `w ⊨ g`,
the false atoms are *unconstrained*, so `w` may flip a `v`-false atom and falsify `φ`. Concretely
the recorded countermodel: `φ = p → q`, `v p = v q = false` (so `v ⊨ φ`), `g = r`,
`Γ = {p→r, q→r}`; the model `w = (p:T, q:F, r:T)` satisfies `Γ` but not `p→q`. Hence
`Γ ⊭ φ` — the TRUE-side conclusion `φ` is **not a semantic consequence of `Γ`**, so it is
underivable in any sound system regardless of how `g` is chosen.

- **Option (a)** (fix `g` = top formula) does not help: the obstruction is about a *subformula*
  node and is independent of `g`. Worse, when `g` is the top tautology, every false-atom literal
  `p → g` is itself a tautology, so `Γ` is semantically empty and cannot derive any
  non-tautological subformula truth.
- **Option (b)** (vary `g := a.imp b` and bridge contexts) does not help either: the two contexts
  `litCtx v g as` and `litCtx v (a.imp b) as` differ on every false atom (`p→g` vs `p→(a→b)`) and
  are **not interderivable**; the "context-equality lemma" the blocker asks for does not exist.
  The contraction-trick derivation `a→(a→b) ⊢ a→b` is itself valid, but it only relocates the
  obstruction one level down and forces an unsatisfiable simultaneous-surrogate requirement.

**Conclusion:** the bug is not the quantification of `goal`; it is the *shape of the TRUE-side
conclusion*. Keep `goal` fixed and abstract; change the conclusion.

### F2 — The correct statement: double-negation (falsum-surrogate) TRUE side

Encode, relative to the surrogate `g`, "`φ` is true" as `¬¬φ = (φ → g) → g` and "`φ` is false" as
`¬φ = φ → g`. The corrected lemma is:

```
v ⊨ φ  ⟹  litCtx v g as ⊢ (φ → g) → g       -- TRUE side  (was: ⊢ φ)
v ⊭ φ  ⟹  litCtx v g as ⊢ φ → g              -- FALSE side (unchanged)
```

**Both branches are valid for every `g`** (no countermodel):

- FALSE side `Γ ⊨ φ → g` when `v ⊭ φ`: if `w ⊨ Γ` and `w ⊨ φ`, then `w ⊭ g` would force `w = v`
  on `as` (false atoms pinned), giving `w ⊭ φ` — contradiction; so `w ⊨ g`. Valid for all `g`.
- TRUE side `Γ ⊨ (φ → g) → g` when `v ⊨ φ`: if `w ⊨ Γ`, `w ⊨ φ → g`, suppose `w ⊭ g`; then false
  atoms are pinned so `w = v` on `as`, giving `w ⊨ φ`, hence `w ⊨ g` via `φ → g` — contradiction.
  Valid for all `g`.

The countermodel from F1 now checks out: `Γ = {p→r, q→r}` *does* entail `((p→q)→r)→r` (the new
TRUE conclusion), even though it does not entail `p→q`. This is precisely the Kuroda/Glivenko
negative translation specialised to the →-fragment, which is the standard literature device for a
falsum-free Kalmár argument (arXiv 2305.05035; arXiv 1512.00091).

Because `g` is fixed throughout, the induction on `φ` uses IHs for `a`, `b` at the **same**
`v, g, as` — i.e. the **same context** `litCtx v g as`. No context bridge, no goal variation.

### F3 — Exact corrected Lean signature

`Proposition.atoms` exists (`ClassicalImpCompleteness.lean:103`), so `hcov` is grounded as written.

```lean
/-- Kalmár truth lemma (falsum-surrogate / double-negation form). For imp-top-only `φ`, under the
literal context `litCtx v goal as` (with `as` covering the atoms of `φ`): if `v ⊨ φ` then the
context derives the double negation `(φ → goal) → goal`; otherwise it derives `φ → goal`. The
surrogate `goal` is fixed and arbitrary. Proved by induction on `φ`; only `atom` and `imp` cases
are live. Peirce's law enters only in the `imp` TRUE-side false-antecedent subcase. -/
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

Notes:
- `goal`, `v`, `as` are **fixed** across the induction; only `hITO`/`hcov` are reverted.
- The litCtx definition (`:114-118`) is **unchanged** and correct: the false-atom literal
  `(atom p).imp goal` is exactly `¬p` under the surrogate. `litCtx_mem` (`:121-132`) is the only
  membership helper needed.
- **No context-equality / context-membership helper beyond `litCtx_mem` is required.** The
  blocker's requested "context-equality lemma relating `litCtx v goal as` and
  `litCtx v (a.imp b) as`" should be dropped from the plan — it neither exists nor is needed.

### F4 — Per-case discharge table

`Γ := litCtx v goal as`. "DT" = `classicalImpAxiom_hasDeductionTheorem` (peels head:
`Deriv (φ::Γ) ψ → Deriv Γ (φ.imp ψ)`). Axiom leaf `K φ ψ := ⟨.ax _ _ (.implyK φ ψ)⟩ : Γ ⊢ φ→(ψ→φ)`.

| Case | `v`-condition | Goal (conclusion) | Discharge recipe | Peirce? |
|------|---------------|-------------------|------------------|---------|
| `atom p` TRUE | `v p = true` | `Γ ⊢ (p→goal)→goal` | literal `atom p ∈ Γ` (`litCtx_mem`); DT over `[p→goal]`: from `p→goal` and `p` get `goal` by `mp_deriv`; DT ⟹ `(p→goal)→goal` | no |
| `atom p` FALSE | `v p = false` | `Γ ⊢ p→goal` | literal `(atom p).imp goal ∈ Γ` (`litCtx_mem`); `assumption_deriv` | no |
| `imp a b` FALSE | `v a=true, v b=false` (`v⊭a→b`) | `Γ ⊢ (a→b)→goal` | IHa-TRUE `Γ⊢(a→goal)→goal`, IHb-FALSE `Γ⊢b→goal`. DT over `[a→b]`: compose `a→b` (assumption) with `b→goal` to `a→goal` (in-ctx imp_trans); `mp_deriv` IHa-TRUE ⟹ `goal`; DT | no |
| `imp a b` TRUE, **false antecedent** | `v a=false` (any `v b`) | `Γ ⊢ ((a→b)→goal)→goal` | IHa-FALSE `Γ⊢a→goal`. DT introduces `H:=(a→b)→goal`; build `Γ,H ⊢ goal` via **Peirce**: derive `Γ,H ⊢ (goal→(a→b))→goal` (DT introduces `K':=goal→(a→b)`; under `a`: `a→goal`⟹`goal`, `K'`⟹`a→b`, ⟹`b`; DT ⟹`a→b`; `H`⟹`goal`); apply `classicalImp_peirce_mp` (φ:=goal, goal-slot:=a→b) ⟹ `goal`; DT ⟹ conclusion | **YES** |
| `imp a b` TRUE, **true consequent** | `v a=true, v b=true` | `Γ ⊢ ((a→b)→goal)→goal` | IHb-TRUE `Γ⊢(b→goal)→goal`. DT introduces `H:=(a→b)→goal`; from `K b a : b→(a→b)` compose with `H` to `b→goal` (in-ctx imp_trans); `mp_deriv` IHb-TRUE ⟹ `goal`; DT | no |

The two TRUE subcases partition `v ⊨ (a→b)`: `v a = false` (covers both `v b` values) and
`v a = true ∧ v b = true`. Split on `BoolEvaluate v a`; in the `true` branch the TRUE side forces
`v b = true` (else it is the FALSE case). `Bool.and_eq_true` on `hITO` gives `a.IsImpTopOnly` and
`b.IsImpTopOnly` for the IHs; `hcov` for `a`/`b` follows from `Proposition.atoms (a.imp b) = a.atoms ++ b.atoms`.

**Peirce instantiation detail (grounded):** `classicalImp_peirce_mp` (`:94-97`) has signature
`{Γ} {φ goal} (h : Deriv ClassicalImpAxiom Γ ((φ.imp goal).imp φ)) : Deriv ClassicalImpAxiom Γ φ`,
i.e. it consumes `Γ ⊢ (φ→goal)→φ` and yields `Γ ⊢ φ`. In the false-antecedent subcase use it with
its `φ := goal` (the surrogate) and its `goal := a.imp b`: it consumes
`Γ,H ⊢ (goal→(a→b))→goal` and yields `Γ,H ⊢ goal`. The lemma's existing shape is therefore exactly
what Phase 7 needs — **Phase 5 requires no change.**

### F5 — Why Peirce is genuinely required (and only there)

K+S alone (intuitionistic implicational logic) cannot prove Peirce's law, which is a classical
→-tautology; so completeness for classical →-tautologies must use Peirce somewhere. Every case
above except the `imp` TRUE false-antecedent subcase uses only K, S (via DT/`mp`), identity, and
context-level composition — all intuitionistically valid. The false-antecedent subcase is exactly
where the classical "reasoning by cases on `goal`" is needed, and it is discharged by the single
`peirce` axiom application. This matches the literature: adding Peirce's rule to the K,S core is
the minimal completion of the implicational fragment (arXiv 1511.02953; Studia Logica,
"Normalization Strategy for the Implicational Fragment of Classical Propositional Logic").

### F6 — Downstream impact (Phases 8 and 9)

- **Phase 8 `classicalImp_elim_atom` — unchanged.** It only manipulates a fixed `goal`:
  `(atom p :: Γ ⊢ goal)` and `((atom p).imp goal :: Γ ⊢ goal)` collapse to `Γ ⊢ goal` via DT + one
  `mp_deriv`. Independent of the truth-lemma conclusion shape.
- **Phase 9 `classicalImp_completeness` — one extra step.** Apply `classicalImp_kalmar` at
  `goal := φ`. For a tautology, `BoolEvaluate v φ = true` for all `v`
  (`tautology_iff_boolEvaluate_true`), so the TRUE side gives
  `Deriv (litCtx v φ as) ((φ.imp φ).imp φ)`. Recover `Deriv (litCtx v φ as) φ` by
  `mp_deriv hKalmarTrue hIdId`, where `hIdId : Deriv (litCtx v φ as) (φ.imp φ)` is
  `classicalImp_imp_self φ` (`:70`, empty-context `Derivable`) weakened via `weakening_deriv`
  (`[] ⊆ anything`). Then feed `∀ v, Deriv (litCtx v φ as) φ` to `classicalImp_collapse` exactly as
  planned. Net change: insert the single `mp_deriv … (weakening_deriv (classicalImp_imp_self φ) …)`.
- **Phases 10 / conservativity — unchanged.**

### F7 — Implementation refinement: context-level helpers

The committed `classicalImp_imp_trans` (`:80-87`) is stated for `Derivable` (empty context) and is
**not** directly usable inside the truth lemma, which composes derivations living in the context
`litCtx v goal as`. Two in-context micro-helpers remove all friction (each ≤ 6 lines, pure
DT+`mp_deriv`+`assumption_deriv`; no new math):

```lean
theorem classicalImp_imp_trans_ctx {Γ} {φ ψ χ}
    (h₁ : Deriv ClassicalImpAxiom Γ (φ.imp ψ)) (h₂ : Deriv ClassicalImpAxiom Γ (ψ.imp χ)) :
    Deriv ClassicalImpAxiom Γ (φ.imp χ)        -- DT over [φ]: assumption φ, mp h₁, mp h₂

theorem classicalImp_weaken_ctx {Γ} {φ ψ}
    (h : Deriv ClassicalImpAxiom Γ ψ) : Deriv ClassicalImpAxiom Γ (φ.imp ψ)  -- K + mp_deriv
```

Alternatively inline `DT (mp_deriv (weakening_deriv h₂ …) (mp_deriv (weakening_deriv h₁ …)
(assumption_deriv …)))` at each use site. Recommended: add the two helpers (cleaner, reused 3×).
These belong in a revised Phase 4/5 block, not as a "context-equality" lemma.

## Decisions

- **D1**: Adopt the double-negation TRUE-side conclusion `(φ → goal) → goal`; keep FALSE side
  `φ → goal`; keep `goal` fixed/abstract. Reject blocker options (a) and (b).
- **D2**: Drop the planned "context-equality lemma" entirely — not needed, does not exist.
- **D3**: Keep `litCtx`, `litCtx_mem`, and `classicalImp_peirce_mp` exactly as committed.
- **D4**: Add two in-context helpers (`..._trans_ctx`, `..._weaken_ctx`); patch Phase 9 with one
  `mp_deriv`-with-identity recovery step. Phase 8 untouched.

## Recommendations

1. **Revise the plan (Phase 7)**: replace the truth-lemma statement with the F3 signature and the
   F4 recipe table. Remove the BLOCKER block's options (a)/(b) and the context-equality requirement.
   Mark Phase 7 `[NOT STARTED]` again under the corrected statement.
2. **Add the F7 context helpers** (revise Phase 4 to include `classicalImp_imp_trans_ctx` and
   `classicalImp_weaken_ctx`, or add them at the head of Phase 7).
3. **Patch Phase 9** recipe: after the TRUE-side application at `goal := φ`, recover
   `litCtx v φ as ⊢ φ` via `mp_deriv` with the weakened `classicalImp_imp_self φ` before
   `classicalImp_collapse`.
4. **Implementer guidance**: prove the `atom` case and the FALSE side first (no Peirce), commit;
   then the two TRUE subcases; verify the Peirce subcase with `lean_goal` at the `Γ,H ⊢ goal`
   intermediate. Whole lemma ≈ 55–70 lines (slightly above the plan's 50-line target — acceptable;
   may split the `imp` case into a private helper if context budget is tight). Zero-debt: no
   `sorry`, no new axiom.

## Risks & Mitigations

- **R1 — `induction φ` reverts**: `hITO`/`hcov` depend on `φ`; revert them before `induction`,
  reintroduce per case (shown in F3). Mitigation: copy the `simp [Proposition.IsImpTopOnly] at hITO`
  idiom for `bot`/`and`/`or` from `ImpConservative.lean:79,84,85`.
- **R2 — Peirce subcase nesting**: the false-antecedent subcase nests two DT introductions
  (`H` then `K'`). Mitigation: build the intermediate `Γ,H ⊢ (goal→(a→b))→goal` as a `have`, check
  with `lean_goal`, then one `classicalImp_peirce_mp` + DT.
- **R3 — context helper omission**: forgetting F7 forces verbose inlining and risks overflow.
  Mitigation: land the two helpers first.
- **R4 — literature fidelity**: the double-negation TRUE side is the *standard* falsum-surrogate
  form, not a deviation; no fidelity flag needed. Confidence high (semantic validity proven for all
  `g`; explicit Hilbert derivations traced for every case incl. the Peirce step; all API signatures
  grounded against the committed files).

## Appendix

- **References**:
  - arXiv 2305.05035 — "Kalmár-style constructive completeness proofs for classical positive
    propositional calculi" (positive calculi with Peirce; constructive Kalmár).
  - arXiv 1512.00091 — "Implicational Propositional Calculus: Tableaux and Completeness" (Kalmár
    approach, Peirce's law as first axiom).
  - arXiv 1511.02953 — "Implicational Completeness".
  - Studia Logica (Springer) — "A New Normalization Strategy for the Implicational Fragment of
    Classical Propositional Logic" (Peirce's rule completes the K,S core).
- **Grounded file references**: litCtx/litCtx_mem `ClassicalImpCompleteness.lean:114-132`;
  peirce_mp `:94-97`; imp_self `:70-74`; imp_trans `:80-87`; ClassicalImpAxiom + DT instance
  `FragmentAxioms.lean:551-645`; Deriv/mp_deriv/weakening_deriv/assumption_deriv
  `Derivation.lean:122-148`; BoolEvaluate imp clause `Bool.lean:93`; HasDeductionTheorem
  `Consistency.lean:187-188`.
</content>
</invoke>
