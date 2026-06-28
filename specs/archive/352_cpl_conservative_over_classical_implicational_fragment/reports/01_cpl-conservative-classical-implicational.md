# Research Report: CPL Conservative over Classical Implicational Fragment CPL⟨→,⊤⟩

Task: 352 | Session: sess_1782454849_22df5a_352 | Agent: cslib-research-agent

## 1. Executive Summary / Go-No-Go

**Recommendation: GO, but optional/low-priority. Use the truth-assignment route, not the
algebraic route.** Matthew Doty himself flagged this as low-interest ("not as interesting in
terms of Curry-Howard or Category theory") and preferred truth assignments over algebraic
semantics. The research confirms this preference is also the *cheapest* route by a wide margin.

The entire task reduces to **one genuinely new theorem**:

> `classicalImp_completeness`: for imp-top-only `φ`, `Tautology φ → Derivable ClassicalImpAxiom φ`
> (the Tarski–Bernays theorem: K, S, Peirce axiomatize the classical implicational fragment).

Everything else — CPL soundness (`prop_soundness_tautology`), CPL completeness
(`prop_completeness`), the `Tautology` bivalent semantics, the axiom-subsumption/deduction-theorem
boilerplate — already exists and is directly reusable. The conservativity theorem is then a
two-line composition.

The risk is concentrated entirely in that one completeness proof. It is a classical, finite, but
**intricate** Hilbert-style argument (Kalmár method adapted to the negation-free implicational
fragment using the conclusion as a "falsum surrogate"). Effort estimate: 1–2 focused
implementation phases (~250–450 new lines split across a fragment-axioms block and one new
completeness module). If the Kalmár derivations prove too fiddly, the honest fallback is to mark
the completeness phase `[BLOCKED]` for user review — **no sorry, no new axiom**.

## 2. Pinning Down the Axiomatization (Deliverable 1)

The classical implicational fragment CPL⟨→,⊤⟩ is axiomatized (with modus ponens) by exactly:

| Axiom | Schema | Status |
|-------|--------|--------|
| **K** (`implyK`, weakening) | `φ → (ψ → φ)` | already in `ImpAxiom` |
| **S** (`implyS`, distribution) | `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` | already in `ImpAxiom` |
| **Peirce** (`peirce`) | `((φ → ψ) → φ) → φ` | already a constructor of `PropositionalAxiom` |

This is the standard **Tarski–Bernays** axiomatization of the implicational fragment of classical
logic, and it is the cleanest fit with the existing code because:

- `ImpAxiom` (K + S) already exists in `FragmentAxioms.lean` — `ClassicalImpAxiom` is literally
  `ImpAxiom` + the existing `peirce` schema.
- `PropositionalAxiom.peirce` is already defined as `((φ.imp ψ).imp φ).imp φ`
  (`ProofSystem/Axioms.lean:58-60`), so the subsumption `ClassicalImpAxiom → PropositionalAxiom`
  is mechanical.
- **Peirce is itself imp-top-only** (no `⊥`, `∧`, `∨`): `((φ→ψ)→φ)→φ` over imp-top-only `φ,ψ` is
  imp-top-only. So the fragment is genuinely purely implicational, and the `IsImpTopOnly`
  fragment-predicate machinery applies unchanged.

The thread "lists candidate schemata that should be verified": K + S + Peirce is the canonical and
recommended set. (Alternatives exist — e.g. Łukasiewicz's single-axiom / three-axiom
implicational bases — but they would not reuse the existing `ImpAxiom`/`peirce` definitions and
offer no benefit. The plan should fix K + S + Peirce.)

**Important structural note:** `ClassicalImpAxiom` is NOT a sub-predicate of `IntPropAxiom`
(Peirce is not intuitionistically valid). It therefore does **not** slot into the existing
intuitionistic chain `IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ ... ⊂ IPL`. It is a **separate classical branch**:
`ImpAxiom ⊆ ClassicalImpAxiom ⊆ PropositionalAxiom`, sitting underneath CPL only.

## 3. Route Evaluation (Deliverable 2)

### Route B — Truth-assignment / Kalmár (RECOMMENDED)

Reduce conservativity to fragment completeness against the existing 2-valued `Tautology`
semantics (`Semantics/Bool.lean`):

```
cpl_conservative_over_imp (hITO : φ.IsImpTopOnly) (h : Derivable PropositionalAxiom φ)
    : Derivable ClassicalImpAxiom φ :=
  classicalImp_completeness hITO (prop_soundness_tautology h)
```

- `prop_soundness_tautology : Derivable PropositionalAxiom φ → Tautology φ`
  (`Metalogic/Soundness.lean:89-91`) — **reuse, done**.
- `classicalImp_completeness : IsImpTopOnly φ → Tautology φ → Derivable ClassicalImpAxiom φ`
  — **the one new theorem**.

Pros: no new Foundations typeclass; no algebra-embedding theorem; reuses `Tautology`,
`prop_soundness_tautology`, `prop_completeness`, the deduction theorem, and the fragment
predicates. Matches Matthew's stated preference. Self-contained in `Logics/Propositional`.

Cons: the implicational-fragment Kalmár completeness proof is the intricate part. Because the
fragment has no `⊥`/`¬`, the standard atom-elimination step must use the **conclusion `φ` as a
falsum surrogate**: prove `⊢ ℓ₁ → … → ℓₙ → φ` for every Boolean assignment, where the "negative
literal" for an atom `p` set false is encoded as `p → φ` (not `¬p`). Peirce's law supplies the
classical case-elimination. The existing Foundations Peirce lemmas
(`Foundations/Logic/Theorems/Propositional/Core.lean`, `HilbertDerivedRules.lean`) are **not
directly reusable** because they are stated for systems containing `⊥`/EFQ; new pure-implicational
derived lemmas are required.

### Route A — Algebraic (Tarski / implication algebras) (NOT recommended)

Mirror the intuitionistic `HilbertAlgCompleteness.lean` (≈500 lines) construction:

1. New Foundations typeclass `ImplicationAlgebra`/`TarskiAlgebra` = `HilbertAlgebra` + Peirce
   identity `((a ⇨ b) ⇨ a) ⇨ a = ⊤`. (Mathlib has `BooleanAlgebra`, `HeytingAlgebra`,
   `GeneralizedHeytingAlgebra`, but **no implication-reduct / Abbott implication algebra** — CSLib
   already maintains a *custom* `HilbertAlgebra` in `Foundations/Order/` precisely because Mathlib
   lacks the implicational reduct. Confirmed by inspection of `Foundations/Order/HilbertAlgebra*`.)
2. A Lindenbaum–Tarski completeness proof over `ClassicalImpAxiom` (mirror the ≈500-line
   `ImpLindenbaumAlgebra` development).
3. **Abbott representation embedding**: every Tarski algebra `→`-embeds into a Boolean algebra
   (the classical analog of `FreeMeetExtension`/`freeMeetEmbed`). This theorem is substantial and
   absent from Mathlib — it is the real cost driver.

Pros: stylistic symmetry with the existing intuitionistic chain (`freeMeetEvaluateEq` pattern).
Cons: 3+ new files including new Foundations math; the Abbott embedding is non-trivial; Matthew
called these algebras "obscure." Much larger surface area for an explicitly low-interest task.

**Verdict:** Route B. It is smaller, matches the requester's preference, and avoids new
Foundations infrastructure entirely.

## 4. Reuse Map vs Existing Chain (Deliverable 3)

Reuse-first findings (Foundations checked first, then Logics/Propositional):

| Need | Existing asset | Location | Reuse |
|------|----------------|----------|-------|
| K, S schemata | `ImpAxiom.implyK/implyS` | `FragmentAxioms.lean:84-90` | extend |
| Peirce schema | `PropositionalAxiom.peirce` | `Axioms.lean:58-60` | copy shape |
| Deduction theorem | `hasDeductionTheorem mem_implyK mem_implyS` | `Metalogic/DeductionTheorem.lean` | reuse (K,S present) |
| Subsumption pattern | `ImpAxiom.toConjImpAxiom`, `IntPropAxiom.toPropAxiom` | `FragmentAxioms.lean`, `Axioms.lean:168` | mirror for `toClassicalImpAxiom`/`toPropAxiom` |
| Substitution closure | `subst_preserves_impAxiom` | `FragmentAxioms.lean:161` | mirror |
| `IsImpTopOnly` predicate + lemmas | `Proposition.IsImpTopOnly`, `imp_isImpTopOnly` | `FragmentPredicates.lean` | reuse (covers Peirce) |
| Bivalent semantics | `Tautology`, `Evaluate`, `BoolEvaluate`, `instDecidableTautology` | `Semantics/Bool.lean` | reuse |
| CPL soundness | `prop_soundness_tautology` | `Metalogic/Soundness.lean:89` | reuse |
| CPL completeness | `prop_completeness`, `prop_completeness_iff_tautology` | `Metalogic/StrongCompleteness.lean:548,558` | reuse |
| `liftDerivationTree` for subsumption | used in `derivableImpOfDerivableInt` | `ImpConservative.lean:135` | reuse |
| Chain capstone | `ConservativeChain.lean` derivability-subsumption section | `ConservativeChain.lean:103-138` | extend with classical branch |

No existing CSLib abstraction covers "classical implicational fragment completeness" — this is a
genuine gap (the chain is currently intuitionistic-only; the `... ⊂ CPL` edge in
`ConservativeChain.lean:25` is the Glivenko negative-translation edge, not a fragment edge).

## 5. Proposed File Plan (Deliverable, for the plan phase)

1. `ProofSystem/FragmentAxioms.lean` (extend): add `inductive ClassicalImpAxiom`
   (`implyK`, `implyS`, `peirce`); `ImpAxiom.toClassicalImpAxiom`;
   `ClassicalImpAxiom.toPropAxiom`; `mem_implyK`/`mem_implyS` witnesses;
   `subst_preserves_classicalImpAxiom`; `classicalImpAxiom_*_isImpTopOnly` (incl. peirce);
   `classicalImpAxiom_hasDeductionTheorem`. Mechanical, ~90 lines.
2. **New** `Metalogic/ClassicalImpCompleteness.lean` (truth-assignment route — note: place under
   `Metalogic/` near `StrongCompleteness.lean`, NOT under `Semantics/Algebra/`, since the chosen
   route is truth-assignment-based; the task text's `Semantics/Algebra/ClassicalImpConservative.lean`
   name presupposed the algebraic route we are declining). Contents: soundness
   `Derivable ClassicalImpAxiom φ → Tautology φ` (easy, mirror `prop_soundness`); the Kalmár-style
   `classicalImp_completeness`; and `cpl_conservative_over_imp` + the biconditional. ~250–400 lines,
   the bulk being Kalmár.
3. `Semantics/Algebra/ConservativeChain.lean` (extend): `derivableClassicalImpOfDerivableProp`
   (subsumption via `liftDerivationTree` + `ClassicalImpAxiom.toPropAxiom`),
   re-export/locate `cpl_conservative_over_imp`, the `classicalImpAxiom_iff_chain` biconditional,
   and extend the chain doc table with the classical branch `CPL⟨→,⊤⟩ ⊂ CPL`.

(If the planner instead prefers the file under `Semantics/`, keep it bivalent-semantics-based;
the key point is it must not pull in algebraic Tarski-algebra machinery.)

## 6. Literature Proof Structure (Tarski–Bernays implicational completeness)

Main claim: K + S + Peirce + MP is complete for classical implicational tautologies.
Strategy: Kalmár method with falsum-surrogate. Numbered steps for downstream agents:

1. **Deduction theorem** for `ClassicalImpAxiom` (from K, S) — reuse `hasDeductionTheorem`.
2. **Pure-implicational derived lemmas** (new; cannot reuse ⊥-based Foundations Peirce lemmas):
   identity `⊢ φ→φ`, composition/`imp_trans`, and the Peirce-driven case lemma
   `⊢ (p → φ) → (((p → φ) → φ) → φ)` style elimination (the classical join).
3. **Kalmár truth lemma** by induction on imp-top-only `φ`, relative to a Boolean assignment `v`
   and a fixed target `θ` (= the goal formula): if `v ⊨ φ` then `⊢ Γᵥ → φ`, and if `v ⊭ φ` then
   `⊢ Γᵥ → (φ → θ)`, where `Γᵥ` lists, for each atom `p`, either `p` (if `v p = true`) or `p → θ`
   (if `v p = false`). The `imp` case uses S/K; the classical closure uses Peirce.
4. **Atom elimination**: from `⊢ Γ, p → θ` and `⊢ Γ, (p → θ) → θ` derive `⊢ Γ → θ` (S + Peirce),
   halving the assignment set; iterate over all atoms of `φ`.
5. **Conclude** `⊢ θ` for a tautology `θ` (every branch yields `θ`), giving
   `Tautology θ → Derivable ClassicalImpAxiom θ`.

Lean translation considerations: atoms of `φ` are finite (induct on the finite atom set / formula
structure); `Γᵥ` is a `List`/`Finset` context discharged via the deduction theorem; keep
everything inside the `IsImpTopOnly` invariant so `Γᵥ` entries stay implicational. Follow the
source step-by-step (literature-fidelity): do not attempt to bypass the Kalmár induction with
`decide`/`aesop` — `Tautology` is only decidable for `Fintype Atom`, whereas the theorem is for
arbitrary `Atom`.

## 7. Tactic Survey (advisory)

`prop_completeness`/`prop_soundness` are exact-term compositions (no search needed for the
top-level conservativity theorem). The Kalmár lemmas are structural Hilbert derivations: expect
`apply`/`exact` with explicit axiom witnesses, `induction φ`, and the deduction-theorem combinators;
`simp [Proposition.IsImpTopOnly]` for fragment-predicate side goals (as in `ImpConservative.lean`).
Avoid `decide` (Atom not Fintype). No rate-limited search tools were needed; all evidence is local.

## 8. Risks & CI

- Risk R1 (primary): Kalmár implicational completeness is fiddly. Mitigation: isolate as its own
  phase; if blocked, mark `[BLOCKED]` (no sorry / no axiom — zero-debt).
- Risk R2: file placement. The task text names a `Semantics/Algebra/` module presupposing the
  algebraic route; the recommended route is truth-assignment, so prefer `Metalogic/`. Planner to
  confirm placement with project conventions.
- CI: changes are additive; existing chain untouched. Must keep green: `lake build`, `lake test`,
  `lake exe checkInitImports` (new file must `import Cslib.Init`), `lake exe lint-style`,
  `lake shake`. New file must be added to the barrel via `lake exe mk_all --module`. Lint: all new
  decls need docstrings; Prop-valued use `theorem`/`lemma`; lowerCamelCase names.

## References

- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` (PropositionalAxiom, peirce, IntPropAxiom)
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` (ImpAxiom and the fragment pattern)
- `Cslib/Logics/Propositional/Semantics/Bool.lean` (Tautology, Evaluate, BoolEvaluate)
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` (prop_soundness_tautology)
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` (prop_completeness)
- `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean` (ipl_conservative_over_imp pattern)
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` (chain capstone)
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` (Route-A cost reference)
- `Cslib/Foundations/Order/HilbertAlgebra*` (custom Hilbert algebra; Mathlib lacks implication algebras)
- Tarski–Bernays: implicational fragment of classical logic axiomatized by K, S, Peirce (standard).
