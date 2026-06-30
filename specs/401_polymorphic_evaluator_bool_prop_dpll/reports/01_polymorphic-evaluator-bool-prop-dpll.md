# Research Report: Polymorphic Evaluator — Bool / Prop / DPLL Reconciliation (Task 401)

**Session**: sess_1782784353_00a32e_401
**Task type**: cslib
**Date**: 2026-06-30
**Status**: researched

## TL;DR

The mathematical infrastructure the task asks for **already exists and builds** (all
declarations are imported in `Cslib.lean`). Thomas Waring's
`GeneralizedHeytingAlgebra`-polymorphic evaluator is implemented as `AlgEvaluate`, and Matthew
Doty's `Atom → Bool` vs `Atom → Prop` (DPLL portability) concern is already addressed by the
`BoolEvaluate` ↔ `Evaluate` bridge and the `Decidable` instances. **Task 401 is therefore a
documentation-consolidation task** ("ONE documented story") plus two small additive lemmas —
NOT new theory development. No new definitions, no new axioms, no sorries required. Zero-debt is
trivially satisfiable.

## What Already Exists (Reuse — do NOT recreate)

### Prop-valued layer — `Cslib/Logics/Propositional/Semantics/Bool.lean`
- `Valuation (Atom) := Atom → Prop` (abbrev) — line 52. **Keep canonical** (per task: canonical
  model construction needs `Atom → Prop`).
- `Evaluate : Valuation Atom → Proposition Atom → Prop` — line 57, + 5 `@[simp]` unfolding lemmas
  (`Evaluate_atom/bot/imp/and/or`).
- `Tautology φ := ∀ v, Evaluate v φ` — line 80.

### Bool-valued (computable / DPLL) layer — same file `Semantics/Bool.lean`
- `BoolValuation (Atom) := Atom → Bool` (abbrev) — line 86.
- `BoolEvaluate : BoolValuation Atom → Proposition Atom → Bool` — line 90 (computable), + 5
  `@[simp]` unfolding lemmas.
- `BoolEvaluate_eq_iff` — line 115: `BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ`.
  **This is "the bridge lemma"** named in the task.
- `BoolEvaluate_eq_false_iff` — line 128.
- `Evaluate_eq_BoolEvaluate` — line 134: any `Valuation` with `[∀ a, Decidable (v a)]` factors
  through `BoolEvaluate`.
- `instDecidableBoolEvaluate` — line 146: `Decidable (Evaluate (fun a => v a = true) φ)`.
- `tautology_iff_boolEvaluate_true` — line 157: `Tautology φ ↔ ∀ v : BoolValuation, BoolEvaluate v φ = true`.
- `instDecidableTautology` — line 175: `[Fintype Atom] [DecidableEq Atom] → Decidable (Tautology φ)`
  (enumerates `2^n` Boolean valuations). **This is the DPLL/SAT entry point.**

### Algebraic (GHA-polymorphic) layer — `Cslib/Logics/Propositional/Semantics/Algebra.lean`
- `AlgEvaluate {H} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H) : Proposition Atom → H`
  — line 90, + 5 `@[simp]` unfolding lemmas. **This is Waring's GHA-polymorphic evaluator.**
- `GHAValid` / `HAValid` / `BAValid` — lines 126/133/140 (validity in all GHA / HA / BA).
- `AlgTValid` + notation `v ⊨[bot_val] T` — line 149 (Waring's `v ⊨ T` theory-modelling pattern).

### The specialization bridges — `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean`
- `propEvaluateEq` — line 58: `Evaluate v φ ↔ AlgEvaluate (fun a => v a) False φ`
  (Prop is the Heyting algebra; `⊥ = False`).
- `boolEvaluateEq` — line 78: `BoolEvaluate v φ = AlgEvaluate (fun a => v a) false φ`
  (Bool is the Boolean algebra; `⊥ = false`).

So **all three evaluators are already provably the same `AlgEvaluate`** specialized at `Prop`
and `Bool`. The "polymorphic evaluator specialized at Bool (computable) and Prop" the task asks
to "surface" already exists as `AlgEvaluate` + these two bridge theorems.

### Soundness anchor — `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean`
- `prop_strong_soundness` — line 386: `SetDerivable PropositionalAxiom Γ φ → SemanticEntails Γ φ`.
- `SemanticEntails` (`Semantics/SemanticConsequence.lean` line 232) is defined via **`Evaluate`**
  (Prop-valued): `∀ v, (∀ ψ ∈ Γ, Evaluate v ψ) → Evaluate v φ`.

## Confirming the Bridge to `prop_strong_soundness` (task requirement)

`prop_strong_soundness` lives entirely in the **Prop / `Evaluate`** world (via `SemanticEntails`).
The DPLL/Bool world reaches it through a fully-existing chain — no new bridge is needed:

```
DPLL decision          Prop metatheory             Algebraic uniformity
BoolEvaluate v φ = true
   ⟺ (BoolEvaluate_eq_iff)        Evaluate (fun a => v a = true) φ
                                       ⟺ (propEvaluateEq)   AlgEvaluate (·) False φ   [Prop = HA]
   ⟺ (boolEvaluateEq)             AlgEvaluate (·) false φ   [Bool = BA]

SemanticEntails Γ φ  :=  ∀ v, (∀ ψ∈Γ, Evaluate v ψ) → Evaluate v φ
prop_strong_soundness :  SetDerivable … Γ φ → SemanticEntails Γ φ   -- stated in Evaluate
```

**Conclusion to document**: `Evaluate` (Prop) is the hub that soundness/completeness/Kripke are
stated in; `BoolEvaluate` is the computable shadow reachable by `BoolEvaluate_eq_iff`; `AlgEvaluate`
is the common generalization. The soundness bridge is *already confirmed* by the existing lemma
chain; Task 401 only needs to **document** this chain in one place.

## Gaps Found (the actual work)

### Gap 1 — Documentation drift in `Bridge.lean` module docstring (DEFECT, must fix)
`Semantics/Algebra/Bridge.lean` lines 22, 25, 31, 36 reference theorem names `prop_evaluate_eq`
and `bool_evaluate_eq`, but the actual declarations are `propEvaluateEq` / `boolEvaluateEq`
(lowerCamelCase, renamed to satisfy the `defsWithUnderscore` lint). The docstring is stale and
points at non-existent names. **Fix: 4 string replacements** in the module docstring.

### Gap 2 — No canonical "ONE story" doc block
The three evaluators are documented in three separate files' module docstrings. There is no single
narrative tying them together as "Prop for uniformity with Kripke; Bool/AlgEvaluate@Bool for
decision procedures; AlgEvaluate as the common generalization; Valuation = Atom→Prop stays
canonical." `Bridge.lean` is the natural host (it already imports both `Algebra` and `Bool` and
sits at the convergence point in `Cslib.lean`).

### Gap 3 — Missing convenience lemma linking classical `Tautology` to `BAValid` (optional, additive)
`tautology_iff_boolEvaluate_true` links `Tautology ↔ Bool`, and `boolEvaluateEq` links
`Bool ↔ AlgEvaluate@Bool`, but there is **no single lemma** presenting classical validity in the
algebraic vocabulary, e.g. `tautology_iff_baValid : Tautology φ ↔ BAValid φ`. Note `BAValid`
quantifies over *all* Boolean algebras whereas `Tautology` is bivalent (the 2-element BA `Bool`).
The two directions:
- `BAValid φ → Tautology φ`: instantiate `BAValid` at `H := Bool`, then rewrite by `boolEvaluateEq`
  and `tautology_iff_boolEvaluate_true`. **Easy, self-contained.**
- `Tautology φ → BAValid φ`: this is *algebraic completeness for CPL*; it should compose existing
  results `prop_soundness_tautology`/classical completeness with `CPL.hilbert_alg_complete`
  (see `Semantics/Algebra/HilbertCompleteness.lean` line 166 and
  `HilbertStrongCompleteness.lean`). Verify the exact statement of `hilbert_alg_complete` before
  committing to a one-line proof; if the round-trip is not immediately available, ship only the
  easy direction as `baValid_imp_tautology` and leave the iff as a documented roadmap note rather
  than introducing any debt.

### Gap 4 — DPLL/SAT entry point not surfaced as "canonical"
`instDecidableTautology` + `BoolEvaluate` are the computable decision path, but nothing in the
docstrings explicitly says "this is the canonical hook a DPLL/Tseitin procedure refines." Matthew
Doty's DPLL/Tseitin development is **not yet in the repo** (grep for DPLL/Tseitin/CNF finds only
unrelated Bimodal and literature hits), so coordination is forward-looking: leave a clearly-named
anchor (`BoolEvaluate`, `instDecidableTautology`) and a docstring pointer so the future DPLL work
plugs in without re-deriving the Bool/Prop bridge.

## Recommended Implementation Direction (concrete)

Primarily documentation; at most one small additive lemma. All changes are zero-debt.

1. **Fix `Bridge.lean` docstring drift** (`Semantics/Algebra/Bridge.lean`): replace
   `prop_evaluate_eq` → `propEvaluateEq` and `bool_evaluate_eq` → `boolEvaluateEq`
   (lines 22, 25, 31, 36).

2. **Expand the `Bridge.lean` module docstring into the canonical "ONE story"** with a table:
   | Evaluator | Type | Valuation | Role | `AlgEvaluate` specialization |
   |-----------|------|-----------|------|------------------------------|
   | `Evaluate` | `Prop` | `Valuation = Atom→Prop` | uniformity with Kripke; soundness/completeness stated here | `AlgEvaluate · False` @ `Prop` (Heyting) — `propEvaluateEq` |
   | `BoolEvaluate` | `Bool` | `BoolValuation = Atom→Bool` | computable decision (DPLL/SAT) | `AlgEvaluate · false` @ `Bool` (Boolean) — `boolEvaluateEq` |
   | `AlgEvaluate` | GHA `H` | `Atom→H` + `bot_val` | common generalization; tiered soundness/completeness | — |
   Include the soundness-chain diagram above and an explicit "Valuation stays `Atom→Prop`
   (canonical model construction needs it)" note.

3. **Add cross-reference pointers** in the three host docstrings:
   - `Semantics/Bool.lean` "Design Notes": point at `boolEvaluateEq`/`propEvaluateEq` and name
     `BoolEvaluate` + `instDecidableTautology` as the canonical DPLL/SAT decision path.
   - `Semantics/Algebra.lean` "Main Definitions": note that `AlgEvaluate` specializes to `Evaluate`
     (`propEvaluateEq`) and `BoolEvaluate` (`boolEvaluateEq`).

4. **(Optional, additive) add `baValid_imp_tautology`** (and, if the completeness round-trip is
   readily available, the full `tautology_iff_baValid`) in `Semantics/Algebra/Bridge.lean`. Verify
   the exact name/signature of `CPL.hilbert_alg_complete` first via `lean_local_search` /
   `lean_hover_info`. If the iff is not a clean one-liner, ship only the easy direction — do NOT
   force it and do NOT add a sorry.

### Files to touch
- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` (docstring fix + expansion; optional lemma)
- `Cslib/Logics/Propositional/Semantics/Bool.lean` (docstring cross-refs only)
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` (docstring cross-refs only)

### Reuse candidates (verify exact signatures before use)
- `CPL.hilbert_alg_complete` / `IPL.hilbert_alg_complete` / `MPL.hilbert_alg_complete`
  (`Semantics/Algebra/HilbertCompleteness.lean`) — for the `Tautology → BAValid` direction.
- `prop_soundness_tautology` (`Metalogic/Soundness.lean`) and the classical completeness theorem
  for the `Tautology ↔ Derivable` half.
- `FragmentPredicates.lean` `coe_AlgEvaluate`-style homomorphism-transport lemmas (lines ~290–355)
  if any algebra-to-algebra transport is needed.

## Constraints / Standards Notes
- Lint: any new lemma needs a docstring (docBlame), lowerCamelCase name (defsWithUnderscore — this
  is exactly why `propEvaluateEq` is not `prop_evaluate_eq`), and `lemma`/`theorem` (defLemma).
- Every touched file already imports `Cslib.Init`; preserve `module` / `@[expose] public section`.
- After edits run `lake build Cslib.Logics.Propositional.Semantics.Algebra.Bridge` then the CI
  pipeline (`lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`).

## Risk / Effort
- Low risk, low effort. Documentation-only path is trivially correct and zero-debt.
- Only nontrivial item is the optional `tautology_iff_baValid` round-trip; the easy direction is
  safe, the hard direction must be verified against existing completeness lemmas, never sorried.
- No blockers. Not blocked on Matthew's DPLL work (forward-looking anchor only).
