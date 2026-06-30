# Research Report: Reconcile Parallel Int/Min Decidability Routes (Tableau vs FMP)

**Task**: 422
**Type**: cslib (Lean 4)
**Status**: researched
**Date**: 2026-06-29

## Executive Summary

CSLib has two registered `instance`s for each of `Decidable (Derivable IntPropAxiom φ)`
and `Decidable (Derivable MinPropAxiom φ)`:

| Route | Declaration | File | Computable? | Sorry status | Type-class needs |
|-------|-------------|------|-------------|--------------|------------------|
| Tableau (Int) | `instDecidableDerivableIntPropAxiom` | `Tableau/Intuitionistic/DecisionProcedure.lean:80` | yes (`instance`) | **sorry-tainted** (task 317) | `[DecidableEq Atom] [Hashable Atom]` |
| Tableau (Min) | `instDecidableDerivableMinPropAxiom` | `Tableau/Minimal/DecisionProcedure.lean:81` | yes (`instance`) | **sorry-tainted** (task 317) | `[DecidableEq Atom] [Hashable Atom]` |
| FMP (Int) | `instDecidableDerivableIntPropAxiom'` | `Metalogic/IntDecidability.lean:430` | no (`noncomputable instance`) | **sorry-free** | `[DecidableEq Atom]` |
| FMP (Min) | `instDecidableDerivableMinPropAxiom'` | `Metalogic/MinDecidability.lean:382` | no (`noncomputable instance`) | **sorry-free** | `[DecidableEq Atom]` |

All four live in namespace `Cslib.Logic.PL`. The barrel `Cslib.lean` imports all four
(lines 424, 429, 517, 524), so both competing instances are simultaneously in scope for any
whole-library importer. **The instance-resolution hazard is confirmed and real.**

**Most important empirical finding**: there is currently **no consumer** — named or via
implicit resolution — of either `Decidable (Derivable IntPropAxiom φ)` or
`Decidable (Derivable MinPropAxiom φ)` anywhere in `Cslib/` or `CslibTests/`. The modal /
temporal / bimodal extensions do **not** build on these instances (see §2). Therefore the
hazard is **latent** (it bites the next `inferInstance`/`decide` against this head, e.g. in a
future downstream file or test), not an active breakage. This makes the reconciliation a
low-risk, mostly-documentation task.

## 1. Instance-Resolution Hazard (core issue)

### Confirmation

Both FMP declarations are registered as `noncomputable instance` (verified by reading lines
430 / 382). Both tableau declarations are plain `instance` (lines 80 / 81). All produce the
identical instance head `Decidable (Derivable {Int,Min}PropAxiom φ)` in the same namespace.

When `Atom` has both `DecidableEq` and `Hashable` (the common case), all conditions for both
instances are met and Lean's resolution picks one by priority, then by recency/import order —
ambiguous and fragile. Critically, the FMP instance is `noncomputable`: if resolution selects
it for a `decide`/`#eval`/kernel-reduction context, that computation **fails to reduce**.
Conversely the tableau instance currently carries `sorryAx` (task 317), so selecting it makes
the resolved `Decidable` axiom-tainted until 317 lands.

### Downstream consumers (who could break)

- **Extensions (Modal / Temporal / Bimodal / LTL)**: `FromPropositional.lean` and the
  `Embedding/*.lean` files import `Cslib.Logics.Propositional.Embedding`, which imports only
  `Cslib.Logics.Propositional.Defs` (syntax/semantics). They do **not** import either
  decidability module and contain **no** reference to `Decidable (Derivable …)`,
  `IValid`/`MValid`, or the propositional tableau. The `decide (…)` occurrences in
  Temporal/Bimodal metalogic are `decide (y ≠ φ)` (DecidableEq on formulas) and the *separate*
  Bimodal tableau (`Bimodal/Metalogic/Decidability/*`) — unrelated to this head.
  **Conclusion: no extension consumer exists; changing resolution cannot break the extensions.**
- **`SequentCalculus/LJ/Decidability.lean`**: consumes `instDecidableIValid` (the `IValid`
  head — a *different* type), not the `Derivable IntPropAxiom` head. Unaffected.
- **No `inferInstance` / `by decide` / term-level use** of the two conflicting heads in the
  whole repo or test suite (grep returned nothing).

### Idiomatic resolution in this codebase

`grep "instance (priority"` returns exactly 3 hits — all `priority := 100`, all for genuine
typeclass-hierarchy diamond disambiguation (`Foundations/Logic/Connectives.lean:206`,
`Foundations/Order/HilbertAlgebra.lean:224`, `Foundations/Order/BrouwerianSemilattice.lean:260`).
**Priority annotations are never used in CSLib to disambiguate two competing proofs of the
same `Decidable` head.** The idiomatic move is therefore **not** an instance-priority hack but
to register exactly **one** `instance` and expose the other result as a named non-instance
`def`/`theorem`.

### Recommendation (canonical instance)

Keep the **tableau** instances (`instDecidableDerivableIntPropAxiom`,
`instDecidableDerivableMinPropAxiom`) as the sole registered, canonical, extension-facing
`instance`s, and **demote the FMP ones to named `noncomputable def`** (see §2 for names). This:
- honours the user's stated routing decision (tableau feeds the logic extensions);
- preserves a **computable** canonical `Decidable` (the FMP one is `noncomputable` and would
  break `decide`);
- loses nothing on the FMP side, because the headline FMP results are already the named
  theorems `int_fmp` / `min_fmp`; the demoted `def` still exposes the decision procedure by name.

**Documented caveat (must appear in the docstrings)**: the canonical tableau instance inherits
task 317's sorries until 317 lands, so the library's resolved `Decidable (Derivable IntPropAxiom φ)`
is axiom-tainted in the interim, whereas the demoted FMP `def` is sorry-free and available by
name as a clean alternative. This is a pre-existing 317 debt, **not** new debt introduced by 422.

**Alternative for the planner/user to weigh (zero-debt-leaning)**: if a sorry-free *resolved*
instance is preferred over computability+routing, swap the roles — register the FMP one as the
canonical `instance` and demote the tableau one to a `def`. I recommend the tableau-canonical
option above per the task's stated preference, but flag this alternative because the sorry-free
property is a legitimate competing consideration. Either way, exactly one `instance` should
remain registered for each head.

## 2. Naming

The primed names `instDecidableDerivableIntPropAxiom'` / `instDecidableDerivableMinPropAxiom'`
are placeholders. On demotion to non-instance `def`s:

- `Metalogic/IntDecidability.lean:430` → `noncomputable def decidableDerivableIntPropAxiomFMP`
- `Metalogic/MinDecidability.lean:382` → `noncomputable def decidableDerivableMinPropAxiomFMP`

**Lint note (must heed)**: `Decidable` is *data* (an inductive with `isTrue`/`isFalse`), not a
`Prop`, so these stay `def` (not `lemma`/`theorem`). CSLib `defsWithUnderscore` lint forbids
underscores in `def` names, so the task's suggested `…_fmp` suffix is **not** lint-clean for a
`def`; use the camelCase acronym suffix `…FMP` (or `…ViaFMP`). The headline FMP biconditionals
`int_fmp` / `min_fmp` are **theorems** (snake_case is fine for Prop-valued declarations) and
need no rename. The canonical tableau instances are already well-named (no prime) — leave them.

## 3. Docstrings — the "two routes, distinct roles" narrative

Add a cross-referencing block to all four module headers. The narrative each should carry:

- **Two independent decision routes exist** for `Derivable {Int,Min}PropAxiom`:
  1. **Tableau route** (`Tableau/{Intuitionistic,Minimal}/DecisionProcedure.lean`): a
     constructive signed-tableau proof-search / countermodel procedure; **computable**; this is
     the canonical extension-facing `instance`. *Becomes genuinely sorry-free only once task
     317 lands* — cite the open obligations:
     `Tableau/Intuitionistic/Scheme.lean:246` (parametric `truthLemma`),
     `Tableau/Intuitionistic/Scheme.lean:519` (open-branch countermodel structural),
     `Tableau/Intuitionistic/Completeness.lean:113` (`IValid → forcing` bridge),
     `Tableau/Minimal/Completeness.lean:110` (`MValid → forcing` bridge; Minimal reuses the
     shared parametric `truthLemma minScheme`, so it also depends on Scheme.lean:246).
  2. **FMP route** (`Metalogic/{Int,Min}Decidability.lean`): a distinct theoretical result —
     the **finite model property** via the finite canonical Kripke model
     (`{Int,Min}FinWorld φ`). **Sorry-free**, depending only on
     `{propext, Classical.choice, Quot.sound}`. Exposed as the theorems `int_fmp` / `min_fmp`
     and the `noncomputable def decidableDerivable…PropAxiomFMP` (not a registered instance, to
     avoid competing with the canonical tableau instance).
- Each header **cross-references the other route's module + declaration name** and states the
  role split (constructive/extension-facing vs theoretical/finite-model-property).

Module headers to edit: `Metalogic/IntDecidability.lean`, `Metalogic/MinDecidability.lean`,
`Tableau/Intuitionistic/DecisionProcedure.lean`, `Tableau/Minimal/DecisionProcedure.lean`.
(The tableau headers already have a "Notes on sorry" section citing 317 — extend, don't
duplicate.)

## 4. Infrastructure relationship (factor vs cross-reference)

### The two world types
- **FMP**: `IntFinWorld φ` / `MinFinWorld φ` — `Finset`-carrier, `Σ`-bounded (Σ = φ.subformulas)
  prime deductively-closed worlds; `Fintype` via injection into `2^Σ`; preorder = carrier ⊆.
- **Tableau**: signed-formula branches (`IBranch`, signed `T(φ)`/`F(φ)` with `Nat` world
  labels), Hintikka-style saturation, `intExtractValuation b` reading a valuation off a branch.

These are **structurally different carriers** (model-theoretic finite prime worlds vs
proof-search branch valuations).

### The two truth lemmas
- `int_fin_truth_lemma` / `min_fin_truth_lemma` (FMP, `IntDecidability.lean:275` /
  `MinDecidability.lean:240`): `IForces …FinVal …BotForces w ψ ↔ ψ ∈ w.carrier`, structural
  induction on ψ over a fixed finite world; **sorry-free**.
- parametric `truthLemma S b …` (tableau, `Scheme.lean:232`): forcing of `intExtractValuation b`
  at Nat-labelled worlds ↔ presence of the signed formula on branch `b`; **317-owned sorry**.

They prove analogous "forcing ↔ membership" statements but over disjoint carrier types and
with opposite completion status (FMP complete; tableau parametric/deferred).

### Shared substrate
The **FMP route** rests on the infinite-canonical-model Lindenbaum machinery in
`Metalogic/IntLindenbaum.lean` (`int_imp_witness`, `int_prime_exclusion`, `intDeductiveClosure`,
and Min analogues) — reused to build the finite world by restriction to Σ. The **tableau
route does not use Lindenbaum**; it is an independent subsystem (signed tableaux + branch
saturation). So the genuinely shared infrastructure between the two routes is **small** — only
the Lindenbaum/prime-exclusion lemmas that FMP imports from the strong-completeness chain.

### Recommendation: document + cross-reference, do NOT factor
Factoring a common truth-lemma abstraction would couple two independently-developed subsystems
across a carrier mismatch, and would have to thread through the still-open task-317 parametric
lemma — high risk, low payoff. **Defer any factoring** (research-or-defer outcome: defer). The
in-scope action for 422 is to add cross-reference docstrings linking the two truth lemmas and
noting the shared Lindenbaum substrate. Do **not** attempt a heavy refactor under 422.

## 5. Recommended Phase Breakdown

All phases: zero new sorries, zero new axioms, CI green. Pre-existing 317 sorries are out of
scope and must not be touched.

- **Phase 1 — Demote + rename FMP instances** (`IntDecidability.lean`, `MinDecidability.lean`):
  change `noncomputable instance instDecidableDerivableIntPropAxiom'` →
  `noncomputable def decidableDerivableIntPropAxiomFMP` (and Min analogue). Update the in-file
  docstring + "Main Results" list lines (29). **Verification gate**: grep confirms no
  `inferInstance`/`decide`/named use of the demoted symbols breaks; `lake build` green; the
  canonical instance the barrel resolves for `Decidable (Derivable IntPropAxiom φ)` is now
  unambiguously the tableau one (no competing instance). Because no consumer exists, resolution
  change is a no-op functionally — confirm via build, not just reasoning.
- **Phase 2 — "Two routes" docstrings** across all four module headers (§3), with mutual
  cross-references and the 317 sorry citations + FMP axiom profile.
- **Phase 3 — Infrastructure cross-reference docstrings** (§4): link `int_fin_truth_lemma` ↔
  parametric `truthLemma`, note the shared `IntLindenbaum` substrate; record the explicit
  "factoring deferred" decision. (Research-or-defer: **defer** the refactor.)
- **Phase 4 — Verification / CI**: `lake build`; `lake exe checkInitImports`; `lake lint`
  (watch `defsWithUnderscore` on the new `def` names, `docBlame` on any new decl);
  `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix`; `lake test`.
  Run `lean_verify` (axiom check) on `decidableDerivableIntPropAxiomFMP` (expect
  `{propext, Classical.choice, Quot.sound}`, no `sorryAx`) and on the canonical tableau instance
  (expect `sorryAx` present until 317 — documents the caveat). Confirm zero new sorries via
  full-repo `grep sorry` diff.

### Risk / Defer notes
- Demotion is safe (no consumers). The only behavioural change is which instance resolves, and
  there is nothing to resolve against today.
- Factoring of truth-lemma/world infrastructure is **deferred** (risky cross-subsystem refactor
  blocked behind open task 317).
- 422 introduces no sorries/axioms; the canonical instance's sorry-taint is pre-existing
  317 debt and is documented, not newly introduced.

## Reuse Check (CSLib reuse-first)
- No new abstraction is recommended. The fix is demotion + documentation, reusing existing
  declarations (`int_fmp`/`min_fmp` already exist as the headline FMP theorems).
- No new notation. No new typeclass. Instance-priority machinery exists but is **not**
  idiomatic for this case (used only for hierarchy diamonds) — avoided.

## Open Questions for Planner/User
1. Canonical choice: tableau (recommended, per user routing + computability) vs FMP
   (sorry-free). §1 documents both; planner should confirm tableau-canonical before Phase 1.
2. Acronym casing of the demoted def: `…FMP` (recommended) vs `…ViaFMP`.
