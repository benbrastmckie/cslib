# Research Report: Task 343 — Canonical `v ⊨ T` Satisfaction Predicate

**Task**: Establish the canonical theory-satisfaction predicate `v ⊨ T` for propositional
logic on the Hilbert/algebraic substrate, generic over an already-applied evaluator, keeping
cslib's primitive `.bot` language and the `bot_val` parameter. Rewire `GHAValid`/`HAValid`/
`BAValid` (Algebra.lean) and `SemanticEntails`/`ISemanticEntails`/`MSemanticEntails`
(SemanticConsequence.lean) to factor through it. Keep task 341's Hilbert proofs untouched via
definitional equality. CI green.

**Status**: researched

---

## 1. Executive Summary

The task is a clean refactor enabled by definitional equality. The new generic predicate

```lean
def SatisfiesTheory {β : Type*} [Top β] (eval : Proposition Atom → β) (T : Theory Atom) : Prop :=
  ∀ A ∈ T, eval A = ⊤
```

is **definitionally equal** to the current `AlgTValid` body when `eval := AlgEvaluate v bot_val`.
By redefining `AlgTValid T v bot_val := SatisfiesTheory (AlgEvaluate v bot_val) T`, every existing
consumer of `AlgTValid`/`v ⊨[bot_val] T` (from task 341) continues to typecheck by `rfl`, because
the elaborated proposition `∀ B ∈ T, AlgEvaluate v bot_val B = ⊤` is unchanged. No proof in
HilbertLindenbaum.lean, Soundness.lean, or HilbertCompleteness.lean needs editing.

The single design subtlety: `SatisfiesTheory` is generic over the **eval function**, so its return
type `β` must carry a `⊤`. For the four target evaluators:
- `AlgEvaluate` → `β = H` (GHA), has `⊤` from `GeneralizedHeytingAlgebra` (`OrderTop`).
- `Evaluate` (Prop) → `β = Prop`, `⊤ = True` (Prop has `Top` / `OrderTop`).
- `BoolEvaluate` (Bool) → `β = Bool`, `⊤ = true` (Bool has `Top`).
- Kripke `IForces val bot_forces w` → `β = Prop`, `⊤ = True`.

This is why generality over the **eval function** (not a bundled Model) is the right boundary: it
unifies four different return types under one `[Top β]` constraint without a record wrapper, and
preserves defeq with the existing `AlgTValid`.

**Recommendation**: Implement in two phases — (P1) introduce `SatisfiesTheory` + `Satisfies`
single-formula predicate + uniform `⊨` notation, redefine `AlgTValid` defeq, deprecate-alias
`v ⊨[bot_val] T`; (P2) rewire the six validity predicates to factor through `SatisfiesTheory`/the
generic eval where it reads cleanly, keeping behavior `rfl`-identical.

---

## 2. Existing Definitions and Exact Locations

### 2.1 Evaluators (the four to factor over)

| Evaluator | File | Line | Return type `β` | `⊤` source |
|---|---|---|---|---|
| `AlgEvaluate v bot_val` | `Semantics/Algebra.lean` | 90–96 | `H` (GHA) | `OrderTop` (GHA) |
| `Evaluate v` | `Semantics/Bool.lean` | 57–62 | `Prop` | `Prop` `Top` (`True`) |
| `BoolEvaluate v` | `Semantics/Bool.lean` | 90–95 | `Bool` | `Bool` `Top` (`true`) |
| `IForces val bf w` | `Semantics/Kripke.lean` | 81–88 | `Prop` | `Prop` `Top` (`True`) |

All have `@[simp]` per-constructor unfolding lemmas immediately following each def (e.g.
`AlgEvaluate_atom`..`AlgEvaluate_or` at Algebra.lean:98–119; `Evaluate_atom`..`Evaluate_or` at
Bool.lean:64–77; etc.). These are unaffected.

### 2.2 The predicate to generalize

`AlgTValid` — `Semantics/Algebra.lean:149–151`:
```lean
def AlgTValid {H : Type*} [GeneralizedHeytingAlgebra H]
    (T : PL.Theory Atom) (v : Atom → H) (bot_val : H) : Prop :=
  ∀ B ∈ T, AlgEvaluate v bot_val B = ⊤
```

Notation — `Semantics/Algebra.lean:153–156`:
```lean
scoped notation:50 v " ⊨[" bot_val "] " T:50 => AlgTValid T v bot_val
```

### 2.3 Validity predicates to rewire (Algebra.lean)

- `GHAValid` — Algebra.lean:126–128: `∀ H [GHA H] v bot_val, AlgEvaluate v bot_val φ = ⊤`
- `HAValid`  — Algebra.lean:133–135: `∀ H [HeytingAlgebra H] v, AlgEvaluate v ⊥ φ = ⊤`
- `BAValid`  — Algebra.lean:140–142: `∀ H [BooleanAlgebra H] v, AlgEvaluate v ⊥ φ = ⊤`

These are **single-formula** validity (quantify over algebras), not theory satisfaction. They
factor through the single-formula `Satisfies` predicate (`eval φ = ⊤`), not `SatisfiesTheory`.

### 2.4 Semantic consequence predicates to rewire (SemanticConsequence.lean)

- `SemanticEntails`  — SemanticConsequence.lean:127–130: `∀ v, (∀ ψ ∈ Γ, Evaluate v ψ) → Evaluate v φ`
- `ISemanticEntails` — :137–143: Kripke, `bot_forces = fun _ => False`
- `MSemanticEntails` — :150–158: Kripke, arbitrary upward-closed `bot_forces`

Note: these use `Prop`-valued forcing where "satisfied" = the Prop holds (i.e. `= True`), not an
explicit `= ⊤`. See §5.2 for the rewiring nuance.

### 2.5 Task-341 consumers that MUST stay untouched (defeq targets)

- `alg_theory_soundness` — `Semantics/Algebra/Soundness.lean:200–221`. Uses `hT : v ⊨[bot_val] AxiomTheory Axioms` and applies `hT ψ (...) : AlgEvaluate v bot_val ψ = ⊤` at line 210.
- `canonicalV_algTValid` — `Semantics/Algebra/HilbertLindenbaum.lean:636–639`. Body `intro B hB; exact canonicalV_axiom_top ...` produces `∀ B ∈ T, ... = ⊤`.
- `hilbert_alg_complete_theory` — `Semantics/Algebra/HilbertCompleteness.lean:64–79`. The statement embeds `v ⊨[bot_val] AxiomTheory Axioms → AlgEvaluate v bot_val φ = ⊤` (line 69).
- `MPL/IPL/CPL.hilbert_alg_complete` — HilbertCompleteness.lean:93–151. Discharge `AlgTValid` via `min/int/prop_alg_axiom_sound`.

All four rely only on (a) the application form `hT ψ hψ : eval ψ = ⊤` and (b) `intro`/`exact` on
the unfolded `∀ B ∈ T, eval B = ⊤`. Both survive the redefinition because `SatisfiesTheory eval T`
reduces to exactly that.

### 2.6 Reuse check (CSLib reuse-first)

- **No** `Satisfies`/`SatisfiesTheory` exists in `Cslib.Foundations.*` for the propositional/algebraic
  evaluator shape. `Cslib/Foundations/Semantics/LTS/NAProd.lean` mentions "Satisfies" only in LTS
  context (unrelated).
- `Cslib.Logics.Modal.Basic.Satisfies` (Modal/Basic.lean:145) is a Kripke modal `Model`-bundled
  predicate `Model → World → Proposition → Prop` — **different shape** (bundled model, has box case).
  Out of scope per the generality boundary (EXCLUDE cross-logic Modal/Temporal/LTL). Do not unify.
- `⊨` notation already exists but **scoped** to other namespaces:
  - `Cslib.Logics.Bimodal` (Validity.lean:60,81) — `⊨ φ` and `Γ ⊨ φ`, scoped.
  - `Cslib.Logics.Modal.Basic` (line 201) — `Modal[m,w ⊨ φ]`, scoped.
  - The current PL bracket form `v ⊨[bot_val] T` (Algebra.lean:156), scoped.
  None collide with a new `scoped notation` in `Cslib.Logic.PL`, since cslib uses `scoped`
  (namespace-local) notations. The uniform `v ⊨ A` / `v ⊨ S` / `v ⊨ T` must be `scoped` in
  `Cslib.Logic.PL` to avoid global clashes.

---

## 3. Recommended New Definitions (Lean code sketches)

Place these in `Semantics/Algebra.lean` (the substrate file that already owns `AlgTValid`), or a
small shared location imported by both Algebra.lean and SemanticConsequence.lean. Since
SemanticConsequence.lean does **not** currently import Algebra.lean, and to keep `SatisfiesTheory`
generic (not GHA-specific), the cleanest home is a new tiny section in `Defs.lean` (already defines
`Theory`) OR keep the generic predicate in `Defs.lean` and `AlgTValid` redefinition in Algebra.lean.
Recommended: **put `Satisfies`/`SatisfiesTheory` + notation in `Defs.lean`** (universally available,
only needs `Top`), then redefine `AlgTValid` in Algebra.lean.

### 3.1 Generic single-formula and theory satisfaction (Defs.lean)

```lean
namespace Cslib.Logic.PL

variable {Atom : Type*}

/-- A formula `A` is satisfied by an (already-applied) evaluator `eval` iff `eval A = ⊤`.
Generic over the evaluator's codomain `β`, which need only have a top element. Instantiated by
`Evaluate` (`β = Prop`), `BoolEvaluate` (`β = Bool`), `AlgEvaluate v bot_val` (`β = H` a GHA),
and Kripke `IForces` (`β = Prop`). The `bot_val` (for the algebraic case) rides inside `eval`,
never in this signature. -/
def Satisfies {β : Type*} [Top β] (eval : Proposition Atom → β) (A : Proposition Atom) : Prop :=
  eval A = ⊤

/-- A theory `T` is satisfied by an (already-applied) evaluator `eval` iff every formula in `T`
is satisfied. This is Waring's `v ⊨ T` shape (`Semantics/Heyting.lean`'s `TValid`), specialized
to cslib's primitive `.bot` language: `bot_val` is carried inside `eval`. -/
def SatisfiesTheory {β : Type*} [Top β] (eval : Proposition Atom → β) (T : Theory Atom) : Prop :=
  ∀ A ∈ T, eval A = ⊤   -- ≡ ∀ A ∈ T, Satisfies eval A

@[inherit_doc] scoped notation:50 eval:50 " ⊨ " A:50 => Satisfies eval A
@[inherit_doc] scoped notation:50 eval:50 " ⊨ " T:50 => SatisfiesTheory eval T
```

**Notation overlap caveat (IMPORTANT)**: `Satisfies eval A` and `SatisfiesTheory eval T` cannot
share the *same* `notation` token shape `eval ⊨ X` because Lean cannot disambiguate `A : Proposition`
vs `T : Theory` from the `⊨` token alone (both are right-hand args). Two resolutions, in order of
preference:

1. **Overloaded notation via distinct elaborators is NOT reliable** here. Instead, declare ONE
   notation backed by a `HasSatisfies`-style class, OR accept that `v ⊨ A` and `v ⊨ T` need the
   reader to rely on expected-type elaboration. Simplest robust approach: keep them as the same
   `⊨` token and let Lean's `notation` overloading pick by expected type of the RHS. Lean *does*
   allow multiple `notation` with identical syntax that desugar to different functions; elaboration
   tries each and keeps the one that typechecks (`Proposition Atom` vs `Theory Atom = Set (...)`).
   These types are disjoint, so disambiguation succeeds. **Recommend prototyping both notations and
   confirming with `lake build` that `v ⊨ A` (A : Proposition) and `v ⊨ T` (T : Set _) both elaborate.**
2. If overloading proves brittle, give the theory form a distinct token, e.g. keep `v ⊨ A` for
   formulas and use `v ⊨ T` only after confirming, or fall back to `eval ⊨ᵀ T`. The task explicitly
   wants uniform `v ⊨ A / v ⊨ S / v ⊨ T`; pursue option 1 first.

> Note `v ⊨ S` in the task: `S` denotes a set/sequent context (also `Set (Proposition Atom)`),
> identical type to `Theory`, so it reuses `SatisfiesTheory`. No third predicate needed.

### 3.2 Redefine `AlgTValid` definitionally (Algebra.lean:149–151)

```lean
/-- A valuation `v` with bottom value `bot_val` models a theory `T` if every axiom of `T`
evaluates to `⊤`. Definitionally `SatisfiesTheory (AlgEvaluate v bot_val) T`; the `bot_val`
rides inside the applied evaluator. Task 341's Hilbert proofs are untouched (defeq). -/
def AlgTValid {H : Type*} [GeneralizedHeytingAlgebra H]
    (T : PL.Theory Atom) (v : Atom → H) (bot_val : H) : Prop :=
  SatisfiesTheory (AlgEvaluate v bot_val) T
```

This is `rfl`-equal to the old body. **Verification**: `SatisfiesTheory (AlgEvaluate v bot_val) T`
unfolds (by `def`) to `∀ A ∈ T, AlgEvaluate v bot_val A = ⊤`, identical to the prior definition
modulo the bound-variable name (`A` vs `B`, irrelevant). `alg_theory_soundness`'s `hT ψ (...)` and
`canonicalV_algTValid`'s `intro B hB` both still elaborate.

### 3.3 Deprecate / alias the bracket notation (Algebra.lean:156)

The task says "deprecate/alias `v ⊨[bot_val] T`". Two options:

- **Keep the bracket notation as an alias** (zero churn, recommended initially): leave the existing
  `scoped notation:50 v " ⊨[" bot_val "] " T:50 => AlgTValid T v bot_val`. Since `AlgTValid` now
  factors through `SatisfiesTheory`, the bracket form still works and equals
  `AlgEvaluate v bot_val ⊨ T`. Add a docstring note marking it legacy.
- **Migrate consumers** to `AlgEvaluate v bot_val ⊨ T` and remove the bracket notation. There are
  exactly 3 *code* uses (HilbertLindenbaum.lean:638, Soundness.lean:206, HilbertCompleteness.lean:69)
  plus doc mentions. All would change from `v ⊨[bot_val] X` to `AlgEvaluate v bot_val ⊨ X`. This is
  the cleaner end-state but touches 341 statement text (still defeq, proofs unchanged).

**Recommendation**: For zero-debt + "341 unchanged", keep the bracket as a deprecated alias in P1;
optionally migrate in a follow-up. Do NOT delete it in the same change that must keep 341 untouched.

---

## 4. Defeq Strategy (keeping task 341 proofs untouched)

The invariant is: the **fully-elaborated `Prop`** behind every 341 statement must be unchanged.

1. `AlgTValid T v bot_val` redefined as `SatisfiesTheory (AlgEvaluate v bot_val) T`
   → unfolds to `∀ A ∈ T, AlgEvaluate v bot_val A = ⊤` (the old body). **defeq ✓**
2. The bracket notation `v ⊨[bot_val] T => AlgTValid T v bot_val` is unchanged → same elaboration.
3. `alg_theory_soundness` (Soundness.lean:200): uses `hT : v ⊨[bot_val] AxiomTheory Axioms`, applies
   `hT ψ h` expecting `AlgEvaluate v bot_val ψ = ⊤`. Application of `SatisfiesTheory`-based `hT` to
   `ψ` and a membership proof yields exactly that (reduces through the `∀ A ∈ T, ...`). **✓**
4. `canonicalV_algTValid` (HilbertLindenbaum.lean:636): body `intro B hB; exact ...` introduces the
   `∀ A ∈ T` binder; reduces identically. **✓**
5. `hilbert_alg_complete_theory` and the three tier theorems: statements embed `v ⊨[bot_val] ...`
   which now routes through `SatisfiesTheory`; proofs use `.mp`/instantiation + the discharge lemmas;
   all defeq. **✓**

**No `rfl` bridge lemmas, no `simp` lemmas, no axioms required.** This is the strict zero-debt
path: a definitional refactor.

**Risk note**: If `Satisfies`/`SatisfiesTheory` were marked `@[irreducible]` or placed behind a
non-`@[expose]` boundary, defeq could break for the consumers. Algebra.lean and Defs.lean both use
`@[expose] public section`; ensure the new defs live inside an `@[expose] public section` (Defs.lean
line 1 region already is) so reducibility is preserved across modules.

---

## 5. Rewiring the Six Validity Predicates

### 5.1 Algebra.lean — `GHAValid`/`HAValid`/`BAValid` (single-formula)

These quantify over algebras and assert `AlgEvaluate ... φ = ⊤`, i.e. `Satisfies (AlgEvaluate v bv) φ`.
Rewire to factor through `Satisfies`:

```lean
def GHAValid (φ : Proposition Atom) : Prop :=
  ∀ (H : Type*) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
    AlgEvaluate v bot_val ⊨ φ          -- ≡ AlgEvaluate v bot_val φ = ⊤

def HAValid (φ : Proposition Atom) : Prop :=
  ∀ (H : Type*) [HeytingAlgebra H] (v : Atom → H), AlgEvaluate v (⊥ : H) ⊨ φ

def BAValid (φ : Proposition Atom) : Prop :=
  ∀ (H : Type*) [BooleanAlgebra H] (v : Atom → H), AlgEvaluate v (⊥ : H) ⊨ φ
```

Each is defeq to the current body (`Satisfies eval φ := eval φ = ⊤`). The 341 completeness theorems
that consume `GHAValid`/`HAValid`/`BAValid` (HilbertCompleteness.lean:94,123,151) use them via
`intro`/instantiation that produces `AlgEvaluate ... φ = ⊤`; still defeq. **✓**

### 5.2 SemanticConsequence.lean — `SemanticEntails`/`ISemanticEntails`/`MSemanticEntails`

These are **Prop-valued** and currently written as "the forcing Prop holds", e.g.
`(∀ ψ ∈ Γ, Evaluate v ψ) → Evaluate v φ`, NOT `Evaluate v φ = ⊤`. Two rewiring options:

**Option A (minimal, recommended): factor the *premise* (theory-satisfaction) only.**
`Evaluate v ψ` (a `Prop`) is propositionally — and definitionally via `eq_true`/`iff` — equal to
`Evaluate v ψ = True = ⊤`, but NOT syntactically defeq in a way the existing `fun v hΓ => ...`
proofs would accept transparently. The hypothesis `∀ ψ ∈ Γ, Evaluate v ψ` is consumed as a
function `Γ-membership → Evaluate v ψ` in lemmas like `SemanticEntails_of_Tautology`
(SemanticConsequence.lean:163, `fun v _ => h v`). Replacing with `SatisfiesTheory (Evaluate v) Γ`
(= `∀ ψ ∈ Γ, Evaluate v ψ = ⊤`) changes the hypothesis type from `... → Prop` to `... → (_ = ⊤)`,
which would BREAK `fun v _ => h v` and the `of_*` lemmas (they ignore the premise, so actually safe)
but would break any consumer that *uses* the premise as a raw Prop.

→ **Therefore, for the Prop-valued entailments, do NOT force them through `SatisfiesTheory`'s
`= ⊤` shape in this task** unless you also migrate the consequent and all consumers. The cleaner
unification for Prop-valued forcing would require a `Satisfies`-for-Prop convention `eval φ` (no
`= ⊤`), which conflicts with the algebraic `= ⊤` convention.

**Option B (full unification, larger):** Introduce the notation `v ⊨ φ` for the Prop-forcing case
as plain `Evaluate v φ` / `IForces ... φ` (no `= ⊤`), distinct from the algebraic `= ⊤` `Satisfies`.
This gives uniform *notation* `v ⊨ A` across Prop/Bool/GHA/Kripke but two underlying predicates
(`eval φ` for Prop-forcing, `eval φ = ⊤` for valued). Risk of notation ambiguity.

**Recommendation for §5.2**: Scope task 343 to (a) the algebraic substrate `Satisfies`/`SatisfiesTheory`
+ `AlgTValid` defeq (the core deliverable), (b) rewire `GHAValid`/`HAValid`/`BAValid` (clean defeq),
and (c) for `SemanticEntails`/`ISemanticEntails`/`MSemanticEntails`, rewire **only the theory-premise**
using a Prop-level `SatisfiesTheory`-analog if and only if it stays defeq — otherwise document that
the Prop-valued entailments adopt the uniform `⊨` *notation* (`(∀ ψ ∈ Γ, v ⊨ ψ)`) where `v ⊨ ψ` for
Prop means `Evaluate v ψ`, and flag the convention split for the planner. This is a genuine design
fork; the planner should choose A or B. Per zero-debt, prefer **A** (smaller, no risk to 341, no
sorry) and leave full Prop/valued unification as an explicit roadmap item, NOT a sorry.

> The task framing ("This underpins the Hilbert completeness theorems") and the defeq mandate both
> point at the **algebraic** substrate as the load-bearing part. The Prop-valued entailment rewiring
> is secondary and should not jeopardize the defeq guarantee.

---

## 6. Generality Boundary (confirmed)

- **INCLUDE**: `Evaluate` (Prop, Bool.lean), `BoolEvaluate` (Bool, Bool.lean),
  `AlgEvaluate` (GHA, Algebra.lean), Kripke `IForces` (Kripke.lean). All five propositional
  evaluators share codomain-with-`⊤`, so `Satisfies`/`SatisfiesTheory` covers them uniformly.
- **EXCLUDE**: `Cslib.Logics.Modal.Basic.Satisfies` (bundled `Model`, has box case),
  Temporal, LTL, Bimodal. Their existing scoped `⊨` notations are namespace-local and do not
  conflict. Do not attempt cross-logic unification — it would force a bundled-Model abstraction,
  contradicting the "generic over the eval FUNCTION, not a bundled Model (defeq)" requirement.

---

## 7. Lint-Prevention Checklist (CSLib environment linters)

- **docBlame**: every new decl (`Satisfies`, `SatisfiesTheory`) needs a docstring — provided in §3.
- **defLemma**: `Satisfies`/`SatisfiesTheory` are `Prop`-valued. They are `def` (predicates), which
  is the established pattern in this file (`AlgTValid`, `GHAValid`, `SemanticEntails` are all `def`,
  not `lemma`). Match the file convention: use `def`. (defLemma targets `theorem`/`lemma` vs `def`
  for proofs, not for predicate definitions — predicates returning `Prop` are conventionally `def`
  here.)
- **defsWithUnderscore**: `SatisfiesTheory`, `AlgTValid` use lowerCamelCase/UpperCamelCase per the
  file's existing style (`AlgEvaluate`, `GHAValid`). No new underscores.
- **dupNamespace**: do not prefix names with `PL`/`Logic` inside `namespace Cslib.Logic.PL`.
- **topNamespace**: notation is `scoped`; keep inside `namespace Cslib.Logic.PL`.
- **simpNF**: do not add `@[simp]` to `Satisfies`/`SatisfiesTheory` (they are definitional; the
  existing `*_atom`/`*_imp` simp lemmas already drive evaluation). If an unfolding simp lemma is
  wanted, add `Satisfies_def`/`SatisfiesTheory_def` `:= Iff.rfl`/`rfl` and verify LHS.
- **unusedSectionVars**: `variable {Atom : Type*}` is used by both new defs.

---

## 8. Suggested Phase Decomposition (for planner)

**Phase 1 — Core predicate + defeq AlgTValid (load-bearing, zero-risk)**
1. Add `Satisfies` + `SatisfiesTheory` + scoped `⊨` notation in `Defs.lean` (inside
   `@[expose] public section`, `namespace Cslib.Logic.PL`).
2. Redefine `AlgTValid` (Algebra.lean:149) as `SatisfiesTheory (AlgEvaluate v bot_val) T`.
3. Keep `v ⊨[bot_val] T` bracket notation as a documented legacy alias.
4. `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness` — confirm 341
   proofs (Soundness, HilbertLindenbaum, HilbertCompleteness) still compile with **no edits**.

**Phase 2 — Rewire algebraic validity predicates (clean defeq)**
5. Rewrite `GHAValid`/`HAValid`/`BAValid` bodies to `AlgEvaluate ... ⊨ φ`.
6. `lake build` the Algebra subtree; confirm defeq holds for the tier completeness theorems.

**Phase 3 — Prop-valued entailments (design fork; choose Option A)**
7. Adopt uniform `⊨` notation for the theory-premise in `SemanticEntails`/`ISemanticEntails`/
   `MSemanticEntails` IF defeq-safe; otherwise document the convention split and leave full
   unification as a roadmap item (NOT a sorry, NOT an axiom).
8. Full CI: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`.

**Verification gate (zero-debt)**: zero `sorry`, zero new axioms, CI green, 341 files unedited
(git diff shows only Defs.lean + Algebra.lean defn bodies + optional SemanticConsequence.lean).

---

## 9. Open Questions / Decisions for Planner

1. **Notation overloading** (`v ⊨ A` vs `v ⊨ T`): must be empirically confirmed via `lake build`
   that Lean disambiguates `Proposition Atom` from `Theory Atom = Set (Proposition Atom)` by
   expected type. If brittle, fall back to a distinct theory token. (Prototype first.)
2. **Bracket notation fate**: alias-and-keep (recommended, 341-safe) vs migrate-and-remove
   (cleaner, touches 341 statement text but stays defeq). Planner to choose.
3. **Prop-valued entailment unification**: Option A (premise-only / notation-only, recommended) vs
   Option B (two predicates under one notation). This is the only non-mechanical decision.
4. **Home of generic predicate**: `Defs.lean` (recommended — only needs `Top`, universally imported)
   vs `Algebra.lean` (GHA-coupled, but SemanticConsequence.lean doesn't import it). Defs.lean wins
   because SemanticConsequence.lean already imports the chain that reaches Defs.lean.

---

## 10. Key File:Line Index

| Symbol | File | Line |
|---|---|---|
| `AlgEvaluate` | Cslib/Logics/Propositional/Semantics/Algebra.lean | 90 |
| `GHAValid` | …/Semantics/Algebra.lean | 126 |
| `HAValid` | …/Semantics/Algebra.lean | 133 |
| `BAValid` | …/Semantics/Algebra.lean | 140 |
| `AlgTValid` | …/Semantics/Algebra.lean | 149 |
| `v ⊨[bot_val] T` notation | …/Semantics/Algebra.lean | 156 |
| `Evaluate` | …/Semantics/Bool.lean | 57 |
| `Tautology` | …/Semantics/Bool.lean | 80 |
| `BoolEvaluate` | …/Semantics/Bool.lean | 90 |
| `IForces` | …/Semantics/Kripke.lean | 81 |
| `IValid` | …/Semantics/Kripke.lean | 145 |
| `MValid` | …/Semantics/Kripke.lean | 153 |
| `SemanticEntails` | …/Semantics/SemanticConsequence.lean | 127 |
| `ISemanticEntails` | …/Semantics/SemanticConsequence.lean | 137 |
| `MSemanticEntails` | …/Semantics/SemanticConsequence.lean | 150 |
| `Theory` (abbrev) | …/Propositional/Defs.lean | 142 |
| `alg_theory_soundness` | …/Semantics/Algebra/Soundness.lean | 200 |
| `canonicalV_algTValid` | …/Semantics/Algebra/HilbertLindenbaum.lean | 636 |
| `hilbert_alg_complete_theory` | …/Semantics/Algebra/HilbertCompleteness.lean | 64 |
| `MPL/IPL.hilbert_alg_complete` | …/Semantics/Algebra/HilbertCompleteness.lean | 93 / 122 |

(All paths under `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/`.)
