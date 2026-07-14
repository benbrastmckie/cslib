# Research Report: Task 491 — Minimal Propositional Base (efq-optional)

- **Task**: Make ex-falso-quodlibet (efq) an OPTIONAL rule of the propositional
  derivation system so the strength hierarchy `minimal ⊂ intuitionistic ⊂ classical`
  is cleanly representable.
- **Task type**: cslib
- **Session**: sess_1784044271_09e821_491
- **Date**: 2026-07-14
- **Status of finding**: The requested design is **already fully implemented in `main`**,
  using *both* mechanisms the task asks the report to recommend (a gated/typeclass-marker
  rule AND a parameterized axiom-predicate derivation). Recommend the implementation phase be
  reduced to **verification-only** or the task flagged **[BLOCKED] for user review** as a
  no-op tracking task. See Section 5.

---

## 0. Headline Answer (Step 1 of the task)

> Step 1: confirm whether #648 already admits a minimal base; if not, gate/parameterize
> the efq rule.

**Confirmed: the descendant of PR #648 on current `main` already admits a full minimal
base.** efq is not built in as a mandatory rule in *either* propositional proof system.
The task description reflects PR #648's *snapshot* (efq baked in, base = intuitionistic,
no minimal variant), but the codebase has since evolved well past that snapshot (via tasks
185, 187, 191, 367, 409, and others). No gating/parameterization work remains — it is done.

The strength hierarchy is representable **three independent ways**, all present and green:

| Encoding | Minimal | Intuitionistic | Classical | Location |
|----------|---------|----------------|-----------|----------|
| Hilbert axiom predicate | `MinPropAxiom` (8) | `IntPropAxiom` (9, +efq) | `PropositionalAxiom` (10, +efq +peirce) | `ProofSystem/Axioms.lean` |
| Bundled typeclass | `MinimalHilbert` | `IntuitionisticHilbert` (+`HasAxiomEFQ`) | `ClassicalHilbert` (+`HasAxiomPeirce`) | `Foundations/Logic/ProofSystem.lean` |
| ND theory + gated rule | `MPL = ∅` | `IPL` (`IsIntuitionistic`) | `CPL` (`IsClassical`) | `NaturalDeduction/Basic.lean`, `Defs.lean` |

Verification: `lake build Cslib.Logics.Propositional.ProofSystem.IntMinInstances
Cslib.Logics.Propositional.NaturalDeduction.Basic` → **Build completed successfully
(638 jobs).**

---

## 1. Where the Propositional Derivation System Lives

There are **two** propositional proof systems (documented in `Defs.lean` lines 39–54),
both bridged by `NaturalDeduction/Equivalence.lean`.

### 1.1 Core proposition type — primitive ⊥ (as #648 established)
`Cslib/Logics/Propositional/Defs.lean:81-92`

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot          -- primitive falsum ⊥
  | imp (a b : Proposition Atom)
  | and (a b : Proposition Atom)
  | or  (a b : Proposition Atom)
deriving DecidableEq, Repr
```
`neg A := A → ⊥`, `top := ⊥ → ⊥` are derived `abbrev`s. This is exactly the
"primitive-⊥ propositional Proposition" the task says it builds on.

### 1.2 Layer 1 — Natural Deduction (`NaturalDeduction/Basic.lean`)
`Theory.Derivation {T : Theory Atom} : Ctx → Proposition → Type` (line 146). Ten ungated
constructors (`ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE`) plus **one gated
constructor**:

```lean
| efq {Γ : Ctx Atom} {A : Proposition Atom} [IsIntuitionistic T] :
    Derivation Γ ⊥ → Derivation Γ A          -- Basic.lean:182
```

`efq` carries an `[IsIntuitionistic T]` instance argument, so it is *structurally
unconstructible* at minimal strength. Logic strength is selected by the theory parameter
`T`:
- `MPL := ∅` (Johansson minimal) — admits no `IsIntuitionistic` instance ⇒ efq gated off.
- `IPL := Set.range (⊥ → ·)` — has `IsIntuitionistic` ⇒ efq available. IPL = MPL + explosion.
- `CPL := Set.range (¬¬· → ·)` — adds DNE via `IsClassical`.

The gate-free fragment is named without a duplicate inductive:
- `Theory.Derivation.IsBotRuleFree` (line 223): recursive predicate, `efq ↦ False`.
- `Theory.MinimalDerivation Γ A := MPL.Derivation Γ A` (line 242).

### 1.3 Layer 2 — Hilbert System (`ProofSystem/`)
`Cslib/Logics/Propositional/ProofSystem/Derivation.lean` — `DerivationTree` is a `Type`
inductive **parameterized over an axiom predicate** `Axioms : PL.Proposition Atom → Prop`,
with exactly 4 constructors (`ax`, `assumption`, `modusPonens`, `weakening`). **efq is NOT
a constructor** — it enters only through whichever axiom family is supplied. `Deriv`,
`Derivable`, and `propDerivationSystem` are all parameterized over `Axioms`.

---

## 2. How efq and IsClassical/DNE Are Currently Structured

### 2.1 Hilbert axiom families (`ProofSystem/Axioms.lean`)
Three inductive `Prop`-valued predicates form a subsumption chain:
- `MinPropAxiom` (8 ctors: implyK, implyS, andI, andE1, andE2, orI1, orI2, orE) — **no efq,
  no peirce**.
- `IntPropAxiom` (9 ctors) — adds `efq (φ) : IntPropAxiom (Proposition.bot.imp φ)` (line 97).
- `PropositionalAxiom` (10 ctors) — adds `efq` **and** `peirce (φ ψ) : ...` (line 59) — Peirce
  is the classical primitive; DNE is derived from it.
- Subsumption theorems: `MinPropAxiom.toIntPropAxiom` (line 155),
  `IntPropAxiom.toPropAxiom` (line 168).

### 2.2 Foundations typeclass hierarchy (`Foundations/Logic/ProofSystem.lean`)
Per-axiom marker classes: `HasAxiomEFQ` (line 125), `HasAxiomPeirce` (line 129), etc.
Bundled three-level hierarchy (lines 341–358), each layer adding exactly the optional axiom:

```lean
class MinimalHilbert (S) …        extends ModusPonens, HasAxiomImplyK, HasAxiomImplyS
class IntuitionisticHilbert (S) … extends MinimalHilbert, HasAxiomEFQ
class ClassicalHilbert (S) …      extends IntuitionisticHilbert, HasAxiomPeirce
```

Opaque tag types (lines 490–497): `Propositional.HilbertMin`, `Propositional.HilbertInt`,
`Propositional.HilbertCl`.

### 2.3 Instance registration
- `ProofSystem/IntMinInstances.lean`: `HilbertInt` → `DerivationTree IntPropAxiom` with
  `IntuitionisticHilbert` instance; `HilbertMin` → `DerivationTree MinPropAxiom` with
  `MinimalHilbert` instance (note: **no** `HasAxiomEFQ` instance registered for `HilbertMin`).
- `ProofSystem/Instances.lean`: `HilbertCl` → `DerivationTree PropositionalAxiom` with
  `HasAxiomEFQ` + `HasAxiomPeirce` + `ClassicalHilbert`.

### 2.4 ND theory-level markers (`Defs.lean:164-206`)
```lean
class IsIntuitionistic (T : Theory Atom) where efq (A) : (⊥ → A) ∈ T
class IsClassical      (T : Theory Atom) where dne (A) : (¬¬A → A) ∈ T
```
with `isIntuitionisticIff : IsIntuitionistic T ↔ IPL ⊆ T`,
`isClassicalIff : IsClassical T ↔ CPL ⊆ T`, base instances `instIsIntuitionisticIPL` /
`instIsClassicalCPL`, and monotone-extension lemmas
`instIsIntuitionisticExtension` / `instIsClassicalExtension`.

### 2.5 IsMinimal marker (`NaturalDeduction/Equivalence.lean:177-267`)
The pattern is even completed on the minimal side:
- `minimal : Theory Atom := AxiomTheory MinPropAxiom` (the 8-schema axiom set).
- `abbrev IsMinimal (T) : Prop := MinimalAxioms (fun φ => φ ∈ T)` (line 189) — reuses the
  existing 8-field `MinimalAxioms` class rather than a duplicate.
- `isMinimalIff : IsMinimal T ↔ minimal ⊆ T`, `instIsMinimalExtension`,
  `instIsMinimalMinimal` — mirroring the `IsIntuitionistic`/`IsClassical` API exactly.

### 2.6 Downstream metalogic already stratified by strength
`Metalogic/` carries a full `Min*` / `Int*` / (classical) triple: `MinSoundness`,
`MinLindenbaum`, `MinStrongCompleteness`, `MinDecidability`; `IntSoundness`, `IntLindenbaum`,
`IntStrongCompleteness`, `IntDecidability`; plus classical completeness variants. Tableau
(`Tableau/Minimal|Intuitionistic|Classical`) and sequent calculus (`SequentCalculus/LJ|LK`)
are likewise stratified. `min_consistent : ¬ Derivable MinPropAxiom ⊥` (MinLindenbaum) is
the operational proof that the minimal base is genuinely efq-free.

---

## 3. Recommended Lean 4 Design (already realized — documented for the record)

The task asks to weigh "typeclass marker vs. parameterized Derivation variant". CSLib has
adopted **both**, each where it fits, and this is the design a fresh implementation *should*
target — so no change is warranted:

- **Hilbert layer → parameterized axiom predicate.** One `DerivationTree Axioms` inductive;
  strength = choice of `Min/Int/PropositionalAxiom`. Zero duplication of the derivation
  type; subsumption via `to*` lemmas; strength markers via the `MinimalHilbert ⊂
  IntuitionisticHilbert ⊂ ClassicalHilbert` extends-chain. This is the reuse-first ideal:
  the derivation engine is written once.

- **ND layer → single inductive with a typeclass-gated rule.** One `Theory.Derivation`
  inductive; `efq` gated on `[IsIntuitionistic T]` so it is *structurally* unconstructible
  at `MPL = ∅` (stronger than "admissible but unused"). The gate-free fragment is named by
  `IsBotRuleFree` / `MinimalDerivation` rather than a second inductive.

Both avoid the anti-pattern the task warns against (a separate efq-baked-in inductive with a
duplicated efq-free clone). If, hypothetically, one were starting from #648's snapshot, the
concrete steps would be: (1) split `PropositionalAxiom` into the `Min ⊂ Int ⊂ Prop` chain
with `to*` subsumption lemmas; (2) add `MinimalHilbert`/`IntuitionisticHilbert` above the
existing `ClassicalHilbert`; (3) add `Propositional.HilbertMin`/`HilbertInt` tag types +
instances; (4) gate the ND `efq` constructor on `[IsIntuitionistic T]`. **All four already
exist.**

---

## 4. Reusable Patterns Identified (task item 3)

1. **`IsIntuitionistic`/`IsClassical`/`IsMinimal` marker trio** (`Defs.lean`,
   `Equivalence.lean`) — the canonical mirror-pattern: a `class`/`abbrev`, an
   `is*Iff : Is* T ↔ <set> ⊆ T` characterization, a base instance, and an
   `instIs*Extension` monotonicity lemma. Any new strength predicate should copy this shape.
2. **Axiom-predicate parameterization** (`Derivation.lean`) — write the proof engine once
   over `Axioms : Proposition → Prop`; select logic by supplying a predicate.
3. **Subsumption `to*` lemmas** (`MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom`) —
   the mechanical `cases`-and-reconstruct proof of hierarchy inclusion.
4. **Gated inductive constructor** (`efq … [IsIntuitionistic T]`) — makes a rule optional
   without a second inductive; pair with a recursive `IsBotRuleFree`-style predicate to name
   the gate-free fragment.
5. **`MinimalAxioms`/`ConjImpAxioms` factor classes** (`Axioms.lean:191`,
   `Equivalence.lean`) — bundle a reusable subset of axiom witnesses so generic Lindenbaum /
   algebraic lemmas parameterize over the minimal fragment.

---

## 5. Mathlib Lemmas Needed

**None.** No new implementation is required, hence no new Mathlib dependency. For reference,
the existing infrastructure already relies only on `Set.mem_range`, `Set.image`, `WithBot`
(`Mathlib.Order.TypeTags`), and `FunLike.Basic` — all already imported in `Defs.lean`. The
`grind`-backed `is*Iff` proofs use CSLib-local `@[scoped grind]` attributes, not Mathlib
lemmas.

---

## 6. Recommendation (Zero-Debt compliant)

Because the deliverable already exists in full and builds green, there is **no sorry-free
implementation gap to close** — and equally no implementation *to do*. Per the zero-debt
policy (never recommend placeholder work, never fabricate a need), the honest routing is:

1. **Preferred**: mark task 491 **[BLOCKED] for user review** as an outdated tracking task —
   its objective ("make efq optional") was completed by prior tasks on the #648 lineage. The
   user decides whether to close it as already-satisfied or repoint it.
2. **If the user wants a deliverable anyway**: scope the implementation phase to
   **verification + documentation only** — e.g. add/confirm a regression test asserting
   `¬ Deriv MinPropAxiom [] ⊥` and the non-derivability of efq at minimal strength (largely
   already covered by `min_consistent`), and/or a short doc note cross-linking the three
   encodings. This must **not** manufacture a redundant `IsMinimal` marker or a duplicate
   efq-free inductive — both already exist and duplication would violate reuse-first.

**Do not** introduce a new efq-free `Derivation` clone or a new axiom to "bridge a gap":
there is no gap.

---

## 7. Key File Reference (absolute paths)

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Defs.lean` — `Proposition`
  (primitive ⊥), `MPL/IPL/CPL`, `IsIntuitionistic`, `IsClassical` (lines 164–206).
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` —
  `Theory.Derivation` with gated `efq` (line 182), `IsBotRuleFree` (223), `MinimalDerivation`
  (242).
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
  — `minimal`, `IsMinimal`, `isMinimalIff`, `instIsMinimalExtension` (177–267).
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Derivation.lean` —
  parameterized `DerivationTree Axioms`.
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Axioms.lean` —
  `MinPropAxiom`/`IntPropAxiom`/`PropositionalAxiom` + subsumption.
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`
  — `HilbertInt`/`HilbertMin` instances.
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Instances.lean` —
  `HilbertCl` classical instances.
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/ProofSystem.lean` —
  `MinimalHilbert ⊂ IntuitionisticHilbert ⊂ ClassicalHilbert`, tag types.

---

## Orchestrator Handoff JSON

```json
{
  "task": 491,
  "phase": "research",
  "status": "researched",
  "session_id": "sess_1784044271_09e821_491",
  "agent_type": "cslib-research-agent",
  "finding": "already_implemented",
  "efq_optional": true,
  "hierarchy_representable": true,
  "encodings_present": [
    "hilbert_axiom_predicate:MinPropAxiom|IntPropAxiom|PropositionalAxiom",
    "typeclass_bundle:MinimalHilbert|IntuitionisticHilbert|ClassicalHilbert",
    "nd_gated_rule:efq[IsIntuitionistic T] over MPL|IPL|CPL"
  ],
  "is_minimal_marker_exists": true,
  "build_status": "green",
  "build_command": "lake build Cslib.Logics.Propositional.ProofSystem.IntMinInstances Cslib.Logics.Propositional.NaturalDeduction.Basic",
  "build_result": "638 jobs, success",
  "mathlib_lemmas_needed": [],
  "sorry_risk": "none",
  "new_definitions_recommended": false,
  "recommended_next_action": "BLOCKED_for_user_review_or_verification_only",
  "rationale": "Task tracks PR #648 snapshot; codebase evolved past it (tasks 185/187/191/367/409). efq already optional in both proof systems. No implementation gap; recommending new work would duplicate existing IsMinimal/MinimalHilbert/MinPropAxiom infrastructure and violate reuse-first.",
  "reference_grounding": {
    "primitive_bot": "Defs.lean:81-104",
    "nd_gated_efq": "NaturalDeduction/Basic.lean:182",
    "is_intuitionistic_is_classical": "Defs.lean:164-206",
    "is_minimal": "NaturalDeduction/Equivalence.lean:189",
    "hilbert_axiom_chain": "ProofSystem/Axioms.lean:48-179",
    "typeclass_hierarchy": "Foundations/Logic/ProofSystem.lean:341-358"
  },
  "artifacts": [
    "specs/491_minimal-propositional-base/reports/01_minimal-propositional-base.md"
  ]
}
```
