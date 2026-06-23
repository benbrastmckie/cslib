# Teammate D Findings: Strategic Vision for Generic Hilbert Proof-Search Tactic

**Task**: 269 — Build generic bounded proof-search tactic for InferenceSystem
**Role**: Teammate D — Horizons (Strategic Vision)
**Date**: 2026-06-22

---

## Key Findings

### Finding 1: This Is Foundational Infrastructure, Not a Nice-to-Have

The task is strategically important because cslib currently has an unusual gap: it has a
rich polymorphic typeclass hierarchy (`InferenceSystem`, `ClassicalHilbert`, `ModalHilbert`,
`TemporalBXHilbert`, `BimodalTMHilbert`) with concrete instances for 20+ proof systems, but
no automation to *use* these systems. Every theorem proof in `Foundations/Logic/Theorems/`
requires manual `ModusPonens.mp` chains. This creates a labor asymmetry: adding a new proof
system takes 10-50 lines (just register instances), but proving theorems in that system
requires hundreds of lines of manual derivation.

A generic `hilbert_search` tactic operating over `InferenceSystem S α` would eliminate this
asymmetry and unlock the full value of the typeclass hierarchy.

**Evidence**: Compare the gap between:
- `Foundations/Logic/Theorems/Combinators.lean` — 5 theorems, each requiring 5-15 manual
  derivation steps per theorem, written out explicitly using `HasAxiomImplyK.implyK`,
  `ModusPonens.mp`, etc.
- `Bimodal/Metalogic/Decidability/` — 1,195-line ProofSearch infrastructure that automates
  exactly this kind of reasoning, but only for Bimodal formulas, not generically.

### Finding 2: Three Adjacent Opportunities Are Directly Enabled

**Opportunity A: Zero-Boilerplate Proof Systems**

When new logics are added to cslib (e.g., LTL already exists, description logics, dynamic
logic), their theorems could be proved by `hilbert_search` immediately after registering
instances — no manual derivation infrastructure needed. This lowers the barrier to adding
new logics from "must build proof automation" to "register instances."

**Opportunity B: Decision Procedure Integration**

The Bimodal `DecisionProcedure.lean` already has `DecisionResult.valid proof` which
produces `DerivationTree .Base [] phi`. A generic tactic could call the specialized
decision procedure when available (via a typeclass `HasDecisionProcedure`) and fall back
to bounded DFS otherwise. This creates a layered automation architecture:
1. Fast path: if `S` has a registered decision procedure, use it
2. Medium path: bounded DFS via `hilbert_search`
3. Slow path: user-guided proof

**Opportunity C: Generic MCS Infrastructure**

`Foundations/Logic/Metalogic/` has generic `SetConsistent`, `SetMaximalConsistent`, and
`Lindenbaum` — but these require `DerivableIn S (HasImp.imp φ ψ)` goals to be discharged
manually. A `hilbert_search` tactic would close most of these goals automatically,
making the generic MCS infrastructure practically usable without per-logic boilerplate.

### Finding 3: Scoping Analysis — The Framework-First Approach Is Correct

The task description correctly identifies the core tension: port ~700 lines from
`BimodalLogic/Automation/ProofSearch/Core.lean`, but adapt to the polymorphic architecture
instead of hardcoding Bimodal formulas.

Two alternative scopings were considered and rejected:

**Alternative A: Propositional-only first, then extend**

Rejected because: cslib's propositional theorems already work (sorry-free, as confirmed by
Task 266 research). The value is in *modal and temporal* systems where automated proof
search would eliminate hundreds of lines of manual derivation per system.

**Alternative B: Build InferenceSystem API improvements first**

Also rejected because: `InferenceSystem.lean` and `ProofSystem.lean` already have the
right API. The `ModusPonens`, `Necessitation`, `TemporalNecessitation`, and all
`HasAxiom*` typeclasses are well-designed. The gap is in automation, not API design.

**Recommended scoping**: The task should be scoped as written — a generic bounded DFS
proof-search tactic with the following phased structure:

Phase 1 (propositional): `MinimalHilbert` context — axiom matching + MP only
Phase 2 (classical): `ClassicalHilbert` — add Peirce, EFQ
Phase 3 (modal): `ModalHilbert` — add necessitation + axiom K
Phase 4 (temporal/bimodal): `TemporalBXHilbert`, `BimodalTMHilbert` — add temporal rules

### Finding 4: The Critical Technical Constraint — Formula Decidability

The `AxiomMatcher.lean` in Bimodal uses `DecidableEq (Formula Atom)` (with
`[DecidableEq Atom]`) to pattern-match formulas. A generic tactic over `InferenceSystem S α`
cannot assume `DecidableEq α` in general. This is the main technical constraint.

**Resolution**: The tactic should require `DecidableEq F` as a constraint. All concrete
formula types in cslib (`PL.Proposition`, `Modal.Proposition`, `Temporal.Formula`,
`Bimodal.Formula`) already have `DecidableEq` instances (they derive it from `DecidableEq Atom`).

The generic signature would be:
```lean
-- Term-mode bounded DFS
def hilbertSearch [DecidableEq F] [ClassicalHilbert S (F := F)]
    (φ : F) (depth : Nat) : Option (InferenceSystem.DerivableIn S φ)
```

Producing `Option (DerivableIn S φ)` rather than constructing a full `DerivationTree`
is the correct abstraction — `DerivableIn` is a `Prop` (`Nonempty (S⇓a)`), which is what
most theorem statements use.

### Finding 5: Aesop Extensibility Is an Unconventional but Viable Long-Term Path

`aesop` is available in cslib (it is a dependency). `aesop` supports custom rule sets via
`@[aesop safe apply]` and `@[aesop unsafe apply (confidence := 70%)]` attributes.

In principle, one could register each `HasAxiom*` typeclass method and `ModusPonens.mp`
as `aesop` rules. The difficulty is that Hilbert-style proof goals are typically of the
form `InferenceSystem.DerivableIn S φ`, and Aesop would need to unfold the formula
structure to apply the right axiom.

**Assessment**: Aesop extensibility is promising as a *long-term* direction but is not
the right first step. The reason: aesop's rule application is goal-directed (backward
chaining from the conclusion), whereas Hilbert proof search naturally works by
axiom-matching (forward from axioms). The bounded DFS approach in the task description
is the right near-term implementation.

If the bounded DFS tactic proves successful and is widely used, registering the core
propositional inference rules as `@[aesop]` lemmas (after `DerivableIn` is proved) would
allow aesop to handle propositional subgoals automatically.

### Finding 6: Proof-by-Reflection Approach Would Be Cleaner but Requires Decidability

The `decide` tactic works for decidable propositions. If `DerivableIn S φ` could be made
`Decidable` (for finite formula types), `decide` would subsume the need for a custom tactic.

**Obstacle**: Hilbert derivability is undecidable in general (for modal/temporal logics
with full formula types). However, for *bounded depth* derivability — "is `φ` derivable
in at most `k` steps?" — decidability holds when `F` is finitely generated.

A proof-by-reflection approach would:
1. Define `BoundedDerivable S φ n : Bool` — a computable function
2. Prove soundness: `BoundedDerivable S φ n = true → DerivableIn S φ`
3. Use `decide` at elaboration time for small `n`

**Assessment**: This is the ideal long-term architecture but requires `[Fintype F]` or
a computable formula enumeration, which is not available generically. Medium-term: build
the term-mode DFS function first, wrap it as a tactic macro second.

### Finding 7: Cross-Cutting Synergies with Tasks 266, 278, 279, 280

The research from Task 266 (Priority 5 in its recommendations) explicitly identified
"Concretize Modal Tag Instances" as unlocking the generic MCS infrastructure. The `hilbert_search`
tactic would complement this: once modal tag instances are registered and `hilbert_search` works,
MCS proofs could use `hilbert_search` to discharge the derivability goals automatically.

Task 278 (simplify proofs with simp/grind normalization tags) and Task 279 (sequent calculus)
are independent. Task 279's LK system is a different proof system (sequent calculus, not
Hilbert), so `hilbert_search` would not apply to sequent goals.

Task 280 (proof system triad gap analysis) would likely recommend `hilbert_search` as
part of the Hilbert system's metatheoretic completeness story.

### Finding 8: Community Alignment — No Known Lean 4 Generic Modal Proof-Search Exists

Searching the codebase and known Lean 4 ecosystem: there is no existing library providing
a generic Hilbert-style proof-search tactic for modal/temporal logics in Lean 4. Mathlib
has no modal logic support. The closest work is:
- `igl` (Intuitionistic Graded Logic) project — not in cslib's dependency tree
- Lean4-modal-logic experiments on GitHub — small, no tactic automation
- BimodalLogic's ProofSearch (1,195 lines) — hardcoded to one formula type

This represents a genuine gap. A generic `hilbert_search` tactic in cslib would be the
first such tool in the Lean 4 ecosystem for Hilbert-style classical modal and temporal logics.

The cslib Zulip discussion would likely be receptive: the library's core mission is
CS formalization infrastructure, and proof automation that works across all logics
fits the "shared infrastructure" philosophy.

---

## Recommended Approach

### Recommended Architecture: Two-Layer Design

**Layer 1: Generic term-mode search function (the core)**

Place in `Cslib/Foundations/Logic/ProofSearch.lean`:

```lean
/-- Bounded DFS proof search over MinimalHilbert systems.
    Returns `some ⟨tree⟩` if a proof of depth ≤ n is found, `none` otherwise. -/
def searchMinimal [DecidableEq F] [MinimalHilbert S (F := F)]
    (Γ : List F) (φ : F) (n : Nat) : Option (InferenceSystem.DerivableIn S φ)
```

Layers build up:
- `searchMinimal` — axiom K, axiom S, MP, assumptions
- `searchClassical` — adds EFQ, Peirce
- `searchModal` — adds necessitation, axiom K (modal), system axioms
- `searchTemporal` / `searchBimodal` — adds temporal rules

**Layer 2: Tactic macro wrapping the term-mode search**

```lean
macro "hilbert_search" : tactic =>
  `(tactic| first
    | exact (searchClassical [] _ 5).get!  -- or a proper failure message
    ...)
```

The macro should:
1. Inspect the goal to identify `InferenceSystem.DerivableIn S φ`
2. Dispatch to the appropriate search layer based on available instances
3. Report failure with remaining goal if depth exceeded

### Recommended File Layout

```
Cslib/Foundations/Logic/
├── ProofSearch.lean         -- Generic bounded DFS + tactic macro
│   ├── Core (searchMinimal, searchClassical, searchModal)
│   ├── Temporal extensions (searchTemporal)
│   └── hilbert_search tactic macro
```

Alternative: place under `Cslib/Logics/Tactics/HilbertSearch.lean` if the cslib maintainers
prefer tactics to live in the Logics namespace. Check with community on Zulip.

### Key Implementation Decisions

1. **Formula representation**: Use `List F` for context (matches all DerivationTree types)
2. **Depth parameter**: Default depth 5, configurable with `hilbert_search (depth := 10)`
3. **Return type**: `Option (DerivableIn S φ)` — do not return a `DerivationTree` directly
   (DerivationTree is Type-valued, not Prop-valued; the tactic needs a `Prop` to close the goal)
4. **Termination**: Use `Nat` fuel parameter with `termination_by fuel`
5. **Axiom selection**: Use a typeclass-dispatched list of axiom instances, not a hardcoded
   match (this is what makes it generic)

---

## Evidence and Examples

### Example 1: Current manual proof (Combinators.lean)

```lean
theorem imp_trans {φ ψ χ : F}
    (h1 : InferenceSystem.DerivableIn S (HasImp.imp φ ψ))
    (h2 : InferenceSystem.DerivableIn S (HasImp.imp ψ χ)) :
    InferenceSystem.DerivableIn S (HasImp.imp φ χ) := by
  have h3 := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S) (φ := HasImp.imp ψ χ) (ψ := φ)) h2
  have h4 := ModusPonens.mp
    (HasAxiomImplyS.implyS (S := S) (φ := φ) (ψ := ψ) (χ := χ)) h3
  exact ModusPonens.mp h4 h1
```

With `hilbert_search`, this would be:
```lean
theorem imp_trans ... := by hilbert_search (assumptions := [h1, h2])
```

### Example 2: What genericity enables

The BimodalLogic ProofSearch (AxiomMatcher.lean + ProofExtraction.lean) is ~600 lines
for a single formula type. A generic version would serve 20+ systems simultaneously.

### Example 3: Stub infrastructure already exists

`AxiomMatcher.lean:456` contains `boundedSearchWithProofStub` — an explicit stub for
"the full implementation [that] performs depth-limited DFS to find derivation trees."
The task directly addresses filling this stub generically.

---

## Confidence Level

**High confidence** on:
- Strategic importance of the task (foundational infrastructure, not nice-to-have)
- The two-layer architecture (term-mode function + tactic macro)
- `DecidableEq F` as the correct technical constraint
- Phased implementation (propositional first, then modal, temporal, bimodal)
- No existing equivalent in the Lean 4 ecosystem

**Medium confidence** on:
- Exact file placement (ProofSearch.lean in Foundations/Logic/ vs. Logics/Tactics/)
  — depends on community preference, recommend Zulip discussion
- Whether `Option (DerivableIn S φ)` or a more refined return type is best
  — could also return `Bool` for decidability use cases
- Long-term Aesop integration timeline — useful but not essential for first version

**Low confidence** on:
- Compilation performance of the generic DFS (may need fuel limits tuned empirically)
- Whether temporal rules (necessitation, BX axioms) can be made efficiently matchable
  generically (they depend on `HasUntil`/`HasSince` typeclasses which are not part of the
  core propositional hierarchy)
