# Research Report: Task #345 — Reconcile Logic Encodings (`IsMinimal`)

**Task**: Reconcile logic encodings — add `IsMinimal` inclusion view + `MinimalAxioms` bridge
**Date**: 2026-06-26
**Mode**: Team Research (4 teammates: Primary, Alternatives, Critic, Horizons)
**Task type**: cslib (Lean 4)

## Summary

All four teammates **independently converged** on one structural finding that dominates this
task: the word **`minimal` does not mean `MPL`**. On the natural-deduction (ND) substrate of
`Defs.lean`, `MPL := ∅` (`Defs.lean:154`) — minimal logic's content lives in the ND inference
*rule constructors*, not in any theory axioms. A naive mirror of `IsIntuitionistic`/`IsClassical`
that sets `minimal = MPL = ∅` makes the required bridge

> `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms`

**FALSE** (the RHS collapses to `∅ ⊆ _ ≡ True`, while `MinimalAxioms (fun _ => False)` is false).
The only meaning of `minimal` that makes both deliverables true and coherent is the **Hilbert
8-schema set**, i.e. `minimal = AxiomTheory MinPropAxiom = {φ | MinPropAxiom φ}` (the schemas
K, S, ∧I, ∧E₁, ∧E₂, ∨I₁, ∨I₂, ∨E from `Axioms.lean:126-150`). Under this meaning, deliverable (1)
`IsMinimal T ↔ minimal ⊆ T` is substantive ("T carries the 8 connective axiom schemas") and is
definitionally `MinimalAxioms (T as predicate)`, which is exactly the reconciliation the task
wants.

The work is **fully provable with no `sorry` and no new axiom** — both bridge directions are 8
mechanical cases reusing the existing `MinPropAxiom.toIntPropAxiom` proof shape (`Axioms.lean:155`).
The one real design decision (all four teammates flagged it) is **file placement**, forced by the
import graph: `Defs.lean` cannot see `MinPropAxiom`/`AxiomTheory` (would create a cycle), so the
8-schema `minimal` cannot literally sit beside `IPL`/`CPL` without re-encoding the schemas inline.

## Key Findings

### 1. Primary Approach (Teammate A)
- This is greenfield: no `minimal`/`IsMinimal` exists in `Logics/Propositional/` (only `MPL`,
  `IPL`, `CPL`). The *pattern* to mirror is fully established by `IsIntuitionistic`/`isIntuitionisticIff`.
- `minimal` must be characterizable as `{φ | MinPropAxiom φ} = AxiomTheory MinPropAxiom` for the
  bridge to be true.
- Offers **Option A** (self-contained `minimal` as a union of 8 `Set.range`s in `Defs.lean` +
  a connecting lemma `mem_minimal_iff_minPropAxiom` downstream) for mirror-location fidelity, and
  **Option B** (`minimal := AxiomTheory MinPropAxiom` downstream) as a strictly lower-risk fallback.
- Full Lean code sketches provided for the class (8 fields), `isMinimalIff`, the monotone
  extension instance, and the bridge proof (forward = `cases` on `MinPropAxiom`; backward = build
  the 8-field structure). Confidence **High** on design, **Medium** on whether bare `grind` closes
  the 8-schema iff.

### 2. Alternative Approaches / Prior Art (Teammate B)
- Task 345 is a **third instance of an existing 4-part template** already in `Defs.lean`
  (`@[scoped grind]` class → `@[scoped grind =]` iff by `grind` → membership instances →
  `@[scoped grind →]` monotone extension).
- The 8 witnesses come **"for free"**: because `Theory = Set = predicate` (`Defs.lean:142`) and
  `mem_axiomTheory` is `@[simp] Iff.rfl` (`Equivalence.lean:88-93`), both bridges collapse — via
  `Set.setOf_subset_setOf` (loogle-confirmed) — to a single load-bearing lemma
  **(★) `MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ`**, provable exactly like
  `MinPropAxiom.toIntPropAxiom`. No 8 separate `Set.range` subset proofs needed.
- Recommends **Option B (downstream placement)** on reuse-first/DRY grounds: putting `minimal`
  in `Defs.lean` would require duplicating the 8 schemas, violating reuse-first.
- Sibling prior art: `Modal/Cube.lean:101-122` (axiom-set `⊆` subsumption family) confirms
  "strength by inclusion" is house style, but `Defs.lean`'s typeclass↔inclusion bridge is the
  better template. Confidence **High** on template/constraint, **Medium** on `grind`.

### 3. Gaps and Shortcomings (Teammate C — Critic)
- **Refuted a false alarm**: the feared carrier mismatch is a non-issue — hover-verified that
  `AxiomTheory : (Proposition→Prop) → Theory Atom` is exactly the predicate→theory adapter, so
  `minimal ⊆ AxiomTheory Axioms` is well-typed `Set.Subset`.
- **Confirmed the central risk (F2)**: `minimal` denotes two incompatible things; reusing `MPL`
  yields a provably false theorem. `Equivalence.lean:52-54` already documents that
  `AxiomTheory Axioms` is "not the same as MPL/IPL/CPL ... not a statement about pure logic strength."
- **Confirmed backward direction is search-free (F4)**: no decidability / deduction theorem
  needed (contrast `ndToHilbert`, which is `noncomputable`).
- **`grind` warning (F5)**: siblings one-shot because each is a *single* schema; the 8-schema
  union/inductive will likely need an explicit `constructor`/`cases` proof. Do not assume the
  one-liner copies over.
- **CI-green checklist (F6)**: camelCase names (`isMinimalIff`, not snake_case), docstrings on the
  class + **each of 8 fields** + every decl (docBlame), `theorem`/`lemma` not `def` for Prop-valued
  (defLemma), `omit [DecidableEq Atom] in` (unusedSectionVars), and **build the whole
  `Logics/Propositional` subtree** because new `@[scoped grind]` attributes can perturb unrelated
  `grind` proofs.
- **Scope check (F7)**: additive only — `MinimalAxioms` stays as a class, so its ~150 downstream
  `[MinimalAxioms Axioms]` constraint sites (HilbertLindenbaum, Soundness, HilbertCompleteness,
  SemanticConsequence, …) are untouched. Any plan that proposes *replacing* the typeclass with an
  inclusion predicate is out of scope. Confidence **High** on F1-F4/F7, **Medium** on F5.

### 4. Strategic Horizons (Teammate D)
- Sharpens the central finding into a **vacuity warning**: deliverable (1) read literally with
  `minimal = MPL = ∅` is *vacuous* (`∅ ⊆ T` always holds). `IsIntuitionistic`/`IsClassical` are
  single-schema supplements over a rule-rich substrate; Hilbert "minimal" is an 8-schema base over
  a rule-poor substrate — *not the same kind of object*, so a naive mirror is a category error.
- **Naming-debt caution (F2)**: CSLib already has two "minimal" abstractions —
  `MinimalAxioms` (7 files) and the load-bearing `MinimalHilbert` in `Foundations/Logic/ProofSystem.lean:342`
  (K, S, MP; 18 files; the backbone consolidated by tasks 350/351). A third bespoke
  `Propositional`-local `minimal` increases fragmentation.
- **Rejects a generic `IsStrength S T` typeclass (F3)**: instance resolution keys on the head `T`,
  but `S` varies per level and isn't determined by the goal, so the class can't resolve like
  `[IsIntuitionistic T]`. "Monotone propagation" (deliverable 3) is *literally `Set.Subset.trans`* —
  there is no theorem to "prove once."
- **Identifies bridge (2) as the high-value, trajectory-aligned core (F4-F5)**: tasks 341/344
  already carry `[MinimalAxioms Axioms]`; the fragment-tower tasks (352/353/354 + 310/311/312/322)
  build an inclusion lattice whose `toX` subsumption maps *are the inclusion idiom in disguise*
  (`AxiomTheory Sub ⊆ AxiomTheory Big`). The bridge lets the witness-bundle and the lattice idiom
  interoperate.
- Recommends scoping **tableau (task 316) out** and noting `Foundations/Logic/` (`MinimalHilbert`)
  as the eventual common home. Confidence **High** on structural claims, **Medium-high** on the
  strategic prioritization.

## Synthesis

### Conflicts Resolved

**Conflict 1 — File placement (A vs B/C/D).** Teammate A recommends **Option A** (self-contained
`minimal` in `Defs.lean` for triad symmetry) as primary; B, C, and D recommend **Option B**
(define `minimal := AxiomTheory MinPropAxiom` downstream in `Equivalence.lean`) on reuse-first/DRY
grounds. **Resolution: prefer Option B.** Three of four teammates favor it, and it is objectively
lower-risk: it (a) avoids duplicating the 8 schemas (reuse-first compliant), (b) makes the
connecting lemma `mem_axiomTheory` *definitional* (`Iff.rfl`) instead of 16 hand-proved range
obligations, and (c) eliminates the `grind`-on-8-way-union risk that A itself flags. Option A is
the fallback **only if** a reviewer insists `IsMinimal` sit physically beside `IsIntuitionistic`
in `Defs.lean`; in that case add A's `mem_minimal_iff_minPropAxiom` connecting lemma. This is the
**one decision the planner must make explicit** (see Open Questions).

**Conflict 2 — Should `IsMinimal T ↔ minimal ⊆ T` exist at all? (D vs A/B).** D warns the
deliverable is vacuous/naming-debt if read over the ND substrate. A and B treat it as a
straightforward third template instance. **Resolution: the deliverable is fine *provided*
`minimal` is the 8-schema set (not `MPL`).** Under `minimal := AxiomTheory MinPropAxiom`,
`IsMinimal T ↔ minimal ⊆ T` is substantive and equals `MinimalAxioms (T as predicate)` — D's
vacuity objection only bites if an implementer reaches for `MPL`. So D's warning becomes a
**hard constraint on the definition**, not a reason to drop deliverable (1). The plan must
docstring loudly that `minimal ≠ MPL` and that `IsMinimal` is a *Hilbert-substrate* notion.

**Conflict 3 — Generic `IsStrength` abstraction (D's caution vs the task's "scalability" framing).**
**Resolution: do not build a generic `IsStrength S T` class** — D's resolution-keying argument is
decisive. Keep the bespoke `T`-keyed characterizations; treat "scalability" as *idiomatic
interoperability* (the inclusion idiom shared with the fragment tower), which the bridge already
delivers.

### Gaps Identified
- **Empirical `grind` behavior untested.** All teammates note (no edits in team research) that
  whether bare `by grind` closes `isMinimalIff` and the bridge iff over the 8-schema condition is
  unverified. Mitigation is mechanical and known (explicit `constructor`/`cases` + the (★) lemma /
  `setOf_subset` chain), so this is a low-risk implementation detail, not a blocker.
- **Exact backward-bridge term plumbing** (A's `mem_minimal_iff_minPropAxiom.mpr` injections under
  Option A) is sketched, not compiled — moot under the recommended Option B.

### Recommendations (for the planner / implementer)

1. **Pin the meaning first**: `minimal := AxiomTheory (@MinPropAxiom Atom)` (the 8 Hilbert schema
   instances). Docstring loudly: `minimal ≠ MPL` (`MPL = ∅`); `IsMinimal` is the Hilbert-substrate
   "carries the 8 connective axiom schemas" notion, distinct from ND minimal logic.
2. **Placement = Option B (downstream, `Equivalence.lean`)** where `MinPropAxiom` and `AxiomTheory`
   are both visible. Fall back to Option A (Defs.lean + connecting lemma) only on explicit reviewer
   request for triad symmetry.
3. **Prove the single core lemma (★)** `MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ` by
   `constructor` + `cases`/constructor, cloning `MinPropAxiom.toIntPropAxiom` (`Axioms.lean:155-165`).
4. **Derive both bridges from (★)** via `mem_axiomTheory` (`@[simp] Iff.rfl`) + `Set.setOf_subset_setOf`:
   - (1) `IsMinimal T ↔ minimal ⊆ T`
   - (2) `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms`  ← the high-value core.
   Try `by grind` first (matching siblings); on failure use the explicit (★) + `setOf_subset` chain.
5. **Monotone propagation (optional deliverable 3)** = thin `Set.Subset.trans` wrapper
   `instIsMinimalExtention {T T'} [IsMinimal T] (h : T ⊆ T') : IsMinimal T'`, `@[scoped grind →]`,
   mirroring `instIsIntuitionisticExtention` (`Defs.lean:188-196`). Include only if it lands clean.
6. **Do NOT** build a generic `IsStrength` class; do **NOT** replace the `MinimalAxioms` typeclass
   (additive only — keep ~150 consumer sites intact); **scope tableau (316) out**.
7. **CI discipline**: camelCase names; docstrings on class + all 8 fields + every decl;
   `theorem`/`lemma` for Prop-valued, `def`/`abbrev` for `minimal`; `omit [DecidableEq Atom] in`;
   run the full pipeline — `lake build` of the whole `Logics/Propositional` subtree, `lake test`,
   `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`.

### Open Questions (planner gate)
- **Triad symmetry vs DRY**: place `IsMinimal`/`minimal` downstream in `Equivalence.lean`
  (recommended, Option B) or beside `IsIntuitionistic` in `Defs.lean` with a connecting lemma
  (Option A)? This is a genuine maintainer-preference call; the synthesis recommends Option B but
  the plan should state the choice and rationale explicitly.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (implementation approach, code sketches) | completed | High (design) / Medium (grind) |
| B | Alternatives / prior art (template, "for free" reduction) | completed | High / Medium (grind) |
| C | Critic (carrier check, vacuity trap, CI checklist) | completed | High / Medium (grind) |
| D | Horizons (vacuity warning, fragment-lattice alignment) | completed | High / Medium-high |

## References

- `Cslib/Logics/Propositional/Defs.lean:142` — `Theory Atom := Set (Proposition Atom)` (defeq trick)
- `Defs.lean:154` — `MPL := ∅` (why `minimal ≠ MPL`)
- `Defs.lean:157-162` — `IPL`/`CPL` as `Set.range` (style reference)
- `Defs.lean:164-196` — `IsIntuitionistic`/`IsClassical` 4-part template (class, iff-by-grind,
  membership instances, `@[scoped grind →]` monotone extension) — the pattern to mirror
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean:126-150` — `MinPropAxiom` 8 constructors
- `Axioms.lean:155-165` — `MinPropAxiom.toIntPropAxiom` (`cases`/constructor proof shape to reuse)
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean:52-54` — docs noting
  `AxiomTheory ≠ MPL/IPL/CPL`
- `Equivalence.lean:85-93` — `AxiomTheory Axioms := {φ | Axioms φ}`, `@[simp] mem_axiomTheory` (`Iff.rfl`)
- `Equivalence.lean:114-165` — `MinimalAxioms` class (fields `h_K`…`h_orE`) + existing instances
- `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean:106-111`,
  `NaturalDeduction/AxiomAdmissibility.lean:228-231` — membership-instance & propagation idioms
- `Foundations/Logic/ProofSystem.lean:342` — `MinimalHilbert` (K,S,MP; 18 files; eventual common home)
- Mathlib: `Set.setOf_subset_setOf`, `Set.setOf_subset` (loogle-confirmed)
- Sibling tasks: 341, 344 (`[MinimalAxioms Axioms]` consumers); 350/351 (`MinimalHilbert`
  consolidation); 352/353/354 + 310/311/312/322 (fragment lattice / `toX` subsumption maps);
  316 (tableau — out of scope)
