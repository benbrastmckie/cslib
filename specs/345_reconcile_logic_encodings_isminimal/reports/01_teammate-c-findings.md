# Task 345 — Teammate C (Critic) Findings

Reconcile the two strength encodings on the Hilbert substrate (inclusion view vs `MinimalAxioms` witness-bundle).

## Key Findings

### F1. The bridge IS well-typed — the feared carrier mismatch dissolves (verified)
The focus prompt's central worry ("`MinimalAxioms` is over a predicate, `minimal ⊆ AxiomTheory Axioms` is over theories — different carriers?") is **unfounded**. `AxiomTheory` is exactly the predicate→theory adapter:
- `MinimalAxioms (Axioms : Proposition Atom → Prop) : Prop` (a Prop-valued typeclass), verified via hover.
- `AxiomTheory (Axioms : Proposition Atom → Prop) : Theory Atom`, verified via hover (`Theory Atom = Set (Proposition Atom)`).
- Therefore `minimal ⊆ AxiomTheory Axioms` is `Set.Subset` between two `Theory Atom` values, provided `minimal : Theory Atom`. Both sides land in the same carrier. **No type error.** This part of the task framing is safe.

### F2. CENTRAL RISK — `minimal` means TWO incompatible things; the task silently conflates them
There are two distinct "minimal" notions in this codebase, and only one of them makes bridge (2) true:

- **ND-inclusion meaning (Defs.lean family):** `MPL := ∅` (verified by hover: "The empty theory corresponds to minimal propositional logic"). In the `Theory.Derivation` ND system the conjunction/disjunction intro/elim are *inference-rule constructors*, so minimal logic needs **zero** extra axiom propositions. The natural analog to `IsIntuitionistic T ↔ IPL ⊆ T` and `IsClassical T ↔ CPL ⊆ T` would be `IsMinimal T ↔ ∅ ⊆ T`, which is **trivially true for every `T`** — a vacuous typeclass.
- **Hilbert witness-bundle meaning (`MinimalAxioms`):** the Hilbert system's only inference rule is modus ponens; the 8 connective schemas (K, S, andI, andE1, andE2, orI1, orI2, orE) are *axioms*. So here "minimal" = the **set of those 8 schema instances**, a non-trivial theory.

**These differ precisely because the two proof systems place the ∧/∨ rules in different layers** (ND: constructors; Hilbert: axioms). Equivalence.lean lines 52–54 already flag this: "`AxiomTheory Axioms` is not the same as `MPL`, `IPL`, or `CPL` ... it is not a statement about pure logic strength."

**Consequence:** bridge (2) `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms` is only TRUE under the Hilbert meaning (`minimal` = the 8 schema instances). If `minimal` is set to `MPL = ∅` (the obvious sibling of `IPL`/`CPL`), the RHS becomes `∅ ⊆ AxiomTheory Axioms` ≡ `True`, making the iff claim "`MinimalAxioms Axioms ↔ True`" — **FALSE** (e.g. `Axioms := fun _ => False` refutes it). The plan MUST define `minimal` as the 8-schema set and must NOT reuse/alias `MPL`. This is the easiest way to get the whole task subtly wrong.

### F3. `minimal` = `AxiomTheory MinPropAxiom`, which forces a FILE-PLACEMENT decision (import direction)
The 8 `MinimalAxioms` schemas are exactly the constructors of the existing inductive `MinPropAxiom` (Axioms.lean:126–150). So the cleanest `minimal` is:
```
minimal : Theory Atom := AxiomTheory (@MinPropAxiom Atom)   -- = {φ | MinPropAxiom φ}
```
Then `minimal ⊆ AxiomTheory Axioms` unfolds to `∀ φ, MinPropAxiom φ → Axioms φ` (pointwise predicate inclusion), and the bridge is essentially `MinimalAxioms Axioms ↔ MinPropAxiom ≤ Axioms`.

**But import direction blocks placing this in Defs.lean.** Verified: `ProofSystem/Axioms.lean:9` does `public import ...Defs`, and Defs.lean does **not** import Axioms. So Defs.lean cannot reference `MinPropAxiom` or `AxiomTheory` without creating a cycle. Two options, each with a cost:
- **(A) Keep the family together in Defs.lean:** define `minimal` as a raw `Set.range`/set-builder union of the 8 schemas (no `MinPropAxiom`). Cost: the 8-schema list is duplicated (drift risk vs `MinPropAxiom`), and bridge (2) (in Equivalence.lean) then needs an extra lemma `minimal = {φ | MinPropAxiom φ}` to connect the two spellings.
- **(B) Place `minimal`/`IsMinimal` in Axioms.lean or Equivalence.lean** (where both `MinPropAxiom` and `AxiomTheory` are visible). Cost: `IsMinimal` no longer sits beside its siblings `IsIntuitionistic`/`IsClassical` in Defs.lean, weakening the organizational analogy that motivated the task. NOTE: `AxiomTheory` is defined in Equivalence.lean, not Axioms.lean — so option B with the `AxiomTheory MinPropAxiom` spelling really means "Equivalence.lean (or later)", not Axioms.lean.

The task description assumes (1) lives in Defs.lean ("Waring's Defs.lean characterises strength by INCLUSION ... add `IsMinimal T ↔ minimal ⊆ T`") while (2) naturally lives in Equivalence.lean. **The plan must resolve this split explicitly.** This is an unstated assumption that will derail an implementer who tries to put everything in one file.

### F4. The "is the backward direction even provable / does it need derivation search?" worry is REFUTED
Both directions of bridge (2) are finite, constructive, and search-free:
- Forward `MinimalAxioms Axioms → minimal ⊆ AxiomTheory Axioms`: `rintro φ hφ; cases hφ` (8 cases over `MinPropAxiom`), each discharged by the matching witness `inst.h_K`/`inst.h_S`/`inst.h_andI`/… (the exact pattern already used in the three `MinimalAxioms` instances at Equivalence.lean:135–165).
- Backward `minimal ⊆ AxiomTheory Axioms → MinimalAxioms Axioms`: build the 8-field structure, each field `fun φ ψ => hsub (MinPropAxiom.implyK φ ψ)` etc.

No decidability, no `deductionTheorem`, no proof-search. (Contrast with `ndToHilbert`, which is `noncomputable` and uses the deduction theorem — that machinery is **not** needed here.) Risk on this axis: **low**.

### F5. `grind` is unlikely to one-shot `isMinimalIff` (proof-effort risk)
The siblings `isIntuitionisticIff`/`isClassicalIff` close with a bare `by grind` because each is a **single** schema (`IPL = Set.range (⊥ → ·)`, one `Set.range`). `IsMinimal`/`minimal` is an **8-schema** condition (a union of 8 ranges, two of which are 3-parameter schemas). Expect `by grind` to be unreliable here; budget an explicit `constructor`/`cases`-style proof and per-schema membership lemmas. Do not assume the one-liner copies over.

### F6. CI-green items that are easy to miss
- **Naming (defsWithUnderscore):** this file uses **camelCase** theorem names (`isIntuitionisticIff`, `isClassicalIff`), not mathlib snake_case. Match it: `isMinimalIff`, and a camelCase bridge name (e.g. `minimalAxiomsIffSubset`), NOT `minimal_axioms_iff_subset`.
- **docBlame:** every new declaration needs a docstring — the `IsMinimal` class, **each of its 8 fields**, `minimal`, `isMinimalIff`, the bridge theorem, and any monotone-propagation lemma.
- **defLemma:** `isMinimalIff` and the bridge are Prop-valued → must be `theorem`/`lemma`, not `def`. `minimal` is Set-valued → `def`/`abbrev` is correct.
- **unusedSectionVars:** copy the siblings' `omit [DecidableEq Atom] in` before the iff theorems (Defs.lean:169,178,188,193).
- **`@[scoped grind]` attributes:** siblings carry `@[scoped grind]`/`@[scoped grind =]`/`@[scoped grind →]`. Adding matching attributes for consistency can perturb unrelated `grind` proofs elsewhere — build the whole `Logics/Propositional` subtree, not just the edited file.
- **shake/checkInitImports:** option (B) adds no new imports (Equivalence.lean already imports everything); option (A) adds none to Defs.lean (`Set.range` already available). Editing existing files means no new `import Cslib.Init` needed. Low risk either way.

### F7. Scope/consumer check — adding the inclusion view does NOT break anything (reassuring)
`MinimalAxioms` has heavy downstream use as a typeclass constraint `[MinimalAxioms Axioms]` across `Semantics/Algebra/*` (HilbertLindenbaum, HilbertLindenbaumRel, Soundness, HilbertStrongCompleteness, HilbertCompleteness) and `Semantics/SemanticConsequence.lean`. Because the task **adds** an iff/bridge and **keeps `MinimalAxioms` as the class** (per "MinimalAxioms STAYS"), none of these consumers change. There is no "replace the typeclass with an inclusion predicate" sub-goal hiding here — if a plan proposes that, it is out of scope and would break ~150 call sites.

## Recommended Approach

1. **Pin the meaning first:** `minimal := AxiomTheory (@MinPropAxiom Atom)` (the 8 Hilbert schema instances). Document loudly that `minimal ≠ MPL` (`MPL = ∅`), and that `IsMinimal` here means "carries the 8 connective axiom schemas," a *Hilbert*-substrate notion, NOT the ND minimal-logic floor.
2. **Resolve file placement explicitly (F3).** Prefer option (B): put `IsMinimal`, `minimal`, `isMinimalIff`, and the bridge in Equivalence.lean (or a small new file under `NaturalDeduction/`/`ProofSystem/` that imports both), since `AxiomTheory` lives there. If the reviewer insists `IsMinimal` sit beside `IsIntuitionistic`/`IsClassical` in Defs.lean, use option (A) and add the connecting lemma `minimal_raw = {φ | MinPropAxiom φ}`.
3. **Prove the bridge by case analysis, not search** (F4): mirror the existing `MinimalAxioms` instance pattern for the forward direction; build the structure field-by-field for the backward direction.
4. **Do not rely on `by grind`** for `isMinimalIff` (F5); write the explicit proof.
5. **Mirror the siblings exactly** for lint: camelCase names, per-field docstrings, `omit [DecidableEq Atom] in`, optional `@[scoped grind]` (F6). Run a full `lake build` of `Logics/Propositional` plus `lake lint`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`.
6. **Treat optional task (3) (monotone propagation)** as a trivial `IsMinimal T → T ⊆ T' → IsMinimal T'` (analog of `instIsIntuitionisticExtention`, Defs.lean:188–196). No `grind →` surprises expected, but include it only if it lands clean.

**No `sorry`, no new axiom, no vacuous `def := True` is required** — the task is fully provable as scoped, provided F2/F3 are handled. If the plan cannot reconcile F3 to the reviewer's satisfaction, flag for user decision rather than forcing a cycle-breaking hack.

## Evidence / Examples

- `MinimalAxioms (Axioms : Proposition Atom → Prop) : Prop` — `Equivalence.lean:114` (hover-verified); 8 schema fields `h_K`…`h_orE` at `Equivalence.lean:115–132`.
- `AxiomTheory (Axioms : Proposition Atom → Prop) : Theory Atom` — `Equivalence.lean:85` (hover-verified). `Theory Atom := Set (Proposition Atom)` — `Defs.lean:142`.
- `MPL : Theory Atom := ∅`, "empty theory corresponds to minimal propositional logic" — `Defs.lean:154` (hover-verified). The empty-theory = minimal mismatch driver.
- Inclusion-family precedent: `isIntuitionisticIff (T) : IsIntuitionistic T ↔ IPL ⊆ T := by grind` with `IPL := Set.range (Proposition.imp ⊥ ·)` — `Defs.lean:157,166–171`; `isClassicalIff` similarly `Defs.lean:175–180`; monotone propagation `instIsIntuitionisticExtention`/`instIsClassicalExtention` `Defs.lean:188–196`.
- `minimal` = closure of the 8 schemas = `MinPropAxiom` constructors — `Axioms.lean:126–150`.
- Import direction (cycle blocker): `Axioms.lean:9` `public import Cslib.Logics.Propositional.Defs`; Defs.lean does not import Axioms (grep-verified).
- "`AxiomTheory Axioms` is not the same as `MPL`/`IPL`/`CPL` ... not a statement about pure logic strength" — `Equivalence.lean:52–54`.
- Existing `MinimalAxioms` instance proof pattern to reuse for the forward bridge — `Equivalence.lean:135–165`.
- Downstream consumers unaffected (constraint-only use): `Semantics/Algebra/HilbertLindenbaum.lean`, `HilbertLindenbaumRel.lean`, `Soundness.lean:201`, `HilbertStrongCompleteness.lean:86,121`, `HilbertCompleteness.lean:65`, `SemanticConsequence.lean:141,215` (grep-verified).
- `minimal`/`IsMinimal`/`MinPL` do not yet exist anywhere in `Logics/Propositional/` (grep-verified) — must be defined from scratch.

## Confidence Level

**High** on F1 (carrier OK — hover-verified), F2 (the ∅-vs-8-schemas conflation — hover + source-verified), F3 (import-direction cycle blocking Defs.lean placement — grep-verified), F4 (bridge is search-free and provable), and F7 (additive, no consumer breakage — grep-verified). **Medium** on F5 (whether `grind` copes — not empirically tested; flagged conservatively). The dominant risk is F2/F3: the task name "minimal" papers over a genuine encoding asymmetry, and an implementer who reuses `MPL` or tries to keep everything in Defs.lean will produce either a false theorem or an import cycle.
