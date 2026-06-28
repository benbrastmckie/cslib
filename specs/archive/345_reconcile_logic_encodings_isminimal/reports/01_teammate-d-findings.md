# Task 345 — Teammate D (Horizons / Strategic Direction) Findings

Strength-axis reconciliation: `IsMinimal` + `MinimalAxioms`↔inclusion bridge, viewed against
the long-term trajectory of the Propositional Logic strength axis and the Foundations generic
layer.

## Key Findings

### F1. The task conflates two strength substrates that use *different* `minimal` sets

The task lists, side by side, two deliverables that secretly refer to **two distinct `minimal`
sets over two distinct substrates**:

| | Substrate | What "strength" measures | "minimal" set |
|---|---|---|---|
| `IsIntuitionistic` / `IsClassical` (Defs.lean) | **Natural Deduction** `Theory` (the 10 ND rule constructors carry the logic) | *theory supplement* beyond the ND base | `IPL = range(⊥→·)`, `CPL = range(¬¬·→·)` — **one schema family each** |
| `MinimalAxioms` (Equivalence.lean) | **Hilbert** `AxiomTheory` (MP is the *only* rule) | the full axiomatization | the **eight** structural schemata K, S, ∧I, ∧E1, ∧E2, ∨I1, ∨I2, ∨E |

Consequence, grounded in `Defs.lean:154`: `MPL := ∅`. So deliverable (1) read literally —
`IsMinimal T ↔ minimal ⊆ T` with `minimal = MPL = ∅` — is **vacuous** (`∅ ⊆ T` always holds),
because in ND minimal logic's content lives in the *inference rules*, not in any theory axioms.
Meanwhile deliverable (2)'s `minimal ⊆ AxiomTheory Axioms` can only be substantive if
`minimal = AxiomTheory MinPropAxiom = {φ | MinPropAxiom φ}` (the eight schemata), because in
Hilbert the connectives *are* axioms. **The same word `minimal` denotes `∅` in (1) and an
8-element schema set in (2).** A planner who does not disambiguate this will either ship a
vacuous `IsMinimal` or silently change its meaning between the two clauses.

This is the single most important strategic observation: `IsIntuitionistic`/`IsClassical` are
*single-schema supplements over a rule-rich substrate*; "minimal logic" in the Hilbert sense is
an *eight-schema base over a rule-poor substrate*. They are not the same kind of object, so a
naive "mirror" is not actually uniform — it is a category error waiting to be entrenched.

### F2. There are already (at least) two "minimal" axiom abstractions; `IsMinimal` risks a third

- `MinimalAxioms` (`Logics/Propositional/NaturalDeduction/Equivalence.lean:114`) — 8 schemata,
  used in **7 files** (the algebraic-completeness stack: `HilbertCompleteness`,
  `HilbertStrongCompleteness`, `HilbertLindenbaum`, `Soundness`, `SemanticConsequence`, …).
- `MinimalHilbert` (`Foundations/Logic/ProofSystem.lean:342`) — K, S, MP *implicational core*,
  used in **18 files** and is the load-bearing generic backbone consolidated by tasks 350/351
  (generic deduction theorem, Lindenbaum, MCS quartet across all four logics).

Adding a third bespoke `minimal`-named entity (`IsMinimal`, and possibly a fresh `minimal`
`Theory` constant) into `Propositional/Defs.lean` **increases** the very fragmentation this task
claims to reconcile. The strategically correct framing is: CSLib's reuse anchor for "minimal" is
`MinimalHilbert` in Foundations, not a new Propositional-local predicate.

### F3. A parameterized `IsStrength S T ↔ S ⊆ T` class buys almost nothing

The focus prompt asks whether a single `IsStrength S T ↔ S ⊆ T` would beat three bespoke
definitions. Verdict: **no, not as a typeclass**, for concrete structural reasons:

- `S ⊆ T` is *already* a `Prop`; wrapping it in a class adds a layer without adding content.
- Typeclass instance resolution keys on the *head* of the instance — here `T`. But the strength
  parameter `S` varies per level. A class indexed by both `S` and `T` cannot be resolved by
  `[IsStrength S T]` the way `[IsIntuitionistic T]` is, because `S` is not determined by the
  goal. The existing classes work precisely *because* `S` is baked in (so resolution keys on `T`).
- The "monotone propagation" the task offers as deliverable (3) is, after the iff,
  **literally `Set.Subset.trans`**: `instIsIntuitionisticExtention`/`instIsClassicalExtention`
  (`Defs.lean:190,195`) are one-line `grind`s that are morally `h.trans`. Generalizing them gives
  you `theorem strength_mono (h : S ⊆ T) (hTT' : T ⊆ T') : S ⊆ T' := h.trans hTT'` — already in
  Mathlib. There is no reusable theorem to "prove once"; transitivity is the abstraction.

So the bespoke classes earn their keep *only* as ergonomic, `grind`-tagged, `T`-keyed instance
carriers used pervasively in the semantics files. The right move is to **keep the inclusion
*characterizations* as primary content and not over-engineer a generic strength class.**

### F4. The genuinely valuable, trajectory-aligned deliverable is bridge (2)

`MinimalAxioms Axioms ↔ AxiomTheory MinPropAxiom ⊆ AxiomTheory Axioms` is:
- **Cheap**: forward = an 8-case split on `MinPropAxiom` feeding the bundle fields; backward =
  each field is the inclusion applied to a constructor. This is exactly the shape already proven
  in `MinPropAxiom.toIntPropAxiom` (`Axioms.lean:155`) and `IntPropAxiom.toPropAxiom` (`:168`).
  `AxiomTheory` membership is `Iff.rfl` (`mem_axiomTheory`, `Equivalence.lean:90`), so the
  inclusion unfolds to `∀ φ, MinPropAxiom φ → Axioms φ`.
- **Reuse-aligned**: tasks 341 and 344 both already carry `[MinimalAxioms Axioms]`. The bridge
  lets their `MinimalAxioms` hypothesis be *stated and discharged in the inclusion idiom*, which
  is the idiom the fragment-tower tasks (below) speak natively.

This clause advances the project's actual goal (strength-axis scalability without abandoning the
witness bundle) far more than the vacuous `IsMinimal`.

### F5. The strength axis is becoming a *lattice of fragments*, not a 3-point chain

Sibling tasks show the real horizon. The completed/active fragment tower
(310/311/312/322/352/353/354) is building a refined inclusion lattice:
`IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ IPL⟨∧,→,⊥,⊤⟩ ⊂ IPL`, a parallel MPL chain
(`ConjImpAxiom`, `ConjImpBotMinAxiom`, `MinPropAxiom` — task 353), and now the *classical* side
(task 352: `ClassicalImpAxiom`/Peirce). Each fragment ships a `toX` subsumption map
(`ConjImpAxiom.toConjImpBotMinAxiom`, `…toMinPropAxiom`, etc.) — **these subsumption maps are
already the inclusion idiom in disguise** (`∀ φ, SmallerAxiom φ → BiggerAxiom φ`, i.e.
`AxiomTheory Smaller ⊆ AxiomTheory Bigger`).

Strategic implication: the inclusion view the task wants is *the lingua franca the fragment tower
already speaks*. A single helper that turns any `Sub.toBig` subsumption into both an
`AxiomTheory Sub ⊆ AxiomTheory Big` fact **and** a `MinimalAxioms`-instance feeder would let the
~7 fragment axiom systems interoperate with the completeness stack uniformly. That is a much
larger payoff than a `IsMinimal` mirror, and it is the natural extension point of bridge (2).

### F6. Cross-proof-system uniformity (ND / Hilbert / tableau) is real but not yet reachable here

Task 316 (tableau soundness, three logics) is a *third* proof system. The focus prompt's vision
of "a `minimal` axiom-set abstraction reusable across natural deduction / sequent / tableau" is
legitimate, but today the strength predicates live only on the `Theory`/`AxiomTheory` substrates.
Tableau strength is encoded in closure conditions (`MinimalClosure` vs intuitionistic vs
classical — task 316 description), not in a theory-inclusion. Forcing a single inclusion
abstraction across all three now would be premature; the honest strategic recommendation is to
**land the Hilbert/ND inclusion bridge cleanly and leave tableau out of scope**, while noting the
Foundations layer (`MinimalHilbert`) as the eventual common home.

## Recommended Approach

1. **Disambiguate `minimal` before writing any Lean (planner gate).** Pick ONE coherent meaning
   and document the substrate in the docstring. Two coherent options:
   - **(A, recommended) Substrate-honest**: do **not** add a vacuous `IsMinimal T ↔ ∅ ⊆ T`. It is
     naming debt (F1, F2) that future readers will misread as "the minimal-logic axioms,"
     colliding with `MinimalAxioms`/`MinimalHilbert`. Instead deliver the substantive half:
     the **Hilbert inclusion bridge** (F4), optionally exposing
     `AxiomTheory MinPropAxiom` under a clearly-named alias (e.g. `minimalAxiomTheory`, **not**
     bare `minimal`).
   - **(B) Mirror-honest**: if the team insists on triad symmetry in `Defs.lean`, define
     `IsMinimal` but **explicitly docstring it as vacuous over the ND substrate** (`minimal = MPL
     = ∅`, content carried by inference rules) and prove `isMinimalIff : IsMinimal T ↔ True` /
     `MPL ⊆ T`. Mark clearly that this is *not* the Hilbert `MinimalAxioms` notion. Acceptable
     only with the disambiguation in writing.

2. **Prioritize bridge (2).** Implement
   `theorem minimalAxioms_iff_subset : MinimalAxioms Axioms ↔ AxiomTheory MinPropAxiom ⊆ AxiomTheory Axioms`
   via the 8-case `MinPropAxiom` split (reuse the `toIntPropAxiom` pattern) and `mem_axiomTheory`.
   This is the reuse-first, trajectory-aligned core of the task.

3. **Make the bridge fragment-tower-ready (stretch, high strategic value).** Provide one helper
   converting any subsumption `(∀ φ, A φ → B φ)` into `AxiomTheory A ⊆ AxiomTheory B`, so the
   existing `toX` maps (351/353 + tower) feed both the inclusion lattice and `MinimalAxioms`
   instance synthesis. Co-locate strength infrastructure with `MinimalHilbert` in
   `Foundations/Logic/` if it is to serve Modal/Temporal/Bimodal later (F2, F6).

4. **Propagation = transitivity.** Do not build a generic `IsStrength` class. If propagation
   lemmas are wanted, state them as thin `Set.Subset.trans` wrappers and `grind`-tag, mirroring
   `instIsClassicalExtention`.

5. **Explicitly scope out tableau** (F6); note Foundations as the eventual common home in the
   module docstring.

## Evidence / Examples

- `Defs.lean:154` `abbrev MPL : Theory := ∅` → `IsMinimal T ↔ MPL ⊆ T` is vacuous.
- `Defs.lean:166-180` `IsIntuitionistic`/`IsClassical` require *one* schema family each
  (`efq`/`dne`); `isIntuitionisticIff`/`isClassicalIff` are the inclusion characterizations the
  task wants to mirror.
- `Defs.lean:190,195` propagation theorems are one-line `grind`s ≅ `Set.Subset.trans`.
- `Equivalence.lean:114-165` `MinimalAxioms` = 8 schemata; instances for `MinPropAxiom`,
  `IntPropAxiom`, `PropositionalAxiom` already exist.
- `Equivalence.lean:85-93` `AxiomTheory Axioms = {φ | Axioms φ}`, `mem_axiomTheory` is `Iff.rfl`
  → inclusion unfolds to `∀ φ, MinPropAxiom φ → Axioms φ`.
- `Axioms.lean:155-179` `MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom` — the exact
  8-/9-case split shape bridge (2) reuses.
- `Foundations/Logic/ProofSystem.lean:342` `MinimalHilbert` (K,S,MP), **18 files** — the existing
  Foundations-level "minimal" anchor; `MinimalAxioms` reaches **7 files**.
- Sibling tasks: 341/344 carry `[MinimalAxioms Axioms]`; 350/351 consolidate on `MinimalHilbert`;
  352/353/354 build the fragment lattice with `toX` subsumption maps (the inclusion idiom);
  316 is the tableau substrate (out of scope).

## Confidence Level

**High** on the structural claims (F1 vacuity of `MPL=∅`, F4 cheapness/shape of the bridge, F3
propagation = `Subset.trans`) — all read directly from source. **Medium-high** on the strategic
recommendations (prefer bridge over vacuous `IsMinimal`; Foundations as common home) — these are
judgment calls grounded in the file/usage counts and sibling-task trajectory, but the team's
appetite for triad notational symmetry in `Defs.lean` may legitimately favor option (B). The
fragment-tower helper (recommendation 3) is a stretch direction, not a hard requirement.
