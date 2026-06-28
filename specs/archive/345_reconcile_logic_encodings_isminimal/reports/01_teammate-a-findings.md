# Task 345 — Teammate A (Primary Angle): Concrete Implementation Findings

Focus: exactly how `IsMinimal` / `minimal` should be defined to mirror
`IsIntuitionistic` / `IsClassical`, what `minimal` is, and exactly how the bridge
`MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms` is stated and proved.

## Key Findings

1. **No `minimal` Theory set or `IsMinimal` class exists yet for propositional logic.**
   `grep` over `Cslib/Logics/Propositional/` finds only `MPL = ∅`, `IPL`, `CPL` (Theory sets)
   and `IsIntuitionistic` / `IsClassical` (classes). The only `IsMinimal*` symbol in the repo
   is `IsMinimalAutomaton` (`Cslib/Computability/Languages/MyhillNerode.lean:169`), which is
   unrelated. So this is greenfield: nothing to reuse for `minimal`, but the *pattern* to
   mirror is fully established.

2. **CRITICAL conceptual point — `minimal ≠ MPL`.** In the ND substrate, `MPL := ∅`
   (`Defs.lean:154`) because the ND `Theory.Derivation` treats the connective rules
   (andI/andE/orI/orE/impI/impE) as *primitive constructors*. A theory `T` only ever adds
   *extra* axioms (efq for intuitionistic, dne for classical). Consequently a "substrate"
   `IsMinimal T` mirroring the ∅ idiom would be **vacuously true for every theory** and useless.
   The `minimal` set required by the bridge is the **Hilbert-flavoured** notion: the set of the
   8 connective+implication schema instances that the Hilbert system must carry as axioms. This
   is exactly the carrier of `MinPropAxiom` (`Axioms.lean:126-150`). The task is correct that
   `MinimalAxioms` stays — but the new `minimal` set lives at a *different layer* than `MPL`.
   This is the central thing the reconciliation must get right.

3. **`minimal` must be characterizable as `{φ | MinPropAxiom φ} = AxiomTheory MinPropAxiom`.**
   For the bridge `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms` to be *true*, `minimal`
   must be exactly the set of all instances of the 8 schemas K, S, andI, andE1, andE2, orI1,
   orI2, orE. `MinPropAxiom`'s 8 constructors (`Axioms.lean:126-150`) generate precisely those.
   `AxiomTheory Axioms = {φ | Axioms φ}` (`Equivalence.lean:85`), so
   `minimal ⊆ AxiomTheory Axioms` unfolds to `∀ φ, MinPropAxiom φ → Axioms φ`, which is
   inter-derivable with the 8-witness `MinimalAxioms Axioms` bundle (`Equivalence.lean:114-132`).

4. **Import constraint forces a placement decision.** `Defs.lean` imports only
   `Foundations.Logic.Connectives` (+ Mathlib); it does **not** import `Axioms.lean`
   (`MinPropAxiom`). `Axioms.lean` imports `Defs.lean` (`Axioms.lean:9`). So if `minimal`/
   `IsMinimal` live in `Defs.lean` (to truly mirror `IPL`/`CPL`/`IsIntuitionistic`), they
   **cannot reference `MinPropAxiom`** — `minimal` must be written self-contained as a union of
   `Set.range`s (like `IPL = Set.range (Proposition.imp ⊥ ·)`, `Defs.lean:157-162`). The link
   to `MinPropAxiom` is then a separate characterization lemma proved downstream in
   `Equivalence.lean` (which already sees both, `Equivalence.lean:9-11`).

5. **Neither direction of the bridge is genuinely "hard" — both are 8 mechanical cases.**
   The forward direction (`MinimalAxioms → ⊆`) is a `cases` on the `MinPropAxiom` witness, each
   branch closed by one field. The backward (`⊆ → MinimalAxioms`) builds the 8-field structure,
   each field obtained by applying the inclusion to the matching constructor. The only real
   *effort* is the intermediate `minimal ↔ MinPropAxiom` membership lemma (16 trivial range
   obligations) **if** `minimal` is defined as a union of ranges in `Defs.lean`.

## Recommended Approach

I recommend **Option A** (mirror placement in `Defs.lean`) as primary, with **Option B** as a
lower-cost fallback if `grind` struggles. The two differ only in where `minimal` is defined and
how much glue the bridge needs.

### Option A (primary): self-contained `minimal` in `Defs.lean`, mirror fidelity

#### A.1 — `minimal` set (in `Defs.lean`, alongside `IPL`/`CPL`)

Real connective syntax from `Defs.lean`: `Proposition.imp`/`.and`/`.or` with scoped
`→`/`∧`/`∨` notation (`Defs.lean:107-111`). Mirror `IPL = Set.range (Proposition.imp ⊥ ·)`:

```lean
/-- Minimal propositional logic: the 8 implication/conjunction/disjunction axiom schemas
(K, S, ∧I, ∧E₁, ∧E₂, ∨I₁, ∨I₂, ∨E) that the Hilbert system carries as axioms. Unlike `MPL = ∅`,
this set is non-empty: in the Hilbert presentation the connective rules are axioms, not primitive
inference rules. -/
abbrev minimal : Theory Atom :=
  Set.range (fun p : Proposition Atom × Proposition Atom => p.1 → (p.2 → p.1))                              -- K
  ∪ Set.range (fun p : Proposition Atom × Proposition Atom × Proposition Atom =>
        (p.1 → (p.2.1 → p.2.2)) → ((p.1 → p.2.1) → (p.1 → p.2.2)))                                          -- S
  ∪ Set.range (fun p : Proposition Atom × Proposition Atom => p.1 → (p.2 → (p.1 ∧ p.2)))                    -- andI
  ∪ Set.range (fun p : Proposition Atom × Proposition Atom => (p.1 ∧ p.2) → p.1)                            -- andE1
  ∪ Set.range (fun p : Proposition Atom × Proposition Atom => (p.1 ∧ p.2) → p.2)                            -- andE2
  ∪ Set.range (fun p : Proposition Atom × Proposition Atom => p.1 → (p.1 ∨ p.2))                            -- orI1
  ∪ Set.range (fun p : Proposition Atom × Proposition Atom => p.2 → (p.1 ∨ p.2))                            -- orI2
  ∪ Set.range (fun p : Proposition Atom × Proposition Atom × Proposition Atom =>
        (p.1 → p.2.2) → ((p.2.1 → p.2.2) → ((p.1 ∨ p.2.1) → p.2.2)))                                        -- orE
```

(A `{φ | (∃ a b, φ = …) ∨ … }` set-builder is an equivalent alternative and may be friendlier to
`grind`; see Risks.)

#### A.2 — `IsMinimal` class (8 fields, mirroring `IsIntuitionistic`'s single `efq` field)

`IsIntuitionistic` (`Defs.lean:165-167`) is `@[scoped grind] class … where efq (A) : (⊥ → A) ∈ T`.
Mirror with 8 fields keyed to the 8 schemas:

```lean
/-- A theory is minimal if it contains the 8 Hilbert connective/implication schemas. -/
@[scoped grind]
class IsMinimal (T : Theory Atom) where
  /-- K schema: φ → (ψ → φ) -/
  k    (φ ψ   : Proposition Atom) : (φ → (ψ → φ)) ∈ T
  /-- S schema: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)) -/
  s    (φ ψ χ : Proposition Atom) : ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))) ∈ T
  /-- ∧-introduction: φ → (ψ → φ ∧ ψ) -/
  andI (φ ψ   : Proposition Atom) : (φ → (ψ → (φ ∧ ψ))) ∈ T
  /-- left ∧-elimination: (φ ∧ ψ) → φ -/
  andE1 (φ ψ  : Proposition Atom) : ((φ ∧ ψ) → φ) ∈ T
  /-- right ∧-elimination: (φ ∧ ψ) → ψ -/
  andE2 (φ ψ  : Proposition Atom) : ((φ ∧ ψ) → ψ) ∈ T
  /-- left ∨-introduction: φ → (φ ∨ ψ) -/
  orI1 (φ ψ   : Proposition Atom) : (φ → (φ ∨ ψ)) ∈ T
  /-- right ∨-introduction: ψ → (φ ∨ ψ) -/
  orI2 (φ ψ   : Proposition Atom) : (ψ → (φ ∨ ψ)) ∈ T
  /-- ∨-elimination: (φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ)) -/
  orE  (φ ψ χ : Proposition Atom) : ((φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))) ∈ T
```

#### A.3 — `isMinimalIff` (mirrors `isIntuitionisticIff`/`isClassicalIff`)

`isIntuitionisticIff` is `omit [DecidableEq Atom] in @[scoped grind =] theorem … : IsIntuitionistic T ↔ IPL ⊆ T := by grind` (`Defs.lean:169-171`). Mirror:

```lean
omit [DecidableEq Atom] in
@[scoped grind =]
theorem isMinimalIff (T : Theory Atom) : IsMinimal T ↔ minimal ⊆ T := by
  grind  -- fallback if grind fails: constructor; aesop / Set.mem_range + Set.union_subset
```

Plus, mirroring `Defs.lean:188-196`, the monotone-extension propagation (task item 3):

```lean
omit [DecidableEq Atom] in
@[scoped grind →]
theorem instIsMinimalExtention {T T' : Theory Atom} [IsMinimal T] (h : T ⊆ T') :
    IsMinimal T' := by grind
```

And a base instance mirroring `instIsIntuitionisticIPL` (`Defs.lean:182-183`):
`instance : IsMinimal (minimal : Theory Atom)` (each field `Set.mem_union_…` + `Set.mem_range.mpr ⟨(φ,ψ), rfl⟩`).

#### A.4 — The bridge (in `Equivalence.lean`, which sees `MinimalAxioms` and `MinPropAxiom`)

First a characterization lemma tying the self-contained `minimal` to `MinPropAxiom`:

```lean
/-- The substrate `minimal` set is exactly the carrier of `MinPropAxiom`. -/
theorem mem_minimal_iff_minPropAxiom {φ : PL.Proposition Atom} :
    φ ∈ (minimal : Theory Atom) ↔ MinPropAxiom φ := by
  constructor
  · rintro (⟨⟨a,b⟩, rfl⟩ | ⟨⟨a,b,c⟩, rfl⟩ | ⟨⟨a,b⟩, rfl⟩ | ⟨⟨a,b⟩, rfl⟩ | ⟨⟨a,b⟩, rfl⟩
            | ⟨⟨a,b⟩, rfl⟩ | ⟨⟨a,b⟩, rfl⟩ | ⟨⟨a,b,c⟩, rfl⟩)
    · exact .implyK a b
    · exact .implyS a b c
    · exact .andI a b
    · exact .andE1 a b
    · exact .andE2 a b
    · exact .orI1 a b
    · exact .orI2 a b
    · exact .orE a b c
  · rintro ⟨..⟩ <;>
      simp only [minimal, Set.mem_union, Set.mem_range] <;>
      first
        | exact .inl ⟨(_, _), rfl⟩            -- adjust injection per constructor
        | ⟨…⟩  -- one witness per schema; aesop can usually discharge all 8
```

Then the bridge itself:

```lean
/-- **Strength bridge**: the witness-bundle `MinimalAxioms` and the inclusion idiom
`minimal ⊆ AxiomTheory Axioms` are interchangeable. -/
theorem minimalAxioms_iff_minimal_subset
    {Axioms : PL.Proposition Atom → Prop} :
    MinimalAxioms Axioms ↔ (minimal : Theory Atom) ⊆ AxiomTheory Axioms := by
  constructor
  · -- forward: 8 witnesses ⇒ inclusion
    intro h φ hφ
    rw [mem_axiomTheory]                       -- goal: Axioms φ
    rcases mem_minimal_iff_minPropAxiom.mp hφ   -- φ is one of the 8 schema instances
    -- close each case with the matching field of h (h.h_K, h.h_S, …)
    all_goals first
      | exact h.h_K _ _    | exact h.h_S _ _ _
      | exact h.h_andI _ _ | exact h.h_andE1 _ _ | exact h.h_andE2 _ _
      | exact h.h_orI1 _ _ | exact h.h_orI2 _ _  | exact h.h_orE _ _ _
  · -- backward: inclusion ⇒ 8 witnesses
    intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro φ ψ <;> intros <;>
      exact mem_axiomTheory.mp
        (h (mem_minimal_iff_minPropAxiom.mpr (by constructor)))
```

The backward branch applies `h` to `mem_minimal_iff_minPropAxiom.mpr ⟨the constructor⟩`; for each
field the right `MinPropAxiom` constructor (`.implyK φ ψ`, …) supplies the membership witness, and
`mem_axiomTheory.mp` (`Equivalence.lean:90-93`) extracts `Axioms`.

### Option B (fallback): define `minimal := AxiomTheory MinPropAxiom`

If `grind`/`aesop` struggle with the 8-way union (see Risks), drop the union-of-ranges entirely
and place `minimal` in `Axioms.lean` or `Equivalence.lean`:

```lean
abbrev minimal : Theory Atom := AxiomTheory (@MinPropAxiom Atom)   -- = {φ | MinPropAxiom φ}
```

Then `mem_minimal_iff_minPropAxiom` is `mem_axiomTheory` (definitional, `Equivalence.lean:88-93`),
and the bridge collapses to `MinimalAxioms Axioms ↔ ∀ φ, MinPropAxiom φ → Axioms φ` with the same
8-case proof but **zero range glue**. Cost: `minimal` no longer literally mirrors `IPL`/`CPL`'s
`Set.range` style and no longer lives in `Defs.lean`. If `IsMinimal T ↔ minimal ⊆ T` is still
wanted at the substrate level, `IsMinimal` can also be defined here (8 fields as in A.2), with
`isMinimalIff` proved via `mem_axiomTheory` + `Set.subset_def` + `cases` on `MinPropAxiom`.

**Recommendation:** attempt Option A.1–A.4; if `grind` in A.3 or the `simp`/`aesop` glue in
`mem_minimal_iff_minPropAxiom` does not close cleanly within a couple of attempts, switch
`minimal` to Option B (a one-line `abbrev`) and keep everything else identical. Option B is
strictly lower-risk and still satisfies both task deliverables 1 and 2 verbatim.

## Which direction is hard, and the per-witness obligation

- **Forward (`MinimalAxioms Axioms → minimal ⊆ AxiomTheory Axioms`)**: after `intro φ hφ` and
  reducing `hφ` to `MinPropAxiom φ`, do `cases hφ`. Eight goals, each of the form
  `Axioms (<schema instance>)`, each discharged by exactly one field:
  K→`h.h_K`, S→`h.h_S`, andI→`h.h_andI`, andE1→`h.h_andE1`, andE2→`h.h_andE2`,
  orI1→`h.h_orI1`, orI2→`h.h_orI2`, orE→`h.h_orE`. Mechanical.
- **Backward (`⊆ → MinimalAxioms Axioms`)**: build the 8-field structure; field `X` for schema
  `σ_X(φ,ψ[,χ])` is `h (proof that σ_X ∈ minimal)`, where the membership proof is the matching
  `MinPropAxiom` constructor (Option B) or a `Set.mem_range` injection (Option A). Mechanical.

Neither is conceptually hard. The *only* nontrivial glue is `mem_minimal_iff_minPropAxiom` in
Option A (16 trivial obligations); Option B makes it definitional.

## Evidence / Examples (file:line)

- `Cslib/Logics/Propositional/Defs.lean:154` — `abbrev MPL : Theory (Atom) := ∅` (so `minimal ≠ MPL`).
- `Defs.lean:157-162` — `IPL = Set.range (Proposition.imp ⊥ ·)`, `CPL = Set.range (fun A ↦ ¬¬A → A)`: the `Set.range` style to mirror.
- `Defs.lean:164-171` — `IsIntuitionistic` class (single `efq` field) + `isIntuitionisticIff … := by grind`: the exact template for `IsMinimal`/`isMinimalIff`.
- `Defs.lean:173-180` — `IsClassical`/`isClassicalIff` (same pattern, second data point).
- `Defs.lean:182-196` — base instances (`instIsIntuitionisticIPL`) and monotone propagation (`instIsIntuitionisticExtention … (h : T ⊆ T') : IsIntuitionistic T' := by grind`): templates for `instIsMinimal (minimal)` and `instIsMinimalExtention` (task item 3).
- `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean:106-111` — `instance : IsIntuitionistic (IPL ∪ CPL)` built with `Set.mem_union_left _ (Set.mem_range.mpr ⟨A, rfl⟩)`: the exact membership idiom for proving `minimal` instances.
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean:126-150` — `MinPropAxiom`'s 8 constructors (implyK, implyS, andI, andE1, andE2, orI1, orI2, orE) = the carrier of `minimal`.
- `Axioms.lean:155-165` — `MinPropAxiom.toIntPropAxiom` via `cases h … exact .implyK …`: the exact `cases`/constructor proof shape the bridge's forward direction reuses.
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean:85-93` — `AxiomTheory Axioms := {φ | Axioms φ}` and `mem_axiomTheory : φ ∈ AxiomTheory Axioms ↔ Axioms φ` (`Iff.rfl`): the membership unfolder for the bridge.
- `Equivalence.lean:114-132` — `MinimalAxioms` class with the 8 named fields `h_K, h_S, h_andI, h_andE1, h_andE2, h_orI1, h_orI2, h_orE`: the exact field names the bridge consumes/produces.
- `Equivalence.lean:135-143` — `instance : MinimalAxioms (@MinPropAxiom Atom)` (each field `fun … => .implyK …`): confirms `MinimalAxioms MinPropAxiom` holds, so `minimal = AxiomTheory MinPropAxiom` is consistent and the bridge instance for `MinPropAxiom` is `Set.Subset.rfl`.
- `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean:286,306,324` — `mem_axiomTheory.mp/.mpr (MinPropAxiom.… / IntPropAxiom.efq …)`: live precedent for combining `mem_axiomTheory` with axiom constructors exactly as the bridge does.
- Import facts: `Defs.lean:9-13` (no `Axioms` import → `minimal` in Defs cannot mention `MinPropAxiom`); `Axioms.lean:9` (`public import …Defs`); `Equivalence.lean:9-11` (sees both → correct home for the bridge).
- Negative result: `grep -rn "IsMinimal\|def minimal\|abbrev minimal"` over `Cslib/Logics/Propositional/` returns nothing (only `MPL`); `IsMinimalAutomaton` (`MyhillNerode.lean:169`) is unrelated.

## Zero-Debt / CI notes

- No `sorry`/axiom needed: every obligation is a finite mechanical case split; if `grind` fails,
  explicit `cases`/`constructor`/`Set.mem_range` closes it. No deferral.
- Lint: `IsMinimal` is a `class` (allowed), all 8 fields need docstrings (docBlame) — included
  above. `minimal`/`isMinimalIff`/`instIsMinimalExtention`/`mem_minimal_iff_minPropAxiom`/
  `minimalAxioms_iff_minimal_subset` need docstrings — included. Names are lowerCamelCase
  (matching `isIntuitionisticIff`, `instIsIntuitionisticExtention`). New `Defs.lean` content sits
  inside the existing `@[expose] public section` / `namespace Cslib.Logic.PL.Theory`.
- Reuse-first satisfied: reuses `Set.range`/`Set.mem_union`/`Set.mem_range`, `AxiomTheory`,
  `mem_axiomTheory`, `MinPropAxiom` constructors, and the `grind`-attribute pattern; no new
  abstraction beyond the three task-mandated declarations.

## Confidence Level

**High** for the design and the bridge statement/proof structure: the `minimal = {φ | MinPropAxiom φ}`
characterization is forced by the bridge's truth, the field/constructor mappings are read directly
from source, and the proof shapes copy existing precedents (`MinPropAxiom.toIntPropAxiom`,
`mem_axiomTheory` usages, `isIntuitionisticIff`).

**Medium** on two points I could not execute (no edits were made): (a) whether a single `grind`
closes `isMinimalIff` over an 8-way `Set.range` union — the existing `grind` proofs are
single-range, so this may need an explicit fallback or the Option B `abbrev`; (b) the precise
`rcases`/injection pattern in `mem_minimal_iff_minPropAxiom`. Option B eliminates both risks at the
cost of mirror-location fidelity, and is the recommended fallback.
