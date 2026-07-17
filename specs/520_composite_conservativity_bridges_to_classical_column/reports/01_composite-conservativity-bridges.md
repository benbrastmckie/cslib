# Research Report: Composite Conservativity Bridges to the Classical Column

**Task:** 520 — Add missing composite bridges collapsing each non-classical base into the
classical column, in `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean`.

**Task type:** cslib (Lean 4 formal verification). **Difficulty:** Low effort, high elegance.
**Parallel-safe:** Yes (single new file section; no shared declarations touched).

## 1. Summary

All ingredient edges already exist and are landed. The task is to add 8 one-line composite
theorems to `Modularity.lean` (4 minimal-base + 4 constructive-base), each a straight function
composition of one Axis-B monotonicity lemma with one Intuitionistic→Classical bridge at the
same rung. The only structural change beyond the theorems themselves is **one new import**:
`Modularity.lean` does **not** currently (even transitively) import `IntToClassical.lean`
(verified via full transitive-closure scan — result `False`), so the classical bridges are not
yet in scope there.

No new proof content, no `sorry`, no new axioms. Each composite inherits the axiom footprint of
its constituents.

## 2. Existing Edges (verified names + signatures)

All predicates are over `{Atom : Type*} {φ : Proposition Atom}` in namespace
`Cslib.Logic.Modal`. `Derivable Axioms φ := Nonempty (DerivationTree Axioms [] φ)`.

### 2a. Axis-B edges (base → intuitionistic, same rung)
File: `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthMonotonicity.lean`

| Lemma | Signature |
|-------|-----------|
| `mkDerivable_implies_ikDerivable` | `Derivable (@MKModalAxiom Atom) φ → Derivable (@IKModalAxiom Atom) φ` |
| `ckDerivable_implies_ikDerivable` | `Derivable (@CKModalAxiom Atom) φ → Derivable (@IKModalAxiom Atom) φ` |
| `mtDerivable_implies_itDerivable` | `Derivable (@MTModalAxiom Atom) φ → Derivable (@ITModalAxiom Atom) φ` |
| `ctDerivable_implies_itDerivable` | `Derivable (@CTModalAxiom Atom) φ → Derivable (@ITModalAxiom Atom) φ` |
| `ms4Derivable_implies_is4Derivable` | `Derivable (@MS4ModalAxiom Atom) φ → Derivable (@IS4ModalAxiom Atom) φ` |
| `cs4Derivable_implies_is4Derivable` | `Derivable (@CS4ModalAxiom Atom) φ → Derivable (@IS4ModalAxiom Atom) φ` |
| `ms5Derivable_implies_is5Derivable` | `Derivable (@MS5ModalAxiom Atom) φ → Derivable (@IS5ModalAxiom Atom) φ` |
| `cs5Derivable_implies_is5Derivable` | `Derivable (@CS5ModalAxiom Atom) φ → Derivable (@IS5ModalAxiom Atom) φ` |

(All are `Derivable_mono (fun _ => <base>_implies_<int>) h` one-liners.)

### 2b. Intuitionistic → Classical bridges (same rung)
File: `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`

| Lemma | Signature | Line |
|-------|-----------|------|
| `ikDerivable_implies_kDerivable` | `Derivable IKModalAxiom φ → Derivable (@KAxiom Atom) φ` | 496 |
| `itDerivable_implies_tDerivable` | `Derivable ITModalAxiom φ → Derivable (@TAxiom Atom) φ` | 539 |
| `is4Derivable_implies_s4Derivable` | `Derivable IS4ModalAxiom φ → Derivable (@S4Axiom Atom) φ` | 650 |
| `is5Derivable_implies_s5Derivable` | `Derivable IS5ModalAxiom φ → Derivable (@ModalAxiom Atom) φ` | 768 |

**Note on S5 target:** the classical S5 axiom predicate is `ModalAxiom` (not `S5Axiom`), so the
S5 composite's conclusion is `Derivable (@ModalAxiom Atom) φ`. This mirrors
`is5Derivable_implies_s5Derivable` exactly.

## 3. Composite Lemmas Needed (8 total)

Each is a pure composition `<int→classical> (<base→int> h)`. Types line up definitionally —
the intermediate `Derivable I*ModalAxiom φ` produced by the Axis-B edge is precisely the input
of the matching bridge.

### Minimal base → classical
```lean
theorem mkDerivable_implies_kDerivable (h : Derivable (@MKModalAxiom Atom) φ) :
    Derivable (@KAxiom Atom) φ :=
  ikDerivable_implies_kDerivable (mkDerivable_implies_ikDerivable h)

theorem mtDerivable_implies_tDerivable (h : Derivable (@MTModalAxiom Atom) φ) :
    Derivable (@TAxiom Atom) φ :=
  itDerivable_implies_tDerivable (mtDerivable_implies_itDerivable h)

theorem ms4Derivable_implies_s4Derivable (h : Derivable (@MS4ModalAxiom Atom) φ) :
    Derivable (@S4Axiom Atom) φ :=
  is4Derivable_implies_s4Derivable (ms4Derivable_implies_is4Derivable h)

theorem ms5Derivable_implies_s5Derivable (h : Derivable (@MS5ModalAxiom Atom) φ) :
    Derivable (@ModalAxiom Atom) φ :=
  is5Derivable_implies_s5Derivable (ms5Derivable_implies_is5Derivable h)
```

### Constructive base → classical
```lean
theorem ckDerivable_implies_kDerivable (h : Derivable (@CKModalAxiom Atom) φ) :
    Derivable (@KAxiom Atom) φ :=
  ikDerivable_implies_kDerivable (ckDerivable_implies_ikDerivable h)

theorem ctDerivable_implies_tDerivable (h : Derivable (@CTModalAxiom Atom) φ) :
    Derivable (@TAxiom Atom) φ :=
  itDerivable_implies_tDerivable (ctDerivable_implies_itDerivable h)

theorem cs4Derivable_implies_s4Derivable (h : Derivable (@CS4ModalAxiom Atom) φ) :
    Derivable (@S4Axiom Atom) φ :=
  is4Derivable_implies_s4Derivable (cs4Derivable_implies_is4Derivable h)

theorem cs5Derivable_implies_s5Derivable (h : Derivable (@CS5ModalAxiom Atom) φ) :
    Derivable (@ModalAxiom Atom) φ :=
  is5Derivable_implies_s5Derivable (cs5Derivable_implies_is5Derivable h)
```

The 8 names were all confirmed **absent** from the entire `Cslib/` tree (grep — "NONE FOUND").

## 4. Required Import Change (the one gap)

`Modularity.lean` currently imports only:
- `...InterSystem.IntuitionisticLatticeMonotonicity`
- `...InterSystem.PropositionalStrengthMonotonicity`
- `...Systems.K.ConservativeExtension`

A transitive-closure scan from `Modularity` confirms `IntToClassical` is **not** reachable.
The Axis-B lemmas are already in scope (via `PropositionalStrengthMonotonicity`); the classical
bridges are not. Implementation must add:

```lean
public import Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical
```

alongside the existing imports (keep alphabetical/logical grouping; `IntToClassical` sorts
before `IntuitionisticLatticeMonotonicity`). No other imports are needed — `KAxiom`, `TAxiom`,
`S4Axiom`, `ModalAxiom`, and all `M*`/`C*` predicates are already transitively available
(the M*/C* predicates through `PropositionalStrengthMonotonicity`; the classical axiom types
through `IntToClassical`).

## 5. Placement & Naming Discipline

- Add the composites inside `namespace Cslib.Logic.Modal`, under a new subsection heading,
  e.g. `/-! ## Cross-Axis Composites Into the Classical Column (Axis B then Int→Classical) -/`,
  positioned after the existing `## Cross-Axis Composites (Axis B then Axis A)` block
  (after line 111) and before `## Axis C` (line 113).
- Naming follows the established `_Derivable_implies__Derivable` convention (Modularity.lean
  "Naming Discipline" section, lines 66-71). The word "conservative" is reserved for genuine
  Axis-C results — these Axis-B∘bridge composites correctly use `_implies_`, NOT "conservative",
  even though the task title says "conservativity bridges" (that is task-tracker prose, not the
  lemma name). Do **not** name any of these `*conservative*`.
- Each theorem needs a docstring (docBlame lint). Model them on the existing composite
  docstrings, e.g.: `` /-- `MK`-derivable formulas are classical-`K`-derivable: chain Axis B (`MK → IK`) then the Int→Classical bridge (`IK → K`). -/ ``
- These are `Prop`-valued `theorem`s (not `def`) — satisfies defLemma. Names are lowerCamelCase
  with no underscores inside identifier segments beyond the sanctioned `_implies_`/`Derivable`
  pattern already used repository-wide — satisfies defsWithUnderscore convention as practiced.

## 6. Verification Expectations

- **Zero sorry:** guaranteed — pure composition of landed, sorry-free theorems.
- **Axioms:** each composite's axiom footprint is the union of its two constituents. The
  classical bridges already rely on classical DNE/Peirce (`rcp`, `double_negation`), so the
  expected closure is exactly `[propext, Classical.choice, Quot.sound]`. Recommend confirming
  with `lean_verify` (fully-qualified, e.g. `Cslib.Logic.Modal.ms5Derivable_implies_s5Derivable`)
  or `#print axioms` on the 8 new names during implementation.
- **Build:** scoped `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Modularity` after
  editing, then full CI order (`lake build`, `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`, and `lake shake` if desired) before PR.
- **Reuse-first check:** No new abstraction is warranted; all needed lifts
  (`Derivable_mono`, `Derivable_of_axiom_derivable`) and edges pre-exist. This is strictly a
  composition/wiring task.

## 7. No Gaps

There are no missing intermediate edges. Every rung (K/T/S4/S5) has both its Axis-B edge (from
both minimal and constructive bases) and its Int→Classical bridge already proved and landed.
The task reduces to: add 1 import + 8 one-line theorems (with docstrings) + verify. Suitable for
a single low-effort implementation phase.
