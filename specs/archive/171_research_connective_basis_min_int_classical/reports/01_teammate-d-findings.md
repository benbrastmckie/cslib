# Teammate D (Horizons) Findings: Strategic Analysis of Connective-Basis Design

## Overview

This report analyzes the long-term strategic implications of the connective-basis decision
for propositional logic in CSLib, with particular attention to how this decision cascades
across the entire multi-logic architecture.

---

## Key Findings

### Finding 1: The Minimal-Basis Approach Is Already the Project Standard

The current codebase has already committed to the `{atom, bot, imp}` primitive basis
for all four formula types:

| Module | Primitive Constructors |
|--------|------------------------|
| `Cslib.Logic.PL.Proposition` | `atom`, `bot`, `imp` |
| `Cslib.Logic.Modal.Proposition` | `atom`, `bot`, `imp`, `box` |
| `Cslib.Logic.Temporal.Formula` | `atom`, `bot`, `imp`, `untl`, `snce` |
| `Cslib.Logic.Bimodal.Formula` | `atom`, `bot`, `imp`, `box`, `untl`, `snce` |

Each formula type derives `neg`, `top`, `and`, `or`, and `iff` as `abbrev` connectives
using the Lukasiewicz convention (`neg φ := imp φ bot`, etc.). This pattern is uniform,
mature, and already working. The `Connectives.lean` module in `Foundations/Logic/` defines
the typeclass hierarchy (`HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`,
`PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`,
`BimodalConnectives`) specifically to make this composable.

**Strategic implication**: This is not a decision still being made - it is the committed
architecture. Any "full primitives" alternative would require rewriting four formula types,
their derived connectives, all downstream proof systems, and the typeclass infrastructure.
The cost is prohibitive.

### Finding 2: Logic Strength Hierarchy Is Handled at the Proof System Level, Not Formula Level

`Cslib.Foundations.Logic.ProofSystem` already defines the three-level Hilbert hierarchy:

```lean
class MinimalHilbert (S : Type*) ...       -- {K, S, MP}
class IntuitionisticHilbert (S : Type*) ...-- extends MinimalHilbert + EFQ
class ClassicalHilbert (S : Type*) ...     -- extends IntuitionisticHilbert + Peirce
```

`Cslib.Logics.Propositional.Defs` defines the corresponding semantic objects:

```lean
abbrev MPL : Theory (Atom) := ∅           -- minimal propositional logic
abbrev IPL : Theory Atom := Set.range (⊥ → ·)  -- adds ex falso
abbrev CPL : Theory Atom := Set.range (¬¬· → ·) -- adds DNE
```

And `Theory.IsIntuitionistic`/`IsClassical` are typeclasses for semantic classification.

This is exactly the Johansson hierarchy implemented correctly: one formula type, three
logics distinguished by their inference rules. The formula syntax is shared; the logic
is specified by which axioms/rules are in scope.

**Strategic implication**: The Johansson insight is already encoded. Minimal, intuitionistic,
and classical logic share the same `Proposition` type but differ in their `Theory` or
`HilbertXxx` tag. A "formula parametric over logic strength" would duplicate what already
exists through the typeclass approach.

### Finding 3: The Typeclass Architecture Scales Well and Is Already Validated

The composability chain is demonstrably working:
- `Foundations/Logic/Connectives.lean` defines the reusable connective typeclasses
- `Foundations/Logic/Axioms.lean` defines polymorphic axiom `abbrev`s (e.g., `ImplyK`,
  `EFQ`, `Peirce`, `AxiomK`, ..., `ModalFuture`) parameterized by `HasBot`, `HasImp`,
  `HasBox`, etc.
- `Foundations/Logic/ProofSystem.lean` bundles these into `MinimalHilbert`,
  `IntuitionisticHilbert`, ..., `BimodalTMHilbert`

This architecture means that new logics can be added by:
1. Defining a new inductive formula type with the appropriate constructors
2. Registering it as an instance of the appropriate bundled connective class
3. Declaring a tag type and proving the required `HasAxiom*` instances

The modal, temporal, and bimodal extensions all follow this exact pattern. It scales.

### Finding 4: The Johansson 1937 Reference Is Missing From references.bib

Searching `references.bib` confirms:
- `Heyting1930` is present
- `Gentzen1935` is present
- `Prawitz1965` is present
- `Church1956` is present

But **Johansson 1937 ("Der Minimalkalkül") is absent**. The current `Connectives.lean`
does cite Heyting and Gentzen but does not cite Johansson. Given that `MinimalHilbert`
is defined and named after Johansson's system, this is a citation gap.

### Finding 5: The Natural Deduction System Has `botE` (EFQ) Built In As a Primitive Rule

`NaturalDeduction/Basic.lean` defines:

```lean
inductive Theory.Derivation ... where
  | ax ...
  | ass ...
  | impI ...
  | impE ...
  | botE ... : Derivation Γ ⊥ → Derivation Γ A   -- ex falso quodlibet
```

This means the current natural deduction system is **intuitionistic**, not minimal.
The `botE` rule is a primitive, not derived from the theory. To support genuine minimal
logic in natural deduction (where `botE` is NOT available), the derivation type would
need to parameterize over whether `botE` is available - or separate derivation types
would be needed for MinML/IPL/CPL.

This is an internal inconsistency: `Propositional.Defs` defines `MPL := ∅` (minimal),
but the `Theory.Derivation` type includes `botE` unconditionally. Minimally-labeled
theorems proved with `botE` are actually intuitionistic theorems.

### Finding 6: Collaboration With PR #607 (Montesi) Matters More Than Technical Perfection

The maintainer (fmontesi) has an active PR (#607) that takes a different approach.
Key strategic considerations:

- CSLib is a **collaborative library** following Mathlib governance norms
- Maintainer PRs typically set precedents for the project
- If PR #607 is merged before PR #635, the architecture in #635 may need adaptation
- The eric-wieser suggestion to co-opt Mathlib classes (e.g., `Lattice`, `BooleanAlgebra`,
  `HeytingAlgebra`) is a legitimate path to reduce duplication
- The `HasBot`/`HasImp` etc. classes in `Connectives.lean` overlap with Mathlib's
  `Bot`, `Top`, `Sup`, `Inf`, `HImp` classes - this may be a source of future friction

**Strategic implication**: The author should prioritize reconciliation with fmontesi's
approach rather than competing with it. The best outcome is a merged design.

---

## Recommended Approach (Long-Term Best Path)

### Primary Recommendation: Preserve the {bot, imp} Minimal Basis, Parameterize Proof Systems

The `{atom, bot, imp}` basis is the correct long-term architecture for the following reasons:

1. **Induction economy**: Every inductive proof over formulas has 3 cases instead of 5-7.
   With four formula types and extensive metalogic (completeness, decidability, etc.),
   this compounds to a substantial reduction in proof obligation size.

2. **Definitional unfolding**: `neg`, `and`, `or` reduce to `imp`/`bot` definitionally,
   so `simp`/`grind` handle them automatically without bridging lemmas.

3. **Consistent with modal and temporal extensions**: `Modal.Proposition` already uses
   `{atom, bot, imp, box}` and `Temporal.Formula` uses `{atom, bot, imp, untl, snce}`.
   The propositional fragment is the common sub-logic of all four formula types.

4. **Literature alignment**: Church 1956, Chagrov-Zakharyaschev 1997, and the CSLib
   roadmap all use the Lukasiewicz convention of deriving connectives from `{imp, bot}`.

### Secondary Recommendation: Fix the botE Inconsistency for Minimal Logic Support

If CSLib wants genuine support for minimal logic (not just the label `MPL := ∅`):

**Option A**: Parameterize `Theory.Derivation` over whether `botE` is available:
```lean
inductive Theory.Derivation (withEFQ : Bool) ... where
  | botE ... : withEFQ = true → Derivation withEFQ Γ ⊥ → Derivation withEFQ Γ A
```

**Option B**: Define separate derivation types `MinDerivation` and `IPLDerivation`,
related by a coercion.

**Option C** (recommended): Keep the current derivation type for intuitionistic/classical
use, and add a separate `Minimal.Derivation` that omits `botE`. The three logics would
then have separate derivation types but share the formula type. This matches the
pattern in `ProofSystem.lean` where `MinimalHilbert`, `IntuitionisticHilbert`, and
`ClassicalHilbert` are separate typeclasses.

### Tertiary Recommendation: Add Johansson 1937 to references.bib

```bibtex
@article{Johansson1937,
  author       = {Johansson, Ingebrigt},
  title        = {Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus},
  journal      = {Compositio Mathematica},
  volume       = {4},
  pages        = {119--136},
  year         = {1937},
}
```

This citation should be added to `Connectives.lean` and `ProofSystem.lean` docstrings
since `MinimalHilbert` is named after Johansson's system.

### On Mathlib Class Alignment (eric-wieser's Suggestion)

Consider whether the following Mathlib classes could replace CSLib's hand-rolled ones:

| CSLib Class | Mathlib Equivalent | Notes |
|-------------|-------------------|-------|
| `HasBot F` | `Bot F` | Direct match |
| `HasImp F` | `HImp F` (Heyting implication) | Different semantics! |
| `PropositionalConnectives F` | `HeytingAlgebra F` | Overkill; adds `inf`, `sup`, `le` |
| None yet | `BooleanAlgebra F` | For classical logic completeness |

The key issue: Mathlib's `HImp` is for Heyting algebras (lattice-based), while CSLib's
`HasImp` is for syntactic implication on formula types. These are different. The Mathlib
classes add unnecessary algebraic structure for pure proof theory.

**Recommendation**: Keep CSLib's `HasBot`/`HasImp`/`HasBox` typeclasses as defined.
They are lighter-weight and better suited to syntax-only formula types. Mathlib alignment
should be pursued only if a compelling concrete benefit is identified.

---

## Evidence/Examples

### Evidence 1: Formula Types Already Follow the Composable Pattern

All four formula types register as instances of their respective bundled classes:

```lean
-- PL
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot; imp := .imp

-- Modal
instance : ModalConnectives (Proposition Atom) where
  bot := .bot; imp := .imp; box := .box

-- Temporal
instance : TemporalConnectives (Formula Atom) where
  bot := .bot; imp := .imp; untl := .untl; snce := .snce

-- Bimodal
instance : BimodalConnectives (Formula Atom) where
  bot := .bot; imp := .imp; box := .box; untl := .untl; snce := .snce
```

This uniform registration pattern is clean, working, and extensible.

### Evidence 2: Roadmap Shows Multi-Logic Architecture Is Mature and Stable

The ROADMAP.md shows:
- Bimodal embedding (PropositionalEmbedding, ModalEmbedding, TemporalEmbedding) is complete
- The dependency structure `Propositional -> Modal, Temporal -> Bimodal` is the established order
- Remaining work is completeness theorems, not architecture changes

Disrupting the formula type now would invalidate this large body of completed work.

### Evidence 3: The Proof System Hierarchy Already Encodes Johansson's Insight

```
ProofSystem.lean:
MinimalHilbert -> IntuitionisticHilbert -> ClassicalHilbert
     |                     |                      |
  {K, S, MP}         + HasAxiomEFQ           + HasAxiomPeirce
```

This is exactly the logical hierarchy: minimal < intuitionistic < classical.
The formula type is shared; the logics differ by their axioms.

### Evidence 4: The botE Inconsistency in NaturalDeduction/Basic.lean

The `Derivation` comment says "defines an instance of `InferenceSystem T Sequent`"
and lists primitives as "axiom, assumption, implication intro/elim, and ex falso quodlibet".
EFQ is listed as primitive, not derived. This matches IPL semantics, not MPL.

The abbreviation `abbrev MPL : Theory (Atom) := ∅` says the minimal logic uses
an empty theory, but `Theory.Derivation` always includes `botE`. So provability
in `MPL` (empty theory, `botE` available) is actually intuitionistic logic, not
Johansson's minimal logic.

---

## Roadmap Alignment Assessment

The Roadmap says the logic library follows:

> Every component lives at the most general level it can compile at.

This principle supports the `{bot, imp}` basis: it is the most general (minimal) basis
from which classical logic can be derived by adding axioms. Adding `and`/`or` as primitives
would violate this principle by baking in classical-specific information at the syntactic level.

The "reuse-first" philosophy of CSLib (always check Foundations/ before recommending
new abstractions) is satisfied here: the formula types, connective typeclasses, polymorphic
axioms, and proof system hierarchy all already exist in Foundations. No new abstractions
are needed.

---

## Creative / Unconventional Approaches

### Could CSLib Use a Single Parametric Formula Type?

Theoretically, one could define:

```lean
inductive Formula (Sig : ConnectiveSignature) (Atom : Type u) : Type u where
  | atom (x : Atom)
  | fromSig : Sig.apply (Formula Sig Atom) → Formula Sig Atom
```

where `ConnectiveSignature` lists which constructors exist. This is essentially
the "algebraic theory" / "syntax functor" approach from categorical logic.

**Assessment**: This is technically elegant but would sacrifice Lean's native
`inductive` machinery (pattern matching, recursion, `DecidableEq` derivation).
The current approach of separate inductive types with identical structure but
different constructors is more practically effective in Lean 4. The typeclass
hierarchy provides the polymorphism benefits without sacrificing concrete types.

### Could the Proof System Be a Typeclass?

It already is: `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert` are
typeclasses. The question is whether the formula type should also be parameterized.

**Assessment**: Keeping formula types concrete (not parameterized) and proof systems
abstract (typeclasses) is the right division. Concrete formula types support efficient
computation and pattern matching; abstract proof systems support polymorphic theorems.

---

## Confidence Level

| Finding | Confidence |
|---------|------------|
| {bot, imp} basis is the committed standard | High |
| Logic hierarchy is at proof system level, not formula level | High |
| Typeclass architecture scales well | High |
| Johansson reference is missing | High |
| botE inconsistency for genuine minimal logic | High |
| Collaboration with PR #607 is strategically important | Medium |
| Mathlib class alignment not recommended | Medium |
| Parametric formula type not recommended | High |

---

## Summary for Synthesis

The strategic answer to the connective-basis question is: **the decision is already
made and is correct**. The `{atom, bot, imp}` basis is uniform across all four
formula types, validated by the complete bimodal logic formalization, and supported
by the `Connectives.lean` typeclass hierarchy.

The main actionable gaps are:
1. Fix the `botE` inconsistency: `MPL` in `Defs.lean` should have no `botE` in its
   natural deduction system (currently, every `Theory.Derivation` includes `botE`)
2. Add Johansson 1937 to `references.bib`
3. Reconcile with PR #607 (Montesi's approach) rather than competing

The connective-basis for minimal, intuitionistic, and classical propositional logic
should remain `{atom, bot, imp}`, with logic strength determined solely by the
proof system (axioms and inference rules).
