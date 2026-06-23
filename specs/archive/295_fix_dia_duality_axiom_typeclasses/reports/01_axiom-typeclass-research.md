# Research Report: Add HasAxiomDiaDualityFwd/Back Typeclasses

## Task

Add `HasAxiomDiaDualityFwd` and `HasAxiomDiaDualityBack` typeclasses to
`Cslib/Foundations/Logic/ProofSystem.lean` to complete the axiom-typeclass pairing pattern.

## Findings

### Axiom Definitions (Axioms.lean, lines 196-219)

The axioms are defined in a `DiaDuality` section requiring `[HasBot F] [HasImp F] [HasBox F] [HasDia F]`:

```lean
protected abbrev AxiomDiaDualityFwd (φ : F) : F :=
  HasImp.imp (HasDia.dia φ)
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)

protected abbrev AxiomDiaDualityBack (φ : F) : F :=
  HasImp.imp
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
    (HasDia.dia φ)
```

Both take a single universally quantified formula `φ : F`.

### Existing Typeclass Pattern (ProofSystem.lean)

Every other axiom in Axioms.lean has a corresponding `HasAxiom*` typeclass. The pattern is:

```lean
/-- The proof system proves {axiom description}. -/
class HasAxiom{Name} where
  {fieldName} {vars : F} : InferenceSystem.DerivableIn S (Axioms.{AxiomName} vars)
```

The sections in ProofSystem.lean group axiom typeclasses by their connective requirements:

| Section | Connectives | Lines |
|---------|-------------|-------|
| `AxiomClasses` | `[HasBot F] [HasImp F]` | 111-133 |
| `AndOrAxiomClasses` | + `[HasAnd F] [HasOr F]` | 137-165 |
| `ModalAxiomClasses` | + `[HasBox F]` (later `[HasUntil F]`) | 167-204 |
| `TemporalAxiomClasses` | + `[HasUntil F] [HasSince F]` | 208-321 |

### Gap Analysis

The DiaDuality axioms require `[HasDia F]`, which is not available in any existing section.
The `ModalAxiomClasses` section only has `[HasBox F]` -- not `[HasDia F]`.

### Insertion Point

Insert a new `DiaDualityAxiomClasses` section between `ModalAxiomClasses` (ends line 204)
and `TemporalAxiomClasses` (starts line 208). This follows the file's organizational pattern
of grouping axiom typeclasses by connective requirements.

### Proposed Implementation

```lean
/-! ### Diamond Duality Axiom Typeclasses -/

section DiaDualityAxiomClasses

variable (S : Type*) [HasBot F] [HasImp F] [HasBox F] [HasDia F] [InferenceSystem S F]

/-- The proof system proves diamond duality forward: ◇φ → ¬□¬φ. -/
class HasAxiomDiaDualityFwd where
  diaDualityFwd {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.AxiomDiaDualityFwd φ)

/-- The proof system proves diamond duality backward: ¬□¬φ → ◇φ. -/
class HasAxiomDiaDualityBack where
  diaDualityBack {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.AxiomDiaDualityBack φ)

end DiaDualityAxiomClasses
```

### Dependencies

- **Upstream**: `HasDia` from `Connectives.lean`, `AxiomDiaDualityFwd`/`Back` from `Axioms.lean`
  (both already imported by ProofSystem.lean via `Axioms.lean` -> `Connectives.lean`)
- **Downstream**: No existing bundled proof system class or instance references these axioms yet.
  They will be consumed when proof systems with primitive `HasDia` are formalized.

### Risks

None. This is a purely additive change with no existing consumers to break.
