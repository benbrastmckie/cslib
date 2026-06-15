# Teammate D: Documentation Design
# Task #179 -- Add Diamond (dia) as Primitive Constructor

**Date**: 2026-06-14
**Focus**: Design specific documentation comments for each relevant location

---

## 1. BibKey Verification

Both required references are confirmed present in `/home/benjamin/Projects/cslib/references.bib`:

- **`Blackburn2001`**: Blackburn, de Rijke, Venema, *Modal Logic*, Cambridge University Press, 2001
- **`ChagrovZakharyaschev1997`**: Chagrov, Zakharyaschev, *Modal Logic*, Oxford University Press, 1997

**Citation format used in this codebase** (confirmed from multiple files):

In module-level docstrings (`/-! ... -/`):
```
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]
```

For inline references to specific theorems:
```
See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.3.
```

Short inline form (used in Cube.lean, ConservativeExtension.lean):
```
[Blackburn2001] Chapter 2
```

Both BibKeys are in `references.bib`. No new entries needed.

---

## 2. Current Documentation State

### `Cslib/Logics/Modal/Basic.lean` -- Module Docstring (lines 17-38)

Current "Primitives" subsection (lines 23-31):
```
## Primitives

The formula type uses `{atom, bot, imp, box}` as primitive constructors (no native `and`/`or`).
Negation, conjunction, disjunction, and diamond (possibility) are derived connectives via
the Lukasiewicz convention: `¬φ := φ → ⊥`, `φ ∧ ψ := ¬(φ → ¬ψ)`, `φ ∨ ψ := ¬φ → ψ`.
```

Current `Proposition.diamond` docstring (line 77):
```lean
/-- Possibility / diamond: ◇φ := ¬□¬φ -/
```

Current `Proposition.box` docstring (line 59):
```lean
  /-- Necessity / box. -/
```

### `Cslib/Foundations/Logic/Connectives.lean` -- `HasBox` (lines 70-73)

Current docstring:
```lean
/-- A type has a necessity (box) modality. -/
class HasBox (F : Type*) where
  /-- The necessity/box modality. -/
  box : F → F
```

Current `ModalConnectives` docstring (line 103):
```lean
/-- Modal connectives: propositional connectives plus necessity. -/
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F
```

### `Cslib/Foundations/Logic/Axioms.lean` -- B, 5, D axioms (lines 150-167)

Current docstrings include inline notes like:
```
/-- Symmetry axiom B: φ → □◇φ
    where ◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥ -/
```

The comment `where ◇φ = (□(φ → ⊥)) → ⊥` makes the classical substitution explicit. This is a
documentation debt: the comment documents the _encoded_ form but does not explain _why_ the
classical substitution is made.

### `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` -- `modalD` (lines 50-53)

Current docstring:
```lean
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥` -/
  | modalD (φ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
```

Similar pattern in B.lean (line 51-52) and K5.lean (line 51-53).

---

## 3. Drafted Comment Text by Location

### Location 1: `Basic.lean` -- Module Docstring, "Primitives" subsection

**Current**: Lines 22-31 of the `/-! # Modal Logic ... -/` block.

**Replace with**:
```
## Primitives

The formula type uses `{atom, bot, imp, box}` as primitive constructors. Negation, conjunction,
and disjunction are derived connectives via the Lukasiewicz convention:
`¬φ := φ → ⊥`, `φ ∧ ψ := ¬(φ → ¬ψ)`, `φ ∨ ψ := ¬φ → ψ`.

Box (`□`) is taken as the primitive modal operator rather than diamond (`◇`), following the
standard treatment in classical modal logic. The box operator corresponds to universal
quantification over accessible worlds, preserves conjunction (`□(φ ∧ ψ) ↔ □φ ∧ □ψ`), and
supports the necessitation rule (from `⊢ φ` conclude `⊢ □φ`). In classical modal logic,
diamond is interdefinable with box via `◇φ ↔ ¬□¬φ`, so choosing box as primitive is
without loss of generality. See [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
Chapter 1 and [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997] Section 1.1.

Diamond (`◇φ`) is currently derived as `¬□¬φ` using classical negation. This derivation is valid
in classical and intermediate logics but not in intuitionistic or minimal modal logic, where `◇φ`
and `¬□¬φ` are not interderivable. When non-classical modal logics are formalized in CSLib,
`◇` should be added as a primitive constructor and the dual equivalence `◇φ ↔ ¬□¬φ` should
become a theorem provable only under classical assumptions (Peirce's law or DNE), not a definition.
```

**Why**: This subsection currently omits the reason box is primitive. The user's concern is specifically
about explaining this design choice and flagging where primitive dia would matter.

---

### Location 2: `Basic.lean` -- `Proposition.diamond` abbrev (line 77-79)

**Current**:
```lean
/-- Possibility / diamond: ◇φ := ¬□¬φ -/
abbrev Proposition.diamond (φ : Proposition Atom) : Proposition Atom :=
  .neg (.box (.neg φ))
```

**Replace docstring with**:
```lean
/-- Possibility / diamond: ◇φ defined as `¬□¬φ`, i.e., `(□(φ → ⊥)) → ⊥`.

This is the classical dual of box. It relies on classical negation: from `◇φ ↔ ¬□¬φ`,
the forward direction (`◇φ → ¬□¬φ`) uses the semantic fact that if some accessible world
satisfies `φ`, then not all accessible worlds satisfy `¬φ`. The backward direction
(`¬□¬φ → ◇φ`) additionally uses the law of excluded middle to produce a witness world.

This derived form is valid in classical and S4-style intuitionistic modal logics (IPC + K)
but not in minimal modal logic. In non-classical settings, `◇` must be a primitive
constructor. See [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
Chapter 1 for the classical treatment. -/
```

**Why**: The current one-liner does not explain the classical dependency or when this would fail.

---

### Location 3: `Connectives.lean` -- `HasBox` class (lines 70-73)

**Current**:
```lean
/-- A type has a necessity (box) modality. -/
class HasBox (F : Type*) where
  /-- The necessity/box modality. -/
  box : F → F
```

**Replace class docstring with**:
```lean
/-- A type has a necessity (box) modality.

Box (`□`) is the canonical modal primitive because it has simpler algebraic properties than
diamond in the classical setting: it preserves conjunction (`□(φ ∧ ψ) ↔ □φ ∧ □ψ`),
distributes over implication (axiom K: `□(φ → ψ) → □φ → □ψ`), and is the subject of
the necessitation rule (if `⊢ φ` then `⊢ □φ`). Necessity corresponds to universal
quantification over accessible worlds in Kripke semantics.

In classical modal logic, diamond is defined as `◇φ := ¬□¬φ`, so `HasBox` alone suffices for
classical systems. For non-classical modal logics (intuitionistic modal logic, minimal modal
logic), diamond is not definable from box via negation, and a separate `HasDia` typeclass
is needed. See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]
Section 1.1. -/
```

**Why**: The single-line docstring gives no motivation for why box and not diamond. The user asked
specifically for this explanation.

---

### Location 4: `Connectives.lean` -- `ModalConnectives` class (line 103-104)

**Current**:
```lean
/-- Modal connectives: propositional connectives plus necessity. -/
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F
```

**Replace docstring with**:
```lean
/-- Modal connectives: propositional connectives plus necessity (box).

Box is chosen as the sole primitive modal operator following the standard classical treatment
([Blackburn2001] Chapter 1). Diamond (possibility) is derived as `◇φ := ¬□¬φ` for all
formula types instantiating this class, using the classical negation already available via
`HasBot` and `HasImp`. Non-classical modal logics require extending this class with `HasDia`. -/
```

---

### Location 5: `Axioms.lean` -- `AxiomB` (lines 150-154)

**Current**:
```lean
/-- Symmetry axiom B: φ → □◇φ
    where ◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥ -/
protected abbrev AxiomB (φ : F) : F :=
  HasImp.imp φ (HasBox.box
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))
```

**Replace docstring with**:
```lean
/-- Symmetry axiom B: `φ → □◇φ`.

Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `HasDia` is not
yet part of `ModalConnectives`. The expanded form is: `φ → □((□(φ → ⊥)) → ⊥)`.
Corresponds to symmetry of the accessibility relation. -/
```

---

### Location 6: `Axioms.lean` -- `Axiom5` (lines 156-161)

**Current**:
```lean
/-- Euclidean axiom 5: ◇φ → □◇φ
    where ◇φ = (□(φ → ⊥)) → ⊥ -/
protected abbrev Axiom5 (φ : F) : F :=
  HasImp.imp
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
    (HasBox.box (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))
```

**Replace docstring with**:
```lean
/-- Euclidean axiom 5: `◇φ → □◇φ`.

Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `HasDia` is not
yet part of `ModalConnectives`. The expanded form is:
`((□(φ → ⊥)) → ⊥) → □((□(φ → ⊥)) → ⊥)`.
Corresponds to right-Euclideanness (if `wRu` and `wRv` then `uRv`) of the accessibility relation. -/
```

---

### Location 7: `Axioms.lean` -- `AxiomD` (lines 163-167)

**Current**:
```lean
/-- Seriality axiom D: □φ → ◇φ
    where ◇φ = (□(φ → ⊥)) → ⊥ -/
protected abbrev AxiomD (φ : F) : F :=
  HasImp.imp (HasBox.box φ)
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
```

**Replace docstring with**:
```lean
/-- Seriality axiom D: `□φ → ◇φ`.

Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `HasDia` is not
yet part of `ModalConnectives`. The expanded form is: `□φ → ((□(φ → ⊥)) → ⊥)`.
Corresponds to seriality of the accessibility relation (every world has a successor). -/
```

---

### Location 8: `ProofSystem/Instances/D.lean` -- `DAxiom.modalD` (lines 50-53)

**Current**:
```lean
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥` -/
  | modalD (φ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
```

**Replace docstring with**:
```lean
  /-- D / seriality: `□φ → ◇φ`.
  Diamond is encoded using the classical derived form `◇φ = ¬□¬φ`, inline-expanded as
  `(□(φ → ⊥)) → ⊥`. See `Axioms.AxiomD` for the abstract form. -/
```

**Similar pattern applies to**: `B.lean` (`modalB`), `K5.lean` (`modalFive`), and all other
instance files that currently have `where ◇φ = ...` inline in their docstrings. The pattern
is: reference `Axioms.AxiomB` / `Axioms.Axiom5` / `Axioms.AxiomD` and note the classical encoding.

---

## 4. Minimal Scope for "Documentation Only" Revision

If the task is revised to add documentation without changing the formula type, the scope is:

### Files to Modify

**File 1: `Cslib/Logics/Modal/Basic.lean`**
- Lines 22-31: Replace "Primitives" subsection in module docstring (Location 1 above)
- Lines 77-79: Replace `Proposition.diamond` docstring (Location 2 above)

**File 2: `Cslib/Foundations/Logic/Connectives.lean`**
- Lines 70-73: Expand `HasBox` class docstring (Location 3 above)
- Lines 103-104: Expand `ModalConnectives` docstring (Location 4 above)

**File 3: `Cslib/Foundations/Logic/Axioms.lean`**
- Lines 150-154: Expand `AxiomB` docstring (Location 5 above)
- Lines 156-161: Expand `Axiom5` docstring (Location 6 above)
- Lines 163-167: Expand `AxiomD` docstring (Location 7 above)
- Add `[ChagrovZakharyaschev1997]` to the modal section reference list (currently no `## References` subsection in the modal section)

**File 4: `Cslib/Logics/Modal/ProofSystem/Instances/D.lean`** (and equivalent in B.lean, K5.lean, etc.)
- `modalD` constructor docstring (Location 8 above)

### What Does NOT Need Changing for Documentation-Only

- Formula constructors (no new `.dia` constructor)
- Proof terms (no proof changes)
- Typeclass hierarchy (no `HasDia` yet)
- All 15 `Metalogic/Systems/*/` files
- Satisfies definition
- `lake test` / `lake build` behavior -- all changes are comments only

### Estimated Effort

Documentation-only scope:
- 4 files
- ~10 docstring edits
- No proof obligations
- Estimated time: 30-45 minutes

Full task 179 (add `.dia` primitive + documentation): 10 hours (from plan)

---

## 5. Citation Format for New Comments

All citations in this codebase use the Mathlib bracket notation in `/-! ... -/` blocks:
```
[Author, *Title*][BibKey]
```

For inline references (inside `/-- ... -/` doc comments):
- Full form (first mention): `[P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]`
- Short form (subsequent): `[Blackburn2001]`

Both `Blackburn2001` and `ChagrovZakharyaschev1997` are confirmed in `references.bib`. No new
BibTeX entries are required for the documentation changes proposed here.

**Recommended specific sections to cite**:
- Box as primitive: [Blackburn2001] Chapter 1.1, [ChagrovZakharyaschev1997] Section 1.1
- Classical duality `◇φ ↔ ¬□¬φ`: [Blackburn2001] Definition 1.15
- Intuitionistic modal logic (future note): Fischer Servi 1984, Simpson 1994 (not in bib yet)

For the intuitionistic modal logic note in Location 1 and Location 2, no citation is strictly
needed if the note is framed as a forward-looking design note rather than a claim about a
specific published result. If a citation is preferred, `ChagrovZakharyaschev1997` Chapter 8
covers the contrast between classical and constructive modal operators.

---

## 6. Summary

The user's concern has two parts:

1. **"include comments about this in the appropriate places"**: Eight specific docstring locations
   were identified across four files. Drafts are provided above for each location.

2. **"clarify why box is taken to be primitive in classical modal systems"**: The core explanation
   belongs in three places: the `HasBox` class docstring (philosophical/algebraic reason),
   the `ModalConnectives` docstring (design decision), and the "Primitives" subsection of
   `Basic.lean` (contextualizes the specific formula type). The reason is: box corresponds to
   universal quantification, supports necessitation, preserves conjunction, and in classical
   logic diamond is recoverable as `¬□¬φ`. In non-classical settings this recovery fails.

Both BibKeys are confirmed present. No new `.bib` entries needed. The documentation-only
revision (4 files, ~10 edits, no proof changes) can be merged independently of the full
primitive-dia implementation (task 179 full scope).
