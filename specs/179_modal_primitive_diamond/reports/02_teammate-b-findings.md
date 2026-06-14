# Teammate B Findings: Alternative Approaches to Making Diamond Primitive

## Task 179 — modal_primitive_diamond

---

## Key Findings

### 1. Current State (Corrected from Task Description)

The task description mentions `{atom, bot, imp, and, or, box}` as the current primitives. **This is incorrect.** The actual `Modal.Proposition` inductive type in `Cslib/Logics/Modal/Basic.lean` has only **four primitive constructors**:

```
{atom, bot, imp, box}
```

`and`, `or`, `neg`, `top`, and `diamond` are all `abbrev`-derived connectives using the Lukasiewicz convention:
- `neg φ := φ → ⊥`
- `and φ ψ := ¬(φ → ¬ψ)`
- `or φ ψ := ¬φ → ψ`
- `diamond φ := ¬□¬φ`

The `Connectives.lean` typeclass design makes this explicit: `ModalConnectives` extends `HasBot + HasImp + HasBox` with no `HasDia` or `HasAnd`/`HasOr`. Axiomatic diamond uses the fully-expanded negation of box form, as seen in `Axioms.lean`:

```lean
-- AxiomB: φ → □◇φ, where ◇φ = (□(φ → ⊥)) → ⊥
protected abbrev AxiomB (φ : F) : F :=
  HasImp.imp φ (HasBox.box
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))
```

This means all modal axioms involving diamond (B, 5, D) are already fully written out without any `HasDia` dependency — they expand diamond inline. **This is the critical architectural decision that shapes all alternatives.**

### 2. Alternative A: Keep Diamond Derived, Add a `HasDia` Typeclass

**Proposal**: Add `HasDia` to `Cslib/Foundations/Logic/Connectives.lean`, let classical logics provide a default instance that expands `dia φ := neg (box (neg φ))`, and let intuitionistic logics provide a primitive instance.

**Assessment: Structurally feasible but solves the wrong problem.**

The Connectives module already has this exact pattern for `HasAnd`/`HasOr`: the `Connectives.lean` docstring explicitly says that `and`/`or` are *primitive constructors in `PL.Proposition`* but Lukasiewicz-derived in `Modal.Proposition`, and that making them primitive is correct for intuitionistic support. `HasDia` would be analogous.

However, a `HasDia` typeclass alone does not solve the core problem. The axioms in `Axioms.lean` — `AxiomB`, `Axiom5`, `AxiomD` — are written by expanding diamond inline (they do not call any `dia` field). The completeness proofs in `Metalogic/Completeness.lean` use the definitional equality `Proposition.diamond φ = neg (box (neg φ))`. If `HasDia.dia` were introduced as a new primitive on `Modal.Proposition`, all these axiom definitions and proof terms would need rewriting to use `HasDia.dia` instead of the expansion.

**Verdict**: `HasDia` is the right interface abstraction, but adding it without making `Proposition.dia` a primitive constructor leaves the axioms still expanding diamond via negation — the same classical derivation problem remains. The typeclass alone does not unlock intuitionistic logics.

### 3. Alternative B: Parameterize Proposition Over Its Connective Set

**Proposal**: A type-level flag (e.g., `inductive PropKind | classical | intuitionistic`) parameterizing the proposition type, with diamond being derived in the classical branch and primitive in the intuitionistic branch.

**Assessment: Architecturally incompatible with the existing design.**

The existing `Connectives.lean` module (which predates task 179) deliberately chose the opposite approach: **one concrete inductive type per logic level, registered as instances of connective typeclasses**. The comments in that file are explicit:

> "Each concrete formula type duplicates its constructors (Lean 4 cannot extend inductives) and registers as an instance of the appropriate bundled class."

Type-level parameterization of the inductive type would require Lean 4 dependent type machinery that creates significant universe-level friction and breaks the clean typeclass dispatch. Mathlib itself does not use this pattern for its classical/constructive variants — it instead uses separate types with shared interfaces.

**Verdict**: Not recommended. The design philosophy of CSLib is explicitly against parameterized formula types.

### 4. Alternative C: Separate Proposition Types Per Logic Family

**Proposal**: `Classical.Proposition` (current design, derived diamond), `Intuitionistic.Proposition` (primitive diamond), with shared metatheory via typeclasses.

**Assessment: Viable in principle, but premature and high-cost.**

The existing `PL.Proposition` (with primitive `and`/`or`) and `Modal.Proposition` (without, using Lukasiewicz) already demonstrate that CSLib is willing to have separate types for different propositional bases. The embedding in `FromPropositional.lean` is a worked example of the cross-type infrastructure needed.

However, creating a separate `Intuitionistic.Modal.Proposition` type now would require:
- A separate `{atom, bot, imp, dia, box}` inductive
- Separate `Satisfies`, `DerivationTree`, `CanonicalModel`, `truth_lemma` etc. for the intuitionistic version
- Cross-type embedding theorems

This is a much larger project than task 179 envisions. And crucially: it would be the right way to formalize IK/IS4 eventually, but it is not the minimal step to make the *classical* systems correct and the library logic-family neutral.

**Verdict**: Correct direction for a future task dedicated to intuitionistic modal logic. Not the right scope for task 179.

### 5. Alternative D: Do Nothing Now

**Proposal**: Keep `diamond` derived, add primitive `dia` only when intuitionistic logics are formalized.

**Assessment: Has a real point-of-no-return concern.**

The task description asks about the refactoring cost if `dia` is added after 50+ files exist. The current file count across `Cslib/Logics/Modal/` already has:
- `Basic.lean`, `Denotation.lean`, `LogicalEquivalence.lean` (core definitions)
- 3 truth lemma families with `| .box φ` cases (no separate `.dia` case needed if derived)
- ~15 ProofSystem instance files
- ~30 Metalogic files

**The critical insight is that refactoring cost is asymmetric**. Changing from derived to primitive diamond requires adding a `| .dia` case to EVERY recursive definition and proof by induction on `Proposition`. These include `Satisfies`, `denotation`, `Context`, `height`, all truth lemma inductions, and all subformula closure computations. The scope assessment in the primary research report (`~55 files`) is accurate.

The point of no return is already approaching. The current state of ~55 Modal files represents near-maximum refactoring cost. The Temporal and Bimodal logics (which have ~150 combined files) embed Modal via `ModalEmbedding.lean` — if Modal adds a primitive `.dia`, the embedding must be updated too.

**Verdict**: Deferring is inadvisable. The cost grows linearly with file count, and the modal logic section is already substantial.

### 6. Upstream Alignment Check

The upstream CSLib (`Cslib/Logics/Bimodal/Syntax/Formula.lean`) confirms that `Bimodal.Formula` defines diamond as:
```lean
abbrev Formula.diamond (φ : Formula Atom) : Formula Atom :=
  Formula.neg (Formula.box (Formula.neg φ))
```

And in `ModalEmbedding.lean`:
```lean
(Modal.Proposition.diamond φ).toBimodal = Bimodal.Formula.diamond φ.toBimodal := rfl
```

This confirms that:
1. The upstream also uses derived diamond (same classical limitation as the fork)
2. The embedding proves `diamond` is preserved definitionally — if `Modal.Proposition` gains a primitive `.dia` constructor, this `rfl` proof breaks and must be replaced with a semantic coherence proof

**Upstream is equally affected by the limitation**; making diamond primitive in `Modal.Proposition` is an improvement that the upstream also needs, but that neither has yet done.

---

## Analysis of How Diamond Actually Appears in Proofs

Looking at the 14 occurrences of `Proposition.diamond` in the codebase, they fall into exactly two categories:

**Category 1: Type signatures of axiom hypotheses** (in `MCS.lean`, `Completeness.lean`)
```lean
h_B : ∀ (φ : Proposition Atom),
  Axioms (φ.imp (Proposition.box (Proposition.diamond φ)))
```
These reference `Proposition.diamond`, which would remain valid even if `diamond` became a primitive constructor instead of an `abbrev` — because `Proposition.diamond φ` would still be a valid term.

**Category 2: Proof steps that rely on definitional equality**
```lean
-- Completeness.lean line 113 area:
unfold Proposition.diamond Proposition.neg  -- relies on abbrev expansion
```
If `.diamond` becomes a primitive constructor, `unfold Proposition.diamond` would not reduce it further — you cannot `unfold` a constructor. Proofs that rely on this unfolding would need to use the `Satisfies.diamond_iff` rewrite lemma instead.

This means the change has two components:
1. **Syntactic**: Add `.dia` constructor, change `diamond` `abbrev` to unfold to `.dia`, add `| .dia` cases
2. **Proof repair**: Replace `unfold Proposition.diamond Proposition.neg` patterns with `rw [Satisfies.diamond_iff]` or `simp [Satisfies]`

---

## Recommended Approach

**Make `dia` primitive in `Modal.Proposition` now, as task 179 proposes.**

The alternatives analysis converges on this conclusion:
- The `HasDia` typeclass alone is insufficient (does not fix classical derivation in axioms)
- Parameterized types are incompatible with the CSLib design philosophy
- Separate intuitionistic types are correct long-term but out of scope
- Deferral increases cost monotonically and the point of no return is already close

The right implementation has three components:

**Component 1: Add `HasDia` to `Connectives.lean`**
```lean
class HasDia (F : Type*) where
  dia : F → F
```
Update `ModalConnectives` to `extends PropositionalConnectives F, HasBox F, HasDia F`.

**Component 2: Add `.dia` constructor to `Modal.Proposition`**
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Proposition Atom)
  | box (φ : Proposition Atom)
  | dia (φ : Proposition Atom)  -- NEW
  deriving DecidableEq, BEq
```
Change `diamond` from an `abbrev` that expands to a notation that resolves to `.dia`:
```lean
-- Keep the ◇ notation pointing to .dia
@[inherit_doc] scoped prefix:40 "◇" => Proposition.dia
```
And provide the classical equivalence as a theorem (not a definition):
```lean
-- Classical systems: this holds as a theorem when Peirce's law is available
theorem Proposition.diamond_eq_neg_box_neg [ClassicalModal] (φ : Proposition Atom) :
    ◇φ ↔ ¬□¬φ := ...
```

**Component 3: Update `Axioms.lean` to use `HasDia`**
The axiomatic forms of B, 5, D use `HasDia.dia` instead of the manually expanded negation:
```lean
protected abbrev AxiomB (φ : F) : F :=
  HasImp.imp φ (HasBox.box (HasDia.dia φ))  -- φ → □◇φ

protected abbrev Axiom5 (φ : F) : F :=
  HasImp.imp (HasDia.dia φ) (HasBox.box (HasDia.dia φ))  -- ◇φ → □◇φ

protected abbrev AxiomD (φ : F) : F :=
  HasImp.imp (HasBox.box φ) (HasDia.dia φ)  -- □φ → ◇φ
```

**`Satisfies` update**: Add the `.dia` case directly (no negation involved):
```lean
| .dia φ => ∃ w', m.r w w' ∧ Satisfies m w' φ
```
The `Satisfies.diamond_iff` theorem becomes trivial (`Iff.rfl`). The `Satisfies.diamond_iff_exists` theorem (used by B, 5, D, 4 axiom proofs) also becomes `Iff.rfl`.

**Proof repair cost**: The proofs in `Completeness.lean` that use `unfold Proposition.diamond Proposition.neg` will need to replace those tactics with direct structural reasoning on `.dia`. Given the truth lemma does induction on `Proposition`, it gains a new `| .dia φ` case that is symmetric to the `.box` case. The canonical model's box witness needs no analogue for diamond because diamond is existential — it already works via `Satisfies.diamond_iff_exists` in the current forward direction of the truth lemma.

---

## Evidence and Examples

**Evidence that change is needed now:**

1. Axiom D (`□φ → ◇φ`) currently encodes diamond as `(□(φ → ⊥)) → ⊥` in `Axioms.lean` — visible proof that it cannot abstract over whether diamond is primitive or derived.

2. The `Connectives.lean` module has explicit comments about why `and`/`or` were made primitive (for intuitionistic support) — the same argument applies verbatim to `dia`.

3. Bimodal's `ModalEmbedding.lean` uses a `rfl` proof for `diamond` preservation — this is only valid because diamond unfolds identically in both types. If `Bimodal.Formula` ever adds primitive `.dia`, the embedding breaks.

4. `Satisfies.diamond_iff` in `Basic.lean` is a 12-line classical proof using `by_contra` and `push_neg` — in a world with primitive `.dia`, it becomes `Iff.rfl`.

**Evidence that alternatives do not work:**

- Attempting `HasDia` with a classical default instance would require `Modal.Proposition` to have `instance : HasDia (Proposition Atom) := ⟨Proposition.diamond⟩`. But then `HasDia.dia = neg ∘ box ∘ neg` definitionally — no intuitionistic logic can override this for a single inductive type.

- The `FromPropositional.lean` proof that `and`/`or` preservation holds `by rfl` depends on the Lukasiewicz expansions being *definitionally equal*. If `PL.Proposition.and` were primitive but `Modal.Proposition.and` were Lukasiewicz-derived, that `rfl` would not hold — a semantic coherence proof would be needed. The same trade-off applies to diamond.

---

## Confidence Level

**High confidence** in these findings:
- Current `Modal.Proposition` primitives: confirmed by direct reading of `Basic.lean`
- That `HasDia` alone is insufficient without a primitive constructor: logically certain (typeclass dispatch does not change the underlying term)
- That parameterized types are out of scope: confirmed by explicit design documentation in `Connectives.lean`
- Refactoring cost growing with file count: confirmed by counting `.diamond` references (14 in Modal alone, plus Bimodal embedding)
- That adding `.dia` now is the correct path: high confidence, consistent with how `and`/`or` were handled

**Medium confidence** in the estimate that the classical equivalence `◇φ ↔ ¬□¬φ` can be proved as a theorem for classical systems: the proof would require Peirce's law (`((φ → ψ) → φ) → φ`) and the K axiom. This is standard classical modal logic, but the proof inside CSLib's Hilbert system would need verification by an implementation agent.

---

## Supplementary: What Remains If Task 179 Is Completed

After making `dia` primitive, the remaining gap (a separate task) would be:

1. **IK formalization**: A new `Cslib/Logics/Modal/Metalogic/IK/` directory with intuitionistic frames `(W, ≤, R)`, bi-relational semantics, and the Fischer Servi interaction conditions. This requires a new proof system tag `Modal.HilbertIK` that omits Peirce's law and states diamond axioms (like `◇(A ∨ B) → ◇A ∨ ◇B`) as primitives.

2. **`HasDia` instance registration**: Once `dia` is a primitive constructor, `Modal.Proposition` registers `instance : HasDia (Proposition Atom) := ⟨.dia⟩`. The axiomatic forms in `Axioms.lean` using `HasDia.dia` then work polymorphically for both classical and intuitionistic logics.

Task 179 is the prerequisite that enables all of this.
