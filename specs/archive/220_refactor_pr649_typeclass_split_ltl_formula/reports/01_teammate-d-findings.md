# Horizons Research: Strategic Direction for PR #649 Refactor

**Role**: Teammate D (Horizons — long-term alignment and strategic direction)
**Task**: 220 — Refactor PR #649: typeclass split + LTL formula

---

## Key Findings

### 1. The MinimalHilbert / GenericMCS Infrastructure Already Exists — and Is Exactly What Matthew Asked For

Matthew's PR review asked for "abstract MCS/Deduction Theorem as classes (only K, S, MP)."
CSLib has **already built this**:

- `Cslib.Foundations.Logic.ProofSystem` defines `MinimalHilbert` (K, S, MP) as the minimal class
- `Cslib.Foundations.Logic.Metalogic.GenericMCS` (at `/Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`) provides `algebraicDerivationSystem` and `algebraic_has_deduction_theorem` for **any** logic with `MinimalHilbert`
- `Cslib.Foundations.Logic.Metalogic.DeductionHelpers` provides `HasHilbertTree` for uniformly proving deduction helpers once, across all four logics

**Strategic implication**: The PR commit need not *build* new MCS/deduction machinery. The correct response to Matthew is to *demonstrate* that the existing `MinimalHilbert → GenericMCS` pipeline covers LTL. If `LTL.Formula` + `LTL.HilbertK` (or similar tag) gets a `MinimalHilbert` instance, the entire MCS and deduction theory flows down for free.

This means: **focus the commit on syntax and connectives, with a brief demonstration that LTL inherits MCS from GenericMCS**. Do not re-implement the metalogic from scratch.

### 2. The Proposed Typeclass Hierarchy Fits the Existing Architecture

The existing `Connectives.lean` has:

```
PropositionalConnectives (HasBot + HasImp)
    |
ModalConnectives (+ HasBox)
TemporalConnectives (+ HasUntil + HasSince)
BimodalConnectives (+ HasBox + HasUntil + HasSince)
```

The proposed split:

```
PropositionalConnectives
    |
FutureTemporalConnectives (+ HasUntil)
   /                 \
LTLConnectives         TemporalConnectives
 (+ HasNext)              (+ HasSince)
```

This is **consistent with how CSLib handles the modal-bimodal split**: ModalConnectives and TemporalConnectives are peers, both extending PropositionalConnectives. The proposed FutureTemporalConnectives simply inserts an intermediate layer, preserving the existing TemporalConnectives class.

**Critical concern**: Adding `FutureTemporalConnectives` as a superclass of `TemporalConnectives` introduces a structural change to `TemporalConnectives`. All existing code importing `TemporalConnectives` will need to remain compilable. In Lean 4, `class TemporalConnectives extends FutureTemporalConnectives, HasSince` will break existing instances unless the existing `TemporalConnectives` instance for `Temporal.Formula` is updated to use the new structure. This is technically manageable but increases diff size.

**Alternative**: Keep `TemporalConnectives` exactly as is. Add `FutureTemporalConnectives` as a *standalone* class (not a superclass). Then `LTLConnectives` extends `FutureTemporalConnectives + HasNext`. This is a strictly additive change — no existing code breaks. The cost is one missing inheritance edge, but this can be addressed by providing a trivial derived instance.

### 3. The LTS Connection: ctchou Wants a Semantic Bridge, Not a Full Semantics Rewrite

ctchou says: "connect to LTS omega-executions, remove irrelevant instances."

CSLib already has `Cslib.LTS.OmegaExecution` at `/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean`:

```lean
def OmegaExecution (lts : LTS State Label)
    (ss : ωSequence State) (μs : ωSequence Label) : Prop :=
  ∀ i, lts.Tr (ss i) (μs i) (ss (i + 1))
```

The standard LTL semantics over omega-words maps cleanly to `ωSequence State`:
- An LTL model is an omega-word `σ : ℕ → (Atom → Prop)`, which matches `ωSequence (Atom → Prop)`
- For LTS-based LTL: an "LTL path" is an omega-execution `ss : ωSequence State` with a labeling function `v : State → Atom → Prop`

**Strategic recommendation**: Define `LTLModel` as:
```lean
structure LTLModel (Atom : Type*) where
  valuation : ℕ → Atom → Prop
```
This is a simple `ωSequence (Atom → Prop)`. Then provide:
1. Satisfaction relation `(M : LTLModel Atom) (i : ℕ) ⊨ φ`
2. A separate (future work) bridging lemma connecting `LTLModel` to `LTS.OmegaExecution`

This satisfies ctchou's request in principle while keeping the scope manageable for a single PR commit.

### 4. `LTL.Formula` as a New Inductive vs. Subtype of `Temporal.Formula`

**Option A — New inductive** (LTL.Formula with {atom, bot, imp, next, untl}):
- Clean separation: LTL is future-only + has Next, which Temporal.Formula lacks as a primitive
- The `next` operator in `Temporal.Formula` is an *abbrev* (= `untl φ bot`), not a primitive constructor
- For LTL completeness proofs, having `next` as a primitive constructor simplifies induction
- Easy to define `LTL.Formula.toTemporal : LTL.Formula Atom → Temporal.Formula Atom` as a ring homomorphism
- Downside: code duplication (countability, BEq, etc.)

**Option B — Subtype approach**:
- `LTLFormula Atom := {φ : Temporal.Formula Atom // φ.snce_free}` where `snce_free` means no `snce` subformulas
- Avoids code duplication
- But: `next` remains an abbrev, not a primitive, so LTL induction still needs to unfold
- Structural induction on the subtype is awkward in Lean 4
- Does NOT support having `next` as a primitive operator

**Option C — Type synonym / alias with constraints**:
- `LTL.Formula Atom := Temporal.Formula Atom` with a separate `IsLTLFormula : Temporal.Formula Atom → Prop`
- No new type at all; just the `FutureTemporalConnectives` typeclass
- ctchou might accept this as "defer LTL.Formula to a follow-up"

**Strategic recommendation**: If the PR must include a `LTL.Formula` type, Option A (new inductive with {atom, bot, imp, next, untl}) is the right call. It is consistent with how CSLib handles `Temporal.Formula` (own inductive, not a subtype of `Propositional.Formula`). The embedding to `Temporal.Formula` is a clean homomorphism. Countability/BEq instances are mechanical copies. Do NOT include them in this PR if scope is tight — save for a follow-up.

### 5. Minimum Diff That Satisfies Both Reviewers

ctchou's requests:
1. Future-time only first (present Temporal with past, LTL without past)
2. Connect to LTS omega-executions
3. Remove "irrelevant instances" (Encodable/Countable/Infinite/Denumerable and BEq are in scope per task description — these should be removed from PR scope)

Matthew's requests:
1. Abstract MCS/Deduction into classes (K, S, MP) — already EXISTS in GenericMCS, just demonstrate it works for LTL

**Minimum viable PR additions**:
1. `Connectives.lean`: Add `FutureTemporalConnectives` class (additive, non-breaking)
2. `Connectives.lean`: Add `HasNext` typeclass (additive)
3. `Connectives.lean`: Add `LTLConnectives` bundle
4. `Cslib/Logics/LTL/Syntax/Formula.lean`: New inductive `LTL.Formula {atom, bot, imp, next, untl}`
5. `Cslib/Logics/LTL/Syntax/Formula.lean`: Instance `LTLConnectives (LTL.Formula Atom)`
6. `Cslib/Logics/LTL/Syntax/Formula.lean`: Embedding `LTL.Formula.toTemporal`
7. `Cslib/Logics/LTL/Semantics/Model.lean`: `LTLModel` over `ℕ → (Atom → Prop)` (satisfying ctchou's LTS connection request at minimal scope)
8. `Cslib/Logics/LTL/Semantics/Satisfies.lean`: Basic satisfaction relation `⊨` for LTL

**Remove from PR scope** (per task description and ctchou):
- Encodable/Countable/Infinite/Denumerable instances (save for completeness PR)
- BEq instances (save for completeness PR)
- Full MCS/completeness infrastructure (GenericMCS already handles it; just need a comment pointing to it)

### 6. Scalability: CTL, CTL*, µ-calculus

Does `FutureTemporalConnectives` (HasBot + HasImp + HasUntil) scale to CTL/CTL*?

- **CTL**: Has path quantifiers A, E (similar to □, ◇ in modal logic). Would require `HasPath` or similar. The `HasUntil` slot would need context (path-scoped vs. state-scoped).
- **CTL***: Combines path formulas and state formulas. More complex typeclass hierarchy needed.
- **µ-calculus**: Has fixpoint operators; LTL/CTL embed via translation. Not directly expressible via simple connective typeclasses.

**Strategic conclusion**: `FutureTemporalConnectives` with `HasUntil` is an appropriate abstraction layer for LTL and future-time temporal logics over linear sequences. It does NOT naturally scale to branching-time logics (CTL/CTL*) without significant extension. This is acceptable — the CSLib roadmap shows linear temporal logic as a distinct track from modal (box-based) logic. The hierarchy should be documented as linear-time-centric.

For the PR, note in the docstring that `FutureTemporalConnectives` is intended for linear-time temporal logics and that branching-time extensions would require additional `HasPath`-style operators.

---

## Recommended Approach

**Strategic recommendation**: The commit should take the **additive, non-breaking** path:

1. **Don't restructure `TemporalConnectives`**: Keep it as `extends PropositionalConnectives, HasUntil, HasSince`. Add `FutureTemporalConnectives` as a new parallel class.

2. **Add `FutureTemporalConnectives` as a standalone ancestor** for `LTLConnectives`. Provide a trivial derived instance `FutureTemporalConnectives` from `TemporalConnectives` if needed for polymorphic lemmas.

3. **New `LTL.Formula` inductive** with {atom, bot, imp, next, untl} as primitives. This is the key deliverable ctchou is asking for.

4. **Minimal LTL semantics** over `ℕ → (Atom → Prop)` to establish the connection to LTS omega-executions. This does not need to be complete — just enough to show the design direction.

5. **Response to Matthew**: Add a comment in `Connectives.lean` or a proof sketch showing that `LTL.Formula` with a suitable proof system would get MCS and the deduction theorem from `GenericMCS` for free.

6. **Remove from PR scope**: Countability/BEq instances, full metalogic.

The minimum diff size to satisfy both reviewers is approximately 4-5 new files: `FutureTemporalConnectives` in Connectives.lean, `LTL/Syntax/Formula.lean`, `LTL/Semantics/Model.lean`, `LTL/Semantics/Satisfies.lean`, and a barrel import `LTL.lean`.

---

## Evidence / Examples

**`GenericMCS.lean` proves deduction theorem works for any `MinimalHilbert` proof system** (lines 42-61):
```lean
variable [MinimalHilbert S (F := F)]

def algebraicDerivationSystem : DerivationSystem F where
  ...
theorem algebraic_has_deduction_theorem :
    HasDeductionTheorem (algebraicDerivationSystem (S := S) (F := F)) := ...
```
This is proof that Matthew's request is already satisfied — LTL just needs to instantiate `MinimalHilbert`.

**`OmegaExecution.lean`** exists at `/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean`:
- `OmegaExecution` over `ωSequence State` is the correct bridge for ctchou's request
- `LTLModel` can be seen as `OmegaExecution` over an atomic valuation sequence

**`TemporalConnectives` structure** (in `Connectives.lean`, line 125):
```lean
class TemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F, HasSince F
```
Adding `FutureTemporalConnectives` as a new class (not changing this) is the safe path.

**`Temporal.Formula.next`** is an abbreviation (not a constructor) in the existing code:
```lean
def next (φ : Formula Atom) : Formula Atom := .untl φ .bot
```
This justifies having `HasNext` as a separate typeclass and `LTL.Formula` as a new inductive with `next` as a primitive constructor.

---

## Confidence Level

| Claim | Confidence |
|-------|------------|
| GenericMCS already satisfies Matthew's request | High |
| Additive approach for FutureTemporalConnectives is safer | High |
| LTL.Formula should be a new inductive (not a subtype) | High |
| LTL semantics should bridge to LTS.OmegaExecution | High |
| CTL/CTL* would need a different typeclass extension | High |
| FutureTemporalConnectives is additive enough to not break existing code | Medium (need to verify all imports of TemporalConnectives) |
| Minimum PR diff can satisfy both reviewers | Medium (depends on reviewer expectations for completeness) |

---

## Risk Flags

1. **Diamond typeclass problem**: If `FutureTemporalConnectives` is made a superclass of `TemporalConnectives`, existing instances break. The task description notes this already (`BimodalConnectives` avoids diamond by not extending `TemporalConnectives` directly).

2. **Scope creep**: ctchou's request for "connect to LTS omega-executions" could be interpreted broadly (full bisimulation and trace equivalence) or narrowly (just define `LTLModel` over sequences). The narrow interpretation keeps the PR focused.

3. **Burgess convention consistency**: The existing `Temporal.Formula` uses Burgess convention (`untl event guard` where event comes first). `LTL.Formula` should use the same convention for `untl`. For `next`, there is no ambiguity.

4. **`HasNext` vs. derived `next`**: If `HasNext` is a typeclass, it must be shown that `LTL.Formula.next` is injective and distinct from `untl φ bot`. This is automatic for a primitive constructor but requires a proof for a derived operator.
