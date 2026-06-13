# Teammate C (Critic) — Task 172 Research Findings

**Task**: Extend `Cslib/Foundations/Logic/Connectives.lean` for the hybrid five-primitive
signature `{atom, bot, imp, and, or}`.

**Role**: Identify gaps, shortcomings, and blind spots.

---

## Key Findings

### Finding 1: ND Preservation Tension — The "Minimal ND" Is Actually Intuitionistic

The current `Theory.Derivation` in `NaturalDeduction/Basic.lean` (the Waring system that task 172
says to "maintain exactly") has `botE` as an **unconditional primitive constructor**:

```lean
| botE {Γ : Ctx Atom} {A : Proposition Atom} :
    Derivation Γ ⊥ → Derivation Γ A
```

This rule fires for **any formula** `A` and **any theory** `T`, including the empty theory `MPL`.
The rule is **not** gated by `[IsIntuitionistic T]` or any axiom. Therefore, `MPL.Derivation`
(which the docstring calls "minimal") is actually **intuitionistic** because `botE` is explosion.

The task 172 description says "maintain Waring's ND system exactly as it is upstream." Task 173
separately says to "restore Waring's sequent-style 10-rule minimal-logic ND system with NO botE
primitive rule." These two requirements **contradict each other**: the system currently in the fork
has `botE` as a primitive, while the stated goal is to have the ND rule set be genuinely minimal
(without `botE`).

**Implication for task 172**: Task 172 works on `Connectives.lean` only; it does not touch the ND
system. But downstream planning must acknowledge this tension: any "extensional equivalence" claim
involving "the ND system" needs to specify whether it means the current fork's ND (with `botE`)
or the post-task-173 ND (without `botE`). These are different systems with different theorems.
Task 172's deliverable (HasAnd/HasOr typeclasses) is correct regardless of this resolution, but
the equivalence statement in task 174 must be careful.

**Confidence**: High. Verified by reading `NaturalDeduction/Basic.lean` lines 85-99 directly.

---

### Finding 2: PropositionalConnectives Instance for Proposition Cannot Extend HasAnd/HasOr Until Task 173

Task 172 adds `HasAnd` and `HasOr` to `PropositionalConnectives`:
```lean
-- Proposed new definition
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F, HasAnd F, HasOr F
```

But `Cslib.Logic.PL.Proposition` currently has only three constructors: `atom`, `bot`, `imp`. At
the end of task 172 (before task 173 runs), the `PropositionalConnectives` instance in `Defs.lean`
must provide `and` and `or`. It can do so only by using the **Lukasiewicz definitions**:

```lean
-- This would be the only option available before task 173
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
  and := fun A B => .imp (.imp A (.imp B .bot)) .bot   -- Lukasiewicz
  or  := fun A B => .imp (.imp A .bot) B               -- Lukasiewicz
```

This creates a **semantic mismatch**: `HasAnd` claims "this type has a conjunction primitive," but
`Proposition.and` is defined as an `imp`/`bot` abbreviation, not a constructor. The typeclass name
`HasAnd` implies primitive status, but the instance would encode derivedness.

**Option A (preferred)**: Add `HasAnd`/`HasOr` to `PropositionalConnectives` but do NOT register
`Proposition` as an instance of the extended `PropositionalConnectives` until task 173 adds the
constructors. Keep a separate, backward-compatible `PropositionalConnectivesBase` that is
`{HasBot, HasImp}` for the current `Proposition` instance.

**Option B (risky)**: Allow the Lukasiewicz instance immediately in task 172. This compiles but
the typeclass semantics are misleading. Downstream code that type-checks on `HasAnd F` would pass
for `Proposition` with Lukasiewicz semantics, and would silently behave differently after task 173
adds the primitive constructors.

**Confidence**: High. Verified by reading `Defs.lean` lines 54-101.

---

### Finding 3: Equivalence Scope Is Technically Trivial but Semantically Fragile

The task says "establish extensional equivalence with the ND system." Before task 173 runs, both
the Hilbert system (`DerivationTree PropositionalAxiom`) and the ND system (`Theory.Derivation`)
operate over the **same formula type** `Proposition Atom = {atom | bot | imp}` with `and`/`or` as
`abbrev`s. In this setting:

- `Hilbert ⊢ (A ∧ B)` means `Hilbert ⊢ .imp (.imp A (.imp B .bot)) .bot` (Lukasiewicz)
- `ND ⊢ (A ∧ B)` means `ND ⊢ .imp (.imp A (.imp B .bot)) .bot` (same object)

The equivalence is **trivially maintained** because both sides refer to the same formula; no new
proof is needed. The existing `hilbert_iff_nd` in `Equivalence.lean` already covers it.

However, once task 173 adds `and`/`or` constructors to `Proposition`, the formula `A ∧ B` becomes
`.and A B` (a new constructor), and then:
- The ND rules (`andI`, `andE1`, `andE2`) must be updated from derived rules over the Lukasiewicz
  encoding to primitive rules over the `.and` constructor.
- The equivalence proof `hilbert_iff_nd` in `Equivalence.lean` breaks because the `and` constructor
  is not handled by the existing `botE`-translation in `ndToHilbert` (which only handles `ax`, `ass`,
  `impE`, `botE`, `impI`).

**Implication for task 172**: Task 172 should not claim to "establish extensional equivalence." That
work belongs to tasks 173-174. Task 172's deliverable is purely the typeclass definitions in
`Connectives.lean`; the equivalence infrastructure lives in `Propositional/`.

**Confidence**: High. Verified by reading `Equivalence.lean` lines 96-230 and `Basic.lean`.

---

### Finding 4: Task Ordering Mismatch — Task 172 Deliverable Is Partial Without Task 173

Task 172 adds `HasAnd`/`HasOr` to `PropositionalConnectives`. But if `Proposition` cannot
meaningfully instantiate these until task 173, then task 172's `PropositionalConnectives` change
has **no instantiation** in the propositional layer. This means:

- The `Axioms.lean` file (which defines `conj'`/`disj'` as local abbreviations using `[HasBot F]
  [HasImp F]` only) will not be upgraded to use `HasAnd`/`HasOr` in task 172.
- The bundled axiom typeclasses `HasAxiomAndIntro`, `HasAxiomAndElim1`, etc. (which task 173 will
  need to add to `ProofSystem.lean`) cannot be added in task 172 because the Hilbert axiom schemata
  require the formula type to actually have `and`/`or` constructors.

**Risk**: If task 172 adds `HasAnd`/`HasOr` to `PropositionalConnectives`, all existing instances
(`Modal.Proposition`, `Temporal.Formula`, `Bimodal.Formula`) immediately break because they do not
provide `HasAnd`/`HasOr`. This forces tasks 175-177 to run concurrently with or before task 172.

**Recommended resolution**: The task 172 scope should be precisely delineated as:
1. Add `HasAnd` and `HasOr` as **standalone atomic typeclasses** (alongside `HasBot`, `HasImp`,
   etc.), without changing the bundled classes.
2. **Do NOT extend** `PropositionalConnectives` to include `HasAnd`/`HasOr` in this task; that
   extension happens in task 173 along with the `Proposition` type change.
3. Revise `ImpBotDerived`: remove `or` and `and` fields (mark them as classical-only
   abbreviations), keep only `neg`, `top` (which are logic-neutral), and optionally `iff`.

**Confidence**: High. Confirmed by instance registrations in `Defs.lean:91`, `Basic.lean:90`,
`Formula.lean:109-110`, `Syntax/Formula.lean:105-106`.

---

### Finding 5: Diamond Problem Is NOT Introduced by This Task

The existing diamond avoidance in `BimodalConnectives` (documented in `Connectives.lean:85-86`)
prevents a typeclass diamond at `PropositionalConnectives`. Adding `HasAnd`/`HasOr` as standalone
atomic typeclasses (not bundled yet) does NOT introduce any new diamond. The risk of diamond only
arises when the bundled classes are extended, which is tasks 173-177.

**Verdict**: This concern is a non-issue for task 172 as properly scoped. It becomes a real concern
for task 177 (Bimodal), where `BimodalConnectives` extends `ModalConnectives` and both would need
`HasAnd`/`HasOr`.

**Confidence**: High.

---

### Finding 6: ImpBotDerived — No Downstream Breakage, But Misleading Framing

`ImpBotDerived` is "intentionally uninstantiated" per the docstring (lines 96-103 of
`Connectives.lean`). Therefore, removing `or` and `and` from it cannot break any downstream
instance. However, the current docstring says:

> "Provides `neg`, `top`, `or`, `and` as abbreviations: negation is implication to falsum..."

The phrasing "These are **forced** once `{imp, bot}` is fixed as the primitive basis" is
**factually incorrect** for intuitionistic logic (where `and`/`or` are NOT definable from
`{imp, bot}`; this was Wajsberg 1938 / McKinsey 1939, noted by Heyting 1930). Task 178 documents
this correction, but task 172 must align the docstring NOW to avoid propagating the error.

**Recommended action**: In task 172, when revising `ImpBotDerived`, update its docstring to:
- Keep `neg` and `top` as logic-neutral derived connectives
- Remove `and` and `or` (or mark them explicitly as classical-only with a clear warning)
- Correct the "forced once {imp, bot} is fixed" language to "valid under classical logic only"

**Confidence**: High. Docstring contradiction confirmed at `Connectives.lean` lines 89-94.

---

### Finding 7: Axioms.lean Uses `conj'`/`disj'` Directly — These Must Not Be Disrupted

`Cslib/Foundations/Logic/Axioms.lean` defines local abbreviations `conj'` and `disj'` at the
`[HasBot F] [HasImp F]` level (lines 48-54). These are used in 15+ temporal and bimodal axiom
definitions (`EnrichmentUntil`, `SelfAccumUntil`, `LinearUntil`, `TempLinearity`, etc.).

Task 172 must not break these abbreviations. The safe approach:
- **Leave `Axioms.lean` entirely unchanged** in task 172.
- Do NOT replace `conj'`/`disj'` with `HasAnd.and`/`HasOr.or` calls in `Axioms.lean` during
  task 172. These replacements should happen only when the formula types have primitive `and`/`or`
  constructors (tasks 173-177).

The existing `conj'`/`disj'` are Lukasiewicz encodings — semantically correct for classical,
intuitionistic, and modal/temporal logics that extend classical PL. After the full five-primitive
refactor (tasks 173-177), these could be replaced with `HasAnd.and`/`HasOr.or`, but that is
out of scope for task 172.

**Confidence**: High. Verified by reading `Axioms.lean` lines 39-55, 190-268.

---

### Finding 8: The HasAnd/HasOr Typeclass Interface Has a Notational Collision Risk

The current `Connectives.lean` uses `scoped` notation in each logic's namespace (e.g., `PL`,
`Modal`). The new `HasAnd` and `HasOr` typeclasses will need notation. The notation `∧` and `∨`
are already claimed by Lean's Mathlib `And` and `Or` types. Within each logic's namespace,
`scoped infix:36 " ∧ " => Proposition.and` etc. currently works.

If `HasAnd` introduces a **typeclass-level** notation `∧` via `scoped notation`, it will collide
with Lean's built-in `And`. The existing pattern in CSLib avoids this by using `scoped` notation
only within each logic's namespace (not at the typeclass level).

**Recommendation**: Do NOT attach notation to `HasAnd`/`HasOr` at the typeclass level. Follow the
existing pattern: notation stays in each logic's namespace. This is consistent with how `HasBot`,
`HasImp`, `HasBox`, etc. have no notation at the typeclass level.

**Confidence**: High. Confirmed by examining all notation declarations in `Connectives.lean`.

---

## Recommended Approach for Task 172

Based on the critical findings above, the **minimal correct scope** for task 172 is:

1. **Add `HasAnd` and `HasOr` as standalone atomic typeclasses** in `Connectives.lean` (alongside
   the existing `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`). Do NOT change any bundled
   classes.

2. **Revise `ImpBotDerived`**: Remove `and` and `or` from the class body (or deprecate them with a
   clear comment that they are classical-only), and correct the misleading docstring that claims
   `{imp, bot}` is a complete basis for all logics.

3. **Leave `Axioms.lean`, `ProofSystem.lean`, `Defs.lean`, and all logic files unchanged.** The
   bundled class extensions (`PropositionalConnectives extends HasAnd, HasOr`) must wait for
   task 173, which adds the constructors to `Proposition`.

4. **Explicitly document the deferred steps** in the task 172 module docstring: "note: bundled
   class extensions and instance registration are deferred to task 173 (when `Proposition` gains
   `and`/`or` constructors)."

This scoping avoids the cascade breakage (Finding 4) and the semantic mismatch (Finding 2).

---

## Evidence / Examples

### Evidence for Finding 1 (botE is unconditional):
```
NaturalDeduction/Basic.lean:97-98
  | botE {Γ : Ctx Atom} {A : Proposition Atom} :
      Derivation Γ ⊥ → Derivation Γ A
```
Compare with `Theory.Derivation.weak` at line 157: it weakens the **theory**, proving that `botE`
fires even with the empty theory (MPL = ∅).

### Evidence for Finding 2 (Proposition has no and/or constructors):
```
Defs.lean:54-61
  inductive Proposition (Atom : Type u) : Type u where
    | atom (x : Atom)
    | bot
    | imp (a b : Proposition Atom)
  deriving DecidableEq, BEq
```
The `Proposition.and` and `Proposition.or` at lines 70-75 are `abbrev`, not constructors.

### Evidence for Finding 4 (cascade breakage if bundled class extended now):
Current instances of `PropositionalConnectives` (and its supers):
- `Defs.lean:91`: `instance : PropositionalConnectives (Proposition Atom)`
- `Basic.lean:90`: `instance : ModalConnectives (Proposition Atom)` (via extends)
- `Temporal/Syntax/Formula.lean:109-110`: `instance : TemporalConnectives (Formula Atom)`
- `Bimodal/Syntax/Formula.lean:105-106`: `instance : BimodalConnectives (Formula Atom)`

None of these provide `HasAnd`/`HasOr`. Extending `PropositionalConnectives` in task 172 without
simultaneously updating all four instances would break the entire build.

### Evidence for Finding 6 (incorrect docstring):
```
Connectives.lean:29-34
  "Falsum and implication are taken as the only propositional primitives because `{imp, bot}`
  is functionally complete for classical logic... letting the derived connectives unfold to
  `imp`/`bot` definitionally, so reasoning about `¬`, `∧`, `∨`, and `↔` needs no separate
  axioms or bridging lemmas."
```
This is correct for CLASSICAL logic but misleading as a general claim, since it applies to a
module used by intuitionistic and minimal logics.

---

## Confidence Level

| Finding | Confidence | Basis |
|---------|-----------|-------|
| 1: botE is unconditional (ND is intuitionistic, not minimal) | High | Direct code reading |
| 2: PropositionalConnectives instance gap (no and/or constructors yet) | High | Direct code reading |
| 3: Equivalence trivial before task 173, broken after without new proof | High | Direct code reading |
| 4: Cascade breakage if bundled class extended in task 172 | High | Instance enumeration |
| 5: Diamond problem is not introduced by task 172 | High | Typeclass analysis |
| 6: ImpBotDerived docstring is factually incorrect for intuit./minimal logic | High | Docstring + literature |
| 7: Axioms.lean conj'/disj' must not be disrupted | High | Direct code reading |
| 8: Notation collision risk from typeclass-level ∧/∨ | High | Lean notation analysis |

**Overall assessment**: Task 172 as currently described conflates two distinct changes:
(A) adding `HasAnd`/`HasOr` typeclasses (safe, standalone) and
(B) extending bundled classes and registering instances (requires task 173 first).
Separating these is the critical design decision for this task.
