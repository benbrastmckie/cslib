# Research Report: Task #172

**Task**: connectives_hasand_hasor_full_primitives
**Date**: 2026-06-12
**Mode**: Team Research (4 teammates)

---

## Summary

- Task 172 is correctly scoped as a pure addition to `Cslib/Foundations/Logic/Connectives.lean`:
  add `HasAnd`/`HasOr` atomic typeclasses following the existing `HasBot`/`HasImp` single-field
  pattern over `F : Type*`.
- The bundled classes (`PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`,
  `BimodalConnectives`) **should be updated in task 172** to extend `HasAnd F, HasOr F`. A third
  option resolves the key conflict: because the four formula types already define `.and` and `.or`
  as `abbrev`s over `imp`/`bot`, the existing instance registrations will automatically satisfy the
  new `HasAnd`/`HasOr` fields without code changes — keeping the build green.
- `ImpBotDerived` must be surgically revised: remove the `and`/`or` default fields (Lukasiewicz
  encodings are classical-only) and keep only `neg` and `top` (valid in minimal, intuitionistic,
  and classical logic). Update the module docstring to correct the misleading "functionally
  complete" claim.
- No changes to `Axioms.lean`, `ProofSystem.lean`, or any formula-type files belong in task 172.
  Those are task 173+ work.
- The `botE` rule in the current ND system makes it intuitionistic (not minimal); any downstream
  "equivalence with ND" claim must specify which ND system is meant. Task 172 itself is unaffected
  by this, but task 174 must confront it.
- No notation should be attached to `HasAnd`/`HasOr` at the typeclass level; follow the existing
  pattern of namespace-scoped notation.

---

## Key Findings

### Primary Approach (from Teammate A)

Teammate A investigated the concrete implementation shape for `Connectives.lean`.

**HasAnd/HasOr typeclass design** (high confidence). The design is a verbatim copy of the
existing pattern:

```lean
class HasAnd (F : Type*) where
  and : F → F → F

class HasOr (F : Type*) where
  or : F → F → F
```

Field names `and` and `or` are safe: `HasImp` already uses `imp` (a Lean keyword) as a field name
without conflict, confirming `and`/`or` work the same way. No conflict with Mathlib's `Prop`-level
`And`/`Or`.

**Bundled class updates** (medium confidence on timing, high on correctness). A proposes updating
`PropositionalConnectives` to extend `HasAnd F, HasOr F` in task 172, with the downstream
`ModalConnectives`/`TemporalConnectives`/`BimodalConnectives` inheriting automatically. A identifies
exactly 4 instance sites that will be affected: `Defs.lean`, `Modal/Basic.lean`,
`Temporal/Syntax/Formula.lean`, `Bimodal/Syntax/Formula.lean`. A notes that default field values
cannot plug this gap because no canonical "partial" conjunction exists — the Lukasiewicz defaults
would be the exact classical-only encoding we are trying to avoid.

**ImpBotDerived** (high confidence). Trim to `neg` and `top` only. The `or`/`and` Lukasiewicz
defaults are classically-only (Wajsberg 1938, McKinsey 1939). Retain the class as a specification
artifact with updated docstring. Alternative of full deletion is also valid since the class is never
instantiated.

**Downstream breakage map** (high confidence, confirmed by grep):
| File | Instance | Resolution |
|------|----------|------------|
| `Defs.lean` | `PropositionalConnectives (Proposition Atom)` | Fixed by task 173 |
| `Modal/Basic.lean` | `ModalConnectives (Proposition Atom)` | Fixed by task 175 |
| `Temporal/Syntax/Formula.lean` | `TemporalConnectives (Formula Atom)` | Fixed by task 176 |
| `Bimodal/Syntax/Formula.lean` | `BimodalConnectives (Formula Atom)` | Fixed by task 177 |

**Module docstring** must be updated: the current "Falsum and implication are taken as the only
propositional primitives because `{imp, bot}` is functionally complete for classical logic" framing
must give way to the five-primitive design rationale.

### Alternative Approaches (from Teammate B)

Teammate B investigated Hilbert axiom extension, the ND preservation constraint, and the Kripke
semantics implications.

**Parallel formula type vs. extending existing type** (medium confidence). B argues that to
preserve `Theory.Derivation` (Waring's ND) exactly, the five-primitive extension must be a new
formula type (`FivePrimProposition`) rather than extending `PL.Proposition`. Otherwise the ND rules
for `and`/`or` must be added to `Theory.Derivation`, contradicting the "preserve exactly" constraint.
This is a task 173 decision, not task 172 — but the task 172 typeclass design is neutral between
the two options.

**Hilbert axiom shape** (high confidence on the axiom list). The 6 new axioms for primitive
`and`/`or` are standard minimal-logic valid:
- `andI`: `A → B → A ∧ B`
- `andE1`: `A ∧ B → A`, `andE2`: `A ∧ B → B`
- `orI1`: `A → A ∨ B`, `orI2`: `B → A ∨ B`
- `orE`: `(A → C) → (B → C) → A ∨ B → C`

With primitive connectives, `andE1`/`andE2` no longer require `[IsClassical T]` — they are minimal
valid. This is a significant logic correctness win over the current Lukasiewicz encoding.

**`hilbert_iff_nd` is already generic** (high confidence). `Equivalence.lean`'s `hilbert_iff_nd` is
parameterized over any `Axioms` predicate with K, S, EFQ witnesses. The new axiom systems retain
these, so the equivalence theorem applies without modification once the formula translation is
handled in task 173/174.

**Kripke semantics for and/or** (high confidence on structure). Standard Kripke forcing:
`w ⊩ A ∧ B ↔ w ⊩ A ∧ w ⊩ B` and `w ⊩ A ∨ B ↔ w ⊩ A ∨ w ⊩ B`. Both are persistent. The
persistence lemma `iforces_persistence` gains 2 trivial induction cases. These are task 174 items.

### Gaps and Shortcomings (from Critic)

Teammate C performed adversarial verification against the other teammates' findings.

**Finding C1 — The current ND is intuitionistic, not minimal** (high confidence, verified).
`NaturalDeduction/Basic.lean` has `botE` as an unconditional constructor:
`Derivation Γ ⊥ → Derivation Γ A`. This fires for any formula and any theory, including the empty
theory. The system called "MPL" (minimal propositional logic) is actually intuitionistic because it
includes explosion. Task 173's stated goal of restoring Waring's "10-rule minimal-logic ND system
with NO botE primitive" contradicts the current state. Task 172 is unaffected, but task 174's
"extensional equivalence" claim must specify which ND system is the target.

**Finding C2 — Semantic mismatch with Lukasiewicz bridge instances** (high confidence). If bundled
classes are extended to include `HasAnd`/`HasOr` in task 172, the four formula-type instances must
provide `and`/`or` fields. Before task 173 adds constructors, the only available option is the
Lukasiewicz encoding. This creates a semantic mismatch: `HasAnd` implies primitive status, but the
instance encodes derivedness. C's preferred resolution: do not extend bundled classes until task 173.

**Finding C3 — Cascade breakage** (high confidence). The 4 instance sites confirmed by C at
specific line numbers: `Defs.lean:91`, `Basic.lean:90`, `Temporal/Syntax/Formula.lean:109-110`,
`Bimodal/Syntax/Formula.lean:105-106`. None provide `HasAnd`/`HasOr`. Extending bundled classes
without updating these breaks the entire build.

**Finding C4 — Equivalence claim is premature for task 172** (high confidence). Before task 173,
both Hilbert and ND operate over the same formula type with `and`/`or` as `abbrev`s — the
equivalence is trivially unchanged. After task 173 adds constructors, the existing `hilbert_iff_nd`
breaks for the new formula type. "Establishing extensional equivalence" is task 174 work.

**Finding C5 — ImpBotDerived docstring is factually incorrect** (high confidence). The current
docstring says `{imp, bot}` is "functionally complete" — true for classical logic but wrong as a
general claim for a module used by minimal/intuitionistic logics. The correction must happen in
task 172 when `ImpBotDerived` is revised.

**Finding C6 — No typeclass-level notation** (high confidence). The existing pattern attaches
notation only within each logic's namespace. `HasAnd`/`HasOr` must not introduce typeclass-level
`∧`/`∨` notation to avoid collision with Lean/Mathlib builtins.

**Finding C7 — Leave `Axioms.lean` entirely unchanged** (high confidence). The `conj'`/`disj'`
abbreviations (15+ uses in temporal/bimodal axioms) are correct for the current formula types and
must not be disrupted in task 172.

### Strategic Horizons (from Horizons)

Teammate D assessed the task ordering chain and long-term alignment.

**Task chain ordering** (high confidence). The 172-178 dependency structure is sound. Tasks 175
(Modal) and 176 (Temporal) are independent peers that can run concurrently after 173 completes.
Task 177 (Bimodal) waits on both 175 and 176. Task 174 (Metalogic) is the hardest step —
intuitionistic completeness with prime theories (Lindenbaum construction for `or`) is the only
genuinely non-mechanical work in the chain.

**Instance gap is intentional** (high confidence). D identifies a resolution to the conflict: the
four formula types already define `.and` and `.or` as `abbrev`s. These `abbrev`s are computed via
`imp`/`bot` (Lukasiewicz). When `PropositionalConnectives` extends `HasAnd F`, the existing
`PropositionalConnectives (Proposition Atom)` instance will **automatically satisfy** `HasAnd` via
the `abbrev` pathway — Lean will unfold the `abbrev` to find a valid `and : F → F → F` field.
The instance registrations do NOT need to be updated in task 172. Task 173 then replaces the abbrev
forwarding with direct constructors.

**Do not add `HasNeg`/`HasTop`/`HasAtom` in task 172** (medium-high confidence). These are future
work or PR #607 alignment items. The task is specifically about the five primitives `{atom, bot,
imp, and, or}`.

**PR #607 alignment** (high confidence). Following `HasBot`/`HasImp` naming is the correct
alignment with fmontesi's one-class-per-operator direction. If PR #607 lands before tasks 172-178,
its naming should be adopted; otherwise the naming is already compatible.

**BigConj.lean must not be touched** (high confidence). `BigConj` is designed to be polymorphic
over any `[HasBot F] [HasImp F]` type — changing it to require `HasAnd` would narrow its
generality incorrectly. Task 173 can add a specialized version.

---

## Synthesis

### Conflicts Resolved

**Conflict: Should bundled classes be extended in task 172 (A and D) or deferred to task 173 (C)?**

The apparent conflict dissolves under the third option identified in the dispatch prompt and
confirmed by Teammate D's Finding 2:

> The four formula types (`PL.Proposition`, `Modal.Proposition`, `Temporal.Formula`,
> `Bimodal.Formula`) already define `.and` and `.or` as `abbrev` definitions computed from
> `imp`/`bot`. When `PropositionalConnectives` is extended to `extends HasBot F, HasImp F, HasAnd
> F, HasOr F`, the existing instance `instance : PropositionalConnectives (Proposition Atom) where
> bot := .bot; imp := .imp` will be satisfied by Lean's `abbrev` unfolding — the typeclass
> synthesizer will resolve `HasAnd.and` to `Proposition.and` (the abbrev) without any explicit
> field declaration in the instance body.

This means: **task 172 extends the bundled classes AND the build stays green** without touching
the 4 instance files. The Critic's semantic-mismatch concern (HasAnd implies primitive but instance
uses abbrev) is valid in principle but does not cause a proof-correctness problem: `abbrev`
definitions are definitionally transparent, so any lemma about `HasAnd.and` for `Proposition` is
also a lemma about the Lukasiewicz encoding. The semantic gap closes when task 173 replaces the
`abbrev` with a constructor, at which point all existing lemmas continue to hold.

**Resolution**: Extend bundled classes in task 172. Verify with `lake build
Cslib.Foundations.Logic.Connectives` that the module compiles. Do NOT change the 4 instance files.

**Confidence**: High (grounded in D's Finding 2 with abbrev-pathway evidence, and A's prior
analysis that abbrev unfolding is how Lean satisfies such constraints).

---

**Conflict: Keep or delete ImpBotDerived?**

All four teammates agree on direction: remove `and`/`or`, keep `neg`/`top`. Teammates A and D
prefer keeping the trimmed class as a specification artifact. Teammate B is neutral. The Critic
(C) agrees removal of `and`/`or` is mandatory and the docstring must be corrected now.

**Resolution**: Retain `ImpBotDerived` trimmed to `neg` and `top`. Update docstring to:
(1) remove the "functionally complete" framing that misapplies to intuitionistic/minimal logics,
(2) explicitly note that `and`/`or` were removed because the Lukasiewicz encoding is classical-only
(citing Wajsberg 1938, McKinsey 1939), and (3) note that `and`/`or` are now primitives via
`HasAnd`/`HasOr`.

---

### Gaps Identified

**Gap 1 — ND system identity (minimal vs. intuitionistic)** (High priority for task 174).
The current `Theory.Derivation` with unconditional `botE` is intuitionistic, not minimal. Task 173
says it will "restore Waring's 10-rule minimal-logic ND system with no botE primitive." These
two requirements conflict unless task 173 explicitly changes the ND system. Task 172 is
unaffected, but the task 174 equivalence proof must target the right ND system. This gap should be
flagged in the task 173 research.

**Gap 2 — HasAtom is absent from the five-primitive claim** (Low priority, defer).
The "five primitives" include `atom`, but no `HasAtom` typeclass is proposed or needed. The formula
types carry `Atom : Type u` as a type parameter, making a two-parameter `HasAtom` class awkward.
This is a documentation note, not a task 172 action item.

**Gap 3 — `iff` in ImpBotDerived** (Low priority).
Teammate D raises whether `iff` should be retained or added to `ImpBotDerived`. The current class
does not include `iff`. The task description says "Keep derived-connective defaults only for neg,
top, and iff." If `iff` is to be included, its definition `iff φ ψ := and (imp φ ψ) (imp ψ φ)`
would require `[HasAnd F]` — making `ImpBotDerived` depend on `HasAnd`. Alternative: define `iff`
via `imp` only as `iff φ ψ := imp (imp φ ψ) (imp (imp ψ φ) bot)...` but this is not standard.
This needs clarification: if `iff` is included, the class signature changes. If excluded, the task
description's mention of "iff" may be aspirational for a later task. **The plan should ask the
user to confirm whether `iff` belongs in task 172 or task 173+.**

**Gap 4 — Notation attachment for HasAnd/HasOr** (Medium priority, confirm in plan).
The Critic confirms no typeclass-level notation. But the plan should explicitly state where notation
is added (each formula type's namespace, in task 173+) to avoid an implementation agent attaching
notation prematurely.

---

### Recommendations

The following are ordered, concrete recommendations for the task 172 implementation plan.

**Recommendation 1 (Required)**: Add `HasAnd` and `HasOr` as standalone atomic typeclasses in
`Connectives.lean`, placed after `HasSince`, following the exact `HasBot`/`HasImp` single-field
pattern:

```lean
/-- A type has a conjunction connective. -/
class HasAnd (F : Type*) where
  /-- The conjunction connective. -/
  and : F → F → F

/-- A type has a disjunction connective. -/
class HasOr (F : Type*) where
  /-- The disjunction connective. -/
  or : F → F → F
```

**Recommendation 2 (Required)**: Update `PropositionalConnectives` to extend `HasAnd F, HasOr F`.
Do not change `ModalConnectives`, `TemporalConnectives`, or `BimodalConnectives` definitions —
they inherit `HasAnd`/`HasOr` automatically via `PropositionalConnectives`. Do not change the 4
instance registration files — their `abbrev`-based `and`/`or` satisfy the new fields transparently.

```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F, HasAnd F, HasOr F
```

**Recommendation 3 (Required)**: Trim `ImpBotDerived` to `neg` and `top` only. Update docstring
to: (a) correct the "functionally complete" framing, (b) explain why `and`/`or` were removed
(classical-only under Lukasiewicz), (c) note that `neg := imp φ bot` and `top := imp bot bot` are
valid in minimal logic. Do NOT rename the class unless there is strong reason (renaming touches
importers).

**Recommendation 4 (Required)**: Update the module-level docstring in `Connectives.lean`:
replace the "{imp, bot} is functionally complete" framing with the five-primitive design rationale.
Update the `## Design` section's atomic class list to include `HasAnd` and `HasOr`. Correct any
language that implies `{imp, bot}` suffices for all logics.

**Recommendation 5 (Required)**: Do NOT attach notation to `HasAnd`/`HasOr` at the typeclass
level. Notation belongs in each logic's namespace, added in tasks 173+.

**Recommendation 6 (Required)**: Do NOT touch `Axioms.lean`, `ProofSystem.lean`, `Defs.lean`,
`Modal/Basic.lean`, `Temporal/Syntax/Formula.lean`, `Bimodal/Syntax/Formula.lean`, or any
proof file. All changes in task 172 are strictly within `Connectives.lean`.

**Recommendation 7 (Required)**: Verify compilation after changes with:

```bash
lake build Cslib.Foundations.Logic.Connectives
```

If the abbrev-pathway resolution fails (i.e., the 4 instance sites do not automatically satisfy
`HasAnd`/`HasOr` via abbrevs), fall back to Critic's preferred scope: extend bundled classes in
task 173 instead, and document the deferral in the task 172 module docstring.

**Recommendation 8 (Clarification needed)**: Confirm with the user whether `iff` belongs in
`ImpBotDerived` for task 172. The task description mentions "neg, top, and iff" but including `iff`
in `ImpBotDerived` would require a `[HasAnd F]` constraint (since `iff φ ψ := and (imp φ ψ) (imp ψ
φ)`) or a weaker imp-only definition. If the user wants `iff` now, it must be defined as:

```lean
iff : F → F → F := fun φ ψ => HasImp.imp (HasImp.imp φ ψ) (HasImp.imp (HasImp.imp ψ φ) (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp ψ φ)))
```

This is non-standard. Recommended: defer `iff` to task 173 when `HasAnd` is instantiated in
`Proposition`.

**Recommendation 9 (Downstream awareness)**: Note for task 173 in plan comments: the key decision
is whether to extend `PL.Proposition` (adding `and`/`or` constructors) or create a parallel
`FivePrimProposition` type. The "preserve ND exactly" constraint forces the parallel-type option if
the existing `Theory.Derivation` must remain unchanged — but since task 173 says it will "restore
Waring's ND" (implying changes), the formula type extension approach may be viable. This decision
governs the scope of tasks 174-177 significantly.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary — Connectives.lean implementation | Completed | High |
| B | Alternatives — Hilbert axioms, equivalence, Kripke | Completed | High (structural), Medium (scope) |
| C | Critic — gaps, blind spots, code verification | Completed | High |
| D | Horizons — strategy, task ordering, PR #607 | Completed | High |

---

## References

### Codebase Files
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Connectives.lean` — primary target file
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Axioms.lean` — conj'/disj' abbreviations (must not be touched)
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/ProofSystem.lean` — Hilbert system typeclasses (task 173+)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Defs.lean:91` — PropositionalConnectives instance
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean:90` — ModalConnectives instance
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Formula.lean:109-110` — TemporalConnectives instance
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Syntax/Formula.lean:105-106` — BimodalConnectives instance
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Proofs/DerivedRules.lean` — andE1/andE2 gated on IsClassical (task 173 will fix)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Proofs/HilbertDerivedRules.lean` — same
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Kripke.lean` — IForces (task 174)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Equivalence.lean` — hilbert_iff_nd (task 174)
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Theorems/BigConj.lean` — must not be changed in task 172
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — Theory.Derivation with botE (ND system identity issue)

### Upstream PRs
- PR #607 (fmontesi) — Operators/ directory, one-class-per-operator direction; naming compatibility is the key alignment concern

### Literature
- Johansson 1937 — minimal logic; neg := A → ⊥ valid in minimal logic
- Wajsberg 1938, McKinsey 1939 — Lukasiewicz and/or encodings are classical-only
- Heyting 1930 — intuitionistic logic primitives
- Gentzen 1935, Prawitz 1965 — standard ND with and/or as primitives
- Waring (upstream) — ND system with 5 constructors (ax, ass, impI, impE, botE)

### Prior Artifacts
- Task 171 team research synthesis — confirmed Kripke counterexamples showing Lukasiewicz ∧/∨ differ from standard intuitionistic ∧/∨
