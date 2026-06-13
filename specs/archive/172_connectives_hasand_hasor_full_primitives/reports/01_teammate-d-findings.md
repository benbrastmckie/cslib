# Teammate D Findings: Strategic Horizons for Task 172 (Connectives.lean Refactor)

**Date**: 2026-06-12
**Task**: 172 — Extend Cslib/Foundations/Logic/Connectives.lean for the five-primitive signature
**Angle**: Strategic Horizons — long-term alignment, task ordering, scope boundaries, risks

---

## Key Findings

### Finding 1: The Task-Ordering Chain Is Correct and the Dependencies Are Sound

The 172-178 chain has a clear, coherent dependency structure:

- **172 (Connectives.lean)**: Add HasAnd/HasOr typeclass layer. Zero downstream breakage risk: no
  existing code depends on the absence of these classes. Pure addition.
- **173 (Propositional)**: Adds and/or constructors to the formula type. Depends on 172 because it
  must register HasAnd/HasOr instances. This is the architecturally most significant task: it
  changes induction arity from 3 to 5 for PL.Proposition.
- **174 (Metalogic)**: Extends Kripke semantics and completeness proofs with and/or clauses.
  Depends on 173 (formula type must exist first). Correctly placed after 173.
- **175, 176 (Modal, Temporal propagation)**: Both depend on 173 (the PL formula type and Hilbert
  axioms are shared foundations for modal/temporal). They do NOT depend on each other — modal and
  temporal are independent peers in the module hierarchy. This parallelism is correct and enables
  concurrent implementation after 173 completes.
- **177 (Bimodal propagation)**: Depends on both 175 and 176, consistent with the ROADMAP.md
  diagram showing Bimodal at the bottom importing from Modal and Temporal peers.
- **178 (Johansson refs + docs)**: Depends on 173 but not on 174-177. It can run any time after
  the Propositional architecture stabilizes. The sequencing is appropriate.

**Conclusion**: The chain ordering is sound. Task 172 is correctly scoped as a pure typeclass
addition that unblocks 173. No reordering is needed.

### Finding 2: Task 172 Should Do Exactly What Is Described — No More, No Less

The task description says: add HasAnd and HasOr atomic typeclasses, update bundled classes, revise
ImpBotDerived. This is the right scope. Three boundary conditions matter:

**Should NOT be expanded into 172**:
- Adding and/or constructors to formula types (task 173 — touches Proposition, inductive structure)
- Adding and/or axiom typeclasses to ProofSystem.lean (task 173/175/176 — tied to formula types)
- Touching Axioms.lean to use HasAnd/HasOr in conj'/disj' (downstream task work)
- Adding HasAtom typeclass (discussed below — not in scope)

**Should be in 172**:
- HasAnd and HasOr as standalone atomic typeclasses
- Updating PropositionalConnectives, ModalConnectives, TemporalConnectives, BimodalConnectives
  to extend HasAnd and HasOr alongside existing fields
- Revising ImpBotDerived: remove the and/or defaults (classical-only); keep neg/top/iff defaults
  (valid in minimal/intuitionistic/classical)
- Updating the module docstring to reflect the new design

The typeclass additions in 172 will create an "instance gap": the four formula types (PL, Modal,
Temporal, Bimodal) will inherit HasAnd/HasOr via their bundled class instances, but their
underlying inductive constructors do NOT yet have and/or. This gap is intentional and correct —
until 173 runs, the formula types use the current abbrev definitions for and/or. The instance
resolution will still work because PropositionalConnectives now extends HasAnd, and PL.Proposition
registers PropositionalConnectives, so HasAnd (PL.Proposition) will be satisfied via the Lukasiewicz
abbrev forwarding. Task 173 then replaces the abbrev forwarding with direct constructors.

**The "instance gap is a feature, not a bug"**: it allows the typeclass layer (172) to be clean and
complete before the formula-type layer (173) catches up.

### Finding 3: ImpBotDerived Needs Surgical Revision, Not Full Deletion

The current `ImpBotDerived` class provides defaults for neg, top, or, and and. The and/or defaults
are Lukasiewicz encodings that are classical-only (task 171 research confirmed this). The neg and
top defaults ARE valid universally: neg φ := imp φ bot holds in minimal logic, and top := imp bot
bot holds in minimal logic.

Recommended treatment:

1. **Remove and/or from ImpBotDerived**: The class currently provides these as defaults using the
   classical Lukasiewicz encoding. Per task 171 findings, these are not logic-neutral and must not
   be presented as derived defaults.

2. **Keep neg and top in ImpBotDerived** (or a renamed class): These are genuinely derived from
   imp+bot in ALL logics (minimal, intuitionistic, classical). The derived neg := A -> bot is
   used extensively in `Axioms.lean` (neg', the temporal/modal axiom abbreviations all use neg').

3. **Optionally add HasNeg, HasTop as atomic typeclasses** (discussed in Finding 4 below).

4. **Rename or redocument the class**: If and/or are removed, ImpBotDerived may need renaming.
   A suitable name is `ImpBotNeg` or `HasNegTop` to signal what remains.

The key docstring correction: the class header currently says "Provides neg, top, or, and as
abbreviations" — after revision this should say "Provides neg and top as abbreviations valid in
all logics based on {imp, bot}."

### Finding 4: Should HasNeg and HasTop Also Be Added as Atomic Typeclasses?

This is the most nuanced strategic question. Two considerations pull in opposite directions:

**Argument for adding HasNeg and HasTop**:
- In formula types where neg is NOT defined as A -> bot (e.g., a three-valued logic with a
  primitive negation), a HasNeg class would allow the axiom library to write neg-polymorphic
  code without assuming the Lukasiewicz encoding.
- PR #607's direction is "one class per operator" at the notation level. HasNeg and HasTop fit
  that direction cleanly.
- The conj'/disj'/neg' abbreviations in Axioms.lean are used 26+ times for the temporal/modal
  axioms. If HasNeg existed, these could be typed via HasNeg.neg instead of the inline imp/bot
  pattern, making the axiom definitions more readable.

**Argument against adding HasNeg and HasTop in task 172**:
- Task 172 is specifically about the FIVE primitives: atom, bot, imp, and, or. Neg and top are
  derived in ALL four existing formula types and will remain derived after the refactor. Adding
  HasNeg/HasTop goes beyond what the task requires.
- The conj'/disj'/neg' abbreviations in Axioms.lean work correctly right now. Changing them
  requires touching Axioms.lean, which is out of scope for 172.
- The downstream tasks (173-177) do not need HasNeg/HasTop — neg stays derived in all four
  formula types after the refactor.
- Risk: adding too many typeclass layers creates resolution overhead without benefit.

**Recommendation**: Do NOT add HasNeg or HasTop in task 172. Add a NOTE in the docstring or
as a comment that these could be future additions following PR #607's direction. If PR #607
introduces HasNeg/HasTop in its Operators/ directory, CSLib can align at that point.

**What about HasAtom?** The "five primitives" include atom, but HasAtom is not mentioned in the
task description. In all four formula types, atom is parameterized by a Type (Atom : Type u),
which is passed to the formula type constructor. A HasAtom typeclass would need to carry the Atom
type as a parameter — making it `class HasAtom (F : Type u) (Atom : Type u) where`. This is
a more complex design (two-parameter typeclass) and would affect the entire inference system.
Leave HasAtom for future work.

### Finding 5: How Task 172 Positions Relative to PR #607 (Upstream)

PR #607 (fmontesi's Operators/ directory) proposes per-operator files in a new
`Cslib/Foundations/Logic/Operators/` directory. The operator-typeclass approach aligns with
what task 172 is doing (HasAnd, HasOr as atomic typeclasses). Two scenarios:

**Scenario A: PR #607 merges before tasks 172-178 land**
- This would introduce and/or typeclasses upstream (possibly named differently)
- Task 172 should then use whatever PR #607 defines, rather than introducing HasAnd/HasOr
  independently, to avoid duplication
- Risk: if PR #607's naming differs, the downstream tasks (173-177) could need adjustment

**Scenario B: Tasks 172-178 land before PR #607**
- Task 172 introduces HasAnd/HasOr in the existing Connectives.lean pattern
- When PR #607 eventually merges, there will be a reconciliation step
- The reconciliation is low-effort if naming conventions match (HasAnd, HasOr)
- The reconciliation is higher-effort if PR #607 uses different names or a different file layout

**Strategic recommendation**: Define HasAnd and HasOr following the existing naming pattern in
Connectives.lean (HasBot/HasImp style). This gives maximum PR #607 compatibility because
PR #607's "one class per operator" principle is exactly what HasBot/HasImp already follows.
If PR #607 uses And.lean / Or.lean files, those could import from Connectives.lean without
conflict.

The key insight: the task description explicitly says "align design with fmontesi's PR #607
operator-typeclass direction." HasAnd/HasOr named and structured like HasBot/HasImp IS that
alignment — same pattern, same namespace.

### Finding 6: The Axioms.lean conj'/disj' Abbreviations Create a Downstream Tension

`Axioms.lean` uses `conj'` and `disj'` as Lukasiewicz-encoding abbreviations throughout the
temporal axioms (BX7 LinearUntil, BX7' LinearSince, BX5 SelfAccumUntil, etc.). After task 173
adds and/or constructors, these formulas will have two representations:
- The old: `conj' φ ψ = imp (imp φ (imp ψ bot)) bot` (Lukasiewicz)
- The new: `HasAnd.and φ ψ` (primitive constructor)

This matters for the temporal/bimodal metalogic (tasks 176, 177): the truth lemma and MCS
membership lemmas will need to handle and/or cases. After the refactor, will the axioms in
`Axioms.lean` be rewritten to use `HasAnd.and`?

**Finding**: Task 172 SHOULD NOT change `Axioms.lean`. The conj'/disj' abbreviations are
correct and can remain. When tasks 173-177 propagate the and/or constructors, each task
should decide whether to update its own axiom usage. The `Axioms.lean` conj'/disj'
abbreviations can stay as-is for temporal axioms — they are used in the HILBERT axioms
where logical equivalence (via completeness) makes the Lukasiewicz encoding interchangeable.

However, the BX13 `EnrichmentUntil` axiom uses `conj' p (HasUntil.untl ψ φ)` — after the
refactor, `and` becomes primitive in the formula type, so task 176 should update these to
use `HasAnd.and` for clarity and consistency. But this is task 176's responsibility, not 172's.

### Finding 7: The BigConj Module Will Need Attention in Task 173 (Not 172)

`Cslib/Foundations/Logic/Theorems/BigConj.lean` implements big conjunction using the Lukasiewicz
encoding: `bigconj : List F → F` requires only `[HasBot F] [HasImp F]`. After task 173 adds
and/or constructors, BigConj could be simplified to use `HasAnd.and` directly.

However, BigConj lives in Foundations (not Propositional), and it's designed to be polymorphic
over any formula type with HasBot+HasImp. After the refactor, not all formula types may have
HasAnd (e.g., a hypothetical future HML or linear-logic type). So BigConj should KEEP its
current Lukasiewicz encoding as the generic fallback, but task 173 can add a simplified version
for concrete formula types.

**Task 172 should not touch BigConj.lean**.

### Finding 8: Risk Assessment for Task 172

The risks are low overall because task 172 is purely additive at the typeclass level:

| Risk | Likelihood | Severity | Mitigation |
|------|-----------|----------|------------|
| Instance conflicts from adding HasAnd/HasOr to bundled classes | Low | Medium | The four formula types already define and/or as abbrevs that resolve via imp/bot; adding HasAnd/HasOr to the bundled class won't conflict since existing instances satisfy them via the abbrev pathway |
| ImpBotDerived revision breaks downstream code | Low | Low | ImpBotDerived is "intentionally uninstantiated" per existing docstring; no code depends on its and/or defaults |
| HasAnd/HasOr naming conflict with future PR #607 | Medium | Medium | Use PR #607-compatible naming (one class, one operator, HasBot pattern); document as aligned with PR #607 |
| Typeclass diamond when updating bundled classes | Low | Low | The BimodalConnectives note in the existing code already handles diamond avoidance; adding HasAnd/HasOr follows the same pattern |
| Task 172 completes but tasks 173+ face obstacles due to typeclass design choices | Low | High | The main risk: if HasAnd/HasOr typeclass signatures are wrong (e.g., wrong universe polymorphism), fixing them in 173 is expensive. Solution: verify `lake build Cslib.Foundations.Logic.Connectives` before committing |

### Finding 9: What the User May Be Missing — The Propositional Axioms Gap

The current `ProofSystem.lean` defines `MinimalHilbert`, `IntuitionisticHilbert`, and
`ClassicalHilbert` in terms of `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, and
`HasAxiomPeirce`. After task 173 adds and/or constructors, there will need to be:

- `HasAxiomAndI`: A ∧ B ← A, B (in conjunction introduction)
- `HasAxiomAndE1`: A ← A ∧ B
- `HasAxiomAndE2`: B ← A ∧ B
- `HasAxiomOrI1`: A ∨ B ← A
- `HasAxiomOrI2`: A ∨ B ← B
- `HasAxiomOrE`: C ← A ∨ B, A → C, B → C

These axiom typeclasses are task 173 work (they go in ProofSystem.lean). **Task 172 should not
add these** — doing so would be premature (the formula constructors don't exist yet to express
these axioms). The task 172 boundary is strictly the connective typeclasses, not the axiom
typeclasses.

However, the user should be aware that when updating ProofSystem.lean in task 173, there is a
design choice: should and/or axioms be added to the base `MinimalHilbert` class (since and/or
elimination is valid in minimal logic), or as separate extension classes? The answer from the
literature (Johansson 1937, Prawitz 1965) is that and/or rules hold in minimal logic, so they
should be part of `MinimalHilbert`. This is a task 173 decision, not task 172.

### Finding 10: The Architecture Change Is Not as Disruptive as Task 171 Research Feared

Task 171's team research (particularly Teammate B and D findings) recommended AGAINST adding
and/or constructors because "adding and/or constructors would require refactoring all four
formula types, all semantic functions, and all existing proofs." This was the correct analysis
given the OLD architecture question (should the CURRENT codebase add and/or?).

The NEW situation (tasks 172-178) is different: the user has DECIDED to make this change
and the tasks are designed to propagate it systematically. The task-173 refactor of PL.Proposition
IS the expensive step (5 constructor cases vs. 3). Tasks 175-177 extend that refactor to modal,
temporal, bimodal. The cost is real but manageable because:

1. Each task is scoped to ONE formula type layer
2. The metalogic extensions (174, 175, 176, 177) are mechanical case additions
3. The bimodal completeness work is already done — it just needs and/or cases added

The key risk is in task 174's intuitionistic completeness with disjunction (prime theories,
Lindenbaum construction). This is the only genuinely mathematically hard step. Everything else
is either structural (adding constructors) or mechanical (adding cases to existing proofs).

---

## Recommended Approach

### For Task 172 Specifically

1. **Add HasAnd and HasOr as atomic typeclasses** in the style of HasBot/HasImp:
   ```lean
   class HasAnd (F : Type*) where
     and : F → F → F
   class HasOr (F : Type*) where
     or : F → F → F
   ```

2. **Update all four bundled classes** to extend HasAnd and HasOr:
   - PropositionalConnectives extends HasBot, HasImp, HasAnd, HasOr
   - ModalConnectives extends PropositionalConnectives, HasBox
   - TemporalConnectives extends PropositionalConnectives, HasUntil, HasSince
   - BimodalConnectives extends ModalConnectives, HasUntil, HasSince (no diamond from temporal
     to avoid diamond in the typeclass hierarchy — consistent with existing approach)

3. **Revise ImpBotDerived**: Remove the `or` and `and` default fields. Keep `neg`, `top`.
   Add `iff` if not already there (iff := (A -> B) ∧ (B -> A) which requires HasAnd, or keep it
   as the imp-based Proposition.iff). Rename class or update docstring.

4. **Update the module docstring** in Connectives.lean: change the architecture description to
   reflect five primitives {atom, bot, imp, and, or} for the formula types, with neg/top/iff
   remaining as derived connectives valid across all logics.

5. **Do NOT touch Axioms.lean, ProofSystem.lean, or any formula type files**. Those are 173+.

6. **Verify** with `lake build Cslib.Foundations.Logic.Connectives` after the changes.

### For the 172-178 Chain Overall

The chain is correctly ordered and scoped. The most significant bottleneck is task 174's
intuitionistic completeness with prime theories. The user should plan for:
- Task 173: possibly 2-3 days of mechanical work (formula type + proof system extensions)
- Task 174: possibly 5-7 days on the prime theory Lindenbaum construction (hard part)
- Tasks 175-177: mechanical, parallelizable after 173 completes

---

## Evidence / Examples

### Current Connectives.lean Structure (for reference):
- HasBot, HasImp, HasBox, HasUntil, HasSince: atomic typeclasses (lines 50-72)
- PropositionalConnectives extends HasBot, HasImp (line 75)
- ModalConnectives extends PropositionalConnectives, HasBox (line 78)
- TemporalConnectives extends PropositionalConnectives, HasUntil, HasSince (line 81)
- BimodalConnectives extends ModalConnectives, HasUntil, HasSince (lines 84-86)
- ImpBotDerived: uninstantiated specification class with neg/top/or/and defaults (lines 104-113)

### Current instance registrations (four formula types):
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Defs.lean:91` — PropositionalConnectives
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean:90` — ModalConnectives
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Formula.lean:110` — TemporalConnectives
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Syntax/Formula.lean:106` — BimodalConnectives

After task 172 adds HasAnd/HasOr to the bundled classes, these four instance sites will
automatically satisfy HasAnd/HasOr — WITHOUT being updated — because the formula types
already define `.and` and `.or` as abbrevs. The instances will resolve via the abbrev
path until task 173 replaces abbrevs with constructors.

### Evidence that ImpBotDerived's and/or are classical-only:
From task 171 team research synthesis: "DerivedRules.lean lines 143, 174, 232 gate andE1,
andE2, and orE on [IsClassical T]." And from the Critic (Teammate C): Kripke counterexamples
show CSLib's Lukasiewicz ∧ and ∨ have different semantics from standard intuitionistic ∧, ∨.

### Evidence that neg/top defaults are universal:
neg φ := imp φ bot is Johansson's own negation in minimal logic (Johansson 1937). In minimal
logic, ¬A := A → ⊥ is valid (you just can't derive ⊥ → A). top := imp bot bot is provable
in minimal logic (it is K applied to bot: ⊥ → (⊥ → ⊥) → ⊥, i.e., the K axiom instance).

---

## Confidence Level

- Task ordering chain is correct: **High confidence**
- Task 172 scope boundaries (add HasAnd/HasOr, revise ImpBotDerived): **High confidence**
- Do not add HasNeg/HasTop in task 172: **Medium-high confidence** (reasonable to defer)
- Do not add HasAtom: **High confidence**
- ImpBotDerived should keep neg/top but remove and/or: **High confidence** (grounded in task 171)
- PR #607 alignment approach (use HasBot/HasImp naming style): **High confidence**
- Axioms.lean conj'/disj' should not be changed in task 172: **High confidence**
- Task 174 intuitionistic completeness with prime theories is the key hard step: **High confidence**
- Instance gap between 172 and 173 is intentional and benign: **High confidence**
