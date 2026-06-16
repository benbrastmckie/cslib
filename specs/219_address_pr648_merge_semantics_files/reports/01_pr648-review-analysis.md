# PR #648 Review Analysis

## Reviewer Comments

PR #648 received CHANGES_REQUESTED from ctchou (pullrequestreview-4502084546) with four points:

1. **bot as primitive** — Likes adding bot as a primitive constructor (positive, no action needed)
2. **Merge Basic.lean and Bool.lean** — Doesn't understand why both files exist; thinks Bool.lean alone suffices
3. **Reference update** — Finds 1930s German paper references unhelpful; recommends Avigad's *Mathematical Logic and Computation* (Cambridge), chapters 2-3
4. **Coordinate with related PRs** — Must coordinate with #607 (fmontesi: logical operators), #587 (thomaskwaring: notation typeclasses and models), and #536 (thomaskwaring: classical/intuitionistic inference systems, ready to merge)

## Current File Structure

- `Semantics/Basic.lean` (~65 lines): `Valuation` (Atom -> Prop), `Evaluate` (Prop-valued recursive evaluation), `Tautology`
- `Semantics/Bool.lean` (~110 lines): `BoolValuation` (Atom -> Bool), `BoolEvaluate` (Bool-valued), bridge lemmas, `Decidable` instance

## Why Both Evaluators Are Needed

**Prop-valued `Evaluate`**:
- Canonical model construction in strong completeness uses `fun p => atom p in S` where S is an MCS — set membership is inherently Prop-valued with no `DecidablePred`
- The same `Atom -> Prop` convention runs through modal, temporal, and bimodal Kripke semantics (`Satisfies` is Prop-valued)
- Propositional `Evaluate` is the degenerate case of Kripke `Satisfies` (no worlds, no accessibility) — keeps a uniform Prop-valued shape across all logics

**Bool-valued `BoolEvaluate`**:
- DPLL/SAT procedures (Matthew Doty's planned work) need computable Bool evaluation
- Bridge lemma `BoolEvaluate_eq_iff` connects Bool computation to Prop metatheory

**Matthew Doty's alternative** (from Zulip): Use `decide` + `Classical.propDecidable` to collapse everything to Bool. This works for classical PL in isolation but would be a stylistic outlier against the Prop-valued semantics used throughout the rest of the library.

## Zulip Context

Active Zulip discussion between Benjamin, Thomas Waring, and Matthew Doty on propositional logic infrastructure. Key points:

- Matthew needs Bool-valued evaluation for DPLL/SAT work (porting Harrison's *Handbook of Practical Logic and Automated Reasoning*)
- Thomas wants generic semantics via `HasEntails` typeclass (PR #587) — his `Model.lean` already defines `Valuation` and `Valuation.interp` for PL as instances of this framework
- Thomas also interested in `GeneralizedHeytingAlgebra` generality for intuitionistic/minimal logic, but that's orthogonal to this PR

## Related PRs

| PR | Author | Status | Relevance |
|----|--------|--------|-----------|
| #536 | thomaskwaring | Ready to merge | Refactors `IsClassical`/`IsIntuitionistic` to refer to inference systems; **wait for this** |
| #587 | thomaskwaring | Open | Generic `HasEntails`/`HasInterpEntails` framework; defines `Valuation` for PL — potential overlap with Basic.lean |
| #607 | fmontesi | Open | Typeclasses for logical operators; refactors modal/propositional with instances |

## Recommended Actions

### 1. Merge into one file
Combine Basic.lean and Bool.lean into a single `Semantics.lean`. ~170 combined lines is reasonable for one file. Keep both evaluators with the bridge lemma.

### 2. Update references
Replace Chagrov/Zakharyaschev citations with Avigad's *Mathematical Logic and Computation* (Cambridge), chapters 2-3.

### 3. Coordinate with related PRs
- Wait for #536 to merge first
- Review #607 and #587 for conflicts, especially #587's generic `Valuation` definition

### 4. Respond to review
- Acknowledge file consolidation
- Explain Prop-valued `Evaluate` is needed for uniform Kripke semantics shape across all logics in the library
- Note `BoolEvaluate` serves Matthew Doty's DPLL/SAT work
