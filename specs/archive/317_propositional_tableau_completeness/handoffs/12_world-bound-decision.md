# Phase 3 Timeboxed Decision: the stated world-bound injection strategy is empirically false

**Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
**Plan**: plans/12_world-bound-prereq-threading.md, Phase 3
**Date**: 2026-07-26
**Outcome**: Phase 3 marked `[BLOCKED]`. Do not proceed to Phase 4 on the plan's stated route.

## What this records

Phase 3 mandates a 30-minute timeboxed check of whether a Phase-5 invariant shape exists that
avoids needing `intApplyRuleFull_outputs_subset`'s `hnw : nextWorld ≤ φ0.complexity + 1`
hypothesis at all, before committing to the "injection from world-creation events into distinct
`.imp`-node positions of φ0" argument the plan and three in-file docstrings
(`Scheme.lean` pre-relocation `:2025-2038`, `:2052-2055`, `:2536-2538`; post-Phase-2-relocation
these are now in the `1478-1978` region) describe as the intended route. Per Postmortem/R10, the
decision is recorded here either way.

**The check did not stay at "is there an alternative shape" — it escalated, because verifying the
stated injection argument against live computed behavior (rather than against the docstring's own
prose) revealed the argument's central claim is false, not merely unproven.**

## The claim being tested

`Scheme.lean`'s docstring (pre-relocation `:1541-1553`, now inside the relocated universe/measure
section) states:

> "...each world created during expansion can be injected into a DISTINCT `.imp`-node position of
> φ0's own parse tree -- since F-signed formulas never propagate via persistence
> (`posFormulasAt`/`propagatePersistence`/`intTImpRule` are `.pos`-only,
> `Rules.lean:126,139-141,174-186`), a given `.imp` position's negative instance can only ever
> exist in the ONE world where its own decomposition lineage placed it."

This is the load-bearing injectivity claim Phase 3/4 would need to formalize.

## Method: direct computation against the real, unmodified functions

Rather than hand-tracing the recursion (error-prone, as an initial hand-trace attempt during this
dispatch demonstrated), the claim was tested by running the actual, unmodified
`intuitionisticTableau`/`intExpandBranches`/`intApplyRuleFull` functions (all fully computable) via
`lean_run_code` (`#eval`) against constructed formulas, with `Atom := Nat`. **No file under `Cslib/`
was read incorrectly or modified for this check** — the test formulas and inspection code were
throwaway top-level `#eval` snippets, not committed anywhere.

## The counterexample

```lean
def p : Proposition Nat := .atom 0   -- and q := .atom 1, r := .atom 2, s := .atom 3, t := .atom 4
def A1 : Proposition Nat := .imp p q                              -- shared position "p → q"
def ante : Proposition Nat := .and (.imp A1 r) (.imp s t)         -- (A1 → r) ∧ (s → t)
def cons_ : Proposition Nat :=                                    -- three sibling disjuncts
  .or (.imp u1 v1) (.or (.imp u2 v2) (.imp u3 v3))
def phi0 : Proposition Nat := .imp ante cons_                     -- ante → cons_
```

`phi0.complexity = 10` (verified by `#eval`). Running `intuitionisticTableau phi0` returns
`.openBranch b` with `b.length = 77` and 9 distinct world labels (`0` through `8`).

Filtering `b` for `.neg`-signed, `.imp`-shaped entries (i.e., exactly the triples that are eligible
to fire the world-creating rule) and printing `(formula, label)` gives:

```
(p → q, 8), (p → q, 7), (p → q, 6), (p → q, 5),
(u2 → v2, 1), (u3 → v3, 1),
(p → q, 4), (p → q, 3),
(u1 → v1, 1),
(p → q, 2), (p → q, 1),
(ante → cons_, 0)
```

**`p → q` — a single static `.imp`-node position in `φ0`'s parse tree, appearing exactly once in
`intSubfmls φ0` — fires the world-creating rule at EIGHT distinct labels (1 through 8), not one.**
The three sibling positions (`u1→v1`, `u2→v2`, `u3→v3`) each fire exactly once, consistent with
the injection claim; `p → q` alone violates it by a factor of 8.

## Why this happens (confirmed against the actual code, not guessed)

The docstring's premise — "F-signed formulas never propagate via persistence" — is true and
irrelevant to what actually happens. The mechanism is:

1. `T(A1 → r)@1` is placed at world 1 (original, from `ante`'s `.and`-decomposition). It is
   **`.pos`-signed**, so it is eligible for persistence copying.
2. Each of the three sibling disjuncts (`F(u_i → v_i)@1`) independently fires the world-creating
   rule, minting a fresh world `w_i`. `intFImpRule`'s `propagatePersistence` copies **every**
   `T`-formula currently at world 1 — including `T(A1 → r)@1` — to each new `w_i`.
3. `applyAllTImpRules` (`Expansion.lean:129-147`, run to fixpoint at the top of every `go` step)
   independently reinforces this: for every `T(φ → ψ)` on the branch, it copies `T(φ → ψ)` **itself**
   to every world accessible from its own label that lacks a copy — a *second*, broader copying
   channel beyond `propagatePersistence`, by design (its docstring at `Expansion.lean:117-126`
   states this explicitly as "Deliverable 6").
4. Each fresh copy `T(A1 → r)@w_i` is a **new** `(sign, formula, label)` triple, distinct from the
   original and from every other copy, so `intStepBranch`'s `expanded`-membership check does not
   suppress it. Each copy independently fires `.pos,.imp`'s BETA branch
   `[[F(A1)@w_i],[T(r)@w_i]]`; DFS-leftmost exploration picks `F(A1)@w_i = F(p → q)@w_i`.
5. `F(p → q)@w_i` is itself `.neg,.imp`-shaped, so it independently fires the world-creating rule
   again — one genuine new-world consumption **per copy**, i.e. once per sibling, all attributable
   to the single static position "`p → q`".

This is not an artifact of a contrived pathological input: it is the direct, necessary consequence
of (a) an antecedent-shared implication being placed as a `T`-formula available for copying, and
(b) *any* branching that creates two or more sibling worlds from the world holding that
`T`-formula. Both (a) and (b) are ordinary, unavoidable tableau behavior — `ante`'s AND-decomposition
and `cons_`'s OR-decomposition are the two most basic connectives in the calculus, not edge cases.

## What is and is not established

- **Established, with reproducible evidence**: the plan's stated proof strategy — an injective map
  from world-creation events into `List.countP isImpShaped (intSubfmls φ0)` — is false as stated.
  `intSubfmls_impCount_le` (a genuinely correct, already-proven, unrelated combinatorial fact about
  static positions) cannot serve as the codomain of the needed injection, because the map is not
  injective: a single position can be — and demonstrably is — consumed multiple times.
- **Not established either way**: whether the target numerical conclusion
  `nextWorld ≤ φ0.complexity + 1` is itself true. The counterexample above still satisfies it
  (8 creation events plus initial world 0, against a bound of 11) — the *proof route* is refuted,
  not (yet, and not necessarily) the *bound*. Two follow-on stress tests attempting to compound the
  effect (nesting the shared position inside a right-associated implication chain of depth ≥ 2,
  intended to multiply the per-copy cost) both **timed out** in the `#eval` sandbox before returning
  a result, for reasons not diagnosed (plausibly `applyAllTImpRules`'s fixpoint re-scanning every
  branch member on every step, interacting with a deeper, still-growing branch — not confirmed to
  be non-termination as opposed to merely slow). This is genuinely open, not swept aside: it is
  reported as unresolved rather than asserted in either direction.

## Disposition (per R10's stopping condition)

Per the plan's own Rollback/Contingency and R10 mitigation: "If the injection cannot be
constructed within this dispatch, commit whatever is green, mark `[PARTIAL]`, and record the exact
resisting goal plus which of the three local step facts failed. Do not introduce a `sorry`, do not
weaken the bound to a vacuous statement, and do not proceed to Phase 4."

The first local step fact Phase 3 asks for — "(ii) each such firing is associated with a distinct
`.imp`-node position of φ0" — is the one that fails, and it fails not because it resists proof
within budget but because it is **false as stated**, with a concrete, reproducible counterexample.
This is a stronger finding than an ordinary stall, so Phase 3 is marked `[BLOCKED]` rather than
`[PARTIAL]`: there is no green partial Lean artifact to commit (the investigation was conducted
entirely via throwaway `#eval` snippets against the unmodified library, per the plan's own
"prohibit new axioms/sorries/vacuous statements" constraint — no speculative Lean was written
against a strategy already known to be unsound).

**This task requires re-planning before Phase 3/4 can be attempted again.** Candidate directions
for a re-plan (not evaluated further here — that is out of scope for a timeboxed check):

1. **A multiset/amortized argument** instead of a strict injection: bound the *total* number of
   `(position, copy-instance)` pairs some other way — e.g. by the number of `(imp-position, source
   world)` pairs, using the fact that copying only ever happens from an already-bounded source set
   (this still needs a base case and has its own circularity risk with the very quantity being
   bounded).
2. **A potential/measure-based argument** tied to `intExpMeasure`'s existing base-3 damped worklist
   measure (already proven, already sized against `intFuel`) rather than a fresh combinatorial
   count — possibly `intExpMeasure_step_lt`/`_branch` (already sorry-free, currently zero call
   sites per Postmortem 1) are closer to the right tool than a new injection lemma, if the goal is
   restated as "this specific numeric quantity decreases" rather than "the world count is bounded".
3. **Independently reverify the target bound itself** with a faster, more targeted computational
   search (e.g. a native-compiled test harness rather than `#eval`, or hand-instrumented tracing
   inside a copy of `intExpandBranches` rather than black-box `#eval` of the public function) before
   investing further proof-engineering effort in either direction.

## Evidence trail

The two working `#eval` snippets (the complexity-10 three-sibling counterexample, and its
`negImpPairs` diagnostic) were run directly against
`Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` at commit `49fbfe3c` (this task's
Phase 2 relocation commit) via the `lean-lsp` MCP `lean_run_code` tool. No files were created or
modified by this investigation; it is reproducible by re-running the snippets in this document
against the same commit.
