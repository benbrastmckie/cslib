# Phase 0 Verification Spike — Decision Record

## R1 pinned-SHA check

`git log -1 --format=%H -- Cslib/Foundations/Logic/Tableau/Measure.lean` returns
`facba1f42469805b666d6eca78156ac4d7be5c71`, matching the plan's pinned SHA exactly. No mismatch.

## Sorry re-grep

Strict scan over `Cslib/Logics/Propositional/Tableau/` returns exactly the plan's expected 4
hits, unchanged line numbers:
- `Intuitionistic/Completeness.lean:133`
- `Minimal/Completeness.lean:125`
- `Intuitionistic/Scheme.lean:592`
- `Intuitionistic/Scheme.lean:1498`

Repo-wide strict scan: 29 hits (matches plan baseline).

## R8: `IBranchSaturation` construction sites

`grep -rn "IBranchSaturation" Cslib/` shows exactly one construction site:
`IExpandedConsistent_sat` (`Intuitionistic/Scheme.lean:904-974`, `constructor` building all 5
fields via the `compound_sat`/`intStepBranch_none_compound_mem` idiom). All other hits are
type annotations, docstrings, or the `structure` declaration itself. Confirmed: no second
construction site in `Soundness.lean`. R8 does not fire.

## Question (a): does forward-only disjunction elimination close `Scheme.lean:592`?

`lean_goal` at `Scheme.lean:592` confirms the exact goal:
```
hsat : IBranchSaturation Atom b
hfimp : IFimpAccess edges b
w : ℕ
a✝ : T(φ'→ψ')@w ∈ b
⊢ ∀ (w' : ℕ), w ≤ w' → IForces val w' φ' → IForces val w' ψ'
```
`sfSatisfied`'s `.pos, .imp` clause (`Scheme.lean:765-771`) already states the exact same-label
disjunction `sat_timp` needs (`F(φ')@l ∈ b ∨ T(ψ')@l ∈ b`), reflexively at the rule's own label
— confirmed by reading `intApplyRuleFull`'s `.pos, .imp` case (`Rules.lean:274-275`,
`.branchingResult [[⟨.neg,φ,l⟩],[⟨.pos,ψ,l⟩]] nextWorld`, hence `≠ .notApplicable`, so
`compound_sat`'s pattern applies unchanged). Given `sat_timp` (reflexive, at `w'`, once added)
and `ITimpAccess` (copy at `w'` since `w'` is edge-accessible, once defined/delivered), the case
closes as: obtain the copy at `w'` from `ITimpAccess`; `hsat.sat_timp` at `w'` gives
`F(φ')@w' ∈ b ∨ T(ψ')@w' ∈ b`; `F(φ')@w'` arm is the contrapositive of `ih_φ'`'s F-direction
against the given `IForces val w' φ'`; `T(ψ')@w'` arm is `ih_ψ'`'s T-direction directly. No
converse IH needed. **Verdict: CONFIRMED. Route (a)'s decomposition works exactly as planned.**

## Question (b): do the two validity bridges need an atom-persistence obligation beyond `sat_timp`?

Read `tableau_complete`'s `hvalid` binder (`Scheme.lean:1927-1930`):
`∀ (edges : IEdges) (b : IBranch Atom), @IForces ... (intAccessPreorder edges)
(intExtractValuation b) (S.modelBot b) 0 φ` — quantified over **arbitrary** `edges`/`b`, not
just the pair `openBranch_countermodel` produces. `lean_goal`/read at
`Intuitionistic/Completeness.lean:133` and `Minimal/Completeness.lean:125` confirms both bridges
are `intro edges _b; sorry` against this same arbitrary-quantified premise — `IValid φ`/
`MValid φ` give forcing at `World = Nat` for SOME upward-closed valuation, not for
`intExtractValuation b` at an arbitrary unrelated `b`/`edges` pair, so the bridge is unprovable
at its current statement. **Verdict: CONFIRMED — matches the plan's Overview finding exactly.**
Phase 7's premise narrowing (adding `IAtomPersist edges b → (modelBot-persistence) → ...` to
`hvalid`'s binder) is required; this is not optional assembly.

## Phase sequence disposition

**CONFIRMED as written.** Both spike questions came back exactly as the plan predicted:
(a) yes — the eight-phase sequence proceeds unchanged; (b) yes — Phases 6 and 7 stay as
separate phases (R9's "no" branch does not apply). No re-plan needed.
