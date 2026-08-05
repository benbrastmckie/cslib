# Research Report: canonical_witness_restriction_probe

## Verdict: CONDITIONAL GO

Restricting the redirect-preservation agreement lemma's witness carrier closes the two
machine-checked stuck cases (`box.mp.inr`, `diamond.mpr`) recorded in the
pinned-witness-truth-lemma plan's `#### Phase 1 Verdict`, **but only if the witness is further
committed to a canonical/term model** (mirroring `extractModelWith`/`extractModelS4`) rather than
left an arbitrary pinned witness. A plain carrier restriction alone (fixing `W := WorldIndex`,
`f := id`, with no further constraint on the witness's valuation) does **not** close the cases: it
merely removes one obstruction (the escape to non-label points) and exposes a second, deeper one
(the semantic-to-syntactic truth-lemma gap) that was previously masked. Both obstructions were
machine-checked in this task, in that order, and the second is priced in Phase 3 below at
5-7 phases / 13.5-17.5 hours for a task-553 v6 plan.

## Probe Method

Two restrictions were attempted in sequence, front-loaded before any large construction, using
CSLib's append-then-revert probe pattern (a probe section delimited by
`/-! ### CANONICAL-WITNESS RESTRICTION PROBE -- REVERT UNLESS SORRY-FREE -/` at the end of
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`), each under a one-dispatch (2-hour) budget per
this task's own kill-gate discipline:

1. **Restriction A** (`W := WorldIndex`, `f := id`, the literal form the pinned-witness-truth-lemma
   plan's Verdict named). Attempted, machine-checked stuck, reverted (did not close sorry-free).
2. **Restriction B1** (carrier restricted to the known-branch-labels subtype
   `{w : WorldIndex // w ∈ modalKnownWorlds b}`, `f` the coercion). Attempted, closed sorry-free
   **conditional on two assumed hypothesis groups**, retained as a landed Lean declaration.

A third phase (pricing) then classified the consequences of adopting Restriction B1/the canonical
choice against the existing `branchSatisfiablePinnedIn` vocabulary, including one further
reverted confirmatory Lean check.

## Phase 1: Restriction A -- Machine-Checked Stuck (Outcome (ii): ESCALATE)

The Restriction-A agreement lemma was stated as a standalone probe over `m : Model WorldIndex
Atom` (carrier fixed to `WorldIndex`, `f` eliminated as `id`), carrying `hsrc`, `hwB`, `hbox`,
`hdia` in the exact shape the pinned-witness-truth-lemma plan's gate lemma used (`hsat` elided to
`True`: its real type `modalS4Saturated` lives in `LoopChecking.lean`, which
`FrameSoundness.lean` does not import, and the elision does not affect the verdict -- both stuck
goals below are reached without ever needing `hsat` to fire).

**`case box.mp.inr`, machine-checked stuck goal**:

```
case box.mp.inr
b : List (SignedFormula (Proposition Atom) WorldIndex)
src wBlock : WorldIndex
m : Model WorldIndex Atom
hsrc : src ∈ modalKnownWorlds b
hwB : wBlock ∈ modalKnownWorlds b
hsat : True
hbox : ∀ (ψ : Proposition Atom),
  { sign := Sign.pos, formula := □ψ, label := src } ∈ b → { sign := Sign.pos, formula := □ψ, label := wBlock } ∈ b
hdia : ∀ (ψ : Proposition Atom),
  { sign := Sign.neg, formula := ◇ψ, label := src } ∈ b → { sign := Sign.neg, formula := ◇ψ, label := wBlock } ∈ b
φ : Proposition Atom
ih : ∀ (x : WorldIndex), Satisfies m x φ ↔ Satisfies { r := fun x y => m.r x y ∨ m.r x src ∧ m.r wBlock y, v := m.v } x φ
x : WorldIndex
hbx : Satisfies m x (□φ)
y : WorldIndex
hxsrc : m.r x src
hwy : m.r wBlock y
⊢ Satisfies { r := fun x y => m.r x y ∨ m.r x src ∧ m.r wBlock y, v := m.v } y φ
```

Attempted closers (`lean_multi_attempt`, all fail): `aesop` ("failed to prove the goal after
exhaustive search"), `tauto`, `simp_all`, `solve_by_elim [hbx, hxsrc, hwy, hsrc, hwB, hbox]`, and
the direct term `exact (ih y).mp (hbx wBlock hwy)` (type mismatch: `hwy : m.r wBlock y` does not
match the expected `m.r x wBlock`).

**`case diamond.mpr` (`diamond.mpr.inr` after `rcases`), machine-checked stuck goal**:

```
case diamond.mpr.inr
b : List (SignedFormula (Proposition Atom) WorldIndex)
src wBlock : WorldIndex
m : Model WorldIndex Atom
hsrc : src ∈ modalKnownWorlds b
hwB : wBlock ∈ modalKnownWorlds b
hsat : True
hbox : ∀ (ψ : Proposition Atom),
  { sign := Sign.pos, formula := □ψ, label := src } ∈ b → { sign := Sign.pos, formula := □ψ, label := wBlock } ∈ b
hdia : ∀ (ψ : Proposition Atom),
  { sign := Sign.neg, formula := ◇ψ, label := src } ∈ b → { sign := Sign.neg, formula := ◇ψ, label := wBlock } ∈ b
φ : Proposition Atom
ih : ∀ (x : WorldIndex), Satisfies m x φ ↔ Satisfies { r := fun x y => m.r x y ∨ m.r x src ∧ m.r wBlock y, v := m.v } x φ
x y : WorldIndex
hsy : Satisfies { r := fun x y => m.r x y ∨ m.r x src ∧ m.r wBlock y, v := m.v } y φ
hxsrc : m.r x src
hwy : m.r wBlock y
⊢ Satisfies m x (◇φ)
```

Attempted closers, all fail: `aesop`, `tauto`, `simp_all`, and the direct term
`exact ⟨wBlock, hxsrc, ?_⟩` (type mismatch: the goal needs `m.r x wBlock` as the first conjunct,
but `hxsrc : m.r x src` only supplies `m.r x src`).

**Diagnosis.** Restriction A changes the carrier type and eliminates the embedding, but does
**not** constrain the universally-quantified induction variable `x` to be a *known* label:
`x : WorldIndex` still ranges over all of `WorldIndex`, of which `modalKnownWorlds b` is a strict
sub-list. Both stuck goals are the same shape as the pinned-witness-truth-lemma plan's own Verdict
up to the carrier/embedding substitution (`f src` becomes `src`, `f wBlock` becomes `wBlock`,
`x : W` becomes `x : WorldIndex`) -- the escape is unchanged because fixing the carrier does not
imply `x` is a known label of `b`. **Outcome (ii): ESCALATE to Restriction B**, exactly as this
plan's own "Planning-run correction to the fix's own framing" section anticipated.

## Phase 2: Restriction B1 -- Conditional Pass (Outcome (ii): GATE A'' PASSES, conditional)

**Chosen encoding: B1** (carrier `{w : WorldIndex // w ∈ modalKnownWorlds b}`, `f` the coercion),
over B2 (a `WorldIndex`-plus-closure-side-condition encoding), because B1 makes the induction
variable a known label *by its type* -- discharging `accPinnedBy`'s membership hypotheses
definitionally rather than threading a separate closure invariant through every case.

A lemma `canonicalWitnessRestrictionProbe_agreementConditional` was appended and **retained**
(landed sorry-free; not reverted) at
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean:5422`. It restates the agreement claim over
`m : Model {w : WorldIndex // w ∈ modalKnownWorlds b} Atom`, carrying:

- `hpinned` -- `accPinnedBy` adapted to the B1 carrier (real content): `∀ w w' : Known, m.r w w'
  → ReflTransGen acc w.1 w'.1`.
- `hbSat`/`hbUnsat` -- `branchSatisfiablePinnedIn`'s branch conjunct specialized at `wBlock`, both
  signs (real content).
- `hbox`/`hdia` -- unchanged from Restriction A (real content).
- `hpropBox`/`hpropDia` -- S4 box/diamond-content forward-persistence-along-`acc`-reachability.
  **Genuinely assumed**: this is Decision Gate B's territory in the pinned-witness-truth-lemma
  plan (its own, separate, still-unexecuted Phase 2), not this task's. Re-deriving it needs
  `modalS4Saturated`/`LoopChecking.lean`, unavailable to `FrameSoundness.lean` without an import
  this probe's append-only edit region does not permit.
- `htruthBoxPos`/`htruthDiaNeg` -- the **truth-lemma** direction: `Satisfies m w (□ψ) →
  T(□ψ)@w.1 ∈ b`, and the diamond-negative dual. **Genuinely assumed** -- this is the phase's
  central named question, answered below.

With all of the above in scope, both cases close by direct forward chaining, with no `sorry` and
no automation hammer: `box.mp.inr` via `htruthBoxPos → hpinned → hpropBox → hbox → hbSat →` unfold
box; `diamond.mpr` via `by_contra → htruthDiaNeg → hpinned → hpropDia → hdia → hbUnsat →`
contradiction against the inductive-hypothesis-transported witness. `lean_verify` reports axioms
`propext`, `Classical.choice`, `Quot.sound` only. `lake build
Cslib.Logics.Modal.Tableau.FrameSoundness`, `lake exe lint-style`, and `lake lint` (scoped to this
declaration and its line range) are all clean.

**The truth-lemma question, answered explicitly.** No hypothesis already in scope -- not
`hpinned`, not `hbSat`/`hbUnsat`, not `hbox`/`hdia`, not the carrier restriction itself -- supplies
`htruthBoxPos`/`htruthDiaNeg` for an *arbitrary* pinned witness `m`. `branchSatisfiablePinnedIn`'s
existential quantifies over *any* `m` satisfying its four conjuncts; the branch conjunct only
constrains `m` in the branch-to-model direction (`T(□ψ)@w ∈ b → Satisfies m (f w) (□ψ)`), never
the converse. The converse (model-to-branch) direction is a genuine soundness-of-negation /
completeness fact, true only when `m`'s valuation is built to *read* branch membership directly
(`extractModelWith`'s shape) combined with a Hintikka/saturation argument -- i.e. a full truth
lemma. **Answer: the truth-lemma direction is NOT available for free; it requires committing to a
canonical/term model rather than an arbitrary pinned witness.**

**`accPinnedBy` degeneration check.** Under B1, the specialized `accPinnedBy` hypothesis is *not*
a degeneration to a total bound `m.r ≤ ReflTransGen acc` -- the restricted carrier already
excludes unknown points, so the hypothesis is exactly as strong as the original `accPinnedBy`
restricted to its own domain. Checked against the reflexive case (`w = w'`); no unsatisfiability
risk identified.

**Why retained, not reverted.** The lemma lands sorry-free (its two assumed hypothesis groups are
explicit parameters, not `sorry`), so per this task's own Rollback/Contingency contract it is
kept as the task's one retained Lean artifact rather than reverted.

## Phase 3: Pricing (GO branch)

**Field-by-field classification of `branchSatisfiablePinnedIn`'s four conjuncts**, under the fully
canonical choice (`W := WorldIndex`, `m.r := Relation.ReflTransGen (acc.hasEdge)`, `f := id`):

| Field | Classification | Reasoning |
|---|---|---|
| `FC m.r` (`s4FC`) | **Collapses** | Free from `Relation.reflexive_reflTransGen` / `Relation.transitive_reflTransGen`, the same route `extractModelS4_refl`/`extractModelS4_trans` already take. |
| Edge conjunct | **Collapses** | `Relation.ReflTransGen.single`, one line. |
| `accPinnedBy` conjunct | **Collapses** | Machine-confirmed (reverted confirmatory check): the hypothesis becomes definitionally identical to the conclusion; the whole conjunct is discharged by `id`. |
| Branch conjunct | **Re-shapes (does not collapse)** | Requires the truth lemma -- the one conjunct with genuinely new proof content. |
| Existential `W`, `m`, `f` | **All collapse to fixed choices** | `WorldIndex`, the canonical relation + a branch-reading valuation, and `id`, respectively. |

**`branchSatisfiablePinnedIn_redirect_mechanical` survival.** Its proof is parametric over any
witness satisfying the three mechanical conjuncts -- it does not inspect what `W`/`m`/`f` *are*.
**All four proof bullets (`Std.Refl`, the `IsTrans` four-case split, the edge conjunct via
`hasEdge_addEdge_cases`, and the `accPinnedBy`-preservation composition) survive verbatim,
unconditionally.** A v6 plan does not need a phase to re-derive this lemma.

**Canonical/term-model construction, priced** (three components):

1. **Valuation**: reuse `extractModelWith`'s clause verbatim, by cross-reference (open design
   question for v6: import `FrameCompleteness.lean` into the soundness side, or re-state the
   three-line valuation locally).
2. **Truth lemma**: `∀ w ∈ modalKnownWorlds b, ∀ χ, Satisfies m w χ ↔` (saturated branch
   membership) -- new proof content, a structural induction mirroring the standard tableau
   completeness argument; its box/diamond cases need the same `modalS4Saturated`-family facts this
   task's Phase 2 had to abstract away.
3. **Base-case and redirect-step re-assembly**: cheap for three conjuncts (per the collapse
   analysis), gated on the truth lemma (component 2) and Gate B (`modalS4Saturated`
   availability, v5's own still-unexecuted Phase 2) for the branch conjunct at both the initial
   state and after the redirect.

**Effort estimate for a task-553 v6 plan, decomposed by workstream:**

| Workstream | Phase(s) | Estimate | Depends on |
|---|---|---|---|
| Decision Gate B (`modalS4Saturated` at a settled ordered-stepper state) | 1 | 3h | none |
| Truth lemma | 1-2 | 4-6h | Gate B |
| Canonical base-case assembly | 1 | 1.5h | truth lemma |
| Redirect-preservation re-assembly | 1 | 2h | base case, truth lemma |
| Wire into 553's soundness argument | 1-2 | 3-5h | redirect re-assembly |
| **Total** | **5-7** | **13.5-17.5h** | -- |

**Residual risk.** The truth lemma's box/diamond cases may need more from `modalS4Saturated` than
Gate B actually supplies -- a *seventh* obstruction. A v6 plan should front-load this as its own
Gate 0: a standalone micro-probe of the truth lemma's box-positive case, under the same
one-dispatch kill-gate discipline this task used, before committing to the full 5-7 phase
programme.

## What Was Not Done, and Why

- **The FrameCompleteness refactor programme was not re-run.** It already landed: its box-plus
  birth content is inline in mainline `successorBirthContent`/`blockingWorldS4Keyed` in
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, not as the separate parallel `...Boxed` family
  earlier plans anticipated.
- **The standing `sorry` was not touched.** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1251`
  (`branchSatisfiableIn_s4FC_ancestor_redirect`) is retained by explicit user decision and was
  outside every phase's declared edit region.
- **The three sub-step 1.1 declarations were preserved unmodified.** `accPinnedBy`,
  `branchSatisfiablePinnedIn`, `branchSatisfiablePinnedIn_redirect_mechanical` (re-located by grep
  at `FrameSoundness.lean:5323`, `:5332`, `:5356`) are byte-identical to their pre-task state --
  confirmed by `git diff` showing no hunk touching them.
- **Decision Gate B (`modalS4Saturated` availability) was not attempted.** It is the
  pinned-witness-truth-lemma plan's own separate Phase 2, out of this task's scope; its
  conclusion is assumed abstractly (via `hpropBox`/`hpropDia`) in this task's Phase 2 probe.
- **No v6 plan was written.** Phase 3 prices what one would need; writing it is a follow-on task's
  job, per this task's own Non-Goals.

## Cross-Reference

Task 553's blocker record (`specs/553_s4_loop_guard_soundness_reachability_restriction/reports/05_gate-a-canonical-witness-blocker-analysis.md`)
has been updated with a pointer to this report (see that file's "After Completion" section).
