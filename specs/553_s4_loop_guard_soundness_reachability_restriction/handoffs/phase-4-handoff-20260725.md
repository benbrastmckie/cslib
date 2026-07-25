# Handoff: Task 553, Phases 1-3 complete, Phase 4 designed but not started

## State

Phases 1-3 of `plans/01_s4-settled-context-scheduling.md` are complete, committed, and verified
green (each its own commit: `task 553 phase 1/2/3: ...`). `lake build` (scoped, per phase),
`lake test` (full suite, ran once after Phase 1 -- exit 0), `lake lint` (full project -- zero
warnings from touched files), `lake exe checkInitImports`, and `lake exe lint-style` all pass.
Repo-wide bare `sorry` count in `Cslib/` is unchanged at 5 throughout. No task-number citations
were introduced in any deliverable file.

Landed so far:
- `CslibTests/S4LoopGuardRegression.lean` (new) -- permanent regression corpus. `cex` (the
  node-size-19 counterexample) currently asserts `CLOSED` (the KNOWN-UNSOUND row, deliberately
  inverted per the plan; Phase 8 flips it). Live-set driver asserts `OPEN` on the same formula.
  B/T controls included.
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`'s `blockingWorldS4Keyed` docstring and
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`'s S4Keyed section header: both corrected
  to state the soundness half is FALSE AS STATED, not deferred, with the counterexample and both
  defects (staleness, no-reachability-restriction) named.
- `LoopChecking.lean`, new section right before `modalStepBranchS4Keyed` (around line 944 as of
  this commit; check current line numbers, they will have shifted after Phase 4 insertions):
  - `modalMintShape : SignedFormula (Proposition Atom) WorldIndex → Bool` -- true exactly at
    `F(□φ)@w` (`.neg, .box _`) and `T(◇φ)@w` (`.pos, .diamond _`).
  - `modalMintShape_boxNeg`, `modalMintShape_diaPos` (simp characterisation lemmas),
    `modalMintShape_eq_false_of_not_boxNeg_diaPos` (complement).
  - `modalNonMintCandidates φ₀ keys b e acc : List (SignedFormula (Proposition Atom)
    WorldIndex)` := `b.filter (fun sf => !modalMintShape sf && !(e.any (· == sf)) &&
    (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable)`.
  - `modalNonMintCandidates_subset` (`⊆ b`, via `List.filter_subset'` -- NOT
    `List.filter_subset`, which has a different signature: monotonicity in the list argument,
    not the "filter is a subset of the original" fact).
  - `modalNonMintCandidates_not_mem_expanded`.
  - `modalNonMintCandidates_eq_nil_iff` : the list is `[]` ↔ `∀ sf ∈ b, modalMintShape sf = true
    ∨ sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable`.

## Next: Phase 4 (`### Phase 4: Ordered Stepper and its Two Structural Lemmas [NOT STARTED]`)

Marked `[NOT STARTED]` in the plan file still -- I designed the approach below but made zero
edits toward it, so do not assume any Phase 4 code exists yet.

### The existing literal traversal to preserve as fallback

`modalStepBranchS4Keyed` (current line ~955, verify before editing -- it will have shifted) is:

```lean
def modalStepBranchS4Keyed (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility ×
            List (WorldIndex × Finset (Sign × Proposition Atom))) :=
  b.findSome? fun sf =>
    if e.any (· == sf) then none
    else
      let (result, newAcc) := modalApplyOneS4Keyed φ₀ keys sf b acc
      let keys' :=
        match sf.sign, sf.formula with
        | .neg, .box φ =>
          match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
          | some _ => keys
          | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)]
        | .pos, .diamond φ =>
          match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
          | some _ => keys
          | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)]
        | _, _ => keys
      match result with
      | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
      | .branching branches =>
        some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
      | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
      | .notApplicable => none
```

**Do not touch this definition.** It must stay byte-for-byte as is (the plan's explicit
requirement, so the landed completeness line stays green).

### Recommended definition of `modalStepBranchS4KeyedOrdered`

Copy the per-formula body **verbatim** (same match arms, same `keys'` computation) but run it
via `findSome?` over `modalNonMintCandidates φ₀ keys b e acc` first, falling back to
**literally calling** `modalStepBranchS4Keyed φ₀ b e acc keys` (not re-deriving `b.findSome?`
separately) when the first search is `none`:

```lean
def modalStepBranchS4KeyedOrdered (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility ×
            List (WorldIndex × Finset (Sign × Proposition Atom))) :=
  match (modalNonMintCandidates φ₀ keys b e acc).findSome? (fun sf =>
      if e.any (· == sf) then none
      else
        let (result, newAcc) := modalApplyOneS4Keyed φ₀ keys sf b acc
        let keys' :=
          match sf.sign, sf.formula with
          | .neg, .box φ =>
            match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
            | some _ => keys
            | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)]
          | .pos, .diamond φ =>
            match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
            | some _ => keys
            | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)]
          | _, _ => keys
        match result with
        | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
        | .branching branches =>
          some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
        | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
        | .notApplicable => none) with
  | some r => some r
  | none => modalStepBranchS4Keyed φ₀ b e acc keys
```

Using the literal call `modalStepBranchS4Keyed φ₀ b e acc keys` as the fallback (rather than
re-deriving the same `b.findSome?` inline) is what makes `_eq_none_iff` nearly free: the
fallback branch of the match is DEFINITIONALLY the old driver's result.

### Key fact to prove FIRST, as a private helper (unlocks all three required lemmas)

**Every element of `modalNonMintCandidates` makes the per-formula body evaluate to `some`, never
`none`.** Concretely: for `sf ∈ modalNonMintCandidates φ₀ keys b e acc`, unfolding gives
`sf ∈ b`, `modalMintShape sf = false` (hence unused for the match arms below), `sf ∉ e` (from
`modalNonMintCandidates_not_mem_expanded`), and `(modalApplyOneS4Keyed φ₀ keys sf b acc).1 ≠
.notApplicable` (from the filter's third conjunct, `RuleResult.isApplicable = true`). The
per-formula body's only `none`-producing arms are the `if e.any (· == sf) then none` guard
(excluded, `sf ∉ e`) and the `.notApplicable => none` result arm (excluded, applicable). So the
body evaluates to `some (...)` for every candidate. This is the SAME fact already used
implicitly in Phase 3's `modalNonMintCandidates_eq_nil_iff` proof (that lemma's forward
direction constructs exactly this "body sf = some" witness to derive a contradiction with
`hnp : ¬ pred sf = true`) -- so it may be worth extracting as a small reusable private lemma
rather than re-deriving it three times.

**Corollary A**: `modalNonMintCandidates φ₀ keys b e acc = [] ↔ (modalNonMintCandidates φ₀ keys
b e acc).findSome? body = none`. Forward: empty list, `findSome?` on `[]` is `none` by
`List.findSome?_nil`. Backward: contrapositive -- if candidates nonempty, its head (or any
element) makes body evaluate to `some` per the key fact above, so `findSome?` cannot be `none`
(use `List.findSome?_eq_none_iff` if it exists, or manually: `List.findSome?_isSome`-style
reasoning, or simplest, case on the list: `cases hc : modalNonMintCandidates ... with | nil =>
... | cons hd tl => have := <key fact applied to hd> ; <derive findSome? = some _ via
List.findSome?_cons_of_some or by unfolding find/findSome? one step>`.

### `modalStepBranchS4KeyedOrdered_eq_none_iff`

`modalStepBranchS4KeyedOrdered φ₀ b e acc keys = none ↔ modalStepBranchS4Keyed φ₀ b e acc keys =
none`. Proof: case on `(modalNonMintCandidates φ₀ keys b e acc).findSome? body`.
- `= none`: the ordered stepper's `match` reduces definitionally to
  `modalStepBranchS4Keyed φ₀ b e acc keys` (the fallback arm), so both sides are literally the
  same expression -- `Iff.rfl` after `simp only [modalStepBranchS4KeyedOrdered, hcase]` (or
  similar unfold), no further work.
- `= some r`: LHS is `some r ≠ none`. For RHS, extract `∃ x ∈ modalNonMintCandidates ...,
  body x = some r` via `List.exists_of_findSome?_eq_some` applied to the case hypothesis (this
  is the SAME Batteries/core lemma Phase 5's measure-proof bridge already relies on, named
  explicitly in the plan's Phase 5 section -- confirm its exact import path/namespace when you
  reach for it; it was NOT needed in Phases 1-3 so its availability has not yet been confirmed
  in this session). From `x ∈ modalNonMintCandidates ...`, get `x ∈ b` (via
  `modalNonMintCandidates_subset`) and `body x = some r ≠ none`, hence
  `modalStepBranchS4Keyed φ₀ b e acc keys = b.findSome? body ≠ none` (since `findSome?` over `b`
  can't be `none` while some element of `b` makes `body` return `some`). Both sides `≠ none`,
  done.

### `modalStepBranchS4KeyedOrdered_selected_mem`

Recommend proving a single case-split helper FIRST (this also directly discharges
`_mintReady` as a corollary, see below), rather than writing three separate ad hoc proofs:

```lean
lemma modalStepBranchS4KeyedOrdered_cases (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (bs es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (acc' : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (h : modalStepBranchS4KeyedOrdered φ₀ b e acc keys = some (bs, es, acc', keys')) :
    (∃ sf ∈ modalNonMintCandidates φ₀ keys b e acc, <body sf> = some (bs, es, acc', keys')) ∨
    (modalNonMintCandidates φ₀ keys b e acc = [] ∧
      modalStepBranchS4Keyed φ₀ b e acc keys = some (bs, es, acc', keys'))
```

(`<body sf>` = the same per-formula body expression, written out.) Proof: case on
`(modalNonMintCandidates φ₀ keys b e acc).findSome? body` exactly as in `_eq_none_iff` above;
`some r` case uses `List.exists_of_findSome?_eq_some` for the left disjunct; `none` case uses
Corollary A for `= []` and the match's reduction to the fallback for the right disjunct.

From `_cases`, `_selected_mem` follows by: in the left disjunct, `sf ∈ candidates ⊆ b` (via
`modalNonMintCandidates_subset`) and `sf ∉ e` (via `modalNonMintCandidates_not_mem_expanded`),
plus the four-way result-shape case split on `<body sf> = some (...)` (mirrors the existing
`List.exists_of_findSome?_eq_some` destructuring pattern the CURRENT `modalStepBranchS4Keyed`
consumers already use elsewhere in this file -- grep for `List.exists_of_findSome?_eq_some` to
find a template). In the right disjunct, apply the SAME extraction to
`modalStepBranchS4Keyed φ₀ b e acc keys = some (...)` (its own `b.findSome?` unfolds the same
way) to get `sf ∈ b`, `sf ∉ e` and the shape facts.

### `modalStepBranchS4KeyedOrdered_mintReady`

Corollary of `_cases`: given `h : modalStepBranchS4KeyedOrdered ... = some (bs,es,acc',keys')`
and (however the final statement chooses to name "the selected formula" -- recommend requiring
the caller to supply `sf` together with a proof that `<body sf> = some (bs,es,acc',keys')`,
matching `_cases`'s left-disjunct shape exactly, so the statement is self-consistent with what
`_selected_mem` produces) plus `modalMintShape sf = true`: apply `_cases` to `h`; the left
disjunct is impossible (its `sf' ∈ candidates` would force `modalMintShape sf' = false` via
`List.mem_filter` unfolding `modalNonMintCandidates`'s definition, but uniqueness of the `sf`
producing a given output tuple is NOT generally available for free -- if the two disjuncts'
witnessing `sf`s cannot be proven equal cheaply, consider instead stating `_mintReady` to take
its OWN `hsel` hypothesis of the same shape as `_cases`'s disjuncts directly, sidestepping the
uniqueness question entirely: i.e. state it as "IF `sf ∈ modalNonMintCandidates ...` (i.e. we
are demonstrably in the candidates-stage) AND `modalMintShape sf = true`, THEN False" (immediate
from the filter) "used to conclude candidates = [] as the ordered stepper's provenance" --
reread the plan's exact wording before finalizing the statement shape, since the plan phrases it
as a fact about "the selected formula" and Phases 9-11 are the actual consumers; matching
whatever shape Phase 9-11's redirect-inertness proof will need to consume is more important than
matching my speculative phrasing above verbatim.

## Watch-outs (mistakes already made and fixed this session, don't repeat)

- `List.filter_subset` is NOT "filter result ⊆ original list" -- it's monotonicity in the list
  argument (`l₁ ⊆ l₂ → filter p l₁ ⊆ filter p l₂`). The lemma needed is `List.filter_subset'`
  (Mathlib, `Data/List/Basic.lean`) or the identically-stated `List.filter_subset_self`.
- `Bool.and_eq_true`, `Bool.not_eq_true'`, `Bool.not_eq_true`, `List.any_eq_true`,
  `List.any_eq_false`, `List.filter_eq_nil_iff` are all real core/Mathlib lemma names verified
  via `lean_loogle` this session and used successfully in Phase 3's proofs -- reuse them rather
  than re-deriving Bool arithmetic by hand.
- `RuleResult.isApplicable` is NOT a `@[simp]` lemma; always pass it explicitly to `simp`/`unfold`
  when case-splitting on a `RuleResult` value's applicability.
- Confirm current line numbers before editing -- Phase 3 shifted everything after line ~465 by
  +138 lines relative to the pre-Phase-3 file.

## Verification checklist for Phase 4 before committing

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds.
- `lean_verify` (fully-qualified `Cslib.Logic.Modal.Tableau.<name>`) on all three required
  lemmas: only `propext`, `Classical.choice`, `Quot.sound` in the axiom list, no `sorryAx`.
- `git grep -hE '^\s*sorry\s*$' -- 'Cslib'` still reads exactly 5.
- Confirm `modalStepBranchS4Keyed` and everything downstream of it (grep for its name across
  `LoopChecking.lean`, `FrameSoundness.lean`, `FrameCompleteness.lean`) still compiles unchanged
  -- it must not have been touched.
- Mark `### Phase 4: ...` `[COMPLETED]` in the plan file, commit as
  `task 553 phase 4: ordered stepper and its two structural lemmas`.
