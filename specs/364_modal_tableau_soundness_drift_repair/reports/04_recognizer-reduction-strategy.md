# Research Report: Recognizer-Reduction Strategy for `modalStepBranch_preserves_sat`

- **Task**: 364 - modal_tableau_soundness_drift_repair
- **Started**: 2026-06-27
- **Completed**: 2026-06-27
- **Effort**: ~3 hours (research + scratch verification)
- **Dependencies**: Root A fix (commit 425c1c53) already landed
- **Sources/Inputs**:
  - `specs/364_.../.error-digest.md` (UPDATE section, sess_1782614477_39b09e)
  - `specs/364_.../.orchestrator-handoff.json`
  - `Cslib/Logics/Modal/Tableau/Defs.lean:105-190` (recognizers + @[simp] lemmas)
  - `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean:94-156` (applyPropRule, tryAllPropRules)
  - `Cslib/Logics/Modal/Tableau/Rules.lean:54-99` (modalApplyOne)
  - `Cslib/Logics/Modal/Tableau/Soundness.lean:200-967` (the proof, read as text only)
  - Scratch verification (`lake env lean`, file deleted after use)
  - Mathlib loogle: `List.of_mem_zip`, `List.getElem_zip`
- **Artifacts**: `specs/364_.../reports/04_recognizer-reduction-strategy.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md
- **Reference-grounding tier**: Tier 3 (implementation-backed; in-repo definitions are ground truth). The propositional/tableau rules trace to Fitting (see Appendix BibKey note).

## Executive Summary

- **Root cause confirmed and sharpened**: the two `| imp a c => cases c with | bot =>` arms
  (negPos at `Soundness.lean:269-289`, negNeg at `Soundness.lean:619-637`) handle `a → ⊥`
  **uniformly as negPos/negNeg**, but this is *both* a reduction failure *and* a semantic error.
  For abstract `a`, `modalAndOf?`/`modalOrOf?` cannot decide, so `find?` never reaches negPos and
  `hsf` never collapses (errors 275/624). Even if it collapsed, the uniform negPos refine is
  **wrong** when `a` is itself a negation (`orPos` fires) or a conjunction (`andPos` fires).
- **The `| bot =>` arm is NOT correct as written** — it must sub-case on `a` (a bounded depth-3
  case tree), exactly mirroring the existing `| atom _ | imp _ _ | box _ =>` (c ≠ ⊥) arm.
- **Two distinct bug classes were conflated in prior digests**:
  (1) **c = ⊥ arms** (negPos/negNeg) — need `cases a` restructuring (genuine work);
  (2) **c ≠ ⊥ arms** (already have `cases a`, semantically correct) — only the *stale nested
  obtain* `⟨⟨hnewBs, _⟩, hnewAcc⟩` is wrong; flatten to `⟨hnewBs, _, hnewAcc⟩` (mechanical).
- **Recommendation: hybrid, strategy-B-dominant.** `cases a` is *mandatory* for correctness of the
  c = ⊥ arms; the per-leaf reduction is `rfl`-grade once the head is concrete, so each leaf uses the
  *existing* simp set + flat obtain. Standalone `@[simp]` reduction lemmas (strategy A) are
  **not needed** and would invent conditioned lemmas that do not exist as unconditional simp facts.
- **Verified in scratch** (all `rfl`): negPos/orPos/andPos and negNeg/orNeg/andNeg fire exactly as
  derived; the stuck case (abstract `a2`) provably fails `rfl`; the flat obtain `⟨hnewBs, _, hnewAcc⟩`
  is the correct post-simp shape.
- **Tail items live in two *separate*, `hsf`-free theorems** (`modalExpandBranches_closed_unsat`,
  `modalTableau_sound`, lines 797-962) and are SAFE to repair with normal `lean_goal` tooling.

## Context & Scope

`Soundness.lean` has 61 scoped-build errors, zero `sorry`. 46 are `Unknown identifier` cascades
downstream of 3 root tactic failures inside `modalStepBranch_preserves_sat` (the theorem whose
`hsf` is a ~400-line unreduced match — forbidden to inspect with `lean_goal`). This report decides
the repair strategy for the recognizer-reduction roots and grounds every claim with file:line
citations and small-context scratch proofs (the only way to gather Lean evidence without overflow).

## Findings

### F1. Dispatch mechanics (grounded)

- `tryAllPropRules` order = `[andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg]`,
  selected by `results.find? (·.isApplicable) |>.getD .notApplicable`
  (`PropositionalRules.lean:153-155`).
- `applyPropRule` dispatches each rule through a recognizer (`PropositionalRules.lean:101-143`):
  andPos→`andOf?`, orPos→`orOf?`, impPos→`impOf?`, negPos→`negOf?`.
- `modalApplyOne` runs `tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?` first;
  if applicable, returns `(propResult, acc)` (`Rules.lean:75-77`).
- Recognizer patterns (`Defs.lean`):
  - `modalNegOf? (.imp a .bot) = some a` — `@[simp] modalNegOf?_neg` (`Defs.lean:110-117`). **Always matches `a → ⊥`.**
  - `modalOrOf? (.imp (.imp a .bot) b) = some (a,b)` (`Defs.lean:129-137`). Matches `a → ⊥` **iff `a` is a negation** (`a = p → ⊥`, then `b = ⊥`).
  - `modalAndOf? (.imp (.imp a (.imp b .bot)) .bot) = some (a,b)` (`Defs.lean:145-153`). Matches `a → ⊥` **iff `a = p → (q → ⊥)`**.
  - `modalImpOf? (.imp a .bot) = none` — `@[simp] modalImpOf?_neg` (`Defs.lean:175-178`). Never fires for `a → ⊥`.

### F2. Confirmed root cause (the `| bot =>` arm is incorrect as written)

For `formula = .imp a .bot` (sign `.pos`), the *first applicable* rule depends on `a`:

| head of `a` | `andOf?` | `orOf?` | rule that fires | current arm does |
|---|---|---|---|---|
| `p → (q → ⊥)` | some | none | **andPos** (`linear [T p, T q]`) | negPos — **WRONG** |
| `p → ⊥` (negation) | none | some | **orPos** (`branching [[T p],[T ⊥]]`) | negPos — **WRONG** |
| atom / `⊥` / `box φ` / `p → q` (q≠⊥, not negation) | none | none | **negPos** (`linear [F a]`) | negPos — correct |

So the arm at `Soundness.lean:269-289` is **doubly broken**: (a) for abstract `a` the recognizers
are undecided, `find?` stalls before negPos, and `hsf` stays the giant match → the `obtain` at
`:275` fails dependent elimination (Root B); (b) even granting reduction, the uniform
`refine ⟨[⟨.neg, a, lbl⟩] ++ b, …⟩` is semantically wrong for the andPos/orPos heads.
The F-side negNeg arm (`:619-637`) has the identical defect (uniform negNeg).

This is corroborated by the author having *already* solved the analogous problem correctly in the
c ≠ ⊥ arm: `:293-382` does `cases a … cases a2 …` and selects orPos / impPos per head.

### F3. The c ≠ ⊥ arms are semantically correct — only the obtain shape is stale

The c ≠ ⊥ arms (`:299,331,358` pos; `:645,701,725` neg) already `cases a`, so heads are concrete
and `hsf` collapses. Their only defect is the **nested** destructuring
`obtain ⟨⟨hnewBs, _⟩, hnewAcc⟩` (`:302,334,361,648,704,728`). The collapsed `hsf` is a
**right-associated 3-conjunct** `newBs = … ∧ newExps = … ∧ newAcc = …` (from `Option.some.injEq`
then two `Prod.mk.injEq`), so the correct pattern is the **flat** `⟨hnewBs, _, hnewAcc⟩` — exactly
the Root-A idiom committed at 425c1c53. These produce the `Unknown identifier hnewBs` cascade at
`:304,336,363,403,650,706,730`.

### F4. Scratch verification (H3/H4 evidence — all compiled with `lake env lean`, file then deleted)

Reduction is `rfl`-grade once the head is concrete (and `modalApplyOne` is unfolded, which the
proof already does at `:211` pos / `:386` neg). Confirmed by standalone `example`s:

- negPos (`a = atom p`): `tryAll ⟨.pos, .imp (.atom p) .bot, l⟩ = .linear [⟨.neg, .atom p, l⟩]` — `rfl` ✓
- negPos (`a = box φ`): `= .linear [⟨.neg, .box φ, l⟩]` — `rfl` ✓
- negPos (`a = imp a1 (.atom s)`, `a1` abstract): `= .linear [⟨.neg, .imp a1 (.atom s), l⟩]` — `rfl` ✓
- orPos (`a = imp a1 .bot`, `a1` abstract): `= .branching [[⟨.pos, a1, l⟩], [⟨.pos, .bot, l⟩]]` — `rfl` ✓
- andPos (`a = imp a1 (.imp a3 .bot)`, `a1,a3` abstract): `= .linear [⟨.pos, a1, l⟩, ⟨.pos, a3, l⟩]` — `rfl` ✓
- **stuck case** (`a = imp a1 a2`, `a2` abstract): `rfl` **fails** as predicted (proves `cases a2` is required, and that the leaves are bounded) ✓
- F-side mirrors: negNeg/orNeg/andNeg all `rfl` ✓
- **obtain shape**: replicating the `match (modalApplyOne …).fst … = some (newBs,newExps,newAcc)`
  shape, the *existing* simp set (`[modalApplyOne, tryAllPropRules, applyPropRule, modalAndOf?,
  modalOrOf?, modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
  Option.some.injEq, Prod.mk.injEq]`) collapses `hsf` and the **flat** `obtain ⟨hnewBs, _, hnewAcc⟩`
  succeeds (EXIT 0). No `SignedFormula.pos/neg` needed (avoids the `unusedSimpArgs` linter, which is
  an *error* in CSLib — cf. `:131,275,624` "This simp argument is unused").

**Key consequence**: each c = ⊥ leaf reduces with the *existing* simp set already in the file — no
new lemmas, no new simp args. The case depth is bounded at 3 (`cases a; cases a2; cases a4`).

### F5. Strategy decision

- **Strategy A (standalone `@[simp]` reduction lemmas)**: REJECTED as the primary mechanism. A
  single lemma for `tryAll ⟨.pos, .imp a .bot, l⟩` has no unconditional RHS (it depends on `a`'s
  head), so it cannot be a simp lemma; per-head-shape lemmas would just re-encode the case tree in a
  different file while adding API surface. Crucially, A *alone cannot fix the semantic error* — the
  arm still refines to negPos. It buys nothing over doing `cases a` inline, since the inline leaves
  already reduce by the existing simp set.
- **Strategy B (`cases a` restructuring)**: REQUIRED and RECOMMENDED. It is the only correctness-
  complete fix, it mirrors an existing in-file template (c ≠ ⊥ arm), and — verified in F4 — each leaf
  closes with the existing simp set + flat obtain, so it does **not** require inspecting the giant
  `hsf` during implementation.
- **Hybrid note**: the only "extraction" worth doing is *moving the per-leaf reduction knowledge into
  this report* (done in F4), so the implementer writes the leaves mechanically without ever calling
  `lean_goal` inside `modalStepBranch_preserves_sat`.

### F6. Tail items (separable; all in `hsf`-free theorems — normal tooling OK)

- **Duplicate `imp` alt (`:746`, error at `:747`)**: the `| imp φ bot2 =>` arm (`:746-786`) is
  **dead code** — F(◇φ) = `imp (box (imp φ ⊥)) ⊥` is an `imp a ⊥` already routed to negNeg in the
  `| imp a c =>` arm (the author's own comments at `:756-785` confirm this). **Fix: delete `:746-786`.**
  This is resolved *by* the negNeg restructuring (its `cases a` `| box _ =>` leaf covers a = box).
- **zip block (`:821-824`)**: `List.mem_zip` was removed from Mathlib (loogle: only
  `List.of_mem_zip` remains, `Init.Data.List.Zip`). Replacement: prove
  `(b, expandedSets.get ⟨i,_⟩) ∈ branches.zip expandedSets` via `List.getElem_zip`
  (`(l.zip l')[i] = (l[i], l'[i])`, `Init.Data.List.Nat.TakeDrop`) + `List.getElem_mem` /
  `List.mem_iff_getElem`. `List.mem_iff_get` at `:819` still exists (not flagged).
- **app-type-mismatch (`:858,872,917`) and `made no progress` (`:878,882,886`), `unsolved goals`
  (`:875`)**: in the `hnewlen` sub-proof and `ih_inner`/`ih` applications of
  `modalExpandBranches_closed_unsat` (`:862-919`). Mechanical; repair with `lean_goal` after the
  zip block is fixed (some cascade from the zip/length plumbing).
- **universe (`:959`, "Failed to infer universe levels of binder `hsat`")**: in `modalTableau_sound`
  application (`:953-962`); `kValid` uses monomorphic `∀ (World : Type)` (`:924`). Mechanical.

## Decisions

1. Adopt **Strategy B (cases-`a` restructuring)** for the c = ⊥ arms (negPos `:269`, negNeg `:619`).
2. **Reject standalone `@[simp]` reduction lemmas** (Strategy A) — unnecessary and cannot fix the
   semantic error.
3. Treat c ≠ ⊥ arms as **mechanical** (flat obtain only).
4. Treat all tail items as a **separate phase** using normal `lean_goal` tooling (they are outside
   `modalStepBranch_preserves_sat`).

## Recommendations (verified Lean idioms + phasing)

### Idiom for each new c = ⊥ leaf (after `cases a` / `cases a2` / `cases a4`)

Per leaf, head concrete → use the existing simp set, flat obtain, then the *correct* rule's refine:

```lean
simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
  Option.some.injEq, Prod.mk.injEq] at hsf
obtain ⟨hnewBs, _, hnewAcc⟩ := hsf   -- FLAT (not ⟨⟨_,_⟩,_⟩)
subst hnewBs hnewAcc
```

Case tree for the **negPos** arm (`a` is the antecedent of `a → ⊥`; F-side negNeg is the dual,
swapping pos↔neg and the same head→rule map):

```
cases a
| bot      => negPos  -- linear [F ⊥]
| atom p   => negPos  -- linear [F (atom p)]
| box φ    => negPos  -- linear [F (box φ)]
| imp a1 a2 =>
    cases a2
    | bot      => orPos   -- branching [[T a1],[T ⊥]]   (a = ¬a1)
    | atom s   => negPos  -- linear [F (imp a1 (atom s))]
    | box ψ    => negPos
    | imp a3 a4 =>
        cases a4
        | bot     => andPos  -- linear [T a1, T a3]      (a = a1 → (a3 → ⊥))
        | atom t  => negPos
        | box χ   => negPos
        | imp _ _ => negPos
```

The orPos/andPos leaves reuse the *existing* branching/linear semantic-discharge code already
written in the c ≠ ⊥ orPos leaf (`:307-327`) and adapted for the `T ⊥`/`T a3` members.

### Mechanical idiom for c ≠ ⊥ arms

Replace `obtain ⟨⟨hnewBs, _⟩, hnewAcc⟩ := hsf` → `obtain ⟨hnewBs, _, hnewAcc⟩ := hsf` at
`:302,334,361,648,704,728`. No other change.

### Phased implementation outline (overflow-safe by construction)

Each phase is one bounded agent run; **no phase requires `lean_goal` inside
`modalStepBranch_preserves_sat`** because all leaf shapes/obtain are pre-verified above.

- **Phase 1 — c ≠ ⊥ flat-obtain sweep (mechanical, ~6 edits).** Apply the obtain flatten at the six
  sites. Verify only with the bounded command
  `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1 | grep -c "error:"`. Expected: clears
  `:304,336,363,403,650,706,730` cascades. *Context stays small: edits are 1-line, no goal inspection.*
- **Phase 2 — negPos c = ⊥ restructuring (`:269-289`).** Replace the arm with the depth-3 case tree
  above; each leaf is copy-adapted from the verified idiom. Verify with the bounded error count only.
  *Never run `lean_goal` here; the leaf shapes are pre-proven in F4.*
- **Phase 3 — negNeg c = ⊥ restructuring (`:619-637`) + delete dead `:746-786`.** Dual case tree;
  deletion resolves the duplicate-`imp` error. Bounded error count only.
- **Phase 4 — tail (separate theorems, normal tooling).** Fix zip block via `List.getElem_zip`
  (`:821-824`), then `hnewlen`/`ih` mismatches (`:858-919`) and the universe binder (`:959`) using
  `lean_goal` freely (these theorems have no giant `hsf`). Full `lake build` at the end.

Phase ordering matters: Phase 1 first removes the largest cascade and confirms the flat-obtain
hypothesis on real code before the heavier Phases 2-3.

## Risks & Mitigations

- **Risk: a leaf `simp` leaves a residual** (e.g. `SignedFormula.neg` not unfolded). *Mitigation*:
  F4 showed the existing set suffices on the replicated shape with no residual; if a residual appears,
  add `SignedFormula.pos`/`neg` *only to that leaf* and immediately check for the `unusedSimpArgs`
  error (it is build-fatal in CSLib).
- **Risk: `cases a` explodes / non-terminating.** *Mitigation*: F4 proves the tree is bounded at
  depth 3 with abstract leaves (andPos rfl with abstract `a1,a3`; orPos rfl with abstract `a1`).
- **Risk: statement drift.** *Mitigation*: `modalStepBranch_preserves_sat`'s signature is untouched;
  only the proof body changes. Zero `sorry` maintained.
- **Risk: combined-alternative `cases c with | atom _ | imp _ _ | box _` keeps `c` referenceable** —
  the existing code already relies on this and builds structurally, so the new negNeg restructuring
  may reuse the same pattern.

## Adversarial Self-Verification (H4)

Challenged each load-bearing claim:

1. **"The `| bot =>` arm is wrong, not just unreduced."** *Challenge*: maybe negPos always fires
   first regardless of `a`? *Resolved*: rule order is andPos, orPos, …, negPos
   (`PropositionalRules.lean:153`); scratch proves orPos fires for `a = ¬q` and andPos for
   `a = q→(r→⊥)` (both `rfl`). So negPos is *not* first-applicable for those heads. Claim holds.
2. **"Reduction is `rfl` once head concrete."** *Challenge*: maybe it needs deeper `cases` than 3?
   *Resolved*: scratch case C (`a2` abstract) fails `rfl` (confirming `cases a2` needed), but cases A
   (`a1,a3` abstract) and B (`a1` abstract) succeed — so leaves stop at depth 3; no infinite descent
   because once `a4`'s head is a concrete non-`⊥` constructor, `andOf?`/`orOf?` reduce to `none`
   definitionally irrespective of deeper subterms.
3. **"Flat obtain is correct."** *Challenge*: maybe some arm yields a left-nested conjunction?
   *Resolved*: the shape derives uniformly from `Option.some.injEq` + 2×`Prod.mk.injEq` →
   right-assoc 3-conjunct; the scratch replica's flat obtain returned EXIT 0; and the committed Root-A
   fix (425c1c53) independently established the same flat shape for boxPos.
4. **"Strategy A adds nothing."** *Challenge*: could `@[simp]` lemmas collapse `hsf` *without*
   `cases a` (avoiding restructuring)? *Resolved*: no single unconditional simp lemma exists for
   `tryAll ⟨.pos, .imp a .bot, l⟩` (RHS depends on `a`); and even a conditioned lemma leaves the
   semantic refine wrong. So A cannot replace B.
5. **"Tail is safe with normal tooling."** *Challenge*: is `hsf` present in the tail theorems?
   *Resolved*: tail errors are in `modalExpandBranches_closed_unsat` (`:797-919`) and
   `modalTableau_sound` (`:936-962`), which contain no `tryAllPropRules`-derived hypothesis; their
   goals are ordinary list/length/universe obligations. Safe.
6. **BibKey traceability**: `Rules.lean:42-43` cites `[Fitting1983]` and `[Smullyan1968]`, but
   `references.bib` contains only `@book{Fitting1969,...}` and **no Smullyan entry**. This is a
   pre-existing citation/BibKey mismatch, *orthogonal* to this repair (the rules are grounded by the
   in-repo definitions, Tier 3). Flagged for separate cleanup; not blocking.

No fundamental flaw found; no `## Revised Direction` needed.

## Context Extension Recommendations

- **Topic**: Overflow-safe repair pattern for proofs with giant unreduced `match` hypotheses.
  **Gap**: no documented protocol for "verify reduction shape in a scratch `lake env lean` file, then
  edit the main proof blind." **Recommendation**: capture as a memory/pattern (see candidates).

## Appendix

- **Verified Mathlib lemmas (loogle)**: `List.of_mem_zip` (`Init.Data.List.Zip`),
  `List.getElem_zip` (`Init.Data.List.Nat.TakeDrop`). `List.mem_zip` does **not** exist (removed).
- **BibKey note**: `Fitting1969` present; `Fitting1983`/`Smullyan1968` cited in `Rules.lean` are not
  in `references.bib`.
- **Scratch method**: standalone `example`s compiled via `lake env lean scratch_364.lean` (imports
  `Cslib.Logics.Modal.Tableau.Rules`); deleted after verification per context discipline. No
  `lean_goal`/`lean_multi_attempt` was used anywhere inside `modalStepBranch_preserves_sat`.
- **Error-site index**: c=⊥ roots `269,275 / 619,624`; c≠⊥ flat-obtain `302,334,361,648,704,728`;
  duplicate-imp `746-786`; zip `821-824`; tail `858,872,875,878,882,886,917,959`.
