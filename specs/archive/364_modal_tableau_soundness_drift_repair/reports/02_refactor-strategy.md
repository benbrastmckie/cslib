# Task 364 — Refactor Strategy for `modalStepBranch_preserves_sat`

**Target:** `Cslib/Logics/Modal/Tableau/Soundness.lean` (948 lines)
**Theorem under repair:** `modalStepBranch_preserves_sat` — **lines 186–787** (~601 lines)
**Toolchain:** `leanprover/lean4:v4.31.0`
**Status:** Phase 1 complete (commit `c299dfdc`); ~68 remaining errors ALL inside this one theorem.
**Prior artifacts read:** `reports/01_drift-diagnosis.md`, source slices 55–787.

## Executive Summary

The catch-22 is real and the proposed refactor is **sound and recommended**. `modalStepBranch_preserves_sat`
is a single monolithic `by` block whose enormous per-goal context is an *artifact of one shared
prologue* (it destructures `hsat` and `hstep` into ~13 accumulating hypotheses before any case
work begins), not an intrinsic property of any individual rule case. Extracting each rule case
into an independently-stated `private lemma` that takes **only the hypotheses that case needs**
bounds every sub-lemma's `lean_goal` context to a small, inspectable size. The proof uses
`cases` (not `induction`) and has **no cross-case `let`/`have` bindings**, so extraction is clean
at case granularity.

**Critical correction to the framing:** the task and `01_drift-diagnosis.md` describe "5 parallel
rule-cases." That is the **positive-sign branch only**. The theorem has a **symmetric negative-sign
branch** with 5 more non-trivial cases. There are **10 Family-3 `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩ := hsf`
sites** (verified by grep: lines 230, 276, 303, 335, 362 [pos] and 402, 625, 649, 705, 729 [neg]).
The refactor must therefore extract **10 sub-lemmas**, not 5. The diagnosis's Family-3 site list
(229/275/302/334/361) under-counted by omitting the entire neg branch.

## 1. Actual Structure of `modalStepBranch_preserves_sat`

**Statement (lines 186–196), MUST be preserved verbatim — it is depended on downstream**
(`modalExpandBranches_closed_unsat` and `modalTableau_sound`, used at line 941):

```lean
theorem modalStepBranch_preserves_sat
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))   -- (split into two binders in source)
    (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiable b acc)
    (hInv : accFreshInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiable b' newAcc
```

**Shared prologue (lines 197–207)** — the source of context bloat:
```lean
obtain ⟨W, m, f, hacc, hb⟩ := hsat        -- 5 names
simp only [modalStepBranch] at hstep
obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
split_ifs at hsf with hexp                 -- hexp NEVER used in any case body (verified)
obtain ⟨sign, formula, lbl⟩ := sf
have hsf_b := hb ⟨sign, formula, lbl⟩ hsfmem
cases sign with ...
```

**Full case map** (`cases sign` → `cases formula` → nested `cases c/a/a2`):

| # | Sign | Formula shape | Rule | Lines | Kind |
|---|------|---------------|------|-------|------|
| — | pos  | `.atom p` | none (T(atom): no rule) | 213–216 | trivial / contradiction |
| — | pos  | `.bot` | none (T(⊥) false) | 217–219 | trivial / contradiction |
| **P1** | pos | `.box φ` | **boxPos** | 220–266 | non-trivial (~47 lines) |
| **P2** | pos | `.imp a .bot` | **negPos** | 270–290 | non-trivial |
| **P3** | pos | `.imp (.imp a1 .bot) c`, c≠⊥ | **orPos** | 297–328 | non-trivial |
| **P4** | pos | `.imp (.imp a1 a2) c`, a2≠⊥, c≠⊥ | **impPos** | 329–356 | non-trivial |
| **P5** | pos | `.imp a c`, a∈{atom,bot,box}, c≠⊥ | **impPos (general)** | 357–383 | non-trivial |
| — | neg  | `.atom p` | none | 389–391 | trivial / contradiction |
| — | neg  | `.bot` | none | 392–395 | trivial / contradiction |
| **N1** | neg | `.box φ` | **boxNeg** (fresh world) | 396–616 | non-trivial (**~220 lines — by far the largest**) |
| **N2** | neg | `.imp a .bot` | **negNeg** | 620–638 | non-trivial |
| **N3** | neg | `.imp (.imp a1 .bot) c`, c≠⊥ | **orNeg** | 644–699 | non-trivial |
| **N4** | neg | `.imp (.imp a1 a2) c`, a2≠⊥, c≠⊥ | **impNeg** | 700–723 | non-trivial |
| **N5** | neg | `.imp a c`, a∈{atom,bot,box}, c≠⊥ | **impNeg (general)** | 724–746 | non-trivial |
| — | neg  | `.imp φ bot2` (degenerate 2nd `imp` arm) | dead | 747–787 | trivial (`simp at bot2`) |

Note on N6/747: the neg-branch `cases formula` has a *second* `| imp φ bot2 =>` arm at 6-space
indent (a pre-existing structural oddity in the source; the file currently does not compile so
this cannot be re-verified, but it predates the bump). It is closed by `simp at bot2` and the
source comments (747–787) explain it is an already-handled diamond-negation shape. **Keep it
inline in the skeleton** — do not extract.

**Hypothesis usage (verified by grep):**
- `hexp` (from `split_ifs`): used by **zero** cases → sub-lemmas do not need it.
- `hInv` (freshness): used by **N1 boxNeg only** (lines 458, 465) → only the boxNeg sub-lemma takes `hInv`.
- `W, m, f, hacc, hb`: needed by every non-trivial case (they supply the reused Kripke model).
- `hsfmem`: needed by boxPos/boxNeg (membership-driven propagation) and the freshness probes.

## 2. Proposed Sub-Lemmas (one per non-trivial case)

All are `private lemma` in `namespace Cslib.Logic.Modal.Tableau` under the existing
`variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]` (line 54). Names follow the file's
existing snake_case-with-suffix convention (`modalClosed_unsat`, `accFreshInv_empty`), which is
mathlib-idiomatic for theorems/lemmas and not flagged by the `defsWithUnderscore` linter (that
linter targets `def`s, not `lemma`s).

**Common signature template** (each non-trivial case discharges the same goal
`∃ b' ∈ newBs, branchSatisfiable b' newAcc`, reusing the inbound model `m, f`):

```lean
private lemma modalStepBranch_preserves_sat_<RULE>
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    <formula-component binders: e.g. (φ lbl) / (a c lbl) / (a1 a2 c lbl)>
    {W : Type*} (m : Model W Atom) (f : WorldIndex → W)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula))
    (hsfmem : (⟨<sign>, <formula>, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (h<pos|neg> : <Satisfies | ¬Satisfies> m (f lbl) <formula>)
    (hsf : <the post-`cases formula` residue eqn> = some (newBs, newExps, newAcc)) :
    ∃ b' ∈ newBs, branchSatisfiable b' newAcc := by
  -- body = verbatim transcription of the case (lines from table), starting with
  --        `simp only [modalApplyOne] at hsf`
```

The exact type of `hsf` and the precise component binders for each case must be **copied from a
single `lean_goal` probe at that case's dispatch site in the skeleton** (see §3). Because the
skeleton goal is tiny, that probe will NOT overflow — this is the whole point of doing Phase 0
first. The 10 sub-lemmas:

| Sub-lemma name | Case | Extra binders | Needs `hInv`? | Drift fix-families |
|----------------|------|---------------|---------------|--------------------|
| `…_boxPos`     | P1 | `(φ lbl)` | no | F3 (line 229/230 obtain), F2 (Satisfies unfold 262), F4 (beq 244) |
| `…_negPos`     | P2 | `(a lbl)` | no | F3 (276), F2 (288) |
| `…_orPos`      | P3 | `(a1 c lbl)` | no | F3 (303), F2 (307) |
| `…_impPos`     | P4 | `(a1 a2 c lbl)` | no | F3 (335), F2 (337) |
| `…_impPosGen`  | P5 | `(a c lbl)` | no | F3 (362), F2 (364) |
| `…_boxNeg`     | N1 | `(φ lbl)` | **YES** | F3 (402), F2 (407), F4 (441/499/506/534/560), F1 (509–512, 553–557) |
| `…_negNeg`     | N2 | `(a lbl)` | no | F3 (625), F2 (635) |
| `…_orNeg`      | N3 | `(a1 c lbl)` | no | F3 (649), F2 (680/693) |
| `…_impNeg`     | N4 | `(a1 a2 c lbl)` | no | F3 (705), F2 (715/721) |
| `…_impNegGen`  | N5 | `(a c lbl)` | no | F3 (729), F2 (738/744) |

`boxNeg` (N1) carries **all four fix-families** and is ~5× the size of any other case — it is the
true bottleneck (see §5).

## 3. Rewritten Main-Theorem Skeleton (preserves the public statement)

The signature (186–196) is **unchanged**. The body collapses to the prologue plus per-case
`exact` dispatch. Trivial contradiction arms stay inline; the degenerate `imp φ bot2` arm stays
inline.

```lean
theorem modalStepBranch_preserves_sat
    (b e : …) (acc : Accessibility) (newBs newExps : …) (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiable b acc) (hInv : accFreshInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiable b' newAcc := by
  obtain ⟨W, m, f, hacc, hb⟩ := hsat
  simp only [modalStepBranch] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  obtain ⟨sign, formula, lbl⟩ := sf
  have hsf_b := hb ⟨sign, formula, lbl⟩ hsfmem
  cases sign with
  | pos =>
    have hpos : Satisfies m (f lbl) formula := hsf_b.1 rfl
    cases formula with
    | atom p => exact absurd hsf (by simp [modalApplyOne, …])      -- inline (213–216)
    | bot    => simp only [modalApplyOne, Satisfies] at hpos        -- inline (217–219)
    | box φ  => exact modalStepBranch_preserves_sat_boxPos    b acc newBs newExps newAcc φ lbl m f hacc hb hsfmem hpos hsf
    | imp a c =>
      cases c with
      | bot => exact modalStepBranch_preserves_sat_negPos     b acc newBs newExps newAcc a lbl m f hacc hb hsfmem hpos hsf
      | atom _ | imp _ _ | box _ =>
        cases a with
        | imp a1 a2 =>
          cases a2 with
          | bot => exact modalStepBranch_preserves_sat_orPos  b acc newBs newExps newAcc a1 c lbl m f hacc hb hsfmem hpos hsf
          | atom _ | imp _ _ | box _ =>
                   exact modalStepBranch_preserves_sat_impPos b acc newBs newExps newAcc a1 a2 c lbl m f hacc hb hsfmem hpos hsf
        | atom _ | bot | box _ =>
                   exact modalStepBranch_preserves_sat_impPosGen b acc newBs newExps newAcc a c lbl m f hacc hb hsfmem hpos hsf
  | neg =>
    have hneg : ¬Satisfies m (f lbl) formula := hsf_b.2 rfl
    cases formula with
    | atom p => exact absurd hsf (by simp [modalApplyOne, …])       -- inline (389–391)
    | bot    => exact absurd hsf (by simp [modalApplyOne, …])       -- inline (392–395)
    | box φ  => exact modalStepBranch_preserves_sat_boxNeg   b acc newBs newExps newAcc φ lbl m f hacc hb hsfmem hneg hInv hsf
    | imp a c =>
      cases c with
      | bot => exact modalStepBranch_preserves_sat_negNeg    b acc newBs newExps newAcc a lbl m f hacc hb hsfmem hneg hsf
      | atom _ | imp _ _ | box _ =>
        cases a with
        | imp a1 a2 =>
          cases a2 with
          | bot => exact modalStepBranch_preserves_sat_orNeg b acc newBs newExps newAcc a1 c lbl m f hacc hb hsfmem hneg hsf
          | atom _ | imp _ _ | box _ =>
                   exact modalStepBranch_preserves_sat_impNeg b acc newBs newExps newAcc a1 a2 c lbl m f hacc hb hsfmem hneg hsf
        | atom _ | bot | box _ =>
                   exact modalStepBranch_preserves_sat_impNegGen b acc newBs newExps newAcc a c lbl m f hacc hb hsfmem hneg hsf
    | imp φ bot2 => simp at bot2                                     -- inline (747–787), degenerate
```

**Important implementation detail on `hsf`:** in the current source the
`simp only [modalApplyOne] at hsf` happens *inside* each case (lines 211 pos / 387 neg). In the
refactor, move that `simp only [modalApplyOne] at hsf` to be the **first line of each sub-lemma**,
so the main theorem passes `hsf` in its raw post-`cases formula` form. The exact raw type of `hsf`
per case is read off a `lean_goal` probe at the corresponding `exact` (the skeleton goal is small,
so this is safe). If unification on `hsf` is fussy, the fallback is to keep `simp only [modalApplyOne]`
in the skeleton and declare each sub-lemma's `hsf` parameter as the *unfolded* equation instead —
either boundary works; pick one and apply uniformly.

The two trivial `pos` arms use `hpos`/`hsf` contradictions exactly as in 213–219; transcribe the
existing two-liners.

## 4. Reuse Check (Foundations-first / Phase-1 infrastructure)

Confirmed reusable — **no new abstractions needed**:

- **`Proposition.beqToEq`** (`private def`, Soundness.lean:78, added in Phase 1 / commit `c299dfdc`):
  converts `(a == b) = true → a = b` for `Proposition Atom` by structural induction. **This is the
  canonical Family-4 fix.** Every `LawfulBEq.eq_of_beq`/`beq_iff_eq` site inside the sub-lemmas
  (notably boxNeg: 441, 499, 506, 534, 560–561; boxPos: 244) should route through
  `Proposition.beqToEq` rather than synthesizing `LawfulBEq (Proposition Atom)` (which no longer
  resolves). Because sub-lemmas live in the same file/namespace, the `private` def is in scope.
- **`branchSatisfiable`** (63) and **`accFreshInv`** (164): reused directly in sub-lemma goals/binders.
- **`accFreshInv_empty`** (171): unchanged; used by the downstream caller, not the sub-lemmas.
- **`modalNextWorld_gt`** (`Cslib/Logics/Modal/Tableau/Branch.lean:104`): the freshness lemma the
  boxNeg sub-lemma needs (used at 446, 523, 579, 606). Reused as-is.
- **Phase-1 proven idioms** (from the committed `modalClosed_unsat` repair) are the transcription
  templates for the sub-lemmas:
  - Family-1 sign idiom: `cases h : sf.sign with | pos => rfl | neg => simp [h, Sign.isPos] at hpos`
    (modalClosed_unsat:119–121) — apply at boxNeg 509–512 and 553–557.
  - Family-4 idiom: `Proposition.beqToEq _ _ hbeq` (modalClosed_unsat:123, 148).

**Optional shared helper** (nice-to-have, not required): a one-line
`Sign.eq_neg_of_not_isPos`/`Sign.eq_pos_of_isPos` to deduplicate the Family-1 sign-contradiction
idiom that recurs in boxNeg. Only worth adding if the inline idiom proves noisy; default is to
inline it.

## 5. Risk / Feasibility Assessment

**Does extraction actually shrink the per-goal context? — YES, for 9 of 10 cases.**
The bloat is caused by the shared prologue accumulating `W, m, f, hacc, hb, sf, hsfmem, hsf, hexp,
sign, formula, lbl, hsf_b` *plus* each case's `simp … at hsf` residue, all coexisting in one
state. A sub-lemma declares only the ~10 binders it needs; `hexp`, `hsf_b`, and the unused
constructor variables vanish. For the small cases (negPos, orPos, impPos, impPosGen, negNeg,
orNeg, impNeg, impNegGen, boxPos) the post-`simp` goal is then small enough for `lean_goal` —
the Family-3 fix becomes inspectable.

**Clean-extraction risks — LOW:**
- **No common induction.** The proof is pure `cases`; each case is logically independent.
- **No cross-case `let`/`have`.** boxNeg's `let w'/f'/newAcc'/witness/boxProps/diaNegProps`
  (411–432) are entirely local to boxNeg; they do not leak across case boundaries. Extraction at
  case granularity contains them.
- **Signature drift risk on `hsf`:** the only real friction (see §3). Mitigated by the
  "probe-the-skeleton-goal" recipe and the unfolded-vs-raw fallback.

**The one genuine hard spot — N1 `boxNeg` (396–616, ~220 lines):**
Extracting boxNeg bounds its *entry* context, but boxNeg internally re-accumulates a large state
(`ww, hwwr, hwwφ, f', boxProps, diaNegProps`, then deeply nested `obtain`/`split_ifs` chains at
486–602, including the gnarly classical blob at 586–596). `lean_goal` *deep inside* boxNeg may
still be sizeable. **Recommended mitigation:** give boxNeg its own phase and, within it, further
decompose its two membership obligations into helper sub-lemmas before drift-repair:
- `…_boxNeg_boxProps_sat` — discharges the `sf' ∈ boxProps` branch (482–530), and
- `…_boxNeg_diaNegProps_sat` — discharges the `sf' ∈ diaNegProps` branch (531–602).

Each helper takes the fresh-world data (`w' = modalNextWorld b`, `f'`, `ww`, `hwwr`, the relevant
membership) as explicit binders, so its goal is small. Alternatively, scope them with internal
`suffices`/`have`-blocks if standalone helpers prove awkward to state. Flag boxNeg as the case most
likely to need a second decomposition pass; size its phase generously.

## 6. Recommended Phase Breakdown for the Follow-Up Plan

Each phase is sized to one bounded agent run, build-driven (`lake build
Cslib.Logics.Modal.Tableau.Soundness`), with the **no-`lean_diagnostic_messages`** discipline and
sparing `lean_goal` use.

- **Phase 0 — Pure structural refactor (no drift-repair).** Extract all 10 rule cases into
  `private lemma … := by sorry` stubs with the §2 signatures; rewrite the main theorem to the §3
  skeleton; keep the two trivial pos arms, two trivial neg arms, and the degenerate `imp φ bot2`
  arm inline (these are short — repair them here too, since they're 2–4 lines and don't overflow).
  **Goal: the file builds with exactly 10 `sorry`s and the main theorem's signature byte-for-byte
  unchanged.** Verify the skeleton dispatch type-checks (each `exact` unifies) — this is where the
  `hsf` boundary is locked in. Commit: `task 364 phase 0: extract modalStepBranch_preserves_sat sub-lemmas (stubbed)`.
- **Phase 1 — boxPos** (`…_boxPos`, F2/F3/F4). Replace its sorry; build; commit.
- **Phase 2 — negPos.** **Phase 3 — orPos.** **Phase 4 — impPos.** **Phase 5 — impPosGen.**
  (Pos-branch cluster; each is small, F2/F3 only. Can be 1–2 cases per agent run.)
- **Phase 6 — negNeg.** **Phase 7 — orNeg.** **Phase 8 — impNeg.** **Phase 9 — impNegGen.**
  (Neg-branch propositional cluster; mirror of phases 2–5.)
- **Phase 10 — boxNeg** (`…_boxNeg`, all four families; **dedicate a full agent run**, and first
  apply the §5 sub-decomposition into `_boxProps_sat` / `_diaNegProps_sat` helpers if `lean_goal`
  overflows mid-case).
- **Phase 11 — Zero-debt verification.** `lake build` clean; `lean_verify
  Cslib.Logic.Modal.Tableau.modalStepBranch_preserves_sat` (or `#print axioms`) shows zero `sorry`
  / zero new axioms; `lake exe lint-style`; `lake exe checkInitImports`. Commit:
  `task 364: complete implementation`.

Phases 1–9 are independent (any order); Phase 10 is the long pole; Phases 1–10 all depend on
Phase 0. A `--team` implementation could parallelize the propositional clusters (phases 1–9) with
**territory contracts per sub-lemma** (each agent owns exactly one `private lemma` body — no file
conflicts since the stubs are disjoint line ranges).

### Zero-Debt Tension — FLAGGED EXPLICITLY

Phase 0 deliberately introduces **10 `sorry` stubs as an intermediate scaffold**. This is the only
way to land the structure *before* drift-repair and thereby break the context-overflow catch-22.
This is acceptable **only** under the strict invariant that the **final state is zero-sorry**:

- The task **must not** be marked `[COMPLETED]`/`[PR READY]` while any sorry remains; Phase 11's
  `lean_verify`/`#print axioms` gate is mandatory and blocking.
- If any per-case phase cannot reach a sorry-free proof, mark **that phase** `[BLOCKED]` with the
  goal state and what's needed — do **not** leave the sorry and move on, and do **not** introduce
  an axiom to bridge it.
- The Phase-0 commit is a green-but-scaffolded checkpoint; every subsequent phase strictly reduces
  the sorry count, never increases it. Recommend tracking a `sorry_inventory` (count + which
  sub-lemmas) in each phase's handoff.

This is faithful drift repair, not redesign: no theorem statement changes, no semantics change —
only the *internal* proof is re-partitioned into named lemmas.

## Appendix — Key Source Coordinates

- Statement: 186–196 · Prologue: 197–207 · Pos branch: 208–383 · Neg branch: 384–787
- Section context: `namespace Cslib.Logic.Modal.Tableau` (50), `open Cslib.Logic.Tableau
  Cslib.Logic.Modal` (52), `variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]` (54),
  `end` (946/948).
- Reuse: `branchSatisfiable` (63), `Proposition.beqToEq` (78), `modalClosed_unsat` (100),
  `accFreshInv` (164), `accFreshInv_empty` (171); `modalNextWorld_gt` (Branch.lean:104);
  `modalApplyOne` (Rules.lean:68); `Model` (Basic.lean:63).
- Family-3 `obtain hnewBs` sites: pos 230/276/303/335/362 · neg 402/625/649/705/729.
- Downstream dependents (signature is load-bearing): `modalExpandBranches_closed_unsat` (798),
  `modalTableau_sound` (917), call site 941.
