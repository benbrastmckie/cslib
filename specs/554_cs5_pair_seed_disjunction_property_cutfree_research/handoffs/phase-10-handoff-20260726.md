# Task 554 Continuation Handoff — After Phase 10

**Date**: 2026-07-26
**Session**: sess_1785046950_33beb4_554
**Plan**: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`

## State

Phase 10 (`NCS5 = NCK′ + {t,4}#_G + {b}[]`, closing Stage C) is now COMPLETE. 10/32 phases done.
Whole-project `lake build` / `lake test` / `lake lint` / `lake exe checkInitImports` / `lake exe
lint-style` / `lake exe mk_all --module` / scoped `lake shake` all green. `Cslib/` sorry census
unchanged at 39, axiom count unchanged at 26, zero new axioms, zero new sorries.

## What Landed (Phase 10: `NCS5`)

Five additional `NestedProof` constructors on the **same** inductive from Phase 9 (not a new
indexed type), in `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Rules.lean`:

| Constructor | Rule | Context kind | Source |
|---|---|---|---|
| `tR` | `t°`: `Γ{A°} / Γ{◇A°}` | `OutputCtx.fillRhs` (no bracket) | Figure 3, page 7 |
| `tL` | `t•`: `Γ{A•} / Γ{□A•}` | `InputCtx.fillLhs` (no bracket) | Figure 3, page 7 |
| `fourR` | `4°`: `Γ{[◇A°,Δ]} / Γ{◇A°,[Δ]}` | `OutputCtx.fillRhs`/`.fillFull` | Figure 3, page 7 |
| `fourL` | `4•`: `Γ{[□A•,Δ]} / Γ{□A•,[Δ]}` | `InputCtx.fillLhs` | Figure 3, page 7 |
| `bStruct` | `b^[]`: `Γ{[[σ],Δ]} / Γ{σ,[Δ]}` | `InputCtx.fillLhs`, `σ,Δ : NestedLhs` | Figure 4, page 8 |

Plus `NestedProof.height` extended with the five new cases (all `p.height + 1`, single-premise),
and `NestedProof.mono` (index-equality transport, `Eq`-cast) with `NestedProof.mono_height`
(height-non-increasing, in fact preserving).

## Key Design Decisions Binding Successors

1. **Which of `X, Y ⊆ {d,t,b,4,5}` this instance needs**: `CS5`'s safe pair is `X = {t,4}`,
   `Y = {b}` -- verified against **Theorem 5.2's exact statement** (page 14, not just the plan's
   paraphrase): `X ⊆ {d,t,4}`, `Y ⊆ {d,b,5}` are *disjoint* domains (`t`/`4` only in `X`, `b`/`5`
   only in `Y`), with side conditions "if `t∈X` and `5∈Y` then `b∈Y`" (vacuous here, `5∉Y`) and
   "if `b∈Y` then `4∈X`" (holds: both present). Only these five constructors are landed; `d^[]`,
   `t^[]`, `4^[]`, `5^[]` (Figure 4) and the naive `b°`/`b•` (eq. (3.2)/(3.3)) are out of scope.
2. **`4°`/`4•` are genuinely distinct from `NCK`'s own `◇°`/`□•`** (Phase 9), not duplicates:
   Figure 2's `◇°`/`□•` build the modal formula fresh from a bare leaf; Figure 3's `4°`/`4•`
   reposition an *already-formed* `◇A°`/`□A•` out of a shared box. Confirmed by direct comparison
   of both figures' premises (re-rendered page 6 this session to check).
3. **`b^[]`'s `σ`, `Δ` are generic `NestedLhs`, not `Proposition`**: Figure 4 is genuinely
   structural (no polarity marker on `Σ`/`Δ` in the source), unlike Figure 2/3's formula-building
   rules. Spelled lowercase `σ` (not capital `Σ`): Mathlib binds capital `Σ` as sigma-type binder
   notation, unusable as a plain identifier here -- same class of clash as `Π`/`π` documented in
   `Context.lean`'s docstring (Phase 7).
4. **`.mono` is the index-equality transport precursor, not full weakening admissibility**: the
   plan's own Phase 19 explicitly says its first task is to "extend Phase 10's `.mono` to the
   height-preserving statement," and the source itself proves the real content-weakening rule
   (Figure `(3.1)`'s `w`) admissible only much later (alongside `nec`/`cut`). Landing the full
   18-constructor admissibility induction now would have been premature and outside this phase's
   2.5-hour budget -- that is Phase 19's dedicated `Admissibility.lean` (3-hour budget). This
   interpretive choice is documented as an inline plan annotation (Phase 10's own task-list item),
   not silently substituted.

## What NOT to Try

- Do not add `t^[]`, `4^[]`, `d^[]`, or `5^[]` (Figure 4) to `NCS5` -- Theorem 5.2 confirms `t`/`4`
  belong only to `X` (Figure 3 form), never `Y` (Figure 4 structural form), for this safe pair.
- Do not attempt Figure `(3.1)`'s full weakening/contraction/cut admissibility here or assume
  `NestedProof.mono` already provides it -- that is Phase 19's job, over all 18 constructors.
- Do not revisit Proposition 3.1 (flagged by Phase 9, still not attempted) -- out of scope for
  both Phase 9 and Phase 10.

## Literature Access This Session

Rendered PDF pages 7 (Figure 3), 8 (Figure 4), and 14 (Theorem 5.1/5.2) directly via `Read` with
`pages`; re-rendered page 6 (Figure 2) to cross-check `4°`/`4•` against `◇°`/`□•`. Consistent with
Phase 9's finding, `pdftotext` is unreliable for `□`/`◇`-bearing rule figures in this PDF's font
encoding -- direct page render remains authoritative.

## Next Action

Resume at **Stage D, Phase 11: Soundness auxiliary lemmas** (Theorem 4.1's Lemma 4.2-4.9 family,
Hilbert-derivability facts about contexts). Depends on Phases 8 (done) and 10 (done, this phase).
New file per the plan: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` (check
the plan's Phase 11 section for the exact filename/task list before starting).

## Do Not Touch

`Cslib/Logics/Modal/Tableau/` -- still owned by concurrent sessions (task 553). Stage only
`Cslib/Logics/Modal/Metalogic/Constructive/` and `Cslib/Logics/Modal/Metalogic/InterSystem/` plus
the task directory; never a repo-wide `git add`.

## Scale Reminder

32 phases total. Stage C (Phases 9-10) is now COMPLETE. Stage D (Phases 11-13, soundness) is
next. Each phase should still be committed independently per the Commit-Per-Green-Substep
Mandate.
