# Task 554 Continuation Handoff — After Phase 9

**Date**: 2026-07-26
**Session**: sess_1785046950_33beb4_554
**Plan**: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`

## State

Phase 9 (`NCK′` rules, the first phase of Stage C) is now COMPLETE. 9/32 phases done. Commit
`fce0ca3b` ("task 554 phase 9: NCK' rules") on `main`. Whole-project `lake build` / `lake test` /
`lake lint` / `lake exe checkInitImports` / `lake exe lint-style` / `lake exe mk_all --module` /
scoped `lake shake` all green at this commit. Invariants held: `Cslib/` sorry census (`bash
.claude/scripts/lean-sorry-census.sh Cslib/`) unchanged at 39, axiom count unchanged at 26
(`grep -rn "^axiom " Cslib/ | wc -l`), zero new axioms, zero new sorries.

## Commit This Session

- New file `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Rules.lean`.
- `Cslib.lean` updated (barrel import, via `lake exe mk_all --module`).
- Plan file: Phase 9 marked `[COMPLETED]` with inline task/verification annotations documenting
  two deviations (see below).
- New progress file `specs/554_.../progress/phase-9-progress.json`.

## What Landed (Phase 9: `NCK′` rules)

**`NestedProof : NestedFull Atom → Type u`**, an inductive proof-tree family indexed by
conclusion, with all 13 rules of Figure 2 (system `NCK`):

| Constructor | Rule | Context kind | Premises |
|---|---|---|---|
| `botL` | `⊥•` | `InputCtx` | 0 (axiom) |
| `id` | `id` | `InputCtx` (constructed inline: `Γ'`,`Λ`,`a`) | 0 (axiom) |
| `andL` | `∧•` | `InputCtx` | 1 |
| `andR` | `∧°` | `OutputCtx` | 2 |
| `orL` | `∨•` | `InputCtx` | 2 |
| `orRLeft`/`orRRight` | `∨°` (both injections) | `OutputCtx` | 1 each |
| `impL` | `⊃•` | `InputCtx` (1st premise via `ctx.outputPruning`) | 2 |
| `impR` | `⊃°` | `OutputCtx` (premise via `fillFull`) | 1 |
| `boxL` | `□•` | `InputCtx` | 1 |
| `boxR` | `□°` | `OutputCtx` | 1 |
| `diaL` | `♦•` | `InputCtx` | 1 |
| `diaR` | `◇°` | `OutputCtx` (conclusion via `fillFull`) | 1 |
| `contract` | `c` | `InputCtx` | 1 |

Plus `NestedProof.height` (structural recursion, `0` for the two axioms, `1 + max(premise
heights)` otherwise — universally quantifies the conclusion index `∀ {Γ}, ...` rather than fixing
it via `variable`, since every recursive call is at a genuinely different `NestedFull Atom`
index than the constructor's own conclusion; fixing `Γ` via `variable` first produces "expected
`NestedProof Γ`, got `NestedProof (different index)`" errors — hit and fixed this session).

## The Central Design Decision: Which Rules Need `InputCtx` vs `OutputCtx`

This was the phase's main interpretive work (Figure 2's rules do not literally spell out which
of Phase 7's four hole-filling operations each one uses). The governing principle, derived from
type-necessity (not stylistic choice):

- **LHS-typed hole content** (`id`, `⊥•`, `∧•`, `∨•`, `⊃•`'s 2nd premise+conclusion, `□•`, `♦•`,
  `c`) → `InputCtx.fillLhs`, since `OutputCtx.fillLhs` alone yields a bare `NestedLhs`, not a
  full sequent. This means every one of these rules' `Γ{ }` bakes in a companion output `ctx.π`,
  which explains for free why `⊥•`/`∨•`'s documented side condition ("the output formula must be
  in the same subtree as the principal formula") needs no separate Lean hypothesis:
  `InputCtx.fillLhs`'s own definition always places the hole and `ctx.π` as the two direct
  children of one shared `box`.
- **RHS-typed hole content** (`∧°`, `∨°`, `⊃°`'s premise, `□°`) → `OutputCtx.fillRhs`/`.fillFull`
  directly, no companion needed.
- **`⊃•`'s 1st premise, `◇°`'s conclusion** → need `OutputCtx.fillFull`/output-pruning
  specifically: `⊃•`'s first premise is `Γ⇓{A°}` (`ctx.outputPruning.fillRhs`); `◇°`'s conclusion
  `Γ{◇A°,[Δ]}` mixes an RHS leaf with an LHS bracket at the same level, which cannot be a single
  `NestedRhs` filler (no RHS comma constructor), so it needs the genuine full-sequent-pair form
  `ctx.fillFull (.dia Δ, ...)`.

**A structural consequence worth flagging for Phase 10+**: `InputCtx.fillLhs` can *never* produce
a flat, box-free `(A•, A°)` pair (confirmed by direct computation, documented in the module
docstring) — even at the maximally trivial `Γ' = Λ = []`, it forces exactly one `box` between the
hole and `ctx.π`. This matters for anything that wants to invoke the atomic `id` axiom "at the
very top" of a derivation (e.g. Proposition 3.1's induction, not attempted this phase — see
below).

## Plan Deviations (Both Documented Inline in the Plan File)

1. **The plan's task-list "`k`" item**: read as referring to the propositional rule family
   (`∧•`/`∧°`/`∨•`/`∨°`/`⊃•`/`⊃°`) already covered by the same bullet, not a distinct Figure-2
   rule — Figure 2 has no rule literally labelled `k` (that name is reserved, in this codebase,
   for the `K`-axiom of the Hilbert system `Constructive/CS5.lean`). All 13 actual Figure 2 rules
   are landed.
2. **"Land the smoke-test derivations the paper gives in §3"**: the source's own §3 text (grepped
   across the whole PDF for "Example") gives no concrete derivation trees between Figure 2 and
   Proposition 3.1 to transcribe. Proposition 3.1 itself ("the general `id`-rule is derivable...
   by a straightforward induction") is a genuine standalone induction over formula structure —
   its base case needs the atomic `id` axiom reachable from a flat `Γ{A•,A°}` at `ctx=[]`, which
   (per the structural fact above) `InputCtx.fillLhs` cannot produce, confirming this is a real
   induction, not a same-phase smoke test. Landed instead: bare `⊥•`/`id` axiom instances plus one
   genuine multi-rule derivation (`∨•` on two `⊥•` instances), documented in the module docstring
   as illustrative examples, not a literal source transcription.

## Literature Access This Session

Rendered PDF page 5 directly (Definition 2.3's exact statement, to resolve whether the
mandatory-box structural property above was a Phase 7 bug or a genuine feature of the source's
own definition — it is genuine, confirmed by the type-necessity argument in this handoff and the
module docstring) and page 6 directly (Figure 2, `NCK`) via the `Read` tool with `pages`.
Cross-checked both against `pdftotext -f 5 -l 9 -layout` of
`~/Projects/Literature/.sources-recovered/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics.pdf`.
Confirmed again this session: `pdftotext` silently drops the `□` glyph in this PDF's font
encoding (Figure 2's `□•`/`□°` rules render with the formula immediately following the missing
glyph, e.g. "`Γ{A•,[∆]}`" instead of "`Γ{□A•,[Δ]}`") — direct page rendering remains the
authoritative source for any `□`-bearing rule.

## Next Action

Resume at **Phase 10: `NCS5 = NCK′ + {t,4}#_G + {b}[]`**. Depends on Phase 9 (done). Same file,
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Rules.lean`. Needs the `t•`/`t°`/`4•`/`4°`
rules (Figure 3, page 7 — already rendered/cross-checked in the Phase 8 session and again this
session) and the `b[]` structural rule (Figure 4, page 8 — not yet rendered this session or last;
render before writing). The plan also asks for weakening/`.mono` transport and height bounds —
`NestedProof.height` (landed this phase) is what those height-non-increasing statements will be
about.

## Do Not Touch

`Cslib/Logics/Modal/Tableau/` — still owned by concurrent sessions this round (task 553; observed
modified again this session at `FrameSoundness.lean`, not touched). Stage only
`Cslib/Logics/Modal/Metalogic/Constructive/` and `Cslib/Logics/Modal/Metalogic/InterSystem/` plus
the task directory; never a repo-wide `git add`. This session also observed uncommitted changes
to `specs/553_.../`, `specs/.orchestrator-multi-state.json`, `specs/TODO.md`, `specs/state.json`
from concurrent sessions in the working tree at session start and throughout — none of these were
touched or staged by this session (staged and committed only the four files listed under "Commit
This Session" above).

## Scale Reminder

32 phases total. Stage C (Phases 9-10) is now 1/2 complete. Stages D-G (soundness,
completeness-with-cut, cut elimination, two-label bridge) not started. Each phase should still be
committed independently per the Commit-Per-Green-Substep Mandate.
