# Continuation Handoff: Plan 08, Wave 9 (Phases 7.5-7.7), Partial

- **Plan**: `plans/08_reformulated-s4-redirect-sound-inv.md` (v7)
- **Date**: 2026-08-05
- **Dispatch scope**: wave 9 (Phases 7.5, 7.6, 7.7), per delegation instructions
- **Outcome**: Phase 7.5 COMPLETE. Phase 7.6 IN PROGRESS (P3 done, arm assembly designed but not
  written). Phase 7.7 NOT STARTED.

## What landed this dispatch (5 commits, all sorry-free, axioms exactly `{propext,
Classical.choice, Quot.sound}`, sorry census held at exactly 1 throughout)

1. **Phase 7.5 — COMPLETE.** `outDeg_ne_zero_of_hasEdge` (bridging fact),
   `tryAllPropRules_output_label_eq` (new supporting lemma), and
   `S4RedirectSoundInv_notBoxDia_step` (the propositional/non-mint arm), stated existentially
   over the produced `nf` to cover `.linear`/`.branching`/`.persistent` uniformly (the plan's own
   prose only named `nf` without settling whether propositional rules ever branch — they do:
   `andNeg`/`orPos`/`impPos`).

2. **Phase 7.6.1 — P3 proven.** `modalApplyOneS4Rules_{boxPos,diaNeg}_layers_eq_nil_of_saturated`:
   under `modalS4Saturated`, each of the K/T/4-rule per-layer candidate lists is individually
   empty. **This is a real, load-bearing finding, not a formality** — contrary to report 06 §6's
   "expected free" framing, a same-world persistent formula genuinely picks up a new 4-rule/K-rule
   candidate once the fresh mint successor is recorded, and only the mint payload's own
   `boxProps`/`boxPlusExtraS4` construction compensates for it.

3. **Phase 7.6.2 — acc-independence helpers.** `boxPropagation_addEdge_of_ne`,
   `modalFourBoxProp_addEdge_of_ne`, `modalFourDiaNegProp_addEdge_of_ne`,
   `modalApplyOneS4Rules_{boxPos,diaNeg}_fst_addEdge_of_ne`: at any world OTHER than the redirect
   source, `addEdge` leaves box-positive/diamond-negative applicability unchanged. This is the
   "other-world" half of conjunct (d)'s discharge for the mint arms; combined with Phase 7.4's
   branch-growth lemma it closes that half completely.

## What is NOT done, explicitly

**Phase 7.6's two mint-unblocked arm theorems** (`S4RedirectSoundInv_boxNeg_mint`,
`S4RedirectSoundInv_diaPos_mint`) are **not yet written**. The full design is worked out and
recorded in the plan file's `#### Phase 7.6 Progress Record` subsection (six numbered items) —
read that section first, it is the authoritative continuation brief, not a repeat of it here.
In summary, six pieces remain:

1. Conjunct (d)'s same-world sub-case (the actual P3-consuming assembly) — design complete,
   not written.
2. Conjunct (d)'s "everything else" (propositional/atomic) sub-case — cheap, mirrors Phase 7.5.
3. `outDeg (acc.addEdge w w') w' = 0` — a standalone freshness fact, design complete.
4. Conjunct (b)'s weakened edge clause — CANNOT reuse `modalApplyOneS4Keyed_boxNeg_mint_sat`
   as a black box (its `hacc` is unconditional); needs a re-derivation of the SAME construction
   with one case split inserted at the `hacc u v hedge` call site.
5. Conjuncts (a) and (c) — straightforward, same shape as Phase 7.5.
6. The diamond-positive mint arm — direct dual of box-negative, once that one lands.

**Phase 7.7 (4-rule arms with the ghost-edge disjunction) is entirely untouched.**

## Why this dispatch stopped here

The remaining Phase 7.6 assembly, plus its diamond-positive mirror, plus all of Phase 7.7, was
judged to exceed what could be completed soundly in the turns remaining this dispatch. Per this
task's standing discipline — never commit a `sorry`, stop at a clean boundary rather than rush —
this is an honest partial rather than a rushed or unsound landing. Every commit this dispatch made
is independently green (scoped build, `checkInitImports`, `lint-style`, sorry census all clean at
each commit).

## Next continuation step

Read the plan file's `#### Phase 7.6 Progress Record` subsection in full, then:

1. Write `S4RedirectSoundInv_boxNeg_mint` following the six-item design there. Start with item 3
   (the `outDeg` fact, self-contained) and item 4 (the weakened conjunct-(b) re-derivation,
   copying `modalApplyOneS4Keyed_boxNeg_mint_sat`'s proof body and changing only the edge-clause
   step), since those are the least novel. Then item 1 (the P3-consuming same-world case) and
   item 2 (the cheap other-case), assembling conjunct (d). Then items 5 (a)/(c), straightforward.
2. Write `S4RedirectSoundInv_diaPos_mint` as the dual (item 6).
3. Close Phase 7.6, update its plan marker to `[COMPLETED]`, record axioms/build/census.
4. Dispatch Phase 7.7 (4-rule arms), independently dispatchable per the plan (`Depends on: 7.4`,
   not on 7.6), if time remains in that continuation.
5. Phase 7.8 (the dispatcher) remains blocked until ALL of 7.5, 7.6, 7.7 close.

## Verification performed this dispatch

- Scoped `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green after every commit.
- `#print axioms` via `lake env lean` (not `lean_verify`) on every new declaration.
- `lake exe lint-style` and `lake exe checkInitImports` clean throughout.
- Sorry census (`grep -rn '^\s*sorry\s*$\|[^a-zA-Z_]sorry\s*$'`) exactly 1 at every checkpoint.
- `git diff --stat` confirmed file-scope compliance (only `FrameCompleteness.lean` touched, plus
  the plan file for markers); `git diff | grep '^-[^-]'` confirmed purely additive changes to the
  Lean file at every commit.
- One cosmetic note: `tryAllPropRules_output_label_eq`'s proof triggers the Lean core
  `linter.flexible` info/warning (a `simp_all`-then-`rcases` sequence on the same goal) — not an
  error, not one of the seven `lake lint` prevention categories this task tracks, does not block
  the build. Left as-is.
