# Probe Verdict: P1/P2 for the Reformulated Mint-Blocked Redirect Arm

- **Task**: 553 (`s4_loop_guard_soundness_reachability_restriction`)
- **Dispatch type**: P1+P2 probe (per `reports/06_mint-blocked-redirect-verdict.md` §6), NOT a
  full Phase 7 implementation
- **Date**: 2026-08-05
- **Session**: sess_1785958880_8ab261

## Overall recommendation

**PROCEED WITH THE REFORMULATED PHASE 7** (report §3's `S4RedirectSoundInv` architecture).

Both P1 and P2 pass. P1 was not merely probed but **fully proven** for the box-negative-blocked
case: a machine-checked, sorry-free, standard-axioms-only Lean theorem now exists in
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`. P2 (the kill criterion) does not trigger
anywhere in `FrameRules.lean`/`Rules.lean`.

## P1 — PASS (stronger than requested: fully proven, not just probed)

`S4RedirectSoundInv` (report §3.2, transcribed against this file's real vocabulary — `s4FC`,
`sfSat`, `Accessibility.hasEdge`/`addEdge`) is defined in `FrameCompleteness.lean` immediately
after the existing four landed Phase 7 arms (`modalApplyOneS4Keyed_{notBoxDia,boxNeg_mint,
diaPos_mint,boxPos,diaNeg}_sat`). The mint-blocked (box-negative) arm is closed by

```
theorem S4RedirectSoundInv_boxNeg_blocked (φ₀ : Proposition Atom) (b e : List (...)) (acc : ...)
    (keys : ...) (Er : List (WorldIndex × WorldIndex)) (src wBlock : WorldIndex) (φ : ...)
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hUniv : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hSat : modalS4Saturated φ₀ b acc)
    (hmint : modalNonMintCandidates φ₀ keys b e acc = [])
    (hblock : blockingWorldS4Keyed φ₀ b keys .neg φ src = some wBlock) :
    S4RedirectSoundInv φ₀ b e (acc.addEdge src wBlock) keys ((src, wBlock) :: Er)
```

`#print axioms` cross-check (direct, not `lean_verify`, per the dispatch's caution about
`lean_verify`'s spurious `sorryAx`):

```
'...modalApplyOneS4Rules_boxPos_notApplicable_of_saturated' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'...modalApplyOneS4Rules_diaNeg_notApplicable_of_saturated' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'...S4RedirectSoundInv_boxNeg_blocked' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Standard axioms only, no `sorryAx`. Sorry census over `Cslib/Logics/Modal/Tableau/`
(`grep -rn "\bsorry\b"`, tactic-use occurrences only): **exactly 1**, the standing
`FrameSoundness.lean:1251` sorry named in the dispatch — unchanged, not touched.

### What closed each conjunct

- **(a)** (every ghost edge recorded): mechanical, via the already-landed
  `hasEdge_addEdge_self_gate0`/`hasEdge_addEdge_mono_gate0` (both already in this file, GATE 0
  section).
- **(b)** (weakened semantic conjunct): the identical model witness from the OLD invariant, no
  reconstruction — `hasEdge_addEdge_cases` case-splits each edge of the extended `acc` into
  "the new edge" (discharged via the `∈ Er'` disjunct) or "an old edge" (inherited from the old
  disjunction, `Er ⊆ Er'`).
- **(c)** (syntactic absorption at the new edge): via the already-landed free transfer
  `blockedRedirect_boxed_{boxPos,diaNeg}_mem` PLUS the already-landed T-self bridges
  `hintikkaS4_{box_pos,dia_neg}_self` — this composition (used already, verbatim, inside
  `modalS4Saturated_addEdge_of_blocked`'s own proof) recovers BOTH the boxed and unwrapped forms
  at `wBlock` from the boxed free transfer alone, sidestepping the unwrapped free transfer's own
  separate `signedSubfmls` relevance side condition entirely.
- **(d)** (frozenness/exhaustion): this is where the report named "one small new lemma" as the
  arm's only open piece. Two new lemmas were added, one per persistent shape:
  `modalApplyOneS4Rules_boxPos_notApplicable_of_saturated` and
  `modalApplyOneS4Rules_diaNeg_notApplicable_of_saturated`. Each shows: given
  `modalS4Saturated`, a box-positive (resp. diamond-negative) persistent-shaped formula's rule
  application is **unconditionally** `.notApplicable` — because every candidate output element
  from all three contributing layers (K's `boxPropagation`/inline diamond-negative filterMap,
  T's `modalTBoxSelf`/`modalTDiaNegSelf`, the 4-rule's `modalFourBoxProp`/`modalFourDiaNegProp`)
  is, BY CONSTRUCTION, filtered against `b` and hence provably `∉ b`; combined with
  `modalS4Saturated`'s own demand that every output element of an applicable rule is `∈ b`, an
  applicable (`.persistent`, necessarily nonempty) result is self-contradictory. Composed with
  the already-landed `modalS4Saturated_addEdge_of_blocked` (giving `modalS4Saturated` at the
  EXTENDED accessibility directly, for free, from the same (c)-transfer facts), this closes (d)
  for box-pos/diaNeg-shaped formulas **at every world, not just `src`** — no case split on
  out-degree or label is needed. For the remaining (propositional/atomic) non-mint shapes,
  mint-readiness (`hmint`, via `modalNonMintCandidates_eq_nil_iff`) plus the already-landed
  `modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box` (fully acc-independent at these shapes)
  closes the case directly.

### Scope note (honest, not elided)

Only the **box-negative-blocked** mint shape (`F(□φ)@src` blocked, guard call
`blockingWorldS4Keyed φ₀ b keys .neg φ src`) was proven. The **diamond-positive-blocked** dual
(`T(◇φ)@src` blocked) was NOT separately written out — it is the exact mirror-image argument
(same two new lemmas, same `blockedRedirect_boxed_diaNeg_mem`/`hintikkaS4_dia_neg_self`
composition, same `modalS4Saturated_addEdge_of_blocked` call with `s := .pos`), but was not
formalized within this probe's time budget. This is a real, flagged gap, not assumed-free: a full
Phase 7 dispatch must write `S4RedirectSoundInv_diaPos_blocked` as a literal (short) companion
theorem before the mint-blocked case can be called fully closed.

### Two visibility widenings (not new content)

`modalUniverseS4_mem_formula` and `mem_signedSubfmls_of_formula_s4loop`, both in
`LoopChecking.lean`, were changed from `private` to public (no proof content touched) — needed
because `FrameCompleteness.lean` cannot see private declarations from an imported file, and (c)'s
relevance-side-condition derivation needs both. Verified via a scoped `lake build
Cslib.Logics.Modal.Tableau.LoopChecking` in isolation before touching `FrameCompleteness.lean`.

## P2 — PASS (the kill criterion does not trigger)

Read directly from `Cslib/Logics/Modal/Tableau/{Rules,FrameRules,Branch}.lean` (not inferred
from report prose, per the dispatch's instruction):

| Rule family | Source | Output-filtered against `b`? |
|---|---|---|
| K box-positive persistent (`boxPropagation`) | `Branch.lean:196-201` | Yes — `if b.any (· == sf) then none else some sf` per successor |
| K diamond-negative persistent (inline in `diamondNeg` arm) | `Rules.lean:152-161` | Yes — same filterMap-against-`b` shape |
| T self-propagation (`modalTBoxSelf`/`modalTDiaNegSelf`) | `FrameRules.lean:62-75` | Yes — `if b.any (· == sf) then [] else [sf]` |
| S4 4-rule (`modalFourBoxProp`/`modalFourDiaNegProp`) | `FrameRules.lean:133-148` | Yes — same filterMap-against-`b` shape, over `acc.successorsOf w` |
| Propositional (`tryAllPropRules ... sf`) | `Rules.lean:85` | N/A — the call takes only `sf`, **never depends on `b` or `acc` at all** |

Every layer that can produce a `.persistent` output filters its own contribution against `b`
before emitting it, and merging (`++`/`.filter (fun x => !kForms.any (·==x))`) only ever removes
elements, never introduces ones absent from a filtered source. Consequently:

- **Branch growth (`b → nf ++ b`)**: `List.any` is monotone under list concatenation
  (`(nf++b).any p = nf.any p || b.any p`), so if an element was already filtered out against `b`
  it stays filtered out against `nf++b`. `.notApplicable` is preserved (in fact: for the
  propositional class, applicability is literally invariant under branch growth, not merely
  preserved when already `.notApplicable`).
- **Edge growth (`acc → acc.addEdge src wBlock`)**: the two new lemmas above show something
  strictly stronger than antitone-applicability under edge growth — `modalS4Saturated` at EITHER
  accessibility forces `.notApplicable` outright, unconditionally, at every box-pos/diaNeg
  formula, by the same filtered-construction argument (not merely "was already notApplicable,
  stays notApplicable" — it is notApplicable regardless of prior state).

**No rule in `FrameRules.lean` re-fires on data it already produced.** The kill condition (some
rule NOT output-filtered) was checked directly against the two worst shapes named in the
dispatch (persistent box-positive, and the propositional/branching family) and neither exhibits
it; by the uniform construction pattern above, none of the other three modal rule families do
either.

## P3 — not attempted (per "skip if not quick")

"Mint seed covers the 4-payload" (`modalFourBoxProp`/`modalFourDiaNegProp` output at the fresh
mint world already `∈ modalApplyOneS4KeyedMint`'s payload) was not separately formalized. The
mint-blocked arm's own (d) proof did not end up needing it — `hintikkaS4_{box_pos,dia_neg}_self`
sidesteps the analogous unwrapped-relevance question by deriving the unwrapped fact FROM the
boxed one via the T-self bridge instead. P3 remains open for a full Phase 7 dispatch's
mint-UNBLOCKED arm restatements (§3.4's `_boxNeg_mint_sat`/`_diaPos_mint_sat` rows), which this
probe did not touch.

## Verification performed

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` (scoped, after the two visibility
  widenings, before touching `FrameCompleteness.lean`): green.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` (scoped, after each edit round):
  green, iterated to convergence.
- `lake build` (full project): green, 3313/3313 jobs, only pre-existing standing sorries
  elsewhere in the library (`FrameSoundness.lean:1227`/`1251` — the SAME standing sorry counted
  twice by warning-vs-source-grep; two unrelated `Logics/Propositional/Tableau/*` sorries, out of
  this task's scope).
- `#print axioms` direct cross-check on all three new declarations (see P1 above): standard
  axioms only.
- `grep -rn "\bsorry\b" Cslib/Logics/Modal/Tableau/"` tactic-use census: exactly 1
  (`FrameSoundness.lean:1251`, the standing retained sorry — unchanged).
- `grep -n "^axiom "`: no new axioms in either modified file.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint` (environment linters, full-project, backgrounded due to runtime): result appended
  below once available; not blocking for this probe verdict (no lint category was targeted or
  plausibly triggered by two new lemmas/one new definition/one new theorem, all fully
  docstring-ed, lowerCamelCase, `lemma`/`theorem` for Prop-valued declarations).

## Files touched

- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — added `S4RedirectSoundInv`, the two new
  `modalApplyOneS4Rules_{boxPos,diaNeg}_notApplicable_of_saturated` lemmas, and
  `S4RedirectSoundInv_boxNeg_blocked`.
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — widened `modalUniverseS4_mem_formula` and
  `mem_signedSubfmls_of_formula_s4loop` from `private` to public (no proof content changed).

## Recommendation for the next dispatch

Proceed with the reformulated Phase 7 (`S4RedirectSoundInv`), per report §3. Before it can be
called complete, still needed:

1. `S4RedirectSoundInv_diaPos_blocked` (the mirror-image companion to the theorem landed here).
2. The mint-unblocked arms (§3.4 rows 2-3) restated against `S4RedirectSoundInv` (currently only
   proven against the OLD, unweakened `branchSatisfiableIn`-style statement in the four existing
   `modalApplyOneS4Keyed_*_sat` lemmas) — P3 becomes relevant here.
3. The 4-rule box-positive/diamond-negative arms (§3.4 row 4) restated with the
   `(w,w') ∈ Er ∨ realized` disjunction.
4. The fuel-induction wrapper assembling all five arms into a genuine step-preservation theorem
   over `modalStepBranchS4KeyedOrdered`, and the terminal payoff (closed-branch contradiction)
   already noted as unaffected in report §3.2.

No part of this is now mathematically open — every remaining piece is "re-wrap a landed lemma
under the new predicate," per the report's own characterization, and this probe's P1/P2 results
confirm that characterization rather than finding a new obstruction.
