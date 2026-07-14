# Handoff: Task 441 Phase 13 (FmpMeasure.lean) — PARTIAL

**Branch**: `task-441-native-refactor` (do NOT merge to main until Phase 15 is green)
**Session**: sess_1783951001_fa3ce4
**Status at handoff**: Phases 1-12 COMPLETE and committed (HEAD `3ce4edcc` at handoff time,
plus one more commit for this phase's partial progress). Phase 13 (`FmpMeasure.lean`, 3011
lines) is PARTIAL: the "measure definitions + shape lemmas" seam is done and committed; the
"decrease/termination proofs" seam remains (98+ errors).

## What's done in Phase 13 so far

All exhaustive-match "Alternative `and`/`or`/`diamond` has not been provided" errors are fixed
(5 sites): `modalSubfmls`, `modalSubfmls_length_le`, `modalDepth`, `modalDepth_le_complexity`,
`modalSubfmls_trans`, `modalDepth_le_of_mem_modalSubfmls`, `modalSf_one_imp_depth_zero`. Each
native `.and`/`.or` case mirrors the existing `.imp` case (binary, both subformula components);
each `.diamond` case mirrors `.box` (unary, adds 1 to depth, since diamond mints a fresh world
exactly like box does in the tableau — see Phase 12's `modalHintikkaSet` discovery). All fixes
verified individually via `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` — these specific
errors are gone; zero sorry/admit introduced.

## What remains (98 errors as of this handoff, in `/tmp` build logs — re-run
`lake build Cslib.Logics.Modal.Tableau.FmpMeasure 2>&1 | grep '^error:'` for a fresh count)

The remaining errors are **all proof-content** (no more exhaustive-match/shape errors), and
cluster around **deeply nested case-splits that disambiguate the OLD Lukasiewicz encoding**
— structurally identical to what Phase 11 (`SoundnessStep.lean`) and Phase 12
(`Tableau/Completeness.lean`) already fixed, but not yet applied here.

### The pattern (see `modalApplyOne_outputs_subset`, ~line 695-786 at handoff time)

The pre-441 code does:
```
rcases ff with _ | _ | ⟨a, c⟩ | φ           -- atom | bot | imp | box (OLD 4-way)
· rcases a with _ | _ | ⟨a2, a3⟩ | a4        -- disambiguate a's shape
  · rcases a4 with _ | _ | ⟨a5, a6⟩ | a7     -- disambiguate deeper
    · rcases a6 with _ | _ | ⟨_, _⟩ | _
      · rcases c with _ | _ | ⟨_, _⟩ | _     -- finally identify diamond-encoded shape
        · exact modalApplyOne_diamondPos_outputs_subset ...
```
This nested exhaustion existed ONLY to detect the Lukasiewicz diamond/and/or encodings, which
no longer exist as `.imp`-nested shapes (task 441 made them separate constructors). **The fix
is NOT to patch each nested `rcases` arm** — it is to flatten every one of these call sites to
a single top-level `rcases ff with atom | bot | imp | and | or | box | diamond` (7-way), with
`.diamond` and `.box` calling the existing `modalApplyOne_diamondPos_outputs_subset` /
`modalApplyOne_boxPos_outputs_subset` / `modalApplyOne_diamondNeg_outputs_subset` /
`modalApplyOne_boxNeg_outputs_subset` helper lemmas directly (these helpers themselves take a
`φ`/formula argument generically and do NOT need to change), and `.and`/`.or` reducing via
`simp` exactly like `.atom`/`.bot` do in the existing code (since `tryAllPropRules` already
fires andPos/andNeg/orPos/orNeg for these natively — see Phase 12's
`modalApplyOne_and_pos`/`_neg`/`or_pos`/`_neg` in `Tableau/Completeness.lean` for the exact
reduction lemmas to reuse, or re-derive local equivalents here if `FmpMeasure.lean` doesn't
import `Completeness.lean`'s section — check import graph first, it does
(`public import Cslib.Logics.Modal.Tableau.Completeness` at the top of this file), so those
lemmas ARE already in scope).

### Known error clusters (line numbers as of this handoff; will shift as fixes land)

- **~695-786**: `modalApplyOne_outputs_subset` — the nested nested-imp nightmare above. Fix by
  flattening per the pattern above.
- **~1143-1212 and a duplicate cluster further down**: same nested-disambiguation pattern
  recurring in a sibling lemma (likely a rank-bound or world-count obligation for a different
  rule family). Same fix.
- **Additional clusters likely exist beyond line ~1450** (the original build hit Lean's
  100-error display cap at line 2783 before this session's fixes; re-run the full build to see
  the current tail once the head clusters are fixed, since fixing earlier errors may change
  later line numbers and reveal previously-hidden errors).
- Errors of shape `omega could not prove the goal`, `Tactic subst failed`, `Tactic introN
  failed: no additional binders` are usually DOWNSTREAM of an unresolved nested-rcases branch
  above them in the same declaration — fix the rcases flattening first, then re-check whether
  these clear up on their own (most should, since they're consequences of the same root cause).

### Mathematical content, NOT just porting

Some of the remaining work may be genuine new proof content (not just flattening), analogous
to Phase 12's `modalHintikkaSet` discovery:

1. **Check `modalWork`/`modalExpMeasure`'s treatment of the persistent rules.** The module
   docstring (top of file) already says *"the persistent modal rules (`boxPos`, `diamondNeg`)
   re-fire without shrinking branch complexity"* — this docstring was written with `diamondNeg`
   already in mind as persistent, suggesting the ORIGINAL author (pre-441, or in an earlier
   scoping pass) anticipated native diamond's arrival. Verify the counting-measure argument
   (`modalWork`, `modalExpMeasure_entry_le_fuel`) doesn't implicitly assume diamondPos is dead
   code anywhere else (search for comments mentioning "dead code" or "never fires" near diamond,
   as in the OLD `Completeness.lean` module note that Phase 12 found and had to correct).
2. **Check the world-bound (`modalWorldBound`) and rank-map invariant sections** (`rankBound`,
   `rankEdge`) for analogous fresh-world assumptions: `diamondPos` mints a fresh world exactly
   like `boxNeg`, so any invariant maintained "only across `boxNeg`" must also be re-derived
   "across `diamondPos`" symmetrically. `boxProps_rank_bound` (around line ~936 at handoff,
   already present) suggests the file already has *some* per-rule-family bound lemmas that may
   need a `diamondProps`-style sibling, or may already generalize — check whether existing
   lemmas parameterize over "the propagated group" abstractly enough to cover diamondPos's
   analogous propagation (`witness :: boxProps ++ diaNegProps` from `Rules.lean`'s
   `.pos, .diamond φ` case) or whether new lemmas are needed.
3. **Re-verify `modalExpMeasure_entry_le_fuel`** (the file's main external-facing result,
   connecting the counting measure to `modalFuel` in `Saturation.lean`) still holds with the
   corrected universe/depth definitions — this is the phase's ultimate deliverable and should
   be the last thing re-checked once all internal lemmas are green.

## Recommended approach for the next dispatch

1. `lake build Cslib.Logics.Modal.Tableau.FmpMeasure 2>&1 | grep '^error:'` for a fresh,
   current error list (line numbers shift after each fix).
2. Fix errors top-to-bottom in the file (earlier fixes often resolve later ones that depend on
   the same declaration).
3. For every `rcases <formula> with _ | _ | ⟨_,_⟩ | _` (4-way, OLD atom|bot|imp|box) that
   appears nested more than one level deep, flatten to the 7-way native pattern
   `atom | bot | imp | and | or | box | diamond` and delete the inner disambiguation layers
   entirely — do NOT try to patch the nested version arm-by-arm.
4. For each `.and`/`.or` case introduced by flattening, first try `simp` (mirroring how
   `.atom`/`.bot` already close via `simp` in the existing code) since `tryAllPropRules`
   resolves them directly via `modalApplyOne_and_pos`/`_neg`/`or_pos`/`_neg`
   (`Tableau/Completeness.lean`).
5. For each `.diamond` case, call the appropriate existing `modalApplyOne_diamondPos_*`/
   `modalApplyOne_diamondNeg_*` helper (search the file for `diamondPos`/`diamondNeg` in
   lemma names — several already exist, per the nested code snippet above; they were written
   assuming diamond needed nested-imp detection to REACH them, so once reachable via a direct
   `.diamond ψ` case, the calls should mostly just work unchanged).
6. Never use `sorry`/`admit`/vacuous placeholders. If a genuine mathematical gap is found
   (per point 2 above, analogous to Phase 12's `modalHintikkaSet` conjunct), fix it with real
   proof content, following the `hintikka_diamond_pos`/`hintikka_diamond_neg` pattern in
   `Tableau/Completeness.lean` as a template for "how to add a symmetric diamond case to an
   existing box-only invariant."
7. Re-run the FULL repo build (`lake build`) once `FmpMeasure.lean` is green, to confirm
   `CompletenessLoop.lean` (Phase 14) is the only remaining red file.

## Files touched this session (all committed except this handoff + final commit)

- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — 5 exhaustive-match fixes (shape lemmas only;
  see "What's done" above). Zero sorry/admit.

## Metadata

See `specs/441_modal_proposition_native_refactor/.return-meta.json` for the final structured
status (`"status": "partial"`, `"requires_user_review": true`,
`"blocked_phase": "Phase 13: FmpMeasure port"`).
