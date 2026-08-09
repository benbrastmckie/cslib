# Task 511 Research Report 03 — Re-verification of the Phase 7 Blocker Against HEAD

- **Date**: 2026-08-08
- **Session**: sess_1786219370_0903ea_511
- **Task**: 511 — S4 loop checking termination (close the termination bound and complete decidability)
- **Scope files**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean`,
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (plus the ten `Cslib/Logics/Modal/Tableau/S4/*.lean`
  modules the barrel now re-exports)
- **HEAD at time of research**: `5ea7152c`

## Executive Summary

**The recorded Phase 7 blocker no longer holds at HEAD, and it was not resolved by either of the two
routes the handoff anticipated.** It was resolved by a third route that the dependency tasks landed
while 511 was blocked: the project stopped trying to reconcile the keyed termination proof with the
live-guard driver `modalTableauS4`, and instead built a *new* real decision procedure —
`modalTableauS4KeyedOrdered` — whose stepper is the keyed one the termination proof is about.

Concretely, at HEAD:

- **Route (a) is ~85% landed, not merely "plausible in principle".** The bespoke S4 keyed top-level
  driver the handoff called for exists twice over: `modalExpandBranchesS4Keyed` /
  `modalTableauS4Keyed` (`S4/Driver.lean:2297`, `LoopChecking.lean:153`) and its successor
  `modalExpandBranchesS4KeyedOrdered` / `modalTableauS4KeyedOrdered` (`S4/Driver.lean:2513`,
  `LoopChecking.lean:200`). Both carry full `processNext`-style fuel inductions.
- **The soundness re-verification the handoff flagged as "unverified" has been completed — and its
  answer was more interesting than expected.** Soundness is *false* for the unordered keyed driver
  (machine-checked counterexample, `CslibTests/S4LoopGuardRegression.lean`, documented at
  `FrameCompleteness.lean:4088-4104`), and *true and proved* for the ordered one:
  `modalTableauS4KeyedOrdered_sound` (`FrameCompleteness.lean:8234`) concludes genuine, unweakened
  `s4Valid φ₀`, sorry-free, with an empty `#print axioms` list.
- **Route (b) (generalizing `RuleApply`/the driver framework to thread opaque per-branch state) is
  moot for closing S4** — and it also partly landed anyway, as the `RuleApplySt` ladder
  (`modalApplyOneS4KeyedSt`, `modalTableauS4Keyed_eq_modalExpandBranchesGenSt`,
  `LoopChecking.lean:168`). It is not on the critical path.
- **What is actually left is a bounded, mechanical port**: the completeness half for the ordered
  driver, then the decidability capstone. Every non-trivial ingredient already exists. Estimated
  ~580 added lines, of which ~490 are near-verbatim structural copies of already-proven unordered
  analogues.

**Recommendation: do not re-block. Proceed to `/plan` with a four-phase shape (below).** The
standing permission to re-block with a sharpened goal state is not needed.

## 1. What Changed Since the Blocker Was Written

The eight dependencies all landed. The four that moved the picture:

| Task | Effect on 511 |
|------|---------------|
| 553 | Built the *ordered* stepper `modalStepBranchS4KeyedOrdered` and the whole soundness stack over it (`S4RedirectSoundInv`, `Ex4Inv`, `modalExpandBranchesS4KeyedOrdered_closed_False`), culminating in `modalTableauS4KeyedOrdered_sound`. This is the load-bearing change. |
| 563 | Birth-key (`□⁺` enrichment) work underlying `blockingWorldS4Keyed`. |
| 564 | Landed the state-threaded `RuleApplySt` bridge (`modalApplyOneS4KeyedSt` + four bridge theorems) — the partial realization of route (b). |
| 565/566/567/586 | Split `LoopChecking.lean` into the ten-module `S4/` cluster (move-only) and reconciled prose. Purely locational, but it means the plan must name new file paths. |

**Verified state of the tree at HEAD** (commands run this dispatch):

- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` — green, 910 jobs, exit 0.
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` — green, 876 jobs.
- Sorry census over `Cslib/` (the README's own two-pattern command): **zero** hits anywhere under
  `Cslib/Logics/Modal/Tableau/`. All 28 remaining repo sorries are in `Logics/Bimodal/` and
  `Logics/Propositional/Tableau/`.
- `lean_verify Cslib.Logic.Modal.Tableau.modalTableauS4KeyedOrdered_sound` → `{"axioms": [], "warnings": []}`
  (control: `modalTableauS4Keyed_complete` → the standard `propext`/`Classical.choice`/`Quot.sound`;
  a bogus name errors, so the empty list is a real result, not a silent lookup failure).

## 2. The Blocker, Re-verified Clause by Clause

The handoff's blocker had three clauses. Their status at HEAD:

| Clause | Status | Evidence |
|--------|--------|----------|
| "`modalTableauS4` runs `modalApplyOneS4`/`blockingWorldS4` (live-set guard)" | **Still literally true**, but no longer relevant — `modalTableauS4` (`S4/Driver.lean:219`) is no longer the intended decision procedure and has no consumer on the decidability path. | `grep def modalTableauS4` |
| "`S4LoopInv`/`modalStepBranchS4_worldBound` are proven only for the keyed shadow stepper" | **Still true, and now a feature rather than a defect** — the keyed stepper is the one the shipped driver runs. `modalStepBranchS4_worldBound` is consumed at `LoopChecking.lean:615`, inside the `modalExpMeasure_step_lt_S4Keyed` chain that both keyed drivers' fuel arguments route through. | `LoopChecking.lean:594-643` |
| "the world-bound is proven about a driver `modalTableauS4` does not run" | **Resolved.** `modalTableauS4KeyedOrdered` runs `modalStepBranchS4KeyedOrdered`, whose measure decrease is `modalExpMeasure_step_lt_S4KeyedOrdered` (`LoopChecking.lean:945`), which factors through the same `modalStepBranchS4_worldBound` pigeonhole bound via `modalStepBranchS4KeyedOrdered_proj`. Fuel sufficiency at the entry state is `modalExpMeasure_entry_le_fuelS4` (`LoopChecking.lean:660`), which is a statement about `modalExpMeasure` and `modalFuelS4` only, hence driver-independent and already applied to both drivers. | `LoopChecking.lean:927-1000`, `8254-8258` in FrameCompleteness |

**One correction to the handoff's own framing, worth carrying forward.** The handoff assumed that
once a keyed top-level driver existed, "soundness and the truth lemma reconnect against the keyed
guard" would be a re-verification step. That assumption was falsified: the unordered keyed guard is
*unsound*, for two independent reasons recorded at `FrameCompleteness.lean:4090-4098` — comparing
prospective minting content against a world's recorded birth key rather than its live content
("staleness"), and admitting a redirect edge without requiring the target be reachable from the
source ("no reachability restriction"). The repair was not to the guard's comparison predicate but
to *when* a minting shape may fire (settled-context scheduling: non-minting candidates first,
minting only once no non-minting rule can fire anywhere on the branch —
`modalStepBranchS4KeyedOrdered`, `S4/Driver.lean:631`). That repair carries both defects, and its
soundness is now proved.

## 3. Inventory: What Exists, What Is Missing

The decidability capstone `instDecidableS4Valid` needs exactly two theorems about one driver:
soundness and completeness. Mirror target is the KB5 pair at `FrameCompleteness.lean:4069-4082`
(`kb5Valid_decides` / `instDecidableKb5Valid`), which is three lines each.

### Landed (verified present at HEAD)

| Declaration | Location |
|---|---|
| `modalTableauS4KeyedOrdered` (entry point, seeds `keys := [(0, ∅)]`, fuel `modalFuelS4 φ`) | `LoopChecking.lean:200` |
| `modalTableauS4KeyedOrdered_sound` | `FrameCompleteness.lean:8234` |
| `modalExpMeasure_step_lt_S4KeyedOrdered` (termination) | `LoopChecking.lean:945` |
| `modalExpMeasure_entry_le_fuelS4` (fuel sufficiency at entry) | `LoopChecking.lean:660` |
| `S4OrderedFuelInv` (the 5-conjunct bundle: `S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧ worldsContiguousS4 ∧ keysOriginS4`) | `S4/HintikkaInvariant.lean:~828` |
| `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv` (one step lemma covering the whole bundle) | `S4/HintikkaInvariant.lean:840` |
| `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` / `_preserves_S4KeyedHintikkaInv` | `S4/Invariant.lean:615`, `S4/HintikkaInvariant.lean:636` |
| `modalStepBranchS4KeyedOrdered_branch_superset`, `_cases`, `_selected_mem`, `_eq_none_iff`, `_proj`, `_newExps_eq_map` | `S4/Driver.lean`, `FrameCompleteness.lean:7869` |
| `modalHintikkaSetS4_eq`, `hintikka_congr_S4` (the keyed→live Hintikka bridge; task 511's own Phase 7 `rfl` bridge) | `S4/Hintikka.lean:101`, `:622` |
| `modalOpenBranchS4_countermodel` (open branch → reflexive-transitive countermodel) | `FrameCompleteness.lean` |
| `modalTableauS4Keyed_initial` + `keysOriginS4_entry` (the seed-state `S4OrderedFuelInv` witness, already assembled verbatim inside `modalTableauS4KeyedOrdered_sound`) | `FrameCompleteness.lean:4118`, `S4/BirthKey.lean:241` |
| Unordered analogues of both target theorems: `modalExpandBranchesS4Keyed_hintikka` (~360 lines), `modalExpandBranchesS4Keyed_openBranch_initial_mem` (~130 lines), `modalTableauS4Keyed_complete` | `LoopChecking.lean:1134`, `:1495`, `FrameCompleteness.lean:4189` |

### Missing (the entire remaining scope)

1. `modalStepBranchS4KeyedOrdered_none_saturated` — the ordered twin of the private
   `modalStepBranchS4Keyed_none_saturated` (`LoopChecking.lean:1099`).
2. Relocation of `modalStepBranchS4KeyedOrdered_newExps_eq_map` from `FrameCompleteness.lean:7869`
   down into `LoopChecking.lean` (layering: the Hintikka lemma lives below `FrameCompleteness`).
3. `modalExpandBranchesS4KeyedOrdered_hintikka` — structural port of the unordered ~360-line lemma.
4. `modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem` — structural port of the ~130-line lemma.
5. `modalTableauS4KeyedOrdered_complete` — near-verbatim copy of `modalTableauS4Keyed_complete`.
6. `s4Valid_decides` + `instDecidableS4Valid` — three lines each, mirroring `kb5Valid_decides` /
   `instDecidableKb5Valid`.

## 4. Machine-Checked De-risking Performed This Dispatch

Item 1 above is the only new proof content that is not a copy, so it was **probed for real** rather
than asserted. A temporary `private lemma` was appended to `LoopChecking.lean`, built, and reverted
(`git diff Cslib/` clean afterwards). The following typechecks as a one-liner:

```lean
private lemma modalStepBranchS4KeyedOrdered_none_saturated (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys = none)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
    sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable :=
  modalStepBranchS4Keyed_none_saturated φ₀ b e acc keys
    ((modalStepBranchS4KeyedOrdered_eq_none_iff φ₀ b e acc keys).mp hstep) sf hsfb
```

`lake build Cslib.Logics.Modal.Tableau.LoopChecking` → `✔ [876/876]`, exit 0. This is exactly the
transfer `modalStepBranchS4KeyedOrdered_eq_none_iff`'s own docstring was written to enable ("lets
later phases — the saturation step in particular — transfer facts about the old stepper's
termination condition to the new one without re-deriving anything").

Item 2 was verified by reading the proof of `modalStepBranchS4KeyedOrdered_newExps_eq_map`
end-to-end: its only dependencies are `modalStepBranchS4KeyedOrdered_cases`,
`modalNonMintCandidates_not_mem_expanded` (public, `S4/Driver.lean:414`),
`modalStepBranchS4KeyedBody`, `modalStepBranchS4Keyed`, and `modalApplyOneS4Keyed` — all in
`S4/Driver.lean`, all below `LoopChecking.lean`. The relocation is a pure move with no proof edit.

## 5. Why the Port (Items 3-4) Is Structural, Not a Second Crux

The unordered `modalExpandBranchesS4Keyed_hintikka` uses exactly six stepper-specific facts. Five
have ordered twins already landed; the sixth is item 1 above:

| Used by the unordered proof | Ordered replacement |
|---|---|
| `modalStepBranchS4Keyed_none_saturated` (9 call sites) | item 1 (probed green above) |
| `modalStepBranchS4Keyed_newExps_const` | `..._newExps_eq_map` after relocation (item 2) |
| `modalStepBranchS4_preserves_S4LoopInv` | `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` |
| `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` | `modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv` |
| `modalExpMeasure_step_lt_S4Keyed` | `modalExpMeasure_step_lt_S4KeyedOrdered` |
| `modalHintikkaSetS4_eq` / `hintikka_congr_S4` (the final bridge) | driver-independent, reused verbatim |

**One deliberate simplification the port should take.** The ordered
`_preserves_S4LoopInv` carries an extra hypothesis `keysOriginS4 b acc keys` and an extra conclusion
conjunct that the unordered one does not. Rather than widening the unordered proof's four-way
per-index conjunction to five, the port should use the already-bundled `S4OrderedFuelInv` as its
per-index hypothesis and `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv` as its single
step lemma. This is strictly less bookkeeping than the unordered original, and the seed-state
witness is already constructed — `modalTableauS4KeyedOrdered_sound` builds
`⟨hLoop, hHintikka, hKW, hWC, hKO⟩` from `modalTableauS4Keyed_initial` + `keysOriginS4_entry` at
`FrameCompleteness.lean:8240-8246`, and that expression is reusable verbatim.

**Residual risk, stated honestly.** Items 3-4 are ~490 lines of induction whose `processNext` inner
`suffices` block is written against explicit `pending`/`done` list-append arithmetic. Structural
ports of this shape in this subsystem have repeatedly cost more than "copy and rename" suggests —
the ordered invariant-preservation twins (tasks 553/564) each needed
`modalStepBranchS4KeyedOrdered_selected_mem` threaded in place of a direct `findSome?` extraction,
and the same substitution will be needed here wherever the unordered proof destructures the step
hypothesis directly. That is a known, bounded shape of friction, not an unknown. It is the reason
the phase plan below puts items 3 and 4 in separate phases rather than one.

## 6. Recommended Route and Phase Shape

**Route: (a), completed against the *ordered* driver.** Not (b).

Rationale: (b) — generalizing the driver framework to thread opaque per-branch state — was partly
built anyway (`RuleApplySt`, task 564) and is *still* not on the critical path, because the ordered
driver's completeness proof needs the keyed bundle `S4OrderedFuelInv` threaded per branch, which no
`Prop`-valued `Aux` over `(b, e, acc)` supplies. Waiting on a framework generalization would trade a
~580-line bounded port for an open-ended abstraction design. The abstraction question is real, but
it is task 597's question, not a precondition for S4 (see §7).

Suggested phases (each independently `lake build`-verifiable, zero sorry throughout):

- **Phase 1 — Ordered saturation + layering prerequisites** (`LoopChecking.lean`, ~40 lines).
  Add `modalStepBranchS4KeyedOrdered_none_saturated` (proof given verbatim in §4, already probed
  green). Relocate `modalStepBranchS4KeyedOrdered_newExps_eq_map` from `FrameCompleteness.lean:7869`
  into `LoopChecking.lean`, deleting the original. Verify: `lake build` on both modules.
- **Phase 2 — `modalExpandBranchesS4KeyedOrdered_hintikka`** (`LoopChecking.lean`, ~370 lines).
  Structural port of `modalExpandBranchesS4Keyed_hintikka` (`:1134-1493`), with `S4OrderedFuelInv`
  as the per-index hypothesis and `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv` as the
  step lemma. This is the phase with real risk; it is deliberately alone.
- **Phase 3 — `modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem`** (`LoopChecking.lean`,
  ~135 lines). Structural port of `:1495`, substituting
  `modalStepBranchS4KeyedOrdered_branch_superset` and the relocated `_newExps_eq_map`.
- **Phase 4 — Completeness and the decidability capstone** (`FrameCompleteness.lean`, ~60 lines).
  `modalTableauS4KeyedOrdered_complete` (copy of `:4189`, feeding the Phase 2/3 lemmas and the
  existing `modalTableauS4Keyed_initial` + `keysOriginS4_entry` seed witness), then
  `s4Valid_decides` and `instDecidableS4Valid` mirroring `kb5Valid_decides` /
  `instDecidableKb5Valid` (`:4069-4082`). Update the two stale prose notes that assert decidability
  is out of scope (`FrameCompleteness.lean:4099-4102`, `LoopChecking.lean:151-152`).

Deliberately **out of scope** for 511 (flag to the planner, do not absorb):

- Retiring `modalTableauS4Keyed` / `modalExpandBranchesS4Keyed` and their unordered proof stack.
  `LoopChecking.lean:188-189` earmarks this as a separate destructive phase, gated on every consumer
  having an ordered replacement — which Phase 4 above is a precondition for, not a part of.
- Retiring the live-guard `modalTableauS4` (`S4/Driver.lean:219`).
- The standing `sorry`-free-but-deliberately-weakened per-step soundness scope note in
  `FrameSoundness.lean` (see `FrameCompleteness.lean:8212-8221`); it is untouched by this work.

## 7. Bearing on Task 597 (flagged, not presupposed)

Task 597 is deciding the tableau driver abstraction across three termination regimes. Two findings
from this dispatch bear on that decision; neither presupposes its outcome:

1. **S4's decidability does not gate on, and should not wait for, the abstraction decision.** The
   remaining work is a within-file port against already-proven ordered lemmas. If 597 later lands a
   unifying abstraction, the S4 driver becomes a candidate *consumer* of it, exactly as
   `modalApplyOneS4KeyedSt` already is for the `RuleApplySt` ladder.
2. **A concrete data point for 597's cost model, from the losing side.** The bespoke-per-regime path
   for S4 has now produced *two* parallel driver stacks (unordered keyed and ordered keyed) with
   near-duplicate invariant-preservation lemmas — roughly 15 `modalStepBranchS4KeyedOrdered_preserves_*`
   twins of `modalStepBranchS4Keyed_preserves_*` — and this task adds two more ~250-line structural
   twins on top. That duplication is the measurable cost of not having an abstraction that can thread
   per-branch state; 597 should weigh it. Counterweight, equally real: the duplication was cheap
   *because* the lemmas were structural copies, and the ordered driver could only be built at all
   because the bespoke path let its scheduling change independently of the guard predicate.

## References

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (barrel + entry points + termination measure)
- `Cslib/Logics/Modal/Tableau/S4/Driver.lean`, `S4/Guard.lean`, `S4/Hintikka.lean`,
  `S4/Invariant.lean`, `S4/HintikkaInvariant.lean`, `S4/BirthKey.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (S4Keyed completeness §4088+, ordered
  soundness §7804-8262, KB5 decidability template §4069-4082)
- `CslibTests/S4LoopGuardRegression.lean` (the unsoundness counterexample and the ordered-driver
  soundness smoke row at `:211`)
- `specs/511_s4_loop_checking_termination/handoffs/07_phase7-blocked-driver-mismatch.md` (the blocker
  re-verified here)
- [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
