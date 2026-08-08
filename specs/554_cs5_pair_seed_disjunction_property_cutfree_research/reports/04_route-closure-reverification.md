# Round 4: Route-Closure Re-verification at HEAD and Disposition Recommendation

**Verdict: re-affirm the user-prescribed `[BLOCKED]` closure with `requires_user_review: true`.**

Nothing has changed. Every route closure re-verifies sorry-free at HEAD (`5ea7152c`), zero files
under `Cslib/Logics/Modal/Metalogic/` have changed since the kill commit, and no completed
dependency landed anything that reopens a route the prior survey closed. The reopening decision
rests on a graph heuristic ("`[BLOCKED]` with zero unmet dependencies = stale") that is
structurally blind to the distinction this task's block actually encodes: it was never waiting on
a dependency, it is waiting on a user decision.

This report does **not** recommend new implementation work.

---

## 1. What was re-verified at HEAD

HEAD: `5ea7152c4a55653b7ffdd628cce26fa2563f73ec`.

Scoped build of `IS5TotalModels`, `CS5Completeness`, and `Nested.Soundness`: **green**, 676 jobs,
first attempt.

Axiom audit (`#print axioms`, run this pass against the built environment):

| Declaration | Module | Axioms | Status |
|---|---|---|---|
| `is5TotalCountermodelSupply_false` | `Intuitionistic/IS5TotalModels.lean:215` | `propext, Classical.choice, Quot.sound` | HOLDS — (R-a) still refuted |
| `boxEm_not_derivable` | `Intuitionistic/IS5TotalModels.lean:138` | none (**axiom-free**) | HOLDS |
| `bforces_boxEm_of_total` | `Intuitionistic/IS5TotalModels.lean:83` | `propext, Classical.choice, Quot.sound` | HOLDS |
| `is5_derivable_of_boxNotMem_transport` | `InterSystem/CS5ToIS5.lean:103` | `propext, Classical.choice, Quot.sound` | HOLDS — (R-b) still ≡ collapse |
| `nested_sound` | `Constructive/Nested/Soundness.lean:1634` | `propext, Classical.choice, Quot.sound` | HOLDS (see §3) |

No `sorryAx` anywhere in the set. Both machine-checked route closures named in the prior handoff
are intact and unweakened.

The docstring cross-reference at `CS5PairSeedRightExclusion`
(`Constructive/CS5Completeness.lean:508-513`) still states both closures correctly and still
points at the two modules above.

## 2. Did anything land since the kill that opens a closed route?

**No. Nothing landed in the relevant tree at all.**

`git diff --name-only bedd7223..HEAD -- Cslib/` returns 33 files, and every one of them is
tableau work:

| Tree | Files changed since kill |
|---|---|
| `Cslib/Logics/Modal/Tableau/` | 25 |
| `Cslib/Logics/Propositional/Tableau/` | 6 |
| `Cslib/Logics/Temporal/Tableau/` | 1 |
| `Cslib/Foundations/Logic/Tableau/` | 1 |
| **`Cslib/Logics/Modal/Metalogic/`** | **0** |

The completed work since 2026-07-28 (tasks 553, 564, 565, 566, 567, 582, 586) is the classical
S4/S5 tableau-decidability and propositional-hygiene line. It shares no definitions, no frame
conditions, and no proof machinery with the constructive `CS5`/`IS5` metalogic. `Foundations/` has
no non-tableau commits in the window.

Reuse check for a possible new lever: the only cut-elimination infrastructure in the library is
propositional/linear (`Propositional/SequentCalculus/LJ/CutElimination.lean`,
`LK/CutElimination.lean`, `LinearLogic/CLL/CutElimination.lean`). None of it is instantiable for
nested-sequent modal cut-elimination — the cut-value well-ordering and the anchored-cut analysis in
ADS15 §6 are over tree-shaped modal contexts, not over `LJ`/`LK` sequents. No new general
conservativity or prime-exclusion abstraction landed in `Foundations/Logic/Metalogic/`.

## 3. The one thing that *is* materially different from report 02 §5.4 — and why it does not change the verdict

Report 02's cost table (2026-07-25) priced the ADS15 nested-sequent row as "nested sequents +
`NCK'` + soundness + completeness + cut-elim (18 pp.) **and** a new pair extension". Since then,
a substantial part of that row has in fact been built — by this task's own plan 02 (phases 6-14)
and its follow-ons (tasks 570, 575):

`Cslib/Logics/Modal/Metalogic/Constructive/Nested/` — 2,953 lines, five modules, barrel-registered,
**zero sorries** (the two `grep` hits for `sorry` are docstring prose asserting their absence):

| Module | Lines | ADS15 coverage |
|---|---|---|
| `Syntax.lean` | 172 | §2 eq. (2.1) grammar, `fm` translation |
| `Context.lean` | 289 | Observation 2.2, Definition 2.3, output pruning |
| `Translation.lean` | 375 | `fm` compositionality over both context kinds |
| `Rules.lean` | 449 | Figure 2 `NCK'`, `NCS5 = NCK' + {t,4}#_G + {b}[]`, `cut`, `CutFree` |
| `Soundness.lean` | 1,668 | Lemmas 4.2–4.9 and **Theorem 4.1 complete** (`nested_sound` covers all 20 constructors including `.cut`; `nested_sound_provable`) |

So Stages B, C and D of plan 02 are done and green. That is a real, durable asset and the cost
table's first row is, in that narrow sense, stale.

**It does not reopen the route, for three independent reasons.**

1. **Landed soundness points the wrong way.** `nested_sound : NestedProof Γ → Derivable
   CS5ModalAxiom Γ.fm` is *nested ⟹ Hilbert*. An exclusion argument consumes the converse:
   Hilbert-derivability ⟹ cut-free nested provability (completeness + cut-elimination), then a
   subformula-property analysis showing no cut-free proof of `τ_R A` exists. None of the landed
   2,953 lines is in that direction.

2. **Stage E is blocked at its first phase, on a machine-verified obstruction.** Plan 02 Phase 14
   (`handoffs/phase-14-handoff-20260726.md`) is `[BLOCKED]` on a Lean-checked structural fact:
   `InputCtx.fillLhs` and `InputCtx.fillEmpty` produce a `.box`-shaped RHS component
   *unconditionally* (`Rules.lean:401-421`, complete case analysis on `ctx.Γ'`). Consequently
   `botL`, `cut`, `contract`, `andL`, `boxL`, `diaL`, `tL`, `fourL`, `bStruct` and `w` can never
   supply the bare `.atom`-shaped RHS that general `id` at `A = ⊥` — and hence every one of the 17
   `CS5ModalAxiom` derivations — requires. Phase 15 (Theorem 5.1, completeness with cut) is
   `[NOT STARTED]` behind it.

3. **Stages F and G are untouched, and Stage G is unpublished mathematics.** Phases 16–25 (cut
   elimination: super-rules, Lemma 6.5 permutation, auxiliary `♦cut`/`□cut`, height-preserving
   admissibility, the cut-value well-ordering, anchored-cut analysis in two parts, commutative
   cases, Theorem 6.3, Theorem 5.2, subformula property) and Phases 26–32 (the two-label pair
   system, cross-rule permutation "the crux", pair cut-elimination, the seed-relative bridge, the
   exclusion argument, discharge) are all `[NOT STARTED]`. That is **19 of plan 02's 32 phases**,
   comprising exactly the two stages report 02 §3.3 identified as the expensive ones, and Stage G
   remains what §3.3 called it: "new mathematics not in the paper."

Honest re-price of the cost table's ADS15 row: **13/32 phases landed, 19 remaining, and the
remaining 19 are strictly the expensive ones.** The row's verdict ("not a route worth opening for
a single exclusion lemma") is unchanged, and the route is in any case on the user's explicit
do-not-re-propose list (task description, "EXPLICITLY NOT ADOPTED", item (a)).

**One named, live sub-question, recorded not recommended.** The Phase 14 handoff itself asks for
"a second pair of eyes" on whether ADS15 Proposition 3.1's "straightforward induction" has a
formalization that dispatch missed — the obstruction may be an artifact of this development's
encoding choices (`NestedLhs.comma` as a raw non-quotiented constructor; `id` restricted to base
atoms; no admissible weakening/exchange) rather than of ADS15's system. That question is genuine
and unresolved. It is **not** a route to this task's obligation: resolving it unblocks Phase 14
only, leaving Phases 15–32 including all of Stages F and G. It belongs to whoever owns the
`Nested/` development, not to this task's disposition.

## 4. Why the reopening premise does not hold

The 2026-08-08 review (`specs/reviews/review-2026-08-08.md` §H3) reopened this task on this basis:

> Six tasks carry `[BLOCKED]` with zero unmet dependencies (37, 409, 511, 554, 568, 583). Only 37
> is genuinely blocked (external upstream). … unblocking **554** releases 537 and 551.

Both halves are unsound as applied here:

- **The staleness test cannot see this block.** Task 554's `dependencies` array is `[]` and always
  was; it was never blocked on another task. Its block is a *user-decision gate*, recorded as
  `requires_user_review: true` in `.orchestrator-handoff.json` and as the second entry of the
  `blockers` array in `specs/state.json` ("Requires user review: (R-a) refuted machine-checked
  … continuation options … are a user decision"). "Zero unmet dependencies" is exactly what a
  correctly-closed user-review block looks like, so the heuristic misclassifies it by construction.

- **"Unblocking 554 releases 537 and 551" inverts the causation.** The verdict 537 and 551 were
  waiting for has already been delivered, and it is negative. Task 537's own recorded blocker says
  so verbatim: *"If it fails, this task closes `[BLOCKED]` with the cost table as justification
  rather than opening a nested-sequent formalisation."* It failed. Task 551's blocker likewise
  records that its named open Prop is refutable as stated and that the §8.1 corrections are the
  land-now items — all of which landed. Re-running 554 does not release those two tasks; the
  answers they need are already written, and acting on those answers is a user decision about
  each of them, not more work here.

The task description's kill-criterion is verbatim: *"If R-a fails, the route is dead and this task
closes `[BLOCKED]` with the section 5.4 cost table as justification — a negative result is a valid
deliverable."* (R-a) failed, machine-checked, and the verdict was upstreamed into the library.
The deliverable was produced. Re-litigating that into new implementation work is precisely what the
rescope forbade.

## 5. Answers to the two consumers — unchanged, re-verified

- **Pair-Lindenbaum consumer (task 551, `CS5PairSeedRightExclusion`)**: the obligation is not
  dischargeable by any surveyed route without user-authorised `CS5 = IS5` collapse. Machine-checked
  at HEAD: the (R-b) residual *is* the collapse (`is5_derivable_of_boxNotMem_transport` +
  `is5_iff_cs5_derivable_of_boxNotMem_transport`), and the (R-a) residual is refuted
  (`is5TotalCountermodelSupply_false`). The collapse's only published basis is Pacheco's
  Lemma 16/18, the unsound argument this task exists to repair.
- **Labelled-soundness consumer (task 537, `sigAt` context-fold)**: fold unrepairable; answer
  **"never"**, unchanged. The missing bridge `□(A∨B) → (□A ∨ □B)` fails already in classical `S5`
  (report 02 §4, §7), so no strengthening of the base logic can supply it.

Note on the (R-a) refutation's exact reach, stated precisely so it is not over-claimed:
`is5TotalCountermodelSupply_false` refutes the *uniform* countermodel supply the route requires,
via the instance `H := ∅`, `A := □a ∨ ¬□a`. That instance is a legitimate instance of the
obligation (`boxEm ∉ cl_CS5(boxInv ∅)`, since it is not even `IS5`-derivable), so the route dies as
a uniform strategy — which is the only way a universally-quantified obligation with downstream
consumers can be discharged. What is *not* claimed, then or now, is that the obligation itself is
false; only this proof strategy is dead.

## 6. Incidental finding (hygiene, not a route)

`Cslib/Logics/Modal/Metalogic/InterSystem/CS5ToIS5.lean:45-46` closes its module docstring with
"The cut-free nested-sequent route (`Constructive/Nested/`) is the adopted alternative." That
sentence predates the 2026-07-26 rescope, which put the nested-sequent formalisation on the
explicit not-adopted list. At HEAD the library therefore names as "adopted" a route the task
description forbids re-proposing. This is a one-sentence docstring correction, not a research
finding; it is outside this task's declared `file_scope`
(`Cslib/Logics/Modal/Metalogic/Constructive/Nested/`) and is recorded here for whoever picks up
the hygiene sweep.

## 7. Recommendation

**(ii) Re-affirm the user-prescribed `[BLOCKED]` closure**, with:

- justification = report 02 §5.4's cost table (re-priced in §3 above: still prohibitive) plus the
  two machine-checked route closures, both re-verified sorry-free at HEAD this pass;
- `requires_user_review: true`;
- both consumers' answers restated as in §5.

No plan should be created. The only legitimate continuations are user decisions, unchanged from
2026-07-28:

1. **Accept the negative result** and close the constructive `CS5` pair-seed line — which also
   means closing 537 and 551 on their own recorded terms, since the verdict they were gated on has
   arrived.
2. **Authorise the `CS5 = IS5` collapse route**, knowing its published basis (Pacheco's
   Lemma 16/18) is the same unsound argument `CS5Completeness.lean` was written to repair, so it
   would have to be proved from scratch rather than cited.
3. **Authorise re-opening the nested-sequent route** (Stages E–G, 19 phases, Stage G unpublished),
   overriding the 2026-07-26 rescope's item (a).

If the intent behind reopening was scheduling throughput rather than mathematics, the
throughput-positive action is to dispose of 537 and 551 on the verdict already delivered — not to
re-run 554.

## 8. References

**Verified at HEAD this pass**
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5TotalModels.lean` (222 lines)
- `Cslib/Logics/Modal/Metalogic/InterSystem/CS5ToIS5.lean` (137 lines)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` (`CS5PairSeedRightExclusion`
  :514, `cs5PairSeedDisjunctionProperty_false` :550)
- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/{Syntax,Context,Translation,Rules,Soundness}.lean`

**Prior artifacts consulted**
- `reports/01_pair-seed-disjunction-collapse.md`, `reports/02_cutfree-literature-grounded.md` (§3.3,
  §5.3, §5.4, §7, §8)
- `plans/02_cutfree-pair-conservativity.md` (Stages A–G, phase status markers)
- `plans/03_ra-probe-product-model.md`, `summaries/03_ra-probe-summary.md`
- `handoffs/phase-14-handoff-20260726.md`, `handoffs/phase-2-handoff-20260728.md`
- `.orchestrator-handoff.json`, `.orchestrator-churn-state.json` (churn 0 across the board)

**Task-graph sources**
- `specs/reviews/review-2026-08-08.md` (§H3, the reopening rationale)
- `specs/state.json` (tasks 537, 551, 554)

**Literature** (unchanged; no new sources consulted, and none could change the disposition —
a new calculus would be another formalisation task, which the rescope excludes)
- [ArisakaDasStrassburger2015], [MarinMoralesStrassburger2021], [Pacheco2024]
