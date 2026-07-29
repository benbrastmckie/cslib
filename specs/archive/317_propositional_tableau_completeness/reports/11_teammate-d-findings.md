# Teammate D (Horizons) Findings — Task 317 Strategic Trajectory

## Key Findings

1. **Task 317 sits at the head of a 4-task dependency fan-out** (375, 413, 430, 456), all
   under the "Propositional Logic" / "Abstraction & Redundancy Cleanup" waves of
   `specs/ROADMAP.md`. Three of the four (375, 430, 456) have a genuine content dependency on
   317's output; 413's dependency looks like sequencing hygiene (avoid editing files 317 has
   open) rather than a content need — see table below.

2. **Task 430 appears to be substantially subsumed by 317's current stated scope**, and its own
   research already says so. 430's blockers field states: "317 v6 Phase 10 already claims both
   validity-bridge sorries... 430 cannot close them until 317 Wave A lands the frame plumbing.
   430 re-runs after 317 as verify/re-gate." Its falsification-spike report (03) concludes the
   fix is "edge ReflTransGen order + new sat_atom_persist saturation field on the returned
   branch (= task 317 B2 territory)." This is the single most consequential scoping question in
   this research: **does 317's item (4) — "close the two IValid/MValid bridges" — actually
   include the atom-persistence/edge-accessibility machinery 430 identified as necessary, or is
   317's "assembly only" framing for item 4 optimistic?**

3. **Evidence the bridges may be harder than "assembly"**: report 10 (`10_wave-a-atomic-derisk.md`,
   the most recent artifact before this dispatch) says the de-risk work "closes 0/4 sorries but
   reshapes 3-4 to edge-frame Phase-10 goals" using an "improved IFimpAccess companion
   predicate" — language that matches 430's edge-accessibility / atom-persistence problem, not a
   trivial wiring step. The task-317 description's item (1) (`sat_timp` field, discharged at
   `IExpandedConsistent_sat`) is about the T-implication modus-ponens fixpoint for
   *consistency*, which is a different saturation concern from 430's atom-persistence upward-closure
   for the *countermodel*. These may be two distinct fields that both need to land before item
   (4) actually closes. I did not re-derive the Lean proof state (out of scope for this angle),
   but flag this as the load-bearing open question for the implementer, not settled by the task
   description's confident framing.

4. **The parametric mandate (discharge truth-lemma/countermodel once over
   `IntMinScheme.{closurePred, modelBot}`) is a cheap, already-built reuse, not a new
   abstraction investment.** `IntMinScheme` already exists in
   `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:122` with `closurePred` and
   `modelBot` fields, an `intuitionisticScheme`/`minimalScheme` instance pair, and a generic
   soundness lemma already written against `S.closurePred`/`S.modelBot` (Scheme.lean:225,
   :537). The task's mandate is to finish threading the *truth lemma* through this
   already-landed parameter surface, not to invent it. This is low-risk and squarely in scope
   for a 2-instance abstraction; there is no premature-generalization concern here because the
   generalization already happened at a prior point in this task's history.

5. **No collision with the concurrent Modal/Tableau refactor (task 557).** 557's file scope is
   `Cslib/Logics/Modal/Tableau/{LoopChecking,FrameSoundness,FrameCompleteness,FmpMeasure,
   GenericDriver,S5Simplification}.lean` + `Boneyard/`. 317's file scope is
   `Propositional/Tableau/Intuitionistic/{Scheme,Completeness}.lean` +
   `Minimal/Completeness.lean`. These are disjoint files in disjoint logic families. 557's own
   abstraction decisions (Lemmon box-plus keys, `RuleApplySt`) are explicitly S4/Modal-scoped —
   its description states box-plus "MUST NOT be lifted into Foundations/" — so there is no
   pending shared-abstraction decision in 557 that 317's `IntMinScheme` parametrization needs to
   align with. The two efforts are abstracting different, non-overlapping axes (Modal
   loop-checking driver state vs. Propositional int/min truth-lemma parameterization).

6. **The actual cross-family abstraction candidate is task 456, not 557.** 456 targets
   `Cslib/Foundations/Logic/Tableau/Blocking.lean` (new), generalizing the Sfor-containment
   device shared by 317's own dedup lemma (`intExpandBranches_world_bound_dedup`, plan 04 Phase
   5.1) and the currently-`[BLOCKED]` Temporal soundness obligation
   (`Temporal/Tableau/Soundness.lean:23-54`). This is the one place where 317's output does feed
   a genuinely shared (cross-logic-family) abstraction, and it is explicitly sequenced after 317
   ("DEPENDS ON task 317 landing first (so the (psi not in forced(x)) side-condition shape is
   settled)"). This is consistent with the ROADMAP's stated "one shared abstraction per concern"
   philosophy and should NOT be pulled forward into 317's scope — it is correctly a separate,
   later task.

## Downstream Consumer Analysis

| Dependent task | What it needs from 317 | Is 317's stated scope sufficient? |
|---|---|---|
| **375** (fold tableau nodes into propositional proof-system TFAE) | The final theorems `intuitionisticTableau_complete` / `minimalTableau_complete` (+ Classical, done elsewhere) sorry-free, so they can be wired as TFAE nodes. Does not care about internal proof shape (parametric vs. duplicated), only that the bridges are true. | **Yes, if item (4) actually closes.** Right-sized — 375 needs exactly what item (4) promises, no more, no less. Risk is contingent on Finding 3 above (is item 4 really "assembly"?). |
| **430** (atom-persistence / upward-closure for the two validity bridges) | Historically, the SAME two bridges as 317 item (4). Its own research (falsification spike, report 03) concluded the fix belongs in "317 B2 territory" (a new saturation field on the returned branch). | **Likely already superseded, not "sufficient vs. insufficient."** If 317 lands item (4) using an equivalent mechanism, 430 has no remaining independent work beyond re-verification. Recommend explicit disposition (see Strategic Recommendation) rather than leaving 430 to "re-run as verify/re-gate" indefinitely. |
| **413** (proof-style simplification/normalization in Propositional/) | Its target files are the general-purpose normalization lemma sites (`ListImplication.lean`, `bigconj_*`), which are outside 317's file scope entirely. The dependency looks like it is there to avoid editing the same Tableau files mid-flight, not because 413 consumes anything 317 produces. | **317's scope is irrelevant to 413's content need — the dependency is a merge-conflict/sequencing artifact, not a technical one.** Could likely be decoupled and run in parallel on the actually-disjoint files, if the orchestrator wants to unblock wave 3 sooner. Flagged as a low-confidence observation since I did not verify 413 never touches Tableau/ files. |
| **456** (generalize Sfor-containment/blocking into `Foundations/Logic/Tableau/Blocking.lean`) | The FINAL, stable shape of `intExpandBranches_world_bound_dedup`'s side condition (`psi ∉ forced(x)`) — needs 317's containment/dedup machinery to stop moving before lifting it into a shared module consumed by Temporal too. | **Sufficient, and correctly sequenced after 317 rather than folded into it.** One nuance: since Gap 1/2 (fuel sufficiency, Sub(φ₀) determinacy) are reported already resolved, the dedup lemma's *shape* may already be stable even before items (1)-(4) land — worth a quick confirmation before treating 456 as strictly blocked on 317's full completion, since items (1)-(4) don't obviously touch the dedup/containment machinery itself. (Medium confidence; would need direct inspection of `intExpandBranches_world_bound_dedup`'s current state to confirm.) |

## Strategic Recommendation

**317's stated scope is right-sized for its primary consumer (375) IF and only IF item (4) is
actually closeable from items (1)-(3) as claimed.** That conditional is the one thing this
research could not verify without reading proof state, and it is the single highest-leverage
thing for the assigned implementer to check first — before touching the docstring repair or the
`sat_timp` field — because if item (4) needs its own additional saturation field (as 430's
falsification spike concluded), the "assembly only" framing under-scopes the task and the
implementer should say so explicitly rather than discover it mid-dispatch.

**Rescope proposal: absorb 430's remaining role into 317 explicitly, then close 430.** Task 430
was created before 317's Gap 1/Gap 2 resolution and before 317 claimed ownership of the exact
same bridges. Its own artifacts already concede this ("re-runs after 317 as verify/re-gate").
Rather than leaving a live task whose only function is to re-verify what 317 did, recommend:
(a) 317's implementation explicitly documents which saturation field/lemma discharges the
atom-persistence obligation for the bridges (whether that's `sat_timp` reused, a new field, or
430's proposed `sat_atom_persist`); (b) once 317 lands, /spawn or /task should close 430 as
subsumed-by-317 rather than dispatching it, unless the verification step turns up a genuine gap
317 didn't cover. This avoids two independent research/implementation efforts converging on the
same two proof obligations.

**The parametric `IntMinScheme` mandate is the right investment and should proceed as scoped.**
It is not a new abstraction bet — it completes one already built into the codebase — and it
does not compete with or need to align with the concurrent Modal/Tableau abstraction work (557),
which operates on a disjoint axis (loop-checking driver state, S4-scoped box-plus keys) in
disjoint files. Do not attempt to unify `IntMinScheme` with anything in Modal/Tableau/ now; that
would be premature generalization the ROADMAP itself doesn't call for anywhere.

**Do not fold 456's Foundations-level generalization into 317.** It is correctly scoped as a
separate, later task per the ROADMAP's own "one shared abstraction per concern" philosophy, and
317 landing first is the right sequencing — with the caveat above that 456 might be startable
slightly earlier than full 317 closure if the dedup lemma's shape is already frozen.

## Alignment and Sequencing Risks

- **File-scope collision with 557: none.** 317 touches only
  `Propositional/Tableau/{Intuitionistic,Minimal}/*`; 557 touches only `Modal/Tableau/*`. Safe
  to run concurrently as currently scoped.
- **Abstraction-philosophy collision with 557: none currently, but watch one thing.** 557's
  description explicitly forbids lifting its box-plus key abstraction into `Foundations/`, and
  its `RuleApplySt` generalization is Modal-driver-specific. If a FUTURE task ever proposes a
  truly generic tableau parameterization spanning Propositional + Modal + Temporal (beyond the
  `IntMinScheme` 2-instance case and beyond 456's containment-only generalization), it would need
  to reconcile with whatever module division 557 lands (its Phase "B. MODULE DIVISION" is
  explicitly not yet decided — "must be REVIEWED AND ACCEPTED in an explicit decision record
  before any file is moved or split"). That is a future risk, not a present one for 317.
- **The real sequencing risk is internal to 317's own task graph (430), not external to 557.**
  Two tasks (317, 430) have independently researched the same validity-bridge obligation. This
  is redundant research effort already spent (430's reports 01-03, 02 team research) that a
  tighter task graph would have avoided. Worth a note for future task-spawning: when a task's
  "remaining scope" description later expands to explicitly claim ownership of another task's
  target sorries (as 317's description does for 430's bridges), the dependent task should be
  re-evaluated for closure/merge at that point, not left dangling.
- **413's dependency edge may be artificially inflating wave sequencing.** If 413 never touches
  files in 317's file_scope, gating it behind 317's full completion may be delaying "Code
  Hygiene" work (wave 3) for no technical reason. Low confidence — flagged for the orchestrator
  to verify, not asserted as fact.

## Confidence Level

**Medium.** High confidence on the structural/dependency-graph claims (downstream task
descriptions, ROADMAP content, file-scope disjointness with 557, `IntMinScheme` already existing
in Scheme.lean — all read directly from source). Medium-to-low confidence on the one claim that
matters most (whether item (4)'s bridges are genuinely "assembly" or secretly require 430's
atom-persistence machinery), since verifying that would require reading live Lean proof state at
the sorry sites, which was out of scope for the Horizons angle and explicitly a proof-content
question better answered by whichever teammate is specifying the proof itself.
