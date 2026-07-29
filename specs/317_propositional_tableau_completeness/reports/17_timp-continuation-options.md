# T-implication Gap 1: Continuation Options Assessed (go/no-go)

- **Task**: 317 - propositional_tableau_completeness
- **Date**: 2026-07-28
- **Agent**: cslib-research-hard-agent (H2 anti-analysis, H3 reference grounding, H4 adversarial
  self-verification)
- **Focus**: blocker research — assess Options 1 (bounded copy channel), 2 (quotient/blocking
  frame), 3 (permanent deferral) for `truthLemma`'s T-implication `sorry`
  (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:602`)
- **Scope**: read-only against `Cslib/`. Zero files under `Cslib/` modified (verified: this
  dispatch issued no Write/Edit against that tree).
- **Repo state**: `683cb3e6` (main), working tree as at dispatch start.

**Sources/Inputs**
- `specs/317_propositional_tableau_completeness/handoffs/16_phase7-gap1-self-copy-removed.md`
- `specs/317_propositional_tableau_completeness/reports/13_blocker-root-cause-and-correct-approach.md`
- `specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md`
- `specs/574_tableau_calculus_repair_ancestor_blocking/reports/01_phase6-blocker-resolution.md`
- `specs/574_tableau_calculus_repair_ancestor_blocking/summaries/01_implementation-summary.md`
- `git show a70187dd` (full three-file diff, read directly)
- Live source: `Scheme.lean`, `Expansion.lean`, `Rules.lean`,
  `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`
- Literature: `chagrovzakharyaschev_1997_modallogic` chunk `0246` (read verbatim), `references.bib`

---

## Executive Verdict

**Option 1 — GO, in a specific reshaped form. Option 2 — NO-GO, with both an in-repo and a
published refutation. Option 3 — applies, but as bookkeeping for task 317 only; it is not a
substitute for the technical decision.**

Four findings drive this, in decreasing order of decision weight:

1. **Reintroducing the copy channel does not reopen the divergence — this is already measured,
   not speculated.** Task 574's own Phase 1 probe ran exactly this comparison. Its variant **V1**
   *is* "ancestor blocking with the self-copy channel retained"; **V3** is "V1 with the self-copy
   removed". Both terminate, and V3 reaches the *identical* saturated branch as V1
   (`len=219, maxLabel=21, distinctLabels=22`, stable across fuel 120/160/200/260 — four
   independent evaluations). All 19 conformance rows match under both
   (`handoffs/01_variant-selection.md`, Tables 3-4, verdict D3). **The algorithm in the tree
   today is exactly V3.** So Option 1's question (a) — "does the copy channel terminate?" — is
   already answered YES by the very probe that removed it. The probe Option 1 was said to need
   has already been run; only a re-confirmation against the post-Phase-6 tree is outstanding.

2. **But a bare revert of `a70187dd` does NOT close Gap 1, for a reason no prior artifact
   records.** `intExpandBranches_openBranch_sat` returns an **existentially quantified,
   invariant-side** edge list (`Scheme.lean:4807`, fed from `augSets` at `:4837`), *not* the
   algorithm's own `edgeSets`. That list carries the task-574 loop-back edges `(x, l)`
   (`Scheme.lean:726-751`). `truthLemma`'s frame is `intAccessPreorder edges` over **that
   augmented list**. The copy channel copies along the algorithm's **raw** edges only
   (`Expansion.lean`, `accessibleWorlds := … filter (isAccessible edges sf.label ·)`). The
   T-imp goal therefore quantifies over strictly more worlds than any copy channel can reach.
   **A loop-back transfer lemma is the real remaining obligation, and it is the gate.**

3. **Closing the T-imp `sorry` in isolation has zero public payoff.** Both public completeness
   theorems already carry their *own*, independent `sorry`s blocked on a *different* fact:
   `intuitionisticTableau_complete` (`Intuitionistic/Completeness.lean:133`) and
   `minimalTableau_complete` (`Minimal/Completeness.lean:125`) are blocked on
   `intExtractValuation` monotonicity along the frame, not on Gap 1. Discharging Gap 1 alone
   moves no public theorem from sorry-carrying to sorry-free. **Do not dispatch a T-imp-only
   phase.**

4. **Gap 1 and the monotonicity blocker are the same fact at two formula shapes.** Both are
   instances of *positive-formula persistence along the augmented accessibility relation*:
   `∀ φ w w', w ≤ w' → T(φ)@w ∈ b → T(φ)@w' ∈ b`. At `φ = atom p` it is the DP-3/DP-4
   monotonicity bridge (already an open task: **430**, `prove_atom_persistence_upward_closure_-
   for_intexpan`, status `planned`). At `φ = φ'→ψ'` it is Gap 1 — the copy at `w'` then lets the
   reflexive `sat_timp` field (`Scheme.lean:118-121`) fire at `w'`. `Scheme.lean:431-434` already
   recommends exactly this shape ("state monotonicity as a NEW field/hypothesis threaded
   alongside `sat_timp`").

**Recommended next action (named, concrete):** do **not** re-plan task 317 Phase 7. Instead
**widen task 430's scope** from atom-persistence to positive-formula-persistence along the
augmented relation, and give it the two-gate structure in §Recommendation below. Task 317's T-imp
`sorry` is then re-annotated as a strategic sorry with `follow_up_task: 430` — the same treatment
DP-2→585 and DP-3/DP-4→430 already receive. That is Option 3 as bookkeeping and Option 1 as the
technical route, in one move.

---

## Source-to-Implementation Mapping (H3, Tier 1)

BibKeys grepped against `references.bib` before citing.

| Source claim | BibKey | In `references.bib` | Lean/artifact target | Notes |
|---|---|---|---|---|
| A filtration relation `S` in the interval `S̲ ⊆ S ⊆ S̄` "may be nontransitive even if the original `R` is transitive … not all `S` in this interval give rise to filtrations of intuitionistic models" | `ChagrovZakharyaschev1997` | Yes, `:75` | Refutes Option 2's `intAccessPreorderQ`-style pullback | Read verbatim: `Literature/sources/chagrovzakharyaschev_1997_modallogic/chunk_0246.md:63-65`, §"THE FILTRATION METHOD", immediately after Thm 5.23's interval discussion. OCR is noisy (`S̲`/`S̄` render as `5`/`S`); the operative sentence is legible and unambiguous |
| Countermodel construction `M ∪ C`, `C = {x ≤ y | Sfor(x) ⊆ Sfor(y)}`; authors report inability to find a filtration on ⪯∩⪰ equivalence classes | `GargGenoveseNegri2012` | Yes, `:239` (D3 from report 13 has since been fixed) | `Scheme.lean:740-751` `augSets` loop-back edges — **landed** | Quote relayed from `574/reports/01`; I did **not** re-read GGN itself (not in corpus). Marked `[UNVERIFIED — second-hand]` |
| Intuitionistic tableaux, `T(φ→ψ)` split, loop-check | `Fitting1983` Ch. 4 | Yes, `:211` | `sat_timp` field shape, `Scheme.lean:115-121` | Cited by existing docstrings |
| Contraction-free G4ip/LJT | `Dyckhoff1992` | Yes, `:218` (D4 fixed) | — | Report 13's defects D3/D4 are both resolved in the current tree |

**Corpus caveat**: the per-repo literature briefing carries a provenance banner; the specific
C&Z chunk consulted reports `provenance_fidelity: verified_conversion`, which is the stronger
tier, but the OCR quality is visibly degraded and the citation should be re-checked against a
physical copy before it appears in a Lean docstring.

---

## Findings

### F1. The copy channel is termination-orthogonal under ancestor blocking — measured

`handoffs/01_variant-selection.md` Table 3:

| Variant | fuel 120 | 160 | 200 | 260 | Terminates? |
|---|---|---|---|---|---|
| V1 = ancestor blocking, `F(ψ)@x` retained, **self-copy retained** | 21 | 21 | 21 | 21 | YES |
| V3 = V1 **+ self-copy removed** | 21 | 21 | — | 21 | YES, identical branch to V1 |

Verdict D3 in that handoff: *"Removing the self-copy channel changes nothing about the
termination outcome once ancestor blocking is active."* The removal commit's own message says
the same (`git show a70187dd`, commit body: "the self-copy is orthogonal hygiene, not the
termination mechanism"). Table 4: all 19 conformance formulas match under V1, V2 and V3 —
zero completeness regression under any of them.

**Consequence for Option 1's question (a):** answered YES, by measurement, before the channel was
ever removed. The framing in `handoffs/16` ("would need its own divergence probe before being
trusted") is over-cautious: the probe exists and its V1 row *is* the bounded-copy configuration.

### F2. Reinstatement is a mechanical revert, not a redesign

`git show a70187dd` touches three `Cslib/` files:
- `Expansion.lean`: deletes the `accessibleWorlds`/`copies`/`combined` block (−9 lines of code
  plus a docstring rewrite). Reinstating is a literal restoration.
- `Scheme.lean` (156 lines): every hunk is a `rfl`-level pattern-match repair —
  `ILabelBound_applyAllTImpRules`, `applyAllTImpRules_subset`, `applyAllTImpRules_count_drop`,
  `applyPersistenceFixpoint_genuine_of_count_le_fuel` — plus deletion of the now-dead helper
  `applyAllTImpRules_copy_notMem` (which the diff preserves in full and which would be restored
  verbatim).
- `Soundness.lean` (112 lines): `applyAllTImpRules_sat`, `freshAbove_applyAllTImpRules`.

All three pre-removal versions were green at the parent commit. **This is low-risk mechanical
work, not the calculus redesign report 13 costed.**

### F3. The real gap: raw edges vs. augmented edges [DECISIVE, and not previously recorded]

`intExpandBranches_openBranch_sat`'s conclusion (`Scheme.lean:4807`):

```lean
∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b
```

The witness is `augSets` (`:4795`, threaded to the `key` invocation at `:4837`), which task 574's
Phase 6 introduced explicitly *decoupled from the algorithm's own edge list*
(`Scheme.lean:740-751`; `574/reports/01` Executive Verdict: *"The lemma is therefore free to
return an edge list that is not the one the algorithm accumulated."*). `augSets` gains a loop-back
edge `(x, l)` at every ancestor-blocking event.

`truthLemma` takes that `edges` and installs `intAccessPreorder edges` as its `Preorder Nat`
(`Scheme.lean:559-569`). So the T-imp goal's `∀ w', w ≤ w' → …` ranges over the **reflexive-
transitive closure of the augmented relation**. The copy channel, by contrast, filters on
`isAccessible edges sf.label ·` where `edges` is the algorithm's raw list. **Strictly weaker.**

The bridge is available *in principle*: a loop-back edge `(x, l)` is recorded only when
`Sfor`-containment `posFormulasAt bPers l ⊆ posFormulasAt bPers x` holds, and per
`Scheme.lean:742-744` ancestor persistence supplies the converse, so `x` and `l` carry the same
positive formulas — `T(φ→ψ)` among them. **But the containment is established against `bPers`
(the branch at blocking time), not the final branch `b`, and it is consumed locally at the
discharge site rather than exported.** Whether it survives to the final branch is the single
largest unretired risk. `[UNVERIFIED — no Lean prototype attempted this dispatch]`

### F4. The "fuel entanglement" half of Gap 1 is already retired

The STOP-gate note's Gap 1 has two halves: (i) fuel sufficiency for a *genuine*
`applyAllTImpRules` fixpoint, (ii) the copy actually reaching `w'`.

Half (i) is **landed and sorry-free**: `applyPersistenceFixpoint_genuine_of_count_le_fuel`
(`Scheme.lean:3495-3500`), retargeted over the enlarged universe `intUniverseExt φ0`
(`:2068`), with `intUniverseExt_length_le` (`:2077`) sized against the post-blocking world bound
`WBound φ0`. The `hb : ∀ x ∈ b, x ∈ intUniverseExt φ0` premise is threaded as `IAllUniv`
(`Scheme.lean:4802`). The only hole on that side is **DP-2** (`intFreshMint_preserves_nw`,
`:2566`, owned by task 585).

Report 13's F2/F3 ("no world bound of any size exists") was measured against the **pre-repair**
calculus and is superseded on this point: under ancestor blocking the witness saturates at
`maxLabel=21` and `WBound φ0` is a proved bound modulo DP-2.

### F5. What `propagatePersistence` already gives, and exactly what is missing

`intFImpRule` (`Rules.lean:159-164`) calls `propagatePersistence` (`:144-146`), which copies
**every** positive formula from `w` to the fresh child `w'` at creation time. So a child created
*after* `T(φ→ψ)@w` arrived already carries its copy — no channel needed.

The hole is exactly: **positive formulas arriving at `w` after `w'` was already minted.** Nothing
in the current calculus re-propagates them. The self-copy channel filled that hole for
implication-shaped formulas only; `applyAllTImpRules`'s surviving `intTImpRule` half fills it for
`T(ψ)`-consequences only.

This also explains why the atom-monotonicity task (430) is blocked: `T(atom p)@w` arriving late
(via a `T(φ→p)`-triggered `intTImpRule` firing) never reaches an older child.
`Scheme.lean:413-420` records the same diagnosis and calls it a "co-inductive dependency on
formula complexity resolved only by REPEATED `applyPersistenceFixpoint` passes".

### F6. Option 2 has both an in-repo and a published refutation

Task 574 **built** the quotient stack and then **refuted and deleted** it:
- Phase 5 (`b70eadc0`…`1ebf52ad`): ~480 lines — `intBlockRep`, `intAccessPreorderQ`, the
  `*Q`-suffixed predicate stack. All four sub-phases landed green.
- Phase 6 blocker research (`5c0db5aa`): the stack cannot carry
  `intExpandBranches_openBranch_sat`'s **forward** induction, because `intBlockRep` is a function
  of the **final** branch and is not monotone under branch growth. A second independent defect in
  `intBlockRep` was found in passing (`574/reports/01` §Secondary Defect).
- Phase 7 (`175f7ea6`): the ~480 lines were deleted, grep-confirmed zero external references.

The replacement — GGN's `M ∪ C` loop-back-edge construction — **is what is in the tree today**.
Rebuilding a quotient would relitigate a settled, measured, prototyped-and-refuted design and
would have to displace working machinery.

The refutation transfers to the T-imp case specifically. `truthLemma` itself runs over the final
branch, so a quotient *could* be defined there — but `IBranchSaturation`/`IFimpAccess`, which
`truthLemma` consumes, are produced by the forward induction, which is precisely where the
obstruction bites.

Independent literature confirmation, read verbatim this dispatch
(`chunk_0246.md:63-65`, `ChagrovZakharyaschev1997`, §The Filtration Method):

> "It is to be noted that a relation S between S̲ and S̄ may be nontransitive even if the
> original R is transitive, in particular, not all S in this interval give rise to filtrations of
> intuitionistic models."

That is exactly the assumption an `intAccessPreorderQ` pullback rests on. Plus GGN's own reported
inability to find such a filtration (`[UNVERIFIED — second-hand via 574/reports/01]`).

**Scope if pursued anyway**: ≥480 lines to rebuild, plus restating `sat_fimp`/`sat_timp` and
`IFimpAccess` over the quotient, plus re-proving the forward induction under a non-monotone
representative map (the recorded blocker). Estimate 800-1500 lines with a known-failed precedent.
**It does not sidestep the `Force → T(_)@w' ∈ b` gap — it relocates it**, because the quotient
still has to supply the copy (or the disjunction) at the quotient representative, by the same
persistence argument Option 1 makes directly.

### F7. Option 3 does not misrepresent the library — but it also decides nothing

Checked directly:
- `truthLemma`'s only consumers are `Intuitionistic/Completeness.lean` and
  `Minimal/Completeness.lean` (grep across `Cslib/`, `CslibTests/`). The Bimodal and Modal
  `truthLemma`s are unrelated declarations in different namespaces.
- Both consumers already carry their own `sorry` (`:133` and `:125` respectively), blocked on
  valuation monotonicity — **independent of Gap 1**.
- `Metalogic/IntDecidability.lean:321` states explicitly that the FMP route deliberately does not
  thread through the parametric `truthLemma` sorry. Report 13 F8's `lean_verify` axiom profile for
  `decidableDerivableIntPropAxiomFMP` (`{propext, Classical.choice, Quot.sound}`, no `sorryAx`)
  is therefore unaffected either way. `[UNVERIFIED this dispatch — I did not re-run lean_verify;
  relied on report 13's recorded result]`

So deferring the T-imp sorry leaves nothing overclaimed: no public theorem changes status, and
the file's own docstrings already record the gap in detail. The precedent (DP-2→585,
DP-3/DP-4→430) is exactly applicable.

**But**: because of F3 and the F7 finding that the public theorems are blocked elsewhere, Option 3
taken *alone* would leave the tableau-completeness programme with no live critical path. It is
the right bookkeeping decision, not the right technical one.

### F8. Report 13's cost estimate is now substantially stale

Report 13's Option A had five steps and a 2500-4000 line estimate. Steps 1-3 (bound/remove the
copy channel; ancestor-directed blocking check; restate `sat_fimp` over a non-raw-`Nat`
accessibility) were **all delivered by task 574**. Step 4 (the world bound via `geomCap`-shaped
machinery) is largely delivered as `WBound`/`intUniverseExt`/`intWork` modulo DP-2. What remains
is step 5 plus the persistence invariant this report identifies. **The honest remaining cost is
roughly 600-1200 lines, not 2500-4000.** `[Low confidence — anchored on the ~480-line quotient
stack and the ~92-line Phase 6 prototype as the reference class]`

---

## Recommendation

**GO on Option 1, reshaped and merged into task 430.** Concretely:

### Immediate (task 317, one dispatch, no `Cslib/` proof work)
Re-annotate the T-imp `sorry` at `Scheme.lean:602` as a **strategic sorry with
`follow_up_task: 430`**, and correct the STOP-gate note's "Recommendation for continuation"
paragraph (`Scheme.lean:526-536`) with F1 and F3 — specifically that (i) the probe Option (a)
asks for has already been run and V1 terminates, and (ii) the real gap is raw-vs-augmented edges,
not the copy channel per se. Leave Phase 7 `[BLOCKED]`, close task 317's remaining phases against
the tracked follow-ups. **This is the only action task 317 should take.**

### Task 430, widened scope: "positive-formula persistence along the augmented relation"

Two hard gates, in this order. **Gate B before any algorithm change** — it is the one that can
kill the option, and it can be attempted against the tree exactly as it stands.

- **Gate A (probe, ~1 dispatch).** Re-run `574/handoffs/01_variant-selection.md`'s methodology
  against the *post-Phase-6* tree for two variants: **V1** (self-copy reinstated verbatim) and
  **V4** (generalize the channel to copy *every* positive formula, not just `T(φ→ψ)`, to
  accessible worlds lacking it). Must show: saturation on `φ0` at `fuel ≥ 120`, and all 20
  `TableauConformance.lean` propositional rows matching. V4 is the higher-value target — it makes
  the persistence invariant hold at *all* formula shapes in one step, closing Gap 1, DP-3 and
  DP-4 together — and it cannot create worlds directly (only `F(φ→ψ)` mints worlds), though it
  can feed `intApplyRuleFull`'s `.pos,.imp` BETA arm indirectly, which is why it needs the probe.
  Fall back to V1 if V4 diverges.
- **Gate B (Lean prototype, ~1 dispatch, GATING).** Without changing any algorithm, prototype:
  ```
  ∀ φ w w', isAccessible augEdges w w' = true → T(φ)@w ∈ b → T(φ)@w' ∈ b
  ```
  restricted to a **single loop-back hop** `(x, l)`, using the `Sfor`-containment available at the
  blocking site, and check it survives to the *final* branch (F3's risk). Follow 574's own
  successful methodology: prototype in `scratch/`, `lake build` green, then decide.
  **If Gate B fails, Option 1 collapses and Option 3 becomes the terminal answer** — say so
  explicitly rather than escalating to Option 2.
- **Then** (≈4 phases): revert `a70187dd`'s three hunks (F2, mechanical); prove copy-completeness
  at a genuine `applyAllTImpRules` fixpoint over raw edges (the `filterMap`/`countP` argument the
  STOP-gate note already sketches at `Scheme.lean:508-513`, mirroring the landed
  `applyAllTImpRules_count_drop`); thread the containment invariant alongside `IAllAccessConsistent`
  and export it in `openBranch_sat`'s conclusion; discharge the T-imp case and instantiate at
  atoms for DP-3/DP-4.

**Does this re-open task 574's settled design?** No — and this matters for the go/no-go. Task 574
settled *termination* (ancestor blocking is the mechanism) and *the reuse-witness admissibility
route* (loop-back edges, not quotient). Reinstating the copy channel contradicts neither: 574's
own D3 verdict records the channel as termination-**orthogonal**, and its removal is described in
its own commit message as "hygiene", explicitly scoped as not addressing Gap 1. This is a
coordinated follow-up, not a reversal. It should still be raised with task 574's record as a
cross-reference, and Gate A is what makes it non-speculative.

**Zero-debt compliance**: no recommendation above defers a `sorry` as a means of *progress*.
Option 3 is recommended only as the accurate status label for a gap owned by a named follow-up
task, matching the existing DP-2/DP-3/DP-4 treatment; no statement is weakened, no axiom
introduced, and no sorry is relocated to manufacture a count decrease.

---

## Risks & Mitigations

| Risk | Mitigation |
|---|---|
| **F3's loop-back transfer fails on the final branch** (the option-killer) | Gate B, run before any algorithm change and before any revert. Cheap: statable against the current tree |
| V4 diverges where V1 does not | Gate A measures both; V1 is the pre-measured fallback |
| Reverting `a70187dd` breaks `Soundness.lean`'s acceptance gate | The pre-removal versions were green at `a70187dd^`; re-verify `intExpandBranches_closed_unsat` sorry-free and axiom-clean at each phase boundary, as task 574 did |
| DP-2 (task 585) still gates `applyPersistenceFixpoint_genuine_of_count_le_fuel`'s `hb` premise in practice | Sequence 585 ahead of, or parallel to, the final discharge phase; the fixpoint lemma itself is already sorry-free |
| `TableauConformance.lean`'s 20 propositional rows shift under V1/V4 | Gate A checks all 20 before any `Cslib/` write; 574 measured zero regression for V1 |
| C&Z citation rests on degraded OCR | Re-check against a physical copy before it appears in any Lean docstring; the Option 2 no-go does not depend on it alone (the in-repo refutation is independent) |

---

## Adversarial Self-Verification (H4)

| # | Claim under attack | Source / counterexample | Outcome |
|---|---|---|---|
| 1 | *"Reinstating the copy channel reopens the divergence"* (the premise of `handoffs/16`'s caution and of the STOP-gate note's option (a)) | `574/handoffs/01_variant-selection.md` Table 3: V1 (self-copy **retained**) saturates at `maxLabel=21` across fuel 120/160/200/260; V3 (removed) reaches the identical branch. Verdict D3 states removal is orthogonal | **Refuted.** The caution is over-stated; the probe already exists |
| 2 | *"So a bare `git revert a70187dd` closes Gap 1"* — my own first conclusion | `Scheme.lean:4807` + `:4837` return `augSets`, not `edgeSets`; design note `:740-751` says the two are decoupled. The copy channel filters on the raw list | **Refuted my own conclusion.** Recommendation revised to add Gate B; this is now the report's load-bearing finding |
| 3 | *"The quotient refutation was about `openBranch_sat`, so it may not bind `truthLemma`"* | `truthLemma` consumes `IBranchSaturation`/`IFimpAccess`, both produced by the forward induction where `intBlockRep`'s non-monotonicity bites (`574/reports/01`) | **Not refuted — the objection fails.** Option 2 stays NO-GO |
| 4 | *"Report 13 refuted any world bound, so F4's fuel-sufficiency claim is dead"* | Report 13 F1/F2 measured the **pre-repair** calculus. Post-repair, `WBound φ0` / `intUniverseExt` exist and `applyPersistenceFixpoint_genuine_of_count_le_fuel` (`Scheme.lean:3495`) is landed sorry-free over them | **Superseded, not contradicted.** Report 13 is correct about the calculus it measured |
| 5 | *"Gap 1 and monotonicity are unrelated; unifying them is my invention"* | `Scheme.lean:431-434` already recommends "state monotonicity as a NEW field/hypothesis threaded alongside `sat_timp`"; task 430's own name is `prove_atom_persistence_upward_closure_for_intexpan` | **Not refuted — the unification is pre-recorded in-file, not invented here** |
| 6 | *"Closing T-imp makes a public theorem sorry-free"* | `Intuitionistic/Completeness.lean:133` and `Minimal/Completeness.lean:125` carry independent sorries blocked on monotonicity | **Refuted.** This is why the report recommends against a T-imp-only phase |
| 7 | *"V4 (copy all positive formulas) obviously terminates since positives don't mint worlds"* | Positives feed `intApplyRuleFull`'s `.pos,.imp` BETA arm, which yields `F(antecedent)@w'` — a negative that *does* mint. This is the original divergence feed | **Not refuted — my own reasoning was too quick.** V4 is therefore gated behind Gate A, not asserted safe |
| 8 | *"The C&Z quote is second-hand from 574's report"* | Read verbatim this dispatch at `Literature/sources/chagrovzakharyaschev_1997_modallogic/chunk_0246.md:63-65` | **Refuted — now first-hand.** The GGN quote remains second-hand and is marked `[UNVERIFIED]` |

**Confidence levels**
- *High (verified against live source or a recorded measurement this dispatch):* F1 (574 Table 3),
  F2 (`git show a70187dd`), F3's mechanism (`Scheme.lean:4795/4807/4837/740-751`), F4
  (`Scheme.lean:3495`), F5 (`Rules.lean:144-164`), F6's in-repo refutation (574 phase commits),
  F7's consumer graph (grep).
- *Medium (design judgement, not prototyped):* the loop-back transfer bridge is *available in
  principle* from `Sfor`-containment. Gate B exists precisely because I did not verify it.
- *Low, flagged not asserted:* F8's 600-1200 line estimate; V4's termination.
- *Second-hand, marked in text:* GGN's self-reported filtration failure; report 13's
  `lean_verify` FMP axiom profile.

**BibKey verification**: `ChagrovZakharyaschev1997` (`:75`), `Fitting1983` (`:211`),
`Dyckhoff1992` (`:218`), `GargGenoveseNegri2012` (`:239`), `NegriVonPlato2001` (`:944`) — all
confirmed present by grep. Report 13's defects D3/D4 (then-dangling `GargGenoveseNegri2012` and
`Dyckhoff`) are **resolved** in the current tree.

**Reuse check (CSLib protocol)**: no new abstraction is proposed. The recommendation reuses the
existing `IAllAccessConsistent`/`augSets` threading pattern (`Scheme.lean:756-799`), the landed
`applyPersistenceFixpoint_genuine_of_count_le_fuel`, `intUniverseExt`/`WBound`, and task 574's own
probe harness methodology. `Foundations/Logic/Tableau/` was checked for a persistence abstraction:
none exists; none is proposed, since the invariant is branch-and-edge-specific.

**H2 compliance**: this dispatch produced a decision with a named next action and two falsifiable
gates, not a survey. The two options the mandate framed as open are resolved in opposite
directions on measured evidence, and the option I recommend is qualified by a gate that can kill
it.
