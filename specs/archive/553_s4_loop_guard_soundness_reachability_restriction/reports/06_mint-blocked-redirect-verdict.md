# Research Report: The Mint-Blocked (Redirect) Case of the S4-Keyed Ordered Step Lemma

- **Task**: 553 (`s4_loop_guard_soundness_reachability_restriction`)
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Report**: 06 (targeted single-blocker research dispatch)
- **Date**: 2026-08-05
- **Session**: sess_1785956924_4d73af
- **Question**: Can the fifth case-split arm of Phase 7's bespoke step-preservation lemma —
  mint-blocked (redirect) — be closed, and if so how?

## Verdict (summary)

**NO-GO on the step lemma as currently stated; CONDITIONAL GO on a reformulated step lemma
that changes only the proof architecture, not one line of the driver, guard, or termination
track.**

- The literal per-step statement — preserve `branchSatisfiableIn s4FC` verbatim, with the
  model realizing **every** recorded `acc` edge including the new redirect edge — is not
  closable from any invariant that is initializable at an arbitrary countermodel. Both known
  route families (rebuild-canonical / extend-ambient) are exhausted for structural reasons
  set out in §2, not for want of lemma-chaining. The two burned implementation dispatches
  were not near-misses.
- The way out is a **reformulated conserved predicate** (`S4RedirectSoundInv`, §3) in which
  redirect edges are quarantined from the semantic edge-realization conjunct and justified
  **syntactically** by payload absorption — facts that are *already landed sorry-free* as the
  four free-transfer lemmas plus `modalStepBranchS4Keyed_blocked_witness_mem`
  (`LoopChecking.lean:9424-9548`, `:9989`). Under this predicate the mint-blocked arm closes
  with **no model construction at all**, and the four landed arms survive with mechanical
  restatements (§3.4).
- This reformulation is the Lean-side restoration of exactly the soundness/completeness
  separation Massacci's subtractive blocking has natively (§4): blocking must be invisible to
  the soundness argument; only completeness may consume the loop-back. CSLib's additive edge
  stays in the driver (completeness needs it, and plan 07's Phases 1-6 already justified it
  there); the *soundness proof* simply stops pretending the redirect edge is a semantic edge.
- **Termination impact: zero** (§5). Nothing definitional changes. By contrast, every
  guard-narrowing fix (ancestor-only redirect, live-set comparison) hits the standing
  world-bound warning head-on.

Named cheap-to-test preconditions for the CONDITIONAL GO are in §6. Failure of probe P2 is
the kill criterion; the fallback is then a genuine NO-GO whose minimal architectural change
is also recorded there.

## 1. Verified state of the obstruction (checked against code, not prose)

Confirmed by direct inspection this dispatch (all line numbers re-verified):

1. The blocked arm is `(.linear [], acc.addEdge sf.label wBlock)` — branch unchanged, one new
   edge (`modalApplyOneS4Keyed`, `LoopChecking.lean:1075-1087`). The per-step obligation for
   this arm is therefore exactly: `branchSatisfiableIn s4FC b acc →
   branchSatisfiableIn s4FC b (acc.addEdge src wBlock)` under settledness + `S4LoopInv` +
   `S4KeyedHintikkaInv`.
2. `branchSatisfiableIn` (`FrameSoundness.lean:112-120`) demands the model realize **every**
   recorded edge: `∀ w w', acc.hasEdge w w' → m.r (f w) (f w')`. This conjunct is the entire
   problem: it turns a bookkeeping edge into a semantic commitment at step time.
3. The capstone `branchSatisfiableIn_s4FC_addEdge_of_blocked`
   (`FrameCompleteness.lean:4358-4385`) discards the ambient model and rebuilds via
   `extractModelS4` + `modalTruthLemmaS4`; it consumes `modalHintikkaSetS4 φ₀ b acc`, whose
   conjuncts 3/4 (`LoopChecking.lean:7122-7127`) require **every** mint-shaped formula on the
   branch to have a witness successor. Settledness (`modalNonMintCandidates = []`,
   `LoopChecking.lean:1205-1211`) guarantees only non-minting exhaustion; unwitnessed sibling
   mint shapes are consistent with it. Gate B's `modalS4Saturated_of_ordered_settled`
   (`LoopChecking.lean:9246`) recovers conjunct 2 at settled states — but nothing recovers
   conjuncts 3/4, and nothing can: they are false at typical mint-ready states.
4. `blockingWorldS4Keyed` (`LoopChecking.lean:655-660`) selects `wBlock` by recorded-key
   equality with `successorBirthContent` — purely syntactic, no reachability constraint of
   any kind (the docstring's own "No reachability restriction" defect note,
   `LoopChecking.lean:640-646`).

The handoff's dead-end analysis (`handoffs/plan07-phase7-handoff-20260805c.md`) is accurate
on every point checked. It was verified, not re-derived.

## 2. Why the statement as stated cannot close (answer to Q1, negative half)

Any invariant `I` threaded through the fuel induction must satisfy:

- **(Init)** `I` holds at `([F(φ₀)@0], e=[], acc=∅, keys=[(0,∅)])` for an **arbitrary** S4
  countermodel of `φ₀` — soundness quantifies over all models, so `I`'s semantic content at
  initialization is at most "some model satisfies the branch".
- **(Blocked)** At a blocked step, `I` must yield a model realizing
  `m.r (f src) (f wBlock)` where `wBlock` was chosen by recorded-key equality.

These are jointly unsatisfiable for any `I` retaining the full edge-realization conjunct:

1. **No valuation-level invariant can force a relation.** Every candidate of the form "the
   model satisfies such-and-such formulas at `f wBlock`" (e.g. key-content satisfaction,
   which is already implied by `keyLowerBd` + branch satisfaction) is compatible with
   `f src` and `f wBlock` being relationally incomparable. Kripke edges are not determined
   by valuations. So the needed edge must either be *in the given model already* — which
   (Init) forbids demanding, since the future match event (`birthContent` growing into key
   equality) is not predictable at initialization and arises at box-arrival steps where the
   same unprovable edge obligation would merely relocate — or be *manufactured*.
2. **Manufacturing the edge means relation surgery, and relation surgery needs a truth
   lemma.** Modifying `m.r` (adding the edge, taking closures, or shrinking to a generated
   sub-relation à la C&Z Theorem 5.51) changes the satisfaction of every **nested** modal
   subformula at every existing world. Re-establishing `∀ sf ∈ b` satisfaction after surgery
   is precisely a truth-lemma obligation, and the branch is not Hintikka-saturated at a
   settled state (conjuncts 3/4 absent). This is not merely "unproved": at a state with a
   genuinely unwitnessed sibling `F(□χ)@u`, `extractModelS4` makes `□χ` true at `u` whenever
   no `¬χ`-world lies in `u`'s recorded cone, so the rebuild route's target statement is
   *false* as a uniform construction, not just out of reach.
3. **The C&Z containment pattern confirms which hypothesis is load-bearing.** Theorem 5.51's
   selective filtration (ChagrovZakharyaschev1997, chunk_0267) builds `Vₙ ⊆ W`, `Sₙ ⊆ R` —
   every generated edge is **contained in the ambient relation** because each successor
   `y(x, □ψ)` is *chosen from the ambient model* (Lemma 5.50). Box discharge across the
   generated relation flows through that containment. The keyed redirect target is chosen
   syntactically, so containment is exactly what it lacks; the interval theorem's
   nontransitivity warning (chunk_0246 L43-65) marks the same boundary from the filtration
   side. The literature pattern that *does* work — pick witnesses from the ambient model —
   is the mint-unblocked arm's landed pattern, and it is constitutively unavailable for a
   pre-chosen loop-back target.

Whether the bare mathematical implication "`b` satisfiable ∧ settled ∧ key-match ⇒ `b` +
redirect edge satisfiable" is *true* remains open (no counterexample was found; over states
actually reachable by the ordered driver it is plausibly true, for the frozenness reasons in
§3.3). But its per-step *proof* would require importing reachability facts into the
invariant — which is precisely the reformulation below, and once those facts are available
the edge-realizing formulation is no longer needed by anything. Do not re-attempt either
catalogued route against the current statement.

## 3. The reformulated decomposition (answer to Q2, and Q1's positive half)

### 3.1 Design principle

Massacci-style blocking is sound because the soundness argument never sees it (§4). CSLib's
redirect edge must stay in `acc` — plan 07's completeness track (Phases 1-6, all landed)
consumes it there via `modalHintikkaSetS4_addEdge_of_blocked` and `extractModelS4`. The
change is confined to the **soundness induction's conserved predicate**: stop requiring the
model to realize redirect edges, and instead carry the syntactic fact that redirect edges
never transmit anything the branch does not already contain.

### 3.2 The conserved predicate

```lean
/-- Ghost decomposition: E_r is the (proof-level) set of redirect-created edges.
    Never computed by the driver; produced by the step lemma itself. -/
def S4RedirectSoundInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex)) : Prop :=
  -- (a) every ghost edge is a recorded edge
  (∀ p ∈ Er, acc.hasEdge p.1 p.2 = true) ∧
  -- (b) SEMANTIC conjunct, weakened: model realizes only NON-redirect edges
  (∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W),
     s4FC m.r ∧
     (∀ w w', acc.hasEdge w w' → (w, w') ∈ Er ∨ m.r (f w) (f w')) ∧
     ∀ sf ∈ b, sfSat m f sf) ∧              -- same satisfaction clause as today
  -- (c) SYNTACTIC absorption: redirect payloads are already on the branch
  (∀ p ∈ Er, ∀ χ,
     ((⟨.pos, .box χ, p.1⟩ ∈ b → (⟨.pos, χ, p.2⟩ ∈ b ∧ ⟨.pos, .box χ, p.2⟩ ∈ b)) ∧
      (⟨.neg, .diamond χ, p.1⟩ ∈ b → (⟨.neg, χ, p.2⟩ ∈ b ∧ ⟨.neg, .diamond χ, p.2⟩ ∈ b)))) ∧
  -- (d) frozenness protection: out-edged worlds are exhausted for non-mint shapes
  (∀ sf ∈ b, modalMintShape sf = false → outDeg acc sf.label ≠ 0 →
     sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable)
```

Step lemma shape: if `S4RedirectSoundInv φ₀ b e acc keys Er` and
`modalStepBranchS4KeyedOrdered` fires producing `(b', e', acc', keys')` (per selected branch
of the result), then `∃ Er' ⊇ Er, S4RedirectSoundInv φ₀ b' e' acc' keys' Er'`.

Terminal payoff: conjunct (b)'s satisfaction clause alone contradicts `isModalClosed b =
true` — `modalClosed_unsatIn`'s proof (`FrameSoundness.lean:141-146`) never touches the edge
conjunct, so the closed-branch contradiction is unaffected by the weakening.
Initialization: `Er = []`, arbitrary countermodel; (c) and (d) vacuous ((d) because
`acc = ∅`).

### 3.3 Why the mint-blocked arm now closes — with already-landed lemmas

At a blocked step (`src`, `wBlock`, `hblock`), take `Er' = (src, wBlock) :: Er`:

- **(a)**: `hasEdge_addEdge_self_gate0`-style fact, trivial.
- **(b)**: the **identical** model witnesses it — no extension, no surgery. The new edge is
  discharged by the `∈ Er'` disjunct; old edges unchanged. This is the arm's entire semantic
  content: nothing.
- **(c) for the new edge**: exactly the four landed free transfers —
  `blockedRedirect_boxed_boxPos_mem` / `blockedRedirect_unwrapped_boxPos_mem` /
  `blockedRedirect_boxed_diaNeg_mem` / `blockedRedirect_unwrapped_diaNeg_mem`
  (`LoopChecking.lean:9424-9548`; sorry-free, standard axioms, derived from `keyLowerBd` +
  `blockingWorldS4Keyed_eq_birthContent` alone). The relevance side-conditions
  (`(s,χ) ∈ signedSubfmls φ₀`) are supplied by `S4LoopInv.bClosure`. (c) for old edges: `b`
  unchanged, inherited.
- **(d)**: `src` may be newly out-edged; settledness at the fire moment
  (`modalStepBranchS4KeyedOrdered_mintReady`, `LoopChecking.lean:1542` +
  `modalNonMintCandidates_eq_nil_iff`, `:1237`) gives global exhaustion, which implies (d)
  for every world. The only delta between `acc` and `acc' = acc.addEdge src wBlock` that
  could re-awaken an inert persistent rule is the new successor `wBlock` of `src` — and its
  payload is already on `b` by (c), so inertness is preserved (this is the one small new
  lemma this arm needs: "persistent applicability is unchanged by adding an edge whose
  payload is already present").

No `modalHintikkaSetS4`, no model rebuild, no witness for sibling mints — the full-branch
saturation requirement is gone because the arm no longer *claims* anything semantic about
the redirect edge. That claim is made exactly once, terminally, by the already-landed
completeness capstone, where full saturation is legitimately available.

### 3.4 The other four arms under the new predicate (the delegation's explicit cross-check)

An invariant that closes this case but breaks the landed four would be worthless; walked
arm-by-arm:

| Arm | (b) semantic | (c) absorption | (d) exhaustion |
|---|---|---|---|
| Propositional (`modalApplyOneS4Keyed_notBoxDia_sat`) | Landed proof reused verbatim — it never consumes edge realization; weaker hypothesis suffices | New formulas land at the fired label `u₀`; by (d), an applicable non-mint, non-expanded formula forces `outDeg acc u₀ = 0`, so `u₀` has no outgoing edges and is not a redirect source — (c) untouched | Needs the *antitone-applicability* family: growing `b` (at fixed `acc`) never turns `.notApplicable` into applicable (rule outputs are filtered against `b`; presence is monotone). Probe P2, §6 |
| Mint-unblocked ×2 (`_boxNeg_mint_sat` / `_diaPos_mint_sat`) | Landed pointwise-extension proof reused; the new mint edge is realized by construction; old redirect edges are now *exempt*, strictly easier | New formulas only at the fresh label `modalNextWorld b` (`accFresh` ⇒ never a redirect source/target in `Er`) | `w` newly out-edged: settledness at fire moment (same `mintReady` fact). New edge's payload ⊆ seed: `modalApplyOneS4KeyedMint`'s payload is by design the same `successorBirthContent` data (K unwrapped + `boxPlusExtraS4` boxed) — probe P3 |
| 4-rule box-positive / diamond-negative (`_boxPos_sat` / `_diaNeg_sat`) | Restated with a per-successor disjunction: successor via non-redirect edge → landed one-hop `IsTrans` proof; successor via `Er` edge → output already `∈ b` by (c), satisfaction free from the branch clause, and `nf ⊆ b` cases are absorbed by dedup | Output lands at successors — for an `Er`-successor it is already present, so no *new* formula appears at any redirect source; for a fresh-mint successor, not a redirect source | Under (d), a persistent rule at an out-edged world is inert, so this arm fires only where the T-self layer has local work (`T(ψ)@w` at a world with `outDeg = 0`) or not at all; either way (d) is preserved because outputs stay at non-out-edged labels |

The landed lemmas' semantic cores are all reused; the restatements replace the blanket
edge-realization hypothesis with the `(w,w') ∈ Er ∨ realized` disjunction and add the
syntactic discharge for the `Er` branch. Nothing landed has to be *re-proved*, only
*re-wrapped* — the same relationship the fourth dispatch found between the private
`.fst`-closed-forms and the new soundness compositions.

### 3.5 Why (d) is the honest crux — and why it is true for this driver

Absorption (c) is stable only because a redirect source's box set never grows after its
out-edges exist. That is a *reachability* fact about the ordered driver — worlds acquire
out-edges only at globally settled moments (`mintReady`), fresh-world bursts are label-local
(fresh worlds have no out-edges until they themselves mint), redirect payloads are
pre-absorbed (free transfers), and mint payloads are pre-seeded (`boxPlusExtraS4`). The
ordering discipline was *built* to make this true (the module note at
`LoopChecking.lean:1135-1158` says as much for the staleness defect); conjunct (d) is the
first formulation that imports that discipline into the soundness invariant, which is
exactly what §2 showed any successful invariant must do. Note `S4LoopInv.outDegEq`
(`LoopChecking.lean:7686`) already ties `outDeg` to expanded mint counts — useful for (d)'s
bookkeeping.

## 4. Literature grounding

**Massacci2000** (Single Step Tableaux, JAR 24(3)):

- Technique 8.2 (chunk_0026): "Before reducing a π-formula, check whether the corresponding
  prefix is not a copy of a shorter prefix" — blocking **suppresses a rule application and
  adds nothing**. At a blocked step Massacci assumes *nothing semantic whatsoever*; a
  restricted calculus is trivially sound if the unrestricted one is. All justification is
  completeness-side: Theorem 8.1 (π-completed open branch ⇒ satisfiable, chunk_0026) and the
  Pruning Lemma 8.2 with `Ftree` (chunk_0027) — this is where ancestry enters, in the
  *metatheoretic model construction only* ("We do not need to prune the branch after the
  proof search terminates. It is enough to know that we can do it", chunk_0030).
- Proposition 8.1 (chunk_0030): box formulas propagate down initial-subsequence chains —
  ancestor box-*monotonicity* is what makes shorter-modal-copy loop-backs coherent in the
  constructed model. The keyed guard's arbitrary-target match has no analogue of this
  monotonicity; it substitutes exact snapshot equality (`successorBirthContent`), which is
  weaker along time (staleness) but is precisely what the free transfers turn into one-hop
  absorption — sufficient for §3, where no cone-depth propagation is ever needed.
- Technique 8.3 / Table IV (chunk_0029): S4 termination is a **prefix-depth bound**
  (`hbL = 2 + dp + p·n`), i.e. per-path — the shape a guard-narrowing fix would force CSLib's
  termination proof into (§5).
- Direct answer to the delegation's question "what does Massacci assume at a blocked step,
  and can the CSLib guard supply it": he assumes nothing, because his blocked step *does*
  nothing; the CSLib guard cannot inherit that argument while the soundness proof treats the
  redirect edge as semantic. §3 restores the separation on the proof side, which the guard
  *can* supply — via the free transfers it already supports.

**ChagrovZakharyaschev1997** (Modal Logic, OLG 35):

- Interval theorem (chunk_0246 L43-65): a filtration relation strictly between finest and
  coarsest "may be nontransitive even if the original R is transitive" — the failure mode
  that killed the route-(3) red-channel *Hintikka* bifurcation (its forward-cone conjuncts
  needed transitive-closure reasoning across mixed channels; Decision Gate B,
  `LoopChecking.lean:9298-9322`). §3 does not re-enter this territory: its absorption is
  strictly one-hop, and re-absorption at each hop is guaranteed because the **boxed** forms
  (`T(□χ)@wBlock`, not just `T(χ)@wBlock`) transfer — the box-plus enrichment.
- Lemmon filtration `□⁺` (chunk_0248 L24-31): `[x]S[y] iff y ⊨ □⁺φ whenever x ⊨ □φ` — the
  published remedy for exactly that transitivity failure, and structurally identical to the
  landed box-plus enrichment of `successorBirthContent` (third/fourth disjuncts,
  `LoopChecking.lean:534-540`). CSLib already made the right move here; §3 is its intended
  consumer on the soundness side.
- Theorem 5.51 (chunk_0267): the containment pattern (`Sₙ ⊆ R`, witnesses chosen from the
  ambient model via Lemma 5.50) — grounds §2's diagnosis that ambient containment is the
  load-bearing hypothesis the syntactically-chosen redirect target constitutively lacks.

## 5. Termination cross-check (Q3)

- **Recommended route (§3): zero impact.** No definition changes — `blockingWorldS4Keyed`,
  `modalApplyOneS4Keyed`, `modalStepBranchS4KeyedOrdered`, `keys`, `acc`, fuel, and every
  termination lemma (`keysDistinct` pigeonhole, `modalKnownWorlds_length_le_worldBoundS4`,
  `modalWorldBoundS4`) are untouched. The change is entirely in which *proposition* the
  soundness induction conserves. There is no soundness-for-termination trade here at all.
- **The alternatives the task description warns about are confirmed dangerous.** Narrowing
  the guard to ancestor-only targets (the plan-03 lineage) would let sibling worlds carry
  duplicate birth keys (the sibling match no longer blocks the mint), destroying
  `keysDistinct` and with it the global `2^(2·|Sf|)` world bound; the replacement is a
  per-path pigeonhole bounding *depth* only (Massacci's own `hbL` shape, Table IV,
  chunk_0029), with total-size control recovered from bounded branching — a full termination
  re-proof, not a patch. Live-set (staleness-only) fixes leave the reachability defect
  intact per the guard's own docstring (`LoopChecking.lean:648-650`). Neither is needed.

## 6. Conditional-GO preconditions (test these, in order, before any full dispatch)

- **P1 (cheapest, near-certain)**: State and close the reformulated mint-blocked arm alone:
  from `mintReady`-settledness + `S4LoopInv` + conjuncts of §3.2, produce `Er' = (src,
  wBlock) :: Er` and discharge (a)-(d). Consumes only landed lemmas plus the one new
  "edge-with-absorbed-payload preserves persistent inertness" lemma. If this closes, the
  dead-end arm is dead no longer. (~1 focused session.)
- **P2 (the genuine risk — kill criterion)**: The antitone-applicability family behind
  (d)-preservation: for each non-mint rule shape, `(modalApplyOneS4Keyed φ₀ keys sf b acc).1
  = .notApplicable → (modalApplyOneS4Keyed φ₀ keys sf (nf ++ b) acc).1 = .notApplicable`
  (b-growth), plus the edge-addition variants for the two mint arms. Probe it on the two
  worst shapes first: persistent box-positive (output filtered against `b` over successors)
  and one branching propositional shape. If some rule in `FrameRules.lean` is *not* output-
  filtered (i.e. can re-fire on data it already produced), (d) is unpreservable as stated
  and the route needs (d) weakened to a reachability-style predicate — treat that as
  route failure for pricing purposes and fall back to §7.
- **P3 (expected free)**: "Mint seed covers the 4-payload": every `modalFourBoxProp`/
  `modalFourDiaNegProp` output at the fresh world is in `modalApplyOneS4KeyedMint`'s payload.
  Should follow from `boxPlusExtraS4`'s definition; likely already implicit in the landed
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` machinery.

Estimated total for the reformulated Phase 7 if P1-P3 pass: the five arm restatements reuse
landed cores; the new mass is P2's lemma family (~10 mechanical lemmas), the invariant
record + dispatcher, and the fuel wrapper — comparable to the third+fourth dispatches
combined, and unlike them it has no open mathematical question at its center.

## 7. If P2 fails: the honest NO-GO and its minimal architectural change

Should (d) prove unpreservable (some rule re-fires on present data), the minimal change is
**driver-level provenance**: record redirect edges in a separate accumulator (the
route-independent `Reds`/`accWithReds` packaging retained at `LoopChecking.lean:9330-9346`
already exists for this), have the soundness track conserve `branchSatisfiableIn s4FC b acc`
over the mint-only `acc`, and let completeness consume `accWithReds acc red` — i.e. the
subtractive geometry of plan 04 but *without* its refuted bifurcated-Hintikka forward-cone
conjuncts, which §3's one-hop absorption replaces. That is a definition change with ripple
through Phases 1-6's landed statements, which is why it is the fallback and not the
recommendation. What it is **not** is a guard change: no variant examined here requires
touching `blockingWorldS4Keyed` or the termination track.

## 8. Do not re-attempt

- `branchSatisfiableIn_s4FC_addEdge_of_blocked` as a per-step lemma (needs conjuncts 3/4;
  false-as-construction at unwitnessed states, §2.2).
- Ambient-model surgery (closure-extension or generated-sub-relation) at step time (§2.2-2.3).
- Any invariant of the form "the model satisfies X at `f wBlock`" as a substitute for the
  edge (§2.1 — valuations cannot force relations).
- Forward-cone extension of the free transfers (refuted by Decision Gate B; §3 needs only
  the one-hop boxed forms).

## Sources

- Massacci2000 — chunks 0026, 0027, 0029, 0030 (Techniques 8.1-8.3, Definition 8.1/8.2,
  Theorem 8.1/8.4, Pruning Lemma 8.2, Propositions 8.1/8.2, Table IV).
- ChagrovZakharyaschev1997 — chunks 0246 (interval theorem, nontransitivity), 0248 (Lemmon
  filtration, `□⁺`), 0267 (Theorem 5.51, Lemma 5.50, containment construction).
- Code: `Cslib/Logics/Modal/Tableau/{LoopChecking,FrameCompleteness,FrameSoundness}.lean` at
  the line references given inline (all re-verified by grep/read this dispatch).
- Task artifacts: `handoffs/plan07-phase7-handoff-20260805c.md`/`...d.md`;
  `plans/07_canonical-witness-truth-lemma.md` `#### Phase 7 Progress Record` (third/fourth
  dispatches); `plans/04_subtractive-blocking-red-channel.md` (route-3 postmortem, via the
  in-file module note at `LoopChecking.lean:9298`).
