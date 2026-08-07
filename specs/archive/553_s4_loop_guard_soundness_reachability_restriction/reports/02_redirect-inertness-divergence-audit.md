# Divergence Audit: Redirect-Inertness and the Witness-Collision Obligation

- **Task**: 553 — `s4_loop_guard_soundness_reachability_restriction`
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Type**: Divergence audit (H5), dispatched after a second block on the same target
- **Date**: 2026-07-26
- **Session**: `sess_1785046950_33beb4_553`
- **Focus**: `divergence audit redirect-inertness witness collision`
- **Plan under audit**: `plans/02_origin-edge-invariant-revision.md` (Phase 12, `[BLOCKED]`)
- **Reference grounding tier**: Tier 3 (implementation-backed), with a documented Tier 1 gap
- **Mode**: Audit only. No `Cslib/**` file was modified. Axiom count unchanged (26).

---

## Headline Verdict

**The Phase 12 retraction is correct, and stronger than the plan states.** The witness-collision
configuration is not merely "not excluded by the landed invariants" — it is **reachable by the
ordered driver, and the two sorried lemmas are FALSE as stated**. This is machine-checked below
against the actual driver definitions, not against the prose.

Consequently:

- Question (1) is answered **"genuinely reachable; no unstated invariant excludes it."** R1 was
  wrong; the Phase 12 retraction was right.
- The two sorries **cannot be closed** by any invariant strengthening, because there is nothing
  to prove — the conclusion is false at a reachable state. Option (a) of the survival question is
  eliminated outright, and option (d) is eliminated with it (you cannot "accept" a sorry standing
  in for a false statement; it is an unsound obligation, not an unproven one).
- The recommended route is **(b), a bounded Route P modification**: record the box-context in the
  birth key in **boxed** form rather than unwrapped, and transmit the boxed form in the mint
  payload. This makes redirect-inertness a three-line consequence of the already-landed
  `S4LoopInv.keyLowerBd`, needing no origin-edge invariant, no mint-readiness, and no
  witness-collision case at all. It is **verdict-neutral on the full 8532-formula corpus**
  (measured, both orderings, zero changes, zero fuel exhaustion) and it **removes the offending
  redirect** on the audit's own witness formula (measured).
- The standing central prediction about termination is **retired in its current form** and
  replaced with a precise, mechanised conditional (§6). It was misframed: Lean-level termination
  is structural on `fuel` and never at risk; the real quantity is fuel *sufficiency*, and the
  guard-dependent link in that chain is `keysDistinct`.

---

## 1. Reference Grounding (H3)

This is a Tier 3 task: the object of study is this repository's own driver, and the audit's
method is differential execution of the shipped definitions. Two canonical literature sources for
the technique under repair are cited in `references.bib` with **verified BibKeys**:

| BibKey | Work | Relevance | Availability |
|--------|------|-----------|--------------|
| `Gore1999` | Goré, *Tableau Methods for Modal and Temporal Logics*, Handbook of Tableau Methods | Canonical treatment of loop-checking/blocking and termination | `references.bib:1023` notes "PDF not yet acquired (paywalled)" |
| `Massacci2000` | Massacci, *Single Step Tableaux for Modal Logics* | Terminating prefixed tableaux across the modal cube incl. S4; loop-checking/prefix management | `references.bib:1010` notes "PDF not yet acquired (paywalled)" |

**Honest Tier 1 gap.** Both BibKeys verify against `references.bib`, but neither full text is
ingested: `literature-search.sh` over the corpus returns `{"results": [], "degraded": true}` for
loop-checking queries, and the per-repo sub-index's 20 entries cover the intuitionistic/temporal
lines, not S4 loop-checking. **No theorem or definition number is cited from either source in
this report**, because none could be verified. Where §5 refers to the standard ancestor-blocking
discipline, it is flagged as an unverified attribution to be checked before any implementation
depends on it.

Stage 4a: `literature-lit-flag-resolve.sh --lit-flag true --orchestrator-mode true` returned
`SUBINDEX_PRESENT` (20 entries, ≥ threshold 3) — per-repo briefing mode, no `AskUserQuestion`,
consistent with `orchestrator_mode: true`.

---

## 2. Question (1): The Retraction, Verified — and the Lemma Refuted

### 2.1 The witness formula

```
φ₀  =  ¬(◇p ∧ ◇(□p ∧ ◇p))        where ¬X := X → ⊥,  p atomic
```

The design is forced by what the collision requires: world `0` must acquire `T(◇p)` with an
**empty** box-context (so the world it mints has key `{(pos,p)}` and only the *unwrapped*
`T(p)` on the branch), and a second, unrelated world must independently acquire both `T(◇p)`
(its own mint trigger, same `p`) and `T(□p)` (so its prospective birth content collapses to the
same singleton). Nesting `□p ∧ ◇p` under the second diamond delivers exactly that: the second
world receives the conjunction as its witness and decomposes it locally.

### 2.2 The machine-checked trace

Probe: `specs/553_.../artifacts/s4witness.lean`, driving `modalStepBranchS4KeyedOrdered`
(the ordered stepper — Route P) from the seed state `([F(φ₀)@0], [], ∅, [(0,∅)])`. Verbatim
output at the redirect step:

> **[SUPERSEDED — see §2.2a below]** The trace immediately below was captured on 2026-07-26
> code, before this repository's driver adopted the box-plus birth-key enrichment (dated
> 2026-08-05). It no longer reproduces against the current shipped driver. It is retained here
> unmodified because it is the historical refutation this section's argument depends on — the
> reason `blockedRedirect_boxctx_mem` was retired still holds, and the argument below (the
> hypothesis-instantiation table and the refutation) is unaffected by the later enrichment. See
> §2.2a for the live 2026-08-06 re-run and its attribution.

```
[6] b = T(p0)@2, T(□p0)@2, T(◇p0)@2, T((□p0∧◇p0))@2, T(p0)@1,
        T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((◇p0∧◇(□p0∧◇p0)))@0, F(φ₀)@0
      acc = [0→2 0→1]   keys = 0↦{} 1↦{+p0} 2↦{+(□p0∧◇p0)}
      e   = [F(φ₀)@0, T((◇p0∧◇(□p0∧◇p0)))@0, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((□p0∧◇p0))@2]
      nonMintCandidates = []
      guard(pos,p0,@2) = (some 1)
      T(box p0)@1 ∈ b  = false
      eBoxOnlyNeg = true      eDiaOnlyPos = true      keys(0) = ∅ : true

[7] acc = [2→1 0→2 0→1]   keys unchanged          <-- REDIRECT edge 2→1 fires, no world minted
[8] b = T(□p0)@1, ...                             <-- 4-rule repairs it ONE STEP LATER
      SATURATED OPEN
```

State `[6]` is a reachable pre-step state at which **every hypothesis of
`blockedRedirect_boxctx_mem` holds and its conclusion is false**:

| Hypothesis (`LoopChecking.lean:2028-2039`) | Instantiation at step [6] | Status |
|---|---|---|
| `hbClosure : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀` | — | Holds by the landed `S4LoopInv.bClosure` (preserved by `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv`, `:7667`); step [6] is reachable from the seed. Not `#eval`-checked: `modalUniverseS4` enumerates `modalWorldBoundS4 φ₀ = 2^(2·|Sf|)` labels and is not evaluable. |
| `hKO : keysOriginS4 b acc keys` | `(0,∅)`→root; `(1,{+p0})`→`u=0`, witness `(pos,p0)`, edge `0→1`; `(2,{+(□p0∧◇p0)})`→`u=0`, witness `(pos,□p0∧◇p0)`, edge `0→2` | Holds (hand-checked; three keys, each closed by the root or witness disjunct) |
| `hK0 : keysRootEmpty keys` | `key(0) = ∅` | `#eval`: true |
| `heBoxOnlyNeg` | no box-positive in `e` | `#eval`: `eBoxOnlyNeg = true` |
| `heDiamondOnlyPos` | no diamond-negative in `e` | `#eval`: `eDiaOnlyPos = true` |
| `hmint : modalNonMintCandidates … = []` | branch is mint-ready | `#eval`: `[]` |
| `hblock : blockingWorldS4Keyed φ₀ b keys .pos p 2 = some 1` | `v = 2`, `wBlock = 1` | `#eval`: `some 1` |
| `hbox : T(□p)@2 ∈ b` | present | `#eval` (visible in `b`) |
| **Conclusion `T(□p)@1 ∈ b`** | — | **`#eval`: false** |

**Therefore `blockedRedirect_boxctx_mem` is a false statement, not an unproven one.** The
`sorry` at `LoopChecking.lean:2080` is unclosable. (`blockedRedirect_diaNeg_mem` at `:2125` is
the mirror shape; the same construction with the dual formula refutes it, and the same argument
applies unchanged — I did not build a second probe for it, so its refutation is by symmetry with
the box case, not independently machine-checked.)

Note the two inline claims in the `sorry` comment that this corrects: the comment says
`T(□ψ)@v` arises "from ordinary propositional decomposition of `v`'s own birth content" — that
is exactly right, and the trace realises it (`T(□p∧◇p)@2` decomposing at step [4]→[5]). The
comment's "Nothing in the landed invariants forces `T(□ψ)@wBlock ∈ b`" is an understatement:
`T(□ψ)@wBlock ∉ b`, full stop.

### 2.2a Live re-run (2026-08-06) — stale recorded verdict, not a regression

**This subsection is additive.** The trace in §2.2 above is retained verbatim as the historical
refutation `blockedRedirect_boxctx_mem` was retired against; nothing above this point was
deleted or edited beyond the `[SUPERSEDED]` pointer note.

Re-running the identical probe (`specs/553_.../artifacts/s4witness.lean`, unmodified, same seed
state) at tree state `3a11702e` on 2026-08-06 no longer reproduces the §2.2 trace. Full live
output (captured verbatim in
`specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/measurement-ledger.md`):

```
[6] …  keys = 0↦{} 1↦{+p0,+p0,+p0} 2↦{+(□p0∧◇p0)}
      guard(pos,p0,@2) = none
      T(box p0)@1 ∈ b = false
[7] acc = [2→3 0→2 0→1]
      keys = 0↦{} 1↦{+p0,+p0,+p0} 2↦{+(□p0∧◇p0)} 3↦{+p0,+□p0,+p0,+p0}
      guard(pos,p0,@2) = (some 3)
      SATURATED OPEN
```

**Three concrete divergences from the §2.2 recorded trace:**

1. `guard(pos,p0,@2)` reads `none` at step [6] (recorded: `some 1`). It still reads `some 1` at
   steps [3]–[4], and reads `some 3` (not `some 1`) at [7].
2. Step [7] **mints a fresh world 3** (`acc = [2→3 0→2 0→1]`) instead of firing the redirect
   edge `2→1` (`acc = [2→1 0→2 0→1]`, the §2.2 recorded transition).
3. The trace **terminates at [7]** with `SATURATED OPEN`; the §2.2 recorded trace continued to
   `[8]`. `keys(3)` now carries a **boxed** member (`+□p0`), which no key in the §2.2 recorded
   trace does.

**Attribution — cause identified and dated, not guessed.** These are precisely the divergences
this report's own §3.1 adversarial-verification table already attributes to the *boxed-key
variant*: "reference produces `acc=[2→1 0→2 0→1]`; boxed produces `acc=[2→3 0→2 0→1]` (fresh
world 3, no redirect)". That boxed-key enrichment was subsequently adopted into the shipped
driver by three commits, all dated **2026-08-05**:

- `80feb736` — "task 563 phase 1: additive box-plus mint definitions"
- `7960c12e` — "task 563 phase 2-3: switch mint payload to additive box-plus"
- `5733dcd1` — "task 563 phase 4-5: enrich birth key with box-plus members"

These commits introduced `boxPlusPair`, `BoxPlusClosed`, and `boxPlusExtraS4`, now declared in
`Cslib/Logics/Modal/Tableau/S4/BirthKey.lean`.

**Chronology proves this predates the tableau-refactor programme that this gate is verifying:**

```
$ git log -1 --format='%h %ad' --date=short 5733dcd1
5733dcd1 2026-08-05
$ git merge-base --is-ancestor 5733dcd1 c8fede26 && echo YES
YES
```

`5733dcd1` (the last of the three box-plus commits) is an ancestor of `c8fede26`, which the
tableau-refactor programme's completion is anchored to — i.e. the box-plus enrichment landed
**before** the programme's own commits began (the programme's `S4/`-extraction commits are dated
2026-08-06, one day later).

**Disposition: this is a stale recorded verdict, not a behaviour-preservation failure.** The
§2.2 trace was captured on 2026-07-26 code and has not been touched since; the driver's minting
behaviour was deliberately changed on 2026-08-05 by a separate, already-landed task, for reasons
this report itself already analyses and endorses in §3.1. No commit belonging to the current
acceptance-gate programme altered this behaviour. Under the acceptance-gate decision rule (an
unexplained regression-corpus divergence is a FAIL even when every build is green; an
*explained and dated* one, predating the programme, is not), this finding does not block
acceptance.

### 2.3 Was there an unstated invariant that could have excluded it?

Three candidates were checked and all fail:

- **Mint-readiness (`hmint`) does not help.** It is `[]` at step [6]. Mint-readiness constrains
  propagation along *existing* edges out of `v`; `v = 2` has no outgoing edges yet, so the
  condition is vacuous exactly where it would need to bite. This confirms Phase 12's own reading.
- **`keysRootEmpty` does not help.** `wBlock = 1 ≠ 0`, so the root disjunct is already ruled out
  by the landed code path; the witness disjunct is what fires.
- **The guard's `min?` does not help.** It selects the *least* matching world, i.e. the
  *oldest* — which is precisely the world least likely to carry `v`'s box-content. If anything
  `min?` makes the collision more likely, not less.

---

## 3. Adversarial Self-Verification (H4)

I tried to refute my own answer to (1) before committing to it. Three attacks, one of which
succeeded against a subsidiary claim and changed the report.

### 3.1 Claim Verification Table

| Claim | Source / Counterexample | Verdict |
|---|---|---|
| The witness-collision configuration is reachable by the ordered driver | `s4witness.lean` trace, step [6]→[7]; redirect edge `2→1` appears with `keys` unchanged | **Confirmed** (machine-checked) |
| Every hypothesis of `blockedRedirect_boxctx_mem` holds at that state | Table in §2.2; 6 of 8 by `#eval`, `hKO` by hand, `hbClosure` by the landed invariant | **Confirmed**, with the two non-`#eval` items explicitly flagged |
| `blockedRedirect_boxctx_mem` is therefore FALSE, not merely unproven | `T(box p0)@1 ∈ b = false` at step [6] | **Confirmed** |
| `blockedRedirect_diaNeg_mem` is likewise false | Argued by symmetry only; no independent probe built | **Asserted, not machine-checked** — medium-high confidence |
| Route P's *invariant* `branchPropAdequateIn` is also false at that state | Attacked and **refuted**: the invariant is `∃ W m f, …`. I built a 3-world reflexive-transitive model (`W={a0,a1,a2}`, `r` = refl-trans closure of `{(a0,a1),(a0,a2)}`, `p` true at `a1,a2`) satisfying the branch, all old edge conjuncts, **and** `□p` at `f 1`. So `branchPropAdequateIn s4FC b (acc + 2→1)` **holds**. | **Refuted my initial suspicion.** Route P's invariant survives; only the syntactic route to it dies |
| The ambient-model-reuse proof strategy is nonetheless dead | 4-world model `W={a0,a1,a2,a3}`, `r` = refl-trans of `{(a0,a1),(a0,a2),(a1,a3)}`, `p` false at `a3`: satisfies the branch and all `acc` edge conjuncts (world 0 has no box-positives, so both are vacuous) but **falsifies `□p` at `f 1`**. `blockedRedirect_propAdequate` (`FrameSoundness.lean:1475`) discards the ambient edge conjunct (`_`) and reuses the ambient `m`, so it cannot recover | **Confirmed** — the defect is in the proof strategy, not the invariant |
| Boxed keys alone (without ordered scheduling) would fix the driver's unsoundness | **Refuted empirically**: `closesBoxed false cex 400 = some true` — the boxed **unordered** driver still closes `cex`. Staleness remains: `v` can acquire new box-positives *after* the redirect edge is fixed, and the permanent edge then transmits them. Route P's ordered scheduling remains necessary | **My hypothesis was wrong; retracted** |
| Boxed keys are verdict-neutral on the corpus | `s4boxed.lean` sweep, 2 atoms, size ≤ 6, fuel 100, 8532 formulas, both orderings: closed = 1650 vs 1650, fuel-exhausted = 0 vs 0, open→closed = 0, closed→open = 0 | **Confirmed** (measured) |
| Boxed keys remove the offending redirect | `s4boxed.lean` differential trace on `φ₀`: reference produces `acc=[2→1 0→2 0→1]`; boxed produces `acc=[2→3 0→2 0→1]` (fresh world 3, no redirect) | **Confirmed** (measured) |
| The termination prediction concerns Route P as landed | **Refuted**: `modalExpandBranchesS4KeyedOrdered` (`:7830`) recurses structurally on `fuel`; its `fuel = 0` arm returns `.openBranch`/`.closed` **from actual closure checks**, so fuel exhaustion can never fabricate a `.closed`. Termination is free; fuel *sufficiency* is a completeness question | **Prediction was misframed** — see §6 |

### 3.2 Recommendations changed by this pass

1. Dropped the claim that Route P's invariant is unsound. It is not; the proof route is.
2. Dropped the claim that boxed keys make the ordered stepper unnecessary. Measured false.
3. Downgraded the `_diaNeg_mem` refutation from "machine-checked" to "by symmetry".
4. Reframed the termination prediction from a live risk to a settled, conditional statement.

### 3.3 Zero-debt compliance

No recommendation below involves a `sorry`, an axiom, or a weakened landed statement. The
recommended route deletes both sorries by making the statements they stand in for provable.

---

## 4. Question (3): R2 and R3, Costed

Both options as recorded in the plan (`plans/02_...md:1082-1094`) are now **dead**, for a reason
neither anticipated: they are strategies for *proving* a statement that is false.

### R2 — strengthen `keysOriginS4` to cover the witness pair

**Dead on arrival.** R2 proposes recording more about the origin mint. But at step [6] the origin
data is complete and correct: `u = 0` genuinely minted world `1` via `T(◇p)@0` with an empty
box-context, and `T(□p)@0 ∉ b` is a true fact about the branch, not a bookkeeping gap. No
invariant over `(b, acc, keys)` can yield `T(□p)@1 ∈ b`, because that membership is false. The
only R2 variant that could work is the one the plan itself flags — forcing `u` to be
box-`p`-saturated *before any redirect into `wBlock`* — which is not an invariant strengthening
at all but a **guard/scheduling change**, i.e. R3.

**Cost if attempted anyway**: unbounded. There is no phase count, because there is no target.

### R3 — a scheduling side condition on the guard

**Technically closes the obligation; breaks the termination backbone.** Adding a side condition
to `blockingWorldS4Keyed`'s filter — block only if `∀ψ, T(□ψ)@v ∈ b → T(□ψ)@wBlock ∈ b` — makes
`blockedRedirect_boxctx_mem` true by unfolding the guard (~5 lines, and `keysOriginS4`,
`keysRootEmpty` and the case-(b) machinery all become dead code).

The cost is precise and fatal as stated:

- `blockingWorldS4Keyed_none_fresh` (`:538`) currently reads *"`none` ⟹ the prospective birth
  content differs from every recorded key."* With an extra conjunct in the filter, `none` can
  arise from a **failed box-check while a key matches**. The lemma becomes false.
- `blockingWorldS4Keyed_none_fresh` is the sole establisher of `S4LoopInv.keysDistinct`
  (`:7160-7164`, docstring: *"exactly what the redesigned guard enforces at minting time"*).
- `keysDistinct` is the hypothesis the pigeonhole argument
  `modalKnownWorlds_length_le_worldBoundS4` consumes to bound the world count by
  `|powerset(signedSubfmls φ₀)| ≤ modalWorldBoundS4 φ₀`.
- That bound feeds `S4LoopInv.bClosure`'s minting cases (labels `≤ modalWorldBoundS4`) and hence
  `modalUniverseS4` closure and `modalExpMeasure_entry_le_fuelS4` (`:8571`).

So R3 collapses: guard → `keysDistinct` → world bound → branch closure → fuel sufficiency. Two
worlds can be minted with equal keys, and the injection into the powerset fails.

**Cost if attempted**: re-architecting `keysDistinct` and the entire pigeonhole chain — 6+ phases,
and it reopens Phases 1-11 (`S4LoopInv` preservation for both drivers). **Not recommended.**

**This is exactly the mechanism the standing central prediction names**, now identified concretely
(§6).

### R-new (recommended) — boxed birth content + boxed mint payload

The diagnosis that R2/R3 both miss: the key records the box-context **unwrapped**
(`successorBirthContent`, `:384-391`, `(pos, ψ)` for `T(□ψ)@w`), and that projection is
*lossy in exactly the direction the obligation needs*. The witness pair `(s, φ)` can collide with
an unwrapped box-context pair — which is literally what happens at step [6]:
`insert (pos,p) {(pos,p)}` collapses to the singleton `{(pos,p)}`, matching a world whose key
came from a bare witness.

Record the box-context **boxed** instead — `(pos, □ψ)` and `(neg, ◇ψ)` — and transmit the boxed
forms in the mint payload so key and branch stay in step. Then:

```
T(□ψ)@v ∈ b                       (hypothesis)
  ⟹ (pos, □ψ) ∈ sbcBoxed φ₀ b s φ v          (boxed filter; □ψ ∈ modalSubfmls φ₀ by bClosure)
  ⟹ (pos, □ψ) ∈ key(wBlock)                  (guard match, blockingWorldS4Keyed_eq_birthContent)
  ⟹ T(□ψ)@wBlock ∈ b                         (S4LoopInv.keyLowerBd, ALREADY LANDED)
```

Three steps. **No `keysOriginS4`, no `keysRootEmpty`, no mint-readiness, no `e`-hypotheses, and
no witness-collision case** — the collision, if it occurs at all, now requires `φ = □ψ`, in which
case `T(□ψ)@wBlock` is on the branch *as `wBlock`'s own witness* via the same `keyLowerBd`. The
gap exists precisely because the unwrapped key discards the information; boxing it puts the
information back where `keyLowerBd` can reach it.

Why boxed transmission is legitimate: it is exactly what `modalFourBoxProp` derives one step
later — visible at step [7]→[8], where the driver itself adds `T(□p0)@1`. Boxing the payload
front-loads a derivation the driver already performs, and it keeps `keyLowerBd` provable at the
mint step (the reason the *key* alone cannot be boxed: the mint payload currently emits only
unwrapped `ψ` — `modalApplyOne`, `Rules.lean:108-113,134-139` — which is the same root cause
that blocked v1 Phase 10).

**Measured behaviour** (`s4boxed.lean`, executable variant, no proofs):

| Measurement | Reference | Boxed |
|---|---|---|
| `cex` (not `s4Valid` — must be OPEN), ordered | OPEN | OPEN |
| `cex`, unordered (documented unsound) | CLOSED | CLOSED |
| T, 4, K axioms (valid — must be CLOSED) | CLOSED | CLOSED |
| `φ₀` witness formula (not valid — must be OPEN), ordered | OPEN | OPEN |
| Corpus 2 atoms, size ≤ 6, fuel 100 (8532 formulas), ordered | closed 1650, fuel-exh. 0 | closed 1650, fuel-exh. 0 |
| Same corpus, unordered | closed 1650, fuel-exh. 0 | closed 1650, fuel-exh. 0 |
| open→closed changes (soundness regression) | — | **0** |
| closed→open changes (completeness change) | — | **0** |
| `acc` on `φ₀` at saturation | `[2→1 0→2 0→1]` (redirect) | `[2→3 0→2 0→1]` (fresh world, **no redirect**) |

Verdict-neutral on the whole corpus, and it removes the offending redirect. That is the profile
of a proof-enabling refactor rather than a behavioural change.

**Cost, honestly**:

- `keysDistinct` and the pigeonhole chain **survive untouched** — the comparison stays plain key
  equality, so `blockingWorldS4Keyed_none_fresh` transfers verbatim. This is the decisive
  advantage over R3.
- `successorBirthContent` changes ⟹ re-prove `keyLowerBd`'s two minting cases
  (`successorBirthContent_boxNeg_subset_relevantSetFinset` `:2137`,
  `_diamondPos_…` `:2207`) and `successorBirthContent_subset_signedSubfmls` (`:2656`).
- Mint payload changes ⟹ re-prove `modalApplyOne_boxNeg_outputs_subset_S4` (`:1905`) and its
  diamond twin against the boxed payload, plus the mint arms of
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` (`:9097`) and `…_preserves_S4LoopInv`.
- **`Cslib/Logics/Modal/Tableau/Rules.lean` must NOT be edited** — `modalApplyOne` is shared with
  K/T/B/S5 and `FmpMeasure.lean`'s `_gen` lemmas. The boxed mint arm belongs in the S4-keyed
  layer, replacing the `modalApplyOne sf b acc` fallthrough at `LoopChecking.lean:754,758` (this
  is what `s4boxed.lean`'s `applyBoxed` does).
- **Assets orphaned**: `keysOriginS4` + entry + two monotonicity lemmas (`:1279-1336`),
  `blockedRedirect_boxctx_mem_of_boxOrigin`/`_diaNeg_mem_of_diaOrigin`, `keysRootEmpty` +
  entry (`:2009-2019`), `modalStepBranchS4Keyed(Ordered)_preserves_keysOriginS4`
  (`:4558`, `:4775`) — Phases 10-12's principal deliverables. Sunk cost, and it should be named
  as such rather than papered over. `blockedRedirect_propAdequate` (`FrameSoundness.lean:1458`)
  **survives** with its hypothesis list shortened.
- `CslibTests/S4LoopGuardRegression.lean` stays valid: the boxed unordered driver still closes
  `cex` (measured), so the documented unsoundness of the unordered line is unchanged.
- **Estimated 4-6 phases**, each within one agent run.

**Residual risk on this route, flagged (not resolved).** §5 identifies a *separate*, larger
problem that R-new does not address and that Phase 13 will hit regardless of which option is
taken.

---

## 5. Question (4): Route P Survival Verdict

### Recommendation: **(b), the bounded modification of §4 (R-new)** — with a mandatory
### precondition that the §5.1 invariant defect is planned for first.

Ranking, with cost and risk:

| Option | Verdict | Cost | Risk |
|---|---|---|---|
| **(a)** close the sorries by further invariant strengthening under Route P | **Eliminated.** The statements are false; there is nothing to prove | n/a | n/a |
| **(d)** accept the two sorries as documented permanent limitations, proceed to Phase 13+ | **Eliminated.** A `sorry` standing in for a *false* lemma is not a limitation, it is an unsound foundation: `blockedRedirect_propAdequate` and hence `modalTableauS4KeyedOrdered_sound` would be derived from a false premise, making the target theorem's proof worthless while it type-checks | 0 phases | Maximal — ships a false theorem |
| **(b)** bounded Route P modification (R-new) | **Recommended** | 4-6 phases; orphans Phases 10-12's origin-edge machinery | Medium. Corpus-neutral and pigeonhole-safe (both measured/argued); the real risk is §5.1, which is not specific to this option |
| **(b′)** R3 (guard side condition) | Not recommended | 6+ phases | High — breaks `keysDistinct` → world bound → fuel sufficiency (§4) |
| **(c)** abandon Route P for a different soundness route | **Viable fallback, not first choice** | 10+ phases; discards Phases 1-12 | High cost, lower proof risk. See below |

On **(c)**: the standard discipline in the tableau literature is *ancestor-only* blocking — a
world may be blocked only against a world on its own branch-ancestor path, which in a
reflexive-transitive frame makes the redirect edge a genuine back-edge and restores
`branchSatisfiableIn` outright (no weakened `branchPropAdequateIn` needed, hence no §5.1
problem). This is also precisely the "reachability restriction" in this task's own title, and the
`blockingWorldS4Keyed` docstring's second named defect (`:491-497`, *"no constraint that `w'` be
reachable from the source at all"*). **Attribution unverified**: `Gore1999` and `Massacci2000`
are the sources to check, and neither PDF is ingested (§1). If (b) stalls, acquiring one of those
two PDFs is the highest-value next action, ahead of any further proof attempt.

### 5.1 A distinct, larger defect that Phase 13 will hit regardless

Found while auditing; **not** the audited target, and it changes the plan's remaining risk
profile, so it must not be passed forward silently.

`branchPropAdequateIn` (`FrameSoundness.lean:1184`) replaces `branchSatisfiableIn`'s edge
conjunct `acc.hasEdge w w' → m.r (f w) (f w')` with a branch-membership-driven conjunct. That
weakening **destroys frame transitivity as a usable lever**, and transitivity is what made
box-propagation preservation free. The symptom is already visible in the landed code:
`branchPropAdequateIn_s4FC_boxPos_trans_mem` (`:1236`) needs an extra hypothesis

```
hready : ∀ v, acc.hasEdge w' v = true → T(□φ)@v ∈ b
```

whose docstring says the bare analogue "is false in general". Phase 13's plan (`:1135`) proposes
to discharge `hready` "trivially for a freshly minted `w'` (no outgoing edges yet), and via
Phase 12's `blockedRedirect_boxctx_mem` for redirect edges". **That case split is not exhaustive.**
Counter-shape, using only genuine mint edges and no redirect at all: with `0→1` and `1→2` both
mint edges, let `T(□ψ)@0` arrive late (propositional decomposition at `0`). The 4-rule at `(0,1)`
adds `T(□ψ)@1`; at that moment `hready` demands `T(□ψ)@2`, which the driver supplies only at the
*next* step, via the 4-rule at `(1,2)`. So `hready` fails at the intermediate state for a plain
mint-edge chain — with `w'` neither freshly minted nor a redirect target.

This is the same transient-gap pattern as the audited defect (`b` is repaired one step later —
compare step [7]→[8]), and it means the per-step preservation of `branchPropAdequateIn` is
**not** obtainable from the current invariant for the box-propagation shapes either.

The natural repair is to make the invariant retain the edge information it discarded — a
disjunctive edge conjunct

```
∀ w w', acc.hasEdge w w' → (m.r (f w) (f w')) ∨ (the current propagation-adequacy clause)
```

so genuine mint edges keep transitivity (making `hready` free again, as it is for
`branchSatisfiableIn`) and only redirect edges take the weakened clause. I have **not** verified
that this disjunctive form is preserved across redirect steps — that is a design question for the
planner, not a finding. It is flagged as the load-bearing open question for Phase 13.

**Planning consequence**: Phase 13 as currently written is under-specified independently of the
witness-collision issue, and the `hready` discharge should be re-planned *before* the R-new work
is dispatched — otherwise R-new lands correctly and Phase 13 blocks a third time on a different
manifestation of the same weakness.

---

## 6. Question (5): The Standing Central Prediction — Retired and Replaced

> *"Narrowing the guard may break TERMINATION rather than merely completeness."*

**Retired in this form.** It has survived five phases because it was not falsifiable as stated.
Two facts settle it analytically, without a new sweep:

1. **Lean-level termination is never at risk.** `modalExpandBranchesS4KeyedOrdered` (`:7830`)
   recurses structurally on `fuel`; Phase 7 recorded that the termination checker accepted the
   copied recursion with no `termination_by`/`decreasing_by`. Nothing about the guard can change
   this.
2. **Fuel exhaustion cannot break soundness, only completeness.** The `fuel = 0` arm returns
   `.openBranch b a` for the first branch failing `isModalClosed`, and `.closed` only when every
   branch genuinely *is* closed. A spurious `.closed` is therefore impossible. So the prediction's
   framing — termination *rather than* completeness — inverts the actual dependency: the
   guard-sensitive quantity is fuel *sufficiency*, which is a completeness property.

**Replacement (precise, mechanised, and settled):**

> Any repair that adds a **side condition to `blockingWorldS4Keyed`'s filter** falsifies
> `blockingWorldS4Keyed_none_fresh` (`:538`), hence `S4LoopInv.keysDistinct` (`:7160`), hence the
> pigeonhole world bound `modalKnownWorlds_length_le_worldBoundS4`, hence
> `S4LoopInv.bClosure`'s minting cases and `modalExpMeasure_entry_le_fuelS4` (`:8571`). Any repair
> that instead **enriches the key being compared** leaves the comparison as plain key equality and
> preserves that entire chain verbatim.

This is a proof, not a prediction: it follows from the `none`-case reading of the guard. It
retires the vague form and gives the concrete discriminator between R3 (breaks it) and R-new
(preserves it). Phase 8's null result is explained rather than merely repeated: at fuel 100 with
size-6 formulas the world bound is `2^(2·|Sf|) ≥ 2^12 = 4096`, so a fuel-100 sweep cannot reach
the bound and was never capable of testing it.

**If empirical confirmation is still wanted**, the experiment that would settle it — stated
precisely, as required — is:

> Instrument the driver to report, per formula, `(max world index, step count, and whether any two
> recorded keys are equal)`. Sweep 2 atoms/size ≤ 7 and 3 atoms/size ≤ 6 at fuel ≥ 5000, for the
> reference ordered driver, the R-new boxed variant, and an R3 side-condition variant. The
> prediction's mechanism is confirmed iff the R3 variant exhibits **two equal recorded keys** on
> some formula (which falsifies `keysDistinct` by direct witness) while the reference and boxed
> variants do not. Fuel exhaustion is the wrong observable and should not be the gate.

The duplicate-key check is the right observable because it tests the actual load-bearing lemma
rather than a downstream proxy. I did not run it: R3 is not recommended, so the measurement has
no decision value unless someone chooses R3 over this report's advice.

---

## 7. Artifacts and Territory

Written (all under this task's `specs/` directory; **no `Cslib/**` file modified**):

- `specs/553_.../artifacts/s4witness.lean` — reachability probe for the witness-collision
  configuration; traces `modalStepBranchS4KeyedOrdered` on `φ₀` and prints every decidable
  hypothesis of `blockedRedirect_boxctx_mem` at each step.
- `specs/553_.../artifacts/s4boxed.lean` — executable boxed-key variant (`sbcBoxed`, `bwBoxed`,
  `mintBoxed`, `applyBoxed`, `bodyBoxed`, ordered and unordered steppers), the `cex`/axiom checks,
  the 8532-formula differential sweep, and the differential edge-set trace. Definitions only; no
  proofs, no `sorry`, no axioms.
- `specs/553_.../reports/02_redirect-inertness-divergence-audit.md` — this report.

Not touched: `Cslib/Logics/Modal/Tableau/**`, `CslibTests/**`, and
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` (concurrent-session territory). No landed
statement weakened, nothing reverted, no proof attempted. Axiom count unchanged at 26; the two
Phase 12 sorries are untouched and remain the only sorries in `Modal/Tableau/`.

Reproduce:

```bash
lake env lean specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4witness.lean
lake env lean specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4boxed.lean
```

(The second takes roughly 20 minutes — it runs four drivers over 8532 formulas twice.)
