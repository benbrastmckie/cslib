# Research Report: Box-Plus Birth Keys for the Keyed S4 Loop Guard

- **Task**: 563 `tableau_boxplus_birth_keys` (Task E of the modal-tableau refactor programme)
- **Session**: `sess_1785926778_90c7a6_563`
- **Date**: 2026-08-05
- **Agent**: cslib-research-agent

---

## 1. Executive Summary

The enrichment is **feasible, empirically verdict-neutral, and structurally bounded**. The single
biggest finding is that the task's stated risk — that `modalTableauS4Keyed_complete` may break —
is **structurally inert**, and I can say why rather than assume it: `modalHintikkaSetGen`'s
conjunct 2 returns literal `True` at exactly the two minting shapes, which is the reason
`hintikka_congr_S4` is provable unconditionally today. Every part of the completeness chain that
could see the guard or the mint payload sees `True` there instead.

The real cost sits somewhere else than the task description anticipates: **the mint payload must
change too, and it cannot change in `Rules.lean`**. `modalApplyOneS4Keyed` currently mints by
falling through to raw `modalApplyOne`, whose payload transmits the box-context *unwrapped*
(`T(ψ)@w'`, never `T(□ψ)@w'`). Without a boxed transmission at mint time, the enriched key's
boxed member has nothing to lower-bound and `keyLowerBd`'s minting case becomes **false**, not
merely hard. `Rules.lean` is shared with K/T/B/S5 and must not be touched (boxed transmission is
unsound for K). The boxed mint arm therefore belongs in the S4-keyed layer, replacing the
`modalApplyOne sf b acc` fallthrough inside `modalApplyOneS4Keyed`.

Empirically measured (this session, executable probe, no proofs):

| Measurement | Reference keyed driver | Box-plus keyed driver |
|---|---|---|
| `cex` (not `s4Valid`, must be OPEN), ordered | OPEN | **OPEN** |
| `cex`, unordered (documented-unsound line) | CLOSED | **CLOSED** |
| T, 4, K axioms (valid, must be CLOSED) | CLOSED | **CLOSED** |
| Corpus: 2 atoms, size ≤ 6, fuel 100, 8532 formulas, ordered | closed 1650, fuel-exh. 0 | closed 1650, fuel-exh. 0 |
| Same corpus, unordered | closed 1650, fuel-exh. 0 | closed 1650, fuel-exh. 0 |
| open→closed (soundness regression) | — | **0** |
| closed→open (completeness change) | — | **0** |
| `acc` on `phiW` at saturation | `[2→1 0→2 0→1]` (redirect) | `[2→3 0→2 0→1]` (fresh world, **no redirect**) |

Artifacts: `specs/563_tableau_boxplus_birth_keys/artifacts/s4boxplus.lean` (keyed track),
`.../s4boxplus_live.lean` (live-guard track).

**Recommendation**: proceed, in 5 phases, with the *additive* mint shape
(`modalApplyOne`'s payload `++ boxPlusExtra`) described in §5. Do not attempt this as one
dispatch.

---

## 2. Baseline (verified this session, not inherited)

- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` → **exit 0, 900 jobs**, one
  `declaration uses 'sorry'` warning at `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1227`.
  This matches the task description's "Modal/Tableau sorry census exactly 1".
- Blast radius outside `LoopChecking.lean` is **prose only**. `successorBirthContent`,
  `blockingWorldS4`, and `blockingWorldS4Keyed` occur in `FrameSoundness.lean` (1 hit),
  `FrameCompleteness.lean` (2 hits), and `CslibTests/S4LoopGuardRegression.lean` (3 hits), and
  **every one of those is inside a docstring or a module comment** — no code position. All
  executable dependency is confined to `LoopChecking.lean`.

Verified by:
```
grep -n "blockingWorldS4Keyed" Cslib/Logics/Modal/Tableau/FrameSoundness.lean \
  Cslib/Logics/Modal/Tableau/FrameCompleteness.lean CslibTests/S4LoopGuardRegression.lean
```

---

## 3. Why the Gate Is Structurally Safe (demonstrated, not assumed)

The task requires the completeness transport be *demonstrated*. Four independent facts, each
located by declaration name:

**(a) `modalHintikkaSetS4`'s conjunct 2 is `True` at the mint shapes.**
`modalHintikkaSetS4` (`LoopChecking.lean`, `def modalHintikkaSetS4`) has literal arms
`| .neg, .box _ => True` and `| .pos, .diamond _ => True`. The mint payload and the guard are
invisible to it.

**(b) `hintikka_congr_S4` already relies on exactly this.** Its own docstring states the argument:
"`modalHintikkaSetGen`'s conjunct 2 returns literal `True` at exactly the two shapes
(`F(□φ)@w`/`T(◇φ)@w`) where `modalApplyOneS4Keyed`/`modalApplyOneS4` can differ". The keyed rule
is *already permitted* to diverge arbitrarily from the live rule at the mint shapes without
disturbing Hintikka-set-hood. Changing the keyed mint payload moves within that existing licence.
The proof body is `simp_all [modalApplyOneS4Keyed]` and will need re-checking, but the argument
does not change shape.

**(c) `modalTableauS4Keyed_complete` never unfolds the guard.**
`FrameCompleteness.lean`, `theorem modalTableauS4Keyed_complete`: it consumes
`modalExpandBranchesS4Keyed_hintikka`, `modalExpandBranchesS4Keyed_openBranch_initial_mem`, and
`modalOpenBranchS4_countermodel` as black boxes, plus `modalTableauS4Keyed_initial`. The only
way it can break is via a changed *field count* on `S4LoopInv`/`S4KeyedHintikkaInv` — see §6
risk R3.

**(d) The blocked-case Hintikka witnesses survive verbatim.**
`modalStepBranchS4Keyed_blocked_witness_mem` derives `⟨s, φ, wBlock⟩ ∈ b` from
`Finset.mem_insert_self` on `successorBirthContent`'s `insert (s, φ)` head. The enrichment adds
disjuncts to the *filter*, never touches the `insert` head, so this proof is unchanged. Same for
`blockedRedirect_unwrapped_boxPos_mem` / `_diaNeg_mem`, whose `Or.inl ⟨rfl, …⟩` /
`Or.inr ⟨rfl, …⟩` steps land in the two disjuncts §5 keeps first and verbatim.

**This is why "both members" beats "boxed only".** The prior-art variant in
`specs/553_.../artifacts/s4boxed.lean` *replaces* `(pos, ψ)` with `(pos, □ψ)`. That would
falsify `blockedRedirect_unwrapped_boxPos_mem`/`_diaNeg_mem` — two landed, sorry-free,
standard-axioms-only lemmas explicitly retained for the route (1) successor plan. Task E's
both-members reading is a strict superset and preserves them. Recommend the task's reading over
the 553 report's `sbcBoxed`.

---

## 4. The Finding the Task Description Does Not Anticipate: the Mint Payload Is Load-Bearing

`keyLowerBd`'s minting case is
`successorBirthContent φ₀ b s φ w ⊆ relevantSetFinset φ₀ (newForms ++ b) (modalNextWorld b)`
(`successorBirthContent_boxNeg_subset_relevantSetFinset`, `_diamondPos_…`).
`relevantSetFinset φ₀ b' w'` is "signed pairs whose instantiation at `w'` is literally on `b'`".
So adding `(pos, □ψ)` to the key **requires `T(□ψ)@w' ∈ newForms ++ b`**.

Today it is not there. `modalApplyOne`'s `boxNeg`/`diamondPos` arms (`Rules.lean`) emit
`⟨.pos, ψ, w'⟩` from `boxPositivesOf b` and `⟨.neg, ψ, w'⟩` from the diamond-negatives — the
unwrapped forms only. The 4-rule (`modalFourBoxProp`, `FrameRules.lean`) *does* produce
`T(□ψ)@w'`, but only over `acc.successorsOf w`, and it fires at the `T(□ψ)@w` dispatch shape one
step *after* the edge `w → w'` exists. At the instant of minting the boxed form is absent.

Consequences, stated plainly:

1. **Enriching the key alone makes `keyLowerBd`'s minting case FALSE.** It is not "harder to
   prove"; there is no proof. Any implementation that enriches keys without touching the payload
   will hit an unprovable goal and must not paper over it with a `sorry`.
2. **`Rules.lean` MUST NOT be edited.** `modalApplyOne` is shared by K/T/B/S5 drivers and by
   `FmpMeasure.lean`'s `_gen` lemmas; boxed transmission is not K-sound. This matches the 553
   audit's explicit instruction ("`Rules.lean` must NOT be edited").
3. **The boxed arm belongs in `modalApplyOneS4Keyed`**, replacing its two
   `| none => modalApplyOne sf b acc` fallthroughs. `blockingWorldS4`/`modalApplyOneS4`/
   `modalHintikkaSetS4` stay as the live-guard reference artifact.

Prior art for the payload shape, both already in-tree:
- `modalFourBoxProp`/`modalFourDiaNegProp` (`FrameRules.lean`) — box-plus at the rule level.
- `boxDiamondPersistence` (`Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean:343`) —
  transmits `{ bsf with label := … }`, i.e. the box formula *itself*, to the fresh time index.
  Directly analogous, and boxed-only, so it also shows the shape is already sanctioned.

---

## 5. Recommended Design

### 5.1 `boxPlusPair` — and a reformulation worth taking

The **existing** filter predicate is exactly "the box-plus partner of `p`, instantiated at `w`,
is on `b`":

```
p.1 = .pos ∧ T(□p.2)@w ∈ b   ⟺   ⟨(boxPlusPair p).1, (boxPlusPair p).2, w⟩ ∈ b
p.1 = .neg ∧ F(◇p.2)@w ∈ b   ⟺   same
```

with

```lean
/-- The box-plus partner of a signed pair: `(pos, ψ) ↦ (pos, □ψ)`, `(neg, ψ) ↦ (neg, ◇ψ)`. -/
def boxPlusPair (p : Sign × Proposition Atom) : Sign × Proposition Atom :=
  match p.1 with
  | .pos => (.pos, .box p.2)
  | .neg => (.neg, .diamond p.2)
```

So the current birth content is `{p ∈ Σ : boxPlusPair p @ w ∈ b}`, and the enrichment is the
union with `{q ∈ Σ : q is itself a box-plus image and q @ w ∈ b}`.

**Do not rewrite the existing two disjuncts into `boxPlusPair` form**, tempting as it is: the
`Or.inl ⟨rfl, …⟩` steps in `blockedRedirect_unwrapped_boxPos_mem`, `_diaNeg_mem`, and both
`successorBirthContent_*_subset_relevantSetFinset` proofs match the current syntactic shape.
Keep them verbatim and *append* two disjuncts. Note the reformulation in the docstring instead.

```lean
def successorBirthContent (φ₀ : Proposition Atom) (b) (s : Sign) (φ) (w) :
    Finset (Sign × Proposition Atom) :=
  insert (s, φ) ((signedSubfmls φ₀).filter (fun p =>
    -- unchanged, in this order:
    (p.1 = Sign.pos ∧ b.any (· == (⟨.pos, .box p.2, w⟩ : SignedFormula _ _))) ∨
    (p.1 = Sign.neg ∧ b.any (· == (⟨.neg, .diamond p.2, w⟩ : SignedFormula _ _))) ∨
    -- box-plus members, appended:
    (p.1 = Sign.pos ∧ (match p.2 with
      | .box _ => b.any (· == (⟨.pos, p.2, w⟩ : SignedFormula _ _)) = true
      | _ => False)) ∨
    (p.1 = Sign.neg ∧ (match p.2 with
      | .diamond _ => b.any (· == (⟨.neg, p.2, w⟩ : SignedFormula _ _)) = true
      | _ => False))))
```

The `match`-on-`p.2` form keeps the predicate decidable without an existential; a Bool-valued
rewrite of the whole filter would break the four proofs above and is not worth it.

### 5.2 `BoxPlusClosed` — a caveat on the naming

`BoxPlusClosed` **cannot** be a closure property of the whole key. The witness pair `(s, φ)` sits
in the key by `insert`, and neither direction of closure holds for it: at a mint from
`F(□(□χ))@w` the witness is `(neg, □χ)` and neither `(neg, χ)` nor `(neg, ◇□χ)` need be on the
branch at birth. A universally-quantified `∀ p ∈ k, boxPlusPair p ∈ k` is **false**; do not write
it and then discover this mid-proof.

The provable contract, scoped to the transmitted box-context:

```lean
/-- `k` records BOTH members of every box-context pair transmitted from `w` on `b`. -/
def BoxPlusClosed (φ₀ : Proposition Atom) (b) (w : WorldIndex)
    (k : Finset (Sign × Proposition Atom)) : Prop :=
  ∀ p ∈ signedSubfmls φ₀,
    (⟨(boxPlusPair p).1, (boxPlusPair p).2, w⟩ : SignedFormula _ _) ∈ b →
      p ∈ k ∧ (boxPlusPair p ∈ signedSubfmls φ₀ → boxPlusPair p ∈ k)
```

This is what `successorBirthContent` satisfies by construction and what the redirect-transfer
lemmas consume. If the planner prefers a different shape, the constraint to respect is: it must
be scoped to the filter, never to the whole key.

### 5.3 The mint payload: use the ADDITIVE shape

```lean
def boxPlusExtraS4 (b) (w : WorldIndex) : List (SignedFormula (Proposition Atom) WorldIndex) :=
  let w' := modalNextWorld b
  (boxPositivesOf b).filterMap (fun (ψ, src) =>
    if src == w then
      let sf' := (⟨.pos, .box ψ, w'⟩ : SignedFormula _ _)
      if b.any (· == sf') then none else some sf'
    else none) ++
  b.filterMap (fun sf' => if sf'.sign == .neg && sf'.label == w then
    match sf'.formula with
    | .diamond ψ =>
      let pr := (⟨.neg, .diamond ψ, w'⟩ : SignedFormula _ _)
      if b.any (· == pr) then none else some pr
    | _ => none
  else none)
```

and then `modalApplyOneS4Keyed`'s two unblocked arms emit
`modalApplyOne`'s own payload `++ boxPlusExtraS4 b sf.label`.

**Why additive, and why it matters for the migration**: every existing membership proof into the
mint payload is a chain of `List.mem_append_left` / `List.mem_cons_of_mem` into the *original*
list. Under `oldPayload ++ extra`, each such chain survives with exactly one more
`List.mem_append_left` wrapper. Under a rewritten payload (the `mintBoxed` shape of
`s4boxed.lean`, which interleaves) every chain must be re-derived. This decision is worth ~20
proof bodies.

Keep the per-formula `if b.any (· == sf') then none else some sf'` dedup guard — the freshness
half of `modalApplyOneS4Keyed_persistentFresh_S4` and the measure argument both key off it.

---

## 6. Blast Radius, Measured

All in `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (10206 lines).

`modalApplyOneS4Keyed_boxNeg_unblocked_eq` / `_diaPos_unblocked_eq` have **50 call sites across
exactly 23 enclosing declarations**, each using both arms once:

```
awk '/^(private )?(lemma|theorem|def) /{...} /modalApplyOneS4Keyed_(boxNeg|diaPos)_unblocked_eq/{print cur}' \
  Cslib/Logics/Modal/Tableau/LoopChecking.lean | sort | uniq -c
```

**Class A — name-swap only (9 declaration families, 18 sites).** They need the equation to pin
`result` and `.snd`; the accessibility component is unchanged
(`acc.addEdge w (modalNextWorld b)`), and they never inspect the payload list:
`_preserves_accFresh`, `_preserves_accKnown`, `_preserves_outDegEq`,
`modalApplyOneS4Keyed_hasEdge_mono`, `_branchingLength_S4`, `_boxNeg_ne_notApplicable`,
`_diaPos_ne_notApplicable`, `_preserves_keysTotal`, `_preserves_keysWorldsKnown`,
`_preserves_keysOriginS4` — for both the `modalStepBranchS4_*` and `modalStepBranchS4KeyedOrdered_*`
variants.

`modalApplyOneS4Keyed_persistentFresh_S4` is also Class A despite the name: it constrains only
`.persistent` results, and the mint is `.linear`, so its mint arms merely derive
`.linear ≠ .persistent`.

**Class B — genuine proof work (6 families, 12 sites + 3 content lemmas).**

| Declaration | Work |
|---|---|
| `successorBirthContent_boxNeg_subset_relevantSetFinset` | two new `rcases` arms; each is the box-positive arm with `modalSubfmls_trans` *removed* (the boxed pair is already in `Σ` by `hpmem`) and the target in `boxPlusExtraS4` |
| `successorBirthContent_diamondPos_subset_relevantSetFinset` | dual |
| `successorBirthContent_subset_signedSubfmls` | unchanged in substance — new disjuncts still land in the `⟨hpmem, -⟩` branch |
| `modalApplyOneS4Keyed_outputsSubsetUniverse_S4` | new `.linear` case for `boxPlusExtraS4`; needs `.box ψ ∈ modalSubfmls φ₀`, immediate from `hb` + `mem_boxPositivesOf`, and the `w' ≤ modalWorldBoundS4 φ₀` bound the existing proof already has |
| `modalApplyOne_boxNeg_outputs_subset_S4` / `_diamondPos_…` | `List.mem_append` split; left half is the verbatim old proof |
| `modalStepBranchS4(KeyedOrdered)_preserves_bClosure` | consumes the two above |
| `modalStepBranchS4(KeyedOrdered)_preserves_keyLowerBd` | the target of the task; consumes the two subset lemmas |
| `modalStepBranchS4(KeyedOrdered)_preserves_worldsContiguousS4` | new formulas are all at `modalNextWorld b`, already introduced by the witness — no new world label, so the extra case closes the same way |
| `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` | `eBoxNegWitness`/`eDiamondPosWitness` need the witness `⟨.neg, ψ, w'⟩`, still the payload head; `hintikkaInv` is `True` at mint shapes |
| `hintikka_congr_S4` | re-check `simp_all [modalApplyOneS4Keyed]`; argument unchanged (§3(b)) |

**New assets to add**: `boxPlusPair`, `BoxPlusClosed`, `boxPlusExtraS4`, a
`modalApplyOneS4KeyedMint` def plus its two unblocked-shape lemmas (drop-in replacements shaped
like `modalApplyOne_boxNeg_mint_fst_S4`), and the two box-plus transfer lemmas
`blockedRedirect_boxed_boxPos_mem` / `_diaNeg_mem` (the payoff — each a three-line consequence of
`keyLowerBd` + the guard match, per the 553 audit's derivation).

**Explicitly NOT touched**: `signedSubfmls_card_le`, `signedSubfmls_powerset_card_le`,
`modalWorldBoundS4`, `modalUniverseS4`, `relevantSetFinset`, `keysUpdate_preserves_keysDistinct`,
`blockingWorldS4Keyed_none_fresh`, and the pigeonhole chain. Confirmed: `modalSubfmls (.box a) =
.box a :: modalSubfmls a` (`FmpMeasure.lean`, `def modalSubfmls`) means `□ψ ∈ modalSubfmls φ₀`
whenever `T(□ψ)@w ∈ b ⊆ modalUniverseS4 φ₀`, so the enriched key stays inside `signedSubfmls φ₀`
and the codomain — hence the world bound — is genuinely unchanged. **Box-plus is free in the
world bound**, as the task states.

---

## 7. Risks

**R1 — `keyLowerBd`'s minting case is false without the payload change.** §4. Highest-severity
item; it is a correctness trap, not a difficulty. Mitigation: land the payload change (Phase 2)
*before* the key change (Phase 3), and keep `lake build` green between them.

**R2 — the live guard `blockingWorldS4` is collateral. MEASURED AND CLOSED (§8).**
`blockingWorldS4` is defined against `successorBirthContent`, so enriching in place changes
`modalApplyOneS4`, `modalTableauS4`, and the `modalExpandBranchesS4` row of
`CslibTests/S4LoopGuardRegression.lean` (asserted OPEN on `cex`). This does **not** endanger
`modalHintikkaSetS4` (§3(a): the guard is invisible to it), only observable verdicts. Measured:
0 verdict changes across 1416 formulas, 0 unsound closures behind fuel exhaustion, and strictly
fewer fuel exhaustions (144 → 60). Residual risk downgraded to low. Fallback, retained but not
expected to be needed: leave `successorBirthContent` alone and add `successorBirthContentPlus`
consumed only by `blockingWorldS4Keyed` — purely additive, zero live-track risk, at the cost of a
duplicated definition and `Plus` twins for the two `blockedRedirect_unwrapped_*` lemmas.

**R3 — field-count churn in `S4LoopInv` / `S4KeyedHintikkaInv`.** If `BoxPlusClosed` is added as
an invariant *field*, `modalTableauS4Keyed_initial` (`FrameCompleteness.lean`) breaks: its
`refine ⟨⟨?_, List.nodup_nil, ?_, accFreshInv_empty _, ?_, …⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩`
is positional. **Recommendation: do not add a field.** `BoxPlusClosed` should be a *derived
lemma about `successorBirthContent`*, threaded as an extra hypothesis where needed — the same
treatment `keysOriginS4` and `keysRootEmpty` already receive ("threaded the same way as
`keysOriginS4` itself: an extra hypothesis, never an `S4LoopInv` field"). This keeps the
`FrameCompleteness.lean` gate at zero edits.

**R4 — regression-test verdicts.** All six `#guard_msgs in #eval` assertions in
`CslibTests/S4LoopGuardRegression.lean` are verdict-only (`"CLOSED"`/`"OPEN"`). The keyed rows
(cex unordered CLOSED, cex ordered OPEN, B axiom OPEN ×2, T axiom CLOSED ×2) are all measured
preserved. The one live-driver row is R2's exposure.

**R5 — step count grows.** Box-plus mints more worlds on some inputs (`phiW`: 4 worlds vs 3).
Fuel-exhaustion count stayed at 0/8532 at fuel 100 in both orderings, and the world bound is
unchanged (§6), so `modalFuelS4` sufficiency transports — but this is the one place where a
larger corpus would add confidence.

---

## 8. Live-Guard Measurement (probe 2) — R2 Is Closed, and Favourably

Spot checks:

```
cex   live reference = OPEN     live BOXPLUS = OPEN     (the regression row's assertion holds)
T     liveRef=CLOSED  livePlus=CLOSED
4     liveRef=CLOSED  livePlus=CLOSED
K     liveRef=CLOSED  livePlus=CLOSED
B     liveRef=OPEN    livePlus=OPEN
```

Corpus sweep, 2 atoms, size ≤ 5, fuel 60, **1416 formulas**
(`artifacts/s4boxplus_live_small.lean`, `artifacts/live-probe-small-output.txt`):

| Cell | Count |
|---|---|
| closed (reference / box-plus) | 252 / 252 |
| fuel-exhausted (reference / box-plus) | 144 / **60** |
| open→closed (soundness regression) | **0** |
| closed→open (completeness change) | **0** |
| `none`→closed | **0** |
| `none`→open | 84 |
| `some`→`none` (termination regression) | **0** |
| unsound candidates (`none`→closed re-checked at reference fuel 600) | **0** |

**The `none` cells had to be audited separately and were.** The open→closed / closed→open
counters ignore fuel-exhausted rows by construction, so a formula the reference could not decide
but box-plus *closes* would slip past them — that is exactly where an unsound closure would hide.
There are none: `none`→closed is 0.

The result is better than neutral. Box-plus decides **84 more formulas** within the same fuel and
regresses none, because `blockingWorldS4` requires `relevantSetFinset = successorBirthContent` as
an **equality**. An unwrapped-only birth content can never equal the live relevant set of a
matured world, since the 4-rule has by then added the boxed pairs to that world. Enriching the key
is what makes the equality reachable, so blocking fires more reliably and fewer worlds are minted.

The larger live sweep (2 atoms, size ≤ 6, fuel 100, **8532 formulas**,
`artifacts/s4boxplus_live.lean` → `artifacts/live-probe-full-output.txt`) completed and confirms
the pattern at scale:

| Cell | Reference | Box-plus |
|---|---|---|
| closed | 1650 | 1650 |
| fuel-exhausted | 893 | **412** |
| open→closed | — | **0** |
| closed→open | — | **0** |

Caveat, stated precisely: the `none`-cell audit (the `none`→closed check, which is the one that
matters for soundness) was run at size ≤ 5 / fuel 60, not at size ≤ 6 / fuel 100. Re-running it at
the larger size would strengthen the evidence and is cheap; it is not a blocker.

**R2 may be treated as closed.** In-place enrichment of `successorBirthContent` is the recommended
site, and the `successorBirthContentPlus` fallback is no longer expected to be needed.

---

## 9. Suggested Phasing (5 phases, each one agent run)

1. **Definitions, no behaviour change.** Add `boxPlusPair`, `boxPlusExtraS4`,
   `modalApplyOneS4KeyedMint` and its two shape lemmas, all unreferenced. `lake build` green by
   construction (purely additive, Task D's pattern).
2. **Switch the mint payload.** Point `modalApplyOneS4Keyed`'s two unblocked arms at
   `modalApplyOneS4KeyedMint`; restate `_boxNeg_unblocked_eq`/`_diaPos_unblocked_eq`; migrate the
   18 Class-A sites. Key still unenriched — `keyLowerBd` still provable (the key is a subset of a
   now-larger relevant set). **Green checkpoint.**
3. **Re-prove the Class-B payload lemmas**: `_outputs_subset_S4` pair,
   `_outputsSubsetUniverse_S4`, `_preserves_bClosure`, `_preserves_worldsContiguousS4`,
   `_preserves_S4KeyedHintikkaInv`. **Green checkpoint.**
4. **Enrich the key**: `successorBirthContent` + `BoxPlusClosed` + the three
   `successorBirthContent_*` lemmas + both `_preserves_keyLowerBd`. **Gate:
   `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`.**
5. **Land the payoff**: `blockedRedirect_boxed_boxPos_mem`/`_diaNeg_mem`; re-check
   `hintikka_congr_S4`; `lake test`; sorry census still exactly 1; `lake shake` findings still 9
   with none in Modal/Tableau.

Zero-debt note: if Phase 4's gate cannot be repaired sorry-free, mark **[BLOCKED]** with the goal
state reached. Do not add a `sorry`, and do not substitute a vacuous definition. The R2 fallback
(a separate `successorBirthContentPlus`) is the sanctioned narrowing if the live track is the
obstruction; it is not a narrowing of Phase 4's own obligation.

---

## 10. Scope Boundary

Box-plus is S4-scoped and **must not be lifted into `Foundations/`**. The Lemmon filtration and
Chagrov–Zakharyaschev Proposition 3.6 are stated for transitive models only. Neither source is
ingested in the local literature corpus, so the attribution here is carried forward from the task
description and the 553 audit rather than verified against the texts — flagged, not asserted. The
in-tree justification is self-contained and sufficient: boxed transmission is exactly what
`modalFourBoxProp` derives one step later on any branch where the mint edge exists, and `s4FC`
supplies the transitivity that makes it sound.

---

## 11. References

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — `successorBirthContent`, `blockingWorldS4`,
  `blockingWorldS4Keyed`, `modalApplyOneS4Keyed`, `S4LoopInv`, `S4KeyedHintikkaInv`,
  `hintikka_congr_S4`, `modalHintikkaSetS4`, and both `_preserves_keyLowerBd`.
- `Cslib/Logics/Modal/Tableau/Rules.lean` — `modalApplyOne` (**do not edit**).
- `Cslib/Logics/Modal/Tableau/FrameRules.lean` — `modalFourBoxProp`, `modalFourDiaNegProp`.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalTableauS4Keyed_complete`,
  `modalTableauS4Keyed_initial`.
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — `def modalSubfmls`.
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean:343` — `boxDiamondPersistence`.
- `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/02_redirect-inertness-divergence-audit.md`
  §4 "R-new" — the boxed-only precursor and its cost accounting.
- `specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4boxed.lean` — boxed-only
  executable variant.
- `specs/563_tableau_boxplus_birth_keys/artifacts/s4boxplus.lean`,
  `.../s4boxplus_live.lean`, `.../live-probe-output.txt` — this session's measurements.
