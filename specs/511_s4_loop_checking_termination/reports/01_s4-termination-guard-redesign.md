# Research Report: Task #511 — S4 Loop-Checking Termination Bound & Decidability

- **Task**: 511 — s4_loop_checking_termination (follow-on to task 506, Phase 8/9)
- **Type**: cslib
- **Session**: sess_1784075478_630e1e_511
- **Date**: 2026-07-14
- **Files studied**: `Cslib/Logics/Modal/Tableau/{LoopChecking,Rules,Saturation,Branch,FmpMeasure,CompletenessLoop,GenericDriver}.lean`; task 506 plan Phase 8/9 BLOCKER note.
- **Central deliverable**: a concrete redesign of the S4 minting-guard / loop invariant so that per-step distinctness is genuinely preserved, with Lean lemma signatures and the pigeonhole argument; plus a decisive finding about Phase 9's reuse of task 510.

## Executive Summary

Three findings, in decreasing order of impact on the task plan:

1. **[Phase 9 blocker is worse than documented]** Task 510's generalized loop lemma
   `modalExpandBranchesGen_hintikka` (CompletenessLoop.lean:876) **cannot be instantiated for
   S4**, even though 510 landed all 9 phases. It still requires `spec : RuleApplicationSpec
   apply` (which S4 provably cannot supply — Correction 3) AND a per-branch `ModalLoopInvGen
   apply … rank` whose `potentialInv` field embeds `ModalPotentialInv`'s `rankBound`/`rankEdge`
   and whose `phiBound` is `… ≤ geomCap …` (both of which S4 provably violates — Correction 1).
   510 abstracted the **rule** but not the **termination measure**. The task 506 plan's "Task
   510 Gate" — which asked only whether 510 concludes in `modalHintikkaSetGen` vs
   `modalHintikkaSet` — checked the wrong thing: 510 does conclude in `modalHintikkaSetGen`
   (good), but the *hypotheses* are the real obstruction. Phase 9 needs an **independent
   generalization** (abstract the termination measure/invariant) or an S4-specific
   re-derivation.

2. **[Both Phase 8 gaps confirmed; live-set distinctness is provably not a loop invariant]**
   `worldSetsDistinct` (LoopChecking.lean:947) states pairwise distinctness of worlds'
   *relevant sets over the current branch `b`*. Because `b` only ever grows and a world's
   relevant set therefore only grows, distinctness is **not monotone-stable**: a persistent
   rule firing can fill in the single coordinate on which two worlds differed, collapsing them
   (Gap 1). And the guard checks the *source* world's set, not the *prospective successor's*
   content, so a fresh world can be born already-equal to an existing one (Gap 2). The fix
   must restate the invariant over **stable birth data**, not the live branch. Concrete
   redesigns are given below.

3. **[Exponent mismatch]** The stated bound `modalWorldBoundS4 φ₀ := 2 ^ (modalSubfmls φ₀).length`
   (LoopChecking.lean:868) is **too small** for the `sameRelevantSet` notion, which
   distinguishes *both signs*: a relevant set is a subset of `modalSubfmls φ₀ × Sign`, of which
   there are `2 ^ (2·|modalSubfmls φ₀|)`. The correct pigeonhole codomain has cardinality
   `2 ^ (2·|Sf|)`, i.e. `4 ^ |Sf|`. Since decidability needs only *a* computable finite bound,
   bump `modalWorldBoundS4` to `2 ^ (2 * (modalSubfmls φ₀).length)` (or `4 ^ …`) and re-check
   `modalUniverseS4_length_le`. Do **not** ship the tight `2^|Sf|` — it is unprovable for the
   current relevant-set notion.

Zero-debt is respected throughout the recommendation: no path relies on `sorry`, `axiom`, or a
vacuous placeholder. Where a proof is out of reach in one implementation run, the recommendation
is decomposition, not deferral.

---

## 1. The Phase 8 Machinery As It Stands

### 1.1 What the branch/driver guarantees (verified against source)

- `modalStepBranchGen apply b e acc` (Saturation.lean:122) selects the first `sf ∈ b` not in
  `expanded`, runs `apply sf b acc`, and appends the result to the **front** of `b`
  (`newForms ++ b`). **The branch only ever grows** — no formula is ever removed. (Verified:
  every `RuleResult` arm produces `_ ++ b` or `branches.map (· ++ b)`.)
- Worlds are minted consecutively: `modalNextWorld b = modalMaxWorld b + 1` (Branch.lean:99).
  Every minting event creates the next integer world, so **#worlds ever created = modalMaxWorld
  b + 1**, and bounding `modalMaxWorld b` is exactly bounding the number of minting events.
- `modalKnownWorlds b` (Branch.lean:89) = all labels appearing in `b`; it only grows.
- K minting (Rules.lean:100-150): `T(◇φ)@w`/`F(□φ)@w` mint `w' = modalNextWorld b` born with
  `{witness ⟨s,φ,w'⟩} ∪ {⟨.pos,ψ,w'⟩ : T(□ψ)@w ∈ b} ∪ {⟨.neg,ψ,w'⟩ : F(◇ψ)@w ∈ b}`. Note the
  box-propagated formulas are the **unwrapped bodies** `⟨.pos,ψ⟩`, not `⟨.pos,□ψ⟩`.
- The S4 4-rule (`modalFourBoxProp`/`modalFourDiaNegProp`) is a **persistent** rule that copies
  the box *itself* (`T(□ψ)`, `F(◇ψ)`) forward along recorded edges — this is what
  `hintikkaS4_box_pos_step` (LoopChecking.lean:421) proves survives one edge.

### 1.2 The current guard (LoopChecking.lean:253-264)

`modalApplyOneS4 φ₀` intervenes only at the two minting shapes. At `⟨.neg,.box φ,w⟩` /
`⟨.pos,.diamond φ,w⟩` it consults `blockingWorld φ₀ b sf.label`, which searches
`modalKnownWorlds b` for the least `w' ≠ w` with `sameRelevantSet φ₀ b w w' = true`
(LoopChecking.lean:195-197). Blocked ⇒ `(.linear [], acc.addEdge w wBlock)` (loop-back, no new
world). Unblocked ⇒ the underlying K rule mints `modalNextWorld b`.

### 1.3 The relevant-set notion (LoopChecking.lean:100-130)

`sameRelevantSet φ₀ b w w' = true ↔ ∀ (s : Sign) (ψ ∈ modalSubfmls φ₀), ⟨s,ψ,w⟩ ∈ b ↔
⟨s,ψ,w'⟩ ∈ b`. Define the **relevant set** of a world:
`R(b,w) := {(s,ψ) ∈ Sign × modalSubfmls φ₀ : ⟨s,ψ,w⟩ ∈ b}`. Then
`sameRelevantSet φ₀ b w w' = true ↔ R(b,w) = R(b,w')`, and `R(b,w)` is **monotone increasing in
`b`** (formulas are only added). Codomain cardinality: `2 ^ (2·|Sf|)`.

---

## 2. Why `worldSetsDistinct` Is Not a Loop Invariant (both gaps proved)

### Gap 1 — persistent growth collapses distinct worlds (the plan's anticipated gap, confirmed)

Let `a ≠ b'` be known worlds with `R(b,a) ≠ R(b,b')`, and suppose they differ **only** at one
coordinate `(s₀,ψ₀)` with `⟨s₀,ψ₀,b'⟩ ∈ b` and `⟨s₀,ψ₀,a⟩ ∉ b`. A persistent rule (K `boxPos`,
T self-propagation, or the 4-rule) may add exactly `⟨s₀,ψ₀,a⟩` to the branch (it is not
otherwise filtered — persistent rules only filter formulas *already present*). After that step
`R(b',a) = R(b',b')` — the two worlds are now identical. `worldSetsDistinct` referred to the
pre-step `b`; it is false for the post-step branch. **Nothing in `modalApplyOneS4`'s persistent
arms re-checks distinctness after appending**, and the guard fires only at minting shapes.

The root cause is structural, not a missing check: because `R(·,·)` grows monotonically, a
"forward-stable" distinctness witness (`⟨s,ψ,a⟩ ∈ b ∧ ⟨s,ψ,b'⟩ ∉ b` that will *never* be filled
in) is not locally recognizable. Therefore **no strengthening of the live-branch predicate
`worldSetsDistinct` can make it a per-step invariant** — the invariant must be stated over data
that does not change after a world is born (Section 4).

### Gap 2 — the guard checks the source world, not the successor (confirmed)

`blockingWorld φ₀ b w` compares `R(b,w)` (the *source*) against other worlds. But the newly
minted `w'` is born with content `BC(b,w,s,φ) := {witness (s,φ)} ∪ {(.pos,ψ) : T(□ψ)@w ∈ b} ∪
{(.neg,ψ) : F(◇ψ)@w ∈ b}` — the box-propagated *bodies*, **not** `R(b,w)`. `R(b,w)` typically
contains `(s,◇φ)`/`(s,□φ)` and other formulas at `w` that are *not* in `BC`, and `BC` contains
the unwrapped bodies that are *not* in `R(b,w)`. So `R(b,w) = R(b,w'')` for some existing `w''`
is neither necessary nor sufficient for the fresh world `w'` to duplicate `w''`. The guard's
check is **unrelated to the distinctness it is supposed to enforce at the successor**. Even on
the unblocked branch, nothing prevents `R(b',w') = R(b',w'')` at the instant of birth.

**Conclusion.** `worldSetsDistinct` over the live branch is unsound as a loop invariant on two
independent counts. The redesign must (i) key worlds on stable birth data, and (ii) make the
guard compare the *prospective successor's content* (not the source's).

---

## 3. Decisive Phase 9 Finding — Task 510 Does Not Unblock S4

The task 506 plan (lines 166-171) raised exactly one requirement on task 510: that its
generalized loop lemma conclude in `modalHintikkaSetGen apply bR aR` rather than
`modalHintikkaSet bR aR`. **510 satisfies that requirement** (CompletenessLoop.lean:856-890
concludes in `modalHintikkaSetGen apply bR aR`). But that was the wrong thing to gate on. The
lemma's **hypotheses** are unsatisfiable for S4:

```
lemma modalExpandBranchesGen_hintikka
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)          -- (A) S4 CANNOT supply
    (φ0 : Proposition Atom) (fuel : Nat) :
    ∀ … accs …,
      modalExpMeasure (modalUniverse φ0) branches expandedSets ≤ fuel →   -- (C) K universe/geomCap
      (∀ i …, ∃ rank, ModalLoopInvGen apply φ0 bi ei ai rank) →           -- (B) S4 CANNOT supply
      … modalExpandBranchesGen apply … = .openBranch bR aR →
      modalHintikkaSetGen apply bR aR
```

- **(A)** `RuleApplicationSpec apply` — GenericDriver.lean:105-108 explicitly names task 506 as
  the system that *cannot* discharge it (`outputsSubsetUniverse` presupposes the depth-based
  `modalWorldBound`; `rankStep` demands the exact per-edge rank decrement the 4-rule breaks).
- **(B)** `ModalLoopInvGen apply φ0 b e acc rank` (CompletenessLoop.lean:133) has field
  `potentialInv : ModalPotentialInv φ0 b e acc rank`, which includes
  `rankBound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label` and
  `rankEdge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w` (FmpMeasure.lean:2342-2344) —
  the two rank fields Correction 1 shows the 4-rule and loop-back edges falsify. It further has
  `phiBound : … ≤ geomCap (modalSubfmls φ0).length (modalDepth φ0)` — the geometric tree
  capacity that D2 explicitly says does not transfer to S4.
- **(C)** Fuel is measured against `modalUniverse φ0` (the K universe, geomCap-sized), not
  `modalUniverseS4`.

**Net:** task 510 generalized the *rule slot* (`apply`) but kept the K/T *termination
scaffolding* (`RuleApplicationSpec` + `ModalPotentialInv` rank fields + `geomCap` + K universe)
hard-wired into both the hypotheses and the fuel measure. S4 replaces exactly that scaffolding.
So Phase 9 **cannot** be `modalExpandBranchesGen_hintikka` instantiated at `modalApplyOneS4`.
This is an independent blocker from Phase 8's bound.

### Implications for Phase 9 (what a follow-on must choose between)

- **Option 9-A (further generalization, preferred if pursued):** introduce a *third*
  generalization that abstracts the termination measure/invariant. Replace the
  `(spec, ModalLoopInvGen, modalExpMeasure ∘ modalUniverse)` triple with an abstract interface
  — e.g. a typeclass/structure `LoopTermination apply` bundling: an abstract universe `U`, a
  per-branch invariant `Inv`, a proof that `modalStepBranchGen apply` preserves `Inv`, that
  saturated `Inv`-branches satisfy the four `modalHintikkaSetGen` conjuncts, and that
  `modalExpMeasure U` decreases. `S4LoopInv` + the world bound would instantiate `Inv`/`U`. This
  is a shared-file (`CompletenessLoop.lean`) change touching K's consumers — **coordinate as its
  own task**, and note it also benefits task 505 (B-system) and 513.
- **Option 9-B (S4-specific re-derivation):** port `modalExpandBranchesGen.processNext`'s
  ~700-line fuel-induction to an S4 driver with `S4LoopInv`. The plan explicitly wanted to avoid
  this; it is the fallback if 9-A is judged too invasive.

Either way, **Phase 9 is gated on Phase 8** (the world bound feeds fuel sufficiency and the
universe) *and* on this generalization — two independent gates, not one.

---

## 4. The Core Deliverable — Concrete Guard / Invariant Redesign

The redesign must satisfy: (R1) the keyed quantity is **stable** (unchanged by later steps);
(R2) the guard blocks on the **successor's** prospective content; (R3) the resulting invariant
is preserved by *every* `modalStepBranchS4` step (minting and persistent); (R4) it injects
worlds into a fixed finite codomain for the pigeonhole.

Two viable designs. **Option A is recommended** (it makes both Phase 8 and 9 tractable and keeps
the guard's spirit); Option B is a lighter-weight fallback that sacrifices the tight bound.

### Option A (recommended): birth-content guard + monotone-lower-bound invariant

**Idea.** Do not track live-set *equality*. Track, for each world, a **stable lower bound** on
its relevant set — its birth content — and make the guard block on birth-content equality. The
invariant asserts that the birth contents are pairwise distinct AND remain lower bounds. Because
birth content never changes and relevant sets only grow, the invariant is monotone-stable.

Concretely, thread a per-world **birth-key** so it is recoverable. Two sub-options for
recoverability:

- **A1 (recompute-from-witness):** every minted world `w'` carries exactly one witness formula
  `⟨s,φ,w'⟩` at birth. Reconstruct a world's key as the pair `(the box-context of its unique
  predecessor-at-birth, its witness)`. This is fragile because the predecessor's box-context
  keeps growing; not recommended.
- **A2 (thread a key list, recommended):** define an S4-specific step that carries an extra
  `keys : List (WorldIndex × RelevantKey)` alongside `(b, e, acc)`, where
  `RelevantKey := List (Sign × Proposition Atom)` (canonically ordered, or a `Finset`). This
  requires an S4-specific driver rather than reusing `modalStepBranchGen` verbatim — but Section
  3 already shows Phase 9 needs an S4-specific loop anyway, so the incremental cost is low and
  the two changes compose.

Key definitions (signatures; `RelevantKey` as a `Finset` for clean pigeonhole):

```lean
/-- The prospective birth content of the successor minted for `⟨s, μφ, w⟩` at branch `b`:
    the witness plus the S4 box-context transmitted from `w`. Computed at mint time; stable. -/
def successorBirthContent (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Finset (Sign × Proposition Atom)

/-- Redesigned guard: block iff some existing known world's CURRENT relevant set already
    equals the prospective successor's birth content. -/
def blockingWorldS4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Option WorldIndex
```

Stable invariant (replaces `worldSetsDistinct`), stated over the threaded `keys`:

```lean
structure S4LoopInv (φ₀ : Proposition Atom)
    (b e : … ) (acc : Accessibility) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    : Prop where
  … -- the six rule-independent fields, over modalUniverseS4
  /-- Every known world has a recorded key. -/
  keysTotal   : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys
  /-- A world's recorded key is a LOWER BOUND on its live relevant set (monotone-stable). -/
  keyLowerBd  : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w
  /-- Distinct worlds have DISTINCT keys (this is what the guard enforces at birth and what
      no later step can violate, since keys never change). -/
  keysDistinct : ∀ w w' k k', (w,k) ∈ keys → (w',k') ∈ keys → w ≠ w' → k ≠ k'
  /-- Keys are drawn from the powerset of the finite signed-subformula set. -/
  keysInUniverse : ∀ w k, (w,k) ∈ keys → k ⊆ signedSubfmls φ₀
```

Preservation obligations (each a named lemma; all discharge without `sorry`):

- `modalStepBranchS4_preserves_keyLowerBd` — persistent steps only *add* formulas, so live sets
  grow; birth keys are unchanged ⇒ `⊆` is preserved (monotone). This is the step that Gap 1
  broke for the old invariant and that the lower-bound formulation *survives*.
- `modalStepBranchS4_preserves_keysDistinct` — keys never change on any step; on a *minting*
  step the new key is, by `blockingWorldS4 = none`, not equal to any existing key (guard
  contract), and on any *persistent* step no key changes ⇒ distinctness preserved. This is the
  step that Gap 2 broke and that the birth-content guard fixes.
- `modalStepBranchS4_preserves_keysTotal` / `_keysInUniverse` — bookkeeping.

**Why this satisfies R1-R4:** keys are historical constants (R1); the guard compares against the
prospective successor content (R2); every step preserves the four key-fields, minting via the
guard contract and persistent via monotonicity (R3); keys inject into `Finset (Sign × Sf)` (R4).

### Option B (fallback): saturation-stable invariant, looser bound, no driver change

If threading `keys` is judged too invasive, restate distinctness only for **saturated** worlds
(the plan's own fallback hint). Define `worldSaturated φ₀ b acc w` (no pending minting-shaped or
persistent-rule obligations remain at `w`), and assert distinctness only among saturated worlds.
The bound then counts saturated worlds; unsaturated worlds are bounded separately by the fuel
already consumed. This avoids a driver change but complicates fuel sufficiency (Phase 9) and
yields a looser, harder-to-state bound. Recommended only if Option A's driver change is rejected.

### The exponent correction (either option)

Replace `modalWorldBoundS4 φ₀ := 2 ^ (modalSubfmls φ₀).length` with

```lean
def modalWorldBoundS4 (φ₀ : Proposition Atom) : Nat := 2 ^ (2 * (modalSubfmls φ₀).length)
```

and re-verify `modalUniverseS4_length_le` (its RHS `2 * (2*modalComplexity φ₀ + 1) *
(modalWorldBoundS4 φ₀ + 1)` is unaffected in *form*; only the numeric value of the bound
changes, and the proof is by the same `omega`/`ring` structure). This is required because
`sameRelevantSet` (and any birth-content key) distinguishes signs, so the codomain is the
powerset of `Sign × Sf`, of size `2^(2|Sf|)`. Decidability needs only a finite computable bound,
so the loosening is harmless.

---

## 5. The Pigeonhole Argument (sketch + verified Mathlib candidates)

Target lemma (Option A form):

```lean
lemma modalKnownWorlds_length_le_worldBoundS4
    (φ₀ : Proposition Atom) (b e : …) (acc : Accessibility) (keys : …)
    (hInv : S4LoopInv φ₀ b e acc keys) :
    (modalKnownWorlds b).length ≤ modalWorldBoundS4 φ₀
```

Argument:
1. Map each known world `w` to its key `k_w ∈ Finset (Sign × Sf)` via `keysTotal`.
2. `keysDistinct` ⇒ this map is **injective** on `modalKnownWorlds b` (distinct worlds ↦
   distinct keys).
3. `keysInUniverse` ⇒ every key lies in `(signedSubfmls φ₀).powerset`.
4. Cardinality: `(signedSubfmls φ₀).powerset.card = 2 ^ (signedSubfmls φ₀).card =
   2 ^ (2·|Sf|) = modalWorldBoundS4 φ₀`.
5. Injective list into a finite set ⇒ length ≤ card.

Then `modalStepBranchS4_worldBound : modalMaxWorld b < modalWorldBoundS4 φ₀` follows because
worlds are consecutive (`modalMaxWorld b + 1 = #worlds = (modalKnownWorlds b).length` under the
"worlds are dense 0..max" fact, itself a small lemma from consecutive minting).

**Verified Mathlib candidates** (names confirmed via leansearch / local grep):
- `Finset.card_powerset : s.powerset.card = 2 ^ s.card` — step 4.
- `Finset.card_le_card_of_injOn` (confirmed present in `Mathlib/Data/Finset/Card.lean`) —
  injective-image cardinality bound, step 5 if working with the world set as a `Finset`.
- `List.Nodup.length_le_card : l.Nodup → l.length ≤ Fintype.card α` (Mathlib.Data.Fintype.Card)
  and `List.toFinset_card_le` / `List.toFinset_card_of_nodup` — for the list-length form.
- `modalKnownWorlds` nodup: needs a small `modalKnownWorlds_nodup` helper (its `foldl` guards
  against duplicates by `ws.any (· == sf.label)`) — likely already available or one-line.

---

## 6. Reuse-Check Results (CSLib reuse-first)

| Concept | Existing asset | Reuse verdict |
|---------|----------------|---------------|
| Per-world formula sets, equality test | `formulasAtWorld`, `sameRelevantSet` + `_iff/_refl/_symm/_trans` (LoopChecking.lean:76-187) | **Reuse.** Sound and complete; keep for the *comparison primitive*. Only the *guard's argument* (source vs successor) and the *invariant statement* change. |
| Universe/fuel counting engine | `modalWork`, `modalExpMeasure` (FmpMeasure.lean:192/197) | **Reuse verbatim** — universe-parametric, rule/world-agnostic (D2 confirmed). |
| Rule-independent invariant fields | `accFreshInv`, `accTargetsKnown`, `outDeg`, `isMintingShaped` (FmpMeasure.lean:786-1895) | **Reuse** in `S4LoopInv`. |
| Generic saturation/Hintikka loop | `modalExpandBranchesGen_hintikka`, `ModalLoopInvGen` (CompletenessLoop.lean) | **Cannot reuse for S4** — Section 3. Requires `RuleApplicationSpec` + rank/`geomCap`. |
| Generic Hintikka *predicate* | `modalHintikkaSetGen` (Saturation.lean:460) — spec-free | **Reuse.** Verify `modalHintikkaSetS4 φ₀ b acc` matches `modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc` (likely a `rfl`/near-`rfl` bridge; Phase 9 needs this alignment). |
| Rank-based invariant `ModalPotentialInv` | FmpMeasure.lean:2326 | **Do NOT reuse/extend** (Correction 1). `S4LoopInv` is a sibling. |
| Pigeonhole | `Finset.card_powerset`, `Finset.card_le_card_of_injOn`, `List.Nodup.length_le_card` | Mathlib; confirmed present. |

No new *notation* is needed (the guard/invariant are plain defs/structures). No new axiom. No
change to `FmpMeasure.lean` or K/T declarations.

---

## 7. Recommended Decomposition, Risks, Zero-Debt Posture

**Recommended phase structure for the implementation plan:**

1. **P1 — Exponent fix (low risk, land first):** bump `modalWorldBoundS4` to `2^(2·|Sf|)`,
   re-verify `modalUniverseS4_length_le`. Independent, green, commit.
2. **P2 — Guard + key redesign (Option A):** `successorBirthContent`, `blockingWorldS4`,
   `relevantSetFinset`, `signedSubfmls`; rewrite `modalApplyOneS4` to consult `blockingWorldS4`;
   re-run CI across Phases 5-7's consumers (the box-pos/dia-neg bridge lemmas and
   `modalTruthLemmaS4` must still build — they depend on `modalApplyOneS4`'s *non-minting*
   behavior, which is unchanged, so risk is contained but must be verified).
3. **P3 — `S4LoopInv` restatement + preservation lemmas** (`_preserves_keyLowerBd`,
   `_preserves_keysDistinct`, `_preserves_keysTotal`, `_preserves_keysInUniverse`). This is the
   mathematical crux; budget generously.
4. **P4 — Pigeonhole `modalKnownWorlds_length_le_worldBoundS4` + `modalStepBranchS4_worldBound`.**
5. **P5 — Phase 9 generalization decision (9-A vs 9-B)** — treat as a **separate task** if 9-A
   (shared-file interface change) is chosen, since it touches K's consumers and benefits
   505/513. Only after P4 lands.

**Risks:**
- Threading `keys` through an S4 driver means S4 no longer reuses `modalStepBranchGen`
  *definitionally* for the *stepping* (it still can for the rule slot). This ripples into Phase
  9's loop. **Mitigation:** since Phase 9 needs an S4-specific loop regardless (Section 3),
  design P2-P5 and the Phase-9 loop together.
- If the team prefers *not* to change the driver, Option B (saturated-world invariant) is the
  fallback, at the cost of a messier fuel-sufficiency proof.
- The pigeonhole codomain `2^(2|Sf|)` is large but only appears in the *bound*, never computed —
  no performance concern (the tableau computation is the decision procedure; the bound only
  sizes fuel).

**Zero-debt:** every lemma above is expected to close without `sorry`/`axiom`. If P3's
`_preserves_keysDistinct` resists within a run, the correct response is to mark that phase
`[BLOCKED]` with the exact open goal and split, **not** to weaken the invariant to something
vacuous. Option B is a *documented alternative design*, not a debt shortcut.

---

## 8. Open Questions for the Planner

1. Accept the driver change (Option A2) or hold to `modalStepBranchGen` reuse (Option B)? Option
   A gives the tight bound and aligns with the unavoidable Phase-9 loop rewrite; recommended.
2. Phase 9 generalization: pursue 9-A (abstract termination interface in `CompletenessLoop.lean`,
   shared with 505/513) or 9-B (S4-local re-derivation)? 9-A is more reusable but is a
   cross-cutting shared-file task requiring coordination.
3. `modalHintikkaSetS4 φ₀ b acc = modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc` — **verified
   `rfl`**: `modalHintikkaSetGen` (Saturation.lean:460-480) is byte-identical to
   `modalHintikkaSetS4` (LoopChecking.lean:373-393) with `apply := modalApplyOneS4 φ₀`. So the
   Phase-9 *conclusion* type aligns for free. This confirms the conclusion was never the
   obstruction — the `modalExpandBranchesGen_hintikka` *hypotheses* (Section 3) are.
