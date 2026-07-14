# Task 419 — The Full Abstract Picture and Curated Result Inventory

**Task type**: cslib (SPIKE — deep synthesis, read-only; no Lean edits)
**Date**: 2026-07-01
**Session**: sess_1782886680_e1cb20 (main-loop research; subagents unavailable under weekly limit)
**Mandate (user)**: Learn everything the blocker teaches. Map all nearby results that *could*
be established, understand the full picture, and curate a **coherent set of results** worth
establishing — leaving aside those that don't matter or "only make a mess." Produce a clear,
definitive vision of the abstract picture.

**Supersedes**: the *disposition* of reports 01–03 (not their source facts). Reports 02/03
established the abstraction is real and the forward lift is done; this report resolves what the
blocker actually *is*, what it forks into, and which results are worth establishing.

---

## 0. Headline — the blocker is a *design fork*, not a wall

Ground truth, re-verified against current committed source this session (all files tracked,
`sorry = 0`):

- The unifying abstraction **exists and is green**: `ProofSig / Deriv / ProofSigHom / Deriv.map`
  with functor laws `map_height`, `map_id`, `map_comp`
  (`Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean`, 317 ln, sorry-free).
- The **forward lift is delivered for all three logics** as `Deriv.map` corollaries: Modal
  (full `Equiv`), PL (full `Equiv`), Bimodal (forward map + HEq intertwining for
  `DerivationTree.lift`). The three overlay files are committed sorry-free.

So **task 419's literal payload — "ONE derivation-lifting result reusable by Modal, Bimodal, and
PL" — is already met in the forward direction.** The `[BLOCKED]` status is not about the lift.
It is about *one strictly-optional layer above it* (backward maps / full `Equiv` for
multi-closure logics), and that layer is gated by **a single representation choice**, not by any
mathematical obstruction. The right output of this spike is therefore not "prove more" but
"decide which of two coherent visions we are building, then establish exactly the results that
vision needs — and no others."

---

## 1. What is established (verified current source)

| Result | Location | State |
|---|---|---|
| `ProofSig F` (`Ax : F → Type`, `closures : List (F → F)`) | ProofSystemMorphism.lean:55 | green |
| `Deriv σ` (5 ctors: ax/assum/mp/close/weak) | :72 | green |
| `ProofSigHom` (`g`, `g_imp`, `axMap`, **Type-valued** `clMap`) | :124 | green |
| `Deriv.map` (the universal forward lift) | :186 | green, sorry-free |
| `map_height`, `map_id`, `map_comp` (functor laws, HEq form) | :209–312 | green |
| Modal overlay: `modalEquiv` + `liftDerivation`/`Derivable_mono` corollaries | Modal/.../LiftViaMorphism.lean | **FULL** |
| PL overlay: `plEquiv` + `liftDerivationTree`/`derivable_mono` corollaries | PL/.../LiftViaMorphism.lean | **FULL** |
| Bimodal overlay: `bimodalSig`, `bimodalHom`, `toDeriv`, `toDeriv_lift` | Bimodal/.../LiftViaMorphism.lean | **forward + HEq only** |

Key structural fact that makes the *forward* direction clean: `ProofSigHom.clMap` is already
**`Type`-valued** (a `Subtype` `{ m' // m' ∈ closures ∧ naturality }`, not a `Prop` `∃`). The
`close` case of `Deriv.map` extracts the witness `m'` *as data*, so no large elimination arises
going forward. This was the correct call and is why Modal/PL/Bimodal all lift with one functor.

---

## 2. The precise boundary — one sentence

> The `Deriv.close` constructor carries its closure-membership as a **`Prop`**
> (`hm : m ∈ σ.closures`, i.e. `List.Mem`, ctors `head`/`tail`); a **backward** map
> `ofDeriv : Deriv σ Γ φ → NativeDerivationTree …` must, in the `close` case, decide *which*
> closure `m` is, i.e. eliminate that non-singleton `Prop` into a `Type`-valued derivation —
> **large elimination the kernel forbids.**

Why only Bimodal hits it (asymmetry that reveals the true cause):

- **PL**: `closures = []` → the `close` case is vacuous → no dispatch → clean.
- **Modal**: `closures = [box]` → `List.mem_singleton` collapses `hm` to the *equality* `m = box`
  (a subsingleton) → clean `rfl` dispatch, full `Equiv`.
- **Bimodal**: `closures = [box, allFuture, swapTemporal]` → three-way `head/tail/tail` case on a
  `Prop` → forbidden.

The `Classical.choice` escape is a **trap, not a fix**: it yields a noncomputable `ofDeriv` whose
round-trip `ofDeriv ∘ toDeriv = id` is *unprovable* (choice is opaque), so it cannot deliver an
`Equiv` — it only launders the debt (documented at Bimodal/…/LiftViaMorphism.lean:46–48).

**The blocker is thus 100% a representation artifact of encoding `closures` as a `List` and the
witness as `Prop` membership.** Change the witness to *data* and it evaporates — cleanly,
sorry-free, computably.

---

## 3. The representation fork (the actual decision)

Three ways to encode the closure witness so backward dispatch is legal. Ranked by
churn-to-cleanliness.

### Option R1 — **surgical**: keep `closures : List`, index `close` by `Fin length`  *(recommended enabler)*
```lean
-- ProofSig unchanged: closures : List (F → F)
| close (i : Fin σ.closures.length) (φ) (d : Deriv σ [] φ)
      : Deriv σ [] (σ.closures.get i φ)
-- clMap becomes an index map with naturality:
clMap : ∀ i : Fin σ₁.closures.length,
    { j : Fin σ₂.closures.length // ∀ φ, g (σ₁.closures.get i φ) = σ₂.closures.get j (g φ) }
```
- Backward `close` case now cases on `i : Fin n` — **`Fin n` is data**, elimination into `Type`
  is legal; round-trip provable; fully computable.
- `ProofSig` signature is *unchanged* (still `List`), so the ergonomic "here are my closures"
  reading survives. Only `close`, `clMap`, `Deriv.map`, and the 3 overlays change.
- Modal/PL are unaffected in *kind* (their proofs get slightly simpler, uniform with Bimodal).

### Option R2 — `closures : Fin n → (F → F)` (the reports' framing)
Equivalent power to R1; changes the `ProofSig` field itself to an indexed family. Slightly more
invasive (every signature literal restated as a `Fin`-family) with no benefit over R1. Prefer R1.

### Option R3 — per-signature `ClosureTag` inductive + `op : Tag → (F → F)`
Best *ergonomics* (named tags, exhaustiveness on `necessitation/temporal_*`) but adds a `Type`
field to `ProofSig` and a bespoke inductive per logic. Overkill unless a logic has many closures
with meaningful names. Not warranted for ≤3 closures.

**Verdict:** R1 is the clean, minimal, computable enabler. It is sorry-free and touches only the
Foundations file + 3 overlays (no concrete-logic inductive is touched — the non-invasive A1
posture is preserved).

---

## 4. The full result lattice (everything nearby that *could* be established)

Grouped by the layer they belong to, with cost and dependency on R1.

**Layer 0 — the lift (DONE).** `Deriv.map` + functor laws; the four lifts as instances.
*Delivered; needs nothing further.*

**Layer 1 — cheap forward corollaries (no R1 needed).**
- `map_length` / context-length preservation; generic `weakening`/`mono` phrased on `Deriv`.
- Bimodal `liftDerivationWith` **as a `Deriv.map` instance** (report 03 §5.1): the cross-syntax
  morphism `liftHom a : ProofSigHom (extSig fc) (bimodalSig fc)` with `g = liftFormula a`. Pure
  **assembly** — every naturality/axiom lemma (`liftFormula_imp`, `liftFormula_swapTemporal`,
  `liftAxiom`, `liftAxiom_preserves_minFrameClass`) already exists; freshness stays orthogonal.
  *Cost: ~1 bridge def + 1 hom + a HEq intertwining lemma. Sorry-free. No R1 needed.*

**Layer 2 — backward maps / full equivalences (needs R1).**
- `ofDeriv` for Bimodal; `bimodalEquiv : DerivationTree fc Γ φ ≃ Deriv (bimodalSig fc) Γ φ`.
- Uniformizes Modal/PL/Bimodal to *all* have full `Equiv` (removes the "Modal is special because
  singleton" asymmetry).
- *Cost: R1 refactor + one backward recursion + two round-trip proofs per logic.*

**Layer 3 — generic metatheory on `Deriv σ` (needs R1 + Layer 2 to be *useful*).** The real
prize *if* pursued:
- Generic **deduction theorem** on `Deriv σ` (given the imp-structure), transported to each logic.
- Generic **height/subformula induction** principle reused across logics.
- Generic **soundness skeleton**: given a semantic algebra, axiom-soundness, and per-closure
  soundness, derive soundness of `Deriv σ` once; pull back to each logic via the `Equiv`.
- *Cost: substantial; this is a metatheory programme, not a lemma.*

---

## 5. Curation — what to establish, what to drop, what would make a mess

### Worth establishing (the coherent core)
1. **Layer 0** — done; keep and document as the headline result.
2. **Layer 1 `liftDerivationWith`-as-instance** — *only if* the conservativity development wants
   the unification visible there; it is redundant with the existing direct `liftDerivationWith`,
   so it is a "nice-to-have completeness of the instance table," not load-bearing.

### Leave aside — does not matter
3. **Layer 1 `map_length` et al.** — establish lazily, only when a consumer needs them. No
   speculative lemma-farming on `Deriv`.

### Actively makes a mess — do NOT do
4. **A2 maximal unification** (replace every native `DerivationTree` by `Deriv σ`): 193 files,
   79 Bimodal + 23 Modal constructor-match sites regress from named ctors to `close m hm`
   dispatch, exhaustiveness checking lost, soundness/completeness inductions permanently
   degraded — with **zero proof-side payoff**. Confirmed by report 02 §6. Reject.
5. **Predicate-ifying Bimodal's `Axiom`** (`Formula → Prop` instead of the `Type` family): breaks
   `liftDerivationWith` (which needs the 42-constructor data); erases exactly what conservativity
   consumes. Reject.
6. **`Classical.choice` backward map**: noncomputable + unprovable round-trip; launders debt into
   an opaque axiom while still failing to give an `Equiv`. Reject (§2).
7. **R1 refactor + full Equivs with no Layer-3 consumer**: if we do the representation change and
   the equivalences but never prove/transport a single generic metatheorem through the backward
   direction, we have paid for plumbing with no payoff (report 02's honest A1 caveat). This is the
   subtle mess to avoid — see §6.

---

## 6. The decision that clarifies the whole picture

Everything above collapses to one question about the *purpose* of `Deriv σ`:

> **Is `Deriv σ` a lifting device, or a shared-metatheory substrate?**

**Vision A — lifting device (already realized).**
`Deriv.map` *is* the unifying result; the four lifts are its instances; backward maps are not
needed. Modal/PL get full `Equiv`s for free (singleton/empty closures); Bimodal gets
forward + HEq, which is *sufficient to exhibit the lift*. **This vision is essentially complete
today.** Under Vision A, the correct disposition of task 419 is **DONE** (payload delivered), and
the `Fin`-index refactor is *not warranted* — the `List`/`Prop` encoding is fine because nothing
ever runs backward. The current `[BLOCKED]` is then a mislabel: it should be **"forward-complete;
backward Equiv intentionally out of scope."**

**Vision B — shared-metatheory substrate.**
`Deriv σ` becomes the object on which generic metatheorems (deduction theorem, height/subformula
induction, a soundness skeleton) are proved **once** and transported to every logic. This is
genuinely valuable *iff* the project intends to consume such generic results. It **requires** the
R1 representation change (to get computable backward maps + provable round-trips), then Layer 2
Equivs, then **at least one real Layer-3 metatheorem actually consumed downstream** to justify the
plumbing. Under Vision B, task 419 is a **multi-phase programme**, and R1 is its first phase.

**The blocker's lesson, stated plainly:** the `List.Mem` large-elimination wall is the exact point
where "lifting" (needs only forward + a `Type`-valued `clMap`, which we have) diverges from
"equivalence / shared metatheory" (needs the closure witness to be *data*). The wall is not an
accident — it is the abstraction telling us these are two different ambitions, and only the second
one has to pay the R1 price. Choosing which ambition we hold is the whole decision.

---

## 7. Recommendation and task disposition

1. **Adopt Vision A as the delivered result now.** Re-frame task 419 from `[BLOCKED]` to a
   **completed forward-lift unification** with a documented, *deliberate* scope line: Modal/PL full
   `Equiv`, Bimodal forward + HEq, no backward `Equiv`. Optionally fold in Layer-1
   `liftDerivationWith`-as-instance for table completeness. Nothing here is blocked or sorry.

2. **Gate Vision B behind a concrete consumer, as a new bounded task — do not auto-pursue.** Only
   if/when the project wants a generic metatheorem reused across logics (deduction theorem,
   soundness skeleton, shared induction), open a task whose **Phase 1 is exactly R1** (surgical
   `Fin length` witness), **Phase 2** the Bimodal `ofDeriv`/`bimodalEquiv` + uniform Modal/PL
   Equivs, and **Phase 3** the *first real* generic metatheorem + its transport (this phase is the
   ROI justification; without it, do not start Phase 1).

3. **The one anti-goal to record permanently:** never pursue A2 (inductive replacement),
   `Prop`-axiom, or `Classical.choice` backward maps. They are the three "mess" attractors around
   this problem.

**Net vision (one paragraph).** CSLib now has a real *morphism-of-proof-systems* layer whose
functorial action is the single derivation-lifting result the four native lifts instantiate — that
is done and green. The only thing the blocker gates is an *equivalence/metatheory* layer on top,
and it gates it for a precise, honest reason: backward transport needs the closure witness to be
data, not a `Prop`. That is a one-line representation change (R1) with no mathematical risk — but
it is worth spending **only** in service of a concrete shared-metatheorem goal. Absent that goal,
the coherent, complete, mess-free result is exactly what exists today: forward unification,
Modal/PL equivalences, Bimodal forward-lift, and a clearly-drawn scope boundary.

---

## Appendix — files read this session (ground-truth verification)
- `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` (whole, 317 ln) — abstraction + functor laws
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean:1–90` — Bimodal overlay + documented obstruction (:41–50)
- Existence/sorry/tracked check on all 8 core files (ProofSystemMorphism, 3× LiftViaMorphism, Modal/Bimodal Lifting, GenericMCS, InferenceSystem)
- Prior reports 02 (virtuous-unification) and 03 (verdict-current-source) absorbed, not re-derived
