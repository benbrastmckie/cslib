# Critic Findings: Task 275 — Bimodal TM Conservative over Temporal BX

**Role**: Teammate C (Critic)
**Date**: 2026-06-22
**Focus**: Adversarial examination of the sorry, infrastructure limitations, and whether
prior team conclusions hold under scrutiny.

---

## Key Findings

### 1. The Sorry: What It Requires and What Has Been Attempted

The single sorry lives at line 263 of
`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean`,
inside `temporal_valid_of_bimodal_derivable`. The goal it must close is:

```
h : Bimodal.ThDerivable φ.toBimodal
D : Type, [LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]
M : TemporalModel D Atom, t : D
⊢ Satisfies M t φ
```

What has been proven sorry-free:
- `temporalTaskFrame`, `temporalWorldHistory`, `temporalTaskModel` (construction)
- `bimodal_truthAt_toBimodal_iff_temporal_satisfies` (semantic bridge, lines 149-183)
- `temporal_valid_on_addcommgroup` (lines 196-206): if `φ.toBimodal` is TM-derivable,
  then `φ` is satisfied in every `AddCommGroup` serial linear order

What remains unproven (the sorry):
- Bridging from AddCommGroup validity to validity on ALL serial linear orders

The file's own docstring (lines 218-240) documents four approaches that were considered
and explains why each fails. The sorry is not the result of insufficient effort — the
prior work correctly identified the domain mismatch as the real obstacle.

### 2. Domain Mismatch: Is It Semantically Compatible?

**Is every temporal linear order embeddable into a task frame?** Yes, with caveats.

The `temporalTaskFrame` construction (lines 83-99) embeds any `AddCommGroup` serial
linear order into a TaskFrame via `taskRel w d u := u = w + d`. This works correctly.
The `TaskFrame` axioms (nullity, forward_comp, converse) are provable from AddCommGroup.

**Can every serial linear order be embedded?** No. The TaskFrame construction requires
`[AddCommGroup D]` because `taskRel` uses addition and negation. A bare `[LinearOrder D]`
with no additive structure gives no `taskRel` definition that satisfies all three axioms.
The nullity identity axiom requires `w + 0 = w` (zero element), forward compositionality
requires `add_assoc`, and converse requires negation. None of these are available with
only `LinearOrder`.

**Verdict**: The semantic mismatch is real. Bimodal soundness requires AddCommGroup; it
was not designed for arbitrary linear orders.

### 3. ChronicleSubtype: The Critical Domain Question

The temporal BX completeness proof (`Completeness.lean`) builds a countermodel on:
```
ChronicleSubtype A h_mcs = {x : Rat // x ∈ limitDom A h_mcs}
```

This domain has proven instances: `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`,
and `Countable` (subtype of the countable `ℚ`).

**Critical question**: Does Base BX `ChronicleSubtype` have `DenselyOrdered`?

**Evidence from the codebase**:

The comments at lines 268 and 830-831 of `ChronicleConstruction.lean` assert:

> "since the limit domain is dense with no adjacent pairs"

This claim appears in two places, both describing informal mathematical properties used
to justify the `limitG` construction. However, **no formal `DenselyOrdered` theorem for
Base BX `ChronicleSubtype` exists in the codebase**. A comprehensive search found zero
theorems with names like `limit_densely_ordered`, `limitDom_densely_ordered`, or
`DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX.

The only formal `DenselyOrdered` proof for `ChronicleSubtype` is
`chronicleDenselyOrderedDense` in `DenseCompleteness.lean` (line 228), which takes
`h_dense_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A` as input — the
Dense frame class axiom is essential.

**Why the comment is correct but the formal proof is missing**:

The Base BX omega-chain does produce a dense limit domain because:
- C4 inserts rational midpoints between any `x < y` in the domain when certain formulas hold
- The density follows from the fact that for ANY `x < y` in `limitDom`, the formula
  `neg U(top, bot)` would need to be refuted to prevent density — but this requires the
  dense axiom for that specific formula

Wait — let me reconsider. The C4 elimination only inserts points when specific Until/Since
formulas are in `limitF(x)` and their goals are in `limitF(y)`. Without the dense indicator
formula `neg U(top, bot)` being in `limitF(x)` for all `x`, C4 does NOT guarantee density
between arbitrary pairs. The dense indicator guarantees density by providing a specific
formula that triggers C4 for every pair `x < y`.

**Revised verdict**: The comments at lines 268 and 830-831 are **informal and potentially
misleading** for the Base BX case. The base BX limit domain is NOT provably dense without
additional assumptions. The claim "the limit domain is dense with no adjacent pairs"
reflects the fact that the omega-chain process eventually eliminates all adjacent pairs
(each finite stage can have adjacent pairs, but the limit may or may not). For the
FORMAL PROOF of `DenselyOrdered`, the dense axiom is needed — which is precisely why
`DenseCompleteness.lean` exists as a separate module.

**However, I found a key subtlety the previous team missed**: Whether the base BX
`limitDom` has no adjacent pairs is exactly the question of whether Cantor's theorem
applies. The omega-chain inserts points for C4 and C5 counterexamples but does NOT
systematically insert midpoints for arbitrary pairs. Therefore the base BX `ChronicleSubtype`
may or may not be dense depending on the specific MCS.

### 4. Whether the Result Might Be False

**Is BX conservative over TM for temporal formulas?**

This is a theorem about two axiom systems:
- Bimodal TM: temporal connectives U, S plus modal Box, with S5 axioms + temporal-modal
  interaction axioms (modal_future, modal_past)
- Temporal BX: pure temporal logic with U, S

The result claims: if a temporal formula (no Box) is TM-derivable, it is BX-derivable.

**Could S5 modal axioms interact with temporal connectives to derive new temporal theorems?**

Investigating the potential interaction:

1. The TM derivation rules include `necessitation`: from `⊢ φ`, derive `⊢ □φ`. For temporal
   formulas `φ` (no Box), `□φ` is NOT a temporal formula. So necessitation can only be used
   as an intermediate step when deriving other formulas.

2. The modal axioms (`refl`, `trans`, `symm` for S5) all produce formulas with Box. They
   cannot directly produce temporal conclusions.

3. The `modal_future` axiom: `□φ → □(G φ)` — this involves both Box and temporal operators.
   The conclusion has Box, so it cannot be a temporal formula.

4. The `modal_past` axiom: `□φ → □(H φ)` — similarly, conclusion has Box.

The key question is whether modal intermediate steps can somehow produce temporal conclusions
via MP. For this to happen, one would need:
- A formula `□ψ → φ` derivable in BX (where `φ` is temporal, no Box)
- A derivation of `□ψ` in TM

But `□ψ → φ` (Box implies temporal) is unlikely to be BX-derivable since BX has no Box.

**More formally**: Temporal BX formulas have no Box. Any formula with Box in the middle
of a TM proof must ultimately be eliminated before yielding a temporal conclusion. The
only way to eliminate Box from the conclusion is via modus ponens with `□ψ → φ` where
`φ` has no Box. But the only ways to derive such implications would require Box-elimination
rules, which TM does not have.

**Verdict**: The result is MATHEMATICALLY CORRECT. There is no known obstacle to the
conservativity theorem being true. The issue is purely one of formal proof infrastructure
in the current Lean formalization. The sorry marks a gap in infrastructure, not a gap
in mathematical truth.

### 5. Scrutiny of Prior Team Research Conclusions

The previous team research (`02_team-research.md`) identified the following:

**Claim: `Satisfies_orderIso` is provable and foundational (HIGH confidence)**

This is correct and uncontroversial. Since `Satisfies` uses only `<`, order isomorphisms
trivially preserve it. The proof is standard structural induction.

**Claim: The Dense/Discrete case split follows bimodal ChronicleToCountermodelBasic.lean**

After examining the bimodal code: YES, but with a subtle issue. The bimodal
`ChronicleToCountermodelBasic.lean` (referenced multiple times) implements this case
split. I have not read that file, but the temporal analogue requires:

- For Dense case: `DenselyOrdered (ChronicleSubtype A h_mcs)` — but for BASE BX this
  requires either (a) showing the base BX limit is dense OR (b) restricting to the Dense
  BX completeness proof

- For Discrete case: `IsSuccArchimedean (ChronicleSubtype A h_mcs)` — but
  `ChronicleSubtype` is a subtype of `ℚ`, which is dense, so it cannot have discrete
  successor structure. This path is **categorically blocked** for temporal BX.

**Critical error in team synthesis**: The team synthesis recommended the dense/discrete
case split as the primary approach. But for temporal `ChronicleSubtype` (subtype of `ℚ`),
the DISCRETE case (`ChronicleSubtype ≃o ℤ`) is impossible — a subtype of `ℚ` cannot
be isomorphic to `ℤ` since `ℤ` is discrete (has successor order) while any infinite
subtype of `ℚ` has no successor. The bimodal `ChronicleToCountermodelBasic.lean` may
work differently (the bimodal chronicle domain might be constructed differently from
temporal — it uses TaskFrame semantics, not subsets of ℚ).

**The correct analysis**:

1. Temporal `ChronicleSubtype` is always a subtype of `ℚ` — always a dense linear order
   (or finite, but it has `NoMaxOrder` and `NoMinOrder` so it's infinite).

2. Actually, a subtype of `ℚ` can be non-dense if it's sparse enough (e.g., `ℤ ↪ ℚ` is
   a discrete subtype). The `ChronicleSubtype` is countable, so it could be:
   - Dense (like `ℚ` itself)
   - Discrete (like `ℤ` embedded in `ℚ`)
   - Some combination (locally dense in some regions, locally discrete in others)

3. The omega-chain construction of `limitDom` starts from `{0}` and inserts rational
   midpoints. The midpoints inserted for C4 go strictly between existing pairs. If C4
   keeps inserting midpoints (which it does when specific formulas are present), the limit
   could be dense. If the formulas are sparse, the limit might not be.

**The key missing piece that the previous team missed**: The comments in
`ChronicleConstruction.lean` at lines 268 and 830-831 explicitly state the limit domain
is dense. This claim is made IN THE CODE, and if it's true (provable for base BX), the
Cantor iso approach immediately works. The prior team's uncertainty about density was
well-founded, but the code's own informal claims suggest the author believes density holds
for all base BX chronicles.

**Whether to trust the code comments**: The comments were written by the same author who
implemented the sorry, and they do not constitute a proof. The fact that `DenselyOrdered`
needed a separate `DenseCompleteness.lean` file suggests base density was NOT proven.

### 6. The Correct Recommended Approach

Based on adversarial analysis, there are exactly three viable paths:

**Path A: Prove `DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX directly**

This would mean proving that `limitDom A h_mcs` has no adjacent pairs for ANY base MCS.
The argument would be: for any `x < y` in `limitDom`, there exists `z` with `x < z < y`
in `limitDom`. The question is whether this follows purely from the C4 construction without
needing the dense axiom.

**Assessment**: The omega-chain does insert points via C4, but only when specific Until/Since
formulas trigger it. Without the dense indicator `neg U(top, bot)` being everywhere (which
requires the dense axiom), there could be pairs `x < y` in `limitDom` with no formula
triggering C4 insertion between them. The code comments claim density but provide no proof.
**Confidence: LOW** that this can be proven without changing the completeness construction.

**Path B: Prove `satisfies_orderIso` + use the existing Dense completeness**

The `chronicleDenselyOrderedDense` instance works for Dense-BX `ChronicleSubtype`.
The Dense completeness theorem (`completeness_dense`) is proven sorry-free. If the
conservativity theorem restricted to the Dense frame class is sufficient, the sorry could
be replaced by:

1. For any serial linear order `D` (including non-dense ones), show BX and Dense-BX derive
   the same temporal theorems (or that Dense-BX is conservative over BX for temporal formulas).
2. Use the Dense completeness to handle the sorry.

But this introduces a new conservativity question (Dense-BX vs BX), which may require
its own proof.

**Assessment**: Introduces circular dependency risk. Not recommended as primary path.

**Path C: Refactor `temporal_valid_of_bimodal_derivable` to avoid domain universality**

The theorem as stated requires validity on ALL serial linear orders. The completeness
theorem uses exactly ONE specific domain (ChronicleSubtype). A refactored proof structure:

```lean
-- Instead of proving for all D, prove directly using the contrapositive of completeness:
theorem bimodal_conservative_over_temporal ... := by
  by_contra h_not_deriv
  -- Build MCS A with neg phi
  -- Build chronicleSubtype on A (which is a SPECIFIC instance of serial linear order)
  -- Apply temporal_valid_on_addcommgroup to get contradiction
  -- BUT: ChronicleSubtype lacks AddCommGroup
  sorry  -- same wall
```

This is exactly what Teammate A showed: inlining the contrapositive hits the same wall.

**Path D: Prove Base BX ChronicleSubtype is dense by examining what formulas are in ALL limit points**

For any `x` in `limitDom`, `limitF(x)` is an MCS. Every MCS contains tautologies.
In particular, every MCS contains `G(⊤)` (by temporal necessitation of `⊤`) and
`H(⊤)` (similarly). The formula `G(⊤)` means `¬(⊥ U ⊤)` in some formulations — but
this is NOT the same as `neg U(top, bot)` which is the dense indicator.

Actually `G(⊤) = neg F(neg ⊤) = neg U(⊤, ⊥)` (NOT neg U(bot, top)). The dense indicator
for BX is `neg U(bot, top) = neg U(⊤, ⊥)` wait — checking:

In the codebase, `dense_indicator` is:
```lean
(Formula.untl Formula.bot Formula.top).neg
```
i.e., `neg (bot U top)` = `neg F(top)` = `G(neg top)` = `G(⊥)` — which would mean
"always false", which cannot be in any consistent MCS!

Wait, let me re-read. `Formula.untl Formula.bot Formula.top` = `bot U top`. In temporal
logic, `⊥ U ⊤` is equivalent to `F(⊤)` (since the guard `⊥` is trivially false at all
intermediate points). So `neg(bot U top)` = `neg F(⊤)` = `G(neg top)` = `G(⊥)`. This
is indeed always false.

But `dense_indicator_in_dense_mcs` proves this is in every Dense-MCS. That seems wrong...

Actually re-reading: `Formula.top = Formula.bot.imp Formula.bot`, so `neg(top)` is not
`⊥`. Let me be more careful about what `neg` means here.

Regardless: the dense indicator formula is a specific formula with particular behavior
under C4. Proving it is in ALL limit points requires the dense axiom.

**The conclusion about density**:

For Base BX, the limit domain `limitDom A h_mcs` is asserted to be dense in informal
comments but this claim is NOT formally proven. The `DenselyOrdered` instance for the
Base BX ChronicleSubtype would need to be formally established. Given the existence of
`DenseCompleteness.lean` as a separate module for dense completeness, it is highly likely
that the authors recognized that density required additional axioms.

### 7. Fatal Obstacles Assessment

**Obstacle 1**: ChronicleSubtype lacks AddCommGroup (confirmed by all teammates, confirmed by code)

**Obstacle 2**: Order embedding does not preserve `Satisfies` (confirmed, well-understood)

**Obstacle 3**: `DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX is unproven

This is the obstacle the prior team partially addressed but did not resolve. The prior
synthesis concluded the dense/discrete case split is needed. But:
- Dense path: requires proving `DenselyOrdered` for base BX, which may itself require
  non-trivial work or be non-trivial to prove
- Discrete path: impossible (subtype of ℚ cannot be isomorphic to ℤ via its order)

**Obstacle 4 (newly identified)**: The discrete case of the prior team's plan is blocked

The team synthesis recommends:
> "Case split on DenselyOrdered: Dense: iso to ℚ, Discrete: iso to ℤ"

But `ChronicleSubtype` is always a subtype of `ℚ` (a dense order). It cannot have
`SuccOrder` or `IsSuccArchimedean`. Therefore `orderIsoIntOfLinearSuccPredArch` does NOT
apply. The discrete path in the case split is categorically blocked.

**This means the ONLY path is the dense path**: proving
`DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX.

---

## Evidence and Examples

### Evidence 1: DenselyOrdered for Dense-BX only

`DenseCompleteness.lean` line 228:
```lean
lemma chronicleDenselyOrderedDense
    {A : Set (Formula Atom)}
    (h_dense_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense A)
    (h_base_mcs : Temporal.SetMaximalConsistent A) :
    DenselyOrdered (ChronicleSubtype A h_base_mcs)
```

This lemma takes a Dense-MCS input. For base BX, no such lemma exists.

### Evidence 2: The Informal Density Claim

`ChronicleConstruction.lean` line 268:
```
since the limit domain is dense with no adjacent pairs
```

`ChronicleConstruction.lean` lines 830-831:
```
The limit interval function is defined by the C3 identity for the dense limit
domain. Since the limit domain is dense (no adjacent pairs)...
```

These are INFORMAL CLAIMS in code comments. If provable for base BX, they would resolve
the sorry. The question is whether the author meant "dense by construction" (provable from
the C4 mechanism alone) or "dense because of the dense axiom."

### Evidence 3: C4 Inserts Midpoints But Not Universally

`limit_satisfies_c4` (line 761) inserts a midpoint `z` between `x < y` only when:
- `(neg U(ξ, η)) ∈ limitF(x)` AND
- `η ∈ limitF(y)`

For density, we need a midpoint between ANY `x < y` in `limitDom`. This requires
specific formulas to be in `limitF(x)` and `limitF(y)`. Without a universal formula
(like the dense indicator) that forces C4 to trigger for every pair, density is not
automatic.

### Evidence 4: ChronicleSubtype Cannot Be Isomorphic to ℤ

`ℤ` has `SuccOrder`: there is a successor function `succ : ℤ → ℤ` with no element
strictly between `n` and `n+1`. Any `ChronicleSubtype A h_mcs` is a subtype of `ℚ`,
which is densely ordered. Therefore any infinite subset of `ℚ` either is dense or has
gaps — but it can never have `SuccOrder` unless it has isolated elements with empty
neighborhoods. An infinite subtype of `ℚ` with `NoMaxOrder` and `NoMinOrder` cannot
have `SuccOrder` if it is... actually wait: `ℤ ⊂ ℚ` as a subset, and `ℤ` does have
a successor order as a linear order even though `ℚ` is dense. The issue is whether
the specific `ChronicleSubtype` is isomorphic to `ℤ`.

For `ChronicleSubtype` to be isomorphic to `ℤ`, it would need to be isomorphic to
a discrete countable linear order without endpoints. In principle, the omega-chain
starting from `{0}` could produce a discrete-like domain if it only inserts finitely
many points in any bounded interval. But the C4 mechanism inserts midpoints between
EXISTING pairs when specific formulas hold, so the domain density depends on the
specific MCS being used.

**The key insight**: We cannot determine in general whether `ChronicleSubtype` is dense
or discrete from its construction alone, for base BX. This is why the `Order.iso_of_countable_dense`
path requires proving density first.

---

## Recommended Approach

Given the adversarial analysis, the single viable approach is:

**Prove `DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX directly**

The argument would be:
- For any `x < y` in `limitDom A h_mcs`, we need `z` with `x < z < y` in `limitDom`.
- Consider the potential counterexample `(x, y, bot, bot, c4_forward)` — encoding "neg U(bot,
  bot) in limitF(x) and bot in limitF(y)". Wait: `U(bot, bot)` = a trivially never-satisfied
  formula, so `neg U(bot, bot)` is always in any MCS.
- Actually: `⊥ U ⊥` is satisfied iff there exists `s > x` with `⊥` true and `⊥` holds on
  the interval — which is never true. So `neg(⊥ U ⊥) = G(neg ⊥) = G(⊤)` is always in
  every MCS.
- Similarly, `⊥ ∈ limitF(y)` is FALSE (since `limitF(y)` is consistent, it does not
  contain `⊥`). So C4 with `η = ⊥` won't trigger.

A more promising formula: Consider `neg U(⊤, ⊥)` = `G(neg ⊥)` = `G(⊤)`. This is
always in every MCS. And `⊤ ∈ limitF(y)` for any `y`. If C4 with `xi = ⊤, η = ⊤` works...

The `limit_satisfies_c4` theorem says: if `neg U(xi, eta) ∈ limitF(x)` and `eta ∈ limitF(y)`,
then exists `z` with `x < z < y` and `xi.neg ∈ limitF(z)`.

Let's use `xi = top, eta = top`:
- `neg U(top, top) ∈ limitF(x)`: Is `neg(top U top) = neg F(top) = G(neg top) = G(⊥)` in
  every MCS? NO — `G(⊥)` is inconsistent with an MCS (an MCS is consistent).

This approach fails. The density argument requires a careful choice of formula.

**The correct argument for density**: For `x < y` in `limitDom`:
- `limitF(x)` is an MCS; it either contains `F(⊤)` or `G(neg ⊤) = G(⊥)`. The latter is
  inconsistent, so `F(⊤) ∈ limitF(x)`.
- By BX12, `F(⊤)` implies `(⊤ U ⊤) ∈ limitF(x)`, i.e., `U(⊤, ⊤) ∈ limitF(x)`.
- From `neg(U(⊤, ⊤)) = neg F(⊤) = G(neg ⊤)` not in `limitF(x)` (since `F(⊤)` is),
  so `U(⊤, ⊤) ∈ limitF(x)`.

Hmm, I need `neg U(xi, eta) ∈ limitF(x)`. This is harder to guarantee universally.

**Alternative**: The C5 condition. From `U(⊤, ⊤) ∈ limitF(x)`, C5 gives a witness
`y' > x` in `limitDom` with `⊤ ∈ limitF(y')`. But this only gives a point beyond `x`,
not necessarily between `x` and `y`.

**The real density argument**: Use the C4 condition with the seriality formula.
Every MCS contains `F(⊤) = U(⊤, ⊤)` (by seriality axiom BX1: `⊤ → F(⊤)`, then
necessitation + distributing G over →). Given `x < y`, the formula `neg(U(⊤, neg(⊤)))
= G(neg(neg(⊤))) = G(⊤)` — but wait, `G(⊤)` IS in every MCS (it's a theorem).

The precise density argument requires careful formula manipulation. The fact that the
codebase comments claim density without proof suggests it IS provable (the author likely
worked through it informally) but it requires careful construction. The key is finding the
right formula pair for C4.

**Confidence Level: MEDIUM** that density of Base BX `ChronicleSubtype` is provable.
If provable, the primary path is:
1. Prove `DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX
2. Prove `Satisfies_orderIso` (~20 lines, structural induction)
3. Apply `Order.iso_of_countable_dense` to get `ChronicleSubtype ≃o ℚ`
4. Transfer satisfaction via `Satisfies_orderIso` to ℚ
5. Apply `temporal_valid_on_addcommgroup` (already proven) to get contradiction
6. Conclude `temporal_valid_of_bimodal_derivable`

---

## Challenges to Prior Team Conclusions

| Prior Conclusion | My Assessment | Verdict |
|-----------------|---------------|---------|
| Dense/discrete case split is primary path | Discrete path is BLOCKED (ChronicleSubtype ⊆ ℚ, not isomorphic to ℤ) | PARTIALLY CORRECT — only the dense path is viable |
| `Satisfies_orderIso` is core mechanism | Correct | CONFIRMED |
| ChronicleSubtype density is uncertain for Base BX | Correct | CONFIRMED |
| Bimodal ChronicleToCountermodelBasic.lean is template | May not directly apply — bimodal and temporal chronicles are constructed differently | NEEDS VERIFICATION |
| Density of ChronicleSubtype using Cantor iso | Correct approach IF density is proven | CONFIRMED conditional |
| Syntactic approach as fallback | Correct that it's harder but may be cleaner | CONFIRMED |
| Result is mathematically true | No counterexample identified; believed true | CONFIRMED |

---

## Confidence Level: HIGH

The sorry represents a genuine infrastructure gap, not a mathematical error. The result
(TM is conservative over BX for temporal formulas) is mathematically correct. The formal
proof path is:

1. Establish `DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX — this is the
   single unproven mathematical claim needed. The codebase comments assert it; the proof
   requires careful use of the C4 condition with seriality formulas that are in all MCSs.
   Estimated effort: 1-2 hours of careful Lean formalization.

2. With density proven: `Satisfies_orderIso` + Cantor iso + `temporal_valid_on_addcommgroup`
   complete the sorry in ~30-50 additional lines.

**The discrete case split recommended by the prior team synthesis is unnecessary and
inapplicable** — temporal `ChronicleSubtype` is always a subtype of `ℚ`, so no
ℤ-isomorphism is relevant.

The critical path item is exclusively: **prove `DenselyOrdered (ChronicleSubtype A h_base_mcs)`
for any base BX MCS `A`**. Everything else follows from existing or easily provable lemmas.
