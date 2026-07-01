# Task 275: Critic Findings — Bimodal TM Conservative over Temporal BX

- **Role**: Critic (Teammate C)
- **Focus**: Gaps, shortcomings, and blind spots in the current approach
- **Date**: 2026-06-22

---

## Key Findings

### The Build State

Running `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.TemporalConservativity`
confirms: the build **fails** (exit code 1) due to the `sorry` in `temporal_valid_of_bimodal_derivable`
(line 263). The build additionally emits:

1. `unusedDecidableInType` warning on `temporal_valid_of_bimodal_derivable` (line 242): `[DecidableEq Atom]`
   is unused in the type and should be removed
2. `longLine` style warning on line 250 (exceeds 100 characters)
3. `unusedDecidableInType` warning on `bimodal_conservative_over_temporal` (line 267): same issue

The sorry is **precisely localized** to `temporal_valid_of_bimodal_derivable`. All other proofs in the
file (`bimodal_truthAt_toBimodal_iff_temporal_satisfies`, `temporal_valid_on_addcommgroup`) appear
structurally correct and should compile. The phase 1 and partial phase 2 work is real progress.

### The Domain Mismatch is a Real Mathematical Obstacle

The domain mismatch is **not** a Lean formalization artifact. It is a genuine mathematical gap:

1. Bimodal `soundness` requires `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]`.
   This signature comes from the `valid` predicate in `Validity.lean`, which uniformly quantifies
   over all D with these constraints. Changing this would require modifying the soundness theorem
   and all of its dependencies — a potentially large refactor.

2. Temporal `completeness` (line 101-128 of Completeness.lean) quantifies over `D : Type` with
   `[LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]` only. The `ChronicleSubtype`
   (a subtype `{x : Rat // x ∈ limitDom A h_mcs}`) is the canonical countermodel domain.

3. `ChronicleSubtype` does NOT have `AddCommGroup`: the subtype `{x : ℚ // x ∈ limitDom}` inherits
   `LinearOrder` from `ℚ`, but subtraction of two elements of `limitDom` is NOT guaranteed to be in
   `limitDom`. Since `limitDom` is defined by a logical chain construction, the subset is dense but
   NOT closed under subtraction. No `AddCommGroup` instance on `ChronicleSubtype` is provided or
   derivable from the structure.

### The Semantic Approach Has a Structural Flaw

The current semantic approach constructs a bimodal model whose time domain D must simultaneously be:
- The domain quantified over in bimodal `soundness` (requires `AddCommGroup D`)
- The domain of the temporal model being checked (must be an arbitrary serial linear order)

These cannot simultaneously be satisfied for the same D if D is, say, `ChronicleSubtype`. The
current file correctly identifies this at lines 209-239 and leaves a sorry.

The document at lines 209-239 says "A correct transfer would require (a) Order.iso_of_countable_dense
for the Dense BX proof, not base BX." This is correct and points to the core issue: Cantor's theorem
for countable dense linear orders without endpoints (used to get an isomorphism to ℚ) applies to
the Dense completeness proof but not the base BX completeness proof, which may use non-dense
countermodel domains.

### How ModalConservativity Avoids the Problem

`ModalConservativity.lean` completely sidesteps the domain issue by hardcoding `D = ℤ`:

```lean
def kripkeAdapterFrame (World : Type) : TaskFrame ℤ where ...
```

The Kripke model worlds (`World`) become the `WorldState` of the task frame, but the temporal
domain D is always `ℤ` (which is a valid `AddCommGroup`). When applying `soundness`, `D = ℤ`
satisfies all constraints trivially.

For `TemporalConservativity`, this trick CANNOT be applied because the temporal model's semantics
(`Satisfies M t φ`) is indexed by the time domain D itself — D is not separable from the model.
This is the fundamental reason the two conservativity proofs have different structures.

### What PropositionalConservativity Does (and Why It Works)

`PropositionalConservativity.lean` also hardcodes `D = ℤ` (via `TaskFrame.trivialFrame` over
ℤ). Propositional formulas have no temporal quantifiers, so there is no D-indexed model to
match against. The valuation is `fun _ p => v p` where `v : Atom → Prop` is independent of D.
This works because CPL completeness requires validity over all `v : Atom → Prop`, and the bimodal
construction works for any fixed D (here ℤ).

### Why `Set.univ_shift_closed` Exists (Not a Showstopper)

`Set.univ_shift_closed` is defined at line 254 of `Cslib/Logics/Bimodal/Semantics/Truth.lean`.
It states `ShiftClosed (Set.univ : Set (WorldHistory ℱ))`. This exists and is used in the
`temporal_valid_on_addcommgroup` proof at line 205 of `TemporalConservativity.lean`. This lemma
is not a gap.

---

## Gaps and Shortcomings

### Gap 1: The Sorry Requires a Non-Trivial Model Transfer Theorem

The sorry requires proving: "If a temporal formula φ is satisfied in every temporal model on
every domain with `AddCommGroup`, then φ is satisfied in every temporal model on every serial
linear order."

The current file's comment (lines 221-239) correctly identifies three sub-approaches and their
problems:
- **Order embedding**: Does NOT preserve temporal satisfaction (witness introduction).
- **Order isomorphism via Cantor**: Works only for Dense BX (countable + dense + no endpoints
  implies isomorphic to ℚ), not Base BX.
- **Incomplete analysis**: The comment doesn't explore whether the base BX countermodel
  (`ChronicleSubtype`) satisfies the hypotheses of Cantor's theorem independently of density.

### Gap 2: ChronicleSubtype's Density Status is Not Investigated

The chronicle construction for BASE BX (as opposed to Dense BX) may or may not produce a dense
linear order. If `ChronicleSubtype` for base BX is countable, dense, and without endpoints, then
Cantor's theorem (`Order.iso_of_countable_dense` in Mathlib) would give an order isomorphism to
ℚ. An order isomorphism to ℚ would preserve temporal satisfaction (since both ℚ and
`ChronicleSubtype` have the same order type), and ℚ has `AddCommGroup`. This path was NOT
fully investigated.

**Key question**: Does the base BX chronicle construction produce a dense countermodel?
The Dense BX completeness proof (`DenseCompleteness.lean`) is separate, suggesting base BX
countermodels may NOT be dense. If so, the Cantor isomorphism path is blocked.

### Gap 3: No Investigation of Direct ℚ-Based Completeness

An alternative that was NOT considered: prove a version of temporal completeness that directly
uses ℚ as the countermodel domain (instead of `ChronicleSubtype`). If temporal BX completeness
could be proved with ℚ as the universal domain (rather than arbitrary `D`), the domain mismatch
disappears entirely. This would require either:
- Modifying the completeness proof to embed `ChronicleSubtype` into ℚ (if the embedding
  preserves satisfaction), or
- Proving a separate "ℚ-completeness" lemma: if φ fails at some model, it fails at a ℚ-model.

### Gap 4: The Syntactic Approach Was Not Investigated in the Plan

The plan mentions "fallback to syntactic derivation translation" but does not investigate it.
The syntactic approach for temporal conservativity would work as follows:

For any TM-derivation of `φ.toBimodal` (a temporal formula embedded into bimodal), construct
a BX-derivation of `φ`. This is valid because:
- All BX axioms are TM axioms
- All temporal rules (temporal necessitation, temporal duality) apply directly
- The modal axioms (T, 4, B, 5, K) and modal necessitation rule only derive modal formulas
- Therefore: any TM-derivation of a temporal formula can be "projected" by removing all modal
  steps, yielding a BX-derivation

This works by induction on derivation tree height. The key lemma needed is:
```
If d : DerivationTree FrameClass.Base [] φ.toBimodal, then d uses only temporal axioms.
```
This follows from the fact that TM's modal axioms (T, 4, B, 5, K) produce formulas involving
`□` which cannot equal `φ.toBimodal` for any `φ : Temporal.Formula Atom`. More precisely:
- `φ.toBimodal` is always box-free (since `Temporal.Formula` has no `box` constructor)
- The modal axioms introduce `Formula.box`
- So any derivation of a box-free conclusion that uses modal axioms must "cancel out" the boxes
  in intermediate steps
- The key insight: can the modal axioms generate new box-free theorems through interaction?

This is the central question for soundness of the syntactic approach.

### Gap 5: Lint Issues Already Present

The build reveals two lint warnings that will cause failures at `lake lint`:
1. `[DecidableEq Atom]` in `temporal_valid_of_bimodal_derivable` is unused in the type —
   must be removed
2. `[DecidableEq Atom]` in `bimodal_conservative_over_temporal` is unused in the type —
   must be removed
3. Line 250 exceeds 100 characters

These are fixable but must be addressed before the task can be considered complete.

---

## Potential Showstoppers

### Showstopper 1: The Modal+Temporal Interaction Could Derive New Temporal Theorems

This is the existential question: is the conservativity result actually TRUE? The claim is that
TM's modal axioms (T, 4, B, 5, K and their interaction with temporal via `modal_future`) do NOT
derive new temporal theorems.

**Evidence it is TRUE**: The `modal_future` axiom (`□φ → G□φ`) and its ilk only allow "lifting"
box statements across temporal operators. No purely temporal formula follows from a box formula
unless the formula already contained a box. A box-free formula cannot be derived by box
introduction (necessitation) and elimination (T axiom) without passing through box-containing
formulas. The interaction axiom preserves this: `modal_future` takes `□φ` to `G□φ`, which is
not box-free.

**Evidence against**: More subtle: the `modal_b` axiom `φ → ◇□φ`, combined with temporal
operators, could in principle create derivable temporal tautologies through exotic interactions.
No explicit counterexample has been found, and the result is expected to be true.

**Risk Level**: Low — the result is expected true, but no formal proof of the interaction property
has been established. The syntactic approach is the most direct path to verifying this.

### Showstopper 2: Domain Transfer Cannot Be Made Formal

If the only resolution of the domain mismatch is the model transfer approach, and model transfer
requires either (a) order isomorphism (blocked for non-dense domains) or (b) embedding with
satisfaction preservation (provably impossible for temporal formulas), then the semantic approach
is fundamentally blocked.

**Assessment**: MEDIUM risk. The semantic approach currently has a sorry with no clear sorry-free
path. The approach needs formal development of either:
- Cantor's theorem applied to ChronicleSubtype (requires investigating density of base BX countermodel)
- A sorry-free syntactic alternative

### Showstopper 3: Syntactic Approach May Require New Infrastructure

If the syntactic approach requires a `boxFree : Formula → Prop` predicate or an `isTemporal`
predicate on bimodal formulas, this is new infrastructure that must be defined and proved
correct. The plan mentions this as non-goal ("no boxFree or isTemporal predicates"). However,
the syntactic approach can likely be done WITHOUT such predicates, by instead proving:

```lean
-- The image of toBimodal is exactly the box-free formulas
theorem toBimodal_is_boxFree (φ : Temporal.Formula Atom) :
    ¬ (∃ ψ, φ.toBimodal = Formula.box ψ)
```

And using structural induction on the derivation tree to show that if the conclusion is in
the image of `toBimodal`, then the derivation uses only BX rules.

---

## Analysis of the Viable Paths Forward

### Path A: Cantor Isomorphism (Requires Research)

1. Prove `ChronicleSubtype` (base BX) is dense (or show it isn't)
2. If dense: `Order.iso_of_countable_dense` gives iso to ℚ
3. Prove temporal satisfaction is preserved by order isomorphism
4. Conclude: if φ fails at ChronicleSubtype model, it fails at ℚ model
5. ℚ has `AddCommGroup` → apply `temporal_valid_on_addcommgroup`

**Feasibility**: Moderate. Requires investigating density of base BX chronicle and proving a
"temporal satisfaction preserved by order isomorphism" lemma. The order isomorphism lemma is
straightforward by induction on formula structure. The density question is the unknown.

### Path B: Strengthened Completeness (Direct ℚ)

1. Show that if φ is not BX-derivable, there exists a ℚ-model falsifying φ
2. This requires either modifying the completeness proof or adding a corollary
3. ℚ has `AddCommGroup` → domain mismatch disappears

**Feasibility**: Low-to-moderate. Requires either modifying the chronicle construction to land
on ℚ directly (risky refactor) or proving ChronicleSubtype ≅ ℚ (Path A).

### Path C: Syntactic Derivation Translation (Independence from Domain)

1. Prove: if `d : DerivationTree Base [] φ.toBimodal` for temporal φ, then it uses only
   temporal/propositional steps (induction on derivation height, case analysis on axioms)
2. Derive: such a derivation can be "temporally projected" to give a BX-derivation of φ
3. No model-theoretic machinery needed, no domain constraints

**Feasibility**: High in principle, but requires either a `boxFree` predicate or a careful
structural argument about derivation trees. The key property is:
- All BX axioms map directly under `toBimodal`
- Modal axioms (T, 4, B, 5, K) produce formulas containing `Formula.box`
- `toBimodal` never produces `Formula.box` outputs (provable by structural induction on `Temporal.Formula`)
- Therefore no modal axiom step can produce `φ.toBimodal` as its conclusion
- By induction: any derivation of `φ.toBimodal` uses only BX axioms and rules

This approach is independent of domain type constraints entirely and is likely the cleanest sorry-free path.

---

## Confidence Level

| Claim | Confidence |
|-------|------------|
| Build fails due to sorry | High — confirmed by running lake build |
| `Set.univ_shift_closed` exists and is correct | High — found in Truth.lean:254 |
| Semantic bridge (Phase 1) is correct | High — proof is complete, no sorry |
| `temporal_valid_on_addcommgroup` (Phase 2 partial) is correct | High — proof is complete, no sorry |
| Domain mismatch is a genuine mathematical obstacle | High — ChronicleSubtype lacks AddCommGroup |
| ModalConservativity avoids the problem by hardcoding D=ℤ | High — confirmed by reading the code |
| Syntactic approach is viable in principle | Medium — requires investigation of toBimodal image |
| Cantor isomorphism path requires density of ChronicleSubtype | High — density is the key unknown |
| The conservativity result is actually TRUE | Medium-High — expected true, no counterexample |

---

## Summary for Implementation Guidance

The current implementation has a real sorry at a real mathematical obstacle. The most direct
sorry-free path is the **syntactic approach** (Path C):

1. Prove `toBimodal_boxFree`: for any `φ : Temporal.Formula Atom`, `φ.toBimodal` does not
   contain any `Formula.box` subformula. This is provable by induction on `φ`.

2. Prove `modal_axioms_produce_box`: every axiom of the form `.modal_t`, `.modal_4`, `.modal_b`,
   `.modal_5_collapse`, `.modal_k_dist`, `.modal_future` produces a formula that IS a box
   formula or has a box on the top-level. This is provable by inspection.

3. Prove the key lemma: if `d : DerivationTree FrameClass.Base [] φ` and `φ` is box-free
   (meaning `φ` is in the image of `Temporal.Formula.toBimodal`), then `d` can be converted
   to a BX-derivation of the preimage `ψ` such that `φ = ψ.toBimodal`.

Step 3 requires induction on `d`. The critical cases are:
- **Axiom**: Modal axioms are excluded because they produce box-containing formulas.
- **MP**: If `d₁ : [] ⊢ (ψ → φ).toBimodal` and `d₂ : [] ⊢ ψ.toBimodal`, and the conclusion
  `φ.toBimodal` is box-free, then both `ψ` and `ψ → φ` must also be temporal formulas,
  so by IH we get BX-derivations of both.
- **Necessitation**: Produces `□φ`, which is NOT in the image of `toBimodal`. So this case
  cannot arise if the conclusion is box-free.

The main complication: the temporal embedding `toBimodal` may not be injective (two different
temporal formulas could map to the same bimodal formula), and the preimage may not be unique.
However, for the purposes of proving the conservativity result, it suffices to find ANY
BX-derivation — not necessarily one corresponding step-by-step to the bimodal derivation.

**Recommendation**: Replace the sorry with the syntactic approach. This eliminates the domain
dependency entirely and avoids the Cantor isomorphism path. The cost is implementing the
`toBimodal`-boxFree lemmas, which are elementary inductions.
