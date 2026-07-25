# CS5 Pair-Seed Disjunction Property: Research Report

**Verdict: (c) the property is open — but it is not the property the module thinks it is.**

Two machine-checked, sorry-free probes show that the named `Prop` is *equivalent* to a single
right-hand exclusion, that the other two open hypotheses follow from it, and that one of the two
recorded Non-Goals rests on a false premise. The genuinely open residue is a **conservativity**
statement, and the obstruction to every translation-based attack on it is named precisely below.

## 1. Headline Results (all machine-checked)

Probe files, both compiling clean under `lake env lean` with axioms
`[propext, Classical.choice, Quot.sound]` and **no `sorryAx`**:

- `/home/benjamin/Projects/cslib/specs/554_cs5_pair_seed_disjunction_property_cutfree_research/probes/cross1_collapse.lean`
- `/home/benjamin/Projects/cslib/specs/554_cs5_pair_seed_disjunction_property_cutfree_research/probes/retraction_bound.lean`

Write `Θ := modalDeductiveClosure CS5PairAxiom (cs5PairSeed H)`,
`K := modalDeductiveClosure CS5ModalAxiom (boxInv H)`, and

- `hL : cs5PairTauL (□A) ∉ Θ`
- `hR : cs5PairTauR A ∉ Θ`
- `hOpen : CS5PairSeedDisjunctionProperty H A`

### R1. `cs5PairTauL (□A)` is *literally* `□ (cs5PairTauL A)` — by `rfl`

`Proposition.map_box` (`Cslib/Logics/Modal/Basic.lean:164`) is definitional, so
`cs5PairTauL (Proposition.box A) = Proposition.box (cs5PairTauL A)` holds by `rfl`. That is
**exactly** the antecedent shape of `CS5PairAxiom.cross1 A`
(`CS5Completeness.lean:115-116`). The left disjunct of the open obligation is the antecedent of
an axiom whose consequent is the right disjunct.

### R2. `hOpen ↔ hR`

- `hR → hOpen` (`probe_dp_of_hR`): `orE` against `cross1 A` and identity gives
  `⊢ (τ_L(□A) ⊔ τ_R A) → τ_R A`; closure of `Θ` transports.
- `hOpen → hR` (`probe_hR_of_dp`): `orI2`.

So `CS5PairSeedDisjunctionProperty H A` is not a disjunction property at all in this system — it
is a notational variant of `hR`.

### R3. `hR → hL`

`probe_hL_of_hR`: if `□(τ_L A) ∈ Θ` then `modus_ponens` against `cross1 A` puts `τ_R A ∈ Θ`.

### R4. `DerivExcludes` at the seed follows from `hR` **alone**

`probe_derivExcludes_of_hR` composes R2 + R3 into the existing
`cs5Pair_derivExcludes_of_disjunctionProperty` (`CS5Completeness.lean:415`), discharging all three
of its hypotheses from `hR`.

**Consequence.** The module currently carries three open obligations (`hL`, `hR`, `hOpen`) plus a
blocked cross-inertness lemma. They are one obligation:

> **`CS5PairSeedRightExclusion H A` : `cs5PairTauR A ∉ Θ`.**

### R5. Non-Goal 2's stated reason is false

The task records: *"the signature-collapse route via a sum-elimination retraction fails because
the first cross axiom's image, box B implies B, is not an instance of the modal axiom schema."*

`CS5ModalAxiom.tBox` **is** `□φ → φ` (`CS5.lean:203-205`; `CS5` contains `T`). `probe_retraction`'s
`cs5PairRetract_schema_compatible` proves, sorry-free, that `Sum.elim id id` maps **every**
`CS5PairAxiom` constructor to a genuine `CS5ModalAxiom` instance — both cross axioms land on
`tBox`. The retraction is schema-compatible.

The route nonetheless fails, for a different reason, also machine-checked
(`cs5PairRetract_bound`): collapsing yields only

    τ_R A ∈ Θ  →  A ∈ cl_{CS5}(H ∪ K)  =  A ∈ H   (H deductively closed, K ⊆ H)

and `□A ∉ H` is entirely compatible with `A ∈ H`. The bound is real but too weak.

Moreover **no atom relabeling can do better**: a retraction `g` must satisfy
`⊢ □(B[g∘inl]) → B[g∘inr]` for all `B`; the atom instance forces `⊢ □q → q'` for
`q = g(inl p)`, `q' = g(inr p)`, which is a theorem only if `q = q'`. Every relabeling
retraction is forced to identify the two copies. The Non-Goal is correct as a *conclusion*; its
*reason* should be corrected in the docstring, because the false reason ("`□B → B` is not a
schema instance") would also wrongly rule out other schema-compatible maps.

### R6. The "no semantic witness exists" docstring claim is also mis-argued

`CS5Completeness.lean:363-367` argues that the cross axioms are sound only under a *common*
valuation for both copies, which collapses `cross1` to `□B → B`. That argument is sound only for
models that are single-copy models over `Atom`. It does not rule out a **product/two-label**
reading: a `cs5FC` model whose worlds are pairs `(x, y)` drawn from one R-cluster, with
`V(inl p) = {(x,y) | x ⊩ p}` and `V(inr p) = {(x,y) | y ⊩ p}`; there `cross1` reads
"`□B` at `x` implies `B` at `y`", which is sound when `r x y` holds at every world of the
restricted frame, and `V∘inl ≠ V∘inr` genuinely.

The *conclusion* (no usable semantic witness) nevertheless stands, for the reason already
recorded as Non-Goal 1: such a product model requires a `cs5FC` model containing worlds `x ⊩ H`
and `y ⊮ A` in one cluster — which is precisely the joint satisfiability of the pair the truth
lemma is being built to produce. Circular. **The claim should be restated** ("any semantic
witness is equivalent to the pair's joint satisfiability, hence circular") rather than left as
"no semantic witness exists", which is not established and is falsifiable in the concrete case
(see §3).

## 2. What Is Actually Open, and Why It Is Hard

`hR` is a **conservativity** statement:

> If `τ_L '' H ∪ τ_R '' K ⊢_{CS5Pair} τ_R A`, then `A ∈ K`.

### 2.1 The pair `(H, K)` is a fixed point of the cross rules

For `H` `CS5`-deductively closed:

- `boxInv H ⊆ K` by construction, so `cross1` never yields right-content outside `K`.
- `K ⊆ H`: `boxInv H ⊆ H` by `tBox` + closure, and `H` is closed, so `cl(boxInv H) ⊆ H`.
  Hence `boxInv K ⊆ K ⊆ H` and `cross2` never yields left-content outside `H`.
- The `B`-axiom transfer closes too: `τ_L B → τ_R ◇B` is derivable (`bBox` on the left copy
  gives `□(τ_L ◇B)`, then `cross1` at `◇B`), and `B ∈ H ⇒ □◇B ∈ H ⇒ ◇B ∈ boxInv H ⊆ K`.
  Symmetrically `τ_R C → τ_L ◇C` with `C ∈ K ⇒ ◇C ∈ H` (via `tBox`, `tDia`, `kdia`).
- Boxes of genuinely *mixed* formulas are **inert**: every `CS5PairAxiom` constructor whose
  principal formula is a box (`k`, `kdia`, `tBox`, `fourBox`, `bBox`, `bDia`, `cross1`, `cross2`)
  is either purely tagged or has a purely-tagged boxed antecedent. No axiom consumes `□φ` for
  mixed `φ`. Necessitation can *produce* mixed boxes; nothing can *use* them.

So on every route inspected, `Θ ∩ τ_L''Prop = τ_L''H` and `Θ ∩ τ_R''Prop = τ_R''K`. `hR` is
almost certainly **true**. What is missing is the argument that MP through *arbitrary mixed
intermediates* cannot short-circuit the fixed point — i.e. exactly a cut-elimination /
subformula-property argument.

### 2.2 The named obstruction: every separating translation needs box-over-disjunction

Generalize the retraction to an arbitrary translation `θ` of the right copy (`θ_L = id`), so that
`cross1` maps to a `CS5` theorem: we need `⊢ □B → θ(B)` for every `B`.

| Case | Requirement | Status |
|------|-------------|--------|
| `B = p` | `⊢ □p → θ(p)` | forces `θ(p) ⊒ □p` |
| `B = ⊥` | `⊢ □⊥ → θ(⊥)` | fine (`tBox`) |
| `B = C ∧ D` | `⊢ □(C∧D) → θC ∧ θD` | fine (`k` + necessitation) |
| `B = □C` | `⊢ □□C → θ(□C)` | fine (`fourBox`) |
| **`B = C ∨ D`** | **`⊢ □(C∨D) → θC ∨ θD`** | **fails**: with `θ ⊒ □` this is `□(C∨D) → □C ∨ □D` |
| `B = C → D` | `⊢ □(C→D) → (θC → θD)` | needs a contravariant companion `θ'` with `⊢ θ'C → □C`; no rule manufactures a box, so `θ'` cannot exist for compound `C` |
| `B = ◇C` | `⊢ □◇C → θ(◇C)` | `□◇p → ◇□p` is not a `CS5` theorem |

The `∨` row is **the same non-theorem** — `□(A ∨ B) → (□A ∨ □B)` — that
`specs/537_labelled_cs5_general_soundness_biconditional` hit from the independent labelled-soundness
direction. The task brief's claim that the two fronts converged on one wall is confirmed, and the
wall now has a precise formulation: *the boxing translation is a homomorphism for the universal
connectives and breaks for the existential ones (`∨`, `◇`) and for the contravariant one (`→`).*

## 3. Sanity Check: No Countermodel Found

Concrete instance: `Atom = {p}`, `H = cl_{CS5}({p})`, `A = p`. Then `□p ∉ H` (`⊢ p → □p` fails),
`K = cl({◇p})` (from `bBox`). A two-world `S5` cluster with `p` true at `w`, false at `v` gives
`w ⊩ H`, `v ⊩ ◇p`, `v ⊮ p`. So `hR` holds here and no refutation is available at this instance;
the difficulty is uniform-in-`H`, not instance-specific. **No countermodel; a refutation
deliverable is not available.**

## 4. Recommendations

### 4.1 Land now (zero research risk, ~60-80 lines, all proofs already exist)

Promote the probe lemmas into `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean`:

1. `cs5Pair_or_imp_right`, `cs5Pair_dp_of_rightExclusion`, `cs5Pair_rightExclusion_of_dp`,
   `cs5Pair_leftExclusion_of_rightExclusion`, and a one-hypothesis
   `cs5Pair_derivExcludes_of_rightExclusion`.
2. Rename/redefine the open obligation: replace `CS5PairSeedDisjunctionProperty` with
   `CS5PairSeedRightExclusion H A : cs5PairTauR A ∉ Θ`, keeping the old name as a deprecated
   abbreviation plus the `↔` lemma so nothing downstream breaks.
3. `cs5PairRetract`, `cs5PairRetract_schema_compatible`, `cs5PairRetract_bound` — a genuine
   library-grade functoriality result and the sharpest bound obtainable by relabeling.
4. Docstring corrections: Non-Goal 2's reason (§R5) and the "no semantic witness" claim (§R6).

This alone removes the blocked cross-inertness lemma from the critical path and reduces the
module's open surface from three obligations to one.

### 4.2 The real research target (multi-task, high cost)

**Two-label conservativity for `CS5`**, not the disjunction property. Concretely: a fully
labelled sequent calculus in the style of Marin–Morales–Strassburger (sequents carrying both the
accessibility relation `R` and the intuitionistic preorder `≤`), with cut admissibility, then:

> from `w : H`, `v : K` with `R w v`, `R v w`, if `v : A` is derivable then `A ∈ K`.

Why this discharges `hR`: cut-elimination gives the subformula property, so no mixed intermediate
is needed; `□`-right introduces a *fresh* label and therefore cannot manufacture a boxed formula
at `w` or `v`; the only boxed formulas available are those already in `H` or `K`; and §2.1 shows
`(H, K)` is closed under exactly those transfers. Nested sequents (Arisaka–Das–Strassburger) are
the alternative presentation; the labelled one is preferable here because CSLib already has a
labelled `CS5` line of work in flight.

**Note on the literature corpus**: `literature-search.sh` returned
`{"results": [], "degraded": true, "fallback_tier": "none"}` — the two papers the brief names as
"present in the corpus" are **not retrievable** through the search path. Anyone planning the
labelled-calculus work should run `/literature` ingestion first; the citations above are from
model knowledge, not from a verified local source, and should be treated as unverified pointers.

### 4.3 Fallback: flagged, not adopted

The deferred collapse route (derive `idb` in `CS5`, then bridge `CS5 → IS5` and compose the
landed `IS5` completeness theorem) remains available and is **not** adopted here. Adopting it is
a mandate change requiring explicit user authorization. Note that §R5's `cs5PairRetract_bound` is
a small piece of evidence *for* that route's feasibility (the collapse map is schema-compatible),
but it is a different theorem from what that route needs.

## 5. What Each Consumer Gains

### Consumer 1 — pair-seed obligation (this task's host module)

**Gain now**: three open obligations plus one blocked lemma collapse to one named obligation, with
all reduction proofs already machine-checked. `cs5Pair_derivExcludes_of_disjunctionProperty` becomes
single-hypothesis. Two incorrect docstring claims get corrected.

**Gain from the cut-free work**: the single remaining obligation `CS5PairSeedRightExclusion` is
discharged, which — per the module's own "What a discharge would unlock" note
(`CS5Completeness.lean:479-484`) — instantiates `Metalogic.prime_set_exclusion` at `CS5PairAxiom`
and yields the box-backward pair for a native `cs5_completeness''`.

### Consumer 2 — labelled `CS5` general-soundness biconditional

Direct answer to the brief's question ("is a context-fold that splits compound context facts
derivable without the box-over-disjunction bridge?"): **No — not as a repair to the fold.**

Dispatch 3's own closing note
(`specs/537_labelled_cs5_general_soundness_biconditional/probes/theta_place_final_gate.lean`)
proposes making `sigAt`'s context-fold recurse into `∨` the way `place` already does for target
formulas. That **relocates** the obligation rather than discharging it: `Θ` sits in the
*antecedent*, so a split `□P0 ∨ □P1` is a *strictly stronger* hypothesis than the flat
`□(P0 ∨ P1)`. Weakening the adequacy statement that way pushes the same non-theorem onto the
caller, which must now establish the split form from the real labelled derivation. That is free
only for `orI1`/`orI2`-originated disjunctions (`hOr_split_from_orI1`) and is exactly *not* free
for the `impI`-discharged compound assumption that `compound_assumption_derivation` proves is
reachable. So the fold cannot be repaired; the `sigAt` freeze is not the binding constraint.

**What the cut-free/labelled treatment gains for this consumer**: it removes the fold entirely.
`Θ` exists only to reduce labelled derivability to *unlabelled* `CS5` derivability, and folding a
multi-label context into one boxed `CS5` formula is precisely the step that makes
box-over-disjunction necessary. In a labelled sequent calculus with cut admissibility the
antecedent stays a labelled multiset and adequacy is stated label-wise, so there is no fold and
no bridge. This is a strictly larger redesign than lifting the `sigAt` Preserved-Asset
constraint, and it is the same calculus Consumer 1 needs — one piece of work unblocks both.

**Durable assets confirmed**: the three probes under
`specs/537_labelled_cs5_general_soundness_biconditional/probes/` remain valid evidence and are
correctly characterized in that task's summaries; nothing in this report contradicts them.

## 6. References

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` — host module.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean:150-220` — `CS5ModalAxiom`, incl. `tBox`.
- `Cslib/Logics/Modal/Basic.lean:140-220` — `Proposition.map` and its homomorphism lemmas.
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean:213-252` — `DerivationTree.map`/`Deriv.map`.
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean:78` — `modalDeductiveClosure`.
- `specs/537_labelled_cs5_general_soundness_biconditional/probes/` — Consumer 2's three probes.
- Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics* — Lemma 16 (unsound as
  published). **Unverified against a local source.**
- Marin, Morales, Straßburger, *A fully labelled proof system for intuitionistic modal logics*
  (2021); Arisaka, Das, Straßburger, *On nested sequents for constructive modal logics* (2015).
  **Unverified against a local source** — see §4.2.
