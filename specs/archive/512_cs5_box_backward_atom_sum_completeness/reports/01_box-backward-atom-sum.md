# Research Report — Task 512: CS5 Box-Backward via Doubled-Atom Combined System

**Task type**: cslib (Lean 4 formal verification, hard / deflection-prone)
**Target file**: `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (1379 lines)
**Depends on**: 509 (soundness + mechanized obstruction, both branches landed)
**Feasibility (headline)**: **UNCERTAIN — cautiously constructive.** The design is internally
coherent and ~70% of the required machinery is reusable or mechanically corollary. There is
exactly **one** genuinely hard, possibly-failing obligation (the combined-system *seed
consistency* / `DerivExcludes` discharge). A rigorous negative result is a live possibility and
is an acceptable outcome per the task.

---

## 1. What box-backward actually requires (grounded restatement)

The module docstring (`CS5.lean:156`) states completeness is open at **exactly** the truth
lemma's box-backward case. Reconstructing the exact obligation from the canonical-model
architecture:

- Worlds are `CS5Segment Atom` (`CS5.lean:985`), each wrapping a `CKSegment CS5ModalAxiom`
  whose tail is *exactly* the **symmetric** tail `cs5Tail seg.head` (`tail_eq`, `CS5.lean:989`).
- `cs5Tail H = {t | QuasiPrime t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}` (`CS5.lean:632`, symmetric —
  the `boxInv t ⊆ H` clause is forced by the `B` axiom's frame condition, see
  `fcbdia_forces_symmetry`, `CS5.lean:689`).
- Reachability `cs5Mreach P Q := cmreach P.seg Q.seg := Q.seg.head ∈ P.seg.tail` (`CS5.lean:994`,
  `Segment.lean:173`); `≤` is head inclusion (`Segment.lean:161`).

The generic `ck_truth_lemma` (`CKTruthLemma.lean:133`) discharges box-backward by re-tailing to
the **maximal** tail via `CKSegment.ofHead` and `box_refuting_theory` (a witness with
`boxInv H ⊆ T`, `A ∉ T`, but **no** `boxInv T ⊆ H`). That witness is **not** in `cs5Tail`, so
`ck_truth_lemma` **cannot** be reused for CS5's box case — CS5 needs its **own**
`cs5_truth_lemma`, exactly as `CS4` needed `cs4_truth_lemma` (`CS4.lean:~455`). This is confirmed
by the design note at `CS5.lean:969` ("Mirrors CS4.lean:341-455").

`cs5_symmetric_tail_box_gap` (`CS5.lean:712`) proves the witness **cannot** live in `H`'s own
symmetric tail: if `□(p ∨ □q) ∈ H`, `q ∉ H`, every symmetric-tail member contains `p`. Hence one
must move to a strictly larger head `H' ⊇ H`, enlarging `boxInv H'` in turn — the circularity
that forces `H'` and `T` to be a **simultaneous** maximal pair. `CS5BoxGapWorld` (`CS5.lean:1246+`)
shows the gap is non-vacuous.

**Therefore the exact deliverable is:**

```lean
theorem cs5_box_backward {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    {A : Proposition Atom} (h_not : Proposition.box A ∉ H) :
    ∃ H' T : Set (Proposition Atom),
      H ⊆ H' ∧ QuasiPrime (@CS5ModalAxiom Atom) H' ∧ QuasiPrime (@CS5ModalAxiom Atom) T ∧
      boxInv H' ⊆ T ∧ boxInv T ⊆ H' ∧ Proposition.box A ∉ H' ∧ A ∉ T
```

`□A ∉ H'` is *required*, not incidental: if `□A ∈ H'` then `A ∈ boxInv H' ⊆ T`, contradicting
`A ∉ T`. Both exclusions are structural necessities of a symmetric-tail witness — matching the
task's stated pair spec verbatim.

**Truth-lemma integration (once the pair exists) is mechanical and low-risk:** build
`w' := CS5Segment.ofHead H'_qprime` (`≥ s` since `H ⊆ H'`), `u := CS5Segment.ofHead T_qprime`;
`cs5Mreach w' u` holds because `T ∈ cs5Tail H'` (the three pair clauses); `A ∉ T` gives, by the
IH, `¬ CKForces A` at `u`, refuting `□A` at `s`. The `H'`-segment is a valid `CS5Segment` because
`cs5Seg` (`CS5.lean:975`) supplies `diam_witness := cs5_diam_witness` for any quasi-prime head.
All other truth-lemma cases (atom/bot/and/or/imp-both, box-forward via `box_reflect`,
diamond-both via `cs5_diam_witness`) port directly from `ck_truth_lemma` / `cs4_truth_lemma`.

---

## 2. The designed repair, assessed

**Design** (from `probes/cs5-pair-primeness.lean:60-72`): encode the pair as a *single* prime
theory over the doubled atom space `Atom ⊕ Atom`. Tag `H'`-formulas via `τ_L := Proposition.map
Sum.inl`, `T`-formulas via `τ_R := Proposition.map Sum.inr`, under a **combined** axiom system
`CS5Combined : Proposition (Atom ⊕ Atom) → Prop` = all 17 `CS5ModalAxiom` constructors **plus**
two cross-condition axiom families:

- `crossLR B : □(τ_L B) → τ_R B`  (internalizes `boxInv H' ⊆ T`)
- `crossRL B : □(τ_R B) → τ_L B`  (internalizes `boxInv T ⊆ H'`)

Because the cross-conditions are now **axioms**, deductive closure preserves them by construction
(via MP) — killing the Phase-8 blocker that `Cons_Y(Z) := boxInv Z ⊆ Y` was not closure-stable
(`probes/cs5-pair-primeness.lean:45-58`). Then a **single** `quasi_prime_set_exclusion` excluding
`E := {τ_L (□A), τ_R A}` (a 2-element set) yields a prime combined theory `T'`, and the pair is
recovered by preimage: `H' := {C | τ_L C ∈ T'}`, `T := {C | τ_R C ∈ T'}`.

### 2.1 Is it sound and mechanizable? — Yes, structurally.

Recovery from a single prime `T'` is clean and each clause has a concrete discharge:

| Pair clause | How recovered from prime `T'` |
|---|---|
| `H ⊆ H'` | seed `τ_L '' H ⊆ S ⊆ T'` |
| `H'`, `T` deductively closed (over `CS5ModalAxiom`) | **τ_L/τ_R derivation-lifting** (§3.3): a CS5-derivation of `C` from `Γ ⊆ H'` lifts to a `CS5Combined`-derivation of `τ_L C` from `τ_L '' Γ ⊆ T'`; closure of `T'` places `τ_L C ∈ T'`, i.e. `C ∈ H'` |
| `H'`, `T` quasi-prime | primeness projects: `τ_L(C∨D)=τ_L C ∨ τ_L D ∈ T'`, `T'` prime + `τ_L` injective ⇒ `C∈H' ∨ D∈H'`. `PrimeAdmissible` fields (`PrimeExclusion.lean:63`) project cleanly |
| `boxInv H' ⊆ T` | `□B∈H' ⇒ τ_L(□B)=□(τ_L B)∈T'`; `crossLR B` is derivable (axiom) so by closure+MP `τ_R B ∈ T'`, i.e. `B∈T` |
| `boxInv T ⊆ H'` | symmetric, via `crossRL` |
| `□A ∉ H'`, `A ∉ T` | `DerivExcludes E T'` at singletons `[τ_L(□A)]`, `[τ_R A]` (using `bigOr [x]=x∨⊥`, `x∈T'⇒x∨⊥∈T'` by `orI1`) |

Every generic ingredient `prime_set_exclusion` needs (`hOrI1/2`, `hOrE`, `hEFQ`, `cl_subset`,
`cl_mem_imp`, `cl_admissible_of_cons`, `bot_mem_cl_of_not_cons`, `hCut`, `hConsChain`) is
**parametric over the axiom predicate** and instantiates for `CS5Combined` exactly as
`quasi_prime_set_exclusion` (`CS5.lean:871`) instantiates them for `CS5ModalAxiom` — provided
`CS5Combined` has propositional constructors `implyK/implyS/efq/orI1/orI2/orE` (it does: they are
among the 17 CS5 constructors, re-declared over `Atom⊕Atom`). This is the reuse spine.

### 2.2 The one hard obligation — combined-system SEED CONSISTENCY.

`prime_set_exclusion` **consumes** `h_excl : DerivExcludes D E S` for the seed `S`; it does not
manufacture it. So the make-or-break lemma is:

```lean
-- S := modalDeductiveClosure CS5Combined (τ_L '' H)   (seed)
DerivExcludes (modalDerivationSystem CS5Combined) {τ_L (□A), τ_R A} S
-- i.e. for every list l over {τ_L(□A), τ_R A}, bigOr l ∉ S
```

Concretely (`l` a singleton is the essential case): **`τ_R A ∉ cl_combined(τ_L '' H)`** and
**`τ_L(□A) ∉ cl_combined(τ_L '' H)`**, plus that no disjunction of them is derivable.

The set-level analogue `cs5_pair_seed_mem` (`probes/cs5-pair-primeness.lean:98`, **sorry-free**)
proves `A ∉ cl_{CS5}(boxInv H)` from `□A ∉ H` via `box_mem_of_boxed_context` — but it lives in a
world where `Y = cl(boxInv H)` is **fixed** and the cross-conditions are **external set
inclusions**. In the combined system both sides grow *and interact through `crossLR`/`crossRL`*:
`crossLR` pushes boxed-L formulas to R, `crossRL` pushes boxed-R formulas back to L. Proving `A`
cannot leak to the R-side through this loop is **not** a mechanical port of `cs5_pair_seed_mem`;
it is the precise content that the Phase-8 finding warned about, now internalized.

**Two discharge routes (recommended order):**

1. **Semantic (recommended).** Prove *soundness of `CS5Combined`* over the two-sorted frame class
   where `τ_L`/`τ_R` atoms are interpreted at a designated `H'`-world / `T`-world pair with the
   symmetric CS5 relation between them (the positive-model dual of `CS5BoxGapWorld`,
   `CS5.lean:1246+`, which is already a landed Kripke countermodel with `Fintype`/`Decidable`
   instances). Then exhibit a concrete model satisfying `τ_L '' H` and refuting `τ_R A` and
   `τ_L(□A)`. Soundness gives `DerivExcludes` for free. This reuses the entire `cs5_soundness`
   apparatus (`CS5.lean:311`, `cs5_axiom_sound''`, `CS5.lean:366`) — the two new cross axioms need
   their own two soundness cases, which are one-liners on the designated pair frame.

2. **Proof-theoretic projection (fallback / obstruction candidate).** Show any combined derivation
   `τ_L '' H ⊢_{CS5Combined} τ_R A` projects to a `CS5` derivation forcing `□A ∈ H`
   (contradiction). The cross axioms have no CS5 analogue; they project to `boxInv`-transfer
   steps. **If this projection cannot be closed, that failure *is* the further mechanized
   obstruction** the task pre-authorizes.

**Verdict on 2.2:** achievable via route 1 with real (not mechanical) effort; genuinely at risk.
This is the single node on which the task's success vs. negative-result outcome turns.

### 2.3 Risk points where the repair could ALSO fail

- **R1 (primary): seed consistency / cross-axiom leakage** (§2.2). If `CS5Combined` is *not*
  sound over any frame separating `τ_R A` from `τ_L '' H` — e.g. if `crossLR`+`crossRL`+`4`/`B`
  collapse the two sorts (a "collapsing" phenomenon, cf. the Pacheco title) — the seed exclusion
  is false and the whole construction is vacuous. **This would be the negative result.**
- **R2: `axMap` totality.** The lifting `CS5ModalAxiom φ → CS5Combined (τ_L φ)` must cover all 17
  cases; each is mechanical (τ_L commutes with every connective, so the CS5Combined constructor at
  `τ_L`-images matches definitionally). Low risk, but 17 cases × commutation = tedious.
- **R3: `bDia`/`Kd` interaction with cross axioms** in seed consistency. `CS5` proves `◇⊥→⊥`
  (`cs5_dia_bot_imp_bot`, `CS5.lean:740`); the combined system's cross axioms could enable new
  `◇`-collapses. Must be checked when building the separating model.
- **R4: `H'` primeness vs. exclusion.** `prime_set_exclusion` gives `PrimeAdmissible T'` in the
  *combined* language; projecting to per-sort quasi-primeness needs `τ_L`/`τ_R` injective on
  `∨`-heads (true) **and** that `T'` prime ⇒ each preimage has the disjunction property. Verified
  clean in §2.1 but must be mechanized.
- **R5: file size / build time** (§5). Zorn + `Deriv.map` over `Atom⊕Atom` may be slow; scope to
  a new file and `lake build` incrementally.

---

## 3. Reuse map (existing asset → intended use)

### 3.1 Prime-exclusion engine (the spine) — REUSE AS-IS, re-instantiated at `CS5Combined`

| Asset | Location | Use |
|---|---|---|
| `prime_set_exclusion` | `PrimeExclusion.lean:558` | the single Zorn application producing prime `T'` |
| `set_maximal_is_prime`, `set_excluding_chain_union`, `DerivExcludes`, `SetExcludingSupersets`, `bigOr` | `PrimeExclusion.lean:428/400/328/334/320` | consumed by `prime_set_exclusion`; nothing to rebuild |
| `quasi_prime_set_exclusion` | `CS5.lean:871` | **template to clone** for `CS5Combined` (swap the axiom system + closure); 10 discharge arguments copy over verbatim |
| `cs5_diam_witness` | `CS5.lean:906` | template for the `E`-exclusion discharge *pattern* (singleton-list handling, `orI1` step); also directly reused for `H'`-segment `diam_witness` |
| `cs5_fcsymbox_theory`, `cs5_fc4_theory` | `CS5.lean:1043/1122` | canonical-closure templates; reused unchanged in `cs5FC''_cs5Mreach` (already landed) |

### 3.2 Canonical-model / truth-lemma scaffold — REUSE, adapt box case only

| Asset | Location | Use |
|---|---|---|
| `ck_truth_lemma` | `CKTruthLemma.lean:133` | **copy** for `cs5_truth_lemma`; keep atom/bot/and/or/imp/diamond/box-forward cases, replace box-backward with `cs5_box_backward` |
| `cs4_truth_lemma` | `CS4.lean:~455` | closest completed template (own truth lemma over a restricted-tail subtype) |
| `ckvalidFC_completeness` | `CKExtension.lean:227` | final wrapper: supply `realize` (Lindenbaum + `cs5_truth_lemma`) + `h_canonFC := cs5FC''_cs5Mreach` |
| `cs5FC''_cs5Mreach` | `CS5.lean:1242` | **already landed** — the frame condition holds; do not rebuild |
| `cs5Seg`, `CS5Segment.ofHead`, `cs5Val`, `cs5Bot`, upward-closure/explosion lemmas | `CS5.lean:975-1030` | build the two witness worlds `w'`, `u` for box-backward integration |
| `CKSegment`, `cmreach`, `cval`, `cbotForces`, `boxInv`, `QuasiPrime`, `.closed`, `.disj` | `Segment.lean:64-183` | world/pair plumbing |
| Lindenbaum: `quasi_prime_exclusion` / `quasi_prime_box_exclusion` | `SegmentLindenbaum.lean:159/188/258` | `realize` witness (underivable ⇒ prime theory omitting φ) |

### 3.3 Derivation transport (the flagged "new infra") — MOSTLY A COROLLARY

The probe called τ_L/τ_R derivation-lifting "genuinely new infrastructure beyond a mapping
exercise". **Finding: it is largely a corollary of task-419 machinery, not built from scratch.**

| Asset | Location | Use |
|---|---|---|
| `Metalogic.Deriv.map` | `ProofSystemMorphism.lean:186` | **the universal lift**: transports `Deriv σ₁ Γ φ` to `Deriv σ₂ (Γ.map g) (g φ)` where `g : F₁ → F₂` **changes the formula type**. Exactly τ_L/τ_R lifting. |
| `ProofSigHom {F₁ F₂}` | `ProofSystemMorphism.lean:124` | the hom to build: `g := τ_L`, `g_imp` (rfl via `Proposition.map`), `axMap` (17 CS5 cases → CS5Combined), `clMap` (box↦box, rfl) |
| `modalSig`, `toDeriv`, `ofDeriv`, `modalEquiv` | `LiftViaMorphism.lean:65/79/94` | bridge `DerivationTree Axioms ≃ Metalogic.Deriv (modalSig Axioms)`; wrap `Deriv.map` back to `DerivationTree` |
| `liftDerivationWith` / `liftFormula` | `Bimodal/.../ConservativeExtension/Lifting.lean` | **direct precedent**: an existing formula-type-relabeling derivation lift via the same `Deriv.map ⟨liftFormula a, …⟩` pattern (cited at `ProofSystemMorphism.lean:185`). Clone this shape for τ_L/τ_R. |

Net: the "new infra" reduces to (a) `Proposition.map : (α→β) → Proposition α → Proposition β`
(simple structural recursion, ~12 lines + commutation `rfl` lemmas — **does not yet exist**,
confirmed by grep), and (b) one `ProofSigHom` per tag with a 17-case `axMap`. The functorial
transport itself is `Deriv.map`. This materially de-risks the projection/closure steps.

### 3.4 Literature (`pacheco_2024_collapsingconstructiveandintuitionisticmodallogics`)

Grounded via the probe's corpus confirmation (`probes/cs5-pair-primeness.lean:5-19`, which quotes
chunks `ec3a8bddd907f0c4` and `39fb2b22fa8afe5a` verbatim). Two defects confirmed and **must not
be transcribed**:

- **Lemma 16/18 negation-completeness move is UNSOUND here**: Pacheco derives `¬(ϕ∨ψ)∈Θ` from
  `ϕ∉Θ, ψ∉Θ` — valid only for negation-complete maximal sets, **false** for a quasi-prime,
  poset-maximal `Θ` carrying cross-conditions (maximality can fail via `Θ□ ⊄ Σ`, not
  inconsistency). Only the **Zorn skeleton** (seed → chain-union → maximal → project) ports; the
  primeness *engine* comes from CSLib's `prime_set_exclusion`, which obtains the disjunction
  property from `hOrE` combination (`set_maximal_is_prime`), never from negation-completeness.
- **Lemma 18's `ϕ ∉ X ∪ Y` invariant + `Γ ⊆ Y`** risks an empty poset if `ϕ` is forced into `Y`.
  The doubled-atom design sidesteps this: exclusion is a *derivability* condition (`DerivExcludes`)
  over the combined theory, not a set-membership invariant carried through Zorn.

The "collapsing" theme of the paper is itself the **warning flag for R1**: constructive S5's `4`+`B`
have known collapse behavior; the seed-consistency lemma is exactly a non-collapse claim for the
two sorts under the combined axioms.

---

## 4. Concrete Lean sketches

**(a) Atom relabeling (new, foundational — put in `Modal/Basic.lean` or `Modal/Substitution.lean`)**
```lean
def Proposition.map (f : α → β) : Proposition α → Proposition β
  | .atom p => .atom (f p)
  | .bot => .bot
  | .imp a b => .imp (a.map f) (b.map f)
  | .and a b => .and (a.map f) (b.map f)
  | .or a b => .or (a.map f) (b.map f)
  | .box a => .box (a.map f)
  | .diamond a => .diamond (a.map f)

@[simp] theorem Proposition.map_imp (f) (a b) :
    (a.imp b).map f = (a.map f).imp (b.map f) := rfl      -- and _box, _or, _and, _bot, _dia
```

**(b) Combined axiom system (new — in the new canonical file)**
```lean
inductive CS5Combined : Proposition (Atom ⊕ Atom) → Prop where
  | base {φ : Proposition (Atom ⊕ Atom)} : CS5ModalAxiom φ → CS5Combined φ   -- reuse all 17
  | crossLR (B : Proposition Atom) :
      CS5Combined ((Proposition.box (B.map Sum.inl)).imp (B.map Sum.inr))
  | crossRL (B : Proposition Atom) :
      CS5Combined ((Proposition.box (B.map Sum.inr)).imp (B.map Sum.inl))
```
(The `base` constructor makes `axMap`'s 17 modal cases a single `CS5Combined.base ∘ (relabel of
the CS5 instance)`; note `CS5ModalAxiom` must be applied at `Atom⊕Atom`, and `τ_L`-image of a
CS5-over-`Atom` axiom is a CS5-over-`Atom⊕Atom` axiom by connective commutation.)

**(c) The τ_L hom + transport (corollary of `Deriv.map`)**
```lean
def τL : ProofSigHom (modalSig (@CS5ModalAxiom Atom)) (modalSig (@CS5Combined Atom)) where
  g := Proposition.map Sum.inl
  g_imp := fun _ _ => rfl
  axMap := fun φ h => ⟨CS5Combined.base (cs5_axiom_relabel Sum.inl h)⟩   -- 17-case helper
  clMap := fun m hm => ⟨Proposition.box, by simpa using hm, fun _ => rfl⟩
-- lifted DerivationTree transport:
--   DerivationTree CS5ModalAxiom Γ φ → DerivationTree CS5Combined (Γ.map τL.g) (τL.g φ)
--   via ofDeriv (Deriv.map τL (toDeriv d))
```

**(d) Seed consistency (the hard lemma — sketch of route-1 semantic discharge)**
```lean
theorem cs5Combined_seed_excludes {H} (hH : QuasiPrime CS5ModalAxiom H)
    (h_not : Proposition.box A ∉ H) :
    DerivExcludes (modalDerivationSystem (@CS5Combined Atom))
      {x | x = (Proposition.box A).map Sum.inl ∨ x = A.map Sum.inr}
      (modalDeductiveClosure CS5Combined ((Proposition.map Sum.inl) '' H)) := by
  -- Build the 2-world designated frame (dual of CS5BoxGapWorld), prove CS5Combined-soundness
  -- there (17 base cases from cs5_axiom_sound'' + 2 cross cases), interpret τ_L at world w
  -- (head H) and τ_R at world u (a boxInv-H tail omitting A), then any bigOr l ∈ closure would
  -- be forced at w, but each disjunct fails there ⇒ contradiction.
  sorry   -- <-- THE node that decides success vs. negative result
```

---

## 5. File-size / organization recommendation

`CS5.lean` is **1379 lines**; the new machinery is ~650-800 lines (Proposition.map + commutation
~40; `axMap` 17-case relabel helper ~120; `CS5Combined` + soundness of cross axioms ~120; seed
consistency ~150-250 — the bulk; projection lemmas ~120; `cs5_box_backward` ~60; `cs5_truth_lemma`
~130; completeness wrapper ~40). CS5.lean would blow past 2000 lines.

**Recommendation (take the deferred split):**
1. `Proposition.map` + `@[simp]` commutation lemmas → **`Modal/Basic.lean`** (broadly reusable;
   already the home of `Proposition`). Keeps the relabel primitive foundational.
2. New file **`Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`**, `import`ing
   `CS5.lean`, housing: `CS5Combined`, the `τL`/`τR` homs + transport corollaries,
   `cs5Combined_*` prime-exclusion instantiation, seed consistency, pair recovery,
   `cs5_box_backward`, `cs5_truth_lemma`, `cs5_completeness`, `cs5_soundness_completeness`.
   (Name mirrors the task's "deferred CS5Canonical.lean split".)
3. Remember `lake exe mk_all --module` after adding the file, and `import Cslib.Init` at top.

This isolates the slow Zorn/`Deriv.map`-over-`Atom⊕Atom` build from the already-green `CS5.lean`.

---

## 6. Phased implementation direction (for the planner)

- **Phase 1 — Atom relabeling primitive.** `Proposition.map` + commutation `@[simp]` lemmas in
  `Basic.lean`. Verify with a scoped build. *Low risk, ~40 lines.* Gate: `rfl` commutation for
  all 7 connectives.
- **Phase 2 — Combined system + derivation transport.** `CS5Canonical.lean`: `CS5Combined`,
  `cs5_axiom_relabel` (17-case `CS5ModalAxiom φ → CS5ModalAxiom (φ.map f)`), `τL`/`τR`
  `ProofSigHom`s, and the `DerivationTree` transport corollaries via `Deriv.map`+`modalEquiv`.
  *Medium risk (tedium), reuses `LiftViaMorphism`/bimodal `Lifting.lean`.*
- **Phase 3 — SEED CONSISTENCY (decision phase).** Prove `cs5Combined_seed_excludes` via route-1
  (combined-frame soundness of the 2 cross axioms + a designated-pair separating model, dual of
  `CS5BoxGapWorld`). **This is the go/no-go gate.** If it cannot be closed sorry-free, pivot to
  route-2 projection; if *that* also fails, land the failure as a mechanized obstruction theorem
  and mark completeness **[BLOCKED]** citing both 509 obstructions + this third one. *High risk.*
- **Phase 4 — Prime `T'` + pair recovery.** Clone `quasi_prime_set_exclusion` at `CS5Combined`;
  apply `prime_set_exclusion` with `E = {τ_L(□A), τ_R A}`; define `H'`/`T` as preimages; prove the
  7 pair clauses (§2.1) using Phase-2 transport for closure and injectivity for primeness. Emit
  `cs5_box_backward`. *Medium risk.*
- **Phase 5 — Truth lemma + completeness.** `cs5_truth_lemma` (clone `ck_truth_lemma`, box-backward
  via `cs5_box_backward`); `realize` via Lindenbaum; `cs5_completeness` /
  `cs5_soundness_completeness` via `ckvalidFC_completeness` + landed `cs5FC''_cs5Mreach`. *Low risk
  once Phase 4 lands.*
- **Verification.** `lake build` (full), `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake shake`, `lake test`; `#print axioms cs5_completeness` must show only
  `Classical.choice`/`propext`/`Quot.sound` (Zorn) — **no `sorryAx`, no new axiom.**

**Zero-debt note:** the only acceptable non-completion is Phase 3 failing, in which case the
deliverable is a *proved* obstruction theorem (negative result), not a `sorry`. No placeholder
`sorry`, no new axiom, no vacuous `def _ := True` at any point (per `.claude/rules/lean4.md`).

---

## 7. Honest feasibility assessment

**UNCERTAIN, leaning constructive on structure but with one real failure node.**
- **In favor:** the design is coherent; pair recovery and truth-lemma integration are mechanical;
  the prime-exclusion engine and `Deriv.map` transport are directly reusable (the flagged "new
  infra" is a corollary, not a rebuild); three landed templates
  (`cs5_diam_witness`/`cs5_fcsymbox_theory`/`cs5_fc4_theory`) plus `quasi_prime_set_exclusion`
  cover the instantiation pattern.
- **Against:** everything hinges on Phase 3 (combined-system seed consistency), which is *not* a
  port of the sorry-free `cs5_pair_seed_mem` — the cross axioms create L↔R interaction that
  Pacheco's "collapsing" theme specifically warns may be non-separable. If `CS5Combined` collapses
  the two sorts, the seed exclusion is false and completeness stays blocked with a **third**
  mechanized obstruction. That is an explicitly acceptable outcome.

I recommend proceeding to `/plan` with Phase 3 flagged as the adversarial decision gate.
