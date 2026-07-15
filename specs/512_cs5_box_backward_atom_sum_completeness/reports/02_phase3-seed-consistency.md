# Research Report 02 — Task 512 Phase 3: Combined-System Seed Consistency

**Task type**: cslib (Lean 4, hard / deflection-prone). **Reference-grounding tier**: 1 (literature-backed).
**Obligation**: `cs5Combined_seed_excludes` — the Phase-3 go/no-go gate.
**Target files**: `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (landed Phases 1–2),
`Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean`, `.../SegmentLindenbaum.lean`.
**Verdict (headline)**: The claim is **very likely TRUE (no obstruction)**. The mechanizable path is
**route-2 (proof-theoretic derivation induction)**, not route-1. Both routes *as sketched in report 01*
are dead; report 01's route-1 recommendation is **corrected** below. Confidence: claim-true ~85–90%,
route-2 mechanizable ~70%.

---

## Source-to-Implementation Mapping (Tier 1)

| Source claim | BibKey | Lean target / landed asset | Translation notes |
|---|---|---|---|
| Lemma 16/18 negation-completeness move | `Pacheco2024` | (deliberately **not** transcribed) | Unsound for quasi-prime poset-maximal sets; only the Zorn skeleton ports. Confirmed verbatim in probe corpus quotes (`cs5-pair-primeness.lean:5–19`). |
| Lemma 18 "collapsing" theme = sort-collapse warning | `Pacheco2024` | risk R1 for `cs5Combined_seed_excludes` | The paper's collapse warning is the reason Phase 3 is a genuine gate; my analysis finds **no** collapse here (see §3, §5). |

BibKey `Pacheco2024` verified against `references.bib:895` (`@misc{Pacheco2024, ... Collapsing
Constructive and Intuitionistic Modal Logics}`). No new bib entry needed.

---

## 1. The obligation, restated against landed source

`CS5Combined` (`CS5Canonical.lean:73–81`, landed, verified) over `Proposition (Atom ⊕ Atom)`:
`base` (all 17 `CS5ModalAxiom` schemata, re-declared) plus
`crossLR B : □(τL B) → τR B` and `crossRL B : □(τR B) → τL B`, where
`τL = Proposition.map Sum.inl`, `τR = Proposition.map Sum.inr` (`CS5Canonical.lean:115–131`).

The go/no-go lemma (plan §Phase 3):

```lean
theorem cs5Combined_seed_excludes {H} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    (h_not : Proposition.box A ∉ H) :
    DerivExcludes (modalDerivationSystem (@CS5Combined Atom))
      {x | x = (Proposition.box A).map Sum.inl ∨ x = A.map Sum.inr}
      (modalDeductiveClosure CS5Combined ((Proposition.map Sum.inl) '' H))
```

`DerivExcludes D E S := ∀ l, (∀ x ∈ l, x ∈ E) → bigOr l ∉ S` (`PrimeExclusion.lean:328`),
`bigOr [] = ⊥`, `bigOr (x::xs) = x ∨ bigOr xs` (`PrimeExclusion.lean:320`). The essential singleton
cases are `τR A ∉ S` and `τL(□A) ∉ S`; the general list case adds only positive disjunctions of these.

## 2. The reframing that changes the problem: the seed pair already satisfies every cross-condition

The single most important finding, missed by report 01: **the constructible seed pair
`(H, cl(boxInv H))` already satisfies ALL the pair clauses except R-primeness**, and this is *landed,
sorry-free* in the probe `cs5_pair_seed_mem` (`cs5-pair-primeness.lean:98`, `#print axioms` clean).
Writing `HR := modalDeductiveClosure CS5ModalAxiom (boxInv H)`, that theorem proves simultaneously:

- `H ⊆ H`, `H` and `HR` deductively closed;
- `boxInv H ⊆ HR` (the **crossLR** cross-condition);
- `boxInv HR ⊆ H` (the **crossRL** cross-condition) — line 109, via `cs5_boxInv_subset` + `boxInv_mono`;
- `□A ∉ H`; and crucially **`A ∉ HR`** — line 110–112, via `box_mem_of_boxed_context`.

Underlying landed ingredients (all in `Cslib/`, re-usable directly, no probe dependency):
- `cs5_boxInv_subset : QuasiPrime CS5ModalAxiom H → boxInv H ⊆ H` (`CS5.lean:621`, axiom `T`).
- `box_mem_of_boxed_context` (`SegmentLindenbaum.lean:109`): `L ⊢ φ` with `□ψ ∈ H` for all `ψ ∈ L`
  ⟹ `□φ ∈ H` — the K-rule closure that forces `A ∉ HR` from `□A ∉ H`.
- `modalDeductiveClosure`/`_closed` (`PrimeTheory.lean:78/127`), `HasBot`/`bigOr`/`DerivExcludes`.
- `box_refuting_theory` (`SegmentLindenbaum.lean:177`): a **quasi-prime** `T ⊇ boxInv H` with `A ∉ T`.

Consequence: **the only thing Phase 4 (`cs5_box_backward`) is missing is R-primeness of the R-theory.**
Phase 3 (`cs5Combined_seed_excludes`) is *weaker*: it needs non-derivability, not a prime witness. So
Phase 3 should be dischargeable without solving Phase 4 — provided the two sorts do not collapse.

Two closure facts that drive everything (both landed): `HR ⊆ H` (since `boxInv H ⊆ H` and `H` closed,
`cs5-pair-primeness.lean:103–105`), and `A ∉ HR`.

## 3. Obstruction check (adversarial): can `τL '' H ⊢ τR A`?

I pressure-tested a derivation of `τR A` from `τL '' H` with the *hardest* case `A ∈ H ∧ □A ∉ H`
(perfectly consistent — necessity does not follow from truth). Fixpoint / leak analysis of the reachable
combined theory:

1. For `C ∈ boxInv H` (i.e. `□C ∈ H`): `τL(□C) = □(τL C) ∈ τL '' H` is a premise, so `crossLR C` fires
   (MP) to give `τR C`. Hence `τR '' (boxInv H) ⊆ S`, extended by R-side S5 axioms to `τR '' HR ⊆ S`.
2. `crossRL` can only reproduce `τL B` for `B` with `□(τR B)` derivable, i.e. `□B ∈ HR`; but
   `HR ⊆ H` (landed) so `□B ∈ H`, so `B ∈ H` (axiom `T`) — **already present**. So **crossRL is
   conservative over `base+crossLR` for L-content**: it never enlarges the L-side beyond `τL '' H`.
3. From `τL A` (if `A ∈ H`) one derives `◇ τR A` (via `bBox: τL A → □◇τL A`, then
   `crossLR(◇A): □(τL ◇A) → ◇ τR A`) — but **never the bare `τR A`**. Getting `τR A` unguarded needs
   `crossLR A` to fire, i.e. `□(τL A) = τL(□A) ∈ S`, i.e. `□A` leaking into the L-closure — which step 2
   forbids (`□A ∉ H`). No S5 rule turns `◇τR A` into `τR A` (`◇X → X` is not a theorem).

The reachable combined theory is thus (informally) `τL '' H ∪ τR '' HR ∪ {◇/□-guarded and mixed
consequences}`, and `A ∉ HR` keeps `τR A` out. **No obstruction derivation was found; the claim holds.**
This matches the S5-cluster intuition: cluster-mates share box-content but may differ on non-boxed
content — exactly `boxInv H = boxInv HR` while `A ∈ H \ HR` is allowed.

## 4. Route-1 (semantic) — CORRECTED: single-witness models cannot validate both cross axioms

Report 01 recommended route-1 (build a designated-pair Kripke model, prove `CS5Combined`-soundness, read
off `DerivExcludes`). Landed soundness apparatus: `cs5_axiom_sound''` (`CS5.lean:366`), `cs5_soundness`
(`CS5.lean:311`) over `cs5FC``/`cs5FC''` frames; the landed finite `decide`-model `CS5BoxGapWorld`
(`CS5.lean:1274–1379`) is a `cs5FC''` frame. Two new soundness cases (`crossLR`/`crossRL`) would be
required.

**Adversarial finding (corrects report 01):** a soundness model must validate `crossRL B : □(τR B) → τL B`
at every world, which forces `boxInv(R-forced) ⊆ (L-forced)` *for all B* — i.e. the model must carry the
crossRL cross-condition. The two candidate R-witnesses each fail exactly one requirement:

- `HR = cl(boxInv H)` satisfies both cross-conditions (§2) **but is not prime**, so it is not the
  forced-set of any world (∨-forcing needs the disjunction property).
- `box_refuting_theory`'s `T*` is **prime** with `A ∉ T*`, `boxInv H ⊆ T*` (validates `crossLR`), **but
  `boxInv T* ⊄ H`** in general, so it **falsifies `crossRL`** — soundness is unavailable.

So no single-world R-witness gives a sound model; a genuinely separating model needs canonical-scale
(many R-worlds) structure whose truth lemma is adjacent to the very box-backward completeness that is open.
This confirms the implementer's route-1 findings (toy frames insufficient; canonical-scale needed) and adds
the precise reason: **crossRL-validity ⟺ carrying the crossRL cross-condition on the model, which no single
Lindenbaum witness provides.** Route-1 is therefore *not* the low-effort path.

## 5. Route-2 (proof-theoretic) — the recommended, mechanizable path; naive projection provably impossible

Report 01's route-2 (collapse projection `π = Sum.elim id id`) yields only `H ⊢ A` — not a contradiction
(the implementer's finding 4). I generalized this to a **general impossibility**: *no* homomorphic
atom-substitution translation `tr : Proposition(Atom⊕Atom) → Proposition Atom` can witness the exclusion.
Such a `tr` (with `tr(inl p)=p`, `tr(inr p)=ρ(p)`, commuting with all connectives incl. `□`) sends the two
cross axioms to the requirements, for all `B`:

- (i) `⊢_CS5 □B → Bρ` (from `crossLR`), and (ii) `⊢_CS5 □(Bρ) → B` (from `crossRL`), where `Bρ = B[ρp/p]`.

At `B = p ∨ q`, (i) becomes `⊢ □(p∨q) → (ρp ∨ ρq)`. With `ρ = □` this is `□(p∨q) → (□p ∨ □q)` — **not a
CS5/S5 theorem**; with `ρ = id` it collapses (fails to separate when `A ∈ H`). No `ρ` satisfies (i)+(ii)
and separates `A`. **Any homomorphic/substitution route is dead** (sharper than the specific collapse
report 01 found). The box on the left "sees through" the connectives of `B` while `ρ` sits at the atoms —
an irreducible non-compositionality.

**What route-2 must therefore be:** a derivation induction on `CS5Combined` `DerivationTree`/`Deriv`
structure (5 rule cases: `ax`, `assumption`, `modus_ponens`, `necessitation`, `weakening` — cf.
`cs5_soundness` at `CS5.lean:325–340`), establishing a **closure-characterization / projection invariant**
that handles mixed (both-sort) formulas non-homomorphically. The concrete skeleton:

1. **Set-level scaffolding (mostly landed).** Re-prove in `CS5Canonical.lean` the seed-pair facts for
   `HR := modalDeductiveClosure CS5ModalAxiom (boxInv H)`: `boxInv H ⊆ HR`, `boxInv HR ⊆ H`, `HR ⊆ H`,
   `A ∉ HR` — direct ports of `cs5_pair_seed_mem`'s body (`cs5-pair-primeness.lean:103–112`) using
   `cs5_boxInv_subset`, `box_mem_of_boxed_context`, `modalDeductiveClosure_closed`. ~40 lines, low risk.
2. **The projection lemma (the crux, new, ~150–220 lines).** By induction on a `CS5Combined` derivation
   `d : Deriv CS5Combined (τL '' H list) φ`, prove an invariant `Φ φ` strong enough to be closure-stable
   and to give: `φ` R-pure (all atoms `inr`) ⟹ `underlying φ ∈ HR`; `φ` L-pure ⟹ `underlying φ ∈ H`.
   The invariant must cover mixed `φ`. The **crossRL-conservativity** fact (§3 step 2: crossRL adds no
   new L-content because `HR ⊆ H`) is the key lever making the `crossRL` axiom case and the mixed
   `modus_ponens` cases go through. `necessitation` only applies to `∅`-context combined theorems
   (`.necessitation` requires empty context, `CS5.lean:334`), which project to CS5 theorems.
3. **Conclude.** `τR A ∈ S` ⟹ (projection) `A ∈ HR` ⟹ contradiction with `A ∉ HR`. Similarly `τL(□A) ∈ S`
   ⟹ `□A ∈ H`, contradicting `h_not`. The `bigOr` disjunction cases: a positive disjunction of
   `{τL(□A), τR A}` in the closed `S` reduces to one disjunct being derivable under the projection (the
   invariant tracks positive-disjunction membership), each refuted as above. ~40 lines.

**Reused τ-transport (landed):** `cs5_lift_deriv_L`/`_R` (`CS5Canonical.lean:151/158`) already transport
CS5→Combined; the projection is their *converse restricted to the seed*, and shares the
`ProofSigHom`/`Deriv.map` shape (`ProofSystemMorphism.lean`) for the mechanical (base-axiom) cases.

## 6. Line-count & non-mechanical steps

- Set-level pair facts (step 1): ~40 lines, **mechanical** (port of landed probe body).
- Projection invariant definition (step 2): the **single non-mechanical node** — designing `Φ` so it is
  closure-stable across the mixed `modus_ponens` case and the two cross-axiom cases. ~150–220 lines.
- Conclusion + `bigOr` handling (step 3): ~40 lines, mostly mechanical.

Total ~230–300 lines. The only genuinely novel step is the mixed-formula invariant `Φ`; everything else is
landed reuse or a mechanical port.

---

## Adversarial Self-Verification

Challenged each claim; revisions and residual uncertainty:

- **"Seed pair satisfies all cross-conditions" (§2)** — VERIFIED against source: `cs5_pair_seed_mem`
  (`cs5-pair-primeness.lean:98–112`) proves membership in `cs5PairPoset` whose definition
  (`:85–91`) literally lists `boxInv p.1 ⊆ p.2`, `boxInv p.2 ⊆ p.1`, `φY ∉ p.2` (= `A ∉ HR`). Confirmed
  by reading the poset definition and the proof body, not the docstring. The probe is `#print axioms`
  clean; its ingredients (`cs5_boxInv_subset`, `box_mem_of_boxed_context`, `modalDeductiveClosure_closed`)
  are all in `Cslib/` (hover-verified signatures). Load-bearing and solid.
- **Report 01's route-1 recommendation** — CHALLENGED and CORRECTED: I initially suspected route-1 was
  simply "heavy"; on verification it is *structurally blocked at single-witness scale* because
  `crossRL`-validity requires the model to carry `boxInv(R) ⊆ L`, which `box_refuting_theory`'s prime
  witness violates and `cl(boxInv H)` cannot supply as a forcing world (non-prime). This is a sharper,
  source-grounded reason than "under-specified companion valuation."
- **"Homomorphic translation impossible" (§5)** — VERIFIED by the `∨` counterexample
  `□(p∨q) → (□p∨□q)` (not an S5 theorem) plus the id-collapse; this is a *general* impossibility for the
  substitution class, strictly stronger than the implementer's single collapse instance. Independent of
  library machinery (a mathematical fact), so not circumventable by a cleverer `ProofSigHom`.
- **"Claim is TRUE" (§3)** — the fixpoint/leak analysis is informal (not a Lean proof). Confidence ~85–90%.
  The residual risk is a *mixed-formula* derivation (e.g. via `orE`/`kdia` through a both-sort formula) that
  the per-sort fixpoint sketch does not visibly cover; this is exactly what step 2's invariant must
  discharge and is the reason route-2 mechanizability is ~70%, not higher. I did **not** manufacture a
  proved obstruction, because every leak attempt failed and asserting a false collapse would be worse than
  an honest "route-2, crux identified."
- **Zero-debt compliance** — the recommendation introduces no `sorry`, no new axiom; the fallback (if step 2
  cannot be closed) remains a *proved* obstruction, not a placeholder.
- **Reuse Check Protocol** — exhausted: Foundations (`PrimeExclusion`, `PrimeTheory`, `ProofSystemMorphism`),
  Constructive (`CS5`, `SegmentLindenbaum`, `Segment`), and the landed `CS5Canonical` transport were all
  searched (grep + `lean_local_search` + `lean_hover_info`); no existing lemma discharges the mixed-formula
  projection, so step 2 is genuinely new (not a missed reuse).

**No fundamental flaw found; no Revised Direction needed.** Recommendation stands: route-2.
