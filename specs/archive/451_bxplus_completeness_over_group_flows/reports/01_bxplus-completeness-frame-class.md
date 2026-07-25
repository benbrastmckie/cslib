# Research Report — Task 451: Completeness of BX⁺ over group-ordered flows

**Goal (as delegated)**: prove `BX⁺` (`Temporal FrameClass.Metric`, defined in task 449) COMPLETE
over the class of ordered-abelian-group (oag) temporal frames — every formula valid on all
group-ordered flows is `BX⁺`-derivable; equivalently every `BX⁺`-consistent formula has a
group-ordered countermodel.

**Reference-grounding tier**: Tier 1 (literature-backed). Grounded in the archived task-445
round-2 obstruction report (`specs/archive/445_fix_temporal_conservativity_domain_mismatch_sorry/reports/02_literature-grounded-conservativity-obstruction.md`),
`Burgess1984` §6.1, `Xu1988` Thm 2.9, and the CSLib axiom/soundness files. All load-bearing
Mathlib facts machine-verified with `lean_run_code` (exit 0).

## TL;DR — the frame class must be decided before implementing; the literal oag goal is NOT clean

Completeness over a **smaller** class is **harder** (the countermodel must live inside the smaller
class). The task's stated target — completeness over the ordered-abelian-group class — splits, via
the four uniformity axioms, into a **dense** sub-case and a **discrete** sub-case:

- **Dense sub-case: SOLVED and clean.** A `BX⁺`-consistent formula whose canonical countermodel is
  densely ordered lands on **ℚ** (a genuine oag) by Cantor's isomorphism theorem
  (`Order.iso_of_countable_dense`), transporting satisfaction along the order-iso. Every Mathlib
  prerequisite is verified present. This is the piece that unlocks task 450's semantic route.

- **Discrete sub-case: this is a genuine obstruction for the *literal* oag goal.** The canonical
  discrete `BX⁺` countermodel is a countable discrete-uniform serial order — order-type
  `ℤ ×ₗ A` for an arbitrary countable linear order `A` (the ℤ-block index). Such an order is an
  oag **iff** `A` is itself a group order, which forces `A` to be *homogeneous*. A `BX⁺`-consistent
  formula can produce a non-homogeneous block index (e.g. `ℤ + ℤ = ℤ ×ₗ 2`), which is a perfectly
  good `BX⁺` frame but is **not** an oag. There is **no Mathlib lemma** to embed such a model into
  an oag preserving Since/Until truth (order-embeddings do not preserve `U(⊥,⊤)`), and it is
  **very likely false** that `BX⁺` is complete over oag: `BX⁺` has no discreteness-induction /
  archimedean axiom, so `Th(oag) ⊋ BX⁺` is the expected outcome (`BX⁺` = logic of *all* uniform
  orders, which is strictly weaker than the logic of the special homogeneous oag subclass).

**Decision**: implement completeness over the class `BX⁺` is genuinely sound-and-complete over —
the **uniform serial-linear class `U`** (each frame either densely ordered, or discrete with
immediate successors/predecessors everywhere) — NOT literally over oag. This is the tight, honest,
sorry-free-achievable result. Deliver the **dense→ℚ (oag) bridge** as the concrete sub-result that
serves task 450. **Escalate** the literal oag-completeness of the discrete case as a precise,
research-level open lemma; do NOT chase it with `sorry` or an axiom (zero-debt).

## Reuse Check Protocol (reuse-first)

| Candidate reuse | Result |
|---|---|
| Cantor / countable-dense iso | **Mathlib `Order.iso_of_countable_dense`** (`Mathlib.Order.CountableDenseLinearOrder`) — verified signature below. Reuse directly. |
| `ChronicleSubtype` countermodel machinery | **Fully reusable.** `ChronicleSubtype A h_mcs = {x : ℚ // x ∈ limitDom A h_mcs}` (`Chronicle/ChronicleToCountermodel.lean:52`), already carries `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`; subtype-of-ℚ ⇒ `Countable` (verified). |
| Dense completeness template | **`completeness_dense`** (`Metalogic/DenseCompleteness.lean:252`) + `chronicleDenselyOrderedDense` (`:227`) are the exact shape to mirror for the Metric case. |
| Metric-MCS → chronicle uniformity | **Reuse `dense_indicator_in_all_limit_points`** (`DenseCompleteness.lean:112`) pattern: it propagates a `¬U(⊤,⊥)` membership to *all* limit points. The Metric case needs the mirror for the four `discrete_*` axioms (they are theorems in every limit-MCS via `theoremInMcsFc`). |
| `validDiscrete` (single-block ℤ) | **Already exists** (`Semantics/Validity.lean:96`) as validity over `[SuccOrder][PredOrder][IsSuccArchimedean]` serial orders. NOTE: `IsSuccArchimedean` forces a *single* ℤ-block (≅ ℤ), so `validDiscrete` is strictly stronger than the multi-block discrete-uniform class the chronicle produces. Do not conflate them. |
| Satisfaction transport along order-iso | **Does NOT exist** — no `Satisfies`/`OrderIso` lemma in `Cslib/Logics/Temporal/` (grep empty). Must be built (standard formula-induction; see §4). |
| oag domain instances on ℚ | **Reuse Mathlib** — `AddCommGroup ℚ`, `IsOrderedAddMonoid ℚ`, `DenselyOrdered ℚ`, `Nontrivial ℚ`, serial instances all verified present. |

## Verified Mathlib facts (all `lean_run_code`, exit 0)

- `Order.iso_of_countable_dense (α β) [LinearOrder α][LinearOrder β][Countable α][DenselyOrdered α][NoMinOrder α][NoMaxOrder α][Nonempty α][Countable β][DenselyOrdered β][NoMinOrder β][NoMaxOrder β][Nonempty β] : Nonempty (α ≃o β)`.
- `AddCommGroup ℚ`, `IsOrderedAddMonoid ℚ`, `DenselyOrdered ℚ`, `NoMaxOrder ℚ`, `NoMinOrder ℚ`, `Nontrivial ℚ` — all `inferInstance`.
- `Countable {x : ℚ // p x}` for any `p` — `inferInstance`.
- `[Nontrivial {x : ℚ // p x}] → Nonempty {x : ℚ // p x}` — `inferInstance`. (So the chronicle's
  existing `Nontrivial` instance discharges Cantor's `Nonempty` hypothesis on the countermodel side,
  and ℚ's `Nontrivial` discharges it on the ℚ side.)

## The architecture (how completeness is currently built)

`completeness` (`Metalogic/Completeness.lean:101`) and `completeness_dense`
(`DenseCompleteness.lean:252`) both work by contrapositive:

1. `¬ derivable φ` ⇒ `{¬φ}` consistent (`neg_consistent_of_not_derivable[_dense]`).
2. Lindenbaum → MCS `M` (`temporal_lindenbaum[_fc]`).
3. Build the chronicle countermodel `ChronicleSubtype M` (a countable suborder of ℚ) with
   `chronicleModel`, zero point `chronicleZero`.
4. `chronicle_truth_lemma`: `Satisfies model t φ ↔ φ ∈ limitF M t.val`.
5. Apply the validity hypothesis at `t₀` (val `= 0`, `limitF 0 = M`), yielding `φ ∈ M`,
   contradicting `φ ∉ M`.

`completeness_dense` differs from `completeness` in exactly one place: it installs
`DenselyOrdered (ChronicleSubtype M)` (`chronicleDenselyOrderedDense`, from the density axiom being
in the Dense-MCS) so the `validDense` hypothesis can be applied. **The Metric case is the same
skeleton with a different order-property installed.**

**Key structural fact (decisive for the frame class):** the chronicle from a `FrameClass.Metric`
MCS is *automatically uniform*. The four `discrete_*` axioms are theorems in every limit-MCS
(`theoremInMcsFc h_mcs (.axiom [] _ .discrete_propagate_fwd (le_refl _))`, mirroring
`dense_indicator_in_dense_mcs`); by the truth lemma, `U(⊥,⊤)` is satisfied at a chronicle point iff
that point has an immediate successor, and the propagate/symm axioms force "has an immediate
successor" to be **constant across the whole model**. So the chronicle is either everywhere-dense or
everywhere-discrete (immediate succ+pred everywhere) — i.e. a member of `U`, but **not** in general
an oag.

## Literature Proof Structure (the completeness argument, step map for downstream)

Main claim to formalize: **`BX⁺` is sound and complete over `U`** (uniform serial linear orders =
dense ⊔ discrete-uniform), with the dense fragment additionally landing on the oag ℚ.

1. **(Soundness side, already done for oag; extend to `U` if a matched pair is wanted.)** Task 449
   proved the four axioms valid over oag (`MetricSoundness.lean`). On the full class `U` the axioms
   are equally valid (on a dense frame `U(⊥,⊤)` is nowhere-true ⇒ symm/propagate vacuous; on a
   discrete-uniform frame `U(⊥,⊤)`/`S(⊥,⊤)` are everywhere-true ⇒ implications trivial). Re-proving
   soundness over `U` is optional — see §Recommendation for the two packaging options.
2. **Consistency → Metric-MCS.** Mirror `neg_consistent_of_not_derivable_dense` + `temporal_lindenbaum_fc`
   at `FrameClass.Metric`.
3. **Chronicle countermodel is uniform.** New lemma(s), mirroring `dense_indicator_in_all_limit_points`:
   propagate `U(⊥,⊤)`-membership (or its negation) to all limit points using `discrete_propagate_fwd/bwd`
   + `discrete_symm_fwd/bwd`, giving a global dichotomy: either the chronicle is `DenselyOrdered`
   (reuse `chronicleDenselyOrderedDense`'s C4 argument, since ¬`U(⊥,⊤)` everywhere ⇒ dense) or it is
   discrete-uniform (every point has an immediate successor and predecessor, via the truth lemma).
4. **Completeness over `U`.** With the dichotomy, apply the `U`-validity hypothesis to the chronicle
   (which is in `U`); conclude `φ ∈ M`, contradiction. This is the honest `BX⁺` completeness theorem.
5. **Dense fragment → ℚ (oag bridge for task 450).** In the dense branch, `ChronicleSubtype M` is
   `Countable + DenselyOrdered + NoMin + NoMax + Nonempty`, so
   `Order.iso_of_countable_dense (ChronicleSubtype M) ℚ` gives `e : ChronicleSubtype M ≃o ℚ`. Define
   the pulled-back model `Mℚ := fun q => model (e.symm q)` on ℚ, and the transport lemma (§4) gives
   `Satisfies model t φ ↔ Satisfies Mℚ (e t) φ`. This refutes `φ` on **ℚ**, a genuine oag — i.e. the
   dense fragment of `BX⁺` is complete over the oag ℚ.

## §4. The one new general lemma: satisfaction transport along an order isomorphism

Needs to be built (does not exist). Statement:

```lean
theorem Satisfies_orderIso {D E : Type*} [LinearOrder D] [LinearOrder E]
    (e : D ≃o E) (M : TemporalModel D Atom) (t : D) (φ : Formula Atom) :
    Satisfies M t φ ↔ Satisfies (fun q => M (e.symm q)) (e t) φ
```

Proof by induction on `φ`. Atoms: `M (e.symm (e t)) = M t` by `e.symm_apply_apply`. Boolean cases:
congruence. The `untl`/`snce` (and derived `allFuture`/`allPast`) cases: the existential/universal
over points transports because `e` is an order-iso — `e` and `e.symm` are strictly monotone
bijections, so `t < s ↔ e t < e s`, and the "empty open interval `(t,s)`" quantifier is preserved
bijectively (`c ∈ (t,s) ↔ e c ∈ (e t, e s)`). This is standard; the only care is matching CSLib's
exact `Satisfies` unfolding for `untl`/`snce` (guard/event Pnueli form). Estimate: ~60–120 lines.
Advisory: prove the `untl`/`snce` step with explicit witness transport (`e c` / `e.symm c`), not
`simp`/`aesop`, because the interval-emptiness quantifier needs the monotone-bijection bridge
explicitly.

## Why the literal oag goal is a genuine obstruction (do NOT paper over)

`Th(smaller class) ⊇ Th(larger class)`, and `oag ⊊ U`, so `BX⁺ = Th(U) ⊆ Th(oag)` (this is exactly
the task-449 soundness direction, already proven). Completeness over oag would require the reverse,
`Th(oag) ⊆ BX⁺`, i.e. every `BX⁺`-consistent formula has an oag countermodel. In the discrete
sub-case:

- The countermodel order-type is `ℤ ×ₗ A`, `A` = the ℤ-block index (`t ~ s` iff finite distance),
  an arbitrary countable linear order.
- `ℤ ×ₗ A` is an oag order **iff** `A` is the order-type of a countable ordered abelian group. This
  forces `A` (hence `ℤ ×ₗ A`) to be **homogeneous** (an oag's translations act transitively). A
  non-homogeneous index such as `A = 2` (two blocks, `ℤ + ℤ`) yields a valid `BX⁺` frame that is
  **not** an oag.
- No truth-preserving repair exists in Mathlib: an order-**embedding** `ℤ ×ₗ A ↪ ℤ ×ₗ ℚ` destroys
  `U(⊥,⊤)` (it fills the empty successor-interval), so the dense-case Cantor trick has no discrete
  analogue.
- Whether *every* discrete `BX⁺`-consistent formula nonetheless admits *some* homogeneous
  (`ℤ ×ₗ ℚ` / `ℤ`) oag countermodel is precisely the open coincidence `Th(oag) =? BX⁺` in the
  discrete direction. The expected answer is **`Th(oag) ⊋ BX⁺`** (the tense logic of the special
  homogeneous oag class is strictly stronger than the logic of all uniform orders — `BX⁺` lacks any
  discreteness-induction axiom that would pin the block index down), which would make the literal
  task goal **false as stated**. Confirming or refuting this is a research-level result with no
  Mathlib support.

**Note on `Burgess1984` §6.1**: Burgess's *metric* tense logic uses explicit metric operators
indexed by group elements ("in exactly `g` units…"), and its oag-completeness is a result about
*that* language. CSLib's `BX⁺` is the non-metric Since/Until approximation (base + 4 uniformity
axioms) introduced as the conservativity-matching base — the literature's oag-completeness does
**not** transfer to it. This is independent grounding that `BX⁺ = Th(oag)` should not be assumed.

## Recommendation (zero-debt, orchestrator-autonomous)

Adopt the honest, achievable target and escalate the open piece. Concretely, for the plan/implement
phases:

1. **PRIMARY (implement, sorry-free): `BX⁺` completeness over the uniform class `U`.** State
   `U`-validity as validity over serial linear orders satisfying the four uniformity axioms
   semantically at every point (this is the standard "frames validating the axioms" class and avoids
   inventing a bespoke `Densely ∨ Discrete` predicate). Build steps 2–4 above by mirroring
   `DenseCompleteness.lean`. New file `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean`.
2. **BRIDGE (implement, sorry-free): dense fragment → ℚ.** Build §4's `Satisfies_orderIso` transport
   lemma (general, reusable) and the ℚ-refutation corollary (step 5). This is the concrete artifact
   that unlocks task 450's semantic route and is the strongest oag statement available without the
   open discrete lemma.
3. **ESCALATE (do NOT implement): literal oag-completeness of the discrete case.** Record in the
   module docstring and the task that full `BX⁺`-over-oag completeness reduces to the open lemma
   "every discrete `BX⁺`-consistent formula has a homogeneous (`ℤ`/`ℤ ×ₗ ℚ`) oag countermodel",
   expected false, requiring a discreteness-induction axiom not present in `BX⁺`. If the user
   specifically needs oag-completeness, the sound resolution is to **strengthen `BX⁺` with a
   discreteness/archimedean axiom** (a new `FrameClass` ≥ Metric) — a separate task — not to force
   the current system.

### Packaging note (soundness/completeness matching)

Task 449's soundness is over oag; the achievable completeness is over `U ⊇ oag`. Two clean options:
- **(a) Keep soundness at oag, add completeness at `U`.** The pair reads "`BX⁺ ⊆ Th(oag)` and
  `Th(U) ⊆ BX⁺`", with `oag ⊆ U` and the `Th(oag) = Th(U)` coincidence flagged open. Least work.
- **(b) Add a soundness-over-`U` theorem** (easy; axioms valid on all of `U` by the vacuous/trivial
  case split above) so `BX⁺ = Th(U)` is a exact sound-and-complete pair. Recommended for a
  self-contained result. Retain the oag soundness as the `oag ⊆ U` corollary.

## Zero-debt / lint-prevention notes

- No `sorry`, no vacuous defs, no new axioms anywhere in the PRIMARY + BRIDGE deliverables.
- New declarations (`Satisfies_orderIso`, `MetricCompleteness` lemmas, uniformity-propagation lemmas,
  the `validMetric`/`U`-validity def) need house-style docstrings (docBlame); `Prop`-valued results
  use `theorem`/`lemma` (defLemma); validity def lowerCamelCase (defsWithUnderscore); no new `@[simp]`
  (simpNF); keep `Atom`/`D`/`E` section vars minimal, `_`-prefix unused (unusedSectionVars);
  `@[nolint dupNamespace]` on any `Temporal.`-prefixed def inside `namespace …Temporal` (mirror
  `BXPlusDerivable`).
- Wiring: new `MetricCompleteness.lean` `public import`s `MetricSoundness` + `DenseCompleteness` (for
  the reusable chronicle/dichotomy lemmas); add to the `Metalogic.lean` barrel; `lake exe mk_all
  --module`; `lake exe checkInitImports`; full CI order per `cslib.md`.

## Tactic Survey (advisory)

- `Satisfies_orderIso`: term/`induction φ`; the `untl`/`snce` step uses `e.lt_iff_lt`,
  `e.symm_apply_apply`, explicit witness maps — **not** `simp`/`aesop` (interval-emptiness needs the
  monotone-bijection bridge shown).
- Uniformity dichotomy: mirror `chronicleDenselyOrderedDense`'s `limit_satisfies_c4` argument for the
  dense branch; `theoremInMcsFc` + `chronicle_truth_lemma` for the discrete branch.
- Cantor step: `obtain ⟨e⟩ := Order.iso_of_countable_dense (ChronicleSubtype M) ℚ` (instances all
  auto-synthesized/verified).

## Source anchors (durable)

- Chronicle countermodel + instances: `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean:52–137`.
- Truth lemma: `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` (`chronicle_truth_lemma`).
- Dense completeness template: `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean:48–271`.
- Base completeness skeleton: `Cslib/Logics/Temporal/Metalogic/Completeness.lean:90–127`.
- BX⁺ definition + oag soundness: `Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean` (whole file).
- Validity hierarchy incl. `validDiscrete`: `Cslib/Logics/Temporal/Semantics/Validity.lean:76–120`.
- Root-cause literature: `Burgess1984` §6.1 (metric = oag time; but metric-operator language),
  `Xu1988` Thm 2.9 (successor not U,S-definable), archived task-445 round-2 report (homogeneity of
  oag = the whole content of the dense/discrete split).

## Adversarial Self-Verification (H4)

- **"Is the dense→ℚ bridge really airtight?"** Yes on the Mathlib side (Cantor + ℚ instances +
  subtype countability all verified exit-0). The only unbuilt piece is the standard
  `Satisfies_orderIso` transport lemma (§4), whose only non-trivial case (interval-preservation for
  `untl`/`snce`) follows from `e` being a strictly-monotone bijection. Low risk.
- **"Is the discrete obstruction real, or am I under-searching for a Mathlib embedding?"** Real: a
  truth-preserving map must be an order-iso onto its image (Since/Until is not preserved by
  sub-order embeddings — it reads the empty-successor-interval), and there is provably no order-iso
  from a non-homogeneous `ℤ + ℤ` onto any homogeneous oag. So no Mathlib order-embedding lemma can
  bridge it; the obstruction is structural, not a search gap.
- **"Could `BX⁺` secretly force density (collapsing to the clean ℚ case)?"** No: `ℤ ⊨ BX⁺` and
  `ℤ ⊨ U(⊥,⊤)`, so `U(⊥,⊤)` is `BX⁺`-consistent — the discrete case genuinely occurs and cannot be
  avoided.
- **"Does stating completeness over `U` (not oag) contradict the task?"** It refines it: the task
  explicitly says "Confirm exactly which frame class BX⁺ is genuinely complete over before
  committing" and "escalate with the exact goal" if an open lemma is needed. `U` is that class; the
  oag gap is the escalated goal. This is compliant, not a deviation.
- **"Is `validDiscrete` a shortcut I'm missing?"** No — `IsSuccArchimedean` in `validDiscrete` forces
  a single ℤ-block (≅ ℤ, an oag), so `validDiscrete` is *stronger* than the multi-block class the
  chronicle produces; using it as the completeness class would demand an archimedean axiom `BX⁺`
  lacks. It is a red herring for completeness (though relevant to a future strengthened logic).

## Revised Direction

None required — the verdict (dense clean, discrete obstruction; implement over `U` + dense→ℚ bridge,
escalate literal oag) is stable under adversarial review and grounded in verified Mathlib facts plus
the archived conservativity analysis. This is a valid zero-debt research outcome: the honest,
achievable completeness theorem is identified and fully scoped, and the one piece that would need an
open/likely-false lemma is escalated with its exact statement rather than deferred with `sorry`.
