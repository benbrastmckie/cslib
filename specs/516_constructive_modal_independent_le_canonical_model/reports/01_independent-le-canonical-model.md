# Research Report 01 — Task 516: The Independent-≤ Canonical Model for CS5 (De-Risking Design)

**Task type**: cslib (Lean 4, foundational rebuild de-risking). **Dispatch**: orchestrator,
session `sess_1784104673_dcb72f`, `orchestrator_mode=true`, `--lit` active. **No production Lean
written** (source read + `lean-lsp`-style inspection of landed declarations + Simpson/AMdPR/Marin
corpus chunks only). **Scope**: settle the single question that decides whether the
user-authorized independent-≤ rebuild has a green path, or whether it is refuted at the
representational level — as tasks 508/509/512 each were.

---

## VERDICT (lead) — `next_action_hint = escalate`

**NO-GO on the independent-≤ rebuild _as framed_. The design premise is refuted, and it is
refuted by CSLib's own already-mechanized infrastructure — not by a conjecture.**

The task authorizes decoupling the intuitionistic preorder `≤` from theory-inclusion `⊆` in
order to make `cs5Incest_forces_symm`'s monotonicity hypothesis (`hmono`) **fail**, so the
`(1,1,0,0)` incestuality witness `u′ ≥ u` is no longer pinned to `u′ := u`. **This cannot
work, for a reason that survives any choice of `≤`:**

> In CSLib's constructive segment semantics, forcing of an atom is head-membership
> (`cval s p := p ∈ s.head`, `Segment.lean:177`) and `CKForces` is **persistent under `≤` for
> every formula, on arbitrary frames** (`ckforces_persistence`, `Forcing.lean:122`; the `.box`
> and `.imp` clauses are `≤`-closed by definition, `Forcing.lean:72,75`). Any truth lemma
> `w ⊩ φ ↔ φ ∈ head w` therefore forces **`head` monotone under whatever `≤` is chosen**:
> `φ ∈ head w ⟹ w ⊩ φ ⟹ (w ≤ w') w' ⊩ φ ⟹ φ ∈ head w'`. That is _exactly_
> `cs5Incest_forces_symm`'s hypothesis `hmono : w ≤ w' → head w ⊆ head w'`
> (`CS5Canonical.lean:645`). Making `≤` "independent of `⊆`" does not remove `hmono`; it makes
> `≤` a **sub-relation** of `⊆` (fewer related pairs, but still `w ≤ w' ⟹ head w ⊆ head w'`),
> which leaves the collapse lemma's hypothesis fully intact. `boxInv` stays monotone along `≤`,
> and `cs5Incest r` still forces plain box-symmetry `boxInv (head u) ⊆ head w`.

So "larger-in-`≤` does not mean more-boxed-formulas" — the crux the dispatch asks me to
establish for question 2 — is **false in any membership-based canonical model with heredity**.
It contradicts the persistence theorem. The only way to defeat `hmono` is to abandon
membership-forcing or heredity, which means abandoning the entire `CKForces`/`Segment`
Henkin architecture the rebuild is supposed to reuse (and, per §Q1, no published construction —
Simpson, AMdPR, Marin — does this; their `≤` is `⊆` or a label-order that is _also_
Θ-monotone).

**Second, corroborating, already-mechanized fact.** For `CS5` specifically, Simpson's two-sided
canonical relation is **provably the same relation** as the discarded symmetric box-tail:
`cs5TwoSidedR_iff_cs5Tail` (`CS5Canonical.lean:511`, axiom-free) shows the diamond clause
`Δ ⊆ diaInv Γ` is an `↔` with the reverse box clause `boxInv Δ ⊆ Γ`, via `cs5_boxInv_subset_iff`
(`CS5.lean:589`). Restoring Simpson's diamond clause restores no independent information over
`CS5`'s quasi-prime theories. This already refuted report 06's two-sided-R fix; the independent-`≤`
idea is the next lever, and it is refuted by the persistence argument above.

**What is NOT blocked (why this is `escalate`, not a flat "CS5 is incomplete").** `CS5 ≡ IS5`
(`CS5.lean:93-99`, Pacheco2024 Thm 13) is complete; Simpson _proves_ its completeness over a
canonical model whose **`≤` is literally `⊆`** (Simpson chunk `682e04d443e7bbd7`, verbatim below).
The genuine obstruction is therefore **not** `≤ = ⊆`; it is the **constructive simultaneous-pair
box-backward construction** — `cs5_symmetric_tail_box_gap` (`CS5.lean:712`) — over the _right_
theories. That is orthogonal to `≤`-independence and is exactly task 512's Phase 8-10 unclosed
primeness problem. A rebuild _can_ close CS5 completeness, but via one of two costly routes
(§Q4), neither of which is "make `≤` independent."

**Confidence:** **~85%** that the independent-`≤` rebuild cannot defeat `cs5Incest_forces_symm`
for the stated reason (grounded in mechanized `ckforces_persistence` + the `le`/`cval`
definitions — this is not a literature inference). The residual ~15% is that a rebuild abandoning
membership-forcing for a fully-labelled/saturated model (Marin) could still reach completeness —
but that is a from-scratch reformalization with ~zero CSLib reuse and does **not** vindicate the
independent-`≤` mechanism.

---

## The obstruction, precisely relocated (read this before the per-question answers)

Task 512 did not stop at report 06's "revise to two-sided R." It **built** the two-sided-R fix
and the Ω-excluding world type, and mechanized (sorry-free, axiom-clean) that **both collapse**.
The three landed lemmas the dispatch names are the load-bearing evidence:

| Lemma | Location | Content | Consequence |
|---|---|---|---|
| `cs5TwoSidedR_iff_cs5Tail` | `CS5Canonical.lean:511` | Simpson's diamond clause `Δ ⊆ diaInv Γ` ⟺ reverse box clause `boxInv Δ ⊆ Γ` for quasi-prime `Γ,Δ` (via `cs5_boxInv_subset_iff`, `CS5.lean:589`) | Report 06's "two-sided R restores independent info" is refuted: two-sided R **=** `cs5Tail` over CS5. |
| `cs5Incest_forces_symm` | `CS5Canonical.lean:643` | For any `CKSegment`-lifted world type: `hmono` + forward box clause ⟹ `cs5Incest r → boxInv (head u) ⊆ head w` (plain box-symmetry) | `cs5Incest` carries no more content than plain symmetry once `≤ ⟹ head-⊆`. |
| `cs5_symmetric_tail_box_gap` | `CS5.lean:712` | `□(p∨□q)∈H`, `boxInv H⊆T`, `boxInv T⊆H`, `q∉H` ⟹ `p∈T` (pure disjunction-property argument, no CS5 axiom) | Every symmetric-tail member of `H` contains `p`; box-backward needs a **strictly larger head** `H'⊋H` (∋q) whose tail is built **simultaneously** with `H'`. |

The two horns of the dilemma, both mechanized:

- **Symmetric/two-sided relation `cs5Tail`** (`boxInv H⊆T ∧ boxInv T⊆H`): symmetry is **free**
  (`cs5Tail_symm`, `CS5.lean:645`), Ω is **not** in a non-exploding world's tail — but
  box-backward **fails** (`cs5_symmetric_tail_box_gap`).
- **One-sided relation `cs5OnesidedR`/`cs5PrimeMreach`** (`boxInv H⊆T` only): box-backward would
  be the plain prime lemma — but symmetry/incestuality **fails**
  (`cs5Incest_cs5PrimeMreach_false`, `CS5Canonical.lean:688`, via `cs5Incest_forces_symm` + Ω
  universally reachable).

The independent-`≤` proposal attacks the **one-sided horn**: keep one-sided R (box-backward OK),
and rescue `cs5Incest` by decoupling `≤` so the witness `u′≥u` is not monotonicity-pinned. The
persistence argument (lead) shows this rescue is impossible: `hmono` is structural.

---

## Q1 — What the literature's `≤` actually is (the independent-≤ construction)

**Simpson 1994 §3.3 — `≤` IS theory-inclusion.** The canonical model (corpus
`simpson_1994_intuitionisticmodallogic`, chunk `682e04d443e7bbd7`, verbatim OCR):

```
B = (W, ≤, R, V) where:
    W  = {X | X is prime},
    X ≤ X'  iff  X ⊆ X',
    X R Y   iff  {◇A | A ∈ Y} ⊆ X  and  {B | □B ∈ X} ⊆ Y,
    V(X)   = {a | a ∈ X}
```

There is **no independent `≤`** in Simpson. `X ≤ X' iff X ⊆ X'` is _exactly_ CSLib's
`Preorder (CKSegment)` head-inclusion (`Segment.lean:161-168`, `le P Q := P.head ⊆ Q.head`;
`CKSegment.le_iff`, `:167`). What decouples Simpson's model from CSLib's failure is **not** the
order; it is (i) `W = {X | X prime}` = **consistent** prime theories (no `Ω = univ`), and (ii)
the box-backward/necessity case discharged by the **prime lemma** (Lemma 3.3.2, chunk
`8372f27240fe345d`: "If `X ⊬ Y` then there exists a prime `X' ⊇ X` such that `X' ⊬ Y` … standard
Lindenbaum") and the **Canonical Model Lemma 3.3.3** (chunk `caf3305a53065b87`: "`X ⊩ A` iff
`A ∈ X`, by induction … using the prime lemma in the implication and necessity cases").

**AMdPR 2001 (constructive S4) and Marin 2021 (fully-labelled IK–IS5).** AMdPR worlds are pairs
`(Γ, Δ)` with `Δ` a prime filter (constructive-diamond "negative information"); Marin's worlds
are **labels** in a saturated labelled derivation, with `≤` and `R` as _independent relational
atoms_ read off the sequent — the closest thing to a genuinely "independent `≤`". **But in both,
heredity forces the label/pair theory `Θ` monotone under `≤`.** Marin's calculus has an explicit
monotonicity rule; AMdPR's saturation makes `Γ` grow along `≤`. So even the labelled model
satisfies `w ≤ w' ⟹ Θ(w) ⊆ Θ(w')` = `hmono`. The "independence" of Marin's `≤` is that it is not
_defined_ as `⊆`; it is not that it _violates_ `Θ`-monotonicity. **No published construction has
a `≤` under which a world can be `≤`-larger while its forced-formula set fails to grow** — that
would break persistence and hence soundness.

**Answer to Q1:** the exact independent-`≤` construction the task asks me to specify **does not
exist in the literature**. Simpson's `≤` is `⊆`; Marin's/AMdPR's `≤` is a label/pair order that
is still Θ-monotone. The premise that Simpson "uses an independent `≤` decoupled from `⊆`" is a
misreading — his `≤` is `⊆` verbatim.

## Q2 — Why the collapse lemmas STILL apply (the crux, rigorous)

The dispatch asks me to show `cs5Incest_forces_symm`'s hypothesis fails under independent `≤`.
**It does not fail. Here is the airtight argument, grounded entirely in landed Lean:**

`cs5Incest_forces_symm` (`CS5Canonical.lean:643-650`) has exactly two hypotheses:

1. `hmono : w ≤ w' → head w ⊆ head w'`
2. `hbox  : r w u → boxInv (head w) ⊆ head u`

Both are **forced by the truth lemma + persistence**, for _any_ `Preorder World` and _any_ `head`:

- **`hbox` is the box-forward truth-lemma direction.** `CKForces … w (.box φ)` unfolds to
  `∀ w', w ≤ w' → ∀ u, r w' u → … u φ` (`Forcing.lean:75`). At `w' := w`: `□φ ∈ head w ⟹
  w ⊩ □φ ⟹ r w u → u ⊩ φ ⟹ φ ∈ head u`. Any truth lemma yields `hbox`.
- **`hmono` is persistence composed with the truth lemma.** `ckforces_persistence`
  (`Forcing.lean:122`) proves `w ≤ w' → w ⊩ φ → w' ⊩ φ` for **every** `φ` on **arbitrary**
  frames (no confluence needed — the `.box`/`.imp` clauses are `≤`-closed by construction).
  With `w ⊩ φ ↔ φ ∈ head w`: `φ ∈ head w → φ ∈ head w'`, i.e. `head w ⊆ head w'`. Any truth
  lemma with any `≤` yields `hmono`.

Therefore, for any world type on which the truth lemma is even _attempted_,
`cs5Incest r → (r w u → boxInv (head u) ⊆ head w)` holds. Enlarging `u` to `u′` with `u ≤ u′`
gives `boxInv (head u) ⊆ boxInv (head u′) ⊆ head w` (monotone `boxInv`), so the incestuality
witness collapses to plain box-symmetry — **independent of how `≤` is defined**, because `≤`
being a sub-relation of `⊆` (which persistence forces) is all `hmono` needs.

The concrete Ω-route (`cs5Incest_cs5PrimeMreach_false`, `CS5Canonical.lean:688`) is a _second_,
independent refutation: `Ω = univ` is `≤`-reachable from every `.ofHead` world, and
`boxInv univ = univ ⊄ T` for non-exploding `T`. An independent `≤` does not banish `Ω` either
(the CS4-template `excl` field only excludes from `some`-built tails, `:652-663`).

**Answer to Q2:** the collapse lemmas are **not** artifacts of `≤ = ⊆`; they are structural
consequences of `CKForces` persistence. Independent `≤` leaves both hypotheses intact. This is
the decisive de-risking finding, and it is negative.

## Q3 — Box-backward + symmetry via the prime lemma (what Simpson actually does, and the real gap)

Simpson verifies the S5 frame condition (F2 / confluence of `≤` and `R`) and box-backward
**without negation-completeness**, using only the disjunction property — corpus-verified:

- **F2** (chunk `79177be0efcb6752`, `a593f14501f059da`): given `X R Y`, `Y ⊆ Y'`, build
  `X' = X ∪ {◇A | A ∈ Y'}`, extend to prime via the prime lemma (Lemma 3.3.2), and show
  `X' R Y'` using **primeness + deductive closure + IK's ◇-distribution axiom** — "as `X` is
  prime, `(A ⊃ B) ∈ X` … by the disjunction property". No `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` step.
- **Box-backward** (necessity case of Lemma 3.3.3, chunk `caf3305a53065b87`): discharged "using
  the prime lemma in the … necessity case" over **consistent prime** theories.

**Mapping to CSLib primitives** (`SegmentLindenbaum.lean`):

| Simpson step | CSLib primitive | Gap |
|---|---|---|
| Prime lemma (Lindenbaum) | `quasi_prime_exclusion` (`:73`) | Produces **quasi-prime = possibly `univ`** (`Segment.lean:58-65`), not consistent-prime |
| Box-refuting witness `boxInv X ⊬ A` | `box_refuting_theory` (`:177`) | Available, but yields quasi-prime `T` |
| Diamond-refuting witness | `dia_refuting_theory` (`:203`) | Available (used by CS4/CS5 `diam_witness`) |
| Non-explosion of a head | `quasi_head_realization` (`:251`) | Realizes an underivable `⊥`, i.e. gives one consistent theory — but the **type** still admits `univ` |

The **decisive gap** (`cs5_symmetric_tail_box_gap`, `CS5.lean:712`): over a **symmetric** tail,
`□q ∈ T ⟹ q ∈ boxInv T ⊆ H`, so a `□(p∨□q)∈H, q∉H` head forces `p` into every tail member. The
box-backward witness must move to `H' ⊋ H` (with `q ∈ H'`) and build `H'` and its tail member
`u` as a **simultaneous maximal pair** with cross-conditions `boxInv H' ⊆ u`, `boxInv u ⊆ H'`,
`p ∉ u`. **Task 512 Phase 8-10 attempted exactly this pair Zorn construction** and found the
cross-invariant `boxInv X ⊆ Y` (other component fixed) is **not stable under the deductive-closure
operator** the library's single-formula primeness engine (`Metalogic.prime_maximal_is_prime`)
requires — a genuine, documented finding (`probes/cs5-pair-primeness.lean`), **not** an artifact
of `≤`. Independent `≤` does nothing for this: the pair construction is about theory-primeness,
not about the order.

**Answer to Q3:** Simpson's box-backward + symmetry are negation-completeness-free and map onto
`quasi_prime_exclusion`/`box_refuting_theory`/`dia_refuting_theory` — but the operative missing
ingredient is (i) **consistency** (exclude `univ` at the type level, which Simpson's `W = {X |
X prime}` has and CSLib's `QuasiPrime` lacks) and (ii) a **simultaneous pair-Lindenbaum** whose
primeness is stable. Neither is `≤`-independence.

## Q4 — Impact on shared infra; the only two genuinely-viable routes

`≤ = head-inclusion` is baked into the **shared** `Preorder (CKSegment)` (`Segment.lean:161`),
consumed by CK/CT/CS4/CS5 truth lemmas. Because independent `≤` is refuted (Q2), there is no
reason to touch that instance at all. The real infra question is where to put **consistency +
pair-Lindenbaum**. Two routes, both real, both costly:

- **Route A — Simpson-faithful (consistent prime + simultaneous pair), ≤ stays `⊆`.**
  Add a `ConsistentQuasiPrime` predicate (`QuasiPrime ∧ ⊥ ∉ S`) and a **pair** Lindenbaum in
  `SegmentLindenbaum.lean` delivering the simultaneous maximal `(H', u)`. **Regression surface:**
  isolated if built as a parallel CS5-only world type (`CS5.lean`/`CS5Canonical.lean` +
  `SegmentLindenbaum` additions); CK/CT/CS4 landed completeness untouched (they need fallible
  `univ` worlds — do **not** generalize `QuasiPrime` to require consistency). **Estimate:** the
  pair-primeness core is the same hard problem Phase 8-10 did not close; ~5-7 phases,
  ~600-1000 lines, with the **primeness-stability hard core unresolved** (the escalation point).
- **Route B — fully-labelled saturated model (Marin 2021).** Worlds = labels, `≤`/`R`
  independent relational atoms, box-backward from proof-search saturation (sidesteps
  Lindenbaum-over-theories entirely). **Regression surface:** none (new file), but **~zero CSLib
  reuse** — a from-scratch reformalization of `Proposition`, sequents, saturation, countermodel
  extraction (report 04 Q4). ~1500-2500 lines.

**Recommendation:** if the user funds a rebuild at all, **Route A, parallel/isolated** (not a
generalization of the shared `≤` or `QuasiPrime`). But Route A's success is gated on the
**unclosed** pair-primeness-stability problem, which is the honest reason for `escalate` rather
than `plan`. **Do not** pursue independent-`≤` (refuted) or two-sided-R (refuted,
`cs5TwoSidedR_iff_cs5Tail`).

## Q5 — Reuse ledger

**Survives / reused:**
- `cs5_axiom_sound_incest` / `cs5_soundness_incest` / `cs5_axiom_sound''` — soundness over the
  frame conditions, axiom-free, unchanged (`CS5Canonical.lean:278`, `CS5.lean:126-128`).
- `box_refuting_theory`, `dia_refuting_theory`, `quasi_prime_exclusion`, `quasi_head_realization`
  (`SegmentLindenbaum.lean:73,177,203,251`) — the single-theory Lindenbaum engine.
- `CKForces` + `ckforces_persistence` (`Forcing.lean:67,122`); CK/CS4 truth-lemma templates.
- `cs5Tail_symm`, `cs5_boxInv_subset_iff`, `cs5_dia_or`, `cs5_dia_bot_imp_bot` (`CS5.lean`).
- **The negative lemmas become permanent GUARDRAILS**: `cs5Incest_forces_symm`,
  `cs5TwoSidedR_iff_cs5Tail`, `cs5_symmetric_tail_box_gap`, `cs5Incest_cs5PrimeMreach_false`,
  `cs5Incest_cs5CanonMreach_false` — they certify that one-sided-R, two-sided-R, and
  independent-`≤` are all dead, keeping future dispatches from re-treading them.

**Discarded:** nothing new is landed to discard — the independent-`≤` world type is refuted
_before_ construction. The Phase 6 `CS5PrimeSegment`/`cs5TwoSidedR` scaffold
(`CS5Canonical.lean:487-623`) is retained only as guardrail context.

## Q6 — Honest risk verdict

**Is the independent-`≤` rebuild likely to close CS5 completeness? No (~85% confident it cannot,
for the stated mechanism).** The mechanism — decoupling `≤` from `⊆` to defeat
`cs5Incest_forces_symm`'s `hmono` — is refuted by `ckforces_persistence` + the `cval`/`le`
definitions: `hmono` is structural, not a consequence of `≤ = ⊆`. The premise "larger-in-`≤` does
not mean more-boxed-formulas" contradicts persistence.

**Residual risks / caveats (the ~15%):**
- A rebuild that **abandons membership-forcing** (Marin fully-labelled/saturated) could reach
  completeness — but that is Route B (from-scratch, zero reuse) and does **not** vindicate the
  independent-`≤` idea; its `≤` is still Θ-monotone.
- Route A (consistent-prime + simultaneous pair) is the genuinely Simpson-faithful path and keeps
  `≤ = ⊆`, but its hard core (pair-primeness stability) is **unclosed** (Phase 8-10) — I cannot
  certify it closes sorry-free; it is the same wall re-approached with a consistency restriction
  as the new (untested) ingredient.
- Truth-lemma-elsewhere risk: since `≤` stays `⊆` in every viable route, the diamond and
  propositional cases (`cs5_diam_witness`, persistence) are undisturbed — no new breakage there.

**A reason it (the independent-`≤` route) cannot work, stated plainly:** persistence of
`CKForces` under `≤` for all formulas (`Forcing.lean:122`) plus atom-forcing-as-membership
(`Segment.lean:177`) make `head` monotone under **any** `≤` compatible with the truth lemma;
hence `cs5Incest_forces_symm` (`CS5Canonical.lean:643`) applies verbatim, and `cs5Incest`
collapses to plain box-symmetry regardless of how `≤` is engineered. The obstruction is the
constructive simultaneous-pair box-backward over consistent theories
(`cs5_symmetric_tail_box_gap`), which is orthogonal to `≤`.

---

## Adversarial self-verification

- *"`hmono` is forced"* — grounded in landed Lean, not literature: `ckforces_persistence`
  (`Forcing.lean:122`, all-formulas persistence on arbitrary frames), `.box`/`.imp` `≤`-closed
  clauses (`Forcing.lean:72,75`), `cval = head-membership` (`Segment.lean:177`),
  `le = head-⊆` (`Segment.lean:162`). Composed with any truth lemma ⟹ `head` monotone under any
  `≤`. I re-derived this rather than citing it.
- *"Simpson's `≤` is `⊆`"* — verbatim corpus chunk `682e04d443e7bbd7` ("X ≤ X' iff X ⊆ X'").
  The task's premise that Simpson uses an independent `≤` is a misreading; stated plainly.
- *"Two-sided R doesn't help"* — `cs5TwoSidedR_iff_cs5Tail` (`CS5Canonical.lean:511`), axiom-free,
  confirmed as a real declaration (not a docstring claim).
- *"The real gap is the pair construction, not `≤`"* — `cs5_symmetric_tail_box_gap`
  (`CS5.lean:712`, 4-line disjunction-property proof, verified) + task 512 Phase 8-10 documented
  primeness-stability finding (`probes/cs5-pair-primeness.lean`, referenced in `CS5.lean:79-91`).
- *"`escalate`, not `plan`/`revise`"* — the authorized lever (independent `≤`) is refuted, so
  there is nothing to plan _on that lever_; the only viable routes (A/B) both have unresolved
  hard cores requiring a human funding decision. Not `plan` (no green mechanism), not `revise`
  (the design premise, not the scoping, is what fails).
- *"Not manufactured pessimism"* — I actively steelmanned pair-worlds (AMdPR) and labelled
  models (Marin): both leave `Θ` monotone; the constructive diamond's "negative information"
  addresses the ◇-case, and `CS5 ≡ IS5` makes it redundant anyway (`CS5.lean:93-99`,
  Alechina redundancy). Neither escapes `hmono`.
- **Zero-debt / reuse-first:** no `sorry`/axiom proposed. The verdict is a mechanized structural
  fact, not a placeholder. BibKeys grounded: `Simpson1994`, `AlechinaMendlerdePaivaRitter2001`,
  `MarinMoralesStrassburger2021`, `Pacheco2024` (all in corpus, chunks cited).

## One-line answer

Independent `≤` cannot rescue CS5 completeness: `CKForces` persistence (`Forcing.lean:122`) forces
`head` monotone under any `≤`, so `cs5Incest_forces_symm` (`CS5Canonical.lean:643`) applies
regardless and `cs5Incest` collapses to plain box-symmetry; the genuine obstruction is the
constructive simultaneous-pair box-backward over consistent theories
(`cs5_symmetric_tail_box_gap`, `CS5.lean:712`), which is orthogonal to `≤` — `escalate`.
