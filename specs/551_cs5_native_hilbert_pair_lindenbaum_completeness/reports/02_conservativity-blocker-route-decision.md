# Research Report: The Phase-4 Conservativity Blocker — Root Cause and Route Decision

- **Task**: 551 — cs5_native_hilbert_pair_lindenbaum_completeness (cslib)
- **Date**: 2026-07-24
- **Session**: sess_1784905751_756cda_551
- **Feeds**: plan revision (`/revise 551`)
- **Verdict**: **Route 4 — declare the blocker research-level/open and re-scope the task.** The
  Phase-4 conservativity obligation is not a mechanical continuation of Phases 1–3; it is a
  constructive **disjunction-property-under-constraint** (cut-elimination-grade) result that has
  now defeated three distinct native attempts and has a structural reason it cannot be discharged
  inside the Hilbert `prime_exclusion` engine. The bounded path to the *sound* theorem is Route A
  (`CS5 ≡ IS5` collapse), which the native mandate forbids — so the decision requires the user.

---

## 1. What the blocker actually is (root cause)

Phase 4 must invoke `prime_exclusion`/`prime_set_exclusion`
(`Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`) at the combined theory `CS5PairAxiom`
over `Atom ⊕ Atom`, excluding `E := {τ_L(□A), τ_R A}` from the seed
`S₀ := τ_L''H ∪ τ_R''(cl(boxInv H))`. That engine has two classes of precondition:

1. **Schema hypotheses** (`hOrE`, `hOrI1`, `hOrI2`, `hEFQ`) quantified over the **entire**
   `Proposition (Atom ⊕ Atom)` type — including genuinely *mixed* formulas such as
   `(atom (inl p)).or (atom (inr q))`. Phase 3's `CS5PairAxiom` (only `left`/`right`/`cross1`/
   `cross2`) does not supply these at mixed formulas. This is the "~9-constructor, mechanical"
   part the handoff flags — real, but genuinely mechanical (add a full propositional core
   quantified over the whole type, keep the modal schemata pure-tagged). **Not the blocker.**

2. **The seed-exclusion precondition** `DerivExcludes D E S₀` (`PrimeExclusion.lean:332`): no
   `bigOr` of a sublist of `E` is in `cl_{CS5PairAxiom}(S₀)`. Concretely three facts —
   `τ_L(□A) ∉ cl(S₀)`, `τ_R A ∉ cl(S₀)`, and the disjunction `τ_L(□A) ⊔ τ_R A ∉ cl(S₀)`. This is
   the **load-bearing blocker**, and it is exactly the "context-relative conservativity" the plan
   named R2 and deferred to Phase 5.

The engine cannot be side-stepped: **every** Lindenbaum/Zorn prime construction in the library
(`prime_exclusion`, `prime_set_exclusion`) is gated on this seed-exclusion. There is no
prime-witness without it.

## 2. Why it is irreducibly hard (the decisive structural reason)

The two individual exclusions are controllable. `τ_R A ∉ cl(S₀)` reduces to two facts that both
follow from the hypothesis `□A ∉ H`:
- `A ∉ cl_{CS5}(boxInv H)` — because for a normal modal logic with deductively-closed `H`,
  `boxInv H ⊢ A` implies `□A ∈ H` (K-distribution over the boxed context), contradicting `□A ∉ H`;
- `A` is not a `CS5` theorem — else `□A` is a theorem, so `□A ∈ H`, same contradiction.
Cross-axiom routes (`cross2 : □(τ_R B) → τ_L B`, `cross1 : □(τ_L B) → τ_R B`) only fire on boxed
antecedents, and `□` is introduced solely by necessitation from `[]`, so they add nothing here.

The **disjunction** exclusion `τ_L(□A) ⊔ τ_R A ∉ cl(S₀)` is the wall. At the *seed*, the theory
is **not prime**, so "neither disjunct is derivable" does **not** give "the disjunction is not
derivable" (constructively the disjunction is strictly weaker). We need the *negative*
`S₀ ⊬ τ_L(□A) ∨ τ_R A` directly — i.e. the **disjunction property of the combined system under
the boxInv cross-constraint**. This is precisely Pacheco 2024's Lemma 16, whose published proof
is *unsound* here (it uses the negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, invalid for a
poset-maximal quasi-prime theory — report 01 §5, and confirmed in the probe corpus).

**No semantic shortcut exists** (this refutes the "just build a countermodel" instinct, i.e.
Route 2 via the landed soundness lemma):

> The landed `cs5PairAxiom_sound` (probe / `CS5Completeness.lean`) requires the doubled valuation
> to tag **both** copies with a **common** underlying `val` (`hval2L`/`hval2R` both `= val`) — the
> cross-axioms are only sound under that identification. Under a common `val`, `τ_L X` and `τ_R X`
> are the *same* semantic fact, so `cross1 : □(τ_L B) → τ_R B` collapses to `□B → B` (axiom `T`).
> Every model the soundness lemma certifies therefore **identifies the two copies**, and in any
> such model, whenever `A ∈ H` (the generic and interesting box-backward case: `H` forces `A` but
> not `□A`), the excluded `τ_R A` is *forced*. Hence **no sound model separates `S₀` from `E`** —
> the exclusion is a purely *syntactic* fact about the Hilbert calculus, with zero semantic
> witnesses.

So the obstruction is a **cut-elimination-grade proof-theoretic separation result**, stated inside
a Hilbert axiom system where such results are maximally awkward (Hilbert systems have no
subformula property / cut-free normal form to induct on). That is the single root cause behind all
three native failures below.

## 3. Adversarial confirmation from the codebase — this exact wall was already hit and discarded

The current atom-sum `CS5PairAxiom` construction is **a re-run of a previously-discarded
approach**. `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`'s module docstring
(lines 14–33) records, verbatim:

> "It replaces an earlier doubled-atom `CS5Combined` atom-sum scaffold that attempted to close
> `CS5`'s box-backward truth-lemma case via a simultaneous-pair construction over `Atom ⊕ Atom`;
> that approach **re-entered Pacheco's unsound negation-completeness move**
> (`cs5Combined_seed_excludes`, **never closed** — see git history for the removed content) and
> **was discarded**."

`cs5Combined_seed_excludes` is the *same* `DerivExcludes S₀` obligation Phase 4 is now blocked on.
The three distinct native attempts and their fates:

| Attempt | Route | Outcome | Evidence |
|---|---|---|---|
| One-set canonical relations | box/dia one-sided, ≤-mediated | **mechanically refuted** | `cs5Incest_cs5CanonMreach_false`, `cs5Incest_cs5PrimeMreach_false`, `cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm` |
| Atom-sum `CS5Combined` (task 512) | pair-as-single-theory | **discarded**, seed-exclusion never closed | CS5Canonical docstring; `cs5Combined_seed_excludes` |
| Atom-sum `CS5PairAxiom` (task 551, current) | pair-as-single-theory, cross-conds internalised | **[BLOCKED]** at same seed-exclusion (as "R2 conservativity") | handoff `blockers[]`; plan Phase 4 |

The `cl`-stability win of the current attempt (cross-conditions internalised as axioms, so
`crossCond_left/right_stable` hold "for free") is **real and correct** — it genuinely fixes the
*primeness-engine applicability* gap that report 01 §6 diagnosed. But it moves the hard content
one step upstream, from "pair primeness under an external `Cons`" to "combined-theory seed
exclusion," which is the *same* disjunction-under-constraint fact. The relocation does not
dissolve it — §2 shows it cannot, because the fact has no semantic witness under the very
soundness lemma the encoding relies on.

The birelational one-sided route (`cs5_box_backward_onesided`, `SegmentLindenbaum.box_refuting_theory`)
*did* close box-backward negation-completeness-free — but then failed at a **different** wall: its
incestuality frame condition is **mechanically false** on every canonical world type
(`cs5Incest_cs5CanonMreach_false`, `cs5Incest_cs5PrimeMreach_false`; a universally-reachable
exploding world `Ω` defeats the monotone `boxInv` inclusion). So that route is not a rescue either.

## 4. Evaluating the four options

**Route 1 — prove the context-relative conservativity directly.** *Rejected as a plan phase.*
- Exact statement needed: for the two-sided seed `S₀ = τ_L''H ∪ τ_R''(cl(boxInv H))` with
  `□A ∉ H`, `CS5PairAxiom ⊬ from S₀` of `bigOr l` for every `l ⊆ {τ_L(□A), τ_R A}` — in
  particular `S₀ ⊬ τ_L(□A) ∨ τ_R A`.
- Induction it needs: an induction on `CS5PairAxiom` derivation trees tracking a "side + boxed-ness"
  invariant, establishing the combined system's **disjunction property relative to the cross
  constraint**. Individual-formula exclusion (§2) is tractable; the disjunction-level negative from
  a non-prime seed is not.
- Why it hits the same wall as task 512: it *is* `cs5Combined_seed_excludes`, which was never
  closed and caused the whole atom-sum approach to be discarded. It has no semantic witness (§2),
  and the only known *correct* technique for a constructive-modal disjunction property is a
  **cut-free labelled/nested sequent** argument — which in this library means transporting from
  `NIKTheorem TS5` (the labelled system), i.e. collapsing into **Route C** (an explicit non-goal:
  it retains the labelled engine, yielding a labelled method, not a Hilbert method). A *direct*
  Hilbert-calculus proof is research-grade and, on the evidence, multi-day-to-open.

**Route 2 — restructure the pair-Lindenbaum argument to avoid conservativity at Phase 4.**
*Rejected: no such restructure exists.* Seed-exclusion is intrinsic to both `prime_exclusion` and
`prime_set_exclusion`; any prime witness needs it. And §2 shows the specific exclusion is
irreducibly syntactic (no model separates `S₀` from `E`), so no choice of seed/exclusion
bookkeeping within the atom-sum frame removes it. The implementer's own search for a
`T`/`tBox`-driven direct characterization of `DerivExcludes S₀` did not find one; the structural
argument in §2 explains why none is available.

**Route 3 — fall back to Route A (`CS5 ≡ IS5` collapse via `is5_completeness`).** *Sound and
bounded, but forbidden by the task's mandate; not a legitimate "hybrid."*
- Readiness (verified in-repo): `is5_completeness : IValidFC is5FC φ → Derivable IS5ModalAxiom φ`
  is **landed** (`IS5.lean:364`). The two collapse axioms `k3` (`cs5_dia_or`, `CS5.lean:539`) and
  `k5` (`cs5_dia_bot_imp_bot`, `CS5.lean:712`) are **landed**, and CS5.lean's own docstring says
  they "corroborate the `CS5 ≡ IS5` collapse."
- Residual Route-A work (report 01 §10): prove `CS5 ⊢ idb`/`k4` (the `□`/`◇` interaction giving
  `is5Derivable ⟺ cs5Derivable`) plus a `CKValid cs5FC ⟺ IValid is5FC` validity-coincidence bridge.
  Report 01 calls this "sound and mostly done." **Caveat / residual risk to check before committing:
  `CS5 ⊢ idb` provability is asserted by report 01 §10 but was not re-verified in this dispatch** —
  it is the one Route-A premise a revision must confirm first (it is a bounded, self-contained
  Hilbert derivation, unlike the open disjunction property).
- Why it is not a "hybrid Route A for the truth lemma, native for the rest": the truth lemma **is**
  the native content. Obtaining box-backward by IS5 transport *is* Route A; there is no coherent
  split that keeps the fallible-world segment truth lemma while importing its hard case from IS5.
  Route A re-bases the semantics onto IS5's birelational frame class — exactly what the native
  mandate (report 01, "Approach constraint"; plan Non-Goals) forbids. Choosing it is a genuine
  **mandate change**, which only the user can authorize.

**Route 4 — declare the blocker research-level/open and re-scope.** *Recommended.* The native
box-backward completeness for constructive CS5 is blocked at a single, precisely-located,
research-grade proof-theoretic lemma (the constructive disjunction property of the combined system
under the boxInv cross-constraint) that (a) has no semantic witness, (b) has resisted three
distinct native mechanization attempts, and (c) inside a Hilbert calculus admits no known correct
technique short of a cut-free/labelled detour (= Route C, a non-goal). This is not a Phase-4
continuation; it is its own research problem.

## 5. Recommendation (decisive) and concrete re-scope for the plan revision

**Chosen route: 4.** Revise the plan / task as follows:

1. **Mark the native box-backward completeness `[BLOCKED — research-level]`.** State the single open
   lemma precisely (the §4 Route-1 statement: the combined-system disjunction property from the
   two-sided seed, equivalently `cs5Combined_seed_excludes`). Record that Phases 1–3 remain landed
   sorry-free and are unaffected; keep them.
2. **Escalate the mandate decision to the user**, because the only bounded path to the *sound* CS5
   completeness theorem is Route A, which the native mandate forbids. Present two options:
   - **(Recommended for a shippable theorem) Re-scope to Route A**: spawn/redirect to prove
     `CS5 ⊢ idb`/`k4` + the `CKValid ⟺ IValid` bridge and inherit `is5_completeness`. Bounded,
     mostly-landed; delivers `Derivable CS5ModalAxiom` completeness, at the cost of the
     method-uniformity mandate. **First action of that route: verify `CS5 ⊢ idb` is derivable**
     (the one unconfirmed premise).
   - **(To preserve the mandate) Keep native, as a research task**: scope a dedicated sub-task to
     the constructive disjunction-property lemma, with a literature/proof-search pass targeting a
     **cut-free** route (nested/labelled sequents for constructive S5, Marin–Morales–Straßburger
     2021; Pacheco 2024 Lemma 16/17 as the *defective* version to repair) rather than a direct
     Hilbert argument. Explicitly accept this is open-ended.
3. **Do not** add the ~9-constructor `CS5PairAxiom` propositional-core extension as "progress":
   it is mechanical but only exposes the load-bearing seed-exclusion sooner; landing it without a
   path to the disjunction property produces an axiom system whose only purpose is a lemma that
   cannot yet be proved.

## 6. Adversarial self-verification against the recorded failure modes

- **Negation-completeness bug** (`ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`): the Route-4 recommendation asserts no
  construction, so it cannot reintroduce the bug; and it correctly identifies that *any* Route-1
  attempt must avoid it — that is precisely why `cs5Combined_seed_excludes` was never closed and
  the approach was discarded. Consistent, not in tension.
- **Circularity**: verified the semantic route is circular and *sharpened why* (§2: cross-axiom
  soundness forces a common valuation → the two copies collapse → no separating model). The Route-4
  claim makes no circular inference. Route A's validity bridge is a soundness/soundness coincidence
  drawing on the independently-landed `is5_completeness`, not on CS5 completeness — not circular.
- **Schema-incompatibility** (`ρ = Sum.elim id id` sends `cross1`'s `□B → B` outside
  `CS5ModalAxiom`): used correctly in the §2 derivability analysis (cross-routes need boxed
  antecedents introduced only by necessitation). The recommendation does not rely on any retraction
  being schema-compatible. The one place I *rely on* an unverified positive claim is `CS5 ⊢ idb`
  for Route A — explicitly flagged in §4 and §5 as the premise to check first, not assumed.

## References (all verified in-repo this session)

- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` — `prime_exclusion` (:226),
  `prime_set_exclusion` (:562), `DerivExcludes` (:332), the `hOrE`/`hCut`/`cl_*` precondition set.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — module docstring (`CS5Combined`
  discard, `cs5Combined_seed_excludes` "never closed"); `cs5Incest_cs5CanonMreach_false` (:448),
  `cs5Incest_cs5PrimeMreach_false`, `cs5_box_backward_onesided` (scaffolded).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — `cs5_dia_or` (`k3`, :539),
  `cs5_dia_bot_imp_bot` (`k5`, :712), `cs5_axiom_sound''` (:447), box-backward-gap docstring.
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5.lean` — `is5_completeness` (:364).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` — landed `CS5PairAxiom`,
  `cs5PairAxiom_left/right_derivable`, `crossCond_left/right_stable`.
- `specs/551_.../probes/cs5-pair-combined-atomsum.lean` — `cs5PairAxiom_sound` (common-valuation
  soundness, the lemma §2 shows cannot witness seed-exclusion).
- `specs/551_.../reports/01_route-b-native-hilbert-cs5-research.md` — original route selection,
  Pacheco Lemma 16 unsoundness (§5), R1/R2 risk register (§9), non-goals (§10).
- [Pacheco 2024, *Collapsing Constructive and Intuitionistic Modal Logics*] — pair technique;
  Lemma 16 (defective disjunction-under-constraint step). Literature FTS index returned no
  Pacheco entry this session (degraded); Lemma 16/17 content is cited via report 01 and the probe
  corpus notes, not re-fetched.
