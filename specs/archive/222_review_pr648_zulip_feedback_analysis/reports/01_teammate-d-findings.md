# Teammate D Findings: Strategic Horizons

**Task**: Task 222 — Review PR #648 and Zulip feedback, strategic analysis
**Researcher**: Teammate D (Horizons)
**Date**: 2026-06-16

---

## Executive Summary

PR #648 (primitive bot for `Proposition`) is the correct foundational move, but it is entering
a community that has two parallel architectural visions: benbrastmckie's Hilbert/Kripke-first
approach (classical, aiming at modal/temporal/bimodal completeness) and thomaskwaring's
algebraic/typeclass-first approach (GHA, aiming at maximal generality). These visions are not
fully compatible, and the PR sequence in the next 6–12 months will crystallize one of them as
the CSLib norm. This document identifies the strategic inflection points and provides a
prioritized action plan.

---

## 1. PR Sequencing: Optimal Landing Order

### Assessment of Open PRs

| PR | Author | Status | Compatibility with #648 |
|----|--------|--------|------------------------|
| #536 | thomaskwaring | Mergeable, ctchou approved | COMPATIBLE — refactors IsClassical/IsIntuitionistic, no conflict with primitive bot |
| #648 | benbrastmckie | CHANGES_REQUESTED | — |
| #587 | thomaskwaring | DRAFT | INCOMPATIBLE — uses 4-constructor Proposition without bot, uses `.impl` not `.imp` |
| #607 | fmontesi | CHANGES_REQUESTED, dirty | PARTIALLY INCOMPATIBLE — uses HasImpl/HasNot where #648 uses HasImp; path collision on Connectives.lean |

### Recommended Landing Sequence

**Phase 1 (prerequisite)**: Merge #536 → then rebase #648
- #536 is already approved and mergeable. ctchou explicitly says #648 should wait for it.
- Both PRs touch `IsClassical`/`IsIntuitionistic` in `Defs.lean` and `NaturalDeduction/Basic.lean`.
- Rebasing is straightforward — #536 adds inference-system refactors, #648 adds semantics/Hilbert. No logical conflict.

**Phase 2**: Land #648 after rebase
- The primitive-bot change is foundational. Landing it before #587 and #607 is the right order.
- Once #648 is merged, #587 and #607 authors must adapt to the five-primitive `Proposition`.

**Phase 3 (post-#648)**: Coordinate with #587 and #607
- #587 needs `Valuation.interp` to handle `bot` case and rename `.impl` → `.imp`.
- #607 needs `HasImpl` vs `HasImp` naming to be resolved — see Section 3.

**Risk**: If #607 merges before #648, the `Connectives.lean` path collision becomes a merge conflict rather than a coordination problem. This is manageable but undesirable.

**Recommendation**: Accelerate #648 through review. Do not wait for #587 or #607.

---

## 2. Design Convergence: Can GHA, Connectives Typeclasses, and Primitive Bot Coexist?

### Three Parallel Visions

**Vision A — benbrastmckie**: Fixed `{atom, bot, imp, and, or}` inductive type, Prop-valued
semantics, Kripke models, Hilbert systems, canonical model completeness. The five primitives
are justified by uniformity with modal/temporal Kripke satisfaction.

**Vision B — thomaskwaring**: Generalized Heyting Algebra (GHA) semantics, polymorphic
`Evaluate` over any `GeneralizedHeytingAlgebra`, typeclasses for connectives (`HasInterp`,
`HasImpl`). Yields the single elegant completeness theorem:
```lean
theorem Theory.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A
```

**Vision C — Matthew Doty**: Bool-valued evaluation, CNF, DPLL, SAT-solver verification.
Decision procedures require computable semantics. Doty is agnostic on the Prop vs Bool debate
at the semantic layer, but has practical needs.

### Compatibility Analysis

**Bot as primitive** (PR #648): Compatible with all three visions.
- GHA interpretation: `⊥` maps to the GHA bottom element — exactly what thomaskwaring's GHA
  `Evaluate` does (`.bot => ⊥`).
- Bool interpretation: `.bot => false` — exactly what #648's `BoolEvaluate` does.
- Kripke interpretation: `IForces` handles `bot` via `botForces` predicate — supported.

**Prop vs Bool debate**: Converging toward coexistence.
- thomaskwaring (in Zulip): GHA unifies both — `Bool` is a `BooleanAlgebra` (a `GeneralizedHeytingAlgebra`), `Prop` is a `HeytingAlgebra`. Both are instances.
- The `BoolEvaluate_eq_iff` bridge in #648 is consistent with this: it will become an instance
  of the GHA theorem specialized to `H = Bool`.
- **The strategic insight**: #648's two-evaluator design is a temporary pragmatic solution that
  naturally dissolves into the GHA framework once #587's approach matures.

**HeytingAlgebra vs GeneralizedHeytingAlgebra**:
- matthewdoty correctly notes that HeytingAlgebra is too strong for minimal logic completeness.
- thomaskwaring confirms GHA (= Heyting algebra without the bottom axiom `⊥ ≤ a`) is the
  correct structure.
- This technical point matters for benbrastmckie's `MinPropAxiom` completeness — the canonical
  model for minimal logic needs the GHA treatment, not just HeytingAlgebra.

**Conclusion**: The three visions ARE technically compatible at the level of `Proposition`.
The primitive-bot design of #648 is the right shared foundation. The disagreement is about
what layers to build on top of that foundation, not about the foundation itself.

---

## 3. Matthew Doty's SAT Direction: Strategic Fit

### What Doty Is Building
- Short-term: `Atom -> Bool` evaluation, CNF, Tseitin transform, DPLL decision procedure
- Medium-term: DPLL soundness/completeness, possibly port MiniSAT
- Long-term interest: Probability logic, Fagin et al. axiomatization

### How This Fits with benbrastmckie's Work

**Synergy point**: `BoolEvaluate_eq_iff` (the bridge lemma in #648) is the exact interface
between benbrastmckie's `Prop`-valued completeness machinery and Doty's `Bool`-valued
decision procedures.

Specifically, DPLL soundness would use:
```lean
-- DPLL finds model v : Atom → Bool satisfying φ
-- BoolEvaluate_eq_iff lets us lift to: Evaluate (fun a => v a = true) φ
-- prop_strong_soundness lets us conclude: SetDerivable PropositionalAxiom ∅ φ fails (or succeeds)
```

This is a clean connection. The MCS machinery in benbrastmckie's `StrongCompleteness.lean` can
also support Doty's probability logic goal: "Γ ⊢ ϕ ⇔ ∀ Pr. ∑{1 − Pr(γ) | γ ∈ Γ} ≥ 1 − Pr(ϕ)"
is a probability-theoretic restatement of Lindenbaum completeness.

**Risk**: If `Evaluate` is dropped (Doty's suggested `canonicalValuation` via `decide`) and only
`BoolEvaluate` remains, the `FromPropositional` embeddings (PL → Modal, PL → Temporal) become
harder. The modal `Satisfies` relation is inherently `Prop`-valued. benbrastmckie's response to
Doty in Zulip correctly identifies this risk.

**Recommendation**: Keep both evaluators (as planned in the file merge). Explicitly frame
`BoolEvaluate` as the interface to Doty's SAT work in the PR description and Zulip response.
Invite Doty to stack a PR on #648 once it merges.

---

## 4. Next Steps After #648: Follow-Up PR Queue

Prioritized list of follow-up PRs needed for benbrastmckie's program:

### Tier 1: Blocked on #648 Merge (immediate queue)

| PR Name | Scope | Dependency |
|---------|-------|------------|
| `feat(Propositional): MinPropAxiom Hilbert system + MinStrongCompleteness` | MinSoundness, MinLindenbaum, MinStrongCompleteness | #648 merged |
| `feat(Propositional): IntPropAxiom Hilbert system + IntStrongCompleteness` | IntSoundness, IntLindenbaum, IntStrongCompleteness | #648 merged |
| `feat(Propositional): PropositionalAxiom Hilbert system + StrongCompleteness` | Soundness, Lindenbaum, StrongCompleteness | #648 merged |
| `feat(Propositional): ND/Hilbert equivalence (hilbert_iff_nd)` | NaturalDeduction/Equivalence.lean | #648 + Hilbert PRs |
| `feat(Propositional): Kripke semantics + IForces persistence` | Semantics/Kripke.lean | #648 merged |
| `feat(Propositional): Intuitionistic/Minimal completeness via IForces` | Metalogic/IntCompleteness.lean | Kripke PR |

### Tier 2: Enable Modal/Temporal Hilbert (strategic)

| PR Name | Scope | Dependency |
|---------|-------|------------|
| `feat(Modal): primitive-bot formula type consensus` | Discussion/Zulip first | Tier 1 complete |
| `feat(Modal): Hilbert system + K/S4/S5 completeness` | Modal Metalogic | PL Hilbert PRs merged |
| `feat(Temporal): Hilbert system + completeness` | Temporal Metalogic | Modal PRs merged |
| `feat(Bimodal): Discrete completeness` | Bimodal/Metalogic/Discrete | task 36 (current sorry) |

### Tier 3: Cross-cutting (long-term)

| PR Name | Scope | Dependency |
|---------|-------|------------|
| `feat(Foundations): GHA-based polymorphic Evaluate` | Unifies Prop/Bool via typeclass | Coordination with #587 author |
| `feat(Propositional): DPLL decision procedure` | SAT/CNF layer | #648 + Doty collaboration |
| `feat(Propositional): Probability logic primitives` | Doty's long-term goal | Hilbert completeness |

**Order discipline**: Each Tier 1 PR should be scoped to ONE completeness theorem. Do not
combine Min, Int, and Classical completeness in a single PR. The Zulip thread confirms
thomaskwaring wants PRs to be small and incremental.

---

## 5. Community Dynamics: Navigating the thomaskwaring Relationship

### The Asymmetry

thomaskwaring is a maintainer/reviewer with parallel work on the same territory. This creates
three tensions:
1. **Parallel development**: His GHA approach and benbrastmckie's Kripke approach have
   overlapping scope but different design philosophies.
2. **Authority differential**: thomaskwaring can approve or block PRs. His "I'd be excited
   to review" comment is encouraging but his earlier caution ("the design of something this
   general would require a fair amount of discussion") suggests gate-keeping instincts.
3. **Draft PR #587**: His draft sits on overlapping territory. If it advances, it may establish
   precedents that constrain benbrastmckie's approach.

### What thomaskwaring Actually Wants (reading between the lines)

- Small, incremental PRs with discussable design decisions.
- Convergence toward algebraic generality (GHA) rather than fixed specialized types.
- Credit for his approach — he hints at parallel work ("I had been sketching something similar").
- Collaboration, not competition.

### Strategic Recommendations for Navigation

**Do**: Acknowledge overlap with #587 explicitly in PR responses and Zulip. Propose concrete
compatibility paths. The GHA approach and the Kripke approach are not mutually exclusive —
they can coexist with bridging theorems.

**Do**: In Zulip threads, attribute the GHA insight to thomaskwaring when citing it. "As
thomaskwaring notes, once #587 matures, `BoolEvaluate` becomes an instance of the GHA
framework specialized to Bool."

**Do NOT**: Try to merge PRs that conflict with #587's design without prior Zulip coordination.
Even if technically mergeable, a PR that forces thomaskwaring to rewrite #587 will generate
friction.

**Do NOT**: Treat the naming disagreement (`HasImp` vs `HasImpl`) as trivial. It signals
broader design authority over the Foundations layer. Adopting `HasImpl` in PR #648 costs
nothing and signals collaborative intent.

**Key opportunity**: Propose a joint Zulip thread on the Foundations/Logic/Connectives.lean
design. Frame it as "let's align before both PRs proceed" rather than "one of us must change."
This preempts the most likely blocker for post-#648 PRs.

---

## 6. Risk Assessment

### Risk 1: Connectives.lean Path Collision (HIGH PROBABILITY, HIGH IMPACT)

Both #648 and #587 create `Cslib/Foundations/Logic/Connectives.lean` with different content.
If either merges without coordination, the other author faces a complete file rewrite.

**Mitigation**: Tag thomaskwaring on PR #648 explicitly noting the path collision. Propose
either: (a) #648 takes the authoritative Connectives.lean and #587 adapts, or (b) start a
joint design thread.

### Risk 2: HasImp vs HasImpl Naming War (MEDIUM PROBABILITY, MEDIUM IMPACT)

PR #607 uses `HasImpl`, PR #648 uses `HasImp`. ctchou's review of #607 may establish a naming
norm before #648 fully coordinates.

**Mitigation**: Proactively adopt `HasImpl` in #648's Connectives.lean. This is a one-line
rename that removes a future blocker.

### Risk 3: Modal Formula Type Incompatibility (LOW PROBABILITY NOW, HIGH IMPACT LATER)

Upstream `Modal/Basic.lean` uses `{atom, not, and, diamond}` as primitives. benbrastmckie's
fork uses `{atom, bot, imp, box}`. These are architecturally incompatible — the Hilbert axioms
(K axiom, Necessitation) require `box` as a primitive.

**Mitigation**: Before submitting any Modal PR upstream, open a Zulip thread titled
"Proposal: switch Modal.Proposition primitives to {atom, bot, imp, box}". Cite benbrastmckie's
Hilbert system development as motivation. Get fmontesi and ctchou buy-in explicitly.

### Risk 4: thomaskwaring's GHA PR Racing Ahead (MEDIUM PROBABILITY, MEDIUM IMPACT)

If #587 advances from DRAFT to open before #648 lands, it may establish the GHA framework as
the CSLib norm for PL semantics, making `Evaluate`/`BoolEvaluate` look like legacy code.

**Mitigation**: Accelerate #648 through the remaining CHANGES_REQUESTED items. Every week of
delay increases the risk that the algebraic approach claims territory first.

### Risk 5: ctchou Re-requests Changes on "Both Evaluators" Decision (MEDIUM PROBABILITY)

ctchou's original comment may have meant "use Bool.lean only" (drop Evaluate), not "merge
files." If the PR response doesn't address this explicitly, a third review cycle is likely.

**Mitigation**: The PR response must include a clear paragraph explaining why `Evaluate`
(Prop-valued) cannot be dropped — specifically the FromPropositional embedding chain and
Kripke uniformity argument. This is the single most important sentence to get right.

---

## 7. Prioritized Action Items

### Immediate (before next push to #648)

1. **RENAME** `HasImp` → `HasImpl` in `Connectives.lean`. One-line change, signals alignment.
2. **DRAFT PR RESPONSE** paragraph explicitly addressing the "ctchou may have meant drop
   Evaluate" ambiguity with the Kripke-uniformity argument.
3. **RESOLVE** `references.bib` merge conflict (pre-existing `<<<<<<< Updated upstream`
   markers), then add `Avigad2023` entry.

### Before Pushing to PR

4. **REBASE** on #536 after it merges (can do today since it's mergeable).
5. **VERIFY** `lake exe lint-style` passes on merged `Semantics/Basic.lean` (no CI surprises).
6. **TAG** thomaskwaring on PR #648 with a comment explaining the Connectives.lean path
   collision and proposing coordination.
7. **TAG** fmontesi on PR #648 flagging the `HasImp` → `HasImpl` naming change direction.

### Post-#648 Merge (immediate next phase)

8. **OPEN ZULIP THREAD** proposing joint design for `Connectives.lean` with thomaskwaring
   before PRing `MinPropAxiom` completeness.
9. **SUBMIT** `feat(Propositional): MinPropAxiom Hilbert + MinStrongCompleteness` (smallest
   first, builds trust with reviewers).
10. **INVITE** Matthew Doty to stack a DPLL PR on the merged #648 branch.

### Strategic (next 3–6 months)

11. **OPEN ZULIP THREAD** on `{atom, bot, imp, box}` vs `{atom, not, and, diamond}` for
    `Modal.Proposition` before writing any Modal upstream PR.
12. **COORDINATE** with thomaskwaring on GHA unification — propose a joint PR that provides
    the polymorphic `Evaluate` as a theorem consequence of both the Kripke and algebraic
    approaches.

---

## 8. Priority Ranking

| Priority | Item | Rationale |
|----------|------|-----------|
| P0 | Address ctchou's "both evaluators" ambiguity in PR response | Prevents third review cycle |
| P0 | Rebase on #536 after merge | Required by reviewer; blocks #648 |
| P1 | Rename HasImp → HasImpl | Removes naming war risk, costs nothing |
| P1 | Resolve references.bib merge conflict + add Avigad2023 | Required by reviewer comment |
| P1 | Tag thomaskwaring about Connectives.lean collision | Prevents silent conflict accumulation |
| P2 | Submit MinPropAxiom Hilbert PR after #648 merges | First step in Tier 1 queue |
| P2 | Open Zulip thread on Connectives.lean joint design | Sets collaborative tone |
| P3 | Open Zulip thread on Modal.Proposition primitive type | Avoids future architectural impasse |
| P3 | Coordinate with Doty on DPLL PR stacking | Community building, practical synergy |
