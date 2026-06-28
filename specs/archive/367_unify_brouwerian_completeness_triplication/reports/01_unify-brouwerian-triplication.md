# Research Report: Unify the Three Brouwerian Completeness Developments (Task 367)

- Task: 367 — Collapse `BrouwerianCompleteness.lean`, `PointedBrouwerianCompleteness.lean`,
  and `MplPointedConservative.lean` into one parametric development (~1000-line net reduction).
- Session: sess_1782560707_b3ce16_367
- Worktree: `/home/benjamin/Projects/cslib/.claude/worktrees/orchestrate-345-348-367` (branch `orchestrate-345-348-367`)
- Status: researched

## Executive Summary

The three modules are ~80% identical. The shared surface is a **Brouwerian Lindenbaum
quotient** built from exactly five derivability facts (K, S, andI, andE1, andE2), plus a
truth lemma and a completeness/iff skeleton. They differ in only two places:

1. **The bot interpretation in the evaluator** — `⊤` (Brouwerian), `⊥` (pointed), or a free
   `bot_val` (free-bot). All three are *definitional specializations* of the single evaluator
   `BrouwerianBotEvaluate v bot_val` that already exists inside `MplPointedConservative.lean`.
2. **One extra instance** — the pointed tier adds `OrderBot` via the `efq` axiom (the only
   place `efq` is used at all). The other two tiers add nothing.

**Key reuse finding (decisive):** The generic Hilbert Lindenbaum machinery in
`HilbertLindenbaum.lean` is *already* parametric over an arbitrary axiom predicate `Axioms`,
and every meet-fragment lemma there (`hilbertLindenbaumLe_refl/trans/antisymm`,
`inf_le_left/right`, `le_inf`, `le_top`, `le_himp_iff`, `mk_eq_top_iff`, the `Inf`/`Himp`
operations and their congruences, `canonicalV`, `canonicalBotVal`) uses **only the five
conj-imp fields** of `MinimalAxioms` — never the three `or` fields. The three target modules
re-derive, by hand, lemmas that already exist generically; they only re-derive them because
the fragment axiom families do **not** satisfy the 8-field `MinimalAxioms` typeclass (they
have no `or` axioms).

The minimal change that captures the variance is therefore: introduce a **5-field
conj-imp typeclass**, generalize the existing meet-fragment lemmas onto it, add one
`BrouwerianSemilattice` instance, and recover the three tiers as corollaries that fix
`bot_val` (and, for the pointed tier, add `OrderBot`). No new axioms; the `bot`
interpretation is the single varying parameter, exactly as the task specifies.

## Files In Scope

| File | Lines | Tier | Bot semantics | Axiom family |
|------|-------|------|---------------|--------------|
| `Algebra/BrouwerianCompleteness.lean` | 528 | Brouwerian (IPL⟨∧,→,⊤⟩) | `bot ↦ ⊤` | `ConjImpAxiom` (5 ctors) |
| `Algebra/PointedBrouwerianCompleteness.lean` | 561 | pointed (IPL⟨∧,→,⊥,⊤⟩) | `bot ↦ ⊥` (OrderBot) | `ConjImpBotAxiom` (6 ctors: +efq) |
| `Algebra/MplPointedConservative.lean` | 658 | free-bot (MPL⟨∧,→,⊥,⊤⟩) | `bot ↦ bot_val` (free) | `ConjImpBotMinAxiom` (5 ctors) |

Total: **1,747 lines** across the three. Substrate (NOT in scope, but consumed):
`Semantics/Algebra.lean` (`AlgEvaluate`/`AlgTValid`), `Algebra/Brouwerian.lean`
(`BrouwerianEvaluate`/`BrouwerianValid`), `Algebra/PointedBrouwerian.lean`
(`PointedBrouwerianEvaluate`/`PointedBrouwerianValid`), `Algebra/HilbertLindenbaum.lean`
(generic Lindenbaum + `MinimalAxioms`), `ProofSystem/FragmentAxioms.lean` (the three
axiom inductives), `Foundations/Order/BrouwerianSemilattice.lean`.

## Exact Shared vs Differing Surface

### Identical across all three (the ~80% copy-paste)

Each module contains, character-identical modulo the `Axioms`/evaluator name substitution:

- **Equivalence relation + setoid**: `*Equiv` (= `Deriv Ax [A] B ∧ Deriv Ax [B] A`),
  `*Equiv_refl/symm/trans`, `*PropositionSetoid`. → *Already generic* as `HilbertEquiv`,
  `hilbertEquiv_refl/symm/trans`, `hilbertPropositionSetoid` in `HilbertLindenbaum.lean`.
- **Quotient type + map**: `*LindenbaumAlgebra`, `*LindenbaumMk`. → *Already generic* as
  `HilbertLindenbaumAlgebra`, `hilbertLindenbaumMk`.
- **Order**: `*LindenbaumLe`, `*LindenbaumLe_mk`. → *Already generic*.
- **Congruences**: `*EquivAndCongr`, `*EquivImpCongr`. → *Already generic* as
  `hilbertEquivAndCongr`, `hilbertEquivImpCongr` (use only h_K,h_S,h_andI,h_andE1,h_andE2).
- **Operations**: `*LindenbaumInf`, `*LindenbaumHimp` + `_mk` simp lemmas. → *Already generic*.
- **Order lemmas**: `_refl`, `_trans`, `_antisymm`, `inf_le_left`, `inf_le_right`, `le_inf`,
  `le_top`, `le_himp_iff`. → *Already generic* (`hilbertLindenbaumLe_*`), all using only the
  five conj-imp fields.
- **`BrouwerianSemilattice` instance**: identical 12-field record in all three.
- **API simp lemmas**: `_mk_le_mk`, `_mk_inf`, `_mk_himp`, `_Top`.
- **Top characterization**: `*LindenbaumMk_eq_top_iff`. → matches generic
  `hilbertLindenbaumMk_eq_top_iff`.
- **Canonical valuation**: `*CanonicalV = fun x => mk (.atom x)`. → matches generic
  `canonicalV`.
- **Truth lemma**: `*CanonicalV_spec` by induction on the formula (atom/imp/and trivial; or
  excluded by the fragment predicate; bot is the one varying case).
- **Completeness + iff skeleton**: instantiate validity at the Lindenbaum algebra, rewrite
  with the truth lemma, finish with `mk_eq_top_iff`.
- **Soundness**: `*_axiom_sound` (case split on the axiom; the 5 conj-imp cases are
  character-identical), `*_soundness` (induction on the derivation tree — identical),
  `*_soundness_derivable`.

### The actual differences (the ~20%)

| Aspect | Brouwerian | Pointed | Free-bot |
|--------|-----------|---------|----------|
| Evaluator | `BrouwerianEvaluate v` (`bot↦⊤`) | `PointedBrouwerianEvaluate v` (`bot↦⊥`) | `BrouwerianBotEvaluate v bot_val` |
| Algebra class | `[BrouwerianSemilattice H]` | `[BSL H] [OrderBot H]` | `[BSL H]` |
| Validity | `BrouwerianValid` (bot fixed ⊤) | `PointedBrouwerianValid` (bot fixed ⊥) | `BrouwerianBotValid` (∀ bot_val) |
| Fragment guard | `IsOrBotFree` | `IsOrFree` | `IsOrFree` |
| Axiom set | `ConjImpAxiom` | `ConjImpBotAxiom` | `ConjImpBotMinAxiom` |
| Extra structure | none | `OrderBot` via `efq` (`bot_le`) | none |
| Soundness extra case | — | `efq` case (`⊥ ⇨ φ = ⊤` via `bot_le`) | — |

Critical observation: the three evaluators have **identical bodies** except the `bot` arm.
`BrouwerianBotEvaluate v bot_val` (already defined at `MplPointedConservative.lean:97`) is the
universal one:

```
BrouwerianEvaluate v φ        = BrouwerianBotEvaluate v ⊤ φ      -- identical bodies, bot_val := ⊤
PointedBrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊥ φ      -- identical bodies, bot_val := ⊥
```

Both hold by `induction φ <;> simp [...]` (every constructor arm matches definitionally; the
`or` arm is `⊤` on both sides). These two one-line bridge lemmas are the entire mechanism for
recovering the `BrouwerianValid` and `PointedBrouwerianValid` tiers from a single free-bot
development.

### Why `efq` is not part of the shared interface

`efq` (`⊥ → φ`) appears in `ConjImpBotAxiom` only and is used in exactly **one** place:
`pointedBrouwerianLindenbaumBot_le` (PointedBrouwerianCompleteness.lean:418-426), which
proves `bot_le` for the `OrderBot` instance. Every order lemma, congruence, and the truth
lemma is `efq`-free. Hence `efq` belongs to a tier-specific corollary, not the parametric core.

## Minimal Parametric Signature

### New typeclass (the only varying proof-theoretic input)

```lean
/-- The five conj-imp axiom witnesses that generate a Brouwerian (meet-)semilattice
Lindenbaum quotient. This is the meet-fragment core of `MinimalAxioms` (which adds the
three `or` witnesses). -/
class ConjImpAxioms {Atom : Type*} (Axioms : PL.Proposition Atom → Prop) : Prop where
  h_K    : ∀ (φ ψ   : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ))
  h_S    : ∀ (φ ψ χ : PL.Proposition Atom), Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  h_andI : ∀ (φ ψ   : PL.Proposition Atom), Axioms (φ.imp (ψ.imp (φ.and ψ)))
  h_andE1: ∀ (φ ψ   : PL.Proposition Atom), Axioms ((φ.and ψ).imp φ)
  h_andE2: ∀ (φ ψ   : PL.Proposition Atom), Axioms ((φ.and ψ).imp ψ)
```

Reuse-first refinement (recommended): make the existing 8-field class **extend** the new
core so there is one source of truth and zero duplication:

```lean
class MinimalAxioms (Axioms) extends ConjImpAxioms Axioms where
  h_orI1 : ...
  h_orI2 : ...
  h_orE  : ...
```

This keeps every existing `MinimalAxioms` instance and `[MinimalAxioms _]` signature working
unchanged (the projections `h_K … h_andE2` are inherited), and means each fragment family
needs only the 3 instances below.

Instances (each `:= ⟨fun .. => .implyK .., …⟩`, mechanical):

```lean
instance : ConjImpAxioms (@ConjImpAxiom Atom)
instance : ConjImpAxioms (@ConjImpBotAxiom Atom)
instance : ConjImpAxioms (@ConjImpBotMinAxiom Atom)
```

(The witnesses already exist: `ConjImp*Axiom.mem_implyK`, `mem_implyS`, and the `.andI/.andE1/.andE2`
constructors used throughout the three files.)

### Generic Brouwerian Lindenbaum (one development)

Approach A (**recommended, maximal reuse**): *generalize the bound* on the meet-fragment
lemmas in `HilbertLindenbaum.lean` from `[MinimalAxioms Axioms]` to `[ConjImpAxioms Axioms]`.
These lemmas already use only `inst.h_K/h_S/h_andI/h_andE1/h_andE2`, so the change is purely
the typeclass parameter (verified by inspection — see "API for Lindenbaum order lemmas"
below). The `sup`-related lemmas (`hilbertLindenbaumSup*`, `hilbertEquivOrCongr`,
`hilbertLindenbaumMk_sup`) and the `GeneralizedHeytingAlgebra` instance keep `[MinimalAxioms]`.
Then add a single `BrouwerianSemilattice` instance valid for `[ConjImpAxioms Axioms]`:

```lean
instance hilbertLindenbaumBSL {Axioms} [ConjImpAxioms Axioms] :
    BrouwerianSemilattice (HilbertLindenbaumAlgebra Axioms) where
  le := hilbertLindenbaumLe ; top := hilbertLindenbaumMk (bot.imp bot)
  inf := hilbertLindenbaumInf ; himp := hilbertLindenbaumHimp
  le_refl := … ; le_trans := … ; le_antisymm := … ; inf_le_left := … ; inf_le_right := …
  le_inf := … ; le_top := … ; le_himp_iff := …
```

Coexistence caveat: `HilbertLindenbaumAlgebra Axioms` would then carry *both* a `BSL` instance
(for `[ConjImpAxioms]`) and a `GeneralizedHeytingAlgebra` instance (for `[MinimalAxioms]`).
A GHA already provides a `BrouwerianSemilattice` via its meet/himp structure, so for an
`Axioms` with `MinimalAxioms` there are two paths to `BrouwerianSemilattice`. **This must be
checked for instance-diamond/defeq conflicts** (see Risks). If diamonds bite, fall back to
Approach B.

Approach B (**fallback, self-contained**): create one new module
`Algebra/BrouwerianLindenbaum.lean` that re-derives the meet-only Lindenbaum once over
`[ConjImpAxioms Axioms]` (≈ a single copy of the ~250-line order-lemma block, parametrized),
producing the `BSL` instance. The three completeness modules then become thin corollary files.
This is guaranteed conflict-free but saves ~250 fewer lines than Approach A.

### Generic soundness, truth lemma, completeness (over `BrouwerianBotEvaluate`)

Keep `BrouwerianBotEvaluate`/`BrouwerianBotValid` as the single substrate evaluator (move
them into `Algebra/Brouwerian.lean` or a new `Algebra/BrouwerianBot.lean` so the unified
completeness module and downstream `MplConservativeChain.lean` can see them — see Migration).
Then prove once:

```lean
-- generic soundness (the 5 shared cases; no efq)
theorem brouwerianBot_axiom_sound {Axioms} [ConjImpAxioms Axioms] {φ}
    (h : Axioms φ) (… mapping each ctor …) : BrouwerianBotValid φ
-- in practice: a case split keyed off ConjImpAxioms is awkward since `Axioms φ` is opaque;
-- simpler: prove generic soundness FROM `BrouwerianBotValid` of each of the 5 schemas as
-- lemmas, then each tier's `*_axiom_sound` does `cases h_ax` and dispatches (incl. efq).

-- generic truth lemma (IsOrFree), using the generalized canonicalV/canonicalBotVal:
theorem brouwerianBotCanonicalV_spec {Axioms} [ConjImpAxioms Axioms] (A) (hA : A.IsOrFree) :
    BrouwerianBotEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) A
      = hilbertLindenbaumMk A
-- generic completeness (IsOrFree):
theorem brouwerianBot_complete {Axioms} [ConjImpAxioms Axioms] {φ} (hfrag : φ.IsOrFree)
    (h : ∀ H [BrouwerianSemilattice H] (v) (b : H), BrouwerianBotEvaluate v b φ = ⊤) :
    Derivable Axioms φ
```

Note the soundness direction does **not** unify as cleanly as the Lindenbaum/completeness
direction, because `cases h_ax` needs the concrete inductive (to enumerate constructors and to
reach the `efq` case for the pointed tier). The recommended shape: prove the five schema-level
soundness facts once as standalone lemmas over `[ConjImpAxioms]` / `BrouwerianBotEvaluate`
(`implyK_sound`, `implyS_sound`, `andI_sound`, `andE1_sound`, `andE2_sound`), then each tier's
`*_axiom_sound` is a 5- or 6-line `cases` that calls them (pointed adds the one `efq` line).
This still removes the bulk (the `implyS` proof is ~12 lines and is the main duplication).

## Recovering Each Tier (names preserved)

Downstream consumers (verified by grep over `Cslib/`, excluding the three files) reference
**only** these names from the three modules:

- `conjImp_brouwerian_complete`, `conjImp_brouwerian_iff`, `conjImp_brouwerian_soundness_derivable`
  (used by `ConjImpConservative.lean`, `ConservativeChain.lean`, `ImpConservative.lean`)
- `conjImpBot_pointedBrouwerian_complete` (used by `ConjImpBotConservative.lean`)
- `conjImpBotMin_brouwerianBot_complete`, `BrouwerianBotEvaluate`, `BrouwerianBotValid`,
  `brouwerianBotEmbeddingLemma` (used by `MplConservativeChain.lean`)

All Lindenbaum internals (`brouwerianLindenbaumMk`, `*LindenbaumAlgebra`, `*CanonicalV`,
`*Mk_eq_top_iff`, the order lemmas, the setoid, congruences) are **private to the three files**
(grep confirmed zero external references). They may be deleted/replaced freely. The task asks
to preserve *every* theorem as corollary or alias; the safe reading is: re-expose the full
public surface of each file (all `theorem`/`def` names listed in Appendix A) as corollaries or
`alias`/`abbrev`, but only the ~8 above are load-bearing for the build.

### Brouwerian tier (`ConjImpAxiom`, `bot_val = ⊤`)

```lean
theorem conjImp_brouwerian_soundness_derivable {φ} (h : Derivable ConjImpAxiom φ) :
    BrouwerianValid φ := by
  -- BrouwerianEvaluate v = BrouwerianBotEvaluate v ⊤ (bridge), then generic soundness at ⊤
theorem conjImp_brouwerian_complete {φ} (hfrag : φ.IsOrBotFree) (h : BrouwerianValid φ) :
    Derivable ConjImpAxiom φ := by
  -- IsOrBotFree ⇒ bot absent ⇒ BrouwerianEvaluate v φ = BrouwerianBotEvaluate v b φ for any b;
  -- feed generic brouwerianBot_complete (note IsOrBotFree → IsOrFree).
theorem conjImp_brouwerian_iff {φ} (hfrag : φ.IsOrBotFree) :
    Derivable ConjImpAxiom φ ↔ BrouwerianValid φ := ⟨…soundness, …complete hfrag⟩
```

The Brouwerian tier keeps its stricter `IsOrBotFree` guard (because `BrouwerianValid` fixes
`bot ↦ ⊤`, so the truth lemma must avoid the `bot` case). Need a helper
`IsOrBotFree φ → IsOrFree φ` (or the bot-absent agreement `BrouwerianEvaluate v φ =
BrouwerianBotEvaluate v b φ`). Check `Algebra/FragmentPredicates.lean` for the former; if
absent it is a 3-line lemma.

### Pointed tier (`ConjImpBotAxiom`, `bot_val = ⊥`, `+OrderBot`)

```lean
-- OrderBot via efq is the ONLY tier-specific structural lemma:
instance : OrderBot (HilbertLindenbaumAlgebra ConjImpBotAxiom) where
  bot := hilbertLindenbaumMk .bot
  bot_le := …  -- exactly pointedBrouwerianLindenbaumBot_le, using ConjImpBotAxiom.efq
theorem conjImpBot_pointedBrouwerian_complete {φ} (hfrag : φ.IsOrFree)
    (h : PointedBrouwerianValid φ) : Derivable ConjImpBotAxiom φ := by
  -- PointedBrouwerianEvaluate v = BrouwerianBotEvaluate v ⊥ (bridge);
  -- at the Lindenbaum algebra ⊥ = [⊥] = canonicalBotVal; apply generic completeness.
```

### Free-bot tier (`ConjImpBotMinAxiom`, free `bot_val`)

Direct specialization of the generic development; `BrouwerianBotValid`,
`BrouwerianBotEvaluate`, `conjImpBotMin_brouwerianBot_*`, `iicBrouwerianBotEvaluateEqAlgEvaluate`,
`brouwerianBotEmbeddingLemma` are preserved (the last two move with the evaluator to substrate).

## API for the Lindenbaum-Quotient Order Lemmas (already in CSLib)

All the order lemmas the three files re-derive **already exist generically** in
`Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean`, parametric over
`Axioms` and currently bounded by `[MinimalAxioms Axioms]` but using only the 5 conj-imp
fields:

| Per-tier (private) lemma | Generic equivalent (HilbertLindenbaum.lean) | Fields used |
|--------------------------|---------------------------------------------|-------------|
| `*Equiv`, `*Equiv_refl/symm/trans`, `*PropositionSetoid` | `HilbertEquiv`, `hilbertEquiv_*`, `hilbertPropositionSetoid` | h_K,h_S |
| `*LindenbaumAlgebra`, `*LindenbaumMk` | `HilbertLindenbaumAlgebra`, `hilbertLindenbaumMk` | — |
| `*LindenbaumLe`, `*LindenbaumLe_mk`, `*Mk_le_mk` | `hilbertLindenbaumLe`, `..Le_mk`, `..Mk_le_mk` | h_K,h_S |
| `*EquivAndCongr`, `*EquivImpCongr` | `hilbertEquivAndCongr`, `hilbertEquivImpCongr` | 5 conj-imp |
| `*LindenbaumInf/Himp` + `_mk` | `hilbertLindenbaumInf/Himp` + `_mk`, `Mk_inf/himp` | — |
| `*Le_refl/trans/antisymm` | `hilbertLindenbaumLe_refl/trans/antisymm` | h_K,h_S |
| `*Inf_le_left/right`, `*Le_inf` | `hilbertLindenbaumInf_le_left/right`, `..Le_inf` | h_andE1/E2/I |
| `*Le_top` | `hilbertLindenbaumLe_top` | h_K,h_S |
| `*Le_himp_iff` | `hilbertLindenbaumLe_himp_iff` | 5 conj-imp |
| `*Mk_eq_top_iff` | `hilbertLindenbaumMk_eq_top_iff` | h_K,h_S |
| `*CanonicalV` | `canonicalV` | — |
| (free-bot) `bot_val = [⊥]` | `canonicalBotVal` | — |

Mathlib building blocks used by the underlying proofs (unchanged, no new dependency):
`Quotient.mk/sound/exact/liftOn₂/lift₂/exists_rep`; the `BrouwerianSemilattice` field set
(`le_himp_iff`, `himp_eq_top_iff`, `himp_inf_le`, `inf_le_left/right`, `le_inf`, `bot_le`,
`top_le_iff`) from `Cslib/Foundations/Order/BrouwerianSemilattice.lean`; for the free-bot
embedding `LowerSet.Iic`, `LowerSet.Iic_inf`, `LowerSet.Iic_top`, `LowerSet.Iic_injective`,
`iicHimp` (from `FreeJoinCompletion.lean`). The Hilbert derived-rule helpers
(`hilbertCutSingletonDeriv`, `hilbertCutListDeriv`, `hilbertImpIDeriv`, `hilbertImpEDeriv`,
`hilbertAndI/E1/E2Deriv`, `hilbertWeakenSingleton`, `assumption_deriv`, `weakening_deriv`) are
already shared and take the axiom witnesses as arguments.

## Recommended Module Layout

1. `NaturalDeduction/Equivalence.lean` — add `class ConjImpAxioms`; refactor
   `MinimalAxioms extends ConjImpAxioms` (keeps all existing instances/uses).
2. `ProofSystem/FragmentAxioms.lean` — add three `instance : ConjImpAxioms (…Axiom)`.
3. `Algebra/HilbertLindenbaum.lean` — weaken bound on the meet-fragment lemmas to
   `[ConjImpAxioms]` (Approach A); add `hilbertLindenbaumBSL` instance.
4. `Algebra/Brouwerian.lean` (or new `Algebra/BrouwerianBot.lean`) — host `BrouwerianBotEvaluate`,
   `BrouwerianBotValid`, simp lemmas, `iicBrouwerianBotEvaluateEqAlgEvaluate`,
   `brouwerianBotEmbeddingLemma`, and the two bridge lemmas
   (`BrouwerianEvaluate = BrouwerianBotEvaluate · ⊤`,
   `PointedBrouwerianEvaluate = BrouwerianBotEvaluate · ⊥`).
5. One unified completeness module (reuse `MplPointedConservative.lean`'s slot, or a new
   `Algebra/BrouwerianCompletenessGeneric.lean`) — generic soundness/truth/completeness, then
   the three tiers as corollaries with **all preserved names**. The other two original files
   become either deleted (with their public names re-exported from the unified module via the
   same `import` graph) or kept as ~30-line re-export shims. Prefer: keep all three filenames
   as thin shims that `import` the unified core and contain the tier corollaries, so consumer
   `import` paths (`Algebra.BrouwerianCompleteness`, etc.) stay valid. That preserves the
   public import surface with zero consumer edits.

## Net Line Estimate

- Removed: ~3 × ~250 lines of duplicated Lindenbaum/order/congruence/setoid machinery
  (≈ 750 lines), plus ~3 × ~60 lines of duplicated soundness `implyS`/tree-induction blocks
  (≈ 180 lines).
- Added: `ConjImpAxioms` class (~10) + `extends` refactor (~0 net) + 3 instances (~24) +
  one `BSL` instance (~16) + generic soundness/truth/completeness (~120) + 2 bridge lemmas
  (~8) + tier corollary shims (~90).
- **Net: roughly −1,000 lines**, consistent with the task's stated target. Achieved without
  new abstraction beyond the single 5-field typeclass (which is a strict factor of the
  existing `MinimalAxioms`).

## Risks / Open Questions for Planning

1. **Instance diamond (Approach A).** With both `BrouwerianSemilattice` (via `ConjImpAxioms`)
   and `GeneralizedHeytingAlgebra` (via `MinimalAxioms`) available on
   `HilbertLindenbaumAlgebra Axioms` for full-axiom `Axioms`, confirm Lean does not see two
   distinct `BrouwerianSemilattice`/`PartialOrder`/`SemilatticeInf` paths with mismatched
   `le`/`inf`. Mitigation: the GHA's `le`/`inf`/`himp` are the *same* underlying functions
   (`hilbertLindenbaumLe/Inf/Himp`), so the instances should be defeq; still, verify with a
   scoped `lake build` early. If it bites, use Approach B (self-contained generic module — no
   GHA on the fragment algebra type).
2. **`MinimalAxioms extends ConjImpAxioms` ripple.** Changing `MinimalAxioms` from a flat
   class to an `extends` class is source-compatible for *consumers* (projections unchanged) but
   every `instance : MinimalAxioms _ where …` literal still lists 8 fields — Lean accepts this
   for `extends` (it auto-builds the parent). Verify the 3 existing instances
   (`MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom` in `Equivalence.lean`) still elaborate.
   If risky, skip the `extends` refactor and just add a standalone
   `instance [MinimalAxioms A] : ConjImpAxioms A` (zero duplication risk, one extra instance).
3. **`IsOrBotFree → IsOrFree`.** The Brouwerian tier needs this (or the bot-absent evaluator
   agreement). Check `Algebra/FragmentPredicates.lean`; likely already present.
4. **`BrouwerianBotEvaluate` relocation.** Moving it out of `MplPointedConservative.lean`
   changes its declaring module; downstream `MplConservativeChain.lean` imports the file, so as
   long as the new home is in that file's transitive imports, no consumer edit is needed. Add
   to `Cslib.lean` barrel via `lake exe mk_all --module` if a new file is created.
5. **`@[simp]` set.** The per-tier `*Mk_inf/_himp/_le_mk/_bot` simp lemmas are used inside the
   truth-lemma `simp only` calls. The generic `hilbertLindenbaumMk_inf/_himp/_le_mk` are
   already `@[simp]`; ensure the generic truth lemma's `simp only` references the generic names.
6. **Soundness genericity limit.** As noted, `*_axiom_sound` cannot be fully collapsed into one
   theorem because `cases h_ax` requires the concrete inductive. Plan for 5 shared schema-soundness
   lemmas + thin per-tier `cases` wrappers, not a single soundness theorem.

## Zero-Debt / Lint Notes

- No `sorry`, no new axioms; every step is a structural proof or a definitional bridge
  (`induction φ <;> simp`). The whole refactor is provably complete with existing API.
- Lint: new `ConjImpAxioms` class + fields need docstrings (docBlame); the class is `Prop`-valued
  so fields are fine; instances need explicit namespace wrapping (topNamespace); use
  lowerCamelCase for instance names; preserve `@[expose] public section` and `module` headers;
  keep `Cslib.Init` import. Run `lake exe mk_all --module` if any file is added/removed and
  `lake shake` after import changes.
- Notation: these modules use no operational-semantics arrows; the only notation in scope is
  `⊨[bot_val]` (`AlgTValid`) from `Semantics/Algebra.lean`, already scoped.

## Appendix A — Full public-name inventory to preserve (per file)

See `grep` output captured during research; the load-bearing externally-referenced subset is:
`conjImp_brouwerian_complete`, `conjImp_brouwerian_iff`, `conjImp_brouwerian_soundness_derivable`,
`conjImpBot_pointedBrouwerian_complete`, `conjImpBotMin_brouwerianBot_complete`,
`BrouwerianBotEvaluate`, `BrouwerianBotValid`, `brouwerianBotEmbeddingLemma`. All other public
names in the three files (`*_axiom_sound`, `*_soundness`, `*_iff`, the Lindenbaum internals,
`iicBrouwerianBotEvaluateEqAlgEvaluate`) are not referenced externally but should be re-exposed
as corollaries/aliases per the task's "every existing theorem preserved" requirement.
