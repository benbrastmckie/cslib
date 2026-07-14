# Task 415 — Audit: Structure-First Propositional Base Lifting into Modal/Temporal/Bimodal

**Task type**: cslib (infrastructure verification + design analysis)
**Status**: research / review — no Lean source modified; this report is the only artifact.
**Date**: 2026-06-29
**Zulip ref**: "Propositional Logic" thread (606970606), Waring's fragment-genericity ask.

> AI-policy note: Per the CSLib/Mathlib AI usage policy, all Zulip-facing prose must be
> human-authored. Every block below marked **[SCAFFOLD — human rewrite before posting]** is a
> draft to be reworded by a human before any upstream communication.

---

## 1. Summary / Verdict

**The structure-first propositional base does NOT lift naturally today; only its classical
collapse survives.** The base is genuinely structure-first at the propositional level — `bot`
is a primitive nullary constructor (`Defs.lean:85`), `efq` is gated `[IsIntuitionistic T]`
(`NaturalDeduction/Basic.lean:182`), `botL` is gated `[IsIntuitionistic T]`
(`SequentCalculus/LJ/Basic.lean:100`), and explosion/DNE are additive property-module
typeclasses (`NaturalDeduction/Basic.lean:61-69`). But the three embeddings into Modal,
Temporal, and Bimodal (`toModal`, `toTemporal`, `toBimodal`) encode `and`/`or` via the
Łukasiewicz definitions `A∧B ↦ ¬(A→¬B)`, `A∨B ↦ ¬A→B`, which are classically but **not**
intuitionistically valid. Their semantic-preservation theorems are stated against two-valued
`PL.Evaluate` and classical satisfaction, so the lift only certifies the CPL fragment. The
minimal/intuitionistic distinction that is the whole point of the structure-first base is
**erased at the embedding boundary**. All three seed findings are **confirmed**; Finding 2 is
**sharpened** (Modal's parametric lemma already serves 15 systems, so the asymmetry is larger
than stated). The good news: the architecture is *poised to surpass* the Zulip vision because
the factoring already exists on the Modal side (`liftDerivation`, `modal_conservative_extension_param`)
and the generic substrate already exists on the PL side (`GenericLindenbaum`, `GenericMCSBridge`) —
the debt is non-instantiation, not absence.

---

## 2. Verified Architecture Map of the Lift

```
                      PL.Proposition Atom   {atom, bot, imp, and, or}   (native ∧/∨)
                      proof systems gated by [IsIntuitionistic T] / [IsClassical T]
                      MPL ⊂ IPL ⊂ CPL    (efq gated, botL gated, DNE gated)
                                 │
                                 │  toModal / toTemporal / toBimodal
                                 │  atom,bot,imp : STRUCTURAL (rfl-preserving)
                                 │  and,or       : ŁUKASIEWICZ (classical-only)
                                 ▼
   Modal.Proposition {atom,bot,imp,box}   Temporal.Formula {atom,bot,imp,untl,snce}
                                          Bimodal.Formula {atom,bot,imp,box,untl,snce}
                          (NO native ∧/∨; NO intuitionistic target system)
                                 │
                                 │  semantic bridge (classical, two-valued)
                                 ▼
        Modal.Satisfies / Temporal.Satisfies / Bimodal.truthAt  ⇔  PL.Evaluate  (Bool)
                                 │
                                 │  soundness + prop_completeness
                                 ▼
                    Conservative extension over **CPL** (PropositionalAxiom)
            Modal: 1 parametric lemma → 15 per-system results
            Temporal: 1 concrete re-proof   Bimodal: 1 concrete re-proof
```

**File:line anchors (all verified by reading source):**

| Component | Location | Note |
|-----------|----------|------|
| Primitive `bot` constructor | `Cslib/Logics/Propositional/Defs.lean:85` | nullary, native |
| `efq` gated `[IsIntuitionistic T]` | `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:182` | MPL admits no instance |
| `botL` gated `[IsIntuitionistic T]` | `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean:100` | LJ analogue |
| Property modules (typeclass) doc | `NaturalDeduction/Basic.lean:61-69` | `IsIntuitionistic`, `IsClassical` additive |
| `toModal` (Łukasiewicz and/or) | `Cslib/Logics/Modal/FromPropositional.lean:58-63` | limitation note :35-41 |
| `modal_satisfies_toModal_iff_evaluate` | `Modal/FromPropositional.lean:106` | bridge to `PL.Evaluate` |
| `toTemporal` | `Cslib/Logics/Temporal/FromPropositional.lean:57-62` | limitation note :34-40 |
| `temporal_satisfies_toTemporal_iff_evaluate` | `Temporal/ConservativeExtension.lean:45` | concrete bridge |
| `toBimodal` + commuting diamond | `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean:59-118` | `embedding_commutes:116` |
| `modal_conservative_extension_param` | `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean:54` | **parametric** |
| `temporal_conservative_extension` | `Temporal/ConservativeExtension.lean:87` | concrete |
| `bimodal_conservative_extension` | `Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean:118` | concrete (seed said :60; the *bridge* lemma starts :60, the theorem is :118) |
| `liftDerivation` (Modal inter-system) | `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean:47` | parametric over axiom subsumption |
| `GenericLindenbaum` substrate | `Cslib/Logics/Propositional/Metalogic/GenericLindenbaum.lean` | additive, deferred :43-52 |
| `GenericMCSBridge` | `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` | axiom-parametric MCS equivalence |

---

## 3. Finding 1 — CPL-Only Embedding (CONFIRMED)

### Verification

All three embeddings are structural on `{atom, bot, imp}` and Łukasiewicz on `{and, or}`:

- `toModal` (`Modal/FromPropositional.lean:58-63`): `and φ₁ φ₂ => φ₁.toModal.and φ₂.toModal`
  where `Modal.Proposition.and/or` are themselves Łukasiewicz macros (the doc at :53-57 expands
  `A∧B = (A→(B→⊥))→⊥`, `A∨B = (A→⊥)→B`).
- `toTemporal` (`Temporal/FromPropositional.lean:61-62`): `and` ↦ `.imp (.imp φ₁ (.imp φ₂ .bot)) .bot`,
  `or` ↦ `.imp (.imp φ₁ .bot) φ₂` — Łukasiewicz inlined.
- `toBimodal` (`Bimodal/Embedding/PropositionalEmbedding.lean:63-64`): identical Łukasiewicz inlining.

The explicit in-source limitation notes are unambiguous and cite `[Wajsberg1938]`,
`[McKinsey1939]`: *"classically valid but not intuitionistically valid… sound for classical
modal logics (e.g. K, S4, S5) but **not** for intuitionistic modal logics. If CSLib adds
intuitionistic modal logic in the future, a separate embedding respecting the native and/or
constructors will be required."* (`Modal/FromPropositional.lean:37-41`; verbatim analogues at
`Temporal/FromPropositional.lean:36-40`, `Bimodal/.../PropositionalEmbedding.lean:34-41`).

The semantic-preservation theorem `modal_satisfies_toModal_iff_evaluate`
(`Modal/FromPropositional.lean:106`) has conclusion `Modal.Satisfies m w φ.toModal ↔
PL.Evaluate (m.v w) φ`. `PL.Evaluate` is the **two-valued Bool valuation** (the `and`/`or`
cases at :118-142 use `by_contra` and `by_cases` — classical reasoning). It therefore certifies
preservation of **classical** tautologyhood only (`tautology_iff_toModal_valid:162`). The
identical pattern holds for Temporal (`:45`, `by_contra`/`by_cases` at :63-74) and Bimodal
(`:60`, same at :87-98).

**Corroborating structural facts** (verified): `Modal.Proposition` exposes only
`{atom, bot, imp, box}` (`Modal/Denotation.lean:38-51` enumerates exactly these cases; no
`and`/`or` arm exists). Grep for `Intuitionistic` across `Modal/`, `Temporal/`, `Bimodal/`
returns **only** `Modal/Tableau/*` files, and the single hit in `Tableau/Defs.lean:40` is a
citation to *Fitting, Proof Methods for Modal and Intuitionistic Logics* — i.e. a book title,
**not** an intuitionistic modal logic. **There is no intuitionistic modal/temporal/bimodal
target in CSLib today.** Finding 1 stands exactly as stated.

### What a structure-preserving embedding would require

To make the minimal/intuitionistic base survive the lift, one needs **all** of:

1. **Native `and`/`or` constructors** on the target syntax (`Modal.Proposition`,
   `Temporal.Formula`, `Bimodal.Formula`) — currently absent. This is a syntax change rippling
   through every recursor (denotation, satisfaction, derivation, tableau).
2. **An intuitionistic target proof system** — a gated-`efq` modal/temporal derivation system
   mirroring the PL design — currently absent.
3. **An intuitionistic (Kripke/birelational) target semantics** preserving forcing of `∧`/`∨`,
   plus a bridge to PL's `IForces` (`Propositional/Semantics/Kripke.lean`, parametric
   `botForces`) rather than to two-valued `PL.Evaluate`.
4. **A structure-preserving embedding theorem** of the form
   `IPL.Derivable φ → IModal.Derivable φ.toIModal` (proof-theoretic preservation), not merely
   `Tautology ↔ valid` (classical-semantic preservation).

This is a large, multi-logic undertaking (a new logic family), **not** a refactor. The honest
near-term move is documentation/abstraction: extract a single `Embedding` typeclass capturing
"structural on atom/bot/imp, Łukasiewicz on and/or" so the three copies share one definition and
one limitation note, and leave a clearly-typed extension point for a future native embedding.

**Effort**: structure-preserving native embedding = **XL (multi-task, weeks)**, gated on a new
intuitionistic-modal logic existing first (out of scope for 415's children). Shared-`Embedding`-
typeclass refactor = **S–M (1 focused task)**.

---

## 4. Finding 2 — Conservativity Asymmetry (CONFIRMED & SHARPENED)

### Verification

- **Modal** is fully factored: `modal_conservative_extension_param`
  (`Modal/Metalogic/ConservativeExtension.lean:54`) takes `Derivable Axioms φ.toModal` plus a
  satisfaction callback `h_sat` and discharges via `prop_completeness` +
  `modal_satisfies_toModal_iff_evaluate`. **Sharpening**: there are **15 per-system
  conservative-extension files** (`Modal/Metalogic/Systems/{K,T,D,B,S4,S5,K4,K5,K45,KB5,D4,D5,D45,DB,TB}/ConservativeExtension.lean`),
  and grep confirms `modal_conservative_extension_param` is referenced in **16** Modal files
  (the param def + all 15 instantiations). The Modal side is the *model* of the structure-first
  vision already realized.
- **Temporal** re-proves concretely: `temporal_conservative_extension`
  (`Temporal/ConservativeExtension.lean:87`) inlines its own bridge lemma
  `temporal_satisfies_toTemporal_iff_evaluate:45` and builds a constant `TemporalModel ℤ`.
- **Bimodal** re-proves concretely: `bimodal_conservative_extension`
  (`Bimodal/.../PropositionalConservativity.lean:118`) inlines
  `bimodal_truthAt_toBimodal_iff_evaluate:60` and builds the trivial `TaskFrame ℤ`.

The three bridge lemmas are **structurally identical** in their `imp`/`and`/`or` arms (compare
`Modal/FromPropositional.lean:114-142`, `Temporal/ConservativeExtension.lean:53-78`,
`Bimodal/.../PropositionalConservativity.lean:77-102` — the `and`/`or` proof scripts are
copy-equal modulo the satisfaction symbol). The only genuine per-logic content is: (a) the model
constructor (Unit model / constant `TemporalModel ℤ` / trivial `TaskFrame ℤ`), and (b) the
soundness call. Finding 2 confirmed; asymmetry is wider than seed (15 vs 1 vs 1).

### Proposed unified signature (Foundations-level conservativity lift)

A single parametric theorem can subsume all three. Sketch (the callback bundle generalizes the
Modal pattern):

```lean
-- Foundations/Logic/Metalogic/ConservativityLift.lean  (NEW)
/-- Generic conservativity of a target logic `L` over CPL through a structural embedding `emb`. -/
theorem conservative_over_cpl
    {Atom : Type*} {Tgt : Type*}                       -- target formula type
    {TgtValid : Tgt → Prop}                            -- "derivable in the target system"
    (emb : PL.Proposition Atom → Tgt)                  -- the embedding (toModal/toTemporal/toBimodal)
    (bridge : ∀ (v : Atom → Prop), TgtValid (emb φ) → PL.Evaluate v φ)
                                                        -- target-validity ⇒ PL.Evaluate, one per logic
    (h : TgtValid (emb φ)) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness; intro v; exact bridge v h
```

Each logic then supplies exactly one `bridge` term, assembled from `{model constructor +
soundness + structural-induction bridge lemma}`. The structural-induction bridge lemma itself
(`imp`/`and`/`or` arms) is logic-independent given a `Satisfies`-shaped relation, so it can
*also* be factored as a second generic lemma parameterized over a "classical truth functional"
typeclass on the target satisfaction. This collapses ~3 bridge proofs + 3 conservativity proofs
into 1 + 1 generic theorems + 3 thin instances.

**Effort**: **M (1 task)**. The Modal param lemma is already 90% of the abstraction; lifting it
to `Foundations/Logic/Metalogic/` and re-instantiating Temporal/Bimodal on top is mechanical.
Risk: the three target satisfaction relations have different shapes (`Modal.Satisfies` vs
`Temporal.Satisfies` vs `Bimodal.truthAt` with `Omega`/`τ`), so the generic "classical truth
functional" typeclass needs care to admit all three.

---

## 5. Finding 3 — GenericLindenbaum Debt (CONFIRMED)

### Verification + line counts

`GenericLindenbaum.lean` (**295 lines**) defines a real, non-vacuous explosion-parameterized
substrate: `GenericTheory Axioms Cons S` (:82), `GenericDeductiveClosure` (:93),
`generic_deriv_from_closure_to_S` (:109), `generic_deriv_imp_of_union` (:153),
`generic_imp_witness` (:264). The explosion difference between MPL and IPL is isolated into the
single `h_cons_ext` callback (:273-274), exactly as designed. The file is explicitly **additive**
and **unused**: *"This file is additive: MinLindenbaum.lean and IntLindenbaum.lean are not
modified. Re-instantiation of MinTheory/IntDCCS off this substrate is deferred to Phase 6 of the
MPL-base structure-first redesign (task 407)."* (`GenericLindenbaum.lean:47-49`).

The parallel files persist (verified `wc -l`):

| File | Lines |
|------|------:|
| `MinLindenbaum.lean` | 247 |
| `IntLindenbaum.lean` | 318 |
| `GenericLindenbaum.lean` (substrate, unused) | 295 |
| `MinSoundness.lean` | 121 |
| `IntSoundness.lean` | 128 |
| `Soundness.lean` (classical) | 93 |
| `MinStrongCompleteness.lean` | 350 |
| `IntStrongCompleteness.lean` | 353 |
| `StrongCompleteness.lean` (classical) | 570 |
| **Total (these 9)** | **2475** |

The Min/Int Lindenbaum pair (247 + 318 = 565 lines) is the immediate consolidation target:
`generic_deriv_from_closure_to_S` / `generic_deriv_imp_of_union` / `generic_imp_witness` already
exist to replace their `min_*`/`int_*` twins. The seed's "~50% duplicated" is a fair estimate for
the Lindenbaum pair; the soundness/strong-completeness trios overlap less (the classical
`StrongCompleteness.lean` at 570 lines carries genuinely extra DNE machinery).

### Consolidation scope

1. **Phase-6 re-instantiation (the named debt)**: re-derive `MinTheory` and `IntDCCS` as
   instances of `GenericTheory` with `Cons := fun _ => True` and
   `Cons := PropSetConsistent IntPropAxiom`, deleting the duplicated bodies of
   `min_deriv_from_closure_to_S`/`int_*` etc. Net: ~565 → ~295 + thin instances.
2. **Strong-completeness**: factor the shared MCS→model construction through
   `GenericMCSBridge.lean` (which already proves `pl_setMaxConsistent_iff_algebraic` for any
   `HasMinimalAxioms` axiom predicate) so `MinStrongCompleteness`/`IntStrongCompleteness` share
   one canonical-model build.
3. **Soundness**: `MinSoundness`/`IntSoundness`/`Soundness` differ mainly by which property-module
   cases (`efq`/DNE) appear — parameterize over the gated rule set.

### Overlap with task 393

Task 393 (`[NOT STARTED]`, deps 386/391/395, **Zulip-first per CONTRIBUTING**) is broader and
**partially overlapping**: it targets (a) one generic quotient-Lindenbaum over the *three
HilbertLindenbaum* builds (~2100 lines: `HilbertLindenbaum`, `HilbertLindenbaumRel`,
`HilbertAlgCompleteness`, + 4th in Bimodal); (b) making `litCtx_congr` public to parameterize the
3 Classical completeness files via `GenericMCSBridge`/`HasMinimalAxioms`; (c) assessing 3
Soundness + 8 conservativity modules + LJ/LK helper duplication. **Relationship**: task 393's
scope (a)/(b) is the *algebraic/quotient* Lindenbaum + Classical-completeness axis;
GenericLindenbaum Phase-6 is the *deductive-closure* Min/Int Lindenbaum axis. They are siblings
sharing `GenericMCSBridge` as common infrastructure. Recommendation: **scope GenericLindenbaum
Phase-6 as a distinct, smaller task that lands first** (it has a ready-made substrate and no Zulip
gate beyond 393's umbrella coordination), and explicitly cross-reference 393 so the conservativity
"(c)" assessment folds in Finding 2's unified lift.

**Effort**: Phase-6 Lindenbaum re-instantiation = **M**. Full 393 = **L (Zulip-gated)**.

---

## 6. Structural-Metatheory & InterSystem Lifting Assessment

### `liftDerivation` (Modal/Metalogic/InterSystem/Lifting.lean:47)

Verified: `liftDerivation` (:47) is a clean parametric structural recursion lifting
`DerivationTree Axioms1 Γ φ → DerivationTree Axioms2 Γ φ` given `h_sub : ∀ φ, Axioms1 φ → Axioms2 φ`,
with corollary `Derivable_mono` (:66). **It generalizes only within the Modal `DerivationTree`
type** — `Proposition Atom` here is `Modal.Proposition`. The Bimodal side has an *analogous but
independent* `liftDerivationWith`/`liftDerivationQfree`
(`Bimodal/Metalogic/ConservativeExtension/Lifting.lean:636,691`) operating on the Bimodal
`DerivationTree` with frame-class/quantifier-free machinery — i.e. the same idea re-implemented.
There is **no shared cross-logic lifting layer**.

The pattern (structural recursion over a derivation tree, mapping axiom/leaf instances under a
subsumption callback while passing `assumption`/`mp`/`weakening`/`necessitation` through) is
**logic-generic**. It could live in `Foundations` over an abstract `DerivationTree`-like
inductive, but CSLib's per-logic derivation trees are separate inductives with different
constructor sets (Modal has `necessitation`; PL has none — confirmed in `GenericMCSBridge.lean`
docstring "4 constructors… no necessitation arm"; Bimodal adds `temporal_duality`). A shared layer
therefore requires either a typeclass over "derivation systems with a subsumption-stable
constructor set" or the existing `InferenceSystem`/`algebraicDerivationSystem` abstraction
(already used by `GenericMCSBridge`) to be the common substrate.

### Per-system structural metatheory (weakening/subst/cut across ND/LJ/LK)

`NaturalDeduction/Basic.lean` alone defines a full structural-metatheory suite on its derivation
type: `Ctx.subst:131`, `Theory.Derivation.weak:286`, `weakTheory:306`, `weakCtx:311`,
`DerivableIn.weak:316`/`weakTheory:321`/`weakCtx:326`, `cut:334`, `cut_away:347`, `subs:363`,
`substAtom:392`. LJ and LK have their own weakening/cut/subst families. Because ND, LJ, and LK are
**three different inductive proof objects** (term-style ND tree, two-sided LK sequent, single-
succedent LJ sequent), a literal shared `weakening`/`cut` is not possible without first unifying
on a common `InferenceSystem`/`DerivationTree` abstraction. **Assessment**: a *shared parametric
layer is feasible only at the `InferenceSystem` level* (the abstraction `GenericMCSBridge` already
leans on). The realistic, high-value move is the narrower one — the gated-rule structural lemmas
(`weak`/`subs`) already thread `[IsIntuitionistic T]` uniformly (e.g. ND `efq`-arm rebinding at
`Basic.lean:301-303`, LJ `botL`-arm at `LJ/Basic.lean:185-187`); these are already
property-module-generic and need no further factoring. A full ND/LJ/LK metatheory unification is
**XL** and likely not worth it; flag as "assessed, deprioritized."

---

## 7. Met / Partial / Open vs the Zulip Structure-First Vision

| Vision element (Zulip 606970606, Waring fragment-genericity) | Status | Evidence / gap |
|---|---|---|
| Primitive `bot`, gated explosion, additive property modules at PL level | **MET** | `Defs.lean:85`, `ND/Basic.lean:182`, `LJ/Basic.lean:100`, property-module doc `:61-69` |
| Metatheorems lift to a fragment by construction (not reproved) — *Modal conservativity* | **MET** | 1 param lemma → 15 systems (`ConservativeExtension.lean:54`; 16 referencing files) |
| Inter-system derivation lifting parameterized over axiom subsumption | **MET (Modal-local)** | `liftDerivation:47`, `Derivable_mono:66` |
| Generic axiom-parametric MCS / Lindenbaum substrate exists | **MET (defined)** | `GenericLindenbaum.lean`, `GenericMCSBridge.lean` |
| …and is actually used to remove Min/Int duplication | **OPEN** | substrate unused; `:47-49` "deferred to Phase 6"; 565 dup lines remain |
| Conservativity lift uniform across Modal/Temporal/Bimodal | **PARTIAL** | Modal param; Temporal/Bimodal concrete re-proofs (Finding 2) |
| Structure-preserving embedding (minimal/intuitionistic base survives lift) | **OPEN** | Łukasiewicz and/or; classical-only bridges (Finding 1); no intuitionistic modal target |
| Native `and`/`or` on target syntaxes | **OPEN** | Modal/Temporal/Bimodal lack `and`/`or` constructors |
| Shared structural metatheory (weakening/cut/subst) across ND/LJ/LK | **OPEN (assessed, deprioritized)** | three distinct inductives; only feasible at `InferenceSystem` level |

**Where CSLib can SURPASS the Zulip ask**: the Zulip thread asks that metatheorems lift to a
fragment *by construction*. CSLib already over-delivers on the Modal axis (15-system parametric
conservativity + `liftDerivation`). Generalizing that one proven pattern into a `Foundations`-level
`conservative_over_cpl` (§4) and instantiating the dormant `GenericLindenbaum` (§5) would make the
*whole* metalogic stack fragment-generic — beyond what the thread requested, with substrates that
already exist.

---

## 8. Prioritized Spawnable Follow-On Tasks

Ranked by (value to structure-first vision) × (tractability). Each is independently spawnable; the
first two close the highest-debt findings with ready-made substrates.

### Rank 1 — Instantiate GenericLindenbaum (close Phase-6 debt) — closes **Finding 3**
- **Scope**: Re-derive `MinTheory` and `IntDCCS` as instances of `GenericTheory Axioms Cons`
  (`Cons := fun _ => True` / `PropSetConsistent IntPropAxiom`), replacing the duplicated
  `min_*`/`int_*` Lindenbaum bodies (`MinLindenbaum.lean` 247L, `IntLindenbaum.lean` 318L) with
  thin instances over `generic_deriv_from_closure_to_S`/`generic_deriv_imp_of_union`/
  `generic_imp_witness`. Keep behavior identical; CI-green (`lake build`/`lint`/`shake`).
- **Dependencies**: none hard (substrate exists); coordinate-only with task 393. **Not Zulip-gated**
  (no public-API surface change beyond internal consolidation — confirm with 393 owner).
- **Effort**: **M**. **Value**: high (deletes ~270 net dup lines, activates dormant 295-line file).

### Rank 2 — Foundations-level parametric conservativity lift — closes **Finding 2**
- **Scope**: Add `Foundations/Logic/Metalogic/ConservativityLift.lean` with
  `conservative_over_cpl` (§4 signature) plus a generic classical-truth-functional bridge lemma;
  re-express `temporal_conservative_extension` and `bimodal_conservative_extension` (and optionally
  re-home `modal_conservative_extension_param`) as thin instances. Collapses 3 bridge + 3
  conservativity proofs to 1 + 1 generic + 3 instances.
- **Dependencies**: none hard. Synergistic with Rank 1 (shared `prop_completeness` usage).
- **Effort**: **M** (risk: unifying `Modal.Satisfies`/`Temporal.Satisfies`/`Bimodal.truthAt` shapes).
  **Value**: high (extends the Modal "by construction" win to all three logics — direct Zulip-ask hit).

### Rank 3 — Shared `Embedding` typeclass + single limitation note — supports **Finding 1**
- **Scope**: Factor the "structural on atom/bot/imp, Łukasiewicz on and/or" pattern into one
  `PropositionalEmbedding` typeclass/abstraction so `toModal`/`toTemporal`/`toBimodal` share a
  definition skeleton and a single authored classical-scope limitation note; keep `simp`/`grind`
  lemma surface. Adds a clearly-typed extension point for a future native embedding.
- **Dependencies**: none. Light touch on three files + the commuting-diamond lemmas.
- **Effort**: **S–M**. **Value**: medium (removes triplicated docs + def boilerplate; documents the
  CPL-only boundary in one place; does NOT itself enable intuitionistic lift).

### Rank 4 — Generalize derivation lifting to a cross-logic layer — supports vision (InterSystem)
- **Scope**: Investigate hoisting `liftDerivation`/`Derivable_mono` (Modal) and
  `liftDerivationWith` (Bimodal) onto the shared `InferenceSystem`/`algebraicDerivationSystem`
  abstraction (already used by `GenericMCSBridge`), yielding one axiom-subsumption lifting result
  reusable by Modal, Bimodal, and PL. Spike first; commit only if the necessitation/temporal_duality
  constructor variance is cleanly abstractable.
- **Dependencies**: benefits from Rank 2's Foundations placement.
- **Effort**: **L** (abstraction risk). **Value**: medium-high if it lands; flagged as spike.

### Rank 5 — (Documentation-only) record the structure-preserving-embedding requirement — closes the **Finding 1 design question**
- **Scope**: A short design note (in-repo, e.g. ORGANISATION.md or a `docs/` design doc) stating
  the four prerequisites for a native, intuitionistic-faithful embedding (native and/or; gated
  intuitionistic target system; birelational target semantics bridging to PL `IForces`;
  proof-theoretic preservation theorem), so the XL native-embedding work is well-specified when an
  intuitionistic modal logic is eventually added. **No Lean change.**
- **Dependencies**: none. **Effort**: **S**. **Value**: medium (prevents re-litigating the boundary).

> **[SCAFFOLD — human rewrite before posting]** Upstream Zulip summary draft (for human author):
> "The propositional base is structure-first (primitive ⊥, gated efq/botL, additive property
> modules). The Modal conservativity stack is already fragment-generic (one parametric lemma, 15
> systems). Two concrete next steps would extend that genericity to the whole metalogic: (1) a
> Foundations-level parametric conservativity lift to unify Temporal/Bimodal with Modal; (2)
> instantiating the existing GenericLindenbaum substrate to remove Min/Int duplication. The
> classical-only embedding (Łukasiewicz and/or) is a deliberate, documented boundary; a
> native/intuitionistic embedding is gated on a future intuitionistic modal logic." — **do not
> post verbatim; reword per AI policy.**

---

## 9. Errata / Re-Verification (2026-07-01)

**Anchors verified with drift.** Two days elapsed between this report's original verification
pass (2026-06-29) and this re-verification (2026-07-01). In the interim, **all five Rank 1-5
follow-on tasks proposed in §8 were already spawned as child tasks (416-420, `parent_task: 415`)
and have all completed** (see §10 below). Several of those completions edited the very files this
report cites, so a subset of line-number anchors have drifted. Every anchor was re-checked by
direct `Read`/`grep`/`wc -l`; corrected anchors are recorded below with the causing task.

**Anchors CONFIRMED, no drift:**
- `Cslib/Logics/Propositional/Defs.lean:85` (`bot` constructor) — exact match.
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:182` (`efq` gated `[IsIntuitionistic T]`) — exact match.
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean:100` (`botL` gated) — exact match.
- `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean:47` (`liftDerivation`) and `:66`
  (`Derivable_mono`) — exact match (task 419 added new files `Conservativity.lean` and
  `LiftViaMorphism.lean` alongside `Lifting.lean` but explicitly did not modify it).
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean:636`
  (`liftDerivationWith`), `:691` (`liftDerivationQfree`) — exact match.
- `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean:54` (`modal_conservative_extension_param`) — exact match.
- 15 per-system `Systems/{K,T,D,B,S4,S5,K4,K5,K45,KB5,D4,D5,D45,DB,TB}/ConservativeExtension.lean`
  files confirmed (`find` count = 15); 16 files reference
  `modal_conservative_extension_param` (`grep -rl` count = 16) — exact match.
- The 9-file line-count table in §5 reproduced exactly via `wc -l`: MinLindenbaum 247,
  IntLindenbaum 318, MinSoundness 121, IntSoundness 128, Soundness 93, MinStrongCompleteness 350,
  IntStrongCompleteness 353, StrongCompleteness 570. `GenericLindenbaum.lean` grew 295 -> 301
  lines (task 416's docstring rewrite, see §10).

**Anchors DRIFTED (all caused by tasks 417/418, now completed — see §10):**

| Symbol | Report cited | Now at | Cause |
|---|---|---|---|
| `modal_satisfies_toModal_iff_evaluate` | `:106` | `:85` | task 418: `toModal` became a thin `.embed` wrapper, shortening the preamble |
| `tautology_iff_toModal_valid` | `:162` | `:141` | same |
| `PL.Proposition.embedding_commutes` (Bimodal) | `:116` | `:105` | same (shared `PropositionalEmbedding` typeclass shortened the file) |
| `temporal_conservative_extension` | `:87` | `:61` | task 417: file thinned to a `conservative_over_cpl` instance (74 lines total now) |
| `bimodal_conservative_extension` | `:118` | `:97` | task 417: file thinned similarly (121 lines total now) |
| `bimodal_truthAt_toBimodal_iff_evaluate` | `:60` | `:61` | negligible (off-by-one, same cause) |

The Łukasiewicz `and`/`or` definitions cited at `Modal/FromPropositional.lean:58-63` (and the
Temporal/Bimodal analogues) **no longer live in the per-logic files** — task 418 hoisted them
into one shared definition, `PL.Proposition.embed` in
`Cslib/Logics/Propositional/Embedding.lean:71-79` (the `PropositionalEmbedding` typeclass), and
`toModal`/`toTemporal`/`toBimodal` are now thin wrappers (`:= φ.embed`) over it. The single
classical-scope limitation note (previously triplicated) now lives once in
`Embedding.lean:26-42`. This is exactly Rank 3's proposed shared-typeclass refactor, already
landed.

## 10. Post-Audit Update — All Five Spawn Candidates Already Exist and Are Complete

**This is the most important correction to make before any downstream reader acts on §8.** A
prior orchestration pass (`git` commit `ce9e3ef8`, "orchestrate tasks 416-420: complete
orchestration (4/5 succeeded)") already created and ran all five §8 spawn candidates as child
tasks with `parent_task: 415`. As of this re-verification, **all five report status
`completed`** in `specs/state.json`/`specs/archive/state.json`:

| Rank | Spawn candidate (§8) | Child task | Status | Outcome |
|---|---|---|---|---|
| 1 | Instantiate GenericLindenbaum (closes Finding 3) | **416** `instantiate_generic_lindenbaum_phase6` | completed | **Correction**: the code-level debt was *already closed* by task 407 phase 6 (commit `9242d243`), which pre-dates this audit. Finding 3's "~565 duplicated lines" claim was driven by a **stale docstring** in `GenericLindenbaum.lean:43-52` (which still said "additive... deferred to Phase 6") that was never updated after phase 6 landed. `MinLindenbaum`/`IntLindenbaum` already delegate to `generic_deriv_from_closure_to_S`/`generic_deriv_imp_of_union`/`generic_imp_witness` — verified by task 416's own re-derivation. 416's only actual deliverable was rewriting the stale docstring. A smaller residual (definitionally-equal closure-scaffolding defs, ~40 lines) remains and is explicitly left to task 393 (see below). |
| 2 | Foundations-level parametric conservativity lift (closes Finding 2) | **417** `parametric_conservativity_lift_foundations` | completed | Delivered `Cslib/Logics/Propositional/Metalogic/ConservativityLift.lean` (`conservative_over_cpl` + `evaluate_iff_of_classicalBridge`); `temporal_conservative_extension`/`bimodal_conservative_extension` re-expressed as thin instances. CI green, 0 new sorry/axioms (per task completion record). |
| 3 | Shared `PropositionalEmbedding` typeclass (supports Finding 1) | **418** `shared_propositional_embedding_typeclass` | completed | Delivered `Cslib/Logics/Propositional/Embedding.lean`; all `toX_*` simp/grind lemmas preserved as `rfl`; single limitation note. CI green, 0 new sorry/axioms. |
| 4 | Cross-logic derivation-lifting spike | **419** `generalize_derivation_lifting_intersystem` | completed | Delivered `Foundations/Logic/Metalogic/ProofSystemMorphism.lean` (forward direction: `ProofSig`/`Deriv`/`ProofSigHom`/`Deriv.map` + functor laws); Modal and PL land as full `Equiv`s, Bimodal as forward map + `HEq` intertwining. Backward/full-Equiv direction for multi-closure Bimodal explicitly out of scope (Vision A), spun off to task 448 (also completed, verdict: NO-GO on the backward-map "Vision B" substrate — insufficient ROI). |
| 5 | Documentation-only structure-preserving-embedding note | **420** `native_embedding_prerequisites_doc` | completed | Doc-only design note recording the four prerequisites, no Lean change, per spec. |

**Implication for this task's remaining scope (Phase 3/4):** the §8 spawn manifest this plan's
Phase 3 was to author has, in effect, already been executed end-to-end by a prior orchestration
run. Phase 3 below is therefore written as a **retrospective** manifest (rank -> task -> outcome)
rather than a prospective one, and Phase 4 requires **no new task creation** — there is nothing
left in the original five-item list to spawn. See `reports/02_spawn-manifest.md` for the full
retrospective manifest and the still-open task-393 cross-reference.

## 11. Artifact Classification (internal vs upstream-facing)

Per the CSLib/Mathlib AI usage policy, artifacts are classified below so no AI-authored prose is
ever mistaken for upstream-ready text.

| Artifact | Classification | Notes |
|---|---|---|
| This report (`reports/01_lifting-audit.md`), all sections except §8's scaffold block | **Internal** | AI-authored analysis for internal task-planning use; not intended for direct upstream posting. |
| §8 Zulip summary draft (marked `[SCAFFOLD — human rewrite before posting]`) | **Upstream-facing (BLOCKED — human rewrite required)** | Must not be posted verbatim; a human author must reword it before any Zulip communication. |
| `reports/02_spawn-manifest.md` (this task's Phase 3 deliverable) | **Internal** | Task-tracking artifact (rank -> task -> status mapping); not upstream-facing. |
| Plan `plans/01_lifting-audit-spawn.md` | **Internal** | Task-management artifact. |
| Summary `summaries/01_*.md` | **Internal** | Task-management artifact. |
| Child tasks 416-420's own summaries/completion_summary fields | **Internal** | Already-completed task-tracking records; not reviewed for upstream-readiness here (out of this task's scope). |

**Consistency check against Phase 1 re-verification:** the §7 met/partial/open matrix and the
"where CSLib can SURPASS" statement (§7 closing paragraph) are **still internally consistent**
after the Phase 1 anchor re-verification and the §10 post-audit update: the "OPEN" items (native
`and`/`or`, structure-preserving embedding) remain open (task 420 only documented the
prerequisites, did not implement them — confirmed no native `and`/`or` constructor exists on
`Modal.Proposition`/`Temporal.Formula`/`Bimodal.Formula` as of this re-verification); the "MET
(defined)" GenericLindenbaum row should be read together with §10's correction (the substrate was
already both *defined and instantiated* before this audit, not merely *defined*); the Modal
"MET" conservativity row is now matched by Temporal/Bimodal via task 417 (upgrading §7's
"PARTIAL" conservativity-uniformity row to **MET**, since `conservative_over_cpl` now unifies all
three). No AI-authored prose is presented as upstream-ready anywhere in this document; the §8
scaffold retains its `[SCAFFOLD]` marker unmodified. Effort estimates in §8 match the spawn
manifest built retrospectively in §10/`02_spawn-manifest.md` (all landed at their estimated
efforts: M/M/S-M/L/S — task 416 downgraded to a trivial doc fix in practice, but was *scoped* at
M going in, consistent with the estimate given the information available at spawn time).

## Appendix — Verification Method

All file:line citations were obtained by reading source directly (Read tool) and by
`grep`/`wc -l`. Seed line numbers were confirmed except: the Bimodal conservativity *theorem*
`bimodal_conservative_extension` is at `:118` (the seed's `:60` is the start of the *bridge
lemma* `bimodal_truthAt_toBimodal_iff_evaluate`). The base-layer anchors in the task's CONTEXT
block used a stale `Syntax/` path prefix; the live paths are
`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:182` (efq) and
`.../SequentCalculus/LJ/Basic.lean:100` (botL) — both verified. No lean-lsp goal/hover calls
were needed since every claim was a definition/theorem statement readable in source; build state
was not exercised (no code change). No Lean source was modified.

**2026-07-01 re-verification appendix**: all §2/§3/§4/§5 anchors re-checked by direct `Read`,
`grep -n`, `grep -rl`, `find`, and `wc -l` (see §9 for the full corrected table). No lean-lsp
goal/hover calls were needed (all claims are definition/theorem-location or line-count facts
readable directly from source and `git log`/`jq` on `specs/state.json` +
`specs/archive/state.json`). No Lean source was modified in this re-verification pass
(`git status` confirms only `specs/415_.../` artifacts changed, plus one pre-existing unrelated
modification to `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` from a different task, present
before this session started and untouched by it).
