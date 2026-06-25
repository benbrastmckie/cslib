# Research Report: Theory-Parametric Algebraic Completeness (Task 341)

**Status**: Research complete — strategy compile-verified end-to-end (scratch file built green
with `lake build`, 0 sorries, 0 new axioms, then removed).

## Objective

Restate propositional algebraic completeness theory-parametrically over `AlgTValid`, adopting
Thomas Waring's `v ⊨ T` formulation as the canonical statement. Introduce a single
theory-parametric completeness theorem and recover the three existing tier theorems
(MPL/IPL/CPL) as corollaries.

## Target Theorem

```
theorem hilbert_alg_complete_theory {Atom : Type u} (Axioms) [MinimalAxioms Axioms] (φ) :
    Derivable Axioms φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v) (bot_val),
      AlgTValid (AxiomTheory Axioms) v bot_val → AlgEvaluate v bot_val φ = ⊤
```

**Universe pinning is mandatory.** Pin `{Atom : Type u}` and quantify `(H : Type u)` matching the
atom universe, mirroring the existing `.{u,u}` annotations. Using `Type _` produces
universe-metavariable type mismatches (verified by hitting and fixing exactly this).

## Existing Machinery (reuse)

- `AlgTValid` predicate: `Cslib/Logics/Propositional/Semantics/Algebra.lean:149` (currently unused).
- `AxiomTheory` (axiom set → theory).
- `MinimalAxioms` typeclass — Lindenbaum scaffolding already parametric in it.
- Lindenbaum scaffolding in `Semantics/Algebra/HilbertLindenbaum.lean`:
  `HilbertLindenbaumAlgebra`, `canonicalV`, `canonicalBotVal`, `canonicalV_spec`,
  `hilbertLindenbaumMk_eq_top_iff`.
- **`canonicalV_axiom_top` ALREADY EXISTS** at `HilbertLindenbaum.lean:624`.
- `min_alg_soundness` derivation match: `Soundness.lean:168`.
- Per-tier `*_alg_axiom_sound` lemmas (Soundness.lean).
- Existing tier theorems: `MPL.hilbert_alg_complete` (HilbertCompleteness.lean:57),
  `IPL.hilbert_alg_complete` (:80), `CPL.hilbert_alg_complete` (:105).

## Work Items (all compile-verified)

### Item 1 — Parametric soundness lemma `alg_theory_soundness`
New lemma parametric in `Axioms`, discharging the `.ax` case from the `AlgTValid` hypothesis.
It mirrors `min_alg_soundness` (`Soundness.lean:168`) with only the `.ax` case changed:
`exact hT ψ (by simpa [AxiomTheory] using h_ax)`. The `modus_ponens`/`assumption`/`weakening`
cases are unchanged. Reuses `himp_eq_top_iff`, `AxiomTheory` unfold via `simpa`. May live in
`Soundness.lean`.

### Item 2 — `canonicalV_algTValid` (nearly free)
```
lemma canonicalV_algTValid (Axioms) [MinimalAxioms Axioms] :
    AlgTValid (AxiomTheory Axioms) (canonicalV Axioms) (canonicalBotVal Axioms) := by
  intro B hB; exact canonicalV_axiom_top Axioms B (by simpa [AxiomTheory] using hB)
```
One-liner using the already-existing `canonicalV_axiom_top`. Fits in `HilbertLindenbaum.lean`.

### Item 3 — Tier corollary bridges (MPL/IPL/CPL)
Each tier theorem recovered from `hilbert_alg_complete_theory` via an **explicit two-direction
proof** (see obstacle below):
- **Forward (soundness)**: instantiate the new theorem at `bot_val = ⊥`, discharge `AlgTValid`
  via the existing `*_alg_axiom_sound` lemmas.
- **Backward (completeness)**: reuse the original Lindenbaum route — `canonicalV_spec` +
  `hilbertLindenbaumMk_eq_top_iff`. For IPL/CPL reuse the verbatim `rfl` bridge
  `(⊥ : HilbertLindenbaumAlgebra _) = canonicalBotVal _`.

## Key Obstacle (resolved): `bot_val` and the Heyting/Boolean specialization

The naive bridge `HAValid φ → theory-parametric-premise` does **NOT** hold. `AlgTValid (AxiomTheory
IntPropAxiom)` only forces `bot_val` to be a *lower bound on the image of `v`* (via the `efq`
axioms), not the algebra's canonical `⊥`; a GHA may have no bottom at all. Therefore the
completeness (backward) direction of each tier corollary **cannot** be sourced from the
validity-predicate — it must reuse the original Lindenbaum instantiation. The forward direction
recovers cleanly at `bot_val = ⊥`.

## Verification

Scratch file `Cslib/Logics/Propositional/Semantics/Algebra/Task341Scratch.lean` built with
`lake build` — 646 jobs, 0 sorries, 0 new axioms; all three tier corollaries (MPL/IPL/CPL)
recovered. Scratch file removed after verification.

## Implementation Targets

- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` — new
  `hilbert_alg_complete_theory` theorem + tier corollaries.
- `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean` — `alg_theory_soundness`.
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` — `canonicalV_algTValid`.

## CI

Full pipeline (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
`lake shake`) must stay green; existing tier theorems must remain (now as corollaries).
