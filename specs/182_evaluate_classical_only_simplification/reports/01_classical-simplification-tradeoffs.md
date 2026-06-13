# Research Report: Classical Upper Layers with Minimal Primitives

## Task 182 — evaluate_classical_only_simplification

### Decision

Keep Modal/, Temporal/, and Bimodal/ classical-only with the minimum number of formula constructors. Revert the primitive `and`/`or` constructors added by tasks 175-177, restoring Lukasiewicz abbreviations in the upper layers. The Propositional layer retains its full five-primitive design and three-tier completeness (minimal/intuitionistic/classical). If weaker propositional logics are needed in the upper layers in the future, primitives can be re-added — the forward playbook is proven and documented in tasks 175-177.

### Target Primitive Sets

```
Propositional:  {atom, bot, imp, and, or}               — 5 (unchanged)
Modal:          {atom, bot, imp, box}                    — 4 (revert and/or)
Temporal:       {atom, bot, imp, untl, snce}             — 5 (revert and/or)
Bimodal:        {atom, bot, imp, box, untl, snce}        — 6 (revert and/or)
```

Derived connectives in the upper layers (classical-only):
```
neg φ   := imp φ bot              — valid in all logics
top     := imp bot bot            — valid in all logics
and φ ψ := neg (imp φ (neg ψ))   — classical only (Lukasiewicz)
or φ ψ  := imp (neg φ) ψ         — classical only (Lukasiewicz)
```

### Rationale

**1. The Propositional layer is the right home for logic-tier complexity.** The three-tier structure (MinimalHilbert / IntuitionisticHilbert / ClassicalHilbert) with prime theories, Zorn's lemma, and ND-Hilbert bridges lives entirely in Propositional/. This is where and/or must be primitive — the intuitionistic completeness proof requires the disjunction property, which fails for the Lukasiewicz encoding. The upper layers consume the classical fragment and don't need this machinery.

**2. Abbreviations cascade simplification through the proof system.** With Lukasiewicz abbreviations, the propositional and/or axioms (andI, andE1, andE2, orI1, orI2, orE) become derivable *theorems* rather than primitive axiom constructors. This shrinks every axiom set:

| Layer | Current axioms per system | Simplified |
|-------|--------------------------|-----------|
| Modal K | 11 (implyK, implyS, efq, peirce, andI, andE1, andE2, orI1, orI2, orE, modalK) | 5 (implyK, implyS, efq, peirce, modalK) |
| Each modal system | 11 + system-specific | 5 + system-specific |
| Soundness cases | 11 per system × 15 systems = 165 | 5 × 15 = 75 |

A ~55% reduction in axiom constructors and soundness proof obligations across all 15 modal systems.

**3. Case analysis overhead is real and permanent.** Every pattern match and induction proof in the Bimodal layer (127 files) carries cases for each constructor. Going from 8 to 6 constructors eliminates ~25% of match cases. The `encodeNat` injectivity proof shrinks from 64 to 36 case pairs. This compounds across every future theorem.

**4. The forward path is proven and repeatable.** Tasks 175-177 established the exact playbook for adding primitive constructors to the upper layers. If intuitionistic modal or temporal logic becomes a research goal, the refactor can be re-executed with known cost (~20 agent dispatches for Bimodal). Nothing is lost by reverting — only deferred.

### How Classical Propositional Logic Expands to Upper Systems

There are three methods by which the Propositional layer connects to Modal/, Temporal/, and Bimodal/. Each works cleanly with abbreviated and/or in the upper layers.

#### Method 1: Syntactic Embedding (FromPropositional)

Each upper layer has a `FromPropositional.lean` file defining a homomorphic injection:

```
embed : Propositional.Proposition Atom → Modal.Proposition Atom
embed (.atom a)    := .atom a
embed (.bot)       := .bot
embed (.imp φ ψ)   := .imp (embed φ) (embed ψ)
embed (.and φ ψ)   := Modal.Formula.and (embed φ) (embed ψ)    -- maps to abbreviation
embed (.or φ ψ)    := Modal.Formula.or (embed φ) (embed ψ)     -- maps to abbreviation
```

The embedding maps Propositional's primitive `.and`/`.or` to Modal's abbreviation-defined `and`/`or`. This is a semantic homomorphism: it preserves all logical properties. The classical equivalence `and φ ψ = ¬(φ → ¬ψ)` holds in the target system (which has Peirce's law), so the embedding is sound.

**Proof obligation**: The embedding must satisfy `Satisfies m w (embed φ) ↔ eval v φ` (relating Modal Kripke satisfaction to Propositional Boolean evaluation). With abbreviations, this requires proving that the Lukasiewicz encoding satisfies the expected semantics — straightforward given Peirce's law.

**Cost**: 2-3 lemmas per embedding file proving the and/or abbreviation cases. These may involve short `sorry`-stubs if the equivalence proof is deferred, or direct proofs using the classical axioms. This is the only concrete cost of reverting.

#### Method 2: Axiom Inheritance via Derivability

The upper layers don't copy propositional axioms — they *derive* them. With a classical proof system (implyK, implyS, efq, peirce), all propositional tautologies are derivable as theorems:

```
-- These become theorems, not axiom constructors:
theorem andI_derived : Derivable Axioms (φ → (ψ → φ ∧ ψ))    -- from implyK, implyS, efq, peirce
theorem andE1_derived : Derivable Axioms (φ ∧ ψ → φ)          -- from peirce
theorem orI1_derived : Derivable Axioms (φ → φ ∨ ψ)           -- from implyK
theorem orE_derived : Derivable Axioms ((φ→χ) → (ψ→χ) → (φ∨ψ→χ))  -- from implyS, peirce
```

These derivability theorems live in the Foundations layer (`Theorems/Propositional/Core.lean`, `Theorems/Combinators.lean`) and are already proven for any system with `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`. The upper layers register these typeclass instances and inherit all propositional theorems for free.

**Key insight**: The Foundations theorems use `HasImp`/`HasBot` typeclasses, so they produce `imp`/`bot`-encoded and/or. This matches the abbreviation definitions perfectly — no translation needed.

#### Method 3: Conservative Extension

The strongest connection: a proof that the upper layer is a *conservative extension* of Classical Propositional Logic. This means: if φ is a propositional formula and Modal K proves φ, then CPL already proves φ. No new propositional truths are introduced by adding modalities.

```
theorem modal_conservative_extension :
    Derivable (@KAxiom Atom) (embed φ) → Derivable (@CPLAxiom Atom) φ
```

This is a standard metalogical result for normal modal logics. It transfers the Propositional completeness theorem upward: if φ is a propositional tautology, the Propositional completeness proof already covers it, and the Modal soundness proof preserves it.

**Implication**: Propositional metalogic results (soundness, completeness, decidability for the propositional fragment) never need reproof in the upper layers. The embedding + conservative extension gives them for free.

### Comparison of Methods

| Method | What it provides | Where it lives | Abbreviation-compatible? |
|--------|-----------------|----------------|-------------------------|
| Syntactic embedding | Formula translation | `FromPropositional.lean` | Yes (maps to abbrevs) |
| Axiom inheritance | Propositional theorems | `Foundations/Theorems/` | Yes (produces imp/bot terms) |
| Conservative extension | Metalogic transfer | `Metalogic/` | Yes (classical equivalence) |

All three methods work cleanly with abbreviated and/or in the upper layers. The Lukasiewicz encoding is invisible to users who work with the `∧`/`∨` notation — it only matters at the kernel level where proofs reduce through `imp`/`bot`.

### Impact on Tasks 179-181

Tasks 179-181 (primitive diamond, allFuture, allPast) should be **deferred**, not abandoned. Their research reports document valid motivation for intuitionistic modal/temporal logic. If that direction becomes a research goal:

1. First re-add primitive and/or (replay tasks 175-177 playbook)
2. Then add diamond/allFuture/allPast (tasks 179-181)
3. Then build intuitionistic proof systems and metalogic

The reverse order doesn't work — intuitionistic diamond requires primitive and/or already in place (can't express `◇A ∨ ◇B` without primitive `∨`).

### Revert Scope

Reverting and/or in the upper layers requires:

| Layer | Files affected | Primary change |
|-------|---------------|----------------|
| Modal | ~55 | Remove .and/.or constructor + all match cases |
| Temporal | ~11 | Remove .and/.or constructor + match cases + MCS helpers |
| Bimodal | ~50+ | Remove .and/.or constructor + match cases (largest) |
| Foundations/Theorems | 0 | Already uses HasImp/HasBot (no change needed) |
| Propositional | 0 | Keeps primitive and/or (unchanged) |

The revert is the mirror image of tasks 175-177. Key operations:
1. Remove `.and`/`.or` constructors from Formula inductive types
2. Restore `abbrev` definitions using Lukasiewicz encoding
3. Remove all `.and`/`.or` match arms from every function and proof
4. Remove andI/andE/orI/orE from axiom inductive types (they become derived theorems)
5. Remove MCS and/or helpers (mcs_or_resolve, etc.) — `implication_property` handles everything via the encoding
6. Restore FromPropositional embedding proofs (2-3 lemmas per file)
7. Verify CI

### Future Weakening Path

If intuitionistic variants are needed later, the expansion path is:

```
Phase 1: Re-add primitive and/or to target layer (replay task 175/176/177)
Phase 2: Add primitive dia / allFuture / allPast (tasks 179/180/181)
Phase 3: Parameterize proof system by theory (remove Peirce as default)
Phase 4: Add bi-relational Kripke semantics (intuitionistic frames)
Phase 5: Prove intuitionistic soundness + completeness
```

Each phase is independently valuable and can stop at any point. Phase 1 alone gives cleaner pattern matching. Phases 1-2 give the full primitive set. Phases 1-5 give complete intuitionistic metalogic.

### References

- Wajsberg, M. (1938). Non-interdefinability of intuitionistic connectives.
- McKinsey, J. (1939). Independence of Heyting's primitives.
- Johansson, I. (1937). Der Minimalkalkül. *Compositio Mathematica*, 4, 119-136.
- Fischer Servi, G. (1984). Axiomatisations for some intuitionistic modal logics.
- Simpson, A. (1994). *The Proof Theory and Semantics of Intuitionistic Modal Logic*. PhD thesis.
- Boudou, J. et al. (2017). A decidable intuitionistic temporal logic. *CSL*.
