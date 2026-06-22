# Zulip Response: CSLib Propositional Logic Thread

**Thread**: CSLib > Propositional Logic
**Responding to**: Thomas Waring (MSG 605341190), Matthew Doty, Ching-Tsun Chou
**Date**: 2026-06-22

---

Thanks for the thoughtful discussion, Thomas and Matthew. I've worked through Thomas's `intuitionistic` branch and investigated whether a typeclass-based split could avoid the hybrid ND design. Here are my conclusions so far.

## On `⊥` as a primitive constructor

I remain convinced that primitive `⊥` is correct, and I think the thread has substantially converged on this. The decisive argument is substitution invariance. `⊥` is a nullary connective rather than a propositional variable. With `⊥`-as-atom, every substitution theorem acquires a `σ(⊥) = ⊥` side condition. With `⊥`-as-constructor, this is automatic: the monad bind case `| .bot => .bot` requires no condition. CSLib's substitution results — `subst_preserves_axiom`, `subst_preserves_intAxiom`, `hilbertSubstitution`, `Theory.Derivation.substAtom` — all work cleanly because of this. The `FromPropositional` embeddings to Modal and Temporal logic also benefit: the map `| .bot => .bot` is direct, with no special-case handling.

## Acknowledging the ND symmetry trade-off

Thomas, your ND symmetry point makes sense. Natural deduction's appeal — as Gentzen articulated it — is that each connective's meaning is given by its introduction and elimination rules. With `⊥` in the syntax, pure ND symmetry would demand that its elimination rule (`efq`) be a primitive constructor of `Derivation`. CSLib's current design breaks this: `⊥` has a syntax constructor but no derivation constructor.

This is a genuine trade-off, not an oversight. The cost of preserving ND symmetry (your `IProposition`/`IDerivation` design) is that it duplicates the entire formula API — monad instance, substitution lemmas, `DecidableEq`, three evaluation functions, two bridge lemmas, and the two `FromPropositional` embeddings. For a library building upward through Modal, Temporal, and Bimodal logics that all share `Proposition`, that is a permanent maintenance multiplier.

There is also a logical reason to accept the hybrid. `⊥` is the one connective with **no introduction rule in any proof system**. Every other connective has both intro and elim rules; `⊥` has only elimination. The asymmetry is a property of `⊥` itself, not of our design. Making `efq` a theory axiom rather than a derivation constructor reflects this directly: it is absent in MPL (where `⊥` has no special proof-theoretic status) and present in IPL/CPL as a logic-dependent rule.

I've updated the `## Implementation notes` section of `NaturalDeduction/Basic.lean` to state this trade-off factually — naming both sides and linking to this thread — rather than presenting the design as settled. I've also restored your original references (Prawitz, Troelstra & Van Dalen, Sorensen & Urzyczyn), which were inadvertently dropped during the ND overhaul.

## On `bot_val`: Johansson's designated constant

The `bot_val : H` parameter in `AlgEvaluate` is not a patch — it is the designated constant of Johansson algebras. In Johansson's original minimal logic (1937), models are algebraic structures that may or may not have a bottom element, and when they do, its interpretation is a free parameter. `bot_val` captures exactly this degree of freedom. For IPL, fixing `bot_val = ⊥` recovers the standard Heyting algebra semantics. For MPL, quantifying over all `bot_val` values is what makes MPL completeness true: if `bot_val` were forced to `⊥`, every model would validate efq, collapsing MPL into IPL. This parallels `botForces` in `KripkeModel`.

## On the parametric completeness style

Your `v ⊨ T` framing is elegant and general, and I completely agree it should be the canonical statement. It is already adopted: `AlgTValid` in `Semantics/Algebra.lean` implements exactly this pattern, and the general completeness theorem `Theory.alg_complete` uses it. The tier-specific corollaries (`MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical`) specialize the algebra type and `bot_val`, giving the clean statements you described. I've also added docstrings to all definitions in `Semantics/Algebra/Completeness.lean` explaining the Lindenbaum construction, which was previously undocumented.

## On `Prop` vs. `Bool` semantics

The dual-evaluator approach resolves this. `Evaluate` (Prop-valued) is needed for canonical model construction: MCS membership `fun p => atom p ∈ S` is irreducibly `Prop`-valued and non-computable. `BoolEvaluate` (Bool-valued) is there for DPLL and SAT. The bridge lemmas `propEvaluateEq` and `boolEvaluateEq` in `Semantics/Algebra/Bridge.lean` connect both to `AlgEvaluate`, confirming they are special cases of the algebraic framework. Matthew, your DPLL work can build entirely on the `BoolEvaluate` layer without touching the metatheory.

## On the typeclass split question

I investigated three approaches to avoid the hybrid ND using typeclasses. None can eliminate it without duplicating the formula type. Lean 4's inductive type system does not support conditionally-available constructors: you cannot make `efq` a constructor of `Derivation` only when a typeclass is satisfied. Options B (split at `Derivation` level) and C (typeclass on connectives) both collapse back to either the current design or Thomas's Option A (separate `IDerivation`). Matthew, your concern about conservative extension proofs is well-founded: with separate formula types, `IPL is conservative over MPL` becomes a theorem about a translation function rather than a subset relation on derivations, which is harder to state cleanly.

Thomas, your `IProposition`/`IDerivation` branch demonstrates that the translation is mechanically possible — `propEquiv`, `toDerivation`, and `toIDerivation` all compile, and the translations are proved correct. This is valuable as a reference. But the `noncomputable toIDerivation` direction (which uses `Classical.choose`) means you cannot compute with intuitionistic derivations built by translation, and the maintenance cost of the duplication table above is prohibitive for CSLib's architecture.

## On the docstring deletion — and a direct apology

You asked: "btw Benjamin, why did you delete that part of the docstring in `NaturalDeduction/Basic`?"

The deletion was a mistake during the ND overhaul (commit `80f54485`, task 173) which removed the `botE` constructor and added six rules and treated the docstring as a clean-slate rewrite. The `## Implementation notes` section has been restored with your original framing (plus an expanded explanation of the trade-off). All four of your original references are back, along with a link to this thread.

## Closing

Thomas, CSLib's propositional logic foundation builds directly on your work. The `Theory.Derivation` type originated in your PR #91, `AlgEvaluate` was inspired by your GHA evaluation suggestion, and `AlgTValid` implements your `v models T` parametric completeness style by name. That foundation is strong and I'm grateful for it.

I recognize you've held off PRs from your branches while this discussion was unresolved. I'd very much like to continue the collaboration — whether through reviewing specific parts of PR #648, merging something from your `kripke` or `hilbert` branches, or working through the DPLL layer with Matthew. Thank you both for the patience and care you've put into this thread.
