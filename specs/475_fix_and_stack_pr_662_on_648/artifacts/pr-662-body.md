Refactors the modal formula type to the primitive set `{atom, bot, imp, box}` and builds out the modal cube and logical equivalence over it.

The original PR mixed this with propositional-logic changes and was large to review. Per reviewer feedback it is now slimmed to the modal layer only — a single commit touching the files below — and builds independently on `main`.

### Files Changed

**`Cslib/Logics/Modal/Basic.lean`** (modified)

`Modal.Proposition` uses `{atom, bot, imp, box}` as primitives; negation, conjunction, disjunction and diamond are derived (`◇φ := ¬□¬φ`). Box is kept primitive so necessitation and the K axiom stay pure rules on a single operator. Proves each of K/T/B/4/5/D valid under its frame condition, with canonicity (the condition is also necessary) for T/B/4/5/D. Diamond's derivation is classical-only; a primitive `HasDia` for intuitionistic/minimal modal logic is noted as future work.

**`Cslib/Logics/Modal/Cube.lean`** (modified)

Assembles the fifteen named logics of the modal cube (K, T, B, 4, 5, D, D4, D5, D45, DB, TB, KB5, S4, S5, K45) as axiom-set unions over the relevant model classes, and proves the standard cube inclusions.

**`Cslib/Logics/Modal/LogicalEquivalence.lean`** (modified)

Defines `Proposition.Equiv S`, parametric in the model class `S`, so equivalence can be stated relative to any modal-cube class (T/B/4/5/S4/S5, …) rather than only the class of all models. Proved to be an equivalence relation and a congruence over one-hole contexts, and registered into the shared `Cslib.Foundations.Logic.LogicalEquivalence` framework.

**`Cslib/Logics/Modal/Denotation.lean`** (modified)

Semantics/denotation for the new primitive set.

**`Cslib/Foundations/Logic/Connectives.lean`** (new file)

A small operator-typeclass hierarchy — `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, bundled into `PropositionalConnectives` and `ModalConnectives`. This follows the one-class-per-operator direction of #607, but is self-owned here rather than depending on #607, which is not yet merged and does not currently carry `HasBot`/the bundled classes. Folding this onto #607's hierarchy once it lands is left to a follow-up.

**`references.bib`** (modified)

Adds `Avigad2022` and `ChagrovZakharyaschev1997` for the sources cited in the modal files.

**`Cslib.lean`, `CslibTests/GrindLint.lean`** (modified)

Module registration for the above, plus `#grind_lint skip` entries for the four new `@[scoped grind]` modal lemmas (the same mechanism already used by `Cslib.Logic.HML`).

## AI Disclosure

Claude (Anthropic) assisted with the rebase, file selection, and CI verification. The Lean proofs are by the contributors listed in the file headers; AI use was limited to mechanical git work and drafting this description.
