# Modal Axiom-Schema Architecture

## Overview

CSLib's modal-logic layer formalizes 15 classical normal modal systems — K, T, D, B (a.k.a. KB),
K4, K5, K45, S4, S5, TB, KB5, D4, D5, D45, DB — each as a Hilbert-style proof system over a
shared propositional/modal `Proposition` language. Historically each system's axiom predicate was
a bespoke, hand-written `inductive <Sys>Axiom` with its own 13-18 constructors, byte-identical to
its siblings on the shared propositional/K/and-or/diamond-duality core and differing only in
which modal-strength schemata (`T`, `D`, `B`, `4`, `5`) it admits. This document describes the
compositional architecture that replaced those hand-written inductives: **15 classical normal
modal systems, unified under 14 renamed `<Sys>Axiom` abbreviations plus S5's pre-existing
`ModalAxiom`**, all expressed as one-line `abbrev`s over a single combinator, `SchemaUnion`, and
a single 18-tag alphabet, `ModalSchemaTag`.

The architecture rests on two libraries acting as two halves of one abstraction:

- **`Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`** (+ `SchemaTags.lean`) — the *syntactic*
  side: the tag alphabet, the existential "schema = set of instances" meaning function, the
  `SchemaUnion` combinator, and the generic subsumption/elimination lemmas that make the modal
  cube's `⊆`-order a `decide`-able computation on `Finset ModalSchemaTag` values.
- **`Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`** (+ `SchemaSoundness.lean`) — the
  *semantic* side: the five frame-condition-to-validity correspondence lemmas for the
  modal-strength differentiators, and the single master soundness lemma, `unionSound`, that
  hinges the two sides together.

Two payoffs fall out of this design directly: **subsumption** collapses from 24 hand-written
per-edge lemmas to one generic `SchemaUnion.subsumption` application discharged by `decide`-able
`Finset.subset` facts, and **soundness** collapses from 15 per-system case-splits to one
`unionSound` application consuming an 18-entry `FrameValidatesTag` table plus the five
frame-correspondence lemmas.

This document covers seven areas, each anchored to real module paths, def/lemma/typeclass names,
and Lean signatures verified against the landed, CI-green code:

1. [The Schema-Tag Alphabet](#1-the-schema-tag-alphabet-modalschematag-holds-and-schemaunion) —
   `ModalSchemaTag`, `.Holds`, and the `SchemaUnion` combinator.
2. [Subsumption as `Finset.subset`](#2-subsumption-as-finsetsubset-the-syntactic-modal-cube) —
   the modal cube as a decidable tag-set computation, and its disambiguation from the
   pre-existing semantic frame-class cube.
3. [`unionSound`: The Syntax/Semantics Hinge](#3-unionsound-the-syntaxsemantics-hinge) —
   compositional soundness via the `FrameCorrespondence` library.
4. [The `HasAxiom*` Insulation Layer](#4-the-hasaxiom-insulation-layer) — why the refactor had
   zero blast radius above the axiom-predicate layer.
5. [S5 = T+4+B](#5-s5--t4b-the-deliberately-omitted-kb5s5-edge) — the disposition of S5's tag set
   and the deliberately omitted KB5→S5 edge.
6. [Design Rationale](#6-design-rationale-representation-a-vs-representation-b) — Representation
   A (chosen) vs. Representation B (rejected).
7. [Scope Boundary](#7-scope-boundary-a-future-instance-not-a-fork) — why the
   intuitionistic/minimal families are a future instance of this abstraction, not a fork.

---

## 1. The Schema-Tag Alphabet: `ModalSchemaTag`, `.Holds`, and `SchemaUnion`

**Durable anchor**: `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`

Every one of the 15 classical normal modal systems' axiom set is built from the same finite
vocabulary of axiom *schemata*. `ModalSchemaTag` names that vocabulary as an 18-constructor
alphabet:

```lean
inductive ModalSchemaTag
  | implyK | implyS | efq | peirce | modalK
  | modalT | modalD | modalB | modalFour | modalFive
  | andI | andE1 | andE2 | orI1 | orI2 | orE
  | diaDualityFwd | diaDualityBack
  deriving DecidableEq
```

The 18 tags group into five roles (4 + 1 + 5 + 6 + 2 = 18):

- **4 propositional-core tags**: `implyK`, `implyS`, `efq`, `peirce`.
- **1 K-distribution tag**: `modalK`.
- **5 modal-strength differentiator tags**: `modalT`, `modalD`, `modalB`, `modalFour`,
  `modalFive` — these are the only tags that vary from system to system.
- **6 and/or tags**: `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`.
- **2 diamond-duality tags**: `diaDualityFwd`, `diaDualityBack`.

A tag by itself is just a label; `ModalSchemaTag.Holds` gives each tag its formula-level meaning
as an existential over the schema's metavariables — the "schema = set of its instances" encoding.
A representative excerpt (18 clauses total, one per tag, each shaped `∃ (metavariables), χ =
(schema instance)`):

```lean
def ModalSchemaTag.Holds : ModalSchemaTag → Proposition Atom → Prop
  | .implyK, χ => ∃ φ ψ : Proposition Atom, χ = φ.imp (ψ.imp φ)
  | .modalT, χ => ∃ φ : Proposition Atom, χ = (Proposition.box φ).imp φ
  | .modalB, χ => ∃ φ : Proposition Atom, χ = Axioms.AxiomB φ
  -- … 15 further clauses, one per remaining tag
```

Every clause's proposition shape matches, byte-for-byte, the corresponding constructor of the
pre-existing per-system axiom inductives, which is what makes it possible to replace those
inductives with a single combinator, `SchemaUnion`, parametrized by a chosen `Finset` of tags:

```lean
def SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop :=
  fun χ => ∃ t ∈ S, t.Holds χ
```

`SchemaUnion S χ` holds iff `χ` is an instance of some tag in `S`. Because the tag alphabet is
finite and carries `DecidableEq`, choosing `S` to be a concrete `Finset` literal turns each
system's axiom predicate into a one-line declaration. Fourteen of the fifteen systems now read
`abbrev <Sys>Axiom := SchemaUnion sysTags` in
`Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,TB,KB5,D4,D5,D45,DB}.lean` — for
example `abbrev KAxiom : Proposition Atom → Prop := SchemaUnion kTags` in `Instances/K.lean` and
`abbrev KB5Axiom : Proposition Atom → Prop := SchemaUnion kb5Tags` in `Instances/KB5.lean`. S5 is
not a structural exception to this pattern: `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`
line 69 reads exactly

```lean
abbrev ModalAxiom : Proposition Atom → Prop := SchemaUnion s5Tags
```

so `ModalAxiom` is the 15th system folded into the same one-line-abbrev-over-`SchemaUnion`
pattern as the other 14 — its name and public API are preserved by redefinition-in-place, and
`Instances/S5.lean`'s "reuses the existing `ModalAxiom` type" docstring describes exactly this:
S5 goes through `SchemaUnion` transitively via `ModalAxiom`, without needing to spell
`SchemaUnion` by name in its own file.

Alongside the combinator, three `@[simp]` elimination lemmas give the ergonomic half of the
design — a concrete `SchemaUnion sysTags φ` obligation rewrites via `simp` into the named
disjunction of its tags' `.Holds` clauses, rather than requiring raw `fin_cases` destructuring at
every call site:

```lean
theorem SchemaUnion.empty_iff {φ : Proposition Atom} :
    SchemaUnion (∅ : Finset ModalSchemaTag) φ ↔ False

theorem SchemaUnion.insert_iff {t : ModalSchemaTag} {S : Finset ModalSchemaTag}
    {φ : Proposition Atom} :
    SchemaUnion (insert t S) φ ↔ t.Holds φ ∨ SchemaUnion S φ

theorem SchemaUnion.union_iff {Sa Sb : Finset ModalSchemaTag} {φ : Proposition Atom} :
    SchemaUnion (Sa ∪ Sb) φ ↔ SchemaUnion Sa φ ∨ SchemaUnion Sb φ
```

**Durable anchors for this section**: `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`
(`ModalSchemaTag`, `ModalSchemaTag.Holds`, `SchemaUnion`, the three `@[simp]` elimination
lemmas), `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (`ModalAxiom`, line 69),
`Cslib/Logics/Modal/ProofSystem/Instances/{K,…,S5}.lean` (the 15 per-system instance-registration
files).
