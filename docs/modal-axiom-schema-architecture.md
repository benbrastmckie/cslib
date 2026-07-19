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

---

## 2. Subsumption as `Finset.subset`: The Syntactic Modal Cube

**Durable anchors**: `SchemaUnion.subsumption` (in
`Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`),
`Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (the 15 per-system tag sets),
`Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` (the 24 direct-edge lemmas).

The modal cube — the familiar inclusion order K ⊂ T ⊂ S4 ⊂ S5, and its 11 further systems and
their edges — used to be witnessed by 24 hand-written, per-edge subsumption lemmas, each proved
by a bespoke case analysis over the source system's axiom inductive. `SchemaUnion` replaces all
24 with one generic lemma:

```lean
theorem SchemaUnion.subsumption {Sa Sb : Finset ModalSchemaTag} (hsub : Sa ⊆ Sb)
    {φ : Proposition Atom} (h : SchemaUnion Sa φ) : SchemaUnion Sb φ
```

Enlarging the tag set only weakens the resulting predicate — the proof is three lines
(`obtain ⟨t, ht, hφ⟩ := h; exact ⟨t, hsub ht, hφ⟩`). Every `XAxiom_implies_YAxiom` lemma across
the cube is now `SchemaUnion.subsumption (by decide) h`: a `decide`-able `Finset.subset` fact,
discharged automatically because `ModalSchemaTag` is a finite `DecidableEq` type and every
system's tag set is a concrete `Finset` literal built from `insert`/`kCore`. This is the
framing point of the whole design: **the modal cube's `⊆`-order IS the `⊆`-order on tag sets** —
subsumption is no longer a proved fact about 15 independent inductives, it is a computation on
15 `Finset` values.

The 15 per-system tag sets (`SchemaTags.lean`) are each the shared 13-tag core, `kCore`, unioned
with a subset of the 5 modal-strength differentiator tags:

```lean
def kCore : Finset ModalSchemaTag :=  -- 13 tags: implyK, implyS, efq, peirce, modalK,
  …                                    -- andI, andE1, andE2, orI1, orI2, orE,
                                        -- diaDualityFwd, diaDualityBack
def kTags   : Finset ModalSchemaTag := kCore
def tTags   : Finset ModalSchemaTag := insert .modalT kCore
def dTags   : Finset ModalSchemaTag := insert .modalD kCore
def bTags   : Finset ModalSchemaTag := insert .modalB kCore                              -- KB
def k4Tags  : Finset ModalSchemaTag := insert .modalFour kCore
def k5Tags  : Finset ModalSchemaTag := insert .modalFive kCore
def k45Tags : Finset ModalSchemaTag := insert .modalFour (insert .modalFive kCore)
def s4Tags  : Finset ModalSchemaTag := insert .modalT (insert .modalFour kCore)
def s5Tags  : Finset ModalSchemaTag := insert .modalT (insert .modalFour (insert .modalB kCore))
def tbTags  : Finset ModalSchemaTag := insert .modalT (insert .modalB kCore)
def kb5Tags : Finset ModalSchemaTag := insert .modalB (insert .modalFive kCore)
def d4Tags  : Finset ModalSchemaTag := insert .modalD (insert .modalFour kCore)
def d5Tags  : Finset ModalSchemaTag := insert .modalD (insert .modalFive kCore)
def d45Tags : Finset ModalSchemaTag := insert .modalD (insert .modalFour (insert .modalFive kCore))
def dbTags  : Finset ModalSchemaTag := insert .modalD (insert .modalB kCore)
```

The 24 direct edges in `AxiomSubsumption.lean` — each now a one-line `SchemaUnion.subsumption (by
decide) h` proof, where previously each was a hand-written per-edge `match`/`cases` lemma — are:

- From K: K→T, K→D, K→B(KB), K→K4, K→K5 (5 edges)
- From D: D→D4, D→D5, D→DB (3 edges)
- From T: T→S4, T→TB (2 edges)
- From B(KB): B→TB, B→DB, B→KB5 (3 edges)
- From K4: K4→S4, K4→D4, K4→K45 (3 edges)
- From K5: K5→D5, K5→K45, K5→KB5 (3 edges)
- From K45: K45→D45 (1 edge)
- From D4: D4→D45 (1 edge)
- From D5: D5→D45 (1 edge)
- Into S5: S4→`ModalAxiom` (S5), TB→`ModalAxiom` (S5) (2 edges)

Total: 5+3+2+3+3+3+1+1+1+2 = 24.

### Disambiguation: this is not `Cslib/Logics/Modal/Cube.lean`

CSLib has a second, pre-existing artifact also called "the modal cube":
`Cslib/Logics/Modal/Cube.lean` defines each classical system as a **semantic** frame-class — a
`Set (Model World Atom)` characterized by a frame property, e.g.

```lean
def T World Atom := logic {m : Model World Atom | Std.Refl m.r}
```

`Cube.lean` was authored for a different purpose (the semantic frame-class cube) and predates the
schema-union combinator. **It must not be conflated with the syntactic tag-set cube described in
this section** (`AxiomSubsumption.lean` / `SchemaTags.lean`, over `Finset ModalSchemaTag`). The
two are independent "modal cube" artifacts living side by side in the codebase:

| Artifact | File | Kind | Each system is a… |
|---|---|---|---|
| Semantic frame-class cube | `Cslib/Logics/Modal/Cube.lean` | pre-existing, frame-based | `Set (Model World Atom)` |
| Syntactic tag-set cube | `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` + `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` | new, proof-theoretic | `Finset ModalSchemaTag` |

This document is about the syntactic tag-set cube only.

---

## 3. `unionSound`: The Syntax/Semantics Hinge

**Durable anchors**: `unionSound`, `FrameValidatesTag` (both in
`Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean`); `Satisfies.modalT_axiom`,
`Satisfies.modalFour_axiom`, `Satisfies.modalB_axiom`, `Satisfies.modalD_axiom`,
`Satisfies.modalFive_axiom` (in `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`).

Subsumption is the syntactic collapse; soundness is the semantic one. Just as the 24 subsumption
edges collapse to one generic lemma, the 15 systems' soundness proofs collapse to one master
lemma, `unionSound`, built on a small reusable library of frame-condition-to-validity
correspondence facts.

**The five frame-correspondence lemmas** (`FrameCorrespondence.lean`) each show that a
modal-strength differentiator axiom is valid on any model whose accessibility relation satisfies
the matching frame condition:

```lean
lemma Satisfies.modalT_axiom {World : Type*} (m : Model World Atom)
    (h_refl : ∀ w, m.r w w) (w : World) (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box φ) φ)

lemma Satisfies.modalFour_axiom {World : Type*} (m : Model World Atom)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) (w : World)
    (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))

lemma Satisfies.modalB_axiom {World} (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) (w) (φ) : Satisfies m w (Axioms.AxiomB φ)

lemma Satisfies.modalD_axiom {World} (m : Model World Atom) (h_serial : Relation.Serial m.r) (w) (φ) :
    Satisfies m w (Proposition.imp (Proposition.box φ)
      (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))

lemma Satisfies.modalFive_axiom {World} (m : Model World Atom)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) (w) (φ) :
    Satisfies m w (((Proposition.box (φ.imp .bot)).imp .bot).imp
      (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))
```

Each lemma's docstring records its provenance verbatim against Blackburn, de Rijke, and Venema's
*Modal Logic* (Cambridge, 2001), Chapter 4, Definition 4.9 and Table 4.1 — the standard reference
for modal frame correspondence — and against the per-system soundness proofs the correspondence
facts were extracted from.

**`FrameValidatesTag`** packages the semantic obligation uniformly over all 18 tags: `True` for
the 13 frame-unconditional tags, and exactly the frame-condition hypothesis for the 5
differentiators — a deliberate design choice that keeps the interface `unionSound` consumes
uniform, so the 13 trivial obligations discharge by `trivial` rather than requiring a type-level
conditional split:

```lean
def FrameValidatesTag {World} (m : Model World Atom) : ModalSchemaTag → Prop
  | .modalT => ∀ w, m.r w w
  | .modalD => Relation.Serial m.r
  | .modalB => ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁
  | .modalFour => ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃
  | .modalFive => ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃
  | .implyK | .implyS | .efq | .peirce | .modalK
  | .andI | .andE1 | .andE2 | .orI1 | .orI2 | .orE
  | .diaDualityFwd | .diaDualityBack => True
```

**`unionSound`** is the master combinator — the hinge itself:

```lean
theorem unionSound {World : Type*} (S : Finset ModalSchemaTag) (m : Model World Atom)
    (hfc : ∀ t ∈ S, FrameValidatesTag m t) {φ : Proposition Atom} (h : SchemaUnion S φ)
    (w : World) : Satisfies m w φ
```

Its proof is a single `cases t with` over all 18 tags. The 13 frame-unconditional cases reuse the
existing validity atoms in `Cslib/Logics/Modal/Metalogic/Soundness.lean`
(`Satisfies.implyK_axiom`, …, `Satisfies.diaDualityBack_axiom`) read-only, and the 5
differentiator cases each delegate directly to the corresponding `FrameCorrespondence` lemma
above (e.g. `exact Satisfies.modalT_axiom m hval w φ'`) rather than re-deriving the frame
argument inline.

Put plainly: the frame-correspondence library (the semantic side) and the schema-union
combinator (the syntactic side) are two halves of one abstraction, and `unionSound` is the hinge
between them — every per-system soundness proof specializes this one lemma instead of
re-deriving a per-system case-split.

**Durable anchors for this section**: `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`
(the five `Satisfies.modal*_axiom` lemmas), `Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean`
(`FrameValidatesTag`, `unionSound`), `Cslib/Logics/Modal/Metalogic/Soundness.lean` (the 13
frame-unconditional validity atoms `unionSound` reuses).

---

## 4. The `HasAxiom*` Insulation Layer

**Durable anchor**: `Cslib/Foundations/Logic/ProofSystem.lean`

Everything in Sections 1-3 lives at the *axiom-predicate* layer: the definition of which
`Proposition` instances count as axioms for a given system. A separate, higher layer —
`Cslib/Foundations/Logic/ProofSystem.lean` — defines one `HasAxiom*` typeclass per schema
(`HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, `HasAxiomK`, `HasAxiomT`,
`HasAxiom4`, `HasAxiomB`, `HasAxiom5`, `HasAxiomD`, the and/or family
`HasAxiomAndI`/`AndE1`/`AndE2`/`OrI1`/`OrI2`/`OrE`, and `HasAxiomDiaDualityFwd`/`Back`, plus
non-modal and temporal `HasAxiom*` classes outside this document's scope). A representative
signature:

```lean
class HasAxiomT where
  T {φ : F} : InferenceSystem.DerivableIn S (Axioms.AxiomT φ)
```

Crucially, `HasAxiomT` asserts *derivability of the axiom instance* (`InferenceSystem.DerivableIn
S (Axioms.AxiomT φ)`) — it says nothing about *how the underlying `<Sys>Axiom` predicate is
constructed*. These typeclasses are bundled via `extends` into a hierarchy of Hilbert-system
classes: `MinimalHilbert` extends into `IntuitionisticHilbert`, which extends into
`ClassicalHilbert`, which extends into `ModalHilbert`; `ModalHilbert` is then extended by one
class per modal-strength differentiator or combination (`ModalTHilbert`, `ModalDHilbert`,
`ModalBHilbert`, `ModalK4Hilbert`, `ModalK5Hilbert`), and those in turn are extended by the
composite systems (`ModalS4Hilbert` extends `ModalTHilbert`; `ModalK45Hilbert` extends
`ModalK4Hilbert`; `ModalTBHilbert`, `ModalKB5Hilbert`, `ModalD4Hilbert`, `ModalD5Hilbert`,
`ModalDBHilbert` each extend their respective single-differentiator ancestor; `ModalD45Hilbert`
extends `ModalD4Hilbert`), up to `ModalS5Hilbert` extending `ModalS4Hilbert`.

**Why this is "representation-agnostic insulation"**, not merely asserted but verified in the
landed code: `Instances/S5.lean` discharges `HasAxiomT` for `Modal.HilbertS5` by constructing a
`DerivationTree` witness,

```lean
instance : HasAxiomT Modal.HilbertS5 (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _ (⟨.modalT, by decide, _, rfl⟩)⟩
```

i.e. a tag-membership proof (`.modalT ∈ s5Tags`, discharged by `decide`) plus a `.Holds` witness.
`HasAxiomT` itself never inspects whether the underlying `<Sys>Axiom` predicate is a bespoke
`inductive` or a `SchemaUnion` combinator — it only ever requires a `DerivableIn` proof. This is
the load-bearing property that made the `SchemaUnion` refactor additive with zero blast radius at
every downstream consumer: the `Systems/*/Completeness.lean` and
`Systems/*/ConservativeExtension.lean` layers (one file per system apiece) route exclusively
through this `HasAxiom*`/bundled-class layer, so replacing 14 inductives with `SchemaUnion`
abbreviations left them untouched.

**Durable anchors for this section**: `Cslib/Foundations/Logic/ProofSystem.lean` (`HasAxiomT`,
the full `HasAxiom*` family, `MinimalHilbert` … `ModalS5Hilbert`), `Instances/S5.lean` (the
`HasAxiomT` instance witness).

---

## 5. S5 = T+4+B: The Deliberately Omitted KB5→S5 Edge

**Durable anchors**: `s5Tags`, `kb5Tags` (`SchemaTags.lean`), the omission note in
`AxiomSubsumption.lean`.

S5's tag set is exactly the K-core plus three differentiators — T, 4, and B:

```lean
def s5Tags  : Finset ModalSchemaTag := insert .modalT (insert .modalFour (insert .modalB kCore))
```

i.e. `kCore ∪ {modalT, modalFour, modalB}`. Notably, `s5Tags` does **not** contain `modalFive`.
KB5's tag set, by contrast, is:

```lean
def kb5Tags : Finset ModalSchemaTag := insert .modalB (insert .modalFive kCore)
```

i.e. `kCore ∪ {modalB, modalFive}` — it carries `modalFive` but neither `modalT` nor `modalFour`.

Because `modalFive ∈ kb5Tags` and `modalFive ∉ s5Tags`, `kb5Tags ⊆ s5Tags` is false: no
`Finset.subset` proof exists, and `decide` on that proposition reports `False`. Consequently
`SchemaUnion.subsumption` cannot produce a `KB5Axiom_implies_ModalAxiom` lemma, and none exists in
`AxiomSubsumption.lean`. This is not an oversight — it is a mechanical, decidable consequence of
the two tag-set definitions, and `AxiomSubsumption.lean`'s own documentation states the omission
explicitly alongside the 24 edges that do hold.

This is a useful worked example of the design's self-documenting property: under the old
per-edge hand-lemma design, a missing cube edge required a separate written justification. Under
the tag-set design, a missing edge is immediately explained by inspecting two `Finset` literals —
the gap is readable straight from the definitions, and any attempt to manufacture the missing
edge fails at `decide` rather than at proof-search.

**Durable anchors for this section**: `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean`
(`s5Tags`, `kb5Tags`), `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` (the
KB5→S5 omission note).

---

## 6. Design Rationale: Representation A vs. Representation B

This design was one of two candidate representations considered for replacing the 14 bespoke
per-system axiom inductives (plus S5's pre-existing `ModalAxiom`) with a single reusable
abstraction.

**Representation A (chosen)** — the architecture described in Sections 1-5: a schema-tag `def`
(`ModalSchemaTag`), an existential `.Holds` meaning function, and a `SchemaUnion (S : Finset
ModalSchemaTag)` combinator parametrized by concrete `Finset` literals per system.

**Representation B (rejected, never implemented in this codebase)** — keep the per-system
`inductive <Sys>Axiom` shape, but generate each one via a macro/elaborator over a tag list (e.g.
a hypothetical `derive_modal_axiom KAxiom [implyK, implyS, efq, peirce, modalK, andCore, orCore,
diaDuality]`), so constructor names and elimination form (`cases h_ax with | implyK … `) would be
preserved verbatim at every call site.

**The trade-off**:

- **Representation A wins on three fronts.** (a) Subsumption collapses from 24 hand-written
  lemmas to one generic `SchemaUnion.subsumption` application plus `decide`-able `Finset.subset`
  facts (Section 2). (b) Soundness collapses from 15 per-system case-splits to one `unionSound`
  application plus an 18-entry validity table (Section 3). (c) The 13-line
  propositional/K/and-or/diamond-duality core no longer needs re-listing per system — it lives
  once, in `kCore`. The migration to Representation A ended up net line-negative in the actual
  landed diff (more lines deleted than added) — the DRY gains outweighed the one-time migration
  cost.
- **Representation A costs.** The *elimination form* changes at every downstream destructuring
  site: `cases h_ax with | implyK … | modalK …` becomes `obtain ⟨t, ht, hφ⟩ := h_ax; fin_cases t
  <;> …`. This cost is substantially tamed by the `SchemaUnion.{empty,insert,union}_iff`
  `@[simp]` elimination API described in Section 1, which turns most such sites into named `simp`
  rewrites rather than raw `fin_cases` destructuring.
- **Representation B wins on migration safety.** Its near-zero downstream blast radius — every
  existing `cases`/`match` site keeps typechecking unchanged — and it delivers the literal DRY
  goal (no re-listing at the source) without touching call sites at all.
- **Representation B costs.** It does not deliver the set-theoretic subsumption-as-`⊆` or
  soundness-as-per-tag-table properties: cross-inductive subsumption would stay an
  O(edges)-sized set of proofs even if each were macro-generated, since the elimination form
  (bespoke inductive constructors) still differs system to system. It also adds metaprogramming
  maintenance burden and is less transparent/auditable to a reviewer than a plain `def`.

**Why Representation A was chosen for long-term foundations**: the goal was durable architecture,
not merely a DRY-er restatement of the same 24+15 previously-independent facts. Representation A
is the only one of the two that makes the modal cube's algebraic structure — a lattice of finite
tag sets under `⊆` — directly visible and machine-checkable in the type theory itself, rather
than hiding the same bespoke facts behind macro-generated syntax. Representation B optimizes for
short-term migration safety; Representation A optimizes for the property this whole document
exists to describe: that subsumption and soundness are *literally* computations on `Finset
ModalSchemaTag`, not just refactored restatements of previously-independent facts.

---

## 7. Scope Boundary: A Future Instance, Not a Fork

**Durable anchor**: the "Design Invariants" section of
`Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`'s module docstring.

`ModalSchemaTag` and `SchemaUnion` were built for the 15 *classical* normal modal systems only.
The module docstring states the scope boundary explicitly as a design invariant:

> `ModalSchemaTag` / `SchemaUnion` stay free of classical-only assumptions: the
> intuitionistic/minimal axiom families are a possible future instance of this same abstraction,
> not generalized to cover them here (out of scope for this task).

CSLib already has intuitionistic and minimal modal axiom families that exist today and were
deliberately kept out of this design's scope: `IKModalAxiom` and `IS5ModalAxiom`
(`Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` and
`Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5.lean`), `CKModalAxiom`
(`Cslib/Logics/Modal/Metalogic/Constructive/CK.lean`), and `MKModalAxiom` and `MTModalAxiom`
(`Cslib/Logics/Modal/Metalogic/Minimal/MK.lean` and
`Cslib/Logics/Modal/Metalogic/Minimal/MT.lean`). These families construct witnesses *into* the
classical `KAxiom`/`ModalAxiom` predicates — cross-family coupling lives in
`Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean` — so their existing call sites had
to keep typechecking unchanged through the refactor described in this document. Nothing about
*their own* internal representation was touched or generalized.

The "future instance, not a fork" framing is the key point: if intuitionistic/minimal schema-union
support is ever wanted, the correct move is to extend or parametrize the existing
`ModalSchemaTag`/`SchemaUnion` shape — for instance by widening the tag alphabet or adding a
parameter distinguishing classical from constructive instances of a tag's meaning — not to build
an independent, parallel `IntSchemaTag`/`IntSchemaUnion` pair from scratch. Keeping
`ModalSchemaTag`/`SchemaUnion` free of classical-only assumptions today is precisely what keeps
that future extension a natural generalization of this same architecture, rather than a
second, incompatible cube living alongside it.

**Durable anchors for this section**: `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` (Design
Invariants docstring), `Cslib/Logics/Modal/Metalogic/Intuitionistic/{IK,IS5}.lean`,
`Cslib/Logics/Modal/Metalogic/Constructive/CK.lean`,
`Cslib/Logics/Modal/Metalogic/Minimal/{MK,MT}.lean`,
`Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`.
