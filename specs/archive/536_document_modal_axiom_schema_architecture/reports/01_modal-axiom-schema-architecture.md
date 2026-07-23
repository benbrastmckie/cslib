# Research Report: Task #536

**Task**: 536 - Document the modal axiom-schema architecture in a new docs/ directory
**Started**: 2026-07-19T16:18:31Z
**Completed**: 2026-07-19T17:05:00Z
**Effort**: ~2 hours (research only)
**Dependencies**: 523 (schema-union axiom combinator; status: completed)
**Sources/Inputs**:
- Codebase: `Cslib/Logics/Modal/ProofSystem/{SchemaUnion,SchemaTags}.lean`,
  `Cslib/Logics/Modal/Metalogic/{FrameCorrespondence,SchemaSoundness}.lean`,
  `Cslib/Foundations/Logic/ProofSystem.lean`,
  `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean`,
  `Cslib/Logics/Modal/ProofSystem/Instances/{K,S5,KB5}.lean`, `Cslib/Logics/Modal/Cube.lean`
- `specs/523_schema_union_axiom_combinator_for_proofsystem_instances/reports/01_schema-union-combinator-blast-radius.md`
- `specs/523_schema_union_axiom_combinator_for_proofsystem_instances/plans/02_schema-union-per-file-rollout.md`
- `specs/523_schema_union_axiom_combinator_for_proofsystem_instances/plans/01_schema-union-staged-rollout.md`
- `specs/523_schema_union_axiom_combinator_for_proofsystem_instances/summaries/07_phase8-redefine-in-place-final-completion-summary.md`
- `specs/state.json` (task 523's completion_summary and original description)
**Artifacts**: this report
**Standards**: report-format.md, subagent-return.md, `.claude/rules/no-task-references-in-deliverables.md`

## Executive Summary

- Task 523 (status: completed) landed exactly the architecture task 536 must document: a
  compositional `SchemaUnion` combinator over an 18-tag `ModalSchemaTag` alphabet, replacing 14
  hand-written per-system axiom inductives (K, T, D, B/KB, K4, K5, K45, S4, TB, KB5, D4, D5, D45,
  DB) plus S5's pre-existing `ModalAxiom`, and pairing with the already-landed
  `FrameCorrespondence.lean` (5 frame-condition→validity lemmas) via a hinge lemma `unionSound`.
  All source code is on disk and verified (see counts and signatures below).
- **The "18-tag alphabet" claim is verified exactly**: `ModalSchemaTag` (in
  `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`) has exactly 18 constructors, confirmed by
  direct read and by counting `deriving DecidableEq` bounds. Listed in full in Finding 1 below.
- **The S5 = T+4+B / omitted KB5→S5 edge is verified exactly**: `s5Tags = kCore ∪ {modalT,
  modalFour, modalB}` (no `modalFive`); `kb5Tags = kCore ∪ {modalB, modalFive}`. Since
  `modalFive ∈ kb5Tags` but `modalFive ∉ s5Tags`, `kb5Tags ⊆ s5Tags` is false, so no
  `KB5Axiom_implies_ModalAxiom`/`S5Axiom` lemma exists or can exist under this design — confirmed
  both by inspecting the tag-set defs and by the explicit doc comment in
  `InterSystem/AxiomSubsumption.lean` and the Phase 8 completion summary.
- Representation A (schema-tag `def` + `Finset` union) was chosen over Representation B
  (macro-generated inductives) via an explicit, recorded maintainer design decision (state.json
  task 523: "DESIGN DECISION (resolved, user 2026-07-18): Representation = A"); the blast-radius
  report and plan v2's "Postmortem Constraints" section give the full rationale trade-off, which
  the final document should present without citing the task number (see Constraint section below).
- One count discrepancy to resolve carefully in the final document: the task-536 description
  and much of the older task-523 prose say "15 hand-written per-system axiom inductives", but
  task 523's own **reconciled** count (recorded in `state.json`'s description field) is **14**
  distinct `<Sys>Axiom` inductives (`K,T,B,D,S4,K4,K5,K45,D4,D5,D45,DB,TB,KB5`) plus **S5's
  pre-existing `ModalAxiom`** (which was not a new bespoke inductive being introduced by this
  refactor — it already existed and is *reused*, not replaced, by `S5.lean`). The docs/ writer
  should use "15 classical normal modal systems, unified under 14 renamed `<Sys>Axiom` abbrevs
  plus S5's `ModalAxiom`" or similar precise phrasing rather than "15 inductives".

## Context & Scope

This is a research-only pass for a `markdown` documentation task whose deliverable (a
`docs/` architecture document, not yet written) must explain the compositional design
`SchemaUnion` + `FrameCorrespondence` establish, using durable code anchors (module paths,
def/lemma/typeclass names) rather than task numbers. `docs/` does not yet exist in the repo root
(confirmed: `ls docs/` — not found; repo root has `CONTRIBUTING.md`, `NOTATION.md`,
`ORGANISATION.md`, `README.md` as its existing top-level prose/standards files, but no `docs/`
directory). The planner/implementer will need to create it.

Task 523's dependency is `[COMPLETED]` (confirmed via `specs/state.json`), so all code referenced
below is real, landed, CI-green code — not aspirational/planned code. The `SchemaUnion.lean` file
path in the task-536 description ("SchemaUnion.lean" was mentioned as possibly not matching what's
on disk) **does exist exactly as named** at
`Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` — the task description's uncertainty
("the directory only shows SchemaSoundness.lean") was stale; both files exist side by side, plus
a third landed file `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (per-system tag-set
definitions) that the task description did not anticipate but which is essential to areas 1, 2,
and 5.

## Findings

### Area 1 — `ModalSchemaTag` (18-tag alphabet), `.Holds`, `SchemaUnion` combinator

**Durable anchor**: `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`

**Verified tag count — exactly 18**, in `namespace Cslib.Logic.Modal`:
```lean
inductive ModalSchemaTag
  | implyK | implyS | efq | peirce | modalK
  | modalT | modalD | modalB | modalFour | modalFive
  | andI | andE1 | andE2 | orI1 | orI2 | orE
  | diaDualityFwd | diaDualityBack
  deriving DecidableEq
```
Grouped by role (this grouping itself is a durable design fact worth reproducing in the doc):
- **4 propositional core tags**: `implyK`, `implyS`, `efq`, `peirce`
- **1 K-distribution tag**: `modalK`
- **5 modal-strength differentiator tags**: `modalT`, `modalD`, `modalB`, `modalFour`, `modalFive`
- **6 and/or tags**: `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`
- **2 diamond-duality tags**: `diaDualityFwd`, `diaDualityBack`
(4+1+5+6+2 = 18, confirmed.)

**`.Holds` — the existential "schema = set of instances" encoding**, signature:
```lean
def ModalSchemaTag.Holds : ModalSchemaTag → Proposition Atom → Prop
  | .implyK, χ => ∃ φ ψ : Proposition Atom, χ = φ.imp (ψ.imp φ)
  | .modalT, χ => ∃ φ : Proposition Atom, χ = (Proposition.box φ).imp φ
  | .modalB, χ => ∃ φ : Proposition Atom, χ = Axioms.AxiomB φ
  …  -- one existential clause per tag, 18 total
```
Every clause has the shape `∃ (metavariables) : Proposition Atom, χ = (schema instance)` — this
is the "schema = set of its instances" encoding the task description names. Each clause's
proposition shape is asserted (in the file's own docstring) to match, byte-for-byte, the
corresponding constructor of the pre-existing per-system axiom inductives, so that bridge
equivalences `SchemaUnion sysTags φ ↔ <Sys>Axiom φ` hold (those bridges were used transiently in
Phase 3-7 of the rollout and deleted once redundant in Phase 8 — see Area 6/7 notes below on
`SchemaBridges.lean`, now deleted).

**`SchemaUnion` combinator**, signature:
```lean
def SchemaUnion (S : Finset ModalSchemaTag) : Proposition Atom → Prop :=
  fun χ => ∃ t ∈ S, t.Holds χ
```
`SchemaUnion S χ` holds iff `χ` is an instance of some tag in `S`. Every one of the 15 classical
normal modal systems' axiom predicate is now (post-523) a one-line `abbrev <Sys>Axiom :=
SchemaUnion sysTags` declaration (confirmed live in `Cslib/Logics/Modal/ProofSystem/Instances/
{K,KB5,...}.lean`, e.g. `abbrev KAxiom : Proposition Atom → Prop := SchemaUnion kTags` in
`Instances/K.lean` and `abbrev KB5Axiom : Proposition Atom → Prop := SchemaUnion kb5Tags` in
`Instances/KB5.lean`). S5 is the one exception worth flagging precisely for the doc: `S5.lean`
still says "Reuses the existing `ModalAxiom` type" in its module docstring and does not itself
redefine `S5Axiom` as an abbrev over `SchemaUnion s5Tags` in the file read — `s5Tags` exists in
`SchemaTags.lean` and is used by the subsumption edges `S4Axiom_implies_ModalAxiom` /
`TBAxiom_implies_ModalAxiom` in `AxiomSubsumption.lean`, so `ModalAxiom` and `SchemaUnion s5Tags`
are treated as interchangeable at the subsumption-lemma level even though `S5.lean`'s
`ModalAxiom` itself is defined in `Metalogic/DerivationTree.lean` (not re-read in this pass; the
planner/implementer should open that file to state precisely whether `ModalAxiom` is itself now
`abbrev`-redefined as `SchemaUnion s5Tags` or merely bridge-equivalent to it — this is the one
open precision gap in this research pass, flagged rather than guessed).

**S5's `ModalAxiom` — confirmed, not an open gap**: `Cslib/Logics/Modal/Metalogic/
DerivationTree.lean` line 69 reads exactly `abbrev ModalAxiom : Proposition Atom → Prop :=
SchemaUnion s5Tags`. So S5 is *not* an exception to the "one-line abbrev over SchemaUnion"
pattern after all — `ModalAxiom` was itself redefined in place as `SchemaUnion s5Tags`, with the
name and public API preserved (the file's own docstring states this: *"the inductive is retired;
`ModalAxiom` is now definitionally `SchemaUnion s5Tags`, preserving the name and public API via
redefinition-in-place"*). `Instances/S5.lean`'s "Reuses the existing `ModalAxiom` type" docstring
is accurate but slightly dated in spirit — pre-refactor, `ModalAxiom` was a genuine bespoke
inductive S5 reused as-is; post-refactor, that same name is a `SchemaUnion` abbrev, so `S5.lean`
ends up going through `SchemaUnion` transitively via `ModalAxiom`, just without saying `SchemaUnion`
by name in its own file. The doc should present `ModalAxiom` as the 15th (and final) system
folded into the same one-line-abbrev pattern, not as a structural outlier.

Also landed in `SchemaUnion.lean` (needed for Area 2, "elimination API"):
- `SchemaUnion.empty_iff : SchemaUnion (∅ : Finset ModalSchemaTag) φ ↔ False` (`@[simp]`)
- `SchemaUnion.insert_iff {t} {S} : SchemaUnion (insert t S) φ ↔ t.Holds φ ∨ SchemaUnion S φ` (`@[simp]`)
- `SchemaUnion.union_iff {Sa} {Sb} : SchemaUnion (Sa ∪ Sb) φ ↔ SchemaUnion Sa φ ∨ SchemaUnion Sb φ` (`@[simp]`)

These let a concrete `SchemaUnion sysTags φ` rewrite via `simp` into the named disjunction of its
tags' `.Holds`, replacing raw `fin_cases t <;> simp_all` destructuring at call sites. Worth a
sentence in the doc as the "ergonomics" half of the design (distinct from the "elegance" half,
which is subsumption/soundness).

### Area 2 — Subsumption as `Finset.subset` (the modal cube as decidable tag-set computation)

**Durable anchors**: `SchemaUnion.subsumption` (in `SchemaUnion.lean`),
`Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (the 15 per-system tag sets),
`Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` (the 24 direct-edge lemmas).

**Generic subsumption lemma**, signature:
```lean
theorem SchemaUnion.subsumption {Sa Sb : Finset ModalSchemaTag} (hsub : Sa ⊆ Sb)
    {φ : Proposition Atom} (h : SchemaUnion Sa φ) : SchemaUnion Sb φ
```
Every `XAxiom_implies_YAxiom` lemma across the modal cube is now `SchemaUnion.subsumption (by
decide) h` — a `decide`-able `Finset.subset` fact discharged automatically because
`ModalSchemaTag` is a finite, `DecidableEq` type and the 15 tag sets are concrete `Finset`
literals built from `insert`/`kCore`. `AxiomSubsumption.lean` states this explicitly in its
module docstring: *"the modal cube IS the `⊆`-order on per-system tag sets… each subsumption
edge is a `decide`-able `Finset.subset` fact"*.

**The 15 per-system tag sets** (`SchemaTags.lean`), each `kCore` (the shared 13-tag base) unioned
with a subset of the 5 differentiators:
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
def s5Tags  : Finset ModalSchemaTag := insert .modalT (insert .modalFour (insert .modalB kCore)) -- T+4+B
def tbTags  : Finset ModalSchemaTag := insert .modalT (insert .modalB kCore)
def kb5Tags : Finset ModalSchemaTag := insert .modalB (insert .modalFive kCore)
def d4Tags  : Finset ModalSchemaTag := insert .modalD (insert .modalFour kCore)
def d5Tags  : Finset ModalSchemaTag := insert .modalD (insert .modalFive kCore)
def d45Tags : Finset ModalSchemaTag := insert .modalD (insert .modalFour (insert .modalFive kCore))
def dbTags  : Finset ModalSchemaTag := insert .modalD (insert .modalB kCore)
```

**The 24 direct edges** in `AxiomSubsumption.lean`, every one now a one-line proof
`SchemaUnion.subsumption (by decide) h` (previously hand-written per-edge `match`/`cases`
lemmas — this collapse is the single biggest "replacing the hand-written per-edge subsumption
lemmas" fact the task description asks the doc to cover):
- From K: K→T, K→D, K→B(KB), K→K4, K→K5 (5 edges)
- From D: D→D4, D→D5, D→DB (3 edges)
- From T: T→S4, T→TB (2 edges)
- From B(KB): B→TB, B→DB, B→KB5 (3 edges)
- From K4: K4→S4, K4→D4, K4→K45 (3 edges)
- From K5: K5→D5, K5→K45, K5→KB5 (3 edges)
- From K45: K45→D45 (1 edge)
- From D4: D4→D45 (1 edge)
- From D5: D5→D45 (1 edge)
- Into S5: S4→ModalAxiom(S5), TB→ModalAxiom(S5) (2 edges)
Total: 5+3+2+3+3+3+1+1+1+2 = 24, confirmed.

Note: `Cslib/Logics/Modal/Cube.lean` is a **pre-existing, semantically distinct** formalization
of "the modal cube" — it defines each system as a `Set (Model World Atom)` (the class of models
satisfying a frame property), e.g. `def T World Atom := logic {m | Std.Refl m.r}`, and is
authored by different contributors (Fabrizio Montesi, Marianna Girlando) for a different purpose
(semantic frame-class cube). **The final doc must not conflate this with the new
`AxiomSubsumption.lean` / `SchemaTags.lean` syntactic tag-set cube** — they are two independent
"modal cube" artifacts in the codebase (one semantic/frame-based, one syntactic/proof-theoretic),
and the task-536 scope is exclusively the latter. A short disambiguating footnote in the doc is
recommended.

### Area 3 — `unionSound` as the syntax/semantics hinge; consuming `FrameCorrespondence`

**Durable anchors**: `unionSound`, `FrameValidatesTag` (both in
`Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean`); `Satisfies.modalT_axiom`,
`Satisfies.modalFour_axiom`, `Satisfies.modalB_axiom`, `Satisfies.modalD_axiom`,
`Satisfies.modalFive_axiom` (in `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`).

**The five frame-condition→validity lemmas** (`FrameCorrespondence.lean`), verified signatures:
```lean
lemma Satisfies.modalT_axiom {World} (m : Model World Atom) (h_refl : ∀ w, m.r w w) (w) (φ) :
    Satisfies m w (Proposition.imp (Proposition.box φ) φ)

lemma Satisfies.modalFour_axiom {World} (m : Model World Atom)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) (w) (φ) :
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
Each lemma's docstring records verbatim provenance ("Copies the `modalT` case from
`Systems/T/Soundness.lean`", etc.) — these five lemmas were extracted from the previously-inline
per-system soundness case-splits into a standalone reusable library, citing Blackburn/de
Rijke/Venema *Modal Logic* Ch. 4, Definition 4.9, Table 4.1 as the source reference (this citation
is itself a durable anchor worth reproducing).

**`FrameValidatesTag`** — the uniform per-tag semantic obligation over all 18 tags:
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
This is `True` for the 13 frame-unconditional tags and exactly the raw frame-condition hypothesis
for the 5 differentiators — uniform over all 18 tags rather than a type-level conditional split,
which is called out as a deliberate design choice in the module docstring ("keeps `unionSound`'s
`hfc` interface uniform: the 13 trivial obligations discharge by `trivial`").

**`unionSound`** — the master soundness combinator, signature:
```lean
theorem unionSound {World : Type*} (S : Finset ModalSchemaTag) (m : Model World Atom)
    (hfc : ∀ t ∈ S, FrameValidatesTag m t) {φ : Proposition Atom} (h : SchemaUnion S φ)
    (w : World) : Satisfies m w φ
```
Its proof is a single `cases t with` over all 18 tags; the 5 differentiator cases each delegate
directly to the corresponding `FrameCorrespondence` lemma (`exact Satisfies.modalT_axiom m hval w
φ'`, etc.) rather than re-deriving the frame argument — this is the exact "hinge" fact the task
description asks the doc to name explicitly. `SchemaSoundness.lean`'s own module docstring states
this composition in almost doc-ready prose: *"`unionSound` is the hinge between this task's
syntactic side (the schema-tag alphabet) and the `FrameCorrespondence` semantic side… the
composition (frame-correspondence's semantic side + schema-union's syntactic side) is a design
invariant of the schema-union rollout."* (Original prose used task numbers 522/523 for the two
sides — the doc must replace those with the module names: `FrameCorrespondence.lean`'s semantic
side and `SchemaUnion.lean`/`SchemaTags.lean`'s syntactic side, per the no-task-references rule.)

### Area 4 — The `HasAxiom*` typeclass insulation layer

**Durable anchor**: `Cslib/Foundations/Logic/ProofSystem.lean`

This file defines one `HasAxiom*` typeclass per schema (`HasAxiomImplyK`, `HasAxiomImplyS`,
`HasAxiomEFQ`, `HasAxiomPeirce`, `HasAxiomK`, `HasAxiomT`, `HasAxiom4`, `HasAxiomB`,
`HasAxiom5`, `HasAxiomD`, `HasAxiomAndI/AndE1/AndE2/OrI1/OrI2/OrE`,
`HasAxiomDiaDualityFwd/Back`, plus non-modal `HasAxiomMF` and 16 temporal `HasAxiom*` classes out
of this task's scope), each stating `InferenceSystem.DerivableIn S (Axioms.X …)` — an assertion
about *derivability of the axiom instance*, never about *how the underlying `<Sys>Axiom`
predicate is constructed*. Representative signature:
```lean
class HasAxiomT where
  T {φ : F} : InferenceSystem.DerivableIn S (Axioms.AxiomT φ)
```
These are bundled via `extends` into the Layer-3 hierarchy: `MinimalHilbert ⊂ IntuitionisticHilbert
⊂ ClassicalHilbert ⊂ ModalHilbert ⊂ {ModalTHilbert, ModalDHilbert, ModalBHilbert, ModalK4Hilbert,
ModalK5Hilbert} ⊂ {ModalS4Hilbert, ModalK45Hilbert, ModalTBHilbert, ModalKB5Hilbert,
ModalD4Hilbert, ModalD5Hilbert, ModalDBHilbert} ⊂ {ModalS5Hilbert}` (exact `extends` chain
confirmed by direct read of the `class Modal*Hilbert` declarations).

**Why this is "representation-agnostic insulation" (verified, not asserted)**: `Instances/S5.lean`
constructs `HasAxiomT Modal.HilbertS5` via
```lean
instance : HasAxiomT Modal.HilbertS5 (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _ (⟨.modalT, by decide, _, rfl⟩)⟩
```
i.e. it discharges the typeclass field by constructing a `DerivationTree` witness whose axiom
premise is `⟨.modalT, by decide, _, rfl⟩` — a tag-membership proof (`.modalT ∈ s5Tags`, discharged
by `decide`) plus a `.Holds` witness. `HasAxiomT` itself never inspects whether `<Sys>Axiom` is an
`inductive` or a `SchemaUnion`; it only requires a `DerivableIn` proof. This is the exact
"representation-agnostic" property task-523's blast-radius report identified as *"the
load-bearing feasibility fact"* enabling the whole refactor to be additive with zero blast radius
at this layer: `Systems/*/Completeness.lean` (15 files) and `Systems/*/ConservativeExtension.lean`
(15 files) both route exclusively through this `HasAxiom*`/bundled-class layer and were
confirmed **insulated** (untouched) by the refactor.

### Area 5 — S5 = T+4+B; the deliberately omitted KB5→S5 edge

**Durable anchors**: `s5Tags`, `kb5Tags` (`SchemaTags.lean`); the "Top-Level Edges" section and
its explanatory note in `AxiomSubsumption.lean`; the Phase 8 completion summary's verification
line.

Verified: `s5Tags := insert .modalT (insert .modalFour (insert .modalB kCore))` — i.e. `kCore ∪
{modalT, modalFour, modalB}` — carries `modalT`, `modalFour`, `modalB` but **not** `modalFive`.
`kb5Tags := insert .modalB (insert .modalFive kCore)` — i.e. `kCore ∪ {modalB, modalFive}` —
carries `modalFive` but not `modalT`/`modalFour`. Since `modalFive ∈ kb5Tags` and `modalFive ∉
s5Tags`, `kb5Tags ⊆ s5Tags` is false (mechanically: no `Finset.subset` proof exists, `decide`
would report `False`), so `SchemaUnion.subsumption` cannot produce a `KB5Axiom_implies_ModalAxiom`
lemma — the omission is not an oversight but a direct, decidable consequence of the tag-set
definitions. `AxiomSubsumption.lean`'s module docstring states this explicitly: *"the edge KB5 →
S5 is omitted because `kb5Tags` … is not a subset of `s5Tags` … S5 = T+4+B and carries `modalB`,
NOT `modalFive`"*. The Phase 8 completion summary independently re-confirms this post-hoc: *"`KB5
→ S5` edge: confirmed still absent (deliberate…) — `modalFive ∈ kb5Tags` but `modalFive ∉
s5Tags`"*. This is a good candidate for a small worked example in the doc: it demonstrates that
subsumption gaps in the cube are now *self-documenting and machine-checkable* (a `decide` failure
would immediately explain why an edge is missing) rather than requiring a separate written
justification as under the old per-edge hand-lemma design.

### Area 6 — Design rationale: Representation A vs. Representation B

**Durable anchors**: the design-decision record itself lives in `specs/state.json`'s task-523
entry (task-management artifact, task-number citation permitted there per the exception in
`.claude/rules/no-task-references-in-deliverables.md`) and in
`specs/523.../reports/01_schema-union-combinator-blast-radius.md` §3-6 plus
`specs/523.../plans/02_schema-union-per-file-rollout.md`'s "Postmortem Constraints" section. **The
final `docs/` deliverable must present this rationale using code/architecture vocabulary only —
no task numbers** (see Constraint section below for exact phrasing guidance).

**Representation A** (chosen): a schema-tag `inductive` (`ModalSchemaTag`) + `.Holds` existential
meaning function + `SchemaUnion (S : Finset ModalSchemaTag)` combinator, exactly as landed.

**Representation B** (rejected fallback, never implemented in this codebase — "break-glass
only"): macro-generated flat inductives — keep the per-system `inductive <Sys>Axiom` shape but
generate each one via a `macro`/elaborator over a tag list (sketched as `derive_modal_axiom
KAxiom [implyK, implyS, efq, peirce, modalK, andCore, orCore, diaDuality]` in the report), so
constructor names and elimination form (`cases h_ax with | implyK … `) are preserved verbatim.

**Trade-off actually recorded** (report §3-4, reproduced here for the doc's rationale section):
- Rep A wins: (a) subsumption collapses from 24 hand-written lemmas to one generic
  `SchemaUnion.subsumption` + `decide`-able `Finset.subset` facts; (b) soundness collapses from 15
  per-system case-splits to one `unionSound` + an 18-entry validity table; (c) the 13-line
  propositional/K/and-or/dia-duality core no longer needs re-listing per system. The refactor
  ended up **net line-negative** (+1483/-2105, net -622 lines in the actual landed diff, confirmed
  in the Phase 8 completion summary) — DRY gains outweighed the one-time migration cost.
- Rep A costs: the *elimination form* changes at every downstream destructuring site — `cases
  h_ax with | implyK … | modalK …` becomes `obtain ⟨t, ht, hφ⟩ := h_ax; fin_cases t <;> …` (tamed,
  post-Phase-2, by the `SchemaUnion.{empty,insert,union}_iff` `@[simp]` elimination API described
  in Area 1, which turns most such sites into named `simp` rewrites rather than raw `fin_cases`).
- Rep B wins: near-zero downstream blast radius — every existing `cases`/`match` site keeps
  typechecking unchanged, and it delivers the literal DRY goal (no re-listing at the source) with
  a single-PR-sized migration.
- Rep B costs: does not deliver the set-theoretic subsumption-as-⊆ or soundness-as-per-tag-table
  properties (cross-inductive subsumption stays O(edges) even if macro-generated); adds
  metaprogramming maintenance burden; less transparent/auditable to reviewers than a plain `def`.
- **Why A was chosen for long-term foundations** (synthesizing the recorded rationale for the
  doc's "why" framing): the explicit ask was durable *architecture*, and Rep A is the only
  representation that makes the modal cube's algebraic structure (a lattice of finite tag sets
  under `⊆`) directly visible and machine-checkable in the type theory itself, rather than merely
  hiding the same 24+15 bespoke facts behind macro-generated syntax. Rep B optimizes for
  short-term migration safety; Rep A optimizes for the property this whole task exists to
  document — that subsumption and soundness are *literally* computations on `Finset
  ModalSchemaTag`, not just DRY-refactored restatements of 39 previously-independent facts.

### Area 7 — Scope boundary: intuitionistic/minimal families as a future instance, not a fork

**Durable anchors**: `SchemaUnion.lean`'s "Design Invariants" docstring section (design invariant
3); `plans/02_schema-union-per-file-rollout.md`'s "Design invariants" #5 ("Scope-open, not
forked").

Verified in the landed `SchemaUnion.lean` module docstring (not paraphrased — this is the exact
text the doc should draw from):
> `ModalSchemaTag` / `SchemaUnion` stay free of classical-only assumptions: the
> intuitionistic/minimal axiom families are a possible future instance of this same abstraction,
> not generalized to cover them here (out of scope for this task).

The rollout plan's design-invariant #5 states the same commitment in fuller form: *"Build the
combinator for the classical 15; keep `ModalSchemaTag`/`SchemaUnion` free of classical-only
assumptions so the intuitionistic/minimal families are a future instance of the same abstraction,
not a parallel copy — WITHOUT generalizing to cover them now (out of scope; YAGNI)."* The
intuitionistic/minimal families that exist today and were explicitly kept **out of scope** (never
touched by the refactor, confirmed via the blast-radius report's Table row and the Phase-8
postmortem's "Do NOT" list) are named concretely: `IKModalAxiom`, `MKModalAxiom`, `CKModalAxiom`,
`IS5ModalAxiom`, `MTModalAxiom` — these live in
`Cslib/Logics/Modal/Metalogic/{Constructive,Intuitionistic,Minimal}/*.lean` (module paths not
individually re-verified in this pass, but their constructor names were confirmed present in the
task-523 report's cross-family-coupling discussion; the planner/implementer should do a quick
`grep -rn "IKModalAxiom\|MKModalAxiom\|CKModalAxiom\|IS5ModalAxiom\|MTModalAxiom"
Cslib/Logics/Modal/` to pin exact file paths before citing them in the doc, since this report did
not re-read those files directly). The key framing point for the doc: these families construct
witnesses *into* the classical `KAxiom`/`ModalAxiom` predicates (cross-family coupling, in
`InterSystem/IntToClassical.lean`), so their existing call sites had to keep typechecking through
the refactor — but nothing about *their own* internal representation was touched or generalized.
The "future instance, not a fork" framing means: when/if someone later wants
intuitionistic/minimal schema-union support, the correct move is to reuse
`ModalSchemaTag`/`SchemaUnion`'s existing shape (extend the tag alphabet or parametrize it), not
to build an independent parallel `IntSchemaTag`/`IntSchemaUnion` pair from scratch.

## Decisions

- The doc's structure should map 1:1 onto the task description's seven numbered areas; this
  report is organized identically (Areas 1-7) to make the hand-off unambiguous.
- The doc must clarify the 14-inductives-plus-S5's-pre-existing-`ModalAxiom` vs. "15 systems"
  distinction (see Executive Summary) rather than repeating the informal "15 hand-written
  inductives" phrasing verbatim.
- The doc must include the `Cube.lean` disambiguation footnote (Area 2) so readers do not conflate
  the pre-existing semantic frame-class cube with the new syntactic tag-set cube.
- Resolved during this research pass (no longer an open gap): `Metalogic/DerivationTree.lean:69`
  confirms `abbrev ModalAxiom : Proposition Atom → Prop := SchemaUnion s5Tags` — S5's `ModalAxiom`
  is the 15th system folded into the same one-line-abbrev-over-`SchemaUnion` pattern as the other
  14 systems (see Area 1's updated finding). No further verification needed on this point before
  writing the doc.

## Risks & Mitigations

- **Risk**: copying task-523's own doc-comment prose verbatim (which freely cites "task 522" /
  "task 523" / "this task") into the new `docs/` file would violate
  `.claude/rules/no-task-references-in-deliverables.md`. **Mitigation**: this report already
  rewrites every such passage in terms of module/file names (see Areas 3 and 6); the
  planner/implementer should treat any remaining task-number phrase encountered while re-reading
  source docstrings as a signal to substitute the corresponding file/module name, never to copy
  through.
- **Risk**: the one unverified item (S5's `ModalAxiom` exact final form) could lead to an
  inaccurate claim in a durable document. **Mitigation**: flagged explicitly above; a single
  targeted `Read` of `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (search for `ModalAxiom`)
  resolves it before the doc is written.
- **Risk**: `docs/` does not exist yet, so the implementer must decide file naming/placement.
  **Mitigation**: not decided here (out of scope for research); recommend the planner choose a
  single-file `docs/modal-axiom-schema-architecture.md` or similar, since the material is
  cohesive and cross-referential (all seven areas describe one abstraction), unless the planner
  judges a multi-file split clearer.

## Context Extension Recommendations

- **Topic**: There is no existing `.claude/context/` entry indexing CSLib's modal-logic
  architecture docs (this is a `markdown`-task-type project, and `.claude/context/index.json` is
  agent-system context, not CSLib-domain context). No action needed — CSLib's own `docs/`
  directory (once created) is the correct long-term home for this knowledge, not
  `.claude/context/`.
- **Gap**: none identified requiring a new `.claude/context/` file; this is a one-off
  domain-documentation deliverable, not a recurring agent-context need.

## Appendix

### Durable anchors (module/file/name index, for the implementer to cross-reference directly — no task numbers)

- `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`
  — `ModalSchemaTag` (18 constructors), `ModalSchemaTag.Holds`, `SchemaUnion`,
    `SchemaUnion.subsumption`, `SchemaUnion.empty_iff`, `SchemaUnion.insert_iff`,
    `SchemaUnion.union_iff`
- `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean`
  — `kCore`, `kTags`, `tTags`, `dTags`, `bTags`, `k4Tags`, `k5Tags`, `k45Tags`, `s4Tags`,
    `s5Tags`, `tbTags`, `kb5Tags`, `d4Tags`, `d5Tags`, `d45Tags`, `dbTags`
- `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`
  — `Satisfies.modalT_axiom`, `Satisfies.modalFour_axiom`, `Satisfies.modalB_axiom`,
    `Satisfies.modalD_axiom`, `Satisfies.modalFive_axiom`
- `Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean`
  — `FrameValidatesTag`, `unionSound`
- `Cslib/Logics/Modal/Metalogic/Soundness.lean`
  — the 13 frame-unconditional validity atoms (`Satisfies.implyK_axiom`, …,
    `Satisfies.diaDualityBack_axiom`) that `unionSound` reuses read-only (file not re-read this
    pass; names confirmed via `unionSound`'s own proof body)
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`
  — `ModalAxiom` (line 69: `abbrev ModalAxiom : Proposition Atom → Prop := SchemaUnion s5Tags`),
    `DerivationTree`, `Deriv`, `Derivable`
- `Cslib/Foundations/Logic/ProofSystem.lean`
  — `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, `HasAxiomK`,
    `HasAxiomT`, `HasAxiom4`, `HasAxiomB`, `HasAxiom5`, `HasAxiomD`,
    `HasAxiomAndI/AndE1/AndE2/OrI1/OrI2/OrE`, `HasAxiomDiaDualityFwd/Back`,
    `ModusPonens`, `Necessitation`, `MinimalHilbert`, `IntuitionisticHilbert`,
    `ClassicalHilbert`, `ModalHilbert`, `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert`,
    `ModalS5Hilbert`, `ModalBHilbert`, `ModalK4Hilbert`, `ModalK5Hilbert`, `ModalK45Hilbert`,
    `ModalTBHilbert`, `ModalKB5Hilbert`, `ModalD4Hilbert`, `ModalD5Hilbert`, `ModalD45Hilbert`,
    `ModalDBHilbert`
- `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean`
  — 24 direct-edge lemmas (`KAxiom_implies_TAxiom`, …, `S4Axiom_implies_ModalAxiom`,
    `TBAxiom_implies_ModalAxiom`), plus the explicit KB5→S5 omission doc comment
- `Cslib/Logics/Modal/ProofSystem/Instances/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}.lean`
  — the 15 per-system instance-registration files; `S5.lean` is the one that reuses
    `ModalAxiom` rather than defining a new `abbrev`
- `Cslib/Logics/Modal/Cube.lean`
  — the pre-existing, semantically distinct frame-class modal cube (`K`, `T`, `B`, `KB5`, `S5`
    defs as `Set (Model World Atom)`) — flag as out-of-scope-but-easily-confused
- `Cslib/Foundations/Logic/InferenceSystem.lean` — `InferenceSystem`, `DerivableIn` (referenced by
  `HasAxiom*`; not re-read this pass, name confirmed via `ProofSystem.lean`'s imports/usage)

### Search queries / reads performed

- `find Cslib/Logics/Modal -type f` (full file listing)
- Direct `Read` of: `SchemaUnion.lean`, `SchemaTags.lean`, `FrameCorrespondence.lean`,
  `SchemaSoundness.lean`, `Foundations/Logic/ProofSystem.lean`,
  `InterSystem/AxiomSubsumption.lean`, `Instances/S5.lean`, `Cube.lean` (partial), task-523
  report/plan/summary artifacts, `specs/state.json` task-523 entry
- `grep -n "SchemaUnion\|sysTags\|kTags\|tTags\|s5Tags"` over `Instances/{K,S5,KB5}.lean` to
  confirm live abbrev redefinitions
- `grep -n "KB5\|S5"` over `Cube.lean` to confirm the semantic-cube's independent K/T/S5/KB5 defs
