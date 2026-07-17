# Research Report: Conservative-Extension & Modularity Across the Propositional-Strength × Modal-Axiom Lattice

- **Task**: 484 (capstone)
- **Type**: cslib
- **Session**: sess_1784044271_09e821_484
- **Date**: 2026-07-14
- **Status**: RESEARCHED

---

## 0. Executive Summary

The lattice this task asks us to "relate" is **already almost entirely built**, but the
cross-cutting *inclusion* lemmas that tie the pieces together are **mostly missing** and are —
with one clearly-scoped exception — **cheap, mechanical `cases`-subsumptions** fed into an
already-existing generic lift (`Derivable_mono`).

Concretely:

1. **All four propositional bases** (minimal, constructive, intuitionistic, classical) and all
   their modal systems share **one** derivation framework: `DerivationTree Axioms Γ φ` /
   `Derivable Axioms φ` over the single modal `Proposition Atom` type, with the axiom set carried
   as a parameter `Axioms : Proposition Atom → Prop`. This is what makes uniform monotonicity
   possible.

2. **The classical modal cube already has its full lattice monotonicity** (24 edges,
   `InterSystem/AxiomSubsumption.lean` + `Conservativity.lean`). The minimal, intuitionistic, and
   constructive bases **do not** — but each rung is a two-constructor extension, so every edge is
   a trivial rename.

3. **The propositional-strength inclusions exist at the *non-modal* `PL.Proposition` level**
   (`MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom`, plus `derivable_mono` chains and the
   algebraic fragment-conservativity converses). At the **modal** level they are **missing**.

4. **The one genuinely non-trivial inclusion is Intuitionistic ⟶ Classical (IK ⟶ K)**: the
   intuitionistic/minimal modal systems use *primitive* `◇` with Fischer-Servi axioms
   (`kdia/cd/idb/dbot`), whereas classical `KAxiom` uses the *dual* `◇` with `diaDuality` axioms.
   These do **not** rename onto each other, so `Derivable_mono` (axiom→axiom) does not apply. This
   direction needs (a) a **new generalized lift** `(∀ φ, A₁ φ → Derivable A₂ φ) → Derivable A₁ φ →
   Derivable A₂ φ` and (b) **per-axiom syntactic derivations** proving each Fischer-Servi schema is
   classically K-derivable. This is the sole Zero-Debt risk area and is scoped as an optional,
   `[BLOCKED]`-gated phase.

5. **A crucial correctness caveat for the report's own framing**: within a *fixed language*, the
   modal-axiom-lattice extensions (K ⊆ T ⊆ S4 ⊆ S5) and the classical-over-intuitionistic
   extension are **NOT conservative** — they are *proper* extensions (T proves `□φ → φ`, a
   K-formula not K-derivable; classical proves Peirce, an intuitionistic-language formula not
   IPL-derivable). "Conservative extension" is only literally true (a) **modal over its
   propositional base** (already proved for classical, `ConservativeExtension.lean`) and (b) on
   **restricted fragments** (Glivenko ¬¬-fragment, bot-free fragment — already proved at PL level).
   The deliverable for the lattice edges is therefore **monotonicity** (the "easy direction"), and
   the report is explicit about where a converse does and does not exist.

The capstone is thus **~80% synthesis of existing assets + one file of mechanical inclusion
lemmas**, with two optional harder phases (IK⟶K syntactic bridge; modal fragment conservativity)
that must be `[BLOCKED]`-gated rather than `sorry`-ed.

---

## 1. Inventory of the Lattice (Deliverable 1)

### 1.1 The shared framework

Every system below derives theorems as `Derivable Axioms φ := Nonempty (DerivationTree Axioms [] φ)`,
where `DerivationTree` (`Cslib/Logics/Modal/Metalogic/DerivationTree.lean:134`) has constructors
`ax | assumption | modus_ponens | necessitation | weakening`, and `Axioms : Proposition Atom → Prop`
selects the system. **All propositional strengths and all modal systems are instances of this one
type**, differing only in the axiom predicate. This is the structural fact that makes the whole
lattice uniformly liftable.

### 1.2 The four propositional bases and their modal systems

The propositional strength is encoded directly in the *propositional constructors* of each modal
axiom predicate (mirroring `MinPropAxiom ⊂ IntPropAxiom ⊂ PropositionalAxiom` from
`Cslib/Logics/Propositional/ProofSystem/Axioms.lean`):

| Base | Prop. constructors present | `◇` treatment |
|------|----------------------------|---------------|
| **Minimal** (MK) | 8: `implyK implyS andI andE1 andE2 orI1 orI2 orE` (no `efq`, no `peirce`) | primitive, Fischer-Servi `k kdia cd idb` |
| **Constructive** (CK) | 9: minimal + `efq` (no `peirce`) | primitive, Wijesekera `k kdia` only (no `cd/idb/dbot`) |
| **Intuitionistic** (IK) | 9: minimal + `efq` | primitive, Fischer-Servi `k kdia cd idb dbot` |
| **Classical** (K) | 10: intuitionistic + `peirce` (= DNE) | **dual** `◇=¬□¬`: `modalK diaDualityFwd diaDualityBack` |

Modal-axiom lattice per base (each rung adds a **box-form + diamond-form** pair, identical across
the minimal/intuitionistic/constructive bases):

- base → T: `+ tBox (□A→A), tDia (A→◇A)`
- T → S4: `+ fourBox (□A→□□A), fourDia (◇◇A→◇A)`
- S4 → S5: `+ bBox (A→□◇A), bDia (◇□A→A)`  *(note: S5 via B/symmetry, deliberately not euclidean `5`)*

#### Full theorem inventory (axiom predicate | biconditional | file:line | frame condition)

**Classical** (namespace `Cslib.Logic.Modal`, predicates in `ProofSystem/Instances/<S>.lean`,
proofs `Systems/<S>/{Soundness,Completeness}.lean`; biconditional is
`<s>_strong_completeness_iff`, set-level, all specializations of parametric
`Metalogic/Completeness.lean` `strong_completeness_iff`):

| Sys | Predicate | biconditional (file:line in `Systems/<S>/Completeness.lean`) | FC |
|-----|-----------|--------------------------------------------------------------|----|
| K | `KAxiom` | `k_strong_completeness_iff`:408 | `fun _ => True` |
| T | `TAxiom` | `t_strong_completeness_iff`:135 | `tFC` reflexive |
| S4 | `S4Axiom` | `s4_strong_completeness_iff`:139 | `s4FC` refl∧trans |
| S5 | `ModalAxiom` | `s5_strong_completeness_iff`:147 | `s5FC` refl∧trans∧eucl |
| D | `DAxiom` | `d_strong_completeness_iff`:504 | `dFC` serial |
| B | `BAxiom` | `b_strong_completeness_iff`:130 | `bFC` symmetric |
| K4 | `K4Axiom` | `k4_strong_completeness_iff`:126 | transitive |
| K5 | `K5Axiom` | `k5_strong_completeness_iff`:127 | euclidean |
| K45 | `K45Axiom` | `k45_strong_completeness_iff`:137 | trans∧eucl |
| D4 | `D4Axiom` | `d4_strong_completeness_iff`:129 | serial∧trans |
| D5 | `D5Axiom` | `d5_strong_completeness_iff`:129 | serial∧eucl |
| D45 | `D45Axiom` | `d45_strong_completeness_iff`:135 | serial∧trans∧eucl |
| DB | `DBAxiom` | `db_strong_completeness_iff`:129 | serial∧sym |
| TB | `TBAxiom` | `tb_strong_completeness_iff`:150 | refl∧sym |
| KB5 | `KB5Axiom` | `kb5_strong_completeness_iff`:140 | sym∧eucl |

**Intuitionistic** (`Metalogic/Intuitionistic/`, biconditional `<s>_soundness_completeness`, weak
single-formula ↔ `Derivable`, all via parametric `ivalidFC_completeness`
`Intuitionistic/Extension.lean:97`):

| Sys | Predicate:line | biconditional:line | FC / validity |
|-----|----------------|--------------------|---------------|
| IK | `IKModalAxiom` IK.lean:75 | `ik_soundness_completeness` IK.lean:260 | `IValid` (all birelational) |
| IT | `ITModalAxiom` IT.lean:71 | `it_soundness_completeness` IT.lean:290 | `itFC` reflexive |
| IS4 | `IS4ModalAxiom` IS4.lean:72 | `is4_soundness_completeness` IS4.lean:342 | `is4FC` refl∧trans |
| IS5 | `IS5ModalAxiom` IS5.lean:84 | `is5_soundness_completeness` IS5.lean:391 | `is5FC` refl∧trans∧sym |

**Minimal** (`Metalogic/Minimal/`, biconditional `<s>_soundness_completeness`; MK is a direct
canonical-model proof, MT/MS4/MS5 via parametric `mkvalidFC_completeness`
`Minimal/MinExtension.lean:1548`):

| Sys | Predicate:line | biconditional:line | FC / validity |
|-----|----------------|--------------------|---------------|
| MK | `MKModalAxiom` MK.lean:68 | `mk_soundness_completeness` MinCompleteness.lean:71 | `MValid` (fallible birelational) |
| MT | `MTModalAxiom` MT.lean:69 | `mt_soundness_completeness` MT.lean:272 | `mtFC` reflexive |
| MS4 | `MS4ModalAxiom` MS4.lean:66 | `ms4_soundness_completeness` MS4.lean:310 | `ms4FC` refl∧trans |
| MS5 | `MS5ModalAxiom` MS5.lean:76 | `ms5_soundness_completeness` MS5.lean:362 | `ms5FC` refl∧trans∧sym |

**Constructive** (`Metalogic/Constructive/`, biconditional orientation `Derivable ↔ Valid`; CK/CT
proved, **CS4/CS5 completeness BLOCKED upstream**):

| Sys | Predicate:line | soundness:line | biconditional:line | FC / validity | Blocked? |
|-----|----------------|----------------|--------------------|---------------|----------|
| CK | `CKModalAxiom` CK.lean:104 | `ck_soundness` CK.lean:189 | `ck_soundness_completeness` CK.lean:270 | `CKValid` | no |
| CT | `CTModalAxiom` CT.lean:61 | `ct_soundness` CT.lean:160 | `ct_soundness_completeness` CT.lean:422 | `ctFC` reflexive | no |
| CS4 | `CS4ModalAxiom` CS4.lean:68 | `cs4_soundness_derivable` CS4.lean:218 | **NONE** | `cs4FC` | **BLOCKED** (documented CS4.lean:22-37, no `sorry`) |
| CS5 | `CS5ModalAxiom` CS5.lean:69 | `cs5_soundness_derivable` CS5.lean:231 | **NONE** | `cs5FC` | **BLOCKED** (documented CS5.lean:20-31, no `sorry`) |

**Parametricity note (relevant to phrasing conservativity as axiom-predicate inclusion):** every
system's derivability is *already* `Derivable <Predicate>`, and every completeness result is a thin
instantiation of a lemma quantified over `Axioms : Proposition Atom → Prop` (`strong_completeness_iff`,
`ivalidFC_completeness`, `mkvalidFC_completeness`, `ckvalidFC_completeness`). So conservativity/
monotonicity **can** be phrased purely as `Derivable Weaker φ → Derivable Stronger φ` given an
axiom-predicate inclusion — exactly the classical `InterSystem` pattern.

### 1.3 What already exists vs. what is missing

| Asset | Status | Location |
|-------|--------|----------|
| Generic axiom→axiom lift `liftDerivation` / `Derivable_mono` | ✅ DONE | `InterSystem/Lifting.lean:47,66` |
| Classical modal-cube monotonicity (24 edges) | ✅ DONE | `InterSystem/AxiomSubsumption.lean`, `Conservativity.lean` |
| Morphism-theoretic restatement of the lift | ✅ DONE | `InterSystem/LiftViaMorphism.lean` |
| Modal-over-CPL conservative extension (classical, 15 systems) | ✅ DONE | `Metalogic/ConservativeExtension.lean` + `Systems/<S>/ConservativeExtension.lean` |
| Propositional strength subsumption (PL level) | ✅ DONE | `Propositional/ProofSystem/Axioms.lean:155,168` |
| Propositional derivability monotonicity chain | ✅ DONE | `Propositional/Semantics/Algebra/ConservativeChain.lean:129,139,152` |
| Fragment conservativity converses (algebraic, PL) | ✅ DONE | `HilbertConservativeGlivenko.lean`, `*Conservative.lean`, `Glivenko.lean` |
| Bimodal/temporal conservative-over-CPL precedent | ✅ DONE | `Bimodal/.../PropositionalConservativity.lean:97` |
| **Modal-cube monotonicity for MIN base** (MK→MT→MS4→MS5) | ❌ MISSING | — |
| **Modal-cube monotonicity for INT base** (IK→IT→IS4→IS5) | ❌ MISSING | — |
| **Modal-cube monotonicity for CONSTR base** (CK→CT→CS4→CS5) | ❌ MISSING | — |
| **Cross-base modal monotonicity** MK→IK, CK→IK (and per-rung) | ❌ MISSING | — |
| **Cross-base modal monotonicity** IK→K (Fischer-Servi ⟶ dual ◇) | ❌ MISSING (hard) | — |
| **Generalized lift** axiom→*derivation* | ❌ MISSING (needed for IK→K) | — |

---

## 2. What "Conservative Extension" and "Modularity" Mean Here (Deliverable 2)

There are **three distinct axes**, and they have different Lean shapes. Being precise about which
axis a given statement lives on is the main conceptual contribution of this capstone.

### Axis A — Modal-axiom lattice (fixed propositional base): K ⊆ T ⊆ S4 ⊆ S5, + D/B/…

- **Monotonicity (the deliverable, "easy direction")**: for an axiom-predicate inclusion
  `h_sub : ∀ φ, WeakerAx φ → StrongerAx φ`,
  `Derivable WeakerAx φ → Derivable StrongerAx φ`, i.e. `Derivable_mono h_sub`.
- **Conservativity converse: DOES NOT HOLD in the same language.** T proves `□φ → φ`, a K-formula
  not K-derivable. There is *no* restricted-fragment converse to state here — these are proper
  extensions, not conservative ones. **The report explicitly recommends NOT attempting a converse
  on this axis; "modularity" here = the monotone chain + the matching frame-condition inclusions.**
- **Frame-condition module composition**: the axiom subsumption `WeakerAx → StrongerAx` is mirrored
  by a *reverse* frame-class inclusion `StrongerFC m → WeakerFC m` (e.g. `s4FC m → tFC m`, since
  `s4FC = refl ∧ trans`). Proving these `FC`-implication lemmas is the Lean witness that "each
  axiom↔frame-condition module composes cleanly." (Several already exist implicitly as the
  canonical-frame-closure lemmas `min_canonical_reflexive_mt`, `is4_canonical_transitive`, etc.)

### Axis B — Propositional strength (fixed modal signature): Min ⊆ Int ⊆ Classical (+ Constr)

- **Monotonicity**: `Derivable WeakerBaseAx φ → Derivable StrongerBaseAx φ`.
  - **Min ⟶ Int, Constr ⟶ Int, Min/Constr per-rung**: mechanical — `IKModalAxiom = MKModalAxiom +
    efq + dbot`; `IKModalAxiom ⊇ CKModalAxiom`; and per rung `ITModalAxiom ⊇ {MT,CT}ModalAxiom`,
    etc. So `Derivable_mono` applies directly. (Note: **MK and CK are incomparable** — MK has
    `cd/idb` but not `efq`; CK has `efq` but not `cd/idb`. Both embed into IK.)
  - **Int ⟶ Classical**: **NOT mechanical** (see §4 Phase 3). Needs the generalized lift + syntactic
    derivations that `kdia/cd/idb/dbot/tDia/…` are classically derivable.
- **Conservativity converse**: classical is **not** conservative over intuitionistic in general
  (Peirce). It is conservative on the **¬¬-fragment (Glivenko)** and the **bot-free fragment**
  (`hilbertIplConservativeOverMpl`). These converses **exist at the PL level via algebra**; a
  *modal* analogue would require new modal-algebraic/semantic machinery and is scoped as
  optional/hard.

### Axis C — Modal over propositional base (the operator extension)

- **Conservativity (genuinely holds and is proved for classical)**: `Derivable KAxiom φ.toModal →
  PL.Derivable PropositionalAxiom φ` (`ConservativeExtension.lean:54`, per-system at
  `Systems/<S>/ConservativeExtension.lean`). Strategy: soundness at the one-world universal `Unit`
  model + CPL completeness (`prop_completeness`). This is the "the modal box adds nothing to the
  propositional theorems" result. The analogous statements for the IPL/MPL bases (modal-over-IPL,
  modal-over-MPL) are **not yet present** but are moderate (the propositional completeness theorems
  they need already exist).

**Design consequence:** the capstone's "conservative extension" theorems are Axis A/B
*monotonicity* (`Derivable_mono` corollaries) + reuse of Axis C conservativity; genuine *converses*
are confined to the already-existing PL fragment results, with modal analogues flagged optional.

---

## 3. Cheap Corollaries vs. Genuine Arguments (Deliverable 3)

### 3.1 CHEAP — pure `cases`-subsumption + `Derivable_mono` (no semantics)

All of the following are one-line `Derivable_mono (fun _ h => <cases h>)` applications, exactly
mirroring the classical `InterSystem` file. They are **independent of any completeness result** (so
the CS4/CS5 completeness blocker does **not** obstruct them — monotonicity is purely syntactic):

1. **Minimal cube**: `MKModalAxiom → MTModalAxiom → MS4ModalAxiom → MS5ModalAxiom` (each rung a
   verbatim rename + drop the two new constructors). ⇒ `mkDerivable_implies_mtDerivable`, etc.
2. **Intuitionistic cube**: `IKModalAxiom → ITModalAxiom → IS4ModalAxiom → IS5ModalAxiom`.
3. **Constructive cube**: `CKModalAxiom → CTModalAxiom → CS4ModalAxiom → CS5ModalAxiom`.
4. **Cross-base into intuitionistic**: `MKModalAxiom → IKModalAxiom`, `CKModalAxiom → IKModalAxiom`,
   and per-rung `MTModalAxiom → ITModalAxiom`, `CTModalAxiom → ITModalAxiom`, `MS4→IS4`, `CS4→IS4`,
   `MS5→IS5`, `CS5→IS5`. (All hold because IT/IS4/IS5's constructor set ⊇ the corresponding
   minimal/constructive set.)
5. **Frame-condition inclusion lemmas** `s4FC m → tFC m`, `is4FC → itFC`, `ms4FC → mtFC`, `cs4FC →
   ctFC`, etc. — `fun h => h.1`-style projections witnessing module composition.

Estimated effort: **1 file per base + 1 cross-base file**, essentially transcription. Each
subsumption lemma is `~14–20` constructor lines like the classical `AxiomSubsumption.lean`.

### 3.2 GENUINE ARGUMENT — the Int ⟶ Classical bridge (moderate/hard)

`Derivable IKModalAxiom φ → Derivable KAxiom φ` cannot use `Derivable_mono` because IK's
`kdia/cd/idb/dbot` are *not* `KAxiom` constructors (classical K has dual-`◇` `modalK/diaDuality`
instead). Two ingredients are required:

- **(3.2a) A new generalized lift** (foundational, ~15 lines, structural recursion on
  `DerivationTree`):
  ```
  Derivable_of_axiom_derivable :
    (∀ φ, A₁ φ → Derivable A₂ φ) → Derivable A₁ φ → Derivable A₂ φ
  ```
  Discharge `ax` via the supplied derivation; recurse through `modus_ponens`/`necessitation`/
  `weakening`/`assumption` using the fact that `Derivable A₂` is closed under those rules (the
  `DerivationTree` constructors). **This does not exist anywhere** (all current engines —
  `liftDerivation`, `liftDerivationTree`, `ProofSigHom.axMap` — are axiom→axiom).
- **(3.2b) Per-axiom classical derivations**: prove `Derivable KAxiom` of each IK modal schema:
  `kdia` (`□(φ→ψ)→(◇φ→◇ψ)`), `cd` (`◇(φ∨ψ)→(◇φ∨◇ψ)`), `idb` (`(◇φ→□ψ)→□(φ→ψ)`), `dbot`
  (`◇⊥→⊥`), and the rung schemata `tDia (A→◇A)`, `fourDia (◇◇A→◇A)`, `bDia (◇□A→A)` — all standard
  theorems of classical K/T/S4/S5 under `◇=¬□¬`, discharged with the existing `HasAxiom*` /
  `Necessitation` instances and modal combinators. `tBox/fourBox/bBox = modalT/modalFour/modalB`
  are direct. **Each is real proof-theory work; each is a Zero-Debt STOP point** (if a derivation
  resists, mark `[BLOCKED]`, never `sorry`).

This direction is the honest content behind "the classical systems arise from the
intuitionistic/minimal ones by adding DNE/efq": adding `peirce`(=DNE) collapses the primitive-`◇`
Fischer-Servi presentation to the dual-`◇` classical one, but *witnessing* that collapse in Lean is
a per-axiom derivation, not a rename.

### 3.3 GENUINE ARGUMENT — modal conservativity converses (hard, optional)

Modal analogues of Glivenko / bot-free conservativity (e.g. classical-modal conservative over
intuitionistic-modal on a fragment) would require new modal-algebraic or semantic-embedding
machinery. **Out of scope for the capstone**; note as future work. The *existing* Axis-C
modal-over-CPL conservativity (`ConservativeExtension.lean`) is reused as-is.

---

## 4. Recommended Lean 4 Design + Phase Decomposition (Deliverable 4)

**Placement**: a new subtree `Cslib/Logics/Modal/Metalogic/InterSystem/` (already the home of the
classical lattice) gains base-specific lattice files plus a cross-base file, mirroring the existing
`AxiomSubsumption.lean` / `Conservativity.lean` split (subsumption lemmas separate from the
`Derivable`-level theorems, for `shake` cleanliness).

### Phase 1 — Per-base modal-axiom lattice monotonicity (CHEAP, parallelizable) ✅ recommended first
- **Files**:
  `InterSystem/MinimalAxiomSubsumption.lean` + `InterSystem/MinimalConservativity.lean`;
  likewise `Intuitionistic…`, `Constructive…` (or one `LatticeSubsumption.lean` +
  `LatticeMonotonicity.lean` grouping all three bases — recommended, less import churn).
- **Content**: `M<X>ModalAxiom_implies_M<Y>ModalAxiom` (and I/C analogues) by `cases`; then
  `m<x>Derivable_implies_m<y>Derivable := Derivable_mono (fun _ => …)`. Plus frame-condition
  inclusion lemmas `ms4FC m → mtFC m` etc.
- **Zero-Debt**: none at risk (pure `cases`; independent of CS4/CS5 completeness).
- **Territory (H7)**: Minimal / Intuitionistic / Constructive files are disjoint — safe to
  parallelize across 3 agents.

### Phase 2 — Cross-base propositional-strength monotonicity into Intuitionistic (CHEAP)
- **File**: `InterSystem/PropositionalStrengthSubsumption.lean` +
  `InterSystem/PropositionalStrengthMonotonicity.lean`.
- **Content**: `MKModalAxiom → IKModalAxiom`, `CKModalAxiom → IKModalAxiom`, and per-rung
  `{MT,CT}→IT`, `{MS4,CS4}→IS4`, `{MS5,CS5}→IS5`; corresponding `Derivable_mono` corollaries.
  Document the **MK/CK incomparability** in the module docstring.
- **Zero-Debt**: none at risk.

### Phase 3 — Intuitionistic ⟶ Classical bridge (MODERATE/HARD, `[BLOCKED]`-gated) ⚠ optional
- **Step 3a**: Add `Derivable_of_axiom_derivable` to `InterSystem/Lifting.lean` (generalized lift,
  §3.2a). Low risk (structural recursion).
- **Step 3b**: `InterSystem/IntToClassical.lean` — for each IK/IT/IS4/IS5 schema, a `Derivable
  KAxiom`/`TAxiom`/`S4Axiom`/`ModalAxiom` derivation; assemble `∀ φ, IKModalAxiom φ → Derivable
  KAxiom φ`; conclude `Derivable IKModalAxiom φ → Derivable KAxiom φ` via 3a. **STOP clause**: if any
  per-axiom derivation cannot be completed, mark the specific schema `[BLOCKED]` with the goal state
  reached and what combinator is missing; do **NOT** `sorry` and do **NOT** add an axiom. Ship
  Phases 1–2 regardless.
- **Risk**: `cd`/`idb` (Fischer-Servi) derivations in classical K are the fiddliest; budget a full
  agent run each.

### Phase 4 — Capstone synthesis & documentation (CHEAP)
- **File**: `InterSystem/Modularity.lean` (or a doc-only `.md`): a single module whose docstring is
  the lattice map, re-exporting the Phase 1–3 theorems, plus:
  - explicit statements distinguishing **monotonicity** (Axes A/B) from **conservativity** (Axis C
    + PL fragments), reusing `modal_conservative_extension` (Axis C) directly;
  - optional: modal-over-IPL / modal-over-MPL conservativity by instantiating the existing
    `conservative_over_cpl` bridge (`ConservativityLift.lean:108`) at IPL/MPL completeness — a
    moderate add, gate as optional.
- **Zero-Debt**: none at risk.

**Recommended minimum viable capstone**: Phases 1, 2, 4 (all cheap, all Zero-Debt-safe) deliver the
complete monotone lattice + the modularity synthesis. Phase 3 is the "nice-to-have" honest Int⟶K
bridge, isolated so its difficulty cannot block the rest.

---

## 5. Reusable Lemmas + Mathlib API (Deliverable 5)

**In-repo reuse (primary):**
- `Derivable_mono` / `liftDerivation` — `InterSystem/Lifting.lean:66,47` — the workhorse for
  Phases 1–2.
- `AxiomSubsumption.lean` (classical) — **the exact template** to copy for the min/int/constr
  subsumption lemmas (constructor-by-constructor `match`).
- `MinPropAxiom.toIntPropAxiom` / `IntPropAxiom.toPropAxiom` — `Propositional/ProofSystem/Axioms.lean:155,168`
  — the naming/shape precedent (`.toX` dot-form) for propositional-strength subsumption.
- `derivable_mono` + `derivableMinOfDerivableInt` / `derivableIntOfDerivableProp` —
  `ConservativeChain.lean:129,139` — precedent for the `Derivable`-level chain.
- `modal_conservative_extension_param` / `modal_conservative_extension` —
  `ConservativeExtension.lean:54` + `Systems/<S>/ConservativeExtension.lean` — reuse verbatim for
  Axis C.
- `conservative_over_cpl` / `evaluate_iff_of_classicalBridge` — `ConservativityLift.lean:108,56` —
  parametric bridge for optional modal-over-IPL/MPL.
- `bimodal_conservative_extension` — `Bimodal/.../PropositionalConservativity.lean:97` — the
  semantic-embedding precedent for any converse.
- Fischer-Servi/classical modal combinators for Phase 3b: existing `HasAxiomK`, `Necessitation`,
  `HasAxiomDiaDualityFwd/Back` instances (`ProofSystem/Instances/K.lean`) + modal theorem lemmas.
- Parametric completeness cores (only if extending completeness, not needed for monotonicity):
  `strong_completeness_iff` (`Metalogic/Completeness.lean`), `ivalidFC_completeness`
  (`Intuitionistic/Extension.lean:97`), `mkvalidFC_completeness` (`Minimal/MinExtension.lean:1548`),
  `ckvalidFC_completeness` (`Constructive/CKExtension.lean:156`).

**Mathlib API**: **minimal** — the work is inductive `cases`/`match` on in-repo predicates. The only
Mathlib touchpoints are the ones already used in the neighbourhood: `Relation.Serial` (classical
`dFC`), `List.map_id` (only if going through the `LiftViaMorphism` route — *not* recommended for the
new lemmas; direct `Derivable_mono` is simpler), and basic `And` projections for `FC` inclusions. No
new Mathlib imports are anticipated.

---

## 6. Zero-Debt & Scope Realism

- **No `sorry`, no new axiom, no vacuous `def X := True`** anywhere in the deliverable. Phases 1, 2,
  4 carry **zero** debt risk (mechanical). Phase 3b is the **only** risk area and is explicitly
  STOP/`[BLOCKED]`-gated per schema.
- **CS4/CS5 completeness is already `[BLOCKED]` upstream (task 501)** — this capstone must **not**
  attempt to unblock it, and does not need to: the constructive-cube *monotonicity* lemmas (Phase 1)
  are syntactic and fully provable regardless.
- **Framing correction is a deliverable, not a bug**: the report deliberately reclassifies most
  requested "conservative extension" results on the lattice edges as **monotonicity**, because the
  same-language converse is false. The genuine conservativity results (Axis C + PL fragments) are
  reused, not re-proved.
- **Recommended dispatch**: `/plan 484` with Phases 1–2–4 as the committed scope and Phase 3 as a
  separate optional wave (consider `--hard` for Phase 3b given its per-axiom derivation content and
  literature-fidelity to Simpson/Fischer-Servi).

---

## Appendix: Key file:line index

- Framework: `Metalogic/DerivationTree.lean:134` (`DerivationTree`), `:201` (`Derivable`)
- Generic lift: `InterSystem/Lifting.lean:47,66`; morphism overlay `InterSystem/LiftViaMorphism.lean`
- Classical lattice (template): `InterSystem/AxiomSubsumption.lean:70-504`, `InterSystem/Conservativity.lean:63-216`
- Axis C conservativity: `Metalogic/ConservativeExtension.lean:54`, `Systems/<S>/ConservativeExtension.lean`
- PL strength: `Propositional/ProofSystem/Axioms.lean:48,89,126,155,168`
- PL monotonicity: `Propositional/Semantics/Algebra/ConservativeChain.lean:129,139,152`
- PL fragment conservativity: `HilbertConservativeGlivenko.lean:88,137,164`, `Glivenko.lean:88`
- Bimodal precedent: `Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean:61,97`
- Foundations morphism (axiom→axiom only): `Foundations/Logic/Metalogic/ProofSystemMorphism.lean:124,186`
- Predicates (min): `MK.lean:68 MT.lean:69 MS4.lean:66 MS5.lean:76`; (int): `IK.lean:75 IT.lean:71 IS4.lean:72 IS5.lean:84`; (constr): `CK.lean:104 CT.lean:61 CS4.lean:68 CS5.lean:69`
