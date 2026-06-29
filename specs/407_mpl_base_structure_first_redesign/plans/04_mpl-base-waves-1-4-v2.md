# Implementation Plan: Task #407 — MPL the structure-first base *with* `⊥` (option C), Waves 1–4 (v2)

- **Task**: 407 — Make MPL the structure-first base logic (`⊥` as nullary connective; explosion/leastness/initiality as independent property modules), carrying Waves 1–4 forward with report 03's sharpenings S1–S3
- **Status**: [NOT STARTED]
- **Effort**: ~16–20 hours (9 phases, each one agent run / ~1–3h)
- **Dependencies**: 398 (completed) — this **builds on, and does not revert,** 398; it re-frames 398's gated `efq` constructor as the explosion property module. Verification baseline: green `main`.
- **Research Inputs**:
  - specs/407_mpl_base_structure_first_redesign/reports/01_mpl-base-structure-first.md (codebase layer map; option C; 6-wave breakdown)
  - specs/407_mpl_base_structure_first_redesign/reports/02_mpl-base-with-vs-without-bot.md (Zulip Design A vs B dispute; fragment-genericity headline)
  - specs/407_mpl_base_structure_first_redesign/reports/03_design-verification-plan-readiness.md (hard-mode adversarial verification; verdict SOUND-AS-IS modulo S1–S3)
  - specs/407_mpl_base_structure_first_redesign/plans/01_mpl-base-waves-1-4.md (prior plan; baseline structure carried forward, not templated verbatim)
- **Artifacts**: plans/04_mpl-base-waves-1-4-v2.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib CONTRIBUTING/NOTATION/ORGANISATION
- **Type**: cslib
- **Lean Intent**: true

## Overview

Make **MPL genuinely the base propositional logic *with* `⊥` a primitive nullary constructor** (Design A, report 02), realized as report 01's **option C**: do **not** revert task 398, but *re-frame* its gated `efq` ND constructor (`NaturalDeduction/Basic.lean:155-156`) as the **explosion property module**, so the base derivation relation is `⊥`-rule-free and IPL is recovered by the existing `IsIntuitionistic` property (`Defs.lean:166-171`). On top of that, reify the semantic **property hierarchy** (designated-bottom → least → explosion-sound) **reusing the existing `Is*`/Mathlib-`OrderBot` conventions**, **genericize the metalogic** so `Min*`/`Int*` Lindenbaum/completeness share one explosion-parameterized substrate, and **unify the tableau** expansion. The headline research deliverable is a **fragment-genericity layer** — treated here as a bounded **spike with an explicit research-or-defer gate**, not as assembly of existing assets (report 03, F2/S3).

This plan covers **Waves 1–4**, decomposed into nine small phases (one agent run each). The two heavy structural items — **W5** (minimal sequent calculus `LM`) and **W6** (literal `⊥`-rule-free ND inductive, option B) — remain **spawned as separate `--hard` tasks (408/409)** and are out of scope here.

### Research Integration

Report 03's verdict is **SOUND TO IMPLEMENT AS-IS**: no wave rests on a false premise, all four GAP claims re-confirmed with only line-number drift, BibKey grounding complete. This v2 applies its three non-blocking sharpenings as concrete, bounded plan adjustments (not a rewrite):

- **S1 (Phase 1)** — *Pin `MinimalDerivation`/`IsBotRuleFree` before the docstring rewrite.* Report 03 (F2) found these names are currently **zero grep hits**. Phase 1 fixes their precise definitional meaning/role first — preferring the trivial theory-abbreviation `MinimalDerivation := (AxiomTheory MinPropAxiom).Derivation` (zero proof churn) and/or an additive `IsBotRuleFree : Derivation → Prop` predicate — so no later phase starts on an undefined term. A literal `⊥`-rule-free *inductive* is explicitly NOT in scope (that is W6/task 409).
- **S2 (Phases 3–4)** — *Reuse `IsIntuitionistic`; do NOT coin a parallel `HasExplosion`.* The proof-level explosion property already exists definitionally (`IsIntuitionistic T ↔ IPL ⊆ T`, `Defs.lean:166-171`); `min_consistent` (`MinLindenbaum.lean:27`) blocks any such instance at MPL strength, so the gated `efq` is genuinely unconstructible at minimal strength. The Wave 2 "named bottom-property hierarchy" REUSES/extends the de-facto `Is*` convention (`IsIntuitionistic`/`IsClassical`/`IsBotFree`) plus Mathlib `Bot`/`OrderBot` for structure, rather than introducing duplicate `Has*` classes. `HasLeastBot` (if introduced) is a thin `Prop`-mixin over `OrderBot`; `HasDesignatedBot` stays the **existing `bot_val` parameter**, not a new structure. NOTATION.md governs notation only, not typeclass naming.
- **S3 (Phase 7)** — *Treat fragment-genericity as OPEN RESEARCH.* Report 03 (F2) showed `fragment-genericity`/generic-Lindenbaum return zero grep hits; the "70–80% done" figure measures theorem *availability* of primitives, not artifact completion of deliverables. Phase 7 is scoped as an exploratory spike with an explicit **research-or-defer decision point**: deliver the mechanism + one worked instance, or document the residual and spawn a follow-on research task — never `sorry` (mark `[BLOCKED]`).

Confirmed facts kept front-and-center so phases stay grounded:
- All four GAP claims confirmed, no semantic drift: `botL` hard-coded at `LJ/Basic.lean:91` and `LK/Basic.lean:76` (no `LM/` directory); metalogic hard-wires EFQ at `IntLindenbaum.lean:69-75,296-301` while `MinLindenbaum` needs none (`:199-201`, no consistency req at `:21,27`).
- Option C is structurally sound: only a stale docstring (`NaturalDeduction/Basic.lean:58-68`, still "IPL as base") and a missing abbreviation remain — cheap Wave 1 items.
- BibKeys all present in `references.bib` and already cited at `Basic.lean:80-89` (`Johansson1937`, `Prawitz1965`, `SorensenUrzyczyn2006`, `TroelstraVanDalen1988`, `TroelstraSchwichtenberg2000`, `Gentzen1935`).

### Prior Plan Reference

Carried forward from `plans/01_mpl-base-waves-1-4.md`: the four-wave spine, the universal-algebra coherence principle (one property, two faces: proof-level explosion = algebra-level leastness), the cherry-pick/small-PR granularity, the additive-first migration discipline, and the W5/W6 spawn decision. Calibration lesson taken from v1: the v1 single coarse "Phase 3" bundled metalogic genericization **and** the fragment-genericity headline into one 5–7h block; report 03's S3 shows these have very different risk profiles, so v2 splits them (Phases 5/6 = genericization, Phase 7 = the open-research spike behind a gate). v1's "zero proof churn" framing for Wave 1 is preserved but pinned concretely via S1.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap_flag = false). No roadmap phases added.

### Universal-algebra coherence (guiding principle)

`⊥` is a single primitive nullary operation in the fixed signature `{⊥,→,∧,∨}` (never excluded); its characteristic properties are introduced axiomatically later, never by changing syntax or by exclude-then-re-add. Two consequences bind the phases: (i) **one property, two faces** — proof-level explosion (`IsIntuitionistic`/the `efq` module, Phases 1–2) and algebra-level leastness (`OrderBot`-backed `HasLeastBot`, Phases 3–4) are the same characteristic property viewed proof-theoretically vs. semantically, tied by soundness; (ii) **consistency across layers** — the ND layer gates explosion as a property on one derivation type; the spawned 408 mirrors this with property-gated `botL`, and 409 is the deliberately-avoided duplication route, trigger-only.

## Goals & Non-Goals

**Goals**:
- Re-frame the ND layer so **MPL is the documented base** and `efq` is an explicitly-named **explosion module**, with a pinned `MinimalDerivation`/`IsBotRuleFree` view of the gate-free fragment (S1). Zero proof churn expected in Wave 1.
- Fold Benjamin's **substitution-invariance / free-algebra argument** (Zulip #604219492) into the in-source design note as the canonical justification for `⊥`-as-constructor; name Design A vs B factually; restore references and link the Zulip thread.
- Introduce a **named semantic property hierarchy** that **reuses** `IsIntuitionistic` and Mathlib `Bot`/`OrderBot` (S2): designated-bottom (existing `bot_val` parameter) → least (`OrderBot`-backed `HasLeastBot`) → explosion-soundness; wire existing `BrouwerianBot` (free `bot_val`) and `PointedBrouwerian` (least) to it; keep `MPL/IPL/CPL.hilbert_alg_complete` green.
- **Genericize the metalogic**: one deductive-closure/implication-witness substrate parameterized by the explosion/consistency property; re-instantiate `Min*` and `Int*` additively-first; delete duplicated code only once both pass.
- **Fragment-genericity spike (headline, S3)**: a bounded exploration of a generic layer over the existing fragment predicates (`IsBotFree`/`IsOrBotFree`/`IsImpTopOnly`) + property typeclasses, with an explicit research-or-defer gate; demonstrate on ≥1 currently-bespoke conservativity link or document the residual and spawn a follow-on.
- **Unify the tableau** expansion behind a closure-predicate parameter; minimal/intuitionistic become instances.
- Preserve **all** MPL/IPL/CPL metatheory and conservativity assets (no deletion/weakening); full `lake build` + CI green against the `main` baseline.

**Non-Goals**:
- **Design B** (MPL without `⊥`): neither B1 (language-extension) nor B2 (`⊥:Atom` encoding) implemented — documented only.
- **W5** (minimal sequent calculus `LM`) and **W6** (literal `⊥`-rule-free ND inductive) — spawned as tasks 408/409.
- A new `HasExplosion` proof-level class (S2: `IsIntuitionistic` already is it); a new `HasDesignatedBot` structure (S2: keep the `bot_val` parameter); a literal `⊥`-rule-free ND inductive (S1: out of scope here).
- The categorical initial-object `0 → A` universal-property witness (report 03 Q3: new mathematics; deferred/stretch).
- Reverting task 398, deleting `bot_val`, or changing the `Proposition` type.
- Any AI-authored Zulip post or PR prose (Zulip AI policy #605827029); human-authored only.
- Connective typeclasses (#606970606 / task 400) — a separate development; do not fold in.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fragment-genericity (Phase 7) is open research larger than a single wave, not asset assembly | M | M | **S3 research-or-defer gate**: scope to a foundation + one demonstrated fragment; if fully-generic conservativity lifting is unreachable, ship the mechanism + worked instance, document the residual precisely, and **spawn** a follow-on research task; never `sorry` (mark `[BLOCKED]`) |
| Metalogic genericization (Phases 5–6) breaks a `Min*`/`Int*` completeness proof | H | M | Land the generic substrate **additively first** (new defs alongside old), migrate one instance at a time, keep each step green; delete duplicates only once both instances pass |
| Phase 3–4 property classes duplicate `IsIntuitionistic`/the `bot_val` parameter (S2 risk) | M | M | Reuse `IsIntuitionistic` for proof-level explosion; `HasLeastBot` thin `Prop`-mixin over Mathlib `OrderBot`; `bot_val` stays a parameter, not a new structure |
| Wave 1 "zero proof churn" violated by an over-ambitious `IsBotRuleFree` inductive | L | L | **S1**: prefer the theory-abbreviation reading (`MinimalDerivation := (AxiomTheory MinPropAxiom).Derivation`) or an additive `Prop` predicate; do not build a `⊥`-rule-free inductive (that is W6/409) |
| Hidden regression in Modal/Temporal/Bimodal or SequentCalculus LJ/LK (consume `Proposition`/embeddings) | H | L | These are insulated (report 01 §3.6/§7); Phase 9 does full `lake build` + targeted module builds |
| Re-opening the community "IPL-base + postpone" compromise (Zulip #606970606) causes friction | M | M | Develop locally to green first; human-authored PR/thread prose only (AI policy #605827029) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 5, 7, 8 | 1 |
| 3 | 4, 6 | 3 (Phase 4), 5 (Phase 6) |
| 4 | 9 | 2, 4, 6, 7, 8 |

Wave-2 phases depend only on the Phase-1 re-framing and edit largely disjoint trees (`NaturalDeduction` docs vs `Semantics/Algebra` vs `Metalogic` vs `Tableau` vs `Conservative`/fragment predicates), so they may be dispatched in parallel with explicit file-territory ownership. Wave-3 phases continue their respective Wave-2 territories sequentially (Phase 4 after 3; Phase 6 after 5). Phase 9 is the integrating full-CI verification.

---

### Phase 1: Pin `MinimalDerivation`/`IsBotRuleFree` (S1) [COMPLETED]

**Goal**: Fix the precise definitional meaning/role of the gate-free-fragment view **before** any docstring rewrite, so no later phase starts on an undefined term. No proof churn.

**Tasks**:
- [ ] Decide and record (in a short in-source comment) the definitional reading: prefer the trivial theory-abbreviation `Theory.MinimalDerivation := (AxiomTheory MinPropAxiom).Derivation` to honor "zero proof churn", and/or an additive `IsBotRuleFree : Theory.Derivation Γ A → Prop` predicate. Explicitly do **not** introduce a literal `⊥`-rule-free inductive (that is W6/task 409).
- [ ] Add the chosen abbreviation/predicate to `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` so "MPL = the `efq`-free fragment" is a named object, grounded in `efq … [IsIntuitionistic T]` (`Basic.lean:155-156`), `IsIntuitionistic T ↔ IPL ⊆ T` (`Defs.lean:166-171`), and `min_consistent : ¬ Derivable MinPropAxiom ⊥` (`MinLindenbaum.lean:27`).
- [ ] Confirm (via the existing `min_consistent` / instance-propagation lemmas `instIsIntuitionisticExtention` `Defs.lean:190`) that the named object is exactly the strength at which `efq` is unconstructible — no new proof obligation.

**Timing**: ~1 hour · **Depends on**: none

**Files to modify**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (abbreviation/predicate + comment).

**Verification**: `lake build` of `Cslib/Logics/Propositional/**` succeeds unchanged (no proof regressions); `git diff` shows the new abbreviation/predicate + comment only; `lake exe checkInitImports`; commit `task 407 phase 1: pin MinimalDerivation/IsBotRuleFree (S1)`.

---

### Phase 2: MPL-base re-framing of ND docstrings + design note [COMPLETED]

**Goal**: Make MPL the *documented* base with `efq` as the explosion module; record the Design A justification. Docs only.

**Tasks**:
- [ ] Rewrite the `## Implementation notes`/design block in `NaturalDeduction/Basic.lean` (`:58-68`, currently "**Design: IPL as base, MPL retained as a fragment**") to state **MPL-as-base with `⊥` primitive**: the base derivation relation is `⊥`-rule-free; `efq` is the explosion property module available exactly at `IsIntuitionistic` strength; IPL/CPL are conservative property-extensions. Reference the Phase-1 `MinimalDerivation`/`IsBotRuleFree` object.
- [ ] Name **Design A vs Design B** factually (report 02 §3/§4); fold in the **substitution-invariance / free-algebra argument** (Zulip #604219492) as the canonical reason for `⊥`-as-constructor; confirm Prawitz / Troelstra–Van Dalen / Sørensen–Urzyczyn / Gentzen / Johansson references present (`Basic.lean:80-89`) and link the Zulip thread.
- [ ] Promote explosion/classicality vocabulary: document `IsIntuitionistic`/`IsClassical`/`MinimalAxioms` as the **property modules** (report 01 §6 Layer 3).
- [ ] Author a top-level design note (e.g. `Cslib/Logics/Propositional/` README or a `Design.lean` docstring) capturing the four-layer structure-first architecture and the Design A/B decision (internal artifact; no Zulip prose).

**Timing**: ~1.5 hours · **Depends on**: 1

**Files to modify**: `NaturalDeduction/Basic.lean` (docstrings); optionally a new design-note doc file; possibly `NaturalDeduction/DerivedRules.lean` (doc only).

**Verification**: full `lake build` unchanged (docs-only); `git diff` shows docs only; `lake exe lint-style`; commit `task 407 phase 2: MPL-base ND docstrings + design note`.

---

### Phase 3: Named semantic property hierarchy — reuse `Is*`/`OrderBot` (S2) [COMPLETED]

**Goal**: Reify "leastness/explosion as independent properties" as named typeclasses that **reuse** the existing conventions, not parallel `Has*` duplicates.

**Tasks**:
- [ ] Introduce thin `Prop`-mixin typeclasses layered over the existing algebra **without** coining `HasExplosion` (reuse `IsIntuitionistic`) and **without** a new `HasDesignatedBot` structure (keep the existing `bot_val : H` parameter, `Semantics/Algebra.lean:82-89`): a `HasLeastBot` mixin defined as a thin layer over Mathlib `OrderBot` (`⊥ ≤ a`), and an explosion-soundness witness expressed via `bot_le`.
- [ ] Defer the categorical initial-object (`0 → A`) universal-property witness (report 03 Q3: new mathematics) — note it as optional/stretch or a follow-on, do not build it here.
- [ ] Add the new mixin(s) to `Semantics/Algebra` (aggregator + a new `Semantics/Algebra/BotProperties.lean` if cleaner), keeping them strictly additive.

**Timing**: ~2 hours · **Depends on**: 1

**Files to modify**: `Semantics/Algebra.lean` (aggregator); new `Semantics/Algebra/BotProperties.lean` (preferred); `Semantics/Algebra/PointedBrouwerian.lean` (reference only this phase).

**Verification**: `lake build` of `Semantics/**` green; new classes are additive (no existing proof touched); `lake exe checkInitImports`; commit `task 407 phase 3: named bottom-property hierarchy reusing Is*/OrderBot (S2)`.

---

### Phase 4: Wire evaluators to the hierarchy; keep completeness green [COMPLETED]

**Goal**: Re-express the existing evaluators through the Phase-3 hierarchy, keeping all completeness/conservativity unchanged in strength.

**Tasks**:
- [ ] Re-express `PointedBrouwerian` explosion-soundness (the `bot_le` route, `PointedBrouwerianCompleteness.lean:79-93`) through the new `HasLeastBot`/`OrderBot` mixin; relate `BrouwerianBot` (free `bot_val`) and `PointedBrouwerian` (least) to the hierarchy via the existing bridge lemmas `pointedBrouwerianEvaluate_eq_botBot`, `brouwerianEvaluate_eq_botTop` (`BrouwerianBot.lean:171-192`).
- [ ] Keep `MPL.hilbert_alg_complete` (GHA), `IPL.hilbert_alg_complete` (Heyting), `CPL.hilbert_alg_complete` (Boolean) (`HilbertCompleteness.lean:93-173`) and the conservativity chains green; re-state in terms of the property mixins only where it does not weaken them.

**Timing**: ~2 hours · **Depends on**: 3

**Files to modify**: `Semantics/Algebra/PointedBrouwerian.lean`, `PointedBrouwerianCompleteness.lean`, `BrouwerianBot.lean`.

**Verification**: `lake build` of `Semantics/**` + `Metalogic/**` green; `MPL/IPL/CPL.hilbert_alg_complete` and conservativity chains unchanged in strength (`git diff` review; `lean_verify` spot-checks; no `sorry`); commit `task 407 phase 4: wire Brouwerian evaluators to bottom-property hierarchy`.

---

### Phase 5: Generic explosion-parameterized Lindenbaum substrate (additive-first) [COMPLETED]

**Goal**: Factor a generic deductive-closure / implication-witness parameterized by the explosion/consistency property, added **alongside** the existing `Min*`/`Int*` code (no deletion yet).

**Tasks**:
- [ ] Factor a generic `GenericDeductiveClosure` / `generic_imp_witness` parameterized by the explosion/consistency **property** — the point where EFQ currently hard-wires in `IntLindenbaum.intNegPhiImpPsi` (`IntLindenbaum.lean:69-75`) and the EFQ-bridge closure (`:296-301`), vs `MinLindenbaum` which needs no EFQ and no consistency req (`:21,27,199-201`). Reuse the existing generic substrate `GenericMCSBridge`, `MCS`, `DeductionTheorem`.
- [ ] Add the substrate in a new `Metalogic/GenericLindenbaum.lean` **without** modifying `MinLindenbaum.lean`/`IntLindenbaum.lean` yet (additive-first; defer migration/deletion to Phase 6).

**Timing**: ~2.5 hours · **Depends on**: 1

**Files to modify**: new `Metalogic/GenericLindenbaum.lean`.

**Verification**: `lake build` of `Metalogic/**` green with the new module compiling alongside the old; no `sorry`; `lean_verify` clean on the new generic lemmas; commit `task 407 phase 5: generic explosion-parameterized Lindenbaum substrate (additive)`.

---

### Phase 6: Re-instantiate `Min*`/`Int*`; unify `bot_forces`; remove duplication [COMPLETED]

**Goal**: Migrate `Min*`/`Int*` onto the Phase-5 substrate one instance at a time and delete duplicated code once both pass.

**Tasks**:
- [ ] Re-instantiate `MinLindenbaum` (no-explosion instance) and `IntLindenbaum` (explosion instance) off `GenericDeductiveClosure`; migrate one instance at a time, keeping each step green; delete the duplicated closure/witness code only after both pass.
- [ ] Unify the canonical `bot_forces` story: minimal uses `⊥ ∈ w` (`MinStrongCompleteness.minBotForces`, `:93-101`), intuitionistic leaves `⊥` unforced — express both as instances of one property-parameterized canonical model.
- [ ] Confirm `MinStrongCompleteness`/`IntStrongCompleteness` and the conservativity chains remain at least as strong as before.

**Timing**: ~2 hours · **Depends on**: 5

**Files to modify**: `Metalogic/MinLindenbaum.lean`, `IntLindenbaum.lean`, `MinStrongCompleteness.lean`, `IntStrongCompleteness.lean`.

**Verification**: `lake build` of `Metalogic/**` green; net line-count **down** (duplication removed); both `Min*`/`Int*` instances pass off the generic substrate; no `sorry`; `lake shake --add-public --keep-implied --keep-prefix`; commit `task 407 phase 6: re-instantiate Min*/Int* on generic substrate; remove duplication`.

---

### Phase 7: Fragment-genericity spike with research-or-defer gate (S3) [COMPLETED]

**Goal**: Bounded exploration of a generic fragment-lifting/conservativity layer, with an explicit decision point — **not** assembly of existing assets.

**Tasks**:
- [ ] **Spike**: build a generic layer over the existing fragment predicates (`IsBotFree`/`IsOrBotFree`/`IsImpTopOnly`, `Conservative.lean:39-44`/`FragmentPredicates.lean:46-68`) + property typeclasses (`MinimalAxioms`/`IsIntuitionistic`) aiming for (i) structural metatheorems (weakening/substitution/admissibility) lifting to a fragment from its specification and (ii) generic conservativity. Attempt to re-derive **one** currently-bespoke conservativity link (e.g. one step of `MplConservativeChain`/`ConservativeChain`, `MplConservativeChain.lean:143-146`, `ConservativeChain.lean:29-40`) through the mechanism.
- [ ] **Research-or-defer gate (explicit decision point)**: if a fully-generic conservativity lifting is reached, land the mechanism + the worked instance (no `sorry`). If it is NOT reachable within this phase, deliver the mechanism + a worked partial, document the residual precisely in the design note, and **spawn a dedicated fragment-genericity research task** — do not block, do not `sorry` (mark `[BLOCKED]` only if nothing lands).

**Timing**: ~3 hours · **Depends on**: 1

**Files to modify**: new generic-lifting module under `Semantics/Algebra/` (e.g. `Semantics/Algebra/FragmentGeneric.lean`); `Conservative.lean`, `ConservativeChain.lean`, `MplConservativeChain.lean`, `FragmentPredicates.lean` (reference/one worked link).

**Verification**: `lake build` of `Semantics/Algebra/**` green; the demonstrated conservativity link re-proved generically with no `sorry` (or the residual documented + follow-on task spawned); `lean_verify` clean on any touched conservativity theorem; commit `task 407 phase 7: fragment-genericity spike + research-or-defer outcome (S3)`.

---

### Phase 8: Tableau unification [IN PROGRESS]

**Goal**: Single parameterized tableau expansion; minimal/intuitionistic become closure-predicate instances.

**Tasks**:
- [ ] Extract a generic `propExpandBranches` parameterized by the closure predicate from the duplicated `intExpandBranches`/minimal reuse (`Tableau/Intuitionistic/*`, `Tableau/Minimal/*`).
- [ ] Re-instantiate intuitionistic (`T(⊥)`-closure) and minimal (`isMinimallyClosed`, `botForces w := T(⊥) at w`) as instances; keep `minimalTableau_decides`/`intuitionisticTableau_decides` and pending soundness/completeness lemmas at least as strong as before.

**Timing**: ~2.5 hours · **Depends on**: 1

**Files to modify**: `Tableau/Intuitionistic/Rules.lean`, `Expansion.lean`, `Scheme.lean`; `Tableau/Minimal/*`; possibly `Tableau/Defs.lean`.

**Verification**: `lake build` of `Tableau/**` green; duplication removed; decision theorems unchanged; `lake exe checkInitImports`; commit `task 407 phase 8: unify tableau expansion behind closure-predicate parameter`.

---

### Phase 9: Full verification, design-note finalization & CI [NOT STARTED]

**Goal**: Confirm the whole library is green and all preserved assets intact; finalize the internal design note.

**Tasks**:
- [ ] Full `lake build`; rebuild-check Modal/Temporal/Bimodal + SequentCalculus LJ/LK (insulated per report 01 §3.6/§7).
- [ ] Confirm all MPL/IPL/CPL metatheory + conservativity chains unchanged in strength (`git diff` review; `lean_verify` spot-checks; no `sorry`/`admit` introduced).
- [ ] Run full CI: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` (and `lake lint`); fix any findings introduced.
- [ ] Finalize the internal design note (Design A adopted; Design B documented-not-implemented; references + Zulip link present; the Phase-7 research-or-defer outcome recorded). **No Zulip post** from this task.

**Timing**: ~1.5 hours · **Depends on**: 2, 4, 6, 7, 8

**Files to modify**: design-note doc only (if any).

**Verification**: whole-library `lake build` + full CI green matching the `main` baseline; commit `task 407 phase 9: full build + CI green; MPL-base design note finalized`.

## Testing & Validation

- [ ] `lake build` (whole library) green, zero `sorry`.
- [ ] `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` pass.
- [ ] `MPL/IPL/CPL.hilbert_alg_complete` and all conservativity chains build, unchanged in strength.
- [ ] `MinimalDerivation`/`IsBotRuleFree` exist as named objects (S1) and resolve to the `efq`-free fragment without new proof obligations.
- [ ] No parallel `HasExplosion` class introduced; `HasLeastBot` is a thin `OrderBot` mixin; `bot_val` remains a parameter (S2).
- [ ] Metalogic duplication measurably reduced (net negative lines in `Metalogic/`); both `Min*`/`Int*` instances pass off the generic substrate.
- [ ] Fragment-genericity (Phase 7): either one conservativity link re-derived generically, or residual documented + follow-on task spawned (S3); no `sorry`.
- [ ] Modal/Temporal/Bimodal + LJ/LK build green (insulation confirmed).
- [ ] No Zulip post authored by AI; design note is internal only.

## Artifacts & Outputs

- plans/04_mpl-base-waves-1-4-v2.md (this file)
- summaries/04_mpl-base-waves-1-4-v2-summary.md (on completion)
- Modified Lean sources across `NaturalDeduction/`, `Semantics/Algebra/`, `Metalogic/`, `Tableau/`; new modules `Metalogic/GenericLindenbaum.lean`, `Semantics/Algebra/BotProperties.lean`, `Semantics/Algebra/FragmentGeneric.lean`; internal design note.
- Possible spawned follow-on: a dedicated fragment-genericity research task if Phase 7's gate defers (in addition to the already-spawned 408/409).

## Rollback/Contingency

- **All changes are additive/conservative** and must not disturb existing MPL/IPL/CPL completeness or conservativity chains, nor task 398's gated `efq` assets. Phases 1–3, 5, 7 are pure additions; Phases 4, 6, 8 re-route existing proofs through new abstractions without weakening them.
- Each phase commits at a green milestone; revert independently with `git revert`.
- Metalogic genericization (Phases 5–6) is additive-first: the generic substrate (Phase 5) lands alongside the old code; if migration of an instance (Phase 6) fails, keep the old proof and the substrate side-by-side and reduce scope rather than break green.
- If the fragment-genericity spike (Phase 7) cannot close, ship the mechanism + one worked partial, document the residual, and rely on a spawned follow-on research task; never `sorry` (mark `[BLOCKED]`).
- Full rollback: revert all `task 407 phase *` commits to restore the `main` baseline; no state/schema migration involved. **Task 398 and all MPL assets remain intact throughout — this task never reverts 398.**
