# Implementation Plan: Task #407 — Make MPL the base logic *with* `⊥` (option C), Waves 1–4

- **Task**: 407 — Make MPL the structure-first base logic (⊥ as nullary connective; explosion/leastness/initiality as independent property modules)
- **Status**: [PLANNED]
- **Effort**: ~14–20 hours (W1 small, W2 small–medium, W3 medium+headline, W4 low–medium, W5-verify)
- **Dependencies**: 398 (completed; provides the gated `efq` constructor this task re-frames), green `main` as the verification baseline
- **Research Inputs**:
  - specs/407_mpl_base_structure_first_redesign/reports/01_mpl-base-structure-first.md (codebase layer map; option C; 6-wave breakdown)
  - specs/407_mpl_base_structure_first_redesign/reports/02_mpl-base-with-vs-without-bot.md (Zulip dispute; Design A vs B; fragment-genericity as headline)
- **Artifacts**: plans/01_mpl-base-waves-1-4.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; cslib CONTRIBUTING/NOTATION/ORGANISATION
- **Type**: cslib
- **Lean Intent**: true

## Overview

Make **MPL genuinely the base propositional logic *with* `⊥` a primitive nullary constructor** (Design A, report 02), realized as report 01's **option C**: do **not** revert task 398, but *re-frame* its gated `efq` ND constructor as the **explosion property module**, so the base derivation relation is `⊥`-rule-free and IPL is recovered by the `IsIntuitionistic` property. On top of that, reify the semantic **property hierarchy** (designated-bottom → least → initial/explosion-sound), **genericize the metalogic** so `Min*`/`Int*` Lindenbaum/completeness share one explosion-parameterized substrate, and **unify the tableau** expansion. The headline research deliverable (report 02 §6.3) is a **fragment-genericity layer**: a way to specify a fragment so structural metatheorems and conservativity **lift generically** rather than being reproved per fragment — the open problem Waring (#606970606) and Doty (#605712144) flagged as the real blocker.

This plan covers **Waves 1–4**. The two heavy structural items — **W5** (minimal sequent calculus `LM`) and **W6** (literal `⊥`-rule-free ND inductive, option B) — are **spawned as separate `--hard` tasks** (see task creation accompanying this plan) and are out of scope here.

### Research Integration
Phases map 1:1 to report 01's Waves 1–4, reordered/loaded per report 02 §6: W1 = MPL-base re-framing (option C), W2 = named property hierarchy, W3 = metalogic genericization **+ fragment-genericity foundation** (headline), W4 = tableau unification, plus a final full-CI verification phase. Design A (with `⊥`) is adopted; Design B is documented-but-not-implemented (report 02 §6, "out of scope").

### Universal-algebra coherence (guiding principle)
This task realizes the **universal-algebra pattern**: `⊥` is a single primitive nullary operation in the fixed signature `{⊥,→,∧,∨}` (never excluded), and its **characteristic properties are introduced axiomatically later** — never by changing syntax or by an exclude-then-re-add of the constant. Two consequences bind the phases below:
- **One property, two faces.** Proof-level **explosion** (`IsIntuitionistic` / the `efq` module, Phase 1) and algebra-level **leastness** (`HasLeastBot` / initiality, Phase 2) are the *same* characteristic property of `⊥`, viewed proof-theoretically vs. semantically, and are tied together by soundness. State them so this correspondence is explicit (Phase 2/3), not incidental.
- **Consistency across layers.** The ND layer gates explosion as a property on *one* derivation type (Phase 1); the spawned sequent-calculus task (408) mirrors this with a **property-gated `botL` on one calculus**, and the spawned option-B task (409) — a *separate* `⊥`-rule-free inductive — is the deliberately-avoided duplication route, kept trigger-only.

### Cherry-pick / PR granularity
Implementation lands on this fork first, then ships upstream by **cherry-picking**. Size each phase's commit as an **independently mergeable small PR** (matching the maintainers' stated small-PR preference, Zulip #603086134/#606970606): self-contained, green on its own, with no forward dependency on a later phase's edits. Where a phase naturally splits (e.g. Phase 3's metalogic genericization vs. fragment-genericity foundation), prefer two cherry-pickable commits over one. The connective-typeclasses work (#606970606) stays a *separate* PR and is not bundled here.

### Prior Plan Reference
No prior plan for task 407. Task 398's plan (`specs/398_.../plans/01_efq-primitive-implementation.md`) is the substrate this plan re-frames, not reverts.

## Goals & Non-Goals

**Goals**:
- Re-frame the ND layer so **MPL is the documented base** and `efq` is an explicitly-named **explosion module** (typeclass-gated), with a `MinimalDerivation`/`IsBotRuleFree` view of the gate-free fragment. Zero proof churn expected in W1.
- Fold Benjamin's **substitution-invariance / free-algebra argument** (Zulip #604219492) into the in-source design note as the canonical justification for `⊥`-as-constructor; name Design A vs Design B factually; link the Zulip thread and restore references.
- Introduce a **named semantic property hierarchy** (`HasDesignatedBot` → `HasLeastBot`/`OrderBot` → initial-object/explosion-soundness) and wire existing `BrouwerianBot` (free `bot_val`) and `PointedBrouwerian` (least) to it; keep `MPL/IPL/CPL.hilbert_alg_complete` green.
- **Genericize the metalogic**: one deductive-closure/implication-witness substrate parameterized by the explosion/consistency property; re-instantiate `Min*` and `Int*`; delete duplicated code.
- **Fragment-genericity foundation (headline)**: a generic layer over the existing fragment predicates (`IsBotFree`/`IsOrBotFree`/`IsImpTopOnly`) + property typeclasses (`MinimalAxioms`/`IsIntuitionistic`) from which **structural lifting and conservativity are derivable generically**. Demonstrate on at least one fragment that previously required a bespoke proof.
- **Unify the tableau** expansion behind a closure-predicate parameter; minimal/intuitionistic become instances.
- Preserve **all** MPL/IPL/CPL metatheory and conservativity assets (no deletion/weakening); full `lake build` + CI green against the `main` baseline.

**Non-Goals**:
- **Design B** (MPL without `⊥`): neither B1 (language-extension) nor B2 (`⊥:Atom` encoding) is implemented — documented only (report 02 §4/§6).
- **W5** (minimal sequent calculus `LM`) and **W6** (literal `⊥`-rule-free ND inductive / Curry-Howard + normalization re-cut) — spawned as separate tasks.
- Reverting task 398, deleting `bot_val`, or changing the `Proposition` type.
- Any Zulip post or PR prose authored by AI (Zulip AI policy #605827029); human-authored only.
- Connective typeclasses (#606970606) — a *separate* development; coordinate with the existing PR, do not fold in here.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| W3 metalogic genericization breaks a `Min*`/`Int*` completeness proof | H | M | Land the generic substrate *additively* first (new defs alongside old), migrate one instance at a time, keep each step green; only delete duplicates once both instances pass |
| Fragment-genericity layer (W3 headline) proves harder than a single task wave | M | M | Scope W3 to a *foundation* + one demonstrated fragment; if a fully-generic conservativity lifting is not reachable, deliver the mechanism + document the residual and **spawn** a follow-on research task rather than block |
| Property-hierarchy typeclasses (W2) clash with existing `OrderBot`/Mathlib instances | M | M | Make new classes thin `Prop`-mixins layered over Mathlib order classes; prefer `IsBotFree`-style predicates over new structures where possible |
| W1 "zero proof churn" turns out to require edits | L | L | W1 is rename/abbreviation/docs; if the compiler demands a proof edit, treat it as a W-scoped change and keep green |
| Re-opening the community "IPL-base + postpone" compromise causes friction | M | M | Develop locally to green first; present on PR/thread only with human-authored prose once results stand (report 02 §7 Q3) |
| Hidden regression in Modal/Temporal/Bimodal (consume `Proposition`/embeddings) | H | L | These are insulated (report 01 §3.6/§7); final phase does full `lake build` + targeted module builds |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phase | Blocked by |
|------|-------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 2 | 3 | 1 |
| 3 | 4 | 1 |
| 4 | 5 | 1,2,3,4 |

Phases 2, 3, 4 depend only on the W1 re-framing and edit largely disjoint areas (Semantics/Algebra vs Metalogic vs Tableau), so they may be dispatched in parallel with explicit file-territory ownership. Phase 5 is the integrating full-CI verification.

---

### Phase 1: MPL-base re-framing of ND + design note (Wave 1) [NOT STARTED]

**Goal**: Make MPL the *documented* base with `efq` as the explosion module; add a gate-free-fragment view; record the Design A justification. No intended proof churn.

**Tasks**:
- [ ] Rewrite the `## Implementation notes` block in `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` to state **MPL-as-base with `⊥` primitive**: the base derivation relation is `⊥`-rule-free; `efq` is the **explosion property module** available exactly at `IsIntuitionistic` strength; IPL/CPL are conservative property-extensions. Name **Design A vs Design B** factually (report 02 §3/§4), fold in the **substitution-invariance / free-algebra argument** (Zulip #604219492) as the canonical reason for `⊥`-as-constructor, link the Zulip thread, and confirm the Prawitz / Troelstra–Van Dalen / Sørensen–Urzyczyn references are present.
- [ ] Add a `Theory.MinimalDerivation`/`IsBotRuleFree` abbreviation (or namespaced view) characterizing the gate-free fragment of `Theory.Derivation`, so "MPL = the `efq`-free fragment" is a named object, not just "the strength where `efq` is unconstructible."
- [ ] Promote the explosion/classicality vocabulary: ensure `IsIntuitionistic`/`IsClassical`/`MinimalAxioms` are documented as the **property modules** (report 01 §6 Layer 3).
- [ ] Author a top-level design note (e.g. `Cslib/Logics/Propositional/README` or a `Design.lean` docstring) capturing the four-layer structure-first architecture and the Design A/B decision (internal artifact; not Zulip prose).

**Timing**: ~2–3 hours · **Depends on**: none

**Files to modify**: `NaturalDeduction/Basic.lean` (docstrings + abbreviation); optionally a new design-note doc file; possibly `NaturalDeduction/DerivedRules.lean` (doc only).

**Verification**: full `lake build` succeeds unchanged (no proof regressions); `git diff` shows docs + the new abbreviation only; commit `task 407 phase 1: MPL-base re-framing (option C) + design note`.

---

### Phase 2: Named semantic property hierarchy (Wave 2) [NOT STARTED]

**Goal**: Reify "leastness/initiality/explosion as independent properties" as named typeclasses and wire the existing evaluators to them, keeping all completeness green.

**Tasks**:
- [ ] Introduce thin `Prop`-mixin typeclasses layering the design's property tower over the existing algebra: `HasDesignatedBot` (an arbitrary `bot_val`; the Johansson constant — already the `AlgEvaluate` parameter), `HasLeastBot` (`⊥ ≤ a`, i.e. `OrderBot`-backed), and an explosion-soundness / initial-object (`0 → A`) witness.
- [ ] Re-express `PointedBrouwerian` explosion-soundness (`PointedBrouwerianCompleteness.lean` `bot_le` route) through the new `HasLeastBot`/initial-object class; relate `BrouwerianBot` (free `bot_val`) and `PointedBrouwerian` (least) to the hierarchy via the existing bridge lemmas (`pointedBrouwerianEvaluate_eq_botBot`, `brouwerianEvaluate_eq_botTop`).
- [ ] Keep `MPL.hilbert_alg_complete` (GHA), `IPL.hilbert_alg_complete` (Heyting), `CPL.hilbert_alg_complete` (Boolean) and the conservativity chains green; re-state them in terms of the property classes only where it does not weaken them.

**Timing**: ~3–4 hours · **Depends on**: 1

**Files to modify**: `Semantics/Algebra/PointedBrouwerian.lean`, `PointedBrouwerianCompleteness.lean`, `BrouwerianBot.lean`, `Semantics/Algebra.lean` (aggregator); possibly a new `Semantics/Algebra/BotProperties.lean`.

**Verification**: `lake build` of `Semantics/**` + `Metalogic/**` green; `MPL/IPL/CPL.hilbert_alg_complete` and conservativity chains unchanged in strength; commit `task 407 phase 2: named bottom-property hierarchy (designated/least/initial)`.

---

### Phase 3: Metalogic genericization + fragment-genericity foundation (Wave 3, headline) [NOT STARTED]

**Goal**: Collapse `Min*`/`Int*` duplication behind one explosion-parameterized substrate, and deliver the fragment-genericity foundation so structural lifting + conservativity are derivable generically.

**Tasks**:
- [ ] Factor a generic deductive-closure / implication-witness (`GenericDeductiveClosure`, `generic_imp_witness`) parameterized by the explosion/consistency **property** (the point where EFQ currently hard-wires in `IntLindenbaum.intNegPhiImpPsi`); re-instantiate `MinLindenbaum`/`IntLindenbaum` as the no-explosion / explosion instances; delete the duplicated code once both pass. Reuse the existing generic substrate (`GenericMCSBridge`, `MCS`, `DeductionTheorem`).
- [ ] Unify the canonical `bot_forces` story: minimal uses `⊥ ∈ w` (`minBotForces`), intuitionistic forces `⊥` unforced — express both as instances of one property-parameterized canonical model.
- [ ] **Fragment-genericity foundation**: build a generic layer over the existing fragment predicates (`IsBotFree`/`IsOrBotFree`/`IsImpTopOnly`, `Conservative.lean`/`FragmentPredicates.lean`) and property typeclasses (`MinimalAxioms`/`IsIntuitionistic`) such that (i) structural metatheorems (weakening/substitution/admissibility) **lift to a fragment from its specification** and (ii) **conservativity is derivable generically** rather than per-fragment. Demonstrate by re-deriving at least one currently-bespoke conservativity link (e.g. one step of `MplConservativeChain`/`ConservativeChain`) through the generic mechanism.
- [ ] If a *fully*-generic conservativity lifting is not reachable within this wave, deliver the mechanism + a worked instance, document the residual precisely, and **spawn** a dedicated fragment-genericity research task (do not block).

**Timing**: ~5–7 hours · **Depends on**: 1

**Files to modify**: `Metalogic/MinLindenbaum.lean`, `IntLindenbaum.lean`, `MinStrongCompleteness.lean`, `IntStrongCompleteness.lean` (+ a new `Metalogic/GenericLindenbaum.lean`); `Semantics/Algebra/Conservative.lean`, `ConservativeChain.lean`, `MplConservativeChain.lean`, `FragmentPredicates.lean` (+ a new generic-lifting module).

**Verification**: `lake build` of `Metalogic/**` + `Semantics/Algebra/**` green; net line-count *down* (duplication removed); the demonstrated conservativity link re-proved generically with no `sorry`; `lean_verify` clean on the touched conservativity theorems; commit `task 407 phase 3: generic explosion-parameterized metalogic + fragment-genericity foundation`.

---

### Phase 4: Tableau unification (Wave 4) [NOT STARTED]

**Goal**: Single parameterized tableau expansion; minimal/intuitionistic become closure-predicate instances.

**Tasks**:
- [ ] Extract a generic `propExpandBranches` parameterized by the closure predicate from the duplicated `intExpandBranches`/minimal reuse (`Tableau/Intuitionistic/*`, `Tableau/Minimal/*`).
- [ ] Re-instantiate intuitionistic (`T(⊥)`-closure) and minimal (`isMinimallyClosed`, `botForces w := T(⊥) at w`) as instances; keep `minimalTableau_decides`/`intuitionisticTableau_decides` and pending soundness/completeness lemmas at least as strong as before.

**Timing**: ~2–3 hours · **Depends on**: 1

**Files to modify**: `Tableau/Intuitionistic/Rules.lean`, `Expansion.lean`, `Scheme.lean`; `Tableau/Minimal/*`; possibly `Tableau/Defs.lean`.

**Verification**: `lake build` of `Tableau/**` green; duplication removed; decision theorems unchanged; commit `task 407 phase 4: unify tableau expansion behind closure-predicate parameter`.

---

### Phase 5: Full verification, design-note finalization & CI (Wave-integrate) [NOT STARTED]

**Goal**: Confirm the whole library is green and all preserved assets intact; finalize the internal design note.

**Tasks**:
- [ ] Full `lake build`; rebuild-check Modal/Temporal/Bimodal + SequentCalculus LJ/LK (insulated per report 01 §3.6/§7).
- [ ] Confirm all MPL/IPL/CPL metatheory + conservativity chains unchanged in strength (`git diff` review; `lean_verify` spot-checks; no `sorry`/`admit` introduced).
- [ ] Run CI: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` (and `lake lint`); fix any findings introduced.
- [ ] Finalize the internal design note (Design A adopted; Design B documented-not-implemented; references + Zulip link present per #606970606). **No Zulip post** from this task.

**Timing**: ~1–2 hours · **Depends on**: 1,2,3,4

**Files to modify**: design-note doc only (if any).

**Verification**: whole-library `lake build` + full CI green matching the `main` baseline; commit `task 407 phase 5: full build + CI green; MPL-base design note finalized`.

## Testing & Validation

- [ ] `lake build` (whole library) green, zero `sorry`.
- [ ] `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake …` pass.
- [ ] `MPL/IPL/CPL.hilbert_alg_complete` and all conservativity chains build, unchanged in strength.
- [ ] Metalogic duplication measurably reduced (net negative lines in `Metalogic/`); both `Min*`/`Int*` instances pass off the generic substrate.
- [ ] At least one conservativity link re-derived through the fragment-genericity mechanism.
- [ ] Modal/Temporal/Bimodal + LJ/LK build green (insulation confirmed).
- [ ] No Zulip post authored by AI; design note is internal only.

## Artifacts & Outputs

- plans/01_mpl-base-waves-1-4.md (this file)
- summaries/01_mpl-base-waves-1-4-summary.md (on completion)
- Modified Lean sources across `NaturalDeduction/`, `Semantics/Algebra/`, `Metalogic/`, `Tableau/`; new modules `Metalogic/GenericLindenbaum.lean`, `Semantics/Algebra/BotProperties.lean` (+ fragment-genericity module), internal design note.
- Spawned tasks: W5 (minimal sequent calculus `LM`) and W6 (literal `⊥`-rule-free ND, option B).

## Rollback/Contingency

- Each phase commits at a green milestone; revert independently with `git revert`.
- W3 is additive-first (new generic defs alongside old); if migration of an instance fails, keep the old proof and the generic substrate side-by-side and reduce scope rather than break green.
- If the fragment-genericity headline (Phase 3) cannot be fully closed, ship the mechanism + one worked instance, document the residual, and rely on the spawned follow-on research task.
- Full rollback: revert all `task 407 phase *` commits to restore the `main` baseline; no state/schema migration involved. Task 398 and all MPL assets remain intact throughout (this task never reverts 398).
