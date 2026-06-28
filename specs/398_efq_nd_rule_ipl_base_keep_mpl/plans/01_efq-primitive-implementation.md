# Implementation Plan: Task #398 — Promote efq to a primitive ND `Derivation` constructor (IPL-as-base, MPL retained)

- **Task**: 398 - Make IPL the base propositional logic: add efq as a primitive ND rule, preserving MPL metatheory
- **Status**: [IMPLEMENTING]
- **Effort**: 11 hours
- **Dependencies**: 397 (green main required as the verification baseline)
- **Research Inputs**: specs/398_efq_nd_rule_ipl_base_keep_mpl/reports/01_efq-primitive-ipl-base.md
- **Artifacts**: plans/01_efq-primitive-implementation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Add ex-falso (`efq` / bottom-elimination) as a **primitive gated constructor** of the natural-deduction `Theory.Derivation` inductive (`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`), so the primitive `⊥` proposition is actually interpreted by a real derivation node rather than routed through an axiom. The constructor is `efq {Γ A} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A`, making efq available exactly at IPL/CPL strength. Because `AxiomTheory MinPropAxiom` admits no `IsIntuitionistic` instance, efq is unconstructible at minimal strength, so `hilbert_iff_nd_min` and the entire MPL metatheory are preserved with no edits. The change propagates as new match arms in every exhaustive recursion over `Theory.Derivation` (Basic, DerivedRules, Equivalence, CurryHoward, Normalization). The definition of done: every PL file plus downstream Modal/Temporal/Bimodal builds green against the task-397 baseline, the full CI pipeline passes, all preserved MPL/conservativity assets remain intact, and there are **zero sorries** (the one structural risk — the subformula property under efq — is decided up front and BLOCKS rather than incurs debt if it cannot be made green).

### Research Integration

The plan follows the recommended **gated-constructor** design from the research report (report §4), not the unconditional "IPL base" variant (report §5, postponed as the general-fragment work, item 5). Every phase's proof obligations, file:line anchors, and discharge sketches are taken from the report's obligation map (§4.1-§4.6) and risk register (§9). The report's 5-phase outline (§10) is refined here into 7 phases so that each Normalization sub-area (Basic/Reduction, Termination, SubformulaProperty) is a separately verifiable agent-sized unit, and so the bridge and Curry-Howard work — which touch disjoint files and depend only on the constructor — can run in parallel.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided to this planning run; no ROADMAP.md consulted. Roadmap alignment is recorded at task level via state.json `completion_summary` on completion.

## Goals & Non-Goals

**Goals**:
- Add the gated `efq` constructor to `Theory.Derivation` and keep `Basic.lean` (`weak`, `subs`, `substAtom`) total and green.
- Redefine `Theory.Derivation.botE := efq d` with an unchanged signature so all `botE` call sites stay source-compatible.
- Keep the ND↔Hilbert equivalence (`hilbert_iff_nd*`) provably intact, so efq-as-rule and efq-as-axiom coincide and MPL (no efq rule) still corresponds.
- Mirror `efq` in the Curry-Howard `Theory.Term` language (`Term.efq`) and repair `Isomorphism`/`Reduction`.
- Extend Prawitz normalization (Basic/Reduction/Termination/SubformulaProperty) with efq arms using a **decided, zero-debt** subformula-property strategy.
- Preserve all completed MPL work (MinSoundness, MinLindenbaum, MinStrongCompleteness, `MPL.hilbert_alg_complete`, `bot_val`/Johansson-algebra parametric semantics, MplConservativeChain/ConservativeChain/ImpConservative and the rest of the conservativity chains) as a retained layer beneath IPL — rebuild-check only, no edits, no deletions.
- Update the `Basic.lean` Implementation-notes (in-source docstrings) to record IPL-as-base with MPL retained as a fragment layer.
- Verify full `lake build` plus downstream Modal/Temporal/Bimodal and run the CI pipeline (`lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake …`).

**Non-Goals**:
- The unconditional/"true IPL base" constructor and the `IsBotFree` efq-free sub-relation (report §5) — postponed general-fragment design (task item 5, Waring).
- Any deletion or weakening of MPL metatheory or conservativity results — explicitly forbidden.
- Any change to `Proposition`, `DecidableEq`, `Proposition.subst`/`Monad`, or the `FromPropositional` embeddings — these are insulated and only rebuilt.
- Posting anything to Zulip. Per the Zulip AI policy, any human-facing Zulip prose must be human-authored; this plan and the in-source docstring edits are internal/source artifacts and do not include Zulip posts.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `Normalization/SubformulaProperty.lean`: efq violates the subformula property for non-atomic conclusions (classic Prawitz problem) | H | M | Decide strategy **before** coding (Phase 4 opening gate); encode Prawitz atomic-restriction in the normal-form predicate + relativise the statement; if green is unreachable, BLOCK the phase — never `sorry` |
| `Normalization/Termination.lean` (~52 match sites): SN measure must cover efq | M | M | Each arm mirrors an existing elimination arm; isolate as its own phase (Phase 5) so volume does not contaminate the risk phase |
| Constructor variable/instance binding errors in `weak` (target `IsIntuitionistic T'`) and `substAtom` (instance not subst-preserved) | M | M | Use `instIsIntuitionisticExtention hTheory` in `weak`; use the derived `impE (ax …)` fallback in `substAtom` (report §4.1.3); verify with `lean_goal` before committing |
| Curry-Howard 1-1 iso breaks without a `Term.efq` mirror | M | L | Add `Term.efq` "abort" combinator and the matching iso/reduction arms (report §4.4) |
| Hidden regression in MPL/conservativity or Modal/Temporal/Bimodal from the new constructor | H | L | These are Hilbert-substrate/Proposition-level and structurally independent; Phase 7 does a full `lake build` + targeted module builds to confirm; no source edits expected |
| `hilbert_iff_nd_min` accidentally broken (would falsify MPL correspondence) | H | L | Gated design makes efq unconstructible at minimal strength; Phase 2 explicitly rebuilds Equivalence + Glivenko consumers to confirm no proof edits are needed |
| Phase exceeds one agent run | M | M | Phases sized to single files/sub-areas; Normalization split into three phases; commit at each green milestone |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 4 |
| 4 | 6 | 4, 5 |
| 5 | 7 | 2, 3, 5, 6 |

Phases within the same wave can execute in parallel. Phases 2, 3, and 4 edit disjoint files (Equivalence/AxiomAdmissibility vs CurryHoward vs Normalization) and depend only on the Phase 1 constructor, so they may be dispatched concurrently with explicit file-territory ownership. Note the **gate** inside Phase 4: its opening subformula-property decision must conclude *feasible* before Phases 5 and 6 begin; if Phase 4 BLOCKS, Phases 5-6 do not start.

---

### Phase 1: Core constructor — `Theory.Derivation.efq` + total recursions [COMPLETED]

**Strategy confirmed**: efq has no redex (⊥ has no intro rule), so isNormal(efq d) = d.isNormal and isStronglyNormal(efq d) = d.isStronglyNormal with NO commuting conversion flags. The conclusion of efq is always grounded in T via IsIntuitionistic.efq, so the subformula property holds without Prawitz atomic restriction. substAtom uses impE (ax (Set.mem_image_of_mem ...)) (D.substAtom f).

**Goal**: Add the gated `efq` constructor and keep `Basic.lean`'s three total recursions (`weak`, `subs`, `substAtom`) and `DerivedRules.botE` green.

**Tasks**:
- [ ] Add the constructor to the `Theory.Derivation` inductive (`Basic.lean:117-146`, after `impE`):
      `| efq {Γ : Ctx Atom} {A : Proposition Atom} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A` with a Lean docstring.
- [ ] Add the `efq` arm to `weak` (`Basic.lean:207-221`), supplying the target instance via `instIsIntuitionisticExtention hTheory` (report §4.1.1).
- [ ] Add the `efq` arm to `subs` (`Basic.lean:281-306`); instance unchanged (`efq (E.subs Ds)`, report §4.1.2).
- [ ] Add the `efq` arm to `substAtom` (`Basic.lean:309-324`) via the **derived-route fallback** `impE (ax hmem) (d.substAtom f)` because `IsIntuitionistic` is not preserved across an arbitrary atom substitution (report §4.1.3); rely on `Proposition.subst` sending `bot ↦ .bot`, `imp ↦ .imp` and `Set.mem_image_of_mem`.
- [ ] Redefine `Theory.Derivation.botE` in `DerivedRules.lean:86-89` to `Derivation.efq d` (signature and `[IsIntuitionistic T]` binder unchanged); leave `DerivableIn.botE` (`:165-168`) untouched.
- [ ] Use `lean_goal`/`lean_diagnostic_messages` to confirm each new arm typechecks before building.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — add constructor; add efq arms to `weak`, `subs`, `substAtom`.
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` — redefine `botE := efq d`.

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` and `…DerivedRules` succeed with zero errors and zero sorries.
- No new `sorry`/`admit`; `weak`/`subs`/`substAtom` remain total (no non-exhaustive-match warnings).
- Commit at green milestone: `task 398 phase 1: add gated efq constructor and total-recursion arms`.

---

### Phase 2: ND↔Hilbert bridge + admissibility [COMPLETED]

**Goal**: Add the `efq` arm to `ndToHilbert` and confirm `hilbert_iff_nd*`, MPL correspondence, Glivenko, and `AxiomAdmissibility` all stay green with no proof edits.

**Tasks**:
- [ ] Add the `efq` arm to `ndToHilbert` (`Equivalence.lean:339-387`): use `mem_axiomTheory.mp (IsIntuitionistic.efq A)` to get `Axioms (⊥ → A)`, then mirror the `impE` case with `.modus_ponens _ _ _ (.ax _ _ hax) ih` (report §4.2). This realises efq-as-rule ↔ efq-as-axiom.
- [ ] Confirm `hilbertToND` (`:287-301`) needs **no** change (it matches the Hilbert tree, not `Theory.Derivation`).
- [ ] Confirm `hilbert_iff_nd*` corollaries (`:407-500`) need no proof edits; rebuild to verify.
- [ ] Confirm `hilbert_iff_nd_ctx_min`/`hilbert_iff_nd_min` (`:450-453`, `:478-482`) still hold: efq is unconstructible at `AxiomTheory MinPropAxiom` strength, so ND-minimal is unchanged (report §4.2 crux — satisfies task item 2's "MPL still corresponds").
- [ ] Confirm `AxiomAdmissibility.lean` builds unchanged (`botE` signature preserved; `:247` Peirce proof, plus the Hilbert-axiom `efq` cases at `:217,:233` are unrelated). Optional: re-target `:247` to `Derivation.efq` for directness (not required).

**Timing**: ~1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` — add `efq` arm to `ndToHilbert`.
- `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` — expected no edit; rebuild check (edit only if the compiler demands it).

**Verification**:
- `lake build …NaturalDeduction.Equivalence` and `…AxiomAdmissibility` succeed.
- `lake build …Metalogic.HilbertConservativeGlivenko` (the sole `hilbert_iff_nd_min` consumer, report §6) succeeds with no edits.
- Zero sorries. Commit: `task 398 phase 2: efq arm in ndToHilbert; hilbert_iff_nd* and MPL correspondence preserved`.

---

### Phase 3: Curry-Howard term mirror [NOT STARTED]

**Goal**: Mirror `efq` in `Theory.Term` and repair the isomorphism and reduction so the 1-1 Curry-Howard correspondence is restored.

**Tasks**:
- [ ] Add `Term.efq [IsIntuitionistic T] : Term Γ ⊥ → Term Γ A` (the "abort"/`absurd` combinator) to the `Theory.Term` inductive (`CurryHoward/Defs.lean:56-95`); update the "10 constructors correspond one-to-one" docstring (`:54-55`).
- [ ] Add the `efq`/`Term.efq` arms to **both** directions of the iso in `CurryHoward/Isomorphism.lean` (2 exhaustive matches), report §4.4.
- [ ] Add the `efq` arm to `CurryHoward/Reduction.lean` (1 match): efq has no introduction to reduce against, so this is a congruence / no-redex arm (plus any efq-permutation congruence if mirrored from the chosen normalization strategy).
- [ ] Verify arms with `lean_goal` before building.

**Timing**: ~1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/CurryHoward/Defs.lean` — add `Term.efq`; update docstring count.
- `Cslib/Logics/Propositional/CurryHoward/Isomorphism.lean` — efq arms in both iso directions.
- `Cslib/Logics/Propositional/CurryHoward/Reduction.lean` — efq congruence arm.

**Verification**:
- `lake build Cslib.Logics.Propositional.CurryHoward.Defs Cslib.Logics.Propositional.CurryHoward.Isomorphism Cslib.Logics.Propositional.CurryHoward.Reduction` succeed.
- Zero sorries; iso matches remain exhaustive. Commit: `task 398 phase 3: mirror efq in Term and repair Curry-Howard iso/reduction`.

---

### Phase 4: Normalization — strategy decision + Basic/Reduction efq arms [NOT STARTED]

**Goal**: Fix the zero-debt subformula-property strategy up front, then add efq arms to `Normalization/Basic.lean` (`height`, `isNormal`, `isStronglyNormal`, structural lemmas) and `Normalization/Reduction.lean`.

**Decided strategy (zero-debt, fixed before coding)** — primary path (a)+(c) with (b) as explicit fallback:
1. The `efq` constructor stays unrestricted in `Theory.Derivation` (matches the Phase 1 gated design).
2. **Prawitz atomic restriction encoded in the normal-form predicate**: in `isNormal`/`isStronglyNormal`, a *normal* efq node requires (i) its premise subderivation is normal/strongly-normal and (ii) its conclusion is atomic or `⊥`. Non-atomic efq is therefore reducible, not normal.
3. **efq-permutation conversions** in `Reduction.lean` push a non-atomic efq toward atomic form and past eliminations where efq is the major premise (mirror of the existing `orE`-as-major-premise commuting cases at `Basic.lean:76-93,138-159`), so strong normalization still reaches a normal form.
4. The subformula-property statement in Phase 6 is **relativised** (fallback (b)) only to the standard Prawitz exception — permitting `⊥` and the atomic formula introduced by a normal efq node — and only if encoding (2) alone leaves a *used* downstream consumer unprovable.

**Gate**: The first tasks below READ the actual `isStronglyNormal`/`subformula_property` definitions to confirm this encoding is expressible against the real statements. If it is determined that no green-provable encoding exists (statement cannot accommodate the Prawitz exception without weakening a downstream consumer), mark this phase **[BLOCKED]** with the specific obstruction for user decision — do NOT introduce a `sorry`, vacuous def, or new axiom, and do NOT start Phases 5-6.

**Tasks**:
- [ ] Read `Normalization/Basic.lean` (`height` `:50-59`, `isNormal` `:72-93`, `isStronglyNormal` `:134-159`, structural lemmas `:168-…`) and `Normalization/SubformulaProperty.lean` (`:52`, `:292`); confirm the decided strategy is expressible. If not, BLOCK (see Gate).
- [ ] `height`: add `| efq _ d => 1 + d.height`.
- [ ] `isNormal`/`isStronglyNormal`: add efq arms encoding the atomic-restriction side condition (premise normal/SN ∧ conclusion atomic-or-⊥), plus commuting-conversion arms where efq is the major premise of another elimination (mirror orE cases).
- [ ] Structural lemmas (`:168-…`): add efq arms as required for totality.
- [ ] `Reduction.lean` (~6 match sites): add efq congruence arms and the chosen efq-permutation conversions.
- [ ] Verify each arm with `lean_goal`; keep matches exhaustive.

**Timing**: ~2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Basic.lean` — efq arms in height/isNormal/isStronglyNormal/structural lemmas.
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Reduction.lean` — efq congruence + permutation conversions.

**Verification**:
- `lake build …Normalization.Basic …Normalization.Reduction` succeed with zero sorries.
- The decided strategy is recorded in an in-source comment for Phase 6 consistency.
- Commit: `task 398 phase 4: normalization efq arms (Basic/Reduction) with decided subformula strategy`.

---

### Phase 5: Normalization — Termination (SN measure) [NOT STARTED]

**Goal**: Add efq arms to `Normalization/Termination.lean` (the ~52-site dominant module) so the strong-normalization measure/recursion accounts for efq.

**Tasks**:
- [ ] Add the efq arm to each of the ~52 match sites in `Termination.lean`, mirroring the corresponding existing elimination arm for the height/measure-decrease obligations (report §4.5, §9).
- [ ] Ensure efq-permutation reductions introduced in Phase 4 are covered by the measure so SN is preserved.
- [ ] Verify representative arms with `lean_goal`; rely on `lake build` for exhaustiveness/termination checking.

**Timing**: ~2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` — efq arms across all match/measure sites.

**Verification**:
- `lake build …Normalization.Termination` succeeds with zero sorries and no termination/exhaustiveness errors.
- Commit: `task 398 phase 5: efq arms in Normalization.Termination (SN measure)`.

---

### Phase 6: Normalization — SubformulaProperty (zero-debt risk) [NOT STARTED]

**Goal**: Add efq arms to `Normalization/SubformulaProperty.lean` implementing the Phase 4 decided strategy, keeping `subformula_property_of_isStronglyNormal` (`:52`) and `subformula_property` (`:292`) green with zero debt.

**Tasks**:
- [ ] Add efq arms to `subformula_property_of_isStronglyNormal` (`:52`) and `subformula_property` (`:292`) (7 match sites) consistent with the atomic-restriction encoding from Phase 4.
- [ ] If the literal statement cannot be discharged under encoding (2) alone, apply the relativised statement (fallback (b)) — permitting `⊥` and the normal-efq-introduced atomic formula — and update only the statement that is internal to this module, re-checking every downstream consumer still builds.
- [ ] If neither (a)+(c) nor the relativised (b) yields a green proof without weakening a *used* result, mark this phase **[BLOCKED]** with the precise unprovable goal — never `sorry`.
- [ ] Verify with `lean_goal`/`lean_diagnostic_messages` that no goals remain.

**Timing**: ~2 hours

**Depends on**: 4, 5

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/SubformulaProperty.lean` — efq arms; relativised statement only if required.

**Verification**:
- `lake build …Normalization.SubformulaProperty` succeeds with **zero sorries**.
- `lean_verify` on `subformula_property` confirms no `sorryAx` in the axiom set.
- Any consumer of `subformula_property` still builds.
- Commit: `task 398 phase 6: efq arms in Normalization.SubformulaProperty (zero-debt)`.

---

### Phase 7: Prose update + full verification & CI [NOT STARTED]

**Goal**: Update the `Basic.lean` Implementation-notes to record IPL-as-base with MPL retained, confirm all preserved MPL assets and downstream logics build, and run the full CI pipeline against the task-397 green baseline.

**Tasks**:
- [ ] Update both `Basic.lean` docstring/Implementation-notes blocks (`:45-73` design trade-off and `:113-116` "10 constructors / ex falso is a derived rule") to state: efq is now a primitive gated ND constructor (IPL/CPL strength); IPL is the base; minimal logic is a retained fragment layer beneath IPL with its Hilbert-substrate metatheory intact (report §10 step 5). These are in-source docstrings (not Zulip prose). Do not post to Zulip.
- [ ] Rebuild-check the preserved MPL assets — `Metalogic/MinSoundness`, `MinLindenbaum`, `MinStrongCompleteness`, `Semantics/Algebra/*` (MplConservativeChain, MplPointedConservative, ConservativeChain, Conservative, ImpConservative, OrImpConservative, ConjImpConservative, ConjImpBotConservative, HilbertAlgCompleteness providing `MPL/IPL/CPL.hilbert_alg_complete`), `Glivenko`, `HilbertConservativeGlivenko` (report §6) — confirm no edits and no deletions.
- [ ] Rebuild downstream consumers: `Cslib/Logics/Modal/**`, `Temporal/**`, `Bimodal/**`, and `SequentCalculus/LJ`,`/LK` completeness (report §7) — confirm insulated and green.
- [ ] Run full `lake build`.
- [ ] Run the CI pipeline: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` (and `lake lint` if configured). Address any lint/style/shake findings introduced by the change.
- [ ] Confirm zero sorries repo-wide for the touched files.

**Timing**: ~1 hour

**Depends on**: 2, 3, 5, 6

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — Implementation-notes docstrings only.

**Verification**:
- Full `lake build` succeeds (whole library green) matching the task-397 baseline.
- `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake …` all pass.
- No MPL/conservativity file deleted or weakened; `git status`/`git diff` confirms MPL files unchanged.
- Commit: `task 398 phase 7: IPL-as-base docstrings; full build + CI green; MPL retained`.

## Testing & Validation

- [ ] `lake build` of the whole library succeeds with zero errors and zero sorries.
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (no unexpected import changes).
- [ ] `hilbert_iff_nd_min` / `hilbert_iff_nd_ctx_min` still provable (MPL correspondence preserved).
- [ ] `lean_verify subformula_property` shows no `sorryAx`.
- [ ] MPL metatheory + conservativity chains build unchanged (no deletions; `git diff` clean on those files).
- [ ] Modal/Temporal/Bimodal and SequentCalculus LJ/LK build green (insulation confirmed).
- [ ] All `botE` call sites compile without edits (`AxiomAdmissibility.lean:247`, `FromHilbert.lean:97,195-203`).

## Artifacts & Outputs

- plans/01_efq-primitive-implementation.md (this file)
- summaries/01_efq-primitive-implementation-summary.md (on completion)
- Modified Lean sources:
  - `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` (rebuild check; edit only if required)
  - `Cslib/Logics/Propositional/CurryHoward/Defs.lean`
  - `Cslib/Logics/Propositional/CurryHoward/Isomorphism.lean`
  - `Cslib/Logics/Propositional/CurryHoward/Reduction.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Basic.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Reduction.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/Normalization/SubformulaProperty.lean`

## Rollback/Contingency

- Each phase commits at a green milestone, so any phase can be reverted independently with `git revert` of its commit without losing earlier phases.
- If Phase 4's opening gate or Phase 6 determines the subformula property cannot be proven green under any of the decided strategies, mark that phase **[BLOCKED]** (and leave Phases 5-7 unstarted if blocked at Phase 4), record the precise unprovable goal, and escalate for user decision — never land a `sorry`, vacuous definition, or new axiom.
- If a downstream MPL/conservativity or Modal/Temporal/Bimodal regression appears in Phase 7 (unexpected per the insulation analysis), revert the offending constructor-arm commit and re-investigate; the constructor change must not require edits to preserved MPL assets.
- Full rollback: revert all `task 398 phase *` commits to restore the task-397 baseline; no schema/state migration is involved.
