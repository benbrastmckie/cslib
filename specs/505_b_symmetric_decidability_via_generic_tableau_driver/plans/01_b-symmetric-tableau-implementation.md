# Implementation Plan: Task #505 — B (Symmetric-Frame) Tableau via Generic Driver

- **Task**: 505 - B symmetric-frame decidability via the generic tableau driver (Phase 4 of task 300)
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: 503 (generic driver + RuleApplicationSpec, DELIVERED green), 510 (generic Hintikka chain, DELIVERED green); soundness-side blocker: task 513 `generalize_tableau_soundness_chain_over_spec` (NOT started — gates the final Decidable phase only)
- **Research Inputs**: reports/01_frame-specific-tableau-extensions.md; reports/03_parent-phase-plan-reference.md; parent plan specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md (Phase 4)
- **Artifacts**: plans/01_b-symmetric-tableau-implementation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Deliver the **B (symmetric-frame)** modal system as Phase 4 of task 300, now that the entire
generic-driver infrastructure B was waiting on is delivered and green. B is a **persistent-only**
extension exactly like T: it adds formulas only at *existing* worlds (backward propagation along
recorded edges), so the K world bound and finite formula catalog survive unchanged and B
discharges `RuleApplicationSpec` the same way T/S5 do — it is **not** the S4 case. The worked
precedent to mirror throughout is T: `Cslib/Logics/Modal/Tableau/TDriver.lean`
(`modalApplyOneT` / `modalApplyOneT_spec` / `modalStepBranchT` / `modalExpandBranchesT` /
`modalTableauT` / `modalExpandBranchesT_hintikka`) and `FrameCompleteness.lean`
(`extractModelT` / `hintikkaT_box_pos` / `hintikkaT_diamond_neg` / `modalTruthLemmaT` /
`modalTableauT_complete` / `tValid`). B's decls mirror these over the **symmetric** closure
(`Relation.SymmGen`) instead of the reflexive one (`Relation.ReflGen`).

The definition of done for each *delivered* phase is a green `lake build` with full CSLib CI clean
(build, checkInitImports, lint, lint-style, test, mk_all when adding files, shake) and **zero
`sorry` / zero new `axiom`**. All of B's green work — the B backward-propagation rule, the driver
+ 11-field spec discharge, the generic Hintikka-chain instantiation, `extractModelB` via `SymmGen`,
the B truth-lemma bridges, `bValid` completeness, and B rule-level soundness via `Satisfies.b` —
lands and commits in phases **before** the final `Decidable (bValid φ)` phase, which is the LAST
phase and carries an explicit **[BLOCKED]-on-task-513** fallback. The task-513 soundness-chain
dependency must not block the rest of B.

### Research Integration

- **Persistent-only classification (report §4, parent Phase 4)**: B's backward box rule
  (`T(□φ)@w` + edge `v→w` ⊢ `T(φ)@v`; dually `F(◇φ)@w` + edge `v→w` ⊢ `F(◇φ)@v`) outputs at
  the *source* world `v` of an already-recorded edge, so it mints no new worlds. This is the
  structural fact that lets B discharge `RuleApplicationSpec` by agreement-with-`modalApplyOne`
  plus catalog membership, exactly as T did (see `GenericDriver.lean` header, which explicitly
  names task 505/B among the downstream consumers of the spec, and excludes only S4).
- **Strategy B (closure-at-extraction)**: extract the countermodel with a *closed* accessibility
  relation `r := Relation.SymmGen acc.hasEdge`; `Std.Symm` comes **free** from
  `Relation.SymmGen.instSymm`. No new frame predicate is defined — reuse `Cube.B` and the
  `Satisfies.b` semantic-validity theorem.
- **Per-system bridges are irreducible (task 510 finding)**: `hintikka_box_pos` /
  `hintikka_diamond_neg` are payload-reading and irreducibly per-system, so B needs its **own**
  `hintikkaB_box_pos` / `hintikkaB_diamond_neg` (T built `hintikkaT_*` analogs). The
  `hintikka_box_neg` / `hintikka_diamond_pos` generic projections are reusable as-is.
- **Generic Hintikka chain (task 510)**: B consumes `modalHintikkaSetGen` (spec-free) and
  `modalExpandBranchesGen_hintikka` (parametrized by `(apply, spec)`); no B-specific Hintikka
  *set* predicate is needed.

### Prior Plan Reference

Parent task 300's plan (`plans/01_frame-extensions-implementation.md`) is the source of Phase 4's
scope. Its Phase 2 (T) postmortem is directly instructive: the original attempt to build T's
`Decidable` inline was BLOCKED because the driver/termination machinery hard-coded `modalApplyOne`.
That blocker has since been resolved for the *completeness* side by the generic driver (task 503) +
generic Hintikka chain (task 510). The remaining, still-open half is the *soundness* side (task
513), which is why B's `Decidable` — needing both directions — remains the one BLOCKED deliverable.
This plan is therefore structured so B collects every green result the generic infrastructure now
makes reachable, and isolates only the Decidable claim behind task 513.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context; no ROADMAP.md consulted. Task 505 is a child
of task 300 (Modal Logic tableau line), delivering that plan's Phase 4.

## Goals & Non-Goals

**Goals**:
- B backward-propagation rule + agreement lemma in `FrameRules.lean` (`modalApplyOneB`).
- B driver (`modalStepBranchB` / `modalExpandBranchesB` / `modalTableauB` + `_eq` lemmas) in a new
  `BDriver.lean`, mirroring `TDriver.lean`.
- `modalApplyOneB_spec : RuleApplicationSpec modalApplyOneB` — all 11 fields discharged (the
  structural-hypothesis interface fixed by the generic driver).
- `modalExpandBranchesB_hintikka` by instantiating the generic `modalExpandBranchesGen_hintikka`.
- `extractModelB` via `Relation.SymmGen` with `Std.Symm` free from `Relation.SymmGen.instSymm`.
- B truth-lemma bridges (`hintikkaB_box_pos`, `hintikkaB_diamond_neg`) + `modalTruthLemmaB` over
  the symmetric closure.
- `bValid` (against `Cube.B` / `Satisfies.b`) + `modalTableauB_complete` (completeness direction,
  fully generic).
- B **rule-level** soundness in `FrameSoundness.lean` via `Satisfies.b`.
- `Decidable (bValid φ)` **iff** task 513 has landed; otherwise a documented `[BLOCKED]` handoff.
- Every delivered phase green: `lake build` passing, zero `sorry`, zero new `axiom`, CSLib CI clean.

**Non-Goals**:
- Re-proving or refactoring the generic driver, generic Hintikka chain, or K
  soundness/completeness/FMP machinery beyond instantiating them for B.
- Generalizing the tableau soundness chain over the spec — that is task 513's scope; this plan
  only *consumes* it (in the final phase) if available.
- Any `sorry`, `axiom`, or vacuous `def bValid_decidable := True`/`trivial` placeholder to "close"
  the Decidable phase. A documented `[BLOCKED]` handoff is the only acceptable contingency there.
- S4-style loop-checking or a new world bound — B mints no new worlds, so none is required.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `Decidable (bValid φ)` blocked on task 513 (soundness chain still K-concrete; task 513 is `not_started`) | H | H | Isolate Decidable as the LAST phase (Phase 9) with an explicit `[BLOCKED]-on-513` fallback and documented open goal state. Phases 1–8 deliver all other B results green and commit independently. |
| Backward-propagation saturation conjunct is the delicate part of the B rule | M | M | Model it on `modalTBoxSelf`/`modalTDiaNegSelf`, but read predecessors from `acc` edges (`v→w`) rather than the self-world; keep `modalApplyOneB` agreeing with `modalApplyOne` outside the two B-relevant shapes so the spec discharge stays an agreement argument. |
| Discharging the 11-field `RuleApplicationSpec` for `modalApplyOneB` | M | L | Mirror `modalApplyOneT_spec` field-by-field: fields reduce to agreement-with-`modalApplyOne` (`modalApplyOneB_eq_of_not_boxPos_diaNeg`) plus catalog-membership, because B adds formulas only at existing worlds. GenericDriver header confirms B is an intended spec discharger (only S4 is excluded). |
| Truth-lemma box bridge over `SymmGen` path shape differs from `ReflGen` | M | M | `Relation.SymmGen` is one symmetric-generation step (not transitive), so the bridge is a single-edge case like T's `ReflGen`, not a path induction like S4's `ReflTransGen`; mirror `hintikkaT_box_pos`/`modalTruthLemmaT` structure with the symmetric edge in place of the reflexive self-edge. |
| `Satisfies.b` stated in an unexpected form (as `Satisfies.four` was for S4) | L | L | **VERIFIED**: `Satisfies.b` (`Basic.lean:323`) is `⇓Modal[m,w ⊨ φ → □◇φ]` under `[Std.Symm m.r]`, unfolding (`change`) to `Satisfies m w φ → ∀ w', m.r w w' → Satisfies m w' (◇φ)` — the expected box-diamond form. The soundness arm uses this directly; no surprise. |
| Shared-file edit conflicts (`FrameRules`/`BDriver`/`FrameCompleteness`/`FrameSoundness`) under concurrent sessions | M | M | Phases sharing a file execute sequentially and scope `git add` narrowly to the touched file(s) + this plan + `Cslib.lean` (mk_all) only. The wave table flags which phases co-edit a file. |
| Lint failures (docBlame, defLemma, simpNF) on new decls | L | M | Docstring every new decl; Prop-valued results as `lemma`/`theorem`; lowerCamelCase names (`modalApplyOneB`, `extractModelB`, `hintikkaB_box_pos`); run full CI at each phase end. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 5, 7 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 6 | 4, 5 |
| 5 | 8 | 2, 6 |
| 6 | 9 | 7, 8 |

Phases within the same wave are *logically* independent. However, several co-edit a single file
(Phases 2/3/4 edit `BDriver.lean`; Phases 5/6/8/9 edit `FrameCompleteness.lean`; Phase 7 edits
`FrameSoundness.lean`; Phase 1 edits `FrameRules.lean`), so under concurrent sessions they must
run **sequentially** with narrowly-scoped `git add`, or under explicit H7 territory contracts.
Recommended serial order: 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9. Each phase is one agent run ending at
a green, zero-sorry milestone with a task-scoped commit.

---

### Phase 1: B backward-propagation rule (FrameRules.lean) [NOT STARTED]

- **Goal:** Add the symmetric box rule and its K-merged application function, so downstream phases
  have `modalApplyOneB` to build on.
- **Tasks:**
  - [ ] In `FrameRules.lean`, add `modalBBoxBack` (given `T(□φ)@w` and every recorded edge `v→w`
    in `acc`, emit `T(φ)@v`) and `modalBDiaNegBack` (given `F(◇φ)@w` and edge `v→w`, emit
    `F(◇φ)@v`) — backward along recorded edges; these read predecessors from `acc`, mirroring
    `modalTBoxSelf`/`modalTDiaNegSelf` but at the edge source rather than the self-world. Include
    the backward-propagation saturation conjunct (the delicate part).
  - [ ] Add `modalApplyOneB` = K rules (`modalApplyOne`) merged with the B backward-propagation
    arms, mirroring `modalApplyOneT` (persistent outputs at existing worlds; no new worlds).
  - [ ] Add `modalApplyOneB_eq_of_not_boxPos_diaNeg`: `modalApplyOneB` agrees with `modalApplyOne`
    outside the two B-relevant shapes (box-positive / diamond-negative), mirroring
    `modalApplyOneT_eq_of_not_boxPos_diaNeg`.
  - [ ] Docstring every decl; `import Cslib.Init` already present in the file.
- **Timing:** 1.5 hours
- **Depends on:** none
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameRules.lean` (B arms).
- **Verification:** `lake build` green; zero sorry/axiom; full CSLib CI clean (build,
  checkInitImports, lint, lint-style, test, shake). `git add` scoped to `FrameRules.lean` + this plan.

---

### Phase 2: B driver definitions (BDriver.lean) [NOT STARTED]

- **Goal:** Define the B tableau driver by instantiating the generic driver on `modalApplyOneB`,
  mirroring `TDriver.lean`'s `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT`.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Modal/Tableau/BDriver.lean` (`import Cslib.Init`; import
    `FrameRules`, `GenericDriver`, and the generic-driver deps that `TDriver.lean` imports).
  - [ ] Define `modalStepBranchB`, `modalExpandBranchesB`, `modalExpandBranchesB` fuel wrapper,
    and `modalTableauB (φ : Proposition Atom) : ModalTableauResult Atom` on `modalApplyOneB`,
    mirroring `TDriver.lean:68-86`.
  - [ ] Prove `modalStepBranchB_eq` / `modalExpandBranchesB_eq` / `modalTableauB_eq` (the
    reduction/agreement `_eq` lemmas), mirroring `TDriver.lean:859-873`.
  - [ ] Register the new file: `lake exe mk_all --module`.
- **Timing:** 1 hour
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Modal/Tableau/BDriver.lean` (new); `Cslib.lean` (mk_all).
- **Verification:** `lake build` green; zero sorry/axiom; `lake exe mk_all --module` registers the
  new file; full CSLib CI clean (including checkInitImports on the new file). `git add` scoped to
  `BDriver.lean` + `Cslib.lean` + this plan.

---

### Phase 3: RuleApplicationSpec discharge for modalApplyOneB (BDriver.lean) [NOT STARTED]

- **Goal:** Discharge the 11-field `RuleApplicationSpec` structural-hypothesis interface for
  `modalApplyOneB`, the piece that unlocks every generic downstream lemma.
- **Tasks:**
  - [ ] Prove `modalApplyOneB_spec : RuleApplicationSpec (Atom := Atom) modalApplyOneB` with all 11
    fields, mirroring `modalApplyOneT_spec` (`TDriver.lean:840`). Each field reduces to
    agreement-with-`modalApplyOne` (via `modalApplyOneB_eq_of_not_boxPos_diaNeg`) plus
    catalog-membership for the two B-relevant shapes, since B adds formulas only at existing
    worlds (no fresh-world minting, so the rank/outDeg/knownWorlds fields carry over as T's did).
  - [ ] Confirm the "backward propagation adds formulas only at existing worlds → K world bound and
    finite formula catalog survive unchanged" claim discharges the world-count / catalog fields
    identically to T (this is the structural crux the task calls out).
- **Timing:** 1.5 hours
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Modal/Tableau/BDriver.lean` (spec discharge).
- **Verification:** `lake build` green; zero sorry/axiom; `modalApplyOneB_spec` type-checks with no
  field left admitted; full CSLib CI clean. `git add` scoped to `BDriver.lean` + this plan.

---

### Phase 4: B Hintikka chain via generic instantiation (BDriver.lean) [NOT STARTED]

- **Goal:** Obtain `modalExpandBranchesB_hintikka` by instantiating the generic Hintikka chain on
  `(modalApplyOneB, modalApplyOneB_spec)`.
- **Tasks:**
  - [ ] Prove `modalExpandBranchesB_hintikka (φ0 : Proposition Atom) (fuel : Nat)` by instantiating
    `modalExpandBranchesGen_hintikka` (task 510) at `(modalApplyOneB, modalApplyOneB_spec)`,
    mirroring `modalExpandBranchesT_hintikka` (`TDriver.lean:891`). This reuses the spec-free
    `modalHintikkaSetGen` saturation predicate; no B-specific Hintikka *set* is defined.
  - [ ] Confirm the generic `hintikka_box_neg` / `hintikka_diamond_pos` projections are available
    for reuse (they are system-agnostic) so only the box-pos / diamond-neg bridges remain
    B-specific (built in Phase 6).
- **Timing:** 1 hour
- **Depends on:** 2, 3
- **Files to modify:** `Cslib/Logics/Modal/Tableau/BDriver.lean` (Hintikka chain).
- **Verification:** `lake build` green; zero sorry/axiom; `modalExpandBranchesB_hintikka`
  type-checks; full CSLib CI clean. `git add` scoped to `BDriver.lean` + this plan.

---

### Phase 5: extractModelB via SymmGen (FrameCompleteness.lean) [NOT STARTED]

- **Goal:** Extract the symmetric countermodel with the symmetric closure of the recorded edges and
  obtain `Std.Symm` for free.
- **Tasks:**
  - [ ] In `FrameCompleteness.lean`, define `extractModelB` via `Relation.SymmGen` (mirroring
    `extractModelT` at `FrameCompleteness.lean:101`, `Relation.ReflGen → Relation.SymmGen`).
  - [ ] Add `extractModelB_r` (`.r = Relation.SymmGen (fun w w' => acc.hasEdge w w' = true)`, by
    `rfl`), `extractModelB_symm` (`Std.Symm (extractModelB b acc).r` free from
    `Relation.SymmGen.instSymm` / `inferInstance`), and `extractModelB_hasEdge_imp_r` (raw
    `acc.hasEdge w w'` edges survive into the symmetric closure via the `SymmGen` single-step
    constructor), mirroring `extractModelT_r` / `extractModelT_refl` / `extractModelT_hasEdge_imp_r`.
- **Timing:** 1 hour
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (extractModelB block).
- **Verification:** `lake build` green; zero sorry/axiom; `extractModelB_symm` obtained without a
  bespoke symmetry proof; full CSLib CI clean. `git add` scoped to `FrameCompleteness.lean` + this plan.

---

### Phase 6: B truth-lemma bridges + modalTruthLemmaB (FrameCompleteness.lean) [NOT STARTED]

- **Goal:** Prove the B-specific truth-lemma bridges over the symmetric closure and assemble the
  full B truth lemma.
- **Tasks:**
  - [ ] Prove `hintikkaB_box_pos` (`T(□ψ)@w ∈ b` together with `Relation.SymmGen acc.hasEdge w w'`
    imply `Satisfies (extractModelB b acc) w' ψ`) and `hintikkaB_diamond_neg` (dual for
    `F(◇ψ)@w`), the two irreducibly per-system payload-reading bridges, mirroring
    `hintikkaT_box_pos` (`FrameCompleteness.lean:549`) / `hintikkaT_diamond_neg` (`:614`) with the
    symmetric single-step edge in place of the reflexive self-edge. Reuse the generic
    `hintikka_box_neg` / `hintikka_diamond_pos` projections for the other two modal cases.
  - [ ] Prove `modalTruthLemmaB` (both signs, all connectives) against `extractModelB b acc`,
    mirroring `modalTruthLemmaT` (`FrameCompleteness.lean:695`); the box/diamond cases delegate to
    the bridges above with `extractModelB_r` unfolding `r w w'` to the `SymmGen` hypothesis the
    bridges want, and diamond-witness / recorded-edge survival via `extractModelB_hasEdge_imp_r`.
- **Timing:** 2 hours
- **Depends on:** 4, 5
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (B bridges + truth lemma).
- **Verification:** `lake build` green; zero sorry/axiom; `modalTruthLemmaB` type-checks; full CSLib
  CI clean. `git add` scoped to `FrameCompleteness.lean` + this plan.

---

### Phase 7: B rule-level soundness (FrameSoundness.lean) [NOT STARTED]

- **Goal:** Land the B soundness arm at the rule level via `Satisfies.b`, independent of the
  task-513 driver-level soundness chain.
- **Tasks:**
  - [ ] In `FrameSoundness.lean`, add `symmFC` (the symmetric frame condition predicate for
    `frameValid`/`branchSatisfiableIn`, mirroring T's `reflFC`) and its `Std.Symm`-carrying
    branch-satisfiability lemmas.
  - [ ] Add rule-level soundness for the two B arms — `modalBBoxBack_sound` /
    `modalBDiaNegBack_sound` — discharged via `Satisfies.b` (`Basic.lean:323`, VERIFIED form
    `φ → □◇φ`, i.e. `Satisfies m w φ → ∀ w', m.r w w' → Satisfies m w' (◇φ)` under `[Std.Symm m.r]`).
    Given `branchSatisfiableIn symmFC` carries the `Std.Symm` witness, the backward step
    `T(□φ)@w` + edge `v→w` ⊢ `T(φ)@v` is sound because symmetry turns the recorded edge `v→w`
    into `w→v`, and `w ⊨ □φ` then gives `v ⊨ φ` (mirroring how T's rule soundness used reflexivity).
  - [ ] Do **not** attempt the driver/branch-level `modalTableauB = .closed → bValid` theorem here
    — that is Phase 9's blocked item (needs task 513's generalized soundness chain).
- **Timing:** 1.5 hours
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (B arm).
- **Verification:** `lake build` green; zero sorry/axiom; B rule-soundness lemmas type-check; full
  CSLib CI clean. `git add` scoped to `FrameSoundness.lean` + this plan.

---

### Phase 8: bValid + B completeness (FrameCompleteness.lean) [NOT STARTED]

- **Goal:** State `bValid` against `Cube.B` / `Satisfies.b` and prove the completeness direction,
  which is fully generic and available now.
- **Tasks:**
  - [ ] Define `bValid (φ : Proposition Atom)` against `Cube.B` / `Satisfies.b` (validity over all
    symmetric models), mirroring `tValid`.
  - [ ] Prove `modalTableauB_complete` (the completeness direction: a valid `φ` yields a closed
    tableau — equivalently an open branch produces a symmetric countermodel refuting `φ` via
    `modalTruthLemmaB` + `extractModelB_symm`), mirroring `modalTableauT_complete`. This direction
    is generic and does **not** depend on task 513.
- **Timing:** 1.5 hours
- **Depends on:** 2, 6
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (bValid + completeness).
- **Verification:** `lake build` green; zero sorry/axiom; `bValid` and `modalTableauB_complete`
  type-check; full CSLib CI clean. `git add` scoped to `FrameCompleteness.lean` + this plan.

---

### Phase 9: Decidable (bValid φ) — BLOCKED on task 513 [NOT STARTED]

- **Goal:** Discharge `Decidable (bValid φ)` by combining B completeness (Phase 8) with the
  driver-level B soundness (`modalTableauB φ = .closed → bValid φ`) — the latter requiring task
  513's generalized soundness chain.
- **Tasks:**
  - [ ] **Precondition check**: verify task 513 (`generalize_tableau_soundness_chain_over_spec`) has
    landed and exposes a spec-instantiable `modalStepBranch_preserves_sat`-generalization, then a
    `modalTableauB_sound` obtained by instantiating at `(modalApplyOneB, modalApplyOneB_spec)`.
  - [ ] If 513 is available: prove `modalTableauB_sound` (driver-level soundness) and assemble
    `Decidable (bValid φ)` / `instDecidableBValid` from soundness + completeness, mirroring the
    task-503-Phase-6 `tValid_decides` / `instDecidableTValid` route for T.
  - [ ] If 513 is **not** available: mark this phase **[BLOCKED]** with the documented open goal
    state — the missing dependency is exactly the generalized `modalStepBranch_preserves_sat`
    (Soundness.lean/SoundnessStep.lean, still K-concrete against `modalApplyOne`). Record that
    Phases 1–8 remain green and preserved, and that B's `Decidable` unblocks the moment task 513
    lands (no B-side rework needed — only instantiation).
- **Timing:** 1 hour (instantiation if 513 landed; else a documented [BLOCKED] handoff)
- **Depends on:** 7, 8 (and external: task 513)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (bValid decidability).
- **Verification:** If delivered — `lake build` green, zero sorry/axiom, `Decidable (bValid φ)`
  type-checks, full CSLib CI clean. If blocked — no partial/sorry code committed; the phase heading
  is marked `[BLOCKED]` with the open goal state documented in this plan.
- **[BLOCKED] fallback:** No `sorry`, no `axiom`, no `def bValid_decidable := True`/`trivial`
  placeholder. A documented `[BLOCKED]`-on-task-513 handoff with the open goal state is the only
  acceptable outcome if task 513 has not landed. This exactly parallels task 503 Phase 6.

---

## Testing & Validation

Run the full CSLib CI pipeline at the end of **every** phase:
- [ ] `lake build` — green, and **zero `sorry` / zero new `axiom`** in all delivered decls.
- [ ] `lake exe checkInitImports` — every new/edited file imports `Cslib.Init` (esp. new `BDriver.lean`).
- [ ] `lake lint` — docstrings on every new decl (docBlame); Prop-valued results as `lemma`/`theorem`
  (defLemma); lowerCamelCase names (`modalApplyOneB`, `extractModelB`, `hintikkaB_box_pos`); `@[simp]`
  only with verified LHS (simpNF); `omit` unused section vars.
- [ ] `lake exe lint-style` — style clean.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe mk_all --module` — new `BDriver.lean` registered (Phase 2 onward).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — dependency analysis clean.
- [ ] Acceptance: `modalApplyOneB_spec` (Phase 3), `modalExpandBranchesB_hintikka` (Phase 4),
  `extractModelB_symm` (Phase 5), `modalTruthLemmaB` (Phase 6), B rule-soundness (Phase 7),
  `bValid` + `modalTableauB_complete` (Phase 8) all type-check green; `Decidable (bValid φ)`
  type-checks **iff** task 513 has landed (Phase 9).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/FrameRules.lean` — B backward-propagation arms (`modalBBoxBack`,
  `modalBDiaNegBack`, `modalApplyOneB`, agreement lemma).
- `Cslib/Logics/Modal/Tableau/BDriver.lean` (new) — B driver defs, `modalApplyOneB_spec` (11-field
  discharge), `modalExpandBranchesB_hintikka`.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `extractModelB` (+ `_r`/`_symm`/`_hasEdge_imp_r`),
  `hintikkaB_box_pos`/`hintikkaB_diamond_neg`, `modalTruthLemmaB`, `bValid`, `modalTableauB_complete`,
  and `Decidable (bValid φ)` (Phase 9, if unblocked).
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — `symmFC` + B rule-level soundness arm.
- `Cslib.lean` — mk_all registration of `BDriver.lean`.
- `specs/505_b_symmetric_decidability_via_generic_tableau_driver/summaries/01_b-symmetric-tableau-summary.md`
  (on completion).

## Rollback/Contingency

- Each phase is a self-contained, task-scoped commit at a green milestone with narrowly-scoped
  `git add` (touched file(s) + this plan + `Cslib.lean` for mk_all only); revert an individual
  phase's commit to roll back without disturbing prior phases or concurrent sessions' files.
- The B line is additive: it introduces one new file (`BDriver.lean`) and adds arms/blocks to
  existing frame files without rewriting K, T, or the generic driver — reverting the B decls
  restores the pre-B state intact.
- The single expected blocker (Phase 9 `Decidable`, gated on task 513) is handled by a documented
  `[BLOCKED]` handoff, never a `sorry`/`axiom`. Phases 1–8 stand alone and ship B's rule,
  driver+spec, Hintikka chain, model extraction, truth lemma, completeness, and rule-level
  soundness independently of task 513.
