# Implementation Plan: Discharge `nested_sound_impL` via the Source's Λ-Chain Induction

- **Task**: 570 - nested_sound_impL_lambda_chain_induction
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours (8 phases)
- **Dependencies**: None
- **Research Inputs**: `specs/570_nested_sound_impL_lambda_chain_induction/reports/01_lambda-chain-induction.md`
- **Artifacts**: plans/01_lambda-chain-induction-plan.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
  - .claude/extensions/lean/rules/lean4.md
- **Type**: cslib (lean4)

---

## Overview

Discharge the strategic `sorry` at `Soundness.lean:1315` (`nested_sound_impL`, the `⊃•` case of
Theorem 4.1) by transcribing the source's own induction over the `Λ{ }` chain. The research
dispatch proved that induction sorry-free in Lean, so the mathematical discovery work is done;
what remains is landing it against a codebase that has two pre-existing defects blocking it and a
build that does not currently compile.

**Definition of done**: `lake build` of the whole `Cslib` library goes RED to green, the Cslib
bare-`sorry` census goes 41 to 40 with `Soundness.lean:1315` gone from the inventory,
`#print axioms nested_sound_impL` is free of `sorryAx`, and no new axioms are introduced.

### Scope Expansion (mandatory, owned by this plan)

**The task title's scope — "discharge `nested_sound_impL`" — is necessary but not sufficient, and
this plan is deliberately wider than the title.** Three defects, each established with
Lean-verified evidence in the research report, make the narrow scope either unsound or
unreachable:

| ID | Defect | Why the narrow scope fails without it |
|----|--------|----------------------------------------|
| D1 | `lemma4_7_ii` was never landed. `Soundness.lean:503`'s `lemma4_7_i_ii` covers part (i) only; the module docstring at `Soundness.lean:35-45` wrongly claims (i) and (ii) are the same visible formula, refuted by a direct `pdftotext -layout` render of page 10. | Lemma 4.7(ii) is the source's *named* ingredient for this very induction. Without it the induction has no inductive step. |
| D2 | `InputCtx.outputPruning` (`Context.lean:188`) is off by one nesting level when `ctx.Λ = []`. | `nested_sound_impL` is **false as stated**, not merely unproved. Landing a proof of it is impossible; landing it any other way would land an unsound theorem. Concrete counterexample: `ctx = ⟨[C•], [], P°⟩`, `C := A`, `B := ⊥` — both premises Lean-proved derivable, conclusion `A ⊃ □((A ⊃ ⊥) ⊃ P)` fails in a 2-world classical S5 model. |
| D3 | **The baseline is RED.** `lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness` fails with `1329:2: Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)`. `nested_sound` matches 18 of `NestedProof`'s 19 constructors. | The task brief's "lake build green" premise is false on a clean tree at `88b198bf`. The exit criterion "build green" is unreachable by discharging `impL` alone. |

A future reader should understand: this plan covers D1, D2, and D3 because any plan that did not
would either produce an unsound theorem or leave the library uncompilable.

### Preserved Assets

The research dispatch compiled eleven declarations sorry-free (`lean_run_code`, zero diagnostics).
**None of these are to be re-derived from scratch.** Each has a designated landing site:

| Compiled artifact | Lands in | Phase | Notes |
|---|---|---|---|
| `lemma4_7_ii` | `Soundness.lean`, §"Lemma 4.7", immediately after `lemma4_7_i_ii` | 1 | ~20 lines, structural near-clone of `lemma4_7_i_ii` |
| `mpAnd` | `Soundness.lean`, new §"Λ-Chain Toolkit" | 3 | `⊢ (A ∧ (A ⊃ B)) ⊃ B` |
| `topBase` | same section | 3 | `⊢ ((⊤ ⊃ A) ∧ (A ⊃ B)) ⊃ B` |
| `andMP` | same section | 3 | `⊢ (U ∧ V) ⊃ W → ⊢ U → ⊢ V → ⊢ W` |
| `lambdaChain_step2` | same section | 3 | `⊢ (X ∧ Z) ⊃ Y → ⊢ (X ∧ (Y ⊃ P)) ⊃ (Z ⊃ P)` |
| `lambdaChain_XZ_imp_Y` | `Soundness.lean`, new §"The Λ-Chain Induction" | 4 | **the headline induction**, 3-case structural recursion |
| `psiX_fm` | same section | 4 | `cases ctx.Λ <;> rfl` |
| `primeRhs_fm` | same section | 4 | `cases ctx.Λ <;> rfl` |
| `impL_repaired` | becomes the **body** of `nested_sound_impL` at `Soundness.lean:1306` | 5 | end-to-end assembled during research |
| `hA_derivable` | **not landed in `Cslib/`** — research-only witness | (2) | Documents D2's counterexample. Optionally reproducible as a `CslibTests/` regression; see Phase 8 optional hardening. |
| `hB_derivable` | **not landed in `Cslib/`** — research-only witness | (2) | Same. |

Eight already-landed declarations are reused, not re-proved: `lemma4_7_iii` (`Soundness.lean:549`),
`lemma4_7_iv` (`Soundness.lean:556`), `lemma4_9_fillRhs` (`Soundness.lean:693`),
`OutputCtx.fillRhs_append` (`Context.lean:204`), `InputCtx.fillLhs_fm_antitone`
(`Translation.lean:274`), `OutputCtx.fillLhs_fm_mono` (`Translation.lean:255`),
`deductionTheorem` (with `implyK`/`implyS` feeders), and `buildRhsChain_append`
(`Context.lean:196`). All 18 existing `nested_sound_*` case lemmas must remain untouched.

### Source-to-Implementation Mapping (H3, Tier 1)

**Source**: R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal
Logics*, LMCS 11(3:7), 2015. **BibKey**: `ArisakaDasStrassburger2015`, verified at
`references.bib:939`. **Local corpus**:
`~/Projects/Literature/sources/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics/`
(`source.pdf` p. 10; `chunk_0022.md`, `chunk_0023.md`).

| Source location | Lean identifier | Status | Phase |
|---|---|---|---|
| Lemma 4.7(i), p. 10 | `lemma4_7_i_ii` | landed; **docstring mislabels it as covering (ii)** | 1 (docstring fix) |
| Lemma 4.7(ii), p. 10 | `lemma4_7_ii` | to land | 1 |
| Lemma 4.7(iii)/(iv), p. 10 | `lemma4_7_iii`, `lemma4_7_iv` | landed, reused | 4 |
| Lemma 4.9 (`⊃•`), p. 10, "an induction on `n` together with Lemma 4.7.(ii) and (iv)" | `lambdaChain_XZ_imp_Y` | to land | 4 |
| Lemma 4.9 (`⊃•`), p. 10, "But this follows from `(L_X ∧ L_Z) ⊃ L_Y`" | `lambdaChain_step2` | to land | 3 |
| Theorem 4.1 (`⊃•` case), pp. 9-10 | `nested_sound_impL` | `sorry` at 1315; to discharge | 5 |
| Lemma 4.9 (`cut`), p. 10, "we additionally observe that `A ⊃ A` is always provable" | `nested_sound_cut` | absent; to land | 7 |
| Observation 2.2 / Definition 2.3, p. 5 | `InputCtx.outputPruning` | defective at `Λ = []`; to repair | 2 |

**Verbatim source text for the `⊃•` case** (page 10, `pdftotext -layout -f 10 -l 10`; this PDF's
font encoding drops the `□` glyph, already documented in the module docstring):

```
                            Γ′ {Λ{A◦ }}         Γ′ {Λ{B • }, Π◦ }
                         ⊃• −−−−−−−−−′−−−−−−−−−−−−−•−−−−−−−−−−−−−
                                   Γ {Λ{A ⊃ B }, Π◦ }
where Γ′ { }, Λ{ }, and Π{ } are output contexts. In particular, let
                         Λ{ } = Λ0 , [Λ1 , [. . . , [Λn , { }] . . .] ]   .
Now let P = fm(Π◦ ) and L_i = fm(Λi ) for i = 0 . . . n, and let
    LX = fm(Λ{A◦ }) = L0 ⊃ (L1 ⊃ (L2 ⊃ (· · · ⊃ (Ln ⊃ A) · · · )))          [□s dropped by pdftotext]
    LY = fm(Λ{B • }) = L0 ∧ ♦(L1 ∧ ♦(L2 ∧ ♦(· · · ∧ ♦(Ln ∧ B) · · · )))
    LZ = fm(Λ{A ⊃ B • }) = L0 ∧ ♦(L1 ∧ ♦(L2 ∧ ♦(· · · ∧ ♦(Ln ∧ (A ⊃ B)) · · · )))
To be able to apply Lemma 4.8, we need to show that (LX ∧ (LY ⊃ P )) ⊃ (LZ ⊃ P ) is
provable in HCK + X. But this follows from (LX ∧ LZ ) ⊃ LY , which can be shown provable
in HCK + X using an induction on n together with Lemma 4.7.(ii) and (iv). For the cut-rule
we additionally observe that A ⊃ A is always provable.
```

---

## Postmortem Constraints

Binding rules for all implementation dispatches on this task. Derived from the research report's
adversarial-verification findings and from one additional shape check performed at plan time
(recorded under "Plan-time refinement" below).

**Do NOT**:

- **Do NOT attempt to prove `nested_sound_impL` before Phase 2 lands.** Against the current
  `InputCtx.outputPruning`, the statement is **refutable**, not merely hard. Any tool-call budget
  spent proving it pre-Phase-2 is spent proving something false. Phase 2 is a hard prerequisite.
- **Do NOT route `⊃•` through `lemma4_8` / `OutputCtx.fillFull`**, even though the source
  literally says "To be able to apply Lemma 4.8". Research considered and rejected this:
  `fillFull`'s singleton-case `comma Φ Γ` merge makes `fm(Γ'.fillFull (Λ.fillRhs Ψ))` differ from
  `fm((Γ' ++ Λ).fillRhs Ψ)` by `⊤`-conjuncts, requiring a bridging *implication* rather than an
  equality. Use `lemma4_9_fillRhs` (uniform base case, no singleton merge, shapes match exactly).
  This is a Lean-encoding divergence from the source's stated route, not a mathematical
  disagreement, and it must stay flagged as such in the code comment.
- **Do NOT rename `lemma4_7_i_ii`.** Correct its docstring to say "(i)" only and keep the
  identifier, to avoid a rename cascade through its call sites.
- **Do NOT delete the `tBox` machinery in `InputCtx.fillEmpty_imp_outputPruning_fillRhs`
  (`Translation.lean:300`).** See "Plan-time refinement" below — it collapses to identity only
  for non-empty `ctx.Γ'`; the `Γ' = []` branch still needs it.
- **Do NOT widen `InputCtx.fillEmpty_imp_outputPruning_fillRhs` by dropping its `hΛ : ctx.Λ = []`
  hypothesis.** Under the repair the general-`Λ` version still requires a genuine `◇`/`□`
  polarity argument (`Λ.fillEmpty`'s `comma`/`dia` shape versus `buildRhsChain`'s nested `box`),
  which is out of scope here.
- **Do NOT introduce any new `axiom`, and do NOT add any `sorry`** — including a "temporary" one
  to get the build green. The exit criteria are census 41 to 40 *and* green build simultaneously.
  If a phase cannot close, see Rollback/Contingency; report it, do not paper over it.
- **Do NOT edit any file outside the declared file scope** (`Soundness.lean`, `Rules.lean`,
  `Context.lean`, `Translation.lean`). `Rules.lean` is in scope only in case the `outputPruning`
  repair requires a docstring correction there; its `impL`/`cut` premise *types* are stated via
  `outputPruning` and need no source edit.
- **Do NOT re-derive any Preserved Asset from scratch.** Transcribe from the research report,
  adapting only to the surrounding namespace and style.

**MUST preserve**:

- All 18 existing `nested_sound_*` case lemmas in `Soundness.lean` and their proofs.
- The eight reused declarations listed under Preserved Assets.
- `Context.lean`'s `buildRhsChain_append` and `OutputCtx.fillRhs_append` — the repair relies on
  them, it must not perturb them.
- The `Nested/` module import graph: `Syntax → Context → {Rules, Translation} → Soundness`.
  `Translation` additionally imports `CS5`. Do not add imports that would create a cycle.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):

1. **The `outputPruning` repair is `ctx.Γ' ++ (ctx.Λ.headD NestedLhs.empty :: ctx.Λ.tail)`.**
   `headD .empty :: tail` is the identity on non-empty `Λ` and yields `[∅]` on `Λ = []`, so this
   changes only the `Λ = []` case. It is a repair *toward* the source (Observation 2.2 /
   Definition 2.3 keep the hole where `Γ{ }` had it; only the `Π` subtree is removed), not a
   divergence from it.
2. **`lemma4_9_fillRhs`, not `lemma4_8`, is the lift through `Γ'`.** See the second Do-NOT above.
3. **The `⊃•` proof takes a two-case split on `ctx.Γ'`.** With `Γ' = G :: r'`,
   `OutputCtx.fillRhs_append` transports premise 1 definitionally. With `Γ' = []`, `hA` reduces to
   an outright theorem, so `necessitation` + `implyK` applies. This asymmetry is intentional and
   sound: a derivable premise can be necessitated; a hypothesis inside a box cannot.
4. **The `cut` case reuses the repaired `impL` argument with `B := A`,** routed through
   `InputCtx.fillLhs_fm_antitone` plus one bridging induction. It is not an independent
   development.

**Plan-time refinement to the research report** (verified at plan time by reading
`Context.lean:100-190`; supersedes the report's Finding 2 sentence "becomes trivially provable:
both sides converge to `Γ'.fillRhs (.box ∅ π)`"):

Under the repair, with `ctx.Λ = []`, `ctx.outputPruning = ctx.Γ' ++ [∅]`, and:

| `ctx.Γ'` | `ctx.fillEmpty` | `ctx.outputPruning.fillRhs ctx.π` | Bridge needed |
|---|---|---|---|
| `G :: r'` | `(G, buildRhsChain r' (box ∅ π))` | `(G, buildRhsChain (r' ++ [∅]) π)` = same, via `buildRhsChain_append` | none — identity implication |
| `[]` | `(∅, box ∅ π)` | `(∅, π)` | **still one `□` apart — `tBox` retained** |

So `InputCtx.fillEmpty_imp_outputPruning_fillRhs` keeps its statement and its `tBox` step; only
its proof needs restructuring into a two-case split on `ctx.Γ'`. Phase 2 must not delete the
`tBox`/`cs5DerivTopImpElim` machinery.

---

## Goals & Non-Goals

- **Goals**:
  - Land Lemma 4.7(ii) and correct the module docstring's false "source duplication" claim (D1).
  - Repair `InputCtx.outputPruning` so `nested_sound_impL` is true as stated (D2).
  - Land the Λ-chain induction and discharge `nested_sound_impL` sorry-free.
  - Land `nested_sound_cut` and the missing `.cut` arm so the library compiles (D3).
  - Cslib bare-sorry census 41 to 40; `lake build` RED to green; full CI gate green.
- **Non-Goals**:
  - Cut admissibility / cut elimination (the source's §6, Stage F) — `cut` stays a primitive
    constructor, exactly as `SeqProof.cut` is in `LJ/Basic.lean`.
  - Generalising `InputCtx.fillEmpty_imp_outputPruning_fillRhs` beyond `ctx.Λ = []`.
  - Reducing any of the other 40 sorries in the Cslib census.
  - A formal Lean refutation of the un-repaired `impL` (optional hardening only, Phase 8).

## Risks & Mitigations

- **Risk (highest residual)**: `OutputCtx.fillLhs_empty_imp_fillEmpty` — the bridging induction
  for `cut` — is the **one piece the research dispatch did not compile**. It was reasoned out and
  hand-checked at `|Λ| = 0, 1, 2` only.
  **Mitigation**: it is isolated in its own phase (Phase 6) with its own green gate, placed off
  the `impL` critical path so its failure cannot block Phases 3-5. It mirrors
  `OutputCtx.fillLhs_fm_mono`'s existing three-case recursion in the same file; use that as the
  template. See Rollback/Contingency if it does not close.
- **Risk**: the D2 blast radius was **grep-checked but not build-checked**. `grep` confirms
  `outputPruning` occurs only in `Context.lean` (the definition), `Rules.lean` (two premise types
  plus docstrings), `Translation.lean` (the bridge plus docstrings), and `Soundness.lean`
  (`nested_sound_impL` plus docstrings) — `Completeness.lean` / `CS5Completeness.lean` were never
  read. The first `lake build` after Phase 2 is the real test.
  **Mitigation**: Phase 2 budgets for fallout explicitly and gates on
  `lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Rules` **and** `...Nested.Translation`
  both green — both are downstream of `Context` and upstream of `Soundness`, so they isolate the
  repair's fallout from the pre-existing `cut` error.
- **Risk**: `lake test` cannot be assessed until the library builds, so Phase 8 is the first
  moment any test signal exists.
  **Mitigation**: Phase 8 is a dedicated gate phase with no new proof obligations, so it has full
  budget to absorb test fallout.
- **Risk**: `lake exe lint-style` is named in the task's invariants but is **not a defined target
  in this repository's `lakefile.toml`** (which defines `lean_exe checkInitImports` only, plus
  `testDriver = CslibTests` and `lintDriver = batteries/runLinter`).
  **Mitigation**: Phase 8 attempts it, records the outcome truthfully, and substitutes the
  repository's actual style gates (`lake exe mk_all --check`, and the `weak.linter.style.*`
  options that run inside `lake build`). Do not report the invariant as met by a command that did
  not run.

---

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 6 | 1 (for 3), 2 (for 6) |
| 3 | 4 | 1, 3 |
| 4 | 5 | 2, 4 |
| 5 | 7 | 5, 6 |
| 6 | 8 | 7 |

Phases within the same wave can execute in parallel. **H7 territory contract**: wave-1 phases have
disjoint file ownership (Phase 1 owns `Soundness.lean`; Phase 2 owns `Context.lean` +
`Translation.lean` + `Rules.lean` docstrings). Wave-2 phases likewise (Phase 3 owns
`Soundness.lean`; Phase 6 owns `Translation.lean`). If dispatched sequentially by the orchestrator,
the wave table still records the true dependency structure; a later phase must never be started
before every phase it is blocked by is `[COMPLETED]`.

**Ordering rationale (build is RED at the start)**: the pre-existing `cut` non-exhaustiveness
error means `Soundness.lean` cannot compile until Phase 7. Every earlier phase that touches
`Soundness.lean` therefore verifies against a **known, named** residual error rather than a clean
build, and each such phase states the exact expected error text. The build reaches green at
Phase 7 — as early as is honest, because `cut`'s proof consumes the repaired `impL`, so `cut`
cannot precede it. Phases 2 and 6 deliver genuine intermediate green checkpoints on the
`Context`/`Rules`/`Translation` modules, which are upstream of the red one.

---

### Phase 1: Land `lemma4_7_ii` and correct the module docstring's (i)/(ii) duplication claim [COMPLETED]

- **Goal:** Land the missing Lemma 4.7(ii) and remove the false claim that Lemma 4.7 parts (i)
  and (ii) display the same formula.
- **Files:** `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` (sole owner)
- **Tasks:**
  - [x] Add `lemma4_7_ii` immediately after `lemma4_7_i_ii` (currently `Soundness.lean:503`),
        with signature
        `theorem lemma4_7_ii (D : Proposition Atom) {A B C : Proposition Atom} (h : Derivable (@CS5ModalAxiom Atom) ((A.and B).imp C)) : Derivable (@CS5ModalAxiom Atom) (((D.imp A).and (D.and B)).imp (D.and C))`.
        Proof shape (from research, compiled): one `deductionTheorem` discharge of the conjunctive
        hypothesis, `andE1`/`andE2` projections, `andI` recombination, MP against the weakened
        hypothesis, `andI` to rebuild `D ∧ C`. Structurally a near-clone of `lemma4_7_i_ii`.
  - [x] Give it a docstring citing "**Lemma 4.7(ii)** (page 10)" and the `ArisakaDasStrassburger2015`
        BibKey, matching the citation style of `lemma4_7_iii`/`lemma4_7_iv`.
  - [x] Rewrite the module-docstring paragraph at `Soundness.lean:35-45` ("Lemma 4.7(i)/(ii): A
        Documented Source Duplication"). Replace the duplication claim with the corrected fact:
        (i) is `((D ⊃ A) ∧ (D ⊃ B)) ⊃ (D ⊃ C)`, (ii) is `((D ⊃ A) ∧ (D ∧ B)) ⊃ (D ∧ C)`; they are
        different statements; `∧`/`⊃` glyphs render cleanly in this PDF, only `□` drops. Note that
        `lemma4_7_i_ii` retains its identifier for call-site stability but covers part (i) only.
  - [x] Correct `lemma4_7_i_ii`'s own docstring (the "This is Lemma 4.7(i) *and* (ii)" sentence
        and the pointer at `Soundness.lean:494-496`) to say part (i) only, pointing at the new
        `lemma4_7_ii` for part (ii).
  - [x] Do NOT rename `lemma4_7_i_ii`.
- **Estimated output:** ~50 lines (20 proof, 30 docstring).
- **Timing:** ~45 minutes.
- **Depends on:** none
- **Verification (build is RED; expect exactly the pre-existing error and no others):**
  ```
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
  ```
  Expected: FAILS with exactly two diagnostics and no more —
  `Soundness.lean:<line>:2: Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)` and
  `Soundness.lean:<line>:8: declaration uses 'sorry'` (line numbers shift by the lines added).
  **Any additional error is Phase-1 fallout and must be fixed before the phase is `[COMPLETED]`.**
  ```
  grep -n "theorem lemma4_7_ii " Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean
  bash .claude/scripts/lean-sorry-census.sh Cslib
  ```
  Expected: the `grep` finds exactly one hit; census still reports `sorry_count: 41` (unchanged —
  this phase adds no sorry and removes none).
- **Done when:** `lemma4_7_ii` elaborates with no `sorry` and no error of its own, the module's
  only remaining errors are the two named above, and no docstring in the file still asserts that
  4.7(i) and (ii) are the same formula.

---

### Phase 2: Repair `InputCtx.outputPruning` and restructure the `Λ = []` pruning bridge [COMPLETED]

- **Goal:** Make `nested_sound_impL` true as stated by giving `outputPruning` the box layer it
  drops at `ctx.Λ = []`, and repair the one downstream proof that unfolds it.
- **Files:** `Cslib/.../Nested/Context.lean`, `Cslib/.../Nested/Translation.lean`,
  `Cslib/.../Nested/Rules.lean` (docstrings only, if needed). Sole owner of all three.
- **Tasks:**
  - [x] Replace `Context.lean:188` with
        `def InputCtx.outputPruning (ctx : InputCtx Atom) : OutputCtx Atom := ctx.Γ' ++ (ctx.Λ.headD NestedLhs.empty :: ctx.Λ.tail)`.
  - [x] Update its docstring: explain that `headD .empty :: tail` is the identity on non-empty `Λ`
        and yields `[∅]` on `Λ = []`, retaining the box layer the hole sits under; cite
        Observation 2.2 / Definition 2.3 (`Γ⇓{ } = Γ'{Λ{ }}` keeps the hole where `Γ{ }` had it,
        only the `Π` subtree is removed); note this reproduces the source's own `[C•, ∅]`
        two-layer decomposition of Example 2.1's `Γ₂{ }`.
  - [x] Update the `Context.lean:87` "Output Pruning" docstring paragraph if it still describes the
        old plain-append semantics.
  - [x] Restructure `InputCtx.fillEmpty_imp_outputPruning_fillRhs` (`Translation.lean:300`).
        **Keep the statement and the `hΛ : ctx.Λ = []` hypothesis unchanged.** Restructure the
        proof as a two-case split on `ctx.Γ'` per the plan-time refinement table above:
        `Γ' = G :: r'` is an identity implication (both sides reduce to
        `(G, buildRhsChain r' (box ∅ π))` via `buildRhsChain_append`); `Γ' = []` retains the
        existing `tBox` + `cs5DerivTopImpElim` argument (`(∅, box ∅ π)` versus `(∅, π)`).
        **Do not delete the `tBox` machinery.**
  - [x] Update `Translation.lean:68` and `Translation.lean:293` docstrings to describe the new
        two-case structure and to note that the `Λ = []` restriction is retained deliberately
        (the general-`Λ` version needs a `◇`/`□` polarity argument, out of scope).
  - [x] Update `Rules.lean:62` and `Rules.lean:223` docstrings if they describe `outputPruning` as
        plain append. **No source change to `impL`/`cut` premise types** — they are stated via
        `outputPruning` and pick the repair up automatically.
  - [x] Fix any additional build fallout the repair surfaces in `Context.lean`/`Rules.lean`/
        `Translation.lean`. If fallout appears in a file outside the declared scope, STOP and
        report it rather than widening scope silently.
- **Estimated output:** ~90 lines (30 proof restructuring, 60 docstrings).
- **Timing:** ~1 hour.
- **Depends on:** none
- **Verification (these modules are upstream of the red one and MUST be fully green):**
  ```
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Context
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Rules
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Translation
  ```
  Expected: **all three succeed with zero errors** — this is a genuine green checkpoint even while
  `Soundness` remains red. This is the blast-radius test for D2.
  ```
  grep -rn "outputPruning" --include=*.lean Cslib/ | grep -v "^Cslib.*:.*--"
  ```
  Expected: hits confined to `Nested/Context.lean`, `Nested/Rules.lean`, `Nested/Translation.lean`,
  `Nested/Soundness.lean`. **A hit in any other file means the grep-checked blast radius was
  wrong — stop and report before proceeding.**
- **Done when:** the three named modules build green, the definition reads exactly as specified,
  `InputCtx.fillEmpty_imp_outputPruning_fillRhs` still carries `hΛ` and still contains its `tBox`
  step, and the `outputPruning` grep is confined to `Nested/`.
- **Commit immediately on green** — this is the highest-value checkpoint in the plan.

---

### Phase 3: Land the four propositional combinators of the Λ-chain toolkit [COMPLETED]

- **Goal:** Land `mpAnd`, `topBase`, `andMP`, and `lambdaChain_step2` — the propositional
  ingredients the induction and the assembly consume.
- **Files:** `Cslib/.../Nested/Soundness.lean` (sole owner)
- **Tasks:**
  - [x] Open a new section `/-! ## Λ-Chain Toolkit (Lemma 4.9, `⊃•`) -/` in `Soundness.lean`,
        placed after the Lemma 4.9 section and before the `⊃•` section at line ~1294.
  - [x] Land `mpAnd (A B : Proposition Atom) : Derivable _ ((A.and (A.imp B)).imp B)` —
        `deductionTheorem` + `andE1`/`andE2` + MP, ~10 lines.
  - [x] Land `topBase (A B : Proposition Atom) : Derivable _ (((Proposition.top.imp A).and (A.imp B)).imp B)`
        — same shape; `⊤ = ⊥ ⊃ ⊥` discharged via `efq`, ~10 lines.
  - [x] Land `andMP : ⊢ (U ∧ V) ⊃ W → ⊢ U → ⊢ V → ⊢ W` — 3-line `andI` + MP combinator.
  - [x] Land `lambdaChain_step2 {X Y Z P : Proposition Atom} (h : Derivable _ ((X.and Z).imp Y)) : Derivable _ ((X.and (Y.imp P)).imp (Z.imp P))`
        — two nested `deductionTheorem` discharges (of the conjunction, then of `Z`), ~15 lines.
        Docstring cites the source's "But this follows from `(L_X ∧ L_Z) ⊃ L_Y`" sentence.
  - [x] Mark `mpAnd`, `topBase`, `andMP` `private` if they are not intended as public API, matching
        the file's existing convention for `cs5Deriv*` helpers. `lambdaChain_step2` is public
        (it is a named source step).
- **Estimated output:** ~70 lines.
- **Timing:** ~45 minutes.
- **Depends on:** 1
- **Verification (build still RED; expect only the pre-existing errors):**
  ```
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
  ```
  Expected: FAILS with **only** the `Missing cases: _, (NestedProof.cut ...)` error and the
  `declaration uses 'sorry'` warning. No error may point at any of the four new declarations.
  ```
  grep -cn "theorem mpAnd \|theorem topBase \|theorem andMP \|theorem lambdaChain_step2 " Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean
  ```
  Expected: `4`.
- **Done when:** all four declarations elaborate cleanly (no error, no `sorry`), and the module's
  diagnostic set is unchanged from Phase 1's.

---

### Phase 4: Land `lambdaChain_XZ_imp_Y` (the Λ-chain induction) and the two shape lemmas [NOT STARTED]

- **Goal:** Land the induction this task is named for, plus the two `Λ = []` normalisation shape
  lemmas the assembly needs.
- **Files:** `Cslib/.../Nested/Soundness.lean` (sole owner)
- **Tasks:**
  - [ ] Land, in the Λ-Chain Toolkit section, the three-case structural recursion (from research,
        compiled sorry-free):
        ```lean
        theorem lambdaChain_XZ_imp_Y (A B : Proposition Atom) :
            ∀ (Λ : OutputCtx Atom),
              Derivable (@CS5ModalAxiom Atom)
                (((Λ.fillRhs (.atom A)).fm.and (Λ.fillLhs (.atom (A.imp B))).fm).imp
                  (Λ.fillLhs (.atom B)).fm)
          | []               => topBase A B
          | [Λ₀]             => lemma4_7_ii Λ₀.fm (mpAnd A B)
          | Λ₀ :: Λ₁ :: rest =>
              lemma4_7_ii Λ₀.fm (lemma4_7_iv (lambdaChain_XZ_imp_Y A B (Λ₁ :: rest)))
        ```
  - [ ] Docstring must record: the motive
        `P(Λ) := ⊢ ((Λ.fillRhs A°).fm ∧ (Λ.fillLhs (A⊃B)•).fm) ⊃ (Λ.fillLhs B•).fm` with `A`, `B`
        fixed outside the recursion as parameters; the three-way `[]` / `[Λ₀]` / `Λ₀ :: Λ₁ :: rest`
        split matching `OutputCtx.fillLhs`'s own recursion (and `OutputCtx.fillLhs_fm_mono`'s and
        `lemma4_8`'s); the reading against the source's `Λ{ } = Λ₀, [Λ₁, [ …, [Λₙ, { }] … ]]`
        (`[]` is the degenerate `Λ{ } = { }` where `fillRhs` supplies the `⊤` antecedent, `[Λ₀]` is
        `n = 0`, `Λ₀ :: Λ₁ :: rest` is `n ≥ 1`); and the verbatim source sentence "using an
        induction on n together with Lemma 4.7.(ii) and (iv)" with the BibKey.
  - [ ] Note in the docstring the definitional identity the cons-cons step relies on, which holds
        by `rfl`: `(buildRhsChain (Λ₁::rest) Ψ).fm = □ ((OutputCtx.fillRhs (Λ₁::rest) Ψ).fm)` —
        this is what lets `lemma4_7_iv`'s `□A ∧ ◇B ⊃ ◇C` shape line up with no rewriting.
  - [ ] Land `psiX_fm (ctx : InputCtx Atom) (A : Proposition Atom) : (buildRhsChain (ctx.Λ.headD .empty :: ctx.Λ.tail) (NestedRhs.atom A)).fm = Proposition.box ((ctx.Λ.fillRhs (.atom A)).fm)`
        — `cases ctx.Λ <;> rfl`.
  - [ ] Land `primeRhs_fm (ctx : InputCtx Atom) (A : Proposition Atom) : ((ctx.Λ.headD .empty :: ctx.Λ.tail).fillRhs (NestedRhs.atom A)).fm = (ctx.Λ.fillRhs (.atom A)).fm`
        — `cases ctx.Λ <;> rfl`.
- **Estimated output:** ~70 lines (25 proof, 45 docstring).
- **Timing:** ~45 minutes.
- **Depends on:** 1, 3
- **Verification (build still RED; expect only the pre-existing errors):**
  ```
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
  ```
  Expected: FAILS with **only** the `Missing cases: _, (NestedProof.cut ...)` error and the
  `declaration uses 'sorry'` warning. No error may point at the three new declarations, and in
  particular no `fail to show termination` on `lambdaChain_XZ_imp_Y`.
  ```
  grep -n "theorem lambdaChain_XZ_imp_Y \|theorem psiX_fm \|theorem primeRhs_fm " Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean
  ```
  Expected: exactly three hits.
- **Done when:** the induction elaborates and its structural recursion is accepted, both shape
  lemmas close by `cases … <;> rfl`, and the module's diagnostic set is unchanged from Phase 3's.

---

### Phase 5: Discharge `nested_sound_impL` — remove the sorry at `Soundness.lean:1315` [NOT STARTED]

- **Goal:** Replace the strategic `sorry` with the assembled proof, taking the census 41 to 40.
- **Files:** `Cslib/.../Nested/Soundness.lean` (sole owner)
- **Tasks:**
  - [ ] Replace the body of `nested_sound_impL` (currently `Soundness.lean:1306-1315`) with the
        research-compiled assembly:
        1. `set ΨX := buildRhsChain (ctx.Λ.headD .empty :: ctx.Λ.tail) (NestedRhs.atom A)`,
           `set ΨY := NestedRhs.box (ctx.Λ.fillLhs (.atom B)) ctx.π`,
           `set ΨZ := NestedRhs.box (ctx.Λ.fillLhs (.atom (A.imp B))) ctx.π`.
        2. `h4 : ⊢ (ΨX.fm ∧ ΨY.fm) ⊃ ΨZ.fm` via
           `lemma4_7_iii (lambdaChain_step2 (P := ctx.π.fm) (lambdaChain_XZ_imp_Y A B ctx.Λ))`,
           after `rw [psiX_fm ctx A]`.
        3. `h5 := lemma4_9_fillRhs h4 ctx.Γ'` — the lift through `Γ'`.
        4. `hAX : ⊢ (ctx.Γ'.fillRhs ΨX).fm`, by `match hΓ : ctx.Γ'` — `[]` uses `necessitation` +
           `implyK` on `hA` (which is a theorem, hence necessitable); `G :: r'` uses
           `OutputCtx.fillRhs_append` to transport `hA` definitionally.
        5. `exact andMP h5 hAX hB`.
  - [ ] Rewrite the section docstring at `Soundness.lean:1294-1303` (`/-! ## ⊃• (impL): Deferred,
        Strategic Sorry -/`). Retitle to describe the landed proof. Record: the source's page-10
        `L_X, L_Y, L_Z` construction; the flagged Lean-encoding divergence (routing through
        `lemma4_9_fillRhs` instead of `lemma4_8`/`fillFull`, with the `⊤`-conjunct reason); and why
        the two-case split on `ctx.Γ'` is needed and sound (a derivable premise can be necessitated,
        a hypothesis inside a box cannot).
  - [ ] Rewrite `nested_sound_impL`'s own docstring from "deferred, see the section docstring above"
        to a statement of what it proves, citing Theorem 4.1's `⊃•` case, pp. 9-10.
  - [ ] Update the `nested_sound` section docstring (`Soundness.lean:1320-1326`) — remove "Every
        constructor except `impL` is fully discharged", which is doubly inaccurate (`cut` is absent
        entirely). Phase 7 finishes this sentence; Phase 5 may leave a forward-pointing note.
  - [ ] Remove the `-- sorry: …` deferral comment block entirely.
- **Estimated output:** ~90 lines (55 proof, 35 docstring).
- **Timing:** ~1 hour 15 minutes.
- **Depends on:** 2, 4
- **Verification (build still RED on `cut` only — the sorry warning must be GONE):**
  ```
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
  ```
  Expected: FAILS with **exactly one** diagnostic —
  `Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)`. The
  `declaration uses 'sorry'` warning MUST be gone. Any other error is Phase-5 fallout.
  ```
  bash .claude/scripts/lean-sorry-census.sh Cslib
  ```
  Expected: `sorry_count: 40`, and
  `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1315` **absent** from the
  inventory (no `Nested/Soundness.lean` entry at any line).
- **Done when:** the census reads 40 with no `Nested/Soundness.lean` entry, and the module's only
  remaining error is the `cut` non-exhaustiveness.
- **Note:** `#print axioms nested_sound_impL` cannot run yet — it requires a compiled module, and
  the module is still red on `cut`. That check is deferred to Phase 8. Do not claim it passed here.

---

### Phase 6: Land `OutputCtx.fillLhs_empty_imp_fillEmpty` (the `cut` bridging induction) [NOT STARTED]

- **Goal:** Land the one piece the research dispatch did not compile: the bridge between
  `fillLhs ∅` and `fillEmpty`.
- **Files:** `Cslib/.../Nested/Translation.lean` (sole owner)
- **Tasks:**
  - [ ] Land
        `theorem OutputCtx.fillLhs_empty_imp_fillEmpty : ∀ (ctx : OutputCtx Atom), Derivable (@CS5ModalAxiom Atom) ((ctx.fillLhs NestedLhs.empty).fm.imp ctx.fillEmpty.fm)`
        immediately after `OutputCtx.fillLhs_fm_mono` (`Translation.lean:255`), **mirroring that
        theorem's existing three-case recursion exactly**:
        - `[]` — the two sides are equal (`fillLhs [] ∅ = ∅` and `fillEmpty [] = ∅`); identity
          implication.
        - `[Γ]` — `fillLhs [Γ] ∅ = comma Γ ∅` (`fm = L₀ ∧ ⊤`) versus `fillEmpty [Γ] = Γ`
          (`fm = L₀`); discharge the `⊤` conjunct via `andE1`.
        - `Γ :: Γ₂ :: rest` — `and`-congruence in the right conjunct
          (`cs5DerivAndCongrRight`) over `◇`-monotonicity (`cs5DerivDiaMono`) applied to the IH,
          exactly as `fillLhs_fm_mono`'s own cons-cons step does.
  - [ ] Docstring: state the `⊤`-conjunct-only difference, cite Observation 2.2's `Γ{∅}` collapse
        semantics (`OutputCtx.fillEmpty` collapses the innermost level rather than substituting),
        and name `OutputCtx.fillLhs_fm_mono` as the structural template.
  - [ ] If the `[Γ]` or cons-cons case does not close as sketched, use `lean_goal` /
        `lean_multi_attempt` to inspect the actual `fm` shapes before adjusting — **do not** change
        the statement to something weaker without recording why.
- **Estimated output:** ~40 lines.
- **Timing:** ~1 hour (highest-uncertainty phase; budget generously).
- **Depends on:** 2
- **Verification (this module is upstream of the red one and MUST be fully green):**
  ```
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Translation
  ```
  Expected: **succeeds with zero errors.** A genuine green checkpoint.
  ```
  grep -n "theorem OutputCtx.fillLhs_empty_imp_fillEmpty" Cslib/Logics/Modal/Metalogic/Constructive/Nested/Translation.lean
  bash .claude/scripts/lean-sorry-census.sh Cslib
  ```
  Expected: exactly one `grep` hit; census unchanged at whatever Phase 5 left it (40 if Phase 5 has
  landed, 41 if this phase runs first in its wave).
- **Done when:** `Translation` builds green with the new theorem present and sorry-free.
- **Commit immediately on green.**

---

### Phase 7: Land `nested_sound_cut` and the missing `.cut` arm — build RED to GREEN [NOT STARTED]

- **Goal:** Close the last `NestedProof` constructor and take the library from RED to green.
- **Files:** `Cslib/.../Nested/Soundness.lean` (sole owner)
- **Tasks:**
  - [ ] Land `nested_sound_cut (ctx : InputCtx Atom) (A : Proposition Atom) (hA : Derivable (@CS5ModalAxiom Atom) (ctx.outputPruning.fillRhs (.atom A)).fm) (hB : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom A)).fm) : Derivable (@CS5ModalAxiom Atom) ctx.fillEmpty.fm`,
        matching `NestedProof.cut`'s premise/conclusion types at `Rules.lean:299-301`. Proof route
        (the source's own one-liner, "For the cut-rule we additionally observe that `A ⊃ A` is
        always provable"):
        1. Apply the now-landed `nested_sound_impL ctx A A hA hB` to obtain
           `⊢ (ctx.fillLhs (.atom (A.imp A))).fm`.
        2. `⊢ A ⊃ A` gives `⊢ ⊤ ⊃ fm((A ⊃ A)•)`; feed it to `InputCtx.fillLhs_fm_antitone`
           (`Translation.lean:274`, fully general in `ctx`) to get
           `⊢ (ctx.fillLhs (A ⊃ A)•).fm ⊃ (ctx.fillLhs ∅).fm`, and MP.
        3. Compose with `OutputCtx.fillLhs_empty_imp_fillEmpty` (Phase 6) lifted appropriately to
           reach `ctx.fillEmpty.fm`. Note `InputCtx.fillEmpty = ctx.Γ'.fillRhs (.box ctx.Λ.fillEmpty ctx.π)`
           while `ctx.fillLhs ∅ = ctx.Γ'.fillRhs (.box (ctx.Λ.fillLhs ∅) ctx.π)` — the Phase-6
           bridge sits at the `ctx.Λ` level and lifts through `□` (`cs5DerivBoxMono`, contravariant
           in the antecedent — use `cs5DerivImpCongrLeft` as `fillLhs_fm_antitone` does) and then
           through `ctx.Γ'` (`OutputCtx.fillRhs_fm_mono`).
  - [ ] Docstring citing Lemma 4.9's `cut` sentence, p. 10, with the BibKey; state explicitly that
        this is soundness of `cut` as a primitive, **not** cut admissibility (§6, out of scope).
  - [ ] Add the arm `| _, .cut ctx A p q => nested_sound_cut ctx A (nested_sound p) (nested_sound q)`
        to `nested_sound`, placed to match `Rules.lean`'s constructor order (after `.bStruct`).
  - [ ] Correct the `nested_sound` section docstring: all 19 constructors are now discharged; remove
        the stale "Every constructor except `impL`" sentence and any residual forward-pointing note
        left by Phase 5.
- **Estimated output:** ~70 lines.
- **Timing:** ~1 hour.
- **Depends on:** 5, 6
- **Verification (the RED-to-green transition — this is the phase that must flip it):**
  ```
  lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
  ```
  Expected: **succeeds with zero errors and zero warnings.**
  ```
  lake build
  ```
  Expected: **succeeds** for the whole `Cslib` default target.
  ```
  bash .claude/scripts/lean-sorry-census.sh Cslib
  ```
  Expected: `sorry_count: 40`, no `Nested/Soundness.lean` entry.
- **Done when:** `lake build` is green for the first time in this task, and the census is 40.
- **Commit immediately on green** — this is the milestone the whole plan exists to reach.

---

### Phase 8: Full CI gate, axiom check, and census re-verification [NOT STARTED]

- **Goal:** Prove every stated exit invariant with a command that actually ran, and record honestly
  any invariant whose named command does not exist in this repository.
- **Files:** none required (fix-forward edits within the declared file scope only if a gate fails).
- **Tasks:**
  - [ ] Run the axiom check now that the module compiles:
        `#print axioms nested_sound_impL`, `#print axioms nested_sound_cut`, `#print axioms nested_sound`
        (via `lean_run_code` or a scratch file — **do not** leave `#print` commands in `Cslib/`,
        `scripts/pre-pr-check.sh` step 2 flags debug artifacts).
  - [ ] Run the CI gates in order, recording each result verbatim:
        `lake build`, `lake exe checkInitImports`, `lake exe mk_all --check`, `lake lint`,
        `lake test`.
  - [ ] Attempt `lake exe lint-style`. It is **not** a defined target in this repository's
        `lakefile.toml` (which declares only `lean_exe checkInitImports`). Record the actual
        outcome; if it does not exist, say so explicitly in the summary and cite
        `lake exe mk_all --check` plus `lake build`'s `weak.linter.style.*` options as the
        substituted style gates. **Do not report this invariant as met by a command that did not run.**
  - [ ] Run `bash scripts/pre-pr-check.sh` and review its four checks (note: its step 1 greps the
        whole `Cslib/Logics/Modal/` tree for `sorry` and will still report the pre-existing
        `FrameSoundness.lean:1270` sorry — that is out of scope and expected).
  - [ ] Re-run `bash .claude/scripts/lean-sorry-census.sh Cslib` and diff the inventory against the
        41-entry baseline to confirm exactly one entry was removed and none added.
  - [ ] **Optional hardening (recommended, do only if all gates above are green):** add a regression
        `example` in `CslibTests/` formalising D2's counterexample against
        `cs5_soundness_derivable''` (`CS5.lean:446`), so the `Λ = []` off-by-one cannot silently
        return. The research report's `hA_derivable`/`hB_derivable` are the compiled starting
        point. Building a `CKValidFC cs5FC''` instance was **not** attempted during research —
        if it does not close within a bounded attempt, drop it and say so; it is not on the
        critical path and must not be allowed to turn a green task red.
- **Estimated output:** ~0-60 lines (0 if all gates pass and hardening is dropped).
- **Timing:** ~45 minutes.
- **Depends on:** 7
- **Verification:**
  ```
  lake build
  lake exe checkInitImports
  lake exe mk_all --check
  lake lint
  lake test
  bash .claude/scripts/lean-sorry-census.sh Cslib
  ```
  Expected: every command exits 0; census `sorry_count: 40`.
  `#print axioms nested_sound_impL` expected to list only `propext`/`Classical.choice`/`Quot.sound`
  (or fewer) — **`sorryAx` must be absent**.
- **Done when:** every exit invariant below is backed by a command that ran and passed, or is
  explicitly recorded as unrunnable-in-this-repository with the substitute named.

---

## Testing & Validation

Exit criteria for the task as a whole. Each must be backed by a command that actually ran:

- [ ] `lake build` green (RED at baseline `88b198bf`; flips at Phase 7).
- [ ] Cslib bare-sorry census 41 to **40**, via `bash .claude/scripts/lean-sorry-census.sh Cslib`.
- [ ] `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1315` absent from the census
      inventory; no `Nested/Soundness.lean` entry at any line.
- [ ] `#print axioms nested_sound_impL` free of `sorryAx`; likewise `nested_sound_cut` and
      `nested_sound`.
- [ ] No new `axiom` declarations anywhere in the diff (`git diff | grep -n '^+.*\baxiom\b'` empty).
- [ ] `lake exe checkInitImports` green.
- [ ] `lake lint` green.
- [ ] `lake test` green (first assessable at Phase 8 — the library did not build before then).
- [ ] `lake exe mk_all --check` green.
- [ ] `lake exe lint-style` — attempted; result recorded truthfully including "target not defined
      in this repository" if that is the outcome.
- [ ] Intermediate green gates: `Nested.Context`, `Nested.Rules`, `Nested.Translation` all build
      green from Phase 2 onward.

## Artifacts & Outputs

- `specs/570_nested_sound_impL_lambda_chain_induction/plans/01_lambda-chain-induction-plan.md` (this file)
- `specs/570_nested_sound_impL_lambda_chain_induction/summaries/01_lambda-chain-induction-summary.md`
- Modified: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Context.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Translation.lean`
- Modified (docstrings only, if needed): `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Rules.lean`
- Possibly added (optional hardening): a regression `example` under `CslibTests/`

## Rollback/Contingency

- **Per-phase commits.** Each phase commits on its own green gate
  (`task 570 phase {P}: {name}`). Phases 2, 6, and 7 are the three real green checkpoints;
  commit each the moment its gate passes. Rollback of any phase is `git revert` of its commit.
- **If Phase 2's build surfaces fallout outside the declared file scope** (i.e. the grep-checked
  blast radius was wrong): STOP. Do not widen scope silently. Report the affected files and the
  error text; the scope expansion is the orchestrator's call, not the implementer's.
- **If Phase 6's bridging induction does not close** (the highest residual risk — it is the one
  piece research did not compile): it is off the `impL` critical path, so Phases 3-5 and the
  census 41-to-40 invariant still land. Phase 7 then cannot close. In that case: mark Phase 6
  `[BLOCKED]`, keep Phases 1-5 committed and green-gated, and report explicitly that `lake build`
  remains RED on the pre-existing `cut` error. **Do not** insert a `sorry` into `nested_sound_cut`
  to force a green build — that trades a real invariant (census 40) for a cosmetic one and
  violates this plan's Postmortem Constraints. If a strategic sorry is nonetheless judged
  necessary, it must be reported as a plan-unanticipated deviation (there is no
  `## Planned Strategic Sorries` table in this plan — `plan_metadata.skeleton` is `false`), and
  evaluated under the weaker claim on the `anti-analysis.md` 5-condition test.
- **If Phase 5's assembly does not reproduce the research-compiled proof**: the report's `impL_repaired`
  compiled end-to-end with `lambdaChain_XZ_imp_Y` and `lambdaChain_step2` supplied as hypotheses,
  and both were independently proved in the same session. Diff the landed statements against the
  report's signatures before touching the proof body — a signature drift is the likeliest cause.
- **Whole-task rollback**: `git revert` the phase commits in reverse order. The baseline
  (`88b198bf`, red build, census 41) is a committed state, so returning to it is always possible.
