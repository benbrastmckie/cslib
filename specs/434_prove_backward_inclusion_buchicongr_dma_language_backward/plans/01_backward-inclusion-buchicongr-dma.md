# Implementation Plan: Task #434

- **Task**: 434 - prove_backward_inclusion_buchicongr_dma_language_backward
- **Status**: [IMPLEMENTING]
- **Effort**: 1.5 hours
- **Dependencies**: None (independent of forward direction; parent task 241)
- **Research Inputs**: Task description (self-contained API map); spawn analysis `specs/241_mcnaughton_theorem/reports/03_spawn-analysis.md`; orchestrator handoff `specs/241_mcnaughton_theorem/.orchestrator-handoff.json`
- **Artifacts**: plans/01_backward-inclusion-buchicongr-dma.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, cslib.md, lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Prove the backward inclusion `buchiCongr_DMA_language_backward : language (buchiCongr_DMA na) ⊆ language na` as a new `private lemma` in `Cslib/Computability/Languages/OmegaRegularLanguage.lean`, placed immediately after `buchiCongr_DMA_language_forward` (~line 446) and before `proof_wanted buchiCongr_DMA_language_eq` (line 460). The proof unfolds the Muller acceptance condition into accept-set membership, destructures the accept witness `(b ∈ infOcc, a, ys)`, establishes that `xs` itself lies in `buchiFamily (a, b)`, and then applies `buchiFamily_saturation` to conclude `xs ∈ language na`. This direction is independent of the Ramsey/recurrence argument used by the forward lemma and can land in its own committed dispatch.

### Research Integration

The task description is the research artifact and supplies the complete API map. The parent task 241 orchestrator handoff (`.orchestrator-handoff.json`) corroborates every anchor used here:

- **DA.Muller language**: `language da xs ↔ (da.run xs).infOcc ∈ da.accept` (DA/Basic.lean:117); unfolded in the file via `rw [ωAcceptor.mem_language]` + `simp only [DA.Muller.instωAcceptor]` (see forward lemma, OmegaRegularLanguage.lean:438-441).
- **accept set** of `buchiCongr_DMA` (OmegaRegularLanguage.lean:394-396): `{S | ∃ b ∈ S, ∃ a : Q, ((na.buchiFamily (a, b) ⊓ language na).toSet).Nonempty}`.
- **buchiFamily_saturation** (BuchiCongruence.lean:181): `Saturates (fun i ↦ (na.buchiFamily i).toSet) (language na).toSet`, where `Saturates f s := ∀ i, (f i ∩ s).Nonempty → f i ⊆ s` (Foundations/Data/Set/Saturation.lean:25).
- **mem_buchiFamily** (BuchiCongruence.lean:107): characterizes `xs ∈ na.buchiFamily (a, b)` as a prefix in `eqvCls a` followed by a flatten of segments each in `eqvCls b - 1`.
- **buchiCongr_DMA_run_eq** (OmegaRegularLanguage.lean:405): `(buchiCongr_DMA na).run xs n = ⟦xs.extract 0 n⟧`.
- **mem_infOcc** (InfOcc.lean:88) and **frequently_in_finite_type** (InfOcc.lean:46) for reasoning about `b ∈ infOcc(run xs)`.
- **buchiFamily_cover** (BuchiCongruence.lean:118): `⨆ i, na.buchiFamily i = ⊤` — fallback for obtaining a decomposition of `xs` if the witness's `a` does not directly match `xs`'s prefix class.

### Prior Plan Reference

No prior plan for task 434. The parent task 241 handoff classifies this backward lemma (SUB-C) as one of the "small" follow-ups once infrastructure landed — in contrast to the forward lemma which overflowed three monolithic dispatches. Effort is calibrated accordingly (single dispatch, ~1.5h).

### Roadmap Alignment

No ROADMAP.md consultation requested (roadmap flag not set). This lemma is a sub-goal of the McNaughton theorem effort (parent task 241): it is one of the two inclusions whose antisymmetry yields `buchiCongr_DMA_language_eq`, which in turn unblocks `IsRegular.iff_da_muller`.

## Goals & Non-Goals

**Goals**:
- Add `private lemma buchiCongr_DMA_language_backward` proving `language (buchiCongr_DMA na) ⊆ language na`, mirroring the signature shape of `buchiCongr_DMA_language_forward` (`[Inhabited Symbol] {State : Type} [Finite State] (na : NA.Buchi State Symbol)`, under `open NA.Buchi in`).
- Zero `sorry` and zero new axioms in the new lemma (verified by `lean_verify`).
- `lake build` green for the module.
- Public-facing docstring on the new lemma (CSLib `docBlame` compliance).

**Non-Goals**:
- Do NOT prove or modify `buchiCongr_DMA_language_forward` (task index 1 / SUB-B).
- Do NOT close `buchiCongr_DMA_language_eq`, `to_da_muller_scaffold`, or `IsRegular.iff_da_muller` (task 435 / SUB-D).
- Do NOT alter the `buchiCongr_DMA` definition, its accept set, or any BuchiCongruence.lean API.
- Do NOT run the full PR pipeline (`lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake`) — only `lake build` + `lean_verify` are in scope per the task's CI requirement. (Full pipeline is task 435's responsibility.)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Witness's `a` from the accept set does not match `xs`'s actual prefix class, so `xs ∈ buchiFamily (a, b)` is not directly true | H | M | The accept condition only fixes `b ∈ infOcc(run xs)`; `a` is existential. If a direct decomposition into `eqvCls a` fails, obtain `xs ∈ buchiFamily (a₀, b₀)` via `buchiFamily_cover`, identify `xs`'s own classes via `buchiCongr_DMA_run_eq` + `mem_infOcc`, and reconcile with the accepting witness through `Saturates`. Escalate via `lean_state_search`/`lean_leansearch` before changing the lemma statement. |
| `⊓`/`.toSet`/`.Nonempty` unfolding on `ωLanguage` does not match expected destructuring shape | M | M | Use `lean_hover_info` on `accept`, `lean_goal` after `simp only [...]`; the `⊓` is the lattice meet on `ωLanguage`, so `inf_def`/`Set.mem_inter_iff` patterns apply (compare `IsRegular.fin_cover_saturates`, OmegaRegularLanguage.lean:238-246). |
| Muller acceptance unfolding differs in the `at hxs` direction vs. the forward lemma's goal-side use | L | M | Mirror lines 438-441 but apply `rw [ωAcceptor.mem_language] at hxs` and `simp only [DA.Muller.instωAcceptor] at hxs`; confirm hypothesis shape with `lean_goal`. |
| `[Finite State]` instance unexpectedly unnecessary or insufficient | L | L | Keep `[Finite State]` to match the forward lemma and `buchiCongr_DMA_language_eq`; `buchiFamily_saturation` does not require it but the surrounding eq statement does. |
| `lean_diagnostic_messages` / `lean_file_outline` hang | M | L | Per cslib.md/lean4.md: do NOT call these; use `lean_goal` + `lake build` instead. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This is a single-lemma proof, so all phases are strictly sequential.

### Phase 1: Lemma scaffold and accept-set unfolding [COMPLETED]

**Goal**: Introduce the lemma with the correct signature, reduce the goal to proving `xs ∈ language na` from a destructured accept witness.

**Tasks**:
- [ ] Add the lemma skeleton after `buchiCongr_DMA_language_forward` (~line 446), before `proof_wanted buchiCongr_DMA_language_eq` (line 460):
  ```lean
  open NA.Buchi in
  private lemma buchiCongr_DMA_language_backward [Inhabited Symbol] {State : Type} [Finite State]
      (na : NA.Buchi State Symbol) :
      language (buchiCongr_DMA na) ⊆ language na := by
    intro xs hxs
    sorry
  ```
- [ ] Unfold the Muller acceptance hypothesis: `rw [ωAcceptor.mem_language] at hxs` then `simp only [DA.Muller.instωAcceptor] at hxs` so that `hxs : ((buchiCongr_DMA na).run xs).infOcc ∈ (buchiCongr_DMA na).accept`. Confirm shape with `lean_goal`.
- [ ] Unfold the accept set (`simp only [buchiCongr_DMA] at hxs` or `change`/`Set.mem_setOf_eq`) and destructure: `obtain ⟨b, hb_inf, a, hys⟩ := hxs` then split the `(... ⊓ language na).toSet.Nonempty` witness into `ys`, `hys_fam : ys ∈ na.buchiFamily (a, b)`, `hys_lang : ys ∈ language na`. Verify the destructuring with `lean_goal`.

**Timing**: 0.4 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - add new private lemma stub with `sorry`, perform acceptance + accept-set unfolding.

**Verification**:
- `lean_goal` shows hypotheses `b`, `hb_inf : b ∈ ((buchiCongr_DMA na).run xs).infOcc`, `a`, `hys_fam`, `hys_lang`, and goal `xs ∈ language na` (a single `sorry` remaining).

### Phase 2: Establish `xs ∈ buchiFamily (a, b)` [BLOCKED]

**BLOCKER** (Phase 2):

- **What failed**: Cannot prove `xs ∈ na.buchiFamily (b, a)` (the literal goal at the
  remaining `sorry`, OmegaRegularLanguage.lean:588) for the *specific* `a` bound by
  destructuring the accept-set witness `hxs`. The companion class `a` in `hfam :
  (na.buchiFamily (b, a) ⊓ language na).toSet.Nonempty` is an *arbitrary* existential
  witness from the accept-set definition — it is **not** algebraically tied to `b` (no
  `b * a = b` / `a * a = a` is known or derivable from `hfam` alone) and is **not** tied
  to `xs`'s actual content (it comes from a separate witness word `ys`, not from `xs`).
  `mem_buchiFamily` requires `xs`'s own loop segments to be *literal substrings of `xs`*
  whose Büchi-congruence class is *exactly* `a` for every segment — there is no freedom to
  substitute or fabricate content, since the decomposition must satisfy
  `xl ++ω xls.flatten = xs` on the nose.

- **What was tried**:
  1. Mirrored `buchiCongr_DMA_accept_mem`'s pattern exactly per the task's hint: applied
     `frequently_iff_strictMono` to `hb_prefix` to extract a strictly monotone breakpoint
     sequence of `b`-recurrence times. This **does** establish (unconditionally, via DMA
     determinism: `run(t_{i+1}) = run(t_i) * class(gap_i)` together with `run(t_i)=run(t_{i+1})=b`)
     that every gap segment `w_i` between consecutive recurrence times satisfies
     `b * ⟦w_i⟧ = b`. Running the *same* `infinite_graph_ramsey` homogeneity argument as
     `buchiCongr_DMA_accept_mem`/`buchiFamily_cover`, but restricted to the (infinite) set of
     `b`-recurrence times, yields a **fresh** idempotent companion `c` (`b*c=b`, `c*c=c`)
     realized as actual substrings of `xs`, giving `xs ∈ na.buchiFamily (b, c)` —
     a genuine, unconditional decomposition of `xs`. This is solid, reusable progress, but
     `c` is **not provably equal to `a`** (the value fixed by `hfam`), so it does not close
     the stated goal `xs ∈ na.buchiFamily (b, a)`.
  2. Attempted to derive `b * a = b` / `a * a = a` from `hfam` directly (via
     `mem_buchiFamily.mp` on its witness `ys`) — not derivable; `mem_buchiFamily` only
     requires each loop segment of `ys` to individually lie in `eqvCls a`, which places no
     algebraic constraint on `a * a` or `b * a`.
  3. Attempted to "normalize" `a` to an idempotent power `a^(N!)` via
     `buchiCongruence_idempotentPow`/`buchiCongruence_absorption` (regrouping `ys`'s loop
     segments in blocks of `N!`) to get a fresh good pair `(b * a^(N!), a^(N!))` — this
     shows `ys`'s own *recurring* prefix class is `b * a^(N!)` (not necessarily `b`), so it
     does not bridge to our given `b` either, since `b * a` is still unknown.
  4. Tried switching the chosen witness index from `(b, a)` to the cover decomposition
     `(a₀, b₀)` already in scope (`hxs_fam : xs ∈ na.buchiFamily (a₀, b₀)`, via
     `buchiFamily_cover`) — this trades one unmatched pair for another; proving
     `(buchiFamily (a₀, b₀) ⊓ language na).Nonempty` has the identical underlying gap
     (relating an arbitrary realized decomposition of `xs` to the accept-set's witness).
  5. Empirically confirmed via `lean_multi_attempt`: `grind [mem_buchiFamily,
     buchiCongruence_mk_append, buchiCongruence_idempotentPow, buchiCongruence_absorption]`
     and `aesop` both fail exhaustively at the goal (no usable closing automation).

- **Why it's stuck**: The accept-set definition of `buchiCongr_DMA`
  (`{S | ∃ a ∈ S, ∃ b, (buchiFamily (a,b) ⊓ language na).Nonempty}`, OmegaRegularLanguage.lean:
  395-397) only asserts *existence* of *some* good companion for *some* recurring class — it
  carries no information tying the witness companion to the recurring class's actual
  realization in `xs`. Closing this goal in general requires a "linked-pair independence"
  theorem from finite-(ω-)semigroup theory: that for a *fixed* recurring class `b`, the
  predicate "`(buchiFamily (b, X) ⊓ language na).Nonempty`" is the *same* for every valid
  idempotent companion `X` realizable as a factorization of *some* `b`-recurring ω-word
  (not just for the one `X` happens to label). This is a real, nontrivial mathematical fact
  in ω-automata/Wilke-algebra theory (related to "saturated/well-defined Muller acceptance
  conditions on ω-semigroups") and is **not currently proved anywhere in CSLib**
  (`BuchiCongruence.lean` has no lemma relating two different companions of the same
  recurring class). Cross-referencing the upstream reference implementation
  (`ctchou/AutomataTheory`, same author/license, the project this file ports from) confirms
  this: its McNaughton proof (`AutomataTheory/Languages/DetMullerLang.lean`) does **not**
  use a `BuchiCongr`-quotient-as-DMA-states construction at all — it uses the Choueka lemma
  (`L^ω = L* · L'↗ω`) plus closure properties instead. `BuchiCongr`/`Ample`/`Saturates` in
  the reference project are used *only* to prove closure under complementation, never to
  build a DMA directly. This `buchiCongr_DMA` construction (and its accept-set, as literally
  stated) therefore appears to be a CSLib-local construction without a verified reference
  proof for this exact direction, consistent with the broader `buchiCongr_DMA_language_eq`
  being independently tagged `[BLOCKED — Phase 4, task 241]` in this same file
  (OmegaRegularLanguage.lean:591), whose own proof sketch (lines 594-601) hand-waves
  precisely this step ("since `b` recurs in `run xs`, one can decompose `xs` to lie in
  `na.buchiFamily (a, b)`") without justifying why the decomposition's companion class must
  equal the accept-set's witness.

- **What is needed**: One of:
  1. A new lemma in `BuchiCongruence.lean` establishing "goodness of `(b, X)` depends only on
     `b`" for `X` ranging over idempotent companions of `b` realizable via Ramsey
     factorization of some `b`-recurring word (the genuine missing piece), **or**
  2. Redefining `buchiCongr_DMA`'s accept set to encode the companion canonically (e.g. via
     a fixed choice function from the Ramsey/idempotent-power construction rather than a bare
     existential) — out of scope per this task's non-goals ("Do NOT alter the `buchiCongr_DMA`
     definition, its accept set"), **or**
  3. Consultation with Ching-Tsun Chou (file's primary author) on whether
     `ctchou/AutomataTheory` has an unported alternative construction for this exact
     direction, since the reference repo's McNaughton proof does not go through this
     congruence-quotient-as-DMA route at all.

- **Prohibited workarounds**: Did NOT use `sorry` placeholders beyond the one already
  present, did NOT introduce `def X := True`/`trivial`/vacuous placeholders, and did NOT
  alter `buchiCongr_DMA`, its accept set, or the already-completed `buchiCongr_DMA_accept_mem`
  / `buchiCongr_DMA_language_forward` lemmas. The file is left exactly as found (one `sorry`
  at line 588), confirmed still building green via `lake build
  Cslib.Computability.Languages.OmegaRegularLanguage` (1096/1096 jobs, only the expected
  `declaration uses 'sorry'` warning, zero errors).

**Goal**: Prove the membership `xs ∈ na.buchiFamily (a, b)` (the index whose family intersects `language na`), which is the substantive step of the proof.

**Tasks**:
- [ ] Translate `hb_inf : b ∈ infOcc(run xs)` into prefix-class recurrence using `buchiCongr_DMA_run_eq` and `mem_infOcc` (InfOcc.lean:88): infinitely many `n` satisfy `⟦xs.extract 0 n⟧ = b`.
- [ ] Build the decomposition required by `mem_buchiFamily` (BuchiCongruence.lean:107): a prefix in `eqvCls a` and a flatten of segments each in `eqvCls b - 1`, with concatenation equal to `xs`. Use `mem_buchiFamily.mpr ⟨xl, xls, ...⟩`.
- [ ] **Decision point / escalation**: if the witness's existential `a` does not coincide with `xs`'s prefix class, do NOT change the lemma statement. Instead obtain `xs ∈ na.buchiFamily (a₀, b₀)` via `buchiFamily_cover` (BuchiCongruence.lean:118), identify `xs`'s classes via `buchiCongr_DMA_run_eq` + `mem_infOcc`/`frequently_in_finite_type` (InfOcc.lean:46), and carry whichever index `(a', b')` makes `(buchiFamily (a', b') ⊓ language na).Nonempty` hold so that Phase 3's saturation step closes the goal. Probe candidate lemmas with `lean_state_search` / `lean_leansearch` / `lean_loogle` before committing.
- [ ] Use `lean_multi_attempt` to test tactic fragments before editing; keep `lean_goal` open at each rewrite.

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - fill in the membership proof producing `hxs_fam : xs ∈ na.buchiFamily (a, b)` (or the reconciled index).

**Verification**:
- `lean_goal` shows a proven hypothesis `xs ∈ na.buchiFamily (a, b)` (or reconciled index) with the remaining goal still `xs ∈ language na`.

### Phase 3: Apply `buchiFamily_saturation` and assemble proof [NOT STARTED]

**Goal**: Conclude `xs ∈ language na` from `xs ∈ buchiFamily (a, b)` and the accept witness, removing the final `sorry`.

**Tasks**:
- [ ] Instantiate `buchiFamily_saturation (na := na)` at index `(a, b)`: from `(na.buchiFamily (a, b) ⊓ language na).toSet.Nonempty` (the accept witness `ys`, reshaped to `(buchiFamily (a,b)).toSet ∩ (language na).toSet`) derive `(na.buchiFamily (a, b)).toSet ⊆ (language na).toSet`. Reconcile `⊓`/`.toSet` with `∩` via `inf_def`/`Set.mem_inter_iff` (cf. OmegaRegularLanguage.lean:246).
- [ ] Apply the subset to `hxs_fam` to obtain `xs ∈ language na`; close the goal (`exact`/`apply`).
- [ ] Remove the `sorry`; confirm "no goals" via `lean_goal`.
- [ ] Add a docstring to the lemma describing the backward inclusion and its proof strategy (accept-set unfold → family membership → saturation), satisfying `docBlame`.

**Timing**: 0.3 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - finalize the saturation application, close the goal, add docstring.

**Verification**:
- `lean_goal` at end of proof reports "no goals".

### Phase 4: CI verification [NOT STARTED]

**Goal**: Confirm the proof compiles green with zero sorries and zero new axioms.

**Tasks**:
- [ ] Run scoped build: `lake build Cslib.Computability.Languages.OmegaRegularLanguage` (fall back to `lake build` if the scoped module path errors).
- [ ] Run `lean_verify Cslib.ωLanguage.buchiCongr_DMA_language_backward` (resolve the exact fully-qualified name via `lean_hover_info` if the namespace prefix differs) — confirm zero sorries and no new axioms beyond the standard set.
- [ ] If any error surfaces, return to the relevant phase; do not leave a partial `sorry`.

**Timing**: 0.3 hours

**Depends on**: 3

**Files to modify**:
- None (verification only).

**Verification**:
- `lake build` exits 0 for the module.
- `lean_verify` on `buchiCongr_DMA_language_backward` reports zero sorries and no new axioms.

## Testing & Validation

- [ ] `lake build` green for `Cslib/Computability/Languages/OmegaRegularLanguage.lean`.
- [ ] `lean_verify` on `buchiCongr_DMA_language_backward`: zero sorries, zero new axioms.
- [ ] New lemma carries a docstring (no `docBlame` regression on the new declaration).
- [ ] No edits to `buchiCongr_DMA`, its accept set, the forward lemma, or BuchiCongruence.lean.

## Artifacts & Outputs

- New `private lemma buchiCongr_DMA_language_backward` in `Cslib/Computability/Languages/OmegaRegularLanguage.lean` (with docstring, sorry-free).
- Updated task metadata (`.return-meta.json`) and orchestrator handoff (`.orchestrator-handoff.json`).

## Rollback/Contingency

The change is additive and confined to a single new lemma. To revert: delete the `buchiCongr_DMA_language_backward` lemma block (the file returns to its prior state — `buchiCongr_DMA_language_forward` and `proof_wanted buchiCongr_DMA_language_eq` are untouched). If the witness-index reconciliation (Phase 2 decision point) proves to require recurrence machinery not yet available, mark Phase 2 [BLOCKED], document the exact goal state reached and the missing lemma, return `status: partial` with `requires_user_review: true`, and leave a single clearly-marked `sorry` rather than any vacuous placeholder.
