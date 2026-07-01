# Implementation Plan: Task #433

- **Task**: 433 - prove_acceptmembership_ramsey_lemma_for_buchicongr_dma_forward
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours
- **Dependencies**: None (parent task 241; required upstream lemmas already proved)
- **Research Inputs**: Task description (self-contained API map); specs/241_mcnaughton_theorem/reports/03_spawn-analysis.md
- **Artifacts**: plans/01_buchicongr-accept-mem-ramsey.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Prove a single private lemma `buchiCongr_DMA_accept_mem` in
`Cslib/Computability/Languages/OmegaRegularLanguage.lean` that establishes the Ramsey /
recurrence core of the forward inclusion of McNaughton's theorem: for any `xs ∈ language na`,
the infinitely-occurring states of the Büchi-congruence DMA run contain a class that, paired
with some partner class, gives a Büchi-family element intersecting `language na`. This is
exactly the membership obligation `infOcc((buchiCongr_DMA na).run xs) ∈ (buchiCongr_DMA na).accept`,
currently a `sorry` inside `buchiCongr_DMA_language_forward` (OmegaRegularLanguage.lean:442).
The lemma is then wired into that forward lemma to discharge the `sorry`. Scope is tightly
limited to this one lemma plus its single call site.

### Research Integration

No separate research report exists; the task description carries the full API map. Grounding
performed during planning (line numbers verified against current sources):

- **Goal shape**: `(buchiCongr_DMA na).accept = {S | ∃ b ∈ S, ∃ a, ((na.buchiFamily (a, b) ⊓ language na).toSet).Nonempty}`
  (OmegaRegularLanguage.lean:393-396). The lemma's conclusion must produce this exact
  existential with `S = ((buchiCongr_DMA na).run xs).infOcc`.
- **`buchiCongr_recurrentClass`** (OmegaRegularLanguage.lean:426-432): for `[Finite State]`,
  gives `a b : Quotient na.BuchiCongruence.eq` with `b * b = b`, `a * b = a`, and
  `a ∈ ((buchiCongr_DMA na).run xs).infOcc`. **The in-`infOcc` class is `a`** (the absorbing
  class), not the idempotent `b`. See Risk R1.
- **`buchiCongr_DMA_run_eq`** (OmegaRegularLanguage.lean:405-417): `(buchiCongr_DMA na).run xs n = ⟦xs.extract 0 n⟧`.
- **`buchiFamily_cover`** (BuchiCongruence.lean:118): `⨆ i, na.buchiFamily i = ⊤`; every `xs`
  lies in some `na.buchiFamily (p, q)`. The cover proof (BuchiCongruence.lean:118-152) uses the
  same Ramsey coloring as `buchiCongruence_recurrentPrefixClass`, so its decomposition pair
  aligns with the recurrent pair: prefix class `⟦xs.take (f 0)⟧` and idempotent segment class `b`.
- **`buchiFamily_saturation`** (BuchiCongruence.lean:181-182):
  `Saturates (fun i ↦ (na.buchiFamily i).toSet) (language na).toSet`. With
  `Saturates f s := ∀ i, (f i ∩ s).Nonempty → f i ⊆ s` (Foundations/Data/Set/Saturation.lean:25).
  Use to upgrade "xs ∈ family and xs ∈ language" into "family ⊆ language" when needed.
- **`mem_buchiFamily`** (BuchiCongruence.lean:107-112): decomposition characterization of
  `xs ∈ na.buchiFamily (a, b)` as a prefix in `eqvCls a` followed by a flattened sequence of
  segments each in `eqvCls b - 1`.
- **`mem_infOcc`** (InfOcc.lean:88): `x ∈ xs.infOcc ↔ ∃ᶠ k in atTop, xs k = x`.
- **`frequently_in_finite_type`** (InfOcc.lean:46): in a finite type,
  `(∃ᶠ k, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k, xs k = x`.
- **DA.Muller language / `Accepts`**: DA/Basic.lean:117; `ωAcceptor.mem_language` /
  `DA.Muller.instωAcceptor` are the unfolding entry points already used at
  OmegaRegularLanguage.lean:439-441.

### Prior Plan Reference

No prior plan. The `buchiCongr_DMA_language_forward` lemma at OmegaRegularLanguage.lean:435-446
contains an inline proof sketch (comments at lines 441-445) and a doc sketch on
`buchiCongr_DMA_language_eq` (lines 447-460) describing the intended argument: "the DMA run
visits class `b` infinitely often ... so `b ∈ infOcc(run xs) =: S` and `(a, b)` witnesses
`S ∈ accept`." Note this sketch phrases the in-`infOcc` class as the idempotent `b`, whereas
`buchiCongr_recurrentClass` delivers the absorbing `a` in `infOcc`. Reconciling these two
namings is the central proof-discovery step (Risk R1).

### Roadmap Alignment

No ROADMAP.md found at specs/ROADMAP.md. No roadmap phases added.

## Goals & Non-Goals

**Goals**:
- Add a private lemma `buchiCongr_DMA_accept_mem` in OmegaRegularLanguage.lean stating: for
  `[Inhabited Symbol] [Finite State]`, `na : NA.Buchi State Symbol`, `xs : ωSequence Symbol`,
  `xs ∈ language na →
   ∃ b ∈ ((buchiCongr_DMA na).run xs).infOcc,
     ∃ a, ((na.buchiFamily (a, b) ⊓ language na).toSet).Nonempty`.
- Prove it with zero `sorry`, reusing the cited private/public lemmas (no new public API, no
  changes to upstream files).
- Wire the lemma into `buchiCongr_DMA_language_forward` to discharge the existing `sorry`
  (OmegaRegularLanguage.lean:442), so the new private lemma is used (no dead-code/unused lint).
- Pass full CI green: `lake build` and `lean_verify` on `buchiCongr_DMA_accept_mem` with zero
  sorries / no extra axioms.

**Non-Goals**:
- Proving `buchiCongr_DMA_language_eq` (the backward direction / full language equality) — it
  remains `proof_wanted`.
- Proving `IsRegular.iff_da_muller` or the Rabin/parity corollaries.
- Editing BuchiCongruence.lean, InfOcc.lean, DA/Basic.lean, or Saturation.lean (read-only
  references).
- Generalizing or restating any upstream lemma signature.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: `buchiCongr_recurrentClass` puts the **absorbing** class `a` in `infOcc`, but `accept` needs the in-`infOcc` class as the **second** (idempotent) component `b` of `buchiFamily (a', b)`. The two namings must be reconciled. | H | H | Use the cover decomposition: by `buchiFamily_cover` get `(p, q)` with `xs ∈ buchiFamily (p, q)`; the cover's coloring matches `recurrentPrefixClass`, so the recurring `infOcc` class equals the prefix class `p` and the idempotent segment class is `q`. Explore actual goal with `lean_goal`/`lean_term_goal` to determine whether the witness is `(p, recurring)` or `(recurring, q)`. Prefer producing the witness `b := recurring infOcc class` and `a := p`, with nonemptiness witnessed by `xs` itself. If the idempotent must be the `infOcc` element, derive its recurrence from `run_eq` + `frequently_in_finite_type`. Resolve empirically with lean-lsp before committing the proof shape. |
| R2: Nonemptiness witness selection — which concrete ω-sequence witnesses `(buchiFamily (a, b) ⊓ language na).Nonempty`. | M | M | `xs` itself is in `language na` (hypothesis) and in some `buchiFamily i` (cover). Use `xs` as the witness; the `⊓` is `ωLanguage` inf whose `.toSet` is set intersection — `⟨xs, mem_cover, hxs⟩`. Confirm the `⊓`/`toSet`/`mem` unfolding with `lean_hover_info` / `simp` lemmas (`ωLanguage.mem_inf` or analogous). |
| R3: `infOcc`/`run` unfolding mismatch when bridging `mem_infOcc` (`∃ᶠ k, xs k = x`) to `run_eq`. | M | M | Mirror the existing `buchiCongr_recurrentClass` body (lines 430-432) which already does `mem_infOcc.mpr (hfreq.mono fun k hk => (buchiCongr_DMA_run_eq …).trans hk)`. Reuse `buchiCongr_recurrentClass` directly rather than re-deriving from `recurrentPrefixClass`. |
| R4: `⊓` / `language` / `toSet` coercion friction (`Nonempty` of an `ωLanguage` inf). | M | M | Use `lean_loogle` / `lean_local_search` for `ωLanguage.mem_inf`, `Set.Nonempty`, `SetLike`/`mem` simp lemmas; test candidate rewrites with `lean_multi_attempt` before editing. |
| R5: Build time / LSP timeout on the large file. | L | M | Use `lean_goal` at the lemma position for fast iteration; run `lean_build` / `lake build` only at phase boundaries, not per tactic. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are strictly sequential (single-lemma proof): each builds the proof term the next
phase depends on. No parallelism within this task.

### Phase 1: Lemma scaffold and goal analysis [IN PROGRESS]

**Goal**: Add the lemma signature with a `sorry` body immediately above
`buchiCongr_DMA_language_forward`, confirm it elaborates, and capture the exact goal state.

**Tasks**:
- [ ] Insert `private lemma buchiCongr_DMA_accept_mem` (with `open NA.Buchi in`) directly
  before `buchiCongr_DMA_language_forward` (around OmegaRegularLanguage.lean:434), signature:
  `[Inhabited Symbol] {State : Type} [Finite State] (na : NA.Buchi State Symbol)
   (xs : ωSequence Symbol) (hxs : xs ∈ language na) :
   ∃ b ∈ ((buchiCongr_DMA na).run xs).infOcc,
     ∃ a, ((na.buchiFamily (a, b) ⊓ language na).toSet).Nonempty := by sorry`
- [ ] Verify the type elaborates (no signature errors) via `lean_diagnostic_messages` /
  `lean_goal` at the `sorry`.
- [ ] Record the precise goal with `lean_goal`; confirm it matches the `accept` membership
  predicate (compare to OmegaRegularLanguage.lean:393-396).
- [ ] Confirm the existential ordering (`∃ b ∈ infOcc, ∃ a, …`) matches `accept` exactly so
  Phase 4 wiring is a direct rewrite, not a reshuffle.

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - add private lemma scaffold above line 434

**Verification**:
- `lean_goal` returns a single goal whose statement is the existential above; no elaboration errors other than the `sorry` warning.

---

### Phase 2: Recurrent class and cover decomposition [IN PROGRESS]

**Goal**: Obtain the recurring `infOcc` class and the cover decomposition of `xs`, establishing
the two facts the witness is built from.

**Tasks**:
- [ ] `obtain ⟨a, b, hbb, hab, hmem⟩ := buchiCongr_recurrentClass na xs` to get
  `b * b = b`, `a * b = a`, `a ∈ ((buchiCongr_DMA na).run xs).infOcc`.
- [ ] Obtain a cover witness: from `buchiFamily_cover` (or `ωLanguage.mem_iSup` on `⊤`) derive
  `∃ p q, xs ∈ na.buchiFamily (p, q)`. Inspect with `lean_goal`/`lean_hover_info` whether the
  cover's pair coincides definitionally with `(a, b)` from `buchiCongr_recurrentClass` (both
  use the same Ramsey coloring — see Research Integration).
- [ ] Determine, using `lean_goal` exploration and Risk R1 mitigation, the correct mapping:
  which class is the `accept` second component `b` (the `infOcc` element) and which is the
  partner `a`. Document the chosen mapping in a one-line proof comment.

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - extend the lemma body (intro hypotheses, obtain destructurings)

**Verification**:
- `lean_goal` shows the recurrent-class hypotheses and the cover membership in context; remaining goal is the existential witness.

---

### Phase 3: Build the witness and discharge nonemptiness [NOT STARTED]

**Goal**: Provide the `∃ b ∈ infOcc, ∃ a, …` witness and close the `Nonempty` subgoal.

**Tasks**:
- [ ] `refine ⟨<recurring class>, <infOcc proof>, <partner class>, ?_⟩` per the Phase 2 mapping
  (use `hmem` for the `∈ infOcc` component, reusing the `buchiCongr_recurrentClass` output as in
  the model at OmegaRegularLanguage.lean:430-432).
- [ ] Close `((na.buchiFamily (a, b) ⊓ language na).toSet).Nonempty` with `xs` as witness:
  `exact ⟨xs, <xs ∈ buchiFamily pair>, hxs⟩`, unfolding `⊓`/`toSet` membership via the
  appropriate `ωLanguage.mem_inf` simp lemma (find with `lean_local_search`/`lean_loogle`).
- [ ] If saturation is needed to align the cover pair with the witness pair, apply
  `buchiFamily_saturation` to convert `(family ∩ language).Nonempty` into `family ⊆ language`
  and back, or to relate the cover pair to the recurrent pair.
- [ ] Use `lean_multi_attempt` to test the final `exact`/`refine` terms before writing them.
- [ ] Remove the `sorry`; confirm `lean_goal` reports "no goals".

**Timing**: 1.0 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - complete the lemma body

**Verification**:
- `lean_diagnostic_messages` at the lemma shows no errors and no `sorry` warning for `buchiCongr_DMA_accept_mem`.

---

### Phase 4: Wire into `buchiCongr_DMA_language_forward` [NOT STARTED]

**Goal**: Discharge the existing `sorry` at OmegaRegularLanguage.lean:442 using the new lemma,
so the private lemma is consumed (no unused-decl lint) and the forward inclusion is complete.

**Tasks**:
- [ ] In `buchiCongr_DMA_language_forward`, after `rw [ωAcceptor.mem_language]` /
  `simp only [DA.Muller.instωAcceptor]`, the goal is `infOcc(run xs) ∈ accept`. Replace the
  `sorry` (line 442) with `exact buchiCongr_DMA_accept_mem na xs hxs` (adjusting to the exact
  membership form; the `accept` set's defining predicate is the lemma's conclusion).
- [ ] If the `accept` membership needs `Set.mem_setOf` / unfolding to match the lemma's
  existential, add the minimal `simp only`/`show` to bridge; verify with `lean_goal`.
- [ ] Confirm `buchiCongr_DMA_language_forward` is now `sorry`-free.

**Timing**: 0.25 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - replace `sorry` at line 442 with application of the new lemma

**Verification**:
- `lean_diagnostic_messages` shows `buchiCongr_DMA_language_forward` with no `sorry` and no errors.

---

### Phase 5: CI verification (lake build + lean_verify, zero sorries) [NOT STARTED]

**Goal**: Confirm the whole module compiles green and the new lemma is axiom-clean and
sorry-free.

**Tasks**:
- [ ] Run `lake build` (or `lean_build`) — must succeed with no errors.
- [ ] Run `lean_verify` on `Cslib.ωLanguage.buchiCongr_DMA_accept_mem` (use the fully-qualified
  name) — confirm zero `sorry`, no unexpected axioms beyond the standard
  `propext/Classical.choice/Quot.sound` set.
- [ ] Grep the file to confirm no remaining `sorry` was introduced by this task (the file's
  only remaining incompleteness markers should be the pre-existing `proof_wanted` declarations,
  which are intentional and unrelated).
- [ ] Run the CSLib CI subset relevant to a single proof change: `lake build` (primary).
  Optionally `lake exe lint-style` on the modified file if quick; full pipeline is out of scope
  for a single-lemma change but `lake build` green is mandatory.

**Timing**: 0.25 hours

**Depends on**: 4

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` exits 0; `lean_verify buchiCongr_DMA_accept_mem` reports sorry-free with only standard axioms.

## Testing & Validation

- [ ] `lake build` succeeds with zero errors.
- [ ] `lean_verify Cslib.ωLanguage.buchiCongr_DMA_accept_mem` reports zero sorries and only
  standard axioms.
- [ ] No new `sorry` anywhere in OmegaRegularLanguage.lean (only pre-existing `proof_wanted`
  remain: `buchiCongr_DMA_language_eq`, `IsRegular.iff_da_muller`).
- [ ] `buchiCongr_DMA_language_forward` no longer contains a `sorry`.
- [ ] No upstream files modified (BuchiCongruence.lean, InfOcc.lean, DA/Basic.lean,
  Saturation.lean unchanged).

## Artifacts & Outputs

- Modified `Cslib/Computability/Languages/OmegaRegularLanguage.lean`:
  - New private lemma `buchiCongr_DMA_accept_mem`.
  - `sorry` in `buchiCongr_DMA_language_forward` discharged.
- Green `lake build`.
- `lean_verify` confirmation of sorry-freeness.

## Rollback/Contingency

- The change is confined to one file and is additive plus one `sorry` replacement. To revert:
  `git checkout -- Cslib/Computability/Languages/OmegaRegularLanguage.lean` restores the
  pre-task state (the original `sorry` at line 442).
- If Risk R1 cannot be resolved (the recurring `infOcc` class genuinely cannot be matched to an
  `accept` second component with an available partner), leave `buchiCongr_DMA_accept_mem` proved
  in whatever reconciled form lean-lsp supports and, if wiring (Phase 4) is blocked, keep the
  forward lemma's `sorry` and mark the task [PARTIAL] with a precise note on the residual goal
  state — do NOT introduce a new `sorry` inside `buchiCongr_DMA_accept_mem` itself.
- If `lean_verify` reveals an unexpected axiom, inspect which tactic introduced it (likely a
  classical-choice path) and confirm it is within CSLib's accepted axiom set; otherwise refactor
  the offending step.
