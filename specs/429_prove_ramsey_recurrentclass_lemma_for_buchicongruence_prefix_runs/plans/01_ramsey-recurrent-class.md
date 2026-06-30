# Implementation Plan: Task #429

- **Task**: 429 - prove_ramsey_recurrentclass_lemma_for_buchicongruence_prefix_runs
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: Task 428 (COMPLETED — monoid/idempotent/absorption lemmas available)
- **Research Inputs**: specs/241_mcnaughton_theorem/reports/02_spawn-analysis.md
- **Artifacts**: plans/01_ramsey-recurrent-class.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Prove a recurrent-class lemma for the Büchi-congruence DMA prefix run: for `[Finite State]`
and any `xs : ωSequence Symbol`, there exist quotient classes `a b : Quotient na.BuchiCongruence.eq`
with `b * b = b` (idempotent), `a * b = a` (absorbing), and `a ∈ ((buchiCongr_DMA na).run xs).infOcc`
(i.e. `∃ᶠ k in atTop, (buchiCongr_DMA na).run xs k = a`). The proof recasts the Ramsey argument
already used by `buchiFamily_cover` (BuchiCongruence.lean:118) at the level of the prefix-class run
`k ↦ ⟦xs.extract 0 k⟧`, which equals `(buchiCongr_DMA na).run xs k` by `buchiCongr_DMA_run_eq`.
Definition of done: a green-building lemma whose `infOcc` conclusion is the exact bridge that lets
task 241 Phase 4 close the forward direction of `buchiCongr_DMA_language_eq`; full CI passes.

### Research Integration

From `02_spawn-analysis.md`: the forward inclusion of `buchiCongr_DMA_language_eq` needs the
recurrent-class witness produced here. Task 428 (now complete) supplies the four reused lemmas:
`buchiCongruence_instMonoid` (Monoid on the quotient), `buchiCongruence_mk_append` (`@[simp]`,
`⟦u ++ v⟧ = ⟦u⟧ * ⟦v⟧`), `buchiCongruence_idempotentPow`, and `buchiCongruence_absorption`.
The plan was further grounded by reading the actual sources (see Key API below), confirming exact
signatures rather than relying on the description alone.

### Prior Plan Reference

No prior plan for task 429.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap_flag not set). This lemma advances the McNaughton
theorem effort tracked by parent task 241.

## Goals & Non-Goals

**Goals**:
- Prove a recurrent-prefix-class core lemma in `BuchiCongruence.lean` (pure prefix-class form,
  no DMA dependency), reusing the task-428 monoid/idempotent/absorption API and `infinite_graph_ramsey`.
- Prove the bridge lemma in `OmegaRegularLanguage.lean` (where `buchiCongr_DMA` and
  `buchiCongr_DMA_run_eq` are `private`), stating the `infOcc` conclusion required by task 241.
- Keep CI green (lake build, checkInitImports, lint, lint-style, shake, test).

**Non-Goals**:
- Proving `buchiCongr_DMA_language_eq` itself (that is task 241 Phase 4).
- Modifying `buchiFamily_cover`, `buchiFamily_saturation`, or the DMA definition.
- Introducing any new public API beyond the two lemmas (both may stay `private`/file-local where
  their neighbors are).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `infinite_graph_ramsey` `h_color` shape mismatch (needs `e.card = 2 ∧ ↑e ⊆ s`) | M | M | Mirror `buchiFamily_cover` exactly: `obtain ⟨b, ns, h_ns, h_color⟩`; `obtain ⟨f, h_mono, rfl⟩ := strictMono_of_infinite h_ns`; apply `h_color {f i, f j}` with `Finset.card_pair` (distinct via `h_mono`) and `↑e ⊆ range f` via `mem_range_self`. |
| `min'/max'` of `{f i, f j}` not reducing to `f i`, `f j` | M | M | Use `i < j ⇒ f i < f j` (`h_mono`) so `min' = f i`, `max' = f j`; reuse the `Finset.min'/max'` rewrite pattern from `buchiFamily_cover` (lines 124, 141-148). |
| Idempotence `b*b=b` rewrite via concatenation | M | L | `append_extract_extract` (Init.lean:485): `extract k m ++ extract m n = extract k n` for `k≤m≤n`; combine with `buchiCongruence_mk_append` (`@[simp]`). |
| `a*b=a` not direct from coloring | M | L | Set `a := ⟦xs.extract 0 (f 0)⟧ * b`; then `a * b = ⟦…⟧ * (b*b) = ⟦…⟧ * b = a` via `mul_assoc` + `hbb`. (Equivalently apply `buchiCongruence_absorption`.) |
| `frequently` conclusion plumbing | L | L | Use `frequently_iff_strictMono` (InfOcc.lean:34) with witness `g := fun m => f (m+1)` (strictMono), proving `⟦xs.extract 0 (f (m+1))⟧ = a` for all `m`. |
| Lemma placement / private visibility | M | L | Core lemma in `BuchiCongruence.lean` (pure, no DMA); bridge lemma in `OmegaRegularLanguage.lean` right after `buchiCongr_DMA_run_eq` (line ~417) so the `private buchiCongr_DMA`/`buchiCongr_DMA_run_eq` are in scope; mark bridge `private`. |
| maxHeartbeats on a large single proof | L | M | Core lemma is ~60-80 lines; if it times out, factor the idempotence and absorption sub-facts into local `have`s (the `buchiFamily_saturation` precedent split `frequently_via_accept` out for the same reason). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Core recurrent-prefix-class lemma in BuchiCongruence.lean [COMPLETED]

- **Goal:** Add and prove a pure prefix-class recurrence lemma (no DMA reference) reusing the
  task-428 monoid API and `infinite_graph_ramsey`.
- **Tasks:**
  - [ ] Confirm the four task-428 lemmas and the Ramsey/extract API exist as cited (quick
        `lean_local_search` / `lean_hover_info`; do NOT call `lean_diagnostic_messages`).
  - [ ] Add lemma after `buchiCongruence_absorption` (BuchiCongruence.lean:~319), before
        `end Cslib.Automata.NA.Buchi`:
        ```lean
        /-- Ramsey recurrent-class lemma at the prefix-class level: for `[Finite State]` and any
        `xs`, there exist congruence classes `a b` with `b` idempotent (`b * b = b`), `a` absorbing
        (`a * b = a`), and the prefix class `⟦xs.extract 0 k⟧` equal to `a` infinitely often. -/
        lemma buchiCongruence_recurrentPrefixClass [Finite State]
            (na : Buchi State Symbol) (xs : ωSequence Symbol) :
            ∃ a b : Quotient na.BuchiCongruence.eq, b * b = b ∧ a * b = a ∧
              ∃ᶠ k in atTop, (⟦xs.extract 0 k⟧ : Quotient na.BuchiCongruence.eq) = a := by
        ```
  - [ ] Proof outline (mirror `buchiFamily_cover` lines 122-128):
        - `have : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index`
        - `let color (t : Finset ℕ) : Quotient na.BuchiCongruence.eq :=
             if h : t.Nonempty then ⟦ xs.extract (t.min' h) (t.max' h) ⟧ else ⟦ [] ⟧`
        - `obtain ⟨b, ns, h_ns, h_color⟩ := infinite_graph_ramsey color`
        - `obtain ⟨f, h_mono, rfl⟩ := strictMono_of_infinite h_ns`
        - Helper `hcol : ∀ i j, i < j → (⟦xs.extract (f i) (f j)⟧ : _) = b`, proved from
          `h_color {f i, f j}` (card 2 via `h_mono`; `↑{f i, f j} ⊆ range f` via `mem_range_self`;
          `min'/max'` reduce to `f i`, `f j` by `h_mono`).
        - `refine ⟨⟦xs.extract 0 (f 0)⟧ * b, b, ?_, ?_, ?_⟩`
        - **`b * b = b`**: rewrite `b = ⟦extract (f 0)(f 1)⟧` and `b = ⟦extract (f 1)(f 2)⟧`
          (via `hcol`), then `buchiCongruence_mk_append` + `append_extract_extract` collapse to
          `⟦extract (f 0)(f 2)⟧ = b` (via `hcol 0 2`).
        - **`a * b = a`**: with `a = ⟦extract 0 (f 0)⟧ * b`, use `mul_assoc` and `b*b=b`
          (or `buchiCongruence_absorption`).
        - **frequently**: apply `frequently_iff_strictMono.mpr ⟨fun m => f (m+1), …, ?_⟩`; for each
          `m` show `⟦xs.extract 0 (f (m+1))⟧ = ⟦extract 0 (f 0)⟧ * b`:
          `⟦extract 0 (f (m+1))⟧ = ⟦extract 0 (f 0) ++ extract (f 0) (f (m+1))⟧`
          (`append_extract_extract`, `0 ≤ f 0 ≤ f (m+1)`) `= ⟦extract 0 (f 0)⟧ * ⟦extract (f 0)(f (m+1))⟧`
          (`buchiCongruence_mk_append`) `= ⟦extract 0 (f 0)⟧ * b` (`hcol 0 (m+1)`).
  - [ ] Verify with `lean_goal` at key steps and `lake build Cslib.Computability.Languages.Congruences.BuchiCongruence`.
- **Timing:** ~2 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` - add the core lemma.
- **Verification:**
  - `lake build Cslib.Computability.Languages.Congruences.BuchiCongruence` succeeds.
  - `lean_verify Cslib.Automata.NA.Buchi.buchiCongruence_recurrentPrefixClass` shows no `sorry`/extra axioms.

### Phase 2: Bridge lemma in OmegaRegularLanguage.lean [COMPLETED]

- **Goal:** State and prove the DMA-level recurrent-class lemma with the `infOcc` conclusion
  required by task 241, reusing the Phase 1 core lemma and `buchiCongr_DMA_run_eq`.
- **Tasks:**
  - [ ] Insert after `buchiCongr_DMA_run_eq` (OmegaRegularLanguage.lean:~416), before
        `proof_wanted buchiCongr_DMA_language_eq`:
        ```lean
        open NA.Buchi in
        /-- Recurrent-class lemma for the Büchi-congruence DMA run: for `[Finite State]` and any
        `xs`, there exist classes `a b` with `b * b = b`, `a * b = a`, and `a` occurring infinitely
        often in the DMA run `(buchiCongr_DMA na).run xs`. Bridge from
        `buchiCongruence_recurrentPrefixClass` via `buchiCongr_DMA_run_eq`. Used by Phase 4 of the
        McNaughton theorem (task 241) to close the forward direction of `buchiCongr_DMA_language_eq`. -/
        private lemma buchiCongr_recurrentClass [Inhabited Symbol] {State : Type} [Finite State]
            (na : NA.Buchi State Symbol) (xs : ωSequence Symbol) :
            ∃ a b : Quotient na.BuchiCongruence.eq, b * b = b ∧ a * b = a ∧
              a ∈ ((buchiCongr_DMA na).run xs).infOcc := by
          obtain ⟨a, b, hbb, hab, hfreq⟩ := buchiCongruence_recurrentPrefixClass na xs
          refine ⟨a, b, hbb, hab, ?_⟩
          simp only [ωSequence.mem_infOcc]
          simp only [buchiCongr_DMA_run_eq] at *  -- rewrites run xs k to ⟦xs.extract 0 k⟧
          exact hfreq
        ```
  - [ ] If `simp only [buchiCongr_DMA_run_eq]` does not fire under the `∃ᶠ` binder, use
        `Filter.Frequently.mono hfreq` with a pointwise rewrite, or
        `refine hfreq.mono fun k hk => ?_; rw [buchiCongr_DMA_run_eq]; exact hk`.
  - [ ] Confirm namespacing: `buchiCongruence_recurrentPrefixClass` resolves via the existing
        `open NA.Buchi in` (the lemma is in namespace `Cslib.Automata.NA.Buchi`).
  - [ ] Verify with `lake build Cslib.Computability.Languages.OmegaRegularLanguage`.
- **Timing:** ~0.75 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - add the bridge lemma.
- **Verification:**
  - `lake build Cslib.Computability.Languages.OmegaRegularLanguage` succeeds.
  - `lean_verify` on the new lemma shows no `sorry`.

### Phase 3: Full CI verification [COMPLETED]

- **Goal:** Confirm the whole repository builds and passes the CSLib CI pipeline.
- **Tasks:**
  - [ ] `lake exe cache get` (if needed for a fresh branch).
  - [ ] `lake build` (full project, syntax linters during build).
  - [ ] `lake exe checkInitImports` (both edited files already import `Cslib.Init` transitively; confirm).
  - [ ] `lake lint` (environment linters — verify no docBlame on the new lemmas; both have docstrings).
  - [ ] `lake exe lint-style` (text linters; `--fix` if needed).
  - [ ] `lake shake --add-public --keep-implied --keep-prefix` (import minimization; no new imports expected).
  - [ ] `lake test` (CslibTests).
- **Timing:** ~0.75 hours
- **Depends on:** 2
- **Files to modify:**
  - None expected (verification only); minor lint/style fixes to the two edited files if flagged.
- **Verification:**
  - All CI commands exit 0; CI green.

## Testing & Validation

- [ ] `buchiCongruence_recurrentPrefixClass` builds with no `sorry` and no added axioms.
- [ ] `buchiCongr_recurrentClass` builds with no `sorry`; conclusion is exactly
      `a ∈ ((buchiCongr_DMA na).run xs).infOcc` with `b * b = b` and `a * b = a`.
- [ ] `lake build` full project green.
- [ ] `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`, `lake test` all pass.
- [ ] No changes to `buchiFamily_cover`, `buchiFamily_saturation`, `buchiCongr_DMA`, or
      `buchiCongr_DMA_run_eq`.

## Artifacts & Outputs

- `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` — new lemma
  `buchiCongruence_recurrentPrefixClass`.
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — new private lemma
  `buchiCongr_recurrentClass`.
- `specs/429_.../summaries/01_ramsey-recurrent-class-summary.md` — implementation summary (at /implement time).

## Rollback/Contingency

- Changes are purely additive (two new lemmas). To revert: delete the two added lemmas; no
  existing declarations are modified, so removal restores the prior green state.
- If Phase 1's single proof exceeds `maxHeartbeats`, factor the `hcol` helper and the idempotence
  step into a separate `private lemma` (precedent: `frequently_via_accept` split from
  `buchiFamily_saturation`), then retry.
- If the core lemma proves intractable at the prefix-class level, fall back to inlining the entire
  Ramsey argument directly inside `buchiCongr_recurrentClass` in OmegaRegularLanguage.lean (single
  lemma), since that file imports both the Ramsey machinery and the task-428 monoid API. Mark the
  phase [BLOCKED] with the reached goal state if neither path closes.

## Key API (grounded from sources)

- `infinite_graph_ramsey` (InfiniteGraphRamsey.lean:125): `∃ c s, s.Infinite ∧ ∀ e : Finset ℕ,
  e.card = 2 → ↑e ⊆ s → color e = c`.
- `strictMono_of_infinite` (InfOcc.lean:82): infinite `ns` ⇒ `∃ φ, StrictMono φ ∧ range φ = ns`.
- `append_extract_extract` (Init.lean:485): `k ≤ m → m ≤ n → extract k m ++ extract m n = extract k n`.
- `buchiCongruence_mk_append` (`@[simp]`, BuchiCongruence.lean:292): `⟦u ++ v⟧ = ⟦u⟧ * ⟦v⟧`.
- `buchiCongruence_idempotentPow` / `buchiCongruence_absorption` (BuchiCongruence.lean:305/314).
- `frequently_iff_strictMono` (InfOcc.lean:34); `mem_infOcc` (`@[simp]`, InfOcc.lean:88).
- `buchiCongr_DMA_run_eq` (OmegaRegularLanguage.lean:405, private): `(buchiCongr_DMA na).run xs n
  = ⟦xs.extract 0 n⟧`.
- Pattern reference: `buchiFamily_cover` (BuchiCongruence.lean:118-151) — same color/Ramsey setup.
