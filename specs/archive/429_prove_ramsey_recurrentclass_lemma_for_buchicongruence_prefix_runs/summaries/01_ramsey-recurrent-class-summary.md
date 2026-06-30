# Implementation Summary: Task #429

- **Task**: 429 - prove_ramsey_recurrentclass_lemma_for_buchicongruence_prefix_runs
- **Status**: COMPLETED
- **Plan**: specs/429_prove_ramsey_recurrentclass_lemma_for_buchicongruence_prefix_runs/plans/01_ramsey-recurrent-class.md

## Outcome

Two new lemmas were added, both building and verified sorry-free:

1. `buchiCongruence_recurrentPrefixClass` in
   `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` — the pure prefix-class core lemma.
2. `buchiCongr_recurrentClass` (private) in
   `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — the DMA-level bridge lemma with the
   `infOcc` conclusion required by task 241 Phase 4.

## Proof Strategy

### Phase 1: Core lemma (`buchiCongruence_recurrentPrefixClass`)

Mirrors `buchiFamily_cover` exactly:
- Color function `t ↦ ⟦xs.extract t.min' t.max'⟧` on `Finset ℕ`.
- `infinite_graph_ramsey` yields monochromatic color `b` and infinite set `ns`.
- `strictMono_of_infinite h_ns` gives `f : ℕ → ℕ` with `range f = ns`.
- Helper `hcol : ∀ i j, i < j → ⟦xs.extract (f i) (f j)⟧ = b` extracted via
  `Finset.min'_pair`, `Finset.max'_pair`, `min_eq_left`, `max_eq_right`.
- `b * b = b` (idempotence): proved via `calc` using `hcol 0 1`, `hcol 1 2`,
  `buchiCongruence_mk_append`, `append_extract_extract`, `hcol 0 2`.
- `a * b = a` with `a := ⟦xs.extract 0 (f 0)⟧ * b`: follows from `mul_assoc` + `hbb`.
- `∃ᶠ k in atTop, ⟦xs.extract 0 k⟧ = a`: via `frequently_iff_strictMono` with witness
  `fun m => f (m+1)`. Each `m` shows `⟦xs.extract 0 (f (m+1))⟧ = ⟦xs.extract 0 (f 0)⟧ * b`
  using `append_extract_extract` + `buchiCongruence_mk_append` + `hcol 0 (m+1)`.

**Key deviation from plan**: Plan proposed rewriting `b` with `← hcol` but `rw` rewrites ALL
occurrences of `b` simultaneously. Fixed by using a `calc` chain that rewrites the individual
factors in context where the RHS is fixed.

### Phase 2: Bridge lemma (`buchiCongr_recurrentClass`)

One-liner using `Frequently.mono`:
```
hfreq.mono fun k hk => (buchiCongr_DMA_run_eq na xs k).trans hk
```
This converts `∃ᶠ k in atTop, ⟦xs.extract 0 k⟧ = a` to
`∃ᶠ k in atTop, (buchiCongr_DMA na).run xs k = a` via `buchiCongr_DMA_run_eq`.

## CI Results

| Check | Result |
|-------|--------|
| `lake build BuchiCongruence` | PASS |
| `lake build OmegaRegularLanguage` | PASS |
| `lake lint` (our files) | PASS (no warnings in modified files) |
| `lake exe lint-style` (our files) | PASS |
| `lake shake` (our files) | PASS (no suggestions) |
| `lake exe mk_all --module` | PASS (No update necessary) |
| `lake test` | Pre-existing failure in `Intuitionistic.Completeness` (unrelated) |
| sorry count (modified files) | 0 |
| New axioms | None (standard: propext, Classical.choice, Quot.sound) |

## Artifacts

- `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` — added `buchiCongruence_recurrentPrefixClass`
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — added `buchiCongr_recurrentClass`

## Plan Deviations

- `hbb` proof: Plan proposed `rw [← hcol 0 1, ← hcol 1 2, ...]` but `rw [← h]` rewrites ALL
  occurrences of `b`, collapsing both factors. Fixed with `calc` chain.
- `heval` sub-proof: Plan used `simp only [color, dif_pos h_ne']`; implemented with `change`
  (required by CSLib lint rule: `show` changed goal, so `change` was required) followed by
  `rw [dif_pos h_ne', min'_pair, max'_pair, min_eq_left, max_eq_right]`.
