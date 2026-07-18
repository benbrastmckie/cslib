# Task 517 Phase 5 Summary — `flo_oldlabel_transport` (the shared old-label reflection lemma)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Plan**: plans/12_wellfounded-zorn-oldlabel-reconstruction.md, Phase 5
- **Status**: [COMPLETED]

## What was proved

`flo_oldlabel_transport` (probe `chain-union-reflection-probe.lean`, ~line 1982) is now
sorry-free: a `NIK`-derivation witnessed at one fresh label `y₀` transports to **any** other label
`y'` present in `(𝒮.H σ).G.X` — old or fresh — matching the theorem's preserved Phase-1 signature
exactly. `lean_verify` confirms axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Plan Deviations

The plan's Task 5.1 anticipated a well-founded/rank induction using FLO-2's edge-locality bound to
avoid the "naive swap" collision the Postmortem Constraints flag. Closer analysis found a simpler
sufficient construction: a **one-directional** relabeling `substFn a b` (`a ↦ b`, identity
elsewhere, in particular fixing `b`) — unlike `swapFn a b`, which is an involution and therefore
also sends `b ↦ a` — never touches `b`'s own incident edges, because it never relocates `b`'s
structure onto `a`. The naive-swap collision is avoided **by construction** (satisfying the task's
own stated requirement), just via a different construction than anticipated. The only freshness
fact the proof uses is `hy₀ : y₀ ∉ (𝒮.H σ).G.X` (already part of the fixed signature); `FLO`/
`rankOf`/FLO-2 are not needed. `_hflo : FLO 𝒮 σ` remains in the signature (renamed with a leading
underscore to silence the unused-variable lint) because Phase 1 fixed it there; the argument is
unused by this proof.

This also subsumes Task 5.2 as originally scoped ("apply the transport lemma to build the full
cofinite premise... from the fresh witness... plus old-label transport... plus the dwitness
case"): because `substFn`-transport does not case on whether `y'` is fresh, old, or dwitness-shaped,
`flo_oldlabel_transport`'s single conclusion already covers every `y'` uniformly, so no separate
assembly step was required. `NIK.freshWitness_transport` is in fact the special case of the new
lemma where the extra hypothesis `y ∉ G.X` also happens to hold.

Both deviations are annotated inline on the plan's Task 5.1/5.2 checklist items.

## New landed assets (probe, all sorry-free, axiom-clean)

- `substFn a b l`: one-directional label substitution (`a ↦ b`, identity elsewhere).
- `substFn_self`, `substFn_other`: basic simp lemmas.
- `List.map_substFn_eq_self`: substitution is a no-op on a context that never mentions `a`.
- `NIK.relabelFresh`: the general one-directional relabeling transport theorem (mirrors
  `NIK.swap_relabel`'s case shape; the `boxI`/`diaE` cases use the target label itself as its own
  preimage, since `substFn a b` fixes every point besides `a`, rather than an involution formula).
- `flo_oldlabel_transport`: the Phase 5 target, built from `NIK.relabelFresh` exactly as
  `NIK.freshWitness_transport` was built from `NIK.swap_relabel`.

## `--lit` finding

Re-read `chunk_0102.md`/`chunk_0103.md` (Prime Lemma 5.3.1's proof and the diamond/deductive-closure
maximality argument). Confirmed: neither chunk contains any further detail on the fresh-vs-old
label distinction beyond what prior phases already extracted. Simpson's informal proof never
surfaces this obstacle — it is an artifact purely of this development's cofinite-quantifier Lean
encoding of `(□I)`/`(◇E)` (`Deduction.lean:288-312`). This confirms, rather than supersedes, the
module docstring's existing diagnosis.

## Verification

- `lake env lean` on the probe: exit 0, zero errors.
- Sorry count unchanged at 4 (`deriv_reflect` line 396, `dwitness_mem_of_maximal` line 944,
  `flo_succ` line 1453, `primeC'_exists_maximal` line 1784 — all pre-existing, documented strategic
  sorries from Phases 2-4, preserved verbatim, none newly introduced by this dispatch).
- `lean_verify Cslib.Logic.Modal.Labelled.flo_oldlabel_transport`: axioms `[propext,
  Classical.choice, Quot.sound]`, no `sorryAx`.
- `lean_verify Cslib.Logic.Modal.Labelled.NIK.relabelFresh`: axioms `[propext, Classical.choice,
  Quot.sound]`, no `sorryAx`.

## Preserved assets

Phases 1-4's landed assets (`Stage`/`FloTask`/`stepExt`/`FloSeq`/`rankOf`/`FLO`, `FloSeq.mono`,
`flo_succ`, `flo_limit`, `flo_succ_fair`/`flo_holds_everywhere`/`primeC'_exists_maximal`) were not
edited. `NIK.swap_relabel`/`NIK.freshWitness_transport`/`NIK.diaWitness_transport` (Phase 3/4) were
not edited either — the new `NIK.relabelFresh`/`substFn` machinery is additive, not a
replacement.

## Next steps

Phase 6: wire `flo_oldlabel_transport` into `ChainCtx.deriv_reflect` (probe ~line 396) and
`dwitness_mem_of_maximal`'s diamond old-label sub-case (probe ~line 944), closing both remaining
non-Phase-2/4 sorries, then re-verify `primeLemma` end-to-end. Recommended: `/implement 517 --hard
--lit`.
