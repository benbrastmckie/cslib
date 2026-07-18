# Joint old-label dispatch handoff — `deriv_reflect` + `dwitness_mem_of_maximal`

## Immediate Next Action

**Do not re-dispatch a quick follow-up against the current `probes/` scaffold.** This dispatch
confirms (with a sharper, independently-re-derived diagnosis) that both sorries need the SAME
fix — route (a): a step-indexed/well-founded Lindenbaum construction replacing Mathlib's
`zorn_le₀` in `primeC_exists_maximal`, carrying a "no label is old outside the base context or a
fresh/reserve-drawn adjunction" invariant through every construction step. This is a
**dedicated, multi-phase undertaking** ("Phase 4.5"), not a lemma-sized gap. Recommend the
orchestrator/user open a new planning effort for it (`/plan` or `/revise` on task 517) rather
than another `/implement --hard` dispatch against the same probe.

Read `probes/chain-union-reflection-probe.lean`'s new module section immediately preceding
`ChainCtx.deriv_reflect` (~line 295) for the full argument, and `dwitness_mem_of_maximal`'s
expanded sorry comment (~line 913) for the diamond-clause-specific instance of the same argument.

## Current State

- `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (1113 → ~1170 lines): **no proof content changed**. Both sorries (`deriv_reflect`,
  `dwitness_mem_of_maximal`) remain exactly where they were, `NOT closed`. What changed: both
  sorries' surrounding docstrings/comments were substantially expanded with a sharpened
  root-cause diagnosis (see below). Build verified green via `lake env lean` — exactly the same
  two `declaration uses 'sorry'` warnings as before this dispatch, no new errors, no regressions.
- No `Cslib/` files touched. `Labelled/Context.lean`, `Labelled/Deduction.lean`,
  `CS5Canonical.lean`, `CKExtension.lean` unchanged (confirmed via `git status --short`).
- `specs/517_labelled_bounded_context_cs5_completeness/plans/11_tprime-repair-cs5-completeness.md`:
  added a new paragraph after Phase 4's existing "On discharging Phase 3's `deriv_reflect` sorry"
  note, recording this dispatch's finding. Phase 3 and Phase 4 remain `[PARTIAL]` (unchanged
  headings) — this dispatch did NOT close either phase.

## What This Dispatch Actually Did

Read Simpson's raw proof text (`chunk_0102.md`/`chunk_0103.md`, the Prime Lemma 5.3.1 proof in
full, including the one-line "(◇E)" justification for the diamond-witness step) plus
`Context.lean`/`Deduction.lean` in full, then re-derived the obstacle from first principles and
tested THREE additional candidate shortcuts beyond the plan's own routes (a)/(b), all
independently ruled out with concrete arguments (not just re-stated as "hard"):

1. **Redefine `Deriv` with a finite-subgraph existential** (motivated by Simpson's `:5090`
   bundling relational + formula open assumptions into one finite list) — shown to reduce to the
   identical uniform-index obstruction one level down (the `boxI`/`diaE` step would need a SINGLE
   finite `G₀` valid across the WHOLE cofinite family; different `y`'s can each need a different
   finite `G₀_y` with no common bound). **Not a fix.**
2. **Skip the swap, reuse the induction hypothesis directly at "old" `y`** — supplies the fact but
   with a DIFFERENT chain index per `y`; `Directed` only bounds finitely many indices at once, not
   an unboundedly-indexed family. **Not a fix** (same obstruction, no relabelling needed to see
   it fail).
3. **A "bounded-old-label" conditional strengthening of `ChainCtx`** (single index dominating
   every old label) — this WOULD close the gap (real, provable implication, sketched and recorded
   in the probe), but is a strengthening of `ChainCtx`'s hypotheses that its current definition
   does not supply. Recorded as a genuine but conditional result, not claimed as closing anything.
4. Additionally confirmed, via direct inspection of `NIK.diaE`'s constructor
   (`Deduction.lean:309-312`), that a naive swap `swapFn v y'` for old `y'` is not merely
   *unproven* but **actively invalid** whenever `H.G` has any edge incident to `y'` other than
   possibly `(y,y')`: such an edge swaps to an edge touching `v`, which the target graph
   `H.G.addEdge y y'` does not know about.

**Conclusion**: route (a) — the step-indexed/well-founded construction — is the only viable
resolution, confirmed independently rather than re-asserted, and is genuinely larger than a
single dispatch: it requires replacing `zorn_le₀` in `primeC_exists_maximal` with a transfinite
recursion (not merely `ω`-indexed, since `Atom : Type u` is not assumed countable, so Simpson's
own "denumerable ⟹ choice-free iterative construction" remark does not directly transfer) that
carries a fresh-labels-only invariant through every step, and re-deriving the whole
`primeC`/`primeC_chain_bddAbove` apparatus against it.

## Key Decisions Made

1. **Did not attempt the transfinite reconstruction in this dispatch.** Scoping it honestly (a
   genuinely new `primeC'`, a well-founded recursion, re-threading every clause proof against a
   new invariant) is a multi-phase undertaking in its own right, not something a single dispatch
   budget can responsibly attempt and land build-green.
2. **Left both sorries exactly as-is** (not weakened, not axiomatized, not papered over) — the
   zero-debt invariant (`probes/` may carry `sorry`; `Cslib/` may not) is unaffected.
3. **Documentation-only edit**, landed as real file content in the probe (not just this handoff),
   per the mission's explicit fallback: "if the obstacle is genuinely deeper than one dispatch —
   produce a SHARP, corrected target definition and a concrete construction sketch."

## What NOT to Try

- **Do not re-attempt routes (a)/(b) as originally stated** without first designing the
  transfinite/well-founded construction properly (a real design task, not a quick fix).
- **Do not attempt Shortcut 1** (finite-subgraph `Deriv`) expecting it to help — formally shown to
  reduce to the same obstruction.
- **Do not attempt Shortcut 2** (direct IH reuse without relabelling) expecting it to avoid the
  index-uniformity problem — it does not.
- **Do not introduce an axiom** to discharge either sorry — explicitly prohibited by the plan's
  own Phase 3 contingency and unchanged by this dispatch.
- **Do not spend another dispatch's budget probing for a "clever" local fix** inside the current
  `probes/` file — three additional angles were tried and ruled out this dispatch, on top of the
  two the plan already named; the remaining path is a genuinely new construction, not a missed
  lemma.

## Remaining Goals (verbatim from plan)

Phase 4's stated objective — "prove `Γ ⊬_G x:A ⟹ ∃ 𝒯-prime (H,Δ) ⊇ (G,Γ) with `Δ ⊬_H x:A`` —
producing an inhabitant of the repaired `TPrime`" — remains assembled (`primeLemma`) but not
fully sorry-free; two documented strategic sorries remain, tracked in `sorry_inventory`.

## References

- Plan: `specs/517_labelled_bounded_context_cs5_completeness/plans/11_tprime-repair-cs5-completeness.md`
  (new paragraph after Phase 4's existing `deriv_reflect` discharge note).
- Probe (all analysis): `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (new module section before `ChainCtx.deriv_reflect`, ~line 295; expanded sorry comment on
  `dwitness_mem_of_maximal`, ~line 913).
- Literature consulted (raster-level read of the actual proof text, not just OCR/chunk text):
  `chunk_0102.md`, `chunk_0103.md` (Lemma 5.3.1 full proof, including the diamond-property
  one-line justification), at
  `/home/benjamin/Projects/Literature/simpson_1994_intuitionisticmodallogic/`.
- Prior handoffs: `phase-3-handoff-20260718.md`, `phase-4-handoff-20260718.md`,
  `nik-subst-followup-handoff-20260718.md`.
