# Follow-up handoff — `NIK.subst` cut admissibility closed

## Immediate Next Action

The only remaining work item for Phase 4/primeLemma is the **joint dispatch on the two
"old label" cofinite-range sorries**: `dwitness_mem_of_maximal`'s diamond sorry
(`probes/chain-union-reflection-probe.lean`, currently near line 945) and Phase 3's
`ChainCtx.deriv_reflect` sorry (currently near line 329). Both share the identical root cause
(cofinite-quantification encoding vs. potentially-infinite `Context.G.X`/graph domain) — see the
Phase 4 handoff (`phase-4-handoff-20260718.md`) and this task's `.orchestrator-handoff.json`
`sorry_inventory` for the full diagnosis and the two candidate closing routes already ruled out
(Mathlib's `zorn_le₀` is non-constructive; no monotonicity-based "old label" argument found yet).
Once both close, `primeLemma` is fully sorry-free and Phase 4's outstanding work is complete —
plus reconsider whether Phase 5 is needed at all (flagged, not yet acted on — see the plan).

## Current State

- **`NIK.subst`** (`probes/chain-union-reflection-probe.lean`, ~line 1041) is now **proven,
  sorry-free**. Closed via a new auxiliary lemma `NIK.subst_aux` (~line 969): structural
  induction on the `NIK`-derivation, generalized over an accumulating prefix `Δ'` (needed because
  `impI`/`orE`/`diaE` prepend to the front of the whole context during the induction, mirroring
  how `NIK.weaken`'s own case shape handles the same three constructors) and re-weakening the
  substituting derivation `hsub` to whichever graph the current case's premises live at
  (`boxI`/`diaE` extend the graph by one edge via `Graph.addEdge`, using a small inline `G ≤
  G.addEdge x w` proof term rather than a new named lemma).
- `Deriv.subst` and `deductiveClosure_of_maximal` (both already written, previously "sorry-free
  modulo `NIK.subst`") are now **unconditionally sorry-free** — confirmed via
  `mcp__lean-lsp__lean_verify` on both `NIK.subst` (axioms: `propext` only) and
  `deductiveClosure_of_maximal` (axioms: `propext`, `Classical.choice`, `Quot.sound` — no
  `sorryAx`).
- `TPrime` clause 1 (deductive closure) is now **fully proven**, alongside clauses 0
  (`clModel`), 2 (consistency), and 3 (disjunction) — all four sorry-free. Only clause 4
  (diamond) still routes through a sorry (`dwitness_mem_of_maximal`'s "old label" case).
- Probe build verified clean: `lake env lean` on the whole probe file exits 0 with exactly TWO
  `declaration uses 'sorry'` warnings (down from three) — `ChainCtx.deriv_reflect` (Phase 3,
  inherited, untouched) and `dwitness_mem_of_maximal` (Phase 4's diamond old-label case,
  untouched). No new axioms, no vacuous definitions.
- Zero-debt invariant holds: all work stayed in `probes/`; `git status --short` confirms this
  dispatch touched only `probes/chain-union-reflection-probe.lean`,
  `plans/11_tprime-repair-cs5-completeness.md`, this handoff file, and
  `.orchestrator-handoff.json`/`.return-meta.json`. `Cslib/Logics/Modal/Tableau/GenericDriver.lean`
  appears modified in `git status` from a **concurrent session** working on a different task
  (511) — not touched by this dispatch, left strictly alone per the territory instruction.

## Key Decisions Made

1. **Generalize via an auxiliary lemma (`NIK.subst_aux`) taking the accumulating prefix `Δ'` as
   an explicit universally-quantified argument**, rather than trying `induction h generalizing
   Δ` directly on the original theorem (whose scrutinee's context index is the compound term
   `Δ ++ (y∶B)::Γ`, not a plain variable). Concretely: prove `∀ {G Γ₀ φ}, NIK 𝒯 G Γ₀ φ → ∀ Δ',
   Γ₀ = Δ'++(y∶B)::Γ → NIK 𝒯 G Γ (y∶B) → NIK 𝒯 G (Δ'++Γ) φ` by `intro G Γ₀ φ hderiv; induction
   hderiv with ...`, keeping the equation `Γ₀ = Δ'++(y∶B)::Γ` and the `hsub`-shaped hypothesis
   *inside* the per-branch goal (not yet introduced) so the induction's motive naturally
   generalizes both. `NIK.subst` itself is then a one-line specialization via `rfl` for the
   equation.
2. **`hsub` is re-derived (weakened) fresh in the `boxI`/`diaE` branches**, not threaded as a
   single fixed hypothesis — since those two constructors' recursive premises live at a
   *different* graph (`G.addEdge x w`), the branch-local `hsub : NIK 𝒯 G Γ (y∶B)` is upgraded via
   `NIK.weaken` and a small inline proof `⟨Set.subset_union_left, fun _ _ h => Or.inl h⟩ : G ≤
   G.addEdge x w` (no new named lemma added to the file for this — it was simpler inline than
   worth naming).
3. Cons/append associativity goals (`(x∶A)::(Δ'++L) = (x∶A)::Δ'++L`) needed an explicit
   `List.cons_append` rewrite after `rw [heq]` — plain `rw [heq]`'s automatic post-rewrite `rfl`
   did not close them on its own.

## What NOT to Try

- Do not re-attempt `NIK.subst` — it is done. Do not re-open its design (the induction shape
  above is settled and verified).
- Do not conflate `NIK.subst`'s closure with the diamond/`deriv_reflect` "old label" sorries —
  they are a genuinely separate, harder obstacle (structural gap between cofinite-quantification
  and a potentially-infinite graph domain), not something `NIK.subst`'s technique bears on.

## Remaining Goals (verbatim from plan, Phase 4 section)

"Discharged all **five** clauses (0 plus the four numbered) with the repaired rules" — now FOUR
of five (0, 1, 2, 3) are sorry-free; only clause 4 (diamond) still carries
`dwitness_mem_of_maximal`'s "old label" sorry, jointly with Phase 3's `deriv_reflect` sorry (same
root cause). See the plan's Phase 4 verification paragraph (updated this dispatch) and
`.orchestrator-handoff.json`'s `sorry_inventory` for the full joint-dispatch framing.

## References

- Plan: `specs/517_labelled_bounded_context_cs5_completeness/plans/11_tprime-repair-cs5-completeness.md`
  (Phase 4 section, task 3's deductive-closure bullet and verification paragraph updated this
  dispatch).
- Prior handoff (still valid background): `specs/517_labelled_bounded_context_cs5_completeness/handoffs/phase-4-handoff-20260718.md`.
- Probe (all work): `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (`NIK.subst_aux` ~line 969, `NIK.subst` ~line 1041).
