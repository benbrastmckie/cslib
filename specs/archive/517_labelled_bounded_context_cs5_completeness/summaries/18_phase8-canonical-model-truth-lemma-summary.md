# Summary: Task 517 Phase 8 — Canonical Model + Truth Lemma (Simpson 5.3.2 / 8.2.6)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Plan**: plans/12_wellfounded-zorn-oldlabel-reconstruction.md, Phase 8
- **Status**: [COMPLETED] (full phase, not partial — both 8.1 and 8.2 landed in one dispatch)

## What Was Built

New mainline file `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/CanonicalModel.lean`
(namespace `Cslib.Logic.Modal.Labelled`), importing `PrimeLemma.lean` and
`Cslib.Logics.Modal.Metalogic.Constructive.Forcing` (for `CKForces`).

### Step 0 confirmations (recorded in the file's module docstring)

- **Canonical relation confirmed a third time**: `chunk_0103.md` (`𝒦^𝒯` construction) states
  `R_(H,Δ)(x,y) iff xRy in H` verbatim — the raw relation, not `𝒯-Comp(H)`. `CanonWorld.r` is
  built directly from `ctx.G.R`.
- **T-Comp confirmed UNNEEDED**: the truth lemma never introduces a `TClosure`/graph-completion
  step. Lemma 8.2.6 (`chunk_0166.md`) is the *bounded* (Ch 7-8) canonical model lemma, out of
  scope for the *unbounded* (Ch 5) route this development uses. `probes/lemma612-scaffold.lean`
  remains an untouched fallback.

### 8.1 — The canonical model

- `CanonWorld 𝒯 Atom`: a pointed `𝒯`-prime context `⟨ctx, lbl, mem⟩` — Simpson's `(H,Δ),y` pair,
  packaged as one type so it instantiates `CKForces`'s single-sorted `World` parameter.
- `CanonWorld.le`: context extension at a fixed label (`w.ctx ≤ w'.ctx ∧ w.lbl = w'.lbl`), with a
  `Preorder` instance.
- `CanonWorld.r`: the raw, same-context accessibility relation (`w.ctx = u.ctx ∧
  w.ctx.G.R w.lbl u.lbl`).
- `canonVal`/`canonBotForces`: the valuation `a_(H,Δ)` and a trivially-`False` `botForces`
  (`TPrime`'s Consistency clause bans exploding worlds, so no world of this model is fallible —
  this is what collapses `CKForces`'s Wijesekera `∀∃`-diamond/`∀`-box to Simpson's plain
  `∃`-diamond/`∀`-box on this particular model).
- The five `CKValidFC`-required monotonicity facts (`canonVal_mono`, `canonBotForces_mono`,
  `canonBotForces_val`, `canonBotForces_r`, `canonBotForces_r_wit`), all trivial given
  `botForces := fun _ => False`.

### 8.2 — The truth lemma (`canon_truth_lemma`)

`CKForces CanonWorld.r canonVal canonBotForces w φ ↔ (w.lbl ∶ φ) ∈ w.ctx.Γ`, by induction on `φ`,
transcribing `chunk_0104.md`/`chunk_0105.md`'s case-by-case proof:

- `atom`/`bot`: immediate from `canonVal`'s definition / `TPrime.consistency`.
- `and`/`or`: direct via the NIK introduction/elimination rules plus `TPrime.disjunction`, no
  context-growing needed.
- `imp` (⊃): forward is `⊃E` + monotonicity + deductive closure. Backward is Simpson's reductio:
  assume the semantic hypothesis, `by_contra` the underivability of `Δ,y:B ⊢ y:C`, apply
  `primeLemma` fresh to `H.addFormula (y∶B)` to obtain a witnessing extension that contradicts the
  semantic hypothesis, concluding `Δ,y:B ⊢ y:C` and hence (via `Deriv.impI`, a new
  `Deriv`-level `(⊃I)` helper) `y:B⊃C ∈ Δ`.
- `box` (□): forward is `□E` + monotonicity + deductive closure. **Backward (the hard direction)**:
  pick a fresh raw prefix variable `z` outside `H`'s witnessing reserve `V'` (via a new
  `Context.addFreshVar` extension — one new node `Label.var z` + edge `y R z`, `Γ` unchanged, with
  the reserve patched to `insert z V'`), `by_contra` the underivability of `z:B` in the extended
  graph, apply `primeLemma` fresh to get a witnessing extension contradicting the semantic
  hypothesis at the new edge, concluding `Δ ⊢_{H∪{yRz}} z:B`. Since `z ∉ H`,
  `NIK.oldLabelTransport` (already landed sorry-free in Phase 6) upgrades the single witness to the
  cofinite family `NIK.boxI` needs (with the empty exclusion set `L := ∅`), giving
  `Δ ⊢_H y:□B`, hence `y:□B ∈ Δ` by deductive closure. **The Ch.6 tree-surgery bridge
  (`probes/lemma612-scaffold.lean`) was not needed** — this closes with only `primeLemma` (already
  landed) plus the one-directional relabeling machinery from Phase 6.
- `diamond` (◇): forward is immediate from `TPrime.diamond`. Backward specializes the `∀∃` clause
  at the reflexive instance `w' := w`, recovering Simpson's plain `∃`-witness, then `◇I` +
  deductive closure.

Two small new lemmas support the box case:
- `Label.InW.mono`: `Label.InW` is monotone in the reserve `V'` (structural recursion, mirrors
  `Label.ne_dwitness_self`'s style).
- `Context.addFreshVar`/`Context.addFreshVar_le`/`Context.mem_addFreshVar`: the "adjoin one fresh
  raw-variable node + edge, `Γ` unchanged" context extension and its basic properties.

A small `Deriv`-level toolkit (`Deriv.of_mem`, `Deriv.impI`) mirrors the filter-and-reweaken
pattern already used by `Deriv.orE`/`Deriv.subst`/`dwitness_mem_of_maximal` in `PrimeLemma.lean`.

## Plan Deviations

- **Ch.6 tree-surgery bridge not needed** for box-backward (plan's contingency anticipated this
  might be required; it was not). Reason: `primeLemma` itself (already landed, Phase 6/7) supplies
  exactly the witnessing-extension reductio Simpson's own proof uses, with no dependency on the
  bounded/tree-surgery apparatus.
- **Single dispatch, not 2-3**: the plan estimated 2-3 dispatches for Phase 8 and explicitly
  permitted a partial landing. Because 8.1's design (pairing a `TPrime` context with a
  distinguished domain element) made every truth-lemma case a direct transcription of
  `chunk_0104.md`/`chunk_0105.md` reusing only already-landed Phase 6/7 machinery
  (`primeLemma`, `NIK.oldLabelTransport`, the five `TPrime` clause fields), the full phase
  (Step 0 + 8.1 + 8.2) completed in one dispatch.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.CanonicalModel`: green.
- Full `lake build Cslib`: 3244/3244 jobs green.
- `lake exe checkInitImports`: pass.
- `lake lint`: 0 warnings (after `@[nolint unusedArguments]` on `Context.addFreshVar`'s freshness
  witness and `canonBotForces`'s constant-`False` world argument — both are genuinely,
  by-design unused in their bodies).
- `lake exe lint-style`: 0 warnings.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestions for the new file.
- `lake exe mk_all --module`: `Cslib.lean` updated with the new import.
- `lake test`: green (9235/9236 built; the one non-"Built" line is the aggregate test-driver
  target; pre-existing `sorry` warnings in unrelated Propositional Tableau files are unregressed
  — none in the new file or in `PrimeLemma.lean`).
- `lean_verify canon_truth_lemma`: axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- `lean_verify Context.addFreshVar`: axioms `[propext, Classical.choice, Quot.sound]`.
- Zero `sorry`, zero new `axiom`, zero vacuous definitions in the new file (`grep` counts confirm
  0 in `CanonicalModel.lean`; the repo-wide `sorry`/`axiom` baseline counts are unchanged by this
  dispatch — all pre-existing occurrences live in files this dispatch did not touch).

## Files Touched

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/CanonicalModel.lean` (new, ~430 lines)
- `Cslib.lean` (barrel import added via `mk_all --module`)
- `specs/517_labelled_bounded_context_cs5_completeness/plans/12_wellfounded-zorn-oldlabel-reconstruction.md`
  (Phase 8 marked `[COMPLETED]`, checklist items checked off with citations)
- `specs/517_labelled_bounded_context_cs5_completeness/summaries/18_phase8-canonical-model-truth-lemma-summary.md`
  (this file)

## Continuation

Phase 9 ("Frame-class match — domain-relative equivalence ⟹ `cs5FCIncest`") is next: derive the
domain-relative `EquivalenceOn` on `H.G.X` from `TPrime.clModel : ClassicalModelOn TS5 H.G.X H.G.R`
(via `equivalence_of_classicalModelOn_TS5`, already landed in `Context.lean`) and match the
`cs5FCIncest` conjuncts (`CS5Canonical.lean:234,255`). `canon_truth_lemma` and the `CanonWorld`
apparatus from this phase are the inputs Phase 10's `cs5_completeness` assembly will combine with
Phase 9's frame-class match.
