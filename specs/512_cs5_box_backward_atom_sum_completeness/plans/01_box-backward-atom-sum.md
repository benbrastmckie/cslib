# Implementation Plan: Task #512 — CS5 Box-Backward via Doubled-Atom Combined System

- **Task**: 512 - cs5_box_backward_atom_sum_completeness
- **Status**: [NOT STARTED]
- **Effort**: 14 hours
- **Dependencies**: 509 (soundness + mechanized obstruction, both branches landed)
- **Research Inputs**: reports/01_box-backward-atom-sum.md
- **Artifacts**: plans/01_box-backward-atom-sum.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Attempt CS5 constructive completeness (Branch A) by discharging the box-backward truth-lemma case
that task 509 left open. The deliverable `cs5_box_backward` must produce, given a quasi-prime `H`
with `□A ∉ H`, a SIMULTANEOUS prime pair `(H', T)` with `H ⊆ H'`, `boxInv H' ⊆ T`, `boxInv T ⊆ H'`,
`A ∉ T`, `□A ∉ H'`. The designed repair encodes the pair as a single prime theory over the doubled
atom space `Atom ⊕ Atom` (tag `H'`-formulas via `τL := Proposition.map Sum.inl`, `T`-formulas via
`τR := Proposition.map Sum.inr`) under a combined axiom system `CS5Combined` that adds the two
cross-condition implications (`crossLR`/`crossRL`) as AXIOMS so deductive closure preserves them by
construction. A single `prime_set_exclusion` at `CS5Combined` excluding `E = {τL(□A), τR A}` yields
a combined prime theory `T'`, from which `(H', T)` are recovered by preimage. The construction then
feeds `cs5_box_backward` → `cs5_truth_lemma` → the CS5 completeness theorem.

**Definition of done**: either (success) `cs5_completeness` lands sorry-free with `#print axioms`
showing only `Classical.choice`/`propext`/`Quot.sound`; or (negative result) the seed-consistency
gate (Phase 3) is proved impossible and lands as a mechanized obstruction theorem with completeness
kept `[BLOCKED]` citing both 509 obstructions plus this third one. NO `sorry` and NO new axiom in any
landed Cslib file under either outcome; probe `sorry` is confined to `specs/512_.../probes/`.

### Research Integration

Integrated from `reports/01_box-backward-atom-sum.md`:
- Exact box-backward obligation reconstructed from the canonical-model architecture (§1): CS5 needs
  its OWN `cs5_truth_lemma` because its tail `cs5Tail` (`CS5.lean:632`) is symmetric; the generic
  `ck_truth_lemma` (`CKTruthLemma.lean:133`) re-tails to a NON-symmetric maximal witness and cannot
  be reused for the box case.
- The flagged "new infrastructure" (τL/τR derivation lifting) is a corollary of the task-419
  `Metalogic.Deriv.map` (`ProofSystemMorphism.lean:186`) / `ProofSigHom` (`:124`) machinery with a
  bimodal `Lifting.lean` precedent (`liftDerivationWith`/`liftFormula`) — NOT built from scratch (§3.3).
- Feasibility is UNCERTAIN with exactly ONE genuine failure node: combined-system seed consistency
  `cs5Combined_seed_excludes` (§2.2), which is NOT a mechanical port of the sorry-free
  `cs5_pair_seed_mem` (`probes/cs5-pair-primeness.lean:98`). This is Phase 3, the go/no-go gate.
- Pacheco Lemma 16/18 (§3.4) negation-completeness move is UNSOUND for a quasi-prime poset-maximal
  set and MUST NOT be transcribed; only the Zorn skeleton (seed → chain-union → maximal → project)
  ports, and the primeness engine comes from CSLib's `prime_set_exclusion` (disjunction property via
  `hOrE`/`set_maximal_is_prime`).

### Prior Plan Reference

No prior plan for task 512. Prior task 509 (`specs/509_rescope_CK_CS5_constructive_completeness/`)
landed CS5 soundness and a mechanized obstruction on both branches; its Phase 8 probe
(`probes/cs5-pair-primeness.lean`) is the design source for the doubled-atom repair and confirms the
closure-instability blocker (`Cons_Y(Z) := boxInv Z ⊆ Y` not closure-stable, `:45-58`) that the
axiomatized cross-conditions are designed to kill.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (roadmap flag not set). This task advances the CS5
constructive-completeness effort tracked under task 509's rescoping.

## Goals & Non-Goals

**Goals**:
- Land `Proposition.map` + `@[simp]` connective-commutation lemmas in `Basic.lean`.
- Land `CS5Combined`, the `τL`/`τR` `ProofSigHom`s, and `DerivationTree` transport corollaries via
  `Deriv.map` in a new file `CS5Canonical.lean`.
- Resolve the go/no-go gate: prove (or refute) `cs5Combined_seed_excludes` sorry-free.
- On success: land `cs5_box_backward`, `cs5_truth_lemma`, and `cs5_completeness` /
  `cs5_soundness_completeness`, sorry-free with no new axiom.
- On failure at Phase 3: land the failure as a mechanized obstruction theorem; keep completeness
  `[BLOCKED]` citing both 509 obstructions plus this third one — still no `sorry`, no new axiom.

**Non-Goals**:
- Do NOT transcribe Pacheco Lemma 16/18 verbatim (negation-completeness is unsound here).
- Do NOT reuse `ck_truth_lemma`'s box-backward case for CS5 (its witness is not in `cs5Tail`).
- Do NOT rebuild the prime-exclusion engine or `Deriv.map`/`ProofSigHom` machinery — re-instantiate.
- Do NOT rebuild `cs5FC''_cs5Mreach` (`CS5.lean:1242`) — already landed.
- Do NOT introduce any `sorry` or any new `axiom` into `Cslib/`; do NOT use a vacuous `def _ := True`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: cross-axiom leakage — `CS5Combined` collapses L/R sorts, making the seed exclusion FALSE (`4`+`B`+cross, the Pacheco "collapsing" theme) | H | M | Phase 3 is an explicit go/no-go gate with two discharge routes; if both fail, the collapse IS the third mechanized obstruction (an ACCEPTABLE outcome), not a `sorry`. |
| R2: `cs5_axiom_relabel` totality — the 17-case `CS5ModalAxiom φ → CS5ModalAxiom (φ.map f)` must cover all constructors | M | L | Each case is τ commuting with one connective (definitional); Phase 2 enumerates all 17 with `@[simp]` map lemmas from Phase 1. |
| R3: `bDia`/`Kd` interaction with cross axioms enabling new `◇`-collapses in seed consistency (`cs5_dia_bot_imp_bot`, `CS5.lean:740`) | M | M | Check when building the separating model in Phase 3; the designated-pair frame must satisfy the two cross soundness cases without new diamond collapse. |
| R4: `H'`/`T` per-sort quasi-primeness projection needs `τL`/`τR` injective on `∨`-heads AND prime `T'` ⇒ each preimage has the disjunction property | M | L | Mechanize the projection in Phase 4 (§2.1 verified clean); `Proposition.map Sum.inl`/`Sum.inr` are injective by structural recursion. |
| R5: file-size / build-time — Zorn + `Deriv.map` over `Atom⊕Atom` may be slow, CS5.lean would exceed 2000 lines | L | M | Split: `Proposition.map` → `Basic.lean`; combined machinery + truth lemma → new `CS5Canonical.lean` importing `CS5.lean`; build incrementally; `lake exe mk_all --module` after adding the file. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are strictly sequential: Phase 3 is a decision gate whose outcome (success vs. obstruction)
selects the content of Phases 4-5. No two phases can execute in parallel.

---

### Phase 1: Atom relabeling primitive (`Proposition.map`) [COMPLETED]

- **Goal:** Add the only genuinely new primitive — `Proposition.map : (α → β) → Proposition α →
  Proposition β` plus `@[simp]` connective-commutation lemmas — in `Basic.lean`. Confirmed absent by
  grep (report §3.3, §4a). *Low risk, ~40 lines.*
- **Tasks:**
  - [ ] Add `Proposition.map` by structural recursion over all 7 constructors
    (`atom`/`bot`/`imp`/`and`/`or`/`box`/`diamond`) per the sketch in report §4(a).
  - [ ] Add `@[simp]` commutation lemmas `Proposition.map_imp`, `_and`, `_or`, `_box`, `_diamond`,
    `_bot`, `_atom` — each `rfl`.
  - [ ] Add injectivity fact for `Proposition.map` under an injective `f` (needed by Phase 4 primeness
    projection) — `Function.Injective f → Function.Injective (Proposition.map f)`, by structural
    recursion.
  - [ ] Locate `Proposition` in `Basic.lean` first via `lean_file_outline` / grep to place the def in
    the correct namespace and section.
- **Timing:** ~1.5 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/{path}/Basic.lean` — home of `Proposition`; add `map` + `@[simp]` lemmas +
    injectivity. (Confirm exact path via grep for `inductive Proposition` before editing.)
- **Success criteria / CI gates:**
  - All 7 commutation lemmas close by `rfl`; scoped `lake build` of `Basic.lean` green.
  - `lake exe checkInitImports`, `lake exe lint-style` clean on the touched file.
  - No `sorry`, no new axiom.
- **Verification:** `lake build <Basic module>` succeeds; `#print axioms Proposition.map` shows no
  `sorryAx`.

---

### Phase 2: Combined system + derivation transport [COMPLETED]

- **Goal:** In a NEW file `CS5Canonical.lean` (importing `CS5.lean`), define `CS5Combined`, the
  17-case relabel helper `cs5_axiom_relabel`, the `τL`/`τR` `ProofSigHom`s, and the `DerivationTree`
  transport corollaries — reusing `Deriv.map` / `LiftViaMorphism`, NOT rebuilding. *Medium risk
  (tedium of 17 cases), ~250-300 lines.*
- **Tasks:**
  - [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` with `import Cslib.Init`
    and `import` of the CS5 module; register via `lake exe mk_all --module`.
  - [ ] Define `inductive CS5Combined : Proposition (Atom ⊕ Atom) → Prop` with a `base` constructor
    wrapping all 17 `CS5ModalAxiom` constructors plus `crossLR (B) : CS5Combined ((box (B.map
    Sum.inl)).imp (B.map Sum.inr))` and `crossRL (B) : CS5Combined ((box (B.map Sum.inr)).imp
    (B.map Sum.inl))` (report §4(b)).
  - [ ] Prove `cs5_axiom_relabel : ∀ {f}, CS5ModalAxiom φ → CS5ModalAxiom (φ.map f)` — 17 cases, each
    discharged by the Phase-1 `@[simp]` commutation lemmas (connective commutes with `map`).
  - [ ] Build `τL : ProofSigHom (modalSig (@CS5ModalAxiom Atom)) (modalSig (@CS5Combined Atom))` with
    `g := Proposition.map Sum.inl`, `g_imp := fun _ _ => rfl`, `axMap := CS5Combined.base ∘
    cs5_axiom_relabel`, `clMap := (box ↦ box, rfl)` (report §4(c)); define `τR` symmetrically with
    `Sum.inr`.
  - [ ] Land the transport corollaries `DerivationTree CS5ModalAxiom Γ φ → DerivationTree CS5Combined
    (Γ.map τL.g) (τL.g φ)` (and `τR`) via `ofDeriv (Deriv.map τL (toDeriv d))` using `modalEquiv`
    (`LiftViaMorphism.lean:65/79/94`); clone the shape of bimodal `liftDerivationWith`.
- **Timing:** ~3 hours
- **Depends on:** 1
- **Reused assets (real names + file:line):**
  - `Metalogic.Deriv.map` — `ProofSystemMorphism.lean:186` (the universal formula-type-changing lift).
  - `ProofSigHom {F₁ F₂}` — `ProofSystemMorphism.lean:124`.
  - `modalSig`, `toDeriv`, `ofDeriv`, `modalEquiv` — `LiftViaMorphism.lean:65/79/94`.
  - `liftDerivationWith` / `liftFormula` — `Bimodal/.../ConservativeExtension/Lifting.lean` (precedent).
  - `CS5ModalAxiom` — the 17 constructors (from `CS5.lean`).
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (new).
- **Success criteria / CI gates:**
  - `CS5Combined`, `cs5_axiom_relabel` (all 17 cases), `τL`, `τR`, and both transport corollaries
    compile sorry-free; `lake build` of the new module green.
  - `lake exe checkInitImports` (verifies `Cslib.Init` import), `lake exe lint-style`,
    `lake shake --add-public --keep-implied --keep-prefix` clean.
  - No `sorry`, no new axiom.
- **Verification:** `#print axioms` on the transport corollaries shows no `sorryAx`; the τL transport
  round-trips a trivial CS5 derivation to a CS5Combined derivation.

---

### Phase 3: SEED CONSISTENCY — the GO/NO-GO DECISION GATE [PARTIAL]

**RESUMED-DISPATCH PROGRESS** (2026-07-15, route-2 dispatch per report 02): pursuing the
proof-theoretic derivation-induction route recommended by
`reports/02_phase3-seed-consistency.md`. Real, sorry-free, axiom-clean progress landed in
`CS5Canonical.lean` (see `summaries/02_phase3-route2-partial-summary.md` and the continuation
handoff `handoffs/02_phase3-route2-continuation.md` for full detail):

- **Landed** (commit "task 512 phase 3: land collapse-projection + HR seed-pair facts"): the
  atom-collapse `ProofSigHom` `τ0` (erases `τL`/`τR` tagging via `Sum.elim id id`, projecting
  `CS5Combined`-derivations back to `CS5ModalAxiom`-derivations); this **fully discharges two of
  the four seed-exclusion obligations**: `cs5Combined_bot_excluded` (`⊥` cannot leak) and
  `cs5Combined_boxA_excluded` (`τL(□A)` cannot leak) — both via direct contradiction
  (`H` consistent / `h_not`). Also landed: the four `HR`-seed-pair facts (mechanical port of
  `cs5_pair_seed_mem`) and the box-equivalence lemmas `□(τL B) ↔ □(τR B)` (syntactic form of
  "crossRL-conservativity", via necessitation + `K` + axiom `4` on the cross axioms).
- **Still open**: `τR A` excluded, and the mixed `bigOr {τL(□A), τR A}` disjunction case. Per
  report 02 §5 (confirmed independently in this dispatch via an explicit L-uniform-valuation
  countermodel argument), **no compositional/homomorphic translation** (which the landed
  collapse projection is an instance of) can witness this direction — it requires the bespoke,
  non-homomorphic derivation-induction invariant report 02 describes, which needs
  canonical-model-scale machinery comparable in depth to `CS5.lean`'s own soundness apparatus (or
  more). This was NOT closed within this dispatch's budget; see the continuation handoff for the
  detailed gap analysis and one promising unexplored lead (a "necessity transfer" conjecture:
  whether `⊢CS5Combined τLΨ → τRA` forces `⊢CS5 Ψ → □A`, which was not confirmed or refuted).
- **Status**: `[PARTIAL]`, not `[BLOCKED]` — no proved obstruction exists (the claim is still
  believed TRUE per report 02's ~85-90% confidence), so this is not the FAILURE/PIVOT branch;
  it is real, incremental progress toward the SUCCESS branch, incomplete due to genuine
  mathematical depth. Phases 4-5 remain `[NOT STARTED]` (both consume Phase 3's full closure).

**RESUMED-DISPATCH PROGRESS 2** (necessity-transfer conjecture attempted, per
`handoffs/03_necessity-transfer-attempted.md`): landed `cs5Combined_necTransfer` (sorry-free,
axiom-clean: `⊢CS5Combined τLΨ→τRA` implies `⊢CS5 □Ψ→□A`) — a genuine but INSUFFICIENT byproduct
of the necessity-transfer conjecture's natural proof-algebra route (necessitation + `K` +
box-equivalence), proved vacuous at exactly the hardest case `Ψ := A` (`□A→□A` trivially true).
This exhausts the necessitation/K/cross-axiom algebraic route as a dead end (structurally: only
boxed-antecedent consequences are reachable this way) and independently sharpens report 02 §4's
semantic-route impossibility to rule out ANY atom-indexed model (not just homomorphic
translations). **Only the derivation-height induction (report 02 §5) remains unexplored** after
three dispatches. Phase 3 remains `[PARTIAL]`.

**BLOCKER** (Phase 3, task 512 implementation dispatch, 2026-07-14 — ORIGINAL, pre-route-2):

- **What failed**: `cs5Combined_seed_excludes` was not closed sorry-free by either route within
  this dispatch's budget. No `sorry`/placeholder was written to `Cslib/` for it (zero-debt
  maintained); the obligation is simply not yet attempted in committed Lean code.
- **What was tried (analysis only, no Lean written for this phase)**:
  1. **Simplification confirmed**: `h_not : Proposition.box A ∉ H` implies `⊥ ∉ H` (else
     `mem_of_bot_mem` would force `□A ∈ H` via `efq`), so `H` is a genuine *consistent* prime
     theory for the whole of Phase 3 — the exploding-head case in `quasi_prime_set_exclusion`'s
     style split is vacuous here and does not need separate handling.
  2. **Naive "identify both copies" semantic model** (set `v(w)(inl p) = v(w)(inr p)` for all `w`,
     any frame) was checked and **fails**: it forces `Satisfies M w (τL C) ↔ Satisfies M w (τR C)`
     for every `C`, which cannot refute `τR A` whenever `A ∈ H` — a live possibility since
     `A ∈ H ∧ □A ∉ H` is perfectly consistent for a normal modal prime theory (necessity does not
     follow from truth). The two copies must be allowed to disagree on non-boxed content while
     agreeing on boxed content — exactly the box-backward gap's semantic content.
  3. **Naive 2-point discrete-frame model** (`World := Bool`, trivial preorder, total relation)
     was checked and **fails** for a different reason: with only two *point* worlds, `Satisfies`
     of a *compound* (boxed) `τL`-tagged formula does not track `H`-membership correctly unless
     the companion world's valuation is *also* pinned to agree with `H` on boxed content — but
     pinning it that tightly requires the companion world's theory to already be the desired
     prime `T` (or something with equivalent closure properties), which is circular relative to
     what Phase 3/4 are trying to construct. A genuine truth-lemma-grade semantic argument appears
     to need canonical-model-scale (effectively infinite) structure, not a hand-built toy frame.
  4. **Naive "collapse to a single copy" proof-theoretic projection** (`π := Sum.elim id id`,
     i.e. `π ∘ τL = π ∘ τR = id`; `crossLR`/`crossRL` project to the already-present `tBox` axiom
     `□B → B`) was checked and **fails**: it only yields `τL '' H ⊢_{Combined} τR A ⟹ H ⊢_{CS5} A`,
     which is not a contradiction (`A ∈ H` is consistent with `h_not`). This confirms route 2 as
     literally sketched in the report is too weak; a *sharper* proof-theoretic invariant
     (tracking, by induction on derivation height/structure, exactly which combined-formulas are
     derivable from the pure-`τL`-tagged seed) would be needed instead, and is comparable in
     depth to a genuine soundness argument, not a mechanical clone.
- **Why it's stuck**: the seed-consistency obligation is a genuine (not merely mechanical)
  mathematical claim about a bespoke combined derivation system; both discharge routes sketched in
  the plan need either (a) canonical-model-scale semantic machinery (not the toy 2-world frame the
  plan sketch suggested — that sketch under-specifies how the companion world's valuation is
  pinned down) or (b) a bespoke proof-theoretic logical-relation/invariant argument by induction
  on `CS5Combined` derivations (not simply the collapse-projection sketch, which is provably too
  weak, per finding 4 above). Both are substantial, genuinely novel proof developments — on the
  order of the semantic soundness apparatus already in `CS5.lean` (`cs5_axiom_sound`/
  `cs5_soundness`, ~150 lines) or more, not a "clone an existing template" step like Phases 2/4/5.
- **What is needed to unblock**: either (a) a correctly-specified separating model — likely
  reusing the *existing* CS5 canonical `CS5Segment`/`cs5Mreach` machinery for the L-side world
  (`CS5Segment.ofHead H`) together with a *second*, honestly-built quasi-prime witness for the
  R-side that already carries the needed cross-conditions (which risks being exactly as hard as
  Phase 4's pair-recovery problem, i.e. potentially circular) — or (b) a derivation-height
  induction proving the sharp invariant "every combined-formula derivable from `τL '' H` is either
  pure-`τL`-tagged with underlying formula in `H`, pure-`τR`-tagged with underlying formula in
  `Y := modalDeductiveClosure CS5ModalAxiom (boxInv H)`, or a positive propositional combination of
  such formulas that is *not* provably equal to `τL(□A)`, `τR A`, or a `bigOr`-disjunction
  containing one of them" — a genuinely new logical-relation lemma, not sketched in this plan in
  enough detail to mechanize directly. `box_mem_of_boxed_context` (used by the sorry-free
  `cs5_pair_seed_mem`, `probes/cs5-pair-primeness.lean:98`) is the key existing ingredient for the
  *pure-`τL`* half of such an invariant (it is exactly how `A ∉ cl_{CS5}(boxInv H)` is established
  at the set level) but does not by itself cover the cross-tagged/mixed-disjunction cases that
  `CS5Combined`'s axioms (applied uniformly over the whole `Atom ⊕ Atom` language, not just
  per-tag) make derivable.
- **Prohibited workarounds**: no `sorry`, no `def _ := True`/vacuous placeholder was introduced for
  this obligation — confirmed absent from `Cslib/` (see Phase 2 commit; nothing was added for
  Phase 3 in this dispatch).

- **Goal:** Prove `cs5Combined_seed_excludes` — that `CS5Combined`'s two cross axioms do NOT collapse
  the L/R sorts, i.e. neither `τR A` nor `τL(□A)` (nor any disjunction of them) is derivable from the
  seed `cl_combined(τL '' H)` when `□A ∉ H`. This is the single node deciding success vs. negative
  result. *High risk, ~150-250 lines.* **This is NOT a mechanical port of the sorry-free
  `cs5_pair_seed_mem` (`probes/cs5-pair-primeness.lean:98`): the cross axioms create L↔R interaction
  that must be shown non-collapsing.**
- **Exact obligation (report §2.2):**
  ```lean
  theorem cs5Combined_seed_excludes {H} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
      (h_not : Proposition.box A ∉ H) :
      DerivExcludes (modalDerivationSystem (@CS5Combined Atom))
        {x | x = (Proposition.box A).map Sum.inl ∨ x = A.map Sum.inr}
        (modalDeductiveClosure CS5Combined ((Proposition.map Sum.inl) '' H))
  ```
- **Tasks (route 1 — semantic, RECOMMENDED first):**
  - [ ] Build the 2-world designated separating frame — the positive-model dual of the landed
    `CS5BoxGapWorld` (`CS5.lean:1246+`, already a Kripke countermodel with `Fintype`/`Decidable`
    instances) — interpreting `τL` atoms at an `H'`-world and `τR` atoms at a `boxInv-H` tail world
    omitting `A`, related by the symmetric CS5 relation.
  - [ ] Prove `CS5Combined`-soundness over this frame class: reuse `cs5_soundness` (`CS5.lean:311`) /
    `cs5_axiom_sound''` (`CS5.lean:366`) for the 17 `base` cases; add exactly TWO new soundness cases
    for `crossLR`/`crossRL` (one-liners on the designated-pair frame).
  - [ ] Exhibit the concrete model satisfying `τL '' H`, refuting `τR A` and `τL(□A)`; soundness then
    yields `DerivExcludes` for the singleton lists, and `bigOr`-disjunction handling closes the
    general list case (each disjunct fails at the designated world).
  - [ ] Check R3: confirm the cross axioms enable no new `◇`-collapse on the frame (`cs5_dia_bot_imp_bot`
    interaction).
- **Tasks (route 2 — proof-theoretic projection, FALLBACK):**
  - [ ] If route 1 cannot be closed sorry-free, attempt: any combined derivation `τL '' H
    ⊢_{CS5Combined} τR A` projects to a `CS5` derivation forcing `□A ∈ H` (contradiction). The cross
    axioms project to `boxInv`-transfer steps.
- **Tasks (PIVOT — if BOTH routes fail):**
  - [ ] Land the failure as a mechanized obstruction theorem in `CS5Canonical.lean` (a PROVED negative
    statement: e.g. `cs5Combined_collapses` showing the seed exclusion is false / the sorts are forced
    to collapse). No `sorry`, no new axiom.
  - [ ] Stop the constructive branch; skip Phases 4-5's completeness content and go directly to the
    obstruction writeup in Phase 5.
- **Timing:** ~4 hours
- **Depends on:** 2
- **Reused assets (real names + file:line):**
  - `CS5BoxGapWorld` — `CS5.lean:1246+` (landed countermodel to dualize).
  - `cs5_soundness` — `CS5.lean:311`; `cs5_axiom_sound''` — `CS5.lean:366`.
  - `cs5_dia_bot_imp_bot` — `CS5.lean:740` (R3 check).
  - `DerivExcludes`, `bigOr` — `PrimeExclusion.lean:328/320`.
  - `cs5_pair_seed_mem` (set-level analogue, sorry-free) — `probes/cs5-pair-primeness.lean:98`
    (reference pattern for the `box_mem_of_boxed_context` step, NOT a direct port).
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`.
- **DECISION GATE — success/failure branches (BOTH pre-specified):**
  - **SUCCESS** (route 1 or route 2 closes `cs5Combined_seed_excludes` sorry-free) → proceed to
    Phase 4 (pair recovery) and Phase 5 (truth lemma + completeness).
  - **FAILURE** (both routes fail — the sorts collapse) → land a PROVED obstruction theorem, mark CS5
    completeness `[BLOCKED]`, and in Phase 5 write the obstruction citing both 509 obstructions plus
    this third one. Still NO `sorry`, NO new axiom. This is an EXPLICITLY ACCEPTABLE outcome.
- **Success criteria / CI gates:** `cs5Combined_seed_excludes` (SUCCESS) OR the obstruction theorem
  (FAILURE) compiles sorry-free; `lake build` green; `checkInitImports`/`lint-style`/`shake` clean;
  no `sorry`, no new axiom. `#print axioms` shows no `sorryAx` on the landed statement.
- **Verification:** `lean_goal` shows "no goals" on the chosen discharge; `#print axioms` clean.

---

### Phase 4: Prime `T'` + pair recovery → `cs5_box_backward` [NOT STARTED]

- **Goal:** (SUCCESS branch only) Clone `quasi_prime_set_exclusion` at `CS5Combined`, apply
  `prime_set_exclusion` with `E = {τL(□A), τR A}` to obtain a prime combined theory `T'`, define
  `H'`/`T` as `τL`/`τR` preimages, prove the 7 pair clauses, and emit `cs5_box_backward`. *Medium
  risk, ~180-250 lines.* (If Phase 3 hit the FAILURE branch, SKIP this phase.)
- **Tasks:**
  - [ ] Clone `quasi_prime_set_exclusion` (`CS5.lean:871`) at `CS5Combined` — swap the axiom system +
    closure; the 10 generic discharge arguments (`hOrI1/2`, `hOrE`, `hEFQ`, `cl_subset`,
    `cl_mem_imp`, `cl_admissible_of_cons`, `bot_mem_cl_of_not_cons`, `hCut`, `hConsChain`) copy over
    because they are parametric over the axiom predicate and `CS5Combined` re-declares
    `implyK/implyS/efq/orI1/orI2/orE` (report §2.1).
  - [ ] Apply `prime_set_exclusion` (`PrimeExclusion.lean:558`) with seed `modalDeductiveClosure
    CS5Combined (τL '' H)` and exclusion `E = {τL(□A), τR A}`, consuming Phase-3's
    `cs5Combined_seed_excludes` as the `h_excl` argument.
  - [ ] Define `H' := {C | τL C ∈ T'}`, `T := {C | τR C ∈ T'}`.
  - [ ] Prove the 7 pair clauses (report §2.1 table):
    - `H ⊆ H'` from the seed inclusion;
    - `H'`, `T` deductively closed (over `CS5ModalAxiom`) via the Phase-2 τL/τR transport + closure;
    - `H'`, `T` quasi-prime via primeness projection + `Proposition.map` injectivity (Phase 1);
    - `boxInv H' ⊆ T` via `crossLR` axiom + closure/MP; `boxInv T ⊆ H'` via `crossRL`;
    - `□A ∉ H'` and `A ∉ T` from `DerivExcludes E T'` at singletons `[τL(□A)]`, `[τR A]` (using
      `bigOr [x] = x ∨ ⊥`, `orI1`).
  - [ ] Emit `cs5_box_backward` with the exact signature from report §1 (lines 44-50).
- **Timing:** ~3 hours
- **Depends on:** 3
- **Reused assets (real names + file:line):**
  - `prime_set_exclusion` — `PrimeExclusion.lean:558`.
  - `set_maximal_is_prime`, `set_excluding_chain_union`, `DerivExcludes`, `SetExcludingSupersets`,
    `bigOr` — `PrimeExclusion.lean:428/400/328/334/320`.
  - `quasi_prime_set_exclusion` — `CS5.lean:871` (template to clone).
  - `cs5_diam_witness` — `CS5.lean:906` (E-exclusion singleton/`orI1` pattern).
  - `cs5_fcsymbox_theory`, `cs5_fc4_theory` — `CS5.lean:1043/1122` (canonical-closure templates).
  - `PrimeAdmissible` fields — `PrimeExclusion.lean:63`.
  - `boxInv`, `QuasiPrime`, `.closed`, `.disj` — `Segment.lean:64-183`.
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`.
- **Success criteria / CI gates:** `cs5_box_backward` compiles sorry-free with the exact §1 signature;
  all 7 pair clauses discharged; `lake build` green; `checkInitImports`/`lint-style`/`shake` clean; no
  `sorry`, no new axiom.
- **Verification:** `#print axioms cs5_box_backward` shows no `sorryAx`; the returned `(H', T)`
  satisfies all seven conjuncts by construction.

---

### Phase 5: Truth lemma + completeness (or obstruction writeup) [NOT STARTED]

- **Goal:** (SUCCESS branch) Land `cs5_truth_lemma` (clone `ck_truth_lemma`, box-backward via
  `cs5_box_backward`), `realize` via Lindenbaum, and `cs5_completeness` /
  `cs5_soundness_completeness` via `ckvalidFC_completeness` + the landed `cs5FC''_cs5Mreach`.
  (FAILURE branch) Write the mechanized-obstruction module docstring/theorem citing all three
  obstructions and keep CS5 completeness `[BLOCKED]`. *Low risk once Phase 4 lands, ~170 lines.*
- **Tasks (SUCCESS branch):**
  - [ ] Clone `ck_truth_lemma` (`CKTruthLemma.lean:133`) into `cs5_truth_lemma`; keep
    atom/bot/and/or/imp/diamond/box-forward cases (port from `ck_truth_lemma`/`cs4_truth_lemma`),
    replace the box-backward case with `cs5_box_backward`.
  - [ ] Build the two witness worlds `w' := CS5Segment.ofHead H'_qprime` (`≥ s` since `H ⊆ H'`) and
    `u := CS5Segment.ofHead T_qprime`; establish `cs5Mreach w' u` from the three pair clauses; apply
    the IH `A ∉ T ⇒ ¬CKForces A` at `u` to refute `□A` at `s` (report §1, integration paragraph).
  - [ ] Provide `realize` via Lindenbaum (`quasi_prime_exclusion` / `quasi_prime_box_exclusion`,
    `SegmentLindenbaum.lean:159/188/258`) + `cs5_truth_lemma`.
  - [ ] Land `cs5_completeness` / `cs5_soundness_completeness` via `ckvalidFC_completeness`
    (`CKExtension.lean:227`) supplying `realize` and `h_canonFC := cs5FC''_cs5Mreach` (`CS5.lean:1242`,
    already landed).
  - [ ] Update the CS5 module docstring (`CS5.lean:156`) to record completeness as PROVED and link the
    new `CS5Canonical.lean`.
- **Tasks (FAILURE branch — if Phase 3 pivoted):**
  - [ ] Write the mechanized obstruction theorem's docstring and keep the CS5 completeness statement
    `[BLOCKED]`, citing both 509 obstructions plus this third (`cs5Combined` sort-collapse) one.
  - [ ] Update `CS5.lean:156` module docstring to reflect the third obstruction and the BLOCKED status.
- **Timing:** ~2.5 hours
- **Depends on:** 4
- **Reused assets (real names + file:line):**
  - `ck_truth_lemma` — `CKTruthLemma.lean:133`; `cs4_truth_lemma` — `CS4.lean:~455` (closest template).
  - `ckvalidFC_completeness` — `CKExtension.lean:227`; `cs5FC''_cs5Mreach` — `CS5.lean:1242` (landed).
  - `cs5Seg`, `CS5Segment.ofHead`, `cs5Val`, `cs5Bot` — `CS5.lean:975-1030`.
  - `cs5_diam_witness` — `CS5.lean:906` (supplies `diam_witness` for the H'-segment).
  - Lindenbaum: `quasi_prime_exclusion`/`quasi_prime_box_exclusion` — `SegmentLindenbaum.lean:159/188/258`.
  - `CKSegment`, `cmreach`, `cval`, `cbotForces`, `boxInv`, `QuasiPrime` — `Segment.lean:64-183`.
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`;
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (docstring at `:156` only).
- **Success criteria / CI gates (SUCCESS):** `cs5_completeness` compiles sorry-free; `#print axioms
  cs5_completeness` shows ONLY `Classical.choice`/`propext`/`Quot.sound` (no `sorryAx`, no new axiom).
  Full pipeline green: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`.
- **Success criteria / CI gates (FAILURE):** the obstruction theorem compiles sorry-free; completeness
  is documented `[BLOCKED]` with three cited obstructions; same full CI pipeline green; no `sorry`, no
  new axiom.
- **Verification:** `#print axioms cs5_completeness` (SUCCESS) or `#print axioms <obstruction>`
  (FAILURE) clean; `lake test` passes.

---

## Testing & Validation

- [ ] `lake build` (full) succeeds after each phase.
- [ ] `lake test` (CslibTests suite) passes at Phase 5.
- [ ] `lake exe checkInitImports` — every touched file imports `Cslib.Init`.
- [ ] `lake exe lint-style` — clean on all touched files.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused/missing imports.
- [ ] `#print axioms cs5_completeness` (SUCCESS) shows only `Classical.choice`/`propext`/`Quot.sound`;
      NO `sorryAx`, NO new axiom. On FAILURE, `#print axioms` on the obstruction theorem is equally clean.
- [ ] `lake exe mk_all --module` run after adding `CS5Canonical.lean`.
- [ ] Grep confirms no `sorry`/`admit`/new `axiom` in any `Cslib/` file touched; probe `sorry` (if any)
      stays under `specs/512_.../probes/`.

## Artifacts & Outputs

- `Cslib/Logics/Modal/{path}/Basic.lean` — `Proposition.map` + `@[simp]` commutation + injectivity (Phase 1).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (new) — `CS5Combined`, `cs5_axiom_relabel`,
  `τL`/`τR` homs + transport, `cs5Combined_seed_excludes` (or obstruction), pair recovery,
  `cs5_box_backward`, `cs5_truth_lemma`, `cs5_completeness`/`cs5_soundness_completeness` (Phases 2-5).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — module docstring update at `:156` (Phase 5).
- `specs/512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md` (this file).
- `specs/512_cs5_box_backward_atom_sum_completeness/summaries/01_box-backward-atom-sum-summary.md`
  (produced at implementation completion).

## Rollback/Contingency

- Each phase is committed separately (`task 512 phase {P}: {name}`) at a green `lake build`; a failing
  phase reverts only its own commit, leaving earlier green phases intact.
- Phase 1 (`Basic.lean`) is broadly reusable and low-risk; if later phases are abandoned it can remain
  (a harmless relabeling primitive) or be reverted independently.
- Phase 3 FAILURE is not a rollback but a planned PIVOT to the mechanized-obstruction deliverable —
  Phases 1-2 stay landed, Phases 4-5 adapt to the obstruction writeup. Completeness remains `[BLOCKED]`.
- No new axiom is ever introduced, so `#print axioms` remains the single acceptance gate; if any
  `sorryAx` appears, revert to the last clean commit and re-dispatch that phase.
