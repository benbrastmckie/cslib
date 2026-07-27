# Phase 6 Summary: `OutputCtx.fillLhs_empty_imp_fillEmpty` (the `cut` bridging induction)

- **Task**: 570 - nested_sound_impL_lambda_chain_induction
- **Phase**: 6 of 8
- **Plan**: `specs/570_nested_sound_impL_lambda_chain_induction/plans/01_lambda-chain-induction-plan.md`
- **Commit**: `14de905a`

## What Was Done

Landed `OutputCtx.fillLhs_empty_imp_fillEmpty` in `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Translation.lean`,
immediately after `OutputCtx.fillLhs_fm_mono` (as specified). This was the plan's flagged
highest-residual-risk phase — the one piece the research dispatch reasoned out on paper but never
compiled.

```lean
theorem OutputCtx.fillLhs_empty_imp_fillEmpty :
    ∀ (ctx : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom) ((ctx.fillLhs NestedLhs.empty).fm.imp ctx.fillEmpty.fm)
  | [] => cs5DerivImpSelf _
  | [Γ] => ⟨.ax [] _ (.andE1 Γ.fm Proposition.top)⟩
  | Γ :: Γ₂ :: rest =>
      cs5DerivAndCongrRight Γ.fm
        (cs5DerivDiaMono (OutputCtx.fillLhs_empty_imp_fillEmpty (Γ₂ :: rest)))
```

## Plan Deviations

**None.** All three cases closed exactly as sketched in the plan on the first attempt:
- `[]`: `fillLhs [] ∅` and `fillEmpty []` both reduce to `.empty` (`fm = ⊤`) — identity via
  `cs5DerivImpSelf`.
- `[Γ]`: `fillLhs [Γ] ∅ = comma Γ ∅` (`fm = Γ.fm ∧ ⊤`) versus `fillEmpty [Γ] = Γ` (`fm = Γ.fm`) —
  discharged directly by the `andE1` axiom instance.
- `Γ :: Γ₂ :: rest`: `cs5DerivAndCongrRight` over `cs5DerivDiaMono` applied to the IH, the
  identical shape as `OutputCtx.fillLhs_fm_mono`'s own cons-cons step (the named structural
  template).

The statement was not weakened or adjusted in any way from the plan's signature.

## Verification

```
lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Translation
```
Succeeds with zero errors and zero warnings (one 100-char style-linter warning was found on first
pass and fixed by rewording a docstring line; final build is fully clean).

```
grep -n "theorem OutputCtx.fillLhs_empty_imp_fillEmpty" Cslib/.../Nested/Translation.lean
```
Exactly one hit (line 285).

```
bash .claude/scripts/lean-sorry-census.sh Cslib
```
`sorry_count: 40`, unchanged from Phase 5's baseline (this phase adds no sorry). No
`Nested/Soundness.lean` entry in the inventory.

```
lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
```
Fails with **exactly one** diagnostic — `Soundness.lean:1536:2: Missing cases: _,
(NestedProof.cut (InputCtx.mk _ _ _) _ _ _)` — the pre-existing D3 error Phase 7 is scoped to fix.
No fallout from this phase's changes.

## Status

Phase 6 `[COMPLETED]`. Census still 40. `Translation` module green. `Soundness` red only on the
expected, named `cut` non-exhaustiveness error. Phases 3-5's critical path is unaffected; Phase 7
(land `nested_sound_cut` and the `.cut` arm, RED to green) can now proceed — both of its
dependencies (Phase 5 and Phase 6) are complete.
