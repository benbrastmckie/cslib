# Phase 7 Summary: Land `nested_sound_cut` and the Missing `.cut` Arm — Build RED to GREEN

## What Was Done

Landed `nested_sound_cut` in `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`,
closing the last unhandled `NestedProof` constructor and taking the whole `Cslib` library from
RED to GREEN for the first time in this task.

### Proof Route

Following the source's own one-liner ("For the cut-rule we additionally observe that `A ⊃ A` is
always provable"):

1. `nested_sound_impL ctx A A hA hB` (the `B := A` instantiation) gives
   `⊢ (ctx.fillLhs (A ⊃ A)•).fm`.
2. `⊢ A ⊃ A` (always provable) weakens to `⊢ ⊤ ⊃ fm((A ⊃ A)•)`, fed through the already-landed
   `InputCtx.fillLhs_fm_antitone` to get `⊢ (ctx.fillLhs (A ⊃ A)•).fm ⊃ (ctx.fillLhs ∅).fm`; `modus
   ponens` with step 1 gives `⊢ (ctx.fillLhs ∅).fm`.
3. Bridge `(ctx.fillLhs ∅).fm ⊃ ctx.fillEmpty.fm` and `modus ponens` to reach the goal.

### The One Genuinely New Piece: A Local Reverse Bridge

Step 3 is where the plan's sketch needed real work beyond direct composition. Phase 6 landed
`OutputCtx.fillLhs_empty_imp_fillEmpty : (Λ.fillLhs ∅).fm ⊃ Λ.fillEmpty.fm` (the forward
direction, at the `OutputCtx`/`ctx.Λ` level). `nested_sound_cut` needs the same fact lifted one
level up, through `box`/`ctx.Γ'`, to `(ctx.fillLhs ∅).fm ⊃ ctx.fillEmpty.fm` (the `InputCtx`
level).

`NestedRhs.box Φ Ψ`'s `fm` translation (`Syntax.lean`) is `□(Φ.fm ⊃ Ψ.fm)` — **contravariant**
in `Φ`. Composing Phase 6's *forward* lemma through the standard congruence chain
(`cs5DerivImpCongrLeft` then `cs5DerivBoxMono`, exactly as `InputCtx.fillLhs_fm_antitone` itself
does) therefore yields the *reverse* box-level implication, not the forward one `nested_sound_cut`
needs to chain forward via `modus ponens`.

Since this phase's file list names `Soundness.lean` as sole owner (no `Translation.lean` edits
permitted), the fix is a new **local private** lemma in `Soundness.lean`,
`cs5DerivFillEmptyImpFillLhsEmpty : Λ.fillEmpty.fm ⊃ (Λ.fillLhs ∅).fm` — the reverse-direction
companion to Phase 6's lemma. It is proved by the identical three-case induction on the
`OutputCtx`, using only combinators already in Soundness.lean's own local Hilbert toolkit, plus
one new tiny private combinator `cs5DerivAndTopIntro : P ⊃ (P ∧ ⊤)` for the `[Γ]` base case (in
place of Phase 6's `andE1` elimination — both directions are provable here since the two formulas
differ only by a redundant `⊤`-conjunct). Feeding this reverse lemma into
`cs5DerivImpCongrLeft` + `cs5DerivBoxMono` + `OutputCtx.fillRhs_fm_mono` yields exactly the
forward `(ctx.fillLhs ∅).fm ⊃ ctx.fillEmpty.fm` bridge needed.

### Other Changes

- Added the arm `| _, .cut ctx A p q => nested_sound_cut ctx A (nested_sound p) (nested_sound q)`
  to `nested_sound`, placed after `.bStruct` to match `Rules.lean`'s constructor order.
- Corrected the `nested_sound` section docstring: removed the stale "every constructor except
  `impL`" sentence now that all 19 constructors (including `cut`) are discharged.
- Docstrings on `nested_sound_cut` and the new local lemmas cite Lemma 4.9's `cut` sentence
  (page 10) and eq. (3.1) (page 7), and explicitly note this is soundness of `cut` as a
  primitive, not cut admissibility (§6, out of scope).

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness`: succeeds, zero errors,
  zero warnings.
- `lake build` (full `Cslib` target): succeeds, 3259/3259 jobs — **the first fully green build in
  this task**, flipping the baseline RED (missing-cases diagnostic on `NestedProof.cut`) to GREEN.
- `lake exe checkInitImports`: passes silently.
- `bash .claude/scripts/lean-sorry-census.sh Cslib`: `sorry_count: 40`, unchanged from the
  Phase 5/6 baseline, with no `Nested/Soundness.lean` entry.
- `lean_verify` on both `nested_sound_cut` and `nested_sound`: only the three standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no new custom axioms.

## Plan Deviations

None against the plan's stated proof route (steps 1–3 followed exactly as sketched). The plan's
step 3 text ("Compose with `OutputCtx.fillLhs_empty_imp_fillEmpty`... lifted appropriately") was
terse about the exact composition; working out that a direct `cs5DerivImpCongrLeft` application
of the *forward* Phase 6 lemma yields the wrong (reverse) direction due to `box`'s contravariance,
and that a new local reverse-direction companion lemma was needed, was this phase's own
discovery — not a deviation from the plan's route, but the concrete mechanism realizing it. No
`Translation.lean` edits were made; the sole-owner constraint held.

## Commit

`bb537ac1` — `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` and the plan file
only (narrow stage).
