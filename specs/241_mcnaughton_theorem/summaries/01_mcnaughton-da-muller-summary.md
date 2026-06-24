# Implementation Summary: McNaughton's Theorem (Task #241)

- **Task**: 241 - mcnaughton_theorem
- **Status**: [PARTIAL]
- **Phase completed**: Phase 1 of 5 (implementation phases)
- **Committed**: `c4d3869d` — task 241 phase 1: reverse direction IsRegular.of_da_muller (DMA→NBA)

## What Was Implemented

### Phase 1: `IsRegular.of_da_muller` (DMA → ω-regular) [COMPLETED]

Added `theorem IsRegular.of_da_muller` to
`Cslib/Computability/Languages/OmegaRegularLanguage.lean` (lines 259–345).

**Statement**: `{State : Type} [Finite State] {Symbol : Type} [Inhabited Symbol] (da : DA.Muller State Symbol) : (language da).IsRegular`

**Proof strategy**:
1. For each state `q`, define a DBA `ba q` (same transition system as `da`, accept = `{q}`). The language of `ba q` is `{xs | q ∈ infOcc(da.run xs)}`.
2. For each `F : Finset State`, the language `langF F = {xs | infOcc(da.run xs) = ↑F}` is ω-regular: it equals `(⋂ q ∈ F, language (ba q)) ∩ (⋂ q ∉ F, (language (ba q))ᶜ)`, a finite intersection of DBA languages and their complements.
3. `language da = ⨆ F ∈ {F : Finset State | ↑F ∈ da.accept}, langF F` (finitely many Finsets since `State` is Finite).
4. Apply `IsRegular.iSup` (union of finitely many ω-regular languages) to conclude.

**Key technical fixes** (over the previous broken attempt):
- Replaced non-existent `Finset.toSet` with Lean 4 coercion `(F : Set State)` throughout
- Used `change` instead of `show` for goal-modifying tactics (style linter compliance)
- Extracted equality from `ωLanguage` set membership via `have h_eq' := h_eq`
- Used `h_fin_infOcc.coe_toFinset` for the `Set.Finite.toFinset` coercion identity
- Named the per-F language via `let langF ...` to avoid line-length violations

**CI result**: `lake build Cslib.Computability.Languages.OmegaRegularLanguage` — clean (0 errors, 0 warnings, 0 sorries, 0 new axioms).

## What Remains

### Phase 2: Forward decomposition scaffold `(⇒)` [NOT STARTED]
### Phase 3: Muller-packaging lemma `(⇒)` [NOT STARTED]
### Phase 4: Assemble `IsRegular.iff_da_muller` [NOT STARTED]
### Phase 5: Full CI verification and cleanup [NOT STARTED]

The forward direction `(⇒)` (ω-regular → DMA) is the genuine determinization content
of McNaughton's theorem. It requires building an explicit `DA.Muller` whose state space
is the quotient of the Büchi congruence and whose accept family comes from the
`buchiFamily` saturation cluster. This is substantially more complex than the reverse
direction and was not completed in this session.

The `proof_wanted IsRegular.iff_da_muller` remains in the file.

## Plan Deviations

- **Phase 0 coordination check**: Phase 0 was already marked [COMPLETED] by a prior agent; this session focused only on repairing Phase 1.
- **Phase 1 approach**: Used the direct decomposition approach (per-state DBA + Finset union) rather than a dedicated `Muller.toNABuchi` construction. The plan said "mirror `toNABuchi` structure" but the direct approach was cleaner and avoided adding new files to `ToNA.lean`.
- **Phases 2–4**: Not attempted due to context budget constraints. The orchestrator instructions permitted stopping after Phase 1 as an "acceptable partial outcome."

## Files Modified

- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — added 95 lines implementing `IsRegular.of_da_muller`

## Continuation Context

For the next agent to continue the forward direction:
1. The state space encoding decision: quotient of `na.BuchiCongruence.eq` where `na` is the NBA for `p` (via `p.IsRegular`).
2. The `buchiFamily` accept-set construction: `na.buchiFamily` = the saturating family.
3. The key lemmas available: `buchiFamily_saturation`, `buchiFamily_cover`, `buchiCongruence_fin_index`, `IsRegular.eq_fin_iSup_hmul_omegaPow`, `IsRegular.fin_cover_saturates`.
4. The `IsRegular.compl` proof in the same file is the exact template to follow.
5. The challenge: packaging the Choueka saturation result into a concrete `DA.Muller` object with the right `accept` set type (`Set (Set State)`).
