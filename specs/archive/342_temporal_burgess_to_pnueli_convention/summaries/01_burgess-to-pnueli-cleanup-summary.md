# Implementation Summary: Task #342 — Burgess -> Pnueli Convention Cleanup

- **Status**: Implemented
- **Session**: sess_1751000000_342abc
- **Phases Completed**: 4 / 4

## What Was Done

This task cleaned up stale documentation that claimed the Temporal module used
"Burgess (event, guard)" argument order when the code had already been migrated
to Pnueli (guard, event) order by task 234.

### Phase 1: Convention docstrings/comments (no code change)

Rewrote Burgess-convention prose to Pnueli in 6 files:

- `Temporal/Syntax/Formula.lean`: Module header, Convention Note section, `someFuture`/`somePast`
  docstrings, complexity measure comments, `next`/`prev`/`release`/`trigger`/`strongRelease`/`strongTrigger` docstrings.
- `Temporal/Semantics/Satisfies.lean`: "Burgess Convention (Event, Guard)" header renamed to
  "Pnueli Convention (Guard, Event)"; inline `(φ=EVENT, ψ=GUARD)` annotation corrected.
- `Temporal/Syntax/Subformulas.lean`: Two inline comments on `allPast`/`allFuture` proofs.
- `LTL/Syntax/Formula.lean`: Convention Note cross-reference updated to state both logics
  agree on Pnueli; Embedding no longer described as doing an argument swap.
- `Temporal/Tableau/Rules.lean`: "Burgess Convention Reminder" section renamed to
  "Convention Note (Pnueli)" with corrected description.
- `Temporal/Tableau/Defs.lean`: Header convention section and `asUntl?` docstring updated;
  the reversed `(event, guard)` tuple in `asUntl?`/`asSnce?` is now documented as a local
  adapter convenience, not a Burgess convention claim.

### Phase 2: BX axiom doc comments

Updated all 17 BX axiom doc comments in `Temporal/ProofSystem/Axioms.lean` that used
Burgess `U(event, guard)` surface notation to Pnueli `U(guard, event)` notation:

- BX2G, BX2H: guard monotonicity — `χ U φ → χ U ψ` → `φ U χ → ψ U χ`
- BX3, BX3': event monotonicity — `φ U χ → ψ U χ` → `χ U φ → χ U ψ`
- BX13, BX13': enrichment — updated inline U/S notation
- BX5, BX5': self-accumulation — updated
- BX6, BX6': absorption — updated
- BX7, BX7': linearity — updated
- BX10, BX10': until/since eventuality — `U(ψ, φ) → F(ψ)` → `U(φ, ψ) → F(ψ)`
- BX12, BX12': F/P equivalence — `F(φ) → U(φ, ⊤)` → `F(φ) → U(⊤, φ)`
- dense_indicator — `¬U(⊤, ⊥)` → `¬U(⊥, ⊤)`

No constructor signatures changed.

### Phase 3: Bridge — reflexiveUntl/reflexiveSnce + Embedding

- Redefined `reflexiveUntl (φ ψ : Formula Atom)` in Pnueli (guard, event) order:
  - Old body: `φ ∨ (ψ ∧ (φ U ψ))` — guard and event were swapped in the formula
  - New body: `ψ ∨ (φ ∧ (φ U ψ))` — φ=guard, ψ=event; semantically correct
  - New docstring: `reflexiveUntl φ ψ at t ↔ ∃ s ≥ t, ψ(s) ∧ ∀ r ∈ [t,s), φ(r)`
- Redefined `reflexiveSnce` analogously: `ψ ∨ (φ ∧ (φ S ψ))`
- Fixed `LTL.Formula.toTemporal` `.untl` clause: removed argument swap
  - Old: `(toTemporal φ₂).reflexiveUntl (toTemporal φ₁)` (LTL guard=φ₁, event=φ₂, but called reversed)
  - New: `(toTemporal φ₁).reflexiveUntl (toTemporal φ₂)` (guard first — matches Pnueli directly)
- Updated `Embedding.lean` module docstring to describe direct Pnueli mapping.

### Phase 4: Verification

- `lake build Cslib.Logics.Temporal.Metalogic.Completeness`: green
- `lake build Cslib.Logics.LTL.ModelChecking`: green
- Zero sorries in Temporal/LTL files (one prose mention in GNBA.lean is pre-existing)
- Zero new axiom declarations
- `lake exe lint-style`: no warnings in touched files
- `lake lint`: no warnings in touched files
- `lake shake`: no warnings in touched files
- Pre-existing Bimodal/Modal build failures confirmed to pre-date this task (present on baseline branch without any changes)

## Plan Deviations

None. All changes stayed within the documented Phase 1-3 scope. The executable semantics
layer (`Satisfies`, `someFuture`, `Axiom` constructors, all Metalogic proofs) was left
unchanged. No `BurgessR*`/BX/Burgess-1982 identifiers were renamed.

## Files Modified

1. `Cslib/Logics/Temporal/Syntax/Formula.lean` — Phase 1 + Phase 3
2. `Cslib/Logics/Temporal/Semantics/Satisfies.lean` — Phase 1
3. `Cslib/Logics/Temporal/Syntax/Subformulas.lean` — Phase 1
4. `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` — Phase 2
5. `Cslib/Logics/Temporal/Tableau/Rules.lean` — Phase 1
6. `Cslib/Logics/Temporal/Tableau/Defs.lean` — Phase 1
7. `Cslib/Logics/LTL/Syntax/Formula.lean` — Phase 1
8. `Cslib/Logics/LTL/Embedding.lean` — Phase 3
