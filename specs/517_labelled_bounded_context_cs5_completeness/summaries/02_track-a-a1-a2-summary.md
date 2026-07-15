# Execution Summary: Task #517 — Track A (A1 + A2)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Plan**: plans/02_decomposed-track-a-b-c.md
- **Session**: sess_1784145761_061228
- **Phases executed**: A1 (IKAx repair), A2 (FS route probe) — both [COMPLETED]
- **Type**: cslib

## What was done

### A1 — `IKAx` repair (`probes/lemma612-scaffold.lean`)

Added Simpson's Figure 3-7 base-`IK` axioms 3/4/5 as new, unconditional `IKAx` constructors
(`diaBot : ¬◇⊥`, `diaOr : ◇(A∨B) ⊃ (◇A∨◇B)`, `fs : (◇A ⊃ □B) ⊃ □(A ⊃ B)`), matching the source
PDF (p.56) exactly. Mechanical, additive (existing constructors kBox/kDia/dDia/tBox/.../fiveB
untouched), so `NIK_to_NIKAx`/`TClosure.hilbertTransport` are structurally unaffected — confirmed
by rebuilding the whole scaffold file (`lake env lean`, exit 0, sorry-free).

### A2 — `CS5 ⊢ FS` route probe (`probes/fischer-servi-probe.lean`, new file)

Attempted a sorry-free syntactic Hilbert derivation of
`FS := (◇A → □B) → □(A → B)` against `CS5ModalAxiom` (`CS5.lean:182`). Outcome is **mixed but
decisive**, landed as two sorry-free theorems:

1. **`fs_context_relative_half`** (`Deriv (@CS5ModalAxiom Atom) [◇A→□B] (A→B)`, depends on
   `[propext, Classical.choice]` — the same footprint as every other `Derivable`-level CS5 fact,
   e.g. `cs5_dia_bot_imp_bot`, `cs5_dia_or`, confirmed by direct comparison). This mechanizes the
   **precise syntactic obstruction**: the context-relative half succeeds unconditionally (chain
   `A → ◇A → □B → B` via `T`'s two halves and modus ponens), but lifting it to the boxed
   `□(A → B)` needs `DerivationTree.necessitation`, whose type requires an **empty**-context
   sub-derivation (`Metalogic/DerivationTree.lean:147`) — and this derivation genuinely uses the
   hypothesis `H := ◇A → □B`, so it is never closed. A short combinator-chain search (attempting
   to "smuggle" `H` into scope via `bBox`) did not find an alternative route within the dispatch's
   bound. **Genuine underivability was not proved** — this is a documented obstruction to the
   *naive* route, not a completeness-level impossibility result.
2. **`fs_sound''`** (`CKValidFC.{u,v} cs5FC'' FS`, **axiom-free**, confirmed via `#print axioms`).
   `FS` **is** semantically valid over every model satisfying `CS5`'s weakened frame condition
   `cs5FC''`. The proof uses *only* the `bBox`/`bDia`-supporting frame clauses (`hsymbox`,
   `hsymm`) — no reflexivity or transitivity needed. This is exactly the fact Track B's
   canonical-model route needs (Simpson's Ch.3 canonical-model confluence condition F2, p.53),
   and it is now a mechanized, reusable lemma rather than an open semantic question.

## Route implication for A3 (next action, not yet executed)

A2's outcome **de-risks Track B** below the plan's original 35-40% estimate: the semantic
confluence fact Track B's canonical-model construction needs is now proved (`fs_sound''`,
sorry-free, axiom-clean). The syntactic gap (`CS5 ⊢ FS` unresolved) does **not** block Track B,
since Simpson's Ch.3 route uses `FS`'s semantic content (F2) directly, not `CS5 ⊢ FS` as a
Hilbert lemma. A3 (paper GO/NO-GO) is the correct next dispatch: verify (i) `cs5FC''` +
`fs_sound''` genuinely coincide with `IS5`'s birelational semantics as Simpson states it, and
(ii) whether the syntactic gap found here blocks any step of Pacheco's `CKB≡IKB ⟹ CS5≡IS5`
corollary chain that Track B (B1/B2) would need.

## Plan Deviations

- A2's success criterion ("EITHER sorry-free `CS5 ⊢ FS`, OR a precisely documented failure") is
  met in an unanticipated *third* way: neither a full proof nor a dead-end, but a **precisely
  diagnosed obstruction plus a decisive, reusable semantic corollary** (`fs_sound''`). This is
  reported as `[COMPLETED]` per the plan's explicit "both outcomes decisive" language, with the
  nuance recorded in the plan file's A2 entry and here rather than silently rounded to either
  extreme.
- No `Cslib/` files were modified. Both landed artifacts are `probes/`-scoped, honoring the plan's
  instruction ("Land the attempt ... in `probes/`") and the zero-debt invariant (no `sorry`, no
  new axiom, no vacuous definition anywhere under `Cslib/`).
- No new labelled-context construct was introduced (`Context.lean`, `Deduction.lean`,
  `Syntax.lean` untouched), so the four guardrail lemmas
  (`cs5_symmetric_tail_box_gap`/`cs5Incest_forces_symm`/`cs5TwoSidedR_iff_cs5Tail`/atom-sum) are
  not implicated by this dispatch's changes.

## Verification

- `lake env lean specs/517_.../probes/lemma612-scaffold.lean` — exit 0, sorry-free (grep-confirmed).
- `lake env lean specs/517_.../probes/fischer-servi-probe.lean` — exit 0, sorry-free (grep-confirmed).
- `#print axioms Cslib.Logic.Modal.fs_sound''` — no axioms.
- `#print axioms Cslib.Logic.Modal.fs_context_relative_half` — `[propext, Classical.choice]`,
  cross-checked identical to `cs5_dia_bot_imp_bot`/`cs5_dia_or` (existing landed CS5 facts) —
  not a new axiom footprint.
- No `Cslib/` file touched; landed CK/CT/CS4/CS5 soundness and task-509 `cs5FC''` are untouched
  by construction (grep-confirmed no diff outside `probes/` and `specs/517_.../plans`).

## Artifacts

- `specs/517_labelled_bounded_context_cs5_completeness/probes/lemma612-scaffold.lean` (edited, A1)
- `specs/517_labelled_bounded_context_cs5_completeness/probes/fischer-servi-probe.lean` (new, A2)
- `specs/517_labelled_bounded_context_cs5_completeness/plans/02_decomposed-track-a-b-c.md` (updated)
- `specs/517_labelled_bounded_context_cs5_completeness/summaries/02_track-a-a1-a2-summary.md` (this file)
