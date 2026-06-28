# Implementation Plan: Task #342 — Burgess -> Pnueli Convention Cleanup (Temporal)

- **Task**: 342 - Temporal Burgess -> Pnueli convention (re-scoped cleanup)
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: None (task 234 already completed the executable migration)
- **Research Inputs**: specs/342_temporal_burgess_to_pnueli_convention/reports/01_burgess-to-pnueli-convention.md
- **Artifacts**: plans/01_burgess-to-pnueli-cleanup.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean
- **Lean Intent**: true

## Overview

The literal task premise ("swap `untl`/`snce` argument order from Burgess to Pnueli across
Syntax/Semantics/Axioms/Metalogic/Embedding") is STALE. Research and the orchestrator handoff
confirm that task 234 already completed the executable migration: `Temporal.Formula.untl`/`snce`
already use the Pnueli order (`untl guard event`), already agree with `Cslib/Logics/LTL`, and the
entire Temporal + LTL tree already builds green and sorry-free. The codebase states this itself in
`Tableau/Defs.lean:205` ("In the Lean inductive, `untl a b` stores guard=a, event=b").

This plan therefore executes the user-confirmed RE-SCOPED CLEANUP only: (1) rewrite the stale
"Burgess (event, guard)" convention docstrings/comments across ~10 files to the Pnueli convention;
(2) rewrite the 22 BX axiom doc-comment surface `U(...)`/`S(...)` notations to guard-first Pnueli
(no constructor signatures change); (3) redefine `reflexiveUntl`/`reflexiveSnce` in Pnueli order
and remove the now-unnecessary argument swap in `LTL.Formula.toTemporal` (which has zero downstream
consumers). The executable semantics layer (`Satisfies`, `someFuture`, `Axiom` constructors, all
Metalogic proofs) is left UNCHANGED. Definition of done: `lake build` green and sorry-free across
the Temporal + LTL tree, plus the CSLib CI pipeline.

### Research Integration

Key findings integrated from `reports/01_burgess-to-pnueli-convention.md`:
- The executable layer is already Pnueli (verified via `Satisfies.lean:61-66`,
  `Formula.lean:137-138` `someFuture = untl top phi`, `Soundness.lean:263-267` `until_F`).
- Genuine residue is doc-only across ~10 files, the 22 BX axiom doc comments, and two derived
  abbrevs plus one embedding clause.
- `reflexiveUntl`/`reflexiveSnce` (`Syntax/Formula.lean:279-289`) are unverified bridge abbrevs
  (no semantic correctness theorem); their bodies are redefined deliberately in Pnueli order.
- `LTL.Formula.toTemporal` (`LTL/Embedding.lean:50`) has zero downstream consumers, so the swap
  removal is purely structural and can only break by failing to build.
- DO-NOT-TOUCH: `BurgessR3Maximal`, `burgessR`, `burgessRSince`, `burgessRSet`, the BX system
  name, and all "Burgess 1982 / Claim 2.11 / Lemma 2.x" references name the completeness
  construction author, not the argument-order convention.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path`/`roadmap_flag` provided). The research
flagged one forward-looking item (out of scope here): `reflexiveUntl`/`toTemporal` lack a semantic
correctness theorem; a future task could add one to lock the LTL -> Temporal embedding meaning.

## Goals & Non-Goals

**Goals**:
- Align all "Burgess (event, guard)" convention docstrings/comments with the actual Pnueli
  (guard, event) code, across the ~10 affected files.
- Rewrite the 22 BX axiom doc-comment surface `U(...)`/`S(...)` notations to guard-first Pnueli,
  matching the (unchanged) Lean terms.
- Redefine `reflexiveUntl`/`reflexiveSnce` in Pnueli (guard, event) order with a precise one-line
  semantic docstring, and remove the argument swap in `LTL.Formula.toTemporal`, updating Embedding
  docstrings accordingly.
- Keep the whole Temporal + LTL tree building green and sorry-free; pass the CSLib CI pipeline.

**Non-Goals**:
- DO NOT swap `untl`/`snce` arguments in `Satisfies`, `someFuture`, the `Axiom` constructors, or
  any Metalogic proof — that would reverse a correct codebase. Executable semantics unchanged.
- DO NOT change the Tableau `asUntl?`/`asSnce?` external `(event, guard)` adapters or their
  consumers in `Tableau/Rules.lean` / `Tableau/Saturation.lean` (out of scope; at most a
  clarifying header comment, no code change).
- DO NOT rename `BurgessR3Maximal`/`burgessR`/`burgessRSince` or any "Burgess 1982 / Claim 2.11 /
  Lemma 2.x" references, nor the Burgess-Xu (BX) system name.
- DO NOT add a new `Satisfies` correctness lemma for `reflexiveUntl` (deferred; see roadmap note).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer takes the literal task and swaps executable args, reversing a correct codebase | H | M | This plan's Non-Goals and every phase state "docs/bridge only; executable layer unchanged"; verification gate (sorry-free + LTL agreement) catches a reversal |
| Editing a `Burgess*` completeness identifier or a "Burgess 1982" reference by mistake | H | M | Phase tasks restrict edits to convention prose only; grep for `Burgess` and triage author-references vs convention-prose before editing; DO-NOT-TOUCH list enforced |
| `reflexiveUntl`/`reflexiveSnce` redefinition changes embedding meaning silently (no correctness theorem to catch it) | M | M | Redefine deliberately to mirror LTL Pnueli order; verify `LTL.Embedding` still builds; document the intended semantics in the docstring; full-tree build acts as structural check |
| Doc/bridge edits in `Formula.lean` and `Embedding.lean` collide between phases | L | M | Sequence the bridge phase (3) after the docstring phase (1) so each file is touched once per wave |
| Tableau adapter comment clarification mistaken for adapter code change | L | L | Restrict Tableau edits to header comment text only; adapter bodies and `@[simp]` lemmas untouched |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Rewrite convention docstrings/comments (no code change) [COMPLETED]

**Goal**: Replace every stale "Burgess (event, guard)" convention docstring/comment with the
correct Pnueli (guard, event) description, so prose matches the unchanged code. No Lean terms
change in this phase.

**Tasks**:
- [ ] `Cslib/Logics/Temporal/Syntax/Formula.lean`: rewrite module doc lines ~49-75 (esp. 51, 55,
      57, 60-75) and per-def convention notes (~135, 145, 195, 208, 210, 220, 222, 226, 228, 262,
      267, 302, 308, 322, 327) to Pnueli (guard, event). Do NOT edit `reflexiveUntl`/`reflexiveSnce`
      here (Phase 3).
- [ ] `Cslib/Logics/Temporal/Semantics/Satisfies.lean`: rewrite module doc header (~16-29,
      "Burgess Convention (Event, Guard)") and the inline `(phi=EVENT, psi=GUARD)` notes (~53-55).
      Leave `untl_iff`/`snce_iff` bodies unchanged (already correct).
- [ ] `Cslib/Logics/Temporal/Syntax/Subformulas.lean`: fix the trailing `[... in Burgess]` notes
      at ~79, 89 (the `change` terms are correct Pnueli; only the comments mislead).
- [ ] `Cslib/Logics/LTL/Syntax/Formula.lean`: rewrite ~62, 64 (claims Temporal is Burgess — now
      false); state that Temporal and LTL agree on Pnueli (guard, event).
- [ ] `Cslib/Logics/Temporal/Tableau/Rules.lean`: fix convention comment at ~34.
- [ ] `Cslib/Logics/Temporal/Tableau/Defs.lean`: clarify the header comment (~37-39) to state
      "internal representation is Pnueli `untl guard event`; this module's `asUntl?`/`asSnce?`
      decomposition adapters expose `(event, guard)` tuples locally." COMMENT TEXT ONLY — do not
      touch `asUntl?`/`asSnce?` bodies or `@[simp]` lemmas.
- [ ] Update the cross-references between the two logics' "Convention Note" sections so each states
      they agree on Pnueli (guard, event).
- [ ] Run `grep -n "Burgess" Cslib/Logics/Temporal Cslib/Logics/LTL -r` and triage each hit:
      convention-prose -> rewrite; author/lemma reference (Burgess 1982, BurgessR*, BX) -> LEAVE.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - docstrings/comments only
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` - docstrings/comments only
- `Cslib/Logics/Temporal/Syntax/Subformulas.lean` - comments only
- `Cslib/Logics/LTL/Syntax/Formula.lean` - comments only
- `Cslib/Logics/Temporal/Tableau/Rules.lean` - comment only
- `Cslib/Logics/Temporal/Tableau/Defs.lean` - header comment only

**Verification**:
- Scoped `lake build` of the touched modules exits 0 (doc edits cannot change semantics).
- `grep "event, guard\|Event, Guard\|(event,guard)"` over the edited files returns only the
  intentional Tableau adapter clarification (no stray Burgess convention claims).
- No `Burgess*` completeness identifier or "Burgess 1982 / Claim 2.x / Lemma 2.x" reference altered.

---

### Phase 2: Rewrite the 22 BX axiom doc comments to Pnueli [COMPLETED]

**Goal**: Rewrite the surface `U(...)`/`S(...)` notation inside the 22 temporal BX axiom
`/-- ... -/` doc strings in `ProofSystem/Axioms.lean` to guard-first Pnueli, so each doc matches
the (unchanged) Lean term it annotates. No constructor signatures change.

**Tasks**:
- [ ] For each temporal axiom constructor, read the Lean term and rewrite the doc `U(event,guard)`
      / `S(...)` notation to guard-first Pnueli. Confirmed examples from research:
      - `until_F` (~182-184): doc `U(psi, phi) -> F(psi)`; term `(untl phi psi).imp (someFuture psi)`
        -> Pnueli doc `U(phi, psi) -> F(psi)`.
      - `F_until_equiv` (~206-208): doc `F(phi) -> U(phi, top)`; term `untl top phi` -> `U(top, phi)`.
- [ ] Rewrite the remaining surface notations: `left_mono_until_G`, `right_mono_until`,
      `enrichment_*`, `self_accum_*`, `absorb_*`, `linear_*`, `since_*`, and the other temporal BX
      axioms, matching each `/-- -/` to its `untl phi psi` (guard-first) / `snce` term.
- [ ] Cross-check each rewritten doc against the actual constructor term (do not infer from the old
      doc); the Lean term is authoritative.
- [ ] Leave the `Burgess-Xu (BX)` system name and any Burgess-1982 references in this file UNCHANGED.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - doc comments only (no constructor signatures)

**Verification**:
- `lake build Cslib.Logics.Temporal.ProofSystem.Axioms` (and dependents `Soundness`) exits 0.
- Constructor signatures byte-identical except for `/-- -/` content (diff shows only comment lines).
- No `Axiom` term or constructor argument order changed.

---

### Phase 3: Bridge — redefine reflexiveUntl/reflexiveSnce + remove toTemporal swap [COMPLETED]

**Goal**: Redefine `reflexiveUntl`/`reflexiveSnce` in Pnueli (guard, event) order with a precise
semantic docstring, and remove the now-unnecessary argument swap in `LTL.Formula.toTemporal`,
updating the Embedding docstrings. `toTemporal` has zero downstream consumers, so this is
structural-only and validated by the build.

**Tasks**:
- [ ] `Cslib/Logics/Temporal/Syntax/Formula.lean` (~279-289): redefine `reflexiveUntl` and
      `reflexiveSnce` so their arguments follow Pnueli (guard, event) order, consistent with the
      inner `untl`/`snce` and with LTL's reading. Replace the (event, guard) docstrings with a
      one-line Pnueli semantic spec.
- [ ] `Cslib/Logics/LTL/Embedding.lean` (~50): change
      `| .untl phi1 phi2 => (toTemporal phi2).reflexiveUntl (toTemporal phi1)` to the
      no-swap Pnueli form `(toTemporal phi1).reflexiveUntl (toTemporal phi2)` (and the
      corresponding `snce` clause), so LTL's `(guard, event)` maps straight through.
- [ ] `Cslib/Logics/LTL/Embedding.lean`: update module docstrings (~12-33, 39-44) describing the
      old swap to reflect the no-swap Pnueli mapping.
- [ ] Verify (via grep/build) that `LTL.Formula.toTemporal` has no downstream consumers beyond the
      embedding file itself (distinct from `PL.Proposition.toTemporal`), confirming safety.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - `reflexiveUntl`/`reflexiveSnce` defs + docstrings
- `Cslib/Logics/LTL/Embedding.lean` - `toTemporal` `untl`/`snce` clauses + module docstrings

**Verification**:
- `lake build Cslib.Logics.LTL.Embedding` and `Cslib.Logics.Temporal.Syntax.Formula` exit 0.
- `someFuture`/`anyFuture`/other abbrevs that consume `reflexiveUntl` (if any) still build.
- No executable change outside these two abbrevs and the embedding clauses.

---

### Phase 4: Full verification (build + sorry-free + CI) [COMPLETED]

**Goal**: Confirm the whole Temporal + LTL tree builds green and sorry-free after the cleanup, and
the CSLib CI pipeline passes.

**Tasks**:
- [ ] Run a full `lake build` of the project (or the Temporal + LTL + Tableau + LTL.ModelChecking
      module set verified at baseline in the research report §5/§7).
- [ ] Confirm zero `sorry`: `grep -rn "sorry" Cslib/Logics/Temporal Cslib/Logics/LTL` returns only
      the known prose mention in `LTL/Semantics/GNBA.lean:37` (not an actual `sorry`).
- [ ] Confirm zero new axioms introduced (no `axiom` declarations added).
- [ ] Run the CSLib CI pipeline: `lake exe lint-style`, `lake shake`, `lake lint` (advisory).
- [ ] Spot-check that Temporal and LTL still agree on Pnueli order (the executable layer is
      unchanged, so agreement is preserved by construction).

**Timing**: 0.75 hours

**Depends on**: 1, 2, 3

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` exits 0 across the Temporal + LTL tree.
- Sorry-free and no new axioms.
- CI pipeline (`lint-style`, `shake`) green; `lint` advisory reviewed.

---

## Testing & Validation

- [ ] Full `lake build` of the Temporal + LTL + Tableau tree exits 0.
- [ ] Sorry-free across `Cslib/Logics/Temporal` and `Cslib/Logics/LTL` (only the GNBA prose mention).
- [ ] No new `axiom` declarations.
- [ ] `lake exe lint-style` and `lake shake` pass; `lake lint` advisory reviewed.
- [ ] Diff review confirms: no executable arg-order swaps in `Satisfies`/`someFuture`/`Axiom`
      constructors/Metalogic; no `Burgess*`/BX/Burgess-1982 identifier or reference renamed; Tableau
      adapter bodies unchanged.

## Artifacts & Outputs

- `specs/342_temporal_burgess_to_pnueli_convention/plans/01_burgess-to-pnueli-cleanup.md` (this file)
- Edited sources (docs + two abbrevs + embedding clauses):
  - `Cslib/Logics/Temporal/Syntax/Formula.lean`
  - `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
  - `Cslib/Logics/Temporal/Syntax/Subformulas.lean`
  - `Cslib/Logics/Temporal/ProofSystem/Axioms.lean`
  - `Cslib/Logics/Temporal/Tableau/Rules.lean`
  - `Cslib/Logics/Temporal/Tableau/Defs.lean` (header comment only)
  - `Cslib/Logics/LTL/Syntax/Formula.lean`
  - `Cslib/Logics/LTL/Embedding.lean`
- Implementation summary at `summaries/01_burgess-to-pnueli-cleanup-summary.md` (on completion).

## Rollback/Contingency

- All edits are doc-comments plus two abbrev redefinitions and two embedding clauses; revert via
  `git checkout -- <file>` per file, or `git revert` the phase commit. Baseline is green and
  sorry-free (research §5), so reverting any phase restores a buildable state.
- If the bridge redefinition (Phase 3) fails to build or appears to change embedding meaning,
  revert only `Formula.lean`/`Embedding.lean` changes and ship Phases 1-2 (pure doc alignment)
  independently; the doc phases carry no semantic risk.
- If any `Burgess*`/BX reference is touched by mistake, restore it immediately — these are
  out-of-scope per the DO-NOT-TOUCH list.
