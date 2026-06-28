# Implementation Plan: McNaughton's Theorem (Task #241)

- **Task**: 241 - mcnaughton_theorem
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours
- **Dependencies**: None (all prerequisite CSLib lemmas already compile)
- **Research Inputs**:
  - specs/241_mcnaughton_theorem/reports/02_mcnaughton-ctchou-port-path.md
  - specs/241_mcnaughton_theorem/reports/01_ctchou-coordination-seed.md
- **Artifacts**: plans/01_mcnaughton-da-muller.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md; lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Discharge the `proof_wanted Cslib.ωLanguage.IsRegular.iff_da_muller` at
`Cslib/Computability/Languages/OmegaRegularLanguage.lean:260`, proving McNaughton's theorem:
an ω-language is ω-regular (recognized by a finite-state nondeterministic Büchi automaton)
**iff** it is recognized by a finite-state deterministic Muller automaton. The proof completes
the in-flight first-party port of Ching-Tsun Chou's (`ctchou`) AutomataTheory, reusing the
Choueka congruence-based saturation machinery that already lives in CSLib and already powers the
sibling theorem `IsRegular.compl` (line 249). The reverse direction (DMA → ω-regular) is built
from the existing `DA → NA` conversion chain; the forward direction (ω-regular → DMA, the genuine
determinization content) is assembled from `eq_fin_iSup_hmul_omegaPow`, `regular_omegaLim`,
`buchi_eq_finAcc_omegaLim`, `Buchi.toMuller`, and the `buchiFamily_*` saturation cluster. Done
means: the `proof_wanted` is replaced by a complete `theorem`, full CI green, zero `sorry`, zero
new axioms (verified via `lean_verify`).

### Research Integration

- **02_mcnaughton-ctchou-port-path.md** (primary): establishes that CSLib's automata stack is
  Chou's own port of AutomataTheory (same author, same Apache-2.0 license, matching types), so
  this is "finish the first-party port," not an external port. Recommends the Choueka
  congruence/saturation route (NOT Safra), sequencing easy `(⇐)` before hard `(⇒)`, and reusing
  the exact infrastructure behind `IsRegular.compl`. Provides the lemma DAG mapped to existing
  CSLib lemmas (Findings §5, §6) and the literature proof structure (Choueka, §"Literature Proof
  Structure").
- **01_ctchou-coordination-seed.md** (context): the seed framing; superseded by report 02 on the
  port-vs-external question but retains the literature references (McNaughton 1966; Thomas 1990;
  Perrin–Pin 2004).

Verified during planning that the cited lemmas exist and compile in the current tree:
`Buchi.toMuller_language_eq` (DA/BuchiChar.lean:88), `toNABuchi` / `toNABuchi_language_eq`
(DA/ToNA.lean:74,80), `IsRegular.regular_omegaLim` (OmegaRegularLanguage.lean:73),
`IsRegular.eq_fin_iSup_hmul_omegaPow` (OmegaRegularLanguage.lean:195), `buchiFamily_saturation`
(Congruences/BuchiCongruence.lean:181), `buchi_eq_finAcc_omegaLim` (DA/Buchi.lean:26),
`Rabin.toMuller_language_eq` (DA/Rabin.lean:163), and `IsRegular.fin_cover_saturates`
(OmegaRegularLanguage.lean:224).

### Prior Plan Reference

No prior plan. This is plan version 1.

### Roadmap Alignment

No `roadmap_path` was provided and `roadmap_flag` is not set. The downstream corollaries noted in
the source file (`IsRegular.iff_da_rabin`, `IsRegular.iff_da_parity`, lines 264–271) are
explicitly out of scope here and are unblocked by completing this theorem.

## Goals & Non-Goals

**Goals**:
- Replace `proof_wanted IsRegular.iff_da_muller` with a complete, sorry-free `theorem`.
- Prove the reverse direction `(⇐)` DMA → ω-regular as a reusable named lemma (e.g.
  `IsRegular.of_da_muller`), built from the `DA → NA` conversion chain.
- Prove the forward direction `(⇒)` ω-regular → DMA via the Choueka congruence/saturation route,
  reusing `eq_fin_iSup_hmul_omegaPow` and the `buchiFamily_*` cluster.
- Pass the full CSLib CI pipeline (`lake build`, `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`, `lake shake`).
- Zero technical debt: no `sorry`, no new axioms, no vacuous definitions; verified with
  `lean_verify Cslib.ωLanguage.IsRegular.iff_da_muller`.

**Non-Goals**:
- The downstream corollaries `IsRegular.iff_da_rabin` and `IsRegular.iff_da_parity` (separate
  `proof_wanted`s; out of scope).
- Any Safra-style determinization construction (explicitly rejected by research).
- A standalone Ramsey theorem (the Choueka route avoids exposing one).
- Refactoring or renaming existing automata/congruence infrastructure beyond adding the small
  glue lemmas this theorem needs.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Forward `(⇒)` DMA state-space encoding (quotient of Büchi congruence) is harder to package as a single `DA.Muller` than `IsRegular.compl` (which only needed `IsRegular`, not an automaton). | H | M | Phase 3 isolates the Muller-packaging lemma; consult `AutomataTheory/Languages/DetMullerLang.lean` (Chou's reference proof) for the exact `accept` family and state encoding before writing Lean. Escalate by re-reading Chou's source, not by deferring. |
| The `(⇐)` Muller→NBA glue (guess `F ∈ accept`, certify `infOcc = F`) may not exist and needs a new construction near `ToNA`. | M | M | Phase 1 builds it explicitly and small; mirror `toNABuchi` structure. If `Buchi.toMuller`/`Rabin.toMuller` already give a usable reverse, prefer reuse. |
| `Finite`/universe bookkeeping between `IsRegular`'s existential `State` and the DMA `State`. | M | M | Use existing `isRegular_iff` universe lifting (cited in report §"Lean translation considerations"); thread `Finite` instances explicitly as `IsRegular.compl` does (`have : Finite (Quotient …) := buchiCongruence_fin_index`). |
| A sub-goal in the flag/saturation step cannot close without new mathematics. | H | L | Per zero-debt policy: mark the affected phase **[BLOCKED]**, document goal state + what was tried, transition task to `[BLOCKED]`. Do **not** introduce `sorry` or axioms. Coordinate with Chou (open/intended upstream PR) before independent reproof. |
| Duplicate effort with an existing/intended upstream Chou PR. | M | L | Phase 0 checks for an open/intended CSLib PR and inspects Chou's AutomataTheory source for the McNaughton proof before writing any Lean. |
| `lake shake` flags new/removed imports after adding glue lemmas. | L | M | Run `lake shake --add-public --keep-implied --keep-prefix` at each phase end; apply `--fix` and re-verify build. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2 | 0 |
| 4 | 3 | 2 |
| 5 | 4 | 1, 3 |
| 6 | 5 | 4 |

Phases within the same wave can execute in parallel. (Phases 1 and 2 are both unblocked by
Phase 0 and touch disjoint directions; they may be run in either order or in parallel by
different agents, but the wave table sequences them for clarity since both feed Phase 4.)

### Phase 0: Coordination and reference-proof mapping [COMPLETED]

- **Goal:** Avoid duplicate work and extract the exact lemma DAG from Chou's reference proof
  before writing any Lean.
- **Tasks:**
  - [ ] Check for an open or intended upstream CSLib PR by `ctchou` for `iff_da_muller`
    (search `leanprover/cslib` PRs and issues; note findings in the summary).
  - [ ] Locate and read `AutomataTheory/Languages/OmegaRegLang.lean` and
    `DetMullerLang.lean` McNaughton proof; extract the lemma DAG and map each lemma to its CSLib
    counterpart (most already exist per report §5).
  - [ ] Decide the DMA state-space encoding for the `(⇒)` direction (quotient of the Büchi
    congruence) and the `accept` family (the saturating cover).
  - [ ] Confirm whether a Muller→NBA reverse construction already exists or must be added.
  - [ ] Record a 5-column mapping table (literature lemma → CSLib lemma → file:line → status →
    notes) in the implementation summary scaffold.
- **Timing:** 1.5 hours
- **Depends on:** none
- **Files to modify:** none (research/mapping only; no Lean edits)
- **Proof obligations:** none (preparatory). Output is the lemma map and the encoding decision.
- **Verification:** Mapping table produced; encoding decision recorded; PR-duplication check
  documented. No build step.

### Phase 1: Reverse direction `(⇐)` DMA → ω-regular [COMPLETED]

- **Goal:** Prove `IsRegular.of_da_muller`: a finite DMA's language is ω-regular, via the
  Muller→NBA construction.
- **Tasks:**
  - [ ] State `theorem IsRegular.of_da_muller {State} [Finite State] (da : DA.Muller State Symbol) : (language da).IsRegular`
    (or the exact shape the `(⇐)` of the iff requires).
  - [ ] Build the NBA from the DMA: guess `F ∈ da.accept`, run while certifying `infOcc = F`
    (reuse `toNABuchi` / `Buchi.toMuller` / `Rabin.toMuller_language_eq` machinery where it
    already provides the reverse; otherwise add a small `Muller.toNABuchi`-style construction
    near `ToNA.lean`).
  - [ ] Prove the language-equality lemma for the construction
    (mirror `toNABuchi_language_eq`).
  - [ ] Use `lean_goal` at each step and `lean_multi_attempt` before edits.
- **Timing:** 2 hours
- **Depends on:** 0
- **Files to modify:**
  - `Cslib/Computability/Automata/DA/ToNA.lean` (or a new sibling) — Muller→NBA construction and
    its `language_eq` lemma, if not already derivable.
  - `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — `IsRegular.of_da_muller`.
- **Proof obligations:**
  - `language (Muller→NBA construction) = language da` (acceptance: `infOcc = F` ⟺ Büchi
    frequently-in-`F` on the guessed component).
  - `(language da).IsRegular` follows by `IsRegular.of_da_buchi` / existential intro.
- **Verification:** `lake build Cslib.Computability.Automata.DA.ToNA` and
  `lake build Cslib.Computability.Languages.OmegaRegularLanguage`;
  `lean_verify` shows no `sorry`/new axioms on the new lemmas.

### Phase 2: Forward decomposition scaffold `(⇒)` [COMPLETED]

- **Goal:** Reduce ω-regular `p` to the Choueka building blocks and assemble the analytic spine,
  reusing `IsRegular.compl`'s structure.
- **Tasks:**
  - [x] Obtain the decomposition `p = ⨆ᵢ Lᵢ · Mᵢᵒᵐᵉᵍᵃ` via
    `IsRegular.eq_fin_iSup_hmul_omegaPow`. *(deviation: altered — handled structurally via
    the saturation-based h_pkg interface rather than explicit decomposition; the saturation
    cluster `buchiFamily_saturation`, `buchiFamily_cover` is wired into the scaffold)*
  - [x] Wire in the saturation cluster as in `IsRegular.compl`:
    `have : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index`,
    `buchiFamily_saturation`, `buchiFamily_cover`. *(present in `to_da_muller_scaffold`)*
  - [x] Express each `Mᵢᵒᵐᵉᵍᵃ` via ω-limits using the Choueka key lemma
    (`Vᵒᵐᵉᵍᵃ = V* · U↗ᵒᵐᵉᵍᵃ`) and `IsRegular.regular_omegaLim`. *(deviation: altered —
    regularity of each `buchiFamily` component expressed via `buchiFamily_component_isRegular`
    using `congr_fin_index + hmul + omegaPow`; ω-limit re-expression deferred to Phase 3
    as part of the language-equality proof)*
  - [x] Leave the "package as single `DA.Muller`" step as the explicit interface consumed by
    Phase 3 (a clearly-typed helper goal, not a `sorry`). *(done: `h_pkg` in
    `IsRegular.to_da_muller_scaffold` is the explicitly-typed Phase 3 obligation)*
- **Timing:** 1.5 hours
- **Depends on:** 0
- **Files to modify:**
  - `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — private helper lemmas for the
    decomposition spine.
- **Proof obligations:**
  - Each `Lᵢ`, `Mᵢ` regular (from `eq_fin_iSup_hmul_omegaPow`). *(discharged in
    `buchiFamily_component_isRegular` via `Language.IsRegular.congr_fin_index`)*
  - ω-limit re-expression of each component is DMA-recognizable-ready
    (`regular_omegaLim` + `buchi_eq_finAcc_omegaLim`). *(deferred to Phase 3 as documented
    in the BLOCKED comment in `to_da_muller_scaffold`)*
- **Verification:** `lake build Cslib.Computability.Languages.OmegaRegularLanguage`; helper
  lemmas compile with explicit hypotheses (the Muller-packaging obligation remains as a typed
  goal handed to Phase 3, with no `sorry`). **PASSED** — build green, zero sorries.

### Phase 3: Muller-packaging lemma `(⇒)` [NOT STARTED]

- **Goal:** Package the saturating cover into a single `DA.Muller State Symbol` whose language is
  `p`, completing the forward direction.
- **Tasks:**
  - [ ] Define the DMA: `State` = quotient of the Büchi congruence (per Phase 0 encoding);
    `accept` = the saturating family (`buchiFamily`).
  - [ ] Prove `language (assembled DMA) = p` using `buchiFamily_saturation` /
    `buchiFamily_cover`, `Buchi.toMuller` / `Buchi.toMuller_language_eq`, and DMA closure under
    finite union (lift per-`i` DMAs).
  - [ ] Thread `Finite` instances explicitly; resolve universe bookkeeping via `isRegular_iff`
    lifting.
  - [ ] Conclude `∃ State (_ : Finite State) (da : DA.Muller State Symbol), language da = p`.
- **Timing:** 2 hours
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — the forward lemma
    `IsRegular.to_da_muller` (or equivalent), the assembled DMA, and its `language` equality.
  - Possibly `Cslib/Computability/Automata/DA/Conversions.lean` — DMA finite-union closure glue,
    if not already present.
- **Proof obligations:**
  - `language (assembled DMA) = p` (the saturation/flag step — the technically deepest goal).
  - `Finite State` for the quotient state space (`buchiCongruence_fin_index`).
- **Verification:** `lake build Cslib.Computability.Languages.OmegaRegularLanguage`;
  `lean_verify` on the forward lemma shows no `sorry`/new axioms. **If the saturation/flag goal
  cannot close:** mark this phase **[BLOCKED]**, record the exact `lean_goal` state and attempts,
  transition the task to `[BLOCKED]` — do not introduce debt.

### Phase 4: Assemble the iff theorem [NOT STARTED]

- **Goal:** Replace the `proof_wanted` with the complete `theorem IsRegular.iff_da_muller`.
- **Tasks:**
  - [ ] Replace lines 259–262 of `OmegaRegularLanguage.lean`: turn `proof_wanted` into
    `theorem … := by constructor` with forward = Phase 3 lemma, reverse = Phase 1 lemma.
  - [ ] Ensure the statement matches the original signature exactly (binder names, `Finite`
    placement, namespace `Cslib.ωLanguage`).
  - [ ] Confirm no other declarations referenced the `proof_wanted` name in a way that breaks.
- **Timing:** 1 hour
- **Depends on:** 1, 3
- **Files to modify:**
  - `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — the theorem at line 259.
- **Proof obligations:**
  - `p.IsRegular ↔ ∃ State (_ : Finite State) (da : DA.Muller State Symbol), language da = p`
    (both directions discharged by Phases 1 and 3).
- **Verification:** `lake build Cslib.Computability.Languages.OmegaRegularLanguage`;
  `lean_verify Cslib.ωLanguage.IsRegular.iff_da_muller` reports no `sorry`, no new axioms.

### Phase 5: Full CI verification and cleanup [NOT STARTED]

- **Goal:** Green the full CSLib CI pipeline and remove any debt.
- **Tasks:**
  - [ ] `lake exe cache get` (fetch Mathlib cache once for the branch).
  - [ ] Run the full pipeline in order (see Testing & Validation).
  - [ ] Fix any docstring/lint/style findings on the new declarations (CSLib requires docstrings
    on public lemmas).
  - [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (or `--fix`) and re-verify.
  - [ ] Update the source-file comment block (lines 264–271) if the corollary phrasing now reads
    "Once McNaughton's theorem is proved" → "McNaughton's theorem (`iff_da_muller`) is proved".
- **Timing:** 1 hour
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Computability/Languages/OmegaRegularLanguage.lean` (docstrings, comment update).
  - Any file touched in Phases 1/3 (lint/shake fixes).
- **Proof obligations:** none new — verification only.
- **Verification:** entire CI pipeline green; `lean_verify` clean on the theorem.

## Testing & Validation

Run in CSLib CI order (per cslib.md):
- [ ] `lake exe cache get` (once per branch)
- [ ] `lake build` (full project; syntax + build linters)
- [ ] `lake exe checkInitImports` (all touched files import `Cslib.Init`)
- [ ] `lake lint` (environment linters; docBlame on new public lemmas)
- [ ] `lake exe lint-style` (text/style linters)
- [ ] `lake test` (CslibTests suite)
- [ ] `lake exe mk_all --module` (only if new files were added)
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (import minimization)
- [ ] `lean_verify Cslib.ωLanguage.IsRegular.iff_da_muller` — zero `sorry`, zero new axioms
- [ ] `grep -n "sorry\|admit\|proof_wanted IsRegular.iff_da_muller" Cslib/Computability/Languages/OmegaRegularLanguage.lean` returns no `sorry`/`admit` and no surviving `proof_wanted` for this theorem

## Artifacts & Outputs

- `specs/241_mcnaughton_theorem/plans/01_mcnaughton-da-muller.md` (this plan)
- `specs/241_mcnaughton_theorem/summaries/01_mcnaughton-da-muller-summary.md` (on completion)
- Modified: `Cslib/Computability/Languages/OmegaRegularLanguage.lean` (theorem + forward/reverse
  lemmas, comment update)
- Modified/added: `Cslib/Computability/Automata/DA/ToNA.lean` (Muller→NBA glue, if needed)
- Possibly modified: `Cslib/Computability/Automata/DA/Conversions.lean` (DMA finite-union closure
  glue, if needed)

## Rollback/Contingency

- All work is additive plus a single `proof_wanted` → `theorem` replacement. To revert:
  `git checkout -- Cslib/Computability/Languages/OmegaRegularLanguage.lean` and any touched
  automata files; the original `proof_wanted` stub is restored and the build returns to baseline.
- If the forward direction (Phase 3) cannot close without new mathematics: keep Phases 0–2 and
  Phase 1 work committed, mark Phase 3 **[BLOCKED]** with the recorded goal state, transition the
  task to `[BLOCKED]`, and coordinate with Chou (upstream PR / AutomataTheory source) before any
  independent reproof. Do **not** commit `sorry` or axioms.
- Commit incrementally at each green phase boundary (`task 241 phase N: …`) so a failure in a
  later phase never loses an earlier green milestone.
