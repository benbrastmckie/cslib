# McNaughton's Theorem: ctchou Port Path and Proof Strategy

## Metadata

- **Task**: 241 (mcnaughton_theorem)
- **Type**: cslib research
- **Date**: 2026-06-24
- **Session**: sess_1782337264_0e4361
- **Author**: cslib-research-agent
- **Supersedes/extends**: `reports/01_ctchou-coordination-seed.md`
- **Target**: `proof_wanted Cslib.ωLanguage.IsRegular.iff_da_muller`

## Summary

The seed report framed ctchou/AutomataTheory as an *external* project to evaluate for
porting. The decisive finding of this deepening pass overturns that framing:

**Ching-Tsun Chou (ctchou) is already a core CSLib contributor, and the entire CSLib
automata/ω-language stack that task 241 builds on is his own port of AutomataTheory.**

- `OmegaRegularLanguage.lean` (which holds the `IsRegular.iff_da_muller` `proof_wanted`)
  is `Copyright (c) 2025 Ching-Tsun Chou`, Apache 2.0.
- `DA/Buchi.lean`, `DA/Basic.lean`, `NA/Basic.lean`, and `Congruences/BuchiCongruence.lean`
  are all authored (or co-authored) by Chou. He has 20 commits to the automata/languages
  directories — the most of any contributor.
- The AutomataTheory README explicitly states: *"The results in this project are being
  ported to CSLib"* and lists "McNaughton's theorem" among results *being ported*
  (not yet underlined/landed).

Therefore the three classic options collapse: this is **not** "port vs. adapt vs. develop
independently from a third party." It is **finish the in-flight first-party port**, ideally
in coordination with Chou, using the proof he has already completed in AutomataTheory.

**Licensing is a non-issue**: both projects are Apache 2.0, same author, and CSLib files
already carry Chou's copyright. No translation layer or relicensing is required.

**Recommendation**: **Adapt/complete the first-party port** (Choueka congruence-based proof),
reusing CSLib's existing `BuchiCongruence` saturation infrastructure. Coordinate with Chou
before independent effort to avoid duplicate work, since his Lean proof of this exact theorem
already exists.

## Findings

### 1. Exact statement to be proved

`Cslib/Computability/Languages/OmegaRegularLanguage.lean:260`:

```lean
/-- McNaughton's Theorem. -/
proof_wanted IsRegular.iff_da_muller {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p
```

where (same file, line 36):

```lean
def IsRegular (p : ωLanguage Symbol) :=
  ∃ (State : Type) (_ : Finite State) (na : NA.Buchi State Symbol), language na = p
```

So the theorem is: **ω-regular (= recognized by a finite-state nondeterministic Büchi
automaton) ↔ recognized by a finite-state deterministic Muller automaton.**

### 2. Type definitions (CSLib) — fully present and matching the seed's questions

| Concept | CSLib definition | Location |
|---------|------------------|----------|
| ω-word | `ωSequence Symbol` (= `ℕ → Symbol`) | `Foundations.Data.OmegaSequence` |
| Base DA | `structure DA extends FLTS … (start : State)` | `DA/Basic.lean:37` |
| DBA | `structure Buchi extends DA (accept : Set State)`; accepts iff `∃ᶠ k, run xs k ∈ accept` | `DA/Basic.lean:91` |
| DMA | `structure Muller extends DA (accept : Set (Set State))`; accepts iff `(run xs).infOcc ∈ accept` | `DA/Basic.lean:106` |
| NBA | `NA.Buchi` (nondeterministic, `Set.Infinite`/`Frequently`-based acceptance) | `NA/Basic.lean`, `DA/Buchi.lean` |

The seed's open questions are answered: CSLib uses its **own** automata types (not Mathlib's
`DFA`/`NFA`), ω-words are `ℕ → α`, Büchi acceptance is `Frequently … atTop`, and Muller
acceptance is `infOcc ∈ accept` (set of states occurring infinitely often). These match
ctchou/AutomataTheory's representations because CSLib's are ported from it.

### 3. Which half of McNaughton is the hard one — and its status

McNaughton splits into two directions:

- **(⇐) DMA → ω-regular (EASY)**: A finite DMA is converted to an NBA. CSLib already has the
  full reverse acceptance-condition chain on the *deterministic* side
  (`Rabin.toMuller_language_eq`, `Buchi.toMuller_language_eq`, `DA → NA` via `ToNA.lean`'s
  `toNABuchi`). The remaining glue is a Muller→NBA construction (guess the accepting set
  `F`, verify `infOcc = F`). This direction is routine.

- **(⇒) ω-regular → DMA (HARD)**: This is the genuine determinization content of McNaughton.
  CSLib's `ToDA.lean` only provides the *subset* powerset construction (`toDA : NA → DA (Set
  State)`), which is **insufficient** for Büchi/Muller (proven by the `eventuallyZero`
  counterexample in `IsRegular.not_da_buchi`, line 61: there is an ω-regular language accepted
  by no DBA at all). So a real determinization (Safra-style, or the congruence/Ramsey route)
  is required.

**Key leverage**: CSLib *already* contains the hard analytic machinery for the congruence
route, because the **complementation theorem `IsRegular.compl` is already proved** (line 249)
using exactly this infrastructure:

- `BuchiCongruence` (`Congruences/BuchiCongruence.lean`, author Chou) with
  `buchiCongruence_fin_index` (finite index),
- `buchiFamily_saturation` / `buchiFamily_cover` (saturating finite cover),
- `IsRegular.fin_cover_saturates` / `…_compl` (saturation lemmas),
- `IsRegular.eq_fin_iSup_hmul_omegaPow` (every ω-regular language = finite ⨆ of `L · Mᵒᵐᵉᵍᵃ`).

This is the same Choueka/right-congruence saturation framework that the AutomataTheory README
says underlies its McNaughton proof ("for any regular language V, there exists U with
Vᵒᵐᵉᵍᵃ = V* · U↗ᵒᵐᵉᵍᵃ" — the `omegaPow`/`omegaLim` key lemma).

### 4. ctchou/AutomataTheory evaluation (the four seed dimensions, resolved)

| Dimension | Finding |
|-----------|---------|
| **Architecture** | Own automata types over `ℕ → Σ` words; congruence-based language theory. **Identical to CSLib** because CSLib is the port. No translation layer needed. |
| **Mathlib version** | README pins no Mathlib version. Irrelevant: the port target is CSLib (Lean `v4.31.0`, Mathlib rev `fabf563`), and the relevant pieces already compile there. |
| **Acceptance conditions** | Büchi = infinitely-often; Muller = `infOcc ∈ accept`. Already mirrored in CSLib `DA/Basic.lean`. |
| **Proof technique** | **Choueka congruence-based** (NOT Safra, NOT a separate Ramsey argument for this theorem). Flag construction for concatenation closure. The saturation half is already ported and proved in CSLib (`IsRegular.compl`). |
| **Licensing** | Apache 2.0 ↔ Apache 2.0, same author. **Zero licensing risk.** |

README "ported to CSLib" list confirms the *prerequisites* are already in CSLib (closure
properties, congruence saturation, `omegaLim`/`omegaPow` of regular languages as DMA,
DMA closure properties), while **"McNaughton's theorem" itself is listed as being ported
but not yet landed** — exactly matching the `proof_wanted` stub.

### 5. Relevant CSLib lemma candidates for the proof

For the **hard (⇒) direction**, the building blocks already in CSLib:

- `IsRegular.eq_fin_iSup_hmul_omegaPow` — decomposes any ω-regular `p` into `⨆ᵢ Lᵢ · Mᵢᵒᵐᵉᵍᵃ`.
- `IsRegular.regular_omegaLim` (`l↗ω` is ω-regular) and `IsRegular.of_da_buchi`.
- `Buchi.toMuller` / `Buchi.toMuller_language_eq` — DBA → DMA, same state space.
- `Rabin.toMuller_language_eq`, `Streett`/`Rabin` duality (for the DMA target packaging).
- The `BuchiCongruence` saturation cluster (`buchiCongruence_fin_index`,
  `buchiFamily_saturation`, `buchiFamily_cover`, `fin_cover_saturates`).
- `DA.buchi_eq_finAcc_omegaLim` (ties DBA acceptance to ω-limits).

For the **easy (⇐) direction**: `ToNA.lean` (`toNABuchi`, `toNABuchi_language_eq`) plus a
small Muller→NBA "guess the infOcc set" construction.

### 6. Mathlib API

Mathlib supplies the analytic substrate already used throughout these files (no new heavy
Mathlib lemmas anticipated):
- `Filter.Frequently … atTop`, `frequently_in_finite_type` (used in `Buchi.toMuller_language_eq`).
- `Set.Finite`, `Set.ncard`, `Quotient`, `Finite.equivFin`, `finProdFinEquiv`.
- `Mathlib.SetTheory.Cardinal.NatCard`, `Mathlib.Data.Finite.Sigma` (already imported).
- Ramsey-type infinite pigeonhole only if the determinization is done via the Büchi/Ramsey
  route; the Choueka congruence route avoids a standalone Ramsey theorem (CSLib's existing
  saturation proof did not need one exposed as a `proof_wanted`).

## Literature Proof Structure (Choueka, as used by ctchou)

Main claim: `p` ω-regular ↔ `p` = `language(DMA)`.

1. **(⇐)** Given finite DMA `a`: build NBA accepting `language a` (guess `F ∈ a.accept`,
   run while certifying `infOcc = F`). Conclude `IsRegular`.
2. **(⇒)** Given ω-regular `p`: by `eq_fin_iSup_hmul_omegaPow`, `p = ⨆ᵢ Lᵢ · Mᵢᵒᵐᵉᵍᵃ`
   with each `Lᵢ, Mᵢ` regular.
3. **Key lemma (Choueka)**: for regular `V`, ∃ regular `U` with `Vᵒᵐᵉᵍᵃ = V* · U↗ᵒᵐᵉᵍᵃ`.
   This re-expresses ω-powers via ω-limits (`↗ω`), which CSLib already knows are DMA-recognizable
   (`IsRegular.regular_omegaLim` + `buchi_eq_finAcc_omegaLim` + `Buchi.toMuller`).
4. **Saturation / right-congruence**: the finite-index Büchi congruence partitions ω-words so
   that the cover is `Muller`-definable; this is the same `buchiFamily_*` saturation already
   proved for `IsRegular.compl`.
5. **Flag construction**: Choueka's "flag" tracks which congruence class / accepting set the
   run settles into, giving the DMA acceptance family. Subtle but already discharged in
   AutomataTheory.
6. **Assemble**: DMA closure under finite union (`DetMullerLang` closure, ported) lifts the
   per-`i` DMAs to a single DMA for `p`.

**Lean translation considerations**: Steps 2–4 are largely *already in CSLib* as named lemmas;
the new work is (a) the `(⇐)` Muller→NBA glue, (b) packaging the saturating cover as a single
`DA.Muller` (state-space = quotient of the Büchi congruence, `accept` = the saturating family),
and (c) the universe/`Finite` bookkeeping (`isRegular_iff` already provides universe lifting).

## Tactic Survey Results

Not yet at a concrete goal state (no scaffold written), so no `lean_multi_attempt` runs were
performed. Anticipated tactic profile, by analogy with the proved `IsRegular.compl` / closure
lemmas in the same file: heavy use of `grind [..]` with the scoped automata grind lemmas,
`simp only` with the `mem_language` / `ωAcceptor.Accepts` unfoldings, `obtain`/`rfl`
destructuring of the `IsRegular` existential, and `Filter.Frequently` reasoning via
`frequently_in_finite_type`. No `omega`/`ring`/`linarith` expected. `decide` not applicable
(infinite state quantification).

## Recommendations

### Primary recommendation: Adapt / complete the first-party port (coordinate with Chou)

1. **Coordinate first.** Chou's AutomataTheory contains a *completed* Lean proof of this exact
   theorem. Before independent reproof, the planner/implementer should (a) inspect
   `AutomataTheory/Languages/OmegaRegLang.lean` and `DetMullerLang.lean` for the McNaughton
   statement and its dependency lemmas, and (b) check whether Chou has an open/intended CSLib
   PR for it. This is the largest effort-saving lever and avoids duplicate work.
2. **Reuse, do not reinvent.** The hard saturation machinery (`BuchiCongruence`,
   `buchiFamily_*`, `eq_fin_iSup_hmul_omegaPow`, `regular_omegaLim`) is already in CSLib and
   already powers `IsRegular.compl`. The proof should be assembled from these, mirroring the
   structure of `IsRegular.compl`.
3. **Sequence the directions.** Prove `(⇐)` (DMA → ω-regular) first — it is small and unblocks
   downstream corollaries — then tackle `(⇒)` via the Choueka route.
4. **Zero-debt.** A complete, sorry-free proof is feasible *precisely because* the analytic
   core already exists in CSLib and a reference proof exists in AutomataTheory. Do **not**
   introduce axioms or `sorry`. If the flag construction proves hard to transcribe, escalate
   by re-reading Chou's source rather than deferring.

### Secondary path (only if coordination stalls): independent congruence proof

If Chou's source cannot be consulted, reproduce the proof natively from
`eq_fin_iSup_hmul_omegaPow` + the saturation cluster + a Muller-packaging lemma. Effort is
**moderate-to-high** but bounded, since every prerequisite lemma already compiles in CSLib.

### Not recommended

- **Safra construction from scratch** — unnecessary; the congruence route is already wired up
  in CSLib and is the technique the reference proof uses.
- **Treating this as an external third-party port with relicensing/translation concerns** —
  factually wrong; same author, same license, same types.

### Effort / risk summary

| Path | Effort | Risk | Licensing |
|------|--------|------|-----------|
| Adapt/complete first-party port (recommended) | Low–Moderate | Low (reference proof exists) | None (Apache 2.0, same author) |
| Independent congruence reproof | Moderate–High | Moderate (flag construction subtlety) | None |
| Safra from scratch | High | High | None |

## Open Items for Planner

1. Locate and read `AutomataTheory/Languages/OmegaRegLang.lean` McNaughton proof to extract
   the exact lemma DAG and map each lemma to its CSLib counterpart (most already exist).
2. Decide the DMA state-space encoding for the `(⇒)` direction (quotient of Büchi congruence).
3. Confirm/create the `(⇐)` Muller→NBA construction (likely a few-line addition near `ToNA`).
4. Check for an existing or intended upstream PR by Chou to avoid duplication.
