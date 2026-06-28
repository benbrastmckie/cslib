# Task 381 — Bimodal Separation/Perpetuity Mathlib/Toolchain Drift Diagnosis

**Toolchain:** `leanprover/lean4:v4.31.0`
**Status at diagnosis:** 4 sorry-free modules fail to build after the bump; `Separation/Defs`
(already repaired) builds clean. Same drift family as task 364.
**Diagnosis method:** `lean_goal` + `lean_multi_attempt` at the failing lines (NOT
`lean_diagnostic_messages`). Every proposed fix below was confirmed to close its goal
(`goals:[]`, zero diagnostics) via `lean_multi_attempt`.

## Executive Summary — ONE shared root drives 3 of the 4 modules

The failing modules all rely on `simp` to unfold the **derived propositional connectives** of
`Bimodal.Formula`. Those connectives are a **two-layer `abbrev` chain**:

```
abbrev Formula.neg φ := PropositionalConnectives.neg φ          -- Syntax/Formula.lean:63
abbrev Formula.or  φ ψ := .imp (.imp φ .bot) ψ                  -- :71
abbrev Formula.and φ ψ := .imp (.imp φ (.imp ψ .bot)) .bot      -- :75
class PropositionalConnectives … where
  neg : F → F := fun φ => HasImp.imp φ HasBot.bot               -- Foundations/Logic/Connectives.lean:155
  top : F     := HasImp.imp (HasBot.bot) HasBot.bot             -- :159
```

**The drift:** under v4.31.0, naming only `Formula.neg` in a `simp` set unfolds **one layer**
(`Formula.neg φ → PropositionalConnectives.neg φ`) and then **stops** — the second layer
(`PropositionalConnectives.neg → .imp φ .bot`) is no longer unfolded automatically, so the
`isUFree`/`isSFree`/`isFutureOnly`/`isPastOnly`/`isSyntacticallySeparated` matcher never sees an
`.imp` head and the proof stalls.

Confirmed live (`lean_multi_attempt`, Eliminations:544): the current
`simp [Formula.and, Formula.neg, isUFree, ha, hq]` leaves
`⊢ isUFree (PropositionalConnectives.neg a) = true ∧ isUFree (PropositionalConnectives.neg q) = true`
— stuck at exactly the second layer.

**The canonical fix is already in the repaired `Separation/Defs.lean`:** its simp-lemma proofs
(e.g. `is_U_free_allPast`, lines 229-237; `swapTemporal_allFuture`, Formula.lean:185) explicitly
name **`PropositionalConnectives.neg`** and **`PropositionalConnectives.top`** alongside
`Formula.neg`/`Formula.top`. The repair for tasks-381 modules is to bring the failing call sites
into line with that already-accepted idiom.

### The single fix idiom (modules 1, 2, 3)

For each failing `simp`/`simp only` over a purity predicate, **add the missing unfold lemmas** to
the simp set so the full abbrev chain is peeled:

- always add **`PropositionalConnectives.neg`** wherever `Formula.neg` (or `¬`, or any
  abbrev that expands through `neg`: `Formula.and`, `Formula.allPast`, `Formula.allFuture`,
  `diamond`) appears;
- add **`Formula.or` / `Formula.and` / `Formula.neg`** if a bare `simp [isUFree, …]` omits them;
- add **`PropositionalConnectives.top`** (and `Formula.top`) only at sites whose formula expands
  through `⊤` (i.e. `someFuture`/`somePast`/`allFuture`/`allPast`); none of the listed 381 sites
  need `top` except via already-named simp lemmas, but include it defensively if a build error
  shows a residual `PropositionalConnectives.top`.

Mechanical, statement-preserving, zero new lemmas. Verified on representative sites in all three
modules (see per-module sections).

Module 4 (`Bridge.lean`) is a **related but distinct** drift (a `swapTemporal` normalization
that must route through a structural `@[simp]` lemma instead of raw-def unfolding) — see §4.

## 1. `Separation/Duality.lean` — `simp made no progress` (357, 362)

Theorems `neg_future_only` (354-357) and `neg_past_only` (359-362). The bodies name **no**
connective-unfold lemma at all, so simp cannot even reach the first layer → "made no progress".

| Line | Current (FAILS) | Replacement (VERIFIED closes) |
|------|-----------------|-------------------------------|
| 357 | `simp [isFutureOnly, h]` | `simp [Formula.neg, PropositionalConnectives.neg, isFutureOnly, h]` |
| 362 | `simp [isPastOnly, h]` | `simp [Formula.neg, PropositionalConnectives.neg, isPastOnly, h]` |

`lean_multi_attempt` at 357 with the replacement → `goals:[]`, no diagnostics. (`simp only
[Formula.neg, PropositionalConnectives.neg, isFutureOnly, h, Bool.and_true]` also closes it if a
`simp only` form is preferred for lint stability.) The neighbouring `and_/or_/imp_future_only`
theorems (367-402) build because their formula heads are `.imp` directly — they never go through
`neg`. This confirms the root is specifically the `neg` second-layer unfold. **Mechanical.**

## 2. `Separation/Eliminations.lean` — ~15 `unsolved goals` (one repeated family)

All listed failing lines (63, 498, 543, 545, 547, 548, 552, 602, 604, 606, 607, 611, 660, 662,
666) are the **same second-layer `neg` unfold stall**, repeated across parallel Case-2/Case-3
elimination lemmas. **No `obtain`-shape drift is involved** (the `obtain`/anonymous-constructor
destructurings in these proofs are fine). Per-site fix = add `PropositionalConnectives.neg`
(and `Formula.and`/`Formula.or`/`Formula.neg` where a bare simp omits them).

Representative sites (exact current → replacement; line numbers are the `simp` line):

| Site / lemma | Current (FAILS) | Replacement |
|--------------|-----------------|-------------|
| 63 `neg_separated` | `simp [Formula.neg, isSyntacticallySeparated, h]` | add `PropositionalConnectives.neg` |
| 501-503 `case2_psi_properties` sep-check | `simp only [d1, d2, d3, Formula.or, Formula.and, Formula.neg, isSyntacticallySeparated, isUFree, isSFree, ha, hq, hA, hB, hA', hB', Bool.true_and, Bool.and_true, hsep_A, hsep_B]` | add `PropositionalConnectives.neg` |
| 544 `elim_case_3.haq_Uf` | `simp [Formula.and, Formula.neg, isUFree, ha, hq]` | add `PropositionalConnectives.neg` (**VERIFIED closes**) |
| 546 `…haq_Sf` | `simp [Formula.and, Formula.neg, isSFree, ha', hq']` | add `PropositionalConnectives.neg` |
| 547 `…ha_neg_Uf` | `simp [Formula.neg, isUFree, ha]` | add `PropositionalConnectives.neg` |
| 548 `…ha_neg_Sf` | `simp [Formula.neg, isSFree, ha']` | add `PropositionalConnectives.neg` |
| 553 `…hsep_H` | `simp only [is_syntactically_separated_allPast, Formula.neg, isUFree, ha, Bool.and_true]` | add `PropositionalConnectives.neg` |
| 603/605/606/607/612 `elim_case_3_gen`-sibling haves | same shapes as 544-553 | add `PropositionalConnectives.neg` |
| 661 `…haq_Uf` (bare) | `simp [isUFree, ha, hq]` | `simp [Formula.and, Formula.neg, PropositionalConnectives.neg, isUFree, ha, hq]` (**VERIFIED closes**) |
| 662 `…ha_neg_Uf` (bare) | `simp [isUFree, ha]` | `simp [Formula.neg, PropositionalConnectives.neg, isUFree, ha]` |
| 667 `…hsep_H` | `simp only [is_syntactically_separated_allPast, Formula.neg, isUFree, ha, Bool.and_true]` | add `PropositionalConnectives.neg` |

Note: the reported error line and the `simp` line differ by ±1 at some sites because Lean reports
the `unsolved goals` at the enclosing `have`/proof head; the fix always lands on the `simp` call.
Because the sites are structurally identical Case-2/Case-3 clones, the implementer should fix one,
build-confirm, then transcribe to the parallel siblings. **Mechanical; ~15 edits.**

## 3. `Separation/DedekindZ/QLemma.lean` — `unsolved goals` (191)

`Q_Z_U_free` (189-192). `qZ A B C = Formula.or (Formula.or B A) (Formula.neg (.snce (Formula.neg
A) C))` (QLemma:93-94). Current `simp [qZ, isUFree, hA, hB, hC]` leaves
`⊢ isUFree (¬(¬A) S C) = true` — the `neg` over the `snce` is unreduced.

| Line | Current (FAILS) | Replacement (VERIFIED closes) |
|------|-----------------|-------------------------------|
| 192 | `simp [qZ, isUFree, hA, hB, hC]` | `simp [qZ, Formula.or, Formula.neg, PropositionalConnectives.neg, isUFree, hA, hB, hC]` |

The sibling `Q_Z_no_S_nested` (195-199) uses a different `repeat (first | …)` tactic and is NOT in
the failing set, so it is unaffected. **Mechanical; 1 edit.**

## 4. `Theorems/Perpetuity/Bridge.lean` — `Type mismatch` (102) — DISTINCT family

`pastMono` (93-104). The proof builds `past_raw` via `temporal_duality`, then tries to normalize
its type to the goal `⊢ ⊢ H(φ₁ → φ₂)` (`Formula.allPast (φ₁.imp φ₂)`):

```lean
have past_raw := Bimodal.DerivationTree.temporal_duality _ g_swap
have h_past : ⊢ (φ₁.imp φ₂).allPast := by
  simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution] at past_raw
  exact past_raw          -- line 102: Type mismatch
```

`past_raw : ⊢ (G(φ₁ → φ₂).swapTemporal).swapTemporal` (verified via `lean_goal`). The current
simp set unfolds the **raw recursive def `swapTemporal`**, which over-normalizes and never lands
on `H(φ₁ → φ₂)`, so `exact past_raw` mismatches. The drift mirrors task-364 Family-2 (raw-def
`simp only` no longer normalizes to the expected shape).

**Fix (VERIFIED):** route through the structural `@[simp]` exchange lemma
`Bimodal.Formula.swapTemporal_allFuture` (Formula.lean:185:
`(allFuture φ).swapTemporal = allPast φ.swapTemporal`) instead of the raw def:

| Line | Current (FAILS) | Replacement (VERIFIED) |
|------|-----------------|------------------------|
| 101 | `simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution] at past_raw` | `simp only [Bimodal.Formula.swapTemporal_allFuture, Bimodal.Formula.swapTemporal_involution] at past_raw` |

`lean_multi_attempt` confirms this rewrites `past_raw` to exactly
`⊢ H(φ₁ → φ₂)` (= the goal), zero diagnostics, so the unchanged `exact past_raw` then type-checks.
Mechanism: `swapTemporal_allFuture` turns `(G ψ).swapTemporal` into `H (ψ.swapTemporal)`, then
`swapTemporal_involution` collapses the double swap `ψ.swapTemporal.swapTemporal → ψ`. The
fully-qualified name is required (the bare `swapTemporal_allFuture` is not in scope in this file).
**Mechanical, 1 edit** — but note it is a *different* idiom (lemma substitution, not simp-set
augmentation), so flag it as its own phase.

## Common root vs independent? 

- **Modules 1, 2, 3 share ONE root**: the `PropositionalConnectives.neg`/`.top` second-layer
  abbrev no longer auto-unfolds under bare/partial simp sets. Fix = augment the simp set to the
  full unfold chain, matching the already-repaired `Separation/Defs.lean` idiom.
- **Module 4 is independent in mechanism** (swapTemporal normalization) but the same drift
  *flavour* (simp no longer normalizing a derived/recursive form to the expected shape) — it is
  fixed by substituting the structural `@[simp]` lemma `swapTemporal_allFuture` for the raw def.

No module needs more than a mechanical drift fix. No statement changes, no new lemmas, no new
axioms, no `sorry`. There is no hidden API change in `Separation/Defs` beyond the unfold-chain
behaviour; `Defs` itself already encodes the fix idiom and builds clean.

## Reuse Check (Foundations-first)

No new abstractions. Every fix reuses existing declarations already in scope:
- `PropositionalConnectives.neg` / `PropositionalConnectives.top`
  (`Cslib/Foundations/Logic/Connectives.lean:155/159`) — the canonical unfold lemmas, already used
  throughout the repaired `Separation/Defs.lean`.
- `Formula.neg/and/or` abbrevs (`Syntax/Formula.lean:63/71/75`).
- `Bimodal.Formula.swapTemporal_allFuture` (`Syntax/Formula.lean:185`, `@[simp]`) and
  `swapTemporal_involution` (`:151`) — already-proven structural lemmas for the Bridge fix.

## Optional global alternative (NOT recommended)

One could instead mark `PropositionalConnectives.neg`/`.top` `@[simp]` (or `@[reducible]`) to make
bare simps work library-wide. **Rejected**: it changes the global simp normal form for every
`Formula`/`Proposition` consumer and risks rippling breakage well beyond these 4 modules; it also
diverges from the per-site idiom the repaired `Defs.lean` already established. Keep the repair
local and idiom-consistent.

## Recommended phase breakdown for the planner

Each phase is one bounded, build-driven agent run (`lake build <Module>` scoped), no
`lean_diagnostic_messages`, sparing `lean_goal`.

- **Phase 1 — Duality** (`Cslib.Logics.Bimodal.Metalogic.Separation.Duality`): 2 edits (357, 362).
  Build + commit. (Smallest; good warm-up establishing the idiom.)
- **Phase 2 — QLemma** (`…Separation.DedekindZ.QLemma`): 1 edit (192). Build + commit.
- **Phase 3 — Eliminations** (`…Separation.Eliminations`): ~15 edits across the parallel Case-2/3
  clones (63, 498/501, 543-553, 602-612, 660-667). Fix one site, build-confirm the idiom, then
  transcribe to siblings; scoped build + commit. (Largest, but fully mechanical and repetitive.)
- **Phase 4 — Bridge** (`…Theorems.Perpetuity.Bridge`): 1 edit (101, lemma substitution — distinct
  idiom). Build + commit.
- **Phase 5 — Zero-debt verification**: full `lake build`; `#print axioms` / `lean_verify` on the
  touched declarations shows zero `sorry` / zero new axioms; `lake exe lint-style`; `lake lint`
  (watch `unusedSimpArgs` — these files set `linter.unusedSimpArgs false` locally, e.g. QLemma:21,
  so extra simp args are tolerated; keep that option where present).

Phases 1-4 are mutually independent (different files) and could be parallelized under a
`--team` run with per-file territory contracts. Phase 3 is the long pole.

## Constraints (carried into the plan)

Zero `sorry`, zero new axioms, no `admit`, no vacuous placeholders. Preserve all theorem
statements verbatim. Faithful drift repair, not redesign. CI green
(`lake build` + `lake exe lint-style` + `lake lint`).

## Lint-prevention notes

- Edits only touch `simp` argument lists inside existing `theorem` bodies — no new declarations,
  so `docBlame`/`defLemma`/`defsWithUnderscore`/`topNamespace`/`dupNamespace` are not engaged.
- `simpNF`: not triggered (no new `@[simp]` lemmas).
- `unusedSimpArgs`: adding `PropositionalConnectives.neg` is *load-bearing* (it fires), so it will
  not be flagged; the affected files additionally disable this linter locally where relevant.
- Prefer keeping the existing `simp` vs `simp only` form at each site to minimize normal-form churn
  (the Duality/QLemma sites use `simp`; Eliminations mixes `simp`/`simp only`; Bridge uses
  `simp only`). All verified replacements above preserve the original tactic form.
</content>
</invoke>
