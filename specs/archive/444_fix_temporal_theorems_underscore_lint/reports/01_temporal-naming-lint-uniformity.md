# Research Report — Task 444: Temporal Theorems Underscore Lint + Naming Uniformity

Session: sess_1782924983_6bcecb_444
Agent: cslib-research-agent
Date: 2026-07-01
Scope: HARD FIX (2 renames + refs) + naming/docstring/lint uniformity sweep on settled task-180 files only.
Change class: renames + docs ONLY. ZERO behavioural change. No sorries. No axioms.

---

## 1. Live scope verification (statuses checked against specs/state.json)

| Task | Status (live) | Consequence for 444 |
|------|---------------|---------------------|
| 449 (define_bxplus_metric_tense_base) | **not_started** | Decls (BX+ / FrameClass.Metric axioms) DO NOT EXIST. **OUT OF SCOPE / follow-up.** |
| 450 (prove_tm_conservative_over_bxplus) | **not_started** | `eraseBox`, restated conservativity DO NOT EXIST. **OUT OF SCOPE.** `TemporalConservativity.lean` scheduled for REWRITE by 450 → **DEFER all naming/docstring work there.** |
| 454 (consolidate_chronicle_pointinsertion_bimodal_temporal) | **completed (committed)** | `Chronicle/PointInsertion/SinceSeedConsistency.lean` + both `Since.lean` are SETTLED. **Do NOT undo.** Reconcile Chronicle/TruthLemma sweep with settled state. |

Excluded entirely (task-301 tableau line — 426/439/425): `Cslib/Logics/Temporal/Tableau/**` (Defs, Rules, Completeness, Saturation, ...). **Do NOT touch.**

Deferred to after 450: `Cslib/Logics/Temporal/Metalogic/ConservativeExtension/TemporalConservativity.lean`.

---

## 2. Live `lake lint` findings in scope (the work queue)

`lake lint` was run and filtered to in-scope paths (Temporal/{Syntax,Semantics,ProofSystem,Metalogic,Theorems}, TemporalEmbedding.lean; minus Tableau, minus TemporalConservativity). **Exactly two live findings, both `defsWithUnderscore`:**

| # | Lint-reported loc | Def keyword line | Declaration | Category |
|---|-------------------|------------------|-------------|----------|
| L1 | `Theorems.lean:51:1` | `Theorems.lean:58` | `allFuture_iff_neg_someFuture_neg` | defsWithUnderscore |
| L2 | `Theorems.lean:68:1` | `Theorems.lean:70` | `allPast_iff_neg_somePast_neg` | defsWithUnderscore |

(Lint reports the docstring-start line; the `def` keyword is a few lines below.)

**No other in-scope lint findings are live.** Categories named in the task mandate but confirmed NOT firing in scope: `defLemma`, `docBlame`, `dupNamespace`, `topNamespace`, `simpNF`, `unusedSectionVars`. The two flagged decls already carry house-style docstrings (so no docBlame), and all `sat_*`/`mcs_*` bridge decls are correctly `theorem`s (so no defLemma). The sweep is therefore **defsWithUnderscore-only + docstring reference hygiene**, not a broad multi-category lint fix.

---

## 3. Classification of the two flagged decls (data vs proposition)

Both return `DerivationTree ...` — i.e. **data (a proof tree), not a `Prop`**. They are correctly declared `def` (noncomputable section). The linter is right that a *data* `def` must be lowerCamelCase, not snake_case. They must NOT be converted to `theorem`/`lemma` (that would be wrong — they carry data). The fix is the rename, keeping `def`.

```
Theorems.lean:58  def allFuture_iff_neg_someFuture_neg (φ : Formula Atom) :
                    DerivationTree FrameClass.Base [] (φ.allFuture ↔ ¬𝐅¬φ) := ...
Theorems.lean:70  def allPast_iff_neg_somePast_neg (φ : Formula Atom) :
                    DerivationTree FrameClass.Base [] (φ.allPast ↔ ¬𝐏¬φ) := ...
```

Namespace: `Cslib.Logic.Temporal.Metalogic` (not `Theorems` — see docstring-accuracy note in §5).

### Recommended names (mathlib-conformant lowerCamelCase, mechanical, unambiguous)

| Old | New |
|-----|-----|
| `allFuture_iff_neg_someFuture_neg` | `allFutureIffNegSomeFutureNeg` |
| `allPast_iff_neg_somePast_neg` | `allPastIffNegSomePastNeg` |

Rationale: direct camelCase of the existing descriptive name; preserves the proposition-mirroring readability; parallels the *semantic* theorem `Satisfies.sat_allFuture_iff_neg_someFuture_neg` (which is a `Prop`/`theorem` and correctly STAYS snake_case). This gives a uniform two-tier convention: data derivation defs = lowerCamelCase; propositions = snake_case theorems.

---

## 4. Exact edit inventory (grep-verified; zero behavioural change)

### 4a. HARD FIX — the two renames (blocks PR)

1. `Cslib/Logics/Temporal/Theorems.lean:58` — `def allFuture_iff_neg_someFuture_neg` → `def allFutureIffNegSomeFutureNeg`
2. `Cslib/Logics/Temporal/Theorems.lean:70` — `def allPast_iff_neg_somePast_neg` → `def allPastIffNegSomePastNeg`

### 4b. Reference updates required by the renames (docstrings/comments — NO code call sites exist)

Grep confirms the two data-defs are **never called from code** — the only occurrences besides the defs themselves are doc/comment references and the *distinct* `sat_*` semantic theorem (which is a different declaration). References to update:

3. `Cslib/Logics/Temporal/Theorems.lean:69` (docstring of the allPast def) — `allFuture_iff_neg_someFuture_neg` → `allFutureIffNegSomeFutureNeg`
4. `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean:34` — `Theorems.allFuture_iff_neg_someFuture_neg` → `Metalogic.allFutureIffNegSomeFutureNeg` (also corrects the wrong `Theorems.` prefix; see §5)
5. `Cslib/Logics/Temporal/Syntax/Formula.lean:97` — `allFuture_iff_neg_someFuture_neg` → `allFutureIffNegSomeFutureNeg`

### 4c. Uniformity candidate (NOT a live lint finding — private def, lint-exempt)

6. `Cslib/Logics/Temporal/ProofSystem/Instances.lean:83` — `private def hyp_syl` → `private def hypSyl`. Returns `DerivationTree ...` (data). Private, so `defsWithUnderscore` does not fire (confirmed: not in lint output). Renaming is a pure uniformity choice under the "data-returning defs lowerCamelCase" mandate; zero behavioural change; all call sites internal to `Instances.lean`.
   - Call sites (all in `Instances.lean`): lines **159, 169, 179, 189, 202, 215** (`⟨hyp_syl ...⟩`).
   - Comment reference: line **150** (`... then chain via hyp_syl.`).
   - Recommendation: INCLUDE for uniformity, but it is optional and does NOT block the PR (not lint-flagged). Flag it as "uniformity, not lint-required" in the plan so the reviewer can accept/skip.

### 4d. Things confirmed IN-SCOPE-but-NO-ACTION

- **`sat_allFuture_iff_neg_someFuture_neg` / `sat_allPast_iff_neg_somePast_neg`** (Satisfies.lean:193/206; consumed in Soundness.lean, Chronicle/TruthLemma.lean): `theorem`s returning `Iff` (propositions). Correct snake_case. **No change.**
- **`mcs_allFuture_iff` / `mcs_allPast_iff` family** (used across CompletenessHelpers.lean): propositions/`theorem`s, correct snake_case. **No change.**
- **`pairing`, `modus_ponens`, `axiom`** used in Theorems.lean: `pairing` (PropositionalHelpers.lean:82) is already lowerCamelCase; `modus_ponens`/`axiom` are `DerivationTree` **constructors** (DerivationTree.lean) — renaming constructors would ripple into out-of-scope Tableau files and is NOT lint-flagged. **OUT OF SCOPE.**
- **`set_option ...` lines** across Metalogic: all are targeted `linter.style.*` / `linter.flexible` / `linter.unusedSimpArgs` / `linter.dupNamespace` suppressions — legitimate, not dev-only debug options (no `pp.*`, `trace.*`, `maxHeartbeats`, `linter.all false`). **No removal warranted in scope.**

---

## 5. Docstring / D3-caveat hygiene (docs-only)

- **Wrong module-prefix reference:** `TemporalEmbedding.lean:34` writes `Theorems.allFuture_iff_neg_someFuture_neg`, but the decl's actual namespace is `Cslib.Logic.Temporal.Metalogic` (file is `Theorems.lean` but the `namespace` inside is `...Metalogic`). Fix the reference to `Metalogic.allFutureIffNegSomeFutureNeg` (or bare `allFutureIffNegSomeFutureNeg`) when renaming.
- **D3 honesty caveat** appears in three places in `Theorems.lean` only (module docstring lines 30–38; def docstring lines 56–57; cross-ref line 69). These are already internally consistent (short def-level caveat points to the module docstring). The mandate to "unify the D3 honesty caveat" is satisfied by keeping the single authoritative statement in the module docstring and the one-line pointer in each def docstring. On rename, ensure the line-69 cross-ref uses the NEW name. (Note: `h_D3`/`D3` tokens found in Chronicle/PointInsertion/* are unrelated local hypothesis names — a "disjunct 3" naming, NOT the honesty caveat. Do not touch.)
- Public decls in scope already carry house-style docstrings; no docBlame gap to fill.

---

## 6. Verification plan (implementation phase)

1. Apply edits 1–5 (mandatory) and optionally 6.
2. `lake build Cslib.Logics.Temporal.Theorems` and `lake build Cslib.Logics.Bimodal.Embedding.TemporalEmbedding` (scoped) — expect green (renames are local; no call sites).
3. `lake lint 2>&1 | grep -E "Temporal/(Syntax|Semantics|ProofSystem|Metalogic|Theorems)|TemporalEmbedding"` — expect ZERO lines (both defsWithUnderscore cleared).
4. Full CI order before PR: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`.
5. Confirm no sorries introduced (there are none; this is a rename). `git diff` should show only identifier renames + doc-comment text.

---

## 7. Out-of-scope / follow-up (encode in plan, do NOT execute now)

- 449 decls (BX+ / FrameClass.Metric axioms): do not exist → defer.
- 450 decls (eraseBox, restated conservativity) + `TemporalConservativity.lean` rewrite: defer entire file to after 450.
- `Tableau/**`: owned by 301 line (426/439/425) — never touch.
- DerivationTree constructor names (`modus_ponens`, etc.): cross-cutting, not lint-flagged, ripples into Tableau — separate task if ever desired.
- 454-settled Chronicle files (`SinceSeedConsistency.lean`, both `Since.lean`): do not modify.

---

## 8. Reuse-first check

No new definitions or abstractions are introduced by this task (rename + docs only), so the CSLib reuse-first gate is trivially satisfied. The two-tier naming convention recommended here (data defs lowerCamelCase / propositions snake_case theorems) is the existing Mathlib+CSLib standard already used by the surrounding `sat_*`, `mcs_*`, `pairing` decls — we are conforming to it, not inventing anything.
