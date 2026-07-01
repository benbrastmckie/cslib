# Research Report — Task 391: Strip Docstring Jargon & Fix Stale Counts

**Task type**: cslib (comment/docstring-only; no proof-logic changes)
**Session**: sess_1782924983_6bcecb_391
**Date**: 2026-07-01
**Reuse-check**: N/A — this task introduces no new definitions/abstractions. It only rewrites
comment text. The CSLib reuse-first protocol does not apply (nothing to reuse-or-define).

---

## Scope & Hard Constraints (verified)

| Constraint | Status |
|-----------|--------|
| Do NOT edit `Connectives.lean` (owned by task 400) | CONFIRMED: jargon lives only in `Cslib/Foundations/Logic/Connectives.lean` (lines 21, 38, 41, 144 — PR #607 / task 340 / task 173). This file is EXCLUDED. |
| StrongCompleteness atom/bot/imp 3-case counts are CORRECT — do not change | CONFIRMED: the "(3 cases: atom, bot, imp)" phrases are in `IntStrongCompleteness.lean:107` and `MinStrongCompleteness.lean:121`. They match the current 3-constructor `Proposition` structure. LEAVE UNCHANGED. |
| Stay clear of proof bodies | Honored. All docstring edits are in `/-! -/` or `/-- -/` blocks. The one in-proof-body site (ListImplication comments) is comment-text-only and flagged with extra caution. |
| Verify staleness before proposing count fixes | Done per-site below. |

**No proof logic is touched anywhere.** Comment/docstring edits cannot break the build unless a
`/-! … -/` or `/-- … -/` delimiter is damaged. Implementer must run `lake build` on each edited
module as a sanity check only.

---

## Part A — Jargon-Strip Sites (task/process references in public docstrings)

### A1. `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean`
Module-header docstring (`/-! -/`, lines 13–58). Three "task 352" references.

- **L19 CURRENT**: `method from the purely implicational case (task 352) with a new conjunction case.`
  **REPLACE**: `method from the purely implicational case (see`
  `ClassicalImpCompleteness.lean`) with a new conjunction case.`
- **L23 CURRENT**: `The proof is the CL-B rung above `classicalImp_completeness` (task 352), mirroring its`
  **REPLACE**: `The proof extends `classicalImp_completeness` (from`
  `ClassicalImpCompleteness.lean`), mirroring its`
  (Strip both "CL-B rung" internal-ladder jargon and "task 352".)
- **L51 CURRENT**: `subcase (false-antecedent branch), exactly as in task 352.`
  **REPLACE**: `subcase (false-antecedent branch), exactly as in the implicational case.`
- **L57 (References block) CURRENT**: `* Task 352: `Cslib/…/ClassicalImpCompleteness.lean` — the direct template; this module adds the `and` case.`
  **REPLACE**: keep the file reference, drop the task tag:
  `* `Cslib/…/ClassicalImpCompleteness.lean` — the direct template; this module adds the `and` case.`

### A2. `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpBotCompleteness.lean`
Two docstrings: module header (13–65) and the `classicalConjImpBot_kalmar` docstring (171–182),
plus the `cpl_conservative_over_classicalConjImpBot` docstring (469–478). Several "task 378 / 352"
and "CL-C rung" references.

- **L18 CURRENT**: `Tarski–Bernays truth-assignment method from the conjunction-implication case (task 378)`
  **REPLACE**: `Tarski–Bernays truth-assignment method from the conjunction-implication case (see`
  `ClassicalConjImpCompleteness.lean`)`
  NOTE: "(task 378)" here labels the *conjunction-implication module*, i.e.
  `ClassicalConjImpCompleteness.lean` — replace the task tag with the file name.
- **L23 CURRENT**: `The proof is the CL-C rung above `classicalConjImp_completeness` (task 378), mirroring its`
  **REPLACE**: `The proof extends `classicalConjImp_completeness` (from`
  `ClassicalConjImpCompleteness.lean`), mirroring its`
- **L37 CURRENT**: `the `atom`, `imp`, and `and` cases are transcribed from `classicalConjImp_kalmar` (task 378);`
  **REPLACE**: `the `atom`, `imp`, and `and` cases are transcribed from `classicalConjImp_kalmar`;`
- **L52 CURRENT**: `(`⊥ → goal`) directly closes the goal. This is the one genuine extension over task 378.`
  **REPLACE**: `(`⊥ → goal`) directly closes the goal. This is the one genuine extension over the`
  `conjunction-implication case.`
- **L55 CURRENT**: `Peirce's law enters only in the `imp` TRUE-side false-antecedent subcase, exactly as in`
  `tasks 352 and 378.`
  **REPLACE**: `… exactly as in the implicational and conjunction-implication cases.`
- **L61–65 (References) CURRENT**: two bullets tagged `Task 352:` and `Task 378:`.
  **REPLACE**: drop the `Task NNN:` prefixes; keep the file paths and descriptive text
  (`* `Cslib/…/ClassicalImpCompleteness.lean` — the original template; …` and
  `* `Cslib/…/ClassicalConjImpCompleteness.lean` — the ∧-extension this module builds on; …`).
- **L178 (kalmar docstring) CURRENT**: `and` cases are transcribed from `classicalConjImp_kalmar` (task 378), retargeted to`
  **REPLACE**: `and` cases are transcribed from `classicalConjImp_kalmar`, retargeted to`
- **L182 (kalmar docstring) CURRENT**: `enters only in the `imp` TRUE-side false-antecedent subcase, as in tasks 352 and 378.`
  **REPLACE**: `… as in the implicational and conjunction-implication cases.`
- **L476–477 (conservativity docstring) CURRENT**:
  `- CL-A: `CPL⟨→,⊤⟩ ⊂ CPL` for imp-top-only formulas (task 352)`
  `- CL-B: `CPL⟨∧,→,⊤⟩ ⊂ CPL` for or-bot-free formulas (task 378)`
  **REPLACE**: keep the CL-A/CL-B *result labels* (they are meaningful math labels used in the
  conservativity table, not task jargon) but strip the trailing `(task NNN)`:
  `- CL-A: `CPL⟨→,⊤⟩ ⊂ CPL` for imp-top-only formulas`
  `- CL-B: `CPL⟨∧,→,⊤⟩ ⊂ CPL` for or-bot-free formulas`

  DECISION NOTE on "CL-A/CL-B/CL-C" and "rung": the *bare labels* `CL-A/CL-B/CL-C` also appear in
  `ConservativeChain.lean` as a documented conservativity-column taxonomy (a math label), so they
  are NOT internal task jargon and may stay where they read as column labels. The word "rung" in
  the *header* prose ("the CL-B rung above …") is ladder-metaphor jargon and is stripped in A1/A2
  header edits above. Implementer: strip "rung"/"task NNN" from prose; keep "CL-x" where it labels
  a conservativity-table row.

### A3. `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` (L44)
- **L44 CURRENT**: `The classical column is 4-for-4: all classical conservativity results use the Kalmár /`
  **REPLACE**: `All three classical conservativity results (CL-A, CL-B, CL-C) use the Kalmár /`
  RATIONALE: "4-for-4" is (a) informal scorekeeping jargon and (b) a **genuinely stale/incorrect
  count** — the table immediately below (L47–51) has exactly THREE rows (CL-A, CL-B, CL-C), and
  L53 itself says "The three towers". See Part B for the staleness classification.
  (This is the "44-45" site from the task description; the count sits on L44.)

### A4. `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean` (L21–22)
- **L21–22 CURRENT**:
  `This is **Route A2** from the strong completeness proof strategy: a fresh relativized copy of`
  `the Lindenbaum construction, chosen to keep the original 341 proof files untouched.`
  **REPLACE**:
  `This is a fresh relativized copy of the Lindenbaum construction, chosen so that the existing`
  `(non-relativized) Lindenbaum development is reused unchanged rather than modified in place.`
  RATIONALE: strips "Route A2" (internal strategy-branch label) and "341 proof files" (a
  point-in-time repo-size figure — process/logistics jargon, not math).

### A5. `Cslib/Foundations/Logic/Tableau/RuleResult.lean` (L34–35)
- **L34–35 CURRENT**:
  `The `persistent` variant is included from day one to support downstream modal and temporal`
  `tableau tasks (tasks 299-301), where box-rules produce signed formulas that must be available`
  **REPLACE**:
  `The `persistent` variant is included to support downstream modal and temporal tableau`
  `calculi, where box-rules produce signed formulas that must be available`
  RATIONALE: strips "from day one" (process idiom) and "(tasks 299-301)".

### A6. `Cslib/Foundations/Logic/PropositionalTableau.lean` (L7)
- **L7 CURRENT**: `-- DEPRECATED: This file is superseded by Cslib.Foundations.Logic.Tableau. See task 297.`
  **REPLACE**: `-- DEPRECATED: This file is superseded by Cslib.Foundations.Logic.Tableau.`
  RATIONALE: strip "See task 297." The deprecation pointer to the successor module is retained.

### A7. `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` (L83–139) — IN-PROOF COMMENTS (caution)
These are inline scratch comments inside two tactic proofs. They contain no task numbers but carry
informal dev-diary jargon. **Comment-text only — do NOT alter any tactic line.** After editing,
`lake build` the module to confirm (comments are inert, so a green build is expected).
- **L83 CURRENT**: `-- Need: ⊢ (φ → ψ) → φ → ψ, which is identity on (φ → ψ)... no.`
  **REPLACE**: `-- Base case: `listImp [] (φ → ψ) = φ → ψ`, so the goal is the identity `⊢ (φ → ψ) → (φ → ψ)`.`
- **L131 CURRENT**: `--   from ⊢ (A → B) → C and ⊢ D → A, get ⊢ D → (B → C)... that's not right.`
  **REPLACE**: delete this line (it records a discarded intermediate attempt; the surrounding
  lines L126–140 already give the correct derivation).
- **L133 CURRENT**: `-- Let me think differently. We need:`
  **REPLACE**: `-- Correct route. We need:`
  OPTIONAL (lower priority): the L126–139 block is verbose stream-of-consciousness derivation
  commentary. Trimming it further is out of the minimal-jargon scope; the three edits above
  remove the clearly-conversational phrases. Keep edits minimal to protect proof bodies.

---

## Part B — Stale-Count Sites (verify-then-fix)

Each classified as STALE (fix) or CORRECT (leave). Verification was done against the current live
code (constructor lists / `grep -c sorry` / referenced line numbers).

### B1. STALE — `IntSoundness.lean:41` "The 3 cases are:"
`int_axiom_sound`'s `cases h_ax with` now has **9** constructors: `implyK, implyS, efq, andI,
andE1, andE2, orI1, orI2, orE` (verified L49–88). The docstring lists only 3 (implyK/implyS/efq).
GENUINELY STALE.
- **L41 CURRENT**: `The 3 cases are:` followed by a 3-item bullet list (L42–45).
- **RECOMMENDED FIX**: change count and rewrite the list to cover all 9, OR (lighter, still
  accurate) reword to avoid an exact count:
  `The axiom cases (implication K/S, EFQ, conjunction intro/elim, disjunction intro/elim) are
  each valid; the two implication cases use persistence and transitivity of ≤, EFQ is vacuous, and
  the ∧/∨ cases are structural.`
  Implementer's choice; both remove the stale "3". Prefer the reworded prose to avoid re-staling
  if more axioms are ever added.

### B2. STALE — `MinSoundness.lean:42` "The 2 cases are:"
`min_axiom_sound`'s `cases h_ax with` has **8** constructors: `implyK, implyS, andI, andE1, andE2,
orI1, orI2, orE` (verified L48–83). Docstring lists only 2. GENUINELY STALE.
- **L42 CURRENT**: `The 2 cases are:` + 2-item list (L43–44).
- **RECOMMENDED FIX**: mirror B1 — reword to
  `The axiom cases (implication K/S, conjunction intro/elim, disjunction intro/elim) are each
  valid; the implication cases use persistence and transitivity of ≤, and the ∧/∨ cases are
  structural.`

### B3. STALE (misattached docstring) — `IntLindenbaum.lean:262`
The task's "IntLindenbaum:320" is a pre-shift line number; the live file is 318 lines. The actual
defect is a **copy-pasted/misattached docstring at L262**: the docstring
`/-- IntPropAxiom is consistent: `[] ⊬ ⊥`. -/` sits above `private noncomputable def
lift_int_to_cl` (L263), which is a *derivation-tree lifter*, not a consistency statement. The
identical docstring correctly belongs to `int_consistent` (L274–275, which it also labels — that
one is correct). So L262 is a misattached duplicate.
- **L262 CURRENT**: `/-- IntPropAxiom is consistent: `[] ⊬ ⊥`. -/`
- **RECOMMENDED FIX** (accurate docstring for `lift_int_to_cl`):
  `/-- Lift an `IntPropAxiom` derivation tree to a `PropositionalAxiom` derivation tree,
  recursing through the tree via `IntPropAxiom.toPropAxiom` on the axiom leaves. -/`
- Leave L274 (`int_consistent`) unchanged — it is correctly attached.

### B4. STALE (line numbers, not the count) — `Intuitionistic/DecisionProcedure.lean:38–42`
The "Notes on sorry" lists **4 deferred sorries** with explicit file:line citations. Verification:
- `Scheme.lean:246` → **STALE**. Actual sorries in `Intuitionistic/Scheme.lean` are at **L409 and
  L1070** (verified). The cited 246/519 no longer match.
- `Scheme.lean:519` → **STALE** (see above).
- `Completeness.lean:113` → CORRECT (Int `Completeness.lean:113` has `sorry`, verified).
- `Minimal/Completeness.lean:110` → CORRECT (verified).
The *count* "4 sorries" is still accurate (2 in Scheme + 1 Int Completeness + 1 Min Completeness).
- **RECOMMENDED FIX**: This module also carries "task 317" / "task 422" process jargon (L38, L45,
  L56–57, L59). Combine the jargon-strip with a **stale-proof rewrite** that drops brittle line
  numbers in favor of lemma/role descriptions (line numbers will re-stale the moment task 317, on
  hold, touches these files):
  - L38 CURRENT: `4 sorries tracked under task 317:` → `four deferred sorries in the completeness
    development:`
  - L39 CURRENT: ``Scheme.lean:246` — parametric `truthLemma S b …` …` → `the parametric
    `truthLemma` in `Intuitionistic/Scheme.lean` (forcing ↔ membership, all connectives)`
  - L40 CURRENT: ``Scheme.lean:519` — open-branch countermodel structural property` → `the
    open-branch countermodel structural property in `Intuitionistic/Scheme.lean``
  - L41 CURRENT: ``Completeness.lean:113` — `IValid → forcing` bridge …` → keep, drop the exact
    line: `the `IValid → forcing` bridge in `Intuitionistic/Completeness.lean` (uses the
    parametric `truthLemma`)`
  - L42 CURRENT: ``Minimal/Completeness.lean:110` — `MValid → forcing` bridge …` → `the
    `MValid → forcing` bridge in `Minimal/Completeness.lean` (reuses `truthLemma minScheme`)`
  - L44–46, L56–57: replace "pre-existing 317 `sorryAx`" / "when task 317 lands" with
    "the deferred completeness `sorryAx`" / "once the deferred completeness sorries are filled".
  - L59: "(as of task 422)" → delete the parenthetical.

### B5. STALE — `Minimal/DecisionProcedure.lean:23` and jargon at L44–52, L63–66
- **L23 CURRENT**: ``minimalTableau_complete`: … Currently rests on 4 sorries in
  `Minimal/Completeness.lean`.` → **STALE on two counts**: (a) it is not "4 sorries", and (b) they
  are not all in `Minimal/Completeness.lean`. The live picture (L45–48) lists **3** deferred
  sorries: 2 in `Intuitionistic/Scheme.lean` (reused via `minScheme`) + 1 in
  `Minimal/Completeness.lean:110`. Verified: `Minimal/Completeness.lean` has exactly **1** `sorry`
  (L110).
  **RECOMMENDED FIX (L23)**: `Rests on the deferred completeness sorries (see "Notes on sorry"
  below).`
- **L45 / L47 CURRENT**: `Scheme.lean:246` / `Scheme.lean:519` → **STALE line numbers** (actual
  409/1070). Rewrite as role descriptions exactly as in B4 (drop line numbers).
- **L48 CURRENT**: `Minimal/Completeness.lean:110 — …` → keep description, drop the exact line.
- Jargon strip: "pre-existing 317 sorries" (L44), "pre-existing 317 `sorryAx`" (L51, L63),
  "not introduced by task 422; it will be resolved when task 317 lands" (L52), "(as of task 422)"
  (L66) — replace with the same jargon-free phrasing as B4.

### B6. `Minimal/Completeness.lean` "Notes on sorry" (task-described "50–51")
The task's "50–51" is pre-shift; the live "Notes on sorry" block is L43–49 (L50–53 is the blank +
`## References`). There is **no numeric count** in this block — it says "the deferred sorries" /
"the remaining sorry" (accurate: the file has exactly 1 `sorry` at L110). The only edit needed is
the **jargon strip** at L49:
- **L49 CURRENT**: `completeness obligations handed to task 317.`
- **REPLACE**: `deferred completeness obligations.`
FLAG (per task instruction): task 317 is on hold and will fill this module's sorry. A comment edit
now is **safe/non-conflicting** (it removes a task tag and touches no proof body). If/when 317
lands, this "Notes on sorry" block should be revisited, but there is no count here to go stale.

### B7. CORRECT — DO NOT CHANGE
- `IntStrongCompleteness.lean:107`: `Proof by structural induction on `φ` (3 cases: atom, bot,
  imp).` — CORRECT (matches the 3-constructor formula structure; task 398 changed derivation
  constructors, not `Proposition`'s atom/bot/imp shape). **LEAVE.**
- `MinStrongCompleteness.lean:121`: same 3-case phrase. **LEAVE.**
- `IntLindenbaum.lean:274`: `int_consistent` docstring — correctly attached. **LEAVE.**

---

## Excluded (ownership / out of scope)
- `Cslib/Foundations/Logic/Connectives.lean` (L21, L38, L41, L144 — PR #607 / task 340 / task 173):
  OWNED by task 400. **Do NOT edit.** Coordinate only.
- The other two `Connectives.lean` files (`Foundations/Logic/Theorems/Propositional/`,
  `Logics/Bimodal/Theorems/Propositional/`) carry none of this jargon and are not in scope.

---

## Zero-Debt / Policy Compliance
- No `sorry`, no axioms, no vacuous defs involved — this is pure comment text. The existing
  deferred sorries (Scheme/Completeness) are pre-existing and OUT OF SCOPE; this task only
  *describes* them more accurately. No new debt is introduced.
- No new definitions → reuse-first protocol is inapplicable.

## Recommended Implementation Ordering (for the planner)
1. Part A jargon strips A1–A6 (pure header/docstring text, mechanically safe).
2. Part B count/docstring fixes B1–B3 (self-contained, no cross-file dependency).
3. Part B4/B5/B6 (DecisionProcedure + Minimal/Completeness) — combine jargon-strip with
   line-number-removal; prefer role descriptions over line numbers to be 317-proof.
4. Part A7 (ListImplication in-proof comments) LAST, with a `lake build` immediately after —
   lowest risk tolerance since it sits in proof bodies (comment-text only).
5. Final `lake build` of the whole project (or scoped builds of each edited module).

## Verification checklist for implementer
- [ ] `Connectives.lean` untouched (git diff must not list it).
- [ ] `IntStrongCompleteness.lean:107` / `MinStrongCompleteness.lean:121` untouched.
- [ ] No tactic/term lines changed in `ListImplication.lean` (only comment lines).
- [ ] `lake build` green for each edited module.
- [ ] `grep -rnE "task [0-9]+|Route A2|N proof files|day one|4-for-4|CL-. rung"` over edited files
      returns nothing (except any intentional CL-x table labels retained per A2 decision note).
