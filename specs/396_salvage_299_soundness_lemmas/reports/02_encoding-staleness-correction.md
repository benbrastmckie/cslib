# Research Report (Supplement): task-441 Encoding-Staleness Correction to the Salvage Plan

- **Task**: 396
- **Type**: cslib
- **Session**: sess_1784044325_11ad9e_396
- **Reference branch/commit**: `wip/task-299-soundness-refactor` @ `27d93e2d` (2026-06-28)
- **Supplements**: `reports/01_salvage-299-soundness-lemmas.md`

## Why this supplement exists

Report `01` correctly identifies the acc-free block (`sfSat`, `sfSat_pos/neg`, `RuleResultSat`,
the four `*_eq_some` recognizer characterizations, `applyPropRule_sat`) as the salvage payload
and correctly excludes the global-Accessibility `modalStepBranch_preserves_sat`. **Its
per-lemma classification stands, with one material correction**: report `01` (items 4–5,
Phase A) recommends adding **`modalOrOf?_eq_some`** and **`modalAndOf?_eq_some`** to `main`
verbatim. That is unsafe — **those two lemma statements are false against current `main`.**

## The finding: `27d93e2d` predates task 441 (native `and`/`or` constructors)

Evidence (verified this session):

- `git merge-base 27d93e2d main` = `83e232b8` ("vet: … fix tasks 384-395", 2026-06-28
  06:19), and `27d93e2d` was authored 2026-06-28 07:16 — **before** task 441 landed.
- On the **299 branch**, `Defs.lean` still uses the Łukasiewicz encoding:
  ```
  def modalOrOf? (φ) := match φ with | .imp (.imp a .bot) b => some (a, b) | _ => none
  ```
  and the branch header literally reads "Łukasiewicz decomposition functions … `φ ∨ ψ := ¬φ → ψ`".
- On **`main`**, task 441 rewrote these (`Cslib/Logics/Modal/Tableau/Defs.lean:33` design note;
  `Modal/Basic.lean:80,82` — `Proposition` now has **native** `| and` and `| or` constructors):
  ```
  def modalOrOf? (φ) := match φ with | .or a b => some (a, b) | _ => none
  def modalAndOf? (φ) := match φ with | .and a b => some (a, b) | _ => none
  ```

Consequence for the two branch lemmas:

| 299-branch lemma | Concludes (Łukasiewicz) | Truth on `main` |
|---|---|---|
| `modalOrOf?_eq_some` | `φ = .imp (.imp a .bot) b` | **FALSE** — must be `φ = .or a b` |
| `modalAndOf?_eq_some` | `φ = .imp (.imp a (.imp b .bot)) .bot` | **FALSE** — must be `φ = .and a b` |

The other two are **encoding-stable** and port as report `01` states:

| 299-branch lemma | Concludes | Truth on `main` |
|---|---|---|
| `modalNegOf?_eq_some` | `φ = .imp ψ .bot` | OK (negation still derived `imp _ bot`, `Defs.lean:138`) |
| `modalImpOf?_eq_some` | `φ = .imp a b` | OK (imp still native, `Defs.lean:192`) |

## Corrected salvage guidance (amends report 01 Phase A/B)

1. **Restate, do not cherry-pick, the `or`/`and` characterizations.** Author fresh:
   ```lean
   lemma modalOrOf?_eq_some  {φ a b} (h : modalOrOf? φ = some (a, b)) : φ = .or a b := by
     unfold modalOrOf? at h; split at h <;> simp_all
   lemma modalAndOf?_eq_some {φ a b} (h : modalAndOf? φ = some (a, b)) : φ = .and a b := by
     unfold modalAndOf? at h; split at h <;> simp_all
   ```
   (Same `unfold; split; simp_all` idiom; against native constructors these are as short as the
   `neg` case, likely shorter than the branch's `imp` proof.)
2. **`modalNegOf?_eq_some` / `modalImpOf?_eq_some` port cleanly** (report `01` items 4, part of 5).
   Re-derive `modalImpOf?_eq_some` fresh — the branch's nested-`split` proof (lines 202–213) may
   collapse on `main`.
3. **`applyPropRule_sat` / `tryAllPropRules_sat` are a template, not a copy.** Their statements
   are acc-free and portable, but their proofs `rw [modalOrOf?_eq_some hd]` /
   `rw [modalAndOf?_eq_some hd]` (branch lines 233,253,277,301) assume the Łukasiewicz shape.
   When ported, the `and`/`or` case-arms must consume the **restated** characterizations and the
   native constructors; the `imp`/`neg` arms transfer directly. `tryAllPropRules_sat` (branch
   `:388`) is a thin wrapper over `applyPropRule_sat` and ports once the latter is reworked.
4. **`sfSat`, `sfSat_pos`, `sfSat_neg`, `RuleResultSat` are encoding-independent** — port
   verbatim (report `01` items 1–3 unchanged).

## Two further corrections to report 01

- **`Proposition.beqToEq` — do not copy (report 01 item 9 said "check … likely redundant").**
  Confirmed: `main`'s `SoundnessStep.lean:83` already has the strictly-better one-liner
  `fun _ _ h => LawfulBEq.eq_of_beq h` (post-441 `Proposition` derives `DecidableEq` ⟹ generic
  `LawfulBEq`). The branch's verbose structural version (and its docstring claim that `LawfulBEq`
  is not auto-generated) is **stale**. **No salvage.**
- **`branchSatisfiable` already exists on `main`** at `SoundnessStep.lean:63` (with `Type*`), not
  only "its own `.{v,u}`" — and `modalClosed_unsat` is already present and current at
  `SoundnessStep.lean:92`. Neither needs salvage. The **`Type` vs `Type*`** point: `main`'s
  completeness loop instantiates `branchSatisfiable.{v, u}` explicitly (`Soundness.lean:174,205…`),
  so the branch's monomorphic `{W : Type}` convention is a **conditional** win for the portable
  block only — safe to adopt on `sfSat`/`RuleResultSat`/`applyPropRule_sat` (report `01` Phase B),
  but do **not** downgrade a shared `branchSatisfiable` to `Type 0` without a completeness rebuild
  check.

## Net recommendation

Report `01`'s Phases A–C remain the right shape, amended as: **Phase A adds four recognizer
`*_eq_some` lemmas, but `or`/`and` are written fresh against native `.or`/`.and` (not
cherry-picked); Phase B ports the `sfSat`/`RuleResultSat`/`applyPropRule_sat` block with `and`/`or`
proof-arms reworked; drop `Proposition.beqToEq` entirely.** No `sorry`/axiom is needed anywhere;
every item is a complete proof or a mechanical restatement. Zero-debt compliant.

The recognizer reverse-characterizations remain the highest-value, friction-relieving salvage —
the correction here only ensures the `or`/`and` two are stated *truthfully* for post-441 `main`.
