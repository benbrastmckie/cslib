# Implementation Plan: Task #428

- **Task**: 428 - expose_buchicongruence_eqvcls_monoid_and_idempotent_lemmas
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/241_mcnaughton_theorem/reports/02_spawn-analysis.md
- **Artifacts**: plans/01_buchi-monoid-idempotent-lemmas.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Expose the multiplicative (monoid) structure on the Büchi-congruence quotient
`Quotient na.BuchiCongruence.eq` and the algebraic lemmas that task 429 (Ramsey
recurrent-class lemma) and ultimately task 241 (`buchiCongr_DMA_language_eq`)
depend on. The work has two layers: (1) **establish** the `Mul`/`One`/`Monoid`
instance on the quotient together with the canonical rewrite
`⟦u ++ v⟧ = ⟦u⟧ * ⟦v⟧`; (2) **prove** the generic idempotent-power collapse
lemma (`b * b = b → b ^ k = b` for `k ≥ 1`) and the absorption corollary
(`b * b = b → a * b = a → a * b ^ k = a`). All edits land in
`Cslib/Computability/Languages/Congruences/RightCongruence.lean` and/or
`BuchiCongruence.lean`. CI must pass `lake build` and `lake exe lint-style`.

### Research Integration

The spawn analysis (`specs/241_mcnaughton_theorem/reports/02_spawn-analysis.md`,
"New Task 1") specifies the three deliverables: (a) the well-definedness rewrite
`⟦u ++ v⟧ = ⟦u⟧ · ⟦v⟧`; (b) idempotent-power collapse `b ^ k = b` when
`b · b = b`; (c) the absorption corollary `a · b ^ k = a` when `b · b = b` and
`a · b = a`. It frames these as "purely algebraic ... no research-grade
difficulty."

**Correction discovered during planning** (verified by `grep` over `Cslib/`):
the multiplication the analysis presupposes does **not yet exist**. There is no
`Mul`, `One`, or `Monoid` instance on `Quotient _.eq` (or on any
`RightCongruence` quotient) anywhere in the repository. Therefore deliverable (a)
is not merely "confirming" an instance — the instance must first be **defined**.
Furthermore, `RightCongruence` (RightCongruence.lean:28-30) only carries
`right_cov : CovariantClass _ _ (fun x y => y ++ x) eq`, i.e. *right* covariance
(`a ~ b → a ++ w ~ b ++ w`). A well-defined multiplication `⟦u⟧ * ⟦v⟧ := ⟦u ++ v⟧`
additionally needs *left* covariance (`a ~ b → w ++ a ~ w ++ b`), which a generic
right congruence does **not** provide. The Büchi congruence specifically *is*
two-sided: its defining relation (BuchiCongruence.lean:36-39) is stated via
`pairLang`/`pairViaLang`, and two words with identical state-to-state transition
behavior remain interchangeable under any common prefix. So the monoid instance
must be built on `Quotient na.BuchiCongruence.eq` (proving left-covariance from
the `pairLang` characterization), not on the generic `RightCongruence` quotient.

### Prior Plan Reference

No prior plan for task 428.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap_flag not set). This task is an
infrastructure prerequisite (INFRA-1) for task 429 and the parent McNaughton
theorem effort (task 241).

## Goals & Non-Goals

**Goals**:
- Define a `Monoid` structure (`Mul`, `One`, associativity, identity laws) on
  `Quotient na.BuchiCongruence.eq` where `⟦u⟧ * ⟦v⟧ = ⟦u ++ v⟧` and `1 = ⟦[]⟧`.
- Provide a named, public rewrite lemma `⟦u ++ v⟧ = ⟦u⟧ * ⟦v⟧` (and/or its
  `Quotient.mk` spelling) usable as a simp/rw lemma by downstream proofs.
- Provide a named idempotent-power collapse lemma: `b * b = b → b ^ k = b` for
  `k ≥ 1`.
- Provide a named absorption corollary: `b * b = b → a * b = a → a * b ^ k = a`.
- CI green: `lake build` and `lake exe lint-style` (plus `lake exe
  checkInitImports`, `lake lint`).

**Non-Goals**:
- Proving the Ramsey recurrent-class lemma (that is task 429).
- Touching `buchiCongr_DMA_language_eq` or any task-241 Phase 4 proof.
- Generalizing the monoid structure to arbitrary two-sided congruences as a new
  typeclass (acceptable as a stretch in Phase 1, but not required; keep scope
  minimal unless the generic route is strictly cleaner).
- Adding `^ω` / infinite-power machinery (that already exists at the `Language`
  level via `buchiFamily`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Generic `RightCongruence` quotient lacks left-covariance, so `Mul` cannot be defined generically | H | H | Define the `Monoid` on `Quotient na.BuchiCongruence.eq` specifically; prove left-covariance from the `pairLang`/`pairViaLang` characterization (mirror the `right_cov.elim` grind in BuchiCongruence.lean:43-45). |
| Mathlib may already provide idempotent-power / `IsIdempotentElem` lemmas, leading to duplicate work | M | M | Before proving from scratch, search Mathlib for `IsIdempotentElem`, `pow_succ`, `IsIdempotentElem.pow*`; reuse if available, otherwise prove by induction on `k`. |
| Defining `Mul` via `Quotient.liftOn₂` / `Quotient.map₂` requires a `Setoid` instance resolution that conflicts with `na.BuchiCongruence.eq` not being a registered `instance` | M | M | Use explicit `Quotient.liftOn₂ _ _ (fun u v => ⟦u ++ v⟧) _` with the `eq` setoid passed explicitly, as elsewhere in the file (`Quotient.mk c.eq`); avoid relying on instance inference. |
| `Monoid` requires `npow`/`One`/associativity boilerplate that grind struggles with | M | M | Derive associativity and identity from `List.append_assoc` / `List.append_nil` / `List.nil_append` transported through `Quotient.sound`/`Quotient.ind`; let `npow` default. |
| `@[expose] public section` + linter (docBlame) requires docstrings on every new declaration | M | M | Add a docstring to every new `def`/`lemma`/`instance`; run `lake lint` and `lake exe lint-style` at phase end. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel. Phase 2 depends on Phase 1
because the idempotent/absorption lemmas are stated in terms of the `Mul`/`Monoid`
(`*`, `^`) introduced in Phase 1, and task 429 needs them usable on the quotient.

### Phase 1: Monoid structure on the BuchiCongruence quotient [COMPLETED]

**Goal**: Make `Quotient na.BuchiCongruence.eq` a `Monoid` with `⟦u⟧ * ⟦v⟧ =
⟦u ++ v⟧` and `1 = ⟦[]⟧`, and expose the canonical rewrite lemma.

**Tasks**:
- [ ] Confirm (via `lean_local_search` / reading) that no `Mul`/`Monoid`/`One`
      instance on the quotient exists, and decide placement (BuchiCongruence.lean
      is the expected home since left-covariance is BuchiCongruence-specific).
- [ ] Prove a left-covariance helper for `BuchiCongruence`: `na.BuchiCongruence.eq
      u u' → na.BuchiCongruence.eq (w ++ u) (w ++ u')` for all `w` (mirror the
      `pairLang_split`/`pairLang_append` grind used in `right_cov.elim`,
      BuchiCongruence.lean:43-45). This is the well-definedness substrate for
      multiplication in the second argument.
- [ ] Define `Mul (Quotient na.BuchiCongruence.eq)` via `Quotient.liftOn₂`
      (or `Quotient.map₂`) with `u v ↦ ⟦u ++ v⟧`; discharge the well-definedness
      obligation using right-covariance (first arg) + the left-covariance helper
      (second arg), composed through transitivity.
- [ ] Define `One (Quotient na.BuchiCongruence.eq) := ⟦[]⟧`.
- [ ] Assemble a `Monoid` instance: associativity from `List.append_assoc`,
      `one_mul`/`mul_one` from `List.nil_append`/`List.append_nil`, all transported
      via `Quotient.ind` / `Quotient.sound`. Let `npow` take its default.
- [ ] State and prove the public rewrite lemma (the (1) deliverable), e.g.
      `buchiCongruence_mk_append : (⟦u ++ v⟧ : Quotient na.BuchiCongruence.eq)
      = ⟦u⟧ * ⟦v⟧` — definitional/`rfl` once `Mul` is defined. Add `@[simp]` if it
      behaves well under the file's `set_option linter` settings.
- [ ] Add docstrings to every new declaration.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` - add the
  left-covariance helper, the `Mul`/`One`/`Monoid` instances on the quotient, and
  the `buchiCongruence_mk_append` rewrite lemma. (Preferred home: left-covariance
  is BuchiCongruence-specific.)
- `Cslib/Computability/Languages/Congruences/RightCongruence.lean` - only if a
  small generic helper (e.g. a `Quotient`-level append-lift skeleton) is cleaner
  to factor here; optional.

**Verification**:
- `lake build Cslib.Computability.Languages.Congruences.BuchiCongruence` succeeds.
- `lean_goal` confirms the `Monoid` field obligations close (no `sorry`).
- The rewrite lemma type-checks and `⟦u⟧ * ⟦v⟧` reduces to `⟦u ++ v⟧`.

---

### Phase 2: Idempotent-power collapse and absorption lemmas [COMPLETED]

**Goal**: Provide the named algebraic lemmas (2) and (3) over the monoid, plus
full CI verification.

**Tasks**:
- [ ] Search Mathlib for an existing idempotent-power result
      (`IsIdempotentElem`, `IsIdempotentElem.pow_succ`, `pow_succ`,
      `lean_leansearch "idempotent power equals self"`). Reuse if present.
- [ ] State and prove the idempotent-power collapse lemma (deliverable (2)):
      for `b : Quotient na.BuchiCongruence.eq` (or generically for any `Monoid M`
      / `b : M`), `b * b = b → ∀ k, 1 ≤ k → b ^ k = b`. Proof by induction on `k`
      using `pow_succ` and the idempotence hypothesis. Prefer the generic `Monoid`
      statement if it costs nothing and is more reusable.
- [ ] State and prove the absorption corollary (deliverable (3)):
      `b * b = b → a * b = a → ∀ k, a * b ^ k = a`. For `k = 0`, `b ^ 0 = 1` and
      `a * 1 = a`; for `k ≥ 1`, rewrite `b ^ k = b` via the collapse lemma then use
      `a * b = a`. (Confirm whether the intended statement is all `k` or `k ≥ 1`;
      the `k = 0` case also holds, so state for all `k` unless task 429 needs the
      `k ≥ 1` form — the analysis text says "for all `k`".)
- [ ] Add docstrings to every new declaration.
- [ ] Run the full CSLib CI subset and fix any lint/style issues.

**Timing**: 1.25 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` - add the
  idempotent-power collapse and absorption lemmas (alongside the monoid instance),
  or place generic-Monoid versions in `RightCongruence.lean` if stated abstractly.

**Verification**:
- `lake build` (full project) succeeds.
- `lake exe lint-style` passes (the task's explicit CI requirement).
- `lake exe checkInitImports` and `lake lint` pass.
- `lean_verify` on each new lemma reports no `sorry`/unexpected axioms.

---

## Testing & Validation

- [ ] `lake build` completes green (no errors, no `sorry`).
- [ ] `lake exe lint-style` passes (explicit task CI requirement).
- [ ] `lake exe checkInitImports` passes (both files already begin with the
      required public imports; no new file added).
- [ ] `lake lint` reports no new docBlame/defLemma/simpNF warnings on added
      declarations.
- [ ] The three deliverable lemmas exist with the names/types downstream tasks
      expect: a `⟦u ++ v⟧ = ⟦u⟧ * ⟦v⟧` rewrite, an idempotent-power collapse, and
      an absorption corollary.
- [ ] `lean_verify` shows no axiom regressions (no `sorryAx`).

## Artifacts & Outputs

- Monoid instance (`Mul`, `One`, `Monoid`) on `Quotient na.BuchiCongruence.eq`.
- Left-covariance helper lemma for `BuchiCongruence`.
- `buchiCongruence_mk_append` (or equivalently-named) rewrite lemma.
- Idempotent-power collapse lemma.
- Absorption corollary lemma.
- Updated `BuchiCongruence.lean` (and optionally `RightCongruence.lean`).

## Rollback/Contingency

- All changes are additive (new instances + lemmas); no existing declarations are
  modified. If a phase fails, `git checkout -- <file>` restores the file.
- If the `Monoid` instance proves harder than estimated (e.g. associativity grind
  blows up `maxHeartbeats`), fall back to a bare `Mul` + `One` plus standalone
  associativity/identity lemmas, and state the idempotent/absorption lemmas using
  explicit `*`/iterated-`*` rather than `^`. Mark the phase [PARTIAL] with the
  reached goal state and what is needed to finish, per cslib.md escalation.
- If left-covariance cannot be discharged by grind, fall back to an explicit proof
  unfolding `pairLang`/`pairViaLang` membership with a middle-state witness.
- Do NOT introduce vacuous definitions (`def X := True`) as placeholders — mark
  [BLOCKED] instead (per rules/cslib.md, rules/lean4.md).
