# Implementation Plan: Task #373

- **Task**: 373 - Curry-Howard Reduction Correspondence
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: Task 332 (normalization termination proof, now sorry-free)
- **Research Inputs**: specs/373_curry_howard_reduction_correspondence/reports/01_curry-howard-design.md
- **Artifacts**: plans/01_curry-howard-reduction.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib (Lean 4)
- **Lean Intent**: false

## Overview

Extend the Curry-Howard layer from a structural isomorphism (constructor-renaming
bijection between `Theory.Derivation` and `Theory.Term`) to a genuine computational
correspondence. Two deliverables: (1) a **reduction correspondence** — define a native
root reduction `Theory.Term.reduceRoot` mirroring `Derivation.reduceRoot`'s 8 redex cases
(5 proper β-redexes + 3 commuting conversions), then prove `reduceRoot_forward`:
`(curryHowardForward d).reduceRoot = d.reduceRoot.map curryHowardForward`, plus the
`_some` compatibility corollary; (2) **term-level strong normalization** — transport the
derivation-level existence theorem `Derivation.exists_stronglyNormal_form`
(`Termination.lean:1884`, from task 332) across the isomorphism to obtain
`Theory.Term.exists_stronglyNormal_form`. All new work lands in a single new file
`Cslib/Logics/Propositional/CurryHoward/Reduction.lean`. Zero new sorry, zero new axioms.

### Research Integration

This plan follows the research report's **Design B (native `Term.reduceRoot`)**
recommendation and its 4-phase structure (report "Phasing Summary"). The report
**built green** (via `lake env lean`, EXIT 0, then removed) every load-bearing
mechanism: the full 8-case `Term.reduceRoot`, `subsOne`/`weakCtx` transport definitions,
`subsOne_fwd`/`weakCtx_fwd` roundtrip lemmas, the two hardest `reduceRoot_forward` cases
(the β-redex `impE (impI _ D) E` case and the commuting `impE (orE …) E` case that
exercises `weakCtx` + `case_` reconstruction), and the entire SN-transport route. Exact
proven proof bodies are reproduced in the report and are carried into the per-phase tasks
below. Verified ground-truth names (re-confirmed against the working tree): maps are
**camelCase** `curryHowardForward`/`curryHowardBackward` (`Isomorphism.lean:54,73`);
roundtrips `curryHoward_backward_forward`/`curryHoward_forward_backward`
(`Isomorphism.lean:92,109`); `Derivation.reduceRoot` is at `Reduction.lean:66` with
exactly 8 `some` cases; `subsOne` at `Reduction.lean:45`; `weakCtx` at `Basic.lean:229`;
`isStronglyNormal` at `Basic.lean:231`; `exists_stronglyNormal_form` at
`Termination.lean:1884`. No reduction relation on `Term` exists yet — it must be created.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap_flag not set). This task advances the
Propositional-Logic Curry-Howard line: it upgrades the task-332 structural isomorphism
into a computational correspondence (reduction + strong normalization transported to the
term language), completing the proofs-as-programs picture for the propositional fragment.

## Goals & Non-Goals

**Goals**:
- Define a native `Theory.Term.reduceRoot : Term G A → Option (Term G A)` with the 8 redex
  cases mirroring `Derivation.reduceRoot` (5 proper β-redexes + 3 commuting conversions).
- Define the supporting `Theory.Term.subsOne` and `Theory.Term.weakCtx` by transport, with
  their forward-compatibility lemmas `subsOne_fwd`/`weakCtx_fwd`.
- Prove the load-bearing `reduceRoot_forward`:
  `(curryHowardForward d).reduceRoot = d.reduceRoot.map curryHowardForward`, plus
  `reduceRoot_forward_some` (the `d reduceRoot d' ⇒ curryHowardForward d reduces to
  curryHowardForward d'` compatibility lemma) and the backward dual `reduceRoot_backward`.
- Transport strong normalization: define `Theory.Term.isStronglyNormal` and prove
  `Theory.Term.exists_stronglyNormal_form (t : Term G A) : ∃ t', t'.isStronglyNormal = true`.
- Land everything in a new `Reduction.lean`, wire it into the barrel, pass full CI on the
  affected targets. No new `sorry`, no new `axiom`.

**Non-Goals**:
- A fully **native** term substitution `Term.subs` re-deriving `Basic.lean`'s `Finset`
  machinery on `Term`. The transport `subsOne`/`weakCtx` (routing through `Derivation.subs`)
  are genuine capture-avoiding operations and are sufficient (report H4 §4). Out of scope.
- Strong normalization as "every reduction sequence halts". The codebase's
  `isStronglyNormal` is a structural single-tree no-redex predicate; the SN deliverable is
  *existence of a normal form*, faithfully matching the derivation-level theorem. The plan
  states this explicitly and does not over-claim (report H4 §2).
- Modifying any existing file's proofs in `CurryHoward/{Defs,Isomorphism}.lean`,
  `NaturalDeduction/Normalization/{Reduction,Termination,Basic}.lean`. They are reused
  unchanged; the only edits outside the new file are barrel/`mk_all` wiring.
- A whole-library `lake build`. Modal/Bimodal are pre-existing red; verification builds the
  SPECIFIC affected targets only.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| One of the 6 not-yet-built `reduceRoot_forward` branches (andE1/andE2 proper + their commuting conversions) is stubborn | M | L | All 6 are strictly simpler than the 2 built cases (proper redexes are bare projections `some t₁`; conjunction commuting mirrors the proven impE/orE shape without `weakCtx`). Fallback: switch that branch (or the whole file) to **Design A** transport `reduceRoot`, where the correspondence is a single `rw [curryHoward_backward_forward]` (built green) — report "Open gap" + Phase-2 fallback |
| Dependent-type mismatch in native `reduceRoot` cases (context `G`/`Γ` args, `weakCtx (Finset.subset_insert _ _)`) | H | L | Exact 8-case body was compiled green and is reproduced verbatim in Phase 1; the worst commuting case (`weakCtx` + nested `case_`/`app`) is the one built in the report (H4 §1) |
| `subsOne`/`weakCtx` transport defs fail to elaborate at the `Term` dependent types | H | L | Both built green; bodies are `curryHowardForward ((curryHowardBackward …).subsOne/weakCtx …)`; `_fwd` lemmas discharged by `unfold; rw [curryHoward_backward_forward, …]` (built) |
| Import/`shake`/`mk_all` drift after adding a new module | M | M | Phase 4 runs `lake exe mk_all --module` for the barrel entry and `lake shake --add-public --keep-implied --keep-prefix`; header is `import Cslib.Init` + `public import …Isomorphism` + `…Normalization.Termination` |
| Lint/doc: missing module docstring, BibKey citations, `def` vs `lemma`, naming | M | M | New file carries module docstring with `[SorensenUrzyczyn2006]`/`[Prawitz1965]` (both VERIFIED in `references.bib`); every decl docstring'd; correspondence facts are `lemma`/`theorem`, reductions/`subsOne`/`weakCtx` are `def`; names lowerCamelCase under `Theory.Term` namespace |
| Accidental whole-library build corrupts the concurrent implementation worktree | H | L | NEVER run bare `lake build`; only `lake build <specific module>`; planning itself is build-free |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 1, 2, 3 |

Phases form a strict linear chain: each builds on the previous declarations landing in the
single new `Reduction.lean`. Each phase is sized to one bounded agent run (~30-130 lines of
output) ending at a build checkpoint on the specific affected target. No two phases run in
parallel.

### Sorry / Axiom Invariant (MUST hold at every commit)

Net real `sorry` and `axiom` tokens introduced by this task = **0**. The new file
`Reduction.lean` must never contain a `sorry` or `axiom` at any committed state. All
mechanisms were built green in research; if any branch resists, use the Design A fallback
(report) rather than introducing a sorry. Verification command at each commit gate:

```bash
f="Cslib/Logics/Propositional/CurryHoward/Reduction.lean"
grep -nE '(^|[^[:alnum:]_])(sorry|axiom)([^[:alnum:]_]|$)' "$f" \
  | grep -vE ':[0-9]+:\s*(--|/-|\*)'
# must return NOTHING (zero matches) at every commit
```

---

### Phase 1: Term substitution, weakening, and native `reduceRoot` [NOT STARTED]

**Goal**: Create `Reduction.lean` with the transport-defined `Term.subsOne`/`Term.weakCtx`,
their forward lemmas `subsOne_fwd`/`weakCtx_fwd`, and the native 8-case `Term.reduceRoot`.
Fully green, zero sorry. (~80 lines; all built green in research.)

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/CurryHoward/Reduction.lean` with header
      `module` + `import Cslib.Init` + `public import Cslib.Logics.Propositional.CurryHoward.Isomorphism`
      + `public import Cslib.Logics.Propositional.NaturalDeduction.Normalization.Termination`
      (the latter transitively provides `Derivation.reduceRoot`, `subsOne`, `weakCtx`,
      `isStronglyNormal`, `exists_stronglyNormal_form`). Module docstring citing
      `[SorensenUrzyczyn2006]` §2.2 and `[Prawitz1965]` Ch. III–IV.
- [ ] Define `Theory.Term.subsOne (t : Term (insert A Γ) B) (s : Term Γ A) : Term Γ B :=`
      `curryHowardForward ((curryHowardBackward t).subsOne (curryHowardBackward s))`.
- [ ] Define `Theory.Term.weakCtx (t : Term Γ A) (h : Γ ⊆ Δ) : Term Δ A :=`
      `curryHowardForward ((curryHowardBackward t).weakCtx h)`.
- [ ] Prove `subsOne_fwd (D E) : curryHowardForward (D.subsOne E) =`
      `(curryHowardForward D).subsOne (curryHowardForward E)` by
      `unfold Term.subsOne; rw [curryHoward_backward_forward, curryHoward_backward_forward]`.
- [ ] Prove `weakCtx_fwd (D h) : curryHowardForward (D.weakCtx h) =`
      `(curryHowardForward D).weakCtx h` by
      `unfold Term.weakCtx; rw [curryHoward_backward_forward]`.
- [ ] Define `Theory.Term.reduceRoot : Term (T:=T) G A → Option (Term (T:=T) G A)` with the
      exact 8-case body from the report (constructor map
      `impI↦lam, impE↦app, andI↦pair, andE1↦fst, andE2↦snd, orI1↦inl, orI2↦inr, orE↦case_`):
      `app (lam _ t) s ↦ some (t.subsOne s)`; `fst _ (pair _ t₁ _) ↦ some t₁`;
      `snd _ (pair _ _ t₂) ↦ some t₂`; `case_ _ (inl _ t) tA _ ↦ some (tA.subsOne t)`;
      `case_ _ (inr _ t) _ tB ↦ some (tB.subsOne t)`;
      `fst G (case_ _ t tA tB) ↦ some (case_ G t (fst _ tA) (fst _ tB))`;
      `snd G (case_ _ t tA tB) ↦ some (case_ G t (snd _ tA) (snd _ tB))`;
      `app (case_ G t tA tB) s ↦ some (case_ G t (app tA (s.weakCtx (Finset.subset_insert _ _)))`
      `(app tB (s.weakCtx (Finset.subset_insert _ _))))`; `_ ↦ none`.
- [ ] Docstrings on every decl; `def` for `subsOne`/`weakCtx`/`reduceRoot`, `theorem`/`lemma`
      for `subsOne_fwd`/`weakCtx_fwd`; lowerCamelCase under the `Theory.Term` namespace.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/CurryHoward/Reduction.lean` - NEW: `subsOne`, `weakCtx`,
  `subsOne_fwd`, `weakCtx_fwd`, `reduceRoot`.

**Build state / staging**: GREEN. Only a new file with definitions + two roundtrip lemmas;
no existing declaration touched.

**Verification**:
- `lake build Cslib.Logics.Propositional.CurryHoward.Reduction` succeeds.
- Sorry/axiom invariant sweep returns nothing.

---

### Phase 2: Forward reduction correspondence [NOT STARTED]

**Goal**: Prove the load-bearing `reduceRoot_forward` and its `_some` compatibility
corollary. End state: full correspondence, zero sorry. (~130 lines; 2/8 hardest cases built
green in research, 6 strictly simpler.)

**Tasks**:
- [ ] Prove `Theory.reduceRoot_forward (d : Derivation G A) :`
      `(curryHowardForward d).reduceRoot = d.reduceRoot.map curryHowardForward`. Proof shape:
      `cases d` (10 constructors), then nested `cases` on the eliminated subderivation
      mirroring `Derivation.reduceRoot`'s match. Each redex case discharged by
      `simp only [Term.reduceRoot, Derivation.reduceRoot, curryHowardForward, Option.map_some,`
      `subsOne_fwd, weakCtx_fwd]`; each non-redex shape gives `none.map _ = none` by `rfl`/`simp`.
      - β-redex case (`impE (impI _ D) E`): reduces to `subsOne_fwd` (built green).
      - commuting case (`impE (orE G D DA DB) E`): `simp only [curryHowardForward, weakCtx_fwd]`,
        exercising `weakCtx` + `case_` reconstruction (built green).
      - remaining 6 (`andE1`/`andE2` proper redexes `some t₁`/`some t₂`; `andE1`/`andE2` over
        `case_` commuting conversions; `orE` left/right proper) are strictly simpler — proper
        redexes are bare projections, conjunction commuting mirrors the proven impE/orE shape
        without `weakCtx`.
- [ ] Prove `Theory.reduceRoot_forward_some (d d') (h : d.reduceRoot = some d') :`
      `(curryHowardForward d).reduceRoot = some (curryHowardForward d')` (the
      `d reduceRoot d' ⇒ curryHowardForward d reduces to curryHowardForward d'` compatibility
      lemma) by `rw [reduceRoot_forward, h, Option.map_some]` (built green).
- [ ] `theorem`/`lemma` keywords; docstrings citing `[SorensenUrzyczyn2006]` §2.2.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/CurryHoward/Reduction.lean` - add `reduceRoot_forward`,
  `reduceRoot_forward_some`.

**Build state / staging**: GREEN. **Fallback** (report "Open gap"): if any of the 6 simpler
branches resists, switch that branch — or, worst case, the whole file — to **Design A**
(transport `reduceRoot := (curryHowardBackward t).reduceRoot.map curryHowardForward`), where
the correspondence is a single `rw [curryHoward_backward_forward]` (built green). Never add a
`sorry`.

**Verification**:
- `lake build Cslib.Logics.Propositional.CurryHoward.Reduction` — `reduceRoot_forward` and
  `reduceRoot_forward_some` elaborate, all 8 cases discharged.
- Sorry/axiom invariant sweep returns nothing.

---

### Phase 3: Backward congruence + term strong normalization [NOT STARTED]

**Goal**: Add the backward dual `reduceRoot_backward`, define `Term.isStronglyNormal`, and
prove the SN deliverable `Term.exists_stronglyNormal_form`. (~60 lines; all built green.)

**Tasks**:
- [ ] Prove `Theory.reduceRoot_backward (t : Term G A) :`
      `(curryHowardBackward t).reduceRoot = (t.reduceRoot).map curryHowardBackward` — the dual
      of Phase 2 via `curryHoward_forward_backward` (Design A form built green; Design B form
      is the inverse case split mirroring `reduceRoot_forward`).
- [ ] Define `Theory.Term.isStronglyNormal (t : Term G A) : Bool :=`
      `(curryHowardBackward t).isStronglyNormal`.
- [ ] Prove the SN deliverable
      `Theory.Term.exists_stronglyNormal_form (t : Term G A) : ∃ t', t'.isStronglyNormal = true`
      with the built-green body:
      `obtain ⟨d', hd'⟩ := (curryHowardBackward t).exists_stronglyNormal_form;`
      `refine ⟨curryHowardForward d', ?_⟩;`
      `unfold Theory.Term.isStronglyNormal; rw [curryHoward_backward_forward]; exact hd'`.
- [ ] OPTIONAL strengthening: `isStronglyNormal_fwd (d) :`
      `(curryHowardForward d).isStronglyNormal = d.isStronglyNormal` (roundtrip), so the SN
      witness can be stated directly over the iso.
- [ ] Docstrings citing `[Prawitz1965]` Ch. IV; note explicitly that this is existence of a
      normal form (single-tree predicate), not termination of all reduction sequences.

**Timing**: 1 hour

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/CurryHoward/Reduction.lean` - add `reduceRoot_backward`,
  `Term.isStronglyNormal`, `Term.exists_stronglyNormal_form`, optional `isStronglyNormal_fwd`.

**Build state / staging**: GREEN. All bodies built green in research.

**Verification**:
- `lake build Cslib.Logics.Propositional.CurryHoward.Reduction` — `exists_stronglyNormal_form`
  elaborates with no sorry/axiom.
- Sorry/axiom invariant sweep returns nothing.

---

### Phase 4: File wiring + CI [NOT STARTED]

**Goal**: Register the new module in the barrel and pass the CI pipeline on the affected
targets. (~30 lines + CI; mechanical.)

**Tasks**:
- [ ] Run `lake exe mk_all --module` so `Reduction.lean` is added to the `Cslib.lean` barrel
      (or hand-edit the relevant aggregator if `mk_all` is unavailable).
- [ ] `lake build Cslib.Logics.Propositional.CurryHoward.Reduction` (the affected target).
- [ ] `lake exe checkInitImports` (new file imports `Cslib.Init`).
- [ ] `lake exe lint-style` and `lake lint` (docstrings on every decl + module; lowerCamelCase;
      `def`/`lemma`/`theorem` correct).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (fix import-graph minimization for
      the new module's `public import`s).
- [ ] `lake test` (CslibTests).
- [ ] Final axiom check: `lean_verify` (or `#print axioms`) on
      `Theory.Term.exists_stronglyNormal_form` and `Theory.reduceRoot_forward` confirms no new
      axioms beyond those already used by task 332's `exists_stronglyNormal_form`.

**Timing**: 1 hour

**Depends on**: 1, 2, 3

**Files to modify**:
- `Cslib.lean` (or the barrel aggregator) - add `import …CurryHoward.Reduction` via `mk_all`.

**Build state / staging**: GREEN. Mechanical wiring + CI. Do NOT run a bare whole-library
`lake build` (Modal/Bimodal pre-existing red, and a concurrent worktree build must not be
corrupted) — build the specific `CurryHoward.Reduction` target.

**Verification**:
- `lake build Cslib.Logics.Propositional.CurryHoward.Reduction` green.
- `lake exe checkInitImports`, `lake exe lint-style`, `lake lint`,
  `lake shake --add-public --keep-implied --keep-prefix`, `lake test` all pass.
- `#print axioms`/`lean_verify` shows no new axioms.
- Sorry/axiom invariant sweep over `Reduction.lean` returns nothing.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.CurryHoward.Reduction` succeeds (specific target,
      not whole library).
- [ ] `lake exe checkInitImports` passes (Reduction.lean imports `Cslib.Init`).
- [ ] `lake exe lint-style` and `lake lint` pass (module + per-decl docstrings; naming).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (import graph for the new
      module's `public import`s).
- [ ] `lake test` (CslibTests) passes.
- [ ] No new axioms: `#print axioms Theory.Term.exists_stronglyNormal_form` and
      `Theory.reduceRoot_forward` show only the axioms already in task 332's transitive base.
- [ ] Sorry/axiom token sweep over `Reduction.lean` returns exactly **0** matches.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/CurryHoward/Reduction.lean` (NEW): `Term.subsOne`,
  `Term.weakCtx`, `subsOne_fwd`, `weakCtx_fwd`, native `Term.reduceRoot` (8 cases),
  `reduceRoot_forward`, `reduceRoot_forward_some` (compatibility lemma), `reduceRoot_backward`,
  `Term.isStronglyNormal`, `Term.exists_stronglyNormal_form` (the SN deliverable), optional
  `isStronglyNormal_fwd`.
- Barrel/`Cslib.lean` updated to import the new module.
- ~250-300 lines of new Lean code; reduction correspondence + term-level SN, zero new sorry,
  zero new axioms.

## Rollback/Contingency

- All work is additive in a single new file; no existing declaration is modified (except
  barrel wiring in Phase 4). If any phase fails, revert that phase's commit; the existing
  CurryHoward isomorphism and Normalization tree remain green and unchanged.
- If any of the 6 simpler `reduceRoot_forward` branches (Phase 2) proves stubborn, switch
  that branch — or the whole file — to **Design A** (transport `reduceRoot`), where the
  correspondence collapses to a single `rw [curryHoward_backward_forward]` (built green in
  research). This trades fidelity for a guaranteed-green proof; never introduce a `sorry`.
- If `shake`/`mk_all` import minimization (Phase 4) is intractable, keep the `public import`s
  explicit and adjust the barrel by hand; the proofs themselves are unaffected.
