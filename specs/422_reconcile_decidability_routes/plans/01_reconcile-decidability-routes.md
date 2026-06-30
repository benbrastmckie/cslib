# Implementation Plan: Reconcile Parallel Int/Min Decidability Routes (Tableau vs FMP)

- **Task**: 422 - Reconcile parallel Int/Min decidability routes (tableau vs FMP): canonical instance, docstrings, infrastructure
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: 411 (Int FMP on main), 421 (Min FMP on main); coordinates with 317 (tableau sorry closure, out of scope here)
- **Research Inputs**: specs/422_reconcile_decidability_routes/reports/01_reconcile-decidability-routes.md
- **Artifacts**: plans/01_reconcile-decidability-routes.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

CSLib's `main` branch carries two registered `Decidable` instances for each of
`Derivable IntPropAxiom φ` and `Derivable MinPropAxiom φ`: a computable **tableau** `instance`
(`Tableau/{Intuitionistic,Minimal}/DecisionProcedure.lean`) and a `noncomputable instance`
**FMP** declaration (`Metalogic/{Int,Min}Decidability.lean`). All four live in namespace
`Cslib.Logic.PL` and are imported by the `Cslib.lean` barrel, producing a latent
instance-resolution ambiguity. The fix is a low-risk demotion-plus-documentation pass: keep the
tableau instances as the sole canonical extension-facing `Decidable` instances, demote the two
FMP instances to named `noncomputable def`s, and add cross-referencing "two routes, distinct
roles" docstrings to all four module headers. **Definition of done**: exactly one registered
`Decidable` instance per proposition class (the tableau one); FMP results available by name as
`noncomputable def`s; all four headers carry mutually cross-referenced docstrings; zero new
sorries or axioms; full CSLib CI green; extensions still build.

### Research Integration

Integrates `reports/01_reconcile-decidability-routes.md` in full. Key findings encoded:
- **Hazard confirmed, but latent**: no consumer (named, `inferInstance`, or `decide`) of either
  conflicting `Decidable` head exists anywhere in `Cslib/` or `CslibTests/`. The
  modal/temporal/bimodal extensions import `Propositional.Embedding → Defs` only — they do not
  touch these instances. Demoting the FMP instances therefore cannot break the extensions; the
  resolution change is a functional no-op confirmed by build, not just reasoning.
- **Idiomatic fix**: register exactly one `instance` per head; expose the other result as a named
  non-instance. Instance-priority annotations are **not** idiomatic here (the repo's only 3 uses
  are all `priority := 100` for typeclass-hierarchy diamonds, never for duplicate `Decidable`
  proofs) and are explicitly avoided.
- **Canonical = TABLEAU** (standing user decision, not re-litigated here): the tableau instances
  are computable, so `decide`/`inferInstance` resolve to them, and they feed the logic
  extensions. The FMP route is a distinct theoretical result accessed by name.
- **Naming/lint**: `Decidable` is data (not `Prop`), so the demoted declarations stay `def` (not
  `lemma`/`theorem`). The `defsWithUnderscore` lint forbids underscores in `def` names, so the
  `_fmp` suffix is forbidden — use camelCase `…FMP`. The headline theorems `int_fmp`/`min_fmp`
  already exist and need no rename.
- **Pre-existing 317 caveat**: the canonical tableau route is sorry-tainted by task 317
  (`Scheme.lean:246`, `Scheme.lean:519`, `Completeness.lean:113`, `Minimal/Completeness.lean:110`)
  while the FMP route is sorry-free (axioms `{propext, Classical.choice, Quot.sound}`). This is
  pre-existing 317 debt, **not** introduced by 422, and must be documented prominently.
- **Infrastructure factoring: DEFER**. FMP `IntFinWorld`/`MinFinWorld` (Finset-carrier Σ-bounded
  prime worlds resting on the `IntLindenbaum` substrate) and the tableau signed-branch machinery
  have disjoint carriers; the tableau route does not use Lindenbaum. Document and cross-reference
  the relationship (`int_fin_truth_lemma`/`min_fin_truth_lemma` vs parametric `truthLemma`); do
  NOT refactor.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided to this dispatch; no ROADMAP.md consulted. Task topic is
`PL-Metalogic`; this plan completes the post-411/421 reconciliation pass for both Int and Min in
a single coherent change.

## Goals & Non-Goals

**Goals**:
- Register exactly one canonical `Decidable` instance per proposition class — the tableau
  `instDecidableDerivableIntPropAxiom` and `instDecidableDerivableMinPropAxiom` — eliminating the
  resolution ambiguity.
- Demote the two FMP instances to `noncomputable def decidableDerivableIntPropAxiomFMP` /
  `decidableDerivableMinPropAxiomFMP` (camelCase, lint-clean), preserving the FMP decision
  procedure by name without registering a competing instance.
- Add a mutually cross-referencing "two routes, distinct roles" docstring to all four module
  headers, citing the 317 sorry obligations and the FMP axiom profile.
- Add infrastructure cross-reference docstrings linking the two truth lemmas and the shared
  Lindenbaum substrate, recording the explicit "factoring deferred" decision.
- Keep full CSLib CI green and the extensions building, with zero new sorries/axioms.

**Non-Goals**:
- Closing or touching any task-317 tableau sorries (out of scope; the canonical instance's
  sorry-taint is pre-existing and documented, not introduced here).
- Refactoring or factoring a shared truth-lemma / world-type abstraction between the FMP and
  tableau subsystems (explicitly deferred — high risk, low payoff, blocked behind open 317).
- Renaming the headline theorems `int_fmp` / `min_fmp` (already well-named).
- Using `instance (priority := …)` to disambiguate (not idiomatic for duplicate `Decidable`
  proofs in this repo).
- Changing the tableau instances' names (already well-named, no prime).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A hidden consumer of a demoted FMP instance breaks on demotion | M | L | Phase 1 greps for `inferInstance`/`decide`/named use of both primed symbols and both heads across `Cslib/` and `CslibTests/` BEFORE editing; build-verify gate confirms no breakage. Research already found zero consumers. |
| New `def` names trip the `defsWithUnderscore` or `docBlame` lint | M | M | Use camelCase `…FMP` (no underscore); add a docstring to each new `def`. Phase 4 runs `lake exe lint-style` and `lake lint` explicitly watching these. |
| Editing tableau headers duplicates the existing "Notes on sorry" section | L | M | Extend the existing 317 sorry notes rather than duplicate; read each header before editing. |
| Accidental introduction of a sorry/axiom or removal of an FMP result | H | L | Phase 4 runs `lean_verify`/`#print axioms` on the demoted FMP defs (expect `{propext, Classical.choice, Quot.sound}`, no `sorryAx`) and on the canonical tableau instance (expect `sorryAx` until 317 — documents caveat); full-repo `grep sorry` diff confirms zero new sorries. |
| Instance resolution silently still ambiguous after edit | M | L | Phase 1 confirms via `lake build` that the barrel resolves the tableau instance unambiguously (no competing `instance` remains for either head). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Demote + rename the two FMP instances to `noncomputable def …FMP` [COMPLETED]

**Goal**: Eliminate the resolution ambiguity by demoting both FMP `noncomputable instance`s to
named `noncomputable def`s (camelCase `…FMP`), leaving the tableau instances as the sole
registered `Decidable` instances. No behavioral change expected (no consumers).

**Tasks**:
- [ ] Grep first (verification precondition): search `Cslib/` and `CslibTests/` for any reference
      to `instDecidableDerivableIntPropAxiom'`, `instDecidableDerivableMinPropAxiom'`, and for
      `inferInstance` / `by decide` / named term-level use against
      `Decidable (Derivable IntPropAxiom …)` and `Decidable (Derivable MinPropAxiom …)`. Confirm
      zero hits (research expects none); record findings.
- [ ] `Metalogic/IntDecidability.lean:430`: change
      `noncomputable instance instDecidableDerivableIntPropAxiom'` →
      `noncomputable def decidableDerivableIntPropAxiomFMP`.
- [ ] `Metalogic/MinDecidability.lean:382`: change
      `noncomputable instance instDecidableDerivableMinPropAxiom'` →
      `noncomputable def decidableDerivableMinPropAxiomFMP`.
- [ ] Update the in-file "Main Results" list / docstring references (e.g. around
      `IntDecidability.lean:29`) to reflect the new `def` names.
- [ ] Ensure each demoted `def` carries a one-line docstring (avoids `docBlame`; sets up Phase 2).
- [ ] `lake build` green; confirm the barrel now resolves the tableau instance unambiguously for
      both heads (no competing registered `instance`).

**Timing**: ~45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/.../Metalogic/IntDecidability.lean` - demote+rename Int FMP instance; update Main Results list.
- `Cslib/.../Metalogic/MinDecidability.lean` - demote+rename Min FMP instance; update Main Results list.

**Verification**:
- Pre-edit grep returns no consumer of the primed symbols or the two heads.
- `lake build` green.
- Exactly one registered `instance` remains per head (the tableau one); the FMP results are
  reachable by their new `def` names.
- CSLib CI pipeline green: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`.

---

### Phase 2: "Two routes, distinct roles" docstrings across all four module headers [COMPLETED]

**Goal**: Add a mutually cross-referencing docstring block to all four module headers describing
the two independent decision routes, their distinct roles, the 317 sorry citations, and the FMP
axiom profile.

**Tasks**:
- [ ] In each of the four headers, document: (1) the **tableau route**
      (`Tableau/{Intuitionistic,Minimal}/DecisionProcedure.lean`) — constructive signed-tableau
      proof-search/countermodel procedure, computable, the canonical extension-facing `instance`,
      genuinely sorry-free only once task 317 lands; and (2) the **FMP route**
      (`Metalogic/{Int,Min}Decidability.lean`) — finite model property via the finite canonical
      Kripke model, sorry-free (`{propext, Classical.choice, Quot.sound}`), exposed as theorems
      `int_fmp`/`min_fmp` and the `noncomputable def decidableDerivable…PropAxiomFMP`.
- [ ] Each header cross-references the other route's module and declaration name, and states the
      role split (constructive/extension-facing vs theoretical/finite-model-property).
- [ ] Cite the open 317 obligations in the tableau-route narrative: `Scheme.lean:246` (parametric
      `truthLemma`), `Scheme.lean:519` (open-branch countermodel structural),
      `Completeness.lean:113` (`IValid → forcing` bridge), `Minimal/Completeness.lean:110`
      (`MValid → forcing` bridge; Minimal reuses the shared parametric `truthLemma minScheme`, so
      it also depends on `Scheme.lean:246`).
- [ ] For the tableau headers, **extend** the existing "Notes on sorry" section citing 317 rather
      than duplicating it.

**Timing**: ~45 minutes

**Depends on**: 1 (the FMP headers must reference the demoted `def` names introduced in Phase 1).

**Files to modify**:
- `Cslib/.../Metalogic/IntDecidability.lean` - header docstring.
- `Cslib/.../Metalogic/MinDecidability.lean` - header docstring.
- `Cslib/.../Tableau/Intuitionistic/DecisionProcedure.lean` - header docstring (extend existing sorry notes).
- `Cslib/.../Tableau/Minimal/DecisionProcedure.lean` - header docstring (extend existing sorry notes).

**Verification**:
- All four headers carry the two-routes narrative with mutual cross-references and correct
  declaration names.
- The 317 sorry citations and FMP axiom profile appear in the relevant headers.
- `lake build` green; `lake exe lint-style` clean.

---

### Phase 3: Infrastructure cross-reference docstrings (factoring deferred) [COMPLETED]

**Goal**: Document the relationship between the FMP and tableau infrastructure without
refactoring, and record the explicit "factoring deferred" decision.

**Tasks**:
- [ ] Add cross-reference docstrings linking the two truth lemmas: `int_fin_truth_lemma`
      (`IntDecidability.lean:275`) / `min_fin_truth_lemma` (`MinDecidability.lean:240`) (FMP,
      sorry-free, structural induction over a fixed finite world) ↔ the parametric
      `truthLemma S b …` (`Scheme.lean:232`, tableau, 317-owned sorry). State that they prove
      analogous "forcing ↔ membership" statements over disjoint carrier types with opposite
      completion status.
- [ ] Note the shared substrate: the FMP route rests on the `IntLindenbaum.lean` machinery
      (`int_imp_witness`, `int_prime_exclusion`, `intDeductiveClosure`, and Min analogues),
      reused to build the finite world by restriction to Σ; the tableau route does not use
      Lindenbaum and is an independent subsystem (signed tableaux + branch saturation).
- [ ] Record the explicit decision: factoring a common truth-lemma/world abstraction is
      **deferred** (research-or-defer outcome: defer) — it would couple two independently
      developed subsystems across a carrier mismatch and thread through the still-open 317
      parametric lemma; high risk, low payoff.

**Timing**: ~30 minutes

**Depends on**: 1 (shares the FMP module files; sequence after the demotion to avoid edit churn).
Can run in parallel with Phase 2 (different docstring regions, but same files — see note).

**Files to modify**:
- `Cslib/.../Metalogic/IntDecidability.lean` - truth-lemma + substrate cross-reference notes.
- `Cslib/.../Metalogic/MinDecidability.lean` - truth-lemma + substrate cross-reference notes.
- `Cslib/.../Tableau/Intuitionistic/Scheme.lean` - parametric `truthLemma` cross-reference note (optional, light touch).

**Verification**:
- Cross-reference docstrings link the truth lemmas and name the shared Lindenbaum substrate.
- The "factoring deferred" decision is recorded in-source.
- `lake build` green; `lake exe lint-style` clean.

**Note on parallelism**: Phases 2 and 3 both touch `Int/MinDecidability.lean`. If executed by
separate parallel agents, assign Phase 2 the header region and Phase 3 the truth-lemma region of
those two files, or serialize 2 → 3. The wave table groups them in Wave 2 for ordering relative
to Phase 1; coordinate file regions to avoid conflicts.

---

### Phase 4: Full CI + axiom verification [NOT STARTED]

**Goal**: Verify zero new sorries/axioms, the FMP/tableau axiom profiles, and full CSLib CI
green, including the extensions.

**Tasks**:
- [ ] Run the full CSLib CI pipeline: `lake build`; `lake test`; `lake exe checkInitImports`;
      `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix`; `lake lint`
      (watch `defsWithUnderscore` on the new `def` names and `docBlame` on any new decl).
- [ ] `lean_verify` / `#print axioms decidableDerivableIntPropAxiomFMP` and
      `decidableDerivableMinPropAxiomFMP`: expect `{propext, Classical.choice, Quot.sound}`, no
      `sorryAx`.
- [ ] `lean_verify` / `#print axioms` on the canonical tableau instances
      (`instDecidableDerivableIntPropAxiom`, `instDecidableDerivableMinPropAxiom`): expect
      `sorryAx` present until 317 — this documents the pre-existing caveat (not a regression).
- [ ] Full-repo `grep sorry` diff vs `main` confirms zero new sorries introduced by 422.
- [ ] Confirm the modal/temporal/bimodal extensions still build (they import
      `Propositional.Embedding → Defs` only; whole-repo `lake build` covers this).

**Timing**: ~30 minutes

**Depends on**: 2, 3

**Files to modify**: none (verification only; fix-forward into the relevant phase's files if a
gate fails).

**Verification**:
- Full CI pipeline green.
- FMP defs axiom-clean (`{propext, Classical.choice, Quot.sound}`, no `sorryAx`); tableau
  instances carry only the pre-existing 317 `sorryAx`.
- Zero new sorries (grep diff); extensions build.

## Testing & Validation

- [ ] `lake build` green (whole repo, including extensions).
- [ ] `lake test` green (CslibTests suite).
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` green.
- [ ] `lake lint` clean — specifically `defsWithUnderscore` on the new `def` names and `docBlame`
      on new declarations.
- [ ] `#print axioms` on the two FMP defs returns `{propext, Classical.choice, Quot.sound}` with
      no `sorryAx`.
- [ ] `#print axioms` on the two tableau instances returns only the pre-existing 317 `sorryAx`
      (documented caveat, not a regression).
- [ ] Pre-edit grep (Phase 1) confirmed no consumer of the demoted symbols/heads.
- [ ] Exactly one registered `Decidable` instance per Int and Min proposition (the tableau ones).
- [ ] All four module headers carry mutually cross-referenced two-routes docstrings.

## Artifacts & Outputs

- `plans/01_reconcile-decidability-routes.md` (this file)
- Modified: `Metalogic/IntDecidability.lean`, `Metalogic/MinDecidability.lean`,
  `Tableau/Intuitionistic/DecisionProcedure.lean`, `Tableau/Minimal/DecisionProcedure.lean`
  (and optionally `Tableau/Intuitionistic/Scheme.lean` for a light cross-reference note).
- `summaries/01_reconcile-decidability-routes-summary.md` (on implementation completion).

## Rollback/Contingency

- All changes are small, localized edits (two `instance`→`def` demotions plus docstrings).
  Revert via `git checkout` of the four modified files if any CI gate cannot be satisfied.
- If a hidden consumer of a demoted FMP instance is discovered in Phase 1 (contrary to research),
  do not proceed with demotion: instead record the consumer, and reconsider whether that consumer
  should be re-pointed at the named `def` or whether the FMP route should remain an instance —
  escalate the canonical decision rather than silently breaking resolution.
- If the FMP defs unexpectedly fail the axiom check (gain a `sorryAx`), halt: this would indicate
  an accidental regression; investigate before completing.
- Factoring infrastructure is explicitly out of scope; any temptation to refactor mid-task should
  be deferred to a follow-on task coordinated with 317.
