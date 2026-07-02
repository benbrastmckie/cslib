# Research Report: Re-sync PR #662 embedded propositional files with #648 head

- **Task**: 468 - resync_pr_662_with_648_head
- **Started**: 2026-07-02T00:00:00Z
- **Completed**: 2026-07-02T00:00:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: PR #648 (`feat/propositional-v2`) is the upstream stack base for PR #662 (`feat/modal-formula-primitives`)
- **Sources/Inputs**:
  - `gh pr view 648/662` metadata + bodies (leanprover/cslib)
  - File blobs fetched at both PR heads: #648 `c9364b6`, #662 `f46056b` (benbrastmckie/cslib fork)
  - `diff -u` of the three propositional files between the two heads
  - Working-tree `main` propositional sources (grep verification)
- **Artifacts**: `specs/468_resync_pr_662_with_648_head/reports/01_resync-pr-662-with-648-head.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md, CSLib CONTRIBUTING/ORGANISATION

## Project Context

- **Upstream Dependency**: PR #648 head (`c9364b6`) — the authoritative target state for the propositional layer.
- **Downstream Dependent**: PR #662 head (`f46056b`) — the modal PR that *stacks on* #648 and re-ships its propositional files; those embedded copies are stale.
- **Note on the working tree**: The repo is on clean `main`, which has NOT yet absorbed #648. Working-tree `Cslib/Logics/Propositional/Defs.lean` still contains `MPL` (L154), `IsIntuitionistic` (L166), `intuitionisticCompletion` (L202). Therefore `main` is *not* the #648-head reference — the #648 branch head `c9364b6` is, and this report compares against it directly.

## Executive Summary

- PR #662 embeds three propositional files (`Defs.lean`, `NaturalDeduction/Basic.lean`, `NaturalDeduction/Theory.lean`) that reflect the **pre-refactor** #648 design, not current #648 head.
- Confirmed at #648 head `c9364b6`: `efq` is a **primitive `Derivation` constructor** (11 constructors), `IPL` is the **empty theory** (`abbrev IPL : Theory Atom := ∅`), and `MPL`, `IsIntuitionistic`, `intuitionisticCompletion` are **all absent**.
- Confirmed at #662 head `f46056b`: `efq` is **not** a primitive rule (10 constructors); `IPL` is `Set.range (Proposition.imp ⊥ ·)`; `MPL = ∅`; `IsIntuitionistic` class and `intuitionisticCompletion` def both present; a family of `IsIntuitionistic.*` derived rules (`efqCtx`, `efqRule`, `contra`, `instIsIntuitionisticOfIsClassical`) present.
- Additional cross-cutting drift: #662's `Defs.lean` `public import`s `Cslib.Foundations.Logic.Connectives` and registers `PropositionalConnectives`/`HasAnd`/`HasOr` instances. **`Connectives.lean` does not exist at #648 head (HTTP 404)** — #648 dropped it. This is a *blocking* stacking conflict for #662's modal files (which depend on `HasBox`/`ModalConnectives`) and must be resolved separately from the three-file resync.
- The #662 PR body is inaccurate: it claims #662 "carries all [#648's] changes including `Connectives.lean` with `PropositionalConnectives`" and describes #648 as "Connective typeclasses + five-primitive propositional formula type" — both no longer true.

## Context & Scope

Reconciliation target = #648 head `c9364b6`. Files to reconcile in #662 = the three propositional files (`.name-only` shows both PRs touch exactly these three: `Defs.lean`, `NaturalDeduction/Basic.lean`, `NaturalDeduction/Theory.lean`). All diffs below are oriented **648-head → 662-head**, so "remove/add" describes edits to apply *to #662* to reach #648 head.

## Findings

### F1. #648 head state (verified)

`648_.../Defs.lean` (132 lines):
- `abbrev IPL : Theory Atom := ∅` with docstring "Ex falso quodlibet is a primitive inference rule (see `Derivation.efq`), so no explosion axioms are needed."
- No `MPL`, no `IsIntuitionistic`, no `intuitionisticCompletion`, no `efq_mem_ipl`.
- Retains `CPL := Set.range (Proposition.imp (Proposition.neg (Proposition.neg ·)) ·)`-style, `dne_mem_cpl`, and `IsClassical` class.
- Does **not** import `Connectives` and does **not** register `PropositionalConnectives`/`HasAnd`/`HasOr`.

`648_.../NaturalDeduction/Basic.lean` (402 lines):
- `Theory.Derivation` has the **primitive `efq` constructor**: `| efq {Γ} {A} : Derivation Γ ⊥ → Derivation Γ A` (docstring "Makes IPL the base logic"). Doc header states "11 constructors in total. IPL is the base logic; ex falso is primitive."
- `efq` cases present in `weak`, `subs`, `substAtom` recursions.
- `abbrev Equiv := IPL.Equiv`.
- References Avigad2022, TroelstraVanDalen1988, Prawitz1965, Gentzen1935 + Zulip thread link.

`648_.../NaturalDeduction/Theory.lean` (93 lines):
- Docstring: "we prove that `CPL` is a classical theory" (no IPL/intuitionistic content).
- `open ... Derivation IsClassical` (no `IsIntuitionistic`).
- Only `instIsClassicalCPL`, `IsClassical.byContra/lem/pierce`, `LEM`, `Pierce`, `instIsClassicalLEM`, `instIsClassicalPierce`.
- `pierce`, `instIsClassicalLEM`, `instIsClassicalPierce` all close explosion goals with the **primitive `efq (...)`** applied to a derivation of `⊥`.
- `LEM`/`Pierce` instances are over the bare theory (`LEM`, `Pierce`), not `LEM ∪ IPL` / `Pierce ∪ IPL`.

### F2. #662 head state (verified — the stale drift)

`662_.../Defs.lean` (172 lines):
- Adds `public import Cslib.Foundations.Logic.Connectives`.
- Registers `instance : PropositionalConnectives (Proposition Atom)`, `HasAnd`, `HasOr`.
- `abbrev MPL : Theory (Atom) := ∅` ("empty theory = minimal propositional logic").
- `abbrev IPL : Theory Atom := Set.range (Proposition.imp ⊥ ·)` + `lemma efq_mem_ipl (A) : (⊥ → A) ∈ IPL`.
- `@[reducible] def intuitionisticCompletion (T : Theory Atom) : Theory (WithBot Atom) := (WithBot.some <$> T) ∪ IPL`.
- `@[scoped grind] class IsIntuitionistic (Atom) (S) [InferenceSystem S (Proposition Atom)] where efq (A) : S⇓(⊥ → A)`.
- Doc header bullets for `IsIntuitionistic` and `Theory.intuitionisticCompletion`.

`662_.../NaturalDeduction/Basic.lean` (390 lines):
- `Theory.Derivation` has **10 constructors — no `efq`**. Doc header: "10 constructors in total. Ex falso quodlibet (bottom elimination) is a derived rule requiring `[IsIntuitionistic T]`."
- No `efq` cases in `weak`/`subs`/`substAtom`.
- `abbrev Equiv := MPL.Equiv`.
- Removed the Troelstra/Prawitz/Gentzen references and the Zulip link; added an `MPL` (minimal logic) doc bullet.

`662_.../NaturalDeduction/Theory.lean` (120 lines):
- Docstring adds "we prove ... that `IPL` is an intuitionistic theory."
- `open ... Derivation IsIntuitionistic IsClassical`.
- Adds `instIsIntuitionisticIPL`, `instIsIntuitionisticIntuitionisticCompletion`, `IsIntuitionistic.efqCtx`, `IsIntuitionistic.efqRule`, `IsIntuitionistic.contra`, `instIsIntuitionisticOfIsClassical`.
- `pierce` proof uses `apply contra A B <;> grind` instead of primitive `efq`.
- `instIsClassicalLEM` is over `LEM ∪ IPL`; `instIsClassicalPierce` over `Pierce ∪ IPL`; both discharge explosion via `impE (A := ⊥) (ax <| Set.mem_union_right _ (efq_mem_ipl A))` instead of primitive `efq`.

### F3. Connectives.lean cross-cutting conflict (blocking for modal, not for the 3-file resync)

- `gh api .../Connectives.lean?ref=c9364b6` → **404 Not Found** (#648 head has no `Connectives.lean`).
- `gh api .../Connectives.lean?ref=f46056b` → present (#662 ships it with `HasBox` + `ModalConnectives`).
- Consequence: after resync, #662's `Defs.lean` must drop the `Connectives` import + three instance registrations. But #662's **modal** files (`Cslib/Logics/Modal/Basic.lean`, `LogicalEquivalence.lean`, `Cube.lean`) and its `Cslib/Foundations/Logic/Connectives.lean` depend on `PropositionalConnectives`/`HasAnd`/`HasOr`/`HasBox`/`ModalConnectives`. Since #648 no longer provides `Connectives.lean`, #662 must either (a) own `Connectives.lean` itself (self-contained, not "carried from #648"), or (b) rebase onto whatever PR now owns the connective typeclasses (#607 per the #648 body). This is a design decision for the author, outside the pure propositional-file resync, and should be surfaced before implementation.

## Decisions

- **Authoritative reference is #648 branch head `c9364b6`, not working-tree `main`.** `main` predates #648.
- **The 3-file propositional resync and the `Connectives.lean` dependency question are separable.** The three-file edits (F4 plan) are mechanical and self-contained; the Connectives question needs an author design decision (F3).
- **No sorry/axiom shortcuts are needed or permitted.** #648 head compiles sorry-free with primitive `efq`; the resync is a faithful transcription of #648-head code into #662, so zero-debt is achievable.

## Recommendations

Priority 1 — mechanical three-file resync (bring #662 embedded files to #648 head):

- **`Cslib/Logics/Propositional/Defs.lean`**
  1. Remove `public import Cslib.Foundations.Logic.Connectives`.
  2. Remove the `PropositionalConnectives`, `HasAnd`, `HasOr` instance blocks.
  3. Remove doc-header bullets for `IsIntuitionistic` and `Theory.intuitionisticCompletion`.
  4. Delete `abbrev MPL := ∅`; change `IPL` back to `abbrev IPL : Theory Atom := ∅` with the primitive-efq docstring.
  5. Delete `lemma efq_mem_ipl`.
  6. Delete `def intuitionisticCompletion`.
  7. Delete `class IsIntuitionistic`.
  8. Keep `CPL`, `dne_mem_cpl`, `IsClassical` unchanged.

- **`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`**
  1. Restore module docstring: "11 constructors", "IPL is the base logic; ex falso is primitive", references (Avigad2022, TroelstraVanDalen1988, Prawitz1965, Gentzen1935) and the Zulip link; remove the `MPL` minimal-logic bullet.
  2. Add the primitive `| efq {Γ} {A} : Derivation Γ ⊥ → Derivation Γ A` constructor to `Theory.Derivation`.
  3. Add `| efq D => efq (D.weak hTheory hCtx)` in `weak`.
  4. Add `| efq E => efq (E.subs Ds)` in `subs`.
  5. Add `| efq D => efq (D.substAtom f)` in `substAtom`.
  6. Change `abbrev Equiv := MPL.Equiv` back to `IPL.Equiv`.

- **`Cslib/Logics/Propositional/NaturalDeduction/Theory.lean`**
  1. Restore docstring to CPL-only wording (drop the IPL-intuitionistic sentence).
  2. `open` line: remove `IsIntuitionistic`.
  3. Delete `instIsIntuitionisticIPL`, `instIsIntuitionisticIntuitionisticCompletion`.
  4. Delete `IsIntuitionistic.efqCtx`, `IsIntuitionistic.efqRule`, `IsIntuitionistic.contra`.
  5. Delete `instIsIntuitionisticOfIsClassical`.
  6. In `pierce`: replace `apply contra A B <;> grind` with the #648-head primitive-`efq` proof term.
  7. In `instIsClassicalLEM`: revert theory from `LEM ∪ IPL` to `LEM`; discharge explosion via primitive `efq (...)` (not `impE (A := ⊥) (ax ...)`).
  8. In `instIsClassicalPierce`: revert `Pierce ∪ IPL` to `Pierce`; same primitive-`efq` discharge.

Priority 2 — align `references.bib`: ensure #662 carries the four keys #648 head adds where its Basic.lean cites them (`Avigad2022`, `Gentzen1935`, `Prawitz1965`, `TroelstraVanDalen1988`). Diff `references.bib` between the two heads during implementation to avoid dangling BibKeys / duplicates.

Priority 3 — resolve the `Connectives.lean` dependency (F3) BEFORE finalizing #662, since #648 head no longer provides it. Author decision required: #662 owns `Connectives.lean` self-contained, or rebase onto the PR that now owns connective typeclasses (#607). This affects #662's modal files, not the three propositional files above.

Priority 4 — PR #662 body corrections:
- "Relationship to Other PRs → PR #648 (stacking dependency)": remove the claim that #662 "carries all its changes including `Connectives.lean` with `PropositionalConnectives`"; state that #648 head now uses a **primitive `efq` rule**, `IPL = ∅` (empty base theory), and has **removed** `MPL`, `IsIntuitionistic`, `intuitionisticCompletion`, and `Connectives.lean`.
- "Contribution Roadmap" item 1: change "PR #648: Connective typeclasses + five-primitive propositional formula type" to drop "Connective typeclasses" (they are no longer in #648).
- Anywhere the body relies on `PropositionalConnectives`/`HasAnd`/`HasOr` being inherited from #648, state their new source (per the F3 decision).
- Verify the Modal "Breaking Changes"/"Design Rationale" text still matches once the connective source is settled.

## Risks & Mitigations

- **Risk**: Treating working-tree `main` as the #648 reference (it still has `MPL`/`IsIntuitionistic`/`intuitionisticCompletion`). **Mitigation**: fetch from branch head `c9364b6`; this report already did so.
- **Risk**: Dropping `Connectives.lean` from #662's `Defs.lean` breaks #662's modal files that need `PropositionalConnectives`/`HasBox`. **Mitigation**: treat F3 as a gating decision; do not merge the propositional resync into #662 without settling where connective typeclasses live.
- **Risk**: Restoring primitive `efq` but leaving a stray `efq_mem_ipl`/`IsIntuitionistic` reference elsewhere causes build failure. **Mitigation**: after edits, `grep -rn "IsIntuitionistic\|intuitionisticCompletion\|efq_mem_ipl\|MPL" Cslib/Logics/Propositional` on the #662 tree must return only the primitive-`efq`-based hits; then run the CSLib CI pipeline (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`).
- **Risk**: `references.bib` merge duplicates/omits the four keys. **Mitigation**: diff `references.bib` at both heads before committing.

## Appendix

- PR #648 head: `c9364b65391b1cc2bfd211102a3deb86f3844d48` (branch `feat/propositional-v2`).
- PR #662 head: `f46056b9b6ebf44c322e88278b64ada959dbf146` (branch `feat/modal-formula-primitives`).
- Both branches live on the `benbrastmckie/cslib` fork; PRs target `leanprover/cslib:main`.
- Fetched blobs for diffing are in the session scratchpad (`648_*`, `662_*`).
- Constructs verified absent at #648 head via HTTP 404 / diff: `Connectives.lean`, `MPL`, `IsIntuitionistic`, `intuitionisticCompletion`, `efq_mem_ipl`, non-primitive `efq` derived rules.
- Constructs verified present at #648 head: primitive `Derivation.efq`, `abbrev IPL := ∅`, `IsClassical`, `CPL`.
