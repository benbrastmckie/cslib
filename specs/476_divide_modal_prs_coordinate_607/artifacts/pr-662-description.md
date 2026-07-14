<!--
DRAFT — proposed description for PR #662 as the NATIVE-PRIMITIVE foundational
semantic layer (version B). NOT applied to the live PR.

INTENT (per contributor): #662 assumes #607 has landed with the full native
primitive set {atom, bot, imp, and, or, box, diamond}, and on that base adds
the foundational semantic layer for the modal metalogic. #662 will be rebased
onto #607 and revised once #607 actually lands.

MISMATCH WITH LIVE STATE (must be resolved before this description is accurate):
  - The live #662 (commit 70b7ec4d) is still the OLD box-alongside-diamond delta
    on #607's not-based {atom, not, and, diamond} type (+22 LOC, 3 files).
  - The layer described below is the 386-line slice staged at
    specs/498_.../artifacts/pr-662-slice/{Basic,Denotation}.lean — NOT yet pushed.
  - Applying this description requires first pushing that slice to
    feat/modal-formula-primitives (gated on #607 adopting native primitives).

RECONCILIATION AT REBASE (revise when #607 lands):
  - The slice uses task-441 naming HasDia / ModalConnectives; #607's Operators.lean
    uses HasDiamond and has no HasBot. Rebase must map HasDia -> HasDiamond and rely
    on #607's landed native `bot`/`imp` primitives (task 497 tracks imp/impl naming).
  - Re-verify LOC, file list, CI, and axiom footprint against the pushed branch
    before using this text.

Verified against the staged slice as of 2026-07-13:
  Basic.lean 296 LOC + Denotation.lean 90 LOC = 386 LOC; 0 sorry.
  Duality = `Satisfies.dual` (classical semantic theorem); K = `Satisfies.k`.
  Axioms: `Satisfies.k` none; `Satisfies.dual` & `satisfies_mem_denotation`
  use propext / Classical.choice / Quot.sound (standard classical only).

Proposed title:
  feat(Logics/Modal): foundational semantic layer for the modal metalogic (stacked on #607)
-->

Adds the **foundational semantic layer** for the modal metalogic, on the native primitive `Proposition` `{atom, bot, imp, and, or, box, diamond}`, building on #607 so `□` and `◇` are both primitive and neither is defined from the other.

**Stacked on #607** (`fmontesi/connectives`). Reuses `Foundations/Logic/Operators.lean` operator typeclasses, so it adds only the semantics on top. This PR will be rebased onto #607 and revised once #607 lands.

## What it provides

- **`Cslib/Logics/Modal/Basic.lean`**
  - `Model` (worlds + accessibility relation + valuation) and the native `Proposition` inductive `{atom, bot, imp, and, or, box, diamond}`, with the connective instances (`ModalConnectives`/`HasAnd`/`HasOr`/… and `Bot`) and the derived `neg`/`top`/`iff` abbreviations.
  - The satisfaction relation `Satisfies` (with `⇓Modal[m,w ⊨ φ]` notation) and **one decomposition lemma per connective** — `neg`/`and`/`or`/`impl`/`box_iff_forall`/`diamond_iff_exists` — each an `Iff.rfl`/structural unfolding, no Łukasiewicz-style bridge lemmas.
  - The **K-axiom validity** theorem `Satisfies.k : ⊨ □(φ→ψ) → (□φ → □ψ)`.
  - The **duality theorem** `Satisfies.dual : ⊨ ◇φ ↔ ¬□¬φ` — a genuine classical *semantic* theorem (since `□` and `◇` are both primitive), not a definitional unfolding.
  - The inference-system scaffolding (`Judgement`, `HasInferenceSystem`, derivation notation), the `theory`/`TheoryEq` bundle with its extensionality lemmas, and `valid`/`logic`.
- **`Cslib/Logics/Modal/Denotation.lean`**
  - The denotational semantics `Proposition.denotation` (set of worlds), the bridge `satisfies_mem_denotation` (satisfaction ↔ denotation membership), and `theoryEq_denotation_eq`.

**Scope:** this is the semantic core only. The T/B/4/5/D frame-correspondence axioms are **excluded** and deferred to a later "systems" PR.

**~386 LOC** across 2 files. No `sorry`; no new axioms (`Satisfies.dual` and `satisfies_mem_denotation` use only the standard classical `propext`/`Classical.choice`/`Quot.sound`; `Satisfies.k` is axiom-free). Full `lake build`, `checkInitImports`, `lint-style`, `lake lint`, `lake test`, and `lake shake` pass.

Both modalities primitive is what the intuitionistic and constructive modal systems (IK, CK) will need downstream — there neither `□` nor `◇` is definable from the other — and duality is recovered as `Satisfies.dual` rather than assumed.

> This PR targets #607 and merges after it. It will be rebased onto #607 and revised once #607's native-primitive `Proposition` lands.

## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and extracting files from a development branch to create a clean PR branch
- Running CI verification commands
- Drafting this PR description

All Lean code was verified to compile cleanly on the PR branch.
