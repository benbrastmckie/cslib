# Task 418 — Research: Shared `PropositionalEmbedding` Typeclass/Abstraction

**Task type**: cslib (refactor / abstraction design)
**Status**: researched
**Date**: 2026-06-29
**Source**: `specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md` §3, Rank 3.
**Goal**: Factor the "structural on atom/bot/imp, Łukasiewicz on and/or" embedding pattern shared
by `toModal`, `toTemporal`, `toBimodal` into one definition skeleton + a single authored
classical-scope limitation note, preserving the simp/grind surface and the commuting-diamond
lemmas, and adding a clearly-typed extension point for a future native embedding. CI green, 0 new
sorry.

---

## 1. Summary / Verdict

**The refactor is tractable and low-risk (S–M).** All three target formula types already register
as instances of the connective-typeclass hierarchy in
`Cslib/Foundations/Logic/Connectives.lean`, and all three already use *identical* Łukasiewicz
`and`/`or` encodings. The only target-specific datum in each embedding is the `atom` injection
`Atom → F`. Therefore the three definitions can be collapsed to one generic recursion
parameterized over `[HasBot F] [HasImp F]` plus an atom map, exposed as a `PropositionalEmbedding`
typeclass. Because every target's connective instance sets `bot := .bot` and `imp := .imp` to the
raw constructors, the rewritten `toX_*` simp/grind lemmas stay `rfl`, so the **entire simp/grind
surface and the commuting-diamond lemmas are preserved by construction**. The only non-mechanical
churn is ~3 bridge-proof files that currently unfold the *raw def* via `simp only
[PL.Proposition.toX, …]`; those must be repointed to the per-constructor simp lemmas (which we keep
verbatim). No sorry, no new axiom.

One hard layering constraint: **the shared definition cannot live in `Foundations/`** because it
embeds *from* `PL.Proposition` (which lives in `Logics/Propositional/`), and Foundations does not
depend on Logics. It must live in a new file under `Cslib/Logics/Propositional/`.

---

## 2. Verified Facts (source-read)

### 2.1 The three embeddings (current state)

| Embedding | File:line | `and`/`or` cases |
|-----------|-----------|------------------|
| `PL.Proposition.toModal` | `Cslib/Logics/Modal/FromPropositional.lean:58-63` | delegates to `Modal.Proposition.and`/`.or` abbrevs |
| `PL.Proposition.toTemporal` | `Cslib/Logics/Temporal/FromPropositional.lean:57-62` | Łukasiewicz **inlined** (`.imp (.imp … .bot) .bot`) |
| `PL.Proposition.toBimodal` | `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean:59-64` | Łukasiewicz **inlined** |

`atom`/`bot`/`imp` cases are structural in all three. The only stylistic difference (Modal uses the
`.and`/`.or` abbrevs; Temporal/Bimodal inline) is *definitionally irrelevant*: the target abbrevs
`Proposition.and`/`Formula.and` are themselves exactly `.imp (.imp φ₁ (.imp φ₂ .bot)) .bot`
(`Modal/Basic.lean:113`, `Temporal/Syntax/Formula.lean:126`, `Bimodal/Syntax/Formula.lean`), and
`or` is `.imp (.imp φ₁ .bot) φ₂`. **All three and/or encodings are the same term.**

### 2.2 Triplicated limitation note

Verbatim (modulo logic name) classical-scope notes at:
- `Modal/FromPropositional.lean:35-41`
- `Temporal/FromPropositional.lean:34-40`
- `Bimodal/Embedding/PropositionalEmbedding.lean:33-41`

Plus near-duplicate "Encoding Rationale" prose and per-constructor docstrings citing
`[Wajsberg1938]`, `[McKinsey1939]`. The same Łukasiewicz rationale is *also* already authored once
in `Foundations/Logic/Connectives.lean:29-37`.

### 2.3 Existing reusable infrastructure (reuse-first check — PASS)

`Cslib/Foundations/Logic/Connectives.lean` already provides:
- `HasBot F` (`:80`), `HasImp F` (`:85`), `HasAnd F` (`:132`), `HasOr F` (`:137`).
- `PropositionalConnectives F extends HasBot F, HasImp F` (`:151`) with **defaulted Łukasiewicz
  `neg`/`top`** fields (`:155`, `:159`).
- `ModalConnectives`/`TemporalConnectives`/`BimodalConnectives` (all extend
  `PropositionalConnectives`).

All three targets are registered instances, mapping to **raw constructors**:
- `Modal.Proposition`: `instance : ModalConnectives (Proposition Atom)` with `bot := .bot;
  imp := .imp` (`Modal/Basic.lean:86-89`).
- `Temporal.Formula`: `instance : TemporalConnectives (Formula Atom)` with `bot := .bot;
  imp := .imp` (`Temporal/Syntax/Formula.lean:105`).
- `Bimodal.Formula`: `instance : BimodalConnectives (Formula Atom)` with `bot := .bot;
  imp := .imp` (`Bimodal/Syntax/Formula.lean:53`).

`PL.Proposition` itself is `PropositionalConnectives (Proposition Atom)`
(`Propositional/Defs.lean:114`), and `Defs.lean` already `public import`s
`Foundations.Logic.Connectives` (`:10`). **No new typeclass for bot/imp is needed.**

There is **no `HasAtom`/atom-injection typeclass** — that is the one thing the new abstraction must
add.

### 2.4 simp/grind surface to preserve

- Modal `toModal_atom/bot/imp/and/or`: `@[simp]`, all `rfl` (`FromPropositional.lean:70-92`); plus
  `toModal_neg` (plain).
- Temporal `toTemporal_atom/bot/imp/and/or`: `@[simp, scoped grind =]`, all `rfl`
  (`FromPropositional.lean:69-93`); plus `toTemporal_neg`. **Grind surface lives here only.**
- Bimodal `toBimodal_atom/bot/imp/and/or`: `@[simp]`, all `rfl`
  (`PropositionalEmbedding.lean:71-96`); plus `toBimodal_neg`.
- Commuting-diamond lemmas (must preserve): `toModal_toBimodal` (`:104`, `@[simp]`),
  `toTemporal_toBimodal` (`:110`, `@[simp]`), `embedding_commutes` (`:116`). Proofs are
  `induction φ <;> simp [*]` — they depend only on the `@[simp]` per-constructor lemmas, which we
  keep verbatim. These involve the *inter-target* embeddings `Modal.Proposition.toBimodal` /
  `Temporal.Formula.toBimodal` (`Bimodal/Embedding/ModalEmbedding.lean`,
  `TemporalEmbedding.lean`) — those are **out of scope** for this task (they embed Modal→Bimodal
  and Temporal→Bimodal, not PL→X) and need no change.

### 2.5 Downstream unfold sites (the only real churn)

Proofs that unfold the *raw def* (`simp only [PL.Proposition.toX, …]`) and would break if `toX`
becomes a thin wrapper:
- `Modal/FromPropositional.lean:115,119,130` (the `modal_satisfies_toModal_iff_evaluate` bridge —
  same file).
- `Temporal/ConservativeExtension.lean:54,59,69`
  (`temporal_satisfies_toTemporal_iff_evaluate`).
- `Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean:71,76,78,83,93`
  (`bimodal_truthAt_toBimodal_iff_evaluate`).

All consumers (15 Modal per-system `ConservativeExtension.lean`, the param lemma, etc.) use the
embedding *opaquely* (apply `toModal`, use the named bridge/simp lemmas) and need no change.

### 2.6 Layering constraint (verified)

`grep -rln "import Cslib.Logics" Cslib/Foundations/` returns only one intra-Foundations hit
(`Order/HilbertAlgebra/DiegoEmbedding.lean`, not a Logics import). **Foundations must not import
Logics.** Since the embedding source `PL.Proposition` is in `Logics/Propositional`, the shared
`embed` belongs in a new `Cslib/Logics/Propositional/` file (imports `Propositional.Defs` +
`Foundations.Logic.Connectives`), which all three target embedding files already transitively
import.

---

## 3. Recommended Design

### 3.1 New file `Cslib/Logics/Propositional/Embedding.lean`

Holds the single skeleton + the single authored limitation note + the extension point.

```lean
import Cslib.Init
public import Cslib.Logics.Propositional.Defs   -- PL.Proposition (+ Connectives transitively)

@[expose] public section
namespace Cslib.Logic

/-- A target formula type `F` admits the classical (Łukasiewicz) embedding of
`PL.Proposition Atom`: it supplies `bot`/`imp` (via the `PropositionalConnectives` hierarchy)
and an injection of atoms. The and/or cases are encoded classically.

**Classical scope only.** [SINGLE AUTHORED NOTE — the one place the Łukasiewicz/[Wajsberg1938],
[McKinsey1939] classical-vs-intuitionistic caveat is stated.] A future native
(intuitionistic-faithful) embedding would instead require `[HasAnd F] [HasOr F]` and target
constructors — see `NativePropositionalEmbedding` below; this class deliberately does NOT
provide it. -/
class PropositionalEmbedding (Atom : Type*) (F : Type*) [HasBot F] [HasImp F] where
  /-- Injection of propositional atoms into the target. -/
  atomEmbed : Atom → F

/-- The single shared embedding skeleton: structural on atom/bot/imp, Łukasiewicz on and/or. -/
def PL.Proposition.embed {Atom F : Type*} [HasBot F] [HasImp F]
    [PropositionalEmbedding Atom F] : PL.Proposition Atom → F
  | .atom p   => PropositionalEmbedding.atomEmbed p
  | .bot      => HasBot.bot
  | .imp a b  => HasImp.imp a.embed b.embed
  | .and a b  => HasImp.imp (HasImp.imp a.embed (HasImp.imp b.embed HasBot.bot)) HasBot.bot
  | .or  a b  => HasImp.imp (HasImp.imp a.embed HasBot.bot) b.embed

@[simp] theorem PL.Proposition.embed_atom [HasBot F] [HasImp F]
    [PropositionalEmbedding Atom F] (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).embed
      = (PropositionalEmbedding.atomEmbed p : F) := rfl
-- …embed_bot / embed_imp / embed_and / embed_or, all rfl…

/-- Extension point (NOT instantiated): a native, intuitionistic-faithful embedding using the
target's native `and`/`or`. No CSLib target currently has an intuitionistic modal/temporal
proof system, so this is a typed placeholder for future work (see task 415 §3). -/
class NativePropositionalEmbedding (Atom : Type*) (F : Type*)
    [HasBot F] [HasImp F] [HasAnd F] [HasOr F] where
  atomEmbed : Atom → F

end Cslib.Logic
```

Notes:
- Keep `embed` a plain `def` (not `abbrev`) so it has clean equational lemmas; expose
  `embed_*` `@[simp]` lemmas.
- `Atom` appears inside `F` (`Modal.Proposition Atom`), so instance resolution recovers it from the
  target type. If resolution is awkward, mark `Atom` an `outParam` or supply the atom map as an
  explicit argument instead of via the class (a `def PL.Proposition.embedWith (atom : Atom → F)`
  variant). **Validate during implementation** (try the typeclass form first; fall back to the
  explicit-argument form if elaboration of the wrapper `rfl` lemmas is fragile).

### 3.2 Each target: instance + thin wrapper, simp lemmas kept verbatim

```lean
-- Modal/FromPropositional.lean
instance : PropositionalEmbedding Atom (Modal.Proposition Atom) where
  atomEmbed := Modal.Proposition.atom

def PL.Proposition.toModal (φ : PL.Proposition Atom) : Modal.Proposition Atom := φ.embed
-- toModal_atom/bot/imp/and/or kept EXACTLY as today (still `rfl`); toModal_neg kept.
```

Identical pattern for `toTemporal` (instance `atomEmbed := Temporal.Formula.atom`, keep
`@[simp, scoped grind =]`) and `toBimodal` (instance `atomEmbed := Bimodal.Formula.atom`).

**Why the simp lemmas stay `rfl`:** with `toModal := φ.embed`, the and-case of `embed` is
`HasImp.imp (HasImp.imp a.embed (HasImp.imp b.embed HasBot.bot)) HasBot.bot`. For the Modal
instance `HasImp.imp = Modal.Proposition.imp` and `HasBot.bot = Modal.Proposition.bot` *by
projection `rfl`* (instance sets `imp := .imp`, `bot := .bot`), so this is defeq to
`Modal.Proposition.and a.embed b.embed = (toModal a).and (toModal b)`. Hence
`toModal_and : (and a b).toModal = a.toModal.and b.toModal := rfl` continues to type-check. Same
reasoning for Temporal/Bimodal.

### 3.3 Collapse the triplicated note

Replace each file's 7-line "Limitations" block (and the redundant "Encoding Rationale" prose) with
a one-line pointer: *"For the classical-scope limitation and the shared embedding skeleton, see
`PL.Proposition.embed` / `PropositionalEmbedding` in `Cslib/Logics/Propositional/Embedding.lean`."*
Keep a one-line module-level summary so each file remains self-describing.

### 3.4 Repoint the ~3 bridge proofs (only non-mechanical edit)

In the three bridge proofs (§2.5), replace `simp only [PL.Proposition.toX, …]` with the
per-constructor simp lemmas, e.g.
`simp only [PL.Proposition.toModal_imp, PL.Proposition.toModal_and, PL.Proposition.toModal_or,
PL.Proposition.toModal_bot, Modal.Satisfies, PL.Evaluate]`, or add `PL.Proposition.embed` to the
unfold set. The downstream proof bodies (`by_contra`/`by_cases`) are unchanged. Verify each with
`lean_goal` before/after, then `lake build` the module.

---

## 4. Alternative Considered (and rejected)

**Push `and`/`or` into `PropositionalConnectives` and define `embed` over the bundled class.** This
overlaps task 173 (which is deferred precisely because `HasAnd`/`HasOr` are not yet fields of
`PropositionalConnectives`). Coupling 418 to 173 enlarges scope and risks the bundled-class change
rippling into the four concrete instances. **Rejected**: keep 418 to `[HasBot F] [HasImp F]` + a
local atom-injection class; this is orthogonal to 173 and strictly smaller.

**Define `embed` in Foundations.** Rejected — violates the Foundations-↛-Logics layering (§2.6).

---

## 5. Tactic / Verification Notes

- The design is `rfl`-transparent; no proof search needed for the wrapper lemmas. No lean-lsp
  search tools were required (every claim is a readable definition/instance). The risk is purely
  *elaboration* (instance resolution for `PropositionalEmbedding Atom (Target Atom)` and the `rfl`
  lemmas), not proof difficulty.
- Recommended verification order during implementation: build `Cslib.Logics.Propositional.Embedding`
  first; then `Cslib.Logics.Modal.FromPropositional` (includes its own bridge); then
  `Cslib.Logics.Temporal.FromPropositional` + `Temporal.ConservativeExtension`; then
  `Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding` +
  `Bimodal.…PropositionalConservativity`; finally full `lake build`, then CI
  (`checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`,
  `lake shake --add-public --keep-implied --keep-prefix`). New file needs
  `lake exe mk_all --module`.
- Lint watch-outs: docstring on the new `class`, `def`, and every `embed_*` lemma (docBlame);
  Prop-valued `embed_*` are `theorem` (defLemma); names lowerCamelCase, no underscores
  (the `embed_atom`-style names follow the existing `toModal_atom` convention — keep consistent);
  `instance` blocks inside `namespace Cslib.Logic` (topNamespace); preserve the
  `@[simp, scoped grind =]` attributes on the Temporal lemmas exactly.

---

## 6. Scope, Effort, Risk

- **Files added**: 1 (`Cslib/Logics/Propositional/Embedding.lean`, ~70–100 lines) + `Cslib.lean`
  barrel update via `mk_all`.
- **Files edited**: 3 embedding files (def → wrapper, instance added, note collapsed, simp lemmas
  kept) + 3 bridge-proof files (repoint unfold). ~6 edited.
- **Net**: removes triplicated notes + 2 inlined and/or skeletons; single source of truth for the
  classical caveat; typed extension point added.
- **Effort**: **S–M** (one focused task). **Risk**: low — main risk is the
  `PropositionalEmbedding Atom F` instance-resolution ergonomics (mitigation: `outParam Atom` or
  explicit-atom-map variant). **0 new sorry; 0 new axiom.** Does NOT enable the intuitionistic lift
  (by design).

---

## 7. Blockers

None. The substrate (`HasBot`/`HasImp`/`PropositionalConnectives` + per-target instances) already
exists; the targets already use identical Łukasiewicz encodings; the simp/grind surface is
`rfl`-preserved. The single design decision to resolve during implementation is typeclass-vs-
explicit-atom-map for the atom injection (both are sorry-free; pick whichever elaborates the `rfl`
wrapper lemmas cleanly).
