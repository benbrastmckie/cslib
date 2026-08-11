# PR #607 Engagement — Consolidated Human-Review Scaffolding Packet

> ============================================================
> **FACTUAL SCAFFOLDING FOR A HUMAN-AUTHORED REVIEW.**
> **Rewrite every sentence in your own words before posting.**
> **CSLib Zulip AI policy #605827029 — agents MUST NOT author PR/Zulip prose.**
> **No paragraph in this file is ready-to-post prose. Every bullet is a *point to make*.**
> ============================================================
>
> This packet consolidates the factual material from files 01, 02, and 03 in this directory,
> ordered by the priority structure in `reports/02_engagement-strategy.md §6`.
> It also anchors explicitly on `benbrastmckie`'s existing 2026-06-17 comment
> (`issuecomment-4735753144`) and marks each point NEW vs ALREADY RAISED.
>
> **Source files**:
> - `01_comparison-tables.md` — design tables, naming options, notation ladder, file-org options
> - `02_falsum-bridge-sketch.md` — verified Lean snippets for HasNot + Bot/Top bridge
> - `03_grind-direction-finding.md` — empirical grind finding (positive and negative)

---

## Anchor: benbrastmckie's 2026-06-17 Comment (Already Posted)

Points already made in `issuecomment-4735753144`:
- Overlap with #648's `Connectives.lean` (now RESOLVED: `Connectives.lean` removed from #648
  per commit `85db79a6`; no competing typeclass module in #648).
- `HasImpl`/`impl` vs `HasImp`/`imp` argument (favoring `imp`; FormalizedFormalLogic
  convention, `impI`/`impE` rule prefix).
- Primitive-`bot` / primitive-`box` motivating case (substitution invariance, free-algebra
  property, necessitation as a pure rule).

The review MUST build on these, NOT restate them. The points below are all ADDITIVE.

---

## Priority 1: Consensus / Low-Friction Wins (Lead Here) [NEW — not in prior comment]

### 1a. File consolidation — endorse the consensus

- **Point**: Three independent reviewers (eric-wieser, ctchou, chenson2018) all asked for
  consolidation. Endorse one option.
  - Preferred: single `Operators.lean` (or `LogicOperators.lean`) with one top-level
    conventions docstring — matches eric-wieser's ask most closely, largest reviewer support.
  - Alternative: ctchou's 3-file split (Modal=box+diamond, Tensor alone, Propositional for rest).
- **Why lead with this**: signals collaboration, costs fmontesi little, builds goodwill before
  the harder naming/falsum points.

### 1b. Tidier instance syntax — endorse eric-wieser's suggestion [NEW]

- **Point**: eric-wieser suggested `instance : HasAnd (Proposition Atom) where and := .and`
  (using `where` syntax and dot-notation shorthand). This is cleaner than the current `{and := .and}`.
- Pure style, no design impact, easy to agree.

---

## Priority 2: Naming Decision — Ask, Don't Dictate [NEW — extends the impl/imp point]

### 2a. `Has` prefix question (most high-leverage) [NEW]

- **Point to make**: eric-wieser flagged "the `Has` prefix is largely a Lean-3-ism" (2026-06-19
  review). This is the biggest architectural question: rename everything to drop `Has`?

- **Counter-argument to surface** (NEW — not in prior comment):
  Bare `And`, `Or`, `Iff` **collide with Lean core/Mathlib**:
  - `core.And : Prop → Prop → Prop` (Lean 4 builtin)
  - `Mathlib.Or`, `Iff` (propositional typeclass)
  Importing `HasAnd`-free connective classes into a proof context that also imports Mathlib
  would create name conflicts. This is a **concrete, practical reason CSLib may retain `Has`**
  (not mere inertia). It also matches CSLib's existing `HasFresh`, `HasContext`, `HasSubstitution`
  in `Foundations/Syntax`.

- **Ask**: request a single maintainer ruling before more code accretes. Both options are
  defensible; the library needs one consistent choice.

### 2b. `impl` vs `imp` — close the loop [ALREADY RAISED, ask for decision]

- Already argued in prior comment (favoring `imp`). Ask for a final decision now, in the
  same breath as the `Has` decision, so both are settled together.

---

## Priority 3: Falsum/Verum via Mathlib `Bot`/`Top` [NEW — corrects prior comment's "add HasBot"]

### 3a. Retract the "add a `HasBot` class" framing [NEW]

- **Point**: The prior comment (from a pre-research draft) suggested adding `HasBot`/`HasTop`.
  This is incorrect. Mathlib already ships `Bot`/`Top`, and CSLib's `Proposition` already uses
  them (`instance : Bot (Proposition Atom) := ⟨.bot⟩` at Defs.lean line 104). Minting `HasBot`
  duplicates Mathlib and runs against eric-wieser's "`Has` is a Lean-3-ism" direction.
  **Explicitly retract this** if the prior comment is still visible to reviewers.

### 3b. State the actual gap and the correct fix [NEW]

- **Point**: The genuine gap is not representability (registering `HasNot` with derived `neg`
  is faithful — #607 already does it for the upstream type). The gap is:
  (i) No `⊥`/`⊤` typeclass in #607's operator set — **Mathlib `Bot`/`Top` fill this**.
  (ii) No polymorphic bridge `¬φ ↔ (φ → ⊥)` for grind/simp.

- **Verified Lean exhibit** (from `02_falsum-bridge-sketch.md`; verified to compile ✓):

  ```lean
  -- Faithful HasNot registration via derived neg:
  instance : HasNot (PL.Proposition Atom) where
    not := Proposition.neg
  -- Bridge (both sides = Proposition.imp A Proposition.bot, hence rfl):
  @[grind =] lemma negBridge (A : Proposition Atom) :
      (A → ⊥ : Proposition Atom) = HasNot.not A := rfl
  ```
  (In the actual code, use #607's `HasNot` and the naming agreed in Priority 2.)

### 3c. Float the default instance — as a question [NEW]

- **Point to float** (not a demand): a default instance
  `instance (priority := 50) [HasImpl α] [Bot α] : HasNot α := ⟨fun φ => HasImpl.impl φ ⊥⟩`
  would make any imp+bot type automatically get `¬` for free, cleanly expressing the
  Johansson/Prawitz convention.
- **Hazard to mention**: diamond-inheritance risk for classical types that also have a
  primitive negation; resolution ambiguity at `HasNot.not` call sites. Recommend letting
  the maintainers decide.

---

## Priority 4: `_def` Bridge-Lemma Direction — Unblock chenson's CHANGES_REQUESTED [NEW]

### 4a. The finding (from `03_grind-direction-finding.md`) [NEW]

- **Empirical finding**: chenson's preferred orientation (constructor → notation, e.g.,
  `φ.and ψ = φ ∧ ψ`) is the CURRENT direction in #607. This orientation makes things harder
  for `grind` in proof contexts where `Satisfies` is defined on constructors, not typeclass
  methods. The root cause: grind sees `Satisfies m w (φ ∧ ψ)` (typeclass notation) and cannot
  reduce further because `Satisfies` only has equations for constructors.

- **Positive result**: For the fork's `Modal.Proposition` (where `∧`, `∨` are `abbrev`s,
  not constructors), `grind` works **without any `_def` lemma at all** (verified: `grind` alone
  proves `Satisfies m w (φ₁ ∧ φ₂) ↔ Satisfies m w φ₁ ∧ Satisfies m w φ₂` ✓).

- **Negative result**: For the upstream propositional (where `Proposition.and` IS a constructor
  and `HasAnd.and` is the typeclass method), `simp` and `grind` BOTH fail without explicit
  bridge hints. The working pattern: `simp [HasAnd.and]` (explicit instance unfolding).

### 4b. Diagnosis and offer [NEW]

- **Point**: Waring's blocker is real and is specific to the upstream propositional (primitive
  constructors + typeclass wrapper). The fix that HELPS grind is to orient the bridge in the
  REVERSE direction from chenson's preference: `notation → constructor`
  (`φ ∧ ψ = φ.and ψ`) — i.e., unfold the notation to the constructor, then grind applies
  Satisfies equations.

- **Trade-off to surface**: The `notation → constructor` orientation means the constructor is
  the simp/grind normal form, not the notation — which is what chenson objects to. There is a
  genuine tension between "notation is normal form" (chenson's aesthetic preference) and
  "grind works for Satisfies proofs" (practical requirement). One resolution: tag both directions
  as equations (or provide the instance equation `HasAnd.and = Proposition.and` as `@[grind =]`).

- **Offer**: Offer to test the settled orientation in the proof context and confirm grind works
  before posting. The fork provides a clean test bed via the `Scratch` approach used here.

### 4c. Minor cleanup note [NEW]

- The fork's current `Satisfies.k` and `Satisfies.dual` use `change` to manually unfold
  notation before applying tactics. For the fork's modal (Architecture A, abbrev-based), this
  is unnecessary — `grind` alone closes the dual (verified ✓). Flag as cleanup debt.
- The prior research report (02) mentioned "a commented-out `grind only` block in `Satisfies.dual`"
  — this may have been cleaned up already; verify against the current PR diff before mentioning.

---

## Priority 5: Notation Precedence → Record in NOTATION.md [NEW]

### 5a. Endorse #607's `infixr` ladder [NEW]

- **Point**: NOTATION.md is currently silent on logical connectives; #607 is effectively
  SETTING the library-wide connective standard. Endorse the ladder explicitly:

  ```
  ↔  20  (infixr) — loosest
  →  25  (infixr)
  ∨  30  (infixr)
  ⊗  35  (infixr) — tensor
  ∧  36  (infixr)
  ¬  40  (prefix) — tightest unary
  □  40  (prefix)
  ◇  40  (prefix)
  ```

- The fork's current non-assoc `infix` for `∧`/`∨`/`→` is weaker (e.g., `a ∧ b ∧ c` is a
  parse error with non-assoc); #607's `infixr` is the superior choice.

### 5b. Open question: `→` at 25 vs. core `→` [NEW]

- **Point to raise**: `→` at precedence 25 inside an `open scoped HasImpl` scope shadows
  Lean's core `→` (Prop implication). Ask fmontesi whether mixed object-/meta-level proof
  contexts parse correctly and whether this has been tested.

### 5c. Concrete offer: write the NOTATION.md section [NEW]

- Offer to open a follow-up PR to record the agreed ladder in NOTATION.md (a pure doc addition,
  very low risk). This is a concrete, unblocking contribution.

---

## Priority 6: Bundles as a Follow-Up PR [NEW]

### 6a. Do NOT push bundles into #607 [NEW]

- **Point**: The fork's downstream development (tasks 229/254/260/266/340; Modal/Temporal/
  Bimodal/LTL) depends on `PropositionalConnectives`, `ModalConnectives`, `BimodalConnectives`,
  etc. These are *additive* over #607's atomic classes and should land as a **separate follow-up
  PR**, not inside #607.

### 6b. The one ask for #607 re: bundles [NEW]

- **Point**: Only ask that #607's atomic classes be shaped so a bundle can `extend Bot, HasImpl,
  HasAnd, HasOr`. This is already true of #607's current design — no change is needed to
  satisfy it. Mention it as positive confirmation.
- Also note: bundles need `neg`/`top` defaulted (Johansson encoding); confirm that with
  Mathlib `Bot` and `HasImpl`, these defaults can be stated polymorphically.

---

## Priority 7: Modality Note (Low Priority) [ALREADY RAISED]

- Already raised in prior comment: `◇ := ¬□¬` is a fork-local instance choice, not a
  #607 blocker. Keep this brief.
- ctchou's open question (parameterised box/diamond for HML): mention as future work without
  requesting any action in #607.
- #607's `HasBox`/`HasDiamond` as independent primitives: this is fine for classical modal;
  non-classical systems would need a separate treatment, not in scope for #607.

---

## Priority 8: Closing — Concrete Offers [NEW]

**Point**: Close with concrete offers that position the review as *unblocking* #607, consistent
with Waring's ask to "help that get merged":

1. Open a follow-up PR with the `PropositionalConnectives`/`ModalConnectives`/… bundle
   hierarchy, built on top of the merged atomic classes.
2. Write the NOTATION.md connective-precedence section.
3. Help reproduce and resolve Waring's `grind`-through-notation issue in #607's proof context
   (the fork provides a test bed; the architectural cause is now identified — see Priority 4).
4. Register the fork's `PL.Proposition` instances against #607's merged classes once it lands
   and the fork rebases.

---

## Verified Lean Exhibit Summary (for easy reference)

All snippets compiled against CSLib's codebase (2026-06-29, `lake build` successful).

| Claim | Snippet | Result |
|---|---|---|
| HasNot for PL.Proposition via derived neg | `instance : HasNot PL := {not := Proposition.neg}` | ✓ rfl / builds |
| Bridge (A → ⊥) = HasNot.not A | `@[grind =] lemma ... := rfl` | ✓ rfl |
| Bot.bot = .bot | `(⊥ : Proposition Atom) = .bot := rfl` | ✓ rfl |
| Top.top = .imp .bot .bot | `(⊤ : Proposition Atom) = .imp .bot .bot := rfl` | ✓ rfl |
| grind alone, Modal and_iff (Architecture A) | `grind` | ✓ closes goal |
| grind alone, Modal dual (Architecture A) | `grind` | ✓ closes goal |
| simp alone, upstream-like (Architecture B) | `simp` | ✗ no progress |
| grind [HasAnd.and], upstream-like (Architecture B) | `grind [HasAnd607.and]` | ✗ fails |
| simp [HasAnd.and], upstream-like (Architecture B) | `simp [HasAnd607.and]` | ✓ closes |

---

*Assembled 2026-06-29 from reports/01_pr607-engagement.md, reports/02_engagement-strategy.md,
and scratch-verified Lean snippets. All data should be verified against the live PR diff before
any review is posted.*
