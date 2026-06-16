# Teammate D Findings: Strategic Horizons for PR #649 Revision

**Task**: 221 — Revise PR #649 based on reviewer feedback
**Role**: Teammate D — Long-term alignment and strategic direction
**Date**: 2026-06-16

---

## Key Findings

### 1. The PR Landscape and Maintainer Power Structure

CSLib has a formal governance hierarchy. The key actors for logic PRs:

- **arademaker** (@arademaker): Area maintainer for Logic. He merged PR #610 adding himself. His stated interests are logic and knowledge representation. His review activity on #648/#649 is notable by *absence* — ctchou and thomaskwaring are the active reviewers here.
- **ctchou** (@ctchou): Reviewer. Approves or blocks. His #648 feedback on future-only operators is the primary directive for #649. He has now given follow-up approval (PR #649 comments: points 1-4 acknowledged). The critical observation: ctchou already has a CHANGES_REQUESTED on #649, not yet resolved. He did NOT request a semantics split on #649; that was thomaskwaring's request on #648.
- **thomaskwaring** (@thomaskwaring): Reviewer. His #648 feedback drove the entire semantic split request. His comment on PR #648 ends with "Please split the semantics development into a separate PR." He has not yet reviewed #649 formally.
- **fmontesi** (@fmontesi): Lead maintainer. His Modal formula type (`{atom, not, and, diamond}`) conflicts with our design. He is the final arbiter but has not yet commented on #648/#649.

**Strategic insight**: The path to merge is ctchou + one more reviewer approval, or arademaker approval. thomaskwaring is the sophisticated design critic; his buy-in on bot-as-primitive determines whether #648 advances.

---

### 2. Strategic Assessment of Bot-as-Primitive

thomaskwaring raised five objections to `bot` as primitive on PR #648. These are *substantive* design concerns, not stylistic quibbles. The current PR #648 (and by extension #649, which stacks on it) cannot ignore them.

**His objections, evaluated**:

| Objection | Strategic Assessment |
|-----------|---------------------|
| Bot behaves like atom in minimal logic | Technically accurate but misses the point: bot is *special* in classical and intuitionistic logics. Primitive bot enables a uniform treatment across all three logic strengths. |
| `[Bot Atom]` assumptions are not a big deal | True for minimal logic; false for completeness proofs where bot's distinctness from atoms is essential (e.g., Lindenbaum construction needs `atom x ≠ bot`). |
| Extra constructor makes proofs verbose | Legitimate; but existing `Temporal.Formula` already uses `{atom, bot, imp, untl, snce}` and our temporal completeness proofs work. The verbosity is manageable. |
| `WithBot.some` substitution is important | Good point. This is the strongest objection: substitutions that embed `Atom → Formula` without sending atoms to bot are common. The current design handles this via `Formula.atom ∘ f` but `WithBot.some` is cleaner. |
| `⊤ := a → a` is a feature | This is a value judgment; both designs are defensible. The five-primitive design with `top := bot → bot` loses some provability-only reasoning, but modal/temporal logics heavily use explicit `⊤` in axioms (e.g., T axiom: `□⊤`). |

**Strategic recommendation**: Do NOT assert that bot-as-primitive is *unambiguously better*. Acknowledge thomaskwaring's points explicitly, especially the WithBot substitution point. Frame the design as a deliberate choice that optimizes for (a) uniform treatment across classical/intuitionistic/minimal, (b) temporal and modal embedding where `bot` appears in derived semantics (e.g., `⊤ = bot → bot` is used in `toTemporal`), and (c) compatibility with CSLib's existing `Modal.Proposition` which already uses `{atom, bot, imp, box}`.

The most compelling independent argument for `bot` as primitive in #648's context: the propositional formula type is the *foundation* for Modal and Temporal, which derive `¬φ := φ → ⊥`. Having bot as an atom-level concept makes the semantics section's Kripke entailment relation cleaner — the `bot` case is just `False`, no need for a `[Bot Atom]` instance and separate entailment.

---

### 3. The `imp` vs `impl` Question

**Evidence from the codebase**:

- `Modal.Proposition` (our codebase, already in CSLib upstream): uses `| imp (φ₁ φ₂ : Proposition Atom)` — **`imp`**
- `Logics/Propositional/Defs.lean` (thomaskwaring's existing code in upstream): uses `| imp (a b : Proposition Atom)` — **`imp`**
- PR #607 (fmontesi): uses `HasImpl` / `Proposition.impl` — **`impl`**
- PR #587 (thomaskwaring): uses `HasImpl` — **`impl`**

The existing upstream code (merged) uses `imp`. The two pending PRs (#607, #587) use `impl`. This means the community may be converging on `impl` but the settled law is `imp`.

**Strategic recommendation**: Keep `imp` for now. The argument that "CSLib's existing formula types use `impl`" is wrong — only our *unmerged* PR uses `impl`; the upstream merged code uses `imp`. thomaskwaring's actual existing code in `Defs.lean` uses `imp`. This is the decisive factor.

If the community later converges on `impl` via #607, a renaming PR can handle it uniformly. Do NOT rename now based on unmerged PRs.

---

### 4. LTL Semantics Split: Strategic Implications

thomaskwaring on #648 and the task description note that `LTL/Semantics/Satisfies.lean` should be removed from this PR. This is now already done (task 220 created it, but the PR #649 currently includes it as one commit on the branch). The question is whether to keep it in the PR.

**Arguments for keeping LTL semantics in PR #649**:
- ctchou's #649 review explicitly asks for "temporal logic that can talk about omega-executions" — including semantics is *responsive* to his request
- The semantics file is small (~55 lines) and separable
- Having semantics makes the PR more complete (syntax without semantics is a stub)

**Arguments for splitting out**:
- thomaskwaring explicitly requested splitting semantics into its own PR (comment on #648)
- The split allows the formula type design to be reviewed/merged independently
- This reduces the number of issues in review simultaneously
- CSLib reviewers have a strong preference for small focused PRs

**Strategic recommendation**: Split the semantics out. thomaskwaring is the more sophisticated design reviewer and will likely block if we don't comply. A separate PR for `LTL.Semantics.Satisfies` (plus future LTS bridge) is also more coherent intellectually — the satisfaction relation is where the LTS connection question belongs.

More importantly: keeping semantics in PR #649 mixes two reviewers' concerns — ctchou wants LTS integration (which the current semantics doesn't deliver) while thomaskwaring wants the semantic design (Heyting algebra approach) to be discussed separately. Splitting satisfies both.

---

### 5. Reference Strategy: Avigad Is the Right Choice

ctchou recommends Avigad's *Mathematical Logic and Computation* (Cambridge, 2022/2023). thomaskwaring agrees on avoiding 1930s German papers.

**Key facts**:
- Avigad's book is already recommended by ctchou for PR #648; adopting it for #649 demonstrates responsiveness
- Avigad covers propositional syntax and semantics in Chapters 2-3 (as ctchou cites)
- For temporal logic specifically, Avigad does not cover LTL directly — the temporal operators `Until` and `Since` are Kamp (1968) and Pnueli (1977)
- **Kamp1968** (phdthesis, English) and **Pnueli1977** (FOCS, English) and **Burgess1984** (Handbook of Philosophical Logic, English) are all in the bib and all in English
- **VardiWolper1986** (LICS, English) is also in the bib

**What needs to change**:
- Remove Johansson1937, Gentzen1935 (German), Heyting1930 (German) from docstrings in Temporal/LTL files — these are inherited from PR #648's propositional layer
- For PR #649's temporal content: use Kamp1968 (English phdthesis), Pnueli1977, Burgess1984, VardiWolper1986 — all English, all already in bib
- Add Avigad2023 (not yet in bib) if cited in the propositional foundation references

**BibKey format**: CSLib uses `{AuthorSurname}{Year}` — so Avigad would be `Avigad2023`.

---

### 6. Relationship with PRs #607 and #587

**PR #607** (fmontesi, feat(Logic): logical operators):
- CHANGES_REQUESTED, dirty merge state
- Uses `HasImpl`, `HasNot` — naming incompatible with our `HasImp`
- Adds connective instances for Modal, Propositional types
- If #607 merges first, our `Connectives.lean` additions would conflict on naming

**PR #587** (thomaskwaring, feat(Foundations/Logic): Notation typeclasses and models):
- DRAFT status
- Proposes `Models α β` typeclass for semantics — this is the type of abstraction thomaskwaring hints at with "Heyting algebra" in his #648 comment
- Has path collision with `Cslib/Foundations/Logic/Connectives.lean`
- thomaskwaring's preferred direction is more abstract than ours

**Strategic implication**: thomaskwaring is building toward a more abstract semantic framework (#587). His request to split semantics from #648/649 is partly motivated by this — he wants the semantic layer to land via his #587 framework, not as an ad hoc addition to our formula files.

This means: removing semantics from PR #649 not only satisfies the stated request, it also *avoids a future conflict* with thomaskwaring's #587 approach. Let #587 land first (or coordinate), then contribute LTL semantics using that framework.

---

### 7. The Modal Formula Type — The Elephant in the Room

The most significant long-term strategic risk is the Modal formula type conflict:

- **Our local `Modal/Basic.lean`** uses `{atom, bot, imp, box}` — a Hilbert-friendly design
- **Upstream `Modal/Basic.lean`** (fmontesi) uses `{atom, not, and, diamond}` — a connective-rich design

These are fundamentally incompatible. PR #649 stacks on #648 (propositional connectives), which in turn would eventually lead to a Modal PR that conflicts with fmontesi's design.

**This must be resolved on Zulip before submitting any Modal PR.** The propositional work in #648/#649 does not expose this conflict yet — but any future PR touching Modal will hit it.

**Strategic recommendation**: After #648 and #649 land, open a dedicated Zulip thread: "Proposal: standardize modal formula primitives on {atom, bot, imp, box}." Invite fmontesi, ctchou, thomaskwaring. The argument for our design:
- Hilbert K axiom and necessitation are cleanly stated with `imp` and `box`
- Diamond is derived classically as `¬□¬`, matching textbook presentations (Blackburn2001 Chapter 1)
- The `{atom, not, and, diamond}` design requires classical logic to derive `□` from `◇`, making it less suitable for non-classical modal logic

---

### 8. PR Sequencing Recommendation

```
NOW:   PR #649 (revision) — temporal formula + LTL formula syntax ONLY
           Remove LTL.Semantics, remove Johansson/Gentzen from docstrings
           Acknowledge bot-as-primitive trade-offs explicitly
           Keep `imp` naming (not `impl`)
           Stack on rebased #648

NEXT:  PR #648 revision — responds to ctchou + thomaskwaring after #536 merge
           Now merged: #536 (inference systems) already landed

THEN:  Propositional Metalogic PR (Soundness + StrongCompleteness for PL)
           Can reference Avigad chapters 2-3

THEN:  LTL Semantics PR (Satisfies + LTS bridge + Valid/Satisfiable)
           Coordinate with #587 (thomaskwaring's Models typeclass)

THEN:  [Zulip thread: modal formula type resolution]

THEN:  Modal PR (if resolved favorably) or defer to upstream team
```

---

### 9. Quick Wins That Build Goodwill

Before pushing bigger design changes, consider these tactical moves:

1. **Respond to ctchou's #649 CHANGES_REQUESTED explicitly**: The comment on PR #649 already acknowledges his points. We should formally request re-review now that the latest commit exists.

2. **Thank thomaskwaring in Zulip**: His design feedback is substantive and correct. Acknowledging his expertise publicly (e.g., "thomaskwaring's point about WithBot.some substitution is well-taken; we're explicitly not claiming the five-primitive design is unambiguously superior") builds trust.

3. **Reference arademaker** (logic area maintainer) in the PR: He hasn't commented yet. A polite tag ("@arademaker as logic area maintainer, would value your input on the propositional formula type design") invites his review and may accelerate approval.

4. **Explicitly note Kripke.lean follows**: ctchou mentioned Kripke semantics. Saying "Kripke.lean exists locally and is planned after classical semantics land" turns a potential future objection into a positive signal.

---

## Recommended Approach

**Core recommendation**: Treat PR #649 as a *minimal, focused contribution* — temporal formula syntax + LTL formula syntax, without semantics. This maximizes the probability of merge by:

1. Respecting thomaskwaring's explicit request to split semantics
2. Keeping the scope small enough that ctchou's CHANGES_REQUESTED can be resolved cleanly
3. Avoiding entanglement with thomaskwaring's #587 semantic framework
4. Not creating new dependencies on design questions (#607 vs #648 naming) that aren't resolved yet

The PR description revision should:
- Note the stack on merged #536 explicitly ("rebased on main as of [date] after #536 merged")
- State the semantics split honestly: "LTL semantics (Satisfies, Valid, Satisfiable) deferred to a follow-up PR, pending coordination with PR #587 on the Models typeclass approach"
- Acknowledge bot-as-primitive trade-offs: one sentence each for the strongest objections (WithBot.some substitution, verbosity), then explain why the design is chosen for temporal/modal compatibility
- Use Pnueli1977, Kamp1968, Burgess1984 as primary references (all English, all in bib)
- Note `imp` naming is consistent with merged upstream code (`Logics/Propositional/Defs.lean`, `Modal/Basic.lean`)

**Should we concede on bot-as-primitive?**

No. thomaskwaring's objections are valid but not blocking — they're design preferences. The five-primitive formula type is already implemented in the temporal and bimodal metalogic (10,000+ lines). Conceding now would require a complete rewrite. Instead, acknowledge the trade-offs honestly and let the reviewers decide.

If thomaskwaring ultimately blocks on this, the escalation path is to request arademaker (logic area maintainer) as a tiebreaker.

---

## Evidence/Examples

**Why `imp` not `impl`**: `Cslib/Logics/Propositional/Defs.lean:87` uses `| imp (a b : Proposition Atom)` — thomaskwaring's own merged code. The word "impl" only appears in unmerged PRs #607 and #587.

**Why semantics split matters**: thomaskwaring's comment on #648: "Please split the semantics development into a separate PR. The point of requesting that large contributions are split up is not just length, but also so that conceptually separate issues can be discussed independently." This is a principled request, not just length management.

**Why the Heyting algebra hint matters**: thomaskwaring says "imo the right way to resolve the Bool/Prop issue is to define the interpretation in any (generalised) Heyting algebra." His PR #587 (`feat(Foundations/Logic): Notation typeclasses and models`) is building exactly this framework. He wants LTL semantics to use this framework when it lands.

**References already in bib (English)**: `Pnueli1977`, `Kamp1968` (English phdthesis), `Burgess1984`, `VardiWolper1986`, `GPSS1980` — these cover the temporal and LTL content in PR #649 without needing German papers.

---

## Confidence Level

- **Imp vs impl naming**: HIGH — the evidence is clear; merged upstream code uses `imp`
- **Semantics split recommendation**: HIGH — thomaskwaring's request is explicit and strategic
- **Bot-as-primitive: acknowledge trade-offs, don't concede**: HIGH — the design is deeply embedded; honest acknowledgment is the right move
- **PR sequencing**: MEDIUM-HIGH — depends on merger timelines and #587 progress
- **Modal formula type conflict**: HIGH concern, MEDIUM on resolution timeline
- **Goodwill tactics**: HIGH — low cost, high expected value
