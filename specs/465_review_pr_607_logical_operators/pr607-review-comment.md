> DRAFT — review and personalize before posting.
>
> Fact-checked 2026-07-02 against `gh pr checks/diff/api` for PR #607, the failing CI run
> log, PR #648/#662 diffs, Lean core source, and the Zulip threads. One substantive
> correction was made in item 3 (the naming status quo was misstated); details in
> draft-factcheck-report.md.

# Review comment for PR #607 (feat(Logic): logical operators)

Thanks for putting this together, Fabrizio. The shared-typeclass direction is the right one and most of the mechanics look good. A few blocking items and a couple of decisions we should settle before merge. I've grouped them below with file:line references.

## 1. CI is red: HML LogicalEquivalence not migrated

The signature change to `LogicalEquivalence` in `Cslib/Foundations/Logic/LogicalEquivalence.lean` was not propagated to `Cslib/Logics/HML/LogicalEquivalence.lean`, which still calls the old 3-argument form. That produces the build failure at HML `LogicalEquivalence.lean:105-106` ("failed to synthesize HasContext (Satisfies.Judgement State Label)" at 105:11, application type mismatch at 106:58). That file needs updating to the new inference-system-parameterized form (`LogicalEquivalence S` / `HasLogicalEquivalence`) to get CI green.

## 2. The HML failure exposes a real design gap (label-parameterized modalities)

Migrating HML isn't purely mechanical. HML needs *label-parameterized* box/diamond: its `Proposition` type has `box (μ : Label)` and `diamond (μ : Label)` constructors. The unary `HasBox α` with `box : α → α` in this PR cannot express that. This is the same question ctchou raised in review ("do we need parameterized box and diamond for HML?") and it hasn't been answered. We'll need a `HasLBox`/`HasLDiamond` (or otherwise parameterized) variant alongside the unary one. Worth deciding the shape now, since HML is the concrete consumer that forces it.

## 3. Naming: `impl` vs `imp`

#607 uses `HasImpl` / `impl`, which matches the existing `Proposition.impl` in the Modal and Propositional code on main. My PRs #648 and #662 rename that to `imp` — matching the natural-deduction rule names `impI` / `impE` in #648 and the `imp` constructor convention in FormalizedFormalLogic's Foundation. So this PR is the status-quo side of that split and mine are the renaming side; either way we should pick one library-wide before merge — it's a cheap rename now and an annoying churn later. I'm happy to align either way: if you prefer `impl`, I'll switch #648/#662 to match. Just want one decision on record.

## 4. Operator file layout — needs an explicit decision

There are three opinions on record and no resolution: chenson2018 and eric-wieser have both suggested consolidating the operators into a single file; ctchou has proposed a 3-file split (Modal for box/diamond, Tensor by itself, Propositional for the rest). Right now the PR ships one-file-per-operator under `Cslib/Foundations/Logic/Operators/`. Could you make the call explicitly so reviewers stop relitigating it? I don't have a strong preference; I just want it settled.

## 5. Notation precedences -> NOTATION.md, plus two deviations from Lean core

Please record the operator notation precedences in NOTATION.md. Two of them deviate from Lean core and are worth calling out (either match core or note the deviation deliberately):

- `HasAnd` is declared `infixr:36`, but core `And` is `infixr:35`. (The 36 carries over the old Modal `infix:36 " ∧ "`, so it's an inherited cslib-ism, not a new choice.)
- `HasIff` is declared `infixr:20` — same precedence as core, but core `Iff` is *non-associative* `infix:20`, so `a ↔ b ↔ c` parses under this PR and is a parse error in core.

Mismatched precedence/associativity with core is the kind of thing that silently changes how mixed expressions parse, so it's better pinned down now.

## 6. The one load-bearing conflict with #648: `Propositional/Defs.lean`

This is the item that actually blocks a clean stack. #607 keeps `⊥` defined as `atom ⊥`, gated on `[Bot Atom]`. #648 makes `⊥` a primitive constructor of the formula type. These two designs of `Proposition` are mutually exclusive.

I'd argue for primitive `⊥`, on substitution-invariance grounds: a nullary operation is fixed by every substitution, so axiom schemes like `⊥ → A` are automatically substitution-closed. With `⊥ = atom ⊥`, every substitution-closure theorem picks up a side condition `σ(⊥) = ⊥`, which then has to be threaded through everything downstream. This is where the Propositional Logic Zulip thread landed: Thomas proposed ⊥-as-primitive with efq as a rule (making IPL the base logic) as the compromise, and #648 now implements exactly that.

Proposal: either #607 adopts primitive `⊥` in `Defs.lean`, or #607 cedes that file's `Proposition` design to #648 and leaves `Defs.lean` out of scope. Once we settle (3) naming and (6) this, I'm happy to rebase #648/#662 onto #607 in one pass so we don't duplicate work.

## 7. What's already right

To be clear, most of this PR is going the right direction and I don't want the list above to read as negative:

- The shared `Has*` typeclasses are the correct abstraction, and I agree with keeping the `Has*` prefix (I saw you defend it against eric-wieser's Lean-3-ism comment — I endorse that).
- The grind-into-notation `_def` lemmas are a nice touch.
- Reusing Mathlib's `Bot` / `Top` rather than reinventing them is the right call.

Happy to pair on the HML migration and the rebase once the two decisions above are made.
