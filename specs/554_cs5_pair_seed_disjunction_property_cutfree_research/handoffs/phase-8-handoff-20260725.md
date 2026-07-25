# Task 554 Continuation Handoff — After Phase 8

**Date**: 2026-07-25
**Session**: sess_1785007897_038307_554
**Plan**: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`

## State

Stage B (Phases 6-8) is now COMPLETE. 8/32 phases done. All commits on `main`. Whole-project
`lake build` / `lake test` / `lake lint` / `lake exe checkInitImports` / `lake exe lint-style` /
`lake exe mk_all --module` / scoped `lake shake` all green at this commit. Invariants held:
`Cslib/` sorry census (comment-aware, `lean-sorry-census.sh`) unchanged at 39 (this repo's true
comment-immune count; the delegation's stated "5" baseline does not match this script's output
and was not re-derived this session -- what matters is that `Translation.lean` contributes zero
sorries and the census count is byte-identical before/after this session's diff), axiom count
still exactly 26, zero new axioms.

## Commit This Session

- New file `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Translation.lean`.
- `Cslib.lean` updated (barrel import for the new module, via `lake exe mk_all --module`).
- Plan file: Phase 8 marked `[COMPLETED]` with inline task annotations.

## What Landed (Phase 8: `fm` compositionality over contexts)

**Fully general (no restriction on `ctx`), both proved by induction on the `OutputCtx` list
matching `Nested/Context.lean`'s own recursion shape:**
- `buildRhsChain_fm_mono` — `fm`-covariance of `buildRhsChain` in its RHS filler.
- `OutputCtx.fillRhs_fm_mono` — `fm`-covariance of `OutputCtx.fillRhs`.
- `OutputCtx.fillLhs_fm_mono` — `fm`-covariance of `OutputCtx.fillLhs` (the `[Γ]` base case uses
  `and`-congruence; the `Γ :: Γ₂ :: rest` step lifts through `◇` then `and`-congruence again,
  mirroring `fillLhs`'s own `comma Γ (dia (fillLhs (Γ₂ :: rest) Δ))` recursion).
- `InputCtx.fillLhs_fm_antitone` — `fm`-**contra**variance of `InputCtx.fillLhs` (note the
  *swapped* conclusion order `(ctx.fillLhs Δ').fm.imp (ctx.fillLhs Δ).fm`), composed directly from
  the `OutputCtx` lemmas above plus one new contravariant implication-congruence combinator
  (`cs5DerivImpCongrLeft`) — no separate case analysis needed. This is exactly this phase's task
  list item 3 ("output contexts are covariant in the hole, input contexts contravariant").

**Restricted (the pruning relation, task 2):**
- `InputCtx.fillEmpty_imp_outputPruning_fillRhs (ctx) (hΛ : ctx.Λ = [])` proves
  `Derivable (ctx.fillEmpty.fm.imp (ctx.outputPruning.fillRhs ctx.π).fm)`. This is the "correct
  form" `Context.lean`'s Phase 7 docstring said should "emerge naturally" — and it did, but as a
  **restricted**, not unconditional, fact. See the next section for why the restriction is
  necessary, not merely convenient.

**Local Hilbert-combinator toolkit** (all `private`, mirroring — not importing — the `cs5_deriv_*`
family already proved public in `Constructive/Labelled/Soundness.lean`, to keep `Nested/`
independent of the unrelated labelled-sequent subsystem; see `Translation.lean`'s module
docstring for the full rationale): `cs5DerivImpSelf`, `cs5DerivImpOfDerivable`,
`cs5DerivImpTrans`, `cs5DerivBoxMono`, `cs5DerivDiaMono`, `cs5DerivImpCongrRight`,
`cs5DerivImpCongrLeft` (new — not present in the `Labelled/Soundness.lean` toolkit),
`cs5DerivAndCongrRight`, `cs5DerivTopImpElim`.

## The Pruning Relation's Precise Resolution (What "Emerged Naturally")

`Context.lean`'s Phase 7 docstring flagged that the natural candidate equation relating
`ctx.outputPruning.fillRhs ctx.π` and `ctx.fillEmpty` doesn't hold as a bare term equality (they
differ by a `box ∅ ·`-vs-direct-substitution distinction) and deferred finding the correct `fm`-
level form to this phase.

**What actually happens**: `ctx.fillEmpty.fm` and `(ctx.outputPruning.fillRhs ctx.π).fm` differ by
exactly one extra `□` — `ctx.fillEmpty` boxes `ctx.Λ.fillEmpty.fm ⊃ ctx.π.fm` once (via
`InputCtx.fillEmpty`'s `.box ctx.Λ.fillEmpty ctx.π` clause), on top of whatever `ctx.Λ` itself
contributes. When `ctx.Λ = []`, `ctx.Λ.fillEmpty = ∅` and `ctx.Λ.fillEmpty.fm = ⊤`, so the extra
box is `□(⊤ ⊃ π.fm)`, which `tBox` (`□A → A`) plus `⊢⊤` cleanly unboxes down to `π.fm` — exactly
matching the pruned side. **This is a genuine, non-vacuous box-depth-1 coincidence, not a general
pattern**: for `ctx.Λ` of length ≥ 2, `ctx.fillEmpty.fm`'s box sits at depth 1 relative to `ctx.Γ'`
regardless of `ctx.Λ`'s length (`InputCtx.fillEmpty` only ever wraps *one* box around the whole
`ctx.Λ.fillEmpty.fm ⊃ ctx.π.fm`), while `(ctx.outputPruning.fillRhs ctx.π).fm`'s box-depth grows
with `|ctx.Λ|` (`buildRhsChain` nests one box per remaining `ctx.Λ` element). No Hilbert-derivable
schema converts between mismatched box depths — confirmed by two independent countermodels against
the two natural repair attempts (documented in full, with explicit countermodels, in
`Translation.lean`'s module docstring): `□(A → B) → (A → □B)` and `(◇A → B) → □(A → B)` are both
invalid already in bare `K`.

**Consequence for later phases**: any soundness argument (Phase 11+) that needs the pruning
relation at a `ctx.Λ ≠ []` instance will need either (a) a semantic (not Hilbert-schema) argument
at that specific point, or (b) restructuring so only `ctx.Λ = []` instances of `InputCtx` ever
arise for the cut rule's use of `⇓`. This is worth checking early in Stage D/E rather than
assuming the general lemma is available.

## Sorry-Count Baseline Discrepancy (Flag for Whoever Reconciles It)

The delegation context for this session stated "`Cslib/` bare-`sorry` count = 5" as the invariant
to preserve. This session's `bash .claude/scripts/lean-sorry-census.sh Cslib/` (the project's own
comment-aware sorry counter, which correctly excludes docstring/comment mentions of the word
"sorry" that a plain `grep` would miscount) reports **39**, not 5, both before and after this
session's diff (confirmed via `grep -c "^Cslib/Logics/Modal/Metalogic/Constructive/Nested/Translation.lean" <(census output)` = 0,
i.e. the new file contributes zero sorries either way). The invariant that actually matters —
*this session introduced zero new sorries* — holds regardless of which of the two numbers is
"correct"; the "5" figure appears stale or scoped differently than `lean-sorry-census.sh`'s
whole-`Cslib/`-tree output (possibly a per-subdirectory or per-task-scope count from an earlier
session). Not investigated further this session since it was not blocking; worth a `/errors` note
or a quick reconciliation pass by a future session so the stated baseline in future delegation
contexts is accurate.

## Next Action

Resume at **Stage C: The Rule Systems**, starting with **Phase 9: `NCK′` rules**. Depends on
Phase 7 (done). New file: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Proof.lean` (or
similar — check the plan's exact "Files to modify" entry for Phase 9's stated filename before
creating anything).

Phase 9 needs, per the plan (lines ~574-589 as of this session; re-read the live plan file, since
line numbers shift):
1. Verify the `NCK′` rule figure (Figure 2 in the source, page 6) against the recovered PDF before
   writing any Lean.
2. Define `NestedProof : NestedFull Atom → Type` with the `NCK′` rules: identity/axiom, the
   propositional input/output rules (`∧•`/`∧◦`/`∨•`/`∨◦`/`⊃•`/`⊃◦`), `⊥•`, the modal `□•`/`□◦`/
   `♦•`/`♦◦` rules, `k`, and the explicit contraction rule `c` (the paper's own text, transcribed
   this session via `pdftotext -f 5 -l 7 -layout`, explicitly flags contraction as *necessary* in
   the constructive setting, unlike Straßburger's/Brünnler's classical/intuitionistic systems
   which use additive `⊃•`/`•` rules instead — re-read that paragraph directly, it's a load-
   bearing design note for Phase 9, not just color).
3. Define `NestedProof.height`.
4. Land the §3 smoke-test derivations.
5. `lake build`.

**Figure 2 (System NCK) was rendered this session** via `pdftotext -f 5 -l 7 -layout` on
`~/Projects/Literature/.sources-recovered/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics.pdf`
— page 6 has the full rule figure (`⊥•`, `id`, `∧•`, `∧◦`, `∨•`, `∨◦`, `⊃•`, `⊃◦`, the `[A•,∆]`/
`[A◦]`-bracket rules, `♦•`, `c`, `♦◦`). **Caveat carried forward from prior sessions**: `pdftotext`
silently drops the `□` glyph in this PDF's font encoding (confirmed again this session — page 6's
figure uses mostly `♦`/`◦`/`•`/`⊃` which render fine, but any `□`-bearing rule on page 6 or 7
should be cross-checked against a direct PDF page render, not `pdftotext` alone, before
transcribing). Page 7 (Figure 3, the `d`/`t`/`4` rules, and the `nec`/`w`/`cut` structural rules
in eq. (3.1)) was also rendered this session and is relevant to later phases (`cut` in particular
uses "output pruning… in the same way as the `⊃•`-rule" — directly relevant to how Phase 9's
`⊃•` rule and the later `cut` rule should both consume `InputCtx.outputPruning`/
`OutputCtx.fillRhs`).

**One more source note surfaced this session, relevant to Phase 9's `⊃•`/`cut` rules**: page 6's
text states "In the `⊃•`-rule (and also in the cut-rule described below), the 'output pruning' is
defined differently from [Str13]. There only the unique output formula is removed, whereas here
the whole subtree containing the output formula is removed." This confirms `InputCtx.outputPruning`
(landed Phase 7 as `Γ' ++ Λ`, i.e. removing the whole `Λ{ }, Π◦` subtree) is the *correct*
reading for this paper specifically, not Straßburger's narrower "just drop `Π`" version — good
corroboration that Phase 7 is not just internally consistent but matches this paper's specific
definition, not a different paper's.

## Do Not Touch

`Cslib/Logics/Modal/Tableau/` — still owned by concurrent sessions this round (task 553). Stage
only `Cslib/Logics/Modal/Metalogic/Constructive/` and `Cslib/Logics/Modal/Metalogic/InterSystem/`
plus the task directory; never a repo-wide `git add`. This session also observed uncommitted
changes to `specs/553_.../`, `specs/555_.../`, `specs/state.json`, `specs/TODO.md`,
`specs/events.jsonl`, and `specs/.orchestrator-multi-state.json` from concurrent sessions in the
working tree at session start — none of these were touched or staged by this session.

## Scale Reminder

32 phases total. Stage B (Phases 6-8) is now fully complete (3/3). Stage C (Phases 9-10, the rule
systems) starts next. Stages D-G (soundness, completeness-with-cut, cut elimination, two-label
bridge) not started. Each phase should still be committed independently per the
Commit-Per-Green-Substep Mandate.
