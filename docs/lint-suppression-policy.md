# Linter Suppression Policy

## The rule

| Form | Status |
|---|---|
| `set_option linter.X false` (no trailing `in`) | **Gated.** Counts may only decrease. |
| `set_option linter.X false in` (declaration-scoped) | Always allowed. |

Enforced by `scripts/check-lint-suppressions.sh`, which runs in the `Lint Hygiene` CI workflow
and as step 6 of `scripts/pre-pr-check.sh`.

## Why blanket suppressions specifically

A file-scoped suppression silences every violation in the file, **including every future one**.
That makes it a ratchet rather than a debt: code added to an already-suppressed file is unlinted
by construction. Ordinary tech debt gets noisier as the file grows and eventually forces
attention; this gets quieter, which is why it went unnoticed long enough to accumulate 276
instances across 108 files.

A declaration-scoped suppression has the opposite property — it dies with the declaration it
annotates and cannot silence anything written later. It decays. That asymmetry, not tidiness, is
the whole reason only one of the two forms is gated.

## How this happened here, for the record

A survey of the tree found **14 of 14 sampled files carried their blanket suppression in their
very first commit**. None were bolted on later in response to a linter complaining. The header is
copied from a neighbouring file when a new file is started — there is no template to fix, which
is precisely why a gate is the intervention that works: it interrupts the copy at the moment it
happens, with an explanation.

Suppression density also tracks incompleteness. `Separation/` and `CounterexampleElimination/`
dominate the counts and are the same directories carrying the `sorry`s. Silencing a style linter
while fighting elaboration mid-proof is a reasonable local move; the problem is only that the
local move is file-scoped and permanent.

## Working with the gate

```bash
bash scripts/check-lint-suppressions.sh            # verify (exit 1 on regression)
bash scripts/check-lint-suppressions.sh --list     # current counts, worst first
bash scripts/check-lint-suppressions.sh --update   # re-baseline after a reduction
```

**When the gate fails**, scope the suppression to the declaration that needs it:

```lean
set_option linter.unusedSectionVars false in
theorem foo ...
```

**When you reduce a file's count**, run `--update` and commit `lint-suppression-baseline.txt`
alongside the change. That locks the gain in — the ceiling can never drift back up.

**If a file-scoped suppression is genuinely justified**, raise its baseline in the same commit
and say why in the commit message. The gate exists to make that a deliberate, reviewable act
rather than a silent side effect.

## Two traps, both already hit in this tree

Both were caught only by rebuilding immediately, which is why the audit protocol requires it:

- **`omit [X] in` is not interchangeable with `set_option linter.X false in`.** `omit` removes
  the instance from scope and changes the declaration's *elaborated type*. It can break
  compilation for declarations whose proof body needs the instance even when the stated type does
  not. `set_option` is warning-only and always safe.
- **`set_option ... in` must precede a declaration's doc comment**, never sit between the doc
  comment and the declaration, or the file fails to parse with
  `unexpected token 'set_option'; expected 'lemma'`.

A related hazard when narrowing `style.openClassical`: `set_option linter.X false in open Y`
scopes the `open`'s downstream visibility to that single command, so a later `Finset.filter`
relying on `Classical.propDecidable` fails with a stuck `DecidablePred` metavariable. Use a
plain unscoped `set_option` line before the `open` instead.

## Relationship to the `--wfail` build gate

The two are independent and both are needed. `lake build --wfail --iofail` catches warnings that
are *visible*; a blanket suppression makes that gate pass by hiding the warning rather than
fixing it. A green `--wfail` build is therefore not evidence that suppressions did not grow —
this ratchet is what distinguishes the two cases.
