# Research: Promote openBranch_countermodel Witness Probes to CslibTests

## Task

Promote the four machine-checked witness probes at
`specs/591_decide_openbranch_countermodel_disposition/scratch/` into `CslibTests/` so they are
CI-protected, mirroring `CslibTests/BetaSplitRefutation.lean`. `file_scope` for the implementation
task is `["CslibTests/"]`.

## The Four Probes: What Each Computes

All four import only `Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`,
`Cslib.Logics.Propositional.Defs`, `Cslib.Foundations.Logic.Tableau.Branch` (MinProbe.lean also
imports `Minimal.Soundness`, though this appears unnecessary — see below). None touch private
declarations; all call only the public `intuitionisticTableau` / `minimalTableau` entry points
(simpler than `BetaSplitRefutation.lean`, which had to recreate the private `intExpandBranches.go`
locally as `goRaw`).

| File | What it checks | Runtime (`lake env lean`, this machine) |
|---|---|---|
| `WitnessProbe.lean` | For `phiRef1`, four specific edge-set candidates against `upwardClosed`/`evalF`: empty, raw tree, pruned `[(1,0)]`, augmented. Confirms `[(1,0)]` is a witness (`upwardClosed=true`, `¬forces phiRef1=true` — i.e. the pair is `(true,false)`) and the other three are not. | **~6.5s** — fast, safe for CI |
| `WitnessSearch2.lean` | `searchWitness`: for 8 formulas (`phiRef1..3`, `exMiddle`, `dblNeg`, `peirce`, `deMorgan`, `dummett`), computes the admissible-edge-pair set `⊑` and **exhaustively enumerates all `2^n` subsets** of it, filtering for ones that falsify the formula. This is the source of the "40 witnesses for `phiRef1`" claim cited in `Scheme.lean`. | **Timed out — no output after 9m10s**, not even for the *first* (`phiRef1`) call. **Not CI-safe as written.** |
| `WitnessSearch3.lean` | `maximalFrameCheck`: computes only the single **maximal** admissible frame (`inclEdges`, no subset enumeration) for the same 8 formulas under `intuitionisticTableau`, plus 4 under `minimalTableau`. This is what backs the "maximal inclusion frame `⊑` is NOT a uniform witness … fails at exactly the `phiRef1`/`phiRef3` family" claim. | **~2.7s** — fast, safe for CI |
| `MinProbe.lean` | For `phiRef1` under `minimalTableau`/`isMinimallyClosed`, checks 5 edge-set candidates via `try1` (val-upward-closed, ⊥-upward-closed, ¬forces). Confirms `[(1,0)]` and `[(1,0),(2,0)]` both discharge **both** upward-closure obligations simultaneously — the fact `Minimal/Completeness.lean:143` cites to retract the "independent refutation" claim. | **~2.5s of computation**, but **currently has a Lean parse error** (see below) — not directly promotable as-is |

**Root cause of the `WitnessSearch2.lean` blowup**: `searchWitness` computes `subsets inclPairs`
(the full powerset of the admissible-pair set) and then filters. Even though the printed
"40 witnesses" figure suggests a small final answer, materializing the whole powerset via `#eval!`
compiled evaluation for `phiRef1`'s branch is what exceeds a 9-minute budget. This is exactly the
scenario the task description anticipated: *"Where a probe's enumeration is too slow for CI,
reduce it to the specific asserted witnesses and keep the full search documented in the module
docstring rather than executed."*

**Recommendation for `WitnessSearch2.lean`**: do not port the `subsets`/`searchWitness` machinery
into the CI-protected file at all. Instead assert only the same **specific witnesses**
`WitnessProbe.lean` already checks directly (fast: `evalF`/`upwardClosed` on one concrete edge
list, no powerset), and record the "40 witnesses total, exhaustively verified interactively but
not re-executed in CI" claim as prose in the module docstring, with a pointer back to the original
scratch file's path for anyone who wants to re-run the full search by hand. This effectively
folds `WitnessSearch2.lean`'s CI-relevant content into (or alongside) the promoted
`WitnessProbe.lean`, since both ultimately certify the same `[(1,0)]` witness for `phiRef1`; the
distinguishing content worth keeping from `WitnessSearch2.lean` is the multi-formula sweep
(`phiRef2/3`, `exMiddle`, `dblNeg`, `peirce`, `deMorgan`, `dummett`), which should also be
converted to single-witness assertions rather than full searches, *if* a witness is known for each
— this needs a concrete witness edge-list per formula, which the current scratch file's
`good.head?` never printed (the run never completed). The implementer should either (a) find fast
witnesses for these formulas separately (e.g. reuse `WitnessSearch3.lean`'s maximal-frame result
where it succeeds — rows 2,4-8 below already witness via the maximal frame, which IS cheap to
compute), or (b) scope the promoted assertions to just `phiRef1` (the formula actually cited by
name in `Scheme.lean`) and document the others as scratch-only, non-promoted evidence.

## The MinProbe.lean Parse Error

`MinProbe.lean` fails to compile cleanly:

```
specs/591_.../scratch/MinProbe.lean:59:75: error: unexpected token '#eval!'; expected 'lemma'
```

Cause: this file (uniquely among the four) prefixes two of its `#eval!` commands with declaration
docstrings (`/-- world table … -/` and `/-- `(edges, val upward-closed, …)`; … -/`) directly above
a bare `#eval!`. Under this repo's `module`-file dialect, a `/-- … -/` doc comment must attach to
a following **declaration** (`def`/`lemma`/`theorem`/etc.), not to a command like `#eval!` — hence
"expected 'lemma'". The other three scratch files avoid this by using plain `--` line comments
before their `#eval!` calls, and `BetaSplitRefutation.lean`/`S4LoopGuardRegression.lean` avoid it
by using the special `#guard_msgs`-argument idiom (`/-- info: … -/` immediately followed by
`#guard_msgs in #eval …`, which the `#guard_msgs` elaborator, not the docstring mechanism,
consumes).

**Fix when promoting**: convert those two `/-- … -/` blocks to `/-! … -/` (free-floating section
doc comments) or plain `--` comments, or — better — replace the bare `#eval!` calls with the
`#guard_msgs` idiom used elsewhere in `CslibTests/` (see below), which sidesteps the issue
entirely since the docstring there is consumed by `#guard_msgs`, not attached to a declaration.

## The CslibTests Promotion Pattern (from `BetaSplitRefutation.lean`, `S4LoopGuardRegression.lean`)

Every promoted regression/witness file in `CslibTests/` follows this shape:

1. Copyright header (`/- Copyright (c) 2026 Benjamin Brast-McKie. … -/`) — **not lint-enforced**
   for `CslibTests/` (`lakefile.toml` sets `weak.linter.style.header = false` for the
   `CslibTests` `lean_lib`), but present in every existing file for consistency.
2. `module` + matching `import` / `public meta import` pairs.
3. A `/-! # Title … -/` module docstring explaining: what is being asserted, why it matters, the
   construction/witness in prose, and (critically) a pointer back to the original scratch file
   path it was promoted from — e.g. `AncestorRedirectRefutation.lean`'s docstring: *"See
   `specs/582_.../scratch_refute_ancestor_redirect.lean` for the original scratch probe this file
   was promoted from."* This is the established citation idiom to reuse for all four probes here
   (pointing at their paths under `specs/591_decide_openbranch_countermodel_disposition/scratch/`).
4. `set_option autoImplicit false` (all four scratch files already have this).
5. Assertions via `/-- info: <exact expected output> -/` immediately followed by `#guard_msgs in`
   then `#eval <expr>` — **not** bare `#eval!`. This is what makes the file's claims CI-protected:
   a `#guard_msgs`-wrapped `#eval` that produces different output than the docstring literal is a
   **build error**, not a silent pass. `S4LoopGuardRegression.lean`'s docstring notes explicitly
   that `#eval` reduces via the compiler and only works from `CslibTests/`, not from inside
   `Cslib/Logics/…` itself — this is *why* these corpora live in `CslibTests/` at all, not merely
   for CI-protection.
6. `weak.linter.privateModule = false` is also set for the whole `CslibTests` lean_lib in
   `lakefile.toml` — irrelevant to these four probes since none touch private declarations.

**Converting bare `#eval!` to the `#guard_msgs` idiom**: the four scratch files currently use bare
`#eval!` (no assertion, no protection — a regression would silently change the printed value with
no build failure). Promotion means running each, capturing the exact printed value, and wrapping
it as `/-- info: <value> -/ #guard_msgs in #eval <expr>` (drop the `!` — plain `#eval` is fine and
is what every existing `CslibTests/` file uses; `#eval!` is a debugging escape hatch for bypassing
warnings, not needed here). I captured current output for all four probes in the table/details
above and below — these are the literal strings the implementer should assert (subject to
re-verification against `mathlib`/`Cslib` at the commit the implementer works from, since these
were captured against the current worktree, not necessarily the exact commit CI will build).

### Captured current output (for reference — re-verify before asserting)

`WitnessProbe.lean` (in `#eval!` call order: `atomTable`, `check []`, `check [(1,0),(2,1)]`,
`check [(1,0)]`, `check [(1,0),(2,1),(1,2),(2,2)]`, two `succs` sanity checks):
```
[(2, [2, 3]), (1, [3]), (0, [])]
some (true, true)
some (true, true)
some (true, false)     -- the witness: upwardClosed=true, ¬forces phiRef1=true
some (false, false)
([0, 1, 2], [1, 2], [1])
([1, 2], [2, 1])
```

`MinProbe.lean` (world table, then `try1 []`, `try1 [(1,0)]`, `try1 [(1,0),(2,1)]`,
`try1 [(2,0)]`, `try1 [(1,0),(2,0)]`):
```
some [(2, [2, 3], false), (1, [3], false), (0, [], false)]
some ([], true, true, false)
some ([(1, 0)], true, true, true)              -- the witness under isMinimallyClosed
some ([(1, 0), (2, 1)], true, true, false)
some ([(2, 0)], true, true, false)
some ([(1, 0), (2, 0)], true, true, true)       -- a second witness
```

`WitnessSearch3.lean` (`checkInt` over `phiRef1, phiRef2, phiRef3, exMiddle, dblNeg, peirce,
deMorgan, dummett`, then `checkMin` over `phiRef1, exMiddle, peirce, dummett`):
```
("OPEN", (true, false), true, false)   -- checkInt phiRef1  (maximal frame FAILS — cited fact)
("OPEN", (true, true), true, true)     -- checkInt phiRef2
("OPEN", (true, false), true, false)   -- checkInt phiRef3  (maximal frame FAILS — cited fact)
("OPEN", (true, true), true, true)     -- checkInt exMiddle
("OPEN", (true, true), true, true)     -- checkInt dblNeg
("OPEN", (true, true), true, true)     -- checkInt peirce
("OPEN", (true, true), true, true)     -- checkInt deMorgan
("OPEN", (true, true), true, true)     -- checkInt dummett
("OPEN", (true, false), true, false)   -- checkMin phiRef1
("OPEN", (true, true), true, true)     -- checkMin exMiddle
("OPEN", (true, true), true, true)     -- checkMin peirce
("OPEN", (true, true), true, true)     -- checkMin dummett
```
(Confirm the exact printed parenthesization with a real `#guard_msgs in #eval` run — the flattened
tuple-printing shape above was captured from stdout and should be re-verified rather than
hand-transcribed into the assertion.)

`WitnessSearch2.lean`: **no output captured** (timed out); do not attempt to reproduce its
`searchWitness` full-enumeration output in the promoted file. See recommendation above.

## Registration Mechanics

- `lakefile.toml` already declares a `CslibTests` `lean_lib` target and
  `testDriver = "CslibTests"`; `lake test` == building the `CslibTests` library, so a failing
  `#guard_msgs` assertion in a new file fails `lake test` directly. No separate test-runner
  wiring is needed.
- New files must be added to the **barrel file** `/home/benjamin/Projects/cslib/CslibTests.lean`
  (alphabetically sorted `public import CslibTests.<Name>` lines). CI enforces this is in sync via
  `lake exe mk_all --check` (`.github/workflows/lean_action_ci.yml`); the implementer should run
  `lake exe mk_all --module` locally after adding files rather than hand-editing the barrel, to
  guarantee correct alphabetical placement.
- `.github/workflows/lean_action_ci.yml` runs `lean-action`'s build+test step (`test-args: ""`,
  i.e. plain `lake test`) — this is the CI job that will pick up the new files once they're in the
  barrel and pass.
- CSLib's own documented CI order (`.claude/rules/cslib.md`) is: `lake build` → `checkInitImports`
  → `lake lint` → `lake exe lint-style` → `lake test` → `lake exe mk_all --module` →
  `lake shake`. Running this full sequence locally before considering the task done is advisable,
  matching how other `CslibTests/` promotions have been verified.

## Naming

The `Scheme.lean` docstring around `openBranch_countermodel` (lines 7868, 7882) and
`Minimal/Completeness.lean` (lines 143-144) currently cite the scratch probes **by their existing
filenames** (`WitnessProbe.lean`, `WitnessSearch2.lean`, `WitnessSearch3.lean`) or inline without
a filename (the `MinProbe.lean` witness, cited only by its computed fact, not a filename).
Precedent exists for renaming on promotion (`scratch_refute_ancestor_redirect.lean` →
`AncestorRedirectRefutation.lean`), but **keeping the same base names**
(`CslibTests/WitnessProbe.lean`, `CslibTests/WitnessSearch2.lean` or its replacement,
`CslibTests/WitnessSearch3.lean`, `CslibTests/MinProbe.lean`) minimizes churn: the only edit then
needed at the `Scheme.lean`/`Minimal/Completeness.lean` citation sites is prepending
`CslibTests/` and dropping the "not promoted"/"not CI-protected" qualifier — a much smaller diff
than a rename would require, and one an editor performing a later, appropriately-scoped pass can
make mechanically. If the implementer prefers more descriptive names (e.g.
`IntOpenBranchWitness.lean`, `MinOpenBranchWitness.lean`) that is also acceptable per the
promotion precedent, provided each new file's docstring includes an explicit "promoted from
`specs/591_.../scratch/<OriginalName>.lean`" pointer (the established idiom, see above) so the
provenance trail is not lost.

## Out-of-Scope Finding: Stale Citations in `Cslib/`

**This is flagged, not actioned** — the delegating task's `file_scope` is `["CslibTests/"]`, and
`Cslib/` source files are out of that scope.

Once these four probes are promoted, two docstring passages become **factually stale**:

1. `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:7868`: *"computed against the
   real algorithm, not CI-protected: see the scratch probes `WitnessProbe.lean`/`WitnessSearch2.lean`,
   not promoted into `CslibTests/`"* — after this task, they ARE promoted and CI-protected.
2. Same file, line 7882: *"(`WitnessSearch3.lean`, computed, not CI-protected)"* — same issue.

Neither statement becomes *wrong in substance* (the underlying mathematical claims stay true), but
both become misleading provenance claims about CI protection status. Recommend a small, targeted
follow-up task (or a scope extension of this one, if the user prefers) to update these two
citation sites to point at `CslibTests/<promoted-name>.lean` and drop the "not CI-protected"
qualifier, mirroring how `Scheme.lean:7843-7844` and `:7872` already correctly cite
`CslibTests/HvalidShapeRefutation.lean` and `CslibTests/BetaSplitRefutation.lean` by their
promoted, in-tree paths. This is a docstring-only edit (no proof/statement changes), low risk, and
small — but it is a real citation-accuracy gap this task's `file_scope` restriction will otherwise
leave behind.

## Zero-Debt / Scope Compliance

- All four probes use only computational (`#eval`-checked) evidence — no `sorry`, no new axioms,
  nothing to defer. Promotion is purely mechanical (format conversion + registration), so the
  zero-sorry / zero-new-axiom constraint is trivially satisfiable here.
- Per the task's explicit instruction, do **not** weaken any assertion to make it pass — if a
  captured value above turns out to differ from what a fresh `#guard_msgs` run reports at
  implementation time, that is a finding to report (possible drift in `intuitionisticTableau`/
  `minimalTableau` since the scratch probes were last run), not something to paper over by
  adjusting the assertion to match without investigation.

## Summary for the Plan

1. Fix `MinProbe.lean`'s doc-comment-before-`#eval!` parse error by converting to the
   `#guard_msgs` idiom (also gives CI protection "for free" for those two calls).
2. Promote `WitnessProbe.lean` and `MinProbe.lean` largely as-is (fast, ~6.5s / ~2.5s), converting
   all bare `#eval!` calls to `/-- info: … -/ #guard_msgs in #eval …`, adding copyright header +
   module docstring with scratch-provenance pointer per the established idiom.
3. Promote `WitnessSearch3.lean` as-is (fast, ~2.7s), same conversion.
4. Do **not** port `WitnessSearch2.lean`'s exhaustive `subsets`/`searchWitness` enumeration into
   CI — it does not complete in 9+ minutes for even the first formula. Instead assert the specific
   known witnesses (reusing `WitnessProbe.lean`'s fast direct-check style), and document the "40
   witnesses, exhaustively verified interactively, not re-executed in CI" claim as prose, with the
   scratch file's path as the place to re-run the full search by hand if ever needed.
5. Add all resulting files to `CslibTests.lean` via `lake exe mk_all --module` (do not hand-edit).
6. Run the CSLib CI-verification order (`lake build`, `checkInitImports`, `lake lint`,
   `lake exe lint-style`, `lake test`, `lake exe mk_all --module` again, `lake shake`) to confirm
   green before declaring done.
7. Flag (do not fix, per `file_scope`) the two stale "not CI-protected" citations in
   `Scheme.lean` as a follow-up.
