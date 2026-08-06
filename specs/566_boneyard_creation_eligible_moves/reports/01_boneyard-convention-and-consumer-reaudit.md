# Research Report: `Boneyard/` Creation and Re-Audited Eligible Moves

**Task**: 566 — Task H of the modal-tableau refactor programme (P3)
**Date**: 2026-08-06
**Type**: cslib research
**Anchoring rule observed**: every finding below is anchored on **declaration names**; line
numbers appear only as navigational conveniences measured against the current tree and are
explicitly marked as such.

---

## 0. Executive Summary

Four headline results, all measured first-hand against the current tree (not inherited):

1. **`Boneyard/` at the repository root requires no changes to any *build, lint, or census*
   mechanism — but two genuinely repo-wide scanners do exist and are exceptions.** All eleven
   CI-relevant mechanisms are scoped by Lake `lean_lib` declaration, by *import reachability* from
   `Cslib.lean`, or by a hardcoded `Cslib` scan root, and are blind to a top-level `Boneyard/` by
   construction (§4.2). **The two exceptions are `.github/workflows/todo-issue.yml` (repo-wide,
   diff-driven, would file GitHub issues for TODO markers in archived code) and
   `scripts/bench/size/run` (repo-wide glob, would count archived lines as live).** Neither blocks
   this task — the three declarations being moved carry no TODO markers, verified — but both are
   standing hazards for future Boneyard growth and must be recorded. See §4.2–§4.4.
   **A further corollary is a risk, not a reassurance**: the exclusion is otherwise *implicit and
   unasserted*, so nothing would catch a regression. §4.4 recommends a defensive self-test
   modelled on upstream's `B0` check.

2. **The consumer re-audit changes the eligible set from four items to three.** The two
   `outDegEq` preservation lemmas are **MOOT** — already removed entirely, confirmed by name.
   The three surviving eligible declarations are `blockedRedirect_boxctx_mem_of_boxOrigin`,
   `blockedRedirect_diaNeg_mem_of_diaOrigin`, and the `keysRootEmpty` / `keysRootEmpty_entry`
   pair. See §2.

3. **Both mandatory carve-outs hold, and one of them is now pinpointed exactly.**
   `branchSatisfiableIn_s4FC_ancestor_redirect` sits at `FrameSoundness.lean:1227` with its
   `sorry` at `:1251` — matching the task's corrected "~1227 / ~1251" figures precisely, not the
   superseded 1220-1244. `keysOriginS4` is emphatically not zero-consumer. See §3.

4. **The move is not a cut-and-paste.** All three eligible declarations are referenced by
   *surviving prose* in `LoopChecking.lean` that would be left dangling, and the file carries a
   now-falsified assertion that no `Boneyard/` exists. See §5 — this is the main
   under-appreciated cost of the task.

---

## 1. Verification Baseline (re-verified against the current tree)

The task instructed re-verification because tasks 564 and 586 have landed since the baseline was
recorded. All figures below were measured in this session.

| Gate | Command | Result | Baseline claim | Verdict |
|---|---|---|---|---|
| Build | `lake build Cslib` | **Build completed successfully (3313 jobs)** | 3313 jobs green | **MATCHES** |
| Modal/Tableau sorry census | the canonical two-grep recipe recorded at `LoopChecking.lean:110-111` | **exactly 1**: `FrameSoundness.lean:1251` | exactly 1 | **MATCHES** |
| Axiom census | `bash scripts/check-axiom-census.sh` | 43 sorryAx-tainted (baseline 43), **exit 0** | zero axioms in Modal/Tableau | **MATCHES** (see note) |
| Shake | `bash scripts/check-shake-residue.sh` | 9 flagged (baseline 9), **exit 0** | shake exit 1 / 9 findings, none in Modal/Tableau | **MATCHES** |
| checkInitImports | `lake exe checkInitImports` | **exit 0** | exit 0 | **MATCHES** |
| Lint suppressions | `bash scripts/check-lint-suppressions.sh` | 19 (ceiling 19), **exit 0** | — | green |
| Sorry suppressions | `bash scripts/check-sorry-suppressions.sh` | markers 18 (ceiling 18); sorries 28 (ceiling 28), **exit 0** | — | green |

**Note on the axiom census.** `scripts/axiom-census-baseline.txt` holds 58 entries repo-wide.
Exactly **one** is in Modal/Tableau:

```
Cslib.Logic.Modal.Tableau.branchSatisfiableIn_s4FC_ancestor_redirect	Cslib/Logics/Modal/Tableau/FrameSoundness.lean	direct
```

This is the carve-out-1 declaration and nothing else. "Zero axioms" and "the single tainted
declaration is the retained-sorry carve-out" are the same fact stated two ways; both hold.

**Baseline impact of the planned move**: none of the three eligible declarations appears in
`axiom-census-baseline.txt`, `shake-residue-baseline.txt`, `sorry-suppression-baseline.txt`,
`lint-suppression-baseline.txt`, or `nolints.json` (grepped by name; zero hits). Removing them
from live code therefore perturbs **no** baseline file. The sorry and axiom census totals are
unchanged because all three are sorry-free and untainted.

---

## 2. Consumer Re-Audit (Research Question 2)

**Method.** Word-boundary grep over `Cslib/`, `CslibTests/`, `scripts/`, and `Cslib.lean`, then
manual classification of every hit as *declaration site* / *code consumer* / *comment-only
mention*. This is the same method the accepted decision record endorsed, re-run now.

### 2.1 Results by declaration name

| Declaration | Total refs | Declaration site | Code consumers | Comment-only | Verdict |
|---|---:|---|---:|---:|---|
| `blockedRedirect_diaNeg_mem_of_diaOrigin` | 1 | `LoopChecking.lean:1825` | **0** | 0 | **ELIGIBLE** |
| `blockedRedirect_boxctx_mem_of_boxOrigin` | 3 | `LoopChecking.lean:1785` | **0** | 2 (`:1822`, `:1865`) | **ELIGIBLE** |
| `keysRootEmpty` | 10 | `LoopChecking.lean:2566` | **1**, and it is `keysRootEmpty_entry` itself | 8 | **ELIGIBLE as a pair** |
| `keysRootEmpty_entry` | 2 | `LoopChecking.lean:2572` | **0** | 1 (`:2560`) | **ELIGIBLE as a pair** |
| `modalStepBranchS4_preserves_outDegEq` | **0** | — | — | — | **MOOT — already gone** |
| `modalStepBranchS4KeyedOrdered_preserves_outDegEq` | **0** | — | — | — | **MOOT — already gone** |

The eligible set is **three units, ~157 lines** (the two `blockedRedirect_*_of_*Origin` lemmas
occupy a contiguous ~101-line block; the `keysRootEmpty` section is ~56 lines including its
section comment).

### 2.2 The `outDegEq` candidate is MOOT — confirmed, as the task anticipated

The task flagged this as "likely already gone via task 564; verify". It is gone, and the
verification is unambiguous:

- `grep` for `modalStepBranchS4_preserves_outDegEq` and
  `modalStepBranchS4KeyedOrdered_preserves_outDegEq` across `Cslib/` + `CslibTests/` returns
  **zero hits**. Both S4-specific preservation lemmas are deleted.
- The `S4LoopInv` structure's field list no longer contains an `outDegEq` field. Its surviving
  fields are `bClosure`, `eNodup`, `eClosure`, `accFresh`, `accKnown`, `keysTotal`, `keyLowerBd`,
  `keysDistinct`, `keysInUniverse`.
- Commit `18f1b47d` is titled *"task 564 phase 2: remove S4LoopInv.outDegEq and orphaned
  preservation lemmas"*.

**A trap worth naming explicitly.** A bare `grep outDegEq` over `Cslib/` still returns 8 hits and
looks alive. Those hits are a **different** `outDegEq`: the field of `ModalPotentialInv` at
`FmpMeasure.lean:2259`, which is heavily consumed on the K/generic line
(`CompletenessLoop.lean` destructures it as `hpot.outDegEq`), together with the generic
preservation lemmas `modalStepBranch_preserves_outDegEq_gen`, `modalStepBranch_preserves_outDegEq`
and `modalStepBranchGen_preserves_outDegEq`. **None of these is a Boneyard candidate and none was
ever one** — the decision record already said so. An implementer who greps the bare token rather
than the two full lemma names will conclude the candidate is live and either move consumed code
or waste a cycle. Anchor on the full names.

### 2.3 Nature of the three eligible declarations

All three are **sorry-free, proven, and true**; their eligibility rests purely on having zero
consumers, not on being broken. Concretely:

- `blockedRedirect_boxctx_mem_of_boxOrigin` derives, from an already-recorded edge `u → wBlock`
  plus `T(□ψ)@u ∈ b` and mint-readiness, that `T(□ψ)@wBlock ∈ b`. Its own docstring calls it "the
  load-bearing half either way".
- `blockedRedirect_diaNeg_mem_of_diaOrigin` is its diamond-context dual.
- `keysRootEmpty` states that every key recorded for world `0` is empty; `keysRootEmpty_entry`
  establishes it at the driver's seed state `keys = [(0, ∅)]`.

The in-file audit comment at the `keysRootEmpty` section already reaches the same conclusion this
re-audit reaches ("`keysRootEmpty` **is** orphaned -- audited, no longer hedged"), and records
that it was retained deliberately as "small, sorry-free, and a true statement about the driver's
seed state that a route (1) successor may want." **Moving, never deleting, is exactly the right
disposition for code with that character** — the provenance is the whole point.

---

## 3. Carve-Out Verification (Research Question 3)

### 3.1 Carve-out 1 — `branchSatisfiableIn_s4FC_ancestor_redirect` is IMMOVABLE. **HOLDS.**

Located by name, as instructed. Current-tree positions:

- Declaration: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1227`
- Its `sorry`: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1251`

**This confirms the task's corrected figures (~1227 / ~1251) and refutes the superseded
1220-1244 range** recorded in the earlier decision record. Post-extraction drift is real; the
task's warning was correct.

It is genuinely zero-consumer (the only other references are its own in-file audit comment at
`:1206`, a cross-reference at `:5294`, and a count citation in `LoopChecking.lean:115`). It is
nevertheless **IMMOVABLE**, for exactly the reason the task states: it carries the one retained
`sorry` in Modal/Tableau, which is an explicit user decision. The zero-consumer rule that
*licenses* moving is not the rule that *protects* code, and the proven-and-consumed rule does not
reach this declaration. Two independent mechanical confirmations that it must stay put:

- It is the sole Modal/Tableau row of `scripts/axiom-census-baseline.txt`. Moving the file out of
  the build would make that baseline row unresolvable and break the census ratchet.
- Its own in-file docstring records that the `sorry` "is retained by explicit user decision", and
  the surrounding comment warns against further attempts to close it.

### 3.2 Carve-out 2 — `keysOriginS4` is NOT eligible. **HOLDS, with a large margin.**

Measured now: **43 references across `Cslib/`** by word-boundary grep. It is declared at
`LoopChecking.lean:1589`, together with `keysOriginS4_entry` (`:1610`), `keysOriginS4_mono_branch`
(`:1626`) and `keysOriginS4_mono_acc` (`:1651`), and is threaded as a hypothesis throughout the
keyed S4 track.

**The "22 code consumers" figure remains unreproducible** — as the decision record already found,
which measured 61 textual references / 55 non-comment at an earlier tree state. My count of 43 is
a third distinct figure, differing because it is scoped to `Cslib/` with a different comment
filter. **Downstream tasks should cite the qualitative fact, not any of the three numbers**: on
every measurement method tried, `keysOriginS4` is pervasively consumed and nowhere near
zero-consumer. The carve-out's conclusion is insensitive to which figure is used.

**The FALSE comment claim is confirmed as false and is already corrected in the tree.** The task
warns that a comment "at `LoopChecking.lean:2001-2002`" claims `keysOriginS4` was removed. At the
current tree that claim no longer sits at those lines; the corresponding passage is now the
`### keysRootEmpty` section's "Consumer audit (measured; supersedes an earlier hedge)" block,
which explicitly retracts it:

> `keysOriginS4` was **not** removed and is **not** orphaned. […] Any future claim that
> `keysOriginS4` was deleted is false and should not be reintroduced.

So the defect the carve-out was written to guard against has already been repaired in place.
**The carve-out itself still stands** — `keysOriginS4` must not be moved — but the implementer
should not go hunting for a stale comment at 2001-2002 to fix, because there is none.

### 3.3 Route-independent preserved assets — all confirmed NOT eligible

These are to be **placed by the abstraction decision, not quarantined**. Re-measured:

| Declaration | Site (current tree) | Measured | Disposition |
|---|---|---:|---|
| `modalS4Saturated` | `LoopChecking.lean:6722` | **36 non-comment code refs** | NOT ELIGIBLE — proven and consumed |
| `hintikkaS4_*` bridge set | `LoopChecking.lean:6756`–`:7202` | 10 declaration sites present | NOT ELIGIBLE (see note) |
| `hasEdge_accWithReds_iff` | `LoopChecking.lean:9087` | 1 code consumer (`:9119`) | NOT ELIGIBLE — consumed |
| `reflTransGen_accWithReds_first_red` | `LoopChecking.lean:9107` | 0 consumers | **HOLD — preserved asset, place it** |
| `blockedRedirect_unwrapped_boxPos_mem` | `LoopChecking.lean:9169` | preserved asset | **HOLD** |
| `blockedRedirect_unwrapped_diaNeg_mem` | `LoopChecking.lean:9201` | preserved asset | **HOLD** |
| `Reds` / `accWithReds` packaging | same section | packaging for the above | **HOLD** |

**Note on the "8, measured, not 10" figure.** The task states the strictly-weakened `hintikkaS4`
bridge set is 8. My grep finds **10 declaration sites** whose names begin `hintikkaS4_`. These are
reconcilable rather than contradictory: `LoopChecking.lean:181-183` records the measured figure as
"**`hintikkaS4_*` bridge set: 8 declarations**", noting that counting *distinct identifiers*
instead returns 11 "because three further names occur only in call positions or prose". The set of
8 is a semantic set (the strictly-weakened bridges), not the syntactic set of all
`hintikkaS4_`-prefixed declarations. **The discrepancy is immaterial to this task** — the whole
group is not Boneyard-eligible under either count — but an implementer must not "correct" the
figure to 10 on the strength of a prefix grep.

---

## 4. The `Boneyard/` Convention: Structure and Exclusion Mechanics (Research Questions 1 and 4)

### 4.1 The upstream convention

The convention is borrowed from `~/Projects/BimodalLogic/FormalSystem/Boneyard/`, which carries a
substantial `README.md`. (Two other sibling repos have `Boneyard/` directories —
`Logos/Theory/Boneyard/` and `TenseModality/Boneyard/` — but neither carries a README or a
documented convention; `BimodalLogic` is the one to model on.)

The task's "roughly 27k lines and 29 sorries" is a **stale snapshot**. The upstream tree now
measures **93 `.lean` files / 59,019 lines** in the primary Boneyard, and its own README documents
a *second* Boneyard at `Metalogic/WeakCanonical/Kamp/Boneyard/` holding **62 files / 27,394
lines**. The task's 27k figure most likely refers to that second, Kamp-local Boneyard rather than
the primary one. **Do not quote 27k/29 as the upstream size**; if a figure is needed, measure it.

The load-bearing elements of the upstream convention, worth porting:

1. **Archival criterion**: a file belongs there when it is *unreachable from every Lake target
   root* and is not intended to become reachable. Unreachability alone is not sufficient — merely
   not-yet-wired code belongs elsewhere. Archiving is for code deliberately out of the development
   path.
2. **Build policy — "Never Compiled"**: stated explicitly as *liveness equals reachability*.
   There is no lakefile target covering the Boneyard; "import lines inside archived files are
   historical text, not build edges", and "stale imports in never-built code are cosmetic and
   need not be repaired."
3. **`#exit` guard**: files with deep API drift place `#exit` after their imports, preserving the
   code as reference while guaranteeing it cannot compile-error if ever accidentally elaborated.
4. **`ARCHIVED (Boneyard)` header docstring** naming the moved declarations and ending
   `Do not import from live code.`
5. **Per-subdirectory `README.md`** plus a **Directory Inventory table** in the root README with
   files / lines / archived-from / why-archived columns.
6. **Sorry counts are not bugs**: "Boneyard sorries represent archived dead ends, not open proof
   obligations."
7. **"Do not grep this directory when auditing live identifier usage"** — upstream records ~8,718
   stale identifier references that would otherwise produce thousands of false positives.
8. **Tombstones**: subdirectories reduced to a README only, marked
   `TOMBSTONE — code deleted; README retained as historical record.`

Upstream enforces its exclusion mechanically via `scripts/check-module-invariants.sh`, using the
pattern `find … -not -path '*/Boneyard/*'` (and `grep -v '/Boneyard/'`), with a **`B0` self-test
that asserts the exclusion pattern really matches the expected number of Boneyard directories**.
Its README explains why: "Several past counts of this repository were wrong for exactly that
reason." That self-test is the single most valuable thing to port. See §4.4.

### 4.2 Exclusion mechanics in THIS repo — the complete mechanism table

Every mechanism below was read at source in this session. The scoping expression is quoted.

| # | Mechanism | Where | Scoping expression | Picks up root-level `Boneyard/`? |
|---|---|---|---|---|
| 1 | `lake build` | `lakefile.toml` | `defaultTargets = ["Cslib"]`; `[[lean_lib]] name = "Cslib"` — Lake defaults the lib's roots to the single module `Cslib`, so only `Cslib.lean` + its transitive imports are built | **NO** |
| 2 | `lake exe mk_all --check` | `.github/workflows/lean_action_ci.yml` | `mk_all.lean`'s `getLeanLibs` returns `package.leanLibs.map (·.name)` = `["Cslib", "CslibTests"]`, then globs each **library directory** | **NO** |
| 3 | `lint-style` | `lean_action_ci.yml` (`leanprover-community/lint-style-action`) | `lint-style.lean`: with no module args it uses `workspace.root.defaultTargets` → lib roots, then `findImportsFromSource`, filtered to the same package. **Import-reachability scoped.** | **NO** |
| 4 | `lake shake` | `scripts/check-shake-residue.sh` | `SHAKE_ARGS=(--add-public --keep-implied --keep-prefix Cslib)`; operates on the **build graph** | **NO** |
| 5 | Sorry ratchet | `scripts/check-sorry-suppressions.sh` | `SCAN_ROOT="Cslib"`; `find "$SCAN_ROOT" -name '*.lean' -type f` | **NO** |
| 6 | Lint-suppression ratchet | `scripts/check-lint-suppressions.sh` | `SCAN_ROOT="Cslib"`; `find "$SCAN_ROOT" -name '*.lean' -type f` | **NO** |
| 7 | Axiom census | `scripts/check-axiom-census.sh` + `scripts/AxiomCensus.lean` | `AxiomCensus.lean` does `import Cslib` and enumerates the **elaborated environment** | **NO** |
| 8 | `checkInitImports` | `scripts/CheckInitImports.lean` | `CoreM.withImportModules #[`Cslib]`, then filters `name.getRoot = `Cslib` over the **import graph** | **NO** |
| 9 | Pre-PR debug/header sweeps | `scripts/pre-pr-check.sh` steps 2-3 | hardcoded `Cslib/Foundations/Logic/ Cslib/Logics/Modal/ Cslib/Logics/Temporal/ Cslib/Logics/Bimodal/` | **NO** |
| 10 | Weekly lints | `.github/workflows/weekly-lints.yml` | `lake build` (and gated on `github.repository == 'leanprover/cslib'`, so it does not even run on this fork) | **NO** |
| 11 | Doc generation | `scripts/gendocs.sh` | `lake build Cslib:docs` | **NO** |
| 12 | Batteries lint driver | `lakefile.toml` `lintDriver = "batteries/runLinter"` | `runLinter.lean`: `defaultTargets` → `lib.getModuleArray` | **NO** |

Two clarifications worth recording, because both look like scoping bugs and are not:

- **`--keep-prefix` in mechanism 4 is a *valueless* flag.** In `SHAKE_ARGS=(--add-public
  --keep-implied --keep-prefix Cslib)`, the trailing `Cslib` is not an argument to
  `--keep-prefix`; it is a positional `<MODULE>` argument, and shake checks everything
  transitively reachable from it. The scope is correct either way (omitting it falls back to the
  package default targets, which is the same thing here), but a future reader should not "fix"
  it.
- **`srcDir` is unset for `[[lean_lib]] Cslib`, so it defaults to `"."` — the repo root.** This
  means `Boneyard/Foo.lean` *is resolvable* on the source search path as module `Boneyard.Foo`.
  It is still never **built** (it matches no lib's `roots`/`globs`, per Lake's `isLocalModule`),
  but the name resolving is why the single-vector warning in §4.3 matters: one `import
  Boneyard.Foo` from anything reachable from `Cslib.lean` would drag the file into the build,
  shake, lint-style, checkInitImports, and the axiom census simultaneously.

### 4.2b The two genuinely repo-wide `.lean` scanners

These are the only mechanisms in the repository that walk `.lean` files without a `Cslib` anchor.
Neither is a blocker for this task; both are standing hazards.

**(a) `.github/workflows/todo-issue.yml` — repo-wide, diff-driven, and it writes to GitHub.**

```yaml
on:
  push:
    branches: [main]
...
      - uses: "alstr/todo-to-issue-action@v5"
        with:
          LANGUAGES: ".github/todo-to-issue-lean.json"
```

`.github/todo-to-issue-lean.json` registers `.lean` with `--` line markers and `/- -/` block
markers. The workflow has **no `paths` or `paths-ignore` filter**, so it scans the whole push
diff. Consequence: a commit that adds Boneyard files containing `TODO:` markers would file a
GitHub issue for each — turning archived dead-end notes into live tracker items, the precise
inversion of what quarantine is for.

**Not triggered by this task**: I grepped both eligible regions for `TODO|FIXME|BUG|HACK|NOTE:|
QUESTION:` and found **zero markers**. This move is safe as-is.

**Mitigation is a genuine tradeoff, not a free fix.** `todo-issue.yml` is upstream-authored (its
history is upstream `chore:`-style commits), so it is a shared/synced workflow file — the same
category `lean_action_ci.yml` warns about in-file: *"every workflow under `.github/workflows/` is
shared with the leanprover/cslib upstream remote, so editing one adds a conflict hunk to every
future sync."* Adding `paths-ignore: ['Boneyard/**']` therefore carries real, recurring cost.
Two options, in order of preference:

1. **Document the constraint in `Boneyard/README.md`**: archived code must not carry live
   `TODO:`/`FIXME:` markers; neutralize them (e.g. to `ARCHIVED-TODO:`) during the move. Zero
   sync cost, and consistent with the fact that a Boneyard TODO is by definition not actionable.
2. **Add `paths-ignore` to `todo-issue.yml`** only if the Boneyard is expected to grow large
   enough that option 1 becomes unenforceable. Accept the sync cost knowingly.

**(b) `scripts/bench/size/run` — repo-wide glob over every top-level directory.**

```python
def find_lean_files() -> Generator[Path, None, None]:
    for p in Path().iterdir():
        if p.name.startswith("."):
            continue
        elif p.is_dir():
            yield from p.glob("**/*.lean")
```

Every non-dotted top-level directory is globbed, so `Boneyard/` would be counted in the size
benchmark. It is **not wired into any CI workflow and is not listed in `scripts/README.md`** — a
manual benchmarking tool — so the blast radius is a distorted local measurement, not a failing
gate. It is nonetheless *exactly* the failure mode upstream's README reports having suffered
("Several past counts of this repository were wrong for exactly that reason"), and it is the
strongest concrete argument for the §4.4 self-test.

A third, lower-stakes item: `.claude/scripts/lean-sorry-census.sh` takes a caller-supplied
`$target` and would count `Boneyard/` if pointed at it. That is correct behaviour for a
parameterised tool; it only matters as a reminder not to point it at the repo root.

### 4.3 Answer to Research Question 4: **no build/lint/census config needs touching**

- **`lakefile.toml`**: no change. Adding a `lean_lib` or glob for Boneyard would be actively
  harmful — it would pull the directory into `mk_all`'s library list (mechanism 2) and into
  `lint-style`'s default targets (mechanism 3), producing exactly the CI failures the
  quarantine exists to prevent.
- **`.gitignore`**: no change, and **must not** be changed. The Boneyard is retained *for
  provenance*; ignoring it would defeat the entire purpose. Use `git mv` so history follows.
- **CI workflows**: no change. Note `lean_action_ci.yml` carries an explicit in-file warning that
  every edit to it "adds a conflict hunk to every future sync" with the `leanprover/cslib`
  upstream remote. Not needing to touch it is a real benefit, not merely a convenience.
- **`lint-style` config / `scripts/nolints-style.txt`**: no change. That file is currently
  **empty (0 lines)**, and mechanism 3 is import-reachability scoped, so no exemption is needed.
- **Baseline files**: no change, per §1.

**Not covered by "no change needed"**: the two repo-wide scanners in §4.2b. Neither requires
action for *this* task (no TODO markers in the moved code; the bench script is not CI-wired), but
both belong in the Boneyard README as standing constraints.

**Three standing invariants** to record in `Boneyard/README.md`, each of which would individually
undo the quarantine:

1. Never add `[[lean_lib]] name = "Boneyard"` to `lakefile.toml`. That single line would make
   `mk_all --check` demand a `Boneyard.lean` aggregator and pull the tree into the linters.
2. Never `import Boneyard.*` from anything reachable from `Cslib.lean`. Because `srcDir` defaults
   to the repo root, the module name *does* resolve — this is the one live vector.
3. Never pass `--scope Boneyard` to `check-sorry-suppressions.sh`. Its `--scope` path is the one
   code path in the ratchet scripts that will walk an arbitrary directory.

**The decisive architectural fact**: the *root-level* placement the task mandates is not
cosmetic — it is what makes all of this free. Placing the Boneyard **under `Cslib/`** would break
mechanism 2 immediately (`mk_all --check` globs the `Cslib/` directory tree and would demand the
new files be imported from `Cslib.lean`, which would in turn pull them into the build, the
censuses, and lint-style). Root placement is load-bearing; record it as such.

### 4.4 Recommended defensive assertion (the one thing worth adding)

Because the exclusion is entirely implicit, **nothing in this repo would notice if it broke**. A
future contributor adding a `lean_lib` glob, or relocating the Boneyard under `Cslib/`, would
silently sweep archived lines into the live counts — precisely the failure upstream's README
reports having suffered ("Several past counts of this repository were wrong for exactly that
reason").

Recommended, in the spirit of upstream's `B0` self-test and cheap to implement:

- Add a check that asserts (a) `Boneyard/` exists at the repository root, (b) no file under
  `Boneyard/` is reachable from `Cslib.lean` — e.g. `grep -c 'Boneyard' Cslib.lean` is `0`, (c) no
  `Boneyard` path appears in `lakefile.toml`, and (d) no `.lean` file under `Boneyard/` carries a
  live `TODO:`/`FIXME:` marker (guarding the `todo-issue.yml` exposure of §4.2b(a) at the cheap
  end, without editing a synced workflow file).
- Mirror upstream's `B0` idea specifically: assert that the exclusion pattern matches the
  *expected number* of Boneyard directories, so that adding a second Boneyard later cannot
  silently escape the filter — that is the exact failure upstream documents having suffered.
- Wire it into `scripts/pre-pr-check.sh` (a local, non-synced file) rather than into
  `lean_action_ci.yml`, matching the established divergence-cost convention this repo already
  follows for `check-lint-suppressions.sh` and `check-shake-residue.sh`.
- If a new script is added under `scripts/`, note that `linter.allScriptsDocumented` requires an
  entry in `scripts/README.md` (currently disabled via `weak.linter.allScriptsDocumented = false`
  in `lakefile.toml`, but documenting it anyway is the low-cost choice).

This is a recommendation, not a blocker.

### 4.5 Proposed layout for this repo

Given the small scope (3 declarations, ~157 lines, all from one file, all from the same
refactor programme), a single subdirectory is proportionate:

```
Boneyard/
├── README.md                          # convention + Directory Inventory table
└── ModalTableauS4Keyed/
    ├── README.md                      # why these three were archived
    ├── RedirectOriginTransfer.lean    # the two blockedRedirect_*_of_*Origin lemmas
    └── KeysRootEmpty.lean             # keysRootEmpty + keysRootEmpty_entry
```

Per the upstream file convention, each `.lean` file carries: the source file's import block
verbatim (here, `import Cslib.Logics.Modal.Tableau.LoopChecking` or the original's own imports),
an `ARCHIVED (Boneyard)` docstring naming the moved declarations and ending
`Do not import from live code.`, then `#exit`, then the excised code verbatim.

The `#exit` guard matters more here than it might appear: these three declarations are stated over
live `LoopChecking` definitions (`modalFourBoxProp`, `modalNonMintCandidates`,
`modalApplyOneS4Keyed`, `successorBirthContent`, and the `S4KeyedHintikkaInv` fields
`eBoxOnlyNeg` / `eDiamondOnlyPos`). They would in principle still elaborate today, but the whole
point of quarantine is that nothing re-checks them as those definitions evolve. `#exit` makes the
inertness explicit rather than incidental.

---

## 5. Implementation Hazards — the move is not a cut-and-paste

This is the finding most likely to be missed. Each item is a concrete edit the move forces.

### 5.1 A now-falsified assertion in `LoopChecking.lean`

`LoopChecking.lean:184-185` (in the measured-figures block) states:

> There is no `Boneyard/` directory (`find . -type d -name 'Boneyard' -not -path './.lake/*'`
> returns nothing).

Creating `Boneyard/` **falsifies this in the same commit**. It must be updated. Given that this
very block is the file's authoritative census of measured figures — and the surrounding programme
has already been burned twice by stale in-file claims (`keysOriginS4`'s false removal claim, and
the superseded `1220-1244` line range) — leaving it stale would be a repeat of the exact defect
class this task exists downstream of.

### 5.2 Dangling prose references to moved declarations

Moving the declarations leaves live docstrings citing names that no longer exist in the tree:

| Surviving reference | Cites | Nature |
|---|---|---|
| `LoopChecking.lean:1822` | `blockedRedirect_boxctx_mem_of_boxOrigin` | docstring of `blockedRedirect_diaNeg_mem_of_diaOrigin` — **moves with it**, so self-resolving |
| `LoopChecking.lean:1865` | `blockedRedirect_boxctx_mem_of_boxOrigin` | "### The Witness Disjunct (Gate)" section: *"case (b) (closed above, via `blockedRedirect_boxctx_mem_of_boxOrigin`)"* — **stays behind, becomes dangling** |
| `LoopChecking.lean:910` | `keysRootEmpty` | `BoxPlusClosed` docstring: *"the same treatment `keysOriginS4`/`keysRootEmpty` already receive"* — **stays behind, becomes dangling** |
| `LoopChecking.lean:2586` | `keysRootEmpty` | "### Redirect-Inertness Assembly -- REMOVED" section, listing the hypotheses that held in the refutation — **stays behind, becomes dangling** |

The `:1865` and `:2586` cases are the load-bearing ones: both sit inside narrative passages that
*explain a refutation*, and both reference the moved lemmas as part of the argument. Simply
deleting the names would damage the explanation. The right repair is to redirect them at the
Boneyard location (e.g. "…now archived at `Boneyard/ModalTableauS4Keyed/`"), preserving the
narrative while making the pointer true.

### 5.3 The `keysRootEmpty` section comment is itself an audit record

The ~40-line section comment preceding `keysRootEmpty` (`LoopChecking.lean:2523`–`:2563`) is not
ordinary documentation — it contains the measured consumer audit, the retraction of the false
`keysOriginS4` removal claim, and the reproduction commands. **The `keysOriginS4` retraction must
stay in `LoopChecking.lean`** (it is about a live, heavily-consumed declaration), while the
`keysRootEmpty`-specific paragraphs should travel to the Boneyard README. Moving the block
wholesale would carry the `keysOriginS4` correction out of the live tree — re-opening exactly the
defect carve-out 2 was written to close.

### 5.4 Verification after the move

Because all three declarations are zero-consumer and sorry-free, the expected post-move state is:
`lake build Cslib` green at **3313 jobs** (unchanged — the moved declarations were leaves, so no
job count change is expected; a change would be a signal worth investigating), Modal/Tableau sorry
census still exactly 1, all five ratchet scripts still exit 0 against unmodified baselines. Any
deviation means a consumer was missed.

---

## 6. Answers to the Four Research Questions

**Q1 — Upstream structure and exclusion mechanics.** §4.1 documents the upstream convention
(archival criterion, never-compiled build policy, `#exit`, `ARCHIVED` header, per-subdirectory
READMEs, inventory table, tombstones, the "do not grep for live usage" warning). Exclusion
upstream is *structural* (liveness = reachability from a Lake root), enforced by a `find … -not
-path '*/Boneyard/*'` filter with a self-test. The task's "27k lines / 29 sorries" is stale — see
§4.1.

**Q2 — Consumer re-audit.** §2. Three eligible units confirmed by name with consumer counts; the
`outDegEq` candidate is MOOT (both S4 preservation lemmas return zero grep hits; the
`S4LoopInv.outDegEq` field is gone), with an explicit warning about the surviving, unrelated,
heavily-consumed `ModalPotentialInv.outDegEq`.

**Q3 — Carve-outs.** §3. Both hold. Carve-out 1 pinpointed at `FrameSoundness.lean:1227` / `:1251`,
confirming the task's corrected figures. Carve-out 2 confirmed with a large margin; its underlying
false comment is already repaired in the tree, so there is no stale comment to hunt for.

**Q4 — Config/scripts to touch.** §4.3: **no build, lint, or census config needs changing** —
all twelve such mechanisms are lean_lib-scoped, import-reachability-scoped, or hardcoded to
`Cslib`, and root-level placement is what makes this free. **Two repo-wide `.lean` scanners are
exceptions** (§4.2b): `todo-issue.yml` (would file GitHub issues for TODO markers in archived
code; not triggered by this move, since the eligible regions carry none) and
`scripts/bench/size/run` (would count archived lines as live; not CI-wired). Three standing
invariants are listed in §4.3. §4.4 recommends a defensive self-test precisely *because* the
exclusion is otherwise implicit and currently unasserted.

---

## 7. Recommended Phase Decomposition (input to planning)

Zero-debt compatible; no phase requires or permits a `sorry`.

1. **Create the quarantine skeleton.** `Boneyard/README.md` (convention, inventory table, the
   three standing invariants of §4.3, and the no-live-TODO-markers rule of §4.2b) and
   `Boneyard/ModalTableauS4Keyed/README.md`. No Lean code moves yet. Verification: full ratchet
   suite still green, proving the no-config-change claim empirically before anything is at stake.
2. **Move the two `blockedRedirect_*_of_*Origin` lemmas** via `git mv`-preserving extraction into
   `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean`; repair the dangling reference at
   the "Witness Disjunct (Gate)" section. Verification: `lake build` green at 3313 jobs.
3. **Move the `keysRootEmpty` pair**, splitting the section comment per §5.3 so the `keysOriginS4`
   retraction stays live. Repair the `BoxPlusClosed` and "Redirect-Inertness Assembly" references.
   Verification: as above.
4. **Correct the falsified no-Boneyard assertion** in `LoopChecking.lean`'s measured-figures block
   and document `Boneyard/` in `ORGANISATION.md`'s "Top-Level Structure" section (which currently
   lists only `Cslib/` subdirectories, with `CslibTests/` mentioned separately under "Testing").
5. **Add the defensive self-test** (§4.4) to `scripts/pre-pr-check.sh`. Optional but recommended.
6. **Full CI gate**: `lake build Cslib` (expect 3313), all five ratchet scripts, `checkInitImports`,
   Modal/Tableau sorry census = 1.

---

## 8. Sources

All findings measured first-hand in this session. Primary sources:

- `/home/benjamin/Projects/cslib/lakefile.toml`
- `/home/benjamin/Projects/cslib/Cslib.lean` (690 `public import` lines; exactly 690 `.lean` files
  under `Cslib/` — the aggregator is complete)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
- `/home/benjamin/Projects/cslib/scripts/{check-sorry-suppressions,check-lint-suppressions,check-axiom-census,check-shake-residue,pre-pr-check,gendocs}.sh`
- `/home/benjamin/Projects/cslib/scripts/{CheckInitImports.lean,AxiomCensus.lean,axiom-census-baseline.txt,nolints-style.txt}`
- `/home/benjamin/Projects/cslib/.github/workflows/{lean_action_ci,lint-hygiene,weekly-lints,docs,shellcheck,todo-issue}.yml`
- `/home/benjamin/Projects/cslib/.github/todo-to-issue-lean.json`
- `/home/benjamin/Projects/cslib/scripts/bench/size/run`
- `/home/benjamin/Projects/cslib/.lake/packages/batteries/scripts/runLinter.lean`
- Lake defaults: `LeanLibConfig.lean` (`srcDir := "."`, `roots := #[name]`, `globs`,
  `isLocalModule`) in the v4.33.0-rc1 toolchain
- `/home/benjamin/Projects/cslib/.lake/packages/mathlib/scripts/{mk_all.lean,lint-style.lean}`
- `/home/benjamin/Projects/cslib/ORGANISATION.md`
- `/home/benjamin/Projects/BimodalLogic/FormalSystem/Boneyard/README.md` (upstream convention)
- `/home/benjamin/Projects/BimodalLogic/scripts/check-module-invariants.sh` (upstream `B0` self-test)
- `/home/benjamin/Projects/cslib/specs/archive/561_tableau_abstraction_decision_record/decisions/01_abstraction-decision-record.md` (accepted decision D4)
