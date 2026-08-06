# Research Report: Tableau Vetting-Pipeline Acceptance Gate (P4)

**Task**: 567 — final acceptance gate for the modal-tableau refactor programme
**Session**: sess_1786030020_688c25_567
**Date**: 2026-08-06
**Tree state**: `1d824cfd` (`main`), working tree clean under `Cslib/` and `CslibTests/`
**Toolchain**: Lean `v4.33.0-rc1`, Lake `5.0.0-src`

> **Every figure below was measured live in this session against the current tree**, not carried
> over from prior artifacts. Where a stored figure and a live measurement disagree, both are
> shown and the disagreement is recorded as a finding.

---

## 0. Executive Summary

**The gate is substantively PASS on every behavioural acceptance criterion.** All seven CI steps
were run. Six pass. One (`lake lint`) fails, but its 145 failures are entirely pre-existing
`unusedArguments` reports elsewhere in the repository — **zero** of them fall in the ten new
`S4/` modules or in `LoopChecking.lean`, and the ten that do fall in `Modal/Tableau/` trace to
work predating this programme.

**Behaviour preservation is confirmed**: `modalTableauS4Keyed_complete` and all six landed
`Decidable` instances are green and depend on **only** the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no custom axiom. The Tableau
sorry census is **exactly 1**, unchanged. The subsystem declares **zero** axioms.

**Two categories of finding require dispositions before the gate can be declared closed:**

1. **Nine documentation-accuracy defects** (§6, findings D1–D9), of which the most serious are a
   systematic **off-by-one module count ("eleven" S4 modules; there are TEN)** appearing in three
   deliverable files including `ORGANISATION.md`, and a **97-line error in the recorded
   `LoopChecking.lean` size** (documented 1,723; actual 1,626). These are in shipped `Cslib/`
   docstrings and a root-level governance document, so they are user-facing.

2. **One regression-corpus reproduction failure** (§5.4, finding D8): `s4witness.lean` does
   **not** reproduce the trace recorded for it in the S4 loop-guard task's report 02. The
   divergence is fully explained and **attributable to the box-plus birth-key enrichment that
   landed in the `563_tableau_boxplus_birth_keys` task on 2026-08-05 — before any commit of the
   current programme** (verified by `git merge-base --is-ancestor`). It is therefore a stale
   recorded verdict, not a behaviour-preservation failure of tasks 564/565/566/586. It must
   still be dispositioned, because the acceptance criterion as written demands exact
   reproduction.

**Recommended verdict**: `PASS WITH FIX TASKS` (see §7 for the proposed verdict grammar and §8
for the recommended fix-task decomposition). No finding blocks the programme; none is a proof
defect; none requires touching a `.lean` proof.

---

## 1. Research Question 1 — The Seven-Step CI Order and What the Root Documents Demand

### 1.1 The CI order (`.claude/rules/cslib.md`, "CSLib CI Verification Order")

The rule specifies eight entries numbered 0–7 (step 0 is a prerequisite fetch, so it is
conventionally described as a seven-step order). Verbatim, with what each requires and its live
result:

| # | Command | What it enforces | Live result |
|---|---------|------------------|-------------|
| 0 | `lake exe cache get` | Fetch Mathlib `.olean` cache once per branch; prevents a 30–45 min rebuild | **N/A** — tree already fully built; `lake build Cslib` returned immediately with no output |
| 1 | `lake build` | Syntax linters, which run *during* the build | **PASS** — exit 0, 3323 jobs |
| 2 | `lake exe checkInitImports` | Every `Cslib.*` module transitively imports `Cslib.Init` | **PASS** — exit 0 (see §2) |
| 3 | `lake lint` | Environment linters (`#lint`) | **FAIL** — exit 1, 145 errors (see §4.3) |
| 4 | `lake exe lint-style` | Text linters (`--fix` auto-fixes) | **PASS** — exit 0 |
| 5 | `lake test` | Runs `CslibTests/` | **PASS** — exit 0, 3863 jobs |
| 6 | `lake exe mk_all --module` | `Cslib.lean` barrel imports every file | **PASS** — "No update necessary"; `Cslib.lean` byte-identical after the run |
| 7 | `lake shake --add-public --keep-implied --keep-prefix` | Import minimisation | **PASS** (ratchet) — 12 flagged files vs baseline 12, exact-set match |

**Reproduction commands** are exactly the table's column 2, run from the repository root.

**Step 3 caveat that materially affects the verdict**: environment linters are *not* in CSLib's
PR CI — they run only on a weekly cron. `lake lint`'s failure is therefore not a merge blocker,
and it is repo-wide pre-existing debt. It is reported here because the seven-step order names it,
not because this programme caused it.

**Step 7 caveat**: `lake shake` is not run bare in this repository. It is wrapped by
`scripts/check-shake-residue.sh`, an exact-set ratchet against
`scripts/shake-residue-baseline.txt`. The wrapper is what should be run; a bare `lake shake`
reports the whole pre-existing residue and is uninformative.

### 1.2 The wider gate: `scripts/pre-pr-check.sh`

The seven-step order is a subset of what this repository actually gates on. `pre-pr-check.sh`
runs ten steps. All were run live:

| # | Step | Live result |
|---|------|-------------|
| 1 | Sorry ratchet, scoped to four trees | **PASS** — markers 18/18, sorries 28/28 |
| 2 | Debug artifacts (`#check`/`#eval`/`dbg_trace` at line start) | **PASS** — zero in `Modal/Tableau/` |
| 3 | Copyright headers (`head -1` matches `^/-`) | **PASS** — zero missing across the whole `Modal/Tableau/` tree |
| 4 | PR-scope module build | **PASS** (covered by the full green build) |
| 5 | `lake build --wfail --iofail` | **FAIL** — exit 1, 6 modules (see §4.4) |
| 6 | Blanket linter-suppression ratchet | **PASS** — 19/19 |
| 7 | Shake import-debt ratchet | **PASS** — 12/12 exact-set |
| 8 | Sorry-suppression count ratchet (unscoped) | **PASS** — 18/18 markers, 28/28 sorries |
| 9 | Axiom-census ratchet | **PASS** — 43 `sorryAx`-tainted declarations vs baseline 43, exact-set match |
| 10 | Boneyard quarantine self-test | **PASS** — all five invariants (a)–(e) hold |

### 1.3 What the four root documents demand of this subsystem

#### `CONTRIBUTING.md` (328 lines)

| Section | Demand | Subsystem status |
|---------|--------|------------------|
| The role of AI (`:59–62`) | Follows the Mathlib AI policy — PR description must name which tools were used and how | **Deferred to PR authoring**; not checkable at gate time. Flag for whoever writes the PR body. |
| Variable names (`:68–70`) | Domain-appropriate names encouraged | **Conformant** — `State`/`μ` convention not applicable; the subsystem uses `φ₀`, `b`, `acc`, `keys`, `w`/`v`, consistently |
| Proof style (`:72–75`) | Proofs readable; golfing fine if compilation does not noticeably slow | **Conformant** — no new automation introduced by the programme; 3323-job build unchanged |
| Notation (`:77–82`) | Find an existing typeclass first; new multi-type notation must be `scoped` or typeclass-backed | **Vacuously conformant** — the ten `S4/` modules and `LoopChecking.lean` declare **zero** notation (see §4.2) |
| Documentation (`:84–87`) | Document definitions and theorems; cite published resources for formalised concepts | **Conformant** — zero undocumented public declarations across the eleven files (§4.1); `README.md:174` cites Fitting 1983 |
| Design principles / Reuse (`:89–95`) | New definitions instantiate existing abstractions | **Conformant** — move-only refactor; no new abstractions introduced |
| CI (`:97–132`) | The step list in §1.1 | See §1.1 |

#### `NOTATION.md` (87 lines)

Two live demands:

1. **Operational-semantics notation Options A/B/C** (`:9–45`) — not applicable. The subsystem
   defines no reduction/transition arrows; it works with `SignedFormula`, `Accessibility`, and
   `ModalTableauResult` directly.
2. **Logic notation scoping / the `S` collision** (`:47–82`) — the rule is that a file opening
   `Bimodal` or `Temporal` while applying a generic proof-system lemma must supply the
   proof-system tag positionally via `@`, not as `(S := ...)`. **Not applicable**: no file in
   `Modal/Tableau/` opens `Bimodal` or `Temporal`.
3. **Guidance for new notation** (`:84–87`) — prefer distinctive multi-character tokens; declare
   `scoped`. **Vacuously satisfied** (zero notation declarations).

**Verdict: NOTATION.md imposes no live obligation on this subsystem, and none is violated.**

#### `ORGANISATION.md` (356 lines)

Two live demands:

1. **Placement** — `Logics/` holds specific logic formalisations (`:13`); `Modal/Tableau/` is
   documented at `:188–199` as "Tableau decision procedures (K/T/B/S4/S5 drivers, saturation,
   soundness/completeness)" with `Support/` and `S4/` subdirectories. **Placement is conformant**:
   the ten new modules live under `Cslib/Logics/Modal/Tableau/S4/`, exactly where `:193` says
   they should.
2. **Boneyard placement** (`:20–26`) — root-level placement is load-bearing; must be excluded
   from `lake build`, `mk_all`, `lint-style`, `shake`, and every census by import-reachability
   from `Cslib.lean`. **Conformant** — verified by `scripts/check-boneyard-quarantine.sh`
   (all five invariants).

**But** `ORGANISATION.md:198` contains a factual error introduced by this programme (finding D1).

#### `CODE_OF_CONDUCT.md` (76 lines)

Standard Contributor Covenant. **Imposes no mechanically checkable obligation on Lean source.**
It governs conduct in issues, PRs, and Zulip. There is nothing for this gate to verify beyond
noting that it exists and that no artifact in this programme contains conduct-relevant content.
Recording this explicitly rather than silently omitting it: **CODE_OF_CONDUCT.md is not a
source-code standard and generates no gate criterion.**

---

## 2. Research Question 2 — The `checkInitImports` Prerequisite: **CLEARED**

**Status: the prerequisite no longer holds. `lake exe checkInitImports` passes with exit 0.**

### What the prior failure was

`Cslib/Logics/Modal/Tableau/README.md:161–171` ("Build gate at capture") records it precisely:
at the original measurement commit `7eb51f69`, `lake build` failed on a **non-exhaustive match**
in `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` — in-flight work on the
constructive nested-sequent development, unrelated to the tableau subsystem.
`lake exe checkInitImports` then failed **downstream as a consequence, not as an independent
defect**: the checker calls `CoreM.withImportModules #[`Cslib]`
(`scripts/CheckInitImports.lean:29`), so a missing `.olean` anywhere in the `Cslib` closure
aborts it before it can compute the import graph.

### Live re-verification

```
$ lake exe checkInitImports        # exit 0, no output
$ ls .lake/build/lib/lean/Cslib/Logics/Modal/Metalogic/Constructive/Nested/
Context.olean  Rules.olean  Soundness.olean  Syntax.olean  Translation.olean   (+ .ilean/.ir/.trace)
```

`Soundness.olean` is present and current. The five `Nested/` modules are imported by the barrel
at `Cslib.lean:388–392`. The recent full builds cleared it exactly as the task description
hypothesised.

**Note the path correction**: the module is at
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` — under `Metalogic/`, not
directly under `Modal/`. `Cslib/Logics/Modal/Constructive/` does not exist. Any fix task or plan
step that hard-codes the shorter path will fail to find the file.

### Budget consequence

**The prerequisite budget can be released.** No remediation work is needed. The gate should still
run `checkInitImports` (it is CI step 2), but it should be budgeted as a fast pass, not as a
repair.

---

## 3. Research Question 3 — Acceptance Criteria, Enumerated and Concretely Verified

### 3.1 Criterion A — `modalTableauS4Keyed_complete` remains green

**Declaration**: `Cslib.Logic.Modal.Tableau.modalTableauS4Keyed_complete`
**Location**: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:4189`
**Signature**: `(φ₀ : Proposition Atom) (h : s4Valid φ₀) : modalTableauS4Keyed φ₀ = .closed`
**Namespace**: `Cslib.Logic.Modal.Tableau` (declared `FrameCompleteness.lean:66`, closed `:8262`)

**Verification method** — `#print axioms` via a standalone snippet (the authoritative check;
`lake build` alone cannot distinguish a `sorryAx`-tainted proof from a clean one when the module
is cached):

```lean
import Cslib.Logics.Modal.Tableau.FrameCompleteness
import Cslib.Logics.Modal.Tableau.CompletenessLoop
#print axioms Cslib.Logic.Modal.Tableau.modalTableauS4Keyed_complete
```

**Result**: `depends on axioms: [propext, Classical.choice, Quot.sound]` — the three standard
Lean axioms only. **PASS.**

### 3.2 Criterion B — the six landed `Decidable` instances remain green

All six verified by the same `#print axioms` route in a single snippet. All six returned
`[propext, Classical.choice, Quot.sound]`.

| System | Instance (fully qualified) | Location |
|--------|----------------------------|----------|
| K | `Cslib.Logic.Modal.Tableau.instDecidableKValid` | `Tableau/CompletenessLoop.lean:2295` |
| T | `Cslib.Logic.Modal.Tableau.instDecidableTValid` | `Tableau/FrameCompleteness.lean:1317` |
| B | `Cslib.Logic.Modal.Tableau.instDecidableBValid` | `Tableau/FrameCompleteness.lean:1933` |
| S5 | `Cslib.Logic.Modal.Tableau.instDecidableS5Valid` | `Tableau/FrameCompleteness.lean:2426` |
| Five | `Cslib.Logic.Modal.Tableau.instDecidableFiveValid` | `Tableau/FrameCompleteness.lean:3204` |
| KB5 | `Cslib.Logic.Modal.Tableau.instDecidableKb5Valid` | `Tableau/FrameCompleteness.lean:4080` |

**PASS — all six.**

### 3.3 Criterion C — Tableau sorry census not above baseline 1

**Reproduction command** (the one `README.md:59–63` documents; re-run, not trusted):

```bash
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; } \
  | sort -u | grep 'Modal/Tableau/'
```

**Result**: exactly one line —
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1251:    sorry`

Confirmed by reading `FrameSoundness.lean:1235–1251`: it is the recorded `[BLOCKED]` obstruction
inside `branchSatisfiableIn_s4FC_ancestor_redirect`, the general (non-`hdirect`) case where
`m.r` must be extended transitively and `hboxback`/`hdianeg` only constrain `src`. The
independent `--wfail` build corroborates it: exactly one `declaration uses 'sorry'` warning in
the subsystem, at `FrameSoundness.lean:1227` (declaration head for the same lemma).

Zero code-position `sorry` in any of the ten `S4/` modules or `LoopChecking.lean`.

**PASS — census is exactly 1, matching baseline.**

### 3.4 Criterion D — no new axioms above the subsystem baseline of zero

Three independent measurements, all agreeing:

1. `grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ | wc -l` → **0**
2. `grep -rnE '^axiom ' Cslib/ | wc -l` → **26** (repo-wide, none in this subsystem)
3. `scripts/check-axiom-census.sh` → **43 `sorryAx`-tainted declarations, baseline 43, exact-set
   match** (the baseline file lists 43 entries; `grep -vc '^#' scripts/axiom-census-baseline.txt`
   = 43)

Note that measurements 2 and 3 count different things and neither supersedes the other: 26 is
`axiom` *declarations*; 43 is the frozen set of *`sorryAx`-tainted public declarations*. The
task description's "43 repo-wide" refers to measurement 3. Both are unchanged.

**PASS — subsystem axiom count is 0; the repo-wide taint set matches the baseline exactly.**

### 3.5 Criterion E — `checkInitImports` and lint-style clean

- `lake exe checkInitImports` — **PASS** (§2).
- `lake exe lint-style` — **PASS**, exit 0, no output.

Note for anyone auditing: **none of the ten `S4/` modules imports `Cslib.Init` directly.** They
satisfy the requirement transitively — every one reaches `Cslib/Logics/Modal/Tableau/FmpMeasure.lean:9`,
which imports it directly. This is legitimate: `scripts/CheckInitImports.lean:31` computes
`env.importGraph.transitiveClosure`, so transitive satisfaction is exactly what the checker
tests. Do not "fix" this by adding direct imports; it would create shake residue.

### 3.6 Criterion F — regression corpora reproduce their recorded verdicts EXACTLY

See §5 in full. Summary: the in-tree corpus **PASSES**; one of the eight out-of-tree probe
harnesses **does not reproduce**, for a reason that predates this programme.

---

## 4. Research Question 4 — Standards Survey of the Subsystem

### 4.1 The ten new `S4/` modules and `LoopChecking.lean`: clean on every mechanical check

| Check | Result |
|-------|--------|
| Copyright header (`head -1` = `/-`, Copyright/Apache/Authors) | **11/11 PASS** — all carry the identical 2026 Brast-McKie block |
| `Cslib.Init` reachability | **11/11 PASS** (transitive via `FmpMeasure.lean:9`; `LoopChecking.lean:9` is direct) |
| Module docstring `/-! # ... -/` | **11/11 PASS** |
| docBlame — undocumented public declarations | **0** across all 11 files. Two raw grep hits were verified as false positives: prose lines starting with the word "structure" inside docstrings at `S4/Driver.lean:1251` and `S4/HintikkaInvariant.lean:59` |
| defLemma — `def` returning `Prop` | 6 occurrences, all legitimate named predicates with `∀`/`∃`/`match` bodies: `S4/BirthKey.lean:118` (`BoxPlusClosed`), `:221` (`keysOriginS4`), `S4/Hintikka.lean:74` (`modalHintikkaSetS4`), `:113` (`modalS4Saturated`), `S4/HintikkaInvariant.lean:828` (`S4OrderedFuelInv`), `S4/InvariantAcc.lean:882` (`worldsContiguousS4`). **No violation** |
| defsWithUnderscore — underscore in `def`/`abbrev`/`structure`/`inductive` name | **0 matches** |
| Debug artifacts (`#check`/`#eval`/`dbg_trace`) | **0 matches** in all 11 files, and 0 across the whole `Modal/Tableau/` tree |
| Code-position `sorry` | **0**. Six substring hits are all docstring prose ("sorry-free", "sorry/axiom counts") |
| `^axiom ` declarations | **0** |

**Lint suppressions in the eleven files — 4 total, all justified and narrow:**

| Location | Suppression | Justification |
|----------|-------------|---------------|
| `S4/Driver.lean:2315` | `let rec @[nolint docBlame] processNext` | Local recursive helper inside a `def` body; no standalone docstring is expected or possible |
| `S4/Driver.lean:2532` | `let rec @[nolint docBlame] processNext` | Same pattern, second driver variant |
| `S4/Redirect.lean:64` | `@[nolint unusedArguments]` on `abbrev Reds` | The abbrev *is* documented (`:59–63`); the suppression targets an unused typeclass argument, a different linter |
| `LoopChecking.lean:27` | `-- shake: keep` on `public import ...S4.Redirect` | Import-minimisation pin, the documented `lake shake` escape hatch |

No `set_option linter.` occurrences in any of the eleven files. The repository-wide blanket-suppression
ratchet is unchanged at **19/19**.

### 4.2 NOTATION.md conformance

**Zero** `notation`/`infix`/`infixl`/`infixr`/`prefix`/`postfix`/`syntax`/`macro_rules`/`declare_syntax_cat`
declarations exist anywhere in `Cslib/Logics/Modal/Tableau/` — the single grep hit
(`S4/Redirect.lean:95`) is the English word "prefix" in prose. The subsystem introduces no
notation at all, so NOTATION.md's scoping rules and the bare-capital-`S` collision warning are
vacuously satisfied. **No finding.**

### 4.3 `lake lint` (CI step 3) — FAILS, entirely pre-existing, zero in the new modules

```
-- Found 145 errors in 13476 declarations (plus 27793 automatically generated ones)
   in Cslib with 15 linters
```

**All 145 come from a single linter, `unusedArguments`** (the log contains exactly one
`linter reports` section header). They span 27 modules across `Computability/`, `Foundations/`,
`Logics/Bimodal/`, `Logics/LTL/`, `Logics/Modal/`, `Logics/Propositional/`, and `Logics/Temporal/`.

**Modal/Tableau contribution — 10 of 145:**

| File:line | Declaration | Unused |
|-----------|-------------|--------|
| `FmpMeasure.lean:2786` | `modalCount_notMem_mono` | arg 3 |
| `FrameSoundness.lean:122` | `branchSatisfiableIn_trivial_imp` | arg 3 |
| `FrameSoundness.lean:1015` | `modalTBoxSelf_sound` | `[Hashable Atom]` |
| `FrameSoundness.lean:1033` | `modalTDiaNegSelf_sound` | `[Hashable Atom]` |
| `FrameSoundness.lean:1119` | `modalFourBoxProp_sound` | `[Hashable Atom]` |
| `FrameSoundness.lean:1139` | `modalFourDiaNegProp_sound` | `[Hashable Atom]` |
| `FrameSoundness.lean:1394` | `modalFourBoxProp_sound_adequate` | `[Hashable Atom]` |
| `FrameSoundness.lean:1418` | `modalFourDiaNegProp_sound_adequate` | `[Hashable Atom]` |
| `FrameSoundness.lean:1620` | `modalBBoxBack_sound` | `[Hashable Atom]` |
| `FrameSoundness.lean:1635` | `modalBDiaNegBack_sound` | `[Hashable Atom]` |

**Zero errors in `Cslib/Logics/Modal/Tableau/S4/` and zero in `LoopChecking.lean`** — verified by
grepping the lint log for those paths (0 hits).

**Pre-existing, not caused by this programme**: `git log -L 1015,1016:.../FrameSoundness.lean`
attributes `modalTBoxSelf_sound` to `a9c3e79d` ("task 300 phase 2 (wip): T-system rules and
soundness lemmas"), far predating the programme. The pattern is uniform: an unused
`[Hashable Atom]` instance binder carried by a section variable.

**Disposition**: not a gate blocker. `lake lint` is not in PR CI (weekly cron only), the failures
are repo-wide and long-standing, and none is in the programme's territory. Recording it as an
explicit **Reasoned Exclusion**, not silently omitting it. A fix is mechanically easy
(`omit [Hashable Atom] in` before the affected block, per the `unusedSectionVars` idiom) and is a
good candidate for a separate hygiene task.

### 4.4 `lake build --wfail --iofail` (pre-pr-check step 5) — FAILS, reproduces the documented exclusion exactly

Exit 1. Six modules carry warnings. This **exactly matches** the Reasoned Exclusion recorded by
the `LoopChecking.lean` split task: *five untouched files, plus three pre-existing warnings
verbatim-moved into `S4/Driver.lean`.*

| Module | Warning count | Distinct sites |
|--------|---------------|----------------|
| `Modal/Tableau/S4/Driver.lean` | 4 | 3 — `:893` longLine (>100 chars), `:2395` flexible `simp_all`, `:2423` unusedSimpArgs |
| `Modal/Tableau/FrameSoundness.lean` | 1 | `:1227` declaration uses `sorry` |
| `Modal/Tableau/FrameCompleteness.lean` | 28 | `:5693` flexible `simp_all` (repeats on replay) |
| `Propositional/Tableau/Intuitionistic/Scheme.lean` | 2 | `:689`, `:7862` — `sorry` |
| `Propositional/Tableau/Intuitionistic/Completeness.lean` | 1 | `:150` — `sorry` |
| `Propositional/Tableau/Minimal/Completeness.lean` | 1 | `:144` — `sorry` |

Five untouched files + `S4/Driver.lean`'s three verbatim-moved sites. **The documented exclusion
reproduces precisely.** No new warning was introduced.

**Methodological warning for whoever re-runs this**: the wrapping shell command's exit code is
*not* lake's. A `lake build --wfail --iofail > log; echo $?` pipeline reports the `echo`'s status.
Read the log's `error: build failed` line, or capture `$?` immediately. This session initially
mis-read the result for exactly this reason.

### 4.5 ORGANISATION.md placement

The ten modules are at `Cslib/Logics/Modal/Tableau/S4/`, which `ORGANISATION.md:193–199`
documents with a bottom-up layering diagram. **Placement conformant.** The prose at `:198`
contains a factual error (finding D1). `Cslib.lean:507–516` carries all ten as `public import`s,
in alphabetical order, consistent with `mk_all`'s output.

The subsystem `README.md` is **not** an anomaly: `find Cslib -iname README.md` returns nine
directory-level READMEs (`Algorithms/`, `Computability/`, `Computability/Distributed/FLP/`,
`Crypto/`, `Foundations/`, `Languages/`, `Languages/Boole/`, `Logics/`, `Logics/Modal/Tableau/`).
Directory READMEs are an established convention here.

---

## 5. The Regression Corpora — Location, Invocation, Recorded Verdicts, and Live Results

### 5.1 In-tree corpus: `CslibTests/S4LoopGuardRegression.lean`

**Location**: `/home/benjamin/Projects/cslib/CslibTests/S4LoopGuardRegression.lean`
**Registered at**: `CslibTests.lean:21`
**How to run**: `lake test` (it is a `#guard_msgs in #eval` corpus; the assertions are checked at
elaboration time, so a green `lake test` *is* the pass)

**Size**: **214 lines**, not the 197 the task description and `README.md:107` both state. This is
not drift from the current programme: `git show` at the three commits that touched the file gives
159 → 197 → **214**, the last step being the phase-10 commit that added the regression witness
row. The stored `197` was correct when written and is now one revision stale. (Finding D5.)

**The eight recorded verdicts, all currently green** (each is a `/-- info: "..." -/ #guard_msgs in
#eval` row; `lake test` exit 0 means all eight matched):

| # | Row | Driver | Recorded verdict |
|---|-----|--------|------------------|
| 1 | KNOWN-UNSOUND | `modalExpandBranchesS4Keyed cex … 400` | `"CLOSED"` |
| 2 | Ordered-driver gate | `modalExpandBranchesS4KeyedOrdered cex … 400` | `"OPEN"` |
| 3 | Live-set control | `modalExpandBranchesS4 cex … 400` | `"OPEN"` |
| 4 | B-axiom control (keyed) | `modalExpandBranchesS4Keyed bAxiom …` | `"OPEN"` |
| 5 | T-axiom control (keyed) | `modalExpandBranchesS4Keyed tAxiom …` | `"CLOSED"` |
| 6 | B-axiom control (ordered) | `modalExpandBranchesS4KeyedOrdered bAxiom …` | `"OPEN"` |
| 7 | T-axiom control (ordered) | `modalExpandBranchesS4KeyedOrdered tAxiom …` | `"CLOSED"` |
| 8 | Soundness capstone | `example (h : modalTableauS4KeyedOrdered tAxiom = .closed) : s4Valid tAxiom` | Type-checks (compile-time API/shape regression, not computational — `h` is an unproved parameter; row 7 independently witnesses non-vacuity) |

**Row 1 is deliberately unsound and must stay `"CLOSED"`.** The file's docstring (`:60–73`) is
explicit: it records the shipped unordered driver's *current, unsound* verdict so that any silent
change to `modalStepBranchS4Keyed`/`blockingWorldS4Keyed` that reopens the closure is caught. A
gate that "fixes" this row to `"OPEN"` would destroy the regression.

**Result: PASS — all eight rows reproduce exactly.**

### 5.2 Out-of-tree probe harnesses

**Location**: `/home/benjamin/Projects/cslib/specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/`
**How to run**: `lake env lean <absolute path>` (they are standalone `#eval`-only files, not in
the lake build; they carry no proofs, no `sorry`, no `axiom`)

| File | Lines | `#eval`s | Cost | Recorded verdict lives in |
|------|-------|----------|------|---------------------------|
| `s4driver.lean` | 21 | 4 | **Cheap** (4 direct calls, fuel 400) | `reports/01_s4-keyed-guard-soundness-falsified.md:116–122` |
| `s4witness.lean` | 99 | 2 | **Cheap** (single linear trace, fuel 40) | `reports/02_redirect-inertness-divergence-audit.md:92–108, :162` |
| `s4probe.lean` | 187 | 7 | **Expensive** — `allUpTo 2 6` = 8,532 formulas, fuel 100, ×2 drivers | `reports/01_…md:85–95, :368–397` |
| `s4boxed.lean` | 295 | 3 | **Moderate** — 8,532-formula sweep ×2 orderings | `reports/02_…md:169–170, :265, :296, :437–455` |
| `s4ancestor.lean` | 422 | 8 | **Expensive** — differential sweep vs baseline 1650/6882/0 | Inline `(expect …)` annotations only; no logged actuals |
| `s4subtractive.lean` | 437 | 9 | **Very expensive** — 8,532-formula sweep ×3 drivers + brute-force semantic oracle over refl-trans frames | `reports/04_massacci-subtractive-blocking-priced.md:391–435`, §5.5 |
| `s4subtractive2.lean` | 228 | 4 | **Most expensive of the eight** — three sweeps, largest 95,730 formulas at fuel 100 | `reports/04_…md:461–472` (§6.3) |
| `s4subtractive3.lean` | 518 | 12 | **Very expensive** — three corpora, 110,741 leaves / 24,314 redirects, 8-condition per-redirect check | `reports/04_…md:475–486` (§6.4) |

**Import resilience after the module split: confirmed.** Every declaration these probes reference
(`blockingWorldS4Keyed`, `modalStepBranchS4Keyed(Ordered)`, `modalApplyOneS4(Keyed)`,
`modalExpandBranchesS4(Keyed)`, `successorBirthContent`, `modalNextWorld`, `modalKnownWorlds`,
`Accessibility`, `isModalClosed`, `modalSubfmls`, `modalMintShape`, `modalNonMintCandidates`)
remains reachable through `LoopChecking.lean`'s transitive `public import` chain. **No probe
needed an import change.** This is the split's central non-regression claim and it holds.

### 5.3 Live re-run: `s4driver.lean` — reproduces EXACTLY

```
$ lake env lean specs/553_.../artifacts/s4driver.lean
modalExpandBranchesS4Keyed cex, fuel 400 = CLOSED
modalExpandBranchesS4 cex, fuel 400 = OPEN
B axiom keyed = OPEN
T axiom keyed = CLOSED
```

Byte-for-byte identical to the four-line block recorded at
`reports/01_s4-keyed-guard-soundness-falsified.md:116–122`. **PASS.**

### 5.4 Live re-run: `s4witness.lean` — **DOES NOT REPRODUCE** (finding D8)

**Recorded** (`reports/02_redirect-inertness-divergence-audit.md:92–108`):

```
[6] …  keys = 0↦{} 1↦{+p0} 2↦{+(□p0∧◇p0)}
      guard(pos,p0,@2) = (some 1)
      T(box p0)@1 ∈ b  = false
[7] acc = [2→1 0→2 0→1]   keys unchanged   <-- REDIRECT edge 2→1 fires, no world minted
[8] b = T(□p0)@1, …                        <-- 4-rule repairs it ONE STEP LATER
      SATURATED OPEN
```

**Live**:

```
[6] …  keys = 0↦{} 1↦{+p0,+p0,+p0} 2↦{+(□p0∧◇p0)}
      guard(pos,p0,@2) = none
      T(box p0)@1 ∈ b = false
[7] acc = [2→3 0→2 0→1]
      keys = 0↦{} 1↦{+p0,+p0,+p0} 2↦{+(□p0∧◇p0)} 3↦{+p0,+□p0,+p0,+p0}
      guard(pos,p0,@2) = (some 3)
      SATURATED OPEN
```

Three concrete divergences:
1. `guard(pos,p0,@2)` is `none` at step [6] (recorded: `some 1`). It reads `some 1` at steps
   [3]–[4] and `some 3` at [7].
2. Step [7] **mints a fresh world 3** (`acc = [2→3 0→2 0→1]`) instead of firing the redirect edge
   `2→1` (`acc = [2→1 0→2 0→1]`).
3. The trace **terminates at [7]** with `SATURATED OPEN`; the recorded trace ran to [8]. Keys now
   carry a **boxed** member (`3↦{…,+□p0,…}`), which the recorded keys do not.

**Root cause — identified and attributed, not guessed.** This is precisely the behaviour
`reports/02` itself attributes to the *boxed-key variant*: its claim table records
*"reference produces `acc=[2→1 0→2 0→1]`; boxed produces `acc=[2→3 0→2 0→1]` (fresh world 3, no
redirect)"*. The boxed-key enrichment was subsequently **adopted into the shipped driver**:

- `boxPlusExtraS4` / `boxPlusPair` / `BoxPlusClosed` were introduced by
  `80feb736` ("task 563 phase 1: additive box-plus mint definitions"), switched into the mint
  payload by `7960c12e` ("phase 2-3: switch mint payload to additive box-plus"), and the birth
  key was enriched by `5733dcd1` ("phase 4-5: enrich birth key with box-plus members"), all dated
  **2026-08-05**.
- They now live at `Cslib/Logics/Modal/Tableau/S4/BirthKey.lean:102` (`boxPlusPair`), `:118`
  (`BoxPlusClosed`), `:132` (`boxPlusExtraS4`).

**Chronology proves this predates the current programme:**

```
$ git log --reverse --format='%h %ad' --date=short -- .../reports/02_redirect-inertness-divergence-audit.md
5ac7cbb7 2026-07-26                    # report 02 first committed
$ git log -1 --format='%h %ad' --date=short 5733dcd1
5733dcd1 2026-08-05                    # box-plus birth-key enrichment lands
$ git merge-base --is-ancestor 5733dcd1 c8fede26 && echo YES
YES                                    # box-plus precedes the 564 completion commit
```

The recorded trace was captured on 2026-07-26 code. The driver's minting behaviour was
deliberately changed on 2026-08-05, before the first commit of tasks 564/565/566/586. **The
divergence is a stale recorded verdict, not a behaviour-preservation failure of this programme.**

**Disposition required.** The acceptance criterion says "reproducing their recorded verdicts
EXACTLY". Taken literally, this fails. The correct disposition is to **re-record** `s4witness.lean`'s
verdict with a note that the box-plus enrichment superseded it — not to treat it as a regression
and not to silently drop the criterion.

### 5.5 The six unrun probes: recommendation

`s4probe.lean`, `s4boxed.lean`, `s4ancestor.lean`, `s4subtractive.lean`, `s4subtractive2.lean`,
`s4subtractive3.lean` were **not** re-run in this session. Cost is the reason: `s4subtractive2.lean`
alone sweeps 95,730 formulas at fuel 100 through two drivers, and `s4subtractive3.lean` performs
an 8-condition check at each of 110,741 terminal open leaves across three corpora.

**Two of them are known to have recorded-verdict integrity problems independent of any re-run:**

- **`s4probe.lean`** — `reports/01` describes a harness containing `dfs`/`tabCloses`, `dfsL`,
  `sat`/`isS4`/`hasCountermodel`/`notS4Valid`, `gen`/`allUpTo`, `classify`/`dfsR`, `statsL`/`badL`,
  and quotes a "Confirmed outputs" block with a countermodel print. **None of those identifiers
  exists in the current on-disk file** (zero grep matches for
  `dfsR|classify|statsL|badL|hasCountermodel|notS4Valid|def sat|def isS4`). The file was rewritten
  after report 01 was authored; the current version has `dfsKeyed`/`dfsOrdered`/`dfsLive`/
  `tabClosesKeyed` plus the phase-8 sweep. The `1650/6882/0` baseline persists across both
  versions, but report 01's specific "Confirmed outputs" trace **is not reproducible from the
  current file**. (Finding D9.)
- **`s4ancestor.lean`** — carries only inline `(expect …)` annotations, e.g. `:323`
  `"(expect ancestor-ordered = some false)"`. There is **no logged actual result** anywhere in the
  file or in the reports. It therefore has no "recorded verdict" to reproduce, and the acceptance
  criterion cannot be applied to it as written.

**Recommendation**: the gate should re-run the two cheap probes (`s4driver.lean`, `s4witness.lean`
— done here) and treat the six expensive ones as **out of scope for a routine acceptance gate**,
with the two integrity problems above recorded as findings. Re-running the full corpus is a
multi-hour job that would need its own task and its own budget; folding it into this gate is not
proportionate.

**Also stale**: `s4subtractive3.lean` embeds inline `LoopChecking.lean:NNNN` line-number citations
(`:6557-6559`, `:7061`, `:8806-8824`) that pointed into the pre-split 11,393-line file. Those
declarations now live in `S4/Hintikka.lean`, `S4/HintikkaInvariant.lean`, and `S4/Driver.lean`.
The declarations exist and are importable under the same names; only the file:line citations are
wrong. (Finding D7.)

---

## 6. Findings Ledger

Every stored figure in `Cslib/Logics/Modal/Tableau/README.md` was re-measured with the command
that README itself documents — which is exactly what its own §"Measured Baseline" preamble
instructs ("if a figure is quoted anywhere in this subsystem's documentation, quote the command
with it, and re-run the command rather than trusting the stored number"). Nine figures do not
reproduce.

| ID | Severity | Finding | Stored | Live | Locations |
|----|----------|---------|--------|------|-----------|
| **D1** | **High** | **S4 module count is TEN, not eleven.** `ls -1 Cslib/Logics/Modal/Tableau/S4/*.lean \| wc -l` = 10; `Cslib.lean` carries 10 (`:507–516`); the build-job delta was `+10`. `LoopChecking.lean`'s own bullet list and ASCII diagram enumerate exactly 10 — the file contradicts itself in the same docstring. | eleven | **ten** | `LoopChecking.lean:39`; `README.md:23, 47, 48, 50`; **`ORGANISATION.md:198`** |
| **D2** | **High** | **`LoopChecking.lean` is 1,626 lines, not 1,723** — a 97-line error. Verified at every commit since the barrel was finalised (`d9e47cf6`, `6a808d2e`, `3fd7715b`, `1d824cfd` all give 1,626). Declaration count (20) is correct. | 1,723 lines | **1,626 lines** | `README.md:45, 22` |
| **D3** | Medium | **Pre-split declaration count is 243, not 241**, so the derived "other 221 declarations" should be **223** — which matches the live `S4/` total exactly. The split *is* declaration-preserving (20 + 223 = 243); the arithmetic was right, the input was off by 2. | 241 / 221 | **243 / 223** | `README.md:43, 47` |
| **D4** | Medium | Repo-wide code-position sorry count is **28**, not 29, under the README's own documented two-grep command. | 29 | **28** | `README.md:65` |
| **D5** | Medium | `CslibTests/S4LoopGuardRegression.lean` is **214 lines**, not 197. Was 197 at `3b2fc5bb`; the phase-10 witness-row commit `ba0a7c22` took it to 214. | 197 | **214** | `README.md:107` |
| **D6** | Medium | `hintikkaS4_*` bridge set is **10 declarations**, not 8, under the README's own command against `S4/Hintikka.lean`. Separately, `ModalTableauResult` spans **9** subsystem modules (not 8) and **13** files repo-wide (not 9) — the repo-wide command scans `specs/`, so it is inherently volatile and should be rescoped or dropped. | 8 / 8 / 9 | **10 / 9 / 13** | `README.md:105, 143, 145` |
| **D7** | Low | `s4subtractive3.lean` embeds pre-split `LoopChecking.lean:NNNN` citations (`:6557-6559`, `:7061`, `:8806-8824`) now pointing at the wrong file. Declarations still exist under the same names in `S4/Hintikka.lean`, `S4/HintikkaInvariant.lean`, `S4/Driver.lean`. | — | — | `specs/553_…/artifacts/s4subtractive3.lean` |
| **D8** | **High** | **`s4witness.lean` does not reproduce its recorded trace** (§5.4). Cause identified and attributed to the box-plus birth-key enrichment landed 2026-08-05, chronologically **before** this programme. Not a behaviour-preservation failure — but the acceptance criterion as written is not met until the verdict is re-recorded. | `acc=[2→1 …]`, `guard=some 1` | `acc=[2→3 …]`, `guard=none` | `reports/02_…md:92–108, :162` |
| **D9** | Medium | **`reports/01`'s description of `s4probe.lean` does not match the on-disk file.** Eight identifiers it names have zero matches in the current file; the "Confirmed outputs" trace is not reproducible from it. The `1650/6882/0` baseline figure survives both versions. | — | — | `reports/01_…md:85–95, :368–397` |

### 6.1 Figures the README self-flags as un-re-measured — confirm they still are

`README.md:52–53` states `FrameSoundness.lean` 5,317 lines and `FrameCompleteness.lean` 4,307
lines "at the original `7eb51f69` capture — neither re-measured by the `S4/` split (out of scope;
re-run `wc -l` before citing)". Live: **5,396** and **8,264**. The `FrameCompleteness` figure is
off by a factor of ~1.9. These are **honestly labelled as stale** and the README instructs re-running,
so this is not a new defect — but any plan that quotes 4,307 will be badly wrong, and the figures
should be refreshed while the other rows are being corrected.

### 6.2 Figures that DO reproduce (recorded so the fix task does not touch them)

| Figure | Stored | Live | Status |
|--------|--------|------|--------|
| `LoopChecking.lean` declarations | 20 | 20 | ✔ |
| Pre-split `LoopChecking.lean` lines | 11,393 | 11,393 | ✔ |
| `S4/*.lean` total lines | 10,294 | 10,294 | ✔ |
| Subsystem sorry census | 1 | 1 | ✔ |
| Subsystem `^axiom` count | 0 | 0 | ✔ |
| Repo-wide `^axiom` count | 26 | 26 | ✔ |
| "Local re-derivation" comment sites | 12 | 12 | ✔ |
| `structure S4LoopInv` location | `S4/Invariant.lean` | `:85` | ✔ |
| Boneyard directory count | 1 | 1 | ✔ |
| Build job count | 3323 | 3323 | ✔ |

---

## 7. Research Question 5 — The Acceptance-Gate Verdict Structure

### 7.1 Proposed verdict grammar

The gate should emit exactly one of four verdicts. The distinction that matters is **"does this
block the programme?"**, not "is everything perfect?".

| Verdict | Meaning | Emitted when |
|---------|---------|--------------|
| **PASS** | Programme accepted; no follow-up needed | Every criterion in §7.2 green, and no finding at Medium or above |
| **PASS WITH FIX TASKS** | Programme accepted; follow-up tasks created and linked | Every criterion in §7.2 green, but one or more Medium/High findings exist that are (a) not proof defects, (b) not behaviour regressions, and (c) independently fixable |
| **CONDITIONAL** | Programme not yet accepted; a bounded, named repair must land first | A criterion is red but the repair is scoped, understood, and estimated |
| **FAIL** | Programme rejected back to implementation | A behavioural criterion is red — sorry census risen, a capstone or instance broken, a new axiom, or an unexplained regression-corpus divergence |

### 7.2 The blocking criteria (any red ⇒ CONDITIONAL or FAIL)

These are the criteria that speak to *correctness*, and they are the only ones that can block:

| # | Criterion | Verification | Live |
|---|-----------|--------------|------|
| B1 | `modalTableauS4Keyed_complete` green, standard axioms only | `#print axioms` | ✔ |
| B2 | All six `Decidable` instances green, standard axioms only | `#print axioms` | ✔ |
| B3 | Tableau sorry census ≤ 1 | README's two-grep command | ✔ (exactly 1) |
| B4 | Subsystem axiom declarations = 0 | `grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/` | ✔ (0) |
| B5 | Repo-wide `sorryAx` taint set unchanged | `scripts/check-axiom-census.sh` | ✔ (43/43 exact set) |
| B6 | `lake build Cslib` green | exit code | ✔ (3323 jobs) |
| B7 | `lake test` green — all eight `S4LoopGuardRegression` rows | exit code | ✔ |
| B8 | `lake exe checkInitImports` green | exit code | ✔ |
| B9 | `lake exe lint-style` green | exit code | ✔ |
| B10 | `mk_all` produces no change | diff `Cslib.lean` before/after | ✔ |
| B11 | Sorry/suppression/shake/lint-suppression/boneyard ratchets green | the four `scripts/check-*.sh` | ✔ (28/28, 18/18, 12/12, 19/19, 5/5) |

**All eleven blocking criteria are green.**

### 7.3 The non-blocking criteria (red ⇒ fix task, never a block)

| # | Criterion | Live | Rationale for non-blocking |
|---|-----------|------|----------------------------|
| N1 | `lake lint` green | ✘ 145 errors | Not in PR CI (weekly cron); all pre-existing; **zero** in programme territory |
| N2 | `lake build --wfail --iofail` green | ✘ 6 modules | Reproduces the documented Reasoned Exclusion **exactly**; no new warning introduced |
| N3 | Documentation figures reproduce | ✘ 9 findings | Documentation accuracy, not correctness. Independently fixable. |
| N4 | Out-of-tree probes reproduce | ✘ 1 of 2 run | Cause identified and chronologically attributed to pre-programme work |

### 7.4 What distinguishes PASS from fix-task-needed — the decision rule

A finding is **fix-task-needed** (not blocking) when **all three** hold:

1. **No proof is weaker.** No `sorry` added, no axiom added, no capstone or instance broken.
   (All nine findings satisfy this: not one touches a proof term.)
2. **The defect is either pre-existing or documentational.** Formally: `git log`/`git merge-base`
   shows the defect's origin commit is not in this programme's commit range, **or** the defect
   lives only in prose/comments/measurement rows.
3. **The fix is independently schedulable** — it does not need the programme reopened, and it does
   not gate any downstream consumer.

A finding is **blocking** when any of the following:

- A blocking criterion (§7.2) is red.
- A regression-corpus divergence has **no identified cause** — an unexplained behavioural change
  is a FAIL even if every build is green, because it means behaviour preservation is unproven.
  (D8 is *not* blocking precisely because its cause is identified and dated.)
- A documentation defect would mislead a reader into an incorrect *correctness* claim — e.g. a
  README understating the sorry census. (D1–D9 are all size/count/inventory figures; none
  misstates a correctness property.)

### 7.5 Recommended verdict for this gate

**`PASS WITH FIX TASKS`.**

All eleven blocking criteria are green. Behaviour preservation is demonstrated at the axiom level
for the capstone and all six instances, the sorry census is exactly at baseline, the subsystem
declares no axioms, and the in-tree regression corpus reproduces all eight verdicts. The nine
findings are documentation-accuracy defects and one stale out-of-tree recorded verdict whose
cause is identified and dated to before the programme began.

---

## 8. Recommended Fix-Task Decomposition

Three tasks, deliberately separated because they have different owners, different review surfaces,
and very different risk profiles.

### Fix task 1 — Correct the measurement rows (Low risk, documentation only)

**Scope**: `Cslib/Logics/Modal/Tableau/README.md`, `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
(docstring only), `ORGANISATION.md`.

Address D1–D6, plus refresh the two self-flagged stale figures from §6.1. Concretely:

- "eleven" → "ten" at `LoopChecking.lean:39`, `README.md:23, 47, 48, 50`, `ORGANISATION.md:198`.
- 1,723 → 1,626 at `README.md:45` (and the `:22` provenance sentence).
- 241 → 243 and 221 → 223 at `README.md:43, 47`.
- 29 → 28 at `README.md:65`.
- 197 → 214 at `README.md:107`.
- 8 → 10 (`hintikkaS4_*`) at `README.md:105`; 8→9 / 9→13 (`ModalTableauResult`) at `README.md:143, 145`,
  and **rescope or drop** the repo-wide `ModalTableauResult` command — as written it scans `specs/`
  and will drift every time a task artifact is added.
- Refresh `FrameSoundness.lean` 5,317 → 5,396 and `FrameCompleteness.lean` 4,307 → **8,264** at
  `README.md:52–53`.

**Verification**: re-run every command in the README's own `Measured Baseline` section and confirm
each stored number matches. This is the README's stated contract with itself.

**Zero risk to proofs** — no `.lean` proof term is touched.

### Fix task 2 — Re-record the out-of-tree probe verdicts (Low risk, artifacts only)

**Scope**: `specs/553_…/reports/02_…md`, `specs/553_…/reports/01_…md`,
`specs/553_…/artifacts/s4subtractive3.lean` (comments only).

Address D7, D8, D9:

- Annotate `reports/02`'s §2.2 trace as **superseded by the box-plus birth-key enrichment**, and
  append the live trace from §5.4 above with its date and the commits (`80feb736`, `7960c12e`,
  `5733dcd1`) that caused it. Do **not** delete the original — it documents a real historical
  refutation of `blockedRedirect_boxctx_mem`, which is still the reason those lemmas were removed.
- Annotate `reports/01`'s `s4probe.lean` harness description as describing a **superseded revision**
  of the file, and note that the `1650/6882/0` baseline is the only figure that carries across.
- Retarget the `LoopChecking.lean:NNNN` citations in `s4subtractive3.lean` to
  `S4/Hintikka.lean`, `S4/HintikkaInvariant.lean`, `S4/Driver.lean`, or replace them with
  declaration names (a durable anchor rather than a line number, which will drift again).

### Fix task 3 — `unusedArguments` hygiene (Medium risk, proof-adjacent; explicitly optional)

**Scope**: repo-wide, 145 sites across 27 modules; 10 in `Modal/Tableau/`.

The uniform pattern is a section-level `[Hashable Atom]` (or analogous) instance binder that the
declaration never uses. The idiomatic fix is `omit [Hashable Atom] in` before the affected block.

**This is explicitly out of scope for the tableau programme** and should not be folded into the
gate. It predates the programme by many tasks, spans seven top-level directories, and `lake lint`
is not in PR CI. Recommend a separate repo-hygiene task, or deliberate deferral with the
Reasoned Exclusion recorded.

### Explicitly NOT recommended

- **Do not** "fix" the `S4LoopGuardRegression.lean` KNOWN-UNSOUND row 1 to `"OPEN"`. It is a
  deliberate regression lock (`:60–73`).
- **Do not** add direct `import Cslib.Init` to the ten `S4/` modules. Transitive satisfaction is
  what `checkInitImports` tests; direct imports would create shake residue.
- **Do not** attempt to make `lake build --wfail --iofail` green as part of this gate. It requires
  either resolving the subsystem's one recorded `[BLOCKED]` `sorry` or touching five untouched
  files, both far outside the programme's scope.
- **Do not** re-run the six expensive probe harnesses as part of this gate (§5.5). If their
  verdicts must be re-established, that needs its own task and its own multi-hour budget.

---

## 9. Reproduction Appendix — Every Command Run in This Session

```bash
cd /home/benjamin/Projects/cslib

# CI steps 1-7
lake build Cslib                                       # exit 0, cached, 3323 jobs
lake exe checkInitImports                              # exit 0
lake lint                                              # exit 1, 145 unusedArguments errors
lake exe lint-style                                    # exit 0
lake test                                              # exit 0, 3863 jobs
lake exe mk_all --module                               # "No update necessary"
bash scripts/check-shake-residue.sh                    # 12/12 exact-set

# pre-pr-check ratchets
bash scripts/check-sorry-suppressions.sh               # markers 18/18, sorries 28/28
bash scripts/check-lint-suppressions.sh                # 19/19
bash scripts/check-axiom-census.sh                     # 43/43 exact-set
bash scripts/check-boneyard-quarantine.sh              # all five invariants OK
lake build --wfail --iofail                            # exit 1, 6 modules (documented exclusion)

# axiom verification (the authoritative behaviour-preservation check)
#   snippet importing FrameCompleteness + CompletenessLoop, then:
#   #print axioms Cslib.Logic.Modal.Tableau.modalTableauS4Keyed_complete
#   #print axioms Cslib.Logic.Modal.Tableau.instDecidable{K,T,B,S5,Five,Kb5}Valid
#   -> all seven: [propext, Classical.choice, Quot.sound]

# regression probes
lake env lean specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4driver.lean
lake env lean specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4witness.lean

# census re-measurement (README's own documented commands)
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; } \
  | sort -u | grep 'Modal/Tableau/'                    # 1 line
grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ | wc -l    # 0
grep -rnE '^axiom ' Cslib/ | wc -l                         # 26
PAT='^(private )?(protected )?(noncomputable )?(theorem|lemma|def|abbrev|instance|structure|inductive) '
grep -cE "$PAT" Cslib/Logics/Modal/Tableau/LoopChecking.lean               # 20
cat Cslib/Logics/Modal/Tableau/S4/*.lean | grep -cE "$PAT"                 # 223
cat Cslib/Logics/Modal/Tableau/S4/*.lean | wc -l                           # 10294
ls -1 Cslib/Logics/Modal/Tableau/S4/*.lean | wc -l                         # 10
wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean                         # 1626
wc -l CslibTests/S4LoopGuardRegression.lean                                # 214

# attribution
git merge-base --is-ancestor 5733dcd1 c8fede26 && echo YES   # box-plus predates 564
git log --reverse --format='%h %ad' --date=short -- \
  specs/553_*/reports/02_redirect-inertness-divergence-audit.md   # 5ac7cbb7 2026-07-26
```

**Warning on exit codes**: wrapping a `lake` invocation in a compound command that ends with
`echo` makes `$?` report the `echo`. Capture `$?` immediately or read lake's own
`error: build failed` line. This session initially mis-read `lake build --wfail --iofail` for
exactly that reason.
