# Boneyard -- Archived Dead-Consumer Code

This directory contains archived Lean declarations that are no longer part of the active
development path in `Cslib/`. Nothing here is deleted -- files are preserved verbatim for
provenance, so a future reader can see what was proven and why it was set aside, without any of
it being reachable from the build.

This convention is ported from `BimodalLogic/FormalSystem/Boneyard/README.md` (a sibling formal
methods repository), scaled down to this repository's much smaller archival needs.

## Archival Criterion

A declaration (or small group of declarations) belongs here when it is **unreachable from every
Lake target root** -- i.e. it has zero code consumers anywhere in `Cslib/`, `CslibTests/`, or
`scripts/`, verified by a word-boundary grep on its full name -- and is not intended to become
reachable again. Unreachability alone is not sufficient: code that is merely not-yet-wired, or
that a near-term successor task is expected to consume, belongs in live code, not here.

Archival does **not** require that a declaration be broken, wrong, or superseded. Every
declaration currently archived under `Boneyard/` is **sorry-free, proven, and true**. Eligibility
here rests purely on re-verified zero-consumer status; moving (never deleting) is the right
disposition specifically *because* the provenance -- what was proven, and that it was proven
correctly -- is the point of keeping it at all.

## Build Policy: Liveness Equals Reachability

There is no Lake target covering `Boneyard/`. Concretely:

- `Boneyard/` is **never built**, never linted, never counted in any sorry/axiom census, and
  never touched by `mk_all`, `shake`, or `lint-style`. See "Why This Is Free" below for the
  mechanical reason every one of those tools is blind to it by construction.
- Import lines inside archived files are **historical text, not build edges**. An `import`
  statement at the top of a Boneyard file records what the code used to depend on; it does not
  cause anything to be built, because the file itself is never reached by any Lake target.
- Stale imports in never-built code are **cosmetic** and need not be repaired. If an archived
  file's import no longer resolves to a file at that path, that is expected and not a defect.

## The `#exit` Guard and `ARCHIVED (Boneyard)` Header Convention

Every `.lean` file under `Boneyard/` follows this shape, in order:

1. The import block needed to state the archived declarations (recorded as historical text, not
   a build edge -- see above).
2. An `ARCHIVED (Boneyard)` header docstring naming every declaration moved into the file, noting
   why it was archived (typically: sorry-free, proven, zero live consumers), and ending with the
   sentence `Do not import from live code.`
3. `#exit`.
4. The excised code, verbatim, including each declaration's own original docstring.

The `#exit` guard matters even though the code would in principle still elaborate: archived
declarations are frequently stated over live definitions in the file they were excised from, and
those live definitions keep evolving. The point of quarantine is that nothing re-checks an
archived declaration as its former dependencies change out from under it. `#exit` makes that
inertness explicit and structural, rather than an accident of nobody importing the file today.

## Directory Inventory

| Subdirectory | Files | Lines | Archived From | Why Archived |
|---|---:|---:|---|---|
| [`ModalTableauS4Keyed/`](ModalTableauS4Keyed/README.md) | 2 | 142 | `Cslib/Logics/Modal/Tableau/LoopChecking.lean` | Two zero-consumer, sorry-free declaration units from the S4-keyed loop-checking track, both re-verified zero-consumer by full-name grep: the `blockedRedirect_*_of_*Origin` pair (`RedirectOriginTransfer.lean`, 106 lines) and the `keysRootEmpty` pair (`KeysRootEmpty.lean`, 36 lines) |

*(File and line counts above are measured, not estimated; they are updated as each unit lands.)*

## Sorry Counts Here Are Not Bugs

If an archived declaration carries a `sorry`, it represents an archived dead end -- a proof
obligation that was deliberately abandoned along with the surrounding approach -- not an open
obligation tracked by this library's sorry census. (As of the declarations currently archived
here, none carries a `sorry`; all three are proven. This note is a standing policy for future
Boneyard growth, not a description of the current contents.)

## Do Not Grep This Directory When Auditing Live Identifier Usage

Declaration names inside `Boneyard/` are frozen at the moment of archival and will diverge from
live code over time as the surviving declarations are renamed, refactored, or removed. A grep
for a live identifier that happens to also appear in an archived file's prose or code will
produce a false positive. When auditing consumer status of a live declaration, scope the grep to
`Cslib/`, `CslibTests/`, and `scripts/` -- never to `Boneyard/`.

## Three Standing Invariants

Each of the following would individually undo the quarantine if violated. They are recorded here
because the exclusion mechanism (see "Why This Is Free" below) is otherwise entirely implicit and
unasserted -- nothing in the existing CI or lint pipeline would notice a violation on its own.

1. **Never add `[[lean_lib]] name = "Boneyard"` (or any Boneyard glob/root) to `lakefile.toml`.**
   That single line would make `lake exe mk_all --check` demand a `Boneyard.lean` aggregator and
   would pull the entire tree into the build, the censuses, and `lint-style`.
2. **Never `import Boneyard.*` from anything reachable from `Cslib.lean`.** Because the `Cslib`
   library's `srcDir` defaults to the repository root, the module name `Boneyard.Foo` *does*
   resolve on the source search path even though it is never built by default -- this is the one
   live vector by which an archived file could be dragged into the build, shake, lint-style,
   `checkInitImports`, and the axiom census simultaneously.
3. **Never pass `--scope Boneyard` (or any Boneyard-rooted path) to
   `scripts/check-sorry-suppressions.sh`.** Its `--scope` option is the one code path among the
   ratchet scripts that will walk an arbitrary directory rather than the hardcoded `Cslib` scan
   root.

## Two Repo-Wide Scanner Constraints

Every build/lint/census mechanism in this repository except the two below is scoped either by
Lake `lean_lib` declaration, by import reachability from `Cslib.lean`, or by a hardcoded `Cslib`
scan root, and is therefore blind to a root-level `Boneyard/` by construction (see "Why This Is
Free"). Two mechanisms are genuine exceptions -- they walk `.lean` files repo-wide with no
`Cslib` anchor:

1. **`.github/workflows/todo-issue.yml`** is diff-driven on every push to `main`, with no `paths`
   or `paths-ignore` filter, and files a GitHub issue for every `TODO:`/`FIXME:`-family marker
   (via `.github/todo-to-issue-lean.json`) it finds in the diff. **Archived code under
   `Boneyard/` MUST NOT carry live `TODO:`/`FIXME:`/`BUG:`/`HACK:`/`NOTE:`/`QUESTION:` markers.**
   If a note is genuinely needed in an archived file, neutralize it to `ARCHIVED-TODO:` (or the
   equivalent prefixed form) so it reads as inert prose rather than an actionable marker. Editing
   `todo-issue.yml` itself to add a `paths-ignore` filter was considered and rejected: every file
   under `.github/workflows/` is shared with the upstream `leanprover/cslib` remote, and editing
   one adds a recurring sync-conflict hunk on every future sync. The zero-cost fix is the
   no-live-marker rule above.
2. **`scripts/bench/size/run`** globs every non-dotted top-level directory for `.lean` files and
   would count `Boneyard/` lines as live in its size benchmark output. It is a manual tool, not
   wired into any CI workflow, so this is a local measurement distortion rather than a failing
   gate -- but it is exactly the failure mode this convention exists to guard against elsewhere
   (see the `B0`-style self-test at `scripts/check-boneyard-quarantine.sh`).

## Why This Is Free: Root-Level Placement Is Load-Bearing, Not Cosmetic

`Boneyard/` is placed at the **repository root**, as a sibling of `Cslib/`, not underneath it.
This is a deliberate architectural choice, not a stylistic one. Every build/lint/census mechanism
in this repository is scoped in one of three ways: by the Lake `lean_lib` declaration for
`Cslib` (whose default targets and module roots are the single module `Cslib`), by *import
reachability* from `Cslib.lean` (`lint-style`, `checkInitImports`, the axiom census), or by a
hardcoded `Cslib` scan root (the ratchet scripts under `scripts/`). None of these mechanisms
globs the repository root, so a root-level `Boneyard/` is invisible to all of them without a
single config edit.

Placing the directory **under `Cslib/`** instead would break this immediately: `lake exe mk_all
--check` globs every `.lean` file inside the `Cslib/` directory tree and would demand each one be
imported from `Cslib.lean`, which would in turn pull the archived declarations into the build,
the sorry/axiom censuses, and `lint-style` -- the exact opposite of quarantine. Root-level
placement is therefore what makes this convention free; moving `Boneyard/` under `Cslib/` at any
point in the future would silently undo it.
