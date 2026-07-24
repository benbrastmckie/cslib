# Research: Remove Bimodal/Temporal Linter Suppressions

Task type: cslib. Scope: nine files carrying file-scoped `set_option linter.* false`
suppressions inherited verbatim from the external BimodalLogic port. Goal: determine, per file,
exactly which suppressions exist and which linter findings actually fire when each is removed, so
the implementer can reformat + drop (or narrow) them.

## Method

All findings below are **empirical**, not guessed. For each suppression the suppression line was
removed from a working copy, the owning module was rebuilt with `lake build <Module>`, and the
emitted warnings were captured, after which the file was reverted (`git checkout`). The
Mathlib linters in question are **syntax linters that run during `lake build`**, not environment
linters — `lake lint` / `lake exe lint-style` do **not** surface them, so verification must use
`lake build <Module>`. The workspace was confirmed clean after all probes.

Linter definitions consulted (Mathlib, in `.lake/packages/mathlib/`):
- `Mathlib/Tactic/Linter/Style.lean` — `longLine` (100-char limit, ignores `http`/imports),
  `setOption`.
- `Mathlib/Tactic/Linter/EmptyLine.lean` — `emptyLine`.
- `Mathlib/Tactic/Linter/FlexibleLinter.lean` — `flexible`.
- `unusedSimpArgs` is a Lean/Mathlib simp linter.

CSLib enables these by default via `Cslib/Init.lean` → `Cslib.Foundations.Lint.Basic` +
`Mathlib.Init`. The `longLine` threshold is the Mathlib default of **100** (CSLib does not
override `linter.style.longLine.maxLineLength`).

## Three linter mechanics that drive the whole task

These behaviours (read from source and confirmed empirically) explain every result and dictate
the fix order:

1. **`emptyLine` is gated on a clean slate.** `emptyLineLinter` returns early if the file has
   *any* non-informational message (`EmptyLine.lean:102`). It therefore only fires once
   `longLine`, `flexible`, and `unusedSimpArgs` are already clean. It flags blank lines **inside
   a command** (e.g. inside a proof body), never blank lines *between* top-level declarations.
   Consequence: `emptyLine` must be the **last** suppression resolved in any file that also has a
   real finding; otherwise its findings are masked.

2. **`setOption` flags unscoped `linter.flexible`.** `setOptionLinter` (`Style.lean:118`) warns
   "Unscoped option `linter.flexible` is not allowed" for a file-scoped `set_option
   linter.flexible false`, but **not** for the scoped `set_option linter.flexible false in <decl>`
   form. Consequence: wherever a file carries both `setOption` and file-scoped `flexible`
   suppressions, the `setOption` suppression exists **solely** to silence the warning about the
   `flexible` line. Narrowing `flexible` to per-declaration `... in` form removes the `setOption`
   trigger, so the `setOption` suppression can then be dropped too. This was confirmed: removing
   only the `setOption` suppression (keeping the file-scoped `flexible` line) fires
   "Unscoped option linter.flexible is not allowed" in both MCSProperties (L49) and Connectives (L26).

3. **`longLine` counts Unicode columns, threshold 100.** Byte-length over-counts these
   symbol-heavy files, so only a Unicode-column measurement (confirmed by the linter itself) is
   authoritative.

## Per-file inventory and empirical findings

Legend: **DEAD** = suppression removed, module rebuilt, zero findings (inherited verbatim, safe
to drop with no reformatting). **REAL** = findings fire; reformatting or narrowing required.

### 1. `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` (L48–50)
| Suppression | Result |
|---|---|
| `linter.style.emptyLine` (L48) | **DEAD** |
| `linter.style.setOption` (L49) | Live only as guard for the `flexible` line (see mechanic 2) |
| `linter.flexible` (L50) | **DEAD** (no flexible findings) |

Resolution: **drop all three.** Because `flexible` has no findings, the file-scoped `flexible`
line can be removed outright; that removes the `setOption` trigger, so `setOption` drops too;
`emptyLine` is dead. **Zero reformatting.**

### 2. `Cslib/Logics/Bimodal/Theorems/Combinators.lean` (L57–58)
| Suppression | Result |
|---|---|
| `linter.style.emptyLine` (L57) | **DEAD** |
| `linter.style.longLine` (L58) | **REAL** — 6 lines >100 chars |

Long lines (original file numbering): **L82 (108), L108 (108), L140 (101), L164 (107), L184
(102), L185 (118)**. Resolution: drop `emptyLine` (dead); wrap the 6 long lines, then drop
`longLine`. (These 6 lines span multiple declarations, so file-scoped `longLine` cannot be
narrowed to a single `... in` — wrapping is required to drop it.)

### 3. `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` (L30)
| Suppression | Result |
|---|---|
| `linter.style.longLine` (L30) | **DEAD** (0 long lines) |

Resolution: **drop outright. Zero reformatting.**

### 4. `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` (L31–32)
| Suppression | Result |
|---|---|
| `linter.style.longLine` (L31) | **DEAD** (0 long lines) |
| `linter.style.emptyLine` (L32) | **REAL** — 5 blank-line-inside-command findings |

Offending blank lines (original file numbering): **L158, L167, L184, L187, L196** — inside the
`persistence` proof and the following declarations. Resolution: drop `longLine` (dead); remove or
replace-with-comment the 5 blank lines, then drop `emptyLine` (resolve it **last**, per mechanic 1).

### 5. `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` (L26–29)
| Suppression | Result |
|---|---|
| `linter.style.setOption` (L26) | Live only as guard for the `flexible` line (mechanic 2) |
| `linter.flexible` (L27) | **REAL** — `simp` flexible tactic in two decls |
| `linter.style.emptyLine` (L28) | **DEAD** |
| `linter.style.longLine` (L29) | **DEAD** (0 long lines) |

Flexible findings: the `simp` inside the `weakening` side-condition `(by intro x; simp; intro h;
left; exact h)` at **L67** (`def iffElimLeft`, ~L60–68) and **L78** (`def iffElimRight`,
~L71–79). Resolution: drop `emptyLine` + `longLine` (both dead). **Narrow `flexible` to
per-declaration** `set_option linter.flexible false in` on `iffElimLeft` and `iffElimRight`
(the reuse-first CSLib-consistent pattern — it matches the already-narrowed form in
`Temporal/Metalogic/GeneralizedNecessitation.lean`). Once `flexible` is scoped, the file-scoped
line is gone, so `setOption` no longer fires and its suppression drops too. (Alternative: rewrite
the two `simp`s to `simp only [...]`; higher risk to a working ported proof, so the `... in`
narrowing is recommended.)

### 6. `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` (L28–29)
| Suppression | Result |
|---|---|
| `linter.style.emptyLine` (L28) | **DEAD** |
| `linter.style.longLine` (L29) | **DEAD** (0 long lines) |

Resolution: **drop both outright. Zero reformatting.**

### 7. `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` (L24–26)
| Suppression | Result |
|---|---|
| `linter.unusedSimpArgs` (L24) | **DEAD** |
| `linter.style.emptyLine` (L25) | **DEAD** |
| `linter.style.longLine` (L26) | **DEAD** (0 long lines) |

Resolution: **drop all three outright. Zero reformatting.**

### 8. `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` (L24 file-scoped; L45/78/154 scoped)
| Suppression | Result |
|---|---|
| `linter.style.emptyLine` (L24, file-scoped) | **DEAD** |
| `linter.flexible ... in` (L45, scoped) | **LIVE** — `simp` at L51; already narrowed |
| `linter.unusedSimpArgs ... in` (L78, scoped) | **LIVE** — unused simp arg at L88; already narrowed |
| `linter.unusedSimpArgs ... in` (L154, scoped) | **LIVE** — unused simp arg at L164; already narrowed |

Resolution: **drop only the file-scoped `emptyLine` (L24).** The three `... in` suppressions are
already in the task's desired per-declaration form and are all live — **keep as-is**. Zero
reformatting.

### 9. `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` (L28)
| Suppression | Result |
|---|---|
| `linter.style.emptyLine` (L28) | **DEAD** |

Resolution: **drop outright. Zero reformatting.**

## Aggregate summary

Of the file-scoped suppressions across the nine files, **only four carry real findings**:

1. **Combinators `longLine`** — wrap 6 lines (L82, L108, L140, L164, L184, L185).
2. **Perpetuity/Principles `emptyLine`** — remove 5 blank lines (L158, L167, L184, L187, L196).
3. **Connectives `flexible`** — narrow to `... in` on `iffElimLeft` / `iffElimRight`.
4. **Connectives `setOption`** — coupled to (3); drops automatically once `flexible` is scoped.

The **GeneralizedNecessitation** scoped `... in` suppressions (3) are live but already narrowed —
leave them. **Everything else is DEAD** (inherited verbatim from the port) and can be deleted with
zero reformatting: MCSProperties (all 3), Combinators `emptyLine`, Perpetuity/Helpers `longLine`,
Perpetuity/Principles `longLine`, Connectives `emptyLine` + `longLine`, Core (both), TemporalDerived
(all 3), GeneralizedNecessitation file-scoped `emptyLine`, PropositionalHelpers `emptyLine`.

That is **13 of the ~17 file-scoped suppression lines droppable with no code change**, 2 files
needing light reformatting (6 line wraps + 5 blank-line removals), and 1 file needing a 2-decl
`flexible` narrowing.

## Recommended fix ordering (per file with a real finding)

Because `emptyLine` is masked while any other warning is present (mechanic 1), within a file:
1. Fix/narrow `longLine`, `flexible`, `unusedSimpArgs` first and drop their suppressions.
2. Then remove the offending blank lines and drop `emptyLine` **last**.
3. For the `setOption`+`flexible` pair, narrow `flexible` to `... in` **before** dropping
   `setOption` (dropping `setOption` while a file-scoped `flexible` remains re-fires it).

## Verification

- Per file: `lake build <Module.Name>` must produce zero warnings after the suppression(s) are
  dropped. (`lake lint` / `lake exe lint-style` will NOT catch these — they are build-time syntax
  linters.)
- Whole task: `lake build` clean, then the CSLib CI order in `.claude/rules/cslib.md`
  (`checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`).

## Zero-debt / CSLib-standards notes

- Every resolution is structural: delete dead suppressions, wrap lines, remove blank lines,
  or narrow to per-declaration scope. **No `sorry`, no new axioms, no vacuous definitions.**
- The `flexible` narrowing (`set_option linter.flexible false in`) is the reuse-first,
  CSLib-consistent choice: it is the exact pattern already present in
  `GeneralizedNecessitation.lean` and is the fix the `setOption` linter's own message recommends,
  and it avoids rewriting a working ported `simp` proof.
- `emptyLine` fixes should prefer removing the stray blank line over inserting a placeholder
  comment, unless a comment genuinely aids readability (the linter accepts either).
