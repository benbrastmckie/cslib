# ModalTableauS4Keyed -- Archived Zero-Consumer Declarations from `LoopChecking.lean`

## Why These Declarations Were Archived

Three declaration units were excised from
`Cslib/Logics/Modal/Tableau/LoopChecking.lean` and moved here, verbatim, after a re-audit
confirmed each is zero-consumer:

- `blockedRedirect_boxctx_mem_of_boxOrigin` and `blockedRedirect_diaNeg_mem_of_diaOrigin`
  (`RedirectOriginTransfer.lean`)
- `keysRootEmpty` and `keysRootEmpty_entry` (`KeysRootEmpty.lean`)

**All three units are sorry-free, proven, and true.** Eligibility for archival rests purely on
re-verified zero-consumer status -- a word-boundary grep of each full declaration name over
`Cslib/`, `CslibTests/`, `scripts/`, and `Cslib.lean` returning zero code-consumer hits -- and
not on the code being broken, wrong, or superseded. Every one of these declarations correctly
proves what its docstring claims.

**Moving, never deleting, is the right disposition for code with this character.** The whole
point of archiving proven, true, zero-consumer code (rather than deleting it) is that the
provenance itself is valuable: a future task revisiting the S4-keyed loop-checking track can find
exactly what was proven, in what form, and read the original docstrings, without that
information having to be reconstructed from git history.

## Contents

| File | Declarations | Archived From |
|---|---|---|
| `RedirectOriginTransfer.lean` | `blockedRedirect_boxctx_mem_of_boxOrigin`, `blockedRedirect_diaNeg_mem_of_diaOrigin` | `Cslib/Logics/Modal/Tableau/LoopChecking.lean` |
| `KeysRootEmpty.lean` | `keysRootEmpty`, `keysRootEmpty_entry` | `Cslib/Logics/Modal/Tableau/LoopChecking.lean` |

See `../README.md` for the general Boneyard convention (`#exit` guard, `ARCHIVED` header,
build-exclusion mechanics, and the standing invariants that keep this directory outside the
build).
