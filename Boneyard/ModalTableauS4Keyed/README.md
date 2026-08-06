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

## The `keysRootEmpty` Audit (Travelled from `LoopChecking.lean`)

`LoopChecking.lean` carried a `### keysRootEmpty -- the Root World Never Re-Mints` section
comment that was an audit record, not ordinary documentation. When the pair was excised, the
comment was split: the `keysOriginS4` retraction paragraphs (about a live, heavily-consumed
declaration) stayed in `LoopChecking.lean`, re-homed under a
`### keysOriginS4 Consumer Audit -- Retraction of an Earlier Hedge` heading. The paragraphs
below, specific to `keysRootEmpty` itself, travelled here verbatim.

> A small standalone bookkeeping fact that `keysOriginS4` itself does not supply: `keysOriginS4`'s
> root disjunct (`w = 0`) says nothing about the recorded key at `0`, but the driver's actual seed
> `keys := [(0, ∅)]` combined with the fact that world `0` is never freshly minted (new entries
> are always `(modalNextWorld b, ...)`, strictly greater than every existing label, hence never
> `0`) means `0`'s recorded key is *always* `∅`. Threaded the same way as `keysOriginS4` itself:
> an extra hypothesis, never an `S4LoopInv` field.
>
> `keysRootEmpty` **is** orphaned -- audited, no longer hedged:
>
> ```
> grep -rn 'keysRootEmpty' --include='*.lean' Cslib/ CslibTests/ | wc -l
> ```
>
> 6 hits, all in `LoopChecking.lean` at the time of this audit: the section heading, the two
> declarations (`keysRootEmpty` and `keysRootEmpty_entry`) with their docstrings, and one prose
> mention in the "Redirect-Inertness Assembly" section. Outside its own entry lemma the
> definition had **zero** consumers. It was retained deliberately rather than pending any
> re-plan: it is small, sorry-free, and a true statement about the driver's seed state that a
> route (1) successor may want -- which is exactly why it is archived here rather than deleted.

A subsequent re-audit, re-run immediately before this excision, reconfirmed the zero-consumer
verdict against the then-current tree, per the Boneyard archival criterion.
