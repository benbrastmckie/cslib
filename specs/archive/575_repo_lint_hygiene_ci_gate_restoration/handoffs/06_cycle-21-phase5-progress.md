# Cycle 21 Handoff — Phase 5 Suppression Audit

- **Task**: 575
- **Session**: sess_1785189125_8d6d8d
- **Cycle**: 21 (twenty-second resume)

## What happened this cycle

Resumed Phase 5 (suppression audit) per the plan's RESUME HERE pointer, starting at
`Duality.lean` and working down the count-3 tier smaller-first, per the delegation instructions.

Processed 5 files, all 3→0 blanket-suppression clean, each verified by scoped rebuild of the
file plus every direct downstream importer, then committed individually (commit-per-green-substep):

1. `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` (420 lines, commit `5169b787`) — 2
   `linter.flexible` sites (bare `simp [X]` followed by `rw [...]`) narrowed to 2
   declaration-scoped `set_option linter.flexible false in`.
2. `Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean` (437 lines, commit `5219bcf6`) — 2
   `linter.flexible` sites, both a simple single-lemma `simp [Set.mem_insert_iff] at h`,
   manually reconstructed as `simp only [Set.mem_insert_iff] at h`.
3. `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` (483 lines, commit `13fbd3cc`) — all 3
   blanket suppressions were unnecessary; zero warnings surfaced on removal.
4. `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (522 lines, commit
   `de86fd71`) — 24 `longLine` warnings (long `have h : DerivationTree ... :=` type
   annotations) fixed by wrapping onto a continuation line; 13 `dupNamespace` warnings on the
   `Chronicle` structure and its `c0`-`c5'` condition defs (deliberately named to match the
   enclosing `...Chronicle` namespace, mirroring the Bimodal tree's identical pattern per this
   file's own module docstring) narrowed to 10 per-declaration
   `set_option linter.dupNamespace false in` lines rather than fixed by renaming (renaming would
   alter the public API, out of hygiene-only scope).
5. `Cslib/Logics/Temporal/Metalogic/MCS.lean` (538 lines, commit `da6f9945`) — 3 identical
   `unusedSimpArgs` sites (an 8-lemma `simp only [...]` block where only
   `Formula.swapTemporal` was actually used) reduced via one `replace_all` edit to
   `simp only [Formula.swapTemporal]`.

Plan file updated (commit `2a721a5c`) with the cycle-21 RESUME HERE entry, header stats, and
Phase 5 heading counts. Full CSLib CI pipeline re-run at cycle close and confirmed clean:

- `lake build --wfail --iofail`: exit 1, exactly the 5 documented baseline sorry warnings
  (`FrameSoundness.lean:1252`, `Intuitionistic/Scheme.lean:570,2583`,
  `Intuitionistic/Completeness.lean:124`, `Minimal/Completeness.lean:118`), no others.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake exe mk_all --module`: "No update necessary".
- `lake shake --add-public --keep-implied --keep-prefix Cslib`: exactly the 12 documented
  upstream-shared files, zero local-only regressions.
- `lake lint`: zero matches on the 7 prevention categories (docBlame, defLemma,
  defsWithUnderscore, simpNF, unusedSectionVars, topNamespace, dupNamespace); only out-of-scope
  `unusedArguments` findings remain (not this task's target).
- `lake test`: exit 0.
- Sorry/axiom/vacuous counts unchanged from baseline: 168 naive-grep sorry occurrences (5
  declarations), 26 axioms, 1 pre-existing unrelated vacuous false positive
  (`Computability/URM/Basic.lean:92`).

## Live re-derived Phase 5 remainder (end of cycle 21)

96 local-only blanket suppressions across 59 files (down from 111/64 at cycle 20's close).
Command used (fs>0 filter, then upstream-gated):

```bash
grep -rln "set_option linter\." Cslib/ | while read f; do
  fs=$(grep "set_option linter\." "$f" | grep -vc " in$")
  if [ "$fs" -gt 0 ]; then echo "$fs $f"; fi
done | sort -rn | while read fs f; do
  git cat-file -e upstream/main:"$f" 2>/dev/null || echo "$fs $f"
done
```

Remaining worst-offenders:
- Count-6: `Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean`
  (3048 lines) — deliberately deferred, by far the largest remaining file.
- Count-3 (5 files): `Bimodal/Metalogic/Soundness/Soundness.lean` (845 lines, **next target**),
  `Bimodal/Metalogic/Decidability/Saturation.lean` (708 lines),
  `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` (578 lines — the Bimodal
  counterpart of the Temporal `ChronicleTypes.lean` just closed this cycle; almost certainly
  needs the identical structure/c0-c5' dupNamespace-narrowing + longLine treatment, re-use this
  cycle's pattern rather than re-deriving it), `Foundations/Logic/Metalogic/Chronicle/
  SinceSeedConsistency.lean` (1072 lines).
- Count-2/count-1 tail below that: not individually surveyed this cycle, re-derive live.

## New findings this cycle

1. When a `structure`/namespace name intentionally collides with its enclosing namespace (the
   `Chronicle` pattern — confirmed identical in both the Temporal and Bimodal BXCanonical trees
   per each file's own module docstring), the resulting `dupNamespace` warnings are a correct,
   permanent narrowing target, not a fixable warning. Renaming would alter the definition and is
   out of hygiene-only scope. Apply `set_option linter.dupNamespace false in` per declaration
   (the structure itself, plus each condition def) rather than attempting a rename.
2. `longLine` warnings on `have h : DerivationTree ... := ...` type annotations are always
   mechanically fixable by wrapping the type annotation onto its own indented continuation line
   with zero term-content change. Rebuild after wrapping to confirm no elaboration change.
3. When a `simp only [...]` blanket-replacement candidate for `unusedSimpArgs` recurs verbatim
   at multiple call sites in one file, a single `replace_all` `Edit` handles every site in one
   pass — but only after confirming (via the collected warning list across all sites, not
   assumption) that every site has the exact same fully-reduced argument list.

Cycle-20 findings remain relevant and were re-confirmed this cycle (see plan's RESUME HERE
section for full text): bare `simp [X]` (vs `simp only [X]`) favors declaration-scoped
`set_option linter.flexible false in` over manual reconstruction unless the pattern is a single,
well-understood lemma; `set_option ... in` must precede the doc comment, not follow it.

## Unaddressed items (unchanged, awaiting human decision, out of scope this cycle)

(A) Phase 7's NOTATION.md-upstream-PR-vs-local-exception decision.
(B) The NOTE-block-deletion sign-off.

Neither blocks continued Phase 5 progress.

## Resume instructions

Start at `Bimodal/Metalogic/Soundness/Soundness.lean` (845 lines) per smaller-files-first within
the count-3 tier. Re-verify line count, suppression count, and upstream status live before
starting (counts only ever go down). Apply the same protocol: remove blanket suppressions,
rebuild, narrow surfaced warnings to declaration-scoped suppressions or manual fixes per the
findings above, rebuild file + downstream importers, commit when green.
