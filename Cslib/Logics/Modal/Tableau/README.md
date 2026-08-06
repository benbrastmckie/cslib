# `Modal/Tableau/` Subsystem Notes

This file holds subsystem-wide measurement documentation that does not belong in any single
`.lean` file's module docstring. It was created by the `LoopChecking.lean` -> `S4/` module split
to receive the `## Measured Baseline` section that had accreted in `LoopChecking.lean`'s header
despite covering the whole subsystem (sorry/axiom censuses, size figures for
`FrameSoundness.lean`/`FrameCompleteness.lean`, inventory tallies), not loop-checking
specifically.

## Measured Baseline (Modal Tableau subsystem)

Recorded here because several size and inventory figures for this subsystem drifted between
prose descriptions and the tree. **Every row below carries the command that reproduces it.**
The rule this section exists to enforce: if a figure is quoted anywhere in this subsystem's
documentation, quote the command with it, and re-run the command rather than trusting the
stored number.

**Provenance of this section**: originally captured at commit `7eb51f69` (Lake 5.0.0-src+68218e8,
Lean 4.31.0) inside `LoopChecking.lean`'s header. The `LoopChecking.lean` size/declaration-count
row below was corrected and re-verified twice since: once against tree state `11607e0f` (the
`LoopChecking.lean` -> `S4/` module split's research baseline, 11,393 lines / 241 declarations),
and again after the split completed (1,723 lines / 20 declarations, with the remaining content
distributed across the eleven `S4/*.lean` modules -- see `LoopChecking.lean`'s own header for the
module map). Every other row (`FrameSoundness.lean`/`FrameCompleteness.lean` sizes, the
sorry/axiom censuses, the inventory tallies) is carried over from the original capture unchanged
by this relocation -- this is a move-only refactor of `LoopChecking.lean`'s internal structure,
not a re-audit of the rest of the subsystem. Re-run every command below before citing a figure.

### Size and declaration density

```
wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean
wc -l Cslib/Logics/Modal/Tableau/FrameSoundness.lean
wc -l Cslib/Logics/Modal/Tableau/FrameCompleteness.lean
PAT='^(private )?(protected )?(noncomputable )?'
PAT="$PAT(theorem|lemma|def|abbrev|instance|structure|inductive) "
grep -cE "$PAT" Cslib/Logics/Modal/Tableau/LoopChecking.lean
```

**Corrected `LoopChecking.lean` figures** (the stale `10,540` lines / `230` declarations quoted
in earlier revisions of this section were themselves already drift by the time the `S4/` split
began -- the split's own Phase 1 baseline re-measured the pre-split file at **11,393 lines /
241 top-level declarations / 58 `private`** using the corrected attribute-aware count pattern
above, which the file's own naive in-header grep undercounts). Post-split,
`LoopChecking.lean` is **1,723 lines / 20 top-level declarations** (the S4 driver's entry
points, its termination measure, and its two end-to-end capstone theorems -- see its module
docstring for the full residue rationale and the eleven-module map). The other 221
declarations / ~9,670 lines live in the eleven `S4/*.lean` modules (10,294 lines total there,
the ~624-line difference from the pre-split figure being expected per-module header/import/
docstring overhead across eleven new files).

`FrameSoundness.lean` 5,317 lines, `FrameCompleteness.lean` 4,307 lines, at the original `7eb51f69`
capture -- neither re-measured by the `S4/` split (out of scope; re-run `wc -l` before citing).

### Sorry census

```
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; } \
  | sort -u | grep 'Modal/Tableau/'
```

**1** in this subsystem: `branchSatisfiableIn_s4FC_ancestor_redirect` in `FrameSoundness.lean`,
the retained, user-decided, immovable obstruction (see that lemma's docstring). Dropping the
final `grep` gives **29** code-position sorries repo-wide. Re-verified unchanged (still exactly
1, still that same lemma) at every phase boundary of the `S4/` module split -- a move-only
refactor cannot introduce or remove a sorry, and the gate enforced it at each step.

Three different definitions of "sorry count" circulate and they do not agree, so state which one
is meant. The 29 above counts sorries in *code position*. The CI-pipeline grep
(`grep -rn "\bsorry\b" Cslib/`, minus comment-leading lines) returns 158 because it also matches
docstring prose such as "sorry-free". The `declaration uses 'sorry'` warning count from an
incremental `lake build` is an **undercount** and must never be used as a census: cached modules
do not re-elaborate and so never re-emit their warnings.

### Axiom census -- a scope distinction, not a corrected number

```
grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ | wc -l    # 0
grep -rnE '^axiom ' Cslib/ | wc -l                         # 26
grep -row 'axiom' Cslib/Logics/Modal/Tableau/ | wc -l      # 3
grep -row 'axiom' Cslib/ | wc -l                           # 1701
```

These are **two scopes, not two candidate values for one quantity, and neither supersedes the
other**: this subsystem declares **0** axioms; the repository declares **26**, none of them here.
The 3 and 1,701 figures are raw word occurrences in prose and identifiers, not declarations, and
are recorded only to show why a naive word-count grep diverges. A previously-noted "26 vs 47"
discrepancy was a scope confusion of exactly this kind, not a drift. Unaffected by the `S4/`
module split (move-only; introduces no new axiom anywhere).

### Inventory figures that drifted

```
grep -rho 'Local re-derivation' Cslib/ | wc -l                                    # 55
grep -rl 'ModalTableauResult' --include='*.lean' Cslib/Logics/Modal/Tableau/ | wc -l   # 8
grep -rl 'ModalTableauResult' --include='*.lean' . --exclude-dir=.lake | wc -l    # 9
grep -nE '^(private )?(theorem|lemma) hintikkaS4_' \
  Cslib/Logics/Modal/Tableau/S4/Hintikka.lean | wc -l   # 8
grep -rn 'structure S4LoopInv' Cslib/Logics/Modal/Tableau/S4/Invariant.lean
wc -l CslibTests/S4LoopGuardRegression.lean                                       # 197
```

(The `hintikkaS4_*`/`S4LoopInv` commands above were updated to their post-split file locations,
`S4/Hintikka.lean` and `S4/Invariant.lean` respectively; the counts they report are unchanged by
the move.)

* **Local re-derivation sites: 55**, not the 77 previously carried (figure as it stood before the
  de-duplication effort below; retained here as a historical baseline, not a live count). 77 is
  not reproducible by any obvious command (`-i 're-derivation'` gives 80, `-i 're-deriv'` gives
  106) and is retired. **The smaller headline does not mean less work.** Every per-lemma
  spot-check behind the old figure was an undercount (`modalSubfmls_trans` 4 sites not 3,
  `modalKnownWorlds_fold_spec` 6 not 4, `hasEdge_addEdge_cases` 7 not 4), and the old per-file
  distribution omitted `LoopChecking.lean`'s **14** sites entirely -- the largest file in the
  subsystem (at the time; since split into the `S4/` module cluster). The de-duplication work is
  larger, not smaller.
* **Post-de-duplication update**: the comment-string count is now **12** (`grep -rho 'Local
  re-derivation' Cslib/ | wc -l`, re-measured after `modalSubfmls_self_mem_S5` was deleted from
  `S5Simplification.lean` and its call sites routed to the public `FmpMeasure.lean` origin),
  down from 55 -- but this number was NEVER the authoritative
  measure of duplication and should not be read as "duplication resolved: 55 minus 12". The
  actual tracking mechanism throughout the de-duplication effort was a declaration-level census
  (base-name/suffix-family matching across the subsystem, driven by a reusable script kept
  alongside the project's task-management artifacts), which is systematically more accurate: the
  comment census both undercounts (several genuine duplicates carried no `Local re-derivation`
  comment at all -- comment-driven deletion would have missed them silently) and overcounts in
  the other direction (some `Local re-derivation`-labelled facts are genuinely distinct
  propositions over frame-specific types like `modalUniverseS4`, not re-derivations of the same
  fact, discovered only by a build-time type mismatch when treated as a duplicate). The remaining
  12 comment sites correspond to the residue documented as Reasoned Exclusions (either the origin
  is already public, the copy dodges an ambient instance, or the dependency graph does not reach
  the origin) plus a handful of genuine specializations (frame-specific restatements,
  keyed-driver variants) that were never duplicates. The declaration-level census, not this
  comment count, is the authoritative figure for future maintenance.
* **`ModalTableauResult` spans 8 modules here, 9 repo-wide** (the ninth is
  `CslibTests/S4LoopGuardRegression.lean`). A previously reported span of 11 is drift.
* **`hintikkaS4_*` bridge set: 8 declarations.** Counting *distinct identifiers* instead returns
  11, because three further names occur only in call positions or prose. See the
  "Redirect Forward-Cone Free Transfer" section (`S4/Redirect.lean`) for what was removed and
  when.
* **One root-level `Boneyard/` directory exists** (`find . -type d -name 'Boneyard' -not -path
  './.lake/*'` returns exactly `./Boneyard`), holding declarations archived from this subsystem
  as zero-consumer under the convention documented in `Boneyard/README.md`. It is excluded from
  `lake build`, every census, and every linter by import-reachability -- see that README's
  "Why This Is Free" section for the mechanism.

### Figures deliberately NOT re-measured

Recorded as gaps rather than filled with substitutes. **No number has been fabricated for any of
these, and none should be quoted as measured.**

* The two amplification figures inherited from earlier analysis -- **4 declarations / 1,036
  lines**, and **43 declarations / 1,983 lines reachable from `modalTableauS4Keyed_complete`** --
  are unverified inheritances. Re-measuring them needs a transitive-dependency closure over the
  elaborated environment, which needs built `.olean`s for these modules.
* The redirect semantic surface (reported as 4 clauses / 14 code lines) is likewise an inherited
  figure, not a row of this capture.

Anything depending on these must re-measure them, or say plainly that it is relying on an
unverified inheritance.

### Build gate at capture

`lake build` failed at the original `7eb51f69` capture, and the failure was **outside this
subsystem**: a non-exhaustive match in
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` (introduced by commit
`88b198bf`, belonging to in-flight work on the constructive nested-sequent development).
`lake exe checkInitImports` then failed downstream as a consequence, not as an independent
defect. This is historical: at the `S4/` module split's own baseline (tree state `11607e0f`) and
throughout the split, `lake build`/`checkInitImports` were green at every phase boundary (see
`specs/565_loopchecking_split_s4_modules/artifacts/baseline.md` for the recorded gate sweep).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
