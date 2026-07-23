# Summary 18: Phase 23 -- KB5 completeness BLOCKED (genuine obstruction); all other sub-deliverables landed

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 23 (KB5 completeness capstone) -- now `[PARTIAL]`

## Scope of this dispatch

Resumed from `summaries/17_phase22-kb5-soundness-factored-completed.md`, which shipped
`modalApplyOneKb5`/`modalTableauKb5_sound` by factoring (Phase 22, COMPLETED). This dispatch's
scope was Phase 23 only: `modalTableauKb5_complete`, `instDecidableKb5Valid`, the two docstring
reconciliations, the probe port, and the regression test.

## The mandatory pre-code analysis found a genuine mathematical obstruction

Before writing any code, per the dispatch instructions, the Five/KB5 completeness structure was
worked through on paper (mirroring `extractModelFive`/`modalTruthLemmaFive`/
`modalTableauFive_complete`, `FrameCompleteness.lean`). The finding, subsequently confirmed by a
machine-checked scout lemma:

**`extractModelKb5`'s relation is forced to be `Relation.EuclGen (Relation.SymmGen acc.hasEdge)`**
-- the *least* `kb5FC` (symmetric + right-Euclidean)-satisfying relation that preserves every raw
tableau edge (a hard requirement shared by every extraction in this file, needed for the
box-negative/diamond-positive "K-style" witness cases). This relation, unlike Five's
non-symmetrized `EuclGen acc.hasEdge`, does **not** keep the root's reach capped at its direct
`acc.hasEdge` successors: given a raw chain `0 → a → c` (root mints direct successor `a`; `a`,
non-root, later mints a fresh witness `c` because no reuse candidate exists yet -- a routine,
reachable shape under Route (a)'s witness-reuse mint arms), `(extractModelKb5 b acc).r 0 c` holds.
This is landed as `extractModelKb5_root_reach_scout` (`FrameCompleteness.lean`), verified
`lean_verify`-clean (zero axioms):

```lean
private lemma extractModelKb5_root_reach_scout {α : Type*} {r : α → α → Prop} {w0 x y : α}
    (h1 : r w0 x) (h2 : r x y) :
    Relation.EuclGen (Relation.SymmGen r) w0 y :=
  Relation.EuclGen.eucl (Relation.EuclGen.base (Relation.SymmGen.of_rel_symm h1))
    (Relation.EuclGen.base (Relation.SymmGen.of_rel h2))
```

`modalApplyOneKb5 := modalApplyOneFive`'s root arm (Phase 22's literal alias) only forces
propagated content at **direct** `acc.hasEdge 0 w'` successors -- by design, since that
restriction is exactly what Five's own soundness needs (Five's root is not itself reflexive, so
over-propagating from root would be unsound for the strictly larger `fiveFC` class). This breaks
the truth lemma's root box-positive case for KB5: `T(□ψ)@0 ∈ b` needs `T(ψ)@w' ∈ b` for *every*
`w'` with `(extractModelKb5 b acc).r 0 w'`, which now includes non-direct-successor worlds like
`c`, but the existing rule's saturation never forces content there.

**Not an impossibility.** K5/KB5 completeness via a rooted Euclidean tableau is standard
(Blackburn–de Rijke–Venema §4.8-4.9). What is blocked is specifically *reusing*
`modalApplyOneFive`'s root-restricted rule for the completeness direction. A fix needs a genuinely
new KB5-specific propagation rule (root triggers dumping to the full non-root cluster, matching
the non-root arm's own unconditional propagation, plus -- since root becomes reflexive whenever it
has a successor, `Relation.symm_rightEuclidean_root_refl` -- propagating root's own box content
back onto world `0`), together with its own soundness proof ("factor, not clone" does not transfer
to this direction: the same unrestricted propagation would be unsound for `fiveFC`) and its own
completeness argument. This is comparable in scope to Phases 15-21's Five construction, not a
same-dispatch fix.

Also confirmed algebraically (not just for this rule): no `kb5FC`-satisfying relation can
simultaneously (a) preserve every raw edge, (b) relate all known non-root worlds to each other
(what the non-root propagation arm's own soundness needs), and (c) restrict root to its direct
successors, once root has any successor and some direct successor has a raw child. `RightEuclidean`
applied to the forced facts `r a 0` (symmetric partner of the required raw-edge survival `r 0 a`)
and `r a c` (raw-edge survival for `a`'s own child) forces `r 0 c` directly -- this is not an
artifact of the `EuclGen (SymmGen ·)` closure choice; no alternative closure operator avoids it.

## What landed (all sorry-free, axiom-free where checked)

1. **`Cslib/Foundations/Relation/Euclidean.lean`**: `EuclGen.symm_of_symm` (`EuclGen` preserves
   symmetry of its base relation) + its packaged `Std.Symm (EuclGen r)` instance. General,
   reusable foundational fact, `lean_verify`-confirmed zero axioms. Built and committed standalone
   (`4ac3022c`) before the rest, since `lake build Cslib.Foundations.Relation.Euclidean` succeeded
   cleanly (no external interruption on that module).
2. **`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`**:
   - `extractModelKb5` + `extractModelKb5_r`/`_rightEuclidean`/`_symm`/`_hasEdge_imp_r` --
     extraction infrastructure, all free/mirroring `extractModelFive`'s pattern.
   - `extractModelKb5_root_reach_scout` (the machine-checked obstruction witness above).
   - A dedicated blocker `/-! -/` note immediately after the extraction lemmas, explaining the
     obstruction precisely for a future dispatch.
   - Reconciled the "5/KB5 Coverage via the S5 Route" docstring (previously at :565-614, relocated
     by content since line numbers had drifted) to the accurate state: 5 (Euclidean) delivered; KB5
     rule + soundness delivered (Phase 22); KB5 completeness specifically blocked, with a pointer to
     the new note. The former "OUT OF SCOPE ... bespoke construction" paragraph (which claimed
     missing library infrastructure) is removed/rewritten -- `Relation.EuclGen` exists and is used.
3. **`Cslib/Logics/Modal/Tableau/S5Simplification.lean`**: same accurate-not-optimistic
   reconciliation of the "Scope Note: Pure-K5 / Pure-5" block (relocated by content, was drifted
   from the plan's cited :3018-3037). The file-local prohibition on introducing a custom `EuclGen`
   closure operator **in this file** is kept verbatim, per instruction -- still correct, since
   `EuclGen` lives in `Euclidean.lean`. Docstring-only edit; no `S5w*` code touched.
4. **`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`**: ported
   `specs/515_.../probes/five-s5-separation.lean`'s theorems (`s5FC_imp_fiveFC`,
   `fiveValid_imp_s5Valid`, `emptyFrame` + its `RightEuclidean`/`Std.Symm` instances,
   `box_atom_holds`, `atom_fails`, `boxImp_s5Valid`, `boxImp_not_fiveValid`,
   `boxImp_not_kb5Valid`, `fiveValid_ssubset_s5Valid`, `s5FC_imp_kb5FC`, `kb5Valid_imp_s5Valid`,
   `kb5Valid_ssubset_s5Valid`) into the live tree, right after `kb5Valid`'s own definition, beside
   the frame-class defs. `lean_verify`-confirmed zero axioms on the two `_ssubset_` capstones.
   Landed 3 dispatch-local `omit [DecidableEq Atom] [Hashable Atom] in` markers had to be *removed*
   from the initial port (those variables are not in scope until later in the file, `variable
   [DecidableEq Atom] [Hashable Atom]` at line 1406) -- caught by re-reading the file's variable
   scoping before building, not by a build failure.
5. **`CslibTests/ModalFrameSeparation.lean`** (new, registered in `CslibTests.lean`): the `□p → p`
   separation regression test. `s5Valid`/`fiveValid` checked via `by decide` against
   `instDecidableS5Valid`/`instDecidableFiveValid` -- confirmed via `lean_run_code` to complete
   quickly (`"success":true,"timed_out":false`), not hang. `kb5Valid`'s negation checked via the
   ported `boxImp_not_kb5Valid` directly (a term proof, not `decide`), since `instDecidableKb5Valid`
   is transitively blocked and there is no `Decidable (kb5Valid φ)` instance to decide against. A
   raw `#eval` was deliberately avoided: Phase 14's own already-landed deviation note (plan file)
   records that `#eval`/`#guard` of the tableau fails to link native symbols
   (`modalFuel._redArg`) inside `CslibTests`' `module`-mode barrel, since `Cslib` is not built with
   `precompileModules := true`. `by decide` (kernel reduction) sidesteps that specific issue.

## Verification performed, and what is still pending

**External interruption, matching Phase 22's own precedent exactly**: at dispatch start (and
throughout most of this dispatch), `Cslib/Logics/Modal/Tableau/LoopChecking.lean` was mid-edit by
a concurrent session (task 511, uncommitted WIP, real build errors: `omega` failure at :927,
`Hashable Atom` synthesis failures at :965/:1037). Per the hard constraint this file was **never
touched, staged, or committed**. `FrameCompleteness.lean` imports `LoopChecking` directly, so a
full `lake build`/`lake test` of the touched modules could not complete for most of the dispatch.

Verification performed instead:
- `lake build Cslib.Foundations.Relation.Euclidean` -- clean, standalone (no dependency on
  `LoopChecking`).
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` -- one attempt got far enough to report
  `✔ Built ... FrameCompleteness` (via a stale-cached `LoopChecking.olean`) before a *later*
  attempt failed specifically on `LoopChecking.olean` going missing from the build cache -- i.e.
  `FrameCompleteness.lean`'s own elaboration succeeded at least once during this dispatch.
- `lean_verify`/`#print axioms`-equivalent via `lean_goal`/`mcp__lean-lsp__lean_verify` on every new
  public declaration: all report `[]` (zero axioms) or the expected
  `[propext, Classical.choice, Quot.sound]`-subset, with one transient exception (`sorryAx`
  reported once on `extractModelKb5_symm` while `LoopChecking` was broken, re-checked clean
  afterward -- consistent with Phase 22's documented "LSP reports stale/incorrect state under this
  interruption" finding, not a real issue; confirmed via `grep -n sorry` across all touched files
  returning zero non-prose hits).
- `lean_run_code` for the two `decide`-based regression checks (`fiveValid`/`s5Valid`) --
  `"success":true,"timed_out":false"` both times.
- `lake exe lint-style <file>` per touched file (all clean); the barrel file `CslibTests.lean`
  itself hits a pre-existing, unrelated tool quirk when linted standalone (`Cslib.lean` reproduces
  the same quirk) -- not a regression, and not hit when `lint-style` runs project-wide (no args).

**Still pending** (blocked purely on the external `LoopChecking.lean` resolving, per Phase 22's own
precedent that this resolved mid-dispatch previously): `lake build` (full), `lake exe
checkInitImports`, `lake lint`, `lake shake --add-public --keep-implied --keep-prefix`, `lake
test`. A follow-up dispatch (or the orchestrator, if it retries) should re-run the full CSLib CI
pipeline once `LoopChecking.lean` is committed/green, and mark Phase 23's "Full CI" checklist item
`[x]` at that point -- no further code changes are expected to be needed.

## Sorry / axiom / vacuous-definition audit

- `grep -rn '\bsorry\b'` across all five touched files: zero non-prose hits (three prose mentions
  of the word "sorry" inside docstrings, e.g. "sorry-free", correctly excluded).
- No `def X := True`/`theorem X := trivial`-style vacuous placeholders introduced anywhere.
- No new `axiom` declarations. Repo-wide `axiom` count unchanged (still the pre-existing baseline).
- `modalTableauKb5_complete`/`instDecidableKb5Valid` are genuinely **not attempted** as stubs --
  they do not appear anywhere in the touched files, consistent with "never introduce a `sorry` or
  placeholder axiom" from the escalation protocol.

## Plan Deviations

- **`modalTableauKb5_complete`/`instDecidableKb5Valid`**: marked `[BLOCKED]` in the plan
  (Phase 23's own checklist), not attempted with a `sorry`. See the obstruction analysis above.
- **Docstring reconciliation**: landed with *accurate* content reflecting the actual (partial)
  delivery state, not the plan's anticipated fully-delivered state. The plan's own line-number
  citations (`FrameCompleteness.lean:571-590`, `S5Simplification.lean:3018-3037`) had drifted;
  both scope notes were relocated by content (grep for "OUT OF SCOPE" / "Scope Note") per the
  dispatch instructions, not by the stale line numbers.
- **Regression test**: landed in `CslibTests/` as instructed, but via `by decide` (not a bare
  `#eval`) for the two decidable cases, and via a direct term proof (not `decide`) for the
  `kb5Valid` negation, per the reasoning in item 5 above. This reuses, rather than re-litigates,
  Phase 14's own already-sanctioned finding about `#eval`/native-linking in `CslibTests`.
- **Full CI**: not run to completion this dispatch, due to the external `LoopChecking.lean`
  interruption (out of this dispatch's control, matching Phase 22's own precedent). All other
  verification substitutes (`lake build` on unblocked modules, `lean_verify`, `lean_run_code`,
  `lint-style` per file, exhaustive `sorry`/axiom grep) were performed instead.

## Files touched

- `/home/benjamin/Projects/cslib/Cslib/Foundations/Relation/Euclidean.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/S5Simplification.lean`
- `/home/benjamin/Projects/cslib/CslibTests.lean`
- `/home/benjamin/Projects/cslib/CslibTests/ModalFrameSeparation.lean` (new)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`

**Never touched**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (concurrent task 511 session).

## Commits

- `4ac3022c` -- `task 515 phase 23.1: add EuclGen.symm_of_symm (symmetric-base preservation)`
- `d5e528b0` -- `task 515 phase 23.2: land extractModelKb5 infra, blocker note, docstring reconciliation, probe port, regression test`

## What remains open

- **`modalTableauKb5_complete`/`instDecidableKb5Valid`**: needs a genuinely new KB5-specific
  propagation rule (not an alias of `modalApplyOneFive`) plus its own soundness and completeness
  proofs. Comparable in scope to Phases 15-21. A follow-up task, per the escalation protocol --
  not re-narrated as an impossibility.
- **Full CI pipeline**: pending `LoopChecking.lean`'s concurrent-session resolution. No code changes
  expected; just re-run and check the box.
- The task-level plan `Status` field remains `[IMPLEMENTING]` -- Phase 23 is `[PARTIAL]`, not
  `[COMPLETED]`, so the plan is not reconciled to `[COMPLETED]` this dispatch.
