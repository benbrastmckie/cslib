# Summary — Land the Measured Tableau Baseline and Correct Four Documentation Defects

- **Scope**: documentation-only. No declaration, definition, proof, or tactic was altered.
- **Files modified**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean`,
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- **Diff**: 191 insertions, 11 deletions — every deleted line is prose inside a docstring.
- **`FrameCompleteness.lean`**: in declared scope but required no edit; left untouched.

---

## 1. The four defects

### Defect (1) — `keysOriginS4` was never removed

The comment claimed `keysOriginS4` and its supporting lemmas had been removed alongside
`blockedRedirect_boxctx_mem`. False. `keysOriginS4` is still declared, together with
`keysOriginS4_entry`, `keysOriginS4_mono_branch`, and `keysOriginS4_mono_acc`.

**Deliberate deviation from the task description's own figure.** The description says
"22 code consumers". That figure is not reproducible and was **not** written into the repository.
The corrected comment records the re-measured figures with the commands that produce them:

```
grep -rn 'keysOriginS4' --include='*.lean' Cslib/ | wc -l                             # 61
grep -rn 'keysOriginS4' --include='*.lean' Cslib/ | grep -vE ':[[:space:]]*(--|[/][-]|[-][|]|[*])' | wc -l   # 55
```

The conclusion is unchanged and holds with a large margin: not zero-consumer, so not
Boneyard-eligible, so the removal claim was false.

The grep in the landed comment uses bracketed character classes (`[/][-]`, `[-][|]`) rather than
the literal two-character sequences. This is not cosmetic: Lean block comments **nest**, so a
literal `/-` inside a `/-! ... -/` docstring opens a nested comment and silently swallows the
rest of the file. The bracketed form was verified to reproduce the same figure (55) before use.

### Defect (2) — stale `_boxed reflTransGen` bridge references

`hintikkaS4_box_pos_reflTransGen_boxed` / `hintikkaS4_dia_neg_reflTransGen_boxed`, and the
forward-cone conjuncts they fed (`redBoxForwardCone` / `redDiaForwardCone`), were deleted by
commit `c4b33f63` ("revert red-channel machinery orphaned by Gate B, retain route-independent
assets"), verified present in the log. The corrected comment now pins the removal to that commit,
states explicitly that the identifiers no longer exist (the only surviving occurrences anywhere
under `Cslib/` are the two prose mentions in that paragraph), and records the consequence: the
`hintikkaS4_*` bridge set is now **8**, where the previously asserted ten **was correct when
written** — `c4b33f63` removed two of them. The near-miss identifier count of 11 is recorded as
a distinct measurement so the two cannot be confused again.

### Defect (3) — the `keysRootEmpty` "possibly orphaned" hedge

Replaced with the audited fact:

```
grep -rn 'keysRootEmpty' --include='*.lean' Cslib/ CslibTests/ | wc -l    # 6
```

All six hits are in `LoopChecking.lean`: the section heading, the two declarations with their
docstrings, and one prose mention. Outside its own entry lemma, `keysRootEmpty` has **zero**
consumers. The comment now says it is retained deliberately — small, sorry-free, true of the
seed state — rather than "pending the re-plan".

### Defect (4) — `branchSatisfiableIn_s4FC_ancestor_redirect` (FrameSoundness.lean)

Both required additions landed:

**(a) Zero-consumer fact.** `grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' --include='*.lean'
Cslib/ CslibTests/` returns exactly 1 hit — the declaration itself. The retained `sorry`
propagates into no other result: recorded obstruction, not load-bearing debt.

**(b) Massacci Theorem 8.1 is stated and never proved.** Independently verified against the
local corpus before writing, not taken on report:

| Check | Finding |
|---|---|
| Theorem 8.1 statement | Present, `chunk_0030.md` — "if the L-tableau … terminates with a π-completed branch, then A is L-satisfiable for U and G". No proof accompanies it. |
| Appendix B.2 | Header "PROOFS OF SECTION 8" at `chunk_0063.md:32`; the body that follows (`chunk_0064.md`) is "Proof (Theorem 8.4)" — **8.4 only**. |
| Deferral | `chunk_0054.md:3-7` defers the Section 8 extension to references [7] (prefixed tableaux) and [20] (completeness via model graphs). |
| Only other mention | `chunk_0030.md:38` — "For K4 or S4 Theorem 8.1 can be extended? to π-modal-completeness." |

The docstring now records that successive soundness routes were appealing to a theorem their
cited source does not prove, so the obstruction is a genuine gap in the source rather than a
transcription failure, and closing it would require importing the model-graph construction from
the deferred references.

The write-up avoids machine-local literature chunk paths in the `.lean` file itself, citing
durable paper-internal anchors (Theorem 8.1, Appendix B.2, references [7]/[20]) instead. The
chunk anchors are recorded here, in the task artifact, where they belong.

---

## 2. The measured baseline table

Landed as a `## Measured Baseline (modal Tableau subsystem)` section in `LoopChecking.lean`'s
module docstring, before `## References`. Every row carries its reproduction command, and the
section states the rule it exists to enforce: quote the command with the figure, and re-run it
rather than trusting the stored number.

Sections landed: size/declaration density; sorry census (with all three competing definitions
distinguished, and the incremental-build warning count explicitly disqualified as a census);
axiom census; drifted inventory figures; deliberately-not-measured figures; build gate.

**Axiom figures landed as a scope distinction, not as a corrected number** — as required.
Tableau subsystem: 0 declarations / 3 raw word matches. Repo-wide `Cslib/`: 26 declarations /
1,701 raw matches. The section states plainly that these are two scopes, not two candidate values
for one quantity, and that neither supersedes the other.

**Corrected figures used** (overriding the task description's stale numbers): `ModalTableauResult`
spans **8** Tableau modules / 9 repo-wide (not 11); re-derivation sites **55** (not 77), landed
together with the reason the smaller headline means *more* work, not less — every per-lemma
spot-check was an undercount and `LoopChecking.lean`'s 14 sites were omitted from the old
distribution.

**Not re-measured, and no substitute fabricated** — recorded explicitly in the landed section:
the two amplification figures (4 declarations / 1,036 lines; 43 declarations / 1,983 lines
reachable from `modalTableauS4Keyed_complete`) and the redirect semantic surface (4 clauses /
14 code lines). The section names these as unverified inheritances and instructs any consumer to
re-measure or say plainly that it is relying on an inheritance.

**Line-count rows are commit-pinned** to `7eb51f69` and flagged as the one part of the table that
moves under ordinary documentation edits — landing this section itself moved two of them
(`LoopChecking.lean` 10,540 → 10,583 before the baseline section; `FrameSoundness.lean`
5,317 → 5,343). The declaration count (230) is unchanged and does not move. Every other figure in
the table was re-run against the working tree and matched.

---

## 3. Verification

**The repo-wide build gate is NOT clear, and is not claimed to be.**
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1329` still fails with
`Missing cases:` (commit `88b198bf`, owned by tasks 554/570). Confirmed still failing, not
repaired, not worked around. `lake exe checkInitImports` was **not** run as a gate and is **not**
reported as passing — it is vacuous while this holds.

**However, scoped verification turned out to be available**, because the failing module is in a
different subtree from both modified files:

| Check | Result |
|---|---|
| `lake build Cslib.Logics.Modal.Tableau.LoopChecking` | **Build completed successfully (847 jobs)** |
| `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` | **Build completed successfully (876 jobs)** |
| Block-comment nesting balance (both files) | balanced — final depth 0, min depth 0 |
| Declaration lines in diff | 0 |
| Removed lines | all prose inside docstrings |
| Tableau sorry census | 1 (unchanged; the pre-existing immovable one) |
| Axiom declarations in modified files | 0 |
| Verified-TRUE claims touched | 0 |

So the documentation edits are **verified to compile**, which is stronger than the anticipated
build-unverified status. They are **not** covered by a repo-wide green build, and
`build_verified` is recorded as `false` in the handoff for exactly that reason, with the scoped
results recorded alongside rather than in place of it.

---

## 4. Plan Deviations

1. **"22 code consumers" not written.** The task description's own figure for defect (1) is not
   reproducible; the re-measured figures (61 / 55) were written with their commands instead, per
   the delegation's correction. Conclusion unchanged.
2. **Comment-safe grep form.** The landed audit command uses `[/][-]` / `[-][|]` character
   classes rather than literal `/-` and `-|`, because a literal `/-` inside a Lean docstring
   opens a nested block comment. Verified to reproduce the same figure before use.
3. **Baseline landed in `LoopChecking.lean` only.** The delegation said "the subsystem's module
   documentation" without naming a file. `LoopChecking.lean` was chosen: it is the subsystem's
   largest module, the one carrying three of the four drifted claims, and the one a reader
   arrives at when chasing these figures. The table was not duplicated into the other two files.
4. **`FrameCompleteness.lean` untouched.** In declared `file_scope`, but none of the four defects
   and no part of the baseline landing required an edit there.
5. **No task-number references added** to any `.lean` file, per
   `.claude/rules/no-task-references-in-deliverables.md`. Pre-existing `specs/553_...` citations
   in surrounding comments were left as found — they are outside this task's four sites.
