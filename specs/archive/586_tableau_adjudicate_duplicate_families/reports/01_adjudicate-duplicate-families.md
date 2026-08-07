# Adjudicating the Duplicate Families the Support Extraction Left Unresolved

**Task**: 586 — statement-equivalence duplicate adjudication for the modal-tableau refactor programme.
**Status**: research complete. Read-only except for one reversible build experiment, fully restored.
**Input**: `specs/558_tableau_support_private_dedup/reports/02_statement-equivalence-audit.md`
(45 rows: 38 IDENTICAL, 6 WEAKER, 1 DIFFERENT, 0 NOT_FOUND). Per instruction, the audit was **not**
re-run; it was taken as given and *located* against the current tree.

---

## 1. Headline: the audit's row set is stale, and 43 of 45 rows no longer exist

The task brief presumes 45 surviving re-derivation rows awaiting deletion. **They do not survive.**
A name-by-name census against the current tree finds **exactly two** of the audited declarations
still present. Of those two, one is explicitly outside this task's scope boundary, and one is in
scope and has been verified deletable.

**Net actionable work for this task: one declaration deletion, eight call-site rewrites, and
prose reconciliation.**

### Why the audit says otherwise

The audit was performed against the *duplicate inventory* recorded in
`.../reports/01_tableau-support-private-dedup.md`, not against the live tree. Its own header says
so ("against the duplicate inventory that extraction measured by signature matching"). Meanwhile
task 558's own Phases 8–11 had already deleted those same declarations. The commit timeline is
unambiguous — all on 2026-08-05:

| Commit | Time | What |
|--------|------|------|
| `08753cd2` | 00:11:28 | phase 8: delete Tier-2 duplicates — LoopChecking.lean and S5Simplification.lean |
| `b248294c` | 00:13:55 | phase 9: delete Tier-2 duplicates in the remaining four files |
| `4f63cdec` | 00:32:42 | phase 11: final census, comment cleanup, and full gate |
| `d7cab22f` | **05:58:34** | **record statement-equivalence audit of surviving re-derivations** |

The audit was committed ~5.5 hours *after* the deletions it enumerates as surviving. This is an
input-staleness defect in the audit, not a regression in the tree: the work the audit recommends
was already done, correctly, by the task that commissioned the audit.

---

## 2. Declaration-level census: all 45 audited rows located by name

Anchored on declaration names only, never line numbers, per the task brief.

### GONE (43 rows — deleted by task 558 phases 8–11)

`modalKnownWorlds_fold_spec_{B,Five,FS,S4,S5}`, `modalKnownWorlds_fold_nodup_S5`,
`mem_modalKnownWorlds_{B,Five,C,FS,S4,S5}`, `modalKnownWorlds_mono_append_{B,C,FS,S4,S5}`,
`modalKnownWorlds_nodup_{S4,S5}`, `known_label_le_modalMaxWorld_Five`,
`mintGroup_label_eq_freshWorld_S4`, `modalMaxWorld_foldl_le_of_forall_{Five,S5w}`,
`modalMaxWorld_le_of_forall_label_le_{Five,S5w}`, `modalSubfmls_trans_{S5,Five}`,
`modalUniverse_mem_formula_{Five,S5w}`, `mem_modalUniverse_of_{Five,S5w}`, `mem_boxPositivesOf_S5`,
`hasEdge_addEdge_cases_{B,Five,C,anc,FS,S4,local}`, `mem_successorsOf_hasEdge_{S4,S5}`,
`hasEdge_mem_successorsOf_origin`, `outDeg_addEdge_{self,ne}_S4`,
`modalExpMeasure_{split,append,const_exp}_S4`.

Zero matches for each as a declaration. `modalSubfmls_trans_S5` survives only as a *prose mention*
in `S5Simplification.lean`'s module docstring recording its own consolidation.

### PRESENT (2 rows)

| Declaration | Origin | Origin public? | Origin reachable? | Verdict |
|---|---|---|---|---|
| `modalSubfmls_self_mem_S5` (`S5Simplification.lean`, private) | `modalSubfmls_self_mem` (`FmpMeasure.lean`) | **yes** (`@[simp] lemma`) | **yes** — `S5Simplification.lean` carries `public import Cslib.Logics.Modal.Tableau.FmpMeasure` | **IN SCOPE — delete** |
| `accFreshInv_append_S4` (`LoopChecking.lean`, private) | `accFreshInv_append` (`Soundness.lean`, private) | no | **no** | **OUT OF SCOPE** |

### Independent cross-check

A suffix-family census over all 910 declarations in `Cslib/Logics/Modal/Tableau/` (matching any
suffixed declaration whose unsuffixed base name also exists as a declaration) returns **14 residue
families** — reproducing task 558 Phase 11's recorded final figure of "14 duplicates / 14 families"
exactly, with zero drift. Twelve of those fourteen are not audit rows at all; they belong to the
`hintikka_congr` / `modalApplyOne_fresh` / `boxProps_outputs_subset` / TDriver→BDriver families
that the audit never covered.

---

## 3. The three verdict classes, adjudicated

### 38 IDENTICAL → 37 already resolved; 1 actionable

The one survivor is `modalSubfmls_self_mem_S5`. See section 4.

### 6 WEAKER → all already deleted; the mandatory pre-deletion check passes retrospectively

The task brief requires confirming that no call site consumes the `.1` (Nodup) component of the
origin conjunction before deleting the weak copies whole-cloth. Since the deletions already
landed, this is a retrospective verification, and it **passes cleanly**:

- The **strong** form is preserved and public: `Support/KnownWorlds.lean` `modalKnownWorlds_fold_spec`
  carries both the `hws0 : ws0.Nodup` hypothesis and the `.Nodup` conjunct, matching the
  `FmpMeasure.lean` original.
- Its `.1` component **is** consumed — `Support/KnownWorlds.lean`'s `modalKnownWorlds_nodup` is
  defined as `(modalKnownWorlds_fold_spec l [] List.nodup_nil).1`.
- `modalKnownWorlds_nodup` is public and has six live consumers (`FmpMeasure.lean` ×4,
  `LoopChecking.lean` ×2).

The per-file recovery-route difference the brief flags (S5Simplification's `_fold_nodup_S5` splinter
vs. the other four files obtaining Nodup from `modalKnownWorlds_nodup_S4/_S5`) is moot: the split
recovery and all five suffixed `_nodup` variants are gone, and every consumer now routes through
the single public `modalKnownWorlds_nodup`. Nothing was lost.

### 1 DIFFERENT → already correctly resolved; the trap did not fire

`hasEdge_mem_successorsOf_origin` was **not** conflated with `mem_successorsOf_hasEdge`.
`Support/Accessibility.lean` now publishes both directions as distinct public lemmas —
`mem_successorsOf_hasEdge` and its converse `hasEdge_mem_successorsOf` — and its module docstring
states explicitly that they "form a converse pair" and that the second "is a distinct fact from
`mem_successorsOf_hasEdge`, not merely its restatement." No further action.

---

## 4. The one actionable item, and the stale rationale blocking it

### What the record says

Task 558's Phase 10 Reasoned Exclusions table retains `modalSubfmls_self_mem` on this ground:

> Its origin is already public **and** the copy exists to dodge an ambient `[Hashable Atom]`
> instance that callers cannot `omit`. De-privatization cannot remove it; deleting it would break
> the call sites it exists to serve.

The copy's own docstring makes the same claim: the origin's "signature implicitly carries unused
`[Hashable Atom]`, which these `omit [Hashable Atom]` lemmas cannot supply".

### Why that rationale is stale

`git blame` dates the two facts:

| Line | Commit date | Content |
|---|---|---|
| `S5Simplification.lean` copy + docstring | **2026-07-15** | `private lemma modalSubfmls_self_mem_S5` created, with the `[Hashable Atom]` rationale |
| `FmpMeasure.lean` origin's `omit` line | **2026-07-27** | `omit [DecidableEq Atom] [Hashable Atom] in` added *above* the origin |

The rationale was true when written and became false twelve days later. The origin now carries the
**same** `omit [DecidableEq Atom] [Hashable Atom] in` prefix as the copy, so the two signatures are
byte-identical and instance-free, and the two proofs are byte-identical
(`cases φ <;> simp [modalSubfmls]`). Phase 10 recorded the exclusion without re-checking the
origin's signature after the 07-27 change.

Corroborating evidence independent of blame: **`S5Simplification.lean` already calls the origin
directly**, at four sites in the same file, alongside `modalSubfmls_trans` (another `omit`-prefixed
`FmpMeasure.lean` origin) inside the very declaration that also uses the copy.

### Empirically verified, not merely argued

A reversible experiment was run and the tree restored:

1. Rewrote all 8 call sites of `modalSubfmls_self_mem_S5` in `S5Simplification.lean` to the origin
   `modalSubfmls_self_mem` → `lake build Cslib.Logics.Modal.Tableau.S5Simplification` **green**.
2. Additionally deleted the `omit` line, docstring, and `private lemma` declaration →
   `lake build` of `S5Simplification` + `FiveSimplification` + `FrameSoundness` **green**.
3. Restored from a pre-experiment copy; `git status --porcelain Cslib/` clean; rebuild green.

The deletion is therefore verified feasible before planning, not assumed.

### Call sites to rewrite (8, all in `S5Simplification.lean`)

All eight are of the identical shape `List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 X)` with
`X ∈ {φ, ψ}`; the rewrite is a pure name substitution to `modalSubfmls_self_mem`. Locate by the
declaration name, not by line number.

A repo-wide reference sweep confirms `S5Simplification.lean` is the **only** live consumer. The
other matches are frozen historical `.lean` artifacts under `specs/archive/`, which are not part of
the build and must not be edited.

---

## 5. Scope boundary: what this task must not absorb

`accFreshInv_append_S4` is the reachability family the brief explicitly excludes. Verified from
the actual import headers:

- `LoopChecking.lean` imports `FmpMeasure`, `FrameRules`, `Support.Accessibility`,
  `Support.KnownWorlds` (+ Mathlib). It does **not** import `Soundness.lean`.
- `Soundness.lean` imports `Saturation`, `SoundnessStep`, `LoopInduction`, `Support.Accessibility`
  — it is a sibling of `LoopChecking`, never upstream of it.
- The origin `accFreshInv_append` is `private` to `Soundness.lean`.

De-privatizing the origin would not help; a new import would be required. This is class (c) in task
558's taxonomy and stays untouched. The sibling class-(c) families (`hasEdge_addEdge_mono` for
`FrameSoundness`, and `modalApplyOne_boxPos_acc_eq` / `modalApplyOne_diamondNeg_acc_eq` /
`not_shape_of_not_or` for `BDriver`←`TDriver`) are likewise out of scope.

---

## 6. Measured baselines (current tree, re-measured after task 564 landed)

| Gate | Baseline | Notes |
|---|---|---|
| `lake build Cslib` | **exit 0, 3313 jobs** | Re-measured; the St-ladder and box-plus landings and task 564 have moved this figure |
| `Modal/Tableau` sorry census | **exactly 1** | `branchSatisfiableIn_s4FC_ancestor_redirect`, `FrameSoundness.lean`. Naive `grep -rn '\bsorry\b'` returns **24** lines over-counting docstring prose (`sorry-free`) and `LoopChecking.lean`'s own census-script text |
| `Modal/Tableau` axioms | **0** | `grep -rnE '^axiom '` |
| `lake shake --add-public --keep-implied --keep-prefix` | **9 findings, exit 1** | 9 files, **none in Modal/Tableau**: `Algorithms/Lean/TimeM`, `Computability/.../MultiTape/Deterministic`, `Foundations/Data/StackTape`, `Foundations/Relation/Defs`, `Computability/.../SingleTape/NonDeterministic`, `Foundations/Relation/Confluence`, `Foundations/Control/Monad/Free`, `Languages/CCS/Basic`, `Languages/CombinatoryLogic/Defs`. **Do not gate on exit 0** |
| `lake lint` | **145 findings, exit 1** | Matches the brief's stated 145 exactly. Gate on **delta**, not exit code. See §6.1 |
| `lake exe checkInitImports` | **exit 0** | |
| `lake exe lint-style` | **exit 0** | |
| `lake test` | **exit 0, 3676 jobs** | |
| `Local re-derivation` comment sites | **13** repo-wide | Drops to 12 after the one deletion. Note `LoopChecking.lean`'s prose records this as "**11**" — already drifted before this task |

Downstream build after the S5Simplification deletion measured **896 jobs** for the three-module
scoped target, vs **868** for `S5Simplification` alone — consistent, no unexpected rebuild fan-out.

### 6.1 Lint baseline

Re-measured: **145 findings, exit 1** — matching the brief's stated baseline exactly, with no drift
from the St-ladder, box-plus, or task 564 landings. (The non-zero exit is the steady state: all 145
are reported at `error:` severity.) The dominant category repo-wide is `unusedArguments` on
instance binders — a large
`[Hashable Atom]` cluster in `FrameSoundness.lean`, plus `[Denumerable …]` / `[NoMaxOrder D]` /
`[NoMinOrder D]` clusters in `Logics/Temporal/` and a `[LawfulBEq α]` finding in `FmpMeasure.lean`.

**Gate on delta = 0, not on exit code.** The mechanism matters here: `unusedArguments` is precisely
the linter that the `omit [DecidableEq Atom] [Hashable Atom] in` discipline exists to satisfy. The
declaration being deleted already carries that `omit` prefix, so it contributes zero findings and
its removal must move the count by exactly zero. A non-zero delta after Phase 2 would signal that
something other than the intended deletion happened.

Additional gates measured green in this pass: `lake exe checkInitImports` **exit 0**,
`lake exe lint-style` **exit 0**.

---

## 7. Reuse check (CSLib reuse-first)

No new definition, lemma, notation, or typeclass is proposed by this task. Every action is a
deletion replaced by a reference to an existing public origin:

- `Support/KnownWorlds.lean` and `Support/Accessibility.lean` already exist and already publish
  every KNOWNWORLDS / SUBFMLS / ACCESSIBILITY origin the audit names. No new Support module is
  needed.
- `FmpMeasure.lean` `modalSubfmls_self_mem` is already public and already imported. No
  de-privatization, no import addition, no re-export.

---

## 8. Recommended plan shape

Small task. Four phases, sequential; phases 2–3 are the only ones that write Lean or prose.

**Phase 1 — Drift guard (verification only).** Re-run the declaration-level census before touching
anything. Expect 14 residue families and exactly the two audit-row survivors. If the census returns
anything else, stop: the tree moved again and the adjudication must be re-derived.

**Phase 2 — Delete the one in-scope duplicate.** In `S5Simplification.lean`: rewrite the 8 call
sites to `modalSubfmls_self_mem`; delete the `omit` line, docstring, and `private lemma
modalSubfmls_self_mem_S5`; rewrite the module docstring's `## modalSubfmls Structural
Re-Derivations` section, whose entire body is now false (it asserts the copy is retained for the
`[Hashable Atom]` reason). Verify with `lake build Cslib.Logics.Modal.Tableau.S5Simplification`
before proceeding — already demonstrated green in §4.

**Phase 3 — Reconcile the stale records.** Three prose defects, all directly caused by the audit
families' deletion:
1. `FiveSimplification.lean` carries an **orphaned section header**
   `/-! ## modalKnownWorlds/modalUniverse Local Re-Derivations` whose body describes Five-suffixed
   re-derivations that no longer exist and which is followed immediately by the next section
   header, with no declarations in between. Remove it.
2. `LoopChecking.lean`'s inventory-census prose records 11 `Local re-derivation` comment sites; the
   true count is 13, becoming 12 after Phase 2. Correct it.
3. `S5Simplification.lean`'s module docstring claims `modalSubfmls_self_mem_S5` is "the sole
   surviving local re-derivation" retained for `[Hashable Atom]` reasons — false on both counts
   after Phase 2.

Also record, in this task's artifacts, that task 558's Phase 10 Reasoned Exclusions entry for
`modalSubfmls_self_mem` is superseded — its evidence ("Confirmed the ambient instance at the copy's
site and the absence of an `omit` escape") did not survive the origin's 2026-07-27 `omit` addition.
Historical plan files under `specs/558_.../` are a record of what was done and should not be
rewritten; the correction belongs in this task's summary.

**Phase 4 — Full gate.** `lake build Cslib` (expect exit 0; job count 3313 or lower by the one
removed declaration), Modal/Tableau sorry census exactly 1, 0 axioms, `lake shake` unchanged at 9
findings with none in Modal/Tableau (not gated on exit 0), `lake lint` delta 0,
`lake exe checkInitImports` exit 0, `lake exe lint-style` exit 0, `lake test` green.

### Zero-debt compliance

No phase can introduce a `sorry`: the only Lean change is deleting a lemma whose proof already
exists verbatim at a reachable public origin, verified by build. No new axioms. If Phase 1's drift
guard fails, the correct response is `[BLOCKED]` for user review, not deferral.

---

## 9. Risks

| Risk | Severity | Mitigation |
|---|---|---|
| Tree moves again between research and implementation | Medium | Phase 1 drift guard is mandatory and gates all writes |
| The brief's premise (45 deletions) is treated as a target, producing invented work | **High** | This report is the countermeasure: the actionable set is one declaration. Do not manufacture deletions to hit 45 |
| `accFreshInv_append_S4` silently absorbed as "the last one left" | High | Explicitly out of scope; §5 records the import-graph evidence |
| `@[simp]` on the origin changes simp behaviour at the 8 sites | Low | The origin is `@[simp]` and already in scope at every site (it is imported publicly), so the simp set is unchanged by the deletion. Build verified green |
| Lint delta from removing a private declaration | Low | Gate on delta, not exit code |

---

## 10. Incidental observations (not scope, recorded so they are not rediscovered)

1. **Stale line-number citations in a sibling subsystem.**
   `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` cites the origin as
   `FmpMeasure.lean:266` and `FmpMeasure.lean:266-754` in two docstrings. The origin now sits at a
   different line. This is exactly the failure mode the task brief warns about ("anchor on
   declaration names, never line numbers"). Different subsystem, not this task's territory —
   flagged for a future prose pass.
2. **`LoopChecking.lean`'s inventory census has already drifted** independently of this task: it
   records 11 `Local re-derivation` comment sites where the tree has 13. That file's own text warns
   the comment count "was NEVER the authoritative measure of duplication," so the drift is
   cosmetic — but Phase 3 should correct it rather than leave a known-wrong number in place.
3. **The audit's own citation-graph notes are now historical.** The `FmpMeasure → S5w → Five`
   chain, the `hasEdge_addEdge_cases_Five`-lives-in-`FrameCompleteness.lean` naming oddity, and the
   `known_label_le_modalMaxWorld` name-divergence finding all concern declarations that no longer
   exist. They needed no action and need none now; task 558 Phase 11.1 resolved the last of them
   (`known_label_le_modalMaxWorld_Five`/`_S5w`) explicitly.
4. **`modalSubfmls_self_mem` and `modalKnownWorlds_nodup_S4` being already public** (a brief note in
   the task description) is consistent with what was measured: the former is a public `@[simp]
   lemma` in `FmpMeasure.lean`, and the latter no longer exists at all — its content is served by
   the public `modalKnownWorlds_nodup` in `Support/KnownWorlds.lean`.
5. **`modalExpMeasure_const_exp_S4`'s provenance gap** is closed by deletion: the declaration is
   gone, and `FmpMeasure.lean` retains the public `modalExpMeasure_const_exp` alongside `_split`
   and `_append`. No enumeration discrepancy survives.
